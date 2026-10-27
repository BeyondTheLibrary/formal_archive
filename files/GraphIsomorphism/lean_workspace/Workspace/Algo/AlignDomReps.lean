/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, lines 9–11 (§14.1), case 1 of the
repair — the cosets of `ker ϕ*` that cover the coset of a version.
-/
import Workspace.Algo.AlignDomKernel
import Workspace.Algo.AggregateTable
import Workspace.Algo.Coset

/-!
# The cosets of `ker ϕ*`

In case 1 of the repair (`m*` small) the round on the dominant window is the strong descent
to `N = ker ϕ*`: the coset `C = σ G*` of a version is written as a union of left cosets
`ρ N`, and the Chain Rule over the orbits of `N` in the window runs on each of them.

The machine lists the cosets as follows.

* **Right coset representatives** `r_1, …, r_s` of `N` in `G*` come from the breadth-first
  search `Algo.rawCosetReps`. Its fuel must reach the index `|G* : N|`, which is at most
  `m*!` because `ϕ*` maps `G*` to `S(Γ*)` (`Algo.relIndex_kerSubgroup_le`). In case 1
  `m*` is `O(log n)`, so `m*^{m*} ≥ m*!` is quasipolynomial, and the fuel is the list of all
  `m*`-tuples over `m*` letters (`Algo.aggTable`, whose guard `m* ≤ (log₂ n + 1)²` holds in
  case 1). Outside case 1 the fuel is one entry.
* **Left cosets of `C`**: if `c ∈ C` then `C = c G* = ⋃ c r_i⁻¹ N`, so the representatives
  are `c r_i⁻¹` (`Algo.adReps`, `Algo.adReps_cover`). The machine takes for `c` the
  lexicographically least element of `C` (`Algo.aggnCanonCoset`), so the list depends on the
  set `C` only.
* There are at most `|G* : N|` of them (`Algo.adReps_length_le`), as
  `Babai.AlignDominantEnum.Spec` asks.
-/

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Pointwise

/-- The test of case 1 of the repair: line 6 found a dominant color and `m*` is small. -/
def alignRSmall (p : RawAction × RawAlignOutcome) : Bool :=
  alignRHasDom (alignRColorOf p) &&
    !rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1))

/-- The letters of the fuel: `m*` points of `Γ` in case 1, none otherwise. -/
def adFuelDom (p : RawAction × RawAlignOutcome) : List ℕ :=
  if alignRSmall p then (rawOne p.1.2.1).take (alignRMs p) else []

/-- The fuel of the search: one entry per `m*`-tuple over `m*` letters, at least `m*!`
entries in case 1. -/
def adFuel (p : RawAction × RawAlignOutcome) : List ℕ :=
  (aggTable 2 (adFuelDom p, p.1.1.1, adFuelDom p)).2.map (fun _ => 0)

/-- §14.1, lines 9–11: **right coset representatives of `ker ϕ*` in `G*`**. -/
def adRightReps (p : RawAction × RawAlignOutcome) : RawGens :=
  rawCosetReps ((p.1.1.1, alignPairG1 p), (alignKerGens p, adFuel p))

/-- §14.1, lines 9–11: **the left cosets of `ker ϕ*` covering the coset of an element `c`**:
the representatives `c r⁻¹`. -/
def adReps (z : (RawAction × RawAlignOutcome) × RawPerm) : RawGens :=
  (adRightReps z.1).map (fun r => rawMul (z.2, rawInv r))

/-! ## The fuel -/

theorem adFuel_length_of_small {p : RawAction × RawAlignOutcome} (hs : alignRSmall p = true)
    (hms : alignRMs p ≤ p.1.2.1.length)
    (hg : alignRMs p ≤ guardBound 2 p.1.1.1.length) :
    (adFuel p).length = alignRMs p ^ alignRMs p := by
  have hdom : adFuelDom p = (rawOne p.1.2.1).take (alignRMs p) := if_pos hs
  have hlen : (adFuelDom p).length = alignRMs p := by
    rw [hdom, List.length_take, rawOne, List.length_range]
    exact min_eq_left hms
  unfold adFuel
  rw [aggTable_of_guard (by rw [hlen]; exact hg)]
  simp only [tupleTable, List.length_map, length_tuplesOf, hlen]

/-- The index of the kernel of a map to `S(Fin k)` is at most `k!`. -/
theorem relIndex_kerSubgroup_le {Ω : Type*} {G : Subgroup (Perm Ω)} {k : ℕ}
    (f : G →* Perm (Fin k)) : (kerSubgroup f).relIndex G ≤ k.factorial := by
  classical
  have h1 : (kerSubgroup f).relIndex G = f.ker.index := by
    rw [kerSubgroup, Subgroup.relIndex, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
  rw [h1, Subgroup.index_ker]
  calc Nat.card f.range ≤ Nat.card (Perm (Fin k)) := Subgroup.card_le_card_group _
    _ = k.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-! ## The left cosets -/

section Cover

variable {n : ℕ} {dom : List ℕ} {gG gH : RawGens} {js : List ℕ}

/-- **The left cosets cover the coset** of `c`: when the fuel reaches the index,
`c G = ⋃ c r⁻¹ H` over the right representatives `r` of `H` in `G`. -/
theorem leftReps_cover (hd : dom.length = n) (hG : RawGens.WF n gG) (hH : RawGens.WF n gH)
    (hle : decGroup n gH ≤ decGroup n gG)
    (hidx : (decGroup n gH).relIndex (decGroup n gG) ≤ js.length + 1)
    {c : RawPerm} (hc : RawPerm.WF n c) :
    decPerm n c • (decGroup n gG : Set (Perm (Fin n))) =
      ⋃ σ ∈ (rawCosetReps ((dom, gG), (gH, js))).map
        (fun r => decPerm n (rawMul (c, rawInv r))), σ • (decGroup n gH : Set (Perm (Fin n))) := by
  set G := decGroup n gG
  set H := decGroup n gH
  have hGe : gG = (gG.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hG).symm
  have hHe : gH = (gH.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hH).symm
  have hsound := rawCosetReps_sound (gensG := gG.map (decPerm n)) (gensH := gH.map (decPerm n))
    (js := js) hd
  have hcov := rawCosetReps_cover dom (gG.map (decPerm n)) (gH.map (decPerm n)) js hd hidx
  rw [← hGe, ← hHe] at hsound hcov
  have hdec : ∀ r ∈ rawCosetReps ((dom, gG), (gH, js)),
      decPerm n (rawMul (c, rawInv r)) = decPerm n c * (decPerm n r)⁻¹ := by
    intro r hr
    have hr' := (hsound.1 r hr).1
    rw [rawMul_of_wf hc (wf_rawInv hr'), rawInv_of_wf hr', decPerm_encPerm, decPerm_encPerm]
  ext τ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgi : g⁻¹ ∈ G := G.inv_mem hg
    obtain ⟨r, hr, hrN⟩ := hcov g⁻¹ hgi
    refine ⟨decPerm n c * (decPerm n r)⁻¹, ⟨r, hr, hdec r hr⟩, ?_⟩
    refine ⟨decPerm n r * g, ?_, ?_⟩
    · have : (g⁻¹ * (decPerm n r)⁻¹)⁻¹ ∈ H := H.inv_mem hrN
      simpa [mul_inv_rev] using this
    · simp [smul_eq_mul, mul_assoc]
  · rintro ⟨σ, ⟨r, hr, rfl⟩, hτ⟩
    rw [hdec r hr] at hτ
    obtain ⟨u, hu, rfl⟩ := hτ
    refine ⟨(decPerm n r)⁻¹ * u, G.mul_mem (G.inv_mem (hsound.1 r hr).2) (hle hu), ?_⟩
    simp [smul_eq_mul, mul_assoc]

/-- **At most `|G : H|` left cosets**: the right representatives lie in distinct right
cosets. -/
theorem leftReps_length_le (hd : dom.length = n) (hG : RawGens.WF n gG) (hH : RawGens.WF n gH)
    (c : RawPerm) :
    ((rawCosetReps ((dom, gG), (gH, js))).map (fun r => rawMul (c, rawInv r))).length ≤
      (decGroup n gH).relIndex (decGroup n gG) := by
  have hGe : gG = (gG.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hG).symm
  have hHe : gH = (gH.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hH).symm
  have hsound := rawCosetReps_sound (gensG := gG.map (decPerm n)) (gensH := gH.map (decPerm n))
    (js := js) hd
  rw [← hGe, ← hHe] at hsound
  rw [List.length_map]
  exact length_le_relIndex (fun r hr => (hsound.1 r hr).2) hsound.2

/-- Every listed representative is a permutation of `Ω`. -/
theorem leftReps_wf (hd : dom.length = n) (hG : RawGens.WF n gG) (hH : RawGens.WF n gH)
    {c : RawPerm} (hc : RawPerm.WF n c) :
    RawGens.WF n ((rawCosetReps ((dom, gG), (gH, js))).map (fun r => rawMul (c, rawInv r))) := by
  have hGe : gG = (gG.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hG).symm
  have hHe : gH = (gH.map (decPerm n)).map (encPerm n) := (map_encPerm_decPerm hH).symm
  have hsound := rawCosetReps_sound (gensG := gG.map (decPerm n)) (gensH := gH.map (decPerm n))
    (js := js) hd
  rw [← hGe, ← hHe] at hsound
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  exact wf_rawMul hc (wf_rawInv (hsound.1 r hr).1)

end Cover

section Spec

variable {n : ℕ} {p : RawAction × RawAlignOutcome}

/-- §14.1, lines 9–11: **the left cosets of `ker ϕ*` cover the coset of `c`**, once the
fuel reaches the index. -/
theorem adReps_cover (hd : p.1.1.1.length = n) (hle : decGroup n (alignKerGens p) ≤
      decGroup n (alignPairG1 p))
    (hidx : (decGroup n (alignKerGens p)).relIndex (decGroup n (alignPairG1 p)) ≤
      (adFuel p).length + 1)
    {c : RawPerm} (hc : RawPerm.WF n c) :
    decPerm n c • (decGroup n (alignPairG1 p) : Set (Perm (Fin n))) =
      ⋃ σ ∈ (adReps (p, c)).map (decPerm n),
        σ • (decGroup n (alignKerGens p) : Set (Perm (Fin n))) := by
  obtain ⟨A, o⟩ := p
  rw [adReps, List.map_map]
  exact leftReps_cover hd (alignPairG1_wf hd) (alignKerGens_wf hd o) hle hidx hc

/-- §14.1, lines 9–11: **at most `|G* : ker ϕ*|` cosets**. -/
theorem adReps_length_le (hd : p.1.1.1.length = n) (c : RawPerm) :
    (adReps (p, c)).length ≤
      (decGroup n (alignKerGens p)).relIndex (decGroup n (alignPairG1 p)) := by
  obtain ⟨A, o⟩ := p
  exact leftReps_length_le hd (alignPairG1_wf hd) (alignKerGens_wf hd o) c

theorem adReps_wf (hd : p.1.1.1.length = n) {c : RawPerm} (hc : RawPerm.WF n c) :
    RawGens.WF n (adReps (p, c)) := by
  obtain ⟨A, o⟩ := p
  exact leftReps_wf hd (alignPairG1_wf hd) (alignKerGens_wf hd o) hc

/-- The number of listed cosets does not depend on the element `c`. -/
theorem length_adReps (z : (RawAction × RawAlignOutcome) × RawPerm) :
    (adReps z).length = (adRightReps z.1).length := by
  rw [adReps, List.length_map]

end Spec

/-! ## Running time -/

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_alignRSmall : PolyFun alignRSmall := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have h1 := polyFun_alignRColorOf.comp polyFun_alignRHasDom
  have h2 : PolyFun (fun p : RawAction × RawAlignOutcome =>
      rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1))) :=
    (polyFun_alignRMs.pair ((polyFun_alignPairG1.pair (pfst (pfst (pfst i)))).comp
      polyFun_rawMaxOrbit)).comp polyFun_rawVeryLarge
  have h3 : PolyFun (fun p : RawAction × RawAlignOutcome =>
      !rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1))) :=
    (PolyFun.ite h2 (polyFun_const false) (polyFun_const true)).of_eq (fun p => by
      cases rawVeryLarge (alignRMs p, rawMaxOrbit (alignPairG1 p, p.1.1.1)) <;> rfl)
  exact polyFun_and h1 h3

theorem polyFun_adFuelDom : PolyFun adFuelDom := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have ht : PolyFun (fun p : RawAction × RawAlignOutcome =>
      (rawOne p.1.2.1).take (alignRMs p)) :=
    (((pfst (psnd (pfst i))).comp polyFun_rawOne).pair polyFun_alignRMs).comp polyFun_take
  exact (PolyFun.ite polyFun_alignRSmall ht (polyFun_const [])).of_eq (fun p => by
    by_cases h : alignRSmall p = true <;> simp [adFuelDom, h])

theorem quasiFun_adFuel : QuasiFun adFuel := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have hin : PolyFun (fun p : RawAction × RawAlignOutcome =>
      (adFuelDom p, p.1.1.1, adFuelDom p)) :=
    polyFun_adFuelDom.pair ((pfst (pfst (pfst i))).pair polyFun_adFuelDom)
  have hmap : PolyFun (fun l : List (List ℕ × ℕ) => l.map (fun _ => (0 : ℕ))) :=
    PolyFun.map (polyFun_const 0)
  exact ((hin.quasiFun.comp (aggQuasiFun_table 2)).comp_poly
    (polyFun_snd.comp hmap)).of_eq (fun _ => rfl)

theorem quasiFun_adRightReps : QuasiFun adRightReps := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have h1 : PolyFun (fun p : RawAction × RawAlignOutcome => (p.1.1.1, alignPairG1 p)) :=
    (pfst (pfst (pfst i))).pair polyFun_alignPairG1
  exact ((h1.quasiFun.pair (polyFun_alignKerGens.quasiFun.pair quasiFun_adFuel)).comp_poly
    polyFun_rawCosetReps).of_eq (fun _ => rfl)

theorem quasiFun_adReps : QuasiFun adReps := by
  have hf : PolyFun (fun z : RawPerm × RawPerm => rawMul (z.1, rawInv z.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_rawInv)).comp polyFun_rawMul
  exact ((polyFun_snd.quasiFun.pair (polyFun_fst.quasiFun.comp quasiFun_adRightReps)).comp_poly
    (PolyFun.mapParam (α := RawPerm) (β := RawPerm) (γ := RawPerm)
      (f := fun z : RawPerm × RawPerm => rawMul (z.1, rawInv z.2)) hf)).of_eq (fun _ => rfl)

end Algo
