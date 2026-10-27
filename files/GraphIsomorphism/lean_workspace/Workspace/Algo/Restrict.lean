/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: restricting an instance to an invariant window (§11.1,
Observation 11.1.11).
-/
import Workspace.Algo.Stabilizer
import Workspace.Luks.Framework

/-!
# Restricting an instance to an invariant window

Observation 11.1.11 of §11.1 says that for a `G`-invariant window `Δ ⊆ Ω` the window
isomorphism problem on `Δ` only depends on the restricted group `G^Δ` and on the restricted
strings `x^Δ`, `y^Δ`.  A recursive call must therefore hand the child an instance **on the
window**, and `Algo.Round.Cost` bounds the size of a child instance by a polynomial of the
child's ground set, so the window has to be relabelled onto `{0, …, |Δ|−1}`.

Here the window arrives as a repetition-free list `Δ` of points below `n`, and the label of a
point of the window is its **position in that list**.  Two routines do the relabelling:

* `Algo.rawRestrictPerm` — one permutation restricted to the window, in window labels;
  `Algo.rawRestrictGens` maps it over a generator list;
* `Algo.rawRestrictStr` — the string `x|_Δ`, in window labels.

The mathematical side is `Babai.restrictHom` of `Workspace/Luks/Framework.lean` (Notation
2.2.1), transported along the bijection `Algo.winEquiv : Fin Δ.length ≃ ↥(Algo.winSet n Δ)`
that the list provides.  The composite is `Algo.winRestrictHom`, and the two specifications
are `Algo.rawRestrictPerm_spec` and `Algo.decGroup_rawRestrictGens`.

Invariance of the window is a hypothesis of every specification; it is decided by
`Algo.rawIsInvariant` of `Workspace/Algo/Orbits.lean`.

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)

variable {n : ℕ}

/-! ## The window as a set of points, and its labelling

`Δ` is a repetition-free list of points below `n`.  `Algo.winSet n Δ` is the set of points it
lists, and `Algo.winEquiv` is the labelling: the label of a point is its position in `Δ`. -/

/-- **The window as a subset of the domain**: the points of `Fin n` that `Δ` lists. -/
def winSet (n : ℕ) (Δ : List ℕ) : Set (Fin n) := {x : Fin n | (x : ℕ) ∈ Δ}

theorem mem_winSet {Δ : List ℕ} {x : Fin n} : x ∈ winSet n Δ ↔ (x : ℕ) ∈ Δ := Iff.rfl

/-- **The point of the window with the label `k`**: the `k`-th entry of `Δ`. -/
def winPt (n : ℕ) (Δ : List ℕ) (hlt : ∀ u ∈ Δ, u < n) (k : Fin Δ.length) : ↥(winSet n Δ) :=
  ⟨⟨Δ[(k : ℕ)], hlt _ (List.getElem_mem k.isLt)⟩, List.getElem_mem k.isLt⟩

theorem winPt_val (Δ : List ℕ) (hlt : ∀ u ∈ Δ, u < n) (k : Fin Δ.length) :
    (((winPt n Δ hlt k : ↥(winSet n Δ)) : Fin n) : ℕ) = Δ.getD (k : ℕ) 0 := by
  rw [List.getD_eq_getElem _ _ k.isLt]
  rfl

theorem winPt_bijective (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) :
    Function.Bijective (winPt n Δ hlt) := by
  constructor
  · intro a b hab
    have : Δ[(a : ℕ)] = Δ[(b : ℕ)] := congrArg (fun z => ((z : ↥(winSet n Δ)) : Fin n).1) hab
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)
  · rintro ⟨y, hy⟩
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem (mem_winSet.1 hy)
    exact ⟨⟨j, hj⟩, Subtype.ext (Fin.ext (by simpa using hjy))⟩

/-- **The labelling of the window.**  The label of a point of the window is its position in
the list `Δ`. -/
noncomputable def winEquiv (n : ℕ) (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) :
    Fin Δ.length ≃ ↥(winSet n Δ) :=
  Equiv.ofBijective _ (winPt_bijective Δ hnd hlt)

theorem winEquiv_apply (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (k : Fin Δ.length) : winEquiv n Δ hnd hlt k = winPt n Δ hlt k := rfl

/-- **The point of the window with a given label**, read in the domain. -/
theorem winEquiv_coe (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n) {k : ℕ}
    (hk : k < Δ.length) :
    ((winEquiv n Δ hnd hlt ⟨k, hk⟩ : ↥(winSet n Δ)) : Fin n)
      = ⟨Δ[k], hlt _ (List.getElem_mem hk)⟩ := by
  apply Fin.ext
  rw [winEquiv_apply, winPt_val Δ hlt ⟨k, hk⟩, List.getD_eq_getElem _ _ hk]

/-- **The label of a point of the window names its position in `Δ`.** -/
theorem winEquiv_symm_val (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (u : ↥(winSet n Δ)) :
    Δ.getD (((winEquiv n Δ hnd hlt).symm u : Fin Δ.length) : ℕ) 0 = ((u : Fin n) : ℕ) := by
  have h : winEquiv n Δ hnd hlt ((winEquiv n Δ hnd hlt).symm u) = u :=
    Equiv.apply_symm_apply _ _
  rw [← winPt_val Δ hlt ((winEquiv n Δ hnd hlt).symm u)]
  exact congrArg (fun z : ↥(winSet n Δ) => ((z : Fin n) : ℕ)) h

/-! ## The restriction homomorphism, in window labels

`Babai.restrictHom G Δ h : G →* S(Δ)` is Notation 2.2.1.  Composing it with the labelling
gives a homomorphism into `S(Fin |Δ|)`, which is what the routines compute. -/

/-- **The restriction homomorphism of Notation 2.2.1, read in window labels.** -/
noncomputable def winRestrictHom (n : ℕ) (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (G : Subgroup (Perm (Fin n))) (hinv : Babai.IsInvariant G (winSet n Δ)) :
    G →* Perm (Fin Δ.length) :=
  ((winEquiv n Δ hnd hlt).symm.permCongrHom : Perm ↥(winSet n Δ) ≃* Perm (Fin Δ.length)
    ).toMonoidHom.comp (Babai.restrictHom G (winSet n Δ) hinv)

theorem winRestrictHom_apply (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    (g : G) (k : Fin Δ.length) :
    winRestrictHom n Δ hnd hlt G hinv g k
      = (winEquiv n Δ hnd hlt).symm
          (Babai.restrictHom G (winSet n Δ) hinv g (winEquiv n Δ hnd hlt k)) := rfl

/-- **The image of `Algo.winRestrictHom` is the paper's `G^Δ`**, in window labels: it is
`Babai.restrictTo` of Notation 2.2.1, carried along the labelling. -/
theorem range_winRestrictHom (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (G : Subgroup (Perm (Fin n))) (hinv : Babai.IsInvariant G (winSet n Δ)) :
    (winRestrictHom n Δ hnd hlt G hinv).range =
      (Babai.restrictTo G (winSet n Δ) hinv).map
        ((winEquiv n Δ hnd hlt).symm.permCongrHom :
          Perm ↥(winSet n Δ) ≃* Perm (Fin Δ.length)).toMonoidHom := by
  rw [winRestrictHom, MonoidHom.range_comp, Babai.restrictTo]

/-- **The value of `Algo.winRestrictHom` at a label**, read back in the domain: the point of
`Δ` with the label `(g|_Δ)(k)` is the image under `g` of the point of `Δ` with the label `k`. -/
theorem winRestrictHom_val (Δ : List ℕ) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    (g : G) (k : Fin Δ.length) :
    Δ.getD ((winRestrictHom n Δ hnd hlt G hinv g k : Fin Δ.length) : ℕ) 0
      = ((g : Perm (Fin n)) ((winEquiv n Δ hnd hlt k : ↥(winSet n Δ)) : Fin n) : ℕ) := by
  rw [winRestrictHom_apply, winEquiv_symm_val]
  rfl

/-! ## The routines -/

/-- **One permutation restricted to the window, in window labels.**  Entry `k` is the position
in `Δ` of the image of `Δ[k]`. -/
def rawRestrictPerm (p : List ℕ × RawPerm) : RawPerm :=
  p.1.map (fun u => rawInvLookup (p.1.zipIdx, rawApply (p.2, u)))

@[simp] theorem length_rawRestrictPerm (Δ : List ℕ) (g : RawPerm) :
    (rawRestrictPerm (Δ, g)).length = Δ.length := by
  simp [rawRestrictPerm]

/-- **A generator list restricted to the window.**  `p.1` is the pair of the domain witness and
the generator list, `p.2` is the window. -/
def rawRestrictGens (p : (List ℕ × List RawPerm) × List ℕ) : List RawPerm :=
  p.1.2.map (fun g => rawRestrictPerm (p.2, g))

/-- **A string restricted to the window**, in window labels. -/
def rawRestrictStr (p : RawStr × List ℕ) : RawStr :=
  p.2.map (fun u => rawGet (p.1, u))

@[simp] theorem length_rawRestrictStr (x : RawStr) (Δ : List ℕ) :
    (rawRestrictStr (x, Δ)).length = Δ.length := by
  simp [rawRestrictStr]

/-! ## The specifications -/

/-- The position of an entry of a repetition-free list is found by the lookup table. -/
theorem rawInvLookup_getElem {Δ : List ℕ} (hnd : Δ.Nodup) {j : ℕ} (hj : j < Δ.length) :
    rawInvLookup (Δ.zipIdx, Δ[j]) = j := by
  have h := lookup_zipIdx_getElem Δ hnd 0 j Δ[j] hj rfl
  rw [rawInvLookup]
  show (List.lookup Δ[j] (Δ.zipIdx 0)).getD 0 = j
  rw [h]
  rfl

/-- **The routine restricts a permutation to the window.**  Paper: the restriction
`G → S(Δ)` of Notation 2.2.1, used in Observation 11.1.11 (§11.1). -/
theorem rawRestrictPerm_spec {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    {g : Perm (Fin n)} (hg : g ∈ G) :
    rawRestrictPerm (Δ, encPerm n g)
      = encPerm Δ.length (winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkΔ : k < Δ.length := by simpa using hk
    set φ := winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ with hφ
    set j : ℕ := (φ ⟨k, hkΔ⟩ : ℕ) with hj
    have hjlt : j < Δ.length := (φ ⟨k, hkΔ⟩).isLt
    -- the point of `Δ` with the label `k`
    have hval : Δ[j]'hjlt = (g ⟨Δ[k]'hkΔ, hlt _ (List.getElem_mem hkΔ)⟩ : ℕ) := by
      have := winRestrictHom_val Δ hnd hlt hinv ⟨g, hg⟩ ⟨k, hkΔ⟩
      rw [List.getD_eq_getElem _ _ hjlt] at this
      rw [this, winEquiv_coe Δ hnd hlt hkΔ]
    rw [getElem_encPerm Δ.length φ k hkΔ]
    show (Δ.map (fun u => rawInvLookup (Δ.zipIdx, rawApply (encPerm n g, u))))[k]'hk = j
    rw [List.getElem_map]
    have happ : rawApply (encPerm n g, Δ[k]'hkΔ)
        = (g ⟨Δ[k]'hkΔ, hlt _ (List.getElem_mem hkΔ)⟩ : ℕ) :=
      rawApply_encPerm n g (hlt _ (List.getElem_mem hkΔ))
    rw [happ, ← hval, rawInvLookup_getElem hnd hjlt]

/-- **The restricted generators are well formed** for the degree `|Δ|`. -/
theorem wf_rawRestrictPerm {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    {G : Subgroup (Perm (Fin n))} (hinv : Babai.IsInvariant G (winSet n Δ))
    {g : Perm (Fin n)} (hg : g ∈ G) :
    RawPerm.WF Δ.length (rawRestrictPerm (Δ, encPerm n g)) := by
  rw [rawRestrictPerm_spec hnd hlt hinv hg]
  exact wf_encPerm _ _

/-- The range of a homomorphism out of a group given by generators is generated by the values
at the generators. -/
theorem range_eq_closure_gens {N : Type*} [Group N] {S : Set (Perm (Fin n))}
    (θ : Subgroup.closure S →* N) :
    θ.range = Subgroup.closure
      {y | ∃ (g : Perm (Fin n)) (hg : g ∈ Subgroup.closure S), g ∈ S ∧ y = θ ⟨g, hg⟩} := by
  apply le_antisymm
  · rintro y ⟨⟨g, hg⟩, rfl⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure ⟨x, _, hx, rfl⟩
    | one =>
        have h1 : (⟨1, Subgroup.one_mem _⟩ : Subgroup.closure S) = 1 := rfl
        rw [h1, map_one]
        exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
        have h1 : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : Subgroup.closure S)
            = (⟨x, hx⟩ : Subgroup.closure S) * ⟨y, hy⟩ := rfl
        rw [h1, map_mul]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
        have h1 : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Subgroup.closure S)
            = (⟨x, hx⟩ : Subgroup.closure S)⁻¹ := rfl
        rw [h1, map_inv]
        exact Subgroup.inv_mem _ ihx
  · rw [Subgroup.closure_le]
    rintro y ⟨g, hg, -, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- **The routine returns a generating list of `G^Δ`**, in window labels.  Paper: Notation
2.2.1 and Observation 11.1.11 (§11.1). -/
theorem decGroup_rawRestrictGens {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (dom : List ℕ) (gens : List (Perm (Fin n)))
    (hinv : Babai.IsInvariant (genGroup gens) (winSet n Δ)) :
    decGroup Δ.length (rawRestrictGens ((dom, gens.map (encPerm n)), Δ))
      = (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range := by
  have hrange : (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range
      = Subgroup.closure {y | ∃ (g : Perm (Fin n)) (hg : g ∈ genGroup gens),
          g ∈ gens ∧ y = winRestrictHom n Δ hnd hlt (genGroup gens) hinv ⟨g, hg⟩} :=
    range_eq_closure_gens (S := {g : Perm (Fin n) | g ∈ gens}) _
  rw [hrange]
  conv_lhs => rw [decGroup, genGroup]
  congr 1
  ext y
  constructor
  · intro hy
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
    rw [rawRestrictGens] at hr
    obtain ⟨gr, hgr, rfl⟩ := List.mem_map.1 hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hgr
    have hmem : g ∈ Subgroup.closure {g : Perm (Fin n) | g ∈ gens} :=
      Subgroup.subset_closure hg
    refine ⟨g, hmem, hg, ?_⟩
    rw [rawRestrictPerm_spec hnd hlt hinv hmem, decPerm_encPerm]
  · rintro ⟨g, hg, hgens, rfl⟩
    refine List.mem_map.2 ⟨rawRestrictPerm (Δ, encPerm n g), ?_, ?_⟩
    · exact List.mem_map.2 ⟨encPerm n g, List.mem_map.2 ⟨g, hgens, rfl⟩, rfl⟩
    · rw [rawRestrictPerm_spec hnd hlt hinv hg, decPerm_encPerm]

/-- **The routine restricts a string to the window.**  Paper: `x^Δ` of Observation 11.1.11
(§11.1), in window labels. -/
theorem rawRestrictStr_spec {s : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (x : Fin n → Fin s) :
    rawRestrictStr (encStr x, Δ)
      = encStr (fun k : Fin Δ.length =>
          x (((winEquiv n Δ hnd hlt k : ↥(winSet n Δ)) : Fin n))) := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have hkΔ : k < Δ.length := by simpa using hk
    show (Δ.map (fun u => rawGet (encStr x, u)))[k]'hk = _
    rw [List.getElem_map, rawGet_encStr x (hlt _ (List.getElem_mem hkΔ))]
    have hrhs : (encStr (fun i : Fin Δ.length =>
          x ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n)))[k]'hk'
        = (x ((winEquiv n Δ hnd hlt ⟨k, hkΔ⟩ : ↥(winSet n Δ)) : Fin n) : ℕ) := by
      simp [encStr]
    rw [hrhs, winEquiv_coe Δ hnd hlt hkΔ]

/-! ## The running time -/

theorem polyFun_rawRestrictPerm : PolyFun rawRestrictPerm := by
  have hf : PolyFun (fun z : (List (ℕ × ℕ) × RawPerm) × ℕ =>
      rawInvLookup (z.1.1, rawApply (z.1.2, z.2))) :=
    ((polyFun_fst.comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawApply)).comp
      polyFun_rawInvLookup
  have hin : PolyFun (fun p : List ℕ × RawPerm =>
      ((((p.1.zipIdx, p.2) : List (ℕ × ℕ) × RawPerm), p.1) :
        (List (ℕ × ℕ) × RawPerm) × List ℕ)) :=
    ((polyFun_fst.comp polyFun_zipIdx).pair polyFun_snd).pair polyFun_fst
  exact (hin.comp (PolyFun.mapParam hf)).of_eq (fun _ => rfl)

theorem polyFun_rawRestrictGens : PolyFun rawRestrictGens :=
  ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.mapParam polyFun_rawRestrictPerm)).of_eq (fun _ => rfl)

theorem polyFun_rawRestrictStr : PolyFun rawRestrictStr :=
  (PolyFun.mapParam polyFun_rawGet).of_eq (fun _ => rfl)

end Algo
