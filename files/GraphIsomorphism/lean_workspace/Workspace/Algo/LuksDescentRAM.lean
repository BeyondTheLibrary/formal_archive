/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Proposition 11.1.6 (Descent), Proposition 11.1.7 (Chain Rule) and the
strong descent of Eq. (64) on the RAM.
-/
import Workspace.Algo.LuksRAM
import Workspace.Algo.GenTransversal

/-!
# Descent, the Chain Rule and strong descent on the RAM (§11.1)

`Workspace/Algo/LuksRAM.lean` gives two program transformers: the Chain Rule over a list of
windows (`Algo.exists_wlProg`) and the descent over a given list of coset representatives
(`Algo.exists_dsProg`).  This file states the three reductions of §11.1 that the paper
phrases for an *arbitrary* subgroup, and proves them on the RAM:

* **Proposition 11.1.6 (Descent).**  For `H ≤ G`, given by generators, the program computes
  the index `|G : H|` (`Algo.rawOrder`) and hands on exactly the `|G : H|` instances
  `Iso^Δ_{Hσ}(x, y) = Iso^Δ_H(x, y^{σ⁻¹})σ`, computing the `j`-th representative `σ` when the
  `j`-th instance is made (`Algo.trRep`, `Workspace/Algo/GenTransversal.lean`)
  (`Algo.proposition_11_1_6_ram_spec`, `Algo.proposition_11_1_6_ram`).
* **Proposition 11.1.7 (Chain Rule).**  Two `G`-invariant windows, processed in succession:
  at most two calls (`Algo.proposition_11_1_7_ram`).
* **Eq. (64) (strong descent).**  Descent to `N` followed by the Chain Rule on the orbits of
  `N` in the window: `|G : N| · m` calls, `m` the number of `N`-orbits, each on one orbit;
  when `G` is transitive on the window and `N ◁ G`, all orbits have `|Δ|/m` points
  (`Algo.eq_64_ram_spec`, `Algo.eq_64_ram`).

## The overhead

The paper states no cost for Prop. 11.1.6 and none for Eq. (64): the recurrence
`T(n) ≤ |G:N| m T(n/m)` has no additive term.  On the RAM a reduction has an additive cost, if
only to write its calls.  The one proved here is polynomial per instance handed on:
`(|G : H| + 2) · poly(size)`, the form Theorem 11.1.9 states.  The `j`-th representative is
computed from the generators and `j` alone, with `j` a machine natural, by walking down the
point stabilizer chain of `G` (`Algo.trRep`).  The calls themselves are charged with a constant
factor (`1000`, `10⁶`), for saving and restoring the state around each call.  See the
the corrected paper "Prop. 11.1.6 and Eq. (64): no additive cost".

No axiom and no `sorry`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## Descent to an arbitrary subgroup: the data -/

section BD

variable {P : Type} [Enc P] [Inhabited P]

/-- **A descent instance** (Prop. 11.1.6): an instance with a window and a payload, and the
generators of the subgroup `H`. -/
abbrev RawBD (P : Type) := (RawWinSI × P) × RawGens

/-- **The index `|G : H|`**, from the two orders. -/
def bdIdx (I : RawBD P) : ℕ :=
  rawOrder (I.1.1.2.2.2.1, I.1.1.2.1) / rawOrder (I.1.1.2.2.2.1, I.2)

/-- The parameter of the representatives: the domain witness, the generators of `G`, and the
generators of `H`. -/
abbrev TrRp := (List ℕ × RawGens) × RawGens

/-- **The prepared descent**: the `|G : H|` representatives are `Algo.trRep` of the parameter
and the index, computed one at a time (`Workspace/Algo/GenTransversal.lean`). -/
def bdDS (I : RawBD P) : RawDS P TrRp :=
  (I.1, (I.2, (((I.1.1.2.2.2.1, I.1.1.2.1), I.2), bdIdx I)))

/-- **Well-formed descent instances**: a well-formed instance and a subgroup `H ≤ G`
(the hypothesis of Prop. 11.1.6). -/
structure BDWF (n : ℕ) (I : RawBD P) : Prop where
  win : WinWF n I.1.1
  wfH : RawGens.WF n I.2
  le : decGroup n I.2 ≤ decGroup n I.1.1.2.1

variable {I : RawBD P}

theorem rawOrder_raw {dom : List ℕ} (hdom : dom.length = n) {gs : RawGens}
    (hgs : RawGens.WF n gs) : rawOrder (dom, gs) = Nat.card (decGroup n gs) := by
  have h := rawOrder_spec dom hdom (gs.map (decPerm n))
  rw [map_encPerm_decPerm hgs] at h
  exact h

/-- **The routine computes the index** `|G : H|`. -/
theorem bdIdx_eq (hI : BDWF n I) :
    bdIdx I = (decGroup n I.2).relIndex (decGroup n I.1.1.2.1) := by
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  rw [bdIdx, rawOrder_raw hx hI.win.2.2.2.2.1, rawOrder_raw hx hI.wfH,
    ← Babai.relIndex_mul_card_of_le hI.le]
  exact Nat.mul_div_cancel _ Nat.card_pos

theorem bdDS_idx (_hI : BDWF n I) : (bdDS I).2.2.2 = bdIdx I := rfl

/-- **The representatives cover `G`**, and the prepared descent is well formed
(`Algo.trRep_cover`). -/
theorem bdDS_wf (hI : BDWF n I) : DSWF trRep n (bdDS I) := by
  have hx : I.1.1.2.2.2.1.length = n := hI.win.1
  have hgG := hI.win.2.2.2.2.1
  set gG := I.1.1.2.1.map (decPerm n) with hgGdef
  set gH := I.2.map (decPerm n) with hgHdef
  have eG : gG.map (encPerm n) = I.1.1.2.1 := map_encPerm_decPerm hgG
  have eH : gH.map (encPerm n) = I.2 := map_encPerm_decPerm hI.wfH
  have hdG : decGroup n I.1.1.2.1 = genGroup gG := rfl
  have hdH : decGroup n I.2 = genGroup gH := rfl
  refine ⟨hI.win, hI.le, ?_⟩
  show (decGroup n I.1.1.2.1 : Set (Perm (Fin n)))
    = ⋃ j ∈ List.range (bdIdx I), decPerm n (trRep (((I.1.1.2.2.2.1, I.1.1.2.1), I.2), j)) •
      (decGroup n I.2 : Set (Perm (Fin n)))
  have hc := trRep_cover hx gG gH (by rw [← hdG, ← hdH]; exact hI.le)
  rw [eG, eH, ← hdG, ← hdH, ← bdIdx_eq hI] at hc
  exact hc

end BD

/-! ## Descent to an arbitrary subgroup on the RAM -/

section BDRAM

variable {P : Type} [Enc P] [Inhabited P]

theorem polyFun_bdIdx : PolyFun (bdIdx (P := P)) := by
  have hx : PolyFun (fun I : RawBD P => I.1.1.2.2.2.1) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst)
  have hG : PolyFun (fun I : RawBD P => I.1.1.2.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact (((hx.pair hG).comp polyFun_rawOrder).div
    ((hx.pair polyFun_snd).comp polyFun_rawOrder)).of_eq (fun _ => rfl)

theorem polyFun_bdDS : PolyFun (bdDS (P := P)) := by
  have hx : PolyFun (fun I : RawBD P => I.1.1.2.2.2.1) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst)
  have hG : PolyFun (fun I : RawBD P => I.1.1.2.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact (polyFun_fst.pair (polyFun_snd.pair (((hx.pair hG).pair polyFun_snd).pair
    polyFun_bdIdx))).of_eq (fun _ => rfl)

set_option maxHeartbeats 4000000 in
/-- **Descent to an arbitrary subgroup on the RAM** (Prop. 11.1.6).  One program transformer
`F`: for every program `Q` that answers the `|G : H|` calls `(Δ, H, σr_j, x, y)` with
polynomially small answers, `F Q` computes the index and runs the descent (`Algo.dsOut`,
correct by `Algo.ds_spec` and `Algo.bdDS_wf`), computing the `j`-th representative when the
`j`-th call is made (`Algo.trRep`), within `1000 · ∑_j τ(call j) + (|G : H| + 2) · poly(size)`
steps: polynomial per instance. -/
theorem exists_bdProg (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI × P → RawCoset) (τ : RawWinSI × P → ℕ) (I : RawBD P),
        BDWF n I →
        (∀ j < bdIdx I, RunsOn 16 Q (dsCall trRep (bdDS I) j)
            (ansQ (dsCall trRep (bdDS I) j)) (τ (dsCall trRep (bdDS I) j)) ∧
          Enc.size (ansQ (dsCall trRep (bdDS I) j))
            ≤ S (Enc.size (dsCall trRep (bdDS I) j))) →
        RunsOn 16 (F Q) I (dsOut trRep ansQ (bdDS I))
          (1000 * (((List.range (bdIdx I)).map (dsCall trRep (bdDS I))).map τ).sum
            + (bdIdx I + 2) * pw c d (Enc.size I)) := by
  obtain ⟨FB, cB, dB, hFB⟩ := exists_dsProg (P := P) polyFun_trRep S hS
  obtain ⟨P2, c2, d2, hP2, hP2s⟩ := polyFun_witness (polyFun_bdDS (P := P))
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = pw c2 d2 t + pw cB dB (pw c2 d2 t) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => pw c2 d2 t + pw cB dB (pw c2 d2 t) from funext hGd]
    exact (polyBound_pw c2 d2).add ((polyBound_pw cB dB).comp (polyBound_pw c2 d2))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => RAM.seq P2 (FB Q), c, d, fun Q hQwf => ?_⟩
  obtain ⟨hBwf, hBrun⟩ := hFB Q hQwf
  refine ⟨wf_seq (CleanComputeAt.wf' hP2) hBwf, ?_⟩
  intro n ansQ τ I hI hQ
  have r := (hP2.runsOn I).seq (hBrun n ansQ τ (bdDS I) (bdDS_wf hI) hQ)
  refine r.mono ?_
  have hsDS : Enc.size (bdDS I) ≤ pw c2 d2 (Enc.size I) := hP2s I
  have t4 : pw cB dB (Enc.size (bdDS I)) ≤ pw cB dB (pw c2 d2 (Enc.size I)) :=
    pw_mono cB dB hsDS
  have t5 := hcd (Enc.size I)
  rw [hGd] at t5
  have e5 : c * (Enc.size I + 1) ^ d = pw c d (Enc.size I) := rfl
  have e6 : pw c2 d2 (Enc.size I) = c2 * (Enc.size I + 1) ^ d2 := rfl
  have e7 : (bdDS I).2.2.2 = bdIdx I := rfl
  rw [e7]
  have t6 : (bdIdx I + 2) * pw cB dB (Enc.size (bdDS I))
      ≤ (bdIdx I + 2) * pw cB dB (pw c2 d2 (Enc.size I)) := Nat.mul_le_mul_left _ t4
  have t7 : c2 * (Enc.size I + 1) ^ d2 + (bdIdx I + 2) * pw cB dB (pw c2 d2 (Enc.size I))
      ≤ (bdIdx I + 2) * pw c d (Enc.size I) := by
    rw [← e6]
    have : pw c2 d2 (Enc.size I) + (bdIdx I + 2) * pw cB dB (pw c2 d2 (Enc.size I))
        ≤ (bdIdx I + 2) * (pw c2 d2 (Enc.size I) + pw cB dB (pw c2 d2 (Enc.size I))) := by
      nlinarith
    have h2 : (bdIdx I + 2) * (pw c2 d2 (Enc.size I) + pw cB dB (pw c2 d2 (Enc.size I)))
        ≤ (bdIdx I + 2) * pw c d (Enc.size I) := Nat.mul_le_mul_left _ (by rw [← e5]; exact t5)
    omega
  generalize (((List.range (bdIdx I)).map (dsCall trRep (bdDS I))).map τ).sum = S1
  generalize (bdIdx I + 2) * pw cB dB (Enc.size (bdDS I)) = V at t6 ⊢
  omega


end BDRAM

/-! ## Proposition 11.1.6 (Descent) -/

/-- An instance of Prop. 11.1.6: an instance `(Δ, G, σ, x, y)` and generators of `H`. -/
abbrev RawDescIn := RawWinSI × RawGens

/-- The descent instance, with an empty payload. -/
def descBD (I : RawDescIn) : RawBD Bool := ((I.1, false), I.2)

/-- **The hypothesis of Prop. 11.1.6**: a well-formed instance and a subgroup `H ≤ G`. -/
def DescInWF (n : ℕ) (I : RawDescIn) : Prop :=
  WinWF n I.1 ∧ RawGens.WF n I.2 ∧ decGroup n I.2 ≤ decGroup n I.1.2.1

theorem DescInWF.bd {I : RawDescIn} (hI : DescInWF n I) : BDWF n (descBD I) :=
  ⟨hI.1, hI.2.1, hI.2.2⟩

/-- The number of instances: the index `|G : H|` as the routine computes it. -/
def descIdx (I : RawDescIn) : ℕ := bdIdx (descBD I)

/-- The `j`-th instance handed on: `(Δ, H, σ r_j⁻¹, x, y)`. -/
def descCall (I : RawDescIn) (j : ℕ) : RawWinSI := (dsCall trRep (bdDS (descBD I)) j).1

/-- The instances handed on, in order. -/
def descCalls (I : RawDescIn) : List RawWinSI := (List.range (descIdx I)).map (descCall I)

/-- The output of the descent, with the calls answered by `ansQ`. -/
def descOut (ansQ : RawWinSI → RawCoset) (I : RawDescIn) : RawCoset :=
  dsOut trRep (fun Wb : RawWinSI × Bool => ansQ Wb.1) (bdDS (descBD I))

theorem biUnion_list_map {Γ β δ : Type*} (L : List β) (g : β → Γ) (F : Γ → Set δ) :
    (⋃ σ ∈ L.map g, F σ) = ⋃ j ∈ L, F (g j) := by
  ext u
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨σ, ⟨j, hj, rfl⟩, hu⟩; exact ⟨j, hj, hu⟩
  · rintro ⟨j, hj, hu⟩; exact ⟨g j, ⟨j, hj, rfl⟩, hu⟩

/-- **Proposition 11.1.6 (Descent), §11.1, what the RAM reduction computes.**  *"Let `H ≤ G`.
Then finding `Iso^Δ_G(x, y)` reduces to `|G : H|` instances of finding `Iso^Δ_H(x, y^σ)` for
various `σ ∈ G`."*  For a well-formed instance `(Δ, G, σ, x, y)` (the coset form of
Remark 11.1.4) and `H ≤ G`, if `ansQ` answers every well-formed instance, then:

* the reduction returns `Iso^Δ_{σG}(x, y)`;
* the number of instances it hands on is `|G : H|`;
* each instance is well formed, has the window `Δ`, the group `H`, and the strings `x, y`
  (so it is `Iso^Δ_{ρH}(x, y) = Iso^Δ_H(x, y^{ρ⁻¹})ρ` by the shift identity, Eq. (59));
* their candidate cosets `ρ_j H` cover `σG`: this is Eq. (62).

The RAM running time is `Algo.proposition_11_1_6_ram`. -/
theorem proposition_11_1_6_ram_spec {ansQ : RawWinSI → RawCoset} {I : RawDescIn}
    (hI : DescInWF n I)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    decCoset n (descOut ansQ I) = (decWinSI n I.1).answer ∧
      descIdx I = (decGroup n I.2).relIndex (decGroup n I.1.2.1) ∧
      (descCalls I).length = descIdx I ∧
      (∀ W ∈ descCalls I, WinWF n W ∧ W.1 = I.1.1 ∧ decGroup n W.2.1 = decGroup n I.2 ∧
        W.2.2.2 = I.1.2.2.2) ∧
      (⋃ W ∈ descCalls I, (decWinSI n W).K) = (decWinSI n I.1).K := by
  have hbd := hI.bd
  have hDS := bdDS_wf hbd
  have hidx := bdDS_idx hbd
  refine ⟨?_, bdIdx_eq hbd, by simp [descCalls], ?_, ?_⟩
  · refine (ds_spec hDS (fun j _ => hQ _ (dsCall_wf hDS j))).1
  · intro W hW
    rw [descCalls, List.mem_map] at hW
    obtain ⟨j, -, rfl⟩ := hW
    exact ⟨dsCall_wf hDS j, rfl, decGroup_dsCall hDS j, rfl⟩
  · have hK : ∀ j, (decWinSI n (descCall I j)).K
        = (decPerm n I.1.2.2.1 * decPerm n (trRep ((bdDS (descBD I)).2.2.1, j))) •
          (decGroup n I.2 : Set (Perm (Fin n))) := by
      intro j
      rw [descCall, decWinSI_dsCall hDS j]
      rfl
    have hKI : (decWinSI n I.1).K
        = decPerm n I.1.2.2.1 • (decGroup n I.1.2.1 : Set (Perm (Fin n))) := by
      rw [decWinSI, decCoset_some]
    rw [descCalls, biUnion_list_map, hKI]
    simp_rw [hK]
    have hc : (decGroup n I.1.2.1 : Set (Perm (Fin n))) = _ := hDS.cover
    rw [hc, smul_biUnion_list, biUnion_list_map]
    show _ = ⋃ j ∈ List.range (bdDS (descBD I)).2.2.2, _
    rw [hidx]
    rfl

theorem polyFun_descBD : PolyFun descBD :=
  ((polyFun_fst.pair (polyFun_const false)).pair polyFun_snd).of_eq (fun _ => rfl)

theorem size_false : Enc.size false = 2 := by
  show listSize [0] = 2
  simp [listSize]

set_option maxHeartbeats 4000000 in
/-- **Proposition 11.1.6 (Descent), §11.1, on the RAM.**  *"Let `H ≤ G`.  Then finding
`Iso^Δ_G(x, y)` reduces to `|G : H|` instances of finding `Iso^Δ_H(x, y^σ)` for various
`σ ∈ G`."*  One program transformer `F`: for every program `Q` that runs on the well-formed
instances with polynomially small answers, `F Q` returns `Iso^Δ_{σG}(x, y)`
(`Algo.proposition_11_1_6_ram_spec`), makes exactly the `|G : H|` calls `Algo.descCalls` (each
with the group `H`), and runs within `1000 · ∑_{W ∈ calls} τ(W) + (|G : H| + 2) · poly(size)`
steps.  The overhead is polynomial per instance handed on, as for Theorem 11.1.9: the `j`-th
representative is computed when the `j`-th call is made (`Algo.trRep`), with the index in
binary. -/
theorem proposition_11_1_6_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawDescIn),
        DescInWF n I →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (F Q) I (descOut ansQ I)
          (1000 * ((descCalls I).map τ).sum + (descIdx I + 2) * pw c d (Enc.size I)) := by
  obtain ⟨Pf, cf, df, hPf, -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun Wb : RawWinSI × Bool => Wb.1))
  obtain ⟨cS, dS, hSb⟩ := hS
  obtain ⟨FB, cB, dB, hFB⟩ := exists_bdProg (P := Bool) (pw cS dS) (polyBound_pw cS dS)
  obtain ⟨Pc, cc, dc, hPc, -⟩ := polyFun_witness polyFun_descBD
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = pw cc dc t + pw cB dB (6 * t + 12)
      + 1000 * pw cf df (2 * chainBound t + 4) := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => pw cc dc t + pw cB dB (6 * t + 12)
      + 1000 * pw cf df (2 * chainBound t + 4) from funext hGd]
    exact ((polyBound_pw cc dc).add ((polyBound_pw cB dB).comp
      (((polyBound_const 6).mul polyBound_id).add (polyBound_const 12)))).add
      ((polyBound_const 1000).mul ((polyBound_pw cf df).comp
        (((polyBound_const 2).mul polyBound_chainBound).add (polyBound_const 4))))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => RAM.seq Pc (FB (RAM.seq Pf Q)), c, d, fun Q hQwf => ?_⟩
  have hQ'wf : Wf (RAM.seq Pf Q) := wf_seq (CleanComputeAt.wf' hPf) hQwf
  obtain ⟨hBwf, hBrun⟩ := hFB (RAM.seq Pf Q) hQ'wf
  refine ⟨wf_seq (CleanComputeAt.wf' hPc) hBwf, ?_⟩
  intro n ansQ τ I hI hQ
  have hbd := hI.bd
  have hDS := bdDS_wf hbd
  let τ' : RawWinSI × Bool → ℕ := fun Wb => cf * (Enc.size Wb + 1) ^ df + τ Wb.1
  have hsm : Enc.size I.1.2.2.2 ≤ Enc.size I :=
    le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (size_fst_le' I)))
  have hcallSize : ∀ j, Enc.size (dsCall trRep (bdDS (descBD I)) j)
      ≤ 2 * chainBound (Enc.size I) + 4 := by
    intro j
    have h1 : Enc.size (dsCall trRep (bdDS (descBD I)) j).1
        ≤ chainBound (Enc.size (dsCall trRep (bdDS (descBD I)) j).1.2.2.2) :=
      size_winSI_le (dsCall_wf hDS j)
    have h1' : (dsCall trRep (bdDS (descBD I)) j).1.2.2.2 = I.1.2.2.2 := rfl
    rw [h1'] at h1
    have h1'' : chainBound (Enc.size I.1.2.2.2) ≤ chainBound (Enc.size I) := mono_chainBound hsm
    have h2 := size_pair_le' (dsCall trRep (bdDS (descBD I)) j)
    have h3 : (dsCall trRep (bdDS (descBD I)) j).2 = false := rfl
    rw [h3, size_false] at h2
    omega
  have r := (hPc.runsOn I).seq (hBrun n (fun Wb => ansQ Wb.1) τ' (descBD I) hbd (fun j _ => by
    have hW := dsCall_wf hDS j
    obtain ⟨hrun, hsz⟩ := hQ _ hW
    refine ⟨(hPf.runsOn _).seq hrun, le_trans hsz (le_trans (hSb _) ?_)⟩
    exact pw_mono cS dS (size_fst_le' _)))
  refine r.mono ?_
  set t := Enc.size I with ht
  set idx := bdIdx (descBD I) with hidx
  have hsum := sum_map_le_of_le ((List.range idx).map
    (dsCall trRep (bdDS (descBD I)))) τ' (fun Wb => τ Wb.1) 1
    (pw cf df (2 * chainBound t + 4)) (fun J hJ => by
      rw [List.mem_map] at hJ
      obtain ⟨j, -, rfl⟩ := hJ
      have e1 : cf * (Enc.size (dsCall trRep (bdDS (descBD I)) j) + 1) ^ df
          ≤ pw cf df (2 * chainBound t + 4) :=
        pw_mono cf df (hcallSize j)
      show cf * (Enc.size (dsCall trRep (bdDS (descBD I)) j) + 1) ^ df
          + τ (dsCall trRep (bdDS (descBD I)) j).1
        ≤ 1 * τ (dsCall trRep (bdDS (descBD I)) j).1 + pw cf df (2 * chainBound t + 4)
      omega)
  have hcalls : ((descCalls I).map τ) = ((List.range idx).map
      (dsCall trRep (bdDS (descBD I)))).map (fun Wb => τ Wb.1) := by
    simp only [descCalls, List.map_map]; rfl
  rw [hcalls]
  simp only [List.length_map, List.length_range] at hsum
  have hsz : Enc.size (descBD I) ≤ 6 * Enc.size I + 8 := by
    have e1 := size_pair_le' (descBD I)
    have e2 := size_pair_le' (descBD I).1
    have e3 : (descBD I).1.2 = false := rfl
    rw [e3, size_false] at e2
    have e4 : Enc.size (descBD I).1.1 ≤ Enc.size I := size_fst_le' I
    have e5 : Enc.size (descBD I).2 ≤ Enc.size I := size_snd_le' I
    omega
  have t1 : pw cB dB (Enc.size (descBD I)) ≤ pw cB dB (6 * t + 12) :=
    pw_mono cB dB (by omega)
  have t5 := hcd t
  rw [hGd] at t5
  have e5 : c * (t + 1) ^ d = pw c d t := rfl
  have e6 : pw cc dc t = cc * (t + 1) ^ dc := rfl
  have hdi : descIdx I = idx := rfl
  rw [hdi]
  set A := pw cf df (2 * chainBound t + 4) with hA
  set B := pw cB dB (6 * t + 12) with hB
  set C := pw cc dc t with hC
  have hGle : C + B + 1000 * A ≤ pw c d t := by rw [← e5]; exact t5
  have hmul : 1000 * (idx * A) + (idx + 2) * B + C ≤ (idx + 2) * pw c d t := by
    have h1 : (idx + 2) * (C + B + 1000 * A) ≤ (idx + 2) * pw c d t := Nat.mul_le_mul_left _ hGle
    nlinarith
  have t1' : (idx + 2) * pw cB dB (Enc.size (descBD I)) ≤ (idx + 2) * B :=
    Nat.mul_le_mul_left _ t1
  have e8 : cc * (Enc.size I + 1) ^ dc = C := rfl
  rw [e8]
  generalize (((List.range idx).map
    (dsCall trRep (bdDS (descBD I)))).map (fun Wb => τ Wb.1)).sum = S1 at hsum ⊢
  generalize (((List.range idx).map
    (dsCall trRep (bdDS (descBD I)))).map τ').sum = S2 at hsum ⊢
  generalize (idx + 2) * pw cB dB (Enc.size (descBD I)) = V at t1' ⊢
  omega

/-! ## Proposition 11.1.7 (Chain Rule) -/

/-- The first call of the Chain Rule: the window `Δ₁` with the candidate coset `σG` of the
instance. -/
def chain1 (W : RawWinSI) (Δ₁ : List ℕ) : RawWinSI :=
  (Δ₁, tidyGens (W.2.2.2.1, W.2.1), normPerm (W.2.2.2.1, W.2.2.1), W.2.2.2.1, W.2.2.2.2)

/-- The second call of the Chain Rule, when the first answer is `G₁σ₁`: the window `Δ₂` with
the candidate coset `G₁σ₁`. -/
def chain2 (W : RawWinSI) (Δ₂ : List ℕ) (g : RawGens) (τ : RawPerm) : RawWinSI :=
  (Δ₂, tidyGens (W.2.2.2.1, g), normPerm (W.2.2.2.1, τ), W.2.2.2.1, W.2.2.2.2)

theorem decWinSI_K_tidy {x : RawStr} (hx : x.length = n) (g : RawGens) (τ : RawPerm) :
    decCoset n (some (tidyGens (x, g), normPerm (x, τ))) = decCoset n (some (g, τ)) := by
  rw [decCoset_some, decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]

/-- **Proposition 11.1.7 (Chain Rule), §11.1, what the RAM reduction computes.**  *"Let `Δ₁`
and `Δ₂` be `G`-invariant subsets of `Ω` and let `Iso^{Δ₁}_G(x, y) = G₁σ`.  Then
`Iso^{Δ₁∪Δ₂}_G(x, y) = Iso^{Δ₂}_{G₁σ}(x, y) = Iso^{Δ₂}_{G₁}(x, y^{σ⁻¹})σ`."*  For a
well-formed instance with candidate coset `K = σG` and two `G`-invariant windows, if `ansQ`
answers every well-formed instance:

* the reduction returns `Iso^{Δ₁ ∪ Δ₂}_K(x, y)`;
* its first call is the instance `Iso^{Δ₁}_K(x, y)`;
* if that answer is empty, there is no other call;
* if that answer is `G₁σ₁`, the only other call is the instance `Iso^{Δ₂}_{G₁σ₁}(x, y)`, the
  middle term of Eq. (63).

The RAM running time is `Algo.proposition_11_1_7_ram`. -/
theorem proposition_11_1_7_ram_spec {ansQ : RawWinSI → RawCoset} {W : RawWinSI}
    {Δ₁ Δ₂ : List ℕ} (hI : WLWF n (W, [Δ₁, Δ₂]))
    (hQ : ∀ V, WinWF n V → decCoset n (ansQ V) = (decWinSI n V).answer) :
    decCoset n (wlOut ansQ (W, [Δ₁, Δ₂])) = Babai.wIso (winSet n Δ₁ ∪ winSet n Δ₂)
        (decWinSI n W).K (decStrN n W.2.2.2.1) (decStrN n W.2.2.2.2) ∧
      WinWF n (chain1 W Δ₁) ∧
      decWinSI n (chain1 W Δ₁) = ⟨(decWinSI n W).K, winSet n Δ₁, decStrN n W.2.2.2.1,
        decStrN n W.2.2.2.2⟩ ∧
      (lcAnsN ansQ (chain1 W Δ₁) = none → wlCalls ansQ (W, [Δ₁, Δ₂]) = [chain1 W Δ₁]) ∧
      (∀ g τ, lcAnsN ansQ (chain1 W Δ₁) = some (g, τ) →
        wlCalls ansQ (W, [Δ₁, Δ₂]) = [chain1 W Δ₁, chain2 W Δ₂ g τ] ∧
        WinWF n (chain2 W Δ₂ g τ) ∧
        decWinSI n (chain2 W Δ₂ g τ) = ⟨(decWinSI n (chain1 W Δ₁)).answer, winSet n Δ₂,
          decStrN n W.2.2.2.1, decStrN n W.2.2.2.2⟩) := by
  have hx : W.2.2.2.1.length = n := hI.1.1
  have hgs := hI.1.2.2.2.2.1
  have h1 := hI.2 Δ₁ (by simp)
  have h2 := hI.2 Δ₂ (by simp)
  have hinv1 : rawIsInvariant (tidyGens (W.2.2.2.1, W.2.1), Δ₁) = true := by
    rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx _) h1.2.1, decGroup_tidyGens hx]
    exact h1.2.2
  have hc1 : wlChild ((W, [Δ₁, Δ₂]), 0, some (W.2.1, W.2.2.1)) = some (chain1 W Δ₁, []) :=
    wlChild_eq_some_of (I := (W, [Δ₁, Δ₂])) (by simp) hinv1
  have hJ1 := (wlChild_wf hI hc1).1
  have hK1 : decWinSI n (chain1 W Δ₁) = ⟨(decWinSI n W).K, winSet n Δ₁,
      decStrN n W.2.2.2.1, decStrN n W.2.2.2.2⟩ := by
    rw [decWinSI, decWinSI]
    congr 1
    exact decWinSI_K_tidy hx _ _
  have hcalls : wlCalls ansQ (W, [Δ₁, Δ₂]) = chain1 W Δ₁ ::
      (wlRound.loopCalls (wlAns ansQ) 1 (W, [Δ₁, Δ₂]) 1
        (lcAnsN ansQ (chain1 W Δ₁))).map Prod.fst := by
    rw [wlCalls]
    show ((wlRound.loopCalls (wlAns ansQ) (0 + 1 + 1) (W, [Δ₁, Δ₂]) 0
      (some (W.2.1, W.2.2.1))).map Prod.fst) = _
    have hc1' : wlRound.child (((W, [Δ₁, Δ₂]) : RawWinList), 0, some (W.2.1, W.2.2.1))
        = some ((chain1 W Δ₁, []) : RawWinList) := hc1
    rw [wlRound.loopCalls_succ_some hc1']
    rfl
  refine ⟨?_, hJ1, hK1, ?_, ?_⟩
  · have h := (wl_spec hI hQ).1
    rw [h]
    congr 1
    ext u
    simp
  · intro hnone
    rw [hcalls, hnone]
    rfl
  · intro g τ hsome
    have hans : decCoset n (some (g, τ)) = (decWinSI n (chain1 W Δ₁)).answer := by
      rw [← hsome]; exact lcAnsN_correct hQ hJ1
    have hsub : decCoset n (some (g, τ)) ⊆ (decWinSI n W).K := by
      rw [hans, hK1]
      exact fun ρ hρ => hρ.1
    have hle : decGroup n g ≤ decGroup n W.2.1 :=
      decGroup_le_of_subset (σ₀ := decPerm n W.2.2.1) (τ := decPerm n τ) hsub
    have hinv2 : rawIsInvariant (tidyGens (W.2.2.2.1, g), Δ₂) = true := by
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx _) h2.2.1, decGroup_tidyGens hx]
      exact isInvariant_of_le h2.2.2 hle
    have hc2 : wlChild ((W, [Δ₁, Δ₂]), 1, some (g, τ)) = some (chain2 W Δ₂ g τ, []) :=
      wlChild_eq_some_of (I := (W, [Δ₁, Δ₂])) (by simp) hinv2
    refine ⟨?_, (wlChild_wf hI hc2).1, ?_⟩
    · rw [hcalls, hsome]
      show chain1 W Δ₁ :: ((wlRound.loopCalls (wlAns ansQ) (0 + 1) (W, [Δ₁, Δ₂]) 1
        (some (g, τ))).map Prod.fst) = _
      have hc2' : wlRound.child (((W, [Δ₁, Δ₂]) : RawWinList), 1, some (g, τ))
          = some ((chain2 W Δ₂ g τ, []) : RawWinList) := hc2
      rw [wlRound.loopCalls_succ_some hc2']
      rfl
    · rw [decWinSI, ← hans, ← decWinSI_K_tidy hx g τ]
      rfl

set_option maxHeartbeats 1000000 in
/-- **Proposition 11.1.7 (Chain Rule), §11.1, on the RAM.**  One program transformer `F`: for
every program `Q` that runs on the well-formed instances with polynomially small answers, `F Q`
returns `Iso^{Δ₁∪Δ₂}_K(x, y)` with at most two calls (`Algo.proposition_11_1_7_ram_spec`),
within `1000 · ∑_{W ∈ calls} τ(W) + poly(size)` steps. -/
theorem proposition_11_1_7_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (W : RawWinSI)
        (Δ₁ Δ₂ : List ℕ), WLWF n (W, [Δ₁, Δ₂]) →
        (∀ V, WinWF n V → RunsOn 16 Q V (ansQ V) (τ V) ∧ Enc.size (ansQ V) ≤ S (Enc.size V)) →
        RunsOn 16 (F Q) ((W, [Δ₁, Δ₂]) : RawWinList) (wlOut ansQ (W, [Δ₁, Δ₂]))
          (1000 * ((wlCalls ansQ (W, [Δ₁, Δ₂])).map τ).sum
            + pw c d (Enc.size ((W, [Δ₁, Δ₂]) : RawWinList))) := by
  obtain ⟨F, c, d, hF⟩ := exists_wlProg S hS
  refine ⟨F, 4 * c, d, fun Q hQ => ⟨(hF Q hQ).1, ?_⟩⟩
  intro n ansQ τ W Δ₁ Δ₂ hI hQr
  refine ((hF Q hQ).2 n ansQ τ _ hI hQr).mono ?_
  have e : ([Δ₁, Δ₂] : RawBlocks).length + 2 = 4 := rfl
  simp only [e]
  have : 4 * pw c d (Enc.size ((W, [Δ₁, Δ₂]) : RawWinList))
      = pw (4 * c) d (Enc.size ((W, [Δ₁, Δ₂]) : RawWinList)) := by
    simp only [pw]; ring
  omega

/-! ## Eq. (64): strong descent -/

/-- An instance of strong descent: an instance `(Δ, G, σ, x, y)` and generators of `N`. -/
abbrev RawSDIn := RawWinSI × RawGens

/-- The descent instance, whose payload is the list of `N`-orbits in the window. -/
def sdBD (I : RawSDIn) : RawBD RawBlocks := ((I.1, winOrbits (I.2, I.1.1)), I.2)

/-- **The hypothesis of strong descent**: a well-formed instance and a subgroup `N ≤ G`.
(Normality and transitivity are needed only for the lengths of the orbits,
`Algo.winOrbits_length_mul`.) -/
def SDInWF (n : ℕ) (I : RawSDIn) : Prop :=
  WinWF n I.1 ∧ RawGens.WF n I.2 ∧ decGroup n I.2 ≤ decGroup n I.1.2.1

theorem SDInWF.bd {I : RawSDIn} (hI : SDInWF n I) : BDWF n (sdBD I) := ⟨hI.1, hI.2.1, hI.2.2⟩

/-- `|G : N|`, as the routine computes it. -/
def sdIdx (I : RawSDIn) : ℕ := bdIdx (sdBD I)

/-- The `|G : N|` chain instances: one coset `σρ_jN` each, with the `N`-orbits as windows. -/
def sdCosets (I : RawSDIn) : List RawWinList :=
  (List.range (sdIdx I)).map (dsCall trRep (bdDS (sdBD I)))

/-- The output of strong descent, with the calls answered by `ansQ`. -/
def sdOut (ansQ : RawWinSI → RawCoset) (I : RawSDIn) : RawCoset :=
  dsOut trRep (wlOut ansQ) (bdDS (sdBD I))

/-- The calls of strong descent. -/
def sdCalls (ansQ : RawWinSI → RawCoset) (I : RawSDIn) : List RawWinSI :=
  (sdCosets I).flatMap (wlCalls ansQ)

theorem rawIsInvariant_sub {I : RawSDIn} (hI : SDInWF n I) :
    rawIsInvariant (I.2, I.1.1) = true := by
  have hw := hI.1
  rw [rawIsInvariant_eq_true_iff hI.2.1 hw.2.2.2.1]
  exact isInvariant_of_le ((rawIsInvariant_eq_true_iff hw.2.2.2.2.1 hw.2.2.2.1).1
    hw.2.2.2.2.2.2.2) hI.2.2

theorem biUnion_winOrbits {I : RawSDIn} (hI : SDInWF n I) :
    (⋃ B ∈ winOrbits (I.2, I.1.1), winSet n B) = winSet n I.1.1 := by
  have hw := hI.1
  have hinv := rawIsInvariant_sub hI
  ext u
  simp only [Set.mem_iUnion, exists_prop, winSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨B, hB, hu⟩
    exact winOrbits_subset hI.2.1 hw.2.2.2.1 hinv hB _ hu
  · intro hu
    obtain ⟨B, hB, huB⟩ := List.mem_flatten.1 (winOrbits_cover hI.2.1 hw.2.2.2.1 hu)
    exact ⟨B, hB, huB⟩

/-- Every coset of strong descent is a well-formed chain instance: the `N`-orbits in `Δ` are
`N`-invariant windows. -/
theorem sdCoset_wf {I : RawSDIn} (hI : SDInWF n I) (j : ℕ) :
    WLWF n (dsCall trRep (bdDS (sdBD I)) j) := by
  have hDS := bdDS_wf hI.bd
  have hw := hI.1
  have hinv := rawIsInvariant_sub hI
  refine ⟨dsCall_wf hDS j, fun B hB => ?_⟩
  have hB' : B ∈ winOrbits (I.2, I.1.1) := hB
  refine ⟨winOrbits_nodup hB', winOrbits_lt hI.2.1 hw.2.2.2.1 hinv hB', ?_⟩
  rw [decGroup_dsCall hDS]
  obtain ⟨p, hp, rfl⟩ := winOrbits_mem hB'
  exact isInvariant_rawOrbit hI.2.1 (hw.2.2.2.1 p hp)

/-- **Eq. (64), §11.1 ("strong descent"), what the RAM reduction computes.**  *"'Strong
descent' begins with descent to an intransitive subgroup `N ≤ G` followed by an application of
the Chain rule to the orbit partition of `N`."*  For a well-formed instance and `N ≤ G`, if
`ansQ` answers every well-formed instance:

* the reduction returns `Iso^Δ_{σG}(x, y)`;
* it descends to the `|G : N|` cosets of `N`;
* it makes at most `|G : N| · m` calls, `m` the number of `N`-orbits in `Δ`;
* each call is a well-formed instance whose window is one of the `N`-orbits in `Δ`, with a
  subgroup of `N` and the strings `x, y`.

That every orbit has `|Δ|/m` points when `G` is transitive on `Δ` and `N ◁ G` (Fact 11.1.8)
is `Algo.winOrbits_length_mul`.  The RAM running time is `Algo.eq_64_ram`. -/
theorem eq_64_ram_spec {ansQ : RawWinSI → RawCoset} {I : RawSDIn} (hI : SDInWF n I)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    decCoset n (sdOut ansQ I) = (decWinSI n I.1).answer ∧
      sdIdx I = (decGroup n I.2).relIndex (decGroup n I.1.2.1) ∧
      (sdCalls ansQ I).length ≤ sdIdx I * (winOrbits (I.2, I.1.1)).length ∧
      ∀ W ∈ sdCalls ansQ I, WinWF n W ∧ W.1 ∈ winOrbits (I.2, I.1.1) ∧
        decGroup n W.2.1 ≤ decGroup n I.2 ∧ W.2.2.2 = I.1.2.2.2 := by
  have hbd := hI.bd
  have hDS := bdDS_wf hbd
  refine ⟨?_, bdIdx_eq hbd, ?_, ?_⟩
  · refine (ds_spec hDS (fun j _ => ?_)).1
    rw [(wl_spec (sdCoset_wf hI j) hQ).1]
    show Babai.wIso (⋃ B ∈ winOrbits (I.2, I.1.1), winSet n B) _ _ _ = _
    rw [biUnion_winOrbits hI]
    rfl
  · rw [sdCalls, List.length_flatMap]
    have h := sum_map_le_of_le (sdCosets I) (fun J => (wlCalls ansQ J).length) (fun _ => 0) 0
      (winOrbits (I.2, I.1.1)).length (fun J hJ => by
        rw [sdCosets, List.mem_map] at hJ
        obtain ⟨j, -, rfl⟩ := hJ
        have := (wl_spec (sdCoset_wf hI j) hQ).2.1
        simpa using this)
    have hl : (sdCosets I).length = sdIdx I := by simp [sdCosets]
    rw [hl, zero_mul, zero_add] at h
    exact h
  · intro W hW
    rw [sdCalls, List.mem_flatMap] at hW
    obtain ⟨J, hJ, hW⟩ := hW
    rw [sdCosets, List.mem_map] at hJ
    obtain ⟨j, -, rfl⟩ := hJ
    obtain ⟨hWf, hWmem, hWstr, hWle, -⟩ := (wl_spec (sdCoset_wf hI j) hQ).2.2 W hW
    refine ⟨hWf, hWmem, ?_, hWstr⟩
    rw [decGroup_dsCall hDS] at hWle
    exact hWle

theorem polyFun_sdBD : PolyFun sdBD := by
  have hΔ : PolyFun (fun I : RawSDIn => I.1.1) := polyFun_fst.comp polyFun_fst
  exact ((polyFun_fst.pair ((polyFun_snd.pair hΔ).comp polyFun_winOrbits)).pair
    polyFun_snd).of_eq (fun _ => rfl)

set_option maxHeartbeats 8000000 in
/-- **Eq. (64), §11.1 ("strong descent"), on the RAM.**  One program transformer `F`: for every
program `Q` that runs on the well-formed instances with polynomially small answers, `F Q`
returns `Iso^Δ_{σG}(x, y)` with at most `|G : N| · m` calls, each on an `N`-orbit
(`Algo.eq_64_ram_spec`), within `10⁶ · ∑_{W ∈ calls} τ(W) + (|G : N| + 2) · poly(size)` steps.
This is the recurrence `T(n) ≤ |G : N| m T(n/m)` of Eq. (64), with a polynomial overhead per
coset of `N` and a constant factor on the calls (see the the corrected paper
"Prop. 11.1.6 and Eq. (64): no additive cost"). -/
theorem eq_64_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ (n : ℕ) (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ) (I : RawSDIn), SDInWF n I →
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W)) →
        RunsOn 16 (F Q) I (sdOut ansQ I)
          (10 ^ 6 * ((sdCalls ansQ I).map τ).sum + (sdIdx I + 2) * pw c d (Enc.size I)) := by
  obtain ⟨FA, cA, dA, hFA⟩ := exists_wlProg S hS
  have hSB : PolyBound (fun m => chainBound m + 4 * m + 2) :=
    (polyBound_chainBound.add ((polyBound_const 4).mul polyBound_id)).add (polyBound_const 2)
  obtain ⟨FB, cB, dB, hFB⟩ := exists_bdProg (P := RawBlocks)
    (fun m => chainBound m + 4 * m + 2) hSB
  obtain ⟨Pp, cp, dp, hPp, hPps⟩ := polyFun_witness polyFun_sdBD
  obtain ⟨G, hGd⟩ : ∃ G : ℕ → ℕ, ∀ t, G t = pw cp dp t + pw cB dB (pw cp dp t)
      + 1000 * ((t + 2) * pw cA dA (2 * chainBound t + 2 * pw cp dp t)) :=
    ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    rw [show G = fun t => pw cp dp t + pw cB dB (pw cp dp t)
      + 1000 * ((t + 2) * pw cA dA (2 * chainBound t + 2 * pw cp dp t)) from funext hGd]
    exact ((polyBound_pw cp dp).add ((polyBound_pw cB dB).comp (polyBound_pw cp dp))).add
      ((polyBound_const 1000).mul ((polyBound_id.add (polyBound_const 2)).mul
        ((polyBound_pw cA dA).comp (((polyBound_const 2).mul polyBound_chainBound).add
          ((polyBound_const 2).mul (polyBound_pw cp dp))))))
  obtain ⟨c, d, hcd⟩ := hG
  refine ⟨fun Q => RAM.seq Pp (FB (FA Q)), c, d, fun Q hQwf => ?_⟩
  obtain ⟨hAwf, hArun⟩ := hFA Q hQwf
  obtain ⟨hBwf, hBrun⟩ := hFB (FA Q) hAwf
  refine ⟨wf_seq (CleanComputeAt.wf' hPp) hBwf, ?_⟩
  intro n ansQ τ I hI hQ
  have hbd := hI.bd
  have hDS := bdDS_wf hbd
  let τB : RawWinList → ℕ := fun J =>
    1000 * ((wlCalls ansQ J).map τ).sum + (J.2.length + 2) * pw cA dA (Enc.size J)
  have r := (hPp.runsOn I).seq (hBrun n (wlOut ansQ) τB (sdBD I) hbd (fun j _ =>
    ⟨hArun n ansQ τ _ (sdCoset_wf hI j) hQ, size_wlOut_le ansQ _⟩))
  refine r.mono ?_
  set t := Enc.size I with ht
  have hsm : Enc.size I.1.2.2.2 ≤ Enc.size I :=
    le_trans (size_snd_le' _) (le_trans (size_snd_le' _) (le_trans (size_snd_le' _)
      (size_fst_le' I)))
  have hlenm : (winOrbits (I.2, I.1.1)).length ≤ t := by
    have h1 := length_winOrbits_le I.2 I.1.1
    have h2 : I.1.1.length ≤ Enc.size I :=
      le_trans (length_le_size _) (le_trans (size_fst_le' _) (size_fst_le' I))
    omega
  have hcallSize : ∀ j, Enc.size (dsCall trRep (bdDS (sdBD I)) j)
      ≤ 2 * chainBound t + 2 * pw cp dp t := by
    intro j
    have h1 : Enc.size (dsCall trRep (bdDS (sdBD I)) j).1
        ≤ chainBound (Enc.size (dsCall trRep (bdDS (sdBD I)) j).1.2.2.2) :=
      size_winSI_le (dsCall_wf hDS j)
    have h1' : (dsCall trRep (bdDS (sdBD I)) j).1.2.2.2 = I.1.2.2.2 := rfl
    rw [h1'] at h1
    have h1'' : chainBound (Enc.size I.1.2.2.2) ≤ chainBound t := mono_chainBound hsm
    have h2 := size_pair_le' (dsCall trRep (bdDS (sdBD I)) j)
    have h3 : Enc.size (dsCall trRep (bdDS (sdBD I)) j).2 ≤ Enc.size (sdBD I) := by
      show Enc.size (sdBD I).1.2 ≤ _
      exact le_trans (size_snd_le' _) (size_fst_le' _)
    have h4 : Enc.size (sdBD I) ≤ pw cp dp t := hPps I
    omega
  set idx := sdIdx I with hidx
  set m := (winOrbits (I.2, I.1.1)).length with hmdef
  set A := pw cA dA (2 * chainBound t + 2 * pw cp dp t) with hA
  have hsum := sum_map_le_of_le ((List.range idx).map (dsCall trRep (bdDS (sdBD I)))) τB
    (fun J => ((wlCalls ansQ J).map τ).sum) 1000 ((t + 2) * A) (fun J hJ => by
      rw [List.mem_map] at hJ
      obtain ⟨j, -, rfl⟩ := hJ
      have e1 : pw cA dA (Enc.size (dsCall trRep (bdDS (sdBD I)) j)) ≤ A :=
        pw_mono cA dA (hcallSize j)
      have e2 : (dsCall trRep (bdDS (sdBD I)) j).2.length = m := rfl
      show 1000 * ((wlCalls ansQ (dsCall trRep (bdDS (sdBD I)) j)).map τ).sum
          + ((dsCall trRep (bdDS (sdBD I)) j).2.length + 2)
            * pw cA dA (Enc.size (dsCall trRep (bdDS (sdBD I)) j))
        ≤ 1000 * ((wlCalls ansQ (dsCall trRep (bdDS (sdBD I)) j)).map τ).sum
          + (t + 2) * A
      rw [e2]
      exact Nat.add_le_add_left (Nat.mul_le_mul (by omega) e1) _)
  have hflat : ((sdCalls ansQ I).map τ).sum
      = (((List.range idx).map (dsCall trRep (bdDS (sdBD I)))).map
          (fun J => ((wlCalls ansQ J).map τ).sum)).sum :=
    sum_map_flatMap _ (wlCalls ansQ) τ
  simp only [List.length_map, List.length_range] at hsum
  have t1 : pw cB dB (Enc.size (sdBD I)) ≤ pw cB dB (pw cp dp t) :=
    pw_mono cB dB (hPps I)
  have t5 := hcd t
  rw [hGd] at t5
  have e5 : c * (t + 1) ^ d = pw c d t := rfl
  set C := pw cp dp t with hC
  set B := pw cB dB C with hB
  have hGle : C + B + 1000 * ((t + 2) * A) ≤ pw c d t := by rw [← e5]; exact t5
  have hmul : 1000 * (idx * ((t + 2) * A)) + (idx + 2) * B + C ≤ (idx + 2) * pw c d t := by
    have h1 : (idx + 2) * (C + B + 1000 * ((t + 2) * A)) ≤ (idx + 2) * pw c d t :=
      Nat.mul_le_mul_left _ hGle
    nlinarith
  have t1' : (idx + 2) * pw cB dB (Enc.size (sdBD I)) ≤ (idx + 2) * B :=
    Nat.mul_le_mul_left _ t1
  have e8 : cp * (Enc.size I + 1) ^ dp = C := rfl
  have e9 : (bdDS (sdBD I)).2.2.2 = idx := rfl
  rw [hflat, show (10 : ℕ) ^ 6 = 1000000 by norm_num, e8, show bdIdx (sdBD I) = idx from rfl]
  generalize (((List.range idx).map (dsCall trRep (bdDS (sdBD I)))).map
    (fun J => ((wlCalls ansQ J).map τ).sum)).sum = S1 at hsum ⊢
  generalize (((List.range idx).map (dsCall trRep (bdDS (sdBD I)))).map τB).sum = S2
    at hsum ⊢
  generalize idx * ((t + 2) * A) = X at hsum hmul
  generalize (idx + 2) * pw cB dB (Enc.size (sdBD I)) = V at t1' ⊢
  omega

/-! ### Fact 11.1.8 inside the window -/

/-- Conjugating by `g ∈ G` carries the `N`-orbit of `u` onto the `N`-orbit of `g u`, when
`N ◁ G`; so the two have the same size (the argument of `Babai.Fact_11_1_8`). -/
theorem orbit_ncard_apply {Ω : Type*} {G N : Subgroup (Perm Ω)} (hN : Babai.IsNormalIn N G)
    {g : Perm Ω} (hg : g ∈ G) (u : Ω) :
    (MulAction.orbit N (g u)).ncard = (MulAction.orbit N u).ncard := by
  have himg : MulAction.orbit N (g u) = (fun w => g w) '' MulAction.orbit N u := by
    ext w
    simp only [Set.mem_image, MulAction.mem_orbit_iff, Subgroup.smul_def]
    constructor
    · rintro ⟨a, rfl⟩
      have hconj : g⁻¹ * (a : Perm Ω) * g ∈ N := by
        have := hN.conj_mem g⁻¹ (inv_mem hg) (a : Perm Ω) a.2
        simpa using this
      refine ⟨(g⁻¹ * (a : Perm Ω) * g) • u, ⟨⟨_, hconj⟩, rfl⟩, ?_⟩
      show g ((g⁻¹ * (a : Perm Ω) * g) u) = (a : Perm Ω) (g u)
      simp [Perm.mul_apply]
    · rintro ⟨w', ⟨a, rfl⟩, rfl⟩
      refine ⟨⟨g * (a : Perm Ω) * g⁻¹, hN.conj_mem _ hg _ a.2⟩, ?_⟩
      show (g * (a : Perm Ω) * g⁻¹) (g u) = g ((a : Perm Ω) u)
      simp [Perm.mul_apply]
  rw [himg, Set.ncard_image_of_injective _ g.injective]

theorem length_rawOrbit_eq {gs : RawGens} (hgs : RawGens.WF n gs) {p : ℕ} (hp : p < n) :
    (rawOrbit (gs, p)).length = (MulAction.orbit (decGroup n gs) (⟨p, hp⟩ : Fin n)).ncard := by
  have h := rawOrbit_spec hgs hp
  have hset : {k | k ∈ rawOrbit (gs, p)} = ((rawOrbit (gs, p)).toFinset : Set ℕ) := by
    ext k; simp
  rw [hset] at h
  have h2 := congrArg Set.ncard h
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_rawOrbit gs p),
    Set.ncard_image_of_injective _ Fin.val_injective] at h2
  exact h2

/-- **Fact 11.1.8 for the window** (and the sentence after it): if `G` is transitive on the
window `Δ` and `N ◁ G`, then every `N`-orbit in `Δ` has `|Δ|/m` points, `m` the number of
`N`-orbits in `Δ`.  This is the `n/m` of Eq. (64). -/
theorem winOrbits_length_mul {I : RawSDIn} (hI : SDInWF n I)
    (hN : Babai.IsNormalIn (decGroup n I.2) (decGroup n I.1.2.1))
    (htr : ∀ u v : Fin n, (u : ℕ) ∈ I.1.1 → (v : ℕ) ∈ I.1.1 →
      ∃ g ∈ decGroup n I.1.2.1, g u = v) :
    ∀ B ∈ winOrbits (I.2, I.1.1),
      B.length * (winOrbits (I.2, I.1.1)).length = I.1.1.length := by
  have hw := hI.1
  have hΔ := hw.2.2.2.1
  have hinv := rawIsInvariant_sub hI
  have hsame : ∀ B ∈ winOrbits (I.2, I.1.1), ∀ B' ∈ winOrbits (I.2, I.1.1),
      B.length = B'.length := by
    intro B hB B' hB'
    obtain ⟨p, hp, rfl⟩ := winOrbits_mem hB
    obtain ⟨p', hp', rfl⟩ := winOrbits_mem hB'
    obtain ⟨g, hg, hgp⟩ := htr ⟨p, hΔ p hp⟩ ⟨p', hΔ p' hp'⟩ hp hp'
    rw [length_rawOrbit_eq hI.2.1 (hΔ p hp), length_rawOrbit_eq hI.2.1 (hΔ p' hp'), ← hgp,
      orbit_ncard_apply hN hg]
  have hnd : (winOrbits (I.2, I.1.1)).flatten.Nodup := by
    rw [List.nodup_flatten]
    refine ⟨fun B hB => winOrbits_nodup hB, ?_⟩
    exact (winOrbits_pairwise hI.2.1 hΔ).imp (fun h k hk hk' => h k hk hk')
  have hperm : (winOrbits (I.2, I.1.1)).flatten.Perm I.1.1 := by
    refine List.perm_of_nodup_nodup_toFinset_eq hnd hw.2.2.1 ?_
    ext k
    simp only [List.mem_toFinset]
    constructor
    · intro hk
      obtain ⟨B, hB, hkB⟩ := List.mem_flatten.1 hk
      exact winOrbits_subset hI.2.1 hΔ hinv hB k hkB
    · intro hk
      exact winOrbits_cover hI.2.1 hΔ hk
  intro B hB
  have hlen := hperm.length_eq
  rw [List.length_flatten] at hlen
  have hmap : (winOrbits (I.2, I.1.1)).map List.length
      = (winOrbits (I.2, I.1.1)).map (fun _ => B.length) :=
    List.map_congr_left (fun B' hB' => hsame B' hB' B hB)
  rw [hmap, List.map_const', List.sum_replicate, smul_eq_mul] at hlen
  rw [← hlen, Nat.mul_comm]

end Algo
