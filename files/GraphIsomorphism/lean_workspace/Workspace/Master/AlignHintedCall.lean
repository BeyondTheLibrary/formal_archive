/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, lines 5–11 (as repaired in the corrected paper): in the round of Procedure Align, the
calls on more than `2n/3` points are exactly the hinted calls of line 11.
-/
import Workspace.Master.Line4cdCore
import Workspace.Master.AlignOtherClasses

/-!
# The hinted call of Procedure Align is the only large call

In the repaired round of Procedure Align, line 11 hands `ϕ*` down to the first
call of the Chain Rule over the orbits of `G*` in the dominant window, when that orbit has more
than `2n/3` points (`Babai.AlignDominantRoundData.HasHint`). Every other call of the round has
at most `2n/3` points, provided the color classes other than the dominant window do:

* the other orbits of `G*` in the dominant window have fewer than `n/3` points
  (`Babai.AlignDominant.other_orbit_small`, used by
  `Babai.AlignDominantRoundData.cosetRound_small_or_hint`);
* the other color classes have at most `2n/3` points
  (`Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`).

So a machine can recognise the hinted call by its size alone. This file states it for a round
of Procedure Align:

* `Babai.AlignShape.three_mul_windowSize_le_or_hasHint`: every call has at most `2n/3` points
  or carries the hint (for the round of Align in lines 4c–4d and in lines 5–7 alike; the
  `Babai.Line4cdData` form is `Babai.Line4cdData.three_mul_windowSize_le_or_hasHint`);
* `Babai.AlignShape.large_call_spec`, `Babai.Line4cdData.large_call_spec`: a call on more
  than `2n/3` points is in case 3, its window is an orbit `u^{G*}` with `u` in the dominant
  window, and its candidate set is a coset of `G*`.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {G : Subgroup (Perm W)} {x y : W → A} {par cost : ℕ}

namespace AlignShape

variable (S : AlignShape W A G x y)

/-- §14.1, lines 5–11: **every call of the round of Procedure Align has at most `2n/3` points
or carries the hint of line 11**, when line 6 found a dominant class `D` and every other color
class has at most `2n/3` points. The hypotheses are the facts `Babai.Line4cdData` records about
its shape (the head is not repeated, the windows are invariant under `G*`, `D` has the group
`G*` and the head as its window, and its enumerations meet their specification), so the lemma
applies to the round of Align in lines 4c–4d and in lines 5–7 alike. The proof is that of the
field `calls_progress` of `Babai.Line4cdData.ofShape`, with `2/3` in place of `4/5` for the
calls outside the dominant window. -/
theorem three_mul_windowSize_le_or_hasHint (hne : S.head ∉ S.tail)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    {D : AlignDominantRoundData W} (hD : S.dom = some D)
    (hd : letI := S.act;
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
        D.toAlignDominant.window = S.head)
    (he : S.domEnum.Spec D)
    (htail : ∀ Δ ∈ S.tail, 3 * Δ.ncard ≤ 2 * Fintype.card W) :
    ∀ J ∈ S.red.calls,
      3 * J.windowSize ≤ 2 * Fintype.card W ∨ D.HasHint (alignInst J) (alignInst J) := by
  classical
  letI := S.act
  have hr : ∀ J : SIInstance W A,
      CosetAlignCall G (preimageSubgroup S.ϕ (structAut S.X')) S.head S.tail J →
      J.Δ = S.head → (S.dominantRound J).run = J.answer := by
    intro J hJ hΔ
    unfold AlignShape.dominantRound
    rw [hD]
    apply D.run_cosetRound _ he J
    · obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
      exact ⟨σ, by rw [hd.1]; exact hσ⟩
    · rw [hd.2]; exact hΔ
  refine calls_cosetAlignExpand (x := x) (y := y) (versions := S.versions) hne hinv hr ?_ ?_
  · intro J hJ hΔ K hK
    unfold AlignShape.dominantRound at hK
    rw [hD] at hK
    have hk : ∃ σ : Perm W, J.K = σ • (D.toAlignDominant.Gs : Set (Perm W)) := by
      obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
      exact ⟨σ, by rw [hd.1]; exact hσ⟩
    exact D.cosetRound_small_or_hint _ he J hk K hK
  · intro J hJ hj
    left
    have hmem : J.Δ ∈ S.tail := by
      rcases List.mem_cons.1 hJ.1 with h | h
      · exact absurd h hj
      · exact h
    exact htail J.Δ hmem

/-- §14.1, lines 5–11: **a call on more than `2n/3` points is the hinted call of line 11**
(under the hypotheses of `Babai.AlignShape.three_mul_windowSize_le_or_hasHint`): the round is
in case 3 (`m*` large), the window of the call is an orbit `u^{G*}` of more than `2n/3` points
with `u` in the dominant window, and its candidate set is a coset of `G*`. -/
theorem large_call_spec (hne : S.head ∉ S.tail)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    {D : AlignDominantRoundData W} (hD : S.dom = some D)
    (hd : letI := S.act;
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
        D.toAlignDominant.window = S.head)
    (he : S.domEnum.Spec D)
    (htail : ∀ Δ ∈ S.tail, 3 * Δ.ncard ≤ 2 * Fintype.card W)
    {J : SIInstance W A} (hJ : J ∈ S.red.calls)
    (hbig : 2 * Fintype.card W < 3 * J.windowSize) :
    D.LargeParam ∧ ∃ u ∈ D.toAlignDominant.window,
      J.Δ = orbit D.toAlignDominant.Gs u ∧
      2 * Fintype.card W < 3 * (orbit D.toAlignDominant.Gs u).ncard ∧
      ∃ σ : Perm W, J.K = σ • (D.toAlignDominant.Gs : Set (Perm W)) := by
  rcases S.three_mul_windowSize_le_or_hasHint hne hinv hD hd he htail J hJ with
    hs | ⟨hL, c, hc⟩
  · omega
  refine ⟨hL, c.u, c.mem_window, ?_, c.dominant, cosetRepOf J.K, ?_⟩
  · have := congrArg SIInstance.Δ hc
    exact this.symm
  · have hK := congrArg SIInstance.K hc
    change (D.toAlignDominant.Gs : Set (Perm W)) = (cosetRepOf J.K)⁻¹ • J.K at hK
    rw [hK, smul_inv_smul]

end AlignShape

namespace Line4cdData

variable (C : Line4cdData W A G x y par cost)

/-- `Babai.AlignShape.three_mul_windowSize_le_or_hasHint` for the round of a
`Babai.Line4cdData`. -/
theorem three_mul_windowSize_le_or_hasHint {D : AlignDominantRoundData W}
    (hD : C.shape.dom = some D)
    (htail : ∀ Δ ∈ C.shape.tail, 3 * Δ.ncard ≤ 2 * Fintype.card W) :
    ∀ J ∈ C.shape.red.calls,
      3 * J.windowSize ≤ 2 * Fintype.card W ∨ D.HasHint (alignInst J) (alignInst J) :=
  C.shape.three_mul_windowSize_le_or_hasHint C.head_not_mem C.windows_invariant hD
    (C.dom_spec D hD) (C.domEnum_spec D hD) htail

/-- §14.1, lines 5–11: **a call on more than `2n/3` points of the round of a
`Babai.Line4cdData` is the hinted call of line 11** (`Babai.AlignShape.large_call_spec`). -/
theorem large_call_spec {D : AlignDominantRoundData W} (hD : C.shape.dom = some D)
    (htail : ∀ Δ ∈ C.shape.tail, 3 * Δ.ncard ≤ 2 * Fintype.card W)
    {J : SIInstance W A} (hJ : J ∈ C.shape.red.calls)
    (hbig : 2 * Fintype.card W < 3 * J.windowSize) :
    D.LargeParam ∧ ∃ u ∈ D.toAlignDominant.window,
      J.Δ = orbit D.toAlignDominant.Gs u ∧
      2 * Fintype.card W < 3 * (orbit D.toAlignDominant.Gs u).ncard ∧
      ∃ σ : Perm W, J.K = σ • (D.toAlignDominant.Gs : Set (Perm W)) :=
  C.shape.large_call_spec C.head_not_mem C.windows_invariant hD (C.dom_spec D hD)
    (C.domEnum_spec D hD) htail hJ hbig

end Line4cdData

end Babai
