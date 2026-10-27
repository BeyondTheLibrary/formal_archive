/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the facts of one round of Procedure Align (§14.1) for a list of versions
that moves with the isomorphisms of the input.
-/
import Workspace.Algo.AlignTransportRun
import Workspace.Master.AlignHintedCall

/-!
# The round of Procedure Align from the transport of the fixed version

`Babai.Line4cdData.ofShape` proves the facts of a round of Procedure Align (`Babai.AlignShape`)
from a canonical family of versions (Theorem 9.2.3), listed once each.  In lines 5–7 of the
Master Algorithm the versions are a list the machine computes (Theorem 13.2.1 with Theorem
9.2.3), which may repeat a version, and what is proved of it is the transport of the fixed
version: every `σ ∈ Iso_G(x, y)` carries `X'` to a listed version
(`Algo.aggnContinuation_transport_of_bip`).  That is all Eq. (71) uses
(`Babai.run_cosetAlignExpand_of_transport`), and the other facts do not look at the versions.
This file states them in that form:

* `Babai.AlignShape.run_red_of_transport`: the round returns `Iso_G(x, y)`;
* `Babai.AlignShape.calls_coset_of_facts`: every call is a coset instance in `G`;
* `Babai.AlignShape.calls_progress_of_facts`: every call has at most `4n/5` points or
  carries the hint of line 11.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {G : Subgroup (Perm W)} {x y : W → A}

namespace AlignShape

variable (S : AlignShape W A G x y)

/-- The call of line 6 on the dominant window is answered correctly by the round of lines
7–11, under the facts `Babai.Line4cdData` records of its shape. -/
theorem dominantRound_run (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D) :
    letI := S.act
    ∀ J : SIInstance W A,
      CosetAlignCall G (preimageSubgroup S.ϕ (structAut S.X')) S.head S.tail J →
      J.Δ = S.head → (S.dominantRound J).run = J.answer := by
  letI := S.act
  intro J hJ hΔ
  unfold AlignShape.dominantRound
  split
  · rfl
  · next D hD =>
      apply D.run_cosetRound _ (he D hD) J
      · obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
        exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩
      · rw [(hd D hD).2]; exact hΔ

/-- Eq. (71) and §14.1, lines 1–11: **the round of Procedure Align returns `Iso_G(x, y)`**
when every `σ ∈ Iso_G(x, y)` carries the fixed version to a listed version
(`Babai.Line4cdData.ofShape`, field `run_red`, with the transport of the fixed version in place
of canonicity). -/
theorem run_red_of_transport (hne : S.head ∉ S.tail)
    (hcover : (⋃ Δ ∈ S.head :: S.tail, Δ) = Set.univ)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D)
    (hT : letI := S.act; ∀ σ : G, strAct x (σ : Perm W) = y → (S.ϕ σ) • S.X' ∈ S.versions) :
    S.red.run = strIso (G : Set (Perm W)) x y := by
  letI := S.act
  exact run_cosetAlignExpand_of_transport hT hne hinv hcover (S.dominantRound_run hd he)

/-- **Every call of the round is a coset instance in `G`** (`Babai.Line4cdData.ofShape`,
field `calls_coset`). -/
theorem calls_coset_of_facts (hne : S.head ∉ S.tail)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D) :
    ∀ J ∈ S.red.calls, IsCosetInstance G J := by
  letI := S.act
  refine calls_cosetAlignExpand (x := x) (y := y) (versions := S.versions) hne hinv
    (S.dominantRound_run hd he) ?_ ?_
  · intro J hJ hΔ K hK
    unfold AlignShape.dominantRound at hK
    split at hK
    · simp only [SIReduction.calls_call, SIReduction.calls_done, List.mem_singleton] at hK
      subst K
      exact hJ.2.1
    · next D hD =>
        refine D.isCosetInstance_calls_cosetRound _ (he D hD) ?_ J ?_ K hK
        · rw [(hd D hD).1]; exact preimageSubgroup_le _ _
        · rw [(hd D hD).1]; exact hJ.2.2 hΔ
  · exact fun J hJ _ => hJ.2.1

/-- **Every call of the round has at most `4n/5` points or carries the hint of line 11**
(`Babai.Line4cdData.ofShape`, field `calls_progress`). -/
theorem calls_progress_of_facts (hne : S.head ∉ S.tail)
    (hinv : letI := S.act; ∀ Δ ∈ S.head :: S.tail,
      IsInvariant (preimageSubgroup S.ϕ (structAut S.X')) Δ)
    (hd : letI := S.act; ∀ D, S.dom = some D →
      D.toAlignDominant.Gs = preimageSubgroup S.ϕ (structAut S.X') ∧
      D.toAlignDominant.window = S.head)
    (he : ∀ D, S.dom = some D → S.domEnum.Spec D)
    (hsmall : ∀ Δ ∈ S.head :: S.tail, (Δ ≠ S.head ∨ S.dom = none) →
      5 * Δ.ncard ≤ 4 * Fintype.card W) :
    ∀ J ∈ S.red.calls,
      5 * J.windowSize ≤ 4 * Fintype.card W ∨ (S.hint (alignInst J)).isSome = true := by
  letI := S.act
  refine calls_cosetAlignExpand (x := x) (y := y) (versions := S.versions) hne hinv
    (S.dominantRound_run hd he) ?_ ?_
  · intro J hJ hΔ K hK
    unfold AlignShape.dominantRound at hK
    split at hK
    · next hD =>
        simp only [SIReduction.calls_call, SIReduction.calls_done, List.mem_singleton] at hK
        subst K
        exact Or.inl (hsmall J.Δ hJ.1 (Or.inr hD))
    · next D hD =>
        have hk : ∃ σ : Perm W, J.K = σ • (D.toAlignDominant.Gs : Set (Perm W)) := by
          obtain ⟨σ, _, hσ⟩ := hJ.2.2 hΔ
          exact ⟨σ, by rw [(hd D hD).1]; exact hσ⟩
        rcases D.cosetRound_small_or_hint _ (he D hD) J hk K hK with hs | hh
        · exact Or.inl (by omega)
        · right
          simp only [AlignShape.hint, hD]
          rw [AlignDominantRoundData.hint, dif_pos hh]
          rfl
  · intro J hJ hj
    exact Or.inl (hsmall J.Δ hJ.1 (Or.inl hj))

end AlignShape

end Babai
