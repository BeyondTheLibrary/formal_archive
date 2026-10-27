import Workspace.Master.CosetAlign
import Workspace.Master.AlignDominantRound

/-! # The boundary between the two forms of Procedure Align

The group round of lines 7–11 cannot be substituted directly into the coset
chain of lines 5–6. It starts from `G*`, even when the incoming candidate set is
a different coset of `G*`. The theorem below isolates the failed value equation.
It concerns the current group-form definition, not a claim of the paper.
-/

universe u v

namespace Babai

open Equiv
open scoped Pointwise

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- On equal constant strings, the existing group round returns `G*` independently
of the incoming candidate set. Its correctness theorem assumes that set is `G*`. -/
theorem AlignDominantRoundData.run_round_const (D : AlignDominantRoundData Ω)
    (a : A) (C : Set (Perm Ω)) :
    (D.round (⟨C, D.toAlignDominant.window, fun _ => a, fun _ => a⟩ : SIInstance Ω A)).run =
      (D.toAlignDominant.Gs : Set (Perm Ω)) := by
  have he : D.round (⟨C, D.toAlignDominant.window, fun _ => a, fun _ => a⟩ : SIInstance Ω A) =
      D.round (⟨(D.toAlignDominant.Gs : Set (Perm Ω)), D.toAlignDominant.window,
        fun _ => a, fun _ => a⟩ : SIInstance Ω A) := rfl
  rw [he, D.run_round _ rfl rfl]
  ext τ
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- A nontrivial incoming coset makes the direct substitution fail, even on
constant strings: the old round returns `G*`, while the requested answer is `σG*`. -/
theorem AlignDominantRoundData.run_round_coset_const_ne (D : AlignDominantRoundData Ω)
    (a : A) (σ : Perm Ω) (hσ : σ ∉ D.toAlignDominant.Gs) :
    let I : SIInstance Ω A :=
      ⟨σ • (D.toAlignDominant.Gs : Set (Perm Ω)), D.toAlignDominant.window,
        fun _ => a, fun _ => a⟩
    (D.round I).run ≠ I.answer := by
  dsimp only
  rw [D.run_round_const]
  intro he
  have h1 : (1 : Perm Ω) ∈
      (⟨σ • (D.toAlignDominant.Gs : Set (Perm Ω)), D.toAlignDominant.window,
        fun _ => a, fun _ => a⟩ : SIInstance Ω A).answer := by
    rw [← he]
    exact D.toAlignDominant.Gs.one_mem
  have hi : σ⁻¹ ∈ D.toAlignDominant.Gs := by
    have hk := h1.1
    rw [mem_perm_smul_set] at hk
    simpa using hk
  exact hσ (by simpa using D.toAlignDominant.Gs.inv_mem hi)

end Babai
