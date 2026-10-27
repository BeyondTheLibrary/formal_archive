/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the sound-test routine against the aligned round of Sec. 15.
-/
import Workspace.Algo.AlignTransfer
import Workspace.Algo.EvaluatorQS

/-!
# The two halves of the final statement, at once

Two sessions built two halves of the top statement, and the final assembly needs both.

* `Algo.Round.runQ_eq_answer_align` (`Workspace/Algo/AlignTransfer.lean`) puts the alignment
  step of Remark 11.1.4 in the middle: the machine builds coset instances, the mathematical
  layer reads group instances, and the two agree by Eq. (59).  It is stated for
  `Algo.Round.RunCostQ`, whose test **decides** well-formedness.
* `Algo.Round.runQS_eq_answer` (`Workspace/Algo/EvaluatorQS.lean`) replaces that test by a
  **sound** one (`Algo.Round.RunCostQS`), which is what the master round can supply, at the
  price of one hypothesis at the root: the instance passes the test.

This file is the two together.  Nothing new is argued: the chain of
`Workspace/Algo/EvaluatorN.lean` is repeated once for the sound-test routine
(`Algo.Round.runQS_eq_answerN`), and the alignment is inserted exactly as in
`Workspace/Algo/AlignTransfer.lean`.

## Main results

* `Algo.Round.runQS_eq_answerN` — the sound-test routine with a node-dependent decoder;
* `Algo.Round.runQS_eq_answer_align` — the sound-test routine against the aligned round: it
  returns a raw answer that the **plain** decoder sends to the answer of the coset instance
  the machine holds.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

namespace Round

variable {R : Round ι ω α} [Enc ι] [Enc ω] [Enc α]

/-- **The sound-test routine answers the instance**, with a node-dependent decoder.

This is `Algo.Round.runQ_eq_answerN` with `Algo.Round.RunCostQ` replaced by
`Algo.Round.RunCostQS` and the hypothesis `R.WF I` replaced by the stronger `C.wfCheck I =
true`, exactly as `Algo.Round.runQS_eq_answer` does for the constant decoder.  The proof is
the same: soundness gives `R.WF I` back, the evaluator is run at its own round count, and
`Algo.Round.runQS_eq_evaluate` names that run. -/
theorem runQS_eq_answerN {κ : Type*} (C : RunCostQS R) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : C.wfCheck I = true) (hf : R.measure I < f) :
    ∃ a : α, R.runQS C c₁ I = some a ∧ decA I a = (M.inst (decI I)).answer := by
  have hwf : R.WF I := C.wfCheck_sound I hI
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hwf)
    simpa [roundCount] using this
  obtain ⟨a, ha, hdec⟩ :=
    evaluate_eq_answerN R M himpl hgrp hrank hlift hmono c₁ hq f
      (roundCount c₁ (R.ground I)) I hwf hf hle
  exact ⟨a, by rw [R.runQS_eq_evaluate C c₁ I hI]; exact ha, hdec⟩

/-- **The sound-test routine answers the instance, in the coset form the machine holds.**

`Algo.Round.runQ_eq_answer_align` with `Algo.Round.RunCostQ` replaced by
`Algo.Round.RunCostQS`: the round `R` is a coset-form round implementing `ρ` with the plain
decoder `decA` over the coset instances `instC`, the round `M` of Sec. 15 holds the aligned
instances and the aligned step, and the routine returns a raw answer that `decA` sends to the
answer of the **coset** instance.  At the root the shift cancels against Eq. (59)
(`Algo.eq_answer_of_alignDec`), so no hypothesis on `Babai.cosetRepOf` is needed.

This is the form `Algo.siWorkspaceRoutine_of_normQS_run` consumes. -/
theorem runQS_eq_answer_align {κ : Type*} (R : Round ι ω α) (C : RunCostQS R) {decI : ι → κ}
    {instC : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))} (M : MasterStep Ω A κ)
    (hMinst : ∀ I : ι, M.inst (decI I) = alignInst (instC (decI I)))
    (hMstep : ∀ I : ι, M.step (decI I) = alignRed (instC (decI I)) (ρ (decI I)))
    (himpl : Implements R decI instC decA ρ)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : C.wfCheck I = true) (hf : R.measure I < f) :
    ∃ a : α, R.runQS C c₁ I = some a ∧ decA a = (instC (decI I)).answer := by
  have himplN : ImplementsN R decI M.inst (alignDec (fun J => instC (decI J)) decA) M.step := by
    intro I' hI'
    rw [show (fun J => M.inst (decI J)) = fun J => alignInst (instC (decI J)) from
        funext hMinst, hMstep I']
    exact implementsN_align himpl I' hI'
  obtain ⟨a, ha, hdec⟩ :=
    runQS_eq_answerN C M himplN hgrp hrank hlift hmono c₁ hq hwin f I hI hf
  rw [hMinst I] at hdec
  exact ⟨a, ha, eq_answer_of_alignDec (I₀ := instC (decI I)) hdec⟩

end Round

end Algo

#print axioms Algo.Round.runQS_eq_answerN
#print axioms Algo.Round.runQS_eq_answer_align
