/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the depth-first
evaluator run for an explicit number of steps. Not part of the faithful formalization.
-/
import Workspace.Explicit.Top.Count

/-!
# The evaluator with an explicit step count

`Algo.Round.runQ` runs `Algo.Round.roundCount c₁ n = 3·2^{30(log₂ n+2)^{c₁+2}}+1` steps, with
`c₁` from an existential. Here the count is a parameter `N : ℕ → ℕ` of the ground, and the run
is correct as soon as `3·nodes + 1 ≤ N (ground)` at the root.

* `Explicit.stepCountE`, `Explicit.runE`: the count and the run;
* `Explicit.runE_eq_answer`: the proof of `Algo.Round.runQ_eq_answerG` with the node bound as
  a hypothesis.
-/

universe u v

namespace Explicit

open Algo Babai RAM

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

section Run
variable [Enc ι] [Enc ω] [Enc α]

/-- The number of steps: `N (ground I)` on an instance that passes the test, none otherwise. -/
def stepCountE (R : Algo.Round ι ω α) (C : Algo.Round.RunCostQ R) (N : ℕ → ℕ) (I : ι) : ℕ :=
  if C.wfCheck I then N (R.ground I) else 0

/-- **The evaluator with the step count `N`.** -/
def runE (R : Algo.Round ι ω α) (C : Algo.Round.RunCostQ R) (N : ℕ → ℕ) (I : ι) : Option α :=
  ((R.stepDFS)^[stepCountE R C N I] (R.startState I)).2

theorem stepCountE_of_wf (R : Algo.Round ι ω α) (C : Algo.Round.RunCostQ R) (N : ℕ → ℕ) {I : ι}
    (hI : R.WF I) : stepCountE R C N I = N (R.ground I) := by
  rw [stepCountE, if_pos ((C.wfCheck_eq_true I).2 hI)]

variable (R : Algo.Round ι ω α) {Good : ι → Prop} {Ch : ι → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))} {win param : ι → ℕ} {q : ℕ → ℕ}

/-- **The run answers every good node once the count covers the tree.** The proof of
`Algo.Round.runQ_eq_answerG`, with the node bound as the hypothesis `hN`. -/
theorem runE_eq_answer (C : Algo.Round.RunCostQ R) (N : ℕ → ℕ)
    (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q)
    (I : ι) (hG : Good I) (hI : R.WF I)
    (hN : 3 * R.nodes (R.measure I + 1) I + 1 ≤ N (R.ground I)) :
    ∃ s : ω, runE R C N I = some (R.finish (I, s)) ∧
      decA I (R.finish (I, s)) = (decI I).answer := by
  have hsteps : R.subSteps (R.measure I + 1) I ≤ N (R.ground I) :=
    (R.subSteps_le (R.measure I + 1) I).trans hN
  have hval := R.evaluate_eq_value (R.measure I + 1) _ I hI (Nat.lt_succ_self _) hsteps
  have hdec := roundValue_eqG R himpl hP.good_child hρ (R.measure I + 1) I hG hI
    (Nat.lt_succ_self _)
  obtain ⟨s, hs⟩ := R.loopAux_eq_finish (R.value (R.measure I)) (R.width I) I 0 (R.init I)
  rw [R.value_succ, hs] at hval hdec
  refine ⟨s, ?_, hdec⟩
  rw [runE, stepCountE_of_wf R C N hI, ← R.evaluate_eq_iterate]
  exact hval

end Run

end Explicit
