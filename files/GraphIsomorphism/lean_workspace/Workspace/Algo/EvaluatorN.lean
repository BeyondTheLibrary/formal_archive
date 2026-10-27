/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the evaluator against a round with a node-dependent answer decoder.
-/
import Workspace.Algo.RoundN
import Workspace.Algo.EvaluatorQ

/-!
# The evaluator against a node-dependent decoder

`Workspace/Algo/RoundN.lean` writes the link between a raw round and a mathematical round
with an answer decoder `decA : ι → α → Set (Equiv.Perm Ω)` that may depend on the node.  The
evaluator itself does not change at all: it never decodes anything.  What changes is the
last three statements of the chain, which name the decoder in their conclusion.

This file is those three statements.  Each proof is the old one with
`Algo.Round.nodes_le_quasiPoly` replaced by `Algo.Round.nodes_le_quasiPolyN` and
`Algo.roundValue_eq` by `Algo.roundValue_eqN`.

## Main results

* `Algo.Round.evaluate_eq_answerN` — the depth-first evaluator returns a raw answer that
  `decA I` sends to `Iso^Δ_K(x,y)`;
* `Algo.Round.evaluate_roundCount_eq_answerN` — the same at the round count the machine
  computes;
* `Algo.Round.runQ_eq_answerN` — the same for the packaged routine `Algo.Round.runQ`, which
  is the form `Algo.siWorkspaceRoutine_of_normQ_run` consumes.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

namespace Round

/-- **The evaluator answers the instance.**  `Algo.Round.evaluate_eq_answer` with a
node-dependent decoder. -/
theorem evaluate_eq_answerN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f N : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f)
    (hN : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1 ≤ N) :
    ∃ a : α, R.evaluate N I = some a ∧ decA I a = (M.inst (decI I)).answer := by
  have hnodes : R.nodes f I
      ≤ 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) :=
    R.nodes_le_quasiPolyN (decA := decA) M himpl hgrp hrank hlift hmono c₁ hq f I hI hf
  have hsteps : R.subSteps f I ≤ N := by
    have := R.subSteps_le f I
    have h3 : 3 * R.nodes f I
        ≤ 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) :=
      Nat.mul_le_mul_left 3 hnodes
    omega
  exact ⟨R.value f I, R.evaluate_eq_value f N I hI hf hsteps,
    roundValue_eqN R himpl (fun I' hI' => M.round_correct (decI I') (hgrp I' hI')) f I hI hf⟩

/-- **The evaluator at its own round count.**  `Algo.Round.evaluate_roundCount_eq_answer`
with a node-dependent decoder. -/
theorem evaluate_roundCount_eq_answerN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    ∃ a : α, R.evaluate (roundCount c₁ (M.inst (decI I)).windowSize) I = some a ∧
      decA I a = (M.inst (decI I)).answer :=
  evaluate_eq_answerN R M himpl hgrp hrank hlift hmono c₁ hq f _ I hI hf (le_refl _)

variable [Enc ι] [Enc ω] [Enc α]

/-- **The routine answers the instance.**  `Algo.Round.runQ_eq_answer` with a node-dependent
decoder.  This is the statement the bridge `Algo.siWorkspaceRoutine_of_normQ_run` is fed
through its hypothesis `hdec`. -/
theorem runQ_eq_answerN {κ : Type*} (R : Round ι ω α) (C : RunCostQ R) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    ∃ a : α, R.runQ C c₁ I = some a ∧ decA I a = (M.inst (decI I)).answer := by
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hI)
    simpa [roundCount] using this
  obtain ⟨a, ha, hdec⟩ :=
    evaluate_eq_answerN R M himpl hgrp hrank hlift hmono c₁ hq f
      (roundCount c₁ (R.ground I)) I hI hf hle
  exact ⟨a, by rw [R.runQ_eq_evaluate C c₁ I hI]; exact ha, hdec⟩

end Round

end Algo

#print axioms Algo.Round.runQ_eq_answerN
