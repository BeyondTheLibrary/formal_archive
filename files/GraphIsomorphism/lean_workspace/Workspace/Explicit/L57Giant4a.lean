/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the round of Corollary 12.0.10
at outcome (2a) inside lines 5–7 of the Master (Sec. 15), bounded at the degree. Not part of the
faithful formalization.
-/
import Workspace.Explicit.CarriersLow
import Workspace.Algo.AggNodeLine57GiantRAM

/-!
# The giant branch of lines 5–7: the round of line 4 with the supplied alignment

At outcome (2a) the round of lines 5–7 runs `Algo.top4aRound` on the node
`Algo.aggnL57GNode` with the answer routine `Algo.l57gSolve` (the constant `none`: the node is
not a window node). All its routines are polynomial, so they are bounded at the degree with any
exponent (`Explicit.TN.top4aFinish_l57g` and the others). The states of the round are bounded
for every state and every answer (`Algo.top4Combine_stored`), so the state bound
`Explicit.top4a_state_q5` needs neither reachability nor a bound on the answers.

The precondition is `Explicit.G4Pre u v e f n I`: the node passes the check of
`Algo.top4aCheck u v e f` (part of `Algo.aggnL57GOn`) and its string has at most `n` letters.
The routines need no precondition; the state bound uses both conjuncts.
-/

set_option synthInstance.maxSize 2048

namespace Explicit

open RAM Algo

/-- The node of the giant branch at degree `n`: it passes the check of outcome (2a) and its
string has at most `n` letters. -/
def G4Pre (u v e f n : ℕ) (I : Top4aNode) : Prop :=
  top4aCheck u v e f I = true ∧ (top4X I.1.1).length ≤ n

namespace TN

variable (k : ℕ) {Pre : ℕ → Top4aNode → Prop}

/-- **The answer of the round at outcome (2a)**, bounded at the degree (it is polynomial: the
answer routine `Algo.l57gSolve` is constant). -/
theorem top4aFinish_l57g :
    TN (top4aFinish l57gSolve) (fun n z => Pre n z.1) k :=
  TN.ofPoly (polyFun_top4aFinishP (polyFun_const none)) _ k

theorem top4aInit : TN Algo.top4aInit Pre k := TN.ofPoly polyFun_top4aInit _ k

theorem top4aChild (e f : ℕ) : TN (Algo.top4aChild e f) (fun n z => Pre n z.1) k :=
  TN.ofPoly (polyFun_top4aChild e f) _ k

theorem top4aCombine : TN Algo.top4aCombine (fun n z => Pre n z.1) k :=
  TN.ofPoly polyFun_top4aCombine _ k

theorem l57gW4 : TN Algo.l57gW4 Pre k := TN.ofPoly polyFun_l57gW4 _ k

end TN

/-- **The states of the round at outcome (2a), with an explicit exponent**: at a node with
`G4Pre u v e f n`, the first state, every state `Algo.top4aCombine` produces (from any state
and any answer) and the answer have size at most `2^{K (log₂ n + 2)^5}`. -/
theorem top4a_state_q5 (u v e f : ℕ) : ∃ K, ∀ n (I : Top4aNode), G4Pre u v e f n I →
    Enc.size (Algo.top4aInit I) ≤ 2 ^ (K * lg n ^ 5) ∧
    (∀ j s A, Enc.size (Algo.top4aCombine (I, j, s, A)) ≤ 2 ^ (K * lg n ^ 5)) ∧
    (∀ s, Enc.size (top4aFinish l57gSolve (I, s)) ≤ 2 ^ (K * lg n ^ 5)) := by
  obtain ⟨K₁, h₁⟩ := q5_of_polyBound (polyBound_top4Bound u v e f)
  obtain ⟨K₂, h₂⟩ := q5_of_polyBound polyBound_chainBound
  refine ⟨K₁ + K₂, fun n I hI => ?_⟩
  have hwf : Top4aWF u v e f I := (top4aCheck_spec u v e f I).1 hI.1
  have hC : Enc.size I.1.1 ≤ topcsContextCap u v (top4X I.1.1).length := hwf.1.1
  have hB : top4Bound u v e f (top4X I.1.1).length ≤ 2 ^ ((K₁ + K₂) * lg n ^ 5) :=
    ((mono_top4Bound u v e f hI.2).trans (h₁ n)).trans
      (StateBoundsX.two_pow_mono (Nat.le_add_right _ _) n)
  refine ⟨(top4Stored_size hC (top4Init_stored I.1)).trans hB,
    fun j s A => (top4Stored_size hC (top4Combine_stored (I.1, j, s, A))).trans hB,
    fun s => ?_⟩
  exact ((size_top4aFinish I s).trans ((mono_chainBound hI.2).trans (h₂ n))).trans
    (StateBoundsX.two_pow_mono (Nat.le_add_left _ _) n)

end Explicit
