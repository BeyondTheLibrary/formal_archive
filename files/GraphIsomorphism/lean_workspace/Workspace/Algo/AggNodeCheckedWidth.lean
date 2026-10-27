import Workspace.Algo.AggNodeCheckedRAM
import Workspace.Algo.AggNodeCertBounds

/-! # A uniform width bound for the checked certificate carrier

The checked carrier bounds the parent context but does not require a valid
action. Its width still has a quasipolynomial bound. Outside the arity guard
the job list is empty. Inside the guard the factorial and the explicit job
list are both bounded in the size of the context. The context-size bound
then gives a bound in the original domain size.
-/

namespace Algo
open RAM RAM.Targets

private theorem checkedRows_quasiFun (c : ℕ) : QuasiFun (aggnPhaseRows c) :=
  ((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).pair
    ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst))).comp_quasiFun
        (aggQuasiFun_testSetsOn c))

/-- An out-of-guard context has no certificate jobs, even when its action is malformed. -/
theorem aggnPhaseRows_eq_nil_of_not_guard {c : ℕ} {C : AggnPhaseCtx}
    (hg : ¬ C.2.2.2.length ≤ guardBound c C.2.1.length) :
    aggnPhaseRows c C = [] := by
  simp [aggnPhaseRows, aggTestSetsOn, aggTable, aggTabSetUp, hg, tabRead]

/-- The numerical width, not merely its binary encoding, is quasipolynomially bounded. -/
theorem aggnPhaseWidth_bound_in_size (c : ℕ) : ∃ d : ℕ, ∀ C : AggnPhaseCtx,
    aggnPhaseWidth c C ≤ 2 ^ ((Nat.log 2 (Enc.size C) + 2) ^ d) := by
  obtain ⟨d, hs⟩ := (checkedRows_quasiFun c).size
  let P := fun N => 2 * 2 ^ ((Nat.log 2 N + 2) ^ d) *
    (N * (2 ^ ((Nat.log 2 N + 2) ^ (c + 1)) * N))
  have hp : QuasiPolyBound P :=
    ((polyBound_const 2).quasiPoly.mul (quasiPolyBound_witness d)).mul
      (polyBound_id.quasiPoly.mul
        ((quasiPolyBound_witness (c + 1)).mul polyBound_id.quasiPoly))
  obtain ⟨e, he⟩ := hp
  refine ⟨e, fun C => le_trans ?_ (he (Enc.size C))⟩
  by_cases hg : C.2.2.2.length ≤ guardBound c C.2.1.length
  · have hn : C.2.1.length ≤ Enc.size C :=
      (length_le_size C.2.1).trans ((size_fst_le' C.2).trans (size_snd_le' C))
    have ht : C.2.2.2.length ≤ Enc.size C :=
      (length_le_size C.2.2.2).trans
        ((size_snd_le' C.2.2).trans ((size_snd_le' C.2).trans (size_snd_le' C)))
    have hguard : C.2.2.2.length ≤ guardBound c (Enc.size C) := by
      apply hg.trans
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hn) 1) c
    have hf := aggnFactorial_le c ht hguard
    have hr := (length_le_size (aggnPhaseRows c C)).trans (hs C)
    have hj : (aggnPhaseJobs c C).length ≤ 2 * 2 ^ ((Nat.log 2 (Enc.size C) + 2) ^ d) := by
      simpa only [aggnPhaseJobs, List.flatMap_cons, List.flatMap_nil, List.length_append,
        List.length_map, List.length_nil, Nat.add_zero, two_mul] using
          Nat.mul_le_mul_left 2 hr
    exact Nat.mul_le_mul hj (Nat.mul_le_mul hn (Nat.mul_le_mul hf hn))
  · simp only [aggnPhaseWidth, aggnPhaseJobs, aggnPhaseRows_eq_nil_of_not_guard hg,
      List.map_nil, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.length_nil,
      Nat.zero_mul, Nat.zero_le]

/-- The width clause required by `CostQ`, for every checked well-formed input.
No action, reachability, or state hypothesis is used. -/
theorem aggnChecked_width_bound (c : ℕ) : ∃ W : ℕ → ℕ,
    QuasiPolyBound W ∧ Monotone W ∧ ∀ (n : ℕ) (I : AggnPhaseNode),
      (aggnCheckedRound c n).WF I →
        (aggnCheckedRound c n).width I ≤ W ((aggnCheckedRound c n).ground I) := by
  obtain ⟨d, hd⟩ := aggnPhaseWidth_bound_in_size c
  let W := fun n => 2 ^ ((Nat.log 2 (2 * aggnCheckedWindowBound n) + 2) ^ d)
  refine ⟨W, (quasiPolyBound_witness d).comp_poly
    ((polyBound_const 2).mul aggnPolyBound_checkedWindow), ?_, ?_⟩
  · intro a b hab
    exact quasiPolyBound_witness_mono d
      (Nat.mul_le_mul_left 2 (aggnMono_checkedWindowBound hab))
  · intro n I hI
    have h : aggnPhaseWidth c I.1 ≤ W n := (hd I.1).trans
      (quasiPolyBound_witness_mono d hI.2.1)
    change I.2.elim (aggnPhaseWidth c I.1) (fun _ => 0) ≤ W I.1.2.1.length
    rw [hI.1]
    cases I.2 with
    | none => exact h
    | some _ => exact Nat.zero_le _

end Algo

#print axioms Algo.aggnPhaseWidth_bound_in_size
#print axioms Algo.aggnChecked_width_bound
