import Workspace.Algo.FamilyEvaluator
import Workspace.SplitOrJohnson.Depth

/-! The number of calls must count the stored list, including repeated
children. A bound on the set of different children would not suffice.
We use the paper's multiplicative budget for this list, and the strictly
decreasing measure to pay for the nodes along each branch. -/
namespace Algo
open RAM Babai
namespace Round
variable {ι ω α : Type*} (R : Round ι ω α)

theorem loopCalls_length_le (rec : ι → α) (I : ι) :
    ∀ w j s, (R.loopCalls rec w I j s).length ≤ w := by
  intro w
  induction w with
  | zero => intros; simp
  | succ w ih =>
    intro j s
    cases h : R.child (I,j,s) with
    | none => rw [R.loopCalls_succ_none h]; simp
    | some J =>
      rw [R.loopCalls_succ_some h,List.length_cons]
      exact Nat.add_le_add_right (ih _ _) 1

theorem roundCalls_length_le (f : ℕ) (I : ι) :
    (R.roundCalls f I).length ≤ R.width I := R.loopCalls_length_le _ I _ _ _

theorem mem_loopCalls_child (rec : ι → α) (I : ι) :
    ∀ w j s J, J ∈ R.loopCalls rec w I j s →
      ∃ k t, R.child (I,k,t) = some J := by
  intro w
  induction w with
  | zero => intro j s J hJ; simp at hJ
  | succ w ih =>
    intro j s J hJ
    cases hc : R.child (I,j,s) with
    | none => rw [R.loopCalls_succ_none hc] at hJ; simp at hJ
    | some J' =>
      rw [R.loopCalls_succ_some hc] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact ⟨j,s,hc⟩
      · exact ih _ _ _ hJ

theorem mem_roundCalls_child {f : ℕ} {I J : ι} (hJ : J ∈ R.roundCalls f I) :
    ∃ k t, R.child (I,k,t) = some J := R.mem_loopCalls_child _ I _ _ _ _ hJ

theorem nodes_le_budget_on (P : ι → Prop) (budget : ι → ℕ)
    (hwf : ∀ I, P I → R.WF I)
    (hpres : ∀ f I J, P I → J ∈ R.roundCalls f I → P J)
    (hpos : ∀ I, P I → 1 ≤ budget I)
    (hsum : ∀ f I, P I → ((R.roundCalls f I).map budget).sum ≤ budget I) :
    ∀ f I, P I → R.nodes f I ≤ R.measure I * budget I := by
  intro f
  induction f with
  | zero => intro I _; simp
  | succ f ih =>
    intro I hI
    have hterm : ∀ J ∈ R.roundCalls f I,
        1 + R.nodes f J ≤ R.measure I * budget J := by
      intro J hJ
      have hm := (R.mem_roundCalls (hwf I hI) J hJ).2
      have hw := hpres f I J hI hJ
      have hc := ih J hw
      have hp := hpos J hw
      have hm := Nat.mul_le_mul_right (budget J) (show R.measure J + 1 ≤ R.measure I by omega)
      nlinarith
    have heq : ∀ L : List ι,
        (L.map (fun J => 1 + R.nodes f J)).sum = L.length + (L.map (R.nodes f)).sum := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega
    rw [R.nodes_succ,← heq]
    calc ((R.roundCalls f I).map (fun J => 1 + R.nodes f J)).sum
        ≤ ((R.roundCalls f I).map (fun J => R.measure I * budget J)).sum :=
          List.sum_le_sum hterm
      _ = R.measure I * ((R.roundCalls f I).map budget).sum := List.sum_map_mul_left _ _ _
      _ ≤ R.measure I * budget I := Nat.mul_le_mul_left _ (hsum f I hI)

theorem nodes_le_budget (budget : ι → ℕ)
    (hpos : ∀ I, R.WF I → 1 ≤ budget I)
    (hsum : ∀ f I, R.WF I → ((R.roundCalls f I).map budget).sum ≤ budget I) :
    ∀ f I, R.WF I → R.nodes f I ≤ R.measure I * budget I :=
  R.nodes_le_budget_on R.WF budget (fun _ h => h)
    (fun _ _ J hI hJ => (R.mem_roundCalls hI J hJ).1) hpos hsum

/-- A semantic invariant can be stronger than the raw termination check.
The one-turn proof is used only after its recursive calls have been proved. -/
theorem value_spec_on (P : ι → Prop) (Good : ι → α → Prop)
    (hstep : ∀ I, P I → ∀ rec : ι → α,
      (∀ J, P J → R.measure J < R.measure I → Good J (rec J)) →
      Good I (R.loopAux rec (R.width I) I 0 (R.init I))) :
    ∀ f I, R.measure I < f → P I → Good I (R.value f I) := by
  intro f
  induction f with
  | zero => intro I hf _; omega
  | succ f ih =>
    intro I hf hI
    rw [R.value_succ]
    exact hstep I hI (R.value f) (fun J hJ hm => ih J (by omega) hJ)

/-- A per-child multiplicative bound controls the sum only when it also
bounds the length of the actual list of calls. -/
theorem roundBudget_sum_le_on (P : ι → Prop) (budget factor : ι → ℕ)
    (hfactor : ∀ I, P I → 0 < factor I)
    (hwidth : ∀ I, P I → R.width I ≤ factor I)
    (hchild : ∀ f I J, P I → J ∈ R.roundCalls f I →
      factor I * budget J ≤ budget I)
    (f : ℕ) (I : ι) (hI : P I) :
    ((R.roundCalls f I).map budget).sum ≤ budget I := by
  have hentry : ∀ J ∈ R.roundCalls f I, budget J ≤ budget I / factor I := by
    intro J hJ
    apply (Nat.le_div_iff_mul_le (hfactor I hI)).2
    simpa only [Nat.mul_comm] using hchild f I J hI hJ
  calc ((R.roundCalls f I).map budget).sum
      ≤ ((R.roundCalls f I).map (fun _ => budget I / factor I)).sum :=
        List.sum_le_sum hentry
    _ = (R.roundCalls f I).length * (budget I / factor I) := by simp
    _ ≤ factor I * (budget I / factor I) :=
        Nat.mul_le_mul_right _ ((R.roundCalls_length_le f I).trans (hwidth I hI))
    _ ≤ budget I := Nat.mul_div_le _ _

theorem roundBudget_sum_le (budget factor : ι → ℕ)
    (hfactor : ∀ I, R.WF I → 0 < factor I)
    (hwidth : ∀ I, R.WF I → R.width I ≤ factor I)
    (hchild : ∀ f I J, R.WF I → J ∈ R.roundCalls f I →
      factor I * budget J ≤ budget I)
    (f : ℕ) (I : ι) (hI : R.WF I) :
    ((R.roundCalls f I).map budget).sum ≤ budget I :=
  R.roundBudget_sum_le_on R.WF budget factor hfactor hwidth hchild f I hI

/-- The two forms of major progress in Section 9.5 pay for every stored
recursive call, with the same cost function as the mathematical proof. -/
theorem splitBudget_child (blocks bit : ι → ℕ) {I J : ι} (hground : R.ground J ≤ R.ground I)
    (hbit : bit J ≤ 1)
    (hprogress : (0 < blocks I ∧ 10 * blocks J ≤ 9 * blocks I) ∨
      (blocks J ≤ blocks I ∧ bit I = 1 ∧ bit J = 0)) :
    turnCost (R.ground I) * costFun (R.ground J) (blocks J) (bit J) ≤
      costFun (R.ground I) (blocks I) (bit I) := by
  rcases hprogress with ⟨hp,hr⟩ | ⟨hr,hi,hj⟩
  · exact turnCost_mul_costFun_le hground hp hr hbit
  · rw [hi,hj]
    exact turnCost_mul_costFun_le_of_hint hground hr

end Round
end Algo
