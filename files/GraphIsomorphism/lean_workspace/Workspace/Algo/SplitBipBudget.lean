import Workspace.Algo.SplitBipRecursionCost

/-! The stored families may need a larger fixed per-turn bound than the
paper's displayed estimate. Its precise exponent does not affect the
argument of Section 9.5: at most two turns are paid for each significant
block reduction. This file keeps that argument with any fixed base. -/
namespace Algo
open RAM Babai

def sbipBudget (base blocks bit : ℕ) : ℕ := base ^ (2 * steps09 blocks + 1 + bit)
def sbipBudgetBound (base n : ℕ) : ℕ := base ^ (14 * (Nat.log 2 n + 1) + 2)

theorem sbipBudget_pos {base : ℕ} (hb : 1 ≤ base) (blocks bit : ℕ) :
    1 ≤ sbipBudget base blocks bit := one_le_pow₀ hb

theorem sbipBudget_le {base n blocks bit : ℕ} (hb : 1 ≤ base)
    (hn : blocks ≤ n) (hbit : bit ≤ 1) :
    sbipBudget base blocks bit ≤ sbipBudgetBound base n := by
  apply Nat.pow_le_pow_right hb
  have hs := (steps09_le_log blocks).trans
    (Nat.mul_le_mul_left 7 (Nat.add_le_add_right (Nat.log_mono_right hn) 1))
  omega

theorem sbipBudget_drop {base blocks child bit childBit : ℕ} (hb : 1 ≤ base)
    (hpos : 0 < blocks) (hred : 10 * child ≤ 9 * blocks) (hbit : childBit ≤ 1) :
    base * sbipBudget base child childBit ≤ sbipBudget base blocks bit := by
  obtain ⟨k,rfl⟩ : ∃ k, blocks = k+1 := ⟨blocks-1,by omega⟩
  have hc : child ≤ reduce09 (k+1) :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hs : steps09 child + 1 ≤ steps09 (k+1) := by
    rw [steps09_succ]
    exact Nat.add_le_add_right (steps09_mono _ _ hc) 1
  change base * base ^ (2 * steps09 child + 1 + childBit) ≤ _
  rw [← pow_succ']
  exact Nat.pow_le_pow_right hb (by omega)

theorem sbipBudget_hint {base blocks child : ℕ} (hb : 1 ≤ base) (hc : child ≤ blocks) :
    base * sbipBudget base child 0 ≤ sbipBudget base blocks 1 := by
  change base * base ^ (2 * steps09 child + 1 + 0) ≤ _
  rw [← pow_succ']
  have hs := steps09_mono _ _ hc
  exact Nat.pow_le_pow_right hb (by omega)

theorem quasiPolyBound_sbipBudgetBound {base : ℕ → ℕ} (hb : QuasiPolyBound base) :
    QuasiPolyBound (fun n => sbipBudgetBound (base n) n) := by
  obtain ⟨c,hc⟩ := hb
  refine ⟨c+5,fun n => ?_⟩
  have hlin : 14 * (Nat.log 2 n + 1) + 2 ≤ 16 * (Nat.log 2 n + 2) := by omega
  have h16 : 16 ≤ (Nat.log 2 n + 2)^4 :=
    (show 16 = 2^4 by norm_num).le.trans (Nat.pow_le_pow_left (by omega) 4)
  calc sbipBudgetBound (base n) n
      ≤ (2 ^ ((Nat.log 2 n + 2)^c)) ^ (14 * (Nat.log 2 n + 1) + 2) :=
        Nat.pow_le_pow_left (hc n) _
    _ = 2 ^ ((Nat.log 2 n + 2)^c * (14 * (Nat.log 2 n + 1) + 2)) := by rw [← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 n + 2)^(c+5)) := by
      apply Nat.pow_le_pow_right (by norm_num)
      calc (Nat.log 2 n + 2)^c * (14 * (Nat.log 2 n + 1) + 2)
          ≤ (Nat.log 2 n + 2)^c * (16 * (Nat.log 2 n + 2)) := Nat.mul_le_mul_left _ hlin
        _ ≤ (Nat.log 2 n + 2)^c * ((Nat.log 2 n + 2)^4 * (Nat.log 2 n + 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h16)
        _ = (Nat.log 2 n + 2)^(c+5) := by rw [pow_add]; ring

theorem exists_roundCount_of_quasiPolyBound {q : ℕ → ℕ} (hq : QuasiPolyBound q) :
    ∃ c, ∀ n, q n ≤ Round.roundCount c n := by
  obtain ⟨c,hc⟩ := hq
  refine ⟨c,fun n => (hc n).trans ?_⟩
  have he : (Nat.log 2 n + 2)^c ≤ 30 * (Nat.log 2 n + 2)^(c+2) := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ Nat.log 2 n + 2 by omega)
      (show c ≤ c+2 by omega)
    omega
  have hp : 2 ^ ((Nat.log 2 n + 2)^c) ≤
      2 ^ (30 * (Nat.log 2 n + 2)^(c+2)) := Nat.pow_le_pow_right (by norm_num) he
  unfold Round.roundCount
  omega

end Algo
