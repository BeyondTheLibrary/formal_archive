import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Explicit running times: the two-scale bound

Part 1 of the explicit running time of Theorem 1.1.1 (see `Explicit/DESIGN.md`).

A routine runs in *two-scale* time when its cost on an input `a` is at most

`tsB A k b D n = 2 ^ (A * (log₂ D + 2) ^ k) * (n + 1) ^ b`,

where `n` is the encoded size of `a` and `D` a *degree* read off `a`. The first factor is
quasipolynomial in the degree, with an explicit exponent `k`; the second is polynomial in the
size. This file holds the arithmetic of this bound only; the machine class is in
`Explicit/NodeMachine.lean`.
-/

namespace Explicit

/-- `log₂ D + 2`, the base of the quasipolynomial factor. It is at least `2`. -/
def lg (D : ℕ) : ℕ := Nat.log 2 D + 2

/-- **The two-scale bound** `2 ^ (A * (log₂ D + 2) ^ k) * (n + 1) ^ b`. -/
def tsB (A k b D n : ℕ) : ℕ := 2 ^ (A * lg D ^ k) * (n + 1) ^ b

theorem two_le_lg (D : ℕ) : 2 ≤ lg D := by unfold lg; omega

theorem one_le_lg_pow (D k : ℕ) : 1 ≤ lg D ^ k :=
  Nat.one_le_pow _ _ (by have := two_le_lg D; omega)

theorem lg_mono {D D' : ℕ} (h : D ≤ D') : lg D ≤ lg D' := by
  unfold lg; have := Nat.log_mono_right (b := 2) h; omega

theorem lg_pow_mono {D D' k k' : ℕ} (hD : D ≤ D') (hk : k ≤ k') : lg D ^ k ≤ lg D' ^ k' :=
  (Nat.pow_le_pow_left (lg_mono hD) k).trans
    (Nat.pow_le_pow_right (by have := two_le_lg D'; omega) hk)

theorem one_le_tsB (A k b D n : ℕ) : 1 ≤ tsB A k b D n := by
  unfold tsB
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity))

theorem tsB_mono {A A' k k' b b' D D' n n' : ℕ} (hA : A ≤ A') (hk : k ≤ k') (hb : b ≤ b')
    (hD : D ≤ D') (hn : n ≤ n') : tsB A k b D n ≤ tsB A' k' b' D' n' := by
  unfold tsB
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hA (lg_pow_mono hD hk))
  · exact (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) hb)

theorem tsB_zero_k (A b D D' n : ℕ) : tsB A 0 b D n = tsB A 0 b D' n := by
  simp [tsB]

theorem tsB_mul (A A' k b b' D n : ℕ) :
    tsB A k b D n * tsB A' k b' D n = tsB (A + A') k (b + b') D n := by
  unfold tsB
  rw [add_mul, pow_add, pow_add]
  ring

theorem two_pow_le_tsB (c k D n : ℕ) : 2 ^ c ≤ tsB c k 0 D n := by
  unfold tsB
  simp only [pow_zero, mul_one]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (one_le_lg_pow D k))

theorem const_le_tsB (c k D n : ℕ) : c ≤ tsB c k 0 D n :=
  (Nat.lt_two_pow_self).le.trans (two_pow_le_tsB c k D n)

theorem self_le_tsB (k D n : ℕ) : n ≤ tsB 0 k 1 D n := by
  unfold tsB; simp

theorem succ_le_tsB (k D n : ℕ) : n + 1 ≤ tsB 0 k 1 D n := by
  unfold tsB; simp

/-- A constant factor goes into the exponent. -/
theorem mul_tsB_le (c A k b D n : ℕ) : c * tsB A k b D n ≤ tsB (A + c) k b D n := by
  have h := Nat.mul_le_mul_right (tsB A k b D n) (const_le_tsB c k D n)
  rw [tsB_mul, Nat.zero_add, Nat.add_comm c A] at h
  exact h

/-- Two bounds add up to a bound. -/
theorem tsB_add_le (A A' k b b' D n : ℕ) :
    tsB A k b D n + tsB A' k b' D n ≤ tsB (A + A' + 2) k (b + b') D n := by
  have h1 := tsB_mono (A' := A + A') (k' := k) (b' := b + b') (D' := D) (n' := n)
    (Nat.le_add_right A A') le_rfl (Nat.le_add_right b b') le_rfl (le_refl n)
  have h2 := tsB_mono (A' := A + A') (k' := k) (b' := b + b') (D' := D) (n' := n)
    (Nat.le_add_left A' A) le_rfl (Nat.le_add_left b' b) le_rfl (le_refl n)
  have h3 := mul_tsB_le 2 (A + A') k (b + b') D n
  omega

/-- **Composition of bounds**: a bound evaluated at a bounded size. -/
theorem tsB_comp_le (A A' k b b' D n : ℕ) :
    tsB A' k b' D (tsB A k b D n) ≤ tsB (A' + b' * (A + 1)) k (b * b') D n := by
  unfold tsB
  set L := lg D ^ k with hL
  have hL1 : 1 ≤ L := one_le_lg_pow D k
  have h1 : 2 ^ (A * L) * (n + 1) ^ b + 1 ≤ 2 ^ ((A + 1) * L) * (n + 1) ^ b := by
    have hp : 1 ≤ (n + 1) ^ b := Nat.one_le_pow _ _ (by omega)
    have hq : 2 ^ ((A + 1) * L) = 2 ^ (A * L) * 2 ^ L := by rw [add_mul, one_mul, pow_add]
    have h2 : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
    have h3 : 1 ≤ 2 ^ (A * L) := Nat.one_le_two_pow
    rw [hq]
    nlinarith [Nat.mul_le_mul h3 hp]
  calc 2 ^ (A' * L) * (2 ^ (A * L) * (n + 1) ^ b + 1) ^ b'
      ≤ 2 ^ (A' * L) * (2 ^ ((A + 1) * L) * (n + 1) ^ b) ^ b' :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 b')
    _ = 2 ^ ((A' + b' * (A + 1)) * L) * (n + 1) ^ (b * b') := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
        congr 2
        ring

/-- **A polynomial change of degree.** -/
theorem lg_le_of_poly {D D' r₀ r : ℕ} (h : D ≤ 2 ^ r₀ * (D' + 1) ^ r) :
    lg D ≤ (r₀ + 2 * r + 3) * lg D' := by
  have hD' : D' + 1 ≤ 2 ^ (Nat.log 2 D' + 1) := Nat.lt_pow_succ_log_self (by norm_num) D'
  have hE : D ≤ 2 ^ (r₀ + r * (Nat.log 2 D' + 1)) := by
    calc D ≤ 2 ^ r₀ * (D' + 1) ^ r := h
      _ ≤ 2 ^ r₀ * (2 ^ (Nat.log 2 D' + 1)) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD' r)
      _ = 2 ^ (r₀ + r * (Nat.log 2 D' + 1)) := by rw [← pow_mul, ← pow_add, mul_comm]
  have hlog : Nat.log 2 D ≤ r₀ + r * (Nat.log 2 D' + 1) := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0; simp
    · calc Nat.log 2 D ≤ Nat.log 2 (2 ^ (r₀ + r * (Nat.log 2 D' + 1))) := Nat.log_mono_right hE
        _ = _ := Nat.log_pow (by norm_num) _
  unfold lg
  nlinarith

theorem tsB_le_of_poly {A k b D D' n r₀ r : ℕ} (h : D ≤ 2 ^ r₀ * (D' + 1) ^ r) :
    tsB A k b D n ≤ tsB (A * (r₀ + 2 * r + 3) ^ k) k b D' n := by
  unfold tsB
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right (by norm_num)
  rw [mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lg_le_of_poly h) k)

end Explicit
