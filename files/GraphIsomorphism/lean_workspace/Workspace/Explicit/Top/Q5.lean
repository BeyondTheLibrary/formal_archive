/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: bounds of the form
`2^{c (log₂ N + 2)^5}`. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeBound

/-!
# Bounds with exponent 5

`Explicit.Q5 T`: `T N ≤ 2^{c (log₂ N + 2)^5}` for all `N`, for some `c`. The class is closed
under sums, products, fixed powers, and composition with a polynomially bounded function
(`Explicit.lg_le_of_poly`). The final time bound of the Master is shown to be in this class.
-/

namespace Explicit

/-- **Exponent 5**: `T N ≤ 2^{c (log₂ N + 2)^5}` for some `c`. -/
def Q5 (T : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ N, T N ≤ 2 ^ (c * lg N ^ 5)

theorem lg_eq (N : ℕ) : lg N = Nat.log 2 N + 2 := rfl

theorem one_le_lg5 (N : ℕ) : 1 ≤ lg N ^ 5 := one_le_lg_pow N 5

theorem Q5.mono {T T' : ℕ → ℕ} (h : Q5 T') (hT : ∀ N, T N ≤ T' N) : Q5 T := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun N => (hT N).trans (hc N)⟩

theorem q5_const (a : ℕ) : Q5 (fun _ => a) :=
  ⟨a, fun N => (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (one_le_lg5 N)))⟩

theorem Q5.mul {T T' : ℕ → ℕ} (h : Q5 T) (h' : Q5 T') : Q5 (fun N => T N * T' N) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c + c', fun N => ?_⟩
  calc T N * T' N ≤ 2 ^ (c * lg N ^ 5) * 2 ^ (c' * lg N ^ 5) := Nat.mul_le_mul (hc N) (hc' N)
    _ = 2 ^ ((c + c') * lg N ^ 5) := by rw [← pow_add, add_mul]

theorem Q5.add {T T' : ℕ → ℕ} (h : Q5 T) (h' : Q5 T') : Q5 (fun N => T N + T' N) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c + c' + 1, fun N => ?_⟩
  have h1 : 2 ^ (c * lg N ^ 5) ≤ 2 ^ ((c + c') * lg N ^ 5) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have h2 : 2 ^ (c' * lg N ^ 5) ≤ 2 ^ ((c + c') * lg N ^ 5) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have h3 : 2 * 2 ^ ((c + c') * lg N ^ 5) ≤ 2 ^ ((c + c' + 1) * lg N ^ 5) := by
    have : 2 ^ ((c + c' + 1) * lg N ^ 5) = 2 ^ ((c + c') * lg N ^ 5) * 2 ^ (lg N ^ 5) := by
      rw [← pow_add, add_mul, one_mul]
    rw [this]
    have h4 : 2 ≤ 2 ^ (lg N ^ 5) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (lg N ^ 5) := Nat.pow_le_pow_right (by norm_num) (one_le_lg5 N)
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h4
  have := hc N
  have := hc' N
  show T N + T' N ≤ _
  omega

theorem Q5.pow {T : ℕ → ℕ} (h : Q5 T) (d : ℕ) : Q5 (fun N => T N ^ d) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨d * c, fun N => ?_⟩
  calc T N ^ d ≤ (2 ^ (c * lg N ^ 5)) ^ d := Nat.pow_le_pow_left (hc N) d
    _ = 2 ^ (d * c * lg N ^ 5) := by rw [← pow_mul]; ring_nf

/-- `2^{A (log₂ N + 2)^k}` with `k ≤ 5`. -/
theorem q5_two_pow_lg (A k : ℕ) (hk : k ≤ 5) : Q5 (fun N => 2 ^ (A * lg N ^ k)) :=
  ⟨A, fun N => Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (lg_pow_mono le_rfl hk))⟩

theorem succ_le_two_pow_lg (N : ℕ) : N + 1 ≤ 2 ^ lg N := by
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have h2 : 2 ^ (Nat.log 2 N + 1) ≤ 2 ^ lg N := Nat.pow_le_pow_right (by norm_num) (by
    unfold lg; omega)
  omega

theorem q5_succ : Q5 (fun N => N + 1) :=
  ⟨1, fun N => (succ_le_two_pow_lg N).trans (Nat.pow_le_pow_right (by norm_num) (by
    rw [one_mul]
    calc lg N = lg N ^ 1 := (pow_one _).symm
      _ ≤ lg N ^ 5 := Nat.pow_le_pow_right (by have := two_le_lg N; omega) (by norm_num)))⟩

theorem q5_id : Q5 (fun N => N) := q5_succ.mono fun N => Nat.le_succ N

/-- A polynomial `2^a (N+1)^b`. -/
theorem q5_poly (a b : ℕ) : Q5 (fun N => 2 ^ a * (N + 1) ^ b) :=
  ((q5_two_pow_lg a 0 (by norm_num)).mono fun N => by simp).mul (q5_succ.pow b)

/-- **Composition with a polynomially bounded function.** -/
theorem Q5.comp_poly {T S : ℕ → ℕ} (h : Q5 T) {a b : ℕ} (hS : ∀ N, S N ≤ 2 ^ a * (N + 1) ^ b) :
    Q5 (fun N => T (S N)) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * (a + 2 * b + 3) ^ 5, fun N => (hc (S N)).trans ?_⟩
  apply Nat.pow_le_pow_right (by norm_num)
  rw [mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lg_le_of_poly (hS N)) 5)

/-- The bound of `Explicit.NodeBound` at degree and size `N`. -/
theorem q5_tsB (A b : ℕ) : Q5 (fun N => tsB A 5 b N N) :=
  (q5_two_pow_lg A 5 le_rfl).mul (q5_succ.pow b)

end Explicit
