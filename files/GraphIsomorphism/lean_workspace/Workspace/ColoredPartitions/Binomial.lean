/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 7.2.1: A binomial inequality.
-/
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# §7.2.1 A binomial inequality (Claim 7.2.4, Proposition 7.2.3)

| Paper | Lean |
|---|---|
| Claim 7.2.4, Eq. (42) | `Babai.choose_sq_le` |
| Eq. (43) | inside the proof of `Babai.choose_sq_le` |
| Proposition 7.2.3, Eq. (41) | `Babai.choose_mul_choose_le_two_thirds` |
| Eq. (44), (45) | inside the proof |
| Eq. (46) | `Babai.two_mul_choose_pred_le` and the case `t₁ = m₁` of the proof |

The inequalities of the paper are between rationals with denominators `2` and `3`; we
state them in `ℕ` in the equivalent cross-multiplied form (`3 * x ≤ 2 * y` for
`x ≤ (2/3) y`), which avoids any question of rounding.

`Nat` subtraction is truncated, so `k - 1` in Claim 7.2.4 is written under the hypothesis
`1 ≤ k`, where it means what the paper means; likewise `k ≤ n - 1` is written `k + 1 ≤ n`,
which for `1 ≤ n` is the same statement.
-/

namespace Babai

open Finset

/-- Claim 7.2.4, Eq. (42).  *"Let `1 ≤ k ≤ n - 1`.  Then `C(n,k)² ≤ 4 C(n,k-1) C(n,k+1)`."*

Proof.  *"Expanding and simplifying, the Claim reduces to the statement
`(k+1)/k ≤ 4(n-k)/(n-k+1)`.  This is true because `(k+1)/k ≤ 2` and
`(n-k)/(n-k+1) ≥ 1/2`."*  Cross-multiplied: after multiplying both sides by `k(k+1)` and
using `C(n,k)·k = C(n,k-1)·(n-k+1)` and `C(n,k+1)·(k+1) = C(n,k)·(n-k)`, the claim reduces
to `(n-k+1)(k+1) ≤ 4k(n-k)`, which holds because `k+1 ≤ 2k` and `n-k+1 ≤ 2(n-k)`. -/
theorem choose_sq_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (n.choose k) ^ 2 ≤ 4 * (n.choose (k - 1) * n.choose (k + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set A := n.choose j with hA
  set B := n.choose (j + 1) with hB
  set C := n.choose (j + 2) with hC
  have e1 : B * (j + 1) = A * (n - j) := Nat.choose_succ_right_eq n j
  have e2 : C * (j + 2) = B * (n - (j + 1)) := Nat.choose_succ_right_eq n (j + 1)
  have hsub : n - (j + 1) = n - j - 1 := by omega
  rw [hsub] at e2
  -- Eq. (43), cross-multiplied
  have key : (n - j) * (j + 2) ≤ 4 * ((j + 1) * (n - j - 1)) := by
    have h1 : n - j ≤ 2 * (n - j - 1) := by omega
    have h2 : j + 2 ≤ 2 * (j + 1) := by omega
    calc (n - j) * (j + 2) ≤ (2 * (n - j - 1)) * (2 * (j + 1)) := Nat.mul_le_mul h1 h2
      _ = 4 * ((j + 1) * (n - j - 1)) := by ring
  have main : B ^ 2 * ((j + 1) * (j + 2)) ≤ (4 * (A * C)) * ((j + 1) * (j + 2)) := by
    calc B ^ 2 * ((j + 1) * (j + 2)) = (B * (j + 1)) * B * (j + 2) := by ring
      _ = (A * (n - j)) * B * (j + 2) := by rw [e1]
      _ = A * B * ((n - j) * (j + 2)) := by ring
      _ ≤ A * B * (4 * ((j + 1) * (n - j - 1))) := Nat.mul_le_mul_left _ key
      _ = 4 * (j + 1) * A * (B * (n - j - 1)) := by ring
      _ = 4 * (j + 1) * A * (C * (j + 2)) := by rw [e2]
      _ = (4 * (A * C)) * ((j + 1) * (j + 2)) := by ring
  exact Nat.le_of_mul_le_mul_right main (by positivity)

/-- A single term of Vandermonde's identity is at most the whole sum. -/
theorem choose_mul_choose_le (a b x y : ℕ) : a.choose x * b.choose y ≤ (a + b).choose (x + y) := by
  rw [Nat.add_choose_eq]
  refine Finset.single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2)
    (fun _ _ => Nat.zero_le _) (a := (x, y)) ?_
  simp

/-- `Nat.choose n ·` is monotone below the middle. -/
theorem choose_le_choose_of_le_half {n : ℕ} : ∀ {a b : ℕ}, a ≤ b → 2 * b ≤ n →
    n.choose a ≤ n.choose b := by
  intro a b
  induction b with
  | zero =>
    intro hab _
    have : a = 0 := by omega
    subst this; exact le_rfl
  | succ b ih =>
    intro hab hb
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact (ih (by omega) (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))
    · have : a = b + 1 := by omega
      subst this; exact le_rfl

/-- Eq. (46), the key step: `C(m-1,t-1) = (t/m) C(m,t) ≤ (1/2) C(m,t)` when `2t ≤ m`. -/
theorem two_mul_choose_pred_le {m t : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) (htm : 2 * t ≤ m) :
    2 * (m - 1).choose (t - 1) ≤ m.choose t := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e : (m' + 1) * m'.choose t' = (m' + 1).choose (t' + 1) * (t' + 1) :=
    Nat.succ_mul_choose_eq m' t'
  have key : (m' + 1) * (2 * m'.choose t') ≤ (m' + 1) * (m' + 1).choose (t' + 1) := by
    calc (m' + 1) * (2 * m'.choose t') = 2 * (t' + 1) * (m' + 1).choose (t' + 1) := by
          rw [show (m' + 1) * (2 * m'.choose t') = 2 * ((m' + 1) * m'.choose t') by ring, e]; ring
      _ ≤ (m' + 1) * (m' + 1).choose (t' + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- Proposition 7.2.3, Eq. (41).  *"Let `m₁, m₂, t₁, t₂` be integers; let `m = m₁ + m₂` and
`t = t₁ + t₂`.  Assume `t ≤ m/2` and `tᵢ ≥ 1` for `i = 1,2`.  Then
`C(m₁,t₁) C(m₂,t₂) ≤ (2/3) C(m,t)`."*

The proof follows the paper.  Eq. (44) is `choose_sq_le`; with
`a_s = C(m₁,s) C(m₂,t-s)` it gives Eq. (45), `a_s² ≤ 16 a_{s-1} a_{s+1} ≤ 4(a_{s-1} +
a_{s+1})²`, hence `a_s ≤ 2(a_{s-1} + a_{s+1})`, hence
`(3/2) a_s ≤ a_{s-1} + a_s + a_{s+1} ≤ ∑_s a_s = C(m,t)` by Vandermonde's identity.  The
remaining cases `tᵢ = mᵢ` are Eq. (46); the cases `tᵢ > mᵢ` are trivial, both sides of the
relevant binomial coefficient being `0`. -/
theorem choose_mul_choose_le_two_thirds {m₁ m₂ t₁ t₂ : ℕ} (ht : 2 * (t₁ + t₂) ≤ m₁ + m₂)
    (ht₁ : 1 ≤ t₁) (ht₂ : 1 ≤ t₂) :
    3 * (m₁.choose t₁ * m₂.choose t₂) ≤ 2 * ((m₁ + m₂).choose (t₁ + t₂)) := by
  -- the degenerate cases `tᵢ > mᵢ`
  rcases Nat.lt_or_ge m₁ t₁ with h | h₁
  · simp [Nat.choose_eq_zero_of_lt h]
  rcases Nat.lt_or_ge m₂ t₂ with h | h₂
  · simp [Nat.choose_eq_zero_of_lt h]
  rcases eq_or_lt_of_le h₁ with h | h₁'
  · -- Eq. (46), the case `t₁ = m₁`
    subst h
    have hm : 1 ≤ t₁ + m₂ := by omega
    have h46a : m₂.choose t₂ ≤ (t₁ + m₂ - 1).choose (t₁ + t₂ - 1) :=
      le_trans (Nat.choose_le_choose (b := t₁ + m₂ - 1) t₂ (by omega))
        (choose_le_choose_of_le_half (by omega) (by omega))
    have h46b : 2 * (t₁ + m₂ - 1).choose (t₁ + t₂ - 1) ≤ (t₁ + m₂).choose (t₁ + t₂) :=
      two_mul_choose_pred_le hm (by omega) ht
    rw [Nat.choose_self]
    omega
  rcases eq_or_lt_of_le h₂ with h | h₂'
  · -- the case `t₂ = m₂`, symmetric to the previous one
    subst h
    have hm : 1 ≤ m₁ + t₂ := by omega
    have h46a : m₁.choose t₁ ≤ (m₁ + t₂ - 1).choose (t₁ + t₂ - 1) :=
      le_trans (Nat.choose_le_choose (b := m₁ + t₂ - 1) t₁ (by omega))
        (choose_le_choose_of_le_half (by omega) (by omega))
    have h46b : 2 * (m₁ + t₂ - 1).choose (t₁ + t₂ - 1) ≤ (m₁ + t₂).choose (t₁ + t₂) :=
      two_mul_choose_pred_le hm (by omega) ht
    rw [Nat.choose_self]
    omega
  -- the main case `1 ≤ tᵢ ≤ mᵢ - 1`
  obtain ⟨u, rfl⟩ : ∃ u, t₁ = u + 1 := ⟨t₁ - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, t₂ = w + 1 := ⟨t₂ - 1, by omega⟩
  set x := m₁.choose u * m₂.choose (w + 2) with hx
  set y := m₁.choose (u + 2) * m₂.choose w with hy
  set a := m₁.choose (u + 1) * m₂.choose (w + 1) with ha
  -- Eq. (44) for `i = 1, 2`
  have e44₁ : (m₁.choose (u + 1)) ^ 2 ≤ 4 * (m₁.choose u * m₁.choose (u + 2)) := by
    have := choose_sq_le (n := m₁) (k := u + 1) (by omega) (by omega)
    simpa using this
  have e44₂ : (m₂.choose (w + 1)) ^ 2 ≤ 4 * (m₂.choose w * m₂.choose (w + 2)) := by
    have := choose_sq_le (n := m₂) (k := w + 1) (by omega) (by omega)
    simpa using this
  -- Eq. (45)
  have e45 : a ^ 2 ≤ 16 * (x * y) := by
    calc a ^ 2 = (m₁.choose (u + 1)) ^ 2 * (m₂.choose (w + 1)) ^ 2 := by rw [ha]; ring
      _ ≤ (4 * (m₁.choose u * m₁.choose (u + 2))) * (4 * (m₂.choose w * m₂.choose (w + 2))) :=
          Nat.mul_le_mul e44₁ e44₂
      _ = 16 * (x * y) := by rw [hx, hy]; ring
  have hamgm : a ≤ 2 * (x + y) := by
    have h4 : 4 * (x * y) ≤ (x + y) ^ 2 := by
      zify
      nlinarith [sq_nonneg ((x : ℤ) - y)]
    have h1 : a ^ 2 ≤ (2 * (x + y)) ^ 2 := by
      calc a ^ 2 ≤ 16 * (x * y) := e45
        _ = 4 * (4 * (x * y)) := by ring
        _ ≤ 4 * (x + y) ^ 2 := Nat.mul_le_mul_left _ h4
        _ = (2 * (x + y)) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).1 h1
  -- `a_{s-1} + a_s + a_{s+1} ≤ ∑_s a_s = C(m,t)` (Vandermonde)
  have hthree : x + a + y ≤ (m₁ + m₂).choose (u + 1 + (w + 1)) := by
    rw [Nat.add_choose_eq]
    have hsub : ({(u, w + 2), (u + 1, w + 1), (u + 2, w)} : Finset (ℕ × ℕ))
        ⊆ Finset.antidiagonal (u + 1 + (w + 1)) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp [Finset.mem_antidiagonal] <;> omega
    have hsum : ∑ p ∈ ({(u, w + 2), (u + 1, w + 1), (u + 2, w)} : Finset (ℕ × ℕ)),
        m₁.choose p.1 * m₂.choose p.2 = x + a + y := by
      rw [Finset.sum_insert (by simp [Prod.ext_iff]), Finset.sum_insert (by simp [Prod.ext_iff]),
        Finset.sum_singleton]
      rw [hx, ha, hy]; ring
    calc x + a + y = ∑ p ∈ ({(u, w + 2), (u + 1, w + 1), (u + 2, w)} : Finset (ℕ × ℕ)),
          m₁.choose p.1 * m₂.choose p.2 := hsum.symm
      _ ≤ ∑ p ∈ Finset.antidiagonal (u + 1 + (w + 1)), m₁.choose p.1 * m₂.choose p.2 :=
          Finset.sum_le_sum_of_subset hsub
  omega

end Babai
