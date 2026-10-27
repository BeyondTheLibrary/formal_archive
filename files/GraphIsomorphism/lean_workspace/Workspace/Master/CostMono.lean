/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the costs of the branches of one round are monotone in the window size.
-/
import Workspace.Master.Line567a

/-!
# The costs of Sec. 15 are monotone

`Babai.Theorem_1_1_1_math_of_masterStep` asks the cost of a round to be monotone: the
recurrence of Sec. 11.4 is solved by comparing the cost at a smaller window with the cost at
the window of the caller, which needs `roundCost` to be non-decreasing.

Each branch cost of Sec. 15 is built from `Nat.log 2`, the factorial, powers and sums, so
each of them is monotone.  The lemmas are collected here, one per cost.
-/

namespace Babai

/-- `ℓ(n) = (log₂ n)³` is non-decreasing. -/
theorem ellOf_mono : Monotone ellOf := by
  intro a b hab
  exact Nat.pow_le_pow_left (Nat.log_mono_right hab) 3

/-- §15, line 2 and line 4b: the cost `ℓ(n)!·n + 7n` is non-decreasing. -/
theorem masterRoundCost_mono : Monotone masterRoundCost := by
  intro a b hab
  have h1 : Nat.factorial (ellOf a) ≤ Nat.factorial (ellOf b) :=
    Nat.factorial_le (ellOf_mono hab)
  have h2 : Nat.factorial (ellOf a) * a ≤ Nat.factorial (ellOf b) * b :=
    Nat.mul_le_mul h1 hab
  rw [masterRoundCost, masterRoundCost]
  omega

/-- §14.1, lines 7–11: the cost `ℓ(n)!·n + n` of the round of the dominant window is
non-decreasing. -/
theorem alignDominantRoundCost_mono :
    Monotone AlignDominantRoundData.alignDominantRoundCost := by
  intro a b hab
  have h1 : Nat.factorial (ellOf a) ≤ Nat.factorial (ellOf b) :=
    Nat.factorial_le (ellOf_mono hab)
  have h2 : Nat.factorial (ellOf a) * a ≤ Nat.factorial (ellOf b) * b :=
    Nat.mul_le_mul h1 hab
  rw [AlignDominantRoundData.alignDominantRoundCost,
    AlignDominantRoundData.alignDominantRoundCost]
  omega

/-- `Babai.qMax` is monotone: it is a supremum over a growing range. -/
theorem qMax_mono (q : ℕ → ℕ) : Monotone (qMax q) := by
  intro a b hab
  refine Finset.sup_le fun k hk => ?_
  exact le_qMax q (le_trans (by have := Finset.mem_range.1 hk; omega) hab)

/-- `n ↦ n^{c·log₂ n}` is non-decreasing.  At `n = 0` its value is `0⁰ = 1`, and every later
value is at least `1`, so the step from `0` costs nothing. -/
theorem pow_mul_log_mono (c : ℕ) : Monotone fun n : ℕ => n ^ (c * Nat.log 2 n) := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.log_zero_right, Nat.mul_zero, pow_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.one_le_pow _ _ hb
  · calc a ^ (c * Nat.log 2 a) ≤ b ^ (c * Nat.log 2 a) := Nat.pow_le_pow_left hab _
      _ ≤ b ^ (c * Nat.log 2 b) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.log_mono_right hab))

/-- §15, lines 4c–4d, Eq. (71): the cost of one round of lines 4c–4d is non-decreasing. -/
theorem line4cdCost_mono (q : ℕ → ℕ) (c : ℕ) : Monotone (line4cdCost q c) := by
  intro a b hab
  have h1 : qMax q a ≤ qMax q b := qMax_mono q hab
  have h2 : a ^ (c * Nat.log 2 a) ≤ b ^ (c * Nat.log 2 b) := pow_mul_log_mono c hab
  have h3 : AlignDominantRoundData.alignDominantRoundCost a
      ≤ AlignDominantRoundData.alignDominantRoundCost b := alignDominantRoundCost_mono hab
  rw [line4cdCost, line4cdCost]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (by omega)) h3

/-- §15, lines 5, 7 and 7a: the cost of one round of lines 5, 7 and 7a is
non-decreasing. -/
theorem line567aCost_mono : Monotone line567aCost := by
  intro a b hab
  have h1 : masterRoundCost a ≤ masterRoundCost b := masterRoundCost_mono hab
  have h3 : AlignDominantRoundData.alignDominantRoundCost a
      ≤ AlignDominantRoundData.alignDominantRoundCost b := alignDominantRoundCost_mono hab
  rw [line567aCost, line567aCost]
  have h4 : (a + 1) * AlignDominantRoundData.alignDominantRoundCost a
      ≤ (b + 1) * AlignDominantRoundData.alignDominantRoundCost b :=
    Nat.mul_le_mul (by omega) h3
  have h5 : aggregateAllowance a ≤ aggregateAllowance b := aggregateAllowance_mono hab
  omega

/-- §15, line 1: the cost of Procedure Reduce-to-Johnson is non-decreasing.  This is
`Babai.line1RoundCost_mono`, repeated here so that the six costs of a round stand
together. -/
theorem line1RoundCost_mono' : Monotone line1RoundCost := line1RoundCost_mono

/-! ## The costs are quasipolynomial

`Babai.Theorem_1_1_1_math_of_masterStep` asks `q(n) ≤ 2^{(log₂ n + 2)^{c₁}}`, which is
`RAM.QuasiPolyBound q` written out.  The lemmas below say that the costs of the branches of
Sec. 15 meet it, so the theorem is not empty.  The check matters: with `log₂ n + 1` in place
of `log₂ n + 2` the hypothesis is unsatisfiable, because at `n = 1` its right side is `2`
while `masterRoundCost 1 = 8`; see the the corrected paper the round-cost hypothesis of
Theorem 1.1.1. -/

/-- The value that shows the old `log₂ n + 1` form of the hypothesis was empty: every
`Babai.Sec15Remaining` has `masterRoundCost n ≤ roundCost n`, and `masterRoundCost 1 = 8`,
while `2 ^ ((Nat.log 2 1 + 1) ^ c₁) = 2` for every `c₁`. -/
theorem masterRoundCost_one : masterRoundCost 1 = 8 := by
  rw [masterRoundCost, ellOf]
  norm_num

/-- The old right side of the hypothesis at `n = 1`: it is `2`, whatever `c₁` is. -/
theorem two_pow_log_one (c₁ : ℕ) : (2 : ℕ) ^ ((Nat.log 2 1 + 1) ^ c₁) = 2 := by
  norm_num

/-- §15, line 2 and line 4b: `ℓ(n)!·n + 7n` is quasipolynomial. -/
theorem quasiPolyBound_masterRoundCost : RAM.QuasiPolyBound masterRoundCost := by
  have h : RAM.QuasiPolyBound (fun n => Nat.factorial (ellOf n) * n + 7 * n) :=
    (quasiPolyBound_factorial_ellOf.mul quasiPolyBound_id).add
      ((RAM.polyBound_const 7).quasiPoly.mul quasiPolyBound_id)
  exact h.mono fun n => le_of_eq rfl

/-- §11.3: the multiplicative cost `q(n) = n^{2 + log₂ n}` of Procedure Reduce-to-Johnson
is quasipolynomial.  From `Babai.line1Cost_le`, `q(n) ≤ 2^{2(log₂ n + 1)²}`, and
`2(log₂ n + 1)² ≤ (log₂ n + 2)³` because `log₂ n + 2 ≥ 2`. -/
theorem quasiPolyBound_line1Cost : RAM.QuasiPolyBound line1Cost := by
  refine ⟨3, fun n => ?_⟩
  refine le_trans (line1Cost_le n) (Nat.pow_le_pow_right (by norm_num) ?_)
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have h1 : (Nat.log 2 n + 1) ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : 2 * L ^ 2 ≤ L * L ^ 2 := Nat.mul_le_mul_right _ hL2
  have h3 : L * L ^ 2 = L ^ 3 := by ring
  omega

/-- §15, line 1: the cost of one round of Procedure Reduce-to-Johnson is
quasipolynomial. -/
theorem quasiPolyBound_line1RoundCost : RAM.QuasiPolyBound line1RoundCost := by
  have h : RAM.QuasiPolyBound (fun n => line1Cost n * n + line1Cost n + n + 2) :=
    (((quasiPolyBound_line1Cost.mul quasiPolyBound_id).add
      quasiPolyBound_line1Cost).add quasiPolyBound_id).add (RAM.polyBound_const 2).quasiPoly
  exact h.mono fun n => le_of_eq rfl

/-- §15, lines 5, 7 and 7a: the cost of one round of lines 5, 7 and 7a is
quasipolynomial. -/
theorem quasiPolyBound_line567aCost : RAM.QuasiPolyBound line567aCost := by
  have h : RAM.QuasiPolyBound (fun n =>
      masterRoundCost n + (n + 1) * AlignDominantRoundData.alignDominantRoundCost n
        + aggregateAllowance n) :=
    (quasiPolyBound_masterRoundCost.add
      (quasiPolyBound_succ.mul quasiPolyBound_alignDominantRoundCost)).add
      quasiPolyBound_aggregateAllowance
  exact h.mono fun n => le_of_eq rfl

/-- **The round-cost hypothesis of Theorem 1.1.1 can be met.**  The cost of the two lines
of Sec. 15 that every `Babai.Sec15Remaining` must pay for, `masterRoundCost + line1RoundCost`
(the field `roundCost_ge`), satisfies it.  So
`Babai.Theorem_1_1_1_math_of_masterStep` is not empty at the assembled round, which the
`log₂ n + 1` form of the hypothesis was. -/
theorem exists_c₁_masterRoundCost_add_line1RoundCost :
    ∃ c₁ : ℕ, ∀ n : ℕ,
      masterRoundCost n + line1RoundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁) :=
  quasiPolyBound_masterRoundCost.add quasiPolyBound_line1RoundCost

end Babai
