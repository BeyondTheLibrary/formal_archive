/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 5: the size of the test set, and the hypotheses of Theorem 13.2.1.
-/
import Workspace.LocalCertificates.Defs
import Workspace.Master.Line2

/-!
# The test set size at §15, line 5

Line 5 of Sec. 15 applies AggregateCertificates (Theorem 13.2.1), which asks for a test set
size `t` with

> `max{8, 2 + log₂ n} < t < m/10`.

Sec. 13.1 says which `t` to take:

> we shall choose `t = O(log n)`.

Here `t = 10 + ⌊log₂ n⌋` (`Babai.testSetSize`).  What the round knows at line 5 is the test
of line 2, `m > ℓ = (log n)³` (`Babai.ellOf`).  The two lemmas below turn that into the two
hypotheses of Theorem 13.2.1, for `n` above the absolute constant `64`:

* `Babai.largeK_testSetSize`: `max{8, 2 + log₂ n} < t`, for every `n ≥ 1`;
* `Babai.ten_mul_testSetSize_lt`: `10 t < m`, for `n ≥ 64`.

The third hypothesis, `LocalCertSetting G ϕ`, asks for `G` transitive, `ϕ` a giant
representation — both are what line 3 fixes — and `m ≥ 10 log₂ n`, which again follows from
`m > (log₂ n)³` for `n ≥ 64` (`Babai.localCertSetting_of_line3`).

**Small `n`.**  The paper handles bounded instances by enumeration, in line 2 of Procedure
Reduce-to-Johnson (Sec. 11.3):

> 2. if `|G| < C₀` for some absolute constant `C₀` then compute `Iso_G(x,y)` by brute
>    force, exit

and Sec. 11.4 states its recurrences "assuming `x` is sufficiently large".  For `n < 64`
the group `G ≤ S(Ω)` has order at most `63!`, an absolute constant, so line 2 of
Reduce-to-Johnson applies and Sec. 15 is never reached.  The threshold `64` below is
therefore not an extra hypothesis on the theorem; it is the range in which the paper's own
brute-force line already answers.
-/

namespace Babai

/-! ### The two polylogarithmic functions of Sec. 15 -/

/-- §15, line 2: *"set `ℓ = (log n)³`"*, with `log` to base 2 and rounded down. -/
def ellOf (n : ℕ) : ℕ := (Nat.log 2 n) ^ 3

/-- §13.1: *"we shall choose `t = O(log n)`"* — the size of the test set of
Theorem 13.1.3 and Theorem 13.2.1. -/
def testSetSize (n : ℕ) : ℕ := 10 + Nat.log 2 n

/-- The test set has at least ten points, whatever `n` is.  This is what makes the calls of
Procedure AggregateCertificates shrink the window: a window of at most `n/t` points with
`t ≥ 5` is at most `4n/5`. -/
theorem five_le_testSetSize (n : ℕ) : 5 ≤ testSetSize n := by
  rw [testSetSize]; omega

/-- `log₂ n < ⌊log₂ n⌋ + 1`: the real logarithm is below the next integer. -/
theorem logb_lt_natLog_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 n < (Nat.log 2 n : ℝ) + 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show ((Nat.log 2 n : ℝ) + 1) = ((Nat.log 2 n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.logb_lt_iff_lt_rpow one_lt_two hpos, Real.rpow_natCast]
  exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two n

/-- `6 ≤ ⌊log₂ n⌋` for `n ≥ 64`. -/
theorem six_le_natLog {n : ℕ} (hn : 64 ≤ n) : 6 ≤ Nat.log 2 n := by
  refine Nat.le_log_of_pow_le one_lt_two ?_
  simpa using hn

/-! ### The hypotheses of Theorem 13.2.1 at line 5 -/

/-- §15, line 5: the test set size satisfies the lower bound of Theorem 13.2.1,
`max{8, 2 + log₂ n} < t`.

*Proof.*  `8 < 10 ≤ t`, and `2 + log₂ n < 3 + ⌊log₂ n⌋ ≤ t`. -/
theorem largeK_testSetSize {n : ℕ} (hn : 1 ≤ n) : LargeK (testSetSize n) n := by
  have h := logb_lt_natLog_succ hn
  have hcast : ((testSetSize n : ℕ) : ℝ) = 10 + (Nat.log 2 n : ℝ) := by
    rw [testSetSize]; push_cast; ring
  rw [LargeK, hcast, max_lt_iff]
  constructor
  · have : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    linarith
  · linarith

/-- §15, line 5: the test set size satisfies the upper bound of Theorem 13.2.1, `10 t < m`.

The round knows `m > ℓ = (log₂ n)³` from the test of line 2.  For `L = ⌊log₂ n⌋ ≥ 6`,
`10 t = 100 + 10 L < L³ < m`. -/
theorem ten_mul_testSetSize_lt {n m : ℕ} (hn : 64 ≤ n) (hm : ellOf n < m) :
    10 * testSetSize n < m := by
  have hL : 6 ≤ Nat.log 2 n := six_le_natLog hn
  rw [ellOf] at hm
  rw [testSetSize]
  have h1 : 36 * Nat.log 2 n ≤ Nat.log 2 n ^ 3 :=
    calc 36 * Nat.log 2 n = 6 * 6 * Nat.log 2 n := by ring
      _ ≤ Nat.log 2 n * Nat.log 2 n * Nat.log 2 n :=
          Nat.mul_le_mul (Nat.mul_le_mul hL hL) le_rfl
      _ = Nat.log 2 n ^ 3 := by ring
  have h2 : 10 * (10 + Nat.log 2 n) < 36 * Nat.log 2 n := by omega
  exact lt_of_lt_of_le (lt_of_lt_of_le h2 h1) (le_of_lt hm)

/-- §15, line 5: the third hypothesis of Theorem 13.2.1, `m ≥ 10 log₂ n`, also follows from
the test of line 2.

*Proof.*  `10 log₂ n < 10(L + 1) = 10L + 10 ≤ L³ < m` for `L = ⌊log₂ n⌋ ≥ 6`. -/
theorem ten_mul_logb_le {n m : ℕ} (hn : 64 ≤ n) (hm : ellOf n < m) :
    10 * Real.logb 2 n ≤ (m : ℝ) := by
  have hL : 6 ≤ Nat.log 2 n := six_le_natLog hn
  have hlog := logb_lt_natLog_succ (n := n) (by omega)
  rw [ellOf] at hm
  have h1 : 36 * Nat.log 2 n ≤ Nat.log 2 n ^ 3 :=
    calc 36 * Nat.log 2 n = 6 * 6 * Nat.log 2 n := by ring
      _ ≤ Nat.log 2 n * Nat.log 2 n * Nat.log 2 n :=
          Nat.mul_le_mul (Nat.mul_le_mul hL hL) le_rfl
      _ = Nat.log 2 n ^ 3 := by ring
  have hnat : 10 * Nat.log 2 n + 10 ≤ m := by omega
  have hcast : (10 : ℝ) * (Nat.log 2 n : ℝ) + 10 ≤ (m : ℝ) := by exact_mod_cast hnat
  linarith

section Setting

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- §15, line 5: **the setting of Theorem 13.2.1 from the data of line 3**.

Line 3 gives a transitive `G` and a giant representation `ϕ : G → S(Γ)`; the test of line 2
gives `m > ℓ = (log₂ n)³`, and for `n ≥ 64` that is more than `10 log₂ n`.  Those three
facts are exactly `Babai.LocalCertSetting`. -/
theorem localCertSetting_of_line3 {ϕ : G →* Equiv.Perm Γ} (htr : IsTransitive G)
    (hgiant : IsGiantRep ϕ) (hn : 64 ≤ Nat.card Ω) (hm : ellOf (Nat.card Ω) < Nat.card Γ) :
    LocalCertSetting G ϕ where
  transitive := htr
  giant := hgiant
  large := ten_mul_logb_le hn hm

end Setting

end Babai
