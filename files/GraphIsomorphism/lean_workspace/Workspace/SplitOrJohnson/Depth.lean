/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.5: how many times the recursion of Procedure Bipartite Split-or-Johnson can call
itself, and why the total multiplicative cost stays quasipolynomial.
-/
import Workspace.Machine.TimeClasses
import Mathlib.Tactic.Linarith

/-!
# §9.5  The depth of the recursion

§9.5 says that a parameter is *significantly reduced* when it drops to at most `0.9` of its
old value, and that the recursion of §9.4-§9.8 makes major progress at every turn.  Two
of the three kinds of major progress reduce `n₂` significantly; the third one, *"`X₂` moves
from clique to UPCC while `n₂` does not increase"*, leaves `n₂` alone but can happen only
once between two reductions, because the turn that starts from the structure it leaves
does reduce `n₂` (§9.7, Case 3a2).  So there are at most **two** turns per significant
reduction of `n₂`, and the number of nested calls is still `O(log n₂)`.

`Babai.steps09` counts those calls: it is the number of times one can replace `n` by
`⌊9n/10⌋` before reaching `0`.  The two facts we need are

* `Babai.steps09_le_log`: `steps09 n ≤ 7 (log₂ n + 1)`, the logarithmic depth — seven
  `0.9`-steps more than halve a number;
* `Babai.quasiPolyBound_costBound`: a quasipolynomial raised to that many powers is again
  a quasipolynomial, which is the cost bound of Theorem 9.2.2.

## Numbering map

| Paper | Lean |
|---|---|
| §9.5, the number of significant reductions of `n₂` | `Babai.steps09` |
| §9.5, the depth is logarithmic | `Babai.steps09_le_log` |
| §9.2, "quasipolynomial multiplicative cost" | `Babai.quasiPolyBound_costBound` |
-/

namespace Babai

/-- One significant reduction of §9.5: `n` becomes at most `0.9 n`, and `⌊9n/10⌋` is the
largest value allowed. -/
def reduce09 (n : ℕ) : ℕ := 9 * n / 10

theorem reduce09_lt {n : ℕ} (hn : 0 < n) : reduce09 n < n :=
  Nat.div_lt_of_lt_mul (by omega)

/-- §9.5.  The number of significant reductions of `n₂` that the recursion of §9.4-§9.8
can still make: the number of times `n` can be replaced by `⌊9n/10⌋` before reaching `0`. -/
def steps09 : ℕ → ℕ
  | 0 => 0
  | (n + 1) => steps09 (reduce09 (n + 1)) + 1
  decreasing_by exact reduce09_lt (Nat.succ_pos n)

@[simp] theorem steps09_zero : steps09 0 = 0 := by rw [steps09]

theorem steps09_succ (n : ℕ) : steps09 (n + 1) = steps09 (reduce09 (n + 1)) + 1 := by
  rw [steps09]

/-- One step of the count: removing one significant reduction costs at most one. -/
theorem steps09_le_reduce (n : ℕ) : steps09 n ≤ steps09 (reduce09 n) + 1 := by
  cases n with
  | zero => simp [reduce09]
  | succ m => exact le_of_eq (steps09_succ m)

/-- `k` steps of the count. -/
theorem steps09_le_iterate (k : ℕ) (n : ℕ) : steps09 n ≤ steps09 (reduce09^[k] n) + k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    calc steps09 n ≤ steps09 (reduce09 n) + 1 := steps09_le_reduce n
      _ ≤ (steps09 (reduce09^[k] (reduce09 n)) + k) + 1 := by
          exact Nat.add_le_add_right (ih (reduce09 n)) 1
      _ = steps09 (reduce09^[k + 1] n) + (k + 1) := by
          rw [Function.iterate_succ_apply]; omega

/-- `k` significant reductions multiply the parameter by at most `(9/10)^k`. -/
theorem reduce09_iterate_mul_le (k n : ℕ) : reduce09^[k] n * 10 ^ k ≤ 9 ^ k * n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : reduce09 (reduce09^[k] n) * 10 ≤ 9 * reduce09^[k] n :=
      Nat.div_mul_le_self _ 10
    calc reduce09^[k + 1] n * 10 ^ (k + 1)
        = (reduce09 (reduce09^[k] n) * 10) * 10 ^ k := by
          rw [Function.iterate_succ_apply']; ring
      _ ≤ (9 * reduce09^[k] n) * 10 ^ k := Nat.mul_le_mul_right _ hstep
      _ = 9 * (reduce09^[k] n * 10 ^ k) := by ring
      _ ≤ 9 * (9 ^ k * n) := Nat.mul_le_mul_left _ ih
      _ = 9 ^ (k + 1) * n := by ring

/-- Seven significant reductions more than halve the parameter. -/
theorem reduce09_iterate_seven_lt {k n : ℕ} (hn : n < 2 ^ (k + 1)) :
    reduce09^[7] n < 2 ^ k := by
  have h1 : reduce09^[7] n * 10 ^ 7 ≤ 9 ^ 7 * n := reduce09_iterate_mul_le 7 n
  have h2 : 9 ^ 7 * n < 9 ^ 7 * 2 ^ (k + 1) :=
    mul_lt_mul_of_pos_left hn (by norm_num)
  have h3 : (9 : ℕ) ^ 7 * 2 ^ (k + 1) = (2 * 9 ^ 7) * 2 ^ k := by ring
  have h4 : (2 * 9 ^ 7) * 2 ^ k ≤ 10 ^ 7 * 2 ^ k :=
    Nat.mul_le_mul_right _ (by norm_num)
  have h5 : reduce09^[7] n * 10 ^ 7 < 2 ^ k * 10 ^ 7 := by
    calc reduce09^[7] n * 10 ^ 7 ≤ 9 ^ 7 * n := h1
      _ < 9 ^ 7 * 2 ^ (k + 1) := h2
      _ = (2 * 9 ^ 7) * 2 ^ k := h3
      _ ≤ 10 ^ 7 * 2 ^ k := h4
      _ = 2 ^ k * 10 ^ 7 := by ring
  exact Nat.lt_of_mul_lt_mul_right h5

theorem steps09_le_of_lt_pow : ∀ (k n : ℕ), n < 2 ^ k → steps09 n ≤ 7 * k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by simpa using hn
    simp [hn0]
  | succ k ih =>
    intro n hn
    have hlt : reduce09^[7] n < 2 ^ k := reduce09_iterate_seven_lt hn
    calc steps09 n ≤ steps09 (reduce09^[7] n) + 7 := steps09_le_iterate 7 n
      _ ≤ 7 * k + 7 := Nat.add_le_add_right (ih _ hlt) 7
      _ = 7 * (k + 1) := by ring

/-- §9.5.  **The recursion has logarithmic depth.**  `n₂` can be significantly reduced at
most `7 (log₂ n₂ + 1)` times. -/
theorem steps09_le_log (n : ℕ) : steps09 n ≤ 7 * (Nat.log 2 n + 1) :=
  steps09_le_of_lt_pow _ n (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- The count is monotone. -/
theorem steps09_mono : ∀ (m n : ℕ), n ≤ m → steps09 n ≤ steps09 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hnm
    cases n with
    | zero => simp
    | succ k =>
      have hm : 0 < m := lt_of_lt_of_le (Nat.succ_pos k) hnm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [steps09_succ, steps09_succ]
      have hred : reduce09 (k + 1) ≤ reduce09 (m' + 1) :=
        Nat.div_le_div_right (Nat.mul_le_mul_left 9 hnm)
      exact Nat.add_le_add_right
        (ih (reduce09 (m' + 1)) (reduce09_lt hm) (reduce09 (k + 1)) hred) 1

/-! ### The cost bound -/

/-- The absolute constant in the exponent of `Babai.turnCost`.

It has to be large enough for every multiplicative cost that one turn of Procedure
Bipartite Split-or-Johnson can incur.  The largest of them is §9.7, Case 3a: *"Apply the
Design lemma to `H`, viewed as a `d₁`-ary relational structure.  (Multiplicative cost
`n₂^{d₁} < n₂^{(7/3) log₂ n₁}`.)"*, which is `2^{(7/3)(log₂ n)²}` and already exceeds
`2^{(log₂ n + 2)²}`.  The other costs of one turn are §9.6 (`n₂`), §9.8 (`n₂`), the extra
factor `m ≤ n₂/2` of §9.7 Case 3a1, and Procedure Reduce-Part2-by-Color (Lemma 9.3.2);
they are polynomial in `n`, and one turn may incur several of them at once, so the
constant must leave room for a polynomial factor as well.

With the value `4` the exponent is `4(log₂ n + 2)²`, which is `(7/3)(log₂ n + 2)²` for
Case 3a plus a slack of `(5/3)(log₂ n + 2)²`; the slack alone covers `n^k` for every
`k ≤ (5/3)(log₂ n + 2)`, so it covers every polynomial factor of one turn on all but
finitely many `n`, and `Babai.constFactor` covers the rest. -/
def turnConst : ℕ := 4

/-- §9.2, §9.4.  The multiplicative cost of **one turn** of Procedure Bipartite
Split-or-Johnson on an instance with `n` points: a quasipolynomial, because step 3a of
§9.7 applies the Design Lemma at a multiplicative cost of `n₂^{d₁}` with
`d₁ ≤ (7/3) log₂ n₁`, which is `2^{(7/3)(log₂ n)²}`.  See `Babai.turnConst` for why the
constant in the exponent is needed. -/
def turnCost (n : ℕ) : ℕ := 2 ^ (turnConst * (Nat.log 2 n + 2) ^ 2)

/-- §9.7, Case 3a.  The cost of the Design Lemma on a `d₁`-ary structure, `n₂^{d₁}` with
`d₁ ≤ (7/3) log₂ n₁`, is below the cost of one turn.  The bound is stated with `3 d₁ ≤
7 log₂ n₁` to avoid dividing natural numbers. -/
theorem designCost_le_turnCost {n n₁ n₂ d₁ : ℕ} (h₁ : n₁ ≤ n) (h₂ : n₂ ≤ n)
    (hd : 3 * d₁ ≤ 7 * Nat.log 2 n₁) : n₂ ^ d₁ ≤ turnCost n := by
  rcases Nat.eq_zero_or_pos n₂ with rfl | hn₂
  · calc (0 : ℕ) ^ d₁ ≤ 1 := by
          rcases Nat.eq_zero_or_pos d₁ with rfl | hd₁
          · simp
          · rw [zero_pow (by omega : d₁ ≠ 0)]; exact Nat.zero_le 1
      _ ≤ turnCost n := Nat.one_le_two_pow
  set L := Nat.log 2 n with hL
  have hlog₂ : Nat.log 2 n₂ ≤ L := Nat.log_mono_right h₂
  have hlog₁ : Nat.log 2 n₁ ≤ L := Nat.log_mono_right h₁
  have hn₂lt : n₂ < 2 ^ (Nat.log 2 n₂ + 1) := Nat.lt_pow_succ_log_self (by norm_num) n₂
  have hstep : n₂ ^ d₁ ≤ (2 ^ (Nat.log 2 n₂ + 1)) ^ d₁ :=
    Nat.pow_le_pow_left hn₂lt.le d₁
  have hexp : (Nat.log 2 n₂ + 1) * d₁ ≤ turnConst * (L + 2) ^ 2 := by
    have h3 : 3 * ((Nat.log 2 n₂ + 1) * d₁) ≤ (L + 1) * (7 * L) := by
      calc 3 * ((Nat.log 2 n₂ + 1) * d₁) = (Nat.log 2 n₂ + 1) * (3 * d₁) := by ring
        _ ≤ (L + 1) * (7 * Nat.log 2 n₁) :=
            Nat.mul_le_mul (by omega) hd
        _ ≤ (L + 1) * (7 * L) := Nat.mul_le_mul_left _ (by omega)
    have h4 : 3 * (turnConst * (L + 2) ^ 2) = 12 * (L + 2) ^ 2 := by
      simp [turnConst]; ring
    nlinarith [sq_nonneg (L + 2), h3]
  calc n₂ ^ d₁ ≤ (2 ^ (Nat.log 2 n₂ + 1)) ^ d₁ := hstep
    _ = 2 ^ ((Nat.log 2 n₂ + 1) * d₁) := by rw [← pow_mul]
    _ ≤ 2 ^ (turnConst * (L + 2) ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

theorem one_le_turnCost (n : ℕ) : 1 ≤ turnCost n := Nat.one_le_two_pow

/-- The cost of one turn only grows with the number of points.  This is what lets a turn
pay for a recursive call on an instance that lives on a subset of `□X`. -/
theorem turnCost_mono {m n : ℕ} (h : m ≤ n) : turnCost m ≤ turnCost n :=
  Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      exact Nat.add_le_add_right (Nat.log_mono_right h) 2) 2))

/-- §9.7, Case 3a.  The multiplicative cost of the block design case, as it is stated in
`Babai.case_9_7`, is below the cost of one turn.

The exponent is `⌊7(⌊log₂ n₁⌋ + 1)/3⌋ + 2`: the paper's `d₁ ≤ (7/3) log₂ n₁` with the real
logarithm read on natural numbers, plus the two extra factors `n₂` for Procedure
Reduce-Part2-by-Color and for the call to §9.8 in Case 3a2.  Those two extra factors are
why `Babai.designCost_le_turnCost` cannot be used directly: there `3 d₁ ≤ 7 log₂ n₁`,
while here `3 d ≤ 7 log₂ n₁ + 13`.  The slack in `Babai.turnConst` covers it. -/
theorem caseCost_9_7_le_turnCost {n n₁ n₂ : ℕ} (h₁ : n₁ ≤ n) (h₂ : n₂ ≤ n) :
    n₂ ^ (7 * (Nat.log 2 n₁ + 1) / 3 + 2) ≤ turnCost n := by
  set d := 7 * (Nat.log 2 n₁ + 1) / 3 + 2 with hd
  set L := Nat.log 2 n with hL
  have hlog₁ : Nat.log 2 n₁ ≤ L := Nat.log_mono_right h₁
  have hlog₂ : Nat.log 2 n₂ ≤ L := Nat.log_mono_right h₂
  -- `3 d ≤ 7 L + 13`
  have h3d : 3 * d ≤ 7 * L + 13 := by
    have hq : 3 * (7 * (Nat.log 2 n₁ + 1) / 3) ≤ 7 * (Nat.log 2 n₁ + 1) :=
      Nat.mul_div_le _ 3 |>.trans_eq rfl
    have : 3 * (7 * (Nat.log 2 n₁ + 1) / 3) ≤ 7 * L + 7 := by
      refine hq.trans ?_
      have : Nat.log 2 n₁ + 1 ≤ L + 1 := by omega
      calc 7 * (Nat.log 2 n₁ + 1) ≤ 7 * (L + 1) := Nat.mul_le_mul_left _ this
        _ = 7 * L + 7 := by ring
    rw [hd]; omega
  have hn₂lt : n₂ < 2 ^ (Nat.log 2 n₂ + 1) := Nat.lt_pow_succ_log_self (by norm_num) n₂
  have hexp : (Nat.log 2 n₂ + 1) * d ≤ turnConst * (L + 2) ^ 2 := by
    have hbase : 3 * ((Nat.log 2 n₂ + 1) * d) ≤ (L + 1) * (7 * L + 13) := by
      calc 3 * ((Nat.log 2 n₂ + 1) * d) = (Nat.log 2 n₂ + 1) * (3 * d) := by ring
        _ ≤ (L + 1) * (7 * L + 13) := Nat.mul_le_mul (by omega) h3d
    have h4 : 3 * (turnConst * (L + 2) ^ 2) = 12 * (L + 2) ^ 2 := by
      simp [turnConst]; ring
    nlinarith [hbase, sq_nonneg (L + 2)]
  calc n₂ ^ d ≤ (2 ^ (Nat.log 2 n₂ + 1)) ^ d := Nat.pow_le_pow_left hn₂lt.le d
    _ = 2 ^ ((Nat.log 2 n₂ + 1) * d) := by rw [← pow_mul]
    _ ≤ 2 ^ (turnConst * (L + 2) ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp

/-- §9.2, §9.5.  The multiplicative cost of the whole recursion of §9.4-§9.8 on an
instance with `n` points and `n₂` vertices in the second part: one turn per significant
reduction of `n₂`, plus the last turn. -/
def costFun (n n₂ b : ℕ) : ℕ := turnCost n ^ (2 * steps09 n₂ + 1 + b)

/-- The quasipolynomial that bounds `Babai.costFun`. -/
def costBound (n : ℕ) : ℕ := turnCost n ^ (14 * (Nat.log 2 n + 1) + 2)

theorem costFun_le_costBound {n n₂ b : ℕ} (h : n₂ ≤ n) (hb : b ≤ 1) :
    costFun n n₂ b ≤ costBound n := by
  refine Nat.pow_le_pow_right (one_le_turnCost n) ?_
  have : steps09 n₂ ≤ 7 * (Nat.log 2 n + 1) :=
    (steps09_le_log n₂).trans
      (Nat.mul_le_mul_left 7 (Nat.add_le_add_right (Nat.log_mono_right h) 1))
  omega

/-- §9.5.  **One turn pays for the recursive call it makes.**  If the instance `Y` handed to
the recursion lives on at most as many points as `X` and its `n₂` is *significantly
reduced* (§9.5: `n₂_new ≤ 0.9 n₂`), then one `Babai.turnCost` times the cost of the
recursion on `Y` is at most the cost of the recursion on `X`.

The hypothesis `0 < n₂` is not a restriction: for `n₂ = 0` the multiplicative cost of every
branch of step 9 is `0` (the cost of §9.6 and of §9.8 is `n₂`, and the exponent of §9.7 is
positive), so nothing has to be paid. -/
theorem turnCost_mul_costFun_le {n nY n₂ n₂Y b bY : ℕ} (hn : nY ≤ n) (hn₂ : 0 < n₂)
    (hred : 10 * n₂Y ≤ 9 * n₂) (hbY : bY ≤ 1) :
    turnCost n * costFun nY n₂Y bY ≤ costFun n n₂ b := by
  obtain ⟨k, rfl⟩ : ∃ k, n₂ = k + 1 := ⟨n₂ - 1, by omega⟩
  have hle : n₂Y ≤ reduce09 (k + 1) :=
    Nat.le_div_iff_mul_le (by norm_num) |>.2 (by omega)
  have hsteps : steps09 n₂Y + 1 ≤ steps09 (k + 1) := by
    rw [steps09_succ]
    exact Nat.add_le_add_right (steps09_mono _ _ hle) 1
  calc turnCost n * costFun nY n₂Y bY
      = turnCost n * turnCost nY ^ (2 * steps09 n₂Y + 1 + bY) := rfl
    _ ≤ turnCost n * turnCost n ^ (2 * steps09 n₂Y + 1 + bY) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (turnCost_mono hn) _)
    _ ≤ turnCost n * turnCost n ^ (2 * steps09 (k + 1) + b) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_turnCost n) (by omega))
    _ = turnCost n ^ (2 * steps09 (k + 1) + 1 + b) := by
        rw [show 2 * steps09 (k + 1) + 1 + b = (2 * steps09 (k + 1) + b) + 1 by omega,
          pow_succ]
        ring
    _ = costFun n (k + 1) b := rfl

/-- §9.5.  **One turn pays for the recursive call of the third kind of major progress.**
*"`X₂` moves from clique to UPCC while `n₂` does not increase"*: the instance `Y` handed
back has the hint (`b = 0`) and at most as many blocks, while the instance the turn started
from had none (`b = 1`).  The odd summand of the exponent of `Babai.costFun` is what pays
for that turn.  See the entry on §9.7, Cases 3a1, 3a2 and 3b in the corrected paper. -/
theorem turnCost_mul_costFun_le_of_hint {n nY n₂ n₂Y : ℕ} (hn : nY ≤ n) (hn₂ : n₂Y ≤ n₂) :
    turnCost n * costFun nY n₂Y 0 ≤ costFun n n₂ 1 := by
  have hsteps : steps09 n₂Y ≤ steps09 n₂ := steps09_mono _ _ hn₂
  calc turnCost n * costFun nY n₂Y 0
      = turnCost n * turnCost nY ^ (2 * steps09 n₂Y + 1 + 0) := rfl
    _ ≤ turnCost n * turnCost n ^ (2 * steps09 n₂Y + 1 + 0) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (turnCost_mono hn) _)
    _ ≤ turnCost n * turnCost n ^ (2 * steps09 n₂ + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_turnCost n) (by omega))
    _ = turnCost n ^ (2 * steps09 n₂ + 1 + 1) := by
        rw [show 2 * steps09 n₂ + 1 + 1 = (2 * steps09 n₂ + 1) + 1 by omega, pow_succ]
        ring
    _ = costFun n n₂ 1 := rfl

/-- §9.2.  *"at quasipolynomial multiplicative cost"*: a quasipolynomial per turn of the
recursion of §9.4-§9.8 (§9.7, Case 3a), and `O(log n)` turns (§9.5), is again a
quasipolynomial. -/
theorem quasiPolyBound_costBound : RAM.QuasiPolyBound costBound := by
  refine ⟨9, fun n => ?_⟩
  have key : ∀ L : ℕ, turnConst * (L + 2) ^ 2 * (14 * (L + 1) + 2) ≤ (L + 2) ^ 9 := by
    intro L
    have h1 : 14 * (L + 1) + 2 ≤ 16 * (L + 2) := by omega
    have h2 : (64 : ℕ) ≤ (L + 2) ^ 6 := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ (L + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    calc turnConst * (L + 2) ^ 2 * (14 * (L + 1) + 2)
        ≤ turnConst * (L + 2) ^ 2 * (16 * (L + 2)) := Nat.mul_le_mul_left _ h1
      _ = 64 * (L + 2) ^ 3 := by simp [turnConst]; ring
      _ ≤ (L + 2) ^ 6 * (L + 2) ^ 3 := Nat.mul_le_mul_right _ h2
      _ = (L + 2) ^ 9 := by ring
  calc costBound n
      = 2 ^ (turnConst * (Nat.log 2 n + 2) ^ 2 * (14 * (Nat.log 2 n + 1) + 2)) := by
        rw [costBound, turnCost, ← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 n + 2) ^ 9) := Nat.pow_le_pow_right (by norm_num) (key _)

end Babai
