/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.4 (Cost estimate).
-/
import Workspace.Luks.ReduceToJohnson

/-!
# §11.4 Cost estimate

> By the cost of the algorithm we mean the number of group operations performed on the
> domain `Ω`.  For a real number `x ≥ 1`, let `T(x)` denote the worst-case cost of solving
> String Isomorphism for strings of length `≤ x`.  Let `T_trans(x)` denote the same
> quantity restricted to transitive groups and `T_Jh(x)` the same quantity further
> restricted to the case when `G` acts on a minimal system of imprimitivity as a Johnson
> group of order `≥ m^{1+log₂ m}` where `m` is the number of blocks (`2 ≤ m ≤ x`).

What is mathematics here — and is formalized — is the *solution of the recurrences*: the
steps (i'), (ii') ⟹ (iii), then (iii) with Eq. (65) ⟹ Eq. (66), and finally the resolution
of Eq. (66) to `T(x) = q(x)^{O(log x)}`, and the analogous resolution of item (v).  The
functions `T`, `T_trans`, `T_Jh` themselves are the cost of an algorithm in a machine model
that the development does not fix, so they appear here as arbitrary real functions
satisfying the paper's inequalities; see the corrected paper.
-/

namespace Babai

/-- §11.4, item **(iii)**.

> (i') `T(x) ≤ 1.1 T_trans(x)`.  (The factor 1.1 absorbs the additive polynomial term.)
> (ii') `T_trans(x) ≤ 1.1 x T_Jh(x)`.
> Combining inequalities (i') and (ii') we obtain (iii) `T(x) ≤ 2x T_Jh(x)`. -/
theorem cost_iii {T Ttrans TJh : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hTJh : 0 ≤ TJh x)
    (hi : T x ≤ 1.1 * Ttrans x) (hii : Ttrans x ≤ 1.1 * x * TJh x) :
    T x ≤ 2 * x * TJh x := by
  nlinarith

/-- §11.4, **Eq. (66)**.

> Our contribution is an inequality of the form `T_Jh(x) ≤ q(x) T(4x/5)`  (65)
> where `q(x)` is a quasipolynomial function.  Combining with item (iii) we obtain
> `T(x) ≤ 2x q(x) T(4x/5) < q(x)² T(4x/5)`.  (66)

The strict inequality needs `2x < q(x)` and `T(4x/5) > 0`, which the paper leaves implicit
(`q` is quasipolynomial, hence eventually larger than `2x`). -/
theorem cost_66 {T TJh q : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) (hTJh : 0 ≤ TJh x)
    (hT : 0 < T (4 * x / 5)) (hq : 2 * x < q x)
    (hiii : T x ≤ 2 * x * TJh x) (h65 : TJh x ≤ q x * T (4 * x / 5)) :
    T x ≤ 2 * x * q x * T (4 * x / 5) ∧
      2 * x * q x * T (4 * x / 5) < q x ^ 2 * T (4 * x / 5) := by
  have hqpos : (0 : ℝ) < q x := lt_of_le_of_lt (by linarith) hq
  constructor
  · nlinarith
  · nlinarith [mul_pos (sub_pos.2 hq) (mul_pos hqpos hT)]

/-- §11.4, the resolution of Eq. (66):

> `T(x) ≤ 2x q(x) T(4x/5) < q(x)² T(4x/5)`  (66)
> which resolves to `T(x) = q(x)^{O(log x)}`, yielding the desired quasipolynomial bound
> on `T(x)`.

Precisely: if `T(x) ≤ 1` below the threshold `x₀` and `T(x) ≤ q(x)² T(4x/5)` above it,
then `T(x) ≤ q(x)^{2n}` as soon as `x < x₀ (5/4)^n`.  Since the least such `n` is
`O(log x)` (`Babai.cost_resolution_log`), this is `T(x) = q(x)^{O(log x)}`. -/
theorem cost_resolution {T q : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hbase : ∀ x, x < x₀ → T x ≤ 1)
    (hq1 : ∀ x, 1 ≤ q x)
    (hqmono : ∀ a b : ℝ, 0 < a → a ≤ b → q a ≤ q b)
    (hTnonneg : ∀ x, 0 ≤ T x)
    (hrec : ∀ x, x₀ ≤ x → T x ≤ q x ^ 2 * T (4 * x / 5)) :
    ∀ (n : ℕ) (x : ℝ), 0 < x → x < x₀ * (5 / 4) ^ n → T x ≤ q x ^ (2 * n) := by
  intro n
  induction n with
  | zero =>
    intro x _ hlt
    simpa using hbase x (by simpa using hlt)
  | succ m ih =>
    intro x hx hlt
    have hq0 : (0 : ℝ) ≤ q x := le_trans zero_le_one (hq1 x)
    rcases lt_or_ge x x₀ with h | h
    · calc T x ≤ 1 := hbase x h
        _ ≤ q x ^ (2 * (m + 1)) := one_le_pow₀ (hq1 x)
    · have hstep : x₀ * (5 / 4 : ℝ) ^ (m + 1) = (x₀ * (5 / 4) ^ m) * (5 / 4) := by ring
      rw [hstep] at hlt
      have h45 : (0 : ℝ) < 4 * x / 5 := by linarith
      have hlt' : 4 * x / 5 < x₀ * (5 / 4) ^ m := by linarith
      have hsub := ih (4 * x / 5) h45 hlt'
      have hqle : q (4 * x / 5) ≤ q x := hqmono _ _ h45 (by linarith)
      have hq45 : (0 : ℝ) ≤ q (4 * x / 5) := le_trans zero_le_one (hq1 _)
      calc T x ≤ q x ^ 2 * T (4 * x / 5) := hrec x h
        _ ≤ q x ^ 2 * q (4 * x / 5) ^ (2 * m) := by
            exact mul_le_mul_of_nonneg_left hsub (by positivity)
        _ ≤ q x ^ 2 * q x ^ (2 * m) := by
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq45 hqle _) (by positivity)
        _ = q x ^ (2 * (m + 1)) := by ring

/-- §11.4: the exponent in `Babai.cost_resolution` is `O(log x)`: the bound applies with
`n = ⌈log_{5/4}(x/x₀)⌉ + 1`. -/
theorem cost_resolution_log {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : 0 < x) :
    x < x₀ * (5 / 4) ^ (⌈Real.logb (5 / 4) (x / x₀)⌉₊ + 1) := by
  set n : ℕ := ⌈Real.logb (5 / 4) (x / x₀)⌉₊ + 1 with hn
  have hb : (1 : ℝ) < 5 / 4 := by norm_num
  have hdiv : 0 < x / x₀ := div_pos hx hx₀
  have hlt : Real.logb (5 / 4) (x / x₀) < (n : ℝ) := by
    have h1 : Real.logb (5 / 4) (x / x₀) ≤ (⌈Real.logb (5 / 4) (x / x₀)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈Real.logb (5 / 4) (x / x₀)⌉₊ : ℝ)) < (n : ℝ) := by
      rw [hn]
      push_cast
      linarith
    linarith
  have := (Real.logb_lt_iff_lt_rpow hb hdiv).1 hlt
  rw [Real.rpow_natCast] at this
  calc x = (x / x₀) * x₀ := by field_simp
    _ < (5 / 4 : ℝ) ^ n * x₀ := by
        exact (mul_lt_mul_of_pos_right this hx₀)
    _ = x₀ * (5 / 4) ^ n := by ring

/-- §11.4, the resolution of item **(v)**.

> (iv) `T_Jh(x) = T_Jh(x,x)`
> (v) `T_Jh(x,y) ≤ q₁(x) (T(4x/5) + T_Jh(x, 0.9y))`
> where `q₁(x)` is a quasipolynomial function.  An upper bound of the form
> `T_Jh(x,y) ≤ T(4x/5) q₁(x)^{O(log y)}` follows, hence Eq. (65) with
> `q(x) = q₁(x)^{O(log x)}`.

Here `f y = T_Jh(x,y)` for a fixed `x`, `A = T(4x/5)` and `c = q₁(x)`; "For
`y < max{5, ℓ(x)}` we set `T(x,y) = 0`" is `hbase` with `y₀ = max{5, ℓ(x)}`.  The bound
obtained is `T_Jh(x,y) ≤ n c^n A` for `y < y₀ (10/9)^n`, and the least such `n` is
`O(log y)`. -/
theorem costJh_resolution {f : ℝ → ℝ} {c A y₀ : ℝ} (hc : 1 ≤ c) (hA : 0 ≤ A)
    (hbase : ∀ y, y < y₀ → f y ≤ 0)
    (hrec : ∀ y, y₀ ≤ y → f y ≤ c * (A + f (0.9 * y))) :
    ∀ (n : ℕ) (y : ℝ), y < y₀ * (10 / 9) ^ n → f y ≤ (n : ℝ) * c ^ n * A := by
  intro n
  induction n with
  | zero =>
    intro y hy
    simpa using hbase y (by simpa using hy)
  | succ m ih =>
    intro y hy
    have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc
    have hcm : (0 : ℝ) ≤ c ^ (m + 1) := by positivity
    rcases lt_or_ge y y₀ with h | h
    · calc f y ≤ 0 := hbase y h
        _ ≤ ((m : ℝ) + 1) * c ^ (m + 1) * A := by positivity
        _ = ((m + 1 : ℕ) : ℝ) * c ^ (m + 1) * A := by push_cast; ring
    · have hstep : y₀ * (10 / 9 : ℝ) ^ (m + 1) = (y₀ * (10 / 9) ^ m) * (10 / 9) := by ring
      rw [hstep] at hy
      have hy' : 0.9 * y < y₀ * (10 / 9) ^ m := by
        norm_num
        linarith
      have hsub := ih (0.9 * y) hy'
      have hccm : c ≤ c ^ (m + 1) := le_self_pow₀ hc (by omega)
      calc f y ≤ c * (A + f (0.9 * y)) := hrec y h
        _ ≤ c * (A + (m : ℝ) * c ^ m * A) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hc0
        _ = c * A + (m : ℝ) * (c * c ^ m) * A := by ring
        _ = c * A + (m : ℝ) * c ^ (m + 1) * A := by rw [pow_succ]; ring
        _ ≤ c ^ (m + 1) * A + (m : ℝ) * c ^ (m + 1) * A := by nlinarith
        _ = ((m + 1 : ℕ) : ℝ) * c ^ (m + 1) * A := by push_cast; ring

end Babai
