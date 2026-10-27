/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12, opening paragraph: the recurrence `f(n) = O(m f(n/m) + n^c)`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# §12, opening paragraph: the recurrence

> Note that the solution to the recurrence `f(n) = O(m f(n/m) + n^c)` is
> `f(n) ≤ n^{c+1+o(1)}` assuming `m → ∞` as `n → ∞` and `c` is a constant.

**Reading.**  `m = m(n)` is a function of `n` with `m(n) → ∞`; `f` is a cost, so
`f ≥ 0`; `O(·)` means: for some constant `C` and all large `n`,
`f(n) ≤ C·(m(n)·f(⌊n/m(n)⌋) + n^c)`; and `n^{c+1+o(1)}` means: for every `ε > 0`,
`f(n) ≤ n^{c+1+ε}` for all large `n`.  In the paper `m = |Γ|` is the size of the set on
which the top action lives, so `m ≤ n` (the windows `n/m` are nonempty); this is the
hypothesis `hmn`.  Without it the claim is false: the term `m(n)·f(⌊n/m(n)⌋) = m(n)·f(0)`
is unbounded in terms of `n` when `m(n) > n`.

**Proof** (the standard unrolling, run as a strong induction).  Put `δ = ε/2` and
`e = c + 1 + δ`.  Once `m(n) ≥ M` with `M^δ ≥ 2C`, the induction hypothesis
`f(⌊n/m⌋) ≤ A⌊n/m⌋^e` gives `m·f(⌊n/m⌋) ≤ A n^e · m^{1-e} ≤ A n^e/(2C)`, hence
`f(n) ≤ A n^e/2 + C n^c ≤ A n^e` for `A ≥ 2C`.  The finitely many small `n` are absorbed
into `A`, and finally `A n^{c+1+δ} ≤ n^{c+1+ε}` once `n^δ ≥ A`.

Nothing later in the paper uses this sentence; it is recorded because it is a precise
mathematical claim of §12.
-/

namespace Babai

open Filter

/-- The bound of the induction: `f(n) ≤ A·n^e` for every `n ≥ 1`. -/
private theorem recurrence_bound {c C δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hC : 1 ≤ C)
    {m : ℕ → ℕ} {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) {M N : ℕ} (hM2 : 2 ≤ M)
    (hMC : 2 * C ≤ (M : ℝ) ^ δ)
    (hN : ∀ n ≥ N, M ≤ m n ∧ m n ≤ n ∧ f n ≤ C * ((m n : ℝ) * f (n / m n) + (n : ℝ) ^ c)) :
    ∀ n, 1 ≤ n →
      f n ≤ (2 * C + ∑ j ∈ Finset.range N, f j) * (n : ℝ) ^ (c + 1 + δ) := by
  set e := c + 1 + δ with he
  set A := 2 * C + ∑ j ∈ Finset.range N, f j with hA
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range N, f j := Finset.sum_nonneg fun j _ => hf0 j
  have hA2C : 2 * C ≤ A := by rw [hA]; linarith
  have he0 : 0 ≤ e := by rw [he]; linarith
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hne : (1 : ℝ) ≤ (n : ℝ) ^ e := Real.one_le_rpow hn1R he0
    by_cases hnN : n < N
    · -- a small `n`: absorbed into `A`
      have h1 : f n ≤ ∑ j ∈ Finset.range N, f j :=
        Finset.single_le_sum (fun j _ => hf0 j) (Finset.mem_range.2 hnN)
      have h2 : f n ≤ A := by rw [hA]; linarith
      have hA0 : 0 ≤ A := by rw [hA]; linarith
      calc f n ≤ A := h2
        _ = A * 1 := (mul_one A).symm
        _ ≤ A * (n : ℝ) ^ e := mul_le_mul_of_nonneg_left hne hA0
    · push Not at hnN
      obtain ⟨hMm, hmn, hrec⟩ := hN n hnN
      set k := m n with hk
      have hk2 : 2 ≤ k := le_trans hM2 hMm
      set q := n / k with hq
      have hq1 : 1 ≤ q := Nat.div_pos hmn (by omega)
      have hqn : q < n := Nat.div_lt_self (by omega) (by omega)
      have ihq := ih q hqn hq1
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hnR0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      -- `⌊n/k⌋^e ≤ n^e / k^e`
      have hqle : (q : ℝ) ≤ (n : ℝ) / (k : ℝ) := Nat.cast_div_le
      have hqe : (q : ℝ) ^ e ≤ (n : ℝ) ^ e / (k : ℝ) ^ e := by
        rw [← Real.div_rpow hnR0 hkR.le]
        exact Real.rpow_le_rpow (by positivity) hqle he0
      -- `k·2C ≤ k^e`, because `k^e = k·k^{c+δ}` and `k^{c+δ} ≥ k^δ ≥ M^δ ≥ 2C`
      have hke : (k : ℝ) * (2 * C) ≤ (k : ℝ) ^ e := by
        have hsplit : (k : ℝ) ^ e = (k : ℝ) * (k : ℝ) ^ (c + δ) := by
          rw [he, show c + 1 + δ = 1 + (c + δ) by ring, Real.rpow_add hkR, Real.rpow_one]
        have h1 : (k : ℝ) ^ δ ≤ (k : ℝ) ^ (c + δ) :=
          Real.rpow_le_rpow_of_exponent_le hk1R (by linarith)
        have h2 : (M : ℝ) ^ δ ≤ (k : ℝ) ^ δ :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hMm) hδ.le
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left (by linarith) hkR.le
      have hkeR : (0 : ℝ) < (k : ℝ) ^ e := Real.rpow_pos_of_pos hkR e
      have hCpos : (0 : ℝ) < C := by linarith
      -- `k·f(⌊n/k⌋) ≤ A·n^e/(2C)`
      have hmain : (k : ℝ) * f q ≤ A * (n : ℝ) ^ e / (2 * C) := by
        have hA0 : 0 ≤ A := by rw [hA]; linarith
        have hne0 : 0 ≤ (n : ℝ) ^ e := by positivity
        calc (k : ℝ) * f q ≤ (k : ℝ) * (A * (q : ℝ) ^ e) :=
              mul_le_mul_of_nonneg_left ihq hkR.le
          _ ≤ (k : ℝ) * (A * ((n : ℝ) ^ e / (k : ℝ) ^ e)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqe hA0) hkR.le
          _ = A * (n : ℝ) ^ e * ((k : ℝ) / (k : ℝ) ^ e) := by ring
          _ ≤ A * (n : ℝ) ^ e * (1 / (2 * C)) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA0 hne0)
              rw [div_le_div_iff₀ hkeR (by linarith)]
              linarith
          _ = A * (n : ℝ) ^ e / (2 * C) := by ring
      -- `n^c ≤ n^e`
      have hce : (n : ℝ) ^ c ≤ (n : ℝ) ^ e :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by rw [he]; linarith)
      have hparen : 0 ≤ (k : ℝ) * f q + (n : ℝ) ^ c := by
        have := hf0 q
        positivity
      calc f n ≤ C * ((k : ℝ) * f q + (n : ℝ) ^ c) := hrec
        _ ≤ C * (A * (n : ℝ) ^ e / (2 * C) + (n : ℝ) ^ c) :=
            mul_le_mul_of_nonneg_left (by linarith) hCpos.le
        _ = A * (n : ℝ) ^ e / 2 + C * (n : ℝ) ^ c := by field_simp
        _ ≤ A * (n : ℝ) ^ e / 2 + (A / 2) * (n : ℝ) ^ e := by
            have h1 : C * (n : ℝ) ^ c ≤ C * (n : ℝ) ^ e :=
              mul_le_mul_of_nonneg_left hce hCpos.le
            have h2 : C * (n : ℝ) ^ e ≤ (A / 2) * (n : ℝ) ^ e :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            linarith
        _ = A * (n : ℝ) ^ e := by ring

/-- **§12, opening paragraph** (Verification of top action).

> Note that the solution to the recurrence `f(n) = O(m f(n/m) + n^c)` is
> `f(n) ≤ n^{c+1+o(1)}` assuming `m → ∞` as `n → ∞` and `c` is a constant.

See the module docstring for the reading of `O(·)` and `o(1)`, and for why `m(n) ≤ n`
(`hmn`, from the paper's setting `m = |Γ|`) is needed. -/
theorem section12_recurrence {c : ℝ} (hc : 0 ≤ c) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hmn : ∀ᶠ n in atTop, m n ≤ n) {f : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f n)
    (hf : ∃ C : ℝ, ∀ᶠ n in atTop, f n ≤ C * ((m n : ℝ) * f (n / m n) + (n : ℝ) ^ c)) :
    ∀ ε > 0, ∀ᶠ n in atTop, f n ≤ (n : ℝ) ^ (c + 1 + ε) := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := hf
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  -- replace `C₀` by `C ≥ 1` (the bracket is nonnegative)
  have hrec : ∀ᶠ n in atTop, f n ≤ C * ((m n : ℝ) * f (n / m n) + (n : ℝ) ^ c) := by
    filter_upwards [hC₀] with n hn
    have hp : 0 ≤ (m n : ℝ) * f (n / m n) + (n : ℝ) ^ c := by
      have := hf0 (n / m n)
      positivity
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hpow : Tendsto (fun M : ℕ => (M : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  -- `M ≥ 2` with `M^δ ≥ 2C`
  obtain ⟨M, hM⟩ := ((hpow.eventually_ge_atTop (2 * C)).and
    (eventually_ge_atTop 2)).exists
  -- `N` beyond which `m(n) ≥ M`, `m(n) ≤ n` and the recurrence holds
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((hm.eventually_ge_atTop M).and hmn).and hrec)
  have hbound := recurrence_bound hc hδ hC1 hf0 hM.2 hM.1
    (fun n hn => ⟨(hN n hn).1.1, (hN n hn).1.2, (hN n hn).2⟩)
  set A := 2 * C + ∑ j ∈ Finset.range N, f j with hA
  filter_upwards [hpow.eventually_ge_atTop A, eventually_ge_atTop 1] with n hnA hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsplit : (n : ℝ) ^ (c + 1 + ε) = (n : ℝ) ^ (c + 1 + δ) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hnpos]
    congr 1
    rw [hδdef]; ring
  rw [hsplit]
  calc f n ≤ A * (n : ℝ) ^ (c + 1 + δ) := hbound n hn1
    _ = (n : ℝ) ^ (c + 1 + δ) * A := mul_comm _ _
    _ ≤ (n : ℝ) ^ (c + 1 + δ) * (n : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left hnA (by positivity)

end Babai
