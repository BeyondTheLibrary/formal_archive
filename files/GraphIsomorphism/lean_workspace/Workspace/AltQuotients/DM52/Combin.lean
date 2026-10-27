/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: the combinatorial Lemma 5.2A of Dixon–Mortimer.
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
# [DiM, Lemma 5.2A]

> **Lemma 5.2A.** Let `n > 6` and put `m := ⌊n/2⌋`.  Then:
> (i) For each divisor `t` of `n` with `3 ≤ t ≤ n/2` we have `{(n/t)!}^t t! < m!(n − m)!`;
> (ii) For each integer `t ≥ 3` and any integers `n₁, …, n_t` such that
> `0 < n₁ ≤ ⋯ ≤ n_t ≤ n/2` and `∑ nᵢ = n` we have
> `n₁! ⋯ n_t! / (m!(n − m)!) ≤ 1/(n − m) < 1/4`.

(The printed display of (ii) is garbled in our copy; the proof of the source shows the
product is at most `m! (n − m − t + 2)!`, which is at most `m!(n − m)!/(n − m)` for `t ≥ 3`,
and `n − m ≥ 4` for `n > 6`.)

Part (i) is `Babai.DM52.lemma_5_2A_i`, proved as in the source by induction on `k = n/t`.
Part (ii) is `Babai.DM52.lemma_5_2A_ii`, in the form `n₁! ⋯ n_t! ≤ m!(n − m − 1)!` (the
source's bound multiplied out), with the parts given as a multiset and only the hypotheses
`1 ≤ nᵢ ≤ m`, `∑ nᵢ ≥ m + 1` used.  The proof is the source's: by `r!s! ≤ (r − d)!(s + d)!`
for `r ≤ s` (moving points from a smaller part to a larger part increases the product), the
product is largest when one part is `m` and all the other parts but one are `1`.
-/

namespace Babai.DM52

open Nat

/-- Moving `d` points from a part of size `x` to a part of size `y ≥ x` does not decrease
`x! y!`. -/
theorem factorial_mul_factorial_le_move {x y d : ℕ} (hxy : x ≤ y) (hd : d ≤ x) :
    x ! * y ! ≤ (x - d)! * (y + d)! := by
  induction d with
  | zero => simp
  | succ d ih =>
    refine (ih (by omega)).trans ?_
    have e1 : (x - d)! = (x - (d + 1) + 1) * (x - (d + 1))! := by
      rw [← Nat.factorial_succ]; congr 1; omega
    have e2 : (y + (d + 1))! = (y + d + 1) * (y + d)! := by
      rw [show y + (d + 1) = (y + d) + 1 by ring]; exact Nat.factorial_succ _
    rw [e1, e2]
    have : x - (d + 1) + 1 ≤ y + d + 1 := by omega
    calc (x - (d + 1) + 1) * (x - (d + 1))! * (y + d)!
        ≤ (y + d + 1) * (x - (d + 1))! * (y + d)! := by gcongr
      _ = (x - (d + 1))! * ((y + d + 1) * (y + d)!) := by ring

/-- `r! s! ≤ 1! (r + s − 1)!` for `r, s ≥ 1` (the inequality of the proof of
[DiM, Lemma 5.2A (ii)]). -/
theorem factorial_mul_factorial_le_merge {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) :
    r ! * s ! ≤ (r + s - 1)! := by
  rcases le_total r s with h | h
  · have := factorial_mul_factorial_le_move (d := r - 1) h (by omega)
    rwa [show r - (r - 1) = 1 by omega, show s + (r - 1) = r + s - 1 by omega,
      Nat.factorial_one, one_mul] at this
  · have := factorial_mul_factorial_le_move (d := s - 1) h (by omega)
    rwa [show s - (s - 1) = 1 by omega, show r + (s - 1) = r + s - 1 by omega,
      Nat.factorial_one, one_mul, mul_comm] at this

/-- Two parts of size at most `M` with sum at least `M`: `x! y! ≤ M! (x + y − M)!`. -/
theorem factorial_mul_factorial_le_two {x y M : ℕ} (hx : x ≤ M) (hy : y ≤ M)
    (hM : M ≤ x + y) : x ! * y ! ≤ M ! * (x + y - M)! := by
  rcases le_total x y with h | h
  · have := factorial_mul_factorial_le_move (d := M - y) h (by omega)
    rwa [show x - (M - y) = x + y - M by omega, show y + (M - y) = M by omega,
      mul_comm (x + y - M)!] at this
  · have := factorial_mul_factorial_le_move (d := M - x) h (by omega)
    rw [show y - (M - x) = x + y - M by omega, show x + (M - x) = M by omega,
      mul_comm (x + y - M)!] at this
    rw [mul_comm]; exact this

/-- Merging all parts: `∏ nᵢ! ≤ (∑ nᵢ − c + 1)!` for `c ≥ 1` parts, all at least `1`. -/
theorem prod_factorial_le_merge (P : Multiset ℕ) (hP : ∀ a ∈ P, 1 ≤ a)
    (hc : 1 ≤ Multiset.card P) :
    (P.map Nat.factorial).prod ≤ (P.sum - Multiset.card P + 1)! := by
  induction P using Multiset.induction_on with
  | empty => simp at hc
  | cons a Q ih =>
    have ha : 1 ≤ a := hP a (Multiset.mem_cons_self a Q)
    have hQ : ∀ b ∈ Q, 1 ≤ b := fun b hb => hP b (Multiset.mem_cons_of_mem hb)
    have hsum : Multiset.card Q ≤ Q.sum := by
      have := Multiset.card_nsmul_le_sum (s := Q) (a := 1) (fun b hb => hQ b hb)
      simpa using this
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons]
    rcases Nat.eq_zero_or_pos (Multiset.card Q) with h0 | hpos
    · rw [Multiset.card_eq_zero.mp h0]
      simp [Nat.sub_add_cancel ha]
    · calc a ! * (Q.map Nat.factorial).prod ≤ a ! * (Q.sum - Multiset.card Q + 1)! :=
            Nat.mul_le_mul_left _ (ih hQ hpos)
        _ ≤ (a + (Q.sum - Multiset.card Q + 1) - 1)! :=
            factorial_mul_factorial_le_merge ha (by omega)
        _ = (a + Q.sum - (Multiset.card Q + 1) + 1)! := by congr 1; omega

/-- **[DiM, Lemma 5.2A (ii)]**, in the form proved there: for `t ≥ 3` parts `nᵢ` with
`1 ≤ nᵢ ≤ M` and `∑ nᵢ ≥ M + 1`, `n₁! ⋯ n_t! ≤ M! (∑ nᵢ − M − 1)!`.  With `M = m = ⌊n/2⌋`
and `∑ nᵢ = n` this is `n₁! ⋯ n_t! ≤ m!(n − m)!/(n − m)`. -/
theorem lemma_5_2A_ii (M : ℕ) : ∀ (P : Multiset ℕ), 3 ≤ Multiset.card P →
    (∀ a ∈ P, 1 ≤ a ∧ a ≤ M) → M + 1 ≤ P.sum →
    (P.map Nat.factorial).prod ≤ M ! * (P.sum - M - 1)! := by
  intro P
  induction h : Multiset.card P using Nat.strong_induction_on generalizing P with
  | _ c ihc =>
  intro hc hP hS
  -- write `P = a :: b :: R`
  obtain ⟨a, P1, rfl⟩ : ∃ a P1, P = a ::ₘ P1 := by
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card P)
    exact ⟨a, _, (Multiset.cons_erase ha).symm⟩
  obtain ⟨b, R, rfl⟩ : ∃ b R, P1 = b ::ₘ R := by
    have : 0 < Multiset.card P1 := by simp at h; omega
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.mp this
    exact ⟨b, _, (Multiset.cons_erase hb).symm⟩
  simp only [Multiset.card_cons] at h
  have hcR : 1 ≤ Multiset.card R := by omega
  have ha := hP a (by simp)
  have hb := hP b (by simp)
  have hR : ∀ x ∈ R, 1 ≤ x ∧ x ≤ M := fun x hx => hP x (by simp [hx])
  have hRsum : Multiset.card R ≤ R.sum := by
    have := Multiset.card_nsmul_le_sum (s := R) (a := 1) (fun x hx => (hR x hx).1)
    simpa using this
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at hS ⊢
  -- `p ≤ z` are `a, b` in increasing order
  set p := min a b with hp
  set z := max a b with hz
  have hpz : p ≤ z := min_le_max
  have hpz_sum : p + z = a + b := min_add_max a b
  have hab : a ! * b ! = p ! * z ! := by
    rcases le_total a b with h' | h'
    · rw [hp, hz, min_eq_left h', max_eq_right h']
    · rw [hp, hz, min_eq_right h', max_eq_left h', mul_comm]
  have hp1 : 1 ≤ p := le_min ha.1 hb.1
  have hzM : z ≤ M := max_le ha.2 hb.2
  have hprod : a ! * (b ! * (R.map Nat.factorial).prod) =
      p ! * z ! * (R.map Nat.factorial).prod := by rw [← mul_assoc, hab]
  rw [hprod]
  by_cases hbig : M + 1 ≤ z + p
  · -- move `M − z` points from `p` to `z`, making a part of size `M`, and merge the rest
    have hmove := factorial_mul_factorial_le_move (d := M - z) hpz (by omega)
    rw [show z + (M - z) = M by omega] at hmove
    have hmerge := prod_factorial_le_merge ((p - (M - z)) ::ₘ R)
      (by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · omega
        · exact (hR x hx).1)
      (by simp)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons]
      at hmerge
    calc p ! * z ! * (R.map Nat.factorial).prod
        ≤ (p - (M - z))! * M ! * (R.map Nat.factorial).prod := Nat.mul_le_mul_right _ hmove
      _ = M ! * ((p - (M - z))! * (R.map Nat.factorial).prod) := by ring
      _ ≤ M ! * (p - (M - z) + R.sum - (Multiset.card R + 1) + 1)! :=
          Nat.mul_le_mul_left _ hmerge
      _ ≤ M ! * (a + (b + R.sum) - M - 1)! := by
          apply Nat.mul_le_mul_left
          apply Nat.factorial_le
          omega
  · -- merge `p` into `z`: the part `z + p − 1 ≤ M`
    push Not at hbig
    have hmerge := factorial_mul_factorial_le_merge hp1 (le_trans hp1 hpz)
    set Q := (p + z - 1) ::ₘ R with hQ
    have hQP : ∀ x ∈ Q, 1 ≤ x ∧ x ≤ M := by
      intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · omega
      · exact hR x hx
    have hQprod : (Q.map Nat.factorial).prod = (p + z - 1)! * (R.map Nat.factorial).prod := by
      simp [hQ]
    have hQsum : Q.sum = a + (b + R.sum) - 1 := by simp [hQ]; omega
    have step : p ! * z ! * (R.map Nat.factorial).prod ≤ (Q.map Nat.factorial).prod := by
      rw [hQprod]; exact Nat.mul_le_mul_right _ hmerge
    refine step.trans ?_
    rcases Nat.lt_or_ge (Multiset.card R) 2 with h1 | h2
    · -- `R = {x}`: two parts
      obtain ⟨x, rfl⟩ : ∃ x, R = {x} := Multiset.card_eq_one.mp (by omega)
      have hx := hR x (by simp)
      rw [hQprod]
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.sum_singleton]
        at hS ⊢
      have := factorial_mul_factorial_le_two (x := p + z - 1) (y := x) (M := M) (by omega)
        hx.2 (by omega)
      refine this.trans (Nat.mul_le_mul_left _ (Nat.factorial_le (by omega)))
    · rcases Nat.lt_or_ge (a + (b + R.sum)) (M + 2) with hS1 | hS2
      · -- `∑ = M + 1`: merge everything
        have := prod_factorial_le_merge Q (fun x hx => (hQP x hx).1) (by simp [hQ])
        refine this.trans ?_
        calc (Q.sum - Multiset.card Q + 1)! ≤ M ! := Nat.factorial_le (by simp [hQ] at *; omega)
          _ ≤ M ! * (a + (b + R.sum) - M - 1)! :=
              Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
      · have hcQ : Multiset.card Q = Multiset.card R + 1 := by simp [hQ]
        have := ihc (Multiset.card Q) (by omega) Q rfl (by omega) hQP (by omega)
        refine this.trans (Nat.mul_le_mul_left _ (Nat.factorial_le (by omega)))

/-- `2^t < t!` for `t ≥ 4`. -/
theorem two_pow_lt_factorial {t : ℕ} (ht : 4 ≤ t) : 2 ^ t < t ! := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [pow_succ, Nat.factorial_succ]
    nlinarith

/-- The step of the induction in [DiM, Lemma 5.2A (i)]: passing from `n = kt` to
`n + t = (k+1)t` multiplies `m!(n − m)!` by at least `(k+1)^t`. -/
theorem middle_factorial_step {k t : ℕ} (ht : 2 ≤ t) :
    (k + 1) ^ t * ((k * t / 2)! * (k * t - k * t / 2)!) ≤
      ((k + 1) * t / 2)! * ((k + 1) * t - (k + 1) * t / 2)! := by
  set n := k * t with hn
  set m := n / 2 with hm
  have hn' : (k + 1) * t = n + t := by rw [hn]; ring
  rw [hn']
  set m' := (n + t) / 2 with hm'
  have hkm : k ≤ m := by
    rw [hm, hn]
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    nlinarith
  have hmm : m ≤ m' := Nat.div_le_div_right (by omega)
  have hnm : n - m ≤ n + t - m' := by omega
  have hj : (m' - m) + ((n + t - m') - (n - m)) = t := by omega
  have h1 : m ! * (m + 1) ^ (m' - m) ≤ m' ! := by
    have := Nat.factorial_mul_pow_le_factorial (m := m) (n := m' - m)
    rwa [show m + (m' - m) = m' by omega] at this
  have h2 : (n - m)! * (n - m + 1) ^ ((n + t - m') - (n - m)) ≤ (n + t - m')! := by
    have := Nat.factorial_mul_pow_le_factorial (m := n - m) (n := (n + t - m') - (n - m))
    rwa [show n - m + ((n + t - m') - (n - m)) = n + t - m' by omega] at this
  have h3 : (k + 1) ^ (m' - m) ≤ (m + 1) ^ (m' - m) := Nat.pow_le_pow_left (by omega) _
  have h4 : (k + 1) ^ ((n + t - m') - (n - m)) ≤ (n - m + 1) ^ ((n + t - m') - (n - m)) :=
    Nat.pow_le_pow_left (by omega) _
  calc (k + 1) ^ t * (m ! * (n - m)!)
      = (m ! * (k + 1) ^ (m' - m)) * ((n - m)! * (k + 1) ^ ((n + t - m') - (n - m))) := by
        have : (k + 1) ^ t = (k + 1) ^ (m' - m) * (k + 1) ^ ((n + t - m') - (n - m)) := by
          rw [← pow_add, hj]
        rw [this]; ring
    _ ≤ (m ! * (m + 1) ^ (m' - m)) * ((n - m)! * (n - m + 1) ^ ((n + t - m') - (n - m))) := by
        gcongr
    _ ≤ m' ! * (n + t - m')! := Nat.mul_le_mul h1 h2

/-- **[DiM, Lemma 5.2A (i)]**: for `n = kt > 6` with `t ≥ 3` and `k ≥ 2` (that is,
`3 ≤ t ≤ n/2`), `(k!)^t t! < m!(n − m)!` where `m = ⌊n/2⌋`.  The proof is the source's
induction on `k`, from `k = 2` (`t > 3`) and `k = 3` (`t = 3`). -/
theorem lemma_5_2A_i {k t : ℕ} (hk : 2 ≤ k) (ht : 3 ≤ t) (hn : 6 < k * t) :
    (k !) ^ t * t ! < (k * t / 2)! * (k * t - k * t / 2)! := by
  -- the induction step
  have step : ∀ k, (k !) ^ t * t ! < (k * t / 2)! * (k * t - k * t / 2)! →
      ((k + 1)!) ^ t * t ! < ((k + 1) * t / 2)! * ((k + 1) * t - (k + 1) * t / 2)! := by
    intro k ih
    calc ((k + 1)!) ^ t * t ! = (k + 1) ^ t * ((k !) ^ t * t !) := by
          rw [Nat.factorial_succ, mul_pow]; ring
      _ < (k + 1) ^ t * ((k * t / 2)! * (k * t - k * t / 2)!) :=
          Nat.mul_lt_mul_of_pos_left ih (by positivity)
      _ ≤ _ := middle_factorial_step (by omega)
  rcases Nat.lt_or_ge t 4 with h3 | h4
  · -- `t = 3`: base `k = 3`
    obtain rfl : t = 3 := by omega
    have hk3 : 3 ≤ k := by omega
    induction k, hk3 using Nat.le_induction with
    | base => decide
    | succ k hk ih => exact step k (ih (by omega) (by omega))
  · -- `t ≥ 4`: base `k = 2`
    induction k, hk using Nat.le_induction with
    | base =>
      rw [show 2 * t / 2 = t by omega, show 2 * t - t = t by omega, Nat.factorial_two]
      have := two_pow_lt_factorial h4
      exact Nat.mul_lt_mul_of_pos_right this (Nat.factorial_pos _)
    | succ k hk ih => exact step k (ih (by nlinarith))

end Babai.DM52
