/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree at least 10.
-/
import Workspace.AltQuotients.DM52.Transport

/-!
# Primitive subgroups of small index in `A_n`, `n ≥ 10`

The first paragraph of the proof of [DiM, Thm. 5.2A] (p. 148): "if `G` is primitive, and
`G ≠ A`, then by Bochert's Theorem (Theorem 3.3B) we have `h ≥ ½⌊(n+1)/2⌋!`.  When `n ≥ 15`
or `n = 13`, this implies that `h ≥ C(n, m)` (see Exercise 5.2.1) which is contrary to
hypothesis.  Hence, if `G` is primitive, then either `n ≤ 12`, `n = 14` or `G = A` … An
examination of the primitive groups of degrees up to 12 and of degree 14 yields the list of
exceptional primitive groups given in part (iii) of the theorem (Exercise 5.2.3–5.2.6)."

This file does the degrees `n ≥ 10`: there is no exceptional group
(`alternatingGroup_le_of_primitive_of_ten_le`).  Degrees `13` and `≥ 15` are Bochert's
theorem with Exercise 5.2.1; degrees `10, 11, 12, 14` are Exercises 5.2.4–5.2.6, done in the
style of the hint of Exercise 5.2.5: Theorem 3.3E (through Sylow's theorem,
`Babai.DM52.alternatingGroup_le_of_not_dvd_index`) forces many primes to divide the index
`h`, and the remaining orders are excluded by counting Sylow subgroups.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

section General

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The arithmetic facts about a primitive `G < A` used in all the degree-by-degree
arguments: with `h = |A : G|`, `2|G|h = n!`, `|S : G| = 2h`, `n ∣ |G|`, and Bochert's bound
`|G|·(n - ⌊n/2⌋)! ≤ n!`. -/
theorem prim_facts {G : Subgroup (Perm α)} (hGA : G ≤ alternatingGroup α)
    (hG : IsPreprimitive G α) (hA : ¬ alternatingGroup α ≤ G) (hn : 2 ≤ Fintype.card α) :
    2 * Nat.card G * G.relIndex (alternatingGroup α) = (Fintype.card α)! ∧
      G.index = 2 * G.relIndex (alternatingGroup α) ∧
      Fintype.card α ∣ Nat.card G ∧
      Nat.card G * (Fintype.card α - Fintype.card α / 2)! ≤ (Fintype.card α)! := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hn
  have hidx : G.index = 2 * G.relIndex (alternatingGroup α) := by
    rw [← Subgroup.relIndex_mul_index hGA, alternatingGroup.index_eq_two, mul_comm]
  have hcard : Nat.card G * G.index = (Fintype.card α)! := by
    rw [G.card_mul_index, Nat.card_perm, Nat.card_eq_fintype_card]
  refine ⟨by rw [← hcard, hidx]; ring, hidx, ?_, bochert G hG hA⟩
  -- `n ∣ |G|`: orbit–stabilizer for the transitive action
  obtain ⟨a⟩ : Nonempty α := inferInstance
  have h1 := MulAction.index_stabilizer G a
  rw [MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card] at h1
  rw [← h1]
  exact (stabilizer G a).index_dvd_card

/-- Theorem 3.3E in the form used: for a prime `p` with `p + 3 ≤ n`, a primitive `G < A`
has `p ∣ 2|A : G|`. -/
theorem prime_dvd_two_mul_relIndex {G : Subgroup (Perm α)} (hGA : G ≤ alternatingGroup α)
    (hG : IsPreprimitive G α) (hA : ¬ alternatingGroup α ≤ G) {p : ℕ} (hp : p.Prime)
    (hpn : p + 3 ≤ Fintype.card α) : p ∣ 2 * G.relIndex (alternatingGroup α) := by
  have hidx := (prim_facts hGA hG hA (by omega)).2.1
  by_contra h
  rw [← hidx] at h
  exact hA (alternatingGroup_le_of_not_dvd_index hG hp hpn h)

/-- Theorem 3.3E in the form used: for an odd prime `q` with `q + 3 ≤ n`, a primitive
`G < A` has `q ∣ |A : G|`. -/
theorem odd_prime_dvd_relIndex {G : Subgroup (Perm α)} (hGA : G ≤ alternatingGroup α)
    (hG : IsPreprimitive G α) (hA : ¬ alternatingGroup α ≤ G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqn : q + 3 ≤ Fintype.card α) : q ∣ G.relIndex (alternatingGroup α) :=
  Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    (prime_dvd_two_mul_relIndex hGA hG hA hq hqn)

/-- **Degrees `13` and `≥ 15`** ([DiM, proof of Thm. 5.2A], Bochert's theorem with
Exercise 5.2.1): a primitive `G ≤ A` with `|A : G| < C(n, ⌊n/2⌋)` is `A`. -/
theorem alternatingGroup_le_of_bochert {G : Subgroup (Perm α)} (hGA : G ≤ alternatingGroup α)
    (hG : IsPreprimitive G α) (hn : 15 ≤ Fintype.card α ∨ Fintype.card α = 13)
    (hidx : G.relIndex (alternatingGroup α) < (Fintype.card α).choose (Fintype.card α / 2)) :
    alternatingGroup α ≤ G := by
  by_contra hA
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by omega)
  have h5 := choose_lt_half_factorial _ hn
  set n := Fintype.card α
  set h := G.relIndex (alternatingGroup α)
  have hn2 : n - n / 2 = (n + 1) / 2 := by omega
  rw [hn2] at h4
  -- `n! = 2|G|h < |G|·⌈n/2⌉! ≤ n!`
  have hG0 : 0 < Nat.card G := Nat.card_pos
  have : 2 * Nat.card G * h < Nat.card G * ((n + 1) / 2)! := by
    calc 2 * Nat.card G * h = Nat.card G * (2 * h) := by ring
      _ < Nat.card G * ((n + 1) / 2)! := by
        apply Nat.mul_lt_mul_of_pos_left _ hG0
        calc 2 * h < 2 * n.choose (n / 2) := by omega
          _ < ((n + 1) / 2)! := h5
  omega

/-- **Degree 14** ([DiM, Exercise 5.2.4], "Using Theorems 3.3B and 3.3E show that there is no
exceptional primitive group of degree 14"): Theorem 3.3E makes `3, 5, 7, 11` divide `h`, so
`1155 ∣ h`, while Bochert gives `h ≥ 7!/2 = 2520` and `h < C(14,7) = 3432`. -/
theorem alternatingGroup_le_of_card_eq_fourteen {G : Subgroup (Perm α)}
    (hGA : G ≤ alternatingGroup α) (hG : IsPreprimitive G α) (hn : Fintype.card α = 14)
    (hidx : G.relIndex (alternatingGroup α) < (Fintype.card α).choose (Fintype.card α / 2)) :
    alternatingGroup α ≤ G := by
  by_contra hA
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by omega)
  have odd_dvd := fun q hq hq2 hqn => odd_prime_dvd_relIndex (q := q) hGA hG hA hq hq2 hqn
  have d3 := odd_dvd 3 Nat.prime_three (by norm_num) (by omega)
  have d5 := odd_dvd 5 Nat.prime_five (by norm_num) (by omega)
  have d7 := odd_dvd 7 (by norm_num) (by norm_num) (by omega)
  have d11 := odd_dvd 11 (by norm_num) (by norm_num) (by omega)
  rw [hn] at h1 h4 hidx
  generalize G.relIndex (alternatingGroup α) = h at *
  have hG0 : 0 < Nat.card G := Nat.card_pos
  have e1 : 2 * Nat.card G * h = 87178291200 := by rw [h1]; decide
  have e4 : Nat.card G * 5040 ≤ 87178291200 := by
    have : (14 - 14 / 2)! = 5040 := by decide
    rw [this] at h4; rw [← show (14 : ℕ)! = 87178291200 by decide]; exact h4
  have e5 : h < 3432 := by
    have : (14 : ℕ).choose (14 / 2) = 3432 := by decide
    omega
  -- `h ≥ 2520`
  have hh : 2520 ≤ h := by nlinarith
  obtain ⟨k, rfl⟩ : 1155 ∣ h := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7) this d7
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 105 11) this d11
  omega

end General

/-! ### Degrees 10, 11 and 12 -/

section Models

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The `11`-cycle `(0 1 ⋯ 10)` of `Fin 11`. -/
def cyc11 : Perm (Fin 11) :=
  ofVec ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0]
    ![10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (by decide)

/-- `x ↦ 2x` on `ℤ/11`, an odd permutation normalizing `⟨cyc11⟩`. -/
def mul11 : Perm (Fin 11) :=
  ofVec ![0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9]
    ![0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5] (by decide)

/-- The `11`-cycle `(0 1 ⋯ 10)` of `Fin 12`. -/
def cyc12 : Perm (Fin 12) :=
  ofVec ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 11]
    ![10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11] (by decide)

/-- `x ↦ 2x` on `ℤ/11 ⊆ Fin 12`, an odd permutation normalizing `⟨cyc12⟩`. -/
def mul12 : Perm (Fin 12) :=
  ofVec ![0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9, 11]
    ![0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11] (by decide)

/-- `(0 1 2 3 4)(5 6 7 8 9)` in `Fin 10`. -/
def cyc10 : Perm (Fin 10) :=
  ofVec ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8] (by decide)

/-- `(0 5)(1 6)(2 7)(3 8)(4 9)`, an odd permutation commuting with `cyc10`. -/
def swp10 : Perm (Fin 10) :=
  ofVec ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4]
    ![5, 6, 7, 8, 9, 0, 1, 2, 3, 4] (by decide)

theorem mul11_conj : mul11 * cyc11 * mul11⁻¹ = cyc11 ^ (2 : ℤ) := by decide
theorem mul11_sign : sign mul11 = -1 := by decide
theorem mul12_conj : mul12 * cyc12 * mul12⁻¹ = cyc12 ^ (2 : ℤ) := by decide
theorem mul12_sign : sign mul12 = -1 := by decide
theorem swp10_conj : swp10 * cyc10 * swp10⁻¹ = cyc10 ^ (1 : ℤ) := by decide
theorem swp10_sign : sign swp10 = -1 := by decide

theorem orderOf_cyc11 : orderOf cyc11 = 11 :=
  orderOf_eq_prime (by decide) (by decide)
theorem orderOf_cyc12 : orderOf cyc12 = 11 :=
  orderOf_eq_prime (by decide) (by decide)
theorem orderOf_cyc10 : orderOf cyc10 = 5 :=
  orderOf_eq_prime (by decide) (by decide)

theorem cycleType_cyc11 : cyc11.cycleType = {11} :=
  cycleType_eq_of_orderOf_prime (by norm_num) orderOf_cyc11 (by norm_num)
theorem cycleType_cyc12 : cyc12.cycleType = {11} :=
  cycleType_eq_of_orderOf_prime (by norm_num) orderOf_cyc12 (by norm_num)

/-- An element of order `5` of `Sym(10)` that is not a `5`-cycle has cycle type `5²`. -/
theorem cycleType_of_orderOf_five {x : Perm (Fin 10)} (hx : orderOf x = 5)
    (hxc : ¬ (x.IsCycle ∧ x.support.card = 5)) :
    x.cycleType = Multiset.replicate 2 5 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (hx ▸ Nat.prime_five)
  rw [hx] at hk
  have hsum : x.cycleType.sum ≤ 10 := by
    rw [sum_cycleType]; exact (Finset.card_le_univ _).trans (by simp)
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with rfl | rfl
  · exfalso; apply hxc
    have hc : x.IsCycle := by rw [← card_cycleType_eq_one, hk]; rfl
    exact ⟨hc, by rw [← hc.orderOf, hx]⟩
  · exact hk

theorem cycleType_cyc10 : cyc10.cycleType = Multiset.replicate 2 5 := by
  apply cycleType_of_orderOf_five orderOf_cyc10
  rintro ⟨-, h⟩
  have : cyc10.support.card = 10 := by decide
  omega

end Models

/-- `|C_S(x)| = 11` for an `11`-cycle `x` of `Sym(11)` or `Sym(12)`. -/
theorem card_centralizer_eleven {n : ℕ} (hn : n = 11 ∨ n = 12) {x : Perm (Fin n)}
    (hx : x.cycleType = {11}) : Nat.card (centralizer ({x} : Set (Perm (Fin n)))) = 11 := by
  rw [nat_card_centralizer, hx]
  rcases hn with rfl | rfl <;> simp

/-- `|C_S(x)| = 50` for `x` of cycle type `5²` in `Sym(10)`. -/
theorem card_centralizer_five_five {x : Perm (Fin 10)}
    (hx : x.cycleType = Multiset.replicate 2 5) :
    Nat.card (centralizer ({x} : Set (Perm (Fin 10)))) = 50 := by
  rw [nat_card_centralizer, hx]
  decide

/-- **Degree 11** ([DiM, Exercise 5.2.6]): Theorem 3.3E makes `3, 5, 7` divide `h`, and
Bochert's bound `h ≥ 6!/2 = 360` leaves `h = 420`, `|G| = 47520`; but then the number of
Sylow `11`-subgroups, `|G : N_G(P)|` with `|N_G(P)|` dividing `|N_A(P)| = 55`, is not
`≡ 1 (mod 11)`. -/
theorem alternatingGroup_le_of_card_eq_eleven {G : Subgroup (Perm (Fin 11))}
    (hGA : G ≤ alternatingGroup (Fin 11)) (hG : IsPreprimitive G (Fin 11))
    (hidx : G.relIndex (alternatingGroup (Fin 11)) < (11 : ℕ).choose (11 / 2)) :
    alternatingGroup (Fin 11) ≤ G := by
  by_contra hA
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  have d5 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_five (by norm_num) (by simp)
  have d7 := odd_prime_dvd_relIndex hGA hG hA (q := 7) (by norm_num) (by norm_num) (by simp)
  simp only [Fintype.card_fin] at h1 h4
  generalize G.relIndex (alternatingGroup (Fin 11)) = h at *
  have e1 : 2 * Nat.card G * h = 39916800 := by rw [h1]; decide
  have e4 : Nat.card G * 720 ≤ 39916800 := by
    have : (11 - 11 / 2)! = 720 := by decide
    rw [this] at h4; rw [← show (11 : ℕ)! = 39916800 by decide]; exact h4
  have e5 : h < 462 := by
    have : (11 : ℕ).choose (11 / 2) = 462 := by decide
    omega
  have hG0 : 0 < Nat.card G := Nat.card_pos
  have hh : 360 ≤ h := by nlinarith
  obtain ⟨k, rfl⟩ : 105 ∣ h := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7) this d7
  have hk : k = 4 := by omega
  subst hk
  have hGcard : Nat.card G = 47520 := by omega
  obtain ⟨x, -, hxord, d, hd1, hd2, hd3, -⟩ := sylow_count_of_le_alternatingGroup hGA
    (p := 11) (by norm_num) (by rw [hGcard]; norm_num) (by rw [hGcard]; norm_num)
    (fun x _ hx => exists_odd_normalizer_of_model mul11_conj mul11_sign
      (by rw [cycleType_eq_of_orderOf_prime (by norm_num) hx (by norm_num),
        cycleType_cyc11]))
  rw [card_centralizer_eleven (Or.inl rfl)
    (cycleType_eq_of_orderOf_prime (by norm_num) hxord (by norm_num)), hGcard] at *
  have hd : d ≤ 55 := by
    have := Nat.le_of_dvd (by norm_num) hd1; omega
  interval_cases d <;> omega

/-- The Sylow `11`-count in degree `12`: a subgroup `G ≤ A_12` of order `N` with `11 ∣ N`,
`121 ∤ N` has a divisor `d` of `55` with `d ∣ N` and `N/d ≡ 1 (mod 11)`. -/
theorem sylow_eleven_twelve {G : Subgroup (Perm (Fin 12))}
    (hGA : G ≤ alternatingGroup (Fin 12)) {N : ℕ} (hN : Nat.card G = N) (h11 : 11 ∣ N)
    (h121 : ¬ 121 ∣ N) : ∃ d, 2 * d ∣ 110 ∧ d ∣ N ∧ N / d % 11 = 1 := by
  obtain ⟨x, -, hxord, d, hd1, hd2, hd3, -⟩ := sylow_count_of_le_alternatingGroup hGA
    (p := 11) (by norm_num) (by rw [hN]; exact h11) (by rw [hN]; norm_num; exact h121)
    (fun x _ hx => exists_odd_normalizer_of_model mul12_conj mul12_sign
      (by rw [cycleType_eq_of_orderOf_prime (by norm_num) hx (by norm_num),
        cycleType_cyc12]))
  rw [card_centralizer_eleven (Or.inr rfl)
    (cycleType_eq_of_orderOf_prime (by norm_num) hxord (by norm_num)), hN] at *
  exact ⟨d, hd1, hd2, hd3⟩

/-- **Degree 12** ([DiM, Exercise 5.2.6]): Theorem 3.3E makes `3, 5, 7` divide `h`; with
Bochert's `h ≥ 360` and `h < C(12,6) = 924`, `|G|` is one of `570240, 456192, 380160,
285120`, each divisible by `11` exactly once, and in each case the number of Sylow
`11`-subgroups cannot be `≡ 1 (mod 11)` (`|N_A(P)| = 55`). -/
theorem alternatingGroup_le_of_card_eq_twelve {G : Subgroup (Perm (Fin 12))}
    (hGA : G ≤ alternatingGroup (Fin 12)) (hG : IsPreprimitive G (Fin 12))
    (hidx : G.relIndex (alternatingGroup (Fin 12)) < (12 : ℕ).choose (12 / 2)) :
    alternatingGroup (Fin 12) ≤ G := by
  by_contra hA
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  have d5 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_five (by norm_num) (by simp)
  have d7 := odd_prime_dvd_relIndex hGA hG hA (q := 7) (by norm_num) (by norm_num) (by simp)
  simp only [Fintype.card_fin] at h1 h4
  generalize G.relIndex (alternatingGroup (Fin 12)) = h at *
  have e1 : 2 * Nat.card G * h = 479001600 := by rw [h1]; decide
  have e4 : Nat.card G * 720 ≤ 479001600 := by
    have : (12 - 12 / 2)! = 720 := by decide
    rw [this] at h4; rw [← show (12 : ℕ)! = 479001600 by decide]; exact h4
  have e5 : h < 924 := by
    have : (12 : ℕ).choose (12 / 2) = 924 := by decide
    omega
  have hG0 : 0 < Nat.card G := Nat.card_pos
  have hh : 360 ≤ h := by nlinarith
  obtain ⟨k, rfl⟩ : 105 ∣ h := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7) this d7
  have hk : 4 ≤ k ∧ k ≤ 8 := by omega
  obtain ⟨hk1, hk2⟩ := hk
  interval_cases k
  · obtain ⟨d, h1, h2, h3⟩ := sylow_eleven_twelve hGA (N := 570240) (by omega) (by norm_num)
      (by norm_num)
    have : d ≤ 55 := by have := Nat.le_of_dvd (by norm_num) h1; omega
    interval_cases d <;> omega
  · obtain ⟨d, h1, h2, h3⟩ := sylow_eleven_twelve hGA (N := 456192) (by omega) (by norm_num)
      (by norm_num)
    have : d ≤ 55 := by have := Nat.le_of_dvd (by norm_num) h1; omega
    interval_cases d <;> omega
  · obtain ⟨d, h1, h2, h3⟩ := sylow_eleven_twelve hGA (N := 380160) (by omega) (by norm_num)
      (by norm_num)
    have : d ≤ 55 := by have := Nat.le_of_dvd (by norm_num) h1; omega
    interval_cases d <;> omega
  · omega
  · obtain ⟨d, h1, h2, h3⟩ := sylow_eleven_twelve hGA (N := 285120) (by omega) (by norm_num)
      (by norm_num)
    have : d ≤ 55 := by have := Nat.le_of_dvd (by norm_num) h1; omega
    interval_cases d <;> omega

/-- **Degree 10** ([DiM, Exercise 5.2.5]): Theorem 3.3E makes `3, 5, 7` divide `h` and
excludes `5`-cycles; with Bochert's `h ≥ 60` and `h < C(10,5) = 252`, `|G|` is `17280` or
`8640`.  An element of order `5` then has cycle type `5²`, with `|N_A(⟨x⟩)|` dividing `100`;
the number of Sylow `5`-subgroups excludes `8640`, and for `17280` forces `N_G(P) = P`, so
Burnside's theorem gives a normal subgroup of order `3456`, which is transitive (the group is
primitive) although `10 ∤ 3456`. -/
theorem alternatingGroup_le_of_card_eq_ten {G : Subgroup (Perm (Fin 10))}
    (hGA : G ≤ alternatingGroup (Fin 10)) (hG : IsPreprimitive G (Fin 10))
    (hidx : G.relIndex (alternatingGroup (Fin 10)) < (10 : ℕ).choose (10 / 2)) :
    alternatingGroup (Fin 10) ≤ G := by
  by_contra hA
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  have d5 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_five (by norm_num) (by simp)
  have d7 := odd_prime_dvd_relIndex hGA hG hA (q := 7) (by norm_num) (by norm_num) (by simp)
  -- no `5`-cycles (Theorem 3.3E)
  have hno5 : ∀ x ∈ G, ¬ (x.IsCycle ∧ x.support.card = 5) := by
    rintro x hx ⟨hc, hs⟩
    exact hA (alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hG Nat.prime_five
      (by simp) hc hs hx)
  simp only [Fintype.card_fin] at h1 h4
  generalize G.relIndex (alternatingGroup (Fin 10)) = h at *
  have e1 : 2 * Nat.card G * h = 3628800 := by rw [h1]; decide
  have e4 : Nat.card G * 120 ≤ 3628800 := by
    have : (10 - 10 / 2)! = 120 := by decide
    rw [this] at h4; rw [← show (10 : ℕ)! = 3628800 by decide]; exact h4
  have e5 : h < 252 := by
    have : (10 : ℕ).choose (10 / 2) = 252 := by decide
    omega
  have hG0 : 0 < Nat.card G := Nat.card_pos
  have hh : 60 ≤ h := by nlinarith
  obtain ⟨k, rfl⟩ : 105 ∣ h := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7) this d7
  have hk : k = 1 ∨ k = 2 := by omega
  obtain ⟨N, hN, hN1⟩ : ∃ N, Nat.card G = N ∧ (N = 17280 ∨ N = 8640) := by
    rcases hk with rfl | rfl
    · exact ⟨17280, by omega, Or.inl rfl⟩
    · exact ⟨8640, by omega, Or.inr rfl⟩
  have h5 : 5 ∣ Nat.card G := by rw [hN]; rcases hN1 with rfl | rfl <;> norm_num
  have h25 : ¬ 5 ^ 2 ∣ Nat.card G := by rw [hN]; rcases hN1 with rfl | rfl <;> norm_num
  obtain ⟨x, hxG, hxord, d, hd1, hd2, hd3, hd4⟩ := sylow_count_of_le_alternatingGroup hGA
    (p := 5) Nat.prime_five h5 h25
    (fun x hx hxo => exists_odd_normalizer_of_model swp10_conj swp10_sign
      (by rw [cycleType_of_orderOf_five hxo (hno5 x hx), cycleType_cyc10]))
  rw [card_centralizer_five_five (cycleType_of_orderOf_five hxord (hno5 x hxG)), hN] at *
  have hd : d ≤ 100 := by have := Nat.le_of_dvd (by norm_num) hd1; omega
  rcases hN1 with rfl | rfl
  · -- `|G| = 17280`: `d = 5`, and Burnside's normal complement is transitive
    have hd5 : d = 5 := by interval_cases d <;> omega
    obtain ⟨K, hKG, hKn, hKcard⟩ := hd4 hd5
    have hKc : Nat.card K = 3456 := by omega
    have hKne : K ≠ ⊥ := by
      rintro rfl; rw [Subgroup.card_bot] at hKc; omega
    have := card_dvd_card_of_normal hG hKG hKn hKne
    rw [hKc, Fintype.card_fin] at this
    omega
  · interval_cases d <;> omega

/-- **Primitive groups of degree `n ≥ 10`** ([DiM, proof of Thm. 5.2A] with Exercises
5.2.1, 5.2.4–5.2.6): a primitive `G ≤ Alt(Ω)` with `|A : G| < C(n, ⌊n/2⌋)` and `n ≥ 10`
contains `Alt(Ω)`. -/
theorem alternatingGroup_le_of_primitive_of_ten_le {α : Type*} [Fintype α] [DecidableEq α]
    {G : Subgroup (Perm α)} (hGA : G ≤ alternatingGroup α) (hG : IsPreprimitive G α)
    (hn : 10 ≤ Fintype.card α)
    (hidx : G.relIndex (alternatingGroup α) < (Fintype.card α).choose (Fintype.card α / 2)) :
    alternatingGroup α ≤ G := by
  rcases (show Fintype.card α = 10 ∨ Fintype.card α = 11 ∨ Fintype.card α = 12 ∨
      Fintype.card α = 14 ∨ (15 ≤ Fintype.card α ∨ Fintype.card α = 13) by omega) with
    h | h | h | h | h
  · let e := Fintype.equivFinOfCardEq h
    refine alternatingGroup_le_of_relabel e (alternatingGroup_le_of_card_eq_ten
      (relabel_le_alternatingGroup e hGA) ((isPreprimitive_relabel_iff e G).mpr hG) ?_)
    rw [relabel_relIndex_alternatingGroup]; rwa [h] at hidx
  · let e := Fintype.equivFinOfCardEq h
    refine alternatingGroup_le_of_relabel e (alternatingGroup_le_of_card_eq_eleven
      (relabel_le_alternatingGroup e hGA) ((isPreprimitive_relabel_iff e G).mpr hG) ?_)
    rw [relabel_relIndex_alternatingGroup]; rwa [h] at hidx
  · let e := Fintype.equivFinOfCardEq h
    refine alternatingGroup_le_of_relabel e (alternatingGroup_le_of_card_eq_twelve
      (relabel_le_alternatingGroup e hGA) ((isPreprimitive_relabel_iff e G).mpr hG) ?_)
    rw [relabel_relIndex_alternatingGroup]; rwa [h] at hidx
  · exact alternatingGroup_le_of_card_eq_fourteen hGA hG h hidx
  · exact alternatingGroup_le_of_bochert hGA hG h hidx

end Babai.DM52
