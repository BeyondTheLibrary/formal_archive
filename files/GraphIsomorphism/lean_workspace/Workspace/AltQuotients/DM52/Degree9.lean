/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 9.
-/
import Workspace.AltQuotients.DM52.Degree9CandA
import Workspace.AltQuotients.DM52.Degree9CandB
import Workspace.AltQuotients.DM52.Degree9CandC

/-!
# Primitive subgroups of small index in `A_9`

The degree-`9` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148, Exercise 5.2.3): a primitive `G < A_9` with
`|A_9 : G| < C(9,4) = 126` is `PΓL₂(8)` acting on the nine points of the projective line
over `F₈`.

**Orders.**  Bochert's theorem gives `|G| ≤ 9!/5! = 3024`, and Theorem 3.3E (with `p = 3, 5`)
makes `15` divide `h = |A : G|`, so `|G|` is one of `3024, 2016, 1728, 1512`.  The order
`1728` is divisible by `64`, which forces `A_9 ≤ G`
(`Babai.DM52.alternatingGroup_le_of_sixtyfour_dvd`).  With `N := N_S(⟨x⟩)` for a `7`-cycle
`x ∈ G`, `|A ∩ N| ∣ 42`, and the Sylow `7`-count excludes `3024`, forces `|G ∩ N| = 7` for
`2016` — which the Sylow `7`-count in a point stabilizer (of order `224`) excludes — and
leaves `|G| = 1512` with `G ∩ N = A ∩ N` of order `42`.

**Recognition.**  Number the points of the projective line: `i < 7` is `α^i`, `7` is `0` and
`8` is `∞`.  After relabeling, `G` contains `x ↦ αx`, `x ↦ x²` and `x ↦ 1/x`, which
generate `A ∩ N`.  The stabilizer of `∞` does not fix `0` (else `{0, ∞}` would be a block),
so `G` contains an element `g` fixing `∞` and swapping `0` and `1`; such a `g` is
`x ↦ σ(x) + 1` for a field automorphism `σ`, possibly after conjugation by `x ↦ x³`, or it
makes a `3`-cycle or an element of order `5`.  The group generated then has order at least
`9 · 8 · 21 = 1512` by the orbit–stabilizer theorem.
-/

namespace Babai.DM52
open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Every even `g` fixing `∞ = 8` and swapping `0 = 7` and `1 = 0` (that is,
`g = (0 7) · lift6 p`) is `x ↦ σ(x) + 1`, or is so after conjugation by `rho9`, or makes a
`3`-cycle or an element of order `5`. -/
theorem degree_nine_candidates : ∀ p : Perm (Fin 6), sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  intro p
  rcases fin6_cases (p 0) with h0 | h0 | h0 | h0 | h0 | h0 <;>
    rcases fin6_cases (p 1) with h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  · exact d9cand_0_1 p h0 h1
  · exact d9cand_0_2 p h0 h1
  · exact d9cand_0_3 p h0 h1
  · exact d9cand_0_4 p h0 h1
  · exact d9cand_0_5 p h0 h1
  · exact d9cand_1_0 p h0 h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  · exact d9cand_1_2 p h0 h1
  · exact d9cand_1_3 p h0 h1
  · exact d9cand_1_4 p h0 h1
  · exact d9cand_1_5 p h0 h1
  · exact d9cand_2_0 p h0 h1
  · exact d9cand_2_1 p h0 h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  · exact d9cand_2_3 p h0 h1
  · exact d9cand_2_4 p h0 h1
  · exact d9cand_2_5 p h0 h1
  · exact d9cand_3_0 p h0 h1
  · exact d9cand_3_1 p h0 h1
  · exact d9cand_3_2 p h0 h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  · exact d9cand_3_4 p h0 h1
  · exact d9cand_3_5 p h0 h1
  · exact d9cand_4_0 p h0 h1
  · exact d9cand_4_1 p h0 h1
  · exact d9cand_4_2 p h0 h1
  · exact d9cand_4_3 p h0 h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)
  · exact d9cand_4_5 p h0 h1
  · exact d9cand_5_0 p h0 h1
  · exact d9cand_5_1 p h0 h1
  · exact d9cand_5_2 p h0 h1
  · exact d9cand_5_3 p h0 h1
  · exact d9cand_5_4 p h0 h1
  · exact absurd (p.injective (h0.trans h1.symm)) (by decide)

theorem mem_M9_of_cases {g : Perm (Fin 9)} (h : g = t9 ∨ g = t9 * mu9 ∨ g = t9 * mu9 ^ 2) :
    g ∈ M9 := by
  rcases h with rfl | rfl | rfl
  · exact t9_mem_M9
  · exact mul_mem t9_mem_M9 mu9_mem_M9
  · exact mul_mem t9_mem_M9 (pow_mem mu9_mem_M9 2)

/-- In a primitive group containing `io9`, the stabilizer of `8` does not fix `7`: otherwise
`{7, 8}` would be a block. -/
theorem exists_stab_eight_move_seven {G : Subgroup (Perm (Fin 9))}
    (hG : IsPreprimitive G (Fin 9)) (hi : io9 ∈ G) : ∃ g ∈ G, g 8 = 8 ∧ g 7 ≠ 7 := by
  by_contra hcon
  push Not at hcon
  have hio : ∀ a, io9 a = 7 ↔ a = 8 := by decide
  have hA1 : ∀ g ∈ G, g 8 = 7 → g 7 = 8 := by
    intro g hg h
    have := hcon (io9 * g) (mul_mem hi hg)
      (by rw [Perm.mul_apply, h]; decide)
    rw [Perm.mul_apply] at this
    exact (hio _).mp this
  have hA2 : ∀ g ∈ G, g 7 = 7 → g 8 = 8 := by
    intro g hg h
    have := hcon (io9 * g * io9) (mul_mem (mul_mem hi hg) hi)
      (by rw [Perm.mul_apply, Perm.mul_apply, show io9 8 = 7 by decide, h]; decide)
    rw [Perm.mul_apply, Perm.mul_apply, show io9 7 = 8 by decide] at this
    exact (hio _).mp this
  have hsm : ∀ g : G, g • ({7, 8} : Set (Fin 9)) = {(g : Perm (Fin 9)) 7, (g : Perm (Fin 9)) 8} := by
    intro g; rw [← Set.image_smul, Set.image_pair]; rfl
  have hB : IsBlock G ({7, 8} : Set (Fin 9)) := by
    rw [isBlock_iff_smul_eq_or_disjoint]
    intro g
    rw [hsm]
    obtain ⟨g, hg⟩ := g
    simp only
    by_cases h8 : g 8 = 8
    · left; rw [h8, hcon g hg h8]
    by_cases h87 : g 8 = 7
    · left; rw [h87, hA1 g hg h87, Set.pair_comm]
    by_cases h77 : g 7 = 7
    · exact absurd (hA2 g hg h77) h8
    by_cases h78 : g 7 = 8
    · have : g⁻¹ 8 = 7 := by rw [Perm.inv_eq_iff_eq, h78]
      have := hA1 g⁻¹ (inv_mem hg) this
      rw [Perm.inv_eq_iff_eq] at this
      exact absurd this.symm h87
    · right
      rw [Set.disjoint_left]
      intro a ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with h | h
      · exact h77 h
      · exact h78 h
      · exact h87 h
      · exact h8 h
  rcases hG.isTrivialBlock_of_isBlock hB with h | h
  · exact absurd (h (by simp : (7 : Fin 9) ∈ ({7, 8} : Set (Fin 9)))
      (by simp : (8 : Fin 9) ∈ ({7, 8} : Set (Fin 9)))) (by decide)
  · have : (0 : Fin 9) ∈ ({7, 8} : Set (Fin 9)) := by rw [h]; trivial
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    revert this; decide

/-- **Degree 9** ([DiM, proof of Thm. 5.2A], Exercise 5.2.3): a primitive `G < A_9` with
`|A_9 : G| < 126` is conjugate to the model `M9` of `PΓL₂(8)`. -/
theorem degree_nine {G : Subgroup (Perm (Fin 9))} (hGA : G ≤ alternatingGroup (Fin 9))
    (hG : IsPreprimitive G (Fin 9)) (hA : ¬ alternatingGroup (Fin 9) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 9)) < 126) :
    ∃ σ : Perm (Fin 9), relabel σ G = M9 := by
  obtain ⟨hcard, x, hxG, hxc, hGN⟩ := degree_nine_order hGA hG hA hidx
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_c9.trans hxc.symm))
  have hconj : ∀ y : Perm (Fin 9), sign y = 1 → ∀ k : ℤ, y * c9 * y⁻¹ = c9 ^ k →
      τ * y * τ⁻¹ ∈ G := by
    intro y hy k hk
    have hmem : τ * y * τ⁻¹ ∈ alternatingGroup (Fin 9) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) := by
      refine ⟨by simp [mem_alternatingGroup, hy], ?_⟩
      apply mem_normalizer_zpowers_of_conj_eq_zpow (k := k)
      rw [← hτ, conj_zpow, ← hk]
      group
    rw [← hGN] at hmem
    exact hmem.1
  set G' := relabel τ⁻¹ G with hG'
  have hc' : c9 ∈ G' := by rw [mem_relabel_perm, inv_inv, hτ]; exact hxG
  have hm' : mu9 ∈ G' := by
    rw [mem_relabel_perm, inv_inv]; exact hconj mu9 mu9_sign 2 c9_conj_mu9
  have hi' : io9 ∈ G' := by
    rw [mem_relabel_perm, inv_inv]; exact hconj io9 io9_sign 6 c9_conj_io9
  have hG'A : G' ≤ alternatingGroup (Fin 9) := relabel_le_alternatingGroup _ hGA
  have hG'p : IsPreprimitive G' (Fin 9) := (isPreprimitive_relabel_iff _ G).mpr hG
  have hA' : ¬ alternatingGroup (Fin 9) ≤ G' := fun h => hA (alternatingGroup_le_of_relabel _ h)
  have hcard' : Nat.card G' = 1512 := by rw [hG', card_relabel, hcard]
  -- an element fixing `8` and sending `7` to `0`
  obtain ⟨g₁, hg₁, hg₁8, hg₁7⟩ := exists_stab_eight_move_seven hG'p hi'
  have hg₁7' : g₁ 7 ≠ 8 := by
    intro h
    exact absurd (g₁.injective (h.trans hg₁8.symm)) (by decide)
  obtain ⟨m₁, hm₁⟩ := c9_orbit' (g₁ 7) hg₁7 hg₁7'
  set t := c9 ^ (m₁ : ℕ) * g₁
  have ht : t ∈ G' := mul_mem (pow_mem hc' _) hg₁
  have ht8 : t 8 = 8 := by
    show (c9 ^ (m₁ : ℕ)) (g₁ 8) = 8
    rw [hg₁8, (c9_pow_fix _).2]
  have ht7 : t 7 = 0 := hm₁
  -- an element fixing `8` and swapping `7` and `0`
  set i := t⁻¹ 7 with hi
  have hi7 : i ≠ 7 := by
    intro h
    have : t (t⁻¹ 7) = 7 := by simp
    rw [← hi, h, ht7] at this
    exact absurd this (by decide)
  have hi8 : i ≠ 8 := by
    intro h
    have : t (t⁻¹ 7) = 7 := by simp
    rw [← hi, h, ht8] at this
    exact absurd this (by decide)
  obtain ⟨m, hm⟩ := c9_orbit i hi7 hi8
  set g := t * c9 ^ (m : ℕ)
  have hg : g ∈ G' := mul_mem ht (pow_mem hc' _)
  have hg8 : g 8 = 8 := by
    show t ((c9 ^ (m : ℕ)) 8) = 8
    rw [(c9_pow_fix _).2, ht8]
  have hg7 : g 7 = 0 := by
    show t ((c9 ^ (m : ℕ)) 7) = 0
    rw [(c9_pow_fix _).1, ht7]
  have hg0 : g 0 = 7 := by
    show t ((c9 ^ (m : ℕ)) 0) = 7
    rw [hm, hi]; simp
  obtain ⟨p, hp⟩ := exists_lift6 (g := swap 0 7 * g)
    (by show swap 0 7 (g 0) = 0; rw [hg0]; decide)
    (by show swap 0 7 (g 7) = 7; rw [hg7]; decide)
    (by show swap 0 7 (g 8) = 8; rw [hg8]; decide)
  have hgp : swap 0 7 * lift6 p = g := by rw [hp, ← mul_assoc, swap_mul_self, one_mul]
  have hcand := degree_nine_candidates p (by rw [hgp]; exact hG'A hg)
  rw [hgp] at hcand
  rcases hcand with hF | hF | hbad
  · exact ⟨τ⁻¹, eq_M9 hcard' hc' hm' hi' hg hg8 hg7 (mem_M9_of_cases hF)⟩
  · refine ⟨rho9⁻¹ * τ⁻¹, ?_⟩
    rw [← relabel_relabel_perm]
    have hc'' : c9 ∈ relabel rho9⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho9_conj]
      exact zpow_mem hc' 3
    have hm'' : mu9 ∈ relabel rho9⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho9_mu9, mul_assoc, mul_inv_cancel, mul_one]; exact hm'
    have hi'' : io9 ∈ relabel rho9⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho9_io9, mul_assoc, mul_inv_cancel, mul_one]; exact hi'
    have hg'' : rho9⁻¹ * g * rho9 ∈ relabel rho9⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv]; simpa [mul_assoc] using hg
    have hr8 : rho9 8 = 8 := by decide
    have hri0 : rho9⁻¹ 0 = 0 := by decide
    have hr7 : rho9 7 = 7 := by decide
    have hri8 : rho9⁻¹ 8 = 8 := by decide
    refine eq_M9 (by rw [card_relabel, hcard']) hc'' hm'' hi'' hg''
      ?_ ?_ (mem_M9_of_cases hF)
    · simp [Perm.mul_apply, hr8, hg8, hri8]
    · simp [Perm.mul_apply, hr7, hg7, hri0]
  · exact absurd hbad (not_bad35 hG'p hA' (by rw [hcard']; norm_num)
      (by simp [hc', hm', hi', hg, inv_mem hg]) words9)

end Babai.DM52
