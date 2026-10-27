/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 8.
-/
import Workspace.AltQuotients.DM52.Degree8CandA
import Workspace.AltQuotients.DM52.Degree8CandB
import Workspace.AltQuotients.DM52.OrbitTools

/-!
# Primitive subgroups of small index in `A_8`

The degree-`8` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148, Exercise 5.2.3): a primitive `G < A_8` with
`|A_8 : G| < C(8,4) = 70` is `AGL₃(2)` acting on the eight vectors of `F₂³`.

**Orders.**  Theorem 3.3E (with `p = 3, 5`) makes `15` divide `h = |A : G|`, so `|G|` is one
of `1344, 672, 448, 336`.  With `N := N_S(⟨x⟩)` for a `7`-cycle `x ∈ G`, `|A ∩ N| ∣ 21`, and
the Sylow `7`-count leaves `|G| = 1344` with `G ∩ N = A ∩ N` of order `21`, and `|G| = 448`
with `|G ∩ N| = 7`.  In the second case the point stabilizer `G_α` has order `56`, and the
Sylow `7`-count in `G_α` together with Burnside's theorem gives a normal subgroup `K ⊴ G_α` of
order `8`.  The fixed points of `K` form a set invariant under a `7`-cycle of `G_α`, so it is
`{α}` or everything; the first is impossible for a `2`-group on `8` points (the number of
fixed points is even), and the second makes `K = 1`.

**Recognition.**  Number the points by `F₂³`: the point `i < 7` is `α^i` for a root `α` of
`X³ + X + 1`, and `7` is `0`.  After relabeling, `G` contains `x ↦ αx` and the Frobenius
`x ↦ x²`, which fix `0`; the stabilizer `G_0` is then recognized as in degree `7` (it
preserves the Fano plane of the nonzero vectors, possibly after conjugation by `x ↦ 3x`),
and one more element `g ∈ G` swapping `0` and `1` is affine or makes a `3`-cycle or an element
of order `5`.  The group generated has order `8 · 168 = 1344` by the orbit–stabilizer theorem.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩


/-- The affine maps fixing `0 = 7` and the basis vectors `α⁰ = 0`, `α¹ = 1` send `α² = 2` into
`{α², α⁴, α⁵, α⁶}`, and fix everything if they also fix `2`. -/
theorem aff8_base : ∀ g : Perm (Fin 8), IsAff8 g → g 7 = 7 → g 0 = 0 → g 1 = 1 →
    (g 2 = 2 ∨ g 2 = 4 ∨ g 2 = 5 ∨ g 2 = 6) ∧ (g 2 = 2 → g = 1) := by
  intro g hA h7 h0 h1
  obtain ⟨p, rfl⟩ := exists_lift68 h0 h7
  exact d8aff p hA h1

/-- `|A8m ∩ Stab(7)| ≤ 168`, by the orbit–stabilizer theorem along the base `7, 0, 1, 2`. -/
theorem card_A8m_stab_le :
    Nat.card (A8m ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) : Subgroup _) ≤ 168 := by
  set X := (A8m ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) : Subgroup _)
  have hX : ∀ g ∈ X, IsAff8 g ∧ g 7 = 7 := fun g hg => ⟨(mem_A8m_iff g).mp hg.1, hg.2⟩
  have b0 := card_le_card_mul_of_mapsTo X 0 (Finset.univ.erase 7) (fun g hg => by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; exact absurd (g.injective (h.trans (hX g hg).2.symm)) (by decide))
  set X0 := (X ⊓ stabilizer (Perm (Fin 8)) (0 : Fin 8) : Subgroup _)
  have b1 := card_le_card_mul_of_mapsTo X0 1 ((Finset.univ.erase 7).erase 0) (fun g hg => by
    have h7 := (hX g hg.1).2
    have h0 : g 0 = 0 := hg.2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd (g.injective (h.trans h0.symm)) (by decide)
    · exact absurd (g.injective (h.trans h7.symm)) (by decide))
  set X1 := (X0 ⊓ stabilizer (Perm (Fin 8)) (1 : Fin 8) : Subgroup _)
  have hX1 : ∀ g ∈ X1, IsAff8 g ∧ g 7 = 7 ∧ g 0 = 0 ∧ g 1 = 1 :=
    fun g hg => ⟨(hX g hg.1.1).1, (hX g hg.1.1).2, hg.1.2, hg.2⟩
  have b2 := card_le_card_mul_of_mapsTo X1 2 {2, 4, 5, 6} (fun g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := hX1 g hg
    rcases (aff8_base g h1 h2 h3 h4).1 with h | h | h | h <;> simp [h])
  have b3 : Nat.card (X1 ⊓ stabilizer (Perm (Fin 8)) (2 : Fin 8) : Subgroup _) ≤ 1 := by
    rw [← Finset.card_singleton (1 : Perm (Fin 8))]
    apply card_le_of_subset_finset
    intro g hg
    obtain ⟨h1, h2, h3, h4⟩ := hX1 g hg.1
    simp [(aff8_base g h1 h2 h3 h4).2 hg.2]
  have : ({2, 4, 5, 6} : Finset (Fin 8)).card = 4 := by decide
  rw [this] at b2
  have e1 : ((Finset.univ : Finset (Fin 8)).erase 7).card = 7 := by decide
  have e2 : (((Finset.univ : Finset (Fin 8)).erase 7).erase 0).card = 6 := by decide
  rw [e1] at b0
  rw [e2] at b1
  calc Nat.card X ≤ 7 * Nat.card X0 := b0
    _ ≤ 7 * (6 * (4 * 1)) := by
      apply Nat.mul_le_mul_left
      exact b1.trans (Nat.mul_le_mul_left _ (b2.trans (Nat.mul_le_mul_left _ b3)))
    _ = 168 := by norm_num

/-- `|A8m| ≤ 1344`. -/
theorem card_A8m_le : Nat.card A8m ≤ 1344 := by
  have := card_le_card_mul_of_mapsTo A8m 7 Finset.univ (fun g _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h := card_A8m_stab_le
  omega

/-! ### Recognition -/

theorem isAff8_c8 : IsAff8 c8 := by decide
theorem isAff8_mu8 : IsAff8 mu8 := by decide
theorem isAff8_s8 : IsAff8 s8 := by decide

/-- Every even `g` fixing `0` and `7` outside `⟨mu8⟩` is affine, or is so after conjugation
by `rho8`, or makes a `3`-cycle or an element of order `5` (the degree-`7` words). -/
theorem degree_eight_candidates1 : ∀ g : Perm (Fin 8), g 7 = 7 → g 0 = 0 → sign g = 1 →
    g ≠ 1 → g ≠ mu8 → g ≠ mu8 ^ 2 →
    IsAff8 g ∨ IsAff8 (rho8⁻¹ * g * rho8) ∨ Bad35 [c8, mu8, g, g⁻¹] words7 := by
  intro g h7 h0 hs h1 hm hm2
  obtain ⟨p, rfl⟩ := exists_lift68 h0 h7
  rcases fin6_cases (p 0) with h | h | h | h | h | h
  · exact d8c1_0 p h hs h1 hm hm2
  · exact d8c1_1 p h hs h1 hm hm2
  · exact d8c1_2 p h hs h1 hm hm2
  · exact d8c1_3 p h hs h1 hm hm2
  · exact d8c1_4 p h hs h1 hm hm2
  · exact d8c1_5 p h hs h1 hm hm2


/-- Every even `g` swapping `0` and `7` is affine or makes a `3`-cycle or an element of
order `5`. -/
theorem degree_eight_candidates2 : ∀ g : Perm (Fin 8), g 7 = 0 → g 0 = 7 → sign g = 1 →
    IsAff8 g ∨ Bad35 [c8, mu8, s8, g, g⁻¹] words8 := by
  intro g h7 h0 hs
  obtain ⟨p, hp⟩ := exists_lift68 (g := swap 0 7 * g)
    (by show swap 0 7 (g 0) = 0; rw [h0]; decide)
    (by show swap 0 7 (g 7) = 7; rw [h7]; decide)
  have hgp : swap 0 7 * lift68 p = g := by rw [hp, ← mul_assoc, swap_mul_self, one_mul]
  subst hgp
  rcases fin6_cases (p 0) with h | h | h | h | h | h
  · exact d8c2_0 p h hs
  · exact d8c2_1 p h hs
  · exact d8c2_2 p h hs
  · exact d8c2_3 p h hs
  · exact d8c2_4 p h hs
  · exact d8c2_5 p h hs

theorem c8_orbit : ∀ b : Fin 8, b ≠ 7 → ∃ m : Fin 7, (c8 ^ (m : ℕ)) 0 = b := by decide

theorem c8_pow_seven : ∀ m : ℕ, (c8 ^ m) 7 = 7 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, Perm.mul_apply, show c8 7 = 7 by decide, ih]

/-- A group `H ≤ A_8` of order dividing `168` containing `c8`, `mu8` and an element `g` of the
stabilizer of `0` outside `⟨mu8⟩` has order `168`. -/
theorem card_closure_eight {H : Subgroup (Perm (Fin 8))} (hHA : H ≤ alternatingGroup (Fin 8))
    (hH : Nat.card H ∣ 168) (hc : c8 ∈ H) (hm : mu8 ∈ H) {g : Perm (Fin 8)} (hg : g ∈ H)
    (hg0 : g 0 = 0) (h1 : g ≠ 1) (h2 : g ≠ mu8) (h3 : g ≠ mu8 ^ 2) : Nat.card H = 168 := by
  have hstab : 4 ≤ Nat.card (H ⊓ stabilizer (Perm (Fin 8)) (0 : Fin 8) : Subgroup _) := by
    have hs : ({1, mu8, mu8 ^ 2, g} : Finset (Perm (Fin 8))).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm h3)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by decide, Ne.symm h2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by decide, by decide, Ne.symm h1⟩
    rw [← hs]
    apply le_card_of_finset
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ⟨hm, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    · exact ⟨pow_mem hm 2, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    · exact ⟨hg, hg0⟩
  have hge := card_le_card_of_orbit H 0 (Finset.univ.erase 7) (fun b hb => by
    obtain ⟨m, hm'⟩ := c8_orbit b (Finset.ne_of_mem_erase hb)
    exact ⟨c8 ^ (m : ℕ), H.pow_mem hc _, hm'⟩) hstab
  have e7 : ((Finset.univ : Finset (Fin 8)).erase 7).card = 7 := by decide
  rw [e7] at hge
  have h21 : 21 ∣ Nat.card H := by
    have e1 := H.orderOf_dvd_natCard hc
    have e2 := H.orderOf_dvd_natCard hm
    rw [orderOf_c8] at e1; rw [orderOf_mu8] at e2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 3) e1 e2
  obtain ⟨x, -, -, s1, s2, s3, s4, -⟩ := sylow_seven_eight hHA (dvd_trans (by norm_num) h21)
    (fun h49 => by have := h49.trans hH; norm_num at this)
  generalize Nat.card (alternatingGroup (Fin 8) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (H ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) = d
    at *
  have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
  have hdle : d ≤ 21 := Nat.le_of_dvd (by norm_num) (s2.trans s1)
  generalize Nat.card H = N at *
  obtain ⟨k, hk⟩ := hH
  have hN : N = 42 ∨ N = 84 ∨ N = 168 := by
    have hk6 : k ≤ 6 := by nlinarith
    interval_cases k <;> omega
  clear hNG
  rcases hN with rfl | rfl | rfl
  · interval_cases d <;> omega
  · interval_cases d <;> omega
  · rfl

/-- The last step of the recognition: a primitive `G ≤ A_8` of order `1344`, not containing
`A_8`, which contains `c8`, `mu8` and an affine element `g₁` of the stabilizer of `0` and `7`
outside `⟨mu8⟩`, is the model `A8m`. -/
theorem eq_A8m {G : Subgroup (Perm (Fin 8))} (hGA : G ≤ alternatingGroup (Fin 8))
    (hG : IsPreprimitive G (Fin 8)) (hA : ¬ alternatingGroup (Fin 8) ≤ G)
    (hcard : Nat.card G = 1344) (hc : c8 ∈ G) (hm : mu8 ∈ G) {g₁ : Perm (Fin 8)}
    (hg₁ : g₁ ∈ G) (hg₁7 : g₁ 7 = 7) (hg₁0 : g₁ 0 = 0) (n1 : g₁ ≠ 1) (n2 : g₁ ≠ mu8)
    (n3 : g₁ ≠ mu8 ^ 2) (hF : IsAff8 g₁) : G = A8m := by
  haveI := hG.toIsPretransitive
  -- the stabilizer of `7` has order `168`
  set H7 := (G ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) : Subgroup _)
  have hH7 : Nat.card H7 = 168 := by
    have := card_eq_card_mul_stabilizer hG.toIsPretransitive (7 : Fin 8)
    rw [hcard, Fintype.card_fin] at this
    change 1344 = 8 * Nat.card H7 at this
    omega
  have hc7 : c8 ∈ H7 := ⟨hc, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
  have hm7 : mu8 ∈ H7 := ⟨hm, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
  have hs7 : s8 ∈ H7 := by
    -- `⟨c8, mu8, g₁⟩` has order `168`, so it is all of `A8m ∩ Stab(7)`, which contains `s8`
    set H1 := closure ({c8, mu8, g₁} : Set (Perm (Fin 8)))
    have hH1 : H1 ≤ H7 := by
      rw [closure_le]; intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hc7
      · exact hm7
      · exact ⟨hg₁, hg₁7⟩
    have hcardH1 : Nat.card H1 = 168 := card_closure_eight (hH1.trans (inf_le_left.trans hGA))
      (hH7 ▸ Subgroup.card_dvd_of_le hH1) (subset_closure (by simp))
      (subset_closure (by simp)) (subset_closure (by simp)) hg₁0 n1 n2 n3
    have hH1A : H1 ≤ A8m ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) := by
      rw [closure_le]; intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨(mem_A8m_iff _).mpr isAff8_c8, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      · exact ⟨(mem_A8m_iff _).mpr isAff8_mu8, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      · exact ⟨(mem_A8m_iff _).mpr hF, hg₁7⟩
    have heq : H1 = A8m ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) :=
      Subgroup.eq_of_le_of_card_ge hH1A (by rw [hcardH1]; exact card_A8m_stab_le)
    have : s8 ∈ H1 := by
      rw [heq]
      exact ⟨(mem_A8m_iff _).mpr isAff8_s8, MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    exact hH1 this
  have hs : s8 ∈ G := hs7.1
  -- an element swapping `7` and `0`
  obtain ⟨g, hg, hg7⟩ : ∃ g ∈ G, g 7 = 0 := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (7 : Fin 8) 0
    exact ⟨g, g.2, hg⟩
  set i := g⁻¹ 7 with hi
  have hi7 : i ≠ 7 := by
    intro h
    have : g i = g 7 := by rw [h]
    rw [hi, show g (g⁻¹ 7) = 7 by simp, hg7] at this
    exact absurd this (by decide)
  obtain ⟨m, hm'⟩ := c8_orbit i hi7
  set g₂ := g * c8 ^ (m : ℕ)
  have hg₂ : g₂ ∈ G := mul_mem hg (pow_mem hc _)
  have hg₂7 : g₂ 7 = 0 := by simp [g₂, Perm.mul_apply, c8_pow_seven, hg7]
  have hg₂0 : g₂ 0 = 7 := by simp [g₂, Perm.mul_apply, hm', hi]
  have hg₂A : IsAff8 g₂ := by
    rcases degree_eight_candidates2 g₂ hg₂7 hg₂0 (hGA hg₂) with h | h
    · exact h
    · exact absurd h (not_bad35 hG hA (by rw [hcard]; norm_num)
        (by simp [hc, hm, hs, hg₂, inv_mem hg₂]) words8)
  -- the group generated by `c8, mu8, s8, g₂` has order at least `8 · 168`
  set K := closure ({c8, mu8, s8, g₂} : Set (Perm (Fin 8)))
  have hKG : K ≤ G := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hc
    · exact hm
    · exact hs7.1
    · exact hg₂
  have hKA : K ≤ A8m := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (mem_A8m_iff _).mpr isAff8_c8
    · exact (mem_A8m_iff _).mpr isAff8_mu8
    · exact (mem_A8m_iff _).mpr isAff8_s8
    · exact (mem_A8m_iff _).mpr hg₂A
  have hK7 : 168 ≤ Nat.card (K ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) : Subgroup _) := by
    set H2 := closure ({c8, mu8, s8} : Set (Perm (Fin 8)))
    have hH2K : H2 ≤ K ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8) := by
      rw [closure_le]; intro y hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨subset_closure (by simp), MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      · exact ⟨subset_closure (by simp), MulAction.mem_stabilizer_iff.mpr (by decide)⟩
      · exact ⟨subset_closure (by simp), MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    have hH2H7 : H2 ≤ H7 := hH2K.trans (inf_le_inf_right _ hKG)
    have hcardH2 : Nat.card H2 = 168 := card_closure_eight (g := s8)
      (hH2H7.trans (inf_le_left.trans hGA))
      (hH7 ▸ Subgroup.card_dvd_of_le hH2H7) (subset_closure (by simp))
      (subset_closure (by simp)) (subset_closure (by simp)) (by decide) (by decide) (by decide)
      (by decide)
    rw [← hcardH2]
    exact Subgroup.card_le_of_le hH2K
  have hge := card_le_card_of_orbit K 7 Finset.univ (fun b _ => by
    by_cases hb : b = 7
    · exact ⟨1, one_mem _, by rw [hb]; rfl⟩
    · obtain ⟨m, hm'⟩ := c8_orbit b hb
      refine ⟨c8 ^ (m : ℕ) * g₂, mul_mem (pow_mem (subset_closure (by simp)) _)
        (subset_closure (by simp)), ?_⟩
      rw [Perm.mul_apply, hg₂7, hm']) hK7
  rw [Finset.card_univ, Fintype.card_fin] at hge
  have hKG' : K = G := Subgroup.eq_of_le_of_card_ge hKG (by rw [hcard]; omega)
  exact Subgroup.eq_of_le_of_card_ge (hKG' ▸ hKA) (by rw [hcard]; exact card_A8m_le)

/-- **Degree 8** ([DiM, proof of Thm. 5.2A], Exercise 5.2.3): a primitive `G < A_8` with
`|A_8 : G| < 70` is conjugate to the model `A8m` of `AGL₃(2)`. -/
theorem degree_eight {G : Subgroup (Perm (Fin 8))} (hGA : G ≤ alternatingGroup (Fin 8))
    (hG : IsPreprimitive G (Fin 8)) (hA : ¬ alternatingGroup (Fin 8) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 8)) < 70) :
    ∃ σ : Perm (Fin 8), relabel σ G = A8m := by
  obtain ⟨hcard, x, hxG, hxc, hGN⟩ := degree_eight_order hGA hG hA hidx
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_c8.trans hxc.symm))
  have hμ : τ * mu8 * τ⁻¹ ∈ G := by
    have hmem : τ * mu8 * τ⁻¹ ∈ alternatingGroup (Fin 8) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
      refine ⟨by simp [mem_alternatingGroup, mu8_sign], ?_⟩
      apply mem_normalizer_zpowers_of_conj_eq_zpow (k := 2)
      rw [← hτ, conj_zpow, ← mu8_conj]
      group
    rw [← hGN] at hmem
    exact hmem.1
  set G' := relabel τ⁻¹ G with hG'
  have hc' : c8 ∈ G' := by rw [mem_relabel_perm, inv_inv, hτ]; exact hxG
  have hm' : mu8 ∈ G' := by rw [mem_relabel_perm, inv_inv]; exact hμ
  have hG'A : G' ≤ alternatingGroup (Fin 8) := relabel_le_alternatingGroup _ hGA
  have hG'p : IsPreprimitive G' (Fin 8) := (isPreprimitive_relabel_iff _ G).mpr hG
  have hA' : ¬ alternatingGroup (Fin 8) ≤ G' := fun h => hA (alternatingGroup_le_of_relabel _ h)
  have hcard' : Nat.card G' = 1344 := by rw [hG', card_relabel, hcard]
  -- an element of the stabilizer of `7` and `0` outside `⟨mu8⟩`
  obtain ⟨g, ⟨⟨hg, hg7⟩, hg0⟩, hgn⟩ : ∃ g ∈ (G' ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8)) ⊓
      stabilizer (Perm (Fin 8)) (0 : Fin 8),
      g ∉ ({1, mu8, mu8 ^ 2} : Finset (Perm (Fin 8))) := by
    by_contra hcon
    push Not at hcon
    have h1 := card_eq_card_mul_stabilizer hG'p.toIsPretransitive (7 : Fin 8)
    rw [hcard', Fintype.card_fin] at h1
    have h2 := card_le_card_mul_of_mapsTo (G' ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8)) 0
      (Finset.univ.erase 7) (fun g hg => by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        intro h
        have h7' : g 7 = 7 := hg.2
        exact absurd (g.injective (h.trans h7'.symm)) (by decide))
    have h3 : Nat.card ((G' ⊓ stabilizer (Perm (Fin 8)) (7 : Fin 8)) ⊓
        stabilizer (Perm (Fin 8)) (0 : Fin 8) : Subgroup _) ≤ 3 := by
      calc _ ≤ ({1, mu8, mu8 ^ 2} : Finset (Perm (Fin 8))).card :=
            card_le_of_subset_finset _ hcon
        _ ≤ 3 := Finset.card_le_three
    have e7 : ((Finset.univ : Finset (Fin 8)).erase 7).card = 7 := by decide
    rw [e7] at h2
    omega
  have hg7' : g 7 = 7 := hg7
  have hg0' : g 0 = 0 := hg0
  replace hg : g ∈ G' := hg
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hgn
  obtain ⟨n1, n2, n3⟩ := hgn
  rcases degree_eight_candidates1 g hg7' hg0' (hG'A hg) n1 n2 n3 with hF | hF | hbad
  · exact ⟨τ⁻¹, eq_A8m hG'A hG'p hA' hcard' hc' hm' hg hg7' hg0' n1 n2 n3 hF⟩
  · refine ⟨rho8⁻¹ * τ⁻¹, ?_⟩
    rw [← relabel_relabel_perm]
    have hc'' : c8 ∈ relabel rho8⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho8_conj]
      exact zpow_mem hc' 3
    have hm'' : mu8 ∈ relabel rho8⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho8_mu8, mul_assoc, mul_inv_cancel, mul_one]; exact hm'
    have hg'' : rho8⁻¹ * g * rho8 ∈ relabel rho8⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv]; simpa [mul_assoc] using hg
    have hr0 : rho8 0 = 0 := by decide
    have hri0 : rho8⁻¹ 0 = 0 := by decide
    have hr7 : rho8 7 = 7 := by decide
    have hri7 : rho8⁻¹ 7 = 7 := by decide
    refine eq_A8m (relabel_le_alternatingGroup _ hG'A)
      ((isPreprimitive_relabel_iff _ G').mpr hG'p)
      (fun h => hA' (alternatingGroup_le_of_relabel _ h)) (by rw [card_relabel, hcard'])
      hc'' hm'' hg'' (by simp [Perm.mul_apply, hr7, hg7', hri7])
      (by simp [Perm.mul_apply, hr0, hg0', hri0]) ?_ ?_ ?_ hF
    all_goals intro h
    all_goals have hg' : g = rho8 * (rho8⁻¹ * g * rho8) * rho8⁻¹ := by group
    all_goals rw [h] at hg'
    · exact n1 (by rw [hg']; group)
    · exact n2 (by rw [hg']; decide)
    · exact n3 (by rw [hg']; decide)
  · exact absurd hbad (not_bad35 hG'p hA' (by rw [hcard']; norm_num)
      (by simp [hc', hm', hg, inv_mem hg]) words7)

end Babai.DM52
