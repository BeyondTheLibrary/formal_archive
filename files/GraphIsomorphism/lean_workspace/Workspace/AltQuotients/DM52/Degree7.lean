/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 7.
-/
import Workspace.AltQuotients.DM52.Degree7Cand

/-!
# Primitive subgroups of small index in `A_7`

The degree-`7` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148): a primitive `G < A_7` with `|A_7 : G| < C(7,3) = 35` is
`PSL₃(2)` acting on the seven points of the Fano plane.

**Orders.**  Theorem 3.3E (with `p = 3`) makes `3` divide `h = |A : G|`, and `7 ∣ |G|`, so
`|G|` is one of `840, 420, 280, 210, 168, 140, 105, 84`.  With `N := N_S(⟨x⟩)` for a
`7`-cycle `x ∈ G`, `|A ∩ N| ∣ 21`, and the Sylow `7`-count leaves only `|G| = 168` with
`G ∩ N = A ∩ N` of order `21`, and `|G| ∈ {840, 105}` with `|G ∩ N| = 7`, where Burnside's
theorem gives a normal subgroup of order `120` or `15`, not divisible by `7`.

**Recognition.**  The Fano plane has points `ℤ/7` and lines `{i, i+1, i+3}`; with
`x ↦ x+1` and `x ↦ 2x` in `G` (after relabeling), an element `g ∈ G_0` outside
`⟨x ↦ 2x⟩` either preserves the Fano plane, or does so after conjugation by the odd
permutation `x ↦ 3x` (which normalizes `⟨x ↦ x+1, x ↦ 2x⟩`), or makes a `3`-cycle or an
element of order `5`.  The group `⟨x ↦ x + 1, x ↦ 2x, g⟩` then has order `168` by the
Sylow `7`-count again.  The model is the image `F7` of `SL₃(2)` acting on the seven nonzero
vectors of `F₂³`, numbered by the powers of a root `α` of `X³ + X + 1`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped MatrixGroups Matrix

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### The Fano plane -/

theorem fanoMatrix_spec : ∀ g : Perm (Fin 7), IsFano g →
    (fanoMatrix g).det = 1 ∧ ∀ i, psi7F (fanoMatrix g) i = g i := by
  intro g hF
  obtain ⟨p, hp⟩ := exists_lift67 (g := swap 0 (g 0) * g) (by simp [swap_apply_right])
  have hg : g = swap 0 (g 0) * lift67 p := by rw [hp, ← mul_assoc, swap_mul_self, one_mul]
  rcases fin7_cases (g 0) with h | h | h | h | h | h | h <;>
    rw [h] at hg <;> subst hg
  · exact d7fano_0 p hF
  · exact d7fano_1 p hF
  · exact d7fano_2 p hF
  · exact d7fano_3 p hF
  · exact d7fano_4 p hF
  · exact d7fano_5 p hF
  · exact d7fano_6 p hF

theorem mem_F7_of_isFano {g : Perm (Fin 7)} (hg : IsFano g) : g ∈ F7 := by
  obtain ⟨h1, h2⟩ := fanoMatrix_spec g hg
  exact MonoidHom.mem_range.mpr ⟨⟨fanoMatrix g, h1⟩, Equiv.ext fun i => h2 i⟩

/-! ### Recognition -/
/-- Every even `g` fixing `0` outside `⟨mu7⟩` preserves the Fano plane, or does so after
conjugation by `rho7`, or makes a `3`-cycle or an element of order `5`. -/
theorem degree_seven_candidates : ∀ g : Perm (Fin 7), g 0 = 0 → sign g = 1 → g ≠ 1 →
    g ≠ mu7 → g ≠ mu7 ^ 2 →
    IsFano g ∨ IsFano (rho7⁻¹ * g * rho7) ∨ Bad35 [c7, mu7, g, g⁻¹] words7 := by
  intro g h0 hs h1 hm hm2
  obtain ⟨p, rfl⟩ := exists_lift67 h0
  rcases fin6_cases (p 0) with h | h | h | h | h | h
  · exact d7cand_0 p h hs h1 hm hm2
  · exact d7cand_1 p h hs h1 hm hm2
  · exact d7cand_2 p h hs h1 hm hm2
  · exact d7cand_3 p h hs h1 hm hm2
  · exact d7cand_4 p h hs h1 hm hm2
  · exact d7cand_5 p h hs h1 hm hm2

theorem c7_orbit : ∀ b : Fin 7, ∃ m : Fin 7, (c7 ^ (m : ℕ)) 0 = b := by decide

/-- A group `H ≤ A_7` of order dividing `168` containing `x ↦ x + 1`, `x ↦ 2x` and an element
`g` of the stabilizer of `0` outside `⟨x ↦ 2x⟩` has order `168`. -/
theorem card_closure_seven {H : Subgroup (Perm (Fin 7))} (hHA : H ≤ alternatingGroup (Fin 7))
    (hH : Nat.card H ∣ 168) (hc : c7 ∈ H) (hm : mu7 ∈ H) {g : Perm (Fin 7)} (hg : g ∈ H)
    (hg0 : g 0 = 0) (h1 : g ≠ 1) (h2 : g ≠ mu7) (h3 : g ≠ mu7 ^ 2) : Nat.card H = 168 := by
  have hstab : 4 ≤ Nat.card (H ⊓ stabilizer (Perm (Fin 7)) (0 : Fin 7) : Subgroup _) := by
    have hs : ({1, mu7, mu7 ^ 2, g} : Finset (Perm (Fin 7))).card = 4 := by
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
  have hge := card_le_card_of_orbit H 0 Finset.univ (fun b _ => by
    obtain ⟨m, hm'⟩ := c7_orbit b
    exact ⟨c7 ^ (m : ℕ), H.pow_mem hc _, hm'⟩) hstab
  simp only [Finset.card_univ, Fintype.card_fin] at hge
  have h21 : 21 ∣ Nat.card H := by
    have e1 := H.orderOf_dvd_natCard hc
    have e2 := H.orderOf_dvd_natCard hm
    rw [orderOf_c7] at e1; rw [orderOf_mu7] at e2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 3) e1 e2
  obtain ⟨x, -, -, s1, s2, s3, s4, -⟩ := sylow_seven_seven hHA (dvd_trans (by norm_num) h21)
    (fun h49 => by have := h49.trans hH; norm_num at this)
  generalize Nat.card (alternatingGroup (Fin 7) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (H ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) = d
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

/-- If a group `H ≤ A_7` of order `168` contains `c7`, `mu7` and a Fano automorphism `g` of
the stabilizer of `0` outside `⟨mu7⟩`, it is `F7`. -/
theorem eq_F7 {H : Subgroup (Perm (Fin 7))} (hHA : H ≤ alternatingGroup (Fin 7))
    (hcard : Nat.card H = 168) (hc : c7 ∈ H) (hm : mu7 ∈ H) {g : Perm (Fin 7)} (hg : g ∈ H)
    (hg0 : g 0 = 0) (h1 : g ≠ 1) (h2 : g ≠ mu7) (h3 : g ≠ mu7 ^ 2) (hF : IsFano g) :
    H = F7 := by
  set K := closure ({c7, mu7, g} : Set (Perm (Fin 7)))
  have hKH : K ≤ H := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hKF : K ≤ F7 := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl
    · exact mem_F7_of_isFano (by decide)
    · exact mem_F7_of_isFano (by decide)
    · exact mem_F7_of_isFano hF
  have hK := card_closure_seven (hKH.trans hHA) (hcard ▸ Subgroup.card_dvd_of_le hKH)
    (subset_closure (by simp)) (subset_closure (by simp)) (subset_closure (by simp)) hg0 h1 h2 h3
  have hKH' : K = H := Subgroup.eq_of_le_of_card_ge hKH (by rw [hK, hcard])
  exact Subgroup.eq_of_le_of_card_ge (hKH' ▸ hKF) (by rw [card_F7, hcard])

/-- **Degree 7** ([DiM, proof of Thm. 5.2A], the examination of the primitive groups of
degree `7`): a primitive `G < A_7` with `|A_7 : G| < 35` is conjugate to the model `F7` of
`PSL₃(2)`. -/
theorem degree_seven {G : Subgroup (Perm (Fin 7))} (hGA : G ≤ alternatingGroup (Fin 7))
    (hG : IsPreprimitive G (Fin 7)) (hA : ¬ alternatingGroup (Fin 7) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 7)) < 35) :
    ∃ σ : Perm (Fin 7), relabel σ G = F7 := by
  obtain ⟨hcard, x, hxG, hxc, hGN⟩ := degree_seven_order hGA hG hA hidx
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_c7.trans hxc.symm))
  have hμ : τ * mu7 * τ⁻¹ ∈ G := by
    have hmem : τ * mu7 * τ⁻¹ ∈ alternatingGroup (Fin 7) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
      refine ⟨by simp [mem_alternatingGroup, mu7_sign], ?_⟩
      apply mem_normalizer_zpowers_of_conj_eq_zpow (k := 2)
      rw [← hτ, conj_zpow, ← mu7_conj]
      group
    rw [← hGN] at hmem
    exact hmem.1
  set G' := relabel τ⁻¹ G with hG'
  have hc' : c7 ∈ G' := by rw [mem_relabel_perm, inv_inv, hτ]; exact hxG
  have hm' : mu7 ∈ G' := by rw [mem_relabel_perm, inv_inv]; exact hμ
  have hG'A : G' ≤ alternatingGroup (Fin 7) := relabel_le_alternatingGroup _ hGA
  have hG'p : IsPreprimitive G' (Fin 7) := (isPreprimitive_relabel_iff _ G).mpr hG
  have hA' : ¬ alternatingGroup (Fin 7) ≤ G' := fun h => hA (alternatingGroup_le_of_relabel _ h)
  have hcard' : Nat.card G' = 168 := by rw [hG', card_relabel, hcard]
  -- an element of the point stabilizer outside `⟨mu7⟩`
  obtain ⟨g, ⟨hg, hg0⟩, hgn⟩ : ∃ g ∈ G' ⊓ stabilizer (Perm (Fin 7)) (0 : Fin 7),
      g ∉ ({1, mu7, mu7 ^ 2} : Finset (Perm (Fin 7))) := by
    by_contra hcon
    push Not at hcon
    have h1 := card_eq_ncard_orbit_mul G' (0 : Fin 7)
    haveI := hG'p.toIsPretransitive
    have h7 : Nat.card (Fin 7) = 7 := by simp
    rw [MulAction.orbit_eq_univ, Set.ncard_univ, h7, hcard'] at h1
    have h2 : Nat.card (G' ⊓ stabilizer (Perm (Fin 7)) (0 : Fin 7) : Subgroup _) ≤ 3 := by
      calc _ ≤ ({1, mu7, mu7 ^ 2} : Finset (Perm (Fin 7))).card := card_le_of_subset_finset _ hcon
        _ ≤ 3 := Finset.card_le_three
    omega
  have hg0' : g 0 = 0 := hg0
  replace hg : g ∈ G' := hg
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hgn
  obtain ⟨n1, n2, n3⟩ := hgn
  rcases degree_seven_candidates g hg0' (hG'A hg) n1 n2 n3 with hF | hF | hbad
  · exact ⟨τ⁻¹, eq_F7 hG'A hcard' hc' hm' hg hg0' n1 n2 n3 hF⟩
  · refine ⟨rho7⁻¹ * τ⁻¹, ?_⟩
    rw [← relabel_relabel_perm]
    have hc'' : c7 ∈ relabel rho7⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho7_conj]
      exact zpow_mem hc' 3
    have hm'' : mu7 ∈ relabel rho7⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv, rho7_mu7, mul_assoc, mul_inv_cancel, mul_one]; exact hm'
    have hg'' : rho7⁻¹ * g * rho7 ∈ relabel rho7⁻¹ G' := by
      rw [mem_relabel_perm, inv_inv]; simpa [mul_assoc] using hg
    have hr0 : rho7 0 = 0 := by decide
    have hri0 : rho7⁻¹ 0 = 0 := by decide
    refine eq_F7 (relabel_le_alternatingGroup _ hG'A) (by rw [card_relabel, hcard'])
      hc'' hm'' hg'' (by simp [Perm.mul_apply, hr0, hg0', hri0]) ?_ ?_ ?_ hF
    all_goals intro h
    all_goals have hg' : g = rho7 * (rho7⁻¹ * g * rho7) * rho7⁻¹ := by group
    all_goals rw [h] at hg'
    · exact n1 (by rw [hg']; group)
    · exact n2 (by rw [hg']; decide)
    · exact n3 (by rw [hg']; decide)
  · exact absurd hbad (not_bad35 hG'p hA' (by rw [hcard']; norm_num)
      (by simp [hc', hm', hg, inv_mem hg]) words7)

end Babai.DM52
