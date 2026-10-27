/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2B] from [DiM, Thm. 5.2A].
-/
import Workspace.AltQuotients.DM52.Intrans
import Workspace.AltQuotients.DM52.Degree5
import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Tools for [DiM, Thm. 5.2B]

[DiM] derive Theorem 5.2B from Theorem 5.2A applied to `G ∩ A` ("then `|A_n : G ∩ A_n| <
C(n,r)` and Theorem 5.2A applies to `G ∩ A_n`.  However some new exceptional cases arise.
We leave the proof as an exercise", p. 150).  The general facts used there:

* the index of `G` in `S` and of `G ∩ A` in `A` (`index_cases`);
* a subgroup of odd index in `Sym(Ω)` contains a transposition (`exists_isSwap_mem_of_odd`,
  Sylow's theorem), so a primitive one is `Sym(Ω)` (Jordan);
* a group containing a primitive group is primitive (`isPreprimitive_of_le`);
* a primitive subgroup of `S_9` of order `3024` does not exist (`not_card_3024`): its
  Sylow `7`-normalizer would be the full normalizer in `S_9`, which contains a
  transposition.
-/

universe u

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- `|A : G ∩ A| = |A : G|`. -/
theorem relIndex_inf_alternatingGroup (G : Subgroup (Perm Ω)) :
    (G ⊓ alternatingGroup Ω).relIndex (alternatingGroup Ω) =
      G.relIndex (alternatingGroup Ω) := by
  rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_right, ← Subgroup.relIndex]

/-- The index of `G` in `S` and of `G₀ := G ∩ A` in `A`: `|S : G| = 2 |A : G₀|` if
`G ≤ A`, and `|S : G| = |A : G₀|` otherwise. -/
theorem index_cases [Nontrivial Ω] (G : Subgroup (Perm Ω)) :
    (G ≤ alternatingGroup Ω ∧
        G.index = 2 * (G ⊓ alternatingGroup Ω).relIndex (alternatingGroup Ω)) ∨
      (¬ G ≤ alternatingGroup Ω ∧
        G.index = (G ⊓ alternatingGroup Ω).relIndex (alternatingGroup Ω)) := by
  have h1 := G.card_mul_index
  have h2 := card_mul_relIndex (inf_le_right : G ⊓ alternatingGroup Ω ≤ alternatingGroup Ω)
  have h3 := two_mul_card_alternatingGroup (Ω := Ω)
  rw [Nat.card_perm] at h1
  have hpos : 0 < Nat.card G := Nat.card_pos
  by_cases hGA : G ≤ alternatingGroup Ω
  · left
    refine ⟨hGA, ?_⟩
    rw [inf_of_le_left hGA] at h2 ⊢
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, ← h3, ← h2]; ring
  · right
    refine ⟨hGA, ?_⟩
    obtain ⟨y, hyG, hyA⟩ := Set.not_subset.mp hGA
    have hodd : sign y = -1 := by
      rcases Int.units_eq_one_or (sign y) with h | h
      · exact absurd (mem_alternatingGroup.mpr h) hyA
      · exact h
    have h4 := card_eq_two_mul_card_inf_alternatingGroup G hyG hodd
    rw [inf_comm] at h4
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, ← h3, ← h2, h4]; ring

omit [Fintype Ω] [DecidableEq Ω] in
/-- A group containing a primitive group is primitive. -/
theorem isPreprimitive_of_le {H G : Subgroup (Perm Ω)} (hle : H ≤ G)
    (hH : IsPreprimitive H Ω) : IsPreprimitive G Ω := by
  haveI : IsPretransitive G Ω := ⟨fun a b => by
    obtain ⟨h, hh⟩ := hH.exists_smul_eq a b
    exact ⟨⟨h, hle h.2⟩, hh⟩⟩
  refine ⟨fun {B} hB => hH.isTrivialBlock_of_isBlock ?_⟩
  intro g₁ g₂ hne
  exact hB (g₁ := ⟨g₁, hle g₁.2⟩) (g₂ := ⟨g₂, hle g₂.2⟩) hne

omit [Fintype Ω] [DecidableEq Ω] in
/-- A group containing a transitive group is transitive. -/
theorem isTransitive_of_le {H G : Subgroup (Perm Ω)} (hle : H ≤ G)
    (hH : IsTransitive H) : IsTransitive G := by
  rw [IsTransitive, isTransitiveAction_iff] at hH ⊢
  obtain ⟨hne, hH⟩ := hH
  refine ⟨hne, ⟨fun a b => ?_⟩⟩
  obtain ⟨h, hh⟩ := hH.exists_smul_eq a b
  exact ⟨⟨h, hle h.2⟩, hh⟩

/-- **A subgroup of odd index in `Sym(Ω)` contains a transposition**: it contains a Sylow
`2`-subgroup of `Sym(Ω)`, and every transposition lies in a conjugate of it. -/
theorem exists_isSwap_mem_of_odd [Nontrivial Ω] {G : Subgroup (Perm Ω)}
    (hodd : ¬ 2 ∣ G.index) : ∃ t ∈ G, IsSwap t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  set Q : Subgroup (Perm Ω) := (P : Subgroup G).map G.subtype with hQ
  have hQp : IsPGroup 2 Q := P.2.map G.subtype
  have hQi : ¬ 2 ∣ Q.index := by
    rw [hQ, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact P.not_dvd_index h
    · exact hodd h
  set S := hQp.toSylow hQi
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  have hsw : IsSwap (swap a b) := ⟨a, b, hab, rfl⟩
  have hZp : IsPGroup 2 (zpowers (swap a b)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hsw.orderOf, pow_one])
  obtain ⟨R, hR⟩ := hZp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm Ω) S R
  have ht : swap a b ∈ (g • S : Sylow 2 (Perm Ω)) := by
    rw [hg]; exact hR (mem_zpowers _)
  have ht' : swap a b ∈ MulAut.conj g • (S : Subgroup (Perm Ω)) := ht
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ht'
  have hmem : g⁻¹ * swap a b * g ∈ Q := by
    have : (MulAut.conj g)⁻¹ • swap a b = g⁻¹ * swap a b * g := by
      simp [MulAut.smul_def, MulAut.conj_symm_apply]
    rw [← this]
    simpa [S] using ht'
  refine ⟨g⁻¹ * swap a b * g, ?_, ?_⟩
  · obtain ⟨y, -, hy⟩ := hmem
    rw [← hy]; exact y.2
  · refine ⟨g⁻¹ a, g⁻¹ b, fun h => hab (g⁻¹.injective h), ?_⟩
    rw [swap_apply_apply, inv_inv]

/-- A subgroup of odd index in `Sym(Ω)` containing a primitive subgroup is `Sym(Ω)`
(Jordan's theorem). -/
theorem eq_top_of_odd_of_isPreprimitive [Nontrivial Ω] {G : Subgroup (Perm Ω)}
    (hodd : ¬ 2 ∣ G.index) (hG : IsPreprimitive G Ω) : G = ⊤ := by
  obtain ⟨t, ht, hsw⟩ := exists_isSwap_mem_of_odd hodd
  exact subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG t hsw ht

/-! ### Degree nine -/

/-- **No primitive subgroup of `S_9` has order `3024`.**  With `P = ⟨x⟩` a Sylow
`7`-subgroup and `d := |N_G(P)|`: `d` divides `|N_S(P)|`, which divides
`|C_S(x)| · 6 = 84`, and the number `3024/d` of Sylow `7`-subgroups is `≡ 1 (mod 7)`; so
`d = 84` and `N_G(P) = N_S(P)`, which contains the transposition of the two fixed points of
`x`; then `G = S_9` by Jordan's theorem. -/
theorem not_card_3024 {G : Subgroup (Perm (Fin 9))} (hG : IsPreprimitive G (Fin 9))
    (hcard : Nat.card G = 3024) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 G := default
  have hfact : (Nat.card G).factorization 7 = 1 := by
    have hp : Nat.Prime 7 := by norm_num
    have h0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    apply le_antisymm
    · by_contra h
      have := (hp.pow_dvd_iff_le_factorization h0 (k := 2)).mpr (by omega)
      rw [hcard] at this; revert this; decide
    · exact (hp.dvd_iff_one_le_factorization h0).mp (by rw [hcard]; decide)
  have hPcard : Nat.card P = 7 := by rw [P.card_eq_multiplicity, hfact, pow_one]
  set P' : Subgroup (Perm (Fin 9)) := (P : Subgroup G).map G.subtype with hP'
  have hP'card : Nat.card P' = 7 := by
    rw [hP', Subgroup.card_map_of_injective G.subtype_injective, hPcard]
  have hP'G : P' ≤ G := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P', x ≠ 1 := by
    by_contra h
    push Not at h
    have : P' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hP'card
    norm_num at hP'card
  have hxord : orderOf x = 7 := by
    have hdvd : orderOf x ∣ 7 := by
      rw [← hP'card, ← Subgroup.orderOf_mk x hxP]; exact orderOf_dvd_natCard _
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzP : (zpowers x : Subgroup (Perm (Fin 9))) = P' := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr hxP
    · rw [hP'card, Nat.card_zpowers, hxord]
  have hxc : x.cycleType = {7} :=
    cycleType_eq_of_orderOf_prime (by norm_num) hxord (by norm_num)
  set N := normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) with hN
  -- `|N| ∣ 84`
  have hN84 : Nat.card N ∣ 84 := by
    have := card_normalizer_zpowers_dvd x
    rwa [card_centralizer_of_cycleType hxc, hxord, Nat.totient_prime (by norm_num)] at this
  -- `N_G(P) ≅ G ∩ N`
  have hsub : (P : Subgroup G) = P'.subgroupOf G := by
    rw [hP']; exact (Subgroup.comap_map_eq_self_of_injective G.subtype_injective _).symm
  have hNG : Nat.card (normalizer ((P : Subgroup G) : Set G)) = Nat.card (G ⊓ N : Subgroup _) := by
    rw [hsub, ← Subgroup.subgroupOf_normalizer_eq hP'G, card_subgroupOf, inf_comm, hN, hzP]
  set d := Nat.card (G ⊓ N : Subgroup _) with hd
  have hdN : d ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_right
  have hdG : d ∣ 3024 := by
    rw [← hcard, hd]; exact Subgroup.card_dvd_of_le inf_le_left
  have hmod : 3024 / d % 7 = 1 := by
    rw [← hNG, ← hcard]
    have h1 := card_sylow_modEq_one (p := 7) (G := G)
    rw [Sylow.card_eq_index_normalizer P] at h1
    have h2 := (normalizer ((P : Subgroup G) : Set G)).card_mul_index
    have hpos : 0 < Nat.card (normalizer ((P : Subgroup G) : Set G)) := Nat.card_pos
    rw [← h2, Nat.mul_div_cancel_left _ hpos]
    exact h1
  have hd84 : d = 84 := by
    have := hdN.trans hN84
    have hle : d ≤ 84 := Nat.le_of_dvd (by norm_num) this
    have key : ∀ d < 85, d ∣ 84 → d ∣ 3024 → 3024 / d % 7 = 1 → d = 84 := by decide
    exact key d (by omega) this hdG hmod
  -- `N ≤ G`
  have hNle : N ≤ G := by
    have hcN : Nat.card N = 84 := Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hN84)
      (hd84 ▸ Nat.le_of_dvd Nat.card_pos hdN)
    have heq : G ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [← hd, hd84, hcN])
    rw [← heq]; exact inf_le_left
  -- the transposition of the two fixed points of `x`
  have hsupp : x.support.card = 7 := by
    rw [← Equiv.Perm.sum_cycleType, hxc]; rfl
  have hc2 : (x.supportᶜ).card = 2 := by
    rw [Finset.card_compl, hsupp]; rfl
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hc2
  have ha : x a = a := by
    have : a ∈ x.supportᶜ := by rw [hsab]; simp
    simpa using this
  have hb : x b = b := by
    have : b ∈ x.supportᶜ := by rw [hsab]; simp
    simpa using this
  have hcomm : Commute (swap a b) x := by
    apply Equiv.Perm.Disjoint.commute
    intro y
    by_cases hya : y = a
    · right; rw [hya, ha]
    by_cases hyb : y = b
    · right; rw [hyb, hb]
    · left; exact swap_apply_of_ne_of_ne hya hyb
  have hswN : swap a b ∈ N := by
    apply Subgroup.centralizer_le_normalizer
    rw [centralizer_zpowers_eq, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcomm.eq.symm
  have htop := subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG (swap a b)
    ⟨a, b, hab, rfl⟩ (hNle hswN)
  rw [htop, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    at hcard
  revert hcard; decide

end Babai.DM52
