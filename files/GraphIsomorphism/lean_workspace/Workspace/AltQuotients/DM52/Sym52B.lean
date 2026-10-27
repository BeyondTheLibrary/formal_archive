/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The case analysis for [DiM, Thm. 5.2B], cited by Theorem 10.4.2 (§10.4).
-/
import Workspace.AltQuotients.DM52.SymTools

/-!
# The cases of [DiM, Thm. 5.2B]

For `G ≤ S` with `G₀ := G ∩ A`, each conclusion of [DiM, Thm. 5.2A] for `G₀` is turned into
a conclusion for `G`:

* case (i) for `G₀` gives case (i) for `G` (`image_eq_of_sandwich`): `Ω \ Δ` is the only
  orbit of `G₀` of length more than `n/2`, so `G`, which normalizes `G₀`, fixes it;
* case (ii) for `G₀` gives case (ii) for `G` (`preservesHalvingPartition_of_normalizes`):
  `G₀` is the full stabilizer in `A` of the halving partition, and the normalizer of that
  group preserves the partition;
* case (iii)(a) for `G₀` gives case (iii)(a) for `G` with blocks of size `2`
  (`blocks_of_six`): blocks of size `3` are excluded by Lagrange's theorem.
-/

universe u

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- The `3`-cycle `(x y w)`-type element `swap x w * swap x y`, which maps `x` to `y` and
fixes every point outside `{x, y, w}`. -/
theorem exists_three_cycle {X : Set Ω} (hX : 3 ≤ X.ncard) {x y : Ω} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) :
    ∃ τ : Perm Ω, sign τ = 1 ∧ τ x = y ∧ ∀ z ∉ X, τ z = z := by
  obtain ⟨w, hw, hwx, hwy⟩ : ∃ w ∈ X, w ≠ x ∧ w ≠ y := by
    have e1 := Set.ncard_diff_singleton_le (X \ {x}) y
    have e3 : ((X \ {x}) \ {y}).ncard + 1 ≥ (X \ {x}).ncard := by
      have := Set.ncard_le_ncard_diff_add_ncard (X \ {x}) {y}
      simp at this; omega
    have e4 : (X \ {x}).ncard + 1 ≥ X.ncard := by
      have := Set.ncard_le_ncard_diff_add_ncard X {x}
      simp at this; omega
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (by omega : ((X \ {x}) \ {y}).ncard ≠ 0)
    simp only [Set.mem_diff, Set.mem_singleton_iff] at hw
    exact ⟨w, hw.1.1, hw.1.2, hw.2⟩
  refine ⟨swap x w * swap x y, ?_, ?_, fun z hz => ?_⟩
  · rw [Perm.sign_mul, sign_swap hwx.symm, sign_swap hxy]; decide
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxy.symm hwy.symm]
  · have hzx : z ≠ x := fun h => hz (h ▸ hx)
    have hzy : z ≠ y := fun h => hz (h ▸ hy)
    have hzw : z ≠ w := fun h => hz (h ▸ hw)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hzx hzw]

omit [Fintype Ω] [DecidableEq Ω] in
/-- A permutation mapping `X` into `X`, whose inverse does the same, fixes `X`. -/
theorem image_eq_of_maps {σ : Perm Ω} {X : Set Ω} (h1 : ∀ x ∈ X, σ x ∈ X)
    (h2 : ∀ x ∈ X, σ⁻¹ x ∈ X) : σ '' X = X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact h1 x hx
  · intro hy; exact ⟨σ⁻¹ y, h2 y hy, by simp⟩

/-- **Case (i)**: if `A_(Δ) ≤ G₀ ≤ A_{Δ}` with `2|Δ| < n` and `G` normalizes `G₀`, then `G`
fixes `Δ`: `Ω \ Δ` is an orbit of `G₀` of length more than `n/2`, and `G` permutes the orbits
of `G₀`. -/
theorem image_eq_of_sandwich (hn : 5 ≤ Nat.card Ω) {G₀ G : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hΔ : 2 * Δ.ncard < Nat.card Ω)
    (hlow : pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G₀)
    (hup : G₀ ≤ setwiseStabilizer (alternatingGroup Ω) Δ)
    (hnorm : ∀ g ∈ G, ∀ τ ∈ G₀, g * τ * g⁻¹ ∈ G₀) {σ : Perm Ω} (hσ : σ ∈ G) :
    σ '' Δ = Δ := by
  set Γ : Set Ω := Δᶜ with hΓ
  have hR : Δ.ncard + Γ.ncard = Nat.card Ω := ncard_add_ncard_compl Δ
  -- `G₀` is transitive on `Γ`
  have htrans : ∀ x ∈ Γ, ∀ y ∈ Γ, ∃ τ ∈ G₀, τ x = y := by
    intro x hx y hy
    by_cases hxy : x = y
    · exact ⟨1, G₀.one_mem, by simp [hxy]⟩
    obtain ⟨τ, hτs, hτx, hτf⟩ := exists_three_cycle (X := Γ) (by omega) hx hy hxy
    exact ⟨τ, hlow ⟨hτs, fun z hz => hτf z (by simpa [hΓ] using hz)⟩, hτx⟩
  -- `G₀` preserves `Γ`
  have hpres : ∀ τ ∈ G₀, ∀ x ∈ Γ, τ x ∈ Γ := by
    intro τ hτ x hx hxΔ
    have h := (hup hτ).2
    have : τ x ∈ τ '' Δ := by rw [h]; exact hxΔ
    exact hx ((τ.injective.mem_set_image).mp this)
  -- `G` maps `Γ` into `Γ`
  have hmaps : ∀ g ∈ G, ∀ y ∈ Γ, g y ∈ Γ := by
    intro g hg y hy
    obtain ⟨z, hz, hgz⟩ : ∃ z ∈ Γ, g z ∈ Γ := by
      by_contra hc
      push Not at hc
      have hsub : g '' Γ ⊆ Δ := by
        rintro _ ⟨z, hz, rfl⟩
        have := hc z hz
        simpa [hΓ] using this
      have := Set.ncard_le_ncard hsub
      rw [Set.ncard_image_of_injective _ g.injective] at this
      omega
    obtain ⟨τ, hτ, hτz⟩ := htrans z hz y hy
    have := hpres _ (hnorm g hg τ hτ) (g z) hgz
    simpa [Perm.mul_apply, hτz] using this
  have hΓeq : σ '' Γ = Γ := image_eq_of_maps (hmaps σ hσ) (hmaps σ⁻¹ (G.inv_mem hσ))
  rw [show Δ = Γᶜ by simp [hΓ], Set.image_compl_eq σ.bijective, hΓeq]

/-- The stabilizer in `Sym(Ω)` of the partition `{B, Ω \ B}`. -/
def halvingStab (B : Set Ω) : Subgroup (Perm Ω) where
  carrier := {σ | σ '' B = B ∨ σ '' B = Bᶜ}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro a b ha hb
    simp only [Set.mem_setOf_eq, Perm.coe_mul, Set.image_comp] at ha hb ⊢
    rcases hb with hb | hb <;> rw [hb]
    · exact ha
    · rw [Set.image_compl_eq a.bijective]
      rcases ha with ha | ha <;> rw [ha]
      · exact Or.inr rfl
      · left; simp
  inv_mem' := by
    rintro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rcases ha with ha | ha
    · left
      conv_lhs => rw [← ha]
      rw [Set.image_image]; simp
    · right
      have : (a⁻¹ : Perm Ω) '' Bᶜ = B := by
        rw [← ha, Set.image_image]; simp
      calc (a⁻¹ : Perm Ω) '' B = (a⁻¹ : Perm Ω) '' (Bᶜ)ᶜ := by rw [compl_compl]
        _ = ((a⁻¹ : Perm Ω) '' Bᶜ)ᶜ := Set.image_compl_eq (a⁻¹).bijective
        _ = Bᶜ := by rw [this]

omit [Fintype Ω] [DecidableEq Ω] in
theorem mem_halvingStab {B : Set Ω} {σ : Perm Ω} :
    σ ∈ halvingStab B ↔ σ '' B = B ∨ σ '' B = Bᶜ := Iff.rfl

/-- **Case (ii)**: if `G₀ ≤ A` preserves a halving partition and has index `½ C(n, n/2)` in
`A`, and `G` normalizes `G₀`, then `G` preserves the same partition.  Indeed `G₀` is then the
full stabilizer of the partition in `A`, so it contains `Alt(B)`; for `g ∈ G`, conjugation
shows that `Alt(B)` fixes `B^g`, which forces `B^g = B` or `B^g = Ω \ B`. -/
theorem preservesHalvingPartition_of_normalizes (hn : 5 ≤ Nat.card Ω)
    {G₀ G : Subgroup (Perm Ω)} (hG₀A : G₀ ≤ alternatingGroup Ω)
    (hH : PreservesHalvingPartition G₀)
    (h2 : 2 * G₀.relIndex (alternatingGroup Ω) = (Nat.card Ω).choose (Nat.card Ω / 2))
    (hnorm : ∀ g ∈ G, ∀ τ ∈ G₀, g * τ * g⁻¹ ∈ G₀) : PreservesHalvingPartition G := by
  obtain ⟨B, hB2, hpres⟩ := hH
  refine ⟨B, hB2, ?_⟩
  set A := alternatingGroup Ω
  set W := halvingStab B ⊓ A with hW
  have hWA : W ≤ A := inf_le_right
  have hG₀W : G₀ ≤ W := fun σ hσ => ⟨hpres σ hσ, hG₀A hσ⟩
  have hC : 0 < (Nat.card Ω).choose (Nat.card Ω / 2) := Nat.choose_pos (Nat.div_le_self _ 2)
  have hdvd := Subgroup.relIndex_dvd_of_le_left A hG₀W
  have hpos : 0 < G₀.relIndex A := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hle := Nat.le_of_dvd hpos hdvd
  have hW2 : 2 * W.relIndex A = (Nat.card Ω).choose (Nat.card Ω / 2) :=
    two_mul_relIndex_eq_of_halving hWA hn ⟨B, hB2, fun σ hσ => hσ.1⟩
      (show W.relIndex A < _ by omega)
  have hmul := Subgroup.relIndex_mul_relIndex G₀ W A hG₀W hWA
  have hWpos : 0 < W.relIndex A := by omega
  have h1 : G₀.relIndex W = 1 := by
    have : G₀.relIndex W * W.relIndex A = 1 * W.relIndex A := by rw [hmul]; omega
    exact Nat.eq_of_mul_eq_mul_right hWpos this
  have hWG₀ : W ≤ G₀ := Subgroup.relIndex_eq_one.mp h1
  -- `Alt(B) ≤ G₀`
  have hAlt : ∀ τ ∈ pointwiseStabilizer A Bᶜ, τ ∈ G₀ := by
    rintro τ ⟨hτA, hτf⟩
    apply hWG₀
    refine ⟨Or.inl ?_, hτA⟩
    have hc : τ '' Bᶜ = Bᶜ := by
      rw [Set.image_congr (fun x hx => hτf x hx), Set.image_id']
    rw [← compl_compl B, Set.image_compl_eq τ.bijective, hc]
  have hR := ncard_add_ncard_compl B
  obtain ⟨z, hz⟩ : (Bᶜ : Set Ω).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  intro σ hσ
  set D := σ '' B with hD
  -- `Alt(B)` fixes `D`
  have hτD : ∀ τ ∈ pointwiseStabilizer A Bᶜ, τ '' D = D := by
    intro τ hτ
    have hρ := hpres _ (by simpa using hnorm σ⁻¹ (G.inv_mem hσ) τ (hAlt τ hτ))
    have heq : τ '' D = σ '' ((σ⁻¹ * τ * σ : Perm Ω) '' B) := by
      rw [hD, Set.image_image, Set.image_image]; congr 1; ext x; simp [Perm.mul_apply]
    rcases hρ with hρ | hρ
    · rw [heq, hρ]
    · exfalso
      rw [hρ, Set.image_compl_eq σ.bijective, ← hD] at heq
      have hτz : τ z = z := hτ.2 z hz
      have e1 : z ∈ D ↔ τ z ∈ τ '' D := (τ.injective.mem_set_image).symm
      rw [heq, hτz, Set.mem_compl_iff] at e1
      tauto
  have hB3 : 3 ≤ B.ncard := by omega
  have hsub : B ⊆ D ∨ B ⊆ Dᶜ := by
    by_contra hc
    push Not at hc
    obtain ⟨⟨x, hxB, hxD⟩, ⟨y, hyB, hyD⟩⟩ := And.intro (Set.not_subset.mp hc.1)
      (Set.not_subset.mp hc.2)
    rw [Set.mem_compl_iff, not_not] at hyD
    have hxy : y ≠ x := fun h => hxD (h ▸ hyD)
    obtain ⟨τ, hτs, hτx, hτf⟩ := exists_three_cycle hB3 hyB hxB hxy
    have hτ : τ ∈ pointwiseStabilizer A Bᶜ := ⟨hτs, fun w hw => hτf w hw⟩
    have : τ y ∈ τ '' D := Set.mem_image_of_mem _ hyD
    rw [hτD τ hτ, hτx] at this
    exact hxD this
  have hDcard : D.ncard = B.ncard := Set.ncard_image_of_injective _ σ.injective
  have hDc := ncard_add_ncard_compl D
  rcases hsub with h | h
  · exact Or.inl (Set.eq_of_subset_of_ncard_le h (by omega)).symm
  · right
    have := Set.eq_of_subset_of_ncard_le h (by omega)
    rw [← compl_compl D, ← this]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The orbit of a nonempty block of a transitive group is a system of imprimitivity. -/
theorem isSystemOfImprimitivity_orbit {G : Subgroup (Perm Ω)} (hT : IsPretransitive G Ω)
    {B : Set Ω} (hB : IsBlock G B) (hBne : B.Nonempty) :
    IsSystemOfImprimitivity G Set.univ (orbit G B) := by
  obtain ⟨hcov, -, hdisj, hGP, -⟩ := blockSystem_facts hT hB hBne
  refine ⟨fun σ _ => Set.image_univ_of_surjective σ.surjective, ?_, hdisj, ?_,
    fun σ hσ C hC => (hGP hσ C).mp hC, ⟨B, mem_orbit_self B⟩, ?_⟩
  · rintro C ⟨g, rfl⟩; exact hBne.smul_set
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨C, hC, hx⟩ := hcov x
    exact Set.mem_sUnion.mpr ⟨C, hC, hx⟩
  · rintro C ⟨g, rfl⟩ C' ⟨g', rfl⟩
    refine ⟨(g' : Perm Ω) * (g : Perm Ω)⁻¹, G.mul_mem g'.2 (G.inv_mem g.2), ?_⟩
    show ((g' : Perm Ω) * (g : Perm Ω)⁻¹) '' (g • B) = g' • B
    rw [smul_set_eq_image, smul_set_eq_image, Set.image_image]
    congr 1; ext x; simp

/-- **Case (iii)(a)**: a transitive, not primitive `G ≤ S_6` of index `15` has a system of
imprimitivity with blocks of size `2`.  A block `B` has size `2` or `3`; for size `3`, `G`
preserves `{B, Ω \ B}`, so `G ∩ S_{B}` has index at most `2` in `G` (order `48`) and divides
`|S_{B}| = 36`, which is impossible. -/
theorem blocks_of_six (h6 : Nat.card Ω = 6) {G : Subgroup (Perm Ω)} (hT : IsTransitive G)
    (hnp : ¬ IsPreprimitive G Ω) (hidx : G.index = 15) :
    ∃ ℬ : Set (Set Ω), IsSystemOfImprimitivity G Set.univ ℬ ∧ ∀ B ∈ ℬ, B.ncard = 2 := by
  classical
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  haveI hpt : IsPretransitive G Ω := ((isTransitiveAction_iff G Ω).mp hT).2
  obtain ⟨B, hB, hBnt⟩ : ∃ B : Set Ω, IsBlock G B ∧ ¬ IsTrivialBlock B := by
    by_contra h
    push Not at h
    exact hnp ⟨fun {B} hB => h B hB⟩
  rw [IsTrivialBlock, not_or] at hBnt
  obtain ⟨hns, hnu⟩ := hBnt
  have hBne : B.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hns (h ▸ Set.subsingleton_empty)
  have hB2 : 2 ≤ B.ncard := by
    have := (Set.one_lt_ncard_iff_nontrivial).mpr (Set.not_subsingleton_iff.mp hns)
    omega
  have hB6 : B.ncard < 6 := by
    rw [← h6, ← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr hnu)
  obtain ⟨hcov, hcard, hdisj, hGP, hmul⟩ := blockSystem_facts hpt hB hBne
  rw [h6] at hmul
  have hB23 : B.ncard = 2 ∨ B.ncard = 3 := by
    have hd : B.ncard ∣ 6 := ⟨_, hmul.symm⟩
    interval_cases hk : B.ncard <;> omega
  rcases hB23 with h2 | h3
  · exact ⟨orbit G B, isSystemOfImprimitivity_orbit hpt hB hBne,
      fun C hC => (hcard C hC).trans h2⟩
  · exfalso
    have hR := ncard_add_ncard_compl B
    have hpresB : ∀ σ ∈ G, (σ : Perm Ω) '' B = B ∨ (σ : Perm Ω) '' B = Bᶜ := by
      intro σ hσ
      rcases (isBlock_iff_smul_eq_or_disjoint.mp hB) ⟨σ, hσ⟩ with h | h
      · left; rwa [smul_set_eq_image] at h
      · right
        rw [smul_set_eq_image] at h
        have hsub : (σ : Perm Ω) '' B ⊆ Bᶜ := fun x hx hxB => Set.disjoint_left.mp h hx hxB
        exact Set.eq_of_subset_of_ncard_le hsub
          (by rw [Set.ncard_image_of_injective _ σ.injective]; omega)
    have hL := relIndex_inf_le_two (K := ⊤) le_top hpresB
    set S := setwiseStabilizer (⊤ : Subgroup (Perm Ω)) B
    have hcG : Nat.card G = 48 := by
      have := G.card_mul_index
      rw [hidx, Nat.card_perm, h6, show (6 : ℕ)! = 720 by decide] at this
      omega
    have hcS : Nat.card S = 36 := by
      have e1 := card_mul_relIndex (le_top : S ≤ ⊤)
      rw [relIndex_setwiseStabilizer le_top (m := 3) (by omega) h3, Subgroup.card_top,
        Nat.card_perm, h6, show (6 : ℕ)! = 720 by decide,
        show (6 : ℕ).choose 3 = 20 by decide] at e1
      omega
    have e2 := card_mul_relIndex (inf_le_left : G ⊓ S ≤ G)
    have hLpos : 0 < (G ⊓ S).relIndex G := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have d1 : Nat.card (G ⊓ S : Subgroup _) ∣ 48 := hcG ▸ Subgroup.card_dvd_of_le inf_le_left
    have d2 : Nat.card (G ⊓ S : Subgroup _) ∣ 36 := hcS ▸ Subgroup.card_dvd_of_le inf_le_right
    have d3 : Nat.card (G ⊓ S : Subgroup _) ∣ 12 := by
      have := Nat.dvd_gcd d1 d2; simpa using this
    have := Nat.le_of_dvd (by norm_num) d3
    have h24 : 24 ≤ Nat.card (G ⊓ S : Subgroup _) := by
      rw [hcG] at e2
      by_contra hc
      have : Nat.card (G ⊓ S : Subgroup _) * (G ⊓ S).relIndex G ≤ 23 * 2 :=
        Nat.mul_le_mul (by omega) hL
      omega
    omega

end Babai.DM52
