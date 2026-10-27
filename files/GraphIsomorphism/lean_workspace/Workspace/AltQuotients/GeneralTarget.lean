/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.5 (Main Structure Theorem) with an arbitrary finite target.
-/
import Workspace.AltQuotients.MainStructure

/-!
# §10.5 with an arbitrary finite target

Section 10 is stated throughout for the target `S_k = S(Fin k)`, as the paper states it.
Section 13 uses it for a giant representation `ϕ : G → S(Γ)` onto an arbitrary finite set
`Γ` (Sec. 13.1).  This file carries the notions of Theorem 10.5.1 — `T(x)`, `t_Δ`, the
standard blocks — and the items of Theorem 10.5.1 that are proved, over to an arbitrary
finite target, by transport along a bijection `Γ ≃ Fin |Γ|`.

Nothing here is new mathematics: each statement is the Section 10 statement with `S_k`
replaced by `S(Γ)`, and each proof is "apply the `Fin k` version to `e ∘ ϕ` and transport
back", where `e : Γ ≃ Fin |Γ|`.

The notions carry the suffix `Gen`; for `Γ = Fin k` they are the Section 10 notions on the
nose (`Babai.affectedGen_eq_affected`, `Babai.TpointGen_eq_Tpoint`).
-/

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Transporting the ingredients of Eq. (51) along a bijection -/

section Transport

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The alternating group is carried onto the alternating group by `S(α) ≃ S(β)`. -/
theorem map_alternatingGroup_congr (e : α ≃ β) :
    (alternatingGroup α).map (Equiv.permCongrHom e).toMonoidHom = alternatingGroup β := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (e.permCongr f) = 1
    rw [Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.1 hf
  · intro hg
    refine ⟨e.symm.permCongr g, ?_, ?_⟩
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.1 hg
    · show e.permCongr (e.symm.permCongr g) = g
      ext b
      simp [Equiv.permCongr_apply]

theorem alternating_le_map_congr_iff (e : α ≃ β) (K : Subgroup (Equiv.Perm α)) :
    alternatingGroup β ≤ K.map (Equiv.permCongrHom e).toMonoidHom ↔ alternatingGroup α ≤ K := by
  rw [← map_alternatingGroup_congr e,
    Subgroup.map_le_map_iff_of_injective (Equiv.permCongrHom e).injective]

theorem permCongrHom_apply_apply (e : α ≃ β) (f : Equiv.Perm α) (b : β) :
    ((Equiv.permCongrHom e).toMonoidHom f) b = e (f (e.symm b)) := rfl

/-- `e ∘ e⁻¹ = id` on permutation groups. -/
theorem permCongrHom_symm_comp (e : α ≃ β) :
    (Equiv.permCongrHom e.symm).toMonoidHom.comp (Equiv.permCongrHom e).toMonoidHom
      = MonoidHom.id (Equiv.Perm α) := by
  refine MonoidHom.ext fun f => Equiv.ext fun a => ?_
  show e.symm.permCongr (e.permCongr f) a = f a
  simp [Equiv.permCongr_apply]

theorem map_permCongrHom_symm (e : α ≃ β) (H : Subgroup (Equiv.Perm α)) :
    (H.map (Equiv.permCongrHom e).toMonoidHom).map (Equiv.permCongrHom e.symm).toMonoidHom
      = H := by
  rw [Subgroup.map_map, permCongrHom_symm_comp, Subgroup.map_id]

/-- The image of a set under a transported permutation. -/
theorem image_permCongrHom_image (e : α ≃ β) (f : Equiv.Perm α) (T : Set α) :
    ((Equiv.permCongrHom e).toMonoidHom f) '' (e '' T) = e '' (f '' T) := by
  ext b
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, by rw [permCongrHom_apply_apply]; simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, by rw [permCongrHom_apply_apply]; simp⟩

/-- The setwise stabilizer transports along `e`. -/
theorem map_setwiseStabilizer_congr (e : α ≃ β) (K : Subgroup (Equiv.Perm α)) (T : Set α) :
    (setwiseStabilizer K T).map (Equiv.permCongrHom e).toMonoidHom
      = setwiseStabilizer (K.map (Equiv.permCongrHom e).toMonoidHom) (e '' T) := by
  have himg : ∀ f : Equiv.Perm α,
      ((Equiv.permCongrHom e).toMonoidHom f) '' (e '' T) = e '' (f '' T) :=
    fun f => image_permCongrHom_image e f T
  ext g
  constructor
  · rintro ⟨f, ⟨hfK, hfT⟩, rfl⟩
    exact ⟨⟨f, hfK, rfl⟩, by rw [himg, hfT]⟩
  · rintro ⟨⟨f, hfK, rfl⟩, hfix⟩
    refine ⟨f, ⟨hfK, ?_⟩, rfl⟩
    rw [himg] at hfix
    exact Set.image_injective.2 e.injective hfix

/-- The pointwise stabilizer transports along `e`. -/
theorem map_pointwiseStabilizer_congr (e : α ≃ β) (K : Subgroup (Equiv.Perm α)) (T : Set α) :
    (pointwiseStabilizer K T).map (Equiv.permCongrHom e).toMonoidHom
      = pointwiseStabilizer (K.map (Equiv.permCongrHom e).toMonoidHom) (e '' T) := by
  ext g
  constructor
  · rintro ⟨f, ⟨hfK, hfT⟩, rfl⟩
    refine ⟨⟨f, hfK, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [permCongrHom_apply_apply]
    simp [hfT y hy]
  · rintro ⟨⟨f, hfK, rfl⟩, hfix⟩
    refine ⟨f, ⟨hfK, fun y hy => ?_⟩, rfl⟩
    have := hfix (e y) ⟨y, hy, rfl⟩
    rw [permCongrHom_apply_apply] at this
    simpa using e.injective this

/-- Eq. (51) transports along `e`: `T` is sandwiched by `H` iff `T^e` is sandwiched by
`H^e`. -/
theorem isSandwichSet_map_congr (e : α ≃ β) {H : Subgroup (Equiv.Perm α)} {T : Set α}
    (h : IsSandwichSet H T) :
    IsSandwichSet (H.map (Equiv.permCongrHom e).toMonoidHom) (e '' T) := by
  obtain ⟨hcard, hlo, hhi⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ e.injective]
    rwa [Nat.card_eq_fintype_card, ← Fintype.card_congr e, ← Nat.card_eq_fintype_card]
  · rw [← map_alternatingGroup_congr e, ← map_pointwiseStabilizer_congr]
    exact Subgroup.map_mono hlo
  · have htop : (⊤ : Subgroup (Equiv.Perm β))
        = (⊤ : Subgroup (Equiv.Perm α)).map (Equiv.permCongrHom e).toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ (Equiv.permCongrHom e).surjective]
    rw [htop, ← map_setwiseStabilizer_congr]
    exact Subgroup.map_mono hhi

/-- Eq. (51) pulls back along `e`. -/
theorem isSandwichSet_of_map_congr (e : α ≃ β) {H : Subgroup (Equiv.Perm α)} {S : Set β}
    (h : IsSandwichSet (H.map (Equiv.permCongrHom e).toMonoidHom) S) :
    IsSandwichSet H (e.symm '' S) := by
  have := isSandwichSet_map_congr e.symm h
  rwa [map_permCongrHom_symm] at this

end Transport

/-! ### The notions of Theorem 10.5.1 with an arbitrary finite target -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}
  {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (ϕ : G →* Equiv.Perm Γ)

/-- **Definition 10.3.4** (Affected) with an arbitrary finite target. -/
def AffectedGen (x : Ω) : Prop := ¬ alternatingGroup Γ ≤ (stabilizer G x).map ϕ

/-- Theorem 10.3.5's set `D`, with an arbitrary finite target. -/
def unaffectedSetGen : Set Ω := {x | ¬ AffectedGen ϕ x}

/-- Theorem 10.5.1 (a): `T(x)`, with an arbitrary finite target. -/
noncomputable def TpointGen (x : Ω) : Set Γ := sandwichSet ((stabilizer G x).map ϕ)

/-- Theorem 10.5.1 (c): `|T(x)|`, with an arbitrary finite target. -/
noncomputable def tPointGen (x : Ω) : ℕ := (TpointGen ϕ x).ncard

/-- Theorem 10.5.1 (e): the standard block of `x`, with an arbitrary finite target. -/
noncomputable def standardBlockGen (x : Ω) : Set Ω :=
  {y | y ∈ orbit G x ∧ TpointGen ϕ y = TpointGen ϕ x}

/-- Theorem 10.5.1 (e): the standard blocks in `Δ`, with an arbitrary finite target. -/
noncomputable def standardBlocksGen (Δ : Set Ω) : Set (Set Ω) :=
  {B | ∃ x ∈ Δ, B = standardBlockGen ϕ x}

@[simp] theorem affectedGen_eq_affected {k : ℕ} (ψ : G →* Equiv.Perm (Fin k)) (x : Ω) :
    AffectedGen ψ x = Affected ψ x := rfl

@[simp] theorem TpointGen_eq_Tpoint {k : ℕ} (ψ : G →* Equiv.Perm (Fin k)) (x : Ω) :
    TpointGen ψ x = Tpoint ψ x := rfl

/-! ### Transport of Theorem 10.5.1 -/

section Main

/-- The bijection `Γ ≃ Fin |Γ|` used for the transport. -/
private noncomputable def eq : Γ ≃ Fin (Fintype.card Γ) := Fintype.equivFin Γ

/-- The transported representation `G → S(Fin |Γ|)`. -/
private noncomputable def fin : G →* Equiv.Perm (Fin (Fintype.card Γ)) :=
  (Equiv.permCongrHom (eq (Γ := Γ))).toMonoidHom.comp ϕ

private theorem map_fin (H : Subgroup G) :
    H.map (fin ϕ) = (H.map ϕ).map (Equiv.permCongrHom (eq (Γ := Γ))).toMonoidHom := by
  rw [fin, Subgroup.map_map]

private theorem range_fin :
    (fin ϕ).range = ϕ.range.map (Equiv.permCongrHom (eq (Γ := Γ))).toMonoidHom := by
  have h := map_fin ϕ (⊤ : Subgroup G)
  simpa [MonoidHom.range_eq_map] using h

private theorem isGiantRep_fin (hϕ : IsGiantRep ϕ) : IsGiantRep (fin ϕ) := by
  rw [IsGiantRep, range_fin, alternating_le_map_congr_iff]
  exact hϕ

private theorem affected_fin (x : Ω) : Affected (fin ϕ) x ↔ AffectedGen ϕ x := by
  unfold Affected AffectedGen
  rw [map_fin, alternating_le_map_congr_iff]

private theorem unaffectedSet_fin : unaffectedSet (fin ϕ) = unaffectedSetGen ϕ := by
  ext x
  simp only [unaffectedSet, unaffectedSetGen, Set.mem_setOf_eq, affected_fin ϕ x]

/-- The transported label: `T(x)` for `fin ϕ` is the image of `T(x)` for `ϕ`. -/
private theorem Tpoint_fin (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Fintype.card Γ) (maxOrbitLength G)) (x : Ω) :
    Tpoint (fin ϕ) x = (eq (Γ := Γ)) '' TpointGen ϕ x := by
  have hk9 : 9 ≤ Fintype.card Γ := by
    have : (9 : ℝ) ≤ ((Fintype.card Γ : ℕ) : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hfin := (theorem_10_5_1_a (fin ϕ) (isGiantRep_fin ϕ hϕ) hk x).1.2
  -- pull the sandwich set back along `e`
  have hback : IsSandwichSet ((stabilizer G x).map ϕ)
      ((eq (Γ := Γ)).symm '' Tpoint (fin ϕ) x) := by
    rw [map_fin] at hfin
    exact isSandwichSet_of_map_congr _ hfin
  have hgen : IsSandwichSet ((stabilizer G x).map ϕ) (TpointGen ϕ x) :=
    isSandwichSet_sandwichSet ⟨_, hback⟩
  have hcard : 5 ≤ Nat.card Γ := by
    rw [Nat.card_eq_fintype_card]; omega
  have := sandwichSet_unique hcard hgen hback
  rw [this]
  ext b
  constructor
  · rintro hb
    exact ⟨(eq (Γ := Γ)).symm b, ⟨b, hb, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    simpa using hc

private theorem tPoint_fin (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Fintype.card Γ) (maxOrbitLength G)) (x : Ω) :
    tPoint (fin ϕ) x = tPointGen ϕ x := by
  rw [tPoint, tPointGen, Tpoint_fin ϕ hϕ hk x,
    Set.ncard_image_of_injective _ (eq (Γ := Γ)).injective]

private theorem standardBlock_fin (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Fintype.card Γ) (maxOrbitLength G)) (x : Ω) :
    standardBlock (fin ϕ) x = standardBlockGen ϕ x := by
  ext y
  simp only [standardBlock, standardBlockGen, Set.mem_setOf_eq, Tpoint_fin ϕ hϕ hk,
    and_congr_right_iff]
  intro _
  exact ⟨fun h => Set.image_injective.2 (eq (Γ := Γ)).injective h, fun h => by rw [h]⟩

private theorem standardBlocks_fin (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK (Fintype.card Γ) (maxOrbitLength G)) (Δ : Set Ω) :
    standardBlocks (fin ϕ) Δ = standardBlocksGen ϕ Δ := by
  ext B
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (standardBlock_fin ϕ hϕ hk y)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (standardBlock_fin ϕ hϕ hk y).symm⟩

variable (hϕ : IsGiantRep ϕ) (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))

include hϕ hk

private theorem hkfin : VeryLargeK (Fintype.card Γ) (maxOrbitLength G) := by
  rwa [Nat.card_eq_fintype_card] at hk

/-- **Theorem 10.5.1 (a)** with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_a_gen (x : Ω) :
    (4 * (TpointGen ϕ x).ncard < Nat.card Γ ∧
        IsSandwichSet ((stabilizer G x).map ϕ) (TpointGen ϕ x)) ∧
      ∀ T : Set Γ, 4 * T.ncard < Nat.card Γ → IsSandwichSet ((stabilizer G x).map ϕ) T →
        T = TpointGen ϕ x := by
  have hkf := hkfin ϕ hϕ hk
  obtain ⟨⟨hlt, hsand⟩, huniq⟩ := theorem_10_5_1_a (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x
  rw [Tpoint_fin ϕ hϕ hkf x, Set.ncard_image_of_injective _ (eq (Γ := Γ)).injective] at hlt
  have hgen : IsSandwichSet ((stabilizer G x).map ϕ) (TpointGen ϕ x) := by
    have hex : ∃ T : Set Γ, IsSandwichSet ((stabilizer G x).map ϕ) T := by
      refine ⟨(eq (Γ := Γ)).symm '' Tpoint (fin ϕ) x, ?_⟩
      rw [map_fin] at hsand
      exact isSandwichSet_of_map_congr _ hsand
    exact isSandwichSet_sandwichSet hex
  have hcard5 : 5 ≤ Nat.card Γ := by
    have : 9 ≤ Fintype.card Γ := by
      have : (9 : ℝ) ≤ ((Fintype.card Γ : ℕ) : ℝ) := le_trans (le_max_left _ _) hkf
      exact_mod_cast this
    rw [Nat.card_eq_fintype_card]; omega
  refine ⟨⟨by rwa [Nat.card_eq_fintype_card], hgen⟩, fun T _ hT => ?_⟩
  exact sandwichSet_unique hcard5 hT hgen

/-- **Theorem 10.5.1 (b)** with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_b_gen (x : Ω) : AffectedGen ϕ x ↔ 1 ≤ (TpointGen ϕ x).ncard := by
  have hkf := hkfin ϕ hϕ hk
  have h := theorem_10_5_1_b (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x
  rw [Tpoint_fin ϕ hϕ hkf x, Set.ncard_image_of_injective _ (eq (Γ := Γ)).injective] at h
  rw [← h, affected_fin]

/-- **Theorem 10.5.1 (c)**, Eq. (54), with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_c_eq54_gen (x : Ω) (σ : G) :
    TpointGen ϕ (σ • x) = (ϕ σ) '' (TpointGen ϕ x) := by
  have hkf := hkfin ϕ hϕ hk
  have h := theorem_10_5_1_c_eq54 (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x σ
  rw [Tpoint_fin ϕ hϕ hkf, Tpoint_fin ϕ hϕ hkf] at h
  refine Set.image_injective.2 (eq (Γ := Γ)).injective ?_
  rw [h]
  exact image_permCongrHom_image (eq (Γ := Γ)) (ϕ σ) (TpointGen ϕ x)

/-- **Theorem 10.5.1 (c)** with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_c_gen {x y : Ω} (hy : y ∈ orbit G x) :
    tPointGen ϕ y = tPointGen ϕ x := by
  have hkf := hkfin ϕ hϕ hk
  have h := theorem_10_5_1_c (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf hy
  rwa [tPoint_fin ϕ hϕ hkf, tPoint_fin ϕ hϕ hkf] at h

/-- **Theorem 10.5.1 (d)** with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_d_gen :
    (∃ x : Ω, AffectedGen ϕ x) ∧
      alternatingGroup Γ ≤ (pointwiseStab G (unaffectedSetGen ϕ)).map ϕ := by
  have hkf := hkfin ϕ hϕ hk
  obtain ⟨⟨x, hx⟩, hle⟩ := theorem_10_5_1_d (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf
  refine ⟨⟨x, (affected_fin ϕ x).1 hx⟩, ?_⟩
  rw [unaffectedSet_fin ϕ, map_fin, alternating_le_map_congr_iff] at hle
  exact hle

/-- **Theorem 10.5.1 (e)** with an arbitrary finite target `S(Γ)`: the standard blocks form
a system of imprimitivity on each orbit. -/
theorem theorem_10_5_1_e_isSystem_gen (x : Ω) :
    IsSystemOfImprimitivity G (orbit G x) (standardBlocksGen ϕ (orbit G x)) := by
  have hkf := hkfin ϕ hϕ hk
  have h := theorem_10_5_1_e_isSystem (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x
  rwa [standardBlocks_fin ϕ hϕ hkf] at h

/-- **Theorem 10.5.1 (e)** with an arbitrary finite target `S(Γ)`: for `t_Δ = 0` the action
on the standard blocks is trivial. -/
theorem theorem_10_5_1_e_trivial_gen (x : Ω) (ht : tPointGen ϕ x = 0) :
    standardBlocksGen ϕ (orbit G x) = {orbit G x} := by
  have hkf := hkfin ϕ hϕ hk
  have h := theorem_10_5_1_e_trivial (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x
    (by rw [tPoint_fin ϕ hϕ hkf]; exact ht)
  rwa [standardBlocks_fin ϕ hϕ hkf] at h

/-- **Theorem 10.5.1 (f)** with an arbitrary finite target `S(Γ)`. -/
theorem theorem_10_5_1_f_gen (x : Ω) {B : Set Ω} (hB : B ∈ standardBlocksGen ϕ (orbit G x))
    {y : Ω} (hy : y ∈ B) :
    (setwiseStab G B).map ϕ = setwiseStabilizer ϕ.range (TpointGen ϕ y) := by
  have hkf := hkfin ϕ hϕ hk
  rw [← standardBlocks_fin ϕ hϕ hkf] at hB
  have h := theorem_10_5_1_f (fin ϕ) (isGiantRep_fin ϕ hϕ) hkf x hB hy
  rw [map_fin, Tpoint_fin ϕ hϕ hkf, range_fin, ← map_setwiseStabilizer_congr] at h
  exact Subgroup.map_injective (Equiv.permCongrHom (eq (Γ := Γ))).injective h

end Main

end Babai
