/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 11 of Procedure Align (Sec. 14.2): the Johnson case data a round of the
dominant window attaches to its calls, carried from the window type `↥Δ` back to `Ω`.
-/
import Workspace.Master.Sec15

/-!
# Carrying a Johnson case along `Babai.windowInstance`

A branch of Sec. 15 runs on the window `Δ` of its instance: the reduction it builds lives
on the type `↥Δ`, and `Babai.liftWindow` reads it back on `Ω`, sending a call
`J' : Babai.SIInstance ↥Δ A` to `Babai.windowInstance K Δ hinv x J'`.  Line 11 of Procedure
Align hands a pair `(G*, ϕ*)` down to each call, and the field `lift` of
`Babai.Sec15Remaining` asks for it on `Ω`.  The round of the dominant window produces it on
`↥Δ`.  This file closes the gap.

The paper never mentions the passage: it says "an instance of String Isomorphism with window
`Δ`" and goes on.  Everything here is bookkeeping, and it is organized in two layers.

* **A bijection of the domains.**  For `e : α ≃ β` the map `σ ↦ e σ e⁻¹`
  (`Equiv.permCongrHom`) carries `S(α)` onto `S(β)`, and every notion of Def. 11.4.1 goes
  with it: transitivity, a system of imprimitivity, acting on it as a Johnson group, hence
  the Johnson case itself (`Babai.isJohnsonCase_map_permCongrHom`).  A giant representation
  composed with a group isomorphism is a giant representation
  (`Babai.isGiantRep_comp_mulEquiv`).
* **The window inside the window.**  For `D ⊆ ↥Δ` the bijection is
  `Babai.windowSetEquiv : ↥D ≃ ↥(Subtype.val '' D)`, and the group identification is
  `Babai.restrictTo_windowPreimSubgroup_image`: the group induced on `Subtype.val '' D` by
  the full preimage of `M'` in `K` is the image of the group induced on `D` by `M'`.

`Babai.JohnsonCaseData.ofWindow` puts the two together.  It keeps `m` and `t` unchanged
(`ofWindow_m`, `ofWindow_t`), which is what the Johnson parameter of the measure of Sec. 15
reads (`Babai.param_ofWindow`).
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### A bijection of the domains -/

section PermCongr

variable {α β : Type*}

/-- `Babai.permCongrHom_apply_apply` without the finiteness hypotheses of its section: the
transported permutation is `e σ e⁻¹`. -/
theorem permCongrHom_apply_pt (e : α ≃ β) (f : Equiv.Perm α) (b : β) :
    ((Equiv.permCongrHom e).toMonoidHom f) b = e (f (e.symm b)) := rfl

/-- `Babai.image_permCongrHom_image` without the finiteness hypotheses of its section. -/
theorem image_permCongrHom_image_gen (e : α ≃ β) (f : Equiv.Perm α) (T : Set α) :
    ((Equiv.permCongrHom e).toMonoidHom f) '' ((e : α → β) '' T) = (e : α → β) '' (f '' T) := by
  ext b
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, by rw [permCongrHom_apply_pt]; simp⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, by rw [permCongrHom_apply_pt]; simp⟩

/-- The image of a set of blocks under a bijection of the domains. -/
def blockImage (e : α ≃ β) (ℬ : Set (Set α)) : Set (Set β) :=
  (fun B => (e : α → β) '' B) '' ℬ

theorem mem_blockImage {e : α ≃ β} {ℬ : Set (Set α)} {C : Set β} :
    C ∈ blockImage e ℬ ↔ ∃ B ∈ ℬ, (e : α → β) '' B = C := Iff.rfl

theorem image_mem_blockImage (e : α ≃ β) {ℬ : Set (Set α)} {B : Set α} (hB : B ∈ ℬ) :
    (e : α → β) '' B ∈ blockImage e ℬ := ⟨B, hB, rfl⟩

/-- `B ↦ e '' B` is injective, so it is a bijection from `ℬ` onto its image. -/
noncomputable def blockImageEquiv (e : α ≃ β) (ℬ : Set (Set α)) : ℬ ≃ blockImage e ℬ :=
  Equiv.Set.image (fun B => (e : α → β) '' B) ℬ (Set.image_injective.2 e.injective)

@[simp] theorem blockImageEquiv_apply_coe (e : α ≃ β) (ℬ : Set (Set α)) (B : ℬ) :
    ((blockImageEquiv e ℬ B : blockImage e ℬ) : Set β) = (e : α → β) '' (B : Set α) := rfl

/-- §2.2.1: a transitive group stays transitive under a bijection of the domains. -/
theorem isTransitive_map_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    (h : IsTransitive G) : IsTransitive (G.map (Equiv.permCongrHom e).toMonoidHom) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨e x, ?_⟩
  ext b
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  have hb : e.symm b ∈ orbit G x := by rw [hx]; trivial
  obtain ⟨⟨σ, hσ⟩, hσx⟩ := hb
  have hσx' : σ x = e.symm b := hσx
  refine ⟨⟨_, ⟨σ, hσ, rfl⟩⟩, ?_⟩
  show (Equiv.permCongrHom e).toMonoidHom σ (e x) = b
  rw [permCongrHom_apply_pt, Equiv.symm_apply_apply, hσx', Equiv.apply_symm_apply]

/-- §2.2.1: a system of imprimitivity on the whole domain stays one under a bijection of
the domains. -/
theorem isSystemOfImprimitivity_map_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    {ℬ : Set (Set α)} (h : IsSystemOfImprimitivity G Set.univ ℬ) :
    IsSystemOfImprimitivity (G.map (Equiv.permCongrHom e).toMonoidHom) Set.univ
      (blockImage e ℬ) where
  invariant := fun σ _ => Set.image_univ_of_surjective (σ : Equiv.Perm β).surjective
  nonempty := by
    rintro _ ⟨B, hB, rfl⟩
    exact (h.nonempty B hB).image _
  pairwiseDisjoint := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ hne
    have hBB' : B ≠ B' := fun hEq => hne (by rw [hEq])
    exact (Set.disjoint_image_iff e.injective).2 (h.pairwiseDisjoint B hB B' hB' hBB')
  covers := by
    ext b
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have : e.symm b ∈ ⋃₀ ℬ := by rw [h.covers]; trivial
    obtain ⟨B, hB, hmem⟩ := this
    exact ⟨_, image_mem_blockImage e hB, ⟨_, hmem, Equiv.apply_symm_apply _ _⟩⟩
  permutes := by
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨B, hB, rfl⟩
    rw [image_permCongrHom_image_gen]
    exact image_mem_blockImage e (h.permutes σ hσ B hB)
  blocks_nonempty := by
    obtain ⟨B, hB⟩ := h.blocks_nonempty
    exact ⟨_, image_mem_blockImage e hB⟩
  transitiveOnBlocks := by
    rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩
    obtain ⟨σ, hσ, hσB⟩ := h.transitiveOnBlocks B hB B' hB'
    exact ⟨_, ⟨σ, hσ, rfl⟩, by rw [image_permCongrHom_image_gen, hσB]⟩

/-- The action on the blocks is carried along by the bijection `B ↦ e '' B` of the block
sets: `G^ℬ` goes to `(G^e)^{ℬ^e}`. -/
theorem map_onBlocks_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    {ℬ : Set (Set α)} (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm α) '' B ∈ ℬ)
    (hperm' : ∀ σ ∈ G.map (Equiv.permCongrHom e).toMonoidHom, ∀ B ∈ blockImage e ℬ,
      (σ : Equiv.Perm β) '' B ∈ blockImage e ℬ) :
    (onBlocks G ℬ hperm).map (Equiv.permCongrHom (blockImageEquiv e ℬ)).toMonoidHom
      = onBlocks (G.map (Equiv.permCongrHom e).toMonoidHom) (blockImage e ℬ) hperm' := by
  have key : ∀ (σ : Equiv.Perm α) (hσ : σ ∈ G),
      (Equiv.permCongrHom (blockImageEquiv e ℬ)).toMonoidHom
          (blockHom G ℬ hperm ⟨σ, hσ⟩)
        = blockHom (G.map (Equiv.permCongrHom e).toMonoidHom) (blockImage e ℬ) hperm'
            ⟨(Equiv.permCongrHom e).toMonoidHom σ, ⟨σ, hσ, rfl⟩⟩ := by
    intro σ hσ
    refine Equiv.ext fun C => Subtype.ext ?_
    obtain ⟨B, hB, hBC⟩ := C.2
    have hCB : (C : Set β) = (e : α → β) '' B := hBC.symm
    have hsymm : (blockImageEquiv e ℬ).symm C = ⟨B, hB⟩ := by
      apply (blockImageEquiv e ℬ).injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext (by rw [blockImageEquiv_apply_coe, hCB])
    show (((blockImageEquiv e ℬ) (blockHom G ℬ hperm ⟨σ, hσ⟩
      ((blockImageEquiv e ℬ).symm C)) : blockImage e ℬ) : Set β) = _
    rw [hsymm, blockImageEquiv_apply_coe]
    show (e : α → β) '' ((σ : Equiv.Perm α) '' B) = _
    show _ = ((Equiv.permCongrHom e).toMonoidHom σ : Equiv.Perm β) '' (C : Set β)
    rw [hCB, image_permCongrHom_image_gen]
  ext g
  constructor
  · rintro ⟨p, ⟨⟨σ, hσ⟩, rfl⟩, rfl⟩
    exact ⟨_, (key σ hσ).symm⟩
  · rintro ⟨⟨_, σ, hσ, rfl⟩, rfl⟩
    exact ⟨blockHom G ℬ hperm ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩, key σ hσ⟩

/-- Conjugating first by `B ↦ e '' B` and then by its inverse followed by the labelling
`e₀` of the blocks is conjugating by `e₀`. -/
theorem permCongrHom_comp_blockImageEquiv (e : α ≃ β) (ℬ : Set (Set α)) {k t : ℕ}
    (e₀ : ℬ ≃ binom (Fin k) t) :
    (Equiv.permCongrHom ((blockImageEquiv e ℬ).symm.trans e₀)).toMonoidHom.comp
        (Equiv.permCongrHom (blockImageEquiv e ℬ)).toMonoidHom
      = (Equiv.permCongrHom e₀).toMonoidHom := by
  refine MonoidHom.ext fun p => Equiv.ext fun s => ?_
  show ((blockImageEquiv e ℬ).symm.trans e₀)
      ((blockImageEquiv e ℬ) (p ((blockImageEquiv e ℬ).symm
        (((blockImageEquiv e ℬ).symm.trans e₀).symm s)))) = e₀ (p (e₀.symm s))
  simp

/-- §11.4: "acting on `ℬ` as the Johnson group `S_k^{(t)}`" is carried along a bijection of
the domains. -/
theorem actsAsJohnsonS_map_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    {ℬ : Set (Set α)} {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm α) '' B ∈ ℬ}
    {hperm' : ∀ σ ∈ G.map (Equiv.permCongrHom e).toMonoidHom, ∀ B ∈ blockImage e ℬ,
      (σ : Equiv.Perm β) '' B ∈ blockImage e ℬ} {k t : ℕ}
    (h : ActsAsJohnsonS G ℬ hperm k t) :
    ActsAsJohnsonS (G.map (Equiv.permCongrHom e).toMonoidHom) (blockImage e ℬ) hperm' k t := by
  obtain ⟨e₀, he₀⟩ := h
  refine ⟨(blockImageEquiv e ℬ).symm.trans e₀, ?_⟩
  rw [← map_onBlocks_permCongrHom e hperm hperm', Subgroup.map_map,
    permCongrHom_comp_blockImageEquiv e ℬ e₀, he₀]

/-- §11.4: "acting on `ℬ` as the Johnson group `A_k^{(t)}`" is carried along a bijection of
the domains. -/
theorem actsAsJohnsonA_map_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    {ℬ : Set (Set α)} {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm α) '' B ∈ ℬ}
    {hperm' : ∀ σ ∈ G.map (Equiv.permCongrHom e).toMonoidHom, ∀ B ∈ blockImage e ℬ,
      (σ : Equiv.Perm β) '' B ∈ blockImage e ℬ} {k t : ℕ}
    (h : ActsAsJohnsonA G ℬ hperm k t) :
    ActsAsJohnsonA (G.map (Equiv.permCongrHom e).toMonoidHom) (blockImage e ℬ) hperm' k t := by
  obtain ⟨e₀, he₀⟩ := h
  refine ⟨(blockImageEquiv e ℬ).symm.trans e₀, ?_⟩
  rw [← map_onBlocks_permCongrHom e hperm hperm', Subgroup.map_map,
    permCongrHom_comp_blockImageEquiv e ℬ e₀, he₀]

/-- §11.4, **Definition 11.4.1 is carried along a bijection of the domains**: if `(G, ℬ)`
is the Johnson case with parameters `k, t` then so is `(G^e, ℬ^e)`. -/
theorem isJohnsonCase_map_permCongrHom (e : α ≃ β) {G : Subgroup (Equiv.Perm α)}
    {ℬ : Set (Set α)} {k t : ℕ} (h : IsJohnsonCase G ℬ k t) :
    IsJohnsonCase (G.map (Equiv.permCongrHom e).toMonoidHom) (blockImage e ℬ) k t where
  t_pos := h.t_pos
  two_mul_t_le := h.two_mul_t_le
  transitive := isTransitive_map_permCongrHom e h.transitive
  system := isSystemOfImprimitivity_map_permCongrHom e h.system
  johnson := by
    rcases h.johnson with hS | hA
    · exact Or.inl (actsAsJohnsonS_map_permCongrHom e hS)
    · exact Or.inr (actsAsJohnsonA_map_permCongrHom e hA)

end PermCongr

/-! ### A giant representation, read through an isomorphism of groups -/

section Giant

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G H : Type*} [Group G] [Group H]

/-- §2.2.1: a giant representation stays one when the group is renamed.  The range of
`ϕ ∘ ψ` is the range of `ϕ` because `ψ` is onto. -/
theorem isGiantRep_comp_mulEquiv (ψ : H ≃* G) {ϕ : G →* Equiv.Perm Γ} (h : IsGiantRep ϕ) :
    IsGiantRep (ϕ.comp ψ.toMonoidHom) := by
  intro g hg
  obtain ⟨a, ha⟩ := h hg
  exact ⟨ψ.symm a, by rw [MonoidHom.comp_apply]; simpa using ha⟩

end Giant

/-! ### The window inside the window

An instance of the round runs on `↥Δ` and its window is a set `D ⊆ ↥Δ`; read on `Ω` its
window is `Subtype.val '' D`, and its group is the full preimage in `K` of the group `M'`
the call is made with respect to.  The two windows are matched by `Babai.windowSetEquiv`,
and the two groups induced on them by `Babai.restrictTo_windowPreimSubgroup_image`. -/

section WindowSet

variable {Ω : Type u} {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

/-- The window of a call of a reduction on `↥Δ`, read on `Ω`: `↥D ≃ ↥(Subtype.val '' D)`. -/
noncomputable def windowSetEquiv (Δ : Set Ω) (D : Set Δ) : D ≃ (Subtype.val '' D : Set Ω) :=
  Equiv.Set.image (Subtype.val : Δ → Ω) D Subtype.val_injective

@[simp] theorem windowSetEquiv_apply_coe (Δ : Set Ω) (D : Set Δ) (w : D) :
    ((windowSetEquiv Δ D w : (Subtype.val '' D : Set Ω)) : Ω) = ((w : Δ) : Ω) := rfl

/-- The lifted window is invariant under the lifted group. -/
theorem isInvariant_image_windowPreimSubgroup (hinv : IsInvariant K Δ)
    {M' : Subgroup (Equiv.Perm Δ)} {D : Set Δ} (hD : IsInvariant M' D) :
    IsInvariant (windowPreimSubgroup K Δ hinv M') (Subtype.val '' D) := by
  intro σ hσ
  obtain ⟨hσK, hσM⟩ := mem_windowPreimSubgroup.1 hσ
  have hρ := hD _ hσM
  show (σ : Equiv.Perm Ω) '' (Subtype.val '' D) = Subtype.val '' D
  rw [← Set.image_comp]
  have hcomp : ((σ : Equiv.Perm Ω) : Ω → Ω) ∘ (Subtype.val : Δ → Ω) =
      (Subtype.val : Δ → Ω) ∘ (restrictHom K Δ hinv ⟨σ, hσK⟩ : Equiv.Perm Δ) := by
    funext w
    exact (coe_restrictHom_apply hinv ⟨σ, hσK⟩ w).symm
  rw [hcomp, Set.image_comp, hρ]

/-- The permutation of the lifted window induced by `τ ∈ K` is the one induced by the
restriction of `τ` to `Δ`, read through `Babai.windowSetEquiv`. -/
theorem restrictHom_windowPreimSubgroup_apply (hinv : IsInvariant K Δ)
    {M' : Subgroup (Equiv.Perm Δ)} {D : Set Δ} (hD : IsInvariant M' D)
    {τ : Equiv.Perm Ω} (hτK : τ ∈ K)
    (hτM : restrictHom K Δ hinv ⟨τ, hτK⟩ ∈ M')
    (hτP : τ ∈ windowPreimSubgroup K Δ hinv M') :
    restrictHom (windowPreimSubgroup K Δ hinv M') (Subtype.val '' D)
        (isInvariant_image_windowPreimSubgroup hinv hD) ⟨τ, hτP⟩
      = (Equiv.permCongrHom (windowSetEquiv Δ D)).toMonoidHom
          (restrictHom M' D hD ⟨_, hτM⟩) := by
  refine Equiv.ext fun w => Subtype.ext ?_
  obtain ⟨u, hu, huw⟩ := w.2
  have hw : ((w : (Subtype.val '' D : Set Ω)) : Ω) = (u : Ω) := huw.symm
  have hsymm : (windowSetEquiv Δ D).symm w = ⟨u, hu⟩ := by
    apply (windowSetEquiv Δ D).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (by rw [windowSetEquiv_apply_coe, hw])
  show (τ : Equiv.Perm Ω) ((w : (Subtype.val '' D : Set Ω)) : Ω) = _
  show _ = (((windowSetEquiv Δ D) (restrictHom M' D hD ⟨_, hτM⟩
    ((windowSetEquiv Δ D).symm w)) : (Subtype.val '' D : Set Ω)) : Ω)
  rw [hsymm, windowSetEquiv_apply_coe, hw]
  exact (coe_restrictHom_apply hinv ⟨τ, hτK⟩ u).symm

/-- **The group induced on the lifted window is the lifted group induced on the window.**

The full preimage in `K` of `M' ≤ K^Δ` induces on `Subtype.val '' D` exactly the image of
`M'^D` under `Babai.windowSetEquiv`. -/
theorem restrictTo_windowPreimSubgroup_image (hinv : IsInvariant K Δ)
    {M' : Subgroup (Equiv.Perm Δ)} (hle : M' ≤ restrictTo K Δ hinv) {D : Set Δ}
    (hD : IsInvariant M' D) :
    restrictTo (windowPreimSubgroup K Δ hinv M') (Subtype.val '' D)
        (isInvariant_image_windowPreimSubgroup hinv hD)
      = (restrictTo M' D hD).map
          (Equiv.permCongrHom (windowSetEquiv Δ D)).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨⟨τ, hτP⟩, rfl⟩
    obtain ⟨hτK, hτM⟩ := mem_windowPreimSubgroup.1 hτP
    exact ⟨_, ⟨⟨_, hτM⟩, rfl⟩,
      (restrictHom_windowPreimSubgroup_apply hinv hD hτK hτM hτP).symm⟩
  · rintro ⟨_, ⟨⟨ρ, hρM⟩, rfl⟩, rfl⟩
    obtain ⟨⟨τ, hτK⟩, hτρ⟩ := MonoidHom.mem_range.1 (hle hρM)
    have hτM : restrictHom K Δ hinv ⟨τ, hτK⟩ ∈ M' := by rw [hτρ]; exact hρM
    have hτP : τ ∈ windowPreimSubgroup K Δ hinv M' :=
      mem_windowPreimSubgroup.2 ⟨hτK, hτM⟩
    refine ⟨⟨τ, hτP⟩, ?_⟩
    rw [restrictHom_windowPreimSubgroup_apply hinv hD hτK hτM hτP]
    congr 2
    exact Subtype.ext hτρ

end WindowSet

/-! ### The Johnson case data of a call, read on `Ω` -/

section OfWindow

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} [Fintype Δ]

/-- The group induced on the lifted window, named as the group induced on the window: the
isomorphism behind `Babai.restrictTo_windowPreimSubgroup_image`. -/
noncomputable def windowRestrictMulEquiv (hinv : IsInvariant K Δ)
    {M' : Subgroup (Equiv.Perm Δ)} (hle : M' ≤ restrictTo K Δ hinv) {D : Set Δ}
    (hD : IsInvariant M' D) :
    restrictTo (windowPreimSubgroup K Δ hinv M') (Subtype.val '' D)
        (isInvariant_image_windowPreimSubgroup hinv hD)
      ≃* restrictTo M' D hD :=
  ((Subgroup.equivMapOfInjective (restrictTo M' D hD)
      (Equiv.permCongrHom (windowSetEquiv Δ D)).toMonoidHom
      (Equiv.permCongrHom (windowSetEquiv Δ D)).injective).trans
    (MulEquiv.subgroupCongr
      (restrictTo_windowPreimSubgroup_image hinv hle hD).symm)).symm

/-- §15, line 11 of Procedure Align: **the Johnson case data of a call of a round that runs
on the window `Δ`, read on `Ω`**.

A round of lines 7–11 runs on the type `↥Δ`; `Babai.liftWindow` sends its call `J'` to
`Babai.windowInstance K Δ hinv x₀ J'`, and this is the hint of that call.  The Johnson
parameter `m` and the parameter `t` of the standard blocks are unchanged
(`Babai.JohnsonCaseData.ofWindow_m`, `ofWindow_t`), because nothing but the names of the
points changes: the group is the full preimage of `M' = d.K` in `K`, the block system is
carried over by `Babai.windowSetEquiv`, and the giant representation is composed with the
identification `Babai.windowRestrictMulEquiv` of the two groups induced on the window. -/
noncomputable def JohnsonCaseData.ofWindow (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {J' : SIInstance Δ A} (d : JohnsonCaseData J') (hle : d.K ≤ restrictTo K Δ hinv) :
    JohnsonCaseData (windowInstance K Δ hinv x₀ J') where
  K := windowPreimSubgroup K Δ hinv d.K
  isGroup := by
    show windowPreim K Δ hinv J'.K = _
    rw [d.isGroup, coe_windowPreimSubgroup]
  invariant := isInvariant_image_windowPreimSubgroup hinv d.invariant
  ℬ := blockImage (windowSetEquiv Δ J'.Δ) d.ℬ
  m := d.m
  t := d.t
  johnson := by
    have h := isJohnsonCase_map_permCongrHom (windowSetEquiv Δ J'.Δ) d.johnson
    rw [← restrictTo_windowPreimSubgroup_image hinv hle d.invariant] at h
    exact h
  two_blocks := by
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := d.two_blocks
    exact ⟨_, image_mem_blockImage _ hB₁, _, image_mem_blockImage _ hB₂,
      fun h => hne (Set.image_injective.2 (windowSetEquiv Δ J'.Δ).injective h)⟩
  ϕ := d.ϕ.comp (windowRestrictMulEquiv hinv hle d.invariant).toMonoidHom
  giant := isGiantRep_comp_mulEquiv _ d.giant
  param_le := by
    show d.m ≤ (windowInstance K Δ hinv x₀ J').windowSize
    rw [windowSize_windowInstance]
    exact d.param_le
  window_large := by
    show 64 ≤ (windowInstance K Δ hinv x₀ J').windowSize
    rw [windowSize_windowInstance]
    exact d.window_large

@[simp] theorem JohnsonCaseData.ofWindow_m (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {J' : SIInstance Δ A} (d : JohnsonCaseData J') (hle : d.K ≤ restrictTo K Δ hinv) :
    (d.ofWindow hinv x₀ hle).m = d.m := rfl

@[simp] theorem JohnsonCaseData.ofWindow_t (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {J' : SIInstance Δ A} (d : JohnsonCaseData J') (hle : d.K ≤ restrictTo K Δ hinv) :
    (d.ofWindow hinv x₀ hle).t = d.t := rfl

/-- §15: **the Johnson parameter of the lifted hinted instance** is the Johnson parameter of
the hint the round attached on the window.  This is what the field `line4cd_decreases` of
`Babai.Sec15Remaining` reads through `Babai.MakesProgress`. -/
@[simp] theorem param_ofWindow (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {J' : SIInstance Δ A} (d : JohnsonCaseData J') (hle : d.K ≤ restrictTo K Δ hinv) :
    param (⟨windowInstance K Δ hinv x₀ J', some (d.ofWindow hinv x₀ hle)⟩ :
      HintedInstance Ω A) = d.m := rfl

/-- §15: the window size of the lifted hinted instance is the window size of the call on
`↥Δ` (`Babai.windowSize_windowInstance`). -/
@[simp] theorem win_windowInstance (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    (J' : SIInstance Δ A) (o : Option (JohnsonCaseData (windowInstance K Δ hinv x₀ J'))) :
    (⟨windowInstance K Δ hinv x₀ J', o⟩ : HintedInstance Ω A).win = J'.windowSize :=
  windowSize_windowInstance hinv x₀ J'

end OfWindow

end Babai
