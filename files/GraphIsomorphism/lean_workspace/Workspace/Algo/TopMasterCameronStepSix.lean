import Workspace.Algo.TopMasterCameronPrepared
import Workspace.Algo.TopMasterHintWindowLink

/-! # The computed step 6 is the step 6 of the live line-1 record
Section 11.3, step 4 finds the minimal blocks of the group induced on the
window, and step 6 descends to the preimage `G₁` of the Cameron subgroup
`N̄` (Theorem 11.2.1). The RAM computes these objects from the raw window.
This file builds the record `Babai.DescentData` of the group-frame instance
of a raw node from exactly those computed objects, and proves that the
subgroup the machine descends to is the record's `K₁`.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- The block action commutes with a bijection of the domains, one element at a
time (the elementwise form of `Babai.map_onBlocks_permCongrHom`). -/
theorem blockHom_permCongrHom {α β : Type*} (e : α ≃ β) {G : Subgroup (Perm α)}
    {ℬ : Set (Set α)} (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Perm α) '' B ∈ ℬ)
    {H : Subgroup (Perm β)} (hH : ∀ σ ∈ H, ∀ B ∈ blockImage e ℬ, (σ : Perm β) '' B ∈ blockImage e ℬ)
    (σ : G) (τ : H) (hστ : (τ : Perm β) = (permCongrHom e).toMonoidHom σ) :
    (permCongrHom (blockImageEquiv e ℬ)).toMonoidHom (blockHom G ℬ hperm σ) =
      blockHom H (blockImage e ℬ) hH τ := by
  refine Equiv.ext fun C => Subtype.ext ?_
  obtain ⟨B, hB, hBC⟩ := C.2
  have hCB : (C : Set β) = (e : α → β) '' B := hBC.symm
  have hsymm : (blockImageEquiv e ℬ).symm C = ⟨B, hB⟩ := by
    apply (blockImageEquiv e ℬ).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (by rw [blockImageEquiv_apply_coe, hCB])
  change (((blockImageEquiv e ℬ) (blockHom G ℬ hperm σ
    ((blockImageEquiv e ℬ).symm C)) : blockImage e ℬ) : Set β) = _
  rw [hsymm, blockImageEquiv_apply_coe, blockHom_apply_coe, blockHom_apply_coe, hστ, hCB,
    image_permCongrHom_image_gen]

/-- §2.2.1: on a nonempty domain, a group is transitive exactly when it has one orbit. -/
theorem isTransitive_iff_orbitList_length {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (G : Subgroup (Perm Ω)) : IsTransitive G ↔ (orbitList G).length = 1 := by
  rw [length_orbitList, IsTransitive, isTransitiveAction_iff, Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨⟨fun a b => ?_⟩, ⟨Quotient.mk'' (Classical.arbitrary Ω)⟩⟩
    induction a using Quotient.inductionOn'
    induction b using Quotient.inductionOn'
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
      (h.exists_smul_eq _ _)))
  · rintro ⟨hs, -⟩
    refine ⟨inferInstance, ⟨fun a b => ?_⟩⟩
    have he : (Quotient.mk'' b : MulAction.orbitRel.Quotient G Ω) = Quotient.mk'' a :=
      hs.elim _ _
    exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact' he))

section Blocks
variable {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)

include hw in
/-- The numbered window group is the group the instance induces on its window. -/
theorem masterCamWindowGroup_map :
    (decGroup W.1.length (primitiveWindowInput W).1).map
      (permCongrHom (winEquiv n W.1 hnd hlt)).toMonoidHom =
      (masterGroupData hinv).windowGroup :=
  masterHintWindowGroup_map (p := (W, default)) hw hnd hlt hinv

/-- §11.3, step 4 at the group-frame instance of a raw node: the computed
minimal blocks of the numbered window group. -/
noncomputable def masterCamBlockData : Babai.BlockData (masterGroupInstance n W) :=
  camMinBlockData (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn (masterGroupData hinv)
    (winEquiv n W.1 hnd hlt) (masterCamWindowGroup_map hw hnd hlt hinv)

/-- The numbering of the computed minimal blocks as blocks of the instance. -/
noncomputable def masterCamBlockEquiv :
    Fin (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≃
      (masterCamBlockData hw hnd hlt hinv htr hn).ℬ :=
  camMinBlockEquiv (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn (masterGroupData hinv)
    (winEquiv n W.1 hnd hlt) (masterCamWindowGroup_map hw hnd hlt hinv)

theorem masterCamBlockEquiv_group :
    (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2).map
        (permCongrHom (masterCamBlockEquiv hw hnd hlt hinv htr hn)).toMonoidHom =
      onBlocks (masterCamBlockData hw hnd hlt hinv htr hn).windowGroup
        (masterCamBlockData hw hnd hlt hinv htr hn).ℬ
        (masterCamBlockData hw hnd hlt hinv htr hn).system.permutes :=
  camMinBlockEquiv_group (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl htr hn
    (masterGroupData hinv) (winEquiv n W.1 hnd hlt) (masterCamWindowGroup_map hw hnd hlt hinv)

/-- **The computed rows are the block action.** For every element of the
ambient group, the stored image row, read through the block numbering, is the
action of its restriction on the blocks of step 4. -/
theorem masterCamBlockHom_row (g : decGroup n W.2.1) :
    (permCongrHom (masterCamBlockEquiv hw hnd hlt hinv htr hn)).toMonoidHom
        (masterWindowBlockHom hx hw hnd hlt hinv htr hn g) =
      blockHom (masterCamBlockData hw hnd hlt hinv htr hn).windowGroup
        (masterCamBlockData hw hnd hlt hinv htr hn).ℬ
        (masterCamBlockData hw hnd hlt hinv htr hn).system.permutes (restrictOnto hinv g) := by
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  let q := camActionRange (masterRestrictionAction_wf hx hw hnd hlt hinv) g
  have hq : ((restrictOnto hinv g : restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) :
      Perm (winSet n W.1)) = (permCongrHom (winEquiv n W.1 hnd hlt)).toMonoidHom q.val := by
    have h1 := masterHintWindowEquiv_restrict (p := (W, default)) hx hw hnd hlt hinv g
    have h2 := masterHintWindowEquiv_coe (p := (W, default)) hw hnd hlt hinv q
    rw [← h1]
    exact h2
  have hrow := camMinimalAction_row hgs (rfl : W.1.length = W.1.length) htr hn q
  refine Equiv.ext fun C => ?_
  have hmin := isMinimalSystemOfImprimitivity_rawMinBlocks hgs (rfl : W.1.length = W.1.length) htr hn
  have hkey := blockHom_permCongrHom (winEquiv n W.1 hnd hlt) hmin.permutes
    (masterCamBlockData hw hnd hlt hinv htr hn).system.permutes q (restrictOnto hinv g) hq
  have := congrArg (fun F : Perm _ => F C) hkey
  rw [← hrow] at this
  exact this

variable {c : RawCameron} (h : c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom)
    (hhi : (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hwindow : 64 ≤ (masterGroupInstance n W).windowSize)

/-- §11.3, step 6 at the group-frame instance of a raw node: Theorem 11.2.1
applied to the computed block action, with the computed Cameron structure.
The enumerations are still the default ones here. -/
noncomputable def masterCamDescentBase : DescentData (masterGroupInstance n W) :=
  camDescentData (masterCamBlockData hw hnd hlt hinv htr hn)
    (masterCamBlockEquiv hw hnd hlt hinv htr hn) h (masterWindowBlockAction W).2.2
    (masterCamBlockEquiv_group hw hnd hlt hinv htr hn) hlo hhi hwindow

include hx in
/-- **The subgroup the machine descends to is `K₁`.** The kernel computed from
the signed Cameron action is the preimage of `N̄` under the block action of the
restriction to the window. -/
theorem masterCamDescentBase_K₁ :
    (masterCamDescentBase hw hnd hlt hinv htr hn h hlo hhi hwindow).K₁ =
      decGroup n (camLiftGens (c, masterWindowBlockAction W)) := by
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  rw [camLiftGens_spec hp h hhi]
  ext g
  rw [mem_camLiftSubgroup]
  change g ∈ windowPreimSubgroup _ _ _ _ ↔ _
  rw [mem_windowPreimSubgroup]
  refine exists_congr fun hg => ?_
  change _ ∈ preimSubgroup _ _ ↔ _
  rw [mem_preimSubgroup]
  have hrow := masterCamBlockHom_row hx hw hnd hlt hinv htr hn ⟨g, hg⟩
  constructor
  · rintro ⟨hr, a, ha, he⟩
    have he2 : (permCongrHom (masterCamBlockEquiv hw hnd hlt hinv htr hn)).toMonoidHom a =
        (permCongrHom (masterCamBlockEquiv hw hnd hlt hinv htr hn)).toMonoidHom
          (masterWindowBlockHom hx hw hnd hlt hinv htr hn ⟨g, hg⟩) := he.trans hrow.symm
    have := (permCongrHom (masterCamBlockEquiv hw hnd hlt hinv htr hn)).injective he2
    convert ha using 1
    exact this.symm
  · intro ha
    refine ⟨(restrictOnto hinv ⟨g, hg⟩).property, _, ha, ?_⟩
    exact hrow
end Blocks
end Algo
