/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background used by the proof of Lemma 10.3.1 (§10.3): maximal blocks of imprimitivity and
the primitivity of the induced action on them.
-/
import Workspace.Prelim.PermGroups

/-!
# Maximal blocks and the primitivity of the block action

The proof of Lemma 10.3.1 begins: "Let `B` be a maximal block of imprimitivity containing
`x` (so `|B| < |Ω|`). … Let `Ω'` be the set of `G`-images of `B`.  This is a system of
imprimitivity on which `G` acts as a primitive group."  The paper asserts both the
existence of `B` and the primitivity of the action on `Ω'` without proof; they are proved
here.

* `Babai.exists_minimalSystemOfImprimitivity_mem`: for a transitive `G` on at least two
  points and any `x ∈ Ω`, a minimal system of imprimitivity
  (`Babai.IsMinimalSystemOfImprimitivity`: at least two blocks, blocks maximal) with a
  block `B ∋ x`, `B ≠ Ω`;
* `Babai.isPrimitive_onBlocks`: `G^ℬ` is primitive for such a system.

The first is the same construction as `Babai.exists_minimalSystemOfImprimitivity`
(`Workspace/Luks/ReduceToJohnson.lean`, §11.3), with the base point prescribed; that file
lies downstream of Section 10, so the construction is repeated here under distinct names.
-/

namespace Babai

open MulAction Equiv

variable {Ω : Type*} [Fintype Ω]

/-! ### Images of blocks -/

/-- The image of a block of imprimitivity under an element of `G` is again a block of
imprimitivity. -/
theorem blockImage_isBlockOfImprimitivity {G : Subgroup (Equiv.Perm Ω)} {B : Set Ω}
    (hB : IsBlockOfImprimitivity G B) {σ : Equiv.Perm Ω} (hσ : σ ∈ G) :
    IsBlockOfImprimitivity G ((σ : Equiv.Perm Ω) '' B) := by
  refine ⟨hB.1.image _, fun g hg => ?_⟩
  have hmem : σ⁻¹ * g * σ ∈ G := mul_mem (mul_mem (inv_mem hσ) hg) hσ
  have hconj : (σ : Equiv.Perm Ω) '' ((σ⁻¹ * g * σ : Equiv.Perm Ω) '' B) =
      (g : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' B) := by
    rw [image_image_eq_mul_image, image_image_eq_mul_image]
    congr 1
    group
  rcases hB.2 _ hmem with h | h
  · left
    rw [← hconj, h]
  · right
    have himg : (σ : Equiv.Perm Ω) '' (((σ⁻¹ * g * σ : Equiv.Perm Ω) '' B) ∩ B) =
        (σ : Equiv.Perm Ω) '' (∅ : Set Ω) := by rw [h]
    rwa [Set.image_inter σ.injective, hconj, Set.image_empty] at himg

/-- Two `G`-images of a block of imprimitivity are equal or disjoint. -/
theorem blockImage_eq_or_disjoint {G : Subgroup (Equiv.Perm Ω)} {B : Set Ω}
    (hB : IsBlockOfImprimitivity G B) {σ τ : Equiv.Perm Ω} (hσ : σ ∈ G) (hτ : τ ∈ G) :
    (σ : Equiv.Perm Ω) '' B = (τ : Equiv.Perm Ω) '' B ∨
      Disjoint ((σ : Equiv.Perm Ω) '' B) ((τ : Equiv.Perm Ω) '' B) := by
  have hmul : (τ * (τ⁻¹ * σ) : Equiv.Perm Ω) = σ := by group
  rcases hB.2 (τ⁻¹ * σ) (mul_mem (inv_mem hτ) hσ) with h | h
  · left
    have h2 : (τ : Equiv.Perm Ω) '' ((τ⁻¹ * σ : Equiv.Perm Ω) '' B) =
        (τ : Equiv.Perm Ω) '' B := by rw [h]
    rwa [image_image_eq_mul_image, hmul] at h2
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    have h2 : (τ : Equiv.Perm Ω) '' (((τ⁻¹ * σ : Equiv.Perm Ω) '' B) ∩ B) =
        (τ : Equiv.Perm Ω) '' (∅ : Set Ω) := by rw [h]
    rwa [Set.image_inter τ.injective, image_image_eq_mul_image, hmul,
      Set.image_empty] at h2

/-! ### A maximal block through a prescribed point -/

/-- §10.3, proof of Lemma 10.3.1: "Let `B` be a maximal block of imprimitivity containing
`x` (so `|B| < |Ω|`)", together with the system `Ω'` of its `G`-images. -/
theorem exists_minimalSystemOfImprimitivity_mem {G : Subgroup (Equiv.Perm Ω)}
    (hG : IsTransitive G) (h2 : 2 ≤ Fintype.card Ω) (u : Ω) :
    ∃ (ℬ : Set (Set Ω)) (B : Set Ω), IsMinimalSystemOfImprimitivity G Set.univ ℬ ∧
      B ∈ ℬ ∧ u ∈ B ∧ B ≠ Set.univ := by
  classical
  have htrans : ∀ x : Ω, ∃ σ ∈ G, (σ : Equiv.Perm Ω) u = x := by
    obtain ⟨v, hv⟩ := hG
    intro x
    have hx : x ∈ orbit G v := by rw [hv]; trivial
    have hu : u ∈ orbit G v := by rw [hv]; trivial
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 hx
    obtain ⟨h, hh⟩ := mem_orbit_iff.1 hu
    refine ⟨(g : Equiv.Perm Ω) * (h : Equiv.Perm Ω)⁻¹, mul_mem g.2 (inv_mem h.2), ?_⟩
    have hh' : (h : Equiv.Perm Ω) v = u := by simpa [Subgroup.smul_def] using hh
    have hg' : (g : Equiv.Perm Ω) v = x := by simpa [Subgroup.smul_def] using hg
    simp only [Equiv.Perm.mul_apply]
    rw [show (h : Equiv.Perm Ω)⁻¹ u = v from by rw [← hh']; simp, hg']
  have hsingle_ne : ({u} : Set Ω) ≠ Set.univ := by
    intro h
    have hsub : ∀ x : Ω, x = u := by
      intro x
      have : x ∈ ({u} : Set Ω) := by rw [h]; trivial
      simpa using this
    have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.2 fun x y => by rw [hsub x, hsub y]
    omega
  have hsing : ({u} : Set Ω) ∈
      {B : Set Ω | IsBlockOfImprimitivity G B ∧ u ∈ B ∧ B ≠ Set.univ} := by
    refine ⟨⟨⟨u, rfl⟩, fun g hg => ?_⟩, rfl, hsingle_ne⟩
    by_cases h : (g : Equiv.Perm Ω) u = u
    · left; simp [h]
    · right
      ext x
      simp only [Set.image_singleton, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl hx
      exact h hx
  obtain ⟨B, hBmax⟩ :=
    Set.Finite.exists_maximal (s := {B : Set Ω | IsBlockOfImprimitivity G B ∧ u ∈ B ∧
      B ≠ Set.univ}) (Set.toFinite _) ⟨_, hsing⟩
  obtain ⟨hBblock, huB, hBne⟩ := hBmax.1
  have hBmaximal : ∀ C : Set Ω, IsBlockOfImprimitivity G C → u ∈ C → C ≠ Set.univ →
      B ⊆ C → C = B := fun C hC huC hCne hBC =>
    Set.Subset.antisymm (hBmax.2 ⟨hC, huC, hCne⟩ hBC) hBC
  refine ⟨{C : Set Ω | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B}, B, ?_,
    ⟨1, one_mem _, by simp⟩, huB, hBne⟩
  have hcovers : ⋃₀ {C : Set Ω | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B} = Set.univ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨σ, hσ, hσu⟩ := htrans x
    exact ⟨(σ : Equiv.Perm Ω) '' B, ⟨σ, hσ, rfl⟩, ⟨u, huB, hσu⟩⟩
  refine ⟨⟨(fun σ _ => by rw [Set.image_univ, Equiv.range_eq_univ]), ?_, ?_, hcovers,
      ?_, ⟨B, ⟨1, one_mem _, by simp⟩⟩, ?_⟩,
    ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    exact hBblock.1.image _
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩ hne
    rcases blockImage_eq_or_disjoint hBblock hσ hτ with h | h
    · exact absurd h hne
    · exact h
  · rintro σ hσ _ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, image_image_eq_mul_image _ _ _⟩
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    refine ⟨τ * σ⁻¹, mul_mem hτ (inv_mem hσ), ?_⟩
    rw [image_image_eq_mul_image]
    congr 1
    group
  · obtain ⟨x, hx⟩ : ∃ x : Ω, x ∉ B := by
      by_contra hcon
      exact hBne (Set.eq_univ_iff_forall.2 (by simpa using hcon))
    obtain ⟨σ, hσ, hσu⟩ := htrans x
    have hxmem : x ∈ (σ : Equiv.Perm Ω) '' B := ⟨u, huB, hσu⟩
    refine (Set.one_lt_ncard (Set.toFinite _)).2
      ⟨B, ⟨1, one_mem _, by simp⟩, (σ : Equiv.Perm Ω) '' B, ⟨σ, hσ, rfl⟩, fun h => ?_⟩
    exact hx (h ▸ hxmem)
  · rintro _ ⟨σ, hσ, rfl⟩ C - hsub hC
    have hCpre : IsBlockOfImprimitivity G ((σ⁻¹ : Equiv.Perm Ω) '' C) :=
      blockImage_isBlockOfImprimitivity hC (inv_mem hσ)
    have hBsub : B ⊆ (σ⁻¹ : Equiv.Perm Ω) '' C := by
      intro z hz
      exact ⟨(σ : Equiv.Perm Ω) z, hsub ⟨z, hz, rfl⟩, by simp⟩
    have huC : u ∈ (σ⁻¹ : Equiv.Perm Ω) '' C := hBsub huB
    by_cases hCuniv : (σ⁻¹ : Equiv.Perm Ω) '' C = Set.univ
    · right
      have himg : (σ : Equiv.Perm Ω) '' ((σ⁻¹ : Equiv.Perm Ω) '' C) = C := by
        rw [image_image_eq_mul_image]; simp
      rw [hCuniv] at himg
      rw [← himg, Set.image_univ, Equiv.range_eq_univ]
    · left
      have heq := hBmaximal _ hCpre huC hCuniv hBsub
      have himg : (σ : Equiv.Perm Ω) '' ((σ⁻¹ : Equiv.Perm Ω) '' C) = C := by
        rw [image_image_eq_mul_image]; simp
      rw [heq] at himg
      exact himg.symm

/-! ### The action on a system of maximal blocks is primitive -/

/-- §10.3, proof of Lemma 10.3.1: "This is a system of imprimitivity on which `G` acts as a
primitive group."

Proof: a block of imprimitivity `𝒞 ⊆ ℬ` for `G^ℬ` has union `⋃₀ 𝒞` a block of
imprimitivity for `G` containing any `B₀ ∈ 𝒞`, so by the maximality of the blocks of `ℬ`
either `⋃₀ 𝒞 = B₀`, and then `𝒞 = {B₀}`, or `⋃₀ 𝒞 = Ω`, and then `𝒞 = ℬ`.  The group
`G^ℬ` has order at least `2` because `G` is transitive on the at least two blocks. -/
theorem isPrimitive_onBlocks {G : Subgroup (Equiv.Perm Ω)} {ℬ : Set (Set Ω)}
    (hℬ : IsMinimalSystemOfImprimitivity G Set.univ ℬ) :
    IsPrimitive (onBlocks G ℬ hℬ.permutes) := by
  classical
  constructor
  · -- `|G^ℬ| ≥ 2`
    obtain ⟨B₁, hB₁, B₂, hB₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hℬ.two_blocks
    obtain ⟨σ, hσ, hσB⟩ := hℬ.transitiveOnBlocks B₁ hB₁ B₂ hB₂
    have hnot1 : blockHom G ℬ hℬ.permutes ⟨σ, hσ⟩ ≠ 1 := by
      intro h
      have := congrArg (fun p : Equiv.Perm ℬ => ((p ⟨B₁, hB₁⟩ : ℬ) : Set Ω)) h
      simp only [blockHom_apply_coe, Equiv.Perm.coe_one, id_eq] at this
      exact hne (this.symm.trans hσB)
    have hnt : Nontrivial ↥(onBlocks G ℬ hℬ.permutes) := by
      refine ⟨⟨⟨blockHom G ℬ hℬ.permutes ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩⟩, 1, ?_⟩⟩
      intro h
      exact hnot1 (congrArg Subtype.val h)
    exact Finite.one_lt_card_iff_nontrivial.2 hnt
  · -- every block of `G^ℬ` is trivial
    intro 𝒞 h𝒞
    obtain ⟨⟨b₀, hb₀⟩, hblock⟩ := h𝒞
    set S : Set Ω := ⋃₀ ((fun b : ℬ => (b : Set Ω)) '' 𝒞) with hS
    -- the union of the blocks in `𝒞` is a block of imprimitivity for `G`
    have hUimage : ∀ σ : Equiv.Perm Ω, ∀ hσ : σ ∈ G,
        (σ : Equiv.Perm Ω) '' S
          = ⋃₀ ((fun b : ℬ => (b : Set Ω)) ''
              ((blockHom G ℬ hℬ.permutes ⟨σ, hσ⟩ : Equiv.Perm ℬ) '' 𝒞)) := by
      intro σ hσ
      ext y
      constructor
      · rintro ⟨z, ⟨_, ⟨b, hb, rfl⟩, hzb⟩, rfl⟩
        exact ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, by
          show σ z ∈ (σ : Equiv.Perm Ω) '' (b : Set Ω)
          exact ⟨z, hzb, rfl⟩⟩
      · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, hy⟩
        have hy' : y ∈ (σ : Equiv.Perm Ω) '' (b : Set Ω) := hy
        obtain ⟨z, hzb, rfl⟩ := hy'
        exact ⟨z, ⟨_, ⟨b, hb, rfl⟩, hzb⟩, rfl⟩
    have hSblock : IsBlockOfImprimitivity G S := by
      refine ⟨?_, fun σ hσ => ?_⟩
      · obtain ⟨y, hy⟩ := hℬ.nonempty (b₀ : Set Ω) b₀.2
        exact ⟨y, ⟨_, ⟨b₀, hb₀, rfl⟩, hy⟩⟩
      · rcases hblock _ ⟨⟨σ, hσ⟩, rfl⟩ with h | h
        · left
          rw [hUimage σ hσ]
          congr 1
          exact congrArg _ h
        · right
          rw [hUimage σ hσ]
          ext y
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          rintro ⟨_, ⟨b, hb, rfl⟩, hyb⟩ ⟨_, ⟨b', hb', rfl⟩, hyb'⟩
          have hbb' : (b : Set Ω) = (b' : Set Ω) := by
            by_contra hne
            have := hℬ.pairwiseDisjoint _ b.2 _ b'.2 hne
            exact Set.disjoint_left.1 this hyb hyb'
          have : b = b' := Subtype.ext hbb'
          have hmem : b' ∈ ((blockHom G ℬ hℬ.permutes ⟨σ, hσ⟩ : Equiv.Perm ℬ) '' 𝒞) ∩ 𝒞 :=
            ⟨this ▸ hb, hb'⟩
          rw [h] at hmem
          exact hmem
    -- maximality of the blocks of `ℬ`
    have hb₀S : (b₀ : Set Ω) ⊆ S := fun y hy => ⟨_, ⟨b₀, hb₀, rfl⟩, hy⟩
    rcases hℬ.blocks_maximal (b₀ : Set Ω) b₀.2 S (Set.subset_univ _) hb₀S hSblock with
      heq | heq
    · -- `𝒞 = {b₀}`
      right
      refine ⟨b₀, Set.Subset.antisymm (fun b hb => ?_) ?_⟩
      · refine Set.mem_singleton_iff.2 (Subtype.ext (Set.Subset.antisymm ?_ ?_))
        · intro y hy
          rw [← heq]
          exact ⟨_, ⟨b, hb, rfl⟩, hy⟩
        · intro y hy
          obtain ⟨z, hz⟩ := hℬ.nonempty (b : Set Ω) b.2
          have hzS : z ∈ S := ⟨_, ⟨b, hb, rfl⟩, hz⟩
          rw [heq] at hzS
          have : (b : Set Ω) = (b₀ : Set Ω) := by
            by_contra hne
            exact Set.disjoint_left.1 (hℬ.pairwiseDisjoint _ b.2 _ b₀.2 hne) hz hzS
          rw [← this] at hy
          exact hy
      · intro b hb
        rw [Set.mem_singleton_iff] at hb
        exact hb ▸ hb₀
    · -- `𝒞 = ℬ`
      left
      refine Set.eq_univ_of_forall fun b => ?_
      obtain ⟨y, hy⟩ := hℬ.nonempty (b : Set Ω) b.2
      have hyS : y ∈ S := by rw [heq]; trivial
      obtain ⟨_, ⟨b', hb', rfl⟩, hyb'⟩ := hyS
      have hbb' : (b : Set Ω) = (b' : Set Ω) := by
        by_contra hne
        exact Set.disjoint_left.1 (hℬ.pairwiseDisjoint _ b.2 _ b'.2 hne) hy hyb'
      exact (Subtype.ext hbb' : b = b') ▸ hb'

end Babai
