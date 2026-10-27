/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.3, Procedure Reduce-to-Johnson, steps 6 and 7: after the Luks descent to
`G₁ = ψ⁻¹(N̄)` the pair `(G₁, ℬ₁)` is a Johnson case.
-/
import Workspace.Master.Sec15
import Workspace.Luks.JohnsonBarrier

/-!
# The Johnson case after the Luks descent (§11.3, steps 6–7)

> 6. else (: `Ḡ` a Cameron group of order `≥ m^{1+log₂ m}` :) reduce `Ḡ` to a Johnson group
>    via Luks descent (: Theorem 11.2.1, multiplicative cost `≤ m` :)
> 7. (: `Ḡ` a Johnson group :) return `Ω, G, ℬ, Ḡ`, `x, y`

Theorem 11.2.1 is applied to the primitive group `Ḡ = G^ℬ` acting on the block system `ℬ`
found at step 4.  It returns a normal subgroup `N̄ ⊴ Ḡ` of index at most `m = |ℬ|` together
with a system `𝒞` of imprimitivity of `N̄` — a partition of `ℬ` — on which `N̄` acts as the
Johnson group `A_k^{(t)}`.

Step 6 replaces `G` by `G₁ = ψ⁻¹(N̄)`, where `ψ : G → S(ℬ)` is the action on the blocks.
What this file proves is the comment of step 7 for `G₁`: **the unions `⋃ C`, for `C ∈ 𝒞`,
form a system of imprimitivity of `G₁`, and `G₁` acts on it as the same Johnson group**
(`Babai.isJohnsonCase_preimSubgroup`).  The map `C ↦ ⋃ C` is a bijection from `𝒞` onto that
block system, and it commutes with the two actions, because `ψ(g)` sends a block `B` to
`g(B)`.

Transitivity of `G₁` is a *hypothesis* of that theorem, and it is not automatic: see
the corrected paper (Sec. 11.3, steps 6–7).  The branch of `Workspace/Master/Line1.lean` splits
on it, and uses the Chain Rule over the orbits of `G₁` when it fails.
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm


/-! ### The union of a set of blocks -/

section BlockUnion

variable {α : Type u} {ℬ : Set (Set α)}

/-- `⋃ C`: the set of points covered by a set `C` of blocks. -/
def blockUnion (C : Set ℬ) : Set α := ⋃ B ∈ C, (B : Set α)

theorem mem_blockUnion {C : Set ℬ} {a : α} :
    a ∈ blockUnion C ↔ ∃ B ∈ C, a ∈ (B : Set α) := by
  simp [blockUnion]

/-- Two blocks of a partition that share a point are equal. -/
theorem eq_of_mem_blocks {G : Subgroup (Equiv.Perm α)} {Δ : Set α}
    (h : IsSystemOfImprimitivity G Δ ℬ) {B B' : ℬ} {a : α}
    (ha : a ∈ (B : Set α)) (ha' : a ∈ (B' : Set α)) : B = B' := by
  refine Subtype.ext ?_
  by_contra hne
  exact (Set.disjoint_left.1 (h.pairwiseDisjoint _ B.2 _ B'.2 hne)) ha ha'

/-- The image of `⋃ C` under `σ` is the union of the images of the blocks of `C`. -/
theorem image_blockUnion (σ : Equiv.Perm α) (C : Set ℬ) :
    σ '' blockUnion C = ⋃ B ∈ C, σ '' (B : Set α) := by
  rw [blockUnion, Set.image_iUnion₂]

end BlockUnion

/-! ### §11.3, steps 6–7: the Johnson case of `G₁ = ψ⁻¹(N̄)` -/

section Descent

variable {α : Type u} {G : Subgroup (Equiv.Perm α)} {ℬ : Set (Set α)}
  {𝒞 : Set (Set ℬ)} {N : Subgroup (Equiv.Perm ℬ)}

/-- The blocks of `G₁` after the Luks descent: the unions of the blocks of `𝒞`. -/
def descentBlocks (𝒞 : Set (Set ℬ)) : Set (Set α) := blockUnion '' 𝒞

variable (hsys : IsSystemOfImprimitivity G Set.univ ℬ)

/-- The action `ψ` of `G` on the blocks sends a block to its image, so it sends `⋃ C` to
`g(⋃ C)`. -/
theorem blockUnion_image_blockPerm {g : Equiv.Perm α} (hg : g ∈ G) (C : Set ℬ) :
    blockUnion ((blockHom G ℬ hsys.permutes ⟨g, hg⟩ : Equiv.Perm ℬ) '' C) =
      g '' blockUnion C := by
  have hB : ∀ B : ℬ, ((blockHom G ℬ hsys.permutes ⟨g, hg⟩ B : ℬ) : Set α) =
      g '' (B : Set α) := fun B => blockHom_apply_coe G ℬ hsys.permutes ⟨g, hg⟩ B
  rw [image_blockUnion]
  ext a
  simp only [mem_blockUnion, Set.mem_iUnion, exists_prop, Set.mem_image]
  constructor
  · rintro ⟨B', ⟨B, hBC, rfl⟩, ha⟩
    exact ⟨B, hBC, by rw [hB B] at ha; exact ha⟩
  · rintro ⟨B, hBC, ha⟩
    exact ⟨_, ⟨B, hBC, rfl⟩, by rw [hB B]; exact ha⟩

variable (hN : N ≤ onBlocks G ℬ hsys.permutes)
  (h𝒞 : IsSystemOfImprimitivity N Set.univ 𝒞)

include hsys hN h𝒞

omit h𝒞 in
/-- Every element of `N̄` is induced by an element of `G₁ = ψ⁻¹(N̄)`. -/
theorem exists_mem_preimSubgroup {ν : Equiv.Perm ℬ} (hν : ν ∈ N) :
    ∃ (g : Equiv.Perm α) (hg : g ∈ preimSubgroup (blockHom G ℬ hsys.permutes) N),
      blockHom G ℬ hsys.permutes
        ⟨g, preimSubgroup_le _ _ hg⟩ = ν := by
  obtain ⟨⟨g, hg⟩, hgν⟩ := MonoidHom.mem_range.1 (hN hν)
  exact ⟨g, mem_preimSubgroup.2 ⟨hg, by rw [hgν]; exact hν⟩, hgν⟩

/-- §11.3, step 7: the unions `⋃ C`, `C ∈ 𝒞`, form a system of imprimitivity of
`G₁ = ψ⁻¹(N̄)`.  (`G₁` acts transitively on these blocks because `N̄` acts transitively on
`𝒞`; transitivity of `G₁` on the points is a separate matter, see the module docstring.) -/
theorem isSystemOfImprimitivity_descentBlocks :
    IsSystemOfImprimitivity (preimSubgroup (blockHom G ℬ hsys.permutes) N)
      Set.univ (descentBlocks 𝒞) := by
  set G₁ := preimSubgroup (blockHom G ℬ hsys.permutes) N with hG₁
  -- the image of `⋃ C` under `g ∈ G₁` is `⋃ (ψ g) C`
  have hact : ∀ (g : Equiv.Perm α) (hg : g ∈ G₁) (C : Set ℬ), C ∈ 𝒞 →
      g '' blockUnion C ∈ descentBlocks 𝒞 := by
    intro g hg C hC
    obtain ⟨hgG, hgN⟩ := mem_preimSubgroup.1 hg
    refine ⟨(blockHom G ℬ hsys.permutes ⟨g, hgG⟩ : Equiv.Perm ℬ) '' C, ?_, ?_⟩
    · exact h𝒞.permutes _ hgN C hC
    · exact blockUnion_image_blockPerm hsys hgG C
  refine ⟨fun σ _ => by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨B, hB⟩ := h𝒞.nonempty C hC
    obtain ⟨a, ha⟩ := hsys.nonempty (B : Set α) B.2
    exact ⟨a, mem_blockUnion.2 ⟨B, hB, ha⟩⟩
  · -- pairwise disjoint
    rintro _ ⟨C, hC, rfl⟩ _ ⟨C', hC', rfl⟩ hne
    have hCC' : C ≠ C' := fun h => hne (by rw [h])
    have hdisj := h𝒞.pairwiseDisjoint C hC C' hC' hCC'
    rw [Set.disjoint_left]
    rintro a ha ha'
    obtain ⟨B, hB, haB⟩ := mem_blockUnion.1 ha
    obtain ⟨B', hB', haB'⟩ := mem_blockUnion.1 ha'
    have : B = B' := eq_of_mem_blocks hsys haB haB'
    subst this
    exact (Set.disjoint_left.1 hdisj) hB hB'
  · -- covers
    ext a
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have haB : a ∈ ⋃₀ ℬ := by rw [hsys.covers]; trivial
    obtain ⟨B, hB, haB⟩ := haB
    have hBC : (⟨B, hB⟩ : ℬ) ∈ ⋃₀ 𝒞 := by rw [h𝒞.covers]; trivial
    obtain ⟨C, hC, hBC⟩ := hBC
    exact ⟨blockUnion C, ⟨C, hC, rfl⟩, mem_blockUnion.2 ⟨⟨B, hB⟩, hBC, haB⟩⟩
  · -- permutes
    rintro σ hσ _ ⟨C, hC, rfl⟩
    exact hact σ hσ C hC
  · -- there is at least one block
    obtain ⟨C, hC⟩ := h𝒞.blocks_nonempty
    exact ⟨blockUnion C, C, hC, rfl⟩
  · -- transitive on the blocks
    rintro _ ⟨C, hC, rfl⟩ _ ⟨C', hC', rfl⟩
    obtain ⟨ν, hν, hνC⟩ := h𝒞.transitiveOnBlocks C hC C' hC'
    obtain ⟨g, hg, hgν⟩ := exists_mem_preimSubgroup hsys hN hν
    refine ⟨g, hg, ?_⟩
    rw [← blockUnion_image_blockPerm hsys (preimSubgroup_le _ _ hg) C, hgν, hνC]

omit hN in
/-- The map `C ↦ ⋃ C` is injective on `𝒞`: a block of `ℬ` in `C` is nonempty, and the
blocks of `ℬ` are pairwise disjoint, so a point of `⋃ C` determines the block of `ℬ` it
lies in, and that block lies in `C`. -/
theorem blockUnion_injOn : Set.InjOn (blockUnion (ℬ := ℬ)) 𝒞 := by
  intro C hC C' hC' heq
  by_contra hne
  obtain ⟨B, hB⟩ := h𝒞.nonempty C hC
  obtain ⟨a, ha⟩ := hsys.nonempty (B : Set α) B.2
  have haC : a ∈ blockUnion C := mem_blockUnion.2 ⟨B, hB, ha⟩
  rw [heq] at haC
  obtain ⟨B', hB', ha'⟩ := mem_blockUnion.1 haC
  have : B = B' := eq_of_mem_blocks hsys ha ha'
  subst this
  exact (Set.disjoint_left.1 (h𝒞.pairwiseDisjoint C hC C' hC' hne)) hB hB'

/-- The bijection `C ↦ ⋃ C` from `𝒞` onto the block system of `G₁ = ψ⁻¹(N̄)`. -/
noncomputable def blockUnionEquiv {ℬ : Set (Set α)} {𝒞 : Set (Set ℬ)}
    (hinj : Set.InjOn (blockUnion (ℬ := ℬ)) 𝒞) : 𝒞 ≃ descentBlocks (ℬ := ℬ) 𝒞 :=
  Equiv.ofBijective (fun C : 𝒞 => (⟨blockUnion (C : Set ℬ), ⟨(C : Set ℬ), C.2, rfl⟩⟩ :
      descentBlocks (ℬ := ℬ) 𝒞))
    ⟨fun C C' h => Subtype.ext (hinj C.2 C'.2 (congrArg Subtype.val h)),
      by rintro ⟨_, C, hC, rfl⟩; exact ⟨⟨C, hC⟩, rfl⟩⟩

omit hN h𝒞 in
@[simp] theorem blockUnionEquiv_apply {ℬ : Set (Set α)} {𝒞 : Set (Set ℬ)}
    (hinj : Set.InjOn (blockUnion (ℬ := ℬ)) 𝒞) (C : 𝒞) :
    ((blockUnionEquiv hinj C : descentBlocks (ℬ := ℬ) 𝒞) : Set α) =
      blockUnion (C : Set ℬ) := rfl

/-- The block action of `G₁` on `{⋃ C | C ∈ 𝒞}` is the block action of `N̄` on `𝒞`, read
through the bijection `C ↦ ⋃ C`.  This is the step *"the map commutes with the action"*. -/
theorem permCongr_blockHom_descentBlocks
    {g : Equiv.Perm α} (hg : g ∈ preimSubgroup (blockHom G ℬ hsys.permutes) N)
    (hν : blockHom G ℬ hsys.permutes ⟨g, preimSubgroup_le _ _ hg⟩ ∈ N) :
    (Equiv.permCongrHom (blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm).toMonoidHom
        (blockHom (preimSubgroup (blockHom G ℬ hsys.permutes) N) (descentBlocks 𝒞)
          (isSystemOfImprimitivity_descentBlocks hsys hN h𝒞).permutes ⟨g, hg⟩) =
      blockHom N 𝒞 h𝒞.permutes
        ⟨blockHom G ℬ hsys.permutes ⟨g, preimSubgroup_le _ _ hg⟩, hν⟩ := by
  have hrw : ∀ P : Equiv.Perm (descentBlocks (ℬ := ℬ) 𝒞),
      (Equiv.permCongrHom (blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm).toMonoidHom P =
        (blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm.permCongr P := fun _ => rfl
  rw [hrw]
  refine Equiv.ext fun C => ?_
  rw [Equiv.permCongr_apply, Equiv.symm_symm]
  have hstep : blockHom (preimSubgroup (blockHom G ℬ hsys.permutes) N) (descentBlocks 𝒞)
      (isSystemOfImprimitivity_descentBlocks hsys hN h𝒞).permutes ⟨g, hg⟩
        (blockUnionEquiv (blockUnion_injOn hsys h𝒞) C) =
      blockUnionEquiv (blockUnion_injOn hsys h𝒞) (blockHom N 𝒞 h𝒞.permutes
        ⟨blockHom G ℬ hsys.permutes ⟨g, preimSubgroup_le _ _ hg⟩, hν⟩ C) := by
    refine Subtype.ext ?_
    exact (blockUnion_image_blockPerm hsys
      (preimSubgroup_le (blockHom G ℬ hsys.permutes) N hg) (C : Set ℬ)).symm
  rw [hstep, Equiv.symm_apply_apply]

/-- §11.3, step 7: **`G₁ = ψ⁻¹(N̄)` acts on its blocks as `N̄` acts on `𝒞`**. -/
theorem map_onBlocks_descentBlocks :
    (onBlocks (preimSubgroup (blockHom G ℬ hsys.permutes) N) (descentBlocks 𝒞)
        (isSystemOfImprimitivity_descentBlocks hsys hN h𝒞).permutes).map
      (Equiv.permCongrHom (blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm).toMonoidHom =
      onBlocks N 𝒞 h𝒞.permutes := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    obtain ⟨hgG, hgN⟩ := mem_preimSubgroup.1 hg
    rw [permCongr_blockHom_descentBlocks hsys hN h𝒞 hg hgN]
    exact ⟨_, rfl⟩
  · rintro _ ⟨⟨ν, hν⟩, rfl⟩
    obtain ⟨g, hg, hgν⟩ := exists_mem_preimSubgroup hsys hN hν
    have hmem : blockHom G ℬ hsys.permutes ⟨g, preimSubgroup_le _ _ hg⟩ ∈ N := by
      rw [hgν]; exact hν
    refine ⟨_, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    rw [permCongr_blockHom_descentBlocks hsys hN h𝒞 hg hmem]
    exact congrArg _ (Subtype.ext hgν)

/-- §11.3, steps 6–7, **the Johnson case after the Luks descent**.

Let `G` be transitive with the system `ℬ` of imprimitivity of step 4, let `N̄ ≤ G^ℬ` be the
normal subgroup of Theorem 11.2.1 and `𝒞` its system of imprimitivity on `ℬ`, on which it
acts as the Johnson group `A_k^{(t)}`.  If `G₁ = ψ⁻¹(N̄)` is transitive, then `(G₁, {⋃ C})`
is the Johnson case with the same parameters `k, t`.

The proof is the paper's: the sets `⋃ C` are a system of imprimitivity of `G₁`
(`Babai.isSystemOfImprimitivity_descentBlocks`), the map `C ↦ ⋃ C` is a bijection
(`Babai.blockUnion_injOn`), and it commutes with the two actions
(`Babai.permCongr_blockHom_descentBlocks`), so the induced group on the new blocks is the
same Johnson group. -/
theorem actsAsJohnsonA_descentBlocks {k t : ℕ}
    (hjohn : ActsAsJohnsonA N 𝒞 h𝒞.permutes k t) :
    ActsAsJohnsonA (preimSubgroup (blockHom G ℬ hsys.permutes) N) (descentBlocks 𝒞)
      (isSystemOfImprimitivity_descentBlocks hsys hN h𝒞).permutes k t := by
  obtain ⟨e, he⟩ := hjohn
  refine ⟨(blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm.trans e, ?_⟩
  have hcomp : (Equiv.permCongrHom
      ((blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm.trans e)).toMonoidHom =
      (Equiv.permCongrHom e).toMonoidHom.comp
        (Equiv.permCongrHom (blockUnionEquiv (blockUnion_injOn hsys h𝒞)).symm).toMonoidHom := by
    ext p : 1
    exact Equiv.ext fun s => rfl
  rw [hcomp, ← Subgroup.map_map, map_onBlocks_descentBlocks hsys hN h𝒞, he]

/-- §11.3, steps 6–7: **`(G₁, {⋃ C})` is the Johnson case**, with the parameters of
Theorem 11.2.1.  Transitivity of `G₁` on the points is the one hypothesis that does not
come from Theorem 11.2.1; see the module docstring and the corrected paper. -/
theorem isJohnsonCase_preimSubgroup {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t ≤ k)
    (hjohn : ActsAsJohnsonA N 𝒞 h𝒞.permutes k t)
    (htr : IsTransitive (preimSubgroup (blockHom G ℬ hsys.permutes) N)) :
    IsJohnsonCase (preimSubgroup (blockHom G ℬ hsys.permutes) N) (descentBlocks 𝒞) k t :=
  ⟨ht, hk, htr, isSystemOfImprimitivity_descentBlocks hsys hN h𝒞,
    Or.inr (actsAsJohnsonA_descentBlocks hsys hN h𝒞 hjohn)⟩

omit hN h𝒞 in
/-- `G₁ = ψ⁻¹(N̄)` is normal in `G`, because `N̄` is normal in `Ḡ = G^ℬ`.  This is what
makes the orbits of `G₁` all of the same size (Fact 11.1.8), which is the progress of the
branch when `G₁` is intransitive. -/
theorem isNormalIn_preimSubgroup (hNnorm : IsNormalIn N (onBlocks G ℬ hsys.permutes)) :
    IsNormalIn (preimSubgroup (blockHom G ℬ hsys.permutes) N) G := by
  refine ⟨preimSubgroup_le _ _, fun σ hσ τ hτ => ?_⟩
  obtain ⟨hτG, hτN⟩ := mem_preimSubgroup.1 hτ
  have hmem : σ * τ * σ⁻¹ ∈ G := mul_mem (mul_mem hσ hτG) (inv_mem hσ)
  refine mem_preimSubgroup.2 ⟨hmem, ?_⟩
  have hsplit : (⟨σ * τ * σ⁻¹, hmem⟩ : G) = ⟨σ, hσ⟩ * ⟨τ, hτG⟩ * (⟨σ, hσ⟩)⁻¹ := rfl
  rw [hsplit, map_mul, map_mul, map_inv]
  exact hNnorm.conj_mem _ ⟨⟨σ, hσ⟩, rfl⟩ _ hτN

end Descent


/-! ### The giant representation of a group acting as a Johnson group

Line 3 of Sec. 15 asks for a giant representation `ϕ : G → S(Γ)`, `|Γ| = m`, *"inferred
from `G`"*.  In the Johnson case `G` acts on its blocks as `A_m^{(t)}`, that is, as the
image of `A(Γ)` under the action on `t`-sets, and that action is faithful for
`1 ≤ t < m` (`Babai.tAction_injective`).  So the block action, read through the
identification of the blocks with `Γ^{(t)}` and then undone by the inverse of
`π ↦ π^{(t)}`, is the representation the paper wants, and its image is exactly `A(Γ)`. -/

section JohnsonGiant

variable {β : Type u} {G : Subgroup (Equiv.Perm β)} {ℬ : Set (Set β)}
  {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm β) '' B ∈ ℬ} {k t : ℕ}

/-- The action of `G` on the blocks, read on `Γ^{(t)}` through the identification of the
blocks with the `t`-subsets of `Γ = Fin k`. -/
noncomputable def johnsonBlockRep (h : ActsAsJohnsonA G ℬ hperm k t) :
    G →* Equiv.Perm (binom (Fin k) t) :=
  (Equiv.permCongrHom h.choose).toMonoidHom.comp (blockHom G ℬ hperm)

theorem range_johnsonBlockRep (h : ActsAsJohnsonA G ℬ hperm k t) :
    (johnsonBlockRep h).range = JohnsonA k t := by
  rw [johnsonBlockRep, MonoidHom.range_comp]
  exact h.choose_spec

/-- §15, line 3: **the giant representation of a group acting as a Johnson group**. -/
noncomputable def johnsonGiantRep (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : ActsAsJohnsonA G ℬ hperm k t) : G →* Equiv.Perm (Fin k) :=
  letI hinj : Function.Injective (tAction (Ω := Fin k) t) :=
    tAction_injective ht (by rw [Fintype.card_fin]; omega)
  (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (MonoidHom.codRestrict (johnsonBlockRep h) (tAction (Ω := Fin k) t).range
      (fun g => by
        have hmem : johnsonBlockRep h g ∈ JohnsonA k t := by
          rw [← range_johnsonBlockRep h]; exact ⟨g, rfl⟩
        obtain ⟨π, -, hπ⟩ := hmem
        exact ⟨π, hπ⟩))

/-- The giant representation of the Johnson case is a giant representation: its image is
`A(Γ)`. -/
theorem isGiantRep_johnsonGiantRep (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : ActsAsJohnsonA G ℬ hperm k t) : IsGiantRep (johnsonGiantRep ht hk h) := by
  intro α hα
  have hinj : Function.Injective (tAction (Ω := Fin k) t) :=
    tAction_injective ht (by rw [Fintype.card_fin]; omega)
  have hmem : tAction t α ∈ (johnsonBlockRep h).range := by
    rw [range_johnsonBlockRep h]
    exact ⟨α, hα, rfl⟩
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, ?_⟩
  have hval : (MonoidHom.codRestrict (johnsonBlockRep h) (tAction (Ω := Fin k) t).range
      (fun g => by
        have hmem : johnsonBlockRep h g ∈ JohnsonA k t := by
          rw [← range_johnsonBlockRep h]; exact ⟨g, rfl⟩
        obtain ⟨π, -, hπ⟩ := hmem
        exact ⟨π, hπ⟩) g : (tAction (Ω := Fin k) t).range) =
      MonoidHom.ofInjective hinj α := by
    refine Subtype.ext ?_
    rw [MonoidHom.ofInjective_apply]
    exact hg
  show (MonoidHom.ofInjective hinj).symm _ = α
  rw [hval, MulEquiv.symm_apply_apply]

end JohnsonGiant

/-! ### Counting the blocks of a Johnson case

Two facts that the construction of a `Babai.JohnsonCaseData` needs: there are at least two
blocks (`two_blocks`), and the Johnson parameter is at most the window size
(`param_le`).  Both come from the count `|ℬ| = C(k,t)` and from `k ≤ C(k,t)`
(`Babai.self_le_choose`, valid for `1 ≤ t` and `2t < k`). -/

section CountBlocks

variable {β : Type u} [Fintype β] {G : Subgroup (Equiv.Perm β)} {Δ : Set β}
  {ℬ : Set (Set β)} {k t : ℕ}

/-- A system of imprimitivity has at most `|β|` blocks: the blocks are nonempty and
pairwise disjoint, so a chosen point of each block distinguishes them. -/
theorem card_blocks_le (h : IsSystemOfImprimitivity G Δ ℬ) :
    Nat.card ℬ ≤ Fintype.card β := by
  classical
  have : Finite ℬ := Set.Finite.to_subtype (Set.toFinite ℬ)
  have hinj : Function.Injective
      (fun B : ℬ => ((h.nonempty (B : Set β) B.2).choose : β)) := by
    intro B B' hBB'
    have h1 := (h.nonempty (B : Set β) B.2).choose_spec
    have h2 := (h.nonempty (B' : Set β) B'.2).choose_spec
    have hBB2 : (h.nonempty (B : Set β) B.2).choose =
        (h.nonempty (B' : Set β) B'.2).choose := hBB'
    rw [hBB2] at h1
    exact eq_of_mem_blocks h h1 h2
  have hle := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_eq_fintype_card] using hle

omit [Fintype β] in
/-- A group acting on `ℬ` as `A_k^{(t)}` has `C(k,t)` blocks. -/
theorem card_blocks_of_actsAsJohnsonA
    {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm β) '' B ∈ ℬ}
    (h : ActsAsJohnsonA G ℬ hperm k t) : Nat.card ℬ = k.choose t := by
  obtain ⟨e, -⟩ := h
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

/-- The Johnson parameter is at most the number of points: `k ≤ C(k,t) = |ℬ| ≤ |β|`. -/
theorem johnson_param_le (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : IsSystemOfImprimitivity G Δ ℬ)
    (hj : ActsAsJohnsonA G ℬ h.permutes k t) : k ≤ Fintype.card β := by
  have h1 : k ≤ Nat.card ℬ := by
    rw [card_blocks_of_actsAsJohnsonA hj]; exact self_le_choose ht hk
  exact le_trans h1 (card_blocks_le h)

/-- A Johnson case has at least two blocks: `|ℬ| = C(k,t) ≥ k ≥ 3`. -/
theorem two_blocks_of_actsAsJohnsonA (ht : 1 ≤ t) (hk : 2 * t < k)
    (h : IsSystemOfImprimitivity G Δ ℬ)
    (hj : ActsAsJohnsonA G ℬ h.permutes k t) :
    ∃ B₁ ∈ ℬ, ∃ B₂ ∈ ℬ, B₁ ≠ B₂ := by
  have : Finite ℬ := Set.Finite.to_subtype (Set.toFinite ℬ)
  have h1 : 1 < Nat.card ℬ := by
    rw [card_blocks_of_actsAsJohnsonA hj]
    have := self_le_choose ht hk
    omega
  have : Nontrivial ℬ := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨B₁, B₂, hne⟩ := exists_pair_ne ℬ
  exact ⟨(B₁ : Set β), B₁.2, (B₂ : Set β), B₂.2, fun hc => hne (Subtype.ext hc)⟩

end CountBlocks

end Babai
