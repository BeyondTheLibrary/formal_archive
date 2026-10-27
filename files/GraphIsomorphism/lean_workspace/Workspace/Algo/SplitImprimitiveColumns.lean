import Workspace.Algo.SplitImprimitiveGraph

/-! # Section 9.6: decode unions of old blocks

The contraction keeps a list of old block names in each new column. Their
unions are the paper's new vertices. Distinct stored components have distinct
unions because the old blocks are nonempty and pairwise disjoint.
-/
namespace Algo
open Babai RAM

section Columns
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s) (name₂ : ↥X.blocks → ℕ)

/-- Decode a new column through the caller's original block dictionary. -/
def impColumnSet (g : List ℕ) : Set ↥s :=
  {x | ∃ B : ↥X.blocks, name₂ B ∈ g ∧ x ∈ B.val}

theorem impColumnSet_rep (hinj : Function.Injective name₂)
    (G : Set ↥X.blocks) (g : List ℕ)
    (hg : ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a) :
    impColumnSet X name₂ g = ⋃ C ∈ G, C.val := by
  ext x
  simp only [impColumnSet,Set.mem_setOf_eq,Set.mem_iUnion,exists_prop]
  constructor
  · rintro ⟨B,hB,hx⟩
    obtain ⟨C,hC,hname⟩ := (hg _).1 hB
    have : C = B := hinj hname
    subst C
    exact ⟨B,hC,hx⟩
  · rintro ⟨B,hB,hx⟩
    exact ⟨B,(hg _).2 ⟨B,hB,rfl⟩,hx⟩

theorem impColumnSet_singleton (hinj : Function.Injective name₂) (B : ↥X.blocks) :
    impColumnSet X name₂ [name₂ B] = B.val := by
  ext x
  simp only [impColumnSet,Set.mem_setOf_eq,List.mem_singleton]
  constructor
  · rintro ⟨C,hC,hx⟩
    have : C = B := hinj hC
    subst C
    exact hx
  · intro hx; exact ⟨B,rfl,hx⟩

end Columns

section Groups
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B)
include h he

theorem impColumnSet_group (B : ↥X.blocks) :
    impColumnSet X name₂ (impGroup (r,e B)) = X.groupUnion B :=
  impColumnSet_rep X name₂ h.inj₂ (X.group B) _ (impGroup_spec h e he B)

/-- Equal mathematical components give exactly the same ordered raw list. -/
theorem impGroup_eq_of_group_eq (B C : ↥X.blocks) (hBC : X.group B = X.group C) :
    impGroup (r,e B) = impGroup (r,e C) := by
  have hm : B ∈ X.group C := by
    rw [← hBC]
    exact mem_blockOf_self _ _
  have hl : labAt (impComponents r) (e B) = labAt (impComponents r) (e C) :=
    ((impComponents_spec h e he C B).2 hm).symm
  simp only [impGroup,impGroupPositions,hl]

/-- Every contracted column names a vertex of the paper's contracted graph. -/
theorem impColumns_contraction :
    impColumnSet X name₂ '' {g | g ∈ impGroups r} = (X.blkContr).blocks := by
  ext D
  constructor
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨i,hi,rfl⟩ := (impGroups_mem _ _).1 hg
    let B := e.symm ⟨i,hi⟩
    refine ⟨B,?_⟩
    have hh := impColumnSet_group h e he B
    simpa only [B,Equiv.apply_symm_apply] using hh.symm
  · rintro ⟨B,rfl⟩
    exact ⟨impGroup (r,e B),(impGroups_mem _ _).2 ⟨e B,(e B).isLt,rfl⟩,
      impColumnSet_group h e he B⟩

/-- No two distinct stored columns contract to the same block union. -/
theorem impColumns_contraction_inj :
    Set.InjOn (impColumnSet X name₂) {g | g ∈ impGroups r} := by
  rintro g hg g' hg' heq
  obtain ⟨i,hi,rfl⟩ := (impGroups_mem _ _).1 hg
  obtain ⟨j,hj,rfl⟩ := (impGroups_mem _ _).1 hg'
  let B := e.symm ⟨i,hi⟩
  let C := e.symm ⟨j,hj⟩
  have hc : impColumnSet X name₂ (impGroup (r,e B)) =
      impColumnSet X name₂ (impGroup (r,e C)) := by
    simpa only [B,C,Equiv.apply_symm_apply] using heq
  rw [impColumnSet_group h e he,impColumnSet_group h e he] at hc
  have hh : X.grpOf B = X.grpOf C := X.grpUnion_injective hc
  have hm : X.group B = X.group C := congrArg Subtype.val hh
  have hl := impGroup_eq_of_group_eq h e he B C hm
  simpa only [B,C,Equiv.apply_symm_apply] using hl

/-- A restriction's singleton columns name exactly its old blocks. -/
theorem impColumns_restriction (G : Set ↥X.blocks) (g : List ℕ)
    (hg : ∀ a, a ∈ g ↔ ∃ C ∈ G, name₂ C = a) :
    impColumnSet X name₂ '' {l | l ∈ g.map (fun b => [b])} = (X.blkZ G).blocks := by
  ext D
  constructor
  · rintro ⟨l,hl,rfl⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hl
    obtain ⟨B,hB,rfl⟩ := (hg _).1 ha
    rw [impColumnSet_singleton X name₂ h.inj₂]
    exact ⟨B,hB,rfl⟩
  · rintro ⟨B,hB,rfl⟩
    exact ⟨[name₂ B],List.mem_map.2 ⟨name₂ B,(hg _).2 ⟨B,hB,rfl⟩,rfl⟩,
      impColumnSet_singleton X name₂ h.inj₂ B⟩

end Groups
end Algo
