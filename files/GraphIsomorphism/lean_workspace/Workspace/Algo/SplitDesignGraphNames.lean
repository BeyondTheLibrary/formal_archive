import Workspace.Algo.SplitDesignGraphSpec
import Workspace.Algo.SplitDesignCase3Defect

/-! The next graph keeps the old point and block names. Disjointness of
the two lists makes this a single injective naming of all its vertices. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (S : Set (Set ↥s)) (H : Set ↥s → Set ↥s → ℕ)

noncomputable def designGraphName (A : (X.linkGraph.restrictBlkHint S H).Vtx) : ℕ :=
  if hA : A.val ∈ X.blocks then name₂ ⟨A.val,hA⟩
  else name₁ ⟨(A.property.resolve_right (fun hh => hA hh.1)).choose,
    (A.property.resolve_right (fun hh => hA hh.1)).choose_spec.1⟩

theorem designGraphName_point (x : ↥X.Pt₁) :
    designGraphName (name₁ := name₁) (name₂ := name₂) S H
      ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ = name₁ x := by
  have hn : ({x.val} : Set ↥s) ∉ X.blocks := fun hh =>
    X.blocks_off₁ _ hh _ (Set.mem_singleton _) x.property
  unfold designGraphName
  rw [dif_neg hn]
  congr 1
  apply Subtype.ext
  exact (Set.singleton_injective (Exists.choose_spec
    ((Or.inl ⟨x.val,x.property,rfl⟩ : IsVertexOn X.part₁
      (X.blocks ∩ S) {x.val}).resolve_right (fun hh => hn hh.1))).2).symm

theorem designGraphName_block (B : ↥X.blocks) (hB : B.val ∈ S) :
    designGraphName (name₁ := name₁) (name₂ := name₂) S H
      ⟨B.val,Or.inr ⟨B.property,hB⟩⟩ = name₂ B := by
  simp [designGraphName,B.property]

include h hw in
theorem designGraphName_injective :
    Function.Injective (designGraphName (name₁ := name₁) (name₂ := name₂) S H) := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩ he
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rcases hB with ⟨y,hy,rfl⟩ | hB
    · rw [designGraphName_point S H ⟨x,hx⟩,designGraphName_point S H ⟨y,hy⟩] at he
      exact Subtype.ext (congrArg (fun z : ↥X.Pt₁ => ({z.val} : Set ↥s)) (h.inj₁ he))
    · rw [designGraphName_point S H ⟨x,hx⟩,designGraphName_block S H ⟨B,hB.1⟩ hB.2] at he
      exact (hw.disjoint _ ((h.left _).2 ⟨⟨x,hx⟩,rfl⟩)
        (he.symm ▸ (h.right _).2 ⟨⟨B,hB.1⟩,rfl⟩)).elim
  · rcases hB with ⟨y,hy,rfl⟩ | hB
    · rw [designGraphName_block S H ⟨A,hA.1⟩ hA.2,designGraphName_point S H ⟨y,hy⟩] at he
      exact (hw.disjoint _ ((h.left _).2 ⟨⟨y,hy⟩,rfl⟩)
        (he ▸ (h.right _).2 ⟨⟨A,hA.1⟩,rfl⟩)).elim
    · rw [designGraphName_block S H ⟨A,hA.1⟩ hA.2,designGraphName_block S H ⟨B,hB.1⟩ hB.2] at he
      exact Subtype.ext (congrArg (fun D : ↥X.blocks => D.val) (h.inj₂ he))

include h hw in
theorem designGraphName_equiv_exists (g : List ℕ) (hnd : g.Nodup)
    (hg : ∀ B : ↥X.blocks, name₂ B ∈ g ↔ B.val ∈ S)
    (hgr : ∀ a ∈ g, a ∈ r.2.2) :
    ∃ e : (X.linkGraph.restrictBlkHint S H).Vtx ≃ Fin (r.2.1 ++ g).length,
      ∀ A, (r.2.1 ++ g)[(e A).val] = designGraphName (name₁ := name₁) (name₂ := name₂) S H A := by
  apply splitNameEquiv_exists _ (designGraphName_injective h hw S H) _
    (List.nodup_append.2 ⟨hw.left_nodup,hnd,fun a ha b hb he => hw.disjoint a ha (he ▸ hgr b hb)⟩)
  intro a
  constructor
  · intro ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨x,rfl⟩ := (h.left _).1 ha
      exact ⟨⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩,designGraphName_point S H x⟩
    · obtain ⟨B,rfl⟩ := (h.right _).1 (hgr a ha)
      exact ⟨⟨B.val,Or.inr ⟨B.property,(hg B).1 ha⟩⟩,designGraphName_block S H B ((hg B).1 ha)⟩
  · rintro ⟨⟨A,hA⟩,rfl⟩
    rcases hA with ⟨x,hx,rfl⟩ | hA
    · rw [designGraphName_point S H ⟨x,hx⟩]
      exact List.mem_append_left _ ((h.left _).2 ⟨⟨x,hx⟩,rfl⟩)
    · rw [designGraphName_block S H ⟨A,hA.1⟩ hA.2]
      exact List.mem_append_right _ ((hg ⟨A,hA.1⟩).2 hA.2)

end
end Algo
