import Workspace.Algo.SplitBipVertexDictionary
import Workspace.Algo.SplitBipPackNames

/-! A stored graph keeps block rows on its persistent names. Refinement
and case dispatch number its vertices temporarily. These lemmas prove that
the actual numbered dictionary still describes the same point sets. -/
namespace Algo
open Babai RAM

structure SbipStoredDictionary {α : Type} (G : VColBipBlk α ℕ) (point : α → ℕ)
    (z : RawSbipStored) (name : G.Vtx → ℕ) : Prop where
  point_name : ∀ x hx, name ⟨{x},Or.inl ⟨x,hx,rfl⟩⟩ = point x
  block_nodup : ∀ B : ↥G.blocks, (sbipDictGet (z.2,name ⟨B.val,Or.inr B.property⟩)).Nodup
  block_mem : ∀ B : ↥G.blocks, ∀ a,
    a ∈ sbipDictGet (z.2,name ⟨B.val,Or.inr B.property⟩) ↔ ∃ x ∈ B.val, point x = a

/-- The complete storage contract returned by the graph-case adapters. -/
def SbipStoredRep {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) (point : ↥s → ℕ) (out : RawSbipStored) : Prop :=
  ∃ name : G.Vtx → ℕ,
    SbipGraphColorNames G out.1 name ∧ SbipStoredDictionary G point out name ∧
    (∀ x, labAt out.1.2.1 (point x) = G.f x) ∧ (sbipGraphVertices out.1).Nodup ∧
    (∀ A, name A ∈ out.1.1.1 ↔ ∃ x, G.part₁ x ∧ A.val = {x}) ∧
    (∀ A, name A ∈ out.1.1.2.1 ↔ A.val ∈ G.blocks) ∧
    (∀ a, a ∈ sbipGraphVertices out.1 ↔ ∃ A, name A = a)

section
variable {α : Type} {G : VColBipBlk α ℕ} {point : α → ℕ}
    {z : RawSbipStored} {name : G.Vtx → ℕ}
    (h : SbipStoredDictionary G point z name)
    (hl : ∀ A, name A ∈ z.1.1.1 ↔ ∃ x, G.part₁ x ∧ A.val = {x})
include h hl

theorem sbipVertexMembers_spec (A : G.Vtx) :
    (sbipVertexMembers (z,name A)).Nodup ∧
      ∀ a, a ∈ sbipVertexMembers (z,name A) ↔ ∃ x ∈ A.val, point x = a := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · have hm := (hl ⟨{x},Or.inl ⟨x,hx,rfl⟩⟩).2 ⟨x,hx,rfl⟩
    rw [sbipVertexMembers_point z hm,h.point_name x hx]
    exact ⟨List.nodup_singleton _,fun a => by simp [eq_comm]⟩
  · have hm : name ⟨A,Or.inr hA⟩ ∉ z.1.1.1 := by
      intro hh
      obtain ⟨x,hx,rfl⟩ := (hl ⟨A,Or.inr hA⟩).1 hh
      exact G.blocks_off₁ _ hA x rfl hx
    rw [sbipVertexMembers_block z hm]
    exact ⟨h.block_nodup ⟨A,hA⟩,h.block_mem ⟨A,hA⟩⟩

theorem sbipNumberedDictionary_spec
    (e : G.Vtx ≃ Fin (sbipNumberedDictionary z).length)
    (he : ∀ A, (sbipGraphCaseVertices z.1)[(e A).val]'(by simpa using (e A).isLt) = name A) :
    SbipVertexDictionary {A | IsVertexOn G.part₁ G.blocks A} point (sbipNumberedDictionary z) e := by
  have hr (A : G.Vtx) : (sbipNumberedDictionary z)[(e A).val] = sbipVertexMembers (z,name A) := by
    rw [← sbipDictGet_get (sbipNumberedDictionary z) (e A)]
    have hh := sbipNumberedDictionary_get z ⟨(e A).val,by simpa using (e A).isLt⟩
    simpa only [he A] using hh
  refine ⟨fun A => ?_,fun A a => ?_⟩
  · exact (congrArg List.Nodup (hr A)).mpr (sbipVertexMembers_spec h hl A).1
  · exact (congrArg (fun l : List ℕ => a ∈ l) (hr A)).to_iff.trans
      ((sbipVertexMembers_spec h hl A).2 a)

end

theorem sbipPack_storedDictionary {α : Type} (G : VColBipBlk α ℕ) (point : α → ℕ)
    (z : RawSbipPack) (eB : ↥G.blocks ≃ Fin z.2.1.length)
    (hnd : ∀ B, (z.2.1[(eB B).val]).Nodup)
    (hm : ∀ B a, a ∈ z.2.1[(eB B).val] ↔ ∃ x ∈ B.val, point x = a) :
    SbipStoredDictionary G point (sbipPack z) (sbipPackName G point z.1.1.length eB) := by
  have hr (B : ↥G.blocks) : sbipDictGet ((sbipPack z).2,
      sbipPackName G point z.1.1.length eB ⟨B.val,Or.inr B.property⟩) = z.2.1[(eB B).val] := by
    rw [sbipPackName_block,sbipPack_dict]
    exact sbipDictGet_get _ (eB B)
  refine ⟨sbipPackName_point G point z.1.1.length eB,?_,?_⟩
  · intro B; rw [hr]; exact hnd B
  · intro B a; rw [hr]; exact hm B a

end Algo
