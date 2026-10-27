import Workspace.Algo.SplitBipGraphStep8Names

/-! The computed constituent is the paper's step-8 graph. Its adjacency
comes from the selected link color. Vertex colors and hints are inherited
along the inclusion of the restricted point set. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)
    (z : RawSbipGraph × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)
include h hnd he hp hr ha hb hl hd

theorem sbipGraphConstituent_vertex (A : (step8Obj X).Vtx) :
    sbipGraphVertexColor (sbipGraphConstituent z,sbipGraphStep8Name X name A) =
      (step8Obj X).initVtxColor A.val := by
  have hleft : sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.1 ↔
      name (sbipGraphStep8OldVertex X A) ∈ z.1.1.1 :=
    (sbipGraphStep8Name_left X name z h hnd e he hp hr ha hb hl hd A).trans
      ((sbipGraphStep8OldVertex_point X A).symm.trans
        (sbipGraphName_left X name z h hp (sbipGraphStep8OldVertex X A)).symm)
  have hright : sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.2 ↔
      name (sbipGraphStep8OldVertex X A) ∈ z.1.1.2.1 :=
    (sbipGraphStep8Name_right X name z h hnd e he hp hr ha hb hl hd A).trans
      (sbipGraphName_right X name z h hr (sbipGraphStep8OldVertex X A)).symm
  rw [initVtxColor_step8Obj X A.property]
  change _ = X.obj.1.1.initVtxColor (sbipGraphStep8OldVertex X A).val
  rw [← h.vertex (sbipGraphStep8OldVertex X A)]
  change (if decide (sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.1) then _
    else if decide (sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.2) then _ else _) = _
  simp only [sbipGraphVertexColor,hleft,hright]
  rfl

theorem sbipGraphRetainedLink_pair (A B : (step8Obj X).Vtx) :
    binColor ((sbipGraphRetainedLink z).1,
      (sbipGraphStep8Name X name A,sbipGraphStep8Name X name B)) =
      VColBipBlk.wlCaseColor X.obj.1.1
        (VColBipBlk.incl (step7Set_subset X) '' A.val)
        (VColBipBlk.incl (step7Set_subset X) '' B.val) := by
  have hh := sbipGraphRefine_spec X.obj.1.1 z.1 name h hnd e he
    (sbipGraphStep8OldVertex X A) (sbipGraphStep8OldVertex X B)
  rw [VColBipBlk.wlCaseColor,dif_pos
    ⟨(sbipGraphStep8OldVertex X A).property,(sbipGraphStep8OldVertex X B).property⟩]
  exact hh

theorem sbipGraphConstituent_initEdge (A B : (step8Obj X).Vtx) :
    sbipGraphEdge (sbipGraphConstituent z,
      (sbipGraphStep8Name X name A,sbipGraphStep8Name X name B)) =
      (step8Obj X).initEdge A.val B.val := by
  have hnd' := List.nodup_append.1 (sbipGraphRetainedLink_nodup X name z h hnd e he hp hr ha hb hl hd)
  rw [sbipGraphConstituent_edge z hnd'.1 hnd'.2.1]
  have hs := (sbipGraphLinkInput_selected X z name h hnd e he hp hr ha hb hl hd).2
  have ht : sbipStep8EdgeTest (sbipGraphRetainedLink z,
      (sbipGraphStep8Name X name A,sbipGraphStep8Name X name B)) = true ↔
      ∃ x, (step8Obj X).part₁ x ∧ A.val = {x} ∧ (x,B.val) ∈ (step8Obj X).E := by
    simp only [sbipStep8EdgeTest,Bool.and_eq_true,decide_eq_true_eq,
      sbipGraphStep8Name_left X name z h hnd e he hp hr ha hb hl hd,
      sbipGraphStep8Name_right X name z h hnd e he hp hr ha hb hl hd,
      sbipGraphRetainedLink_pair X name z h hnd e he hp hr ha hb hl hd]
    change ((∃ x, (step8Obj X).part₁ x ∧ A.val = {x}) ∧ B.val ∈ (step8Obj X).blocks) ∧
      _ = sbipFirstInvolved (sbipGraphRetainedLink z) ↔ _
    rw [show sbipFirstInvolved (sbipGraphRetainedLink z) = step8Color X from hs]
    constructor
    · rintro ⟨⟨⟨x,hx,hA⟩,hB⟩,hc⟩
      refine ⟨x,hx,hA,hx,hB,?_⟩
      rwa [hA,Set.image_singleton] at hc
    · rintro ⟨x,hx,hA,hE⟩
      refine ⟨⟨⟨x,hx,hA⟩,hE.2.1⟩,?_⟩
      rw [hA,Set.image_singleton]
      exact hE.2.2
  simp only [sbipStep8Edge,VColBipBlk.initEdge,ht]
  split_ifs <;> rfl

theorem sbipGraphConstituent_names :
    SbipGraphColorNames (step8Obj X) (sbipGraphConstituent z) (sbipGraphStep8Name X name) := by
  refine ⟨sbipGraphStep8Name_injective X name h.injective,
    sbipGraphConstituent_vertex X name z h hnd e he hp hr ha hb hl hd,
    sbipGraphConstituent_initEdge X name z h hnd e he hp hr ha hb hl hd,?_⟩
  intro A B
  exact h.hint (sbipGraphStep8OldVertex X A) (sbipGraphStep8OldVertex X B)

end
end Algo
