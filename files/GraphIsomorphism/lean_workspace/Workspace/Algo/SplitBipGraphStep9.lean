import Workspace.Algo.SplitBipGraphStep8Read
import Workspace.Algo.SplitBipGraphNumbered
import Workspace.Algo.SplitDesignNames

/-! The graph prepared in steps 3--8 supplies the complete numbered
input of step 9. Both refinements and both selections are computed from
the original decorated graph. -/
namespace Algo
open Babai RAM
open scoped Classical

def sbipGraphStep9Input (z : RawSbipGraph × (ℕ × ℕ)) : RawUpccCase :=
  sbipGraphNumbered (sbipGraphConstituent z)

theorem polyFun_sbipGraphStep9Input : PolyFun sbipGraphStep9Input :=
  polyFun_sbipGraphConstituent.comp polyFun_sbipGraphNumbered

theorem sbipGraphStep9Input_wf (z : RawSbipGraph × (ℕ × ℕ)) : (sbipGraphStep9Input z).WF :=
  sbipGraphNumbered_wf _

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

theorem sbipGraphStep9Vertices_nodup :
    (sbipGraphCaseVertices (sbipGraphConstituent z)).Nodup :=
  List.nodup_append_comm.1 (sbipGraphRetainedLink_nodup X name z h hnd e he hp hr ha hb hl hd)

theorem sbipGraphStep9_equiv_exists :
    ∃ e9 : (step8Obj X).Vtx ≃ Fin (sbipGraphCaseVertices (sbipGraphConstituent z)).length,
      ∀ A, (sbipGraphCaseVertices (sbipGraphConstituent z))[(e9 A).val]'(e9 A).isLt =
        sbipGraphStep8Name X name A := by
  obtain ⟨e8,he8⟩ := sbipGraphStep8Name_equiv_exists X name z h hnd e he hp hr ha hb hl hd
  apply splitNameEquiv_exists _ (sbipGraphStep8Name_injective X name h.injective) _
    (sbipGraphStep9Vertices_nodup X name z h hnd e he hp hr ha hb hl hd)
  intro a
  have hm : a ∈ sbipGraphCaseVertices (sbipGraphConstituent z) ↔
      a ∈ (sbipGraphRetainedLink z).2.1 ++ (sbipGraphRetainedLink z).2.2 := by
    change a ∈ (sbipGraphRetainedLink z).2.2 ++ (sbipGraphRetainedLink z).2.1 ↔ _
    simp only [List.mem_append,or_comm]
  rw [hm]
  constructor
  · intro ha'
    obtain ⟨i,hi,hia⟩ := List.getElem_of_mem ha'
    exact ⟨e8.symm ⟨i,hi⟩,(he8 (e8.symm ⟨i,hi⟩)).symm.trans
      (by simpa only [Equiv.apply_symm_apply] using hia)⟩
  · rintro ⟨A,rfl⟩
    exact he8 A ▸ List.getElem_mem (e8 A).isLt

variable
    (e9 : (step8Obj X).Vtx ≃ Fin (sbipGraphCaseVertices (sbipGraphConstituent z)).length)
    (he9 : ∀ A, (sbipGraphCaseVertices (sbipGraphConstituent z))[(e9 A).val]'(e9 A).isLt =
      sbipGraphStep8Name X name A)
include he9

theorem sbipGraphStep9Input_color (A B : (step8Obj X).Vtx) :
    binColor ((sbipGraphStep9Input z).1,(e9 A,e9 B)) = step8CaseColor X A.val B.val := by
  rw [step8CaseColor_vtx]
  change binColor (sbipGraphCaseTable (sbipGraphConstituent z),(e9 A,e9 B)) =
    ((step8Obj X).wlConfig).natColor A B
  rw [VColBipBlk.natColor_wlConfig,VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
  exact sbipGraphCaseTable_spec (step8Obj X) (sbipGraphConstituent z) (sbipGraphStep8Name X name)
    (sbipGraphConstituent_names X name z h hnd e he hp hr ha hb hl hd) e9 he9 A B

theorem sbipGraphStep9Input_left_names :
    sbipGraphNumberedPoint (step8Obj X) (sbipGraphConstituent z) e9 '' Set.univ =
      {a | a ∈ (sbipGraphStep9Input z).2.1} :=
  sbipGraphNumbered_left_names (step8Obj X) (sbipGraphConstituent z)
    (sbipGraphStep8Name X name) e9 he9
    (sbipGraphStep9Vertices_nodup X name z h hnd e he hp hr ha hb hl hd)
    (sbipGraphStep8Name_left X name z h hnd e he hp hr ha hb hl hd)

theorem sbipGraphStep9Input_right_names :
    sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent z) e9 '' Set.univ =
      {a | a ∈ (sbipGraphStep9Input z).2.2} :=
  sbipGraphNumbered_right_names (step8Obj X) (sbipGraphConstituent z)
    (sbipGraphStep8Name X name) e9 he9
    (sbipGraphStep9Vertices_nodup X name z h hnd e he hp hr ha hb hl hd)
    (sbipGraphStep8Name_right X name z h hnd e he hp hr ha hb hl hd)

theorem sbipGraphStep9Input_case :
    (sbipStep9Case (sbipGraphStep9Input z) = 0 ↔ Step9Imprimitive X) ∧
    (sbipStep9Case (sbipGraphStep9Input z) = 1 ↔ ¬ Step9Imprimitive X ∧ Step9Clique X) ∧
    (sbipStep9Case (sbipGraphStep9Input z) = 2 ↔ ¬ Step9Imprimitive X ∧ ¬ Step9Clique X) := by
  let g := sbipGraphConstituent z
  have hgd := sbipGraphStep9Vertices_nodup X name z h hnd e he hp hr ha hb hl hd
  have hpos (A : (step8Obj X).Vtx) : (e9 A).val < g.1.2.1.length ↔
      A.val ∈ (step8Obj X).blocks := by
    rw [← sbipPrefix_mem _ _ hgd (e9 A)]
    change (sbipGraphCaseVertices (sbipGraphConstituent z))[(e9 A).val]'(e9 A).isLt ∈ g.1.2.1 ↔ _
    rw [he9 A]
    exact sbipGraphStep8Name_right X name z h hnd e he hp hr ha hb hl hd A
  let eb : ↥(step8Blks X) ≃ Fin g.1.2.1.length := {
    toFun := fun B => ⟨e9 B.val,(hpos B.val).2 B.property⟩
    invFun := fun i => ⟨e9.symm ⟨i.val,by
      change i.val < (g.1.2.1 ++ g.1.1).length
      simp only [List.length_append]
      omega⟩,(hpos _).1 (by simpa using i.isLt)⟩
    left_inv := fun B => Subtype.ext (e9.symm_apply_apply B.val)
    right_inv := by
      intro i
      apply Fin.ext
      change (e9 (e9.symm ⟨i.val,by
        change i.val < (g.1.2.1 ++ g.1.1).length
        simp only [List.length_append]
        omega⟩)).val = i.val
      simp only [Equiv.apply_symm_apply] }
  let eb' : ↥(step8Blks X) ≃ Fin (sbipGraphStep9Input z).2.2.length :=
    eb.trans (finCongr (by simp [sbipGraphStep9Input,sbipGraphNumbered,g]))
  apply sbipStep9Case_spec X (sbipGraphStep9Input z) eb'
  intro u v
  simp only [sbipGraphStep9Input,sbipGraphNumbered,List.getElem_range]
  change binColor ((sbipGraphStep9Input z).1,(e9 u.val,e9 v.val)) = _
  exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9 u.val v.val

theorem sbipGraphStep9Input_upccNames
    (h6 : ¬ Step6Imprimitive X) (hi : ¬ Step9Imprimitive X) (hc : ¬ Step9Clique X) :
    UpccCaseNames (step9UPCCObj X hd h6 hi hc) e9 (sbipGraphStep9Input z) := by
  refine ⟨sbipGraphCaseTable_length _,?_,?_,?_⟩
  · exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
  · exact sbipGraphStep9Input_left_names X name z h hnd e he hp hr ha hb hl hd e9 he9
  · exact sbipGraphStep9Input_right_names X name z h hnd e he hp hr ha hb hl hd e9 he9

theorem sbipGraphStep9Input_point_cover (a : ℕ) :
    a ∈ (sbipGraphStep9Input z).2.1 ↔
      ∃ x, sbipGraphNumberedPoint (step8Obj X) (sbipGraphConstituent z) e9 x = a := by
  change a ∈ {a | a ∈ (sbipGraphStep9Input z).2.1} ↔ _
  rw [← sbipGraphStep9Input_left_names X name z h hnd e he hp hr ha hb hl hd e9 he9]
  simp

theorem sbipGraphStep9Input_block_cover (a : ℕ) :
    a ∈ (sbipGraphStep9Input z).2.2 ↔
      ∃ B, sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent z) e9 B = a := by
  change a ∈ {a | a ∈ (sbipGraphStep9Input z).2.2} ↔ _
  rw [← sbipGraphStep9Input_right_names X name z h hnd e he hp hr ha hb hl hd e9 he9]
  simp

theorem sbipGraphStep9Input_impNames (h6 : ¬ Step6Imprimitive X) (hi : Step9Imprimitive X) :
    ImpNames (step9ImpObj X hd h6 hi)
      (sbipGraphNumberedPoint (step8Obj X) (sbipGraphConstituent z) e9)
      (sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent z) e9) (sbipGraphStep9Input z) := by
  refine ⟨sbipGraphNumberedPoint_injective _ _ _,sbipGraphNumberedBlock_injective _ _ _,
    sbipGraphStep9Input_point_cover X name z h hnd e he hp hr ha hb hl hd e9 he9,
    sbipGraphStep9Input_block_cover X name z h hnd e he hp hr ha hb hl hd e9 he9,?_,?_⟩
  · intro x B
    exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
      ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ ⟨B.val,Or.inr B.property⟩
  · intro B C
    exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
      ⟨B.val,Or.inr B.property⟩ ⟨C.val,Or.inr C.property⟩

theorem sbipGraphStep9Input_designNames (h6 : ¬ Step6Imprimitive X) (hc : Step9Clique X) :
    DesignNames (step9DesignObj X hd h6 hc)
      (sbipGraphNumberedPoint (step8Obj X) (sbipGraphConstituent z) e9)
      (sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent z) e9) (sbipGraphStep9Input z) := by
  refine ⟨sbipGraphNumberedPoint_injective _ _ _,sbipGraphNumberedBlock_injective _ _ _,
    sbipGraphStep9Input_point_cover X name z h hnd e he hp hr ha hb hl hd e9 he9,
    sbipGraphStep9Input_block_cover X name z h hnd e he hp hr ha hb hl hd e9 he9,?_,?_,?_⟩
  · intro x B
    exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
      ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ ⟨B.val,Or.inr B.property⟩
  · intro B C
    exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
      ⟨B.val,Or.inr B.property⟩ ⟨C.val,Or.inr C.property⟩
  · intro x y
    exact sbipGraphStep9Input_color X name z h hnd e he hp hr ha hb hl hd e9 he9
      ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ ⟨{y.val},Or.inl ⟨y.val,y.property,rfl⟩⟩

end
end Algo
