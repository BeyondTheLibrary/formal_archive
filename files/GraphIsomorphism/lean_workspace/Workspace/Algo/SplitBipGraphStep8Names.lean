import Workspace.Algo.SplitBipGraphConstituent
import Workspace.Algo.SplitNamedLists

/-! The vertices retained in step 8 use their old names. The inclusion
of the restricted point set identifies them with exactly the dominant
points and selected blocks of the computed link. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)

noncomputable def sbipGraphStep8OldVertex (A : (step8Obj X).Vtx) : X.obj.1.1.Vtx :=
  ⟨VColBipBlk.incl (step7Set_subset X) '' A.val,
    step7Vtx_subset_vtx X (step8Vtx_image_mem X A.property)⟩

noncomputable def sbipGraphStep8Name (A : (step8Obj X).Vtx) : ℕ :=
  name (sbipGraphStep8OldVertex X A)

theorem sbipGraphStep8Name_injective (hi : Function.Injective name) :
    Function.Injective (sbipGraphStep8Name X name) := by
  intro A B hh
  have he := congrArg (fun C : X.obj.1.1.Vtx => C.val) (hi hh)
  exact Subtype.ext (VColBipBlk.incl_image_injective (step7Set_subset X) he)

theorem sbipGraphStep8OldVertex_point (A : (step8Obj X).Vtx) :
    (∃ x, X.obj.1.1.part₁ x ∧ (sbipGraphStep8OldVertex X A).val = {x}) ↔
      ∃ p, (step8Obj X).part₁ p ∧ A.val = {p} := by
  constructor
  · rintro ⟨x,hx,hA⟩
    have hm : x ∈ VColBipBlk.incl (step7Set_subset X) '' A.val := by
      change x ∈ (sbipGraphStep8OldVertex X A).val
      rw [hA]
      exact Set.mem_singleton x
    obtain ⟨p,_,hp⟩ := hm
    refine ⟨p,?_,?_⟩
    · change X.obj.1.1.part₁ (VColBipBlk.incl (step7Set_subset X) p)
      exact hp.symm ▸ hx
    · apply VColBipBlk.incl_image_injective (step7Set_subset X)
      change (sbipGraphStep8OldVertex X A).val =
        VColBipBlk.incl (step7Set_subset X) '' {p}
      rw [Set.image_singleton,hp,hA]
  · rintro ⟨p,hp,hA⟩
    refine ⟨VColBipBlk.incl (step7Set_subset X) p,hp,?_⟩
    change VColBipBlk.incl (step7Set_subset X) '' A.val = _
    rw [hA,Set.image_singleton]

variable (z : RawSbipGraph × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)

include h hp in
theorem sbipGraphName_left (A : X.obj.1.1.Vtx) :
    name A ∈ z.1.1.1 ↔ ∃ x, X.obj.1.1.part₁ x ∧ A.val = {x} := by
  change name A ∈ {a | a ∈ z.1.1.1} ↔ _
  rw [← hp]
  constructor
  · rintro ⟨x,_,hx⟩
    exact ⟨x.val,x.property,(congrArg (fun B : X.obj.1.1.Vtx => B.val) (h.injective hx)).symm⟩
  · rintro ⟨x,hx,hA⟩
    exact ⟨⟨x,hx⟩,Set.mem_univ _,congrArg name (Subtype.ext hA.symm)⟩

include h hr in
theorem sbipGraphName_right (A : X.obj.1.1.Vtx) :
    name A ∈ z.1.1.2.1 ↔ A.val ∈ X.obj.1.1.blocks := by
  change name A ∈ {a | a ∈ z.1.1.2.1} ↔ _
  rw [← hr]
  constructor
  · rintro ⟨B,_,hB⟩
    have hh := congrArg (fun C : X.obj.1.1.Vtx => C.val) (h.injective hB)
    change B.val = A.val at hh
    exact hh ▸ B.property
  · intro hA
    exact ⟨⟨A.val,hA⟩,Set.mem_univ _,rfl⟩

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphStep8Name_left (A : (step8Obj X).Vtx) :
    sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.1 ↔
      ∃ x, (step8Obj X).part₁ x ∧ A.val = {x} := by
  have hh := sbipGraphLinkInput_names X z name h hnd e he hp hr ha hb hl hd
  change sbipGraphStep8Name X name A ∈ (sbipLinkInput (sbipGraphPrepared z)).2.1 ↔ _
  rw [hh.left]
  constructor
  · rintro ⟨x,hx⟩
    have hs := congrArg (fun C : X.obj.1.1.Vtx => C.val) (h.injective hx)
    refine ⟨step8Point X x,step8Point_part₁ X x,?_⟩
    apply VColBipBlk.incl_image_injective (step7Set_subset X)
    change VColBipBlk.incl (step7Set_subset X) '' A.val =
      VColBipBlk.incl (step7Set_subset X) '' {step8Point X x}
    rw [Set.image_singleton,incl_step8Point]
    exact hs.symm
  · rintro ⟨x,hx,hA⟩
    let u : ↥(dominantClass X) :=
      ⟨VColBipBlk.incl (step7Set_subset X) x,(step7Obj_part₁_iff X x).1 hx⟩
    refine ⟨u,congrArg name (Subtype.ext ?_)⟩
    change {u.val} = VColBipBlk.incl (step7Set_subset X) '' A.val
    rw [hA,Set.image_singleton]

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphStep8Name_right (A : (step8Obj X).Vtx) :
    sbipGraphStep8Name X name A ∈ (sbipGraphRetainedLink z).2.2 ↔
      A.val ∈ (step8Obj X).blocks := by
  have hh := sbipGraphLinkInput_names X z name h hnd e he hp hr ha hb hl hd
  let B := VColBipBlk.incl (step7Set_subset X) '' A.val
  change sbipGraphStep8Name X name A ∈ sbipStep7Right (sbipLinkInput (sbipGraphPrepared z)) ↔ _
  constructor
  · intro hA
    have hm := (sbipSecondClass_mem _ _ _).1 hA
    obtain ⟨C,hC⟩ := (hh.right _).1 hm.1
    have hs := congrArg (fun D : X.obj.1.1.Vtx => D.val) (h.injective hC)
    change C.val = B at hs
    change B ∈ X.obj.1.1.blocks
    exact hs ▸ C.property
  · intro hA
    have hB : B ∈ step7Blocks X := by
      rw [← step7Obj_blocks_image X]
      exact ⟨A.val,hA,rfl⟩
    exact (sbipStep7Right_spec hh hd ⟨B,hB.1⟩).2 hB

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphRetainedLink_nodup :
    ((sbipGraphRetainedLink z).2.1 ++ (sbipGraphRetainedLink z).2.2).Nodup := by
  have hs : (sbipGraphRetainedLink z).2.1.Sublist z.1.1.1 := List.filter_sublist
  have ht : (sbipGraphRetainedLink z).2.2.Sublist z.1.1.2.1 := List.filter_sublist
  exact hnd.sublist (hs.append ht)

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphStep8Name_equiv_exists :
    ∃ e8 : (step8Obj X).Vtx ≃
      Fin ((sbipGraphRetainedLink z).2.1 ++ (sbipGraphRetainedLink z).2.2).length,
      ∀ A, ((sbipGraphRetainedLink z).2.1 ++ (sbipGraphRetainedLink z).2.2)[(e8 A).val]'(e8 A).isLt =
        sbipGraphStep8Name X name A := by
  have hh := sbipGraphLinkInput_names X z name h hnd e he hp hr ha hb hl hd
  apply splitNameEquiv_exists _ (sbipGraphStep8Name_injective X name h.injective) _
    (sbipGraphRetainedLink_nodup X name z h hnd e he hp hr ha hb hl hd)
  intro a
  constructor
  · intro ha'
    rcases List.mem_append.1 ha' with ha' | ha'
    · obtain ⟨x,rfl⟩ := (hh.left a).1 ha'
      refine ⟨⟨{step8Point X x},Or.inl ⟨_,step8Point_part₁ X x,rfl⟩⟩,?_⟩
      apply congrArg name
      apply Subtype.ext
      exact Set.image_singleton
    · obtain ⟨B,hB⟩ := (hh.right a).1 ((sbipSecondClass_mem _ _ _).1 ha').1
      have hs := (sbipStep7Right_spec hh hd B).1 (hB.symm ▸ ha')
      obtain ⟨A,hA,himg⟩ := step8Vtx_image_surj X (Or.inr hs)
      refine ⟨⟨A,hA⟩,?_⟩
      exact (congrArg name (Subtype.ext himg)).trans hB
  · rintro ⟨A,rfl⟩
    rcases A.property with hA | hA
    · exact List.mem_append_left _
        ((sbipGraphStep8Name_left X name z h hnd e he hp hr ha hb hl hd A).2 hA)
    · exact List.mem_append_right _
        ((sbipGraphStep8Name_right X name z h hnd e he hp hr ha hb hl hd A).2 hA)

end
end Algo
