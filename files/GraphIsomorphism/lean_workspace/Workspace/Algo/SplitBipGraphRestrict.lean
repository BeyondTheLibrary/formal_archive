import Workspace.Algo.SplitBipGraphPrepare

/-! Step 5 keeps the original vertex names. Its domain and configuration
therefore agree with the paper's restriction without renaming the stored
point colors or block dictionaries. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)
    {r : RawSbipStep5Input}

def sbipGraphBlockName (B : ↥X.obj.1.1.blocks) : ℕ :=
  name ⟨B.val,Or.inr B.property⟩

def sbipGraphRestrictedName (A : ↥(step5Vtx X)) : ℕ :=
  name ⟨A.val,step5Vtx_subset_vtx X A.property⟩

theorem sbipGraphRestricted_domain
    (h : SbipClassNames X (sbipGraphPointName X name) r.1.1)
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ r.1.2})
    (hnd : r.1.1.1.2.Nodup) (hb : 0 < r.1.1.2.2) (hd : ¬ AllClassesSmall X) :
    sbipGraphRestrictedName X name '' Set.univ = {a | a ∈ (sbipStep5 r).1.1.1} := by
  ext a
  constructor
  · rintro ⟨⟨A,hA⟩,_,rfl⟩
    rcases hA with ⟨x,hx,rfl⟩ | hA
    · exact List.mem_append_left _ ((sbipDominant_spec h hnd hb hd ⟨x,hx.1⟩).2 hx)
    · apply List.mem_append_right
      have hh := Set.mem_image_of_mem (sbipGraphBlockName X name) (Set.mem_univ ⟨A,hA⟩)
      rw [hr] at hh
      exact hh
  · intro ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨x,rfl⟩ := sbipName_surj h (List.mem_of_mem_filter ha)
      have hx := (sbipDominant_spec h hnd hb hd x).1 ha
      exact ⟨⟨{x.val},Or.inl ⟨x.val,hx,rfl⟩⟩,Set.mem_univ _,rfl⟩
    · have hm : a ∈ sbipGraphBlockName X name '' Set.univ := by rw [hr]; exact ha
      obtain ⟨B,_,rfl⟩ := hm
      exact ⟨⟨B.val,Or.inr B.property⟩,Set.mem_univ _,rfl⟩

theorem sbipGraphRestricted_config
    (h : SbipClassNames X (sbipGraphPointName X name) r.1.1)
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ r.1.2})
    (hnd : r.1.1.1.2.Nodup) (hb : 0 < r.1.1.2.2) (hd : ¬ AllClassesSmall X)
    (hc : ∀ A B : X.obj.1.1.Vtx, binColor (r.1.1.1.1,(name A,name B)) =
      VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val) :
    PartitionStructure.ofNamedColoring (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 r).1.1,
        (sbipGraphRestrictedName X name A,sbipGraphRestrictedName X name B))) =
      step5Config X := by
  have hm (A : ↥(step5Vtx X)) :
      sbipGraphRestrictedName X name A ∈ (sbipStep5 r).1.1.1 := by
    have hh := Set.mem_image_of_mem (sbipGraphRestrictedName X name) (Set.mem_univ A)
    rw [sbipGraphRestricted_domain X name h hr hnd hb hd] at hh
    exact hh
  have he : (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 r).1.1,
        (sbipGraphRestrictedName X name A,sbipGraphRestrictedName X name B))) =
      (fun A B : ↥(step5Vtx X) => VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val) := by
    funext A B
    rw [sbipStep5_table r (hm A) (hm B)]
    exact hc _ _
  rw [he]
  rfl

variable (z : RawSbipGraph × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)

include h hnd he hp ha hb hl hd in
theorem sbipGraphSteps35_continue :
    (sbipGraphSteps35 z).2 = some (sbipStep5 (sbipGraphPrepared z)) ∧
    (sbipStep5 (sbipGraphPrepared z)).2.1.1.length = (step5Obj X).V₁.ncard ∧
    sbipAlphaValue (sbipStep5 (sbipGraphPrepared z)).1.2 = alphaNew X := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  have hh : sbipNoDominant (sbipGraphClasses z) = false :=
    Bool.eq_false_iff.2 (fun ht => hd ((sbipNoDominant_iff hc hl hb).1 ht))
  refine ⟨?_,(sbipStep5_parts hc hl hb hd).2.2⟩
  simp [sbipGraphSteps35,sbipGraphPrepared,hh]

include h hnd he hp ha hb hl hd in
theorem sbipGraphSteps35_config
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1}) :
    PartitionStructure.ofNamedColoring (fun A B : ↥(step5Vtx X) =>
      binColor ((sbipStep5 (sbipGraphPrepared z)).1.1,
        (sbipGraphRestrictedName X name A,sbipGraphRestrictedName X name B))) =
      step5Config X := by
  apply sbipGraphRestricted_config X name
    (sbipGraphClasses_names X z name h hnd e he hp ha) hr hl hb hd
  intro A B
  rw [VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
  exact sbipGraphRefine_spec X.obj.1.1 z.1 name h hnd e he A B

end
end Algo
