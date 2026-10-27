import Workspace.Algo.SplitBipGraphRestrict
import Workspace.Algo.SplitBipLink

/-! The link scans use the same computed refinement as step 5. Their
names come from the stored graph, so the selected colors do not enter as
extra assumptions. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (z : RawSbipGraph × (ℕ × ℕ))
    (name : X.obj.1.1.Vtx → ℕ)
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)

def sbipGraphDominantName (x : ↥(dominantClass X)) : ℕ :=
  sbipGraphPointName X name ⟨x.val,x.property.1⟩

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphLinkInput_names :
    SbipLinkNames X (sbipGraphDominantName X name) (sbipGraphBlockName X name)
      (sbipLinkInput (sbipGraphPrepared z)) := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  have hcolor (A B : X.obj.1.1.Vtx) :
      binColor (sbipGraphRefine z.1,(name A,name B)) =
        VColBipBlk.wlCaseColor X.obj.1.1 A.val B.val := by
    rw [VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
    exact sbipGraphRefine_spec X.obj.1.1 z.1 name h hnd e he A B
  refine ⟨?_,?_,?_,?_⟩
  · intro a
    change a ∈ sbipDominant (sbipGraphClasses z) ↔ _
    constructor
    · intro hh
      obtain ⟨x,rfl⟩ := sbipName_surj hc (List.mem_of_mem_filter hh)
      exact ⟨⟨x.val,(sbipDominant_spec hc hl hb hd x).1 hh⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact (sbipDominant_spec hc hl hb hd ⟨x.val,x.property.1⟩).2 x.property
  · intro b
    change b ∈ z.1.1.2.1 ↔ _
    rw [← show b ∈ sbipGraphBlockName X name '' Set.univ ↔ b ∈ z.1.1.2.1
      from by rw [hr]; rfl]
    simp
  · intro B
    exact hcolor ⟨B.val,Or.inr B.property⟩ ⟨B.val,Or.inr B.property⟩
  · intro x B
    exact hcolor ⟨{x.val},Or.inl ⟨x.val,x.property.1,rfl⟩⟩ ⟨B.val,Or.inr B.property⟩

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphLinkInput_selected :
    sbipFirstNontrivial (sbipLinkInput (sbipGraphPrepared z)) = step7Color X ∧
    sbipFirstInvolved ((sbipLinkInput (sbipGraphPrepared z)).1,
      ((sbipLinkInput (sbipGraphPrepared z)).2.1,
        sbipStep7Right (sbipLinkInput (sbipGraphPrepared z)))) = step8Color X := by
  have hh := sbipGraphLinkInput_names X z name h hnd e he hp hr ha hb hl hd
  exact ⟨sbipFirstNontrivial_spec hh hd,sbipFirstInvolved_spec hh hd⟩

end
end Algo
