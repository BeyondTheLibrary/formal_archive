import Workspace.Algo.SplitBipGraphLink
import Workspace.Algo.SplitNamedLists
import Workspace.Algo.ExtendPartitionSpec

/-! Step 6 scans the actual restricted configuration. Recoding closes
the gaps in its color names before the component routine reads the first
part. The returned local partition is extended to the parent first part. -/
namespace Algo
open Babai RAM

def sbipGraphComponentTable (z : RawSbipGraph × (ℕ × ℕ)) : RawConfig :=
  sbipStep6Table ((sbipStep5 (sbipGraphPrepared z)).1.1,
    sbipDominant (sbipGraphClasses z))

def sbipGraphComponentPartition (z : RawSbipGraph × (ℕ × ℕ)) : RawColPart :=
  rawExtendPartition ((z.1.1.1,sbipDominant (sbipGraphClasses z)),
    sbipStep6 (sbipGraphComponentTable z))

theorem polyFun_sbipGraphComponentTable : PolyFun sbipGraphComponentTable :=
  (((polyFun_sbipGraphPrepared.comp sbipPoly_step5).comp polyFun_fst).comp polyFun_fst |>.pair
    (polyFun_sbipGraphClasses.comp sbipPoly_dominant)).comp sbipPoly_step6Table

theorem polyFun_sbipGraphComponentPartition : PolyFun sbipGraphComponentPartition :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst |>.pair
    (polyFun_sbipGraphClasses.comp sbipPoly_dominant)).pair
      (polyFun_sbipGraphComponentTable.comp sbipPoly_step6)).comp polyFun_rawExtendPartition

@[simp] theorem sbipGraphComponentTable_length (z : RawSbipGraph × (ℕ × ℕ)) :
    (sbipGraphComponentTable z).1.length = (sbipDominant (sbipGraphClasses z)).length :=
  sbipIndexed_length _ _

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

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphDominant_equiv_exists :
    ∃ eW : ↥(dominantClass X) ≃ Fin (sbipDominant (sbipGraphClasses z)).length,
      ∀ x, (sbipDominant (sbipGraphClasses z))[(eW x).val]'(eW x).isLt =
        sbipGraphDominantName X name x := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  have hh := sbipGraphLinkInput_names X z name h hnd e he hp hr ha hb hl hd
  apply splitNameEquiv_exists _ ?_ _ (hl.filter _) hh.left
  intro x y hxy
  have hi := hc.injective (show sbipGraphPointName X name ⟨x.val,x.property.1⟩ =
    sbipGraphPointName X name ⟨y.val,y.property.1⟩ from hxy)
  exact Subtype.ext (congrArg (fun t : ↥X.obj.1.1.V₁ => t.val) hi)

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphComponentTable_names
    (eW : ↥(dominantClass X) ≃ Fin (sbipDominant (sbipGraphClasses z)).length)
    (hw : ∀ x, (sbipDominant (sbipGraphClasses z))[(eW x).val]'(eW x).isLt =
      sbipGraphDominantName X name x) :
    SbipStep6Names X (sbipGraphComponentTable z)
      (eW.trans (finCongr (sbipGraphComponentTable_length z).symm)) := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  have hd' := sbipGraphRestricted_domain X name (r := sbipGraphPrepared z) hc hr hl hb hd
  have ht : ∀ a, a ∈ (sbipStep5 (sbipGraphPrepared z)).1.1.1 ↔
      ∃ A, sbipGraphRestrictedName X name A = a := by
    intro a
    rw [← show a ∈ sbipGraphRestrictedName X name '' Set.univ ↔
      a ∈ (sbipStep5 (sbipGraphPrepared z)).1.1.1 from by rw [hd']; rfl]
    simp
  intro u v
  have hh := sbipStep6Table_spec X (sbipStep5 (sbipGraphPrepared z)).1.1
    (sbipGraphRestrictedName X name) ht
    (sbipGraphSteps35_config X name z h hnd e he hp ha hb hl hd hr)
    (sbipDominant (sbipGraphClasses z)) eW.symm
    (fun i => by simpa only [Equiv.apply_symm_apply] using hw (eW.symm i)) (eW u) (eW v)
  simpa only [Equiv.symm_apply_apply] using hh

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphComponentTable_test :
    sbipImprimitive (sbipGraphComponentTable z) = true ↔ Step6Imprimitive X := by
  obtain ⟨eW,hw⟩ := sbipGraphDominant_equiv_exists X z name h hnd e he hp hr ha hb hl hd
  exact sbipStep6_iff _
    (sbipGraphComponentTable_names X z name h hnd e he hp hr ha hb hl hd eW hw)

end
end Algo
