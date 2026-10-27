import Workspace.Algo.SplitBipStep9

/-! Section 9.4, step 9: transport of the case test and its UPCC branch. -/

namespace Algo
open Babai RAM

/-- The case tag depends only on the named binary configuration. -/
theorem sbipCase_congr (p q : RawConfig) (e : Fin p.1.length ≃ Fin q.1.length)
    (h : ∀ u v, namedBin q.1.length q (e u) (e v) = namedBin p.1.length p u v) :
    sbipCase q = sbipCase p := by
  have hi : sbipImprimitive q = sbipImprimitive p := by
    apply Bool.eq_iff_iff.mpr
    simp only [sbipImprimitive_spec]
    exact exists_congr (fun k => isDisconnectedColor_map e h k)
  have hc : sbipClique q = sbipClique p := by
    apply Bool.eq_iff_iff.mpr
    simp only [sbipClique_spec]
    constructor
    · intro hh u v a b huv hab
      simpa only [h] using hh (e u) (e v) (e a) (e b)
        (fun he => huv (e.injective he)) (fun he => hab (e.injective he))
    · intro hh u v a b huv hab
      have hk := hh (e.symm u) (e.symm v) (e.symm a) (e.symm b)
        (fun he => huv (e.symm.injective he)) (fun he => hab (e.symm.injective he))
      simpa only [← h,Equiv.apply_symm_apply] using hk
  simp only [sbipCase,hi,hc]

/-- Moving the two part lists in their old order preserves the case tag. -/
theorem sbipStep9Case_relabel {r : RawUpccCase} {π : RawPerm}
    (hw : r.WF) (hπ : RawPerm.WF r.1.1.length π) :
    sbipStep9Case (UpccCase.relabelInput π r) = sbipStep9Case r := by
  unfold sbipStep9Case UpccCase.relabelInput
  apply sbipCase_congr _ _ (finCongr (by simp))
  intro u v
  change binColor (sbipIndexed (relabelWL (π,r.1),permList π r.2.2),
    ((finCongr (by simp)) u,(finCongr (by simp)) v)) =
      binColor (sbipIndexed (r.1,r.2.2),(u,v))
  change binColor (sbipIndexed (relabelWL (π,r.1),permList π r.2.2),(u.val,v.val)) =
    binColor (sbipIndexed (r.1,r.2.2),(u.val,v.val))
  rw [sbipIndexed_get (relabelWL (π,r.1)) (permList π r.2.2)
      ⟨u.val,by simpa using u.isLt⟩ ⟨v.val,by simpa using v.isLt⟩,
    sbipIndexed_get r.1 r.2.2 ⟨u.val,by simpa using u.isLt⟩ ⟨v.val,by simpa using v.isLt⟩]
  simp only [permList,List.getElem_map]
  exact binColor_relabel hw.table hπ
    (hw.right_lt (List.getElem_mem _)) (hw.right_lt (List.getElem_mem _))

/-- Section 9.4, step 9(iii): dispatch preserves the shifted canonicity
of the implemented UPCC family. -/
theorem sbipStep9Version_upcc_relabel
    (iv dv : RawUpccCase × ℕ → RawUpccCaseOutcome)
    {r : RawUpccCase} {π : RawPerm} (hw : r.WF)
    (hπ : RawPerm.WF r.1.1.length π) (hcase : sbipStep9Case r = 2)
    (x : Fin r.1.1.length) :
    sbipStep9Version iv dv id (UpccCase.relabelInput π r,rawApply (π,x)) =
      UpccCase.relabelOutcome π (sbipStep9Version iv dv id (r,x)) := by
  rw [sbipStep9Version_upcc iv dv id ((sbipStep9Case_relabel hw hπ).trans hcase),
    sbipStep9Version_upcc iv dv id hcase]
  exact UpccCase.versionF_relabel hw hπ x

end Algo
