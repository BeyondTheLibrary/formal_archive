import Workspace.Algo.SplitBipCaseOutcomeNumbered
import Workspace.Algo.SplitBipCaseOutcomePartition
import Workspace.Algo.SplitBipGraphComponentValidity

/-! The actual step-9 context restores exactly the dominant point list.
Thus the paper's alpha rescaling, already proved at step 5, supplies the
parent bound for every valid local partition returned by a case.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)
    (z : RawSbipStored × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1.1 name)
    (hnd : (sbipGraphVertices z.1.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1.1).length)
    (he : ∀ A,(sbipGraphVertices z.1.1)[(e A).val] = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)
include h hnd he hp hr ha hb hl hd

/-- Exact parent-domain decoder, with both enumerations tied to the
computed lists. The extra block and the color shift are the paper's
`extendPartition`, not a separately chosen partition of the same size. -/
theorem sbipCaseStep9_partition_decode (q : RawColPart) :
    ∃ (eV : ↥(BipBlockInputs.V₁ X) ≃ Fin z.1.1.1.1.length)
      (eW : ↥(Subtype.val '' dominantClass X) ≃
        Fin (sbipDominant (sbipGraphClasses (z.1.1,z.2))).length),
      (∀ x,z.1.1.1.1[(eV x).val] = sbipGraphAmbientPointName X name x.val) ∧
      (∀ x,(sbipDominant (sbipGraphClasses (z.1.1,z.2)))[(eW x).val] =
        sbipGraphAmbientPointName X name x.val) ∧
      (decColPartition z.1.1.1.1.length (sbipCasePartition
        ((z.1.1.1.1,sbipGraphStep9Dictionary z,(sbipGraphStep9Input (z.1.1,z.2)).2.1),q))).pushforward eV.symm =
        extendPartition (BipBlockInputs.V₁ X) (Subtype.val '' dominantClass X)
          ((decColPartition (sbipDominant (sbipGraphClasses (z.1.1,z.2))).length q).pushforward eW.symm) := by
  let g := (z.1.1,z.2)
  obtain ⟨eV,heV⟩ := sbipGraphParent_equiv_exists X name g h hnd e he hp ha hl
  obtain ⟨eW,heW⟩ := sbipGraphDominant_equiv_exists X g name h hnd e he hp hr ha hb hl hd
  let eW' := (splitImageEquiv (dominantClass X)).trans eW
  have heW' (x : ↥(Subtype.val '' dominantClass X)) :
      (sbipDominant (sbipGraphClasses g))[(eW' x).val] = sbipGraphAmbientPointName X name x.val := by
    rw [show sbipGraphAmbientPointName X name x.val =
      sbipGraphPointName X name ⟨liftPt x,(liftPt_mem x).1⟩ from
      sbipGraphAmbientPointName_get X name ⟨liftPt x,(liftPt_mem x).1⟩]
    exact heW (wPt x)
  refine ⟨eV,eW',heV,heW',?_⟩
  rw [sbipCasePartition_step9]
  let P := (decColPartition (sbipDominant (sbipGraphClasses g)).length q).pushforward eW'.symm
  apply ColoredPartition.ext
  · funext x
    exact rawExtendPartition_color P (sbipGraphAmbientPointName X name) eV heV eW' heW'
      (hl.filter _) (sbipGraphAmbientPointName_dominant X name g h hnd e he hp ha hb hl hd)
      (fun _ => rfl) x
  · apply Setoid.ext
    intro x y
    exact rawExtendPartition_part P (sbipGraphAmbientPointName X name) eV heV eW' heW'
      (hl.filter _) (sbipGraphAmbientPointName_dominant X name g h hnd e he hp ha hb hl hd)
      (fun _ _ => Iff.rfl) x y

theorem sbipCaseStep9_partition_valid (q : RawColPart)
    (hq : (decColPartition (sbipGraphStep9Input (z.1.1,z.2)).2.1.length q).IsAlphaPartition
      (alphaNew X)) :
    (decColPartition z.1.1.1.1.length (sbipCasePartition
      ((z.1.1.1.1,sbipGraphStep9Dictionary z,(sbipGraphStep9Input (z.1.1,z.2)).2.1),q))).IsAlphaPartition (BipBlockInputs.alpha X) := by
  let g := (z.1.1,z.2)
  obtain ⟨eV,heV⟩ := sbipGraphParent_equiv_exists X name g h hnd e he hp ha hl
  obtain ⟨eW,heW⟩ := sbipGraphDominant_equiv_exists X g name h hnd e he hp hr ha hb hl hd
  let eW' := (splitImageEquiv (dominantClass X)).trans eW
  have heW' (x : ↥(Subtype.val '' dominantClass X)) :
      (sbipDominant (sbipGraphClasses g))[(eW' x).val] = sbipGraphAmbientPointName X name x.val := by
    rw [show sbipGraphAmbientPointName X name x.val =
      sbipGraphPointName X name ⟨liftPt x,(liftPt_mem x).1⟩ from
      sbipGraphAmbientPointName_get X name ⟨liftPt x,(liftPt_mem x).1⟩]
    exact heW (wPt x)
  have hlen : (sbipGraphStep9Input g).2.1.length = (sbipDominant (sbipGraphClasses g)).length := by
    simp only [sbipGraphStep9Input,sbipGraphNumbered,List.length_map,List.length_range]
    rfl
  have hq' : (decColPartition (sbipDominant (sbipGraphClasses g)).length q).IsAlphaPartition
      (alphaNew X) := hlen ▸ hq
  let P := (decColPartition (sbipDominant (sbipGraphClasses g)).length q).pushforward eW'.symm
  have hP : P.IsAlphaPartition (alphaNew X) := by
    apply ColoredPartition.isAlphaPartition_of_kernel_rel _ P eW'.symm ?_ ?_ hq'
    · intro x y
      change labAt q.1 x = labAt q.1 y ↔ labAt q.1 (eW' (eW'.symm x)) = labAt q.1 (eW' (eW'.symm y))
      simp
    · intro x y
      change cellOf q x = cellOf q y ↔ cellOf q (eW' (eW'.symm x)) = cellOf q (eW' (eW'.symm y))
      simp
  have hbalance : alphaNew X * ((Subtype.val '' dominantClass X).ncard : ℝ) =
      BipBlockInputs.alpha X * ((BipBlockInputs.V₁ X).ncard : ℝ) := by
    simpa only [step8V₁_eq] using alphaNew_mul_step8V₁ hd
  rw [sbipCasePartition_step9]
  exact rawExtendPartition_valid P (sbipGraphAmbientPointName X name) eV heV eW' heW'
    (hl.filter _) (sbipGraphAmbientPointName_dominant X name g h hnd e he hp ha hb hl hd)
    (fun _ => rfl) (fun _ _ => Iff.rfl)
    (extendPartition.isAlphaPartition (dominantClass_image_subset_V₁ X) inferInstance inferInstance
      P (alphaNew_lt_one hd).le (by have hh := X.obj.2.1; change (2 : ℝ)/3 ≤ BipBlockInputs.alpha X at hh; linarith) hbalance hP)

/-- The half-partitions of cases (i) and (iii) meet the rescaled local bound. -/
theorem sbipCaseStep9_halfPartition_valid (q : RawColPart)
    (hq : (decColPartition (sbipGraphStep9Input (z.1.1,z.2)).2.1.length q).IsAlphaPartition (1/2)) :
    (decColPartition z.1.1.1.1.length (sbipCasePartition
      ((z.1.1.1.1,sbipGraphStep9Dictionary z,(sbipGraphStep9Input (z.1.1,z.2)).2.1),q))).IsAlphaPartition (BipBlockInputs.alpha X) := by
  apply sbipCaseStep9_partition_valid X name z h hnd e he hp hr ha hb hl hd q
  refine ⟨hq.1,hq.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hh := twothirds_le_alphaNew hd
  linarith

end
end Algo
