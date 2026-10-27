import Workspace.Algo.SplitBipTurnOutcomeIso

/-! Step 6 returns exactly the component partition, extended by the one
complement block. This read-off supplies the partition itself, which is
needed to transport the returned family, rather than just its size bound.
-/
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
    (he : ∀ A,(sbipGraphVertices z.1)[(e A).val] = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)
include h hnd he hp hr ha hb hl hd

theorem sbipGraphComponentPartition_decode :
    ∃ e₁ : ↥X.obj.1.1.V₁ ≃ Fin z.1.1.1.length,
      (∀ x,z.1.1.1[(e₁ x).val] = sbipGraphPointName X name x) ∧
      sbipGraphDecodePartition X.obj.1.1 e₁ (sbipGraphComponentPartition z) =
        extendPartition (BipBlockInputs.V₁ X) (Subtype.val '' dominantClass X)
          (compPartition (dominantClass X) (step6Color X)) := by
  obtain ⟨e₁,he₁⟩ := sbipGraphEarly_point_equiv_exists X z.1 name h hp hl
  let eV := (splitImageEquiv X.obj.1.1.V₁).trans e₁
  have heV (x : ↥(BipBlockInputs.V₁ X)) :
      z.1.1.1[(eV x).val] = sbipGraphAmbientPointName X name x.val := by
    rw [show sbipGraphAmbientPointName X name x.val =
      sbipGraphPointName X name (wPt x) from sbipGraphAmbientPointName_get X name (wPt x)]
    exact he₁ _
  obtain ⟨eW,heW⟩ := sbipGraphDominant_equiv_exists X z name h hnd e he hp hr ha hb hl hd
  have hn := sbipGraphComponentTable_names X z name h hnd e he hp hr ha hb hl hd eW heW
  let p := sbipStep6 (sbipGraphComponentTable z)
  let P := compPartition (dominantClass X) (step6Color X)
  let eW' := (splitImageEquiv (dominantClass X)).trans eW
  have heW' (x : ↥(Subtype.val '' dominantClass X)) :
      (sbipDominant (sbipGraphClasses z))[(eW' x).val] =
        sbipGraphAmbientPointName X name x.val := by
    rw [show sbipGraphAmbientPointName X name x.val =
      sbipGraphPointName X name ⟨liftPt x,(liftPt_mem x).1⟩ from
      sbipGraphAmbientPointName_get X name ⟨liftPt x,(liftPt_mem x).1⟩]
    exact heW (wPt x)
  have hc (x : ↥(Subtype.val '' dominantClass X)) :
      labAt p.1 (eW' x) = P.color x := by
    exact (sbipStep6_spec _ hn (wPt x) (wPt x)).1
  have hrel (x y : ↥(Subtype.val '' dominantClass X)) :
      cellOf p (eW' x) = cellOf p (eW' y) ↔ P.part x y := by
    have hh := (sbipStep6_spec _ hn (wPt x) (wPt y)).2
    change labAt p.2 (eW' x) = labAt p.2 (eW' y) ↔ P.part x y at hh
    simp only [cellOf,Prod.mk.injEq,hc]
    exact (and_iff_right rfl).trans hh
  have hmem := sbipGraphAmbientPointName_dominant X name z h hnd e he hp ha hb hl hd
  refine ⟨e₁,he₁,?_⟩
  apply ColoredPartition.ext
  · funext x
    exact rawExtendPartition_color P (sbipGraphAmbientPointName X name) eV heV eW' heW'
      (hl.filter _) hmem hc x
  · apply Setoid.ext
    intro x y
    exact rawExtendPartition_part P (sbipGraphAmbientPointName X name) eV heV eW' heW'
      (hl.filter _) hmem hrel x y

end
end Algo
