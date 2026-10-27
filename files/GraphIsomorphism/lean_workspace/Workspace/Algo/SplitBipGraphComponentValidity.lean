import Workspace.Algo.SplitBipGraphComponents

/-! The component exit returns a partition on the parent first part.
The local names are those selected by step 5. The complement is the single
extra block of the paper's extension. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def splitImageEquiv {s : Set Ω} (W : Set ↥s) : ↥(Subtype.val '' W) ≃ ↥W where
  toFun := wPt
  invFun x := mkPt x.property
  left_inv _ := Subtype.ext rfl
  right_inv := wPt_mkPt

variable (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)

noncomputable def sbipGraphAmbientPointName (x : Ω) : ℕ :=
  if hx : x ∈ BipBlockInputs.V₁ X then
    sbipGraphPointName X name (wPt ⟨x,hx⟩) else 0

theorem sbipGraphAmbientPointName_get (x : ↥X.obj.1.1.V₁) :
    sbipGraphAmbientPointName X name x.val.val = sbipGraphPointName X name x := by
  rw [sbipGraphAmbientPointName,dif_pos (show x.val.val ∈ BipBlockInputs.V₁ X from
    ⟨x.val,x.property,rfl⟩)]
  rfl

variable (z : RawSbipGraph × (ℕ × ℕ))
    (h : SbipGraphColorNames X.obj.1.1 z.1 name)
    (hnd : (sbipGraphVertices z.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1).length)
    (he : ∀ A, (sbipGraphVertices z.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)

include h hnd he hp ha hl in
theorem sbipGraphParent_equiv_exists :
    ∃ eV : ↥(BipBlockInputs.V₁ X) ≃ Fin z.1.1.1.length,
      ∀ x, z.1.1.1[(eV x).val]'(eV x).isLt = sbipGraphAmbientPointName X name x.val := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  obtain ⟨eV,heV⟩ := splitNameEquiv_exists _ hc.injective z.1.1.1 hl (fun a => by
    rw [← show a ∈ sbipGraphPointName X name '' Set.univ ↔ a ∈ z.1.1.1
      from by rw [hp]; rfl]
    simp)
  refine ⟨(splitImageEquiv X.obj.1.1.V₁).trans eV,fun x => ?_⟩
  rw [show sbipGraphAmbientPointName X name x.val =
    sbipGraphPointName X name (wPt x) from sbipGraphAmbientPointName_get X name (wPt x)]
  exact heV _

include h hnd he hp ha hb hl hd in
theorem sbipGraphAmbientPointName_dominant (x : ↥(BipBlockInputs.V₁ X)) :
    sbipGraphAmbientPointName X name x.val ∈ sbipDominant (sbipGraphClasses z) ↔
      x.val ∈ Subtype.val '' dominantClass X := by
  have hc := sbipGraphClasses_names X z name h hnd e he hp ha
  rw [show sbipGraphAmbientPointName X name x.val =
    sbipGraphPointName X name (wPt x) from sbipGraphAmbientPointName_get X name (wPt x),
    sbipDominant_spec hc hl hb hd]
  constructor
  · intro hx
    exact ⟨liftPt x,hx,rfl⟩
  · rintro ⟨u,hu,heq⟩
    have hu' : u = liftPt x := Subtype.ext heq
    change liftPt x ∈ dominantClass X
    rwa [← hu']

include h hnd he hp hr ha hb hl hd in
theorem sbipGraphComponentPartition_valid (hi : Step6Imprimitive X) :
    (decColPartition z.1.1.1.length (sbipGraphComponentPartition z)).IsAlphaPartition
      (BipBlockInputs.alpha X) := by
  obtain ⟨eV,heV⟩ := sbipGraphParent_equiv_exists X name z h hnd e he hp ha hl
  obtain ⟨eW,heW⟩ := sbipGraphDominant_equiv_exists X z name h hnd e he hp hr ha hb hl hd
  have hn := sbipGraphComponentTable_names X z name h hnd e he hp hr ha hb hl hd eW heW
  let p := sbipStep6 (sbipGraphComponentTable z)
  let P := compPartition (dominantClass X) (step6Color X)
  let eW' := (splitImageEquiv (dominantClass X)).trans eW
  have heW' (x : ↥(Subtype.val '' dominantClass X)) :
      (sbipDominant (sbipGraphClasses z))[(eW' x).val]'(eW' x).isLt =
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
  exact rawExtendPartition_valid P (sbipGraphAmbientPointName X name) eV heV eW' heW'
    (hl.filter _) (sbipGraphAmbientPointName_dominant X name z h hnd e he hp ha hb hl hd)
    hc hrel (step6_isAlphaPartition X hd hi inferInstance)

end
end Algo
