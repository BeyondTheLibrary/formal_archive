import Workspace.Algo.SplitBipStoredDictionary
import Workspace.Algo.SplitBipGraphStep9

/-! Steps 5--8 retain old block rows while restricting the point carrier.
The next dictionary follows the actual second refinement's numbering.
Thus every row passed to a case describes its vertex on the smaller
carrier, expressed in the original ambient point names. -/
namespace Algo
open Babai RAM

def sbipGraphStep9Dictionary (z : RawSbipStored × (ℕ × ℕ)) : List (List ℕ) :=
  sbipNumberedDictionary (sbipGraphConstituent (z.1.1,z.2),z.1.2)

theorem polyFun_sbipGraphStep9Dictionary : PolyFun sbipGraphStep9Dictionary :=
  (((((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_sbipGraphConstituent).pair
    (polyFun_fst.comp polyFun_snd)).comp polyFun_sbipNumberedDictionary)

@[simp] theorem sbipGraphStep9Dictionary_length (z : RawSbipStored × (ℕ × ℕ)) :
    (sbipGraphStep9Dictionary z).length =
      (sbipGraphCaseVertices (sbipGraphConstituent (z.1.1,z.2))).length :=
  sbipNumberedDictionary_length _

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (name : X.obj.1.1.Vtx → ℕ)
    (point : ↥X.car → ℕ) (z : RawSbipStored × (ℕ × ℕ))
    (hs : SbipStoredDictionary X.obj.1.1 point z.1 name)
include hs

theorem sbipGraphConstituent_storedDictionary :
    SbipStoredDictionary (step8Obj X) (point ∘ VColBipBlk.incl (step7Set_subset X))
      (sbipGraphConstituent (z.1.1,z.2),z.1.2) (sbipGraphStep8Name X name) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    have hx' : X.obj.1.1.part₁ (VColBipBlk.incl (step7Set_subset X) x) := hx
    have he : sbipGraphStep8OldVertex X ⟨{x},Or.inl ⟨x,hx,rfl⟩⟩ =
        ⟨{VColBipBlk.incl (step7Set_subset X) x},Or.inl ⟨_,hx',rfl⟩⟩ :=
      Subtype.ext (Set.image_singleton)
    change name (sbipGraphStep8OldVertex X _) = point _
    rw [he]
    exact hs.point_name _ hx'
  · intro B
    exact hs.block_nodup ⟨VColBipBlk.incl (step7Set_subset X) '' B.val,B.property⟩
  · intro B a
    have hh := hs.block_mem ⟨VColBipBlk.incl (step7Set_subset X) '' B.val,B.property⟩ a
    refine hh.trans ?_
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,ha⟩
      exact ⟨x,hx,ha⟩
    · rintro ⟨x,hx,ha⟩
      exact ⟨VColBipBlk.incl (step7Set_subset X) x,⟨x,hx,rfl⟩,ha⟩

variable
    (h : SbipGraphColorNames X.obj.1.1 z.1.1 name)
    (hnd : (sbipGraphVertices z.1.1).Nodup)
    (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices z.1.1).length)
    (he : ∀ A, (sbipGraphVertices z.1.1)[(e A).val]'(e A).isLt = name A)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ z.1.1.1.1})
    (hr : sbipGraphBlockName X name '' Set.univ = {a | a ∈ z.1.1.1.2.1})
    (ha : sbipAlphaValue z.2 = BipBlockInputs.alpha X)
    (hb : 0 < z.2.2) (hl : z.1.1.1.1.Nodup) (hd : ¬ AllClassesSmall X)
include h hnd he hp hr ha hb hl hd

theorem sbipGraphStep9Dictionary_spec
    (e9 : (step8Obj X).Vtx ≃ Fin (sbipGraphStep9Dictionary z).length)
    (he9 : ∀ A, (sbipGraphCaseVertices (sbipGraphConstituent (z.1.1,z.2)))[(e9 A).val]'
      (by simpa using (e9 A).isLt) = sbipGraphStep8Name X name A) :
    SbipVertexDictionary {A | IsVertexOn (step8Obj X).part₁ (step8Obj X).blocks A}
      (point ∘ VColBipBlk.incl (step7Set_subset X)) (sbipGraphStep9Dictionary z) e9 :=
  sbipNumberedDictionary_spec (sbipGraphConstituent_storedDictionary X name point z hs)
    (sbipGraphStep8Name_left X name (z.1.1,z.2) h hnd e he hp hr ha hb hl hd) e9 he9

theorem sbipGraphStep9Dictionary_equiv_exists :
    ∃ e9 : (step8Obj X).Vtx ≃ Fin (sbipGraphStep9Dictionary z).length,
      (∀ A, (sbipGraphCaseVertices (sbipGraphConstituent (z.1.1,z.2)))[(e9 A).val]'
        (by simpa using (e9 A).isLt) = sbipGraphStep8Name X name A) ∧
      SbipVertexDictionary {A | IsVertexOn (step8Obj X).part₁ (step8Obj X).blocks A}
        (point ∘ VColBipBlk.incl (step7Set_subset X)) (sbipGraphStep9Dictionary z) e9 := by
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (z.1.1,z.2) h hnd e he hp hr ha hb hl hd
  let eD := e9.trans (finCongr (sbipGraphStep9Dictionary_length z).symm)
  have hD : ∀ A, (sbipGraphCaseVertices (sbipGraphConstituent (z.1.1,z.2)))[(eD A).val]'
      (by simpa using (eD A).isLt) = sbipGraphStep8Name X name A := he9
  exact ⟨eD,hD,sbipGraphStep9Dictionary_spec X name point z hs h hnd e he hp hr ha hb hl hd eD hD⟩

end
end Algo
