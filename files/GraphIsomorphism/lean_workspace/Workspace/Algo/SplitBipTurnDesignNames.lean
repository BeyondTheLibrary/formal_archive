import Workspace.Algo.SplitBipTurnUpccPartition
import Workspace.Algo.SplitDesignTestsTransport

/-! The DesignCase input uses the freshly numbered Step 9 vertices. Its
actual dictionary recovers the persistent point names, independently of
the incoming order of points and blocks.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

/-- Sec. 9.7, Case 2 input (Babai v2.5): the actual DesignCase record at a represented
node names the points and blocks of the Step 9 design object, with the paper's colors. -/
theorem design_case_names (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    let U := step9DesignObj X hd h6 hcl
    ∃ eD : ↥U.vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length,
      DesignNames U (fun x => (eD (U.vtxOfPt x)).val)
        (fun B => (eD (U.vtxOfBlk B)).val) (sbipTurnCase I.1).2.1 ∧
      SbipVertexDictionary U.vtxSet (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2) eD ∧
      ∀ A,binColor ((sbipTurnCase I.1).2.1.1,(eD A,eD A)) = U.c A.val A.val := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  refine ⟨eD,sbipGraphStep9Input_designNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hcl,hD,?_⟩
  intro A
  exact sbipGraphStep9Input_color X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 A A

/-- Reading a DesignCase partition and extending it at this parent gives
exactly the corresponding partition of the mathematical first part. -/
theorem design_partition_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X)
    (eD : ↥(step9DesignObj X hd h6 hcl).vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length)
    (hn : DesignNames (step9DesignObj X hd h6 hcl)
      (fun x => (eD ((step9DesignObj X hd h6 hcl).vtxOfPt x)).val)
      (fun B => (eD ((step9DesignObj X hd h6 hcl).vtxOfBlk B)).val) (sbipTurnCase I.1).2.1)
    (hD : SbipVertexDictionary (step9DesignObj X hd h6 hcl).vtxSet (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2) eD)
    (e₁ : ↥(step9DesignObj X hd h6 hcl).Pt₁ ≃ Fin (sbipTurnCase I.1).2.1.2.1.length)
    (he₁ : ∀ x,(sbipTurnCase I.1).2.1.2.1[(e₁ x).val] =
      (eD ((step9DesignObj X hd h6 hcl).vtxOfPt x)).val)
    (P : ColoredPartition ↥(Subtype.val '' (step9DesignObj X hd h6 hcl).Pt₁) ℕ)
    (q : RawColPart)
    (hc : ∀ x,labAt q.1 (e₁ x) = P.color (mkPt x.property))
    (hp : ∀ x y,cellOf q (e₁ x) = cellOf q (e₁ y) ↔ P.part (mkPt x.property) (mkPt y.property)) :
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition q)).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (step8V₁ X) P)⟩ := by
  let U := step9DesignObj X hd h6 hcl
  let eW := (splitImageEquiv U.Pt₁).trans e₁
  let name := fun x : ↥(Subtype.val '' U.Pt₁) => (eD (U.vtxOfPt (wPt x))).val
  have heW (x : ↥(Subtype.val '' U.Pt₁)) :
      (sbipTurnCase I.1).2.1.2.1[(eW x).val] = name x := he₁ (wPt x)
  have hrow (x : ↥(Subtype.val '' U.Pt₁)) :
      sbipDictPoint (sbipGraphStep9Dictionary I.1.2,name x) = x.val.val :=
    sbipVertexDictionary_point hD
      (fun _ _ hh => Subtype.ext (Fin.ext hh)) (wPt x).val (Or.inl ⟨_,(wPt x).property,rfl⟩)
  have hcover (a : ℕ) : a ∈ (sbipTurnCase I.1).2.1.2.1 ↔ ∃ x,name x = a := by
    rw [hn.left]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨mkPt x.property,by simpa only [name,wPt_mkPt] using hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨wPt x,hx⟩
  apply h.case_partition_named_decode P (step8V₁_subset X) q name eW heW hrow hcover
  · intro x
    exact hc (wPt x)
  · intro x y
    exact hp (wPt x) (wPt y)

end SbipNodeRep
end Algo
