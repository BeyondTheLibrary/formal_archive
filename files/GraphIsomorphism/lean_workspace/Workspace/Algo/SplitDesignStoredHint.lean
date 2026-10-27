import Workspace.Algo.SplitDesignStoredFields

/-! The packed graph's vertex positions match the old point-first list.
Thus the new hint reads the selected structure's exact ordered-pair colors. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase}
    (point : ↥s → ℕ) (d : List (List ℕ)) (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    (h₁ : ∀ x, (e (X.vtxOfPt x)).val = name₁ x)
    (w : List ℕ) (S : Set (Set ↥s)) (H : Set ↥s → Set ↥s → ℕ)
    (cols : List ℕ) (hint : RawConfig)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (eB : ↥(X.linkGraph.restrictBlkHint S H).blocks ≃ Fin cols.length)
    (heB : ∀ B, cols[(eB B).val] = name₂ ⟨B.val,B.property.1⟩)

local notation "z" => sbipFromCasePack ((w,d),(designStoredRaw ((r,cols),hint),0))

include hd hp h₁ he₁ heB in
theorem designStored_hint_index (hnd : (sbipPackVertices z).Nodup)
    (A : (X.linkGraph.restrictBlkHint S H).Vtx) :
    ∃ i : Fin (r.2.1 ++ cols).length,
      rawLetterIndex (sbipPackVertices z,
        sbipPackName (X.linkGraph.restrictBlkHint S H) point w.length eB A) = i ∧
      (r.2.1 ++ cols)[i.val] = designGraphName (name₁ := name₁) (name₂ := name₂) S H A := by
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · let u : ↥X.Pt₁ := ⟨x,hx⟩
    have hi : (e₁ u).val < (r.2.1 ++ cols).length := by
      simp only [List.length_append]; have := (e₁ u).isLt; omega
    refine ⟨⟨(e₁ u).val,hi⟩,?_,?_⟩
    · rw [sbipPackName_point (X.linkGraph.restrictBlkHint S H) point w.length eB x hx]
      have hh := sbipPackIndex_point z hnd
        (designStoredPointEquiv (r := r) d w S H cols hint e₁ u)
      rw [designStoredPointEquiv_get point d e hd hp h₁ w S H cols hint e₁ he₁ u] at hh
      exact hh
    · rw [List.getElem_append_left (e₁ u).isLt,he₁,designGraphName_point S H u]
  · let B : ↥(X.linkGraph.restrictBlkHint S H).blocks := ⟨A,hA⟩
    have hi : r.2.1.length+(eB B).val < (r.2.1 ++ cols).length := by
      simp only [List.length_append]; have := (eB B).isLt; omega
    refine ⟨⟨r.2.1.length+(eB B).val,hi⟩,?_,?_⟩
    · rw [sbipPackName_block (X.linkGraph.restrictBlkHint S H) point w.length eB B]
      have hh := sbipPackIndex_block z hnd
        (designStoredBlockEquiv (r := r) d w S H cols hint eB B)
      simpa only [sbipFromCasePack,designStoredRaw,sbipDictPoints,List.length_map] using hh
    · change (r.2.1 ++ cols)[r.2.1.length+(eB B).val]'hi = _
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp only [Nat.add_sub_cancel_left,heB]
      exact (designGraphName_block S H ⟨A,hA.1⟩ hA.2).symm

include hd hp h₁ he₁ heB in
theorem designStored_hint (hnd : (sbipPackVertices z).Nodup)
    (hH : ∀ A B : (X.linkGraph.restrictBlkHint S H).Vtx,
      binColor (hint,(designGraphName (name₁ := name₁) (name₂ := name₂) S H A,
        designGraphName (name₁ := name₁) (name₂ := name₂) S H B)) =
          (X.linkGraph.restrictBlkHint S H).h A.val B.val)
    (A B : (X.linkGraph.restrictBlkHint S H).Vtx) :
    binColor ((z).2.2.2.2.2,
      (rawLetterIndex (sbipPackVertices z,sbipPackName (X.linkGraph.restrictBlkHint S H) point w.length eB A),
       rawLetterIndex (sbipPackVertices z,sbipPackName (X.linkGraph.restrictBlkHint S H) point w.length eB B))) =
      (X.linkGraph.restrictBlkHint S H).h A.val B.val := by
  obtain ⟨i,hi,heI⟩ := designStored_hint_index point d e hd hp h₁ w S H cols hint e₁ he₁ eB heB hnd A
  obtain ⟨j,hj,heJ⟩ := designStored_hint_index point d e hd hp h₁ w S H cols hint e₁ he₁ eB heB hnd B
  rw [hi,hj]
  change binColor (sbipIndexed (hint,r.2.1 ++ cols),(i,j)) = _
  rw [sbipIndexed_get,heI,heJ]
  exact hH A B

end
end Algo
