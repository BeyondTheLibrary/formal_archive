import Workspace.Algo.SplitDesignDomJohnson

/-! # Exact colors of the dominant Johnson output

The stored point name retrieves its own trace label. Counting differences
of these labels then gives the paper's Johnson coloring on the dominant class.
-/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
    (p : ℕ × ℕ) (hb : 0 < p.2)
include h he₁ he₂ hb

theorem designDomJohnson_row (hleft : r.2.1.Nodup)
    (x : ↥(X.domClass (sbipAlphaValue p))) :
    rawJRow (designDomJohnson (r,p),name₁ ⟨x.val,x.property.1⟩) =
      designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩) := by
  obtain ⟨eA,heA⟩ := designDomEquiv_exists h e₁ he₁ e₂ he₂ p hb
  have hpoint : (designDomPoints (r,p))[(eA x).val]? = some (name₁ ⟨x.val,x.property.1⟩) := by
    simp only [designDomPoints,List.getElem?_map,List.getElem?_eq_getElem (eA x).isLt,heA,
      Option.map_some,labAt,List.getD_eq_getElem _ _ (e₁ ⟨x.val,x.property.1⟩).isLt,he₁]
  have hrow : (designDomLabels (r,p))[(eA x).val]? =
      some (designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩)) := by
    simp only [designDomLabels,List.getElem?_map,List.getElem?_eq_getElem (eA x).isLt,heA,
      Option.map_some]
  have hh := rawJ_lookup_zip (designDomPoints (r,p)) (designDomLabels (r,p)) (eA x)
    (name₁ ⟨x.val,x.property.1⟩) (designDomLabel ((r,p),e₁ ⟨x.val,x.property.1⟩))
    (designDomPoints_nodup p hleft) (by simp [designDomPoints,designDomLabels]) hpoint hrow
  exact congrArg (fun o => o.getD []) hh

theorem designDomJohnson_color (hleft : r.2.1.Nodup) (hd : X.DomHyp (sbipAlphaValue p))
    (x y : ↥(X.domClass (sbipAlphaValue p))) :
    rawJDiff (designDomJohnson (r,p),(name₁ ⟨x.val,x.property.1⟩,name₁ ⟨y.val,y.property.1⟩)) =
      X.domJohnsonColor (sbipAlphaValue p) (mkPt x.property) (mkPt y.property) := by
  classical
  obtain ⟨eC,heC⟩ := designBigEquiv_exists h e₁ he₁ e₂ he₂
  have hrow := designDomJohnson_row h e₁ he₁ e₂ he₂ p hb hleft
  have hnd : (rawJRow (designDomJohnson (r,p),name₁ ⟨x.val,x.property.1⟩)).Nodup := by
    rw [hrow]; exact (designDomLabel_sorted _ _).nodup
  have hlt : ∀ a ∈ rawJRow (designDomJohnson (r,p),name₁ ⟨x.val,x.property.1⟩),
      a < (designBigPositions r).length := by
    rw [hrow]; exact designDomLabel_lt _ _
  rw [rawJDiff_eq_card hnd hlt,hrow,hrow,
    designDomLabel_set h e₁ he₁ e₂ he₂ p hb eC heC hd x,
    designDomLabel_set h e₁ he₁ e₂ he₂ p hb eC heC hd y,
    designDom_localSize hd x y]
  change _ = ((X.nbhd x.val ∩ X.bigTwin) \ (X.nbhd y.val ∩ X.bigTwin)).ncard
  split
  · rw [← Finset.image_sdiff _ _ eC.injective,Finset.card_image_of_injective _ eC.injective,
      X.card_traceFinset_sdiff]
  · have he (A B : Finset (Fin (designBigPositions r).length)) :
        (Finset.univ \ A) \ (Finset.univ \ B) = B \ A := by
      ext i
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      tauto
    rw [he,← Finset.image_sdiff _ _ eC.injective,Finset.card_image_of_injective _ eC.injective]
    have hc : (X.traceFinset y.val).card = (X.traceFinset x.val).card := by
      rw [X.card_traceFinset,X.card_traceFinset,designDom_localSize hd x y]
    rw [Finset.card_sdiff_comm hc,X.card_traceFinset_sdiff]

end
end Algo
