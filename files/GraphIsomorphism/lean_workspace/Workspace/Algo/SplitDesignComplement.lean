import Workspace.Algo.SplitDesignJohnson

/-! # Section 9.7: the complemented neighborhood hypergraph

The paper's Design Lemma input uses the smaller of the neighborhood rank
and its complement rank, as recorded in the corrected paper. The rows already
computed for the Johnson labels give this hypergraph on block positions.
-/
namespace Algo
open Babai RAM

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

/-- Complementing a row agrees with complementing the edge in the paper's carrier. -/
theorem designLabel_blockSet (x : ↥X.Pt₁) :
    splitRowSet r.2.2.length (designLabel (r,e₁ x)) =
      (if 2 * X.d₁ ≤ X.n₂ then X.toBlkFinset (X.nbhd x.val)
       else Finset.univ \ X.toBlkFinset (X.nbhd x.val)).image (designBlockEquiv e₂) := by
  classical
  have hh := designRow_image h e₁ he₁ e₂ he₂ x
  have hb : (X.label x.val).image e₂ =
      (X.toBlkFinset (X.nbhd x.val)).image (designBlockEquiv e₂) := by
    ext i
    obtain ⟨B,rfl⟩ := e₂.surjective i
    rw [Finset.mem_image]
    constructor
    · rintro ⟨C,hC,he⟩
      have hCB := e₂.injective he
      subst C
      rw [← hh,mem_splitRowSet,designRow_mem h e₁ he₁ e₂ he₂]
      simpa only [BlkCaseObj.label,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hC
    · intro hm
      rw [← hh,mem_splitRowSet,designRow_mem h e₁ he₁ e₂ he₂] at hm
      exact ⟨B,by simpa only [BlkCaseObj.label,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hm,rfl⟩
  change rawJSet _ _ = _
  rw [designLabel_set h e₁ he₁ e₂ he₂,hb]
  split
  · rfl
  · exact (Hypergraph.image_sdiff_univ' (designBlockEquiv e₂) _).symm

/-- Every stored complemented row is exactly one neighborhood edge. -/
theorem designLabels_edges (F : Finset (Fin r.2.2.length)) :
    F ∈ (decSplitHypergraph r.2.2.length (designLabels r)).edgeSet ↔
      ∃ x : ↥X.Pt₁, F =
        (if 2 * X.d₁ ≤ X.n₂ then X.toBlkFinset (X.nbhd x.val)
         else Finset.univ \ X.toBlkFinset (X.nbhd x.val)).image (designBlockEquiv e₂) := by
  constructor
  · rintro ⟨i,hi⟩
    let j : Fin r.2.1.length := ⟨i.val,by simpa [decSplitHypergraph] using i.isLt⟩
    refine ⟨e₁.symm j,?_⟩
    rw [← designLabel_blockSet h e₁ he₁ e₂ he₂,Equiv.apply_symm_apply,← hi]
    change splitRowSet _ ((designLabels r).getD i.val []) = _
    have hj : i.val < r.2.1.length := j.isLt
    simp [designLabels,j,hj]
  · rintro ⟨x,rfl⟩
    refine ⟨⟨(e₁ x).val,by simpa [decSplitHypergraph] using (e₁ x).isLt⟩,?_⟩
    change splitRowSet _ ((designLabels r).getD (e₁ x).val []) = _
    rw [show (designLabels r).getD (e₁ x).val [] = designLabel (r,e₁ x) by
      simp [designLabels,(e₁ x).isLt]]
    exact designLabel_blockSet h e₁ he₁ e₂ he₂ x

/-- The row hypergraph is the paper's `nbhdHg` through the explicit block bijection. -/
theorem designLabels_image_mem (F : Finset ↥X.blkAmb) :
    F.image (designBlockEquiv e₂) ∈
      (decSplitHypergraph r.2.2.length (designLabels r)).edgeSet ↔
        F ∈ X.nbhdHg.edgeSet := by
  classical
  rw [designLabels_edges h e₁ he₁ e₂ he₂]
  have hinj := Finset.image_injective (designBlockEquiv e₂).injective
  simp only [hinj.eq_iff]
  rw [BlkCaseObj.nbhdHg]
  split
  · rw [Hypergraph.edgeSet_ofFinsetSet]
    simp only [Finset.mem_coe,X.mem_edgeFinsetFam]
    constructor
    · rintro ⟨x,rfl⟩; exact ⟨X.nbhd x.val,⟨x.val,x.property,rfl⟩,rfl⟩
    · rintro ⟨S,⟨x,hx,rfl⟩,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
  · rw [Hypergraph.edgeSet_compl,Hypergraph.edgeSet_ofFinsetSet]
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨X.toBlkFinset (X.nbhd x.val),
        (X.mem_edgeFinsetFam _).2 ⟨X.nbhd x.val,⟨x.val,x.property,rfl⟩,rfl⟩,rfl⟩
    · rintro ⟨S,hS,rfl⟩
      obtain ⟨T,⟨x,hx,rfl⟩,rfl⟩ := (X.mem_edgeFinsetFam _).1 hS
      exact ⟨⟨x,hx⟩,rfl⟩

end Specification
end Algo
