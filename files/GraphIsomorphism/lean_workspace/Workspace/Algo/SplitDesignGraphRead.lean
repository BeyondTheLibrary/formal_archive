import Workspace.Algo.SplitDesignGraphHint

/-! Each stored Case 3 graph starts the next refinement with exactly the
paper's initial coloring. The vertex positions come from its retained names. -/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h hw he₂

open scoped Classical in
theorem designReadGraph_refine (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    ∃ e : (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
        (designReadMathHint e₂ o)).Vtx ≃ Fin (r.2.1 ++ designReadSelected (r,o)).length,
      (∀ A, (r.2.1 ++ designReadSelected (r,o))[(e A).val]'(e A).isLt =
        designGraphName (name₁ := name₁) (name₂ := name₂) _ _ A) ∧
      ∀ A B, binColor (designGraphRefine (designCase3Graph (r,o)),(e A,e B)) =
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).wlNamed A B := by
  let S := designReadSelectedSet r name₂ o
  let H := designReadMathHint e₂ o
  have hg : ∀ B : ↥X.blocks, name₂ B ∈ designReadSelected (r,o) ↔ B.val ∈ S :=
    fun B => (designReadSelectedSet_mem o B).symm
  have hgr := designReadSelected_sub r o hL
  obtain ⟨e,he⟩ := designGraphName_equiv_exists h hw S H (designReadSelected (r,o))
    (designReadSelected_nodup hw o hnd hL) hg hgr
  refine ⟨e,he,?_⟩
  exact designGraphRefine_spec h hw (designReadSelected (r,o)) hg hgr H
    (designReadNamedHint (r,o)) (designGraphName (name₁ := name₁) (name₂ := name₂) S H)
    (designGraphName_point S H) (designGraphName_block S H)
    (designGraphName_injective h hw S H) (designReadGraph_hint h hw e₂ he₂ o) e he

open scoped Classical in
theorem designCallReadGraph_refine {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) :
    ∃ e : (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
        (designReadMathHint e₂ o)).Vtx ≃ Fin (r.2.1 ++ designReadSelected (r,o)).length,
      (∀ A, (r.2.1 ++ designReadSelected (r,o))[(e A).val]'(e A).isLt =
        designGraphName (name₁ := name₁) (name₂ := name₂) _ _ A) ∧
      ∀ A B, binColor (designGraphRefine (designCase3Graph (r,o)),(e A,e B)) =
        (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
          (designReadMathHint e₂ o)).wlNamed A B := by
  obtain ⟨hnd,hL⟩ := designCallReadFirst_names r ho
  exact designReadGraph_refine h hw e₂ he₂ o hnd hL

end
end Algo
