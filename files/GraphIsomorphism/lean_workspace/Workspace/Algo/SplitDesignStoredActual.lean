import Workspace.Algo.SplitDesignStoredBridge

/-! Every actual Design Lemma return supplies its selected columns and
hint to the common stored-graph bridge. No output field is assumed. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (hn : DesignNames X name₁ name₂ r) (hw : r.WF)
    (point : ↥s → ℕ) (d : List (List ℕ)) (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    (h₁ : ∀ x, (e (X.vtxOfPt x)).val = name₁ x)
    (h₂ : ∀ B, (e (X.vtxOfBlk B)).val = name₂ B)
    (hnsize : r.1.1.length = d.length)
    (hc : ∀ A, binColor (r.1,(e A,e A)) = X.c A.val A.val)
    (w : List ℕ) (hlt : ∀ x, point x < w.length)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include hn hw hd hp h₁ h₂ hnsize hc hlt he₂

theorem designCallReadStored_complete {xs : List ℕ} {o : RawDesignReadOut}
    (ho : (xs,o) ∈ designCallReadFamily r) :
    let Y := X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o) (designReadMathHint e₂ o)
    let out := designStored ((w,d),designCase3Graph (r,o))
    ∃ name : Y.Vtx → ℕ,
      SbipGraphColorNames Y out.1 name ∧ SbipStoredDictionary Y point out name ∧
      (∀ x, labAt out.1.2.1 (point x) = Y.f x) ∧ (sbipGraphVertices out.1).Nodup ∧
      (∀ A, name A ∈ out.1.1.1 ↔ ∃ x, Y.part₁ x ∧ A.val = {x}) ∧
      (∀ A, name A ∈ out.1.1.2.1 ↔ A.val ∈ Y.blocks) ∧
      (∀ a, a ∈ sbipGraphVertices out.1 ↔ ∃ A, name A = a) := by
  obtain ⟨hnd,hL⟩ := designCallReadFirst_names r ho
  exact designStored_complete hn hw point d e hd hp h₁ h₂ hnsize hc w hlt
    (designReadSelectedSet r name₂ o) (designReadMathHint e₂ o)
    (designReadSelected (r,o)) (designReadNamedHint (r,o))
    (designReadSelected_nodup hw o hnd hL) (designReadSelected_sub r o hL)
    (fun B => (designReadSelectedSet_mem o B).symm)
    (designReadGraph_hint hn hw e₂ he₂ o)

end
end Algo
