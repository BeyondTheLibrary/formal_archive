import Workspace.Algo.SplitDesignStoredActual
import Workspace.Algo.SplitDesignCase12Spec

/-! The tied twin classes retain every block and the twin hint. Its
padding is zero on pairs meeting the first part, just as in the graph.
The other Case 2 graph has the original zero hint. -/
namespace Algo
open Babai RAM
open scoped Classical

theorem designTwinHint_off (r : RawUpccCase) (a b : ℕ)
    (h : a ∉ r.2.2 ∨ b ∉ r.2.2) : binColor (designTwinHint r,(a,b)) = 0 := by
  have hh : (designTwinHint r).2.lookup [a,b] = none := by
    apply List.lookup_eq_none_iff.2
    intro p hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.1 hp
    simp only [designTwinHintRow,bne_iff_ne]
    intro he
    subst t
    have hm := (mem_tuplesOf _ _ _).1 ht |>.2
    exact h.elim (fun ha => ha (hm a (by simp))) (fun hb => hb (hm b (by simp)))
  change ((designTwinHint r).2.lookup [a,b]).getD 0 = 0
  rw [hh]
  rfl

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (hn : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include hn hw he₁ he₂

theorem designTieStored_hint (A B : (X.linkGraph.restrictBlkHint X.blocks X.twinHint).Vtx) :
    binColor (designTwinHint r,
      (designGraphName (name₁ := name₁) (name₂ := name₂) X.blocks X.twinHint A,
       designGraphName (name₁ := name₁) (name₂ := name₂) X.blocks X.twinHint B)) =
      (X.linkGraph.restrictBlkHint X.blocks X.twinHint).h A.val B.val := by
  rcases A with ⟨A,hA⟩
  rcases B with ⟨B,hB⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · have hxb : ({x} : Set ↥s) ∉ (X.linkGraph.restrictBlkHint X.blocks X.twinHint).blocks :=
      fun hh => X.blocks_off₁ _ hh.1 x rfl hx
    have hxn : name₁ ⟨x,hx⟩ ∉ r.2.2 := fun hh => hw.disjoint _ ((hn.left _).2 ⟨_,rfl⟩) hh
    rw [designGraphName_point _ _ ⟨x,hx⟩,designTwinHint_off _ _ _ (Or.inl hxn)]
    exact ((X.linkGraph.restrictBlkHint X.blocks X.twinHint).h_off _ _ (Or.inl hxb)).symm
  · rcases hB with ⟨y,hy,rfl⟩ | hB
    · have hyb : ({y} : Set ↥s) ∉ (X.linkGraph.restrictBlkHint X.blocks X.twinHint).blocks :=
        fun hh => X.blocks_off₁ _ hh.1 y rfl hy
      have hyn : name₁ ⟨y,hy⟩ ∉ r.2.2 := fun hh => hw.disjoint _ ((hn.left _).2 ⟨_,rfl⟩) hh
      rw [designGraphName_point _ _ ⟨y,hy⟩,designTwinHint_off _ _ _ (Or.inr hyn)]
      exact ((X.linkGraph.restrictBlkHint X.blocks X.twinHint).h_off _ _ (Or.inr hyb)).symm
    · rw [designGraphName_block _ _ ⟨A,hA.1⟩ hA.2,
        designGraphName_block _ _ ⟨B,hB.1⟩ hB.2,
        designTwinHint_spec hn e₁ he₁ e₂ he₂ hw.right_nodup,
        VColBipBlk.restrictBlkHint_h hA hB]

end

section Actual
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

theorem designTieStored_complete :
    SbipStoredRep (X.linkGraph.restrictBlkHint X.blocks X.twinHint) point
      (designStored ((w,d),designTieGraph r)) := by
  obtain ⟨e₁,he₁⟩ := designStored_point_equiv_exists hn hw
  exact designStored_complete hn hw point d e hd hp h₁ h₂ hnsize hc w hlt
    X.blocks X.twinHint r.2.2 (designTwinHint r) hw.right_nodup (fun _ ha => ha)
    (fun B => iff_of_true ((hn.right _).2 ⟨B,rfl⟩) B.property)
    (designTieStored_hint hn hw e₁ he₁ e₂ he₂)

omit hn hw hd hp h₁ h₂ hnsize hc hlt he₂ in
theorem designLinkGraph_zero_hint (S : Set (Set ↥s)) :
    X.linkGraph.restrictBlkHint S (fun _ _ => 0) = X.linkGraph.restrictBlk S := by
  simp only [VColBipBlk.restrictBlkHint,VColBipBlk.restrictBlk,BlkCaseObj.linkGraph,ite_self]

theorem designOtherStored_complete :
    SbipStoredRep (X.linkGraph.restrictBlk (X.blocks \ X.bigTwin)) point
      (designStored ((w,d),designOtherGraph r)) := by
  obtain ⟨e₁,he₁⟩ := designStored_point_equiv_exists hn hw
  rw [← designLinkGraph_zero_hint (X := X)]
  apply designStored_complete hn hw point d e hd hp h₁ h₂ hnsize hc w hlt
    (X.blocks \ X.bigTwin) (fun _ _ => 0) (designOtherNames r) ([],[])
    (designOtherNames_nodup hw) (fun _ ha => designOtherNames_sub ha)
    (designOtherNames_mem hn e₁ he₁ e₂ he₂)
  intro A B
  simp [binColor,tblGet,VColBipBlk.restrictBlkHint]

end Actual
end Algo
