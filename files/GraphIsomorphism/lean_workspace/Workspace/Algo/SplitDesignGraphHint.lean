import Workspace.Algo.SplitDesignGraphNames
import Workspace.Algo.SplitDesignHintValidity

/-! The complete stored hint table agrees on every pair of vertices.
Pairs meeting the first part have color zero, as required by the graph. -/
namespace Algo
open Babai RAM

theorem designReadNamedHint_off (z : RawUpccCase × RawDesignReadOut) (a b : ℕ)
    (h : a ∉ z.1.2.2 ∨ b ∉ z.1.2.2) :
    binColor (designReadNamedHint z,(a,b)) = 0 := by
  have hh : (designReadNamedHint z).2.lookup [a,b] = none := by
    apply List.lookup_eq_none_iff.2
    intro p hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.1 hp
    simp only [designReadNamedHintRow,bne_iff_ne]
    intro he
    subst t
    have hm := (mem_tuplesOf _ _ _).1 ht |>.2
    exact h.elim (fun ha => ha (hm a (by simp))) (fun hb => hb (hm b (by simp)))
  change ((designReadNamedHint z).2.lookup [a,b]).getD 0 = 0
  rw [hh]
  rfl

theorem designReadSelected_sub (r : RawUpccCase) (o : RawDesignReadOut)
    (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    ∀ a ∈ designReadSelected (r,o), a ∈ r.2.2 := by
  unfold designReadSelected
  split
  · exact designReadNamedFirst_sub o hL
  · intro a ha
    exact List.mem_of_mem_filter ha

theorem designReadSelected_nodup {r : RawUpccCase} (hw : r.WF) (o : RawDesignReadOut)
    (hnd : (designReadFirst o).Nodup) (hL : ∀ i ∈ designReadFirst o, i < r.2.2.length) :
    (designReadSelected (r,o)).Nodup := by
  unfold designReadSelected
  split
  · exact designReadNamedFirst_nodup hw o hnd hL
  · exact hw.right_nodup.filter _

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h hw he₂

open scoped Classical in
theorem designReadGraph_hint (o : RawDesignReadOut)
    (A B : (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
      (designReadMathHint e₂ o)).Vtx) :
    binColor (designReadNamedHint (r,o),
      (designGraphName (name₁ := name₁) (name₂ := name₂) _ _ A,
       designGraphName (name₁ := name₁) (name₂ := name₂) _ _ B)) =
      (X.linkGraph.restrictBlkHint (designReadSelectedSet r name₂ o)
        (designReadMathHint e₂ o)).h A.val B.val := by
  classical
  let S := designReadSelectedSet r name₂ o
  let H := designReadMathHint e₂ o
  rcases A with ⟨A,hA⟩
  rcases B with ⟨B,hB⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · have hxb : ({x} : Set ↥s) ∉ (X.linkGraph.restrictBlkHint S H).blocks :=
      fun hh => X.blocks_off₁ _ hh.1 _ (Set.mem_singleton _) hx
    have hxn : name₁ ⟨x,hx⟩ ∉ r.2.2 :=
      fun hh => hw.disjoint _ ((h.left _).2 ⟨_,rfl⟩) hh
    rw [designGraphName_point _ _ ⟨x,hx⟩,
      designReadNamedHint_off _ _ _ (Or.inl hxn)]
    exact ((X.linkGraph.restrictBlkHint S H).h_off _ _ (Or.inl hxb)).symm
  · rcases hB with ⟨y,hy,rfl⟩ | hB
    · have hyb : ({y} : Set ↥s) ∉ (X.linkGraph.restrictBlkHint S H).blocks :=
        fun hh => X.blocks_off₁ _ hh.1 _ (Set.mem_singleton _) hy
      have hyn : name₁ ⟨y,hy⟩ ∉ r.2.2 :=
        fun hh => hw.disjoint _ ((h.left _).2 ⟨_,rfl⟩) hh
      rw [designGraphName_point _ _ ⟨y,hy⟩,
        designReadNamedHint_off _ _ _ (Or.inr hyn)]
      exact ((X.linkGraph.restrictBlkHint S H).h_off _ _ (Or.inr hyb)).symm
    · rw [designGraphName_block _ _ ⟨A,hA.1⟩ hA.2,
        designGraphName_block _ _ ⟨B,hB.1⟩ hB.2,
        designReadNamedHint_spec h hw e₂ he₂ o ⟨A,hA.1⟩ ⟨B,hB.1⟩]
      rw [VColBipBlk.restrictBlkHint_h hA hB,designReadMathHint_on e₂ o ⟨A,hA.1⟩ ⟨B,hB.1⟩]

end
end Algo
