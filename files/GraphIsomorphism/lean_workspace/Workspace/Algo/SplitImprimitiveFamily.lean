import Workspace.Algo.SplitImprimitiveInput

/-! # Section 9.6: exact coverage of the paper's choices

A good output alone does not show that the chosen family follows the paper.
Here both directions are checked against the ordered branches: all block
choices in step 1, and only the selected graphs in step 2.
-/
namespace Algo
open Babai RAM

section Family
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s)

open scoped Classical in
/-- The family prescribed by steps 1 and 2 of Procedure ImprimitiveCase. -/
def ImpPaperOutcome (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))) : Prop :=
  if ImprimitiveSplits X then
    ∃ B : ↥X.blocks, Z = ⟨Subtype.val '' X.Pt₁,
      Sum.inl (kerPartition X.Pt₁ (fun x => X.c {x} B.val))⟩
  else
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ∃ Y : VColBipBlk ↥s ℕ, Z = ⟨s,Sum.inr Y⟩ ∧
      Y ∈ X.step2Cands ∧ 1 / 2 ≤ Y.defect₁ ∧
      (X.hasGoodBlock → Y ∈ X.blkZ '' X.groups)

variable {X} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)
    (hleft : r.2.1.Nodup) (hright : r.2.2.Nodup)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h hleft hright he₁ he₂

/-- Each returned version follows the corresponding mathematical branch. -/
theorem impCase_paper (q : RawImpOutcome) (hq : q ∈ impCase r) :
    ∃ Z, ImpOutcomeRep X name₁ name₂ r e₁ q Z ∧ ImpPaperOutcome X Z := by
  classical
  unfold impCase at hq
  split at hq
  next hs =>
    obtain ⟨b,hb,rfl⟩ := List.mem_map.1 hq
    obtain ⟨B,rfl⟩ := (h.right _).1 hb
    refine ⟨_,impSplit_rep h e₁ he₁ B,?_⟩
    rw [ImpPaperOutcome,if_pos ((impSplits_spec h hleft).1 hs)]
    exact ⟨B,rfl⟩
  next hs =>
    obtain ⟨g,hg,rfl⟩ := List.mem_map.1 hq
    have hn : ¬ ImprimitiveSplits X := fun hx => hs ((impSplits_spec h hleft).2 hx)
    obtain ⟨Y,hrep,hY,hdef,hbranch,_⟩ := impStep2Graphs_spec h hleft hright e₂ he₂ hn g hg
    refine ⟨⟨s,Sum.inr Y⟩,⟨rfl,Y,rfl,hrep⟩,?_⟩
    rw [ImpPaperOutcome,if_neg hn]
    exact ⟨Y,rfl,hY,hdef,hbranch⟩

/-- Every mathematical choice in the paper's selected branch is represented. -/
theorem impCase_complete (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)))
    (hZ : ImpPaperOutcome X Z) :
    ∃ q ∈ impCase r, ImpOutcomeRep X name₁ name₂ r e₁ q Z := by
  classical
  by_cases hs : ImprimitiveSplits X
  · rw [ImpPaperOutcome,if_pos hs] at hZ
    obtain ⟨B,rfl⟩ := hZ
    refine ⟨(impSplitLab (r,name₂ B),none),?_,impSplit_rep h e₁ he₁ B⟩
    rw [impCase,if_pos ((impSplits_spec h hleft).2 hs)]
    exact List.mem_map.2 ⟨_,(h.right _).2 ⟨B,rfl⟩,rfl⟩
  · rw [ImpPaperOutcome,if_neg hs] at hZ
    obtain ⟨Y,rfl,hY,hdef,hbranch⟩ := hZ
    obtain ⟨q,hq,hrep⟩ := impStep2Graphs_covers h hleft hright e₂ he₂ Y hY hdef hbranch
    refine ⟨([],some q),?_,rfl,Y,rfl,hrep⟩
    rw [impCase,if_neg (fun hh => hs ((impSplits_spec h hleft).1 hh))]
    exact List.mem_map.2 ⟨q,hq,rfl⟩

end Family
end Algo
