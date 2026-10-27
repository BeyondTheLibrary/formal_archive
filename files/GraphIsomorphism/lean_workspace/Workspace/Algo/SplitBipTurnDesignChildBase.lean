import Workspace.Algo.SplitBipTurnChild
import Workspace.Algo.SplitDesignStoredTie
import Workspace.Algo.SplitDesignCallProgress
import Workspace.Algo.SplitDesignCase3Defect
import Workspace.SplitOrJohnson.Step9Design

/-! DesignCase may keep the number of blocks only when it supplies the
paper's hint. A parent that already carries the hint has halved its blocks
before reaching DesignCase, so every such call passes the strict raw measure.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem design_child {t : Set (Fin m)} (hcl : Step9Clique X)
    (Y : VColBipBlk ↥t ℕ) (g : RawSbipStored)
    (hs : SbipStoredRep Y (fun x => x.val.val) g)
    (hV : Subtype.val '' Y.V₁ = step8V₁ X)
    (hadm : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      Y.IsThm922Input (alphaNew X))
    (hprogress : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      10 * Y.numBlocks ≤ 9 * step8NumBlocks X ∨
        (Y.numBlocks ≤ step8NumBlocks X ∧ Y.HasHint)) :
    SbipChildGood I X g := by
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  let Z : Pt (BipBlockInputs (Fin m)) :=
    ⟨t,⟨(Y,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩
  have hcount := sbipStoredRep_block_count hs
  have hparent := h.block_count
  have hsteps := step8NumBlocks_le X
  have hpos := two_le_numBlocks_of_step9 hd
  have hle : Y.numBlocks ≤ step8NumBlocks X := hprogress.elim (by omega) And.left
  have hrawle : g.1.1.2.1.length ≤ sbipNodeBlocks I := by omega
  have hnh : ¬ (g.1.1.2.1.length < sbipNodeBlocks I ∧
      10 * g.1.1.2.1.length ≤ 9 * sbipNodeBlocks I) → Y.HasHint := by
    intro hnot
    rcases hprogress with hshrink | hh
    · exact False.elim (hnot ⟨by omega,by omega⟩)
    · exact hh.2
  have hrep : SbipNodeRep m (sbipNodeMakeChild (I,g)) Z := by
    refine ⟨h.ground,hs,h.case_alpha hd,h.case_denominator hd,?_⟩
    intro hz
    apply hnh
    intro hlt
    simp [sbipNodeBit,sbipNodeMakeChild,hlt] at hz
  refine ⟨Z,hrep,hV,rfl,?_,?_,?_⟩
  · change 10 * Y.numBlocks ≤ 9 * BipBlockInputs.numBlocks X ∨
      (Y.numBlocks ≤ BipBlockInputs.numBlocks X ∧ Y.HasHint)
    exact hprogress.elim (fun hh => Or.inl (by omega))
      (fun hh => Or.inr ⟨by omega,hh.2⟩)
  · by_cases hmajor : 10 * g.1.1.2.1.length ≤ 9 * sbipNodeBlocks I
    · exact Or.inl ⟨by omega,hmajor⟩
    · refine Or.inr ⟨hrawle,?_,?_⟩
      · have hnzero : sbipNodeBit I ≠ 0 := by
          intro hz
          have hhalf := two_mul_step8NumBlocks_le_of_hint X hd hcl (h.hint hz)
          omega
        by_cases hz : I.2 = 0
        · exact False.elim (hnzero (by simp [sbipNodeBit,hz]))
        · simp [sbipNodeBit,hz]
      · simp [sbipNodeBit,sbipNodeMakeChild,hmajor]
  · apply sbipNodeAdmit_eq
    by_cases hlt : g.1.1.2.1.length < sbipNodeBlocks I
    · exact sbipNodeMakeChild_lt_of_drop I g hlt
    · have heq : g.1.1.2.1.length = sbipNodeBlocks I := by omega
      apply sbipNodeMakeChild_lt_of_equal I g heq
      have hnzero : sbipNodeBit I ≠ 0 := by
        intro hz
        have hhalf := two_mul_step8NumBlocks_le_of_hint X hd hcl (h.hint hz)
        omega
      by_cases hz : I.2 = 0
      · exact False.elim (hnzero (by simp [sbipNodeBit,hz]))
      · simp [sbipNodeBit,hz]

/-- The actual restricted link has the same first part and updated threshold.
The absolute defect from Reduce-Part2-by-Color supplies admissibility. -/
theorem design_restricted_child (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (S : Set (Set ↥(step7Set X))) (c : Set ↥(step7Set X) → Set ↥(step7Set X) → ℕ)
    (g : RawSbipStored)
    (hs : SbipStoredRep ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c)
      (fun x => x.val.val) g)
    (hS : S ⊆ (step9DesignObj X hd h6 hcl).blocks)
    (hdef : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      (((step9DesignObj X hd h6 hcl).n₁ : ℚ) - 1) / 2 ≤
        ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlk S).symDefect₁)
    (hprogress : letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
      letI : DecidableEq ↥(step7Set X) := Classical.decEq _
      10 * S.ncard ≤ 9 * step8NumBlocks X ∨
        (S.ncard ≤ step8NumBlocks X ∧
          ((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint S c).HasHint)) :
    SbipChildGood I X g := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  let U : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(step9DesignObj X hd h6 hcl,alphaNew X),twothirds_le_alphaNew hd,
      alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt := BlkBlockDesignInputs.numBlocks_lt_n₁ U
  have h3 : 3 ≤ (step9DesignObj X hd h6 hcl).n₁ := by
    have hh := two_le_step8NumBlocks hd
    change step8NumBlocks X < (step9DesignObj X hd h6 hcl).n₁ at hlt
    omega
  apply h.design_child hd hcl _ g hs rfl
  · exact (restrictObjHint_pred U c hS h3 hdef).2.2
  · rwa [VColBipBlk.restrictBlkHint_numBlocks
      (X := (step9DesignObj X hd h6 hcl).linkGraph) hS]

end SbipNodeRep
end Algo
