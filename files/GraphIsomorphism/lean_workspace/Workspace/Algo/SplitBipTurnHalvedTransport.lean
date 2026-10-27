import Workspace.Algo.SplitBipTurnCaseTransport

/-! Attach the computed next threshold to a specific halved graph.
Keeping the graph explicit lets its isomorphism pass directly to the
recursive input, without choosing a different semantic representative.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem halved_child_rep {t : Set (Fin m)} (Y : VColBipBlk ↥t ℕ) (g : RawSbipStored)
    (hs : SbipStoredRep Y (fun x => x.val.val) g)
    (hV : Subtype.val '' Y.V₁ = step8V₁ X)
    (hhalf : 2 * Y.numBlocks ≤ step8NumBlocks X)
    (hdef : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      1/2 ≤ Y.defect₁) :
    letI : Fintype ↥t := Fintype.ofFinite _
    letI : DecidableEq ↥t := Classical.decEq _
    ∃ hadm : Y.IsThm922Input (alphaNew X),
      SbipNodeRep m (sbipNodeMakeChild (I,g))
        ⟨t,⟨(Y,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  have hadm := isThm922Input_of_halved Y (twothirds_le_alphaNew hd) hV
    (two_le_step8V₁_ncard hd) (step8NumBlocks_lt hd) hhalf hdef
  refine ⟨hadm,h.ground,hs,h.case_alpha hd,h.case_denominator hd,?_⟩
  have hcount := sbipStoredRep_block_count hs
  have hsmall : g.1.1.2.1.length < sbipNodeBlocks I := by
    rw [hcount,h.block_count]
    have hle := step8NumBlocks_le X
    have hpos := two_le_numBlocks_of_step9 hd
    omega
  have hmajor : 10 * g.1.1.2.1.length ≤ 9 * sbipNodeBlocks I := by
    rw [hcount,h.block_count]
    have hh := step8NumBlocks_le X
    omega
  intro hz
  simp [sbipNodeBit,sbipNodeMakeChild,hsmall,hmajor] at hz

end SbipNodeRep
end Algo
