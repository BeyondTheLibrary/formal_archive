import Workspace.Algo.SplitBipTurnReturns
import Workspace.Algo.SplitImprimitiveStoredBridge
import Workspace.Algo.SplitUpccStoredBridge

/-! The graph returned by a case becomes the next raw node. Its stored
representation determines the number of blocks. The next stage bit is
computed from that count, and every valid paper call passes admission.
-/
namespace Algo
open Babai RAM
open scoped Classical

theorem sbipStoredRep_block_count {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {G : VColBipBlk ↥s ℕ} {point : ↥s → ℕ} {z : RawSbipStored}
    (h : SbipStoredRep G point z) : z.1.1.2.1.length = G.numBlocks := by
  obtain ⟨name,hc,hd,hf,hnd,hl,hr,hcover⟩ := h
  have hm (a : ℕ) : a ∈ z.1.1.2.1 ↔ ∃ B : ↥G.blocks,name ⟨B.val,Or.inr B.property⟩ = a := by
    constructor
    · intro ha
      obtain ⟨A,hA⟩ := (hcover a).1 (List.mem_append_right _ ha)
      exact ⟨⟨A.val,(hr A).1 (hA ▸ ha)⟩,hA⟩
    · rintro ⟨B,rfl⟩
      exact (hr _).2 B.property
  obtain ⟨e,_⟩ := splitNameEquiv_exists (fun B : ↥G.blocks => name ⟨B.val,Or.inr B.property⟩) (fun B C he =>
    Subtype.ext (congrArg (fun A : G.Vtx => A.val) (hc.injective he))) _
    (List.nodup_append.1 hnd).2.1 hm
  simpa only [Nat.card_coe_set_eq,Nat.card_fin] using (Nat.card_congr e).symm

/-- The local first part and updated threshold are retained with every
recursive answer, so each level performs its own complement extension. -/
def SbipChildGood {m : ℕ} (I : RawSbipNode) (X : Pt (BipBlockInputs (Fin m)))
    (g : RawSbipStored) : Prop :=
  ∃ Y : Pt (BipBlockInputs (Fin m)),
    SbipNodeRep m (sbipNodeMakeChild (I,g)) Y ∧
    BipBlockInputs.V₁ Y = step8V₁ X ∧ BipBlockInputs.alpha Y = alphaNew X ∧
    (10 * BipBlockInputs.numBlocks Y ≤ 9 * BipBlockInputs.numBlocks X ∨
      (BipBlockInputs.numBlocks Y ≤ BipBlockInputs.numBlocks X ∧ Y.obj.1.1.HasHint)) ∧
    ((0 < sbipNodeBlocks I ∧
        10 * sbipNodeBlocks (sbipNodeMakeChild (I,g)) ≤ 9 * sbipNodeBlocks I) ∨
      (sbipNodeBlocks (sbipNodeMakeChild (I,g)) ≤ sbipNodeBlocks I ∧
        sbipNodeBit I = 1 ∧ sbipNodeBit (sbipNodeMakeChild (I,g)) = 0)) ∧
    sbipNodeAdmit (I,g) = some (sbipNodeMakeChild (I,g))

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem halved_child {t : Set (Fin m)} (Y : VColBipBlk ↥t ℕ) (g : RawSbipStored)
    (hs : SbipStoredRep Y (fun x => x.val.val) g)
    (hV : Subtype.val '' Y.V₁ = step8V₁ X)
    (hhalf : 2 * Y.numBlocks ≤ step8NumBlocks X)
    (hdef : letI : Fintype ↥t := Fintype.ofFinite _
      letI : DecidableEq ↥t := Classical.decEq _
      1/2 ≤ Y.defect₁) :
    SbipChildGood I X g := by
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  have hadm := isThm922Input_of_halved Y (twothirds_le_alphaNew hd) hV
    (two_le_step8V₁_ncard hd) (step8NumBlocks_lt hd) hhalf hdef
  let Z : Pt (BipBlockInputs (Fin m)) :=
    ⟨t,⟨(Y,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩
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
  have hrep : SbipNodeRep m (sbipNodeMakeChild (I,g)) Z := by
    refine ⟨h.ground,hs,h.case_alpha hd,h.case_denominator hd,?_⟩
    intro hz
    simp [sbipNodeBit,sbipNodeMakeChild,hsmall,hmajor] at hz
  refine ⟨Z,hrep,hV,rfl,Or.inl ?_,Or.inl ⟨?_,hmajor⟩,sbipNodeAdmit_eq I g
    (sbipNodeMakeChild_lt_of_drop I g hsmall)⟩
  · change 10 * Y.numBlocks ≤ 9 * BipBlockInputs.numBlocks X
    have hh := step8NumBlocks_le X
    omega
  · rw [h.block_count]
    exact lt_of_lt_of_le (by omega : 0 < 2) (two_le_numBlocks_of_step9 hd)

end SbipNodeRep
end Algo
