import Workspace.Algo.SplitBipTurnDecode
import Workspace.Algo.SplitBipGraphEarly1
import Workspace.Algo.SplitBipGraphEarly2
import Workspace.Algo.SplitBipGraphEarly4

/-! The stored node invariant supplies every hypothesis of the actual
early exits. This file connects their positional bounds to the common
named outcome decoder used by the recursive family.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem early1_good (c : ℕ) (hsmall : sbipGraphSmall1 c I.1.2.1.1 = true)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly1 c (sbipTurnGraphInput I.1)) :
    SbipReturnGood I X (rawAlignPartition q) := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e₁,_⟩ := sbipGraphEarly_point_equiv_exists X I.1.2.1.1 name hc hp h.left_nodup
  apply h.partition_good
  exact sbipGraphEarly1_valid X (sbipTurnGraphInput I.1) e₁ h.alpha
    (by simpa only [sbipGraphSmall1,decide_eq_true_eq] using hsmall) q hq

theorem early2_good (c : ℕ) (hsmall : sbipGraphSmall2 c I.1.2.1.1 = true)
    (q : RawColPart) (hq : q ∈ sbipGraphEarly2 (c+1) I.1.2.1.1) :
    SbipReturnGood I X (rawAlignPartition q) := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e₁,he₁⟩ := sbipGraphEarly_point_equiv_exists X I.1.2.1.1 name hc hp h.left_nodup
  obtain ⟨e₂,he₂⟩ := sbipGraphEarly_block_equiv_exists X I.1.2.1.1 name hc hr h.right_nodup
  apply h.partition_good
  exact sbipGraphEarly2_valid X I.1.2.1.1 name hc h.left_nodup h.right_nodup e₁ e₂ he₁ he₂
    (by simpa only [sbipGraphSmall2,decide_eq_true_eq] using hsmall) q hq

theorem early4_good (hexit : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 = none) :
    SbipReturnGood I X (rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput I.1))) := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  apply h.partition_good
  exact sbipGraphEarly4_valid X (sbipTurnGraphInput I.1) name hc hnd e he hp
    h.alpha h.denominator h.left_nodup hexit

theorem dominant_of_continue
    (hexit : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 ≠ none) : ¬ AllClassesSmall X := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  exact fun hh => hexit ((sbipGraphSteps35_exit_iff X (sbipTurnGraphInput I.1) name hc hnd e he hp
    h.alpha h.denominator h.left_nodup).2 hh)

theorem component_good (hd : ¬ AllClassesSmall X)
    (hi : sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput I.1)) = true) :
    SbipReturnGood I X (rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput I.1))) := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  have hi' := (sbipGraphComponentTable_test X (sbipTurnGraphInput I.1) name hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd).1 hi
  apply h.partition_good
  exact sbipGraphComponentPartition_valid X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd hi'

end SbipNodeRep
end Algo
