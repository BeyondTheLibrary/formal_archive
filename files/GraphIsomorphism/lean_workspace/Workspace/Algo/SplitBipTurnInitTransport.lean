import Workspace.Algo.SplitBipTurnDesignReturnFamily
import Workspace.Algo.SplitBipTurnCaseTransport
import Workspace.Algo.SplitBipTurnImpPartition
import Workspace.Algo.SplitBipTurnUpccPartition

/-! Every immediate return of the literal turn has its matching return at
an isomorphic represented node. Early exits were handled before; here the
three Step 9 branches are dispatched by their computed tag, which agrees
at isomorphic parents.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

/-- When no early exit fires, the turn is exactly the Step 9 dispatch. -/
theorem sbipTurn_eq_cases (c : ℕ) (I : RawSbipNode) (hne : ¬ SbipTurnEarly c I) :
    sbipTurn c I.1 = sbipTurnCases (sbipTurnCase I.1) := by
  simp only [SbipTurnEarly,not_or] at hne
  obtain ⟨h1,h2,h4,h6⟩ := hne
  unfold sbipTurn
  rw [if_neg h1,if_neg h2]
  unfold sbipTurnLarge
  cases hh : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
  | none => exact (h4 hh).elim
  | some a =>
    simp only [Option.elim_some,sbipTurnAfter35,if_neg h6]

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h

/-- Past the early exits, the paper's Step 6 test has failed. -/
theorem not_step6_of_not_early (c : ℕ) (hne : ¬ SbipTurnEarly c I) :
    ¬ AllClassesSmall X ∧ ¬ Step6Imprimitive X := by
  simp only [SbipTurnEarly,not_or] at hne
  obtain ⟨_,_,h4,h6⟩ := hne
  have hd := h.dominant_of_continue h4
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  exact ⟨hd,fun hh => h6 ((sbipGraphComponentTable_test X (sbipTurnGraphInput I.1) name hc hnd
    e he hp hr h.alpha h.denominator h.left_nodup hd).2 hh)⟩

include h' hφ

/-- Sec. 9.4, step 9: every return of the Step 9 dispatch (ImprimitiveCase,
DesignCase, or UPCC case) has its matching return at an isomorphic parent. -/
theorem cases_return_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnCases (sbipTurnCase I.1)) :
    ∃ o',(o',none) ∈ sbipTurnCases (sbipTurnCase J.1) ∧ SbipNamedOutcomeIso I J X Y φ o o' := by
  have hs := h.case_spec hd
  have ht := h.case_tag_transport h' φ hφ hd
  unfold sbipTurnCases at hout ⊢
  rw [← ht]
  split at hout
  next hi =>
    rw [if_pos hi]
    exact h.imp_return_transport h' φ hφ hd h6 (hs.1.1 hi) o hout
  next hi =>
    rw [if_neg hi]
    split at hout
    next hcl =>
      rw [if_pos hcl]
      exact h.design_return_transport h' φ hφ hd h6 (hs.2.1.1 hcl).2 o hout
    next hcl =>
      rw [if_neg hcl]
      have hi' : ¬ Step9Imprimitive X := fun hh => hi (hs.1.2 hh)
      have hcl' : ¬ Step9Clique X := fun hh => hcl (hs.2.1.2 ⟨hi',hh⟩)
      exact h.upcc_return_transport h' φ hφ hd h6 hi' hcl' o hout

/-- Sec. 9.4: every immediate return of the actual turn (the early exits of
steps 1, 2, 4, 6, and the Step 9 case returns) has its matching return at
an isomorphic represented node. -/
theorem init_transport (c : ℕ) (o : RawAlignOutcome) (hout : o ∈ sbipNodeInit c I) :
    ∃ o' ∈ sbipNodeInit c J,SbipNamedOutcomeIso I J X Y φ o o' := by
  by_cases hearly : SbipTurnEarly c I
  · exact h.early_init_transport h' φ hφ c hearly o hout
  have hearly' : ¬ SbipTurnEarly c J := fun hh => hearly
    (h'.early_of_iso h φ.symm ((BipBlockInputs (Fin m)).symm_mem hφ) c hh)
  obtain ⟨hd,h6⟩ := h.not_step6_of_not_early c hearly
  have hout' := (sbipTurnReturns_mem (sbipTurn c I.1) o).1 hout
  rw [sbipTurn_eq_cases c I hearly] at hout'
  obtain ⟨o',ho',hiso⟩ := h.cases_return_transport h' φ hφ hd h6 o hout'
  refine ⟨o',(sbipTurnReturns_mem _ o').2 ?_,hiso⟩
  rw [sbipTurn_eq_cases c J hearly']
  exact ho'

end SbipNodeRep
end Algo
