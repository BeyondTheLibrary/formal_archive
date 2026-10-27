import Workspace.Algo.SplitBipTurnDesignReturn

/-! Every immediate outcome of the literal unified turn decodes to a
valid paper outcome on the current parent first part.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem cases_return_good (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnCases (sbipTurnCase I.1)) :
    SbipReturnGood I X o := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hcases := sbipGraphStep9Input_case X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9
  unfold sbipTurnCases at hout
  split at hout
  next hi => exact h.imp_return_good hd h6 (hcases.1.1 hi) o hout
  next hi =>
    split at hout
    next hcl => exact h.design_return_good hd h6 (hcases.2.1.1 hcl).2 o hout
    next hcl =>
      have hi' : ¬ Step9Imprimitive X := fun hh => hi (hcases.1.2 hh)
      have hcl' : ¬ Step9Clique X := fun hh => hcl (hcases.2.1.2 ⟨hi',hh⟩)
      exact h.upcc_return_good hd h6 hi' hcl' o hout

theorem after35_return_good (hd : ¬ AllClassesSmall X)
    (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnAfter35 I.1) :
    SbipReturnGood I X o := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  unfold sbipTurnAfter35 at hout
  split at hout
  next hi =>
    have ho := List.mem_singleton.1 hout
    have ho' := congrArg Prod.fst ho
    change o = rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput I.1)) at ho'
    rw [ho']
    exact h.component_good hd hi
  next hi =>
    apply h.cases_return_good hd _ o hout
    exact fun hh => hi ((sbipGraphComponentTable_test X (sbipTurnGraphInput I.1) name hc hnd e he hp hr
      h.alpha h.denominator h.left_nodup hd).2 hh)

theorem large_return_good (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnLarge I.1) :
    SbipReturnGood I X o := by
  unfold sbipTurnLarge at hout
  cases he : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
  | none =>
    simp only [he,Option.elim_none,List.mem_singleton] at hout
    have ho := congrArg Prod.fst hout
    change o = rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput I.1)) at ho
    rw [ho]
    exact h.early4_good he
  | some q =>
    simp only [he,Option.elim_some] at hout
    exact h.after35_return_good (h.dominant_of_continue (by rw [he]; simp)) o hout

theorem turn_return_good (c : ℕ) (o : RawAlignOutcome)
    (hout : (o,none) ∈ sbipTurn c I.1) : SbipReturnGood I X o := by
  unfold sbipTurn at hout
  split at hout
  next hsmall =>
    obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
    have ho' := congrArg Prod.fst ho
    change rawAlignPartition q = o at ho'
    rw [← ho']
    exact h.early1_good c hsmall q hq
  next hlarge =>
    split at hout
    next hsmall =>
      obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
      have ho' := congrArg Prod.fst ho
      change rawAlignPartition q = o at ho'
      rw [← ho']
      exact h.early2_good c hsmall q hq
    next hlarge' => exact h.large_return_good o hout

end SbipNodeRep

theorem sbipNodeInit_good (m c : ℕ) (I : RawSbipNode) :
    SbipAnswersGood m I (sbipNodeInit c I) := by
  intro X h o ho
  exact h.turn_return_good c o ((sbipTurnReturns_mem _ o).1 ho)

end Algo
