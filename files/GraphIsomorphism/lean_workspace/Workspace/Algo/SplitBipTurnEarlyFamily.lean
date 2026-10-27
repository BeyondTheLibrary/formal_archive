import Workspace.Algo.SplitBipTurnBranchTransport

/-! Every answer of a turn that exits before Step 9 has its matching
answer at an isomorphic input. The proof follows the actual test order,
so an earlier exit cannot be replaced by a later compatible partition.
-/
namespace Algo
open Babai RAM
open scoped Classical

/-- The actual turn reaches one of its four early exits. -/
def SbipTurnEarly (c : ℕ) (I : RawSbipNode) : Prop :=
  sbipGraphSmall1 c I.1.2.1.1 = true ∨ sbipGraphSmall2 c I.1.2.1.1 = true ∨
    (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 = none ∨
    sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput I.1)) = true

private theorem sbipTurnChildren_map_partition (L : List RawColPart) :
    sbipTurnChildren (L.map sbipTurnPartition) = [] := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simpa only [List.map_cons,sbipTurnChildren,List.filter_cons,
      sbipTurnIsReturn,sbipTurnPartition,sbipTurnReturn,Option.elim_none,
      Bool.not_true,Bool.false_eq_true,reduceIte] using ih

theorem sbipNodeGraphs_eq_nil_of_early (c : ℕ) (I : RawSbipNode)
    (hearly : SbipTurnEarly c I) : sbipNodeGraphs c I = [] := by
  unfold sbipNodeGraphs sbipTurn
  by_cases h1 : sbipGraphSmall1 c I.1.2.1.1 = true
  · rw [if_pos h1]
    exact sbipTurnChildren_map_partition _
  rw [if_neg h1]
  by_cases h2 : sbipGraphSmall2 c I.1.2.1.1 = true
  · rw [if_pos h2]
    exact sbipTurnChildren_map_partition _
  rw [if_neg h2]
  cases h4 : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
  | none =>
    simp [sbipTurnLarge,h4,sbipTurnChildren,sbipTurnIsReturn,sbipTurnPartition,sbipTurnReturn]
  | some a =>
    have h6 : sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput I.1)) = true := by
      rcases hearly with hh | hh | hh | hh
      · exact (h1 hh).elim
      · exact (h2 hh).elim
      · rw [h4] at hh; cases hh
      · exact hh
    simp [sbipTurnLarge,h4,sbipTurnAfter35,h6,sbipTurnChildren,sbipTurnIsReturn,
      sbipTurnPartition,sbipTurnReturn]

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hφ

theorem early_of_iso (c : ℕ) (hearly : SbipTurnEarly c I) : SbipTurnEarly c J := by
  have hs := h.small_tests_transport h' φ hφ c
  rcases hearly with hh | hh | hh | hh
  · exact Or.inl (hs.1 ▸ hh)
  · exact Or.inr (Or.inl (hs.2 ▸ hh))
  · exact Or.inr (Or.inr (Or.inl ((h.early4_test_transport h' φ hφ).1 hh)))
  · by_cases h4 : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 = none
    · exact Or.inr (Or.inr (Or.inl ((h.early4_test_transport h' φ hφ).1 h4)))
    · exact Or.inr (Or.inr (Or.inr
        ((h.component_test_transport h' φ hφ (h.dominant_of_continue h4)) ▸ hh)))

theorem early_init_transport (c : ℕ) (hearly : SbipTurnEarly c I)
    (o : RawAlignOutcome) (hout : o ∈ sbipNodeInit c I) :
    ∃ o' ∈ sbipNodeInit c J,SbipNamedOutcomeIso I J X Y φ o o' := by
  have hout' := (sbipTurnReturns_mem (sbipTurn c I.1) o).1 hout
  have hs := h.small_tests_transport h' φ hφ c
  by_cases h1 : sbipGraphSmall1 c I.1.2.1.1 = true
  · have h1' : sbipGraphSmall1 c J.1.2.1.1 = true := hs.1 ▸ h1
    rw [sbipTurn,if_pos h1] at hout'
    obtain ⟨q,hq,he⟩ := List.mem_map.1 hout'
    have hoe : o = rawAlignPartition q := (congrArg Prod.fst he).symm
    subst o
    obtain ⟨q',hq',hiso⟩ := h.early1_named_transport h' φ hφ.2 hφ.1 h1 q hq
    refine ⟨rawAlignPartition q',?_,hiso⟩
    apply (sbipTurnReturns_mem _ _).2
    rw [sbipTurn,if_pos h1']
    exact List.mem_map.2 ⟨q',hq',rfl⟩
  have h1' : ¬ sbipGraphSmall1 c J.1.2.1.1 = true := by rwa [← hs.1]
  by_cases h2 : sbipGraphSmall2 c I.1.2.1.1 = true
  · have h2' : sbipGraphSmall2 c J.1.2.1.1 = true := hs.2 ▸ h2
    rw [sbipTurn,if_neg h1,if_pos h2] at hout'
    obtain ⟨q,hq,he⟩ := List.mem_map.1 hout'
    have hoe : o = rawAlignPartition q := (congrArg Prod.fst he).symm
    subst o
    obtain ⟨q',hq',hiso⟩ := h.early2_named_transport h' φ hφ.2 h2 q hq
    refine ⟨rawAlignPartition q',?_,hiso⟩
    apply (sbipTurnReturns_mem _ _).2
    rw [sbipTurn,if_neg h1',if_pos h2']
    exact List.mem_map.2 ⟨q',hq',rfl⟩
  have h2' : ¬ sbipGraphSmall2 c J.1.2.1.1 = true := by rwa [← hs.2]
  rw [sbipTurn,if_neg h1,if_neg h2] at hout'
  by_cases h4 : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 = none
  · have h4' := (h.early4_test_transport h' φ hφ).1 h4
    have hoe : o = rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput I.1)) := by
      simp only [sbipTurnLarge,h4,Option.elim_none,List.mem_singleton] at hout'
      exact congrArg Prod.fst hout'
    subst o
    refine ⟨rawAlignPartition (sbipGraphEarly4 (sbipTurnGraphInput J.1)),?_,
      h.early4_named_transport h' φ hφ.2⟩
    apply (sbipTurnReturns_mem _ _).2
    simp only [sbipTurn,if_neg h1',if_neg h2',sbipTurnLarge,h4',Option.elim_none,
      List.mem_singleton,sbipTurnPartition,sbipTurnReturn]
  have hd := h.dominant_of_continue h4
  have h6 : sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput I.1)) = true :=
    hearly.resolve_left h1 |>.resolve_left h2 |>.resolve_left h4
  have h6' : sbipImprimitive (sbipGraphComponentTable (sbipTurnGraphInput J.1)) = true :=
    (h.component_test_transport h' φ hφ hd) ▸ h6
  have h4' : (sbipGraphSteps35 (sbipTurnGraphInput J.1)).2 ≠ none :=
    fun hh => h4 ((h.early4_test_transport h' φ hφ).2 hh)
  have hout'' : (o,none) ∈ sbipTurnAfter35 I.1 := by
    cases hh : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
    | none => exact (h4 hh).elim
    | some a => simpa only [sbipTurnLarge,hh,Option.elim_some] using hout'
  have hoe : o = rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput I.1)) := by
    rw [sbipTurnAfter35,if_pos h6,List.mem_singleton] at hout''
    exact congrArg Prod.fst hout''
  subst o
  refine ⟨rawAlignPartition (sbipGraphComponentPartition (sbipTurnGraphInput J.1)),?_,
    h.component_named_transport h' φ hφ hd⟩
  apply (sbipTurnReturns_mem _ _).2
  rw [sbipTurn,if_neg h1',if_neg h2']
  cases hh : (sbipGraphSteps35 (sbipTurnGraphInput J.1)).2 with
  | none => exact (h4' hh).elim
  | some a =>
    simp only [sbipTurnLarge,hh,Option.elim_some,sbipTurnAfter35,if_pos h6',
      List.mem_singleton,sbipTurnPartition,sbipTurnReturn]

omit h' hφ in
theorem early_value_eq_init (c f : ℕ) (hearly : SbipTurnEarly c I) :
    (sbipRound c).value (f+1) I = sbipNodeInit c I := by
  rw [h.value_family_eq c f,sbipNodeGraphs_eq_nil_of_early c I hearly]
  simp

theorem early_value_transport (c f g : ℕ) (hearly : SbipTurnEarly c I)
    (o : RawAlignOutcome) (hout : o ∈ (sbipRound c).value (f+1) I) :
    ∃ o' ∈ (sbipRound c).value (g+1) J,SbipNamedOutcomeIso I J X Y φ o o' := by
  rw [h.early_value_eq_init c f hearly] at hout
  rw [h'.early_value_eq_init c g (h.early_of_iso h' φ hφ c hearly)]
  exact h.early_init_transport h' φ hφ c hearly o hout

end SbipNodeRep
end Algo
