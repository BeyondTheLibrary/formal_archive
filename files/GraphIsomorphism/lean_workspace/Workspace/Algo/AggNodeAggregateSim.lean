import Workspace.Algo.AggNodeAggregate

/-! # Exact simulations of the two consecutive phases

Finishing the certificate phase switches the active component without a
recursive call. The comparison phase starts its own cursor at zero and
retains the completed certificate stores throughout.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

private theorem certInit_size (c d : ℕ) (I : AggnPhaseNode) :
    Enc.size ((aggnUniformRound c d).init I) ≤ aggnStateCap d I.1.2.1.length := by
  dsimp only [aggnUniformRound, aggnBoundedInit]
  exact aggnCapState_size d _ _

private theorem certCombine_size (c d : ℕ) (z : AggnPhaseNode × ℕ × AggnPhaseState × RawCoset) :
    Enc.size ((aggnUniformRound c d).combine z) ≤ aggnStateCap d z.1.1.2.1.length := by
  dsimp only [aggnUniformRound, aggnBoundedCombine]
  exact aggnCapState_size d _ _

private theorem compareInit_size (c d : ℕ) (I : AggnPhaseNode) :
    Enc.size ((aggnCompareBoundedRound c d).init I) ≤ aggnCompareStateCap d I.1.2.1.length := by
  dsimp only [aggnCompareBoundedRound, aggnCompareBoundedInit]
  exact aggnCompareCapState_size d _ _

private theorem compareCombine_size (c d : ℕ) (z : AggnPhaseNode × ℕ × AggnCompareState × RawCoset) :
    Enc.size ((aggnCompareBoundedRound c d).combine z) ≤ aggnCompareStateCap d z.1.1.2.1.length := by
  dsimp only [aggnCompareBoundedRound, aggnCompareBoundedCombine]
  exact aggnCompareCapState_size d _ _

attribute [local irreducible] Enc.size aggnBoundedInit aggnCompareBoundedInit
  aggnBoundedCombine aggnCompareBoundedCombine

private theorem certCall_active {c d : ℕ} {C : AggnPhaseCtx} {j : ℕ} {s : AggnPhaseState}
    {J : AggnPhaseNode} (h : (aggnUniformRound c d).child ((C, none), j, s) = some J) :
    s.1.isEmpty = false ∧ j < aggnPhaseWidth c C := by
  obtain ⟨_, W, hraw, _⟩ := aggnCheckedChild_some h
  simp only [aggnPhaseChild, Option.elim_none] at hraw
  split at hraw
  next hj =>
    refine ⟨?_, hj⟩
    cases hs : s.1 with
    | nil => simp [hs] at hraw
    | cons a rest => rfl
  next => simp at hraw

private theorem compareCall_index {c d : ℕ} {C : AggnPhaseCtx} {j : ℕ} {s : AggnCompareState}
    {J : AggnPhaseNode} (h : (aggnCompareBoundedRound c d).child ((C, none), j, s) = some J) :
    j < aggnCompareWidth c C := by
  by_contra hn
  have he := (aggnCompareBoundedRound c d).child_eq_none (C, none) j s (Nat.le_of_not_gt hn)
  rw [he] at h
  contradiction

/-- The first phase preserves the not-yet-used comparison state. -/
theorem aggnAggregate_cert_sim {β : Type*} (c dc dp n : ℕ) (C : AggnPhaseCtx)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnPhaseState → Prop}
    (h : PhaseMatch (aggnUniformRound c dc) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnUniformRound c dc).init (C, none)) S Q) :
    PhaseMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnAggregateRound c dc dp).init (C, none)) S
      (fun b j v => ∃ s, Q b j s ∧
        v = (s, 0, (aggnCompareBoundedRound c dp).init (C, none)) ∧
        Enc.size s ≤ aggnStateCap dc C.2.1.length ∧ j ≤ aggnPhaseWidth c C) := by
  let P := (aggnCompareBoundedRound c dp).init (C, none)
  let Rel : ℕ → AggnPhaseState → ℕ → AggnAggregateState → Prop := fun jR vR jM vM => jM = jR ∧ vM = (vR, 0, P) ∧
    Enc.size vR ≤ aggnStateCap dc C.2.1.length ∧ jR ≤ aggnPhaseWidth c C
  have hm := aggnPhaseMatch_sim (M := aggnAggregateRound c dc dp)
    (decI' := aggnPhaseDecode n) (I' := (C, none)) Rel ?_ h
    (k := 0) (t := ((aggnAggregateRound c dc dp).init (C, none)))
    ⟨rfl, rfl, certInit_size c dc _, Nat.zero_le _⟩
  · apply phaseMatch_weaken hm
    rintro b j v ⟨jR, vR, hQ, hj, hv, hs, hw⟩
    subst j
    exact ⟨vR, hQ, hv, hs, hw⟩
  · intro jR vR jM vM hr J hJ
    obtain ⟨rfl, rfl, hs, hj⟩ := hr
    have ha := certCall_active hJ
    have hglobal : jM < aggnAggregateWidth c C := ha.2.trans_le (Nat.le_add_right _ _)
    refine ⟨J, ?_, rfl, ?_⟩
    · dsimp only [aggnAggregateRound, aggnAggregateChild]
      rw [Option.elim_none, if_pos hglobal, if_neg (Bool.eq_false_iff.mp ha.1)]
      exact hJ
    · intro ans
      refine ⟨rfl, ?_, certCombine_size c dc _, by omega⟩
      dsimp only [aggnAggregateRound, aggnAggregateCombine]
      rw [if_neg (Bool.eq_false_iff.mp ha.1)]
      exact aggnAggregatePack_eq (c := c) (dc := dc) (dp := dp) (C := C)
        (s := ((aggnUniformRound c dc).combine ((C, none), jM, vR, ans), 0, P))
        (certCombine_size c dc ((C, none), jM, vR, ans)) (Nat.zero_le _)
        (compareInit_size c dp (C, none))

/-- The second phase retains every completed certificate and shifts only the outer cursor. -/
theorem aggnAggregate_compare_sim {β : Type*} (c dc dp n : ℕ) (C : AggnPhaseCtx)
    (saved : AggnPhaseState) (hstop : saved.1 = [])
    (hsaved : Enc.size saved ≤ aggnStateCap dc C.2.1.length)
    (start : ℕ) (hstart : start ≤ aggnPhaseWidth c C)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnCompareState → Prop}
    (h : PhaseMatch (aggnCompareBoundedRound c dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnCompareBoundedRound c dp).init (C, none)) S Q) :
    PhaseMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel start (saved, 0, (aggnCompareBoundedRound c dp).init (C, none)) S
      (fun b j v => ∃ j' s, Q b j' s ∧ j = start + j' ∧ v = (saved, j', s)) := by
  let Rel : ℕ → AggnCompareState → ℕ → AggnAggregateState → Prop := fun jR vR jM vM => jM = start + jR ∧ vM = (saved, jR, vR)
  apply aggnPhaseMatch_sim (M := aggnAggregateRound c dc dp)
    (decI' := aggnPhaseDecode n) (I' := (C, none)) Rel ?_ h ⟨by omega, rfl⟩
  intro jR vR jM vM hr J hJ
  obtain ⟨hj, rfl⟩ := hr
  have hi := compareCall_index hJ
  have hglobal : jM < aggnAggregateWidth c C := by unfold aggnAggregateWidth; omega
  refine ⟨J, ?_, rfl, ?_⟩
  · dsimp only [aggnAggregateRound, aggnAggregateChild]
    rw [Option.elim_none, if_pos hglobal, hstop]
    exact hJ
  · intro ans
    refine ⟨by omega, ?_⟩
    dsimp only [aggnAggregateRound, aggnAggregateCombine]
    rw [hstop]
    simp only [List.isEmpty_nil, if_true]
    exact aggnAggregatePack_eq (c := c) (dc := dc) (dp := dp) (C := C)
      (s := (saved, jR + 1, (aggnCompareBoundedRound c dp).combine ((C, none), jR, vR, ans)))
      hsaved (by dsimp only; omega) (compareCombine_size c dp ((C, none), jR, vR, ans))

end Algo
