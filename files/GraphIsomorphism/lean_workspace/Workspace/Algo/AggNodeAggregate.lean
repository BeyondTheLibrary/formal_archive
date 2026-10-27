import Workspace.Algo.AggNodeCompareBoundedMatch
import Workspace.Algo.AggNodeUniformMatch

/-! # One carrier for the two phases of Section 13.2

Run all certificates first. When their pending list is empty, retain both
certificate stores and run the comparison phase. The comparison cursor
starts at zero. Each component is capped by its already proved bound.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

abbrev AggnAggregateState := AggnPhaseState × ℕ × AggnCompareState

def aggnAggregateWidth (c : ℕ) (C : AggnPhaseCtx) : ℕ :=
  aggnPhaseWidth c C + aggnCompareWidth c C

def aggnAggregatePack (c dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) : AggnAggregateState :=
  (aggnCapState dc (C.2.1.length, s.1), min s.2.1 (aggnCompareWidth c C),
    aggnCompareCapState dp (C.2.1.length, s.2.2))

def aggnAggregateChild (c : ℕ) (z : AggnPhaseNode × ℕ × AggnAggregateState) : Option AggnPhaseNode :=
  z.1.2.elim
    (if z.2.1 < aggnAggregateWidth c z.1.1 then
      if z.2.2.1.1.isEmpty then
        aggnCompareCheckedChild c (z.1, z.2.2.2.1, z.2.2.2.2)
      else aggnCheckedChild c (z.1, z.2.1, z.2.2.1)
    else none) (fun _ => none)

def aggnAggregateInit (c dc dp : ℕ) (I : AggnPhaseNode) : AggnAggregateState :=
  ((aggnUniformRound c dc).init I, 0, (aggnCompareBoundedRound c dp).init I)

def aggnAggregateCombine (c dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnAggregateState × RawCoset) :
    AggnAggregateState :=
  let s := z.2.2.1
  aggnAggregatePack c dc dp z.1.1
    (if s.1.1.isEmpty then
      (s.1, s.2.1 + 1, (aggnCompareBoundedRound c dp).combine (z.1, s.2.1, s.2.2, z.2.2.2))
    else ((aggnUniformRound c dc).combine (z.1, z.2.1, s.1, z.2.2.2), s.2.1, s.2.2))

theorem aggnAggregateChild_some {c : ℕ} {z : AggnPhaseNode × ℕ × AggnAggregateState}
    {J : AggnPhaseNode} (h : aggnAggregateChild c z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  cases ho : z.1.2 with
  | some W => simp [aggnAggregateChild, ho] at h
  | none =>
    simp only [aggnAggregateChild, ho, Option.elim_none] at h
    split at h
    next hg =>
      split at h
      next hp =>
        obtain ⟨_, W, _, hW⟩ := aggnCompareCheckedChild_some h
        exact ⟨rfl, W, hW⟩
      next hp =>
        obtain ⟨_, W, _, hW⟩ := aggnCheckedChild_some h
        exact ⟨rfl, W, hW⟩
    next => simp at h

def aggnAggregateRound (c dc dp : ℕ) : Round AggnPhaseNode AggnAggregateState RawCoset where
  WF := fun I => AggnCheckedWF I.1.2.1.length I
  ground := fun I => I.1.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnAggregateWidth c I.1) (fun _ => 0)
  child := aggnAggregateChild c
  init := aggnAggregateInit c dc dp
  combine := aggnAggregateCombine c dc dp
  finish := fun _ => none
  bot := none
  child_eq_none := by
    intro I j s hj
    cases ho : I.2 with
    | some W => simp [aggnAggregateChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      simp only [aggnAggregateChild, ho, Option.elim_none]
      exact if_neg (Nat.not_lt_of_ge hj)
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnAggregateChild_some hJ
    refine ⟨rfl, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    exact aggnCheckedWindow_wf _ _
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnAggregateChild_some hJ
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnAggregateChild_some hJ
    exact le_rfl

/-- Capping an already bounded state preserves it exactly. -/
theorem aggnAggregatePack_eq {c dc dp : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    (hc : Enc.size s.1 ≤ aggnStateCap dc C.2.1.length)
    (hj : s.2.1 ≤ aggnCompareWidth c C)
    (hp : Enc.size s.2.2 ≤ aggnCompareStateCap dp C.2.1.length) :
    aggnAggregatePack c dc dp C s = s := by
  rw [aggnAggregatePack, aggnCapState_eq hc, aggnCompareCapState_eq hp, Nat.min_eq_left hj]

/-- Completing both pending lists ends the preliminary work immediately. -/
theorem aggnAggregateChild_done (c : ℕ) (I : AggnPhaseNode) (j : ℕ)
    (s : AggnAggregateState) (hc : s.1.1 = []) (hp : s.2.2.1 = []) :
    aggnAggregateChild c (I, j, s) = none := by
  cases ho : I.2 <;>
    simp [aggnAggregateChild, ho, hc, aggnCompareCheckedChild, aggnCompareChild, hp]

end Algo
