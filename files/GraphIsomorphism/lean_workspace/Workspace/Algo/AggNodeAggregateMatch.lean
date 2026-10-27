import Workspace.Algo.AggNodeAggregateRAM
import Workspace.Algo.AggNodeAggregateSim
import Workspace.Algo.AggNodeCompareReadOff

/-! # Section 13.2's two preliminary phases in one runnable carrier

Both phases use the same explicit test-set, representative, and transporter
choices. At their common endpoint, both certificate stores and the complete
comparison table are available to the later aggregation cases.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

attribute [local irreducible] Enc.size aggnBoundedInit aggnCompareBoundedInit
  aggnBoundedCombine aggnCompareBoundedCombine

/-- One degree-uniform carrier executes the two phases in the paper's order.
Every correct raw answer encoding preserves both final stores. -/
theorem aggnAggregate_phases (c : ℕ) : ∃ dc dp : ℕ,
    Nonempty (Round.RunCostQ (aggnAggregateRound c dc dp)) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnAggregateRound c dc dp).WF (C, none) → AggnPhaseCtxWF c n m C ϕ →
      LocalCertSetting (decGroup n C.1.1.2) ϕ →
      LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      PhaseMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))) (.done ()))
        (fun _ _ v => v.1.1 = [] ∧ AggnStoresComplete c ϕ v.1.2.1 ∧
          v.2.2.1 = [] ∧ AggnCompareTableFor c ϕ (aggnCompareTable c (C, v.2.2.2.1))) := by
  obtain ⟨dc, _, hc⟩ := aggnUniform_certificates c
  obtain ⟨dp, _, hp⟩ := aggnCompareBounded_tables c
  refine ⟨dc, dp, aggnAggregate_hasRunCostQ c dc dp, ?_⟩
  intro n m C ϕ hI hC hset ht htm hx hy
  let E := aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
    ((aggnPhaseRows c C).map (winSet m))
  have hcert : PhaseMatch (aggnUniformRound c dc) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnPhaseWidth c C) 0 ((aggnUniformRound c dc).init (C, none))
      (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E)
      (fun _ _ v => v.1 = [] ∧ AggnStoresComplete c ϕ v.2.1) :=
    hc n m C ϕ hI hC hset.giant ht htm hx hy
  have hcert' := aggnAggregate_cert_sim c dc dp n C hcert
  have hcomp := hp n m C ϕ hI hC hset ht htm hx hy
  change PhaseMatch _ _ _ _ (aggnPhaseWidth c C + aggnCompareWidth c C) _ _
    ((certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E).bind fun _ =>
      (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E).bind fun _ => .done ()) _
  apply phaseMatch_bind hcert'
  rintro result j v ⟨saved, ⟨hstop, hstores⟩, rfl, hsize, hj⟩
  have hcomp' := aggnAggregate_compare_sim c dc dp n C saved hstop hsize j hj hcomp
  have hend := phaseMatch_bind
    (P' := fun (_ : Unit) (_ : ℕ) (v : AggnAggregateState) => v.1.1 = [] ∧
      AggnStoresComplete c ϕ v.1.2.1 ∧ v.2.2.1 = [] ∧
      AggnCompareTableFor c ϕ (aggnCompareTable c (C, v.2.2.2.1)))
    (k := fun _ => .done ()) hcomp' (by
      rintro bs j' v' ⟨cursor, state, ⟨he, htable⟩, hj', rfl⟩
      exact phaseMatch_done ⟨hstop, hstores, he, htable⟩)
  simpa only [Nat.add_zero] using hend

end Algo
