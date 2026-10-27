import Workspace.Algo.AggNodeAggregate

/-! # Uniform RAM bounds for both aggregate phases

The carrier caps each retained component separately. Its comparison cursor
is clamped to the original comparison width. These operations give closure
for every raw state without assuming either phase's semantic invariant.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

theorem aggnQuasiFun_aggregateWidth (c : ℕ) : QuasiFun (aggnAggregateWidth c) :=
  ((aggnQuasiFun_phaseWidth c).pair (aggnQuasiFun_compareWidth c)).comp_poly polyFun_add

theorem aggnQuasiFun_aggregatePack (c dc dp : ℕ) :
    QuasiFun (fun z : AggnPhaseCtx × AggnAggregateState => aggnAggregatePack c dc dp z.1 z.2) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z) := polyFun_id
  have hC := pfst hz
  have hs := psnd hz
  have hn := (pfst (psnd hC)).comp polyFun_length
  have hc := (hn.pair (pfst hs)).comp (aggnPolyFun_capState dc)
  have hp := (hn.pair (psnd (psnd hs))).comp (aggnPolyFun_compareCapState dp)
  have hj := ((pfst (psnd hs)).quasiFun.pair
    (hC.comp_quasiFun (aggnQuasiFun_compareWidth c))).comp_poly polyFun_min
  exact hc.quasiFun.pair (hj.pair hp.quasiFun)

theorem aggnQuasiFun_aggregateInit (c dc dp : ℕ) : QuasiFun (aggnAggregateInit c dc dp) :=
  (aggnQuasiFun_boundedInit c dc 0).pair
    ((quasiFun_const 0).pair (aggnQuasiFun_compareBoundedInit c dp))

theorem aggnQuasiFun_aggregateChild (c : ℕ) : QuasiFun (aggnAggregateChild c) := by
  let X := AggnPhaseNode × ℕ × AggnAggregateState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := psnd (psnd hz)
  have htest := (pfst (pfst hs)).comp polyFun_isEmpty
  have hc := (hI.pair (hj.pair (pfst hs))).comp_quasiFun (aggnQuasiFun_checkedChild c)
  have hp := (hI.pair ((pfst (psnd hs)).pair (psnd (psnd hs)))).comp_quasiFun
    (aggnQuasiFun_compareCheckedChild c)
  have hbranch := QuasiFun.ite htest hp hc
  have hwidth := (pfst hI).comp_quasiFun (aggnQuasiFun_aggregateWidth c)
  have hgate := (hj.quasiFun.pair hwidth).comp_poly plt
  have hrun := aggnQuasiFun_ite hgate hbranch (quasiFun_const none)
  exact (((psnd hI).pair hz).comp_quasiFun
    (QuasiFun.optionElim hrun (quasiFun_const none))).of_eq (fun z => by
      simp only [aggnAggregateChild, decide_eq_true_eq])

theorem aggnQuasiFun_aggregateCombine (c dc dp : ℕ) : QuasiFun (aggnAggregateCombine c dc dp) := by
  let X := AggnPhaseNode × ℕ × AggnAggregateState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hc := pfst hs
  have hk := pfst (psnd hs)
  have hp := psnd (psnd hs)
  have htest := (pfst hc).comp polyFun_isEmpty
  have hnextc := (hI.pair (hj.pair (hc.pair ha))).comp_quasiFun (aggnQuasiFun_boundedCombine c dc 0)
  have hnextp := (hI.pair (hk.pair (hp.pair ha))).comp_quasiFun (aggnQuasiFun_compareBoundedCombine c dp)
  have hcomp := hc.quasiFun.pair (((hk.pair (polyFun_const 1)).comp polyFun_add).quasiFun.pair hnextp)
  have hcert := hnextc.pair (hk.pair hp).quasiFun
  have hnext := QuasiFun.ite htest hcomp hcert
  exact (((pfst hI).quasiFun.pair hnext).comp (aggnQuasiFun_aggregatePack c dc dp)).of_eq
    (fun _ => by dsimp only [aggnAggregateCombine, aggnUniformRound, aggnBoundedRound])

/-- A scalar bound for the two retained states and one cursor. -/
theorem aggnAggregateState_size {dc dp n w : ℕ} {s : AggnAggregateState}
    (hc : Enc.size s.1 ≤ aggnStateCap dc n) (hj : s.2.1 ≤ w)
    (hp : Enc.size s.2.2 ≤ aggnCompareStateCap dp n) :
    Enc.size s ≤ 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + w + 2) := by
  have hn : Enc.size s.2.1 ≤ w + 2 := by
    rw [Small.size_nat]
    have := size_le_self s.2.1
    omega
  have h0 : Enc.size s ≤ 2 * Enc.size s.1 + 2 * Enc.size s.2 := Combine.size_pair_le _ _
  have h1 : Enc.size s.2 ≤ 2 * Enc.size s.2.1 + 2 * Enc.size s.2.2 := Combine.size_pair_le _ _
  omega

attribute [local irreducible] Enc.size aggnBoundedInit aggnCompareBoundedInit
  aggnBoundedCombine aggnCompareBoundedCombine

theorem aggnAggregate_hasRunCostQ (c dc dp : ℕ) : Nonempty (Round.RunCostQ (aggnAggregateRound c dc dp)) := by
  obtain ⟨Wc, hWc, hWcm, hcw⟩ := aggnChecked_width_bound c
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  let B := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  have hBm : Monotone B := by
    intro a b hab
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (aggnMono_stateCap dc hab)
        (aggnMono_compareStateCap dp hab)) (hWpm hab)) 2)
  have hwidth : ∀ I, (aggnAggregateRound c dc dp).WF I →
      aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length := by
    intro I hI
    exact hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hpack : ∀ I, (aggnAggregateRound c dc dp).WF I → ∀ s,
      Enc.size (aggnAggregatePack c dc dp I.1 s) ≤ B I.1.2.1.length := by
    intro I hI s
    dsimp only [aggnAggregatePack]
    exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
      (w := Wp I.1.2.1.length) (aggnCapState_size dc _ _)
      ((Nat.min_le_right _ _).trans (hwidth I hI)) (aggnCompareCapState_size dp _ _)
  refine ⟨{
    bound := fun k => aggnCheckedBound k + 2
    polyBound_bound := aggnPolyBound_checked.add (polyBound_const 2)
    mono_bound := fun _ _ h => Nat.add_le_add_right (aggnMono_checkedBound h) 2
    stateBound := B
    quasiPolyBound_stateBound := hB
    mono_stateBound := hBm
    widthBound := fun n => Wc n + Wp n
    quasiPolyBound_widthBound := hWc.add hWp
    quasiFun_child := aggnQuasiFun_aggregateChild c
    quasiFun_init := aggnQuasiFun_aggregateInit c dc dp
    quasiFun_combine := aggnQuasiFun_aggregateCombine c dc dp
    quasiFun_finish := quasiFun_const none
    ground_le := fun I => (length_le_size I.1.2.1).trans
      ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans (size_fst_le' I)))
    size_le := fun I hI => (aggnCheckedRound_size c I.1.2.1.length I hI).trans (Nat.le_add_right _ 2)
    init_le := by
      intro I _
      dsimp only [aggnAggregateRound, aggnAggregateInit]
      have hc : Enc.size ((aggnUniformRound c dc).init I) ≤ aggnStateCap dc I.1.2.1.length := by
        dsimp only [aggnUniformRound]
        unfold aggnBoundedInit
        exact aggnCapState_size dc I.1.2.1.length _
      have hp : Enc.size ((aggnCompareBoundedRound c dp).init I) ≤
          aggnCompareStateCap dp I.1.2.1.length := by
        dsimp only [aggnCompareBoundedRound]
        unfold aggnCompareBoundedInit
        exact aggnCompareCapState_size dp I.1.2.1.length _
      exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
        (w := Wp I.1.2.1.length)
        (s := ((aggnUniformRound c dc).init I, 0, (aggnCompareBoundedRound c dp).init I))
        hc (Nat.zero_le _) hp
    combine_le := by
      intro I j s a hI _ _
      dsimp only [aggnAggregateRound, aggnAggregateCombine]
      exact hpack I hI _
    finish_le := fun I _ _ _ => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound I.1.2.1.length + 2
      rw [size_none]
      omega
    bot_le := fun m => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound m + 2
      rw [size_none]
      omega
    width_le := ?_
    polyFun_ground := aggnPolyFun_ground c dc 0
    wfCheck := aggnUniformWfCheck
    polyFun_wfCheck := aggnPolyFun_uniformWfCheck
    wfCheck_eq_true := aggnUniformWfCheck_spec c dc
    measureBound := fun _ => 1
    polyBound_measureBound := polyBound_const 1
    mono_measureBound := fun _ _ _ => le_rfl
    measure_le := ?_ }⟩
  · intro I hI
    have hc := hcw I.1.2.1.length I hI
    have hp := hpw I hI
    change I.2.elim (aggnAggregateWidth c I.1) (fun _ => 0) ≤ _
    change I.2.elim (aggnPhaseWidth c I.1) (fun _ => 0) ≤ _ at hc
    change I.2.elim (aggnCompareWidth c I.1) (fun _ => 0) ≤ _ at hp
    cases ho : I.2 <;> simp only [ho, Option.elim_none, Option.elim_some] at hc hp ⊢
    · exact Nat.add_le_add hc hp
    · exact Nat.zero_le _
  · intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

noncomputable def aggnAggregateRunCostQ (c dc dp : ℕ) : Round.RunCostQ (aggnAggregateRound c dc dp) :=
  Classical.choice (aggnAggregate_hasRunCostQ c dc dp)

end Algo
