/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the round of Sec. 15, lines 5–7, with the giant branch
(`Algo.aggnL57GRound`) has the cost data the machine packaging needs.
-/
import Workspace.Algo.AggNodeLine57Giant
import Workspace.Algo.AggNodeLine57RAM

/-!
# The round of lines 5–7 with the giant branch runs on the machine

`Algo.aggnL57G_hasRunCostQ` gives `Algo.aggnL57GRound` the cost data `Algo.Round.RunCostQ`.
Outside the giant branch the round is `Algo.aggnL57Round`, whose bounds hold on every state
(`Algo.aggnL57_hasRunCostQ_strong`).  In the giant branch the node of Cor. 12.0.10 passed the
well-formedness test of `Algo.top4aRound`, so its state, its answer and its width have the
polynomial bounds of `Algo.top4aRunCostQ`, in the size of that node; the node is a
polynomial function of the context (`Algo.top4AggregateInput_size_bdd`), whose size is
bounded by the degree of the node of the carrier.  The count of the branch is kept below the
width of the node of Cor. 12.0.10, and the stores through the caps of the aggregate carrier.
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])
private theorem polyFun_isNone {α : Type*} [Enc α] : PolyFun (fun o : Option α => o.isNone) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) (polyFun_const false))).of_eq
    (fun o => by cases o <;> rfl)

/-! ## The routines -/

section Routines

variable (c b t d dc dp u v e f : ℕ)

theorem quasiFun_aggnL57GNode : QuasiFun (aggnL57GNode c dc dp) :=
  (polyFun_fst.quasiFun.pair (aggnQuasiFun_aggregatePack c dc dp)).comp_poly
    polyFun_top4AggregateEnter

theorem polyFun_l57gW4 : PolyFun l57gW4 := by
  have hel : PolyFun (fun I : Top4aNode => I.1.2.elim (top4Width I.1.1) (fun _ => 0)) :=
    (((psnd (pfst polyFun_id)).pair polyFun_id).comp (PolyFun.optionElim
      ((pfst (pfst polyFun_id)).comp polyFun_top4Width) (polyFun_const 0)))
  exact (PolyFun.ite polyFun_top4aGate hel (polyFun_const 0)).of_eq (fun I => by
    unfold l57gW4; cases top4aGate I <;> rfl)

theorem quasiFun_aggnL57GOn : QuasiFun (aggnL57GOn c b t d dc dp u v e f) := by
  have hcont : QuasiFun (fun z : AggnPhaseCtx × AggnAggregateState =>
      aggnL57Cont c b t d (z.1, aggnAggregatePack c dc dp z.1 z.2)) :=
    (polyFun_fst.quasiFun.pair (aggnQuasiFun_aggregatePack c dc dp)).comp
      (aggnQuasiFun_continuation c b t d)
  have htag := hcont.comp_poly (polyFun_fst.natEq (polyFun_const 2))
  have hchk := (quasiFun_aggnL57GNode c dc dp).comp_poly (polyFun_top4aCheck u v e f)
  exact (htag.pair hchk).comp_poly (polyFun_and polyFun_fst polyFun_snd)

theorem quasiFun_aggnL57GActive : QuasiFun (aggnL57GActive c b t d dc dp u v e f) := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have h1 : QuasiFun (fun q : Z => q.1.2.isNone) := ((psnd (pfst z)).comp polyFun_isNone).quasiFun
  have h2 : QuasiFun (fun q : Z => (aggnAggregateChild c (q.1, q.2.1, q.2.2.1.1)).isNone) :=
    (((pfst z).pair ((pfst (psnd z)).pair (pfst (pfst (psnd (psnd z)))))).comp_quasiFun
      (aggnQuasiFun_aggregateChild c)).comp_poly polyFun_isNone
  have h3 : QuasiFun (fun q : Z => aggnL57GOn c b t d dc dp u v e f (q.1.1, q.2.2.1.1)) :=
    ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z))))).comp_quasiFun
      (quasiFun_aggnL57GOn c b t d dc dp u v e f)
  exact (((h1.pair h2).comp_poly (polyFun_and polyFun_fst polyFun_snd)).pair h3).comp_poly
    (polyFun_and polyFun_fst polyFun_snd)

theorem quasiFun_aggnL57GPos : QuasiFun (aggnL57GPos c dc dp) := by
  let P := AggnPhaseCtx × AggnL57GState
  have z : PolyFun (fun q : P => q) := polyFun_id
  have hnode : QuasiFun (fun q : P => aggnL57GNode c dc dp (q.1, q.2.1.1)) :=
    ((pfst z).pair (pfst (pfst (psnd z)))).comp_quasiFun (quasiFun_aggnL57GNode c dc dp)
  exact ((psnd (psnd z)).quasiFun.pair ((polyFun_const 0).quasiFun.pair
    (hnode.comp_poly polyFun_top4aInit))).comp_poly polyFun_optionGetD

theorem polyFun_avEmb : PolyFun avEmb :=
  (pfst polyFun_id).pair ((((pfst (psnd (pfst polyFun_id))).pair (psnd polyFun_id)).comp
    aggnPolyFun_checkedWindow).comp polyFun_some)

theorem quasiFun_aggnL57GTopChild : QuasiFun (aggnL57GTopChild c dc dp e f) := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hnode : QuasiFun (fun q : Z => aggnL57GNode c dc dp (q.1.1, q.2.2.1.1)) :=
    ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z))))).comp_quasiFun
      (quasiFun_aggnL57GNode c dc dp)
  have hpos : QuasiFun (fun q : Z => aggnL57GPos c dc dp (q.1.1, q.2.2)) :=
    ((pfst (pfst z)).pair (psnd (psnd z))).comp_quasiFun (quasiFun_aggnL57GPos c dc dp)
  have hgate : QuasiFun (fun q : Z => decide (q.2.1 < aggnAggregateWidth c q.1.1 +
      l57gW4 (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1)))) :=
    ((pfst (psnd z)).quasiFun.pair (((pfst (pfst z)).comp_quasiFun
      (aggnQuasiFun_aggregateWidth c)).pair (hnode.comp_poly polyFun_l57gW4) |>.comp_poly
        polyFun_add)).comp_poly plt
  have hch : QuasiFun (fun q : Z => top4aChild e f (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1),
      (aggnL57GPos c dc dp (q.1.1, q.2.2)).1, (aggnL57GPos c dc dp (q.1.1, q.2.2)).2)) :=
    (hnode.pair ((hpos.comp_poly polyFun_fst).pair (hpos.comp_poly polyFun_snd))).comp_poly
      (polyFun_top4aChild e f)
  have hmap : PolyFun (fun r : Top4aNode × AggnPhaseCtx =>
      r.1.1.2.map (fun W => avEmb (r.2, W))) :=
    (((psnd (pfst (pfst polyFun_id))).pair (psnd polyFun_id)).comp (PolyFun.optionElim
      (polyFun_const none) (((psnd polyFun_id).pair (pfst polyFun_id)).comp polyFun_avEmb
        |>.comp polyFun_some))).of_eq (fun r => by
          obtain ⟨⟨⟨ctx, o⟩, α⟩, C⟩ := r
          cases o <;> rfl)
  have hbind : QuasiFun (fun q : Z => (top4aChild e f (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1),
      (aggnL57GPos c dc dp (q.1.1, q.2.2)).1, (aggnL57GPos c dc dp (q.1.1, q.2.2)).2)).bind
      (fun J => J.1.2.map (fun W => avEmb (q.1.1, W)))) :=
    ((hch.pair (pfst (pfst z)).quasiFun).comp (QuasiFun.optionElim (quasiFun_const none)
      hmap.quasiFun)).of_eq (fun q => by
        dsimp only
        cases top4aChild e f (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1),
          (aggnL57GPos c dc dp (q.1.1, q.2.2)).1, (aggnL57GPos c dc dp (q.1.1, q.2.2)).2) <;> rfl)
  exact (aggnQuasiFun_ite hgate hbind (quasiFun_const none)).of_eq (fun q => by
    unfold aggnL57GTopChild; simp only [decide_eq_true_eq])

theorem quasiFun_aggnL57GChild : QuasiFun (aggnL57GChild c b t d dc dp u v e f) := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hold : QuasiFun (fun q : Z => aggnL57Child c b t d dc dp (q.1, q.2.1, q.2.2.1)) :=
    ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z))))).comp_quasiFun
      (quasiFun_aggnL57Child c b t d dc dp)
  exact (aggnQuasiFun_ite (quasiFun_aggnL57GActive c b t d dc dp u v e f)
    (quasiFun_aggnL57GTopChild c dc dp e f) hold).of_eq (fun q => by unfold aggnL57GChild; rfl)

theorem quasiFun_aggnL57GTopCombine : QuasiFun (aggnL57GTopCombine c dc dp) := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState × RawCoset
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hnode : QuasiFun (fun q : Z => aggnL57GNode c dc dp (q.1.1, q.2.2.1.1.1)) :=
    ((pfst (pfst z)).pair (pfst (pfst (pfst (psnd (psnd z)))))).comp_quasiFun
      (quasiFun_aggnL57GNode c dc dp)
  have hpos : QuasiFun (fun q : Z => aggnL57GPos c dc dp (q.1.1, q.2.2.1)) :=
    ((pfst (pfst z)).pair (pfst (psnd (psnd z)))).comp_quasiFun (quasiFun_aggnL57GPos c dc dp)
  have hpk : QuasiFun (fun q : Z => aggnAggregatePack c dc dp q.1.1 q.2.2.1.1.1) :=
    ((pfst (pfst z)).pair (pfst (pfst (pfst (psnd (psnd z)))))).comp_quasiFun
      (aggnQuasiFun_aggregatePack c dc dp)
  have hk : QuasiFun (fun q : Z => min ((aggnL57GPos c dc dp (q.1.1, q.2.2.1)).1 + 1)
      (l57gW4 (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1.1)))) :=
    (((hpos.comp_poly polyFun_fst).pair (quasiFun_const 1) |>.comp_poly polyFun_add).pair
      (hnode.comp_poly polyFun_l57gW4)).comp_poly polyFun_min
  have hst : QuasiFun (fun q : Z => top4aCombine (aggnL57GNode c dc dp (q.1.1, q.2.2.1.1.1),
      (aggnL57GPos c dc dp (q.1.1, q.2.2.1)).1, (aggnL57GPos c dc dp (q.1.1, q.2.2.1)).2,
      q.2.2.2)) :=
    (hnode.pair ((hpos.comp_poly polyFun_fst).pair ((hpos.comp_poly polyFun_snd).pair
      (psnd (psnd (psnd z))).quasiFun))).comp_poly polyFun_top4aCombine
  exact ((hpk.pair (quasiFun_const none)).pair ((hk.pair hst).comp_poly polyFun_some)).of_eq
    (fun q => by unfold aggnL57GTopCombine; rfl)

theorem quasiFun_aggnL57GCombine : QuasiFun (aggnL57GCombine c b t d dc dp u v e f) := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState × RawCoset
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hact : QuasiFun (fun q : Z => aggnL57GActive c b t d dc dp u v e f (q.1, q.2.1, q.2.2.1)) :=
    ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z))))).comp_quasiFun
      (quasiFun_aggnL57GActive c b t d dc dp u v e f)
  have hold : QuasiFun (fun q : Z =>
      ((aggnL57Combine c b t d dc dp (q.1, q.2.1, q.2.2.1.1, q.2.2.2), none) : AggnL57GState)) :=
    (((pfst z).pair ((pfst (psnd z)).pair ((pfst (pfst (psnd (psnd z)))).pair
      (psnd (psnd (psnd z)))))).comp_quasiFun (quasiFun_aggnL57Combine c b t d dc dp)).pair
      (quasiFun_const none)
  exact (aggnQuasiFun_ite hact (quasiFun_aggnL57GTopCombine c dc dp) hold).of_eq (fun q => by
    unfold aggnL57GCombine; rfl)

theorem quasiFun_aggnL57GFinish : QuasiFun (aggnL57GFinish c b t d dc dp u v e f) := by
  let Z := AggnPhaseNode × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have htest : QuasiFun (fun q : Z =>
      q.1.2.isNone && aggnL57GOn c b t d dc dp u v e f (q.1.1, q.2.1.1)) :=
    (((psnd (pfst z)).comp polyFun_isNone).quasiFun.pair
      (((pfst (pfst z)).pair (pfst (pfst (psnd z)))).comp_quasiFun
        (quasiFun_aggnL57GOn c b t d dc dp u v e f))).comp_poly
      (polyFun_and polyFun_fst polyFun_snd)
  have hnode : QuasiFun (fun q : Z => aggnL57GNode c dc dp (q.1.1, q.2.1.1)) :=
    ((pfst (pfst z)).pair (pfst (pfst (psnd z)))).comp_quasiFun (quasiFun_aggnL57GNode c dc dp)
  have hpos : QuasiFun (fun q : Z => aggnL57GPos c dc dp (q.1.1, q.2)) :=
    ((pfst (pfst z)).pair (psnd z)).comp_quasiFun (quasiFun_aggnL57GPos c dc dp)
  have htop := (hnode.pair (hpos.comp_poly polyFun_snd)).comp
    (quasiFun_top4aFinish (solve := l57gSolve) (quasiFun_const _))
  have hold : QuasiFun (fun q : Z => aggnL57Finish (q.1, q.2.1)) :=
    ((pfst z).pair (pfst (psnd z))).comp polyFun_aggnL57Finish |>.quasiFun
  exact (aggnQuasiFun_ite htest htop hold).of_eq (fun q => by unfold aggnL57GFinish; rfl)

end Routines

/-! ## The cost data -/

attribute [local irreducible] Enc.size

theorem aggnL57G_hasRunCostQ (c b t d dc dp u v e f : ℕ) :
    Nonempty (Round.RunCostQ (aggnL57GRound c b t d dc dp u v e f)) := by
  obtain ⟨RC, hRCc, hRCf⟩ := aggnL57_hasRunCostQ_strong c b t d dc dp
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  obtain ⟨K0, hK0, hK0m, hK0s⟩ := top4AggregateInput_size_bdd
  obtain ⟨F, hF, hFm, hFs⟩ := polyFun_top4AutoEnter.size.exists_polyBound
  obtain ⟨GK, hGK, hGKm, hGKs⟩ := aggnL57GCap_le c b t d dc dp u v e f
  -- the size of the node of Cor. 12.0.10, in the degree
  let Q4 : ℕ → ℕ := fun n => F (K0 (aggnCheckedBound n))
  have hQ4 : PolyBound Q4 := hF.comp (hK0.comp aggnPolyBound_checked)
  have hQ4m : Monotone Q4 := fun a b hab => hFm _ _ (hK0m (aggnMono_checkedBound hab))
  -- the stores through the caps
  let B : ℕ → ℕ := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  have hBm : Monotone B := by
    intro a b hab
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (aggnMono_stateCap dc hab)
        (aggnMono_compareStateCap dp hab)) (hWpm hab)) 2)
  -- the state of the giant branch
  let TB : ℕ → ℕ := fun n => l57gW4Bound u v (Q4 n) + top4Bound u v e f (Q4 n)
  have hTB : PolyBound TB := ((polyBound_l57gW4Bound u v).comp hQ4).add
    ((polyBound_top4Bound u v e f).comp hQ4)
  have hTBm : Monotone TB := fun a b hab => Nat.add_le_add
    (mono_l57gW4Bound u v (hQ4m hab)) (mono_top4Bound u v e f (hQ4m hab))
  have hsizeC : ∀ I, (aggnL57GRound c b t d dc dp u v e f).WF I →
      Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length := fun I hI =>
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  have hwidth : ∀ I, (aggnL57GRound c b t d dc dp u v e f).WF I →
      aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length := fun I hI =>
    hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hpack : ∀ I, (aggnL57GRound c b t d dc dp u v e f).WF I → ∀ s,
      Enc.size (aggnAggregatePack c dc dp I.1 s) ≤ B I.1.2.1.length := by
    intro I hI s
    dsimp only [aggnAggregatePack]
    exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
      (w := Wp I.1.2.1.length) (aggnCapState_size dc _ _)
      ((Nat.min_le_right _ _).trans (hwidth I hI)) (aggnCompareCapState_size dp _ _)
  -- the node of Cor. 12.0.10, when the test of outcome (2a) holds
  have hnode : ∀ I, (aggnL57GRound c b t d dc dp u v e f).WF I → ∀ s,
      aggnL57GOn c b t d dc dp u v e f (I.1, s) = true →
        Top4aWF u v e f (aggnL57GNode c dc dp (I.1, s)) ∧
          (top4X (aggnL57GNode c dc dp (I.1, s)).1.1).length ≤ Q4 I.1.2.1.length := by
    intro I hI s hon
    have hwf : Top4aWF u v e f (aggnL57GNode c dc dp (I.1, s)) :=
      (top4aCheck_spec u v e f _).1 (by
        unfold aggnL57GOn at hon
        simp only [Bool.and_eq_true] at hon
        exact hon.2)
    refine ⟨hwf, ?_⟩
    have hg := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).ground_le
      (aggnL57GNode c dc dp (I.1, s))
    have hsz : Enc.size (aggnL57GNode c dc dp (I.1, s)) ≤ Q4 I.1.2.1.length :=
      (hFs _).trans (hFm _ _ ((hK0s _ _).trans (hK0m (hsizeC I hI))))
    exact hg.trans hsz
  have hnone2 : ∀ {α : Type} [Enc α], Enc.size (none : Option α) = 2 := fun {_} _ => size_none
  refine ⟨{
    bound := fun n => RC.bound n + chainBound (Q4 n)
    polyBound_bound := RC.polyBound_bound.add (polyBound_chainBound.comp hQ4)
    mono_bound := fun _ _ h => Nat.add_le_add (RC.mono_bound h) (mono_chainBound (hQ4m h))
    stateBound := fun n => 2 * RC.stateBound n + 4 * B n + 8 * TB n + 64
    quasiPolyBound_stateBound := ((((polyBound_const 2).quasiPoly.mul RC.quasiPolyBound_stateBound).add
      ((polyBound_const 4).quasiPoly.mul hB)).add ((polyBound_const 8).mul hTB).quasiPoly).add
      (polyBound_const 64).quasiPoly
    mono_stateBound := fun _ _ h => Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left 2 (RC.mono_stateBound h)) (Nat.mul_le_mul_left 4 (hBm h)))
      (Nat.mul_le_mul_left 8 (hTBm h))) 64
    widthBound := fun n => RC.widthBound n + GK (aggnCheckedBound n)
    quasiPolyBound_widthBound := RC.quasiPolyBound_widthBound.add
      (hGK.comp aggnPolyBound_checked).quasiPoly
    quasiFun_child := quasiFun_aggnL57GChild c b t d dc dp u v e f
    quasiFun_init := RC.quasiFun_init.comp_poly (polyFun_id.pair (polyFun_const none))
    quasiFun_combine := quasiFun_aggnL57GCombine c b t d dc dp u v e f
    quasiFun_finish := quasiFun_aggnL57GFinish c b t d dc dp u v e f
    ground_le := RC.ground_le
    size_le := fun I hI => (RC.size_le I hI).trans (Nat.le_add_right _ _)
    init_le := ?_
    combine_le := ?_
    finish_le := ?_
    bot_le := fun m => (RC.bot_le m).trans (Nat.le_add_right _ _)
    width_le := ?_
    polyFun_ground := RC.polyFun_ground
    wfCheck := RC.wfCheck
    polyFun_wfCheck := RC.polyFun_wfCheck
    wfCheck_eq_true := RC.wfCheck_eq_true
    measureBound := RC.measureBound
    polyBound_measureBound := RC.polyBound_measureBound
    mono_measureBound := RC.mono_measureBound
    measure_le := RC.measure_le }⟩
  · -- the initial state
    intro I hI
    have h1 := RC.init_le I hI
    have h2 := Combine.size_pair_le ((aggnL57Round c b t d dc dp).init I)
      (none : Option (ℕ × Top4State))
    have h3 : Enc.size (none : Option (ℕ × Top4State)) = 2 := hnone2
    change Enc.size (((aggnL57Round c b t d dc dp).init I, none) : AggnL57GState) ≤
      2 * RC.stateBound I.1.2.1.length + 4 * B I.1.2.1.length + 8 * TB I.1.2.1.length + 64
    change Enc.size ((aggnL57Round c b t d dc dp).init I) ≤ RC.stateBound I.1.2.1.length at h1
    omega
  · -- the combine keeps the state small
    intro I j s a hI _ _
    change Enc.size (aggnL57GCombine c b t d dc dp u v e f (I, j, s, a)) ≤
      2 * RC.stateBound I.1.2.1.length + 4 * B I.1.2.1.length + 8 * TB I.1.2.1.length + 64
    unfold aggnL57GCombine
    split
    next hact =>
      have hon : aggnL57GOn c b t d dc dp u v e f (I.1, s.1.1) = true := by
        unfold aggnL57GActive at hact
        simp only [Bool.and_eq_true] at hact
        exact hact.2
      obtain ⟨hwf, hlen⟩ := hnode I hI s.1.1 hon
      set N := aggnL57GNode c dc dp (I.1, s.1.1) with hN
      set p := aggnL57GPos c dc dp (I.1, s)
      have hk : min (p.1 + 1) (l57gW4 N) ≤ l57gW4Bound u v (Q4 I.1.2.1.length) := by
        have hw := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).width_le N hwf
        change l57gW4 N ≤ l57gW4Bound u v (top4X N.1.1).length at hw
        exact (Nat.min_le_right _ _).trans (hw.trans (mono_l57gW4Bound u v hlen))
      have hst : Enc.size (top4aCombine (N, p.1, p.2, a)) ≤ top4Bound u v e f (Q4 I.1.2.1.length) :=
        (top4Stored_size (e := e) (f := f) hwf.1.1 (top4Combine_stored (N.1, p.1, p.2, a))).trans
          (mono_top4Bound u v e f hlen)
      have hks := size_nat_le_self (min (p.1 + 1) (l57gW4 N))
      have hpk := hpack I hI s.1.1
      have e1 := Combine.size_pair_le (min (p.1 + 1) (l57gW4 N)) (top4aCombine (N, p.1, p.2, a))
      have e2 : Enc.size (some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a))) =
          Enc.size (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a)) + 2 :=
        size_some_eq _
      have e3 := Combine.size_pair_le (aggnAggregatePack c dc dp I.1 s.1.1)
        (none : Option ADState)
      have e4 : Enc.size (none : Option ADState) = 2 := hnone2
      have e5 := Combine.size_pair_le (aggnAggregatePack c dc dp I.1 s.1.1, (none : Option ADState))
        (some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a)))
      show Enc.size (((aggnAggregatePack c dc dp I.1 s.1.1, none),
        some (min (p.1 + 1) (l57gW4 N), top4aCombine (N, p.1, p.2, a))) : AggnL57GState) ≤ _
      dsimp only [TB]
      omega
    next =>
      have h1 := hRCc I j s.1 a hI
      have h2 := Combine.size_pair_le (aggnL57Combine c b t d dc dp (I, j, s.1, a))
        (none : Option (ℕ × Top4State))
      have h3 : Enc.size (none : Option (ℕ × Top4State)) = 2 := hnone2
      show Enc.size ((aggnL57Combine c b t d dc dp (I, j, s.1, a), none) : AggnL57GState) ≤ _
      omega
  · -- the answer is small
    intro I s hI _
    change Enc.size (aggnL57GFinish c b t d dc dp u v e f (I, s)) ≤
      RC.bound I.1.2.1.length + chainBound (Q4 I.1.2.1.length)
    unfold aggnL57GFinish
    split
    next htest =>
      have hon : aggnL57GOn c b t d dc dp u v e f (I.1, s.1.1) = true := by
        simp only [Bool.and_eq_true] at htest
        exact htest.2
      obtain ⟨-, hlen⟩ := hnode I hI s.1.1 hon
      have h := size_top4aFinish (solve := l57gSolve) (aggnL57GNode c dc dp (I.1, s.1.1))
        (aggnL57GPos c dc dp (I.1, s)).2
      exact (h.trans (mono_chainBound hlen)).trans (Nat.le_add_left _ _)
    next => exact (hRCf I s.1 hI).trans (Nat.le_add_right _ _)
  · -- the width
    intro I hI
    have h1 := RC.width_le I hI
    have hG : aggnL57GCap c b t d dc dp u v e f I.1 ≤ GK (aggnCheckedBound I.1.2.1.length) :=
      (hGKs I.1).trans (hGKm (hsizeC I hI))
    change I.2.elim (aggnAggregateWidth c I.1 + aggnL57Cap c b t d dc dp I.1 +
      aggnL57GCap c b t d dc dp u v e f I.1) (fun _ => 0) ≤ _
    change I.2.elim (aggnAggregateWidth c I.1 + aggnL57Cap c b t d dc dp I.1) (fun _ => 0) ≤
      RC.widthBound I.1.2.1.length at h1
    cases ho : I.2 with
    | none =>
      rw [ho] at h1
      simp only [Option.elim_none] at h1 ⊢
      change _ ≤ RC.widthBound I.1.2.1.length + GK (aggnCheckedBound I.1.2.1.length)
      omega
    | some W =>
      simp only [Option.elim_some]
      exact Nat.zero_le _

/-- The cost data of the round of lines 5–7 with the giant branch. -/
noncomputable def aggnL57GRunCostQ (c b t d dc dp u v e f : ℕ) :
    Round.RunCostQ (aggnL57GRound c b t d dc dp u v e f) :=
  Classical.choice (aggnL57G_hasRunCostQ c b t d dc dp u v e f)

end Algo
