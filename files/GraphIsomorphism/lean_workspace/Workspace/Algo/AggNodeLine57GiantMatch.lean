/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the round of Sec. 15, lines 5–7, with the giant branch
(`Algo.aggnL57GRound`) matches the Master's reductions: at outcome (2a) of Theorem 13.2.1 the
two phases followed by Cor. 12.0.10, and at every other exit what `Algo.aggnL57Round` matches.
-/
import Workspace.Algo.AggNodeLine57Giant
import Workspace.Algo.AggNodeLine57Match

/-!
# The round of lines 5–7 with the giant branch matches the Master side

**Outcome (2a).** On the Master side, outcome (2a) of Theorem 13.2.1 is
`Babai.line5Case2aFunCoset`: the two phases of Procedure AggregateCertificates on the window,
then Cor. 12.0.10 with the choices of `Babai.SmallDefectData` (`Babai.line4bBranchCoset`),
both lifted from the window.  It is not a constructor of `Babai.Line57Shape`: the Master
dispatches it before `Babai.Line57Shape` is read (`Babai.line567aFunCoset`).  On the window
the tree is `(aggregateRoundStrong ϕ x y E (.done ∅)).bind (fun _ => T)` with `T` the tree of
Cor. 12.0.10.  `Algo.aggnL57G_giant_match` proves that the round walks this tree call for call
and returns its answer, when `T` is the tree the machine computes
(`Algo.top4AggregateTree`: the two large orbits read off the completed stores, and the
choices of Cor. 12.0.10 computed by the entry routine).  That hypothesis ties the Master's
supplied choices to the computed ones; the value of `T` is `Iso_G(x, y)` in any case
(`Algo.top4Aggregate_spec`).

The calls of Cor. 12.0.10 are windows of `Fin n` whose strings take their values among those
of `x` and `y` (`Algo.allCalls_top4AggregateTree`), so the checked window normalization of
the carrier changes none of them.

**The other exits.** At every other exit the round is `Algo.aggnL57Round`: stretch 3 of that
round transfers to this one (`Algo.aggnL57G_of_stretch3`), which gives the Align exits
(`Algo.aggnL57G_align_match`, `Algo.aggnL57G_align_match_small`) and the exits with no
versions (`Algo.aggnL57G_nil_match`, `Algo.aggnL57G_rejectCase_match`,
`Algo.aggnL57G_rejectDefect_match`).
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets Babai Equiv

/-! ## The well-formedness test of the giant branch holds -/

/-- The parameters `u v` of the test of the giant branch fit the nodes of the carrier: the
node of Cor. 12.0.10 read off a context of size at most the carrier's cap is well formed. -/
def L57GWFOK (u v e f : ℕ) : Prop :=
  ∀ (n : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState), C.1.1.1.length = n →
    Enc.size C ≤ 2 * aggnCheckedWindowBound n → Top4aWF u v e f (top4AggregateEnter (C, s))

theorem exists_l57GWFOK (e f : ℕ) : ∃ u v, L57GWFOK u v e f := by
  obtain ⟨K0, hK0, hK0m, hK0s⟩ := top4AggregateInput_size_bdd
  obtain ⟨a, a', hab⟩ := hK0.comp ((polyBound_const 2).mul aggnPolyBound_checkedWindow)
  obtain ⟨u, v, huv⟩ := top4AutoEnter_uniform_wf a a' e f
  exact ⟨u, v, fun n C s hn hC => huv n _ hn
    ((hK0s C s).trans ((hK0m hC).trans (hab n)))⟩

/-! ## The branch taken -/

section Branch

variable {c b t d dc dp u v e f : ℕ}

theorem aggnL57GActive_of_agg {z : AggnPhaseNode × ℕ × AggnL57GState}
    (h : aggnAggregateChild c (z.1, z.2.1, z.2.2.1.1) ≠ none) :
    aggnL57GActive c b t d dc dp u v e f z = false := by
  unfold aggnL57GActive
  cases hz : aggnAggregateChild c (z.1, z.2.1, z.2.2.1.1) with
  | none => exact absurd hz h
  | some J => simp

theorem aggnL57GActive_of_off {z : AggnPhaseNode × ℕ × AggnL57GState}
    (h : aggnL57GOn c b t d dc dp u v e f (z.1.1, z.2.2.1.1) = false) :
    aggnL57GActive c b t d dc dp u v e f z = false := by
  unfold aggnL57GActive
  rw [h, Bool.and_false]

theorem aggnL57GActive_of_on {z : AggnPhaseNode × ℕ × AggnL57GState} (ho : z.1.2 = none)
    (hagg : aggnAggregateChild c (z.1, z.2.1, z.2.2.1.1) = none)
    (h : aggnL57GOn c b t d dc dp u v e f (z.1.1, z.2.2.1.1) = true) :
    aggnL57GActive c b t d dc dp u v e f z = true := by
  unfold aggnL57GActive
  rw [ho, hagg, h]
  rfl

theorem aggnL57GChild_of_inactive {z : AggnPhaseNode × ℕ × AggnL57GState}
    (h : aggnL57GActive c b t d dc dp u v e f z = false) :
    aggnL57GChild c b t d dc dp u v e f z = aggnL57Child c b t d dc dp (z.1, z.2.1, z.2.2.1) := by
  unfold aggnL57GChild
  rw [h]
  rfl

theorem aggnL57GCombine_of_inactive {z : AggnPhaseNode × ℕ × AggnL57GState × RawCoset}
    (h : aggnL57GActive c b t d dc dp u v e f (z.1, z.2.1, z.2.2.1) = false) :
    aggnL57GCombine c b t d dc dp u v e f z =
      (aggnL57Combine c b t d dc dp (z.1, z.2.1, z.2.2.1.1, z.2.2.2), none) := by
  unfold aggnL57GCombine
  rw [h]
  rfl

theorem aggnL57GFinish_of_off {z : AggnPhaseNode × AggnL57GState}
    (h : aggnL57GOn c b t d dc dp u v e f (z.1.1, z.2.1.1) = false) :
    aggnL57GFinish c b t d dc dp u v e f z = aggnL57Finish (z.1, z.2.1) := by
  unfold aggnL57GFinish
  rw [h, Bool.and_false]
  rfl

end Branch

section Match

variable {c b t d dc dp u v e f n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- §15, line 5, **stretch 1**: the round runs the two phases of AggregateCertificates as the
aggregate carrier does, and ends them in a state `((s, none), none)` with `s` a state the
phases end in, at an index at most the width of the carrier. -/
theorem aggnL57G_stretch1 (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1) :
    PhaseMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnAggregateWidth c C) 0 ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ()))
      (fun _ j w => j ≤ aggnAggregateWidth c C ∧ w = ((w.1.1, none), none) ∧
        AggnL57Post c dc dp C ϕ w.1.1) := by
  set M := aggnL57GRound c b t d dc dp u v e f with hM
  have hP := phaseMatch_index (hok n m C ϕ hI hC hset ht htm hx hy)
  let Rel : ℕ → AggnAggregateState → ℕ → AggnL57GState → Prop := fun jR vR jM vM =>
    jM = jR ∧ vM = ((vR, none), none) ∧ aggnAggregatePack c dc dp C vR = vR
  have h1 := aggnPhaseMatch_sim (M := M) (decI' := aggnPhaseDecode n)
    (I' := ((C, none) : AggnPhaseNode)) Rel ?sim hP (k := 0) (t := M.init (C, none))
    ⟨rfl, rfl, aggnAggregateInit_pack c dc dp C⟩
  case sim =>
    rintro jR vR jM vM ⟨hj, hv, hpk⟩ J hJ
    subst jM vM
    have hJ' : aggnAggregateChild c ((C, none), jR, vR) = some J := hJ
    have hA : ∀ w : AggnL57GState, w.1.1 = vR →
        aggnL57GActive c b t d dc dp u v e f ((C, none), jR, w) = false := by
      intro w hw
      apply aggnL57GActive_of_agg
      dsimp only
      rw [hw, hJ']
      simp
    refine ⟨J, ?_, rfl, fun a => ⟨rfl, ?_, ?_⟩⟩
    · show aggnL57GChild c b t d dc dp u v e f ((C, none), jR, ((vR, none), none)) = some J
      rw [aggnL57GChild_of_inactive (hA _ rfl)]
      show aggnL57Child c b t d dc dp ((C, none), jR, (vR, none)) = some J
      unfold aggnL57Child
      rw [hJ']
      rfl
    · show aggnL57GCombine c b t d dc dp u v e f ((C, none), jR, ((vR, none), none), a) =
        ((aggnAggregateCombine c dc dp ((C, none), jR, vR, a), none), none)
      rw [aggnL57GCombine_of_inactive (hA _ rfl)]
      show (aggnL57Combine c b t d dc dp ((C, none), jR, (vR, none), a), none) = _
      unfold aggnL57Combine
      rw [hJ']
      rfl
    · exact aggnAggregateCombine_pack c dc dp ((C, none), jR, vR, a)
  refine phaseMatch_weaken h1 ?_
  rintro w j x ⟨jR, sR, ⟨⟨hq1, hstores, hq2, htbl⟩, hjle⟩, hj, hv, hpk⟩
  subst j x
  exact ⟨by omega, rfl, hpk, hq1, hstores, hq2, htbl⟩

/-- The test of outcome (2a) fails at a state the two phases end in whose tag is not `2`. -/
theorem aggnL57GOn_of_tag {s : AggnAggregateState} (hs : AggnL57Post c dc dp C ϕ s)
    (htag : (aggnContinuation c b t d (C, s)).1 ≠ 2) :
    aggnL57GOn c b t d dc dp u v e f (C, s) = false := by
  unfold aggnL57GOn
  dsimp only
  rw [hs.1]
  simp only [aggnL57Cont, htag, decide_false, Bool.false_and]

/-- **Stretch 3 of `Algo.aggnL57Round` is stretch 3 of this round** when the test of outcome
(2a) fails: from a state the two phases end in, both rounds make the same calls and give the
same answer. -/
theorem aggnL57G_of_stretch3 {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR)
    (hoff : aggnL57GOn c b t d dc dp u v e f (C, sR) = false) {k jR : ℕ}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      k jR (sR, none) T
      (fun B j w => (aggnL57Round c b t d dc dp).child ((C, none), j, w) = none ∧
        decCoset n ((aggnL57Round c b t d dc dp).finish ((C, none), w)) = B)) :
    PhaseMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      k jR ((sR, none), none) T
      (fun B j w => (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, w) = none ∧
        decCoset n ((aggnL57GRound c b t d dc dp u v e f).finish ((C, none), w)) = B) := by
  have hagg := aggnL57_agg_done hpost
  let Rel : ℕ → AggnL57State → ℕ → AggnL57GState → Prop := fun jR vR jM vM =>
    jM = jR ∧ vM = (vR, none) ∧ vR.1 = sR
  have hA : ∀ j (w : AggnL57GState), w.1.1 = sR →
      aggnL57GActive c b t d dc dp u v e f ((C, none), j, w) = false := by
    intro j w hw
    apply aggnL57GActive_of_off
    dsimp only
    rw [hw]
    exact hoff
  have h1 := aggnPhaseMatch_sim (M := aggnL57GRound c b t d dc dp u v e f)
    (decI' := aggnPhaseDecode n) (I' := ((C, none) : AggnPhaseNode)) Rel ?sim h
    (k := jR) (t := ((sR, none), none)) ⟨rfl, rfl, rfl⟩
  case sim =>
    rintro j1 vR jM vM ⟨hj, hv, hs⟩ J hJ
    subst jM vM
    refine ⟨J, ?_, rfl, fun a => ⟨rfl, ?_, ?_⟩⟩
    · show aggnL57GChild c b t d dc dp u v e f ((C, none), j1, (vR, none)) = some J
      rw [aggnL57GChild_of_inactive (hA j1 _ hs)]
      exact hJ
    · show aggnL57GCombine c b t d dc dp u v e f ((C, none), j1, (vR, none), a) = _
      rw [aggnL57GCombine_of_inactive (hA j1 _ hs)]
      rfl
    · show (aggnL57Combine c b t d dc dp ((C, none), j1, vR, a)).1 = sR
      obtain ⟨s1, o⟩ := vR
      dsimp only at hs
      subst hs
      unfold aggnL57Combine
      dsimp only
      rw [hagg j1, Option.elim_none, hpost.1]
  refine phaseMatch_weaken h1 ?_
  rintro B j' w ⟨j1, vR, ⟨hc, hf⟩, hj, hv, hs⟩
  subst j' w
  refine ⟨?_, ?_⟩
  · show aggnL57GChild c b t d dc dp u v e f ((C, none), j1, (vR, none)) = none
    rw [aggnL57GChild_of_inactive (hA j1 _ hs)]
    exact hc
  · show decCoset n (aggnL57GFinish c b t d dc dp u v e f ((C, none), (vR, none))) = B
    rw [aggnL57GFinish_of_off (by dsimp only; rw [hs]; exact hoff)]
    exact hf

/-- The tree of lines 5–7 at an exit is the two phases followed by the exit's reduction. -/
theorem line57Shape_red_eq_bind (S : Line57Shape (Fin n) ℕ (decGroup n C.1.1.2)
      (decStrN n C.2.1) (decStrN n C.2.2.1) ϕ C.2.2.2.length)
    (E : AggEnum (Fin n) (Fin m)) :
    S.red E = (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E (.done ())).bind
      (fun _ => S.inner) := by
  change aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E S.inner = _
  simp only [aggregateRoundStrong, SIReduction.bind_assoc]
  rfl

/-- §15, lines 5–7, **the Align exit on the RAM** for the round with the giant branch (no
dominant class, or `m*` large); the statement of `Algo.aggnL57_align_match`, with the tag not
`2`. -/
theorem aggnL57G_align_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (Ws : List (Set (Fin n)))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      AVDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S Ws)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = false)
    (hng : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 ≠ 2) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  rw [line57Shape_red_eq_bind]
  refine loopMatch_of_phaseMatch (phaseMatch_bind
    (aggnL57G_stretch1 hok hI hC hset ht htm hx hy) ?_) (fun B j w hw => hw)
    (show aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C ≤ aggnAggregateWidth c C +
      aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C by omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨hjle, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  exact aggnL57G_of_stretch3 hpost (aggnL57GOn_of_tag hpost (hng sR hpost))
    (aggnL57_align_stretch3 hx hy S Ws hS hsmall hpost hjle)

/-- §15, lines 5–7, **the Align exit in case 1 of the repair of lines 7–11**
for the round with the giant branch; the statement of `Algo.aggnL57_align_match_small`, with
the tag not `2`. -/
theorem aggnL57G_align_match_small (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (S : AlignShape (Fin n) ℕ (decGroup n C.1.1.2) (decStrN n C.2.1) (decStrN n C.2.2.1))
    (D : AlignDominantRoundData (Fin n))
    (hS : ∀ s, AggnL57Post c dc dp C ϕ s →
      ADDescribes n (aggnL57Hdr c b t d dc dp (C, s)) S D)
    (hsmall : ∀ s, AggnL57Post c dc dp C ϕ s →
      l57Small (aggnL57Hdr c b t d dc dp (C, s)) = true)
    (hng : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 ≠ 2) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  rw [line57Shape_red_eq_bind]
  refine loopMatch_of_phaseMatch (phaseMatch_bind
    (aggnL57G_stretch1 hok hI hC hset ht htm hx hy) ?_) (fun B j w hw => hw)
    (show aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C ≤ aggnAggregateWidth c C +
      aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C by omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨hjle, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  exact aggnL57G_of_stretch3 hpost (aggnL57GOn_of_tag hpost (hng sR hpost))
    (aggnL57_align_small_stretch3 hx hy S D hS hsmall hpost hjle)

/-- §15, lines 5–7, **the exits with no versions and no giant branch** for the round with the
giant branch; the statement of `Algo.aggnL57_nil_match`, with the tag not `2`. -/
theorem aggnL57G_nil_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s →
      (aggnContinuation c b t d (C, s)).1 ≠ 1 ∧ (aggnContinuation c b t d (C, s)).1 ≠ 3 ∧
        (aggnContinuation c b t d (C, s)).1 ≠ 4)
    (hng : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 ≠ 2) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ∅)) := by
  have he : (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ())).bind (fun _ => (.done ∅ : SIReduction (Fin n) ℕ (Set (Perm (Fin n))))) =
      aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ∅) := by
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [← he]
  refine loopMatch_of_phaseMatch (c := aggnAggregateWidth c C + 0) (phaseMatch_bind
    (aggnL57G_stretch1 hok hI hC hset ht htm hx hy) ?_) (fun B j w hw => hw) (by
      show aggnAggregateWidth c C + 0 ≤ aggnAggregateWidth c C +
        aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C
      omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨-, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  exact aggnL57G_of_stretch3 hpost (aggnL57GOn_of_tag hpost (hng sR hpost))
    (aggnL57_nil_stretch3 htag hpost jR)

/-- §15, lines 5–7, **the reject exit of outcome (2b)** for the round with the giant branch;
the statement of `Algo.aggnL57_rejectCase_match`. -/
theorem aggnL57G_rejectCase_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hcx : Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length)
    (hcy : ¬ (Case2 (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.2.1) C.2.2.2.length))
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 = 0) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.rejectCase (ϕ := ϕ) (ts := C.2.2.2.length) hcx hcy).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) :=
  aggnL57G_nil_match hok hI hC hset ht htm hx hy (fun s hs => by
    have := htag s hs
    omega) (fun s hs => by
    have := htag s hs
    omega)

/-- §15, lines 5–7, **the reject exit of outcome (3)** for the round with the giant branch;
the statement of `Algo.aggnL57_rejectDefect_match`. -/
theorem aggnL57G_rejectDefect_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hne : (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard ≠
      (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard)
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 = 5) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.rejectDefect (ϕ := ϕ) (ts := C.2.2.2.length) hne).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) :=
  aggnL57G_nil_match hok hI hC hset ht htm hx hy (fun s hs => by
    have := htag s hs
    omega) (fun s hs => by
    have := htag s hs
    omega)

/-! ## Outcome (2a) -/

/-- §15, line 5, outcome (2a), **the giant branch runs Cor. 12.0.10 call for call**: from a
state of `Algo.top4aRound` on the node of the branch, matched against a tree whose calls have
strings with values at most `2n`, the round runs the same calls from the corresponding state
and stops with the same answer. -/
theorem aggnL57G_top4_transport (hx : RawStr.WF n (2 * n) C.2.1)
    {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR)
    (hon : aggnL57GOn c b t d dc dp u v e f (C, sR) = true)
    {jR : ℕ} (hjle : jR ≤ aggnAggregateWidth c C) :
    ∀ {w j4 : ℕ} {st4 : Top4State} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))},
      LoopMatch (top4aRound u v e f l57gSolve) (top4aDecode n) (decCoset n)
        (aggnL57GNode c dc dp (C, sR)) w j4 st4 T →
      AllCalls (StrValsIn {x | x ≤ 2 * n}) T →
      j4 + w ≤ l57gW4 (aggnL57GNode c dc dp (C, sR)) →
      ∀ p : Option (ℕ × Top4State),
        p.getD (0, top4aInit (aggnL57GNode c dc dp (C, sR))) = (j4, st4) →
      PhaseMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n)
        (C, none) w (jR + j4) ((sR, none), p) T
        (fun B j z => (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, z) = none ∧
          decCoset n ((aggnL57GRound c b t d dc dp u v e f).finish ((C, none), z)) = B) := by
  have hagg := aggnL57_agg_done hpost
  have hxn : C.2.1.length = n := hx.1
  set I4 := aggnL57GNode c dc dp (C, sR) with hI4
  have hA : ∀ j (p : Option (ℕ × Top4State)),
      aggnL57GActive c b t d dc dp u v e f ((C, none), j, ((sR, none), p)) = true :=
    fun j p => aggnL57GActive_of_on rfl (hagg j) hon
  have hpos : ∀ p : Option (ℕ × Top4State),
      aggnL57GPos c dc dp (C, ((sR, none), p)) = p.getD (0, top4aInit I4) := fun _ => rfl
  intro w j4 st4 T h
  induction h with
  | done w j4 st4 a hc ha =>
    intro _ _ p hp
    refine phaseMatch_mono (phaseMatch_done ⟨?_, ?_⟩) (Nat.zero_le w)
    · show aggnL57GChild c b t d dc dp u v e f ((C, none), jR + j4, ((sR, none), p)) = none
      unfold aggnL57GChild
      rw [hA, if_pos rfl]
      unfold aggnL57GTopChild
      dsimp only
      rw [hpos, hp]
      split_ifs
      · change (top4aChild e f (I4, j4, st4)).bind _ = none
        change top4aChild e f (I4, j4, st4) = none at hc
        rw [hc]
        rfl
      · rfl
    · show decCoset n (aggnL57GFinish c b t d dc dp u v e f ((C, none), ((sR, none), p))) = a
      unfold aggnL57GFinish
      dsimp only
      rw [hon]
      simp only [Option.isNone_none, Bool.and_self, if_true]
      rw [hpos, hp]
      exact ha
  | call w j4 st4 J k hc hn ih =>
    rintro ⟨hPJ, hk⟩ hbud p hp
    change top4aChild e f (I4, j4, st4) = some J at hc
    obtain ⟨-, K, hK, rfl⟩ := top4aChild_some hc
    obtain ⟨-, W, rfl, -⟩ := top4Child_some hK
    have hgate : jR + j4 < aggnAggregateWidth c C + l57gW4 I4 := by omega
    have hdec : top4aDecode n (((I4.1.1, some W) : Top4Node), I4.2) =
        aggnPhaseDecode n (avEmb (C, W)) := by
      have hvals : StrValsIn {x | x ≤ 2 * n} (decWinSI n W) := hPJ
      exact (aggnCheckedWindow_decode hxn W (fun i => hvals.1 i) (fun i => hvals.2 i)).symm
    have hchild : (aggnL57GRound c b t d dc dp u v e f).child ((C, none), jR + j4, ((sR, none), p)) =
        some (avEmb (C, W)) := by
      show aggnL57GChild c b t d dc dp u v e f ((C, none), jR + j4, ((sR, none), p)) = _
      unfold aggnL57GChild
      rw [hA, if_pos rfl]
      unfold aggnL57GTopChild
      dsimp only
      rw [hpos, hp, if_pos hgate]
      change (top4aChild e f (I4, j4, st4)).bind _ = _
      rw [hc]
      rfl
    rw [hdec] at hn ⊢
    refine phaseMatch_call hchild (fun a ha => ?_)
    have hcomb : (aggnL57GRound c b t d dc dp u v e f).combine
        ((C, none), jR + j4, ((sR, none), p), a) =
        ((sR, none), some (j4 + 1, (top4aRound u v e f l57gSolve).combine (I4, j4, st4, a))) := by
      show aggnL57GCombine c b t d dc dp u v e f ((C, none), jR + j4, ((sR, none), p), a) = _
      unfold aggnL57GCombine
      rw [hA, if_pos rfl]
      unfold aggnL57GTopCombine
      dsimp only
      rw [hpos, hp, hpost.1, Nat.min_eq_left (show j4 + 1 ≤ l57gW4 (aggnL57GNode c dc dp (C, sR)) by
        rw [← hI4]; omega)]
      rfl
    rw [hcomb, show jR + j4 + 1 = jR + (j4 + 1) by omega]
    have ha' : decCoset n a = (top4aDecode n ((I4.1.1, some W), I4.2)).answer := by
      rw [hdec]; exact ha
    rw [← hdec]
    exact ih a ha' (hk _) (by omega) _ rfl

/-- §15, line 5, **outcome (2a) of Theorem 13.2.1 on the RAM**: when the tag the round
computes after the two phases of AggregateCertificates is `2`, the round
`Algo.aggnL57GRound` matches the Master's reduction of outcome (2a) on the window — the two
phases, then Cor. 12.0.10 (`Babai.line5Case2aFunCoset`, `Babai.line4bBranchCoset`) — call for
call, with the width of the node as budget, and returns its answer, provided the tree `T` of
Cor. 12.0.10 on the Master side is the one the machine computes from the completed stores
(`Algo.top4AggregateTree`). -/
theorem aggnL57G_giant_match (hok : AggnPhasesOK c dc dp) (hwf : L57GWFOK u v e f)
    (hcap : TopwpCap e f)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hm : HugeM m (Nat.card (Fin n)))
    (htag : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 = 2)
    (T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))))
    (hT : ∀ s (hs : AggnL57Post c dc dp C ϕ s) (h2a : aggnAggregateGiantBranch (C, s) = true),
      top4AggregateTree hC hs.2.2.1 hset hm h2a = T) :
    LoopMatch (aggnL57GRound c b t d dc dp u v e f) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done (∅ : Set (Perm (Fin n))))).bind
            (fun _ => T)) := by
  have he : (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done (∅ : Set (Perm (Fin n))))).bind (fun _ => T) =
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ())).bind (fun _ => T) := by
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [he]
  refine loopMatch_of_phaseMatch (phaseMatch_bind
    (aggnL57G_stretch1 hok hI hC hset ht htm hx hy) ?_) (fun B j w hw => hw)
    (show aggnAggregateWidth c C + aggnL57GCap c b t d dc dp u v e f C ≤ aggnAggregateWidth c C +
      aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C by omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨hjle, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  dsimp only at hjle hpost ⊢
  have htag2 := htag sR hpost
  have h2a : aggnAggregateGiantBranch (C, sR) = true :=
    ((aggnContinuation_tag c b t d (C, sR)).2.1.1 htag2).2
  have hnode : aggnL57GNode c dc dp (C, sR) = top4AggregateEnter (C, sR) := by
    unfold aggnL57GNode
    rw [hpost.1]
  have hxn : C.2.1.length = n := hx.1
  have hwfI : Top4aWF u v e f (aggnL57GNode c dc dp (C, sR)) := by
    rw [hnode]
    refine hwf n C sR hC.action.1 ?_
    have := hI.2.1
    rw [hxn] at this
    exact this
  have hon : aggnL57GOn c b t d dc dp u v e f (C, sR) = true := by
    unfold aggnL57GOn
    dsimp only
    rw [hpost.1, (top4aCheck_spec u v e f _).2 (by rw [← hpost.1] at hwfI ⊢; exact hwfI)]
    simp only [aggnL57Cont, htag2, decide_true, Bool.and_self]
  have hloop := top4Aggregate_loop (a := u) (b := v) hC hpost.2.2.1 hset hm h2a hcap l57gSolve
  rw [hT sR hpost h2a] at hloop
  dsimp only at hloop
  rw [← hnode] at hloop
  have hcalls : AllCalls (StrValsIn {x | x ≤ 2 * n}) T := by
    rw [← hT sR hpost h2a]
    exact allCalls_top4AggregateTree hC hpost.2.2.1 hset hm h2a
      (fun i => aggnDecodedStr_le hx i) (fun i => aggnDecodedStr_le hy i)
  have hmain := aggnL57G_top4_transport (b := b) (t := t) (d := d) hx hpost hon hjle hloop
    hcalls (by rw [l57gW4_eq, Nat.zero_add]) none rfl
  rw [Nat.add_zero] at hmain
  refine phaseMatch_mono hmain ?_
  have hc := aggnL57GW_le_cap c b t d dc dp u v e f C sR
  unfold aggnL57GW at hc
  rw [if_pos hon] at hc
  rw [l57gW4_eq]
  exact hc

end Match

end Algo
