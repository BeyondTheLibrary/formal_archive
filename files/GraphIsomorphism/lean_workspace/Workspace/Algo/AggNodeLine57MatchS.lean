/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the Align exits of the round of Sec. 15, lines 5–7, with a condition
at every step that may read the fold state.
-/
import Workspace.Algo.AggNodeLine57GiantMatch
import Workspace.Algo.PhaseMatchS

/-!
# The Align exits of lines 5–7 with a condition at every step

`Algo.aggnL57G_align_match` and `Algo.aggnL57G_align_match_small` say that the round of lines
5–7 walks the Master's tree at the Align exits.  The hint routine of lines 5–7
(`Algo.masterL57Hint`) reads the header of Procedure Align from the fold state, so the
condition on a call at a step of stretch 3 has to know that the fold is in stretch 3, at a
state whose aggregate part is a state `sR` the two phases end in.  The simulation that proves
stretch 3 (`Algo.aggnL57G_of_stretch3`) records exactly that, so the same proof carries the
condition along (`Algo.phaseMatchS_sim`).  The calls of stretch 1 are small whatever the
state, so there the condition comes from the calls alone (`Algo.PhaseMatch.toS`).
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets Babai Equiv

section Match

variable {c b t d dc dp u v e f n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} {CM : ℕ → AggnL57GState → AggnPhaseNode → Prop}

/-- The states of stretch 3 the fold of lines 5–7 reaches from the end state `sR` of the
phases: none yet, or one step of Procedure Align (`Algo.l57Step`) on the header of `sR`. -/
def L57Reach (c b t d dc dp : ℕ) (C : AggnPhaseCtx) (sR : AggnAggregateState)
    (o : Option ADState) : Prop :=
  o = none ∨ ∃ st a, o = some (l57Step (aggnL57Hdr c b t d dc dp (C, sR), st, a))

/-- **Stretch 3 of `Algo.aggnL57Round` is stretch 3 of the round with the giant branch**
(`Algo.aggnL57G_of_stretch3`), with a condition at every step: at a step of stretch 3 the
fold state is `((sR, o), none)` for the state `sR` the phases ended in. -/
theorem aggnL57G_of_stretch3S {sR : AggnAggregateState} (hpost : AggnL57Post c dc dp C ϕ sR)
    (hoff : aggnL57GOn c b t d dc dp u v e f (C, sR) = false) {k jR : ℕ}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (V : SIInstance (Fin n) ℕ → Prop) (hV : ∀ K ∈ T.calls, V K)
    (hCM : ∀ j (s : AggnL57GState) J, s.1.1 = sR → s.2 = none → L57Reach c b t d dc dp C sR s.1.2 →
      (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V (aggnPhaseDecode n J) → CM j s J)
    (h : PhaseMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      k jR (sR, none) T
      (fun B j w => (aggnL57Round c b t d dc dp).child ((C, none), j, w) = none ∧
        decCoset n ((aggnL57Round c b t d dc dp).finish ((C, none), w)) = B)) :
    PhaseMatchS (aggnL57GRound c b t d dc dp u v e f) CM (aggnPhaseDecode n) (decCoset n)
      (C, none) k jR ((sR, none), none) T
      (fun B j w => (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, w) = none ∧
        decCoset n ((aggnL57GRound c b t d dc dp u v e f).finish ((C, none), w)) = B) := by
  have hagg := aggnL57_agg_done hpost
  let Rel : ℕ → AggnL57State → ℕ → AggnL57GState → Prop := fun jR vR jM vM =>
    jM = jR ∧ vM = (vR, none) ∧ vR.1 = sR ∧ L57Reach c b t d dc dp C sR vR.2
  have hA : ∀ j (w : AggnL57GState), w.1.1 = sR →
      aggnL57GActive c b t d dc dp u v e f ((C, none), j, w) = false := by
    intro j w hw
    apply aggnL57GActive_of_off
    dsimp only
    rw [hw]
    exact hoff
  have h1 := phaseMatchS_sim (M := aggnL57GRound c b t d dc dp u v e f) (CM := CM)
    (decI' := aggnPhaseDecode n) (I' := ((C, none) : AggnPhaseNode)) V Rel ?sim h hV
    (k := jR) (t := ((sR, none), none)) ⟨rfl, rfl, rfl, Or.inl rfl⟩
  case sim =>
    rintro j1 vR jM vM ⟨hj, hv, hs, hr⟩ J hJ hVJ
    subst jM vM
    have hch : (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j1, (vR, none)) =
        some J := by
      show aggnL57GChild c b t d dc dp u v e f ((C, none), j1, (vR, none)) = some J
      rw [aggnL57GChild_of_inactive (hA j1 _ hs)]
      exact hJ
    refine ⟨J, hch, rfl, hCM j1 (vR, none) J hs rfl hr hch hVJ, fun a => ⟨rfl, ?_, ?_, ?_⟩⟩
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
    · show L57Reach c b t d dc dp C sR (aggnL57Combine c b t d dc dp ((C, none), j1, vR, a)).2
      obtain ⟨s1, o⟩ := vR
      dsimp only at hs
      subst hs
      unfold aggnL57Combine
      dsimp only
      rw [hagg j1, Option.elim_none]
      exact Or.inr ⟨_, _, rfl⟩
  refine phaseMatchS_weaken h1 ?_
  rintro B j' w ⟨j1, vR, ⟨hc, hf⟩, hj, hv, hs, -⟩
  subst j' w
  refine ⟨?_, ?_⟩
  · show aggnL57GChild c b t d dc dp u v e f ((C, none), j1, (vR, none)) = none
    rw [aggnL57GChild_of_inactive (hA j1 _ hs)]
    exact hc
  · show decCoset n (aggnL57GFinish c b t d dc dp u v e f ((C, none), (vR, none))) = B
    rw [aggnL57GFinish_of_off (by dsimp only; rw [hs]; exact hoff)]
    exact hf

/-- Stretch 1 of the round with the giant branch (`Algo.aggnL57G_stretch1`), with a condition
at every step that holds at every state whose call has the property `V₁`. -/
theorem aggnL57G_stretch1S (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57GRound c b t d dc dp u v e f).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (V₁ : SIInstance (Fin n) ℕ → Prop)
    (hV₁ : ∀ K ∈ (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ())).calls, V₁ K)
    (hCM₁ : ∀ j s J, (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V₁ (aggnPhaseDecode n J) → CM j s J) :
    PhaseMatchS (aggnL57GRound c b t d dc dp u v e f) CM (aggnPhaseDecode n) (decCoset n)
      (C, none) (aggnAggregateWidth c C) 0 ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ()))
      (fun _ j w => j ≤ aggnAggregateWidth c C ∧ w = ((w.1.1, none), none) ∧
        AggnL57Post c dc dp C ϕ w.1.1) :=
  PhaseMatch.toS V₁ hCM₁ (aggnL57G_stretch1 hok hI hC hset ht htm hx hy) hV₁

/-- §15, lines 5–7, **the Align exit** (no dominant class, or `m*` large; `Algo.aggnL57G_align_match`)
with a condition at every step: at the steps of stretch 1 it follows from a property `V₁` of
the call, at the steps of stretch 3 from a property `V₃` of the call and the state of the
fold, which is `((sR, o), none)` for a state `sR` the phases end in. -/
theorem aggnL57G_align_matchS (hok : AggnPhasesOK c dc dp)
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
    (hng : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 ≠ 2)
    (V₁ V₃ : SIInstance (Fin n) ℕ → Prop)
    (hV₁ : ∀ K ∈ (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ())).calls, V₁ K)
    (hV₃ : ∀ K ∈ S.red.calls, V₃ K)
    (hCM₁ : ∀ j s J, (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V₁ (aggnPhaseDecode n J) → CM j s J)
    (hCM₃ : ∀ sR, AggnL57Post c dc dp C ϕ sR → ∀ j (s : AggnL57GState) J, s.1.1 = sR →
      s.2 = none → L57Reach c b t d dc dp C sR s.1.2 → (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V₃ (aggnPhaseDecode n J) → CM j s J) :
    LoopMatchS (aggnL57GRound c b t d dc dp u v e f) CM (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  rw [line57Shape_red_eq_bind]
  refine loopMatchS_of_phaseMatchS (phaseMatchS_bind
    (aggnL57G_stretch1S hok hI hC hset ht htm hx hy V₁ hV₁ hCM₁) ?_) (fun B j w hw => hw)
    (show aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C ≤ aggnAggregateWidth c C +
      aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C by omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨hjle, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  exact aggnL57G_of_stretch3S hpost (aggnL57GOn_of_tag hpost (hng sR hpost)) V₃ hV₃
    (hCM₃ sR hpost) (aggnL57_align_stretch3 hx hy S Ws hS hsmall hpost hjle)

/-- §15, lines 5–7, **the Align exit in case 1 of the repair of lines 7–11**
(`Algo.aggnL57G_align_match_small`) with a condition at every step, as in
`Algo.aggnL57G_align_matchS`. -/
theorem aggnL57G_align_match_smallS (hok : AggnPhasesOK c dc dp)
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
    (hng : ∀ s, AggnL57Post c dc dp C ϕ s → (aggnContinuation c b t d (C, s)).1 ≠ 2)
    (V₁ V₃ : SIInstance (Fin n) ℕ → Prop)
    (hV₁ : ∀ K ∈ (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) (.done ())).calls, V₁ K)
    (hV₃ : ∀ K ∈ S.red.calls, V₃ K)
    (hCM₁ : ∀ j s J, (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V₁ (aggnPhaseDecode n J) → CM j s J)
    (hCM₃ : ∀ sR, AggnL57Post c dc dp C ϕ sR → ∀ j (s : AggnL57GState) J, s.1.1 = sR →
      s.2 = none → L57Reach c b t d dc dp C sR s.1.2 → (aggnL57GRound c b t d dc dp u v e f).child ((C, none), j, s) = some J →
      V₃ (aggnPhaseDecode n J) → CM j s J) :
    LoopMatchS (aggnL57GRound c b t d dc dp u v e f) CM (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57GRound c b t d dc dp u v e f).width (C, none)) 0
      ((aggnL57GRound c b t d dc dp u v e f).init (C, none))
      ((Line57Shape.align (ϕ := ϕ) (ts := C.2.2.2.length) S).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) := by
  rw [line57Shape_red_eq_bind]
  refine loopMatchS_of_phaseMatchS (phaseMatchS_bind
    (aggnL57G_stretch1S hok hI hC hset ht htm hx hy V₁ hV₁ hCM₁) ?_) (fun B j w hw => hw)
    (show aggnAggregateWidth c C + aggnL57Cap c b t d dc dp C ≤ aggnAggregateWidth c C +
      aggnL57Cap c b t d dc dp C + aggnL57GCap c b t d dc dp u v e f C by omega)
  rintro - jR ⟨⟨sR, o⟩, p⟩ ⟨hjle, hv, hpost⟩
  simp only [Prod.mk.injEq] at hv
  obtain ⟨⟨-, rfl⟩, rfl⟩ := hv
  exact aggnL57G_of_stretch3S hpost (aggnL57GOn_of_tag hpost (hng sR hpost)) V₃ hV₃
    (hCM₃ sR hpost) (aggnL57_align_small_stretch3 hx hy S D hS hsmall hpost hjle)

end Match

end Algo
