import Workspace.Algo.AggNodeCompareBounded
import Workspace.Algo.AggNodeCompareCheckedMatch

/-! # Exact comparison execution with its RAM bound

One cap exponent works for every input degree and every correct-answer
encoding. The all-answer state invariant proves that the cap is inactive
at every actual recursive call and at initialization.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

private theorem aggnCompareEnvelopeBound_mono {c : ℕ} {C : AggnPhaseCtx}
    (B : AggnCompareEnvelope c C) : Monotone (aggnCompareEnvelopeBound B) := by
  intro j k hjk
  unfold aggnCompareEnvelopeBound
  omega

private theorem aggnCompareCheckedCall_index {c : ℕ} {I J : AggnPhaseNode}
    {j : ℕ} {s : AggnCompareState} (h : (aggnCompareCheckedRound c).child (I, j, s) = some J) :
    j + 1 ≤ aggnCompareWidth c I.1 := by
  have hj : j < (aggnCompareCheckedRound c).width I := by
    by_contra hn
    have he := (aggnCompareCheckedRound c).child_eq_none I j s (Nat.le_of_not_gt hn)
    rw [he] at h
    contradiction
  change j < I.2.elim (aggnCompareWidth c I.1) (fun _ => 0) at hj
  cases ho : I.2 <;> simp only [ho, Option.elim_none, Option.elim_some] at hj <;> omega

/-- Transport the existing exact match while normalizing arbitrary answer encodings. -/
theorem aggnCompareBoundedLoopMatch {β : Type*} {c d n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) (B : AggnCompareEnvelope c I.1)
    (hcap : aggnCompareEnvelopeBound B (aggnCompareWidth c I.1) ≤ aggnCompareStateCap d I.1.2.1.length)
    {w j : ℕ} {s : AggnCompareState} {S : SIReduction (Fin n) ℕ β}
    {Q : β → ℕ → ℕ → AggnCompareState → Prop}
    (h : LoopMatchK (aggnCompareCheckedRound c) (aggnPhaseDecode n) (decCoset n) I w j s S Q) :
    AggnCompareBound B j s →
      LoopMatchK (aggnCompareBoundedRound c d) (aggnPhaseDecode n) (decCoset n) I w j s S Q := by
  induction h with
  | done w j s b Q hQ => intro _; exact .done w j s b Q hQ
  | call w j s J cont Q hc hn ih =>
    intro hs
    have hj := aggnCompareCheckedCall_index hc
    apply LoopMatchK.call (R := aggnCompareBoundedRound c d)
      (decI := aggnPhaseDecode n) (decA := decCoset n) (I := I) w j s J cont Q hc
    intro a ha
    have han : decCoset n (aggnNormAnswer I.1.2.1 a) = (aggnPhaseDecode n J).answer := by
      rw [aggnNormAnswer_decode hlen]
      exact ha
    have hb := hs.combine_norm a I rfl j
    have hsize := hb.size.trans ((aggnCompareEnvelopeBound_mono B hj).trans hcap)
    have he : (aggnCompareBoundedRound c d).combine (I, j, s, a) =
        (aggnCompareCheckedRound c).combine (I, j, s, aggnNormAnswer I.1.2.1 a) :=
      aggnCompareCapState_eq hsize
    rw [he]
    exact ih (aggnNormAnswer I.1.2.1 a) han hb

/-- No valid initial state is discarded either. -/
theorem aggnCompareBoundedPhaseMatch {β : Type*} {c d n : ℕ} {C : AggnPhaseCtx}
    (hlen : C.2.1.length = n) (B : AggnCompareEnvelope c C)
    (hcap : aggnCompareEnvelopeBound B (aggnCompareWidth c C) ≤ aggnCompareStateCap d C.2.1.length)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnCompareState → Prop}
    (h : PhaseMatch (aggnCompareCheckedRound c) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnCompareCheckedRound c).init (C, none)) S Q) :
    PhaseMatch (aggnCompareBoundedRound c d) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnCompareBoundedRound c d).init (C, none)) S Q := by
  have hb := aggnCompareBound_init B
  dsimp only [aggnCompareCheckedRound, aggnCompareRound] at hb
  have hs := hb.size.trans ((aggnCompareEnvelopeBound_mono B (Nat.zero_le _)).trans hcap)
  have he : (aggnCompareBoundedRound c d).init (C, none) = (aggnCompareCheckedRound c).init (C, none) := by
    dsimp only [aggnCompareBoundedRound, aggnCompareBoundedInit, aggnCompareCheckedRound, aggnCompareRound]
    exact aggnCompareCapState_eq hs
  rw [he]
  exact fun r => aggnCompareBoundedLoopMatch hlen B hcap (h r) hb

/-- Section 13.2's full comparison phase, with one executable RAM carrier
for every degree and an exact result list for every correct-answer encoding. -/
theorem aggnCompareBounded_comparisons (c : ℕ) : ∃ d : ℕ,
    Nonempty (Round.RunCostQ (aggnCompareBoundedRound c d)) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnCompareCheckedRound c).WF (C, none) →
      AggnPhaseCtxWF c n m C ϕ → IsGiantRep ϕ → 2 ≤ C.2.2.2.length →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      PhaseMatch (aggnCompareBoundedRound c d) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnCompareWidth c C) 0 ((aggnCompareBoundedRound c d).init (C, none))
        (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))))
        (fun B _ v => v.1 = [] ∧ v.2.1.reverse.map (decCoset n) = B) := by
  obtain ⟨d, hd⟩ := aggnCompareEnvelope_exists c
  refine ⟨d, aggnCompareBounded_hasRunCostQ c d, ?_⟩
  intro n m C ϕ hI hC hgiant h2 hx hy
  obtain ⟨B, hB⟩ := hd (C, none) hI
  have hcap : aggnCompareEnvelopeBound B (aggnCompareWidth c C) ≤ aggnCompareStateCap d C.2.1.length :=
    hB.trans (Nat.le_add_right _ _)
  exact aggnCompareBoundedPhaseMatch hC.source B hcap
    (aggnCompareChecked_comparisons hC hgiant h2 hx hy)

end Algo
