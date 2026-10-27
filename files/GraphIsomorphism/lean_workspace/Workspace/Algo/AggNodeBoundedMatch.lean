import Workspace.Algo.AggNodeBoundedRun
import Workspace.Algo.AggNodeCheckedMatch

/-! # The size cap preserves every certificate execution

The invariant holds for every normalized answer sequence. At an actual call,
the round's width gate bounds the number of answers so far. Thus the cap is
inactive after each update. Normalization preserves the decoded answer for
every supplied encoding, and the existing fixed-tree match supplies the
unchanged complete certificate stores.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

private theorem aggnEnvelopeBound_mono {c : ℕ} {C : AggnPhaseCtx}
    (B : AggnStateEnvelope c C) : Monotone (aggnEnvelopeBound B) := by
  intro j k hjk
  unfold aggnEnvelopeBound
  omega

private theorem aggnCheckedCall_index {c n : ℕ} {I J : AggnPhaseNode}
    {j : ℕ} {s : AggnPhaseState} (h : (aggnCheckedRound c n).child (I, j, s) = some J) :
    j + 1 ≤ aggnPhaseWidth c I.1 := by
  have hj : j < (aggnCheckedRound c n).width I := by
    by_contra hn
    have he := (aggnCheckedRound c n).child_eq_none I j s (Nat.le_of_not_gt hn)
    rw [he] at h
    contradiction
  change j < I.2.elim (aggnPhaseWidth c I.1) (fun _ => 0) at hj
  cases ho : I.2 <;> simp only [ho, Option.elim_none, Option.elim_some] at hj <;> omega

/-- Transport the existing exact match while normalizing arbitrary answer encodings. -/
theorem aggnBoundedLoopMatch {β : Type*} {c d n : ℕ} {I : AggnPhaseNode}
    (hlen : I.1.2.1.length = n) (B : AggnStateEnvelope c I.1)
    (hcap : aggnEnvelopeBound B (aggnPhaseWidth c I.1) ≤ aggnStateCap d I.1.2.1.length)
    {w j : ℕ} {s : AggnPhaseState} {S : SIReduction (Fin n) ℕ β}
    {Q : β → ℕ → ℕ → AggnPhaseState → Prop}
    (h : LoopMatchK (aggnCheckedRound c n) (aggnPhaseDecode n) (decCoset n) I w j s S Q) :
    AggnPhaseBound B j s →
      LoopMatchK (aggnBoundedRound c d n) (aggnPhaseDecode n) (decCoset n) I w j s S Q := by
  induction h with
  | done w j s b Q hQ => intro _; exact .done w j s b Q hQ
  | call w j s J cont Q hc hn ih =>
    intro hs
    have hj := aggnCheckedCall_index hc
    apply LoopMatchK.call (R := aggnBoundedRound c d n)
      (decI := aggnPhaseDecode n) (decA := decCoset n) (I := I) w j s J cont Q hc
    intro a ha
    have han : decCoset n (aggnNormAnswer I.1.2.1 a) = (aggnPhaseDecode n J).answer := by
      rw [aggnNormAnswer_decode hlen]
      exact ha
    have hb := hs.combine_norm a I rfl j
    have hsize := hb.size.trans ((aggnEnvelopeBound_mono B hj).trans hcap)
    have he : (aggnBoundedRound c d n).combine (I, j, s, a) =
        (aggnCheckedRound c n).combine (I, j, s, aggnNormAnswer I.1.2.1 a) :=
      aggnCapState_eq hsize
    rw [he]
    exact ih (aggnNormAnswer I.1.2.1 a) han hb

/-- No valid initial state is discarded either. -/
theorem aggnBoundedPhaseMatch {β : Type*} {c d n : ℕ} {C : AggnPhaseCtx}
    (hlen : C.2.1.length = n) (B : AggnStateEnvelope c C)
    (hcap : aggnEnvelopeBound B (aggnPhaseWidth c C) ≤ aggnStateCap d C.2.1.length)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ β} {Q : β → ℕ → AggnPhaseState → Prop}
    (h : PhaseMatch (aggnCheckedRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnCheckedRound c n).init (C, none)) S Q) :
    PhaseMatch (aggnBoundedRound c d n) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel 0 ((aggnBoundedRound c d n).init (C, none)) S Q := by
  have hb := aggnPhaseBound_init B
  dsimp only [aggnCheckedRound, aggnPhaseRound] at hb
  have hs := hb.size.trans ((aggnEnvelopeBound_mono B (Nat.zero_le _)).trans hcap)
  have he : (aggnBoundedRound c d n).init (C, none) = (aggnCheckedRound c n).init (C, none) := by
    dsimp only [aggnBoundedRound, aggnBoundedInit, aggnCheckedRound, aggnPhaseRound]
    exact aggnCapState_eq hs
  rw [he]
  exact fun r => aggnBoundedLoopMatch hlen B hcap (h r) hb

/-- Sec. 13.2, the full certificate phase has an actual `RunCostQ` carrier.
One cap exponent works for every degree, input, and correct-answer encoding.
The store conclusion is exactly the existing complete-store specification. -/
theorem aggnBounded_certificates (c : ℕ) : ∃ d : ℕ,
    (∀ n, Nonempty (Round.RunCostQ (aggnBoundedRound c d n))) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnCheckedRound c n).WF (C, none) →
      AggnPhaseCtxWF c n m C ϕ → IsGiantRep ϕ →
      LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      PhaseMatch (aggnBoundedRound c d n) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnPhaseWidth c C) 0 ((aggnBoundedRound c d n).init (C, none))
        (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            C.2.2.2 C.2.1 C.1.2.1))
        (fun _ _ v => v.1 = [] ∧ AggnStoresComplete c ϕ v.2.1) := by
  obtain ⟨d, hd⟩ := aggnEnvelope_exists c
  refine ⟨d, fun n => aggnBounded_hasRunCostQ c d n, ?_⟩
  intro n m C ϕ hI hC hgiant ht htm hx hy
  obtain ⟨B, hB⟩ := hd n (C, none) hI
  have hcap : aggnEnvelopeBound B (aggnPhaseWidth c C) ≤ aggnStateCap d C.2.1.length :=
    hB.trans (Nat.le_add_right _ _)
  exact aggnBoundedPhaseMatch hC.source B hcap (aggnChecked_certificates hC hgiant ht htm hx hy)

end Algo
