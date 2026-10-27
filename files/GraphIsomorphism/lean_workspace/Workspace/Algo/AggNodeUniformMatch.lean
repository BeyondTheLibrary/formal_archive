import Workspace.Algo.AggNodeUniform
import Workspace.Algo.AggNodeBoundedMatch

/-! # The degree-uniform RAM carrier matches the certificate phase

Only the validity predicate changes from the fixed-degree carrier. All
observable calls and all state updates are identical. The final theorem
selects one cap exponent and one runnable carrier before quantifying over
input degrees and raw encodings.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem aggnUniformLoopMatch {β : Type*} {c d n : ℕ} {I : AggnPhaseNode}
    {w j : ℕ} {s : AggnPhaseState} {S : SIReduction (Fin n) ℕ β}
    {Q : β → ℕ → ℕ → AggnPhaseState → Prop}
    (h : LoopMatchK (aggnBoundedRound c d n) (aggnPhaseDecode n) (decCoset n) I w j s S Q) :
    LoopMatchK (aggnUniformRound c d) (aggnPhaseDecode n) (decCoset n) I w j s S Q := by
  induction h with
  | done w j s b Q hQ => exact .done w j s b Q hQ
  | call w j s J cont Q hc hn ih =>
    exact .call w j s J cont Q hc (fun a ha => ih a ha)

/-- Normalized input contexts enter the uniform carrier directly. -/
theorem aggnUniformWF_of_context {c d n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hshort : C.1.1.2.length ≤ n * n)
    (hletters : ∀ xs ∈ [C.1.1.1, C.1.2.1, C.2.1, C.2.2.1, C.2.2.2],
      ∀ a ∈ xs, a < 2 * n + 1) : (aggnUniformRound c d).WF (C, none) := by
  have h := aggnCheckedWF_of_context hC hshort hletters
  change AggnCheckedWF C.2.1.length (C, none)
  simpa only [hC.source] using h

/-- Sec. 13.2, one runnable machine carrier for every degree and every encoding
of correct recursive answers, with the original complete-store conclusion. -/
theorem aggnUniform_certificates (c : ℕ) : ∃ d : ℕ,
    Nonempty (Round.RunCostQ (aggnUniformRound c d)) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnUniformRound c d).WF (C, none) →
      AggnPhaseCtxWF c n m C ϕ → IsGiantRep ϕ →
      LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      PhaseMatch (aggnUniformRound c d) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnPhaseWidth c C) 0 ((aggnUniformRound c d).init (C, none))
        (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            C.2.2.2 C.2.1 C.1.2.1))
        (fun _ _ v => v.1 = [] ∧ AggnStoresComplete c ϕ v.2.1) := by
  obtain ⟨d, _, hmatch⟩ := aggnBounded_certificates c
  refine ⟨d, aggnUniform_hasRunCostQ c d, ?_⟩
  intro n m C ϕ hI hC hgiant ht htm hx hy
  have hIfixed : (aggnCheckedRound c n).WF (C, none) := by
    change AggnCheckedWF C.2.1.length (C, none) at hI
    simpa only [hC.source] using hI
  exact fun r => aggnUniformLoopMatch (hmatch n m C ϕ hIfixed hC hgiant ht htm hx hy r)

end Algo
