import Workspace.Algo.AggNodeLine57Match
import Workspace.Algo.AggNodeGuideRejectSpec

/-! # The local-guide reject exit of lines 5–7 on the RAM
Tag `6` of `aggnContinuation` is the exit of the local guide in outcome (3) of
Theorem 13.2.1. On the Master side it is the constructor
`Babai.Line57Shape.rejectGuide`, which carries the class condition
`Babai.GuideClassMissing`. Here the round of lines 5–7 is matched against the Master's
reduction of that exit: under outcome (3) at `x`, `|D(x)| = |D(y)|` and the class condition,
the computed tag is `6` (`aggnContinuation_six_classes`), so the round runs the two phases
of AggregateCertificates and answers `∅`.
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets Babai Equiv

variable {c b t d dc dp n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

/-- §15, lines 5–7, **the reject exit of the local guide on the RAM** (entry 121): under
outcome (3) at `x`, with `|D(x)| = |D(y)|`, and when some class of `∼` meets `y` and no tuple
of `x`, the round of lines 5–7 matches the Master's reduction of
`Babai.Line57Shape.rejectGuide`. -/
theorem aggnL57_rejectGuide_match (hok : AggnPhasesOK c dc dp)
    (hI : (aggnL57Round c b t d dc dp).WF (C, none)) (hC : AggnPhaseCtxWF c n m C ϕ)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
    (hx : RawStr.WF n (2 * n) C.2.1) (hy : RawStr.WF n (2 * n) C.2.2.1)
    (hW : Nonempty (Fin n))
    (h3 : (¬ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
        ¬ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length)) ∧
      (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard =
        (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard)
    (hg : GuideClassMissing ϕ C.2.2.2.length (decStrN n C.2.1) (decStrN n C.2.2.1) hset ht
      ((Nat.card_fin m).symm ▸ htm) hW) :
    LoopMatch (aggnL57Round c b t d dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
      ((aggnL57Round c b t d dc dp).width (C, none)) 0
      ((aggnL57Round c b t d dc dp).init (C, none))
      ((Line57Shape.rejectGuide (ϕ := ϕ) (ts := C.2.2.2.length) hset ht
          ((Nat.card_fin m).symm ▸ htm) hW hg).red
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m)))) :=
  aggnL57_nil_match hok hI hC hset ht htm hx hy (fun s hs => by
    have h6 := (aggnContinuation_six_classes hC hs.2.2.1 hs.2.2.2.2 hset ht htm b t d).mpr
      ⟨h3, hg⟩
    omega)

end Algo
