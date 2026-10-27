import Workspace.Algo.AggNodeEnum
import Workspace.LocalCertificates.StrongAggregate

/-! # Certificate lists extracted from a raw run

Fix a raw solver and read each stage's lists from its loop state. These lists
satisfy the strong-descent specifications. This does not yet give a phase
match: that match must handle every encoding of a correct child answer.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

/-- The raw state used to choose the lists at stage `i`. -/
def aggnStageInput (solve : RawLCSI → RawCoset) (p : RawLCLoop) (i : ℕ) : AggrInput :=
  aggrInputOf (lcLoop solve i p)

/-- The representative order actually selected in one raw run. -/
noncomputable def aggnCertReps (n : ℕ) (solve : RawLCSI → RawCoset) (p : RawLCLoop)
    (i : ℕ) : List (Perm (Fin n)) := aggrReps n (aggnStageInput solve p i)

/-- The orbit windows actually selected in one raw run. -/
def aggnCertWindows (n : ℕ) (solve : RawLCSI → RawCoset) (p : RawLCLoop)
    (i : ℕ) : List (Set (Fin n)) :=
  (aggrWindows (aggnStageInput solve p i)).map (winSet n)

section Certificate

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {st0 : RawLCSt} {solve : RawLCSI → RawCoset}
  (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
  (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)

include hsolve h0

/-- Every stage of the chosen run supplies the two cover equations. -/
theorem aggnCert_cover {i : ℕ} (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom)) :
    StrongStageCover (stages ϕ (decStrN n xs) (winSet m tdom) i)
      (aggnCertReps n solve ((xs, tdom), st0) i)
      (aggnCertWindows n solve ((xs, tdom), st0) i) := by
  have hs := stateFor_lcLoop hsolve h0 i (Nat.le_of_lt hi)
  change StrongStageCover _ (aggrReps n (aggrInputOf (lcLoop solve i ((xs, tdom), st0))))
    ((aggrWindows (aggrInputOf (lcLoop solve i ((xs, tdom), st0)))).map (winSet n))
  rw [lcLoop_eq_pair solve i st0]
  exact aggrStage_cover hs

/-- Every stage of the chosen run supplies the factorial and orbit bounds. -/
theorem aggnCert_bound {i : ℕ} (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom)) :
    StrongStageBound (stages ϕ (decStrN n xs) (winSet m tdom) i)
      (aggnCertReps n solve ((xs, tdom), st0) i)
      (aggnCertWindows n solve ((xs, tdom), st0) i) := by
  have hs := stateFor_lcLoop hsolve h0 i (Nat.le_of_lt hi)
  change StrongStageBound _ (aggrReps n (aggrInputOf (lcLoop solve i ((xs, tdom), st0))))
    ((aggrWindows (aggrInputOf (lcLoop solve i ((xs, tdom), st0)))).map (winSet n))
  rw [lcLoop_eq_pair solve i st0]
  exact aggrStage_bound hs

/-- The strong certificate with the raw lists has the paper's value. -/
theorem aggnCert_run :
    (certRunStrong ϕ (decStrN n xs) (winSet m tdom)
      (aggnCertReps n solve ((xs, tdom), st0))
      (aggnCertWindows n solve ((xs, tdom), st0))).run =
        (windowOut ϕ (decStrN n xs) (winSet m tdom),
          certK ϕ (decStrN n xs) (winSet m tdom)) :=
  run_certRunStrong _ _ (fun _ hi => aggnCert_cover hsolve h0 hi)

/-- Reading `lcOutOf` at the end agrees with the strong certificate value. -/
theorem aggnCert_readOut :
    let p := lcRun solve ((xs, tdom), st0)
    (winSet n (lcOutOf p).1, decGroup n (lcOutOf p).2.2.1) =
      (certRunStrong ϕ (decStrN n xs) (winSet m tdom)
        (aggnCertReps n solve ((xs, tdom), st0))
        (aggnCertWindows n solve ((xs, tdom), st0))).run := by
  dsimp only
  rw [aggnCert_run hsolve h0]
  have hs := stateFor_lcRun hsolve h0
  rw [show lcRun solve ((xs, tdom), st0) =
    ((xs, tdom), (lcRun solve ((xs, tdom), st0)).2) from
      Prod.ext (lcRun_fst (solve := solve)) rfl]
  exact Prod.ext (lcwOut_window hs) (lcwOut_certK hs)

/-- Theorem 13.1.3: the chosen raw lists give the strong-descent call bounds. -/
theorem aggnCert_calls (h5 : 5 ≤ (winSet m tdom).ncard) :
    (certRunStrong ϕ (decStrN n xs) (winSet m tdom)
      (aggnCertReps n solve ((xs, tdom), st0))
      (aggnCertWindows n solve ((xs, tdom), st0))).calls.length ≤
        Nat.factorial (winSet m tdom).ncard * Nat.card (Fin n) ^ 2 ∧
    ∀ I ∈ (certRunStrong ϕ (decStrN n xs) (winSet m tdom)
      (aggnCertReps n solve ((xs, tdom), st0))
      (aggnCertWindows n solve ((xs, tdom), st0))).calls,
      (winSet m tdom).ncard * I.Δ.ncard ≤ Nat.card (Fin n) := by
  simpa only [calls_certRunStrong] using
    theorem_13_1_3_strong_calls h5 (aggnCertReps n solve ((xs, tdom), st0))
      (aggnCertWindows n solve ((xs, tdom), st0))
      (fun _ hi => aggnCert_bound hsolve h0 hi)

end Certificate

end Algo
