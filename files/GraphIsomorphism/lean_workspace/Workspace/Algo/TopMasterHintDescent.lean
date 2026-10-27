import Workspace.Algo.TopMasterDescentOpenCost
import Workspace.Algo.TopMasterWindowAction

/-! # The inherited giant action supplies the descent input
The hint images already follow the ambient generator order. Compose the
restriction action with the hinted action and retain those exact rows.
The actual line-2 test proves the representative-table guard.
-/
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

 def masterHintDescInput (p : MasterHintInput) : MasterDescInput := (p.1, p.2.1)
 def masterHintDescSelect (p : RawMasterSI) : MasterDescInput :=
  (p.1, p.2.elim ([], []) Prod.fst)
 theorem polyFun_masterHintDescInput : PolyFun masterHintDescInput :=
  polyFun_fst.pair (polyFun_snd.comp polyFun_fst)
 theorem polyFun_masterHintDescSelect : PolyFun masterHintDescSelect := by
  exact polyFun_fst.pair (((polyFun_snd.pair (polyFun_const (0 : ℕ))).comp
    (PolyFun.optionElim (polyFun_const (([], []) : List ℕ × RawGens))
      (polyFun_fst.comp polyFun_fst))).of_eq (fun p => by cases p.2 <;> rfl))

 theorem masterHintDescSelect_some (p : MasterHintInput) :
    masterHintDescSelect (p.1, some p.2) = masterHintDescInput p := rfl

section Action
variable {n m : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hw : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)

 noncomputable def masterHintDescHom : decGroup n p.1.2.1 →* Perm (Fin m) :=
  ϕ.comp (camActionRange (p := masterRestrictionAction p.1)
    (masterRestrictionAction_wf (W := p.1) hx hw hnd hlt hinv))

 include hp in
 theorem masterHintDescInput_wf : RawAction.WF n m (masterDescAction (masterHintDescInput p))
    (masterHintDescHom hx hw hnd hlt hinv (ϕ := ϕ)) :=
  masterCompose_wf (p := masterRestrictionAction p.1) (z := p.2.1)
    (masterRestrictionAction_wf (W := p.1) hx hw hnd hlt hinv) hp

 include hx hnd hlt in
 theorem masterHintDescInput_guard (hr : masterHintRoute p = 1) :
    (masterHintDescInput p).2.1.length ≤ guardBound 3 (masterHintDescInput p).1.2.2.2.1.length := by
  have h := (masterHintRoute_line2 p).mp hr
  have hl := Nat.log_mono_right (b := 2) (length_le_of_nodup_lt hnd hlt)
  change p.2.1.1.length ≤ (Nat.log 2 p.1.2.2.2.1.length + 1) ^ 3
  rw [hx]
  exact h.trans (Nat.pow_le_pow_left (by omega) 3)

end Action

 theorem masterHintDesc_cost (a b : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterDescOpenOps 3 masterHintDescSelect))) :=
  masterDescOpen_runCostQ a b 3 masterHintDescSelect polyFun_masterHintDescSelect (fun _ => rfl)

end Algo
