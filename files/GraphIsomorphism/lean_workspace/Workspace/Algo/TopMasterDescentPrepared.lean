import Workspace.Algo.TopMasterDescentWindowMatch

/-! # The actual input and return routines for master line 2
Move the parent candidate to its group frame, restore the source outside
the window, and retain the supplied action rows. The final representative
shift returns the answer to the original candidate coset.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

 def masterDescPreparedInput (p : MasterDescInput) : MasterDescInput := (masterChainPrepared p.1, p.2)
 def masterDescPreparedSelect (p : RawMasterSI) : MasterDescInput :=
  masterDescPreparedInput (masterHintDescSelect p)

 theorem polyFun_masterDescPreparedInput : PolyFun masterDescPreparedInput :=
  (polyFun_fst.comp polyFun_masterChainPrepared).pair polyFun_snd
 theorem polyFun_masterDescPreparedSelect : PolyFun masterDescPreparedSelect :=
  polyFun_masterHintDescSelect.comp polyFun_masterDescPreparedInput

 def masterShiftOps {S : Type} (F : MasterOps S) : MasterOps S :=
  { F with finish := fun z => top3Shift (z.1.1.2.2.2.1, z.1.1.2.2.1, F.finish z) }

 theorem quasiFun_masterShiftFinish {S : Type} [Enc S] {F : MasterOps S}
    (hf : QuasiFun F.finish) : QuasiFun (masterShiftOps F).finish := by
  have hx : PolyFun (fun z : RawMasterSI × S => z.1.1.2.2.2.1) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hr : PolyFun (fun z : RawMasterSI × S => z.1.1.2.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  exact (hx.quasiFun.pair (hr.quasiFun.pair hf)).comp_poly polyFun_top3Shift

 theorem masterShiftOps_finish_size {S : Type} (F : MasterOps S) (p : RawMasterSI) (s : S) :
    Enc.size ((masterShiftOps F).finish (p, s)) ≤ chainBound (masterDegree p) :=
  size_top3Shift_le rfl le_rfl _ _

 theorem masterShiftOps_match {S : Type} (a b : ℕ) (F : MasterOps S)
    {n : ℕ} {p : RawMasterSI} (hx : p.1.2.2.2.1.length = n)
    {w j : ℕ} {s : S} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n) p w j s T) :
    LoopMatch (masterAdmittedRound a b (masterShiftOps F)) (fun J => decWinSI n J.1) (decCoset n) p w j s
      (T.bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  induction h with
  | done w j s A hc ha =>
    refine .done w j s _ hc ?_
    change decCoset n (top3Shift (p.1.2.2.2.1, p.1.2.2.1, F.finish (p, s))) = _
    rw [decCoset_top3Shift hx]
    exact congrArg (fun C => decPerm n p.1.2.2.1 • C) ha
  | call w j s J k hc hn ih =>
    exact .call w j s J _ hc (fun A hA => ih A hA)

 def masterDescPreparedOps (c : ℕ) : MasterOps AggnRecomputeState :=
  masterShiftOps (masterDescOpenOps c masterDescPreparedSelect)

set_option maxHeartbeats 1200000 in
/-- The prepared branch has one raw carrier at all ambient degrees. -/
theorem masterDescPrepared_runCostQ (a b c : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterDescPreparedOps c))) := by
  obtain ⟨B, hB, hmB, hbound⟩ := masterDescOpen_uniform_bounds a b c
    masterDescPreparedSelect polyFun_masterDescPreparedSelect (fun _ => rfl)
  have hf : QuasiFun (masterDescOpenOps c masterDescPreparedSelect).finish :=
    (((polyFun_fst.comp polyFun_masterDescPreparedSelect).pair polyFun_snd).comp_quasiFun
      (quasiFun_masterDescOpenFinish c))
  refine ⟨masterAdmittedRunCostQ a b (masterDescPreparedOps c) B B hB hmB hB
    (polyFun_masterDescPreparedSelect.comp_quasiFun (quasiFun_masterDescOpenWidth c))
    (((polyFun_fst.comp polyFun_masterDescPreparedSelect).pair polyFun_snd).comp_quasiFun
      (quasiFun_masterDescOpenChild c))
    (polyFun_masterDescPreparedSelect.comp_quasiFun (quasiFun_masterDescOpenInit c))
    (((polyFun_fst.comp polyFun_masterDescPreparedSelect).pair polyFun_snd).comp_quasiFun
      (quasiFun_masterDescOpenCombine c))
    (quasiFun_masterShiftFinish hf)
    (fun p hp => (hbound p hp).1)
    (fun p j s A hp _ _ => (hbound p hp).2.1 j s A) ?_
    (fun p hp => (hbound p hp).2.2)⟩
  intro p s _ _
  exact (masterShiftOps_finish_size _ p s).trans (by unfold masterInputCap; omega)

 theorem masterDescPrepared_action (p : MasterDescInput) :
    masterDescAction (masterDescPreparedInput p) = masterDescAction p := rfl

 theorem masterDescPrepared_id {n : ℕ} {p : MasterDescInput} (hx : p.1.2.2.2.1.length = n) :
    decPerm n (masterDescPreparedInput p).1.2.2.1 = 1 := decPerm_rawOne hx

 theorem masterDescPrepared_target {n : ℕ} {p : MasterDescInput}
    (hx : p.1.2.2.2.1.length = n) (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n) :
    decStrN n (masterDescPreparedInput p).1.2.2.2.2 =
      extendStr (winSet n p.1.1) (masterGroupInstance n p.1).x
        (restrictStr (winSet n p.1.1) (masterGroupInstance n p.1).y) :=
  masterChainPrepared_target hx hnd hlt
end Algo
