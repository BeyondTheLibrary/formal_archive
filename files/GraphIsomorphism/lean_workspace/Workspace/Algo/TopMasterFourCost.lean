import Workspace.Algo.TopMasterFourCoset

/-! # Uniform RAM and storage bounds for the master line 4b phase -/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets

theorem polyFun_master4X : PolyFun master4X :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_snd

theorem polyFun_master4Child (e f u v : ℕ) : PolyFun (master4Child e f u v) := by
  have hc : PolyFun (fun z : Master4Node × ℕ × Top4State => top4wChild e f u v (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp (polyFun_top4wChild e f u v)
  exact ((hc.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.optionElim (polyFun_const none)
      ((polyFun_fst.pair polyFun_snd).comp polyFun_some))).of_eq
      (fun z => by unfold master4Child; cases top4wChild e f u v (z.1.1, z.2) <;> rfl)

theorem polyFun_master4Init : PolyFun master4Init := polyFun_fst.comp polyFun_top4wInit
theorem polyFun_master4Combine : PolyFun master4Combine :=
  ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_top4wCombine

theorem quasiFun_master4Finish {solve : RawWinSI → RawCoset} (hsolve : QuasiFun solve) :
    QuasiFun (master4Finish solve) := by
  have hI : PolyFun (fun z : Master4Node × Top4State => z.1.1) := polyFun_fst.comp polyFun_fst
  have hx : PolyFun (fun z : Master4Node × Top4State => master4X z.1) :=
    polyFun_fst.comp polyFun_master4X
  have hr : PolyFun (fun z : Master4Node × Top4State => z.1.2) := polyFun_fst.comp polyFun_snd
  have hfin := (hI.pair polyFun_snd).quasiFun.comp (quasiFun_top4wFinish hsolve)
  have hshift := (hx.quasiFun.pair (hr.quasiFun.pair hfin)).comp polyFun_top3Shift.quasiFun
  exact (((hI.comp polyFun_snd).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hshift (polyFun_snd.quasiFun.comp hfin)))

def master4Check (a b c d e f u v : ℕ) (I : Master4Node) : Bool :=
  top4wCheck a b c d e f u v I.1 && decide (Enc.size I.2 ≤ strBound (master4X I).length)

theorem polyFun_master4Check (a b c d e f u v : ℕ) : PolyFun (master4Check a b c d e f u v) :=
  wftPolyFun_and (polyFun_fst.comp (polyFun_top4wCheck a b c d e f u v))
    ((polyFun_snd.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_master4X.comp polyFun_length).comp polyFun_top4aStrBound))
theorem master4Check_spec (a b c d e f u v : ℕ) (I : Master4Node) :
    master4Check a b c d e f u v I = true ↔ Master4WF a b c d e f u v I := by
  simp [master4Check, Master4WF, top4wCheck_spec]

def master4Bound (a b c d e f u v n : ℕ) : ℕ :=
  16 * (top4wBound a b c d e f u v n + strBound n + 4)
theorem polyBound_master4Bound (a b c d e f u v : ℕ) : PolyBound (master4Bound a b c d e f u v) :=
  (polyBound_const 16).mul (((polyBound_top4wBound a b c d e f u v).add polyBound_strBound).add
    (polyBound_const 4))
theorem mono_master4Bound (a b c d e f u v : ℕ) : Monotone (master4Bound a b c d e f u v) := by
  intro N M h
  have := mono_top4wBound a b c d e f u v h
  have := mono_strBound h
  unfold master4Bound
  omega
theorem top4wBound_le_master4Bound (a b c d e f u v n : ℕ) :
    top4wBound a b c d e f u v n ≤ master4Bound a b c d e f u v n := by
  unfold master4Bound
  omega

theorem master4Node_size {a b c d e f u v : ℕ} {I : Master4Node}
    (hI : Master4WF a b c d e f u v I) :
    Enc.size I ≤ master4Bound a b c d e f u v (master4X I).length := by
  have hnode := top4wNode_size hI.1
  have hr := hI.2
  have hpair := size_pair_le' I
  change Enc.size I.1 ≤ top4wBound a b c d e f u v (master4X I).length at hnode
  unfold master4Bound
  omega

theorem master4Finish_size (solve : RawWinSI → RawCoset) (I : Master4Node) (s : Top4State) :
    Enc.size (master4Finish solve (I, s)) ≤ chainBound (master4X I).length := by
  have hf := size_top2NormC_le (n := (master4X I).length) rfl le_rfl
    (I.1.2.elim (topwCosetPreimage (I.1.1.1.1, I.1.1.1.2.1,
      top4aFinish solve (I.1.1.2, s))) solve)
  have hs := size_top3Shift_le (n := (master4X I).length) rfl le_rfl I.2 (top4wFinish solve (I.1, s))
  unfold master4Finish
  dsimp only
  cases I.1.2 with
  | none => exact hs
  | some _ => exact hf

def master4RunCostQ (a b c d e f u v : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (master4Round a b c d e f u v solve) where
  bound := master4Bound a b c d e f u v
  polyBound_bound := polyBound_master4Bound a b c d e f u v
  mono_bound := mono_master4Bound a b c d e f u v
  stateBound := top4wBound a b c d e f u v
  quasiPolyBound_stateBound := (polyBound_top4wBound a b c d e f u v).quasiPoly
  mono_stateBound := mono_top4wBound a b c d e f u v
  widthBound := (top4wRunCostQ a b c d e f u v solve hsolve).widthBound
  quasiPolyBound_widthBound := (top4wRunCostQ a b c d e f u v solve hsolve).quasiPolyBound_widthBound
  quasiFun_child := (polyFun_master4Child e f u v).quasiFun
  quasiFun_init := polyFun_master4Init.quasiFun
  quasiFun_combine := polyFun_master4Combine.quasiFun
  quasiFun_finish := quasiFun_master4Finish hsolve
  ground_le := fun I => ((top4wRunCostQ a b c d e f u v solve hsolve).ground_le I.1).trans (size_fst_le' I)
  size_le := fun _ hI => master4Node_size hI
  init_le := fun I hI => (top4wRunCostQ a b c d e f u v solve hsolve).init_le I.1 hI.1
  combine_le := by
    intro I j s z hI _ _
    have hctx := (size_fst_le' I.1.1.2.1).trans ((size_fst_le' I.1.1.2).trans
      ((size_snd_le' I.1.1).trans hI.1.1))
    have hh := top4Stored_size_context hctx
      (top4Combine_stored (I.1.1.2.1, j, s,
        topwCosetImage (I.1.1.1.1.1, I.1.1.1.2.1, z)))
    exact hh.trans (top4ContextBound_le_top4wBound a b c d e f u v _)
  finish_le := by
    intro I s _ _
    have h := master4Finish_size solve I s
    change Enc.size (master4Finish solve (I, s)) ≤ master4Bound a b c d e f u v (master4X I).length
    unfold master4Bound top4wBound
    omega
  bot_le := fun n => ((top4wRunCostQ a b c d e f u v solve hsolve).bot_le n).trans
    (top4wBound_le_master4Bound a b c d e f u v n)
  width_le := fun I hI => (top4wRunCostQ a b c d e f u v solve hsolve).width_le I.1 hI.1
  polyFun_ground := polyFun_master4X.comp polyFun_length
  wfCheck := master4Check a b c d e f u v
  polyFun_wfCheck := polyFun_master4Check a b c d e f u v
  wfCheck_eq_true := master4Check_spec a b c d e f u v
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := fun I hI => (top4wRunCostQ a b c d e f u v solve hsolve).measure_le I.1 hI.1

theorem polyFun_master4Enter : PolyFun master4Enter :=
  polyFun_masterLine4bEnter.pair
    ((((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair
      (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)).comp polyFun_normPerm)

theorem master4Enter_uniform_wf (A B c d e f u v : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (p : MasterHintInput), p.1.2.2.2.1.length = n → Enc.size p ≤ topcsContextCap A B n →
      Master4WF a b c d e f u v (master4Enter p) := by
  obtain ⟨a, b, h⟩ := masterLine4bEnter_uniform_wf A B c d e f u v
  exact ⟨a, b, fun n p hn hp => ⟨h n p hn hp, size_perm_le' le_rfl (wf_normPerm rfl _)⟩⟩

end Algo
