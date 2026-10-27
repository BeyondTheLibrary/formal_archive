import Workspace.Algo.TopMasterChainReturn

/-! # Uniform RAM and storage bounds for the master orbit-chain return -/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets

theorem polyFun_masterChainReturnX : PolyFun masterChainReturnX :=
  (polyFun_fst.comp polyFun_fst).comp polyFun_masterChainX

theorem polyFun_masterChainReturnChild : PolyFun (masterChainReturnChild) := by
  have hc : PolyFun (fun z : MasterChainReturnNode × ℕ × RawCoset => masterChainChild (z.1.1, z.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp (polyFun_masterChainChild)
  exact ((hc.pair (polyFun_fst.comp polyFun_snd)).comp
    (PolyFun.optionElim (polyFun_const none)
      ((polyFun_fst.pair polyFun_snd).comp polyFun_some))).of_eq
      (fun z => by unfold masterChainReturnChild; cases masterChainChild (z.1.1, z.2) <;> rfl)

theorem polyFun_masterChainReturnInit : PolyFun masterChainReturnInit := polyFun_fst.comp polyFun_masterChainInit
theorem polyFun_masterChainReturnCombine : PolyFun masterChainReturnCombine :=
  ((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_masterChainCombine

theorem quasiFun_masterChainReturnFinish {solve : RawWinSI → RawCoset} (hsolve : QuasiFun solve) :
    QuasiFun (masterChainReturnFinish solve) := by
  have hI : PolyFun (fun z : MasterChainReturnNode × RawCoset => z.1.1) := polyFun_fst.comp polyFun_fst
  have hx : PolyFun (fun z : MasterChainReturnNode × RawCoset => masterChainReturnX z.1) :=
    polyFun_fst.comp polyFun_masterChainReturnX
  have hr : PolyFun (fun z : MasterChainReturnNode × RawCoset => z.1.2) := polyFun_fst.comp polyFun_snd
  have hfin := (hI.pair polyFun_snd).quasiFun.comp (quasiFun_masterChainFinish hsolve)
  have hshift := (hx.quasiFun.pair (hr.quasiFun.pair hfin)).comp polyFun_top3Shift.quasiFun
  exact (((hI.comp polyFun_snd).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hshift (polyFun_snd.quasiFun.comp hfin)))

def masterChainReturnCheck (a b : ℕ) (I : MasterChainReturnNode) : Bool :=
  masterChainCheck a b I.1 && decide (Enc.size I.2 ≤ strBound (masterChainReturnX I).length)

theorem polyFun_masterChainReturnCheck (a b : ℕ) : PolyFun (masterChainReturnCheck a b) :=
  wftPolyFun_and (polyFun_fst.comp (polyFun_masterChainCheck a b))
    ((polyFun_snd.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_masterChainReturnX.comp polyFun_length).comp polyFun_top4aStrBound))
theorem masterChainReturnCheck_spec (a b : ℕ) (I : MasterChainReturnNode) :
    masterChainReturnCheck a b I = true ↔ MasterChainReturnWF a b I := by
  simp [masterChainReturnCheck, MasterChainReturnWF, masterChainCheck_spec]

def masterChainReturnBound (a b n : ℕ) : ℕ :=
  16 * (masterDescBound a b n + strBound n + 4)
theorem polyBound_masterChainReturnBound (a b : ℕ) : PolyBound (masterChainReturnBound a b) :=
  (polyBound_const 16).mul (((polyBound_masterDescBound a b).add polyBound_strBound).add
    (polyBound_const 4))
theorem mono_masterChainReturnBound (a b : ℕ) : Monotone (masterChainReturnBound a b) := by
  intro N M h
  have := mono_masterDescBound a b h
  have := mono_strBound h
  unfold masterChainReturnBound
  omega
theorem masterDescBound_le_masterChainReturnBound (a b n : ℕ) :
    masterDescBound a b n ≤ masterChainReturnBound a b n := by
  unfold masterChainReturnBound
  omega

theorem masterChainReturnNode_size {a b : ℕ} {I : MasterChainReturnNode}
    (hI : MasterChainReturnWF a b I) :
    Enc.size I ≤ masterChainReturnBound a b (masterChainReturnX I).length := by
  have hnode := masterChainNode_size hI.1
  have hr := hI.2
  have hpair := size_pair_le' I
  change Enc.size I.1 ≤ masterDescBound a b (masterChainReturnX I).length at hnode
  unfold masterChainReturnBound
  omega

theorem masterChainReturnFinish_size (solve : RawWinSI → RawCoset) (I : MasterChainReturnNode) (s : RawCoset) :
    Enc.size (masterChainReturnFinish solve (I, s)) ≤ chainBound (masterChainReturnX I).length := by
  have hf := size_top2NormC_le (n := (masterChainReturnX I).length) rfl le_rfl
    (I.1.2.elim s solve)
  have hs := size_top3Shift_le (n := (masterChainReturnX I).length) rfl le_rfl I.2 (masterChainFinish solve (I.1, s))
  unfold masterChainReturnFinish
  dsimp only
  cases I.1.2 with
  | none => exact hs
  | some _ => exact hf

def masterChainReturnRunCostQ (a b : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (masterChainReturnRound a b solve) where
  bound := masterChainReturnBound a b
  polyBound_bound := polyBound_masterChainReturnBound a b
  mono_bound := mono_masterChainReturnBound a b
  stateBound := chainBound
  quasiPolyBound_stateBound := polyBound_chainBound.quasiPoly
  mono_stateBound := mono_chainBound
  widthBound := (masterChainRunCostQ a b solve hsolve).widthBound
  quasiPolyBound_widthBound := (masterChainRunCostQ a b solve hsolve).quasiPolyBound_widthBound
  quasiFun_child := (polyFun_masterChainReturnChild).quasiFun
  quasiFun_init := polyFun_masterChainReturnInit.quasiFun
  quasiFun_combine := polyFun_masterChainReturnCombine.quasiFun
  quasiFun_finish := quasiFun_masterChainReturnFinish hsolve
  ground_le := fun I => ((masterChainRunCostQ a b solve hsolve).ground_le I.1).trans (size_fst_le' I)
  size_le := fun _ hI => masterChainReturnNode_size hI
  init_le := fun I hI => (masterChainRunCostQ a b solve hsolve).init_le I.1 hI.1
  combine_le := by
    intro I j s z _ _ _
    change Enc.size (top2NormC (masterChainReturnX I) z) ≤ chainBound (masterChainReturnX I).length
    exact size_top2NormC_le rfl le_rfl z
  finish_le := by
    intro I s _ _
    have h := masterChainReturnFinish_size solve I s
    change Enc.size (masterChainReturnFinish solve (I, s)) ≤ masterChainReturnBound a b (masterChainReturnX I).length
    unfold masterChainReturnBound masterDescBound
    omega
  bot_le := fun n => ((masterChainRunCostQ a b solve hsolve).bot_le n).trans
    (masterDescBound_le_masterChainReturnBound a b n)
  width_le := fun I hI => (masterChainRunCostQ a b solve hsolve).width_le I.1 hI.1
  polyFun_ground := polyFun_masterChainReturnX.comp polyFun_length
  wfCheck := masterChainReturnCheck a b
  polyFun_wfCheck := polyFun_masterChainReturnCheck a b
  wfCheck_eq_true := masterChainReturnCheck_spec a b
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := fun I hI => (masterChainRunCostQ a b solve hsolve).measure_le I.1 hI.1

theorem polyFun_masterChainReturnEnter : PolyFun masterChainReturnEnter :=
  polyFun_masterChainPreparedEnter.pair
    ((((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))).comp polyFun_normPerm)

theorem masterChainReturnEnter_uniform_wf (A B : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (W : RawWinSI), W.2.2.2.1.length = n → Enc.size W ≤ topcsContextCap A B n →
      MasterChainReturnWF a b (masterChainReturnEnter W) := by
  obtain ⟨a, b, h⟩ := masterChainPreparedEnter_uniform_wf A B
  exact ⟨a, b, fun n W hn hW => ⟨h n W hn hW, size_perm_le' le_rfl (wf_normPerm rfl _)⟩⟩

end Algo
