import Workspace.Algo.TopMasterChainRound

/-! # Complete local RAM bounds for the orbit Chain Rule -/
set_option maxHeartbeats 800000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem polyFun_masterChainX : PolyFun masterChainX :=
  pfst (psnd (psnd (psnd polyFun_fst)))

theorem polyFun_masterChainArray : PolyFun masterChainArray := by
  have hW : PolyFun (fun p : MasterChainInput => p.1) := polyFun_fst
  have hx := pfst (psnd (psnd (psnd hW)))
  have hy := psnd (psnd (psnd (psnd hW)))
  have hg := pfst (psnd hW)
  have hr := pfst (psnd (psnd hW))
  exact hx.pair (hy.pair (polyFun_snd.pair ((hg.pair hr).comp polyFun_some)))

theorem polyFun_masterChainLeaf : PolyFun masterChainLeaf :=
  ((polyFun_fst.comp polyFun_masterChainArray).pair polyFun_snd).comp polyFun_topclLeaf

theorem polyFun_masterChainChild : PolyFun masterChainChild := by
  let X := MasterChainNode × ℕ × RawCoset
  have hp : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hs : PolyFun (fun z : X => z.2.2) := psnd polyFun_snd
  have hj : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hw := (psnd hp).comp polyFun_length
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × X =>
      (z.2.1.1, some (masterChainLeaf (z.2.1.1, z.2.2.1, z.1)))) := by
    have hp' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.1.1) := polyFun_snd.comp hp
    have hj' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.2.1) := polyFun_snd.comp hj
    exact hp'.pair (((hp'.pair (hj'.pair polyFun_fst)).comp polyFun_masterChainLeaf).comp polyFun_some)
  have hmap := (hs.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) (hbody.comp polyFun_some))
  have hrun : PolyFun (fun z : X => if z.2.1 < z.1.1.2.length then
      z.2.2.map (fun c => (z.1.1, some (masterChainLeaf (z.1.1, z.2.1, c)))) else none) :=
    (PolyFun.ite ((hj.add (polyFun_const 1)).le hw) hmap (polyFun_const none)).of_eq (fun z => by
      cases z.2.2 <;> simp only [Option.elim_none, Option.elim_some, Option.map_none, Option.map_some]
        <;> simp [Nat.succ_le_iff])
  exact ((((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none)))).of_eq (fun _ => rfl)

theorem polyFun_masterChainInit : PolyFun masterChainInit :=
  ((polyFun_fst.comp polyFun_masterChainX).pair
    ((polyFun_fst.comp polyFun_masterChainArray).comp (psnd (psnd polyFun_snd)))).comp
      polyFun_top2NormC

theorem polyFun_masterChainCombine : PolyFun masterChainCombine :=
  (((pfst polyFun_fst).comp polyFun_masterChainX).pair (psnd (psnd polyFun_snd))).comp
    polyFun_top2NormC

theorem quasiFun_masterChainFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (masterChainFinish solve) := by
  have hx : QuasiFun (fun p : MasterChainNode × RawCoset => masterChainX p.1.1) :=
    ((pfst polyFun_fst).comp polyFun_masterChainX).quasiFun
  have hh : QuasiFun (fun p : MasterChainNode × RawCoset => p.1.2.elim p.2 solve) :=
    (((psnd polyFun_fst).pair polyFun_snd).quasiFun.comp
    (QuasiFun.optionElim polyFun_id.quasiFun (polyFun_fst.comp_quasiFun hs)))
  exact (hx.pair hh).comp polyFun_top2NormC.quasiFun

def masterChainCheck (a b : ℕ) (I : MasterChainNode) : Bool :=
  decide (Enc.size I.1 ≤ topcsContextCap a b (masterChainX I.1).length) &&
    I.2.elim true (fun W => decide (Enc.size W ≤ masterDescJobBound (Enc.size I.1)) &&
      decide (W.2.2.2.1.length = (masterChainX I.1).length))

theorem polyFun_masterChainCheck (a b : ℕ) : PolyFun (masterChainCheck a b) := by
  have hn : PolyFun (fun I : MasterChainNode => (masterChainX I.1).length) :=
    (polyFun_fst.comp polyFun_masterChainX).comp polyFun_length
  have hz : PolyFun (fun I : MasterChainNode => Enc.size I.1) := polyFun_fst.comp AggnSizeRoutine.polyFun_size
  have h1 := hz.le (hn.comp (polyFun_topcsContextCap a b))
  have hbody : PolyFun (fun p : RawWinSI × MasterChainInput =>
      decide (Enc.size p.1 ≤ masterDescJobBound (Enc.size p.2)) &&
        decide (p.1.2.2.2.1.length = (masterChainX p.2).length)) :=
    wftPolyFun_and ((polyFun_fst.comp AggnSizeRoutine.polyFun_size).le
      ((polyFun_snd.comp AggnSizeRoutine.polyFun_size).comp polyFun_masterDescJobBound))
      ((((pfst (psnd (psnd (psnd polyFun_fst)))).comp polyFun_length).natEq
        ((polyFun_snd.comp polyFun_masterChainX).comp polyFun_length)))
  exact wftPolyFun_and h1
    ((polyFun_snd.pair polyFun_fst).comp (PolyFun.optionElim (polyFun_const true) hbody))

theorem masterChainCheck_spec (a b : ℕ) (I : MasterChainNode) :
    masterChainCheck a b I = true ↔ MasterChainWF a b I := by
  cases ho : I.2 <;> simp [masterChainCheck, MasterChainWF, ho, and_assoc]

theorem masterChainNode_size {a b : ℕ} {I : MasterChainNode} (hI : MasterChainWF a b I) :
    Enc.size I ≤ masterDescBound a b (masterChainX I.1).length := by
  have hs := size_pair_le' I
  have hc := hI.1
  cases ho : I.2 with
  | none =>
    have he : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold masterDescBound
    omega
  | some W =>
    have hW := (hI.2 W ho).1
    have hm := mono_masterDescJobBound hc
    have he : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold masterDescBound
    omega

def masterChainRunCostQ (a b : ℕ) (solve : RawWinSI → RawCoset) (hs : QuasiFun solve) :
    Round.RunCostQ (masterChainRound a b solve) where
  bound := masterDescBound a b
  polyBound_bound := polyBound_masterDescBound a b
  mono_bound := mono_masterDescBound a b
  stateBound := chainBound
  quasiPolyBound_stateBound := polyBound_chainBound.quasiPoly
  mono_stateBound := mono_chainBound
  widthBound := topcsContextCap a b
  quasiPolyBound_widthBound := (polyBound_topcsContextCap a b).quasiPoly
  quasiFun_child := polyFun_masterChainChild.quasiFun
  quasiFun_init := polyFun_masterChainInit.quasiFun
  quasiFun_combine := polyFun_masterChainCombine.quasiFun
  quasiFun_finish := quasiFun_masterChainFinish hs
  ground_le := fun I => (length_le_size _).trans ((size_fst_le' I.1.1.2.2.2).trans
    ((size_snd_le' I.1.1.2.2).trans ((size_snd_le' I.1.1.2).trans
      ((size_snd_le' I.1.1).trans ((size_fst_le' I.1).trans (size_fst_le' I))))))
  size_le := fun _ hI => masterChainNode_size hI
  init_le := by
    intro I _
    change Enc.size (top2NormC (masterChainX I.1) (masterChainArray I.1).2.2.2) ≤ chainBound (masterChainX I.1).length
    exact size_top2NormC_le (n := (masterChainX I.1).length) rfl le_rfl _
  combine_le := by
    intro I j s z hI _ _
    change Enc.size (top2NormC (masterChainX I.1) z) ≤ chainBound (masterChainX I.1).length
    exact size_top2NormC_le rfl le_rfl _
  finish_le := by
    intro I s _ _
    have h := size_top2NormC_le (n := (masterChainX I.1).length) rfl le_rfl (I.2.elim s solve)
    change Enc.size (top2NormC (masterChainX I.1) (I.2.elim s solve)) ≤
      masterDescBound a b (masterChainX I.1).length
    unfold masterDescBound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ masterDescBound a b n
    rw [size_none]
    unfold masterDescBound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    cases I.2 with
    | none => exact (length_le_size _).trans ((size_snd_le' I.1).trans hI.1)
    | some _ => exact Nat.zero_le _
  polyFun_ground := (polyFun_fst.comp polyFun_masterChainX).comp polyFun_length
  wfCheck := masterChainCheck a b
  polyFun_wfCheck := polyFun_masterChainCheck a b
  wfCheck_eq_true := masterChainCheck_spec a b
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp
end Algo
