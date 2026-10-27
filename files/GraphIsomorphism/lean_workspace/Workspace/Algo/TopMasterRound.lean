import Workspace.Algo.TopMasterAdmission
import Workspace.Algo.AggNodeCheckedLocal

/-! # One uniform master carrier with admitted recursive calls
The branch dispatcher supplies local routines on a common fold-state
carrier. A single executable admission check enforces the round laws.
The cost package concerns only these local routines. Recursive work is
represented by children and is charged by the existing evaluator.
-/
namespace Algo
open RAM RAM.Targets Babai

structure MasterOps (S : Type) where
  width : RawMasterSI → ℕ
  child : RawMasterSI × ℕ × S → Option RawMasterSI
  init : RawMasterSI → S
  combine : RawMasterSI × ℕ × S × RawCoset → S
  finish : RawMasterSI × S → RawCoset

def masterGuardedChild {S : Type} (a b : ℕ) (F : MasterOps S)
    (z : RawMasterSI × ℕ × S) : Option RawMasterSI :=
  if z.2.1 < F.width z.1 then masterAdmitChild a b (z.1, F.child z) else none

 theorem masterGuardedChild_some {S : Type} {a b : ℕ} {F : MasterOps S}
    {p J : RawMasterSI} {j : ℕ} {s : S}
    (h : masterGuardedChild a b F (p, j, s) = some J) :
    j < F.width p ∧ F.child (p, j, s) = some J ∧ MasterInputWF a b J ∧
      masterDegree J = masterDegree p ∧ masterRawMeasure J < masterRawMeasure p ∧
        rawIsInvariant (J.1.2.1, J.1.1) = true := by
  unfold masterGuardedChild at h
  split_ifs at h with hj
  exact ⟨hj, masterAdmitChild_some.mp h⟩

def masterAdmittedRound {S : Type} (a b : ℕ) (F : MasterOps S) :
    Round RawMasterSI S RawCoset where
  WF := MasterInputWF a b
  ground := masterDegree
  measure := masterRawMeasure
  width := F.width
  child := masterGuardedChild a b F
  init := F.init
  combine := F.combine
  finish := F.finish
  bot := none
  child_eq_none := by
    intro p j s hj
    exact if_neg (Nat.not_lt.mpr hj)
  child_wf := by
    intro p j s J _ hJ
    exact (masterGuardedChild_some hJ).2.2.1
  child_measure := by
    intro p j s J _ hJ
    exact (masterGuardedChild_some hJ).2.2.2.2.1
  child_ground := by
    intro p j s J _ hJ
    exact (masterGuardedChild_some hJ).2.2.2.1.le

 theorem quasiFun_masterGuardedChild {S : Type} [Enc S] (a b : ℕ) {F : MasterOps S}
    (hw : QuasiFun F.width) (hc : QuasiFun F.child) : QuasiFun (masterGuardedChild a b F) := by
  have hj : PolyFun (fun z : RawMasterSI × ℕ × S => z.2.1 + 1) :=
    (polyFun_snd.comp polyFun_fst).add (polyFun_const 1)
  have hg := (hj.quasiFun.pair (polyFun_fst.comp_quasiFun hw)).comp_poly polyFun_le
  have hrun := (polyFun_fst.quasiFun.pair hc).comp_poly (polyFun_masterAdmitChild a b)
  exact (aggnQuasiFun_ite hg hrun (quasiFun_const none)).of_eq
    (fun z => by simp only [masterGuardedChild, decide_eq_true_eq, Nat.add_one_le_iff])

 theorem masterDegree_le_size (p : RawMasterSI) : masterDegree p ≤ Enc.size p :=
  (length_le_size _).trans ((size_fst_le' p.1.2.2.2).trans ((size_snd_le' p.1.2.2).trans
    ((size_snd_le' p.1.2).trans ((size_snd_le' p.1).trans (size_fst_le' p)))))

/-- The uniform evaluator package, once the actual branch routines and
bounds have been assembled. There is no assumption on a recursive solver. -/
def masterAdmittedRunCostQ {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S)
    (stateBound widthBound : ℕ → ℕ)
    (hsb : QuasiPolyBound stateBound) (hsbm : Monotone stateBound)
    (hwb : QuasiPolyBound widthBound)
    (hw : QuasiFun F.width) (hc : QuasiFun F.child) (hi : QuasiFun F.init)
    (hu : QuasiFun F.combine) (hf : QuasiFun F.finish)
    (hinit : ∀ p, MasterInputWF a b p → Enc.size (F.init p) ≤ stateBound (masterDegree p))
    (hcombine : ∀ p j s A, MasterInputWF a b p → Enc.size s ≤ stateBound (masterDegree p) →
      Enc.size A ≤ masterInputCap a b (masterDegree p) →
        Enc.size (F.combine (p, j, s, A)) ≤ stateBound (masterDegree p))
    (hfinish : ∀ p s, MasterInputWF a b p → Enc.size s ≤ stateBound (masterDegree p) →
      Enc.size (F.finish (p, s)) ≤ masterInputCap a b (masterDegree p))
    (hwidth : ∀ p, MasterInputWF a b p → F.width p ≤ widthBound (masterDegree p)) :
    Round.RunCostQ (masterAdmittedRound a b F) where
  bound := masterInputCap a b
  polyBound_bound := polyBound_masterInputCap a b
  mono_bound := mono_masterInputCap a b
  stateBound := stateBound
  quasiPolyBound_stateBound := hsb
  mono_stateBound := hsbm
  widthBound := widthBound
  quasiPolyBound_widthBound := hwb
  quasiFun_child := quasiFun_masterGuardedChild a b hw hc
  quasiFun_init := hi
  quasiFun_combine := hu
  quasiFun_finish := hf
  ground_le := masterDegree_le_size
  size_le := fun _ h => h.1
  init_le := hinit
  combine_le := hcombine
  finish_le := hfinish
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ masterInputCap a b n
    rw [size_none]
    unfold masterInputCap
    omega
  width_le := hwidth
  polyFun_ground := polyFun_masterDegree
  wfCheck := masterInputCheck a b
  polyFun_wfCheck := polyFun_masterInputCheck a b
  wfCheck_eq_true := masterInputCheck_spec a b
  measureBound := masterMeasureBound
  polyBound_measureBound := polyBound_masterMeasureBound
  mono_measureBound := mono_masterMeasureBound
  measure_le := fun _ h => masterRawMeasure_le h.2.1 h.2.2

/-- The local cost data of a carrier: the arguments of `masterAdmittedRunCostQ`,
kept as data so that carriers can be combined before they are run. The update
and final bounds hold for every fold state, so that they survive when two
carriers share one state type. -/
structure MasterOpsCost {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S) where
  stateBound : ℕ → ℕ
  widthBound : ℕ → ℕ
  quasiPoly_state : QuasiPolyBound stateBound
  mono_state : Monotone stateBound
  quasiPoly_width : QuasiPolyBound widthBound
  quasiFun_width : QuasiFun F.width
  quasiFun_child : QuasiFun F.child
  quasiFun_init : QuasiFun F.init
  quasiFun_combine : QuasiFun F.combine
  quasiFun_finish : QuasiFun F.finish
  init_le : ∀ p, MasterInputWF a b p → Enc.size (F.init p) ≤ stateBound (masterDegree p)
  combine_le : ∀ p j s A, MasterInputWF a b p →
    Enc.size A ≤ masterInputCap a b (masterDegree p) →
      Enc.size (F.combine (p, j, s, A)) ≤ stateBound (masterDegree p)
  finish_le : ∀ p s, MasterInputWF a b p →
    Enc.size (F.finish (p, s)) ≤ masterInputCap a b (masterDegree p)
  width_le : ∀ p, MasterInputWF a b p → F.width p ≤ widthBound (masterDegree p)

/-- A carrier with its local cost data runs as one raw round. -/
def MasterOpsCost.runCostQ {S : Type} [Enc S] {a b : ℕ} {F : MasterOps S}
    (C : MasterOpsCost a b F) : Round.RunCostQ (masterAdmittedRound a b F) :=
  masterAdmittedRunCostQ a b F C.stateBound C.widthBound C.quasiPoly_state C.mono_state
    C.quasiPoly_width C.quasiFun_width C.quasiFun_child C.quasiFun_init C.quasiFun_combine
    C.quasiFun_finish C.init_le (fun p j s A hp _ hA => C.combine_le p j s A hp hA)
    (fun p s hp _ => C.finish_le p s hp) C.width_le

 theorem masterGuardedChild_chain {S : Type} (a b : ℕ) {F : MasterOps S}
    {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (h2 : 1 < (winOrbits (W.2.1, W.1)).length)
    (u : RawCoset → S) (hw : F.width (W, none) = (winOrbits (W.2.1, W.1)).length)
    (hc : ∀ j s, F.child ((W, none), j, u s) = masterChainOpenChild (W, j, s))
    (j : ℕ) (s : RawCoset)
    (hcos : ∀ J, masterChainOpenChild (W, j, s) = some J →
      ∃ G : Subgroup (Equiv.Perm (Fin n)), IsCosetInstance G (decWinSI n J.1)) :
    masterGuardedChild a b F ((W, none), j, u s) = masterChainOpenChild (W, j, s) := by
  unfold masterGuardedChild
  rw [hw, hc]
  split_ifs with hj
  · exact masterChainOpen_admitted a b hW hinv h2 j s hcos
  · exact (masterChainOpenChild_eq_none W j s (Nat.le_of_not_gt hj)).symm

 theorem masterAdmittedRound_chain_match {S : Type} (a b : ℕ) {F : MasterOps S}
    {n B C₀ : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2) (q : ℕ) (hC : 1 < C₀)
    (u : RawCoset → S) (hw : F.width (W, none) = (winOrbits (W.2.1, W.1)).length)
    (hc : ∀ j s, F.child ((W, none), j, u s) = masterChainOpenChild (W, j, s))
    (hi : F.init (W, none) = u (masterChainOpenInit W))
    (hu : ∀ j s A, F.combine ((W, none), j, u s, A) = u (masterChainOpenCombine (W, j, s, A)))
    (hf : ∀ s, F.finish ((W, none), u s) = masterChainOpenFinish (W, s)) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (W, none) (F.width (W, none)) 0 (F.init (W, none))
      (masterChainReturnTree hW.2.2.1 hW.1 hW.2.1 hinv hr q hC) := by
  rw [hw, hi]
  apply masterChainOpen_match hW.2.2.2.2.2.1.1 hW.2.2.1 hW.1 hW.2.1 hinv hr q hC
    (masterAdmittedRound a b F) id u (W, none) (fun J => decWinSI n J.1) (fun _ => rfl)
  · intro j s hj
    change masterGuardedChild a b F ((W, none), j, u s) = none
    rw [masterGuardedChild_chain a b hW ((rawIsInvariant_eq_true_iff hW.2.2.1 hW.2.1).mpr hinv)
      (masterChainRoute_multiple hW.2.2.1 hW.1 hW.2.1 hinv hr hC) u hw hc j s
      (fun J hJ => by rw [hj] at hJ; cases hJ), hj]
  · intro j s J hj hG
    change masterGuardedChild a b F ((W, none), j, u s) = some J
    rw [masterGuardedChild_chain a b hW ((rawIsInvariant_eq_true_iff hW.2.2.1 hW.2.1).mpr hinv)
      (masterChainRoute_multiple hW.2.2.1 hW.1 hW.2.1 hinv hr hC) u hw hc j s
      (fun J' hJ' => by rw [hj] at hJ'; cases hJ'; exact hG), hj]
  · exact hu
  · exact hf
end Algo
