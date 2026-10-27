import Workspace.Algo.TopMasterChainRoute

/-! # Restoring the candidate representative after the orbit chain
The representative shifts the root answer. Recursive children retain
their own candidate cosets, so their answers are passed through unchanged.
This is Equation (59) around the computed Chain Rule phase.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev MasterChainReturnNode := MasterChainNode × RawPerm
def masterChainReturnX (I : MasterChainReturnNode) : RawStr := I.1.1.1.2.2.2.1
def masterChainReturnChild (z : MasterChainReturnNode × ℕ × RawCoset) : Option MasterChainReturnNode :=
  (masterChainChild (z.1.1, z.2)).map (fun J => (J, z.1.2))
def masterChainReturnInit (I : MasterChainReturnNode) : RawCoset := masterChainInit I.1
def masterChainReturnCombine (z : MasterChainReturnNode × ℕ × RawCoset × RawCoset) : RawCoset :=
  masterChainCombine (z.1.1, z.2)
def masterChainReturnFinish (solve : RawWinSI → RawCoset) (z : MasterChainReturnNode × RawCoset) : RawCoset :=
  z.1.1.2.elim
    (top3Shift (masterChainReturnX z.1, z.1.2, masterChainFinish solve (z.1.1, z.2)))
    (fun _ => masterChainFinish solve (z.1.1, z.2))
def MasterChainReturnWF (a b : ℕ) (I : MasterChainReturnNode) : Prop :=
  MasterChainWF a b I.1 ∧ Enc.size I.2 ≤ strBound (masterChainReturnX I).length
noncomputable def masterChainReturnDecode (n : ℕ) (I : MasterChainReturnNode) : SIInstance (Fin n) ℕ :=
  masterChainDecode n I.1

def masterChainReturnRound (a b : ℕ) (solve : RawWinSI → RawCoset) :
    Round MasterChainReturnNode RawCoset RawCoset where
  WF := MasterChainReturnWF a b
  ground I := (masterChainReturnX I).length
  measure I := (masterChainRound a b solve).measure I.1
  width I := (masterChainRound a b solve).width I.1
  child := masterChainReturnChild
  init := masterChainReturnInit
  combine := masterChainReturnCombine
  finish := masterChainReturnFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    have h := (masterChainRound a b solve).child_eq_none I.1 j s hj
    change masterChainChild (I.1, j, s) = none at h
    simp [masterChainReturnChild, h]
  child_wf := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    have hK := (masterChainRound a b solve).child_wf I.1 j s K hI.1 hk
    obtain ⟨c, _, _, _, rfl⟩ := masterChainChild_some hk
    exact ⟨hK, hI.2⟩
  child_measure := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact (masterChainRound a b solve).child_measure I.1 j s K hI.1 hk
  child_ground := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact (masterChainRound a b solve).child_ground I.1 j s K hI.1 hk

theorem masterChainReturnLoopMatch {n a b : ℕ} {C : MasterChainInput} {r : RawPerm}
    (hx : C.1.2.2.2.1.length = n) (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : RawCoset} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))},
      LoopMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n) (C, none) w j s T →
      LoopMatch (masterChainReturnRound a b solve) (masterChainReturnDecode n) (decCoset n) ((C, none), r)
        w j s (T.bind (fun A => .done (decPerm n r • A))) := by
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    change masterChainChild ((C, none), j, s) = none at hc
    change decCoset n (masterChainFinish solve ((C, none), s)) = A at ha
    refine .done w j s _ ?_ ?_
    · change (masterChainChild ((C, none), j, s)).map _ = none
      rw [hc]
      rfl
    · change decCoset n (top3Shift (C.1.2.2.2.1, r, masterChainFinish solve ((C, none), s))) = _
      rw [decCoset_top3Shift hx, ha]
  | call w j s J k hc hn ih =>
    change masterChainChild ((C, none), j, s) = some J at hc
    change LoopMatch _ _ _ _ (w + 1) j s (.call (masterChainReturnDecode n (J, r)) _)
    refine .call w j s (J, r) _ ?_ ?_
    · change (masterChainChild ((C, none), j, s)).map _ = some (J, r)
      rw [hc]
      rfl
    · exact fun A hA => ih A hA

def masterChainReturnEnter (W : RawWinSI) : MasterChainReturnNode :=
  (masterChainPreparedEnter W, normPerm (W.2.2.2.1, W.2.2.1))

end Algo
