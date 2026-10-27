import Workspace.Algo.TopMasterCallLetters

/-! # Normalized direct calls on the ambient master domain
Every proposed window call is read on its parent's domain. On a genuine
call, its decoded strings have the existing alphabet bound, so this
normalization preserves the entire instance and every admission check.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 def masterCheckedCall (z : RawStr × RawWinSI) : RawMasterSI :=
  (aggnCheckedWindow z, none)

 theorem polyFun_masterCheckedCall : PolyFun masterCheckedCall :=
  aggnPolyFun_checkedWindow.pair (polyFun_const none)

 theorem masterCheckedCall_degree (x : RawStr) (W : RawWinSI) :
    masterDegree (masterCheckedCall (x, W)) = x.length :=
  (aggnCheckedWindow_wf x W).2.2.2.2.2.1.1

 theorem masterCheckedCall_decode {n : ℕ} {x : RawStr} (hx : x.length = n)
    (W : RawWinSI) (hW : MasterCallLetters (2 * n + 1) (decWinSI n W)) :
    decWinSI n (masterCheckedCall (x, W)).1 = decWinSI n W :=
  aggnCheckedWindow_decode hx W (fun i => Nat.le_of_lt_succ (hW.1 i))
    (fun i => Nat.le_of_lt_succ (hW.2 i))

 theorem masterCheckedCall_wf (a b : ℕ) (x : RawStr) (W : RawWinSI) :
    MasterInputWF a b (masterCheckedCall (x, W)) := by
  have hw := aggnCheckedWindow_wf x W
  have hsize := aggnCheckedWindow_size hw
  refine ⟨?_, ?_, le_rfl⟩
  · have hpair := size_pair_le' (masterCheckedCall (x, W))
    have hn : Enc.size (masterCheckedCall (x, W)).2 = 2 := size_none
    rw [masterCheckedCall_degree]
    change Enc.size (masterCheckedCall (x, W)).1 ≤ _ at hsize
    unfold masterInputCap
    omega
  · change (aggnCheckedWindow (x, W)).1.length ≤ (aggnCheckedWindow (x, W)).2.2.2.1.length
    rw [hw.2.2.2.2.2.1.1]
    exact length_le_of_nodup_lt hw.1 hw.2.1

 theorem masterCheckedCall_window {n : ℕ} {x : RawStr} (hx : x.length = n) (W : RawWinSI) :
    masterWindowSize (masterCheckedCall (x, W)) = (decWinSI n W).windowSize := by
  have hw := aggnCheckedWindow_wf x W
  rw [hx] at hw
  change (aggnCheckedWindow (x, W)).1.length = (winSet n W.1).ncard
  rw [← ncard_winSet _ hw.1 hw.2.1]
  exact congrArg Set.ncard (aggnCheckedWin_decode hx W.1)

 theorem masterCheckedCall_measure {p : RawMasterSI} (W : RawWinSI)
    (hp : masterWindowSize p ≤ masterDegree p)
    (hW : (decWinSI (masterDegree p) W).windowSize < masterWindowSize p) :
    masterRawMeasure (masterCheckedCall (p.1.2.2.2.1, W)) < masterRawMeasure p := by
  have hn : masterDegree (masterCheckedCall (p.1.2.2.2.1, W)) = masterDegree p :=
    masterCheckedCall_degree _ _
  have hw := masterCheckedCall_window (n := masterDegree p) rfl W
  have hq : masterParameter (masterCheckedCall (p.1.2.2.2.1, W)) =
      2 * masterWindowSize (masterCheckedCall (p.1.2.2.2.1, W)) := rfl
  apply masterRawMeasure_lt hn _ _ (Or.inl (hw ▸ hW))
  · rw [hw]; exact hW.le
  · rw [hq, hw]; omega

/-- **Real calls pass the invariance check of `masterAdmit`.** Every call the paper's
algorithm makes is a coset instance (its window is invariant under the group of its
coset), and has the letter bound of `MasterCallLetters`. Then the normalized call
`masterCheckedCall` passes `rawIsInvariant`: its generators generate that group, and
its window is the call's window. -/
 theorem masterCheckedCall_rawIsInvariant {n : ℕ} {x : RawStr} (hx : x.length = n)
    (W : RawWinSI) (hW : MasterCallLetters (2 * n + 1) (decWinSI n W))
    {G : Subgroup (Perm (Fin n))} (hC : IsCosetInstance G (decWinSI n W)) :
    rawIsInvariant ((masterCheckedCall (x, W)).1.2.1, (masterCheckedCall (x, W)).1.1) =
      true := by
  have hw := aggnCheckedWindow_wf x W
  rw [hx] at hw
  rw [← masterCheckedCall_decode hx W hW] at hC
  exact rawIsInvariant_of_isCosetInstance hw hC

 theorem masterCheckedCall_admitted (a b : ℕ) {p : RawMasterSI} (W : RawWinSI)
    (hp : masterWindowSize p ≤ masterDegree p)
    (hW : (decWinSI (masterDegree p) W).windowSize < masterWindowSize p)
    (hL : MasterCallLetters (2 * masterDegree p + 1) (decWinSI (masterDegree p) W))
    {G : Subgroup (Perm (Fin (masterDegree p)))}
    (hC : IsCosetInstance G (decWinSI (masterDegree p) W)) :
    masterAdmitChild a b (p, some (masterCheckedCall (p.1.2.2.2.1, W))) =
      some (masterCheckedCall (p.1.2.2.2.1, W)) :=
  masterAdmitChild_some.mpr ⟨rfl, masterCheckedCall_wf a b _ _, masterCheckedCall_degree _ _,
    masterCheckedCall_measure W hp hW, masterCheckedCall_rawIsInvariant rfl W hL hC⟩

end Algo
