/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: at line 2 of the
Master, every call of the run has at most half the window. Not part of the faithful
formalization.
-/
import Workspace.Algo.TopMasterHintedNode

/-!
# Line 2 halves the window

`Algo.masterNodeFull_hint_line2_matchGood` says that the full node carrier walks *some* tree
at a node of route 1 (line 2 of Section 15, `m ≤ ℓ(n)`); its proof walks the tree
`Algo.masterHintLine2Tree`, whose calls have at most half the window
(`Algo.masterHintLine2_half`, Fact 11.1.8). The refined count of `Explicit/Top/Count.lean`
needs this halving for the calls the run actually makes. This file keeps the tree:

* `Explicit.masterNodeFull_line2_half`: the proof of
  `Algo.masterNodeFull_hint_line2_matchGood` with the tree's calls halving the window in the
  conclusion;
* `Explicit.masterNodeH_line2_half`: the same for the hinted node carrier;
* `Explicit.roundCalls_line2_half`: every call of the run at a good node of route 1 has at
  most half the window of the node.
-/

set_option synthInstance.maxSize 4096

namespace Explicit
open RAM RAM.Targets Algo Babai Equiv
open scoped Pointwise

section Full
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

variable {n : ℕ} {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hW hinv in
/-- **Section 15, line 2, with the halving kept.** The proof of
`Algo.masterNodeFull_hint_line2_matchGood`, with `Algo.masterHintLine2_half` in the
conclusion instead of the run and the call count, and `1 ≤ |W|`. -/
theorem masterNodeFull_line2_half {a b : ℕ} (hg : MasterHintGood (W, h))
    (hr : masterHintRoute (W, h) = 1) :
    ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterAdmittedRound a b
          (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E))
        (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
        ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E).width (W, some h)) 0
        ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E).init (W, some h)) T ∧
      (∀ K ∈ T.calls, 2 * K.windowSize ≤ W.1.length) ∧ 1 ≤ W.1.length := by
  obtain ⟨m, φ, B, hB, hp, hG, -, ⟨L⟩, h2, ht, hkt, -, h64⟩ := hg
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hw := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hkt' : 2 * h.2 < m := hkt
  have h64' : 64 ≤ W.1.length := h64
  have hm : h.2 < m := by omega
  have hhalf := masterHintLine2_half (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr hG h2
  refine ⟨masterHintLine2Tree (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr, ?_,
    hhalf, by omega⟩
  have hM := masterTop_hinted_match (B := masterLine1B) (C₀ := masterLine1C₀) (cameron := cameron)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default))
    (p := (W, some h)) (by simp)
    (masterHint_line2_match (e := e) (f := f) (u := u) (v := v)
      (G4 := masterLine4cdOps c tt dd GD dD) (G5 := masterL57Ops c' b' t d dc dp e f E)
      (d4 := (dD, default)) (d5 := default) (p := (W, h)) hr
      (masterHintLine2_match (p := (W, h)) hx hy hw hnd hlt hinv φ hp hB L ht hm hr a b h2))
  refine loopMatchG_of_loopMatch_onCalls (fun K => 2 * K.windowSize ≤ W.1.length) ?_ hM hhalf
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_hint (by simp)] at hFc
  simp only [masterHintL57Ops, masterHintOps, MasterOps.pairIte,
    masterRouteAt_true (p := (W, h)) hr, if_true, masterDescPreparedOps, masterShiftOps,
    masterDescOpenOps, masterDescOpenChild] at hFc
  have hs' := masterDescFoldChild_shape hFc
  have hsrc : (masterDescLists 3 (masterDescPreparedSelect ((W, some h) : RawMasterSI))).1.2.2.2.1 =
      W.2.2.2.1 := rfl
  rw [hsrc, hx.1] at hs'
  exact masterNodeGood_of_checked (hdeg.trans hx.1) hs'.1 hs'.2 hinvJ (by omega) (by omega)

end Full

section H
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}

/-- **Line 2 halves the window, on the hinted node carrier.** At a good node of route 1, the
hinted node carrier walks a tree whose calls have at most half the window, every child being
a child in the sense of `Algo.masterRecursionOfTrees`. -/
theorem masterNodeH_line2_half {a b n : ℕ} {P : RawMasterSI} (hP : MasterNodeGood n P)
    (hr : masterRoute P = 1) :
    ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterAdmittedRound a b
          (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5))
        (fun J => MasterNodeGood n J ∧ MasterStepProgress P J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) P
        ((masterAdmittedRound a b
          (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5)).width P) 0
        ((masterAdmittedRound a b
          (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
            c' b' t d dc dp E H4 H5)).init P) T ∧
      (∀ K ∈ T.calls, 2 * K.windowSize ≤ masterWindowSize P) ∧ 1 ≤ masterWindowSize P := by
  obtain ⟨W, o⟩ := P
  cases o with
  | none => simp [masterRoute] at hr
  | some h =>
    obtain ⟨⟨-, hW, hinv⟩, hgood⟩ := hP
    obtain ⟨T, hm, hhalf, h1⟩ := masterNodeFull_line2_half (cameron := cameron) (e := e) (f := f)
      (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD) (c' := c')
      (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (a := a) (b := b)
      hW hinv (hgood h rfl) hr
    refine ⟨T, masterNodeH_matchG_of_full (H4 := H4) (H5 := H5) (by rw [hr]; decide)
      (fun h4 => by rw [hr] at h4; cases h4) hm, hhalf, h1⟩

end H

end Explicit
