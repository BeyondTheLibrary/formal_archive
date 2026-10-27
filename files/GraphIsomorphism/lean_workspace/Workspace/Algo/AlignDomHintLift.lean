/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure Align, line 11 (§14.1), at a node of the Master Algorithm —
what the hinted call of lines 5–7 needs from the node carrier.
-/
import Workspace.Algo.AlignDomHintL57
import Workspace.Algo.TopMasterHintedL57

/-!
# The hinted call of lines 5–7 on the node carrier

The node carrier lifts each call of the round of lines 5–7 from the node's window `Δ` to the
node's domain (`Algo.topwRawInstance`) and normalizes it (`Algo.masterCheckedCall`).  The hint
of case 3 (`Algo.alignDomHintAt`) is good for the lifted call when the lifted call is the
dominant orbit of `G*` read on the domain (`Algo.alignDomHintAt_good`).  That splits in two:

* on the window, the call of the round is the dominant orbit of `G*`, with group `G*` (the
  Section 13 side, where the round is defined);
* the lift keeps both: its group is the preimage of the window call's group under the
  restriction to `Δ`, and its window is the image of the window call's window.  This is a
  property of the carrier alone, stated here as `Algo.MasterL57LiftFacts`.

`Algo.masterHintStepOK_of_liftFacts` puts the two together: it is the hinted branch of
`Algo.MasterHintStepOK` for the hint `Algo.alignDomHintAt`.
-/
set_option synthInstance.maxSize 2048

namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- **What the node carrier does to a window call** (the obligation of the carrier used by the
hinted call of lines 5–7): at a raw node `P` of degree `n`, a call `J` on the node's window
`Δ = P.1.1` whose group lies in the restriction of the node's group to `Δ` is lifted
(`Algo.topwRawInstance`) and normalized (`Algo.masterCheckedCall`) to a call on `Fin n`

* whose group is the preimage of the group of `J` under the restriction to `Δ`, and
* whose window is the image of the window of `J` under the numbering of `Δ`. -/
def MasterL57LiftFacts (n : ℕ) : Prop :=
  ∀ (P : RawMasterSI) (J V : RawWinSI) (hnd : P.1.1.Nodup) (hlt : ∀ u ∈ P.1.1, u < n)
    (hinv : IsInvariant (decGroup n P.1.2.1) (winSet n P.1.1)),
    MasterRawNode n P →
    J.1.Nodup → (∀ k ∈ J.1, k < P.1.1.length) → RawGens.WF P.1.1.length J.2.1 →
    decGroup P.1.1.length J.2.1 ≤
      (winRestrictHom n P.1.1 hnd hlt (decGroup n P.1.2.1) hinv).range →
    topwRawInstance (masterWinCtx P, J) = some V →
    (∀ g, g ∈ decGroup n (masterCheckedCall (P.1.2.2.2.1, V)).1.2.1 ↔
      ∃ h : g ∈ decGroup n P.1.2.1,
        winRestrictHom n P.1.1 hnd hlt (decGroup n P.1.2.1) hinv ⟨g, h⟩ ∈
          decGroup P.1.1.length J.2.1) ∧
    (∀ x : Fin n, x ∈ winSet n (masterCheckedCall (P.1.2.2.2.1, V)).1.1 ↔
      ∃ k ∈ winSet P.1.1.length J.1,
        ((winEquiv n P.1.1 hnd hlt k : ↥(winSet n P.1.1)) : Fin n) = x)

/-- §14.1, line 11, **the hinted call of lines 5–7 on the node carrier**: when the window
call `J` of the round is the dominant orbit of `G*` (its group is `G*` and its window is the
`G*`-orbit of a point of the dominant window) with more than `2|Δ|/3` points, the hint
`Algo.alignDomHintAt` meets the hinted branch of `Algo.MasterHintStepOK` for the lifted call,
given the carrier's obligation `Algo.MasterL57LiftFacts`. -/
theorem masterHintStepOK_of_liftFacts {n : ℕ} (hF : MasterL57LiftFacts n)
    {W : RawWinSI} {h : RawMasterHint} (hP : MasterNodeGood n (W, some h))
    {m : ℕ} [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    {ϕ : decGroup W.1.length (masterHintTop (W, h)).1.1.2 →* Perm (Fin m)}
    (hA : RawAction.WF W.1.length m (masterHintTop (W, h)).1 ϕ)
    (hG : IsTransitive (decGroup W.1.length (masterHintTop (W, h)).1.1.2))
    (hϕ : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength (decGroup W.1.length (masterHintTop (W, h)).1.1.2)))
    {t : ℕ} (ht : ∀ u : Fin W.1.length, tPoint ϕ u = t)
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    {o : RawAlignOutcome} {X' : Pt (SplitOutcomes (Fin m))}
    (hX : decAlignOutcome m o = some X')
    {α : ℝ} (hα : 1 / 2 < α)
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) X') (hm : 217 ≤ m)
    (hmn : m ≤ W.1.length)
    (hhd : alignRHasDom (alignRColorOf ((masterHintTop (W, h)).1, o)) = true)
    (hnt : 2 ≤ alignRMs ((masterHintTop (W, h)).1, o))
    (hLP : VeryLargeK (alignRMs ((masterHintTop (W, h)).1, o))
      (maxOrbitLength (decGroup W.1.length (alignPairG1 ((masterHintTop (W, h)).1, o)))))
    {J V : RawWinSI} (hJnd : J.1.Nodup) (hJlt : ∀ k ∈ J.1, k < W.1.length)
    (hJwf : RawGens.WF W.1.length J.2.1)
    (hJK : decGroup W.1.length J.2.1 =
      decGroup W.1.length (alignPairG1 ((masterHintTop (W, h)).1, o)))
    {u : Fin W.1.length}
    (hu : u ∈ winSet W.1.length (alignRDomWindow (alignRColorOf ((masterHintTop (W, h)).1, o),
      alignRDomColor (alignRColorOf ((masterHintTop (W, h)).1, o)))))
    (hJwin : winSet W.1.length J.1 =
      orbit (decGroup W.1.length (alignPairG1 ((masterHintTop (W, h)).1, o))) u)
    (hV : topwRawInstance (masterWinCtx (W, some h), J) = some V)
    (hbig : 2 * W.1.length < 3 * (masterCheckedCall (W.2.2.2.1, V)).1.1.length) :
    MasterHintStepOK n (W, some h) V
      (some (alignDomHintAt ((((masterHintTop (W, h)).1, o), W.1),
        (masterCheckedCall (W.2.2.2.1, V)).1))) := by
  obtain ⟨⟨hdeg, hWwf, hinv⟩, -⟩ := hP
  have hnd : W.1.Nodup := hWwf.1
  have hlt : ∀ u ∈ W.1, u < n := hWwf.2.1
  have hgs : RawGens.WF n W.2.1 := hWwf.2.2.1
  set A := (masterHintTop (W, h)).1 with hAdef
  have hAgrp : decGroup W.1.length A.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hgs hnd hlt hinv
  have hG1 : decGroup W.1.length (alignPairG1 (A, o)) ≤ decGroup W.1.length A.1.2 := by
    rw [decGroup_alignPairG1 hA hϕ hK hX]
    exact preimageSubgroup_le _ _
  have hJle : decGroup W.1.length J.2.1 ≤
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range := by
    rw [hJK, ← hAgrp]
    exact hG1
  obtain ⟨hKV, hwinV⟩ := hF (W, some h) J V hnd hlt hinv ⟨hdeg, hWwf, hinv⟩ hJnd hJlt hJwf
    hJle hV
  set C' := (masterCheckedCall (W.2.2.2.1, V)).1 with hC'
  have hC'wf := aggnCheckedWindow_wf W.2.2.2.1 V
  have hxn : W.2.2.2.1.length = n := hdeg
  rw [hxn] at hC'wf
  obtain ⟨hgood, hlen, hhalf, hlab⟩ := alignDomHintAt_good_alpha hnd hlt hinv hAgrp hA hG hϕ hvl ht
    hK hX hα hZ hm hmn hhd hnt hLP (W := C') hC'wf.1 hC'wf.2.1 hC'wf.2.2.1
    (fun g => by rw [hKV g, hJK]) hu
    (fun x => by
      rw [hwinV x, hJwin])
    hbig
  refine ⟨hgood, fun i hi => ?_, ?_⟩
  · have him : i < m := hlab i hi
    have hWn : W.1.length ≤ n := length_le_of_nodup_lt hnd hlt
    omega
  · have hmA : A.2.1.length = m := hA.2.1
    change 2 * (alignDomHintAt (((A, o), W.1), C')).1.1.length ≤ h.1.1.length
    have hAh : A.2.1 = h.1.1 := rfl
    rw [hlen, ← hAh, hmA]
    exact hhalf

end Algo
