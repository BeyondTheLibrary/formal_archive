/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the line-1 threshold.
Not part of the faithful formalization.
-/
import Workspace.Explicit.Line1.Case

/-!
# The master recursion at explicit line-1 thresholds

The progress relation of the master recursion (`Algo.MasterStepProgress`) and the obligation of
a node (`Algo.MasterNodeTreeOK`) name the Chain Rule nodes through the route test at the fixed
thresholds (`Algo.masterLine1Route`). Here they are restated at any thresholds `B`, `C₀`
(`Explicit.MasterChainRuleNodeX`, `Explicit.MasterStepProgressX`,
`Explicit.MasterNodeTreeOKX`), and:

* the line-1 nodes: the proofs of `Algo.masterNodeFull_line1_matchG`,
  `Algo.masterNodeFull_cameron_matchG` and `Algo.masterNodeFull_line1_matchGood`, copied to
  constants with `Explicit.Line1OK` (`Explicit.masterNodeH_line1_treeOKX`);
* the hinted nodes: the node carrier runs the hinted carrier there whatever the thresholds,
  so a match at the fixed thresholds is a match at any thresholds
  (`Explicit.loopMatchG_hint_transport`, `Explicit.treeOKX_of_treeOK_hint`);
* `Explicit.masterRecursionOfTreesX`: the construction of `Algo.masterRecursionOfTrees`, with
  the progress relation at the thresholds `B`, `C₀`.
-/

set_option maxHeartbeats 1200000

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv
open scoped Pointwise

/-! ## The progress relation at thresholds `B`, `C₀` -/

/-- `Algo.MasterChainRuleNode` at the thresholds `B`, `C₀`: no hint, and the route test
selects step 3. -/
def MasterChainRuleNodeX (B C₀ : ℕ) (P : RawMasterSI) : Prop :=
  P.2 = none ∧ masterReduceRoute B C₀ P.1 = 2

/-- `Algo.MasterStepProgress` at the thresholds `B`, `C₀`. -/
def MasterStepProgressX (B C₀ : ℕ) (P J : RawMasterSI) : Prop :=
  (MasterChainRuleNodeX B C₀ P → masterWindowSize J < masterWindowSize P ∧
      masterParameter J ≤ masterParameter P) ∧
    (¬ MasterChainRuleNodeX B C₀ P → MakesProgress masterWindowSize masterParameter P J)

/-- `Algo.MasterNodeTreeOK` at the thresholds `B`, `C₀`. -/
def MasterNodeTreeOKX (B C₀ : ℕ) {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ)
    (q : ℕ → ℕ) (P : RawMasterSI) (T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))) : Prop :=
  LoopMatchG R (fun J => MasterNodeGood n J ∧ MasterStepProgressX B C₀ P J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) P (R.width P) 0 (R.init P) T ∧
    T.run = (decWinSI n P.1).answer ∧ T.calls.length ≤ q (masterWindowSize P) ∧
    (MasterChainRuleNodeX B C₀ P → 1 ≤ masterWindowSize P ∧
      (T.calls.map SIInstance.windowSize).sum ≤ masterWindowSize P)

theorem MasterNodeTreeOKX.mono_q {B C₀ : ℕ} {ω : Type} {R : Round RawMasterSI ω RawCoset}
    {n : ℕ} {q q' : ℕ → ℕ} {P : RawMasterSI} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : MasterNodeTreeOKX B C₀ R n q P T) (hq : ∀ m, q m ≤ q' m) :
    MasterNodeTreeOKX B C₀ R n q' P T :=
  ⟨h.1, h.2.1, h.2.2.1.trans (hq _), h.2.2.2⟩

/-! ## Line 1 with its children -/

/-- **The children of line 1 without hint have the checked shape.**  At a well-formed node
where the route test does not select step 6, every child the line-1 carrier proposes, at any
fold state, is a window instance of the checked shape on the same domain, without hint. -/
theorem masterLine1Ops_child_shapeX {B C₀ n : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {P J : RawMasterSI} {j : ℕ} {s : AggnRecomputeState} (hP : MasterRawNode n P)
    (hr : masterReduceRoute B C₀ P.1 ≠ 4)
    (h : (masterLine1Ops B C₀ cameron).child (P, j, s) = some J) :
    AggnCheckedWindowWF n J.1 ∧ J.2 = none := by
  obtain ⟨hdeg, hW, hinv⟩ := hP
  have hraw : rawIsInvariant (P.1.2.1, P.1.1) = true :=
    (rawIsInvariant_eq_true_iff hW.2.2.1 hW.2.1).mpr hinv
  simp only [masterLine1Ops, MasterOps.ite] at h
  split_ifs at h with h0 h1 h2 h3
  · exact absurd h (by simp [masterLeafOps])
  · exact absurd h (by simp [masterLeafOps])
  · exact masterChainOpenChild_wf hW hraw h
  · simp only [masterBlockOps, masterShiftOps, masterDescOpenOps, masterDescOpenChild] at h
    have hs := masterDescFoldChild_shape h
    have hx : (masterDescLists 3 (masterBlockSelect P)).1.2.2.2.1 = P.1.2.2.2.1 :=
      masterBlockSelect_source P
    have hd : P.1.2.2.2.1.length = n := hdeg
    rw [hx, hd] at hs
    exact hs
  · exfalso
    apply hr
    simp only [masterRouteIs, decide_eq_true_eq] at h0 h1 h2 h3
    have := masterReduceRoute_le_four B C₀ P.1
    omega


/-- The condition on the calls of a line-1 round without hinted children: a coset instance,
and a strictly smaller window (Chain Rule) or a window of at most half the size. -/
def MasterLine1CallOKX (B C₀ : ℕ) (n : ℕ) (W : RawWinSI) (K : SIInstance (Fin n) ℕ) : Prop :=
  (∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G K) ∧
    (masterReduceRoute B C₀ W = 2 → K.windowSize < (decWinSI n W).windowSize) ∧
    (masterReduceRoute B C₀ W ≠ 2 → 1 ≤ (decWinSI n W).windowSize ∧
      2 * K.windowSize ≤ (decWinSI n W).windowSize)

/-- A child whose decoded call passes `Explicit.MasterLine1CallOKX` makes the progress of
Sec. 11.4 from its line-1 parent. -/
theorem masterStepProgress_line1X {B C₀ n : ℕ} {W : RawWinSI} {J : RawMasterSI}
    (hW : AggnCheckedWindowWF n W) (hJ : MasterRawNode n J) (hJ2 : J.2 = none)
    (hV : MasterLine1CallOKX B C₀ n W (decWinSI n J.1)) : MasterStepProgressX B C₀ (W, none) J := by
  have hwJ := masterWindowSize_eq_of_rawNode hJ
  have hwP : masterWindowSize ((W, none) : RawMasterSI) = (decWinSI n W).windowSize :=
    (ncard_winSet W.1 hW.1 hW.2.1).symm
  have hpJ : masterParameter J = 2 * masterWindowSize J := by
    obtain ⟨J1, J2⟩ := J
    subst hJ2
    rfl
  have hpP := masterParameter_none (W := W)
  constructor
  · rintro ⟨-, h2⟩
    have := hV.2.1 h2
    omega
  · intro hc
    have h2 : masterReduceRoute B C₀ W ≠ 2 := fun h => hc ⟨rfl, h⟩
    obtain ⟨h1, hle⟩ := hV.2.2 h2
    exact Or.inl ⟨by omega, by omega⟩

section Case
variable {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {B C₀ : ℕ} (hL : Line1OK B C₀)

include hW in
/-- **The calls of line 1 without hinted children pass `Explicit.MasterLine1CallOKX`**: steps 1–2
make no call, step 3 makes the Chain Rule calls on the orbits (each a coset instance on a
smaller window), and step 5 makes the calls of the Luks step on the kernel orbits (each a
coset instance on at most half the window, `Babai.decreases_blockLuksBranch`). -/
theorem masterLine1Tree_calls_okX (hr : masterReduceRoute B C₀ W ≠ 4) :
    ∀ K ∈ (masterLine1TreeX hW hinv hc hs hL).calls, MasterLine1CallOKX B C₀ n W K := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  unfold masterLine1TreeX masterLine1CaseX
  by_cases h0 : masterReduceRoute B C₀ W = 0
  · rw [dif_pos h0, if_pos (by omega)]
    intro K hK
    simp [masterFixedStringCase, Line1Case.branch, bruteForceBranch, masterNodeShift] at hK
  rw [dif_neg h0]
  by_cases h1 : masterReduceRoute B C₀ W = 1
  · rw [dif_pos h1, if_pos (by omega)]
    intro K hK
    simp [masterSmallGroupCaseX, Line1Case.branch, bruteForceBranch, masterNodeShift] at hK
  rw [dif_neg h1, if_neg (by omega)]
  by_cases h2 : masterReduceRoute B C₀ W = 2
  · rw [dif_pos h2]
    intro K hK
    simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done,
      List.append_nil] at hK
    refine ⟨⟨_, calls_chainRuleCoset_isCosetInstance (masterChainData hW.2.2.1 hW.2.1 hinv)
      ⟨_, (masterChainRoute_nonempty hW.2.2.1 hW.1 hW.2.1 hinv h2
        hL.one_lt).choose_spec⟩ K hK⟩, fun _ => ?_,
      fun h => absurd h2 h⟩
    exact (masterChainCase_progress hW.2.2.1 hW.1 hW.2.1 hinv h2 _ hL.one_lt).1 K hK
  rw [dif_neg h2]
  by_cases h3 : masterReduceRoute B C₀ W = 3
  · rw [dif_pos h3]
    intro K hK
    simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done,
      List.append_nil] at hK
    let b := masterStepFiveData hW hx hinv hL.block h3
    change K ∈ (blockLuksCoset b).calls at hK
    refine ⟨⟨_, calls_blockLuksCoset_isCosetInstance b K hK⟩, fun h => absurd h h2,
      fun _ => ⟨?_, ?_⟩⟩
    · classical
      obtain ⟨w⟩ := b.transitive.nonempty
      have : 0 < Fintype.card (masterGroupInstance n W).Δ := Fintype.card_pos_iff.2 ⟨w⟩
      have := b.card_window
      change 1 ≤ (masterGroupInstance n W).windowSize
      omega
    · have hmem : alignInst K ∈ (blockLuksBranch b).calls := by
        rw [blockLuksBranch_eq, Babai.calls_alignRed]
        exact List.mem_map_of_mem hK
      have := decreases_blockLuksBranch b _ hmem
      rwa [windowSize_alignInst] at this
  exact absurd (masterReduceRoute_fourX h0 h1 h2 h3) hr

end Case

section FullMatch
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {B C₀ : ℕ}

/-- **Section 15, line 1, in the full node carrier, with its children.**  At a well-formed
node without hint where the route test does not select step 6, the full node carrier walks
the round of line 1 (`Explicit.masterLine1TreeX`), and every child it produces on the path of the
match is a well-formed raw node without hint that makes the progress of Sec. 11.4. -/
theorem masterNodeFull_line1_matchGX {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron) (hL : Line1OK B C₀)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (hr : masterReduceRoute B C₀ W ≠ 4) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterRawNode n J ∧ J.2 = none ∧ MasterStepProgressX B C₀ (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1TreeX hW hinv hc hs hL) := by
  have hm := masterTop_line1_matchX (a := a) (b := b) hW hinv hc hs hL
    (masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default) c' b' t d dc dp E)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default) hcap
  refine loopMatchG_of_loopMatch_onCalls (MasterLine1CallOKX B C₀ n W) ?_ hm
    (masterLine1Tree_calls_okX hW hinv hc hs hL hr)
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_line1 rfl] at hFc
  have hP : MasterRawNode n ((W, none) : RawMasterSI) := ⟨hW.2.2.2.2.2.1.1, hW, hinv⟩
  obtain ⟨hJW, hJ2⟩ := masterLine1Ops_child_shapeX hP hr hFc
  have hJ : MasterRawNode n J := ⟨hdeg.trans hW.2.2.2.2.2.1.1, hJW,
    (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
  exact ⟨hJ, hJ2, masterStepProgress_line1X hW hJ hJ2 hV⟩

end FullMatch

/-! ### The round of step 6 with its children -/

section FullMatch
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {B C₀ : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Section 15, line 1, step 6, in the full node carrier, with its children.**  At a
well-formed node without hint where the route test selects step 6, the full node carrier
walks the round of line 1 (`Explicit.masterLine1TreeX`), and every child it produces on the path
of the match is a good node (`Algo.MasterNodeGood`) that makes the progress of Sec. 11.4.
This is `Babai.DescentData.decreases_branch` on the raw nodes: when `G₁` is transitive the
child keeps the window and carries the Johnson hint of step 7, whose parameter `k ≤ |Δ|`
halves the parameter `2|Δ|` of the node (recurrence (ii)); otherwise the child is an orbit of
`G₁`, of at most half the window (Fact 11.1.8). -/
theorem masterNodeFull_cameron_matchGX {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron) (hL : Line1OK B C₀)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (hr4 : masterReduceRoute B C₀ W = 4) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterNodeGood n J ∧ MasterStepProgressX B C₀ (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1TreeX hW hinv hc hs hL) := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  have hw := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hr : masterReduceRoute B C₀ W = 4 := hr4
  have H := masterCamRoute_specX hx hw hnd hlt hinv hL.cam hr hc hs hL.b25
  have htr := masterCamRoute_transitive hw hnd hlt hinv hr
  have hn := masterCamRoute_two hw hnd hlt hinv hL.cam hr
  have h64 := masterCamRoute_window hw hnd hlt hinv hL.cam hr
  have hwindow := masterCamRoute_windowSize hw hnd hlt hinv hL.cam hr
  set cc := (masterCamRouteInput cameron (W, none)).1 with hcc
  have hsize : (masterGroupInstance n W).windowSize = W.1.length := ncard_winSet W.1 hnd hlt
  -- the condition on the calls: outside the transitive case, at most half the window
  let V : SIInstance (Fin n) ℕ → Prop := fun K =>
    (winOrbits (camLiftGens (cc, masterWindowBlockAction W), W.1)).length ≠ 1 →
      2 * K.windowSize ≤ W.1.length
  have hcalls : ∀ K ∈ (masterLine1TreeX hW hinv hc hs hL).calls, V K := by
    intro K hK hne
    have h0 : masterReduceRoute B C₀ W ≠ 0 := by omega
    have h1 : masterReduceRoute B C₀ W ≠ 1 := by omega
    have h2 : masterReduceRoute B C₀ W ≠ 2 := by omega
    have h3 : masterReduceRoute B C₀ W ≠ 3 := by omega
    unfold masterLine1TreeX masterLine1CaseX at hK
    rw [if_neg (by omega), dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3] at hK
    simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done,
      List.append_nil] at hK
    let D := masterCamDescentData hx hw hnd hlt hinv htr hn H.choose H.choose_spec.1
      H.choose_spec.2.1 hwindow
    change K ∈ D.cosetBranch.calls at hK
    have hnt : ¬ IsTransitive D.G₁ := fun ht => hne
      ((masterCamDescentData_transitive_iff hx hw hnd hlt hinv htr hn H.choose
        H.choose_spec.1 H.choose_spec.2.1 hwindow).mp ht)
    have hmem : alignInst K ∈ D.branch.calls := by
      rw [DescentData.branch_eq, calls_alignRed]
      exact List.mem_map_of_mem hK
    have := D.calls_windowSize_branch_of_not hnt _ hmem
    rw [windowSize_alignInst, hsize] at this
    exact this
  have hm := masterTop_line1_matchX (a := a) (b := b) hW hinv hc hs hL
    (masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default) c' b' t d dc dp E)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default) hcap
  refine loopMatchG_of_loopMatch_onCalls V ?_ hm hcalls
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_line1 rfl] at hFc
  have hnc : ¬ MasterChainRuleNodeX B C₀ ((W, none) : RawMasterSI) := fun hch => by
    have := hch.2
    change masterReduceRoute B C₀ W = 2 at this
    omega
  have hpP : masterParameter ((W, none) : RawMasterSI) = 2 * W.1.length := rfl
  simp only [masterLine1Ops, MasterOps.ite, masterRouteIs_falseX (B := B) (C₀ := C₀) (W := W) (k := 0) (by omega),
    masterRouteIs_falseX (B := B) (C₀ := C₀) (W := W) (k := 1) (by omega), masterRouteIs_falseX (B := B) (C₀ := C₀) (W := W) (k := 2)
      (by omega), masterRouteIs_falseX (B := B) (C₀ := C₀) (W := W) (k := 3) (by omega), Bool.false_eq_true,
    if_false, masterCamPreparedOps, masterShiftOps, masterCamSelectOps] at hFc
  have hg : masterCamRouteInput cameron (W, none) = (cc, masterWindowBlockInput W) := rfl
  rw [hg, masterCamPrepared_hint] at hFc
  by_cases hh : masterCamHasHint (cc, masterWindowBlockInput W) = true
  · -- the transitive case: a Cameron child with the Johnson hint of step 7
    rw [if_pos hh] at hFc
    unfold masterCamOpenChild at hFc
    split_ifs at hFc with hjw
    simp only [Option.some.injEq] at hFc
    subst hFc
    have h1 : (winOrbits (camLiftGens (cc, masterWindowBlockAction W), W.1)).length = 1 := by
      rw [masterCamHasHint_eq] at hh
      exact of_decide_eq_true hh
    have ha := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
    have hW' := masterCamPrepared_wf hx cc (masterWindowBlockAction W).2 hW
    have ha' : RawAction.WF n (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterDescAction (masterCamPrepared (cc, masterWindowBlockInput W)).2)
        (masterWindowBlockHom hx hw hnd hlt hinv htr hn) := ha
    have hJW := masterCameronChildInput_window_wf
      (p := (masterCamPrepared (cc, masterWindowBlockInput W)).2) (c := cc) ha' hW' j
    have hgood := masterCamChild_hintGood hx hw hnd hlt hinv htr hn H.choose H.choose_spec.2.1
      H.choose_spec.1 h64 h1 j
    refine ⟨⟨⟨hdeg.trans hx, hJW, (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩,
      fun h' hh' => ?_⟩, fun hch => absurd hch hnc, fun _ => Or.inr ⟨?_, ?_, ?_⟩⟩
    · simp only [Option.some.injEq] at hh'
      subst hh'
      exact hgood
    · exact le_refl W.1.length
    · rw [hpP]
      omega
    · have hle : masterParameter (((masterCameronChildInput
          (masterCamPrepared (cc, masterWindowBlockInput W), j)).1,
          some (masterCameronChildInput
            (masterCamPrepared (cc, masterWindowBlockInput W), j)).2) : RawMasterSI) ≤
          W.1.length := masterParameter_le_of_hintGood hgood
      change 2 * masterParameter (((masterCameronChildInput
          (masterCamPrepared (cc, masterWindowBlockInput W), j)).1,
          some (masterCameronChildInput
            (masterCamPrepared (cc, masterWindowBlockInput W), j)).2) : RawMasterSI) ≤
        masterParameter ((W, none) : RawMasterSI)
      rw [hpP]
      omega
  · -- the intransitive case: an orbit call of at most half the window
    rw [if_neg hh] at hFc
    have hs' := masterDescFoldChild_shape hFc
    have hsrc : (masterCamLists (masterCamPrepared (cc, masterWindowBlockInput W))).1.2.2.2.1 =
        W.2.2.2.1 := rfl
    rw [hsrc, hx] at hs'
    obtain ⟨hJW, hJ2⟩ := hs'
    have hJ : MasterRawNode n J := ⟨hdeg.trans hx, hJW,
      (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
    have hne : (winOrbits (camLiftGens (cc, masterWindowBlockAction W), W.1)).length ≠ 1 := by
      intro h1
      apply hh
      rw [masterCamHasHint_eq]
      exact decide_eq_true h1
    have h2 := hV hne
    have hwJ := masterWindowSize_eq_of_rawNode hJ
    have hwP : masterWindowSize ((W, none) : RawMasterSI) = W.1.length := rfl
    refine ⟨⟨hJ, fun h' hh' => by rw [hJ2] at hh'; cases hh'⟩, fun hch => absurd hch hnc,
      fun _ => Or.inl ⟨?_, ?_⟩⟩
    · rw [hwP]
      omega
    · rw [hwP, hwJ]
      omega

/-- **Section 15, line 1, in the full node carrier, with its children, at every route.**  At a
well-formed node without hint, the full node carrier walks the round of line 1
(`Explicit.masterLine1TreeX`), and every child it produces on the path of the match is a good
node that makes the progress of Sec. 11.4 (`Babai.Line1Case.decreases_branch`). -/
theorem masterNodeFull_line1_matchGoodX {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron) (hL : Line1OK B C₀)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterNodeGood n J ∧ MasterStepProgressX B C₀ (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1TreeX hW hinv hc hs hL) := by
  by_cases hr : masterReduceRoute B C₀ W = 4
  · exact masterNodeFull_cameron_matchGX hW hinv hc hs hL hcap hr
  · refine (masterNodeFull_line1_matchGX hW hinv hc hs hL hcap hr).mono ?_
    rintro J ⟨hJ, hJ2, hpr⟩
    exact ⟨⟨hJ, fun h hh => by rw [hJ2] at hh; cases hh⟩, hpr⟩

end FullMatch

/-! ## The line-1 nodes of the hinted node carrier -/

section Node
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    {B C₀ : ℕ}

/-- **A node without hint of the hinted node carrier, at thresholds with
`Explicit.Line1OK`**: the carrier walks the tree of line 1 (`Explicit.masterLine1TreeX`) with
the obligation `Explicit.MasterNodeTreeOKX` (the none case of `Algo.masterNodeFull_treeOK_at`
and `Algo.masterNodeH_treeOK`). -/
theorem masterNodeH_line1_treeOKX {a b n : ℕ} (q45 : ℕ → ℕ) (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hL : Line1OK B C₀)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (W : RawWinSI)
    (hP : MasterNodeGood n ((W, none) : RawMasterSI)) :
    ∃ T, MasterNodeTreeOKX B C₀ (masterAdmittedRound a b (masterNodeHOps B C₀
      cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n (rawMasterRoundCost q45)
      (W, none) T := by
  obtain ⟨⟨-, hW, hinv⟩, -⟩ := hP
  have hsize : (decWinSI n W).windowSize = W.1.length := ncard_winSet W.1 hW.1 hW.2.1
  have hwin : masterWindowSize ((W, none) : RawMasterSI) = W.1.length := rfl
  refine ⟨masterLine1TreeX hW hinv hc hs hL,
    masterNodeH_matchG_of_full (by simp [masterRoute]) (fun h4' => by simp [masterRoute] at h4')
      (masterNodeFull_line1_matchGoodX hW hinv hc hs hL hcap),
    masterLine1Tree_runX hW hinv hc hs hL, ?_, fun hch => ?_⟩
  · have := masterLine1Tree_calls_lengthX hW hinv hc hs hL
    rw [hsize] at this
    rw [hwin]
    unfold rawMasterRoundCost
    omega
  · have := masterLine1Tree_chainX hW hinv hc hs hL hch.2
    rw [hsize] at this
    rw [hwin]
    exact this

end Node

/-! ## The hinted nodes: a match does not depend on the thresholds -/

section Transport
variable {cameron : RawGens × List ℕ → Option RawCameron} {T' : Type} {H : MasterOps T'}
    {dT : T'}

theorem masterTopOps_hint_eq {B C₀ B' C₀' : ℕ} {P : RawMasterSI} (hP : P.2 ≠ none) :
    (masterTopOps B C₀ cameron H dT).width P = (masterTopOps B' C₀' cameron H dT).width P ∧
    (masterTopOps B C₀ cameron H dT).init P = (masterTopOps B' C₀' cameron H dT).init P ∧
    (∀ j s, (masterTopOps B C₀ cameron H dT).child (P, j, s) =
      (masterTopOps B' C₀' cameron H dT).child (P, j, s)) ∧
    (∀ j s a, (masterTopOps B C₀ cameron H dT).combine (P, j, s, a) =
      (masterTopOps B' C₀' cameron H dT).combine (P, j, s, a)) ∧
    (∀ s, (masterTopOps B C₀ cameron H dT).finish (P, s) =
      (masterTopOps B' C₀' cameron H dT).finish (P, s)) := by
  have hsel : masterIsLine1 P = false :=
    Bool.eq_false_iff.mpr fun h => hP ((masterIsLine1_iff P).mp h)
  refine ⟨?_, ?_, fun j s => ?_, fun j s a => ?_, fun s => ?_⟩ <;>
    simp only [masterTopOps, MasterOps.pairIte, hsel, Bool.false_eq_true, if_false]

/-- **At a hinted node the match does not depend on the line-1 thresholds**: the node
carrier runs the hinted carrier there. -/
theorem loopMatchG_hint_transport {a b n B C₀ B' C₀' : ℕ} {P : RawMasterSI} (hP : P.2 ≠ none)
    {C C' : RawMasterSI → Prop} (hCC : ∀ J, C J → C' J)
    {Tr : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatchG (masterAdmittedRound a b (masterTopOps B' C₀' cameron H dT)) C
      (fun J => decWinSI n J.1) (fun _ => decCoset n) P
      ((masterTopOps B' C₀' cameron H dT).width P) 0
      ((masterTopOps B' C₀' cameron H dT).init P) Tr) :
    LoopMatchG (masterAdmittedRound a b (masterTopOps B C₀ cameron H dT)) C'
      (fun J => decWinSI n J.1) (fun _ => decCoset n) P
      ((masterTopOps B C₀ cameron H dT).width P) 0
      ((masterTopOps B C₀ cameron H dT).init P) Tr := by
  obtain ⟨hw, hi, hch, hco, hfi⟩ := masterTopOps_hint_eq (cameron := cameron) (H := H)
    (dT := dT) (B := B) (C₀ := C₀) (B' := B') (C₀' := C₀') hP
  rw [hw, hi]
  refine LoopMatchG.embed (R := masterAdmittedRound a b (masterTopOps B' C₀' cameron H dT)) id
    ?_ (fun j s a => hco j s a) (fun s => hfi s) (h.mono hCC)
  intro j s
  change masterGuardedChild a b _ (P, j, s) = masterGuardedChild a b _ (P, j, s)
  unfold masterGuardedChild
  rw [hw, hch]

/-- **The obligation of a hinted node does not depend on the line-1 thresholds.** -/
theorem treeOKX_of_treeOK_hint {a b n B C₀ : ℕ} {q : ℕ → ℕ} {P : RawMasterSI}
    (hP : P.2 ≠ none) {Tr : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : MasterNodeTreeOK (masterAdmittedRound a b
      (masterTopOps masterLine1B masterLine1C₀ cameron H dT)) n q P Tr) :
    MasterNodeTreeOKX B C₀ (masterAdmittedRound a b (masterTopOps B C₀ cameron H dT)) n q
      P Tr := by
  have hnc : ¬ MasterChainRuleNode P := fun hch => hP hch.1
  have hncX : ¬ MasterChainRuleNodeX B C₀ P := fun hch => hP hch.1
  refine ⟨loopMatchG_hint_transport hP ?_ h.1, h.2.1, h.2.2.1, fun hch => absurd hch hncX⟩
  rintro J ⟨hG, hpr⟩
  exact ⟨hG, fun hch => absurd hch hncX, fun _ => hpr.2 hnc⟩

end Transport

/-! ## The recursion from one tree at every good node -/

section Rec
variable {S : Type} {a b n B C₀ : ℕ} {F : MasterOps S} {q : ℕ → ℕ}
    (hT : ∀ P, MasterNodeGood n P → (masterAdmittedRound a b F).WF P →
      ∃ T, MasterNodeTreeOKX B C₀ (masterAdmittedRound a b F) n q P T)

open scoped Classical in
/-- `Algo.masterTreeOf` for the obligation `Explicit.MasterNodeTreeOKX`. -/
noncomputable def masterTreeOfX (P : RawMasterSI) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if h : MasterNodeGood n P ∧ (masterAdmittedRound a b F).WF P then
    Classical.choose (hT P h.1 h.2)
  else .done ∅

theorem masterTreeOfX_spec (P : RawMasterSI) (hG : MasterNodeGood n P)
    (hW : (masterAdmittedRound a b F).WF P) :
    MasterNodeTreeOKX B C₀ (masterAdmittedRound a b F) n q P (masterTreeOfX hT P) := by
  classical
  unfold masterTreeOfX
  rw [dif_pos ⟨hG, hW⟩]
  exact Classical.choose_spec (hT P hG hW)

/-- `Algo.masterRecursionOfTrees` with the progress relation at the thresholds `B`, `C₀`
(the same construction). -/
noncomputable def masterRecursionOfTreesX (hq : Monotone q)
    (hfin : ∀ P s, masterDegree P = n → RawCoset.WF n (F.finish (P, s))) :
    MasterRecursion (masterAdmittedRound a b F) n where
  Good := MasterNodeGood n
  Ch P J := MasterNodeGood n J ∧ MasterStepProgressX B C₀ P J
  ρ := masterTreeOfX hT
  q := q
  impl := fun P hG hW => (masterTreeOfX_spec hT P hG hW).1
  correct := fun P hG hW => (masterTreeOfX_spec hT P hG hW).2.1
  progress := by
    refine ⟨fun _ J hJ => hJ.1, fun P hG => masterWindowSize_eq_of_rawNode hG.1,
      fun P hG _ => ?_, fun P hG hW => (masterTreeOfX_spec hT P hG hW).2.2.1,
      fun P hG hW => ?_⟩
    · obtain ⟨W, o⟩ := P
      cases o with
      | none => exact le_of_eq rfl
      | some h =>
        have : masterParameter ((W, some h) : RawMasterSI) ≤
            masterWindowSize ((W, some h) : RawMasterSI) :=
          masterParameter_le_of_hintGood (hG.2 h rfl)
        omega
    · have hT' := masterTreeOfX_spec hT P hG hW
      by_cases hch : MasterChainRuleNodeX B C₀ P
      · obtain ⟨h1, hsum⟩ := hT'.2.2.2 hch
        exact Or.inr ⟨h1, fun J hJ => hJ.2.1 hch, hsum⟩
      · exact Or.inl fun J hJ => hJ.2.2 hch
  mono := hq
  win_le := fun P hG _ => by
    obtain ⟨hdeg, hW, -⟩ := hG.1
    change P.1.1.length ≤ masterDegree P
    rw [hdeg]
    exact length_le_of_nodup_lt hW.1 hW.2.1
  finish_wf := fun P s hG _ => hfin P s hG.1.1
  root := fun I hI => ⟨⟨masterRoot_rawNode hI, fun h hh => by cases hh⟩,
    masterInputWF_of_checked a b (masterRoot_rawNode hI).2.1⟩
end Rec

end Explicit
