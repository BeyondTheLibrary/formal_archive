import Workspace.Algo.TopMasterRecursion
import Workspace.Algo.TopMasterL57Calls

/-! # The master recursion at line-1 nodes: the children and their progress

Section 15, line 1: at a node without a Johnson hint the Master Algorithm runs one round of
Procedure Reduce-to-Johnson (Sec. 11.3).  For the lift-free evaluator
(`Workspace/Algo/EvaluatorP.lean`) the node carrier must walk the paper's round with a
condition on every child it produces on the path of the match (`Algo.LoopMatchG`): the child
is a well-formed raw node (`Algo.MasterRawNode`) and it makes the progress of Sec. 11.4
(`Algo.MasterStepProgress`).

The progress is the one of `Babai.MasterStep.decreases`: at a Chain Rule node (step 3 of
Reduce-to-Johnson, recurrence (i) of Sec. 11.4) every child has a strictly smaller window and
no larger parameter; at every other node every child makes the progress of recurrences
(ii)/(v) (`Babai.MakesProgress`), both read on the raw window size and the raw Johnson
parameter of the nodes.

This file proves the condition at the line-1 nodes whose round has no hinted children:
steps 1–2 (no calls), step 3 (the Chain Rule on the orbits) and step 5 (the Luks step on a
small primitive block action).  Step 6 produces hinted children (the Johnson case data of
step 7) and is treated with the hint meaning.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ### The progress relation between raw nodes -/

/-- A node where the master carrier runs the Chain Rule of line 1 (step 3 of
Reduce-to-Johnson): no hint, and the route test selects step 3. -/
def MasterChainRuleNode (P : RawMasterSI) : Prop :=
  P.2 = none ∧ masterLine1Route P.1 = 2

/-- **The progress of one round of Sec. 11.4 between a node and a child**, on the raw window
size and the raw Johnson parameter: at a Chain Rule node the child's window is strictly
smaller and its parameter no larger (recurrence (i)); at any other node the child makes the
progress of recurrences (ii)/(v) (`Babai.MakesProgress`). -/
def MasterStepProgress (P J : RawMasterSI) : Prop :=
  (MasterChainRuleNode P → masterWindowSize J < masterWindowSize P ∧
      masterParameter J ≤ masterParameter P) ∧
    (¬ MasterChainRuleNode P → MakesProgress masterWindowSize masterParameter P J)

/-- The raw window size of a well-formed node is the size of its decoded window. -/
theorem masterWindowSize_eq_of_rawNode {n : ℕ} {P : RawMasterSI} (hP : MasterRawNode n P) :
    masterWindowSize P = (decWinSI n P.1).windowSize :=
  (ncard_winSet P.1.1 hP.2.1.1 hP.2.1.2.1).symm

/-- A node without hint has parameter twice its window. -/
theorem masterParameter_none {W : RawWinSI} :
    masterParameter ((W, none) : RawMasterSI) = 2 * masterWindowSize ((W, none) : RawMasterSI) :=
  rfl

/-! ### Children of the checked shape -/

/-- A child of the descent fold is a normalized window call on the source's domain. -/
theorem masterDescFoldChild_shape {X : AggnRecomputeInput} {j : ℕ} {s : AggnRecomputeState}
    {J : RawMasterSI} (h : masterDescFoldChild (X, j, s) = some J) :
    AggnCheckedWindowWF X.1.2.2.2.1.length J.1 ∧ J.2 = none := by
  obtain ⟨K, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨aggnCheckedWindow_wf _ _, rfl⟩

/-- **The children of line 1 without hint have the checked shape.**  At a well-formed node
where the route test does not select step 6, every child the line-1 carrier proposes, at any
fold state, is a window instance of the checked shape on the same domain, without hint. -/
theorem masterLine1Ops_child_shape {n : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {P J : RawMasterSI} {j : ℕ} {s : AggnRecomputeState} (hP : MasterRawNode n P)
    (hr : masterLine1Route P.1 ≠ 4)
    (h : (masterLine1Ops masterLine1B masterLine1C₀ cameron).child (P, j, s) = some J) :
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
    have := masterReduceRoute_le_four masterLine1B masterLine1C₀ P.1
    unfold masterLine1Route
    omega

section Full
variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

/-- At a node without hint the full node carrier proposes the children of line 1. -/
theorem masterNodeFull_child_line1 {P : RawMasterSI} (hP : P.2 = none) (j : ℕ)
    (s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState) :
    (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).child (P, j, s) =
      (masterLine1Ops B C₀ cameron).child (P, j, s.1) := by
  simp only [masterNodeFullOps, masterNodeOps, masterTopOps, MasterOps.pairIte]
  rw [if_pos ((masterIsLine1_iff P).mpr hP)]

end Full

/-- The condition on the calls of a line-1 round without hinted children: a coset instance,
and a strictly smaller window (Chain Rule) or a window of at most half the size. -/
def MasterLine1CallOK (n : ℕ) (W : RawWinSI) (K : SIInstance (Fin n) ℕ) : Prop :=
  (∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G K) ∧
    (masterLine1Route W = 2 → K.windowSize < (decWinSI n W).windowSize) ∧
    (masterLine1Route W ≠ 2 → 1 ≤ (decWinSI n W).windowSize ∧
      2 * K.windowSize ≤ (decWinSI n W).windowSize)

/-- A child whose decoded call passes `Algo.MasterLine1CallOK` makes the progress of
Sec. 11.4 from its line-1 parent. -/
theorem masterStepProgress_line1 {n : ℕ} {W : RawWinSI} {J : RawMasterSI}
    (hW : AggnCheckedWindowWF n W) (hJ : MasterRawNode n J) (hJ2 : J.2 = none)
    (hV : MasterLine1CallOK n W (decWinSI n J.1)) : MasterStepProgress (W, none) J := by
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
    have h2 : masterLine1Route W ≠ 2 := fun h => hc ⟨rfl, h⟩
    obtain ⟨h1, hle⟩ := hV.2.2 h2
    exact Or.inl ⟨by omega, by omega⟩

theorem isCosetInstance_of_isGroupInstance {Ω A : Type*} {K : SIInstance Ω A}
    (h : IsGroupInstance K) : ∃ G : Subgroup (Perm Ω), IsCosetInstance G K := by
  obtain ⟨G, hK, hinv⟩ := h
  refine ⟨G, G, 1, le_rfl, G.one_mem, ?_, hinv⟩
  rw [hK]
  exact (one_smul (Perm Ω) (G : Set (Perm Ω))).symm

section Case
variable {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron)

include hW in
/-- **The calls of line 1 without hinted children pass `Algo.MasterLine1CallOK`**: steps 1–2
make no call, step 3 makes the Chain Rule calls on the orbits (each a coset instance on a
smaller window), and step 5 makes the calls of the Luks step on the kernel orbits (each a
coset instance on at most half the window, `Babai.decreases_blockLuksBranch`). -/
theorem masterLine1Tree_calls_ok (hr : masterLine1Route W ≠ 4) :
    ∀ K ∈ (masterLine1Tree hW hinv hc hs).calls, MasterLine1CallOK n W K := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  unfold masterLine1Tree masterLine1Case
  by_cases h0 : masterLine1Route W = 0
  · rw [dif_pos h0, if_pos (by omega)]
    intro K hK
    simp [masterFixedStringCase, Line1Case.branch, bruteForceBranch, masterNodeShift] at hK
  rw [dif_neg h0]
  by_cases h1 : masterLine1Route W = 1
  · rw [dif_pos h1, if_pos (by omega)]
    intro K hK
    simp [masterSmallGroupCase, Line1Case.branch, bruteForceBranch, masterNodeShift] at hK
  rw [dif_neg h1, if_neg (by omega)]
  by_cases h2 : masterLine1Route W = 2
  · rw [dif_pos h2]
    intro K hK
    simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done,
      List.append_nil] at hK
    refine ⟨⟨_, calls_chainRuleCoset_isCosetInstance (masterChainData hW.2.2.1 hW.2.1 hinv)
      ⟨_, (masterChainRoute_nonempty hW.2.2.1 hW.1 hW.2.1 hinv h2
        masterLine1_one_lt).choose_spec⟩ K hK⟩, fun _ => ?_,
      fun h => absurd h2 h⟩
    exact (masterChainCase_progress hW.2.2.1 hW.1 hW.2.1 hinv h2 _ masterLine1_one_lt).1 K hK
  rw [dif_neg h2]
  by_cases h3 : masterLine1Route W = 3
  · rw [dif_pos h3]
    intro K hK
    simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done,
      List.append_nil] at hK
    let b := masterStepFiveData hW hx hinv masterLine1_block_cutoff h3
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
  exact absurd (masterLine1Route_four h0 h1 h2 h3) hr

end Case

section FullMatch
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

/-- **Section 15, line 1, in the full node carrier, with its children.**  At a well-formed
node without hint where the route test does not select step 6, the full node carrier walks
the round of line 1 (`Algo.masterLine1Tree`), and every child it produces on the path of the
match is a well-formed raw node without hint that makes the progress of Sec. 11.4. -/
theorem masterNodeFull_line1_matchG {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (hr : masterLine1Route W ≠ 4) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterRawNode n J ∧ J.2 = none ∧ MasterStepProgress (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1Tree hW hinv hc hs) := by
  have hm := masterTop_line1_match (a := a) (b := b) hW hinv hc hs
    (masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default) c' b' t d dc dp E)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default) hcap
  refine loopMatchG_of_loopMatch_onCalls (MasterLine1CallOK n W) ?_ hm
    (masterLine1Tree_calls_ok hW hinv hc hs hr)
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_line1 rfl] at hFc
  have hP : MasterRawNode n ((W, none) : RawMasterSI) := ⟨hW.2.2.2.2.2.1.1, hW, hinv⟩
  obtain ⟨hJW, hJ2⟩ := masterLine1Ops_child_shape hP hr hFc
  have hJ : MasterRawNode n J := ⟨hdeg.trans hW.2.2.2.2.2.1.1, hJW,
    (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
  exact ⟨hJ, hJ2, masterStepProgress_line1 hW hJ hJ2 hV⟩

end FullMatch

end Algo
