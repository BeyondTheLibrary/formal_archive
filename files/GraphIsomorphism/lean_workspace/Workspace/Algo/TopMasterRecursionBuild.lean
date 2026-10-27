import Workspace.Algo.TopMasterRecursionHint
import Workspace.Algo.TopMasterConstants

/-! # The master recursion of the full node carrier

Section 15: the obligations of `Algo.MasterRecursion` for the full node carrier
`Algo.masterNodeFullOps`, at the good nodes (`Algo.MasterNodeGood`).  At a node without hint
the carrier walks the round of line 1 (`Algo.masterLine1Tree`); at a hinted node it walks the
round of line 2, 4a or 4b (`Algo.TopMasterRecursionHint`) or, at lines 4c–4d and 5–7, the
round of the parameter carriers of the Section 13 track (`Algo.MasterParamRoutes`).

This file collects, for every good node, one tree the carrier walks with the conditions on
its children, its correctness, its number of calls and, at a Chain Rule node, the sum of its
windows (`Algo.MasterNodeTreeOK`), and builds `Algo.MasterRecursion` from them
(`Algo.masterRecursion_full`).
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ### The tree of line 1 -/

section Line1
variable {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron)

include hW in
/-- **Section 15, line 1, is correct** on the machine's tree: the round of
Reduce-to-Johnson, in the group frame of the node and shifted back, returns `Iso_G(x,y)`. -/
theorem masterLine1Tree_run :
    (masterLine1Tree hW hinv hc hs).run = (decWinSI n W).answer := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  have hc' := (masterLine1Case hW hinv hc hs).run_branch
  have hcos : (masterLine1Case hW hinv hc hs).cosetBranch.run =
      (masterGroupInstance n W).answer := by
    have h1 : (1 : Perm (Fin n)) ∈ (masterGroupInstance n W).K :=
      (decGroup n W.2.1).one_mem
    rw [← run_alignRed_of_one_mem h1, ← Line1Case.branch_eq_alignRed]
    exact hc'
  unfold masterLine1Tree
  split_ifs
  · rw [SIReduction.run_bind, hc']
    exact masterGroupInstance_answer hx
  · rw [SIReduction.run_bind, hcos]
    exact masterGroupInstance_answer hx

/-- **Section 15, line 1, the number of calls**: at most `q·n + q + n + 2` with
`q = n^{2 + log₂ n}` (`Babai.line1RoundCost`). -/
theorem masterLine1Tree_calls_length :
    (masterLine1Tree hW hinv hc hs).calls.length ≤ line1RoundCost (decWinSI n W).windowSize := by
  have hb := (masterLine1Case hW hinv hc hs).calls_length_branch
  have hcb : (masterLine1Case hW hinv hc hs).cosetBranch.calls.length =
      (masterLine1Case hW hinv hc hs).branch.calls.length := by
    rw [Line1Case.branch_eq_alignRed, calls_length_alignRed]
  unfold masterLine1Tree
  split_ifs
  · simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
    exact hb
  · simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
    rw [hcb]
    exact hb

include hW in
/-- **Section 15, line 1, step 3: the Chain Rule round** (recurrence (i) of Sec. 11.4).  At a
Chain Rule node the window is nonempty and the windows of the calls add up to at most the
window, because they are the orbits of the group on the window. -/
theorem masterLine1Tree_chain (h2 : masterLine1Route W = 2) :
    1 ≤ (decWinSI n W).windowSize ∧
      ((masterLine1Tree hW hinv hc hs).calls.map SIInstance.windowSize).sum ≤
        (decWinSI n W).windowSize := by
  have h0 : masterLine1Route W ≠ 0 := by omega
  have h1 : masterLine1Route W ≠ 1 := by omega
  unfold masterLine1Tree masterLine1Case
  rw [if_neg (by omega), dif_neg h0, dif_neg h1, dif_pos h2]
  simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
  obtain ⟨hn, -, hsum⟩ := decreases_chainRuleBranch (masterChainData hW.2.2.1 hW.2.1 hinv)
    ⟨_, (masterChainRoute_nonempty hW.2.2.1 hW.1 hW.2.1 hinv h2 masterLine1_one_lt).choose_spec⟩
    (masterChainRoute_intransitive hW.2.2.1 hW.1 hW.2.1 hinv h2)
  rw [List.map_map] at hsum
  have hf : (HintedInstance.win ∘ fun J : SIInstance (Fin n) ℕ =>
      (⟨J, none⟩ : HintedInstance (Fin n) ℕ)) = SIInstance.windowSize := rfl
  rw [hf] at hsum
  refine ⟨hn, ?_⟩
  have e := sum_windowSize_calls_alignRed (masterGroupInstance n W)
    (masterChainCase hW.2.2.1 hW.1 hW.2.1 hinv h2 (line1Cost (masterGroupInstance n W).windowSize)
      masterLine1_one_lt).cosetBranch
  rw [← e]
  exact hsum

end Line1

/-! ### The final shift is well formed -/

theorem rawCoset_wf_top3Shift {n : ℕ} {dom : List ℕ} (hd : dom.length = n) (r : RawPerm)
    (c : RawCoset) : RawCoset.WF n (top3Shift (dom, r, c)) := by
  cases hq : top3Shift (dom, r, c) with
  | none => trivial
  | some q =>
    obtain ⟨gs, ρ⟩ := q
    obtain ⟨h1, -, h3⟩ := top3Shift_wf hd r c hq
    exact ⟨h1, h3⟩

/-- The answers of the line-1 carrier are well formed: every branch returns through the
final shift to the node's candidate coset. -/
theorem masterLine1Ops_finish_wf {B C₀ n : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    (P : RawMasterSI) (s : AggnRecomputeState) (hx : P.1.2.2.2.1.length = n) :
    RawCoset.WF n ((masterLine1Ops B C₀ cameron).finish (P, s)) := by
  unfold masterLine1Ops
  simp only [MasterOps.ite]
  split_ifs
  all_goals exact rawCoset_wf_top3Shift (dom := P.1.2.2.2.1) hx _ _

/-- The answers of the hinted carrier are well formed, given that those of the
dominant-class carrier `GD` are. -/
theorem masterHintL57Ops_finish_wf {TD : Type} {e f u v c tt dd : ℕ} {GD : MasterOps TD}
    {dD : TD} {c' b' t d dc dp E n : ℕ}
    (hGD : ∀ P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s)))
    (P : RawMasterSI) (s : MasterHintState (TD × AggnRecomputeState) AggnL57GState)
    (hx : P.1.2.2.2.1.length = n) :
    RawCoset.WF n ((masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default)
      c' b' t d dc dp E).finish (P, s)) := by
  unfold masterHintL57Ops masterHintOps masterLine4cdOps
  simp only [MasterOps.pairIte]
  split_ifs
  all_goals first
    | exact hGD _ _ hx
    | exact rawCoset_wf_top3Shift (dom := P.1.2.2.2.1) hx _ _

/-- **The answer of every node is well formed.**  Every branch of the full node carrier
returns through the final shift `top3Shift` to the node's candidate coset, except the
dominant-class carrier `GD` of lines 4c–4d, whose answers are assumed well formed. -/
theorem masterNodeFull_finish_wf {TD : Type} {B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v c tt dd : ℕ} {GD : MasterOps TD}
    {dD : TD} {c' b' t d dc dp E n : ℕ}
    (hGD : ∀ P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s)))
    (P : RawMasterSI) (s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState)
    (hP : masterDegree P = n) :
    RawCoset.WF n
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).finish (P, s)) := by
  have hx : P.1.2.2.2.1.length = n := hP
  unfold masterNodeFullOps masterNodeOps masterTopOps
  simp only [MasterOps.pairIte]
  split_ifs
  · exact masterLine1Ops_finish_wf P _ hx
  · exact masterHintL57Ops_finish_wf hGD P _ hx

/-! ### One tree at every good node -/

/-- **The tree a good node walks, with what the recursion needs of it**: the carrier `R`
walks `T` with a good child that makes the progress of Sec. 11.4 at every call
(`Algo.LoopMatchG`), `T` returns `Iso_G(x,y)`, it makes at most `q(n)` calls on a window of
size `n`, and at a Chain Rule node the window is nonempty and the windows of the calls add
up to at most the window (recurrence (i)). -/
def MasterNodeTreeOK {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) (q : ℕ → ℕ)
    (P : RawMasterSI) (T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))) : Prop :=
  LoopMatchG R (fun J => MasterNodeGood n J ∧ MasterStepProgress P J) (fun J => decWinSI n J.1)
      (fun _ => decCoset n) P (R.width P) 0 (R.init P) T ∧
    T.run = (decWinSI n P.1).answer ∧ T.calls.length ≤ q (masterWindowSize P) ∧
    (MasterChainRuleNode P → 1 ≤ masterWindowSize P ∧
      (T.calls.map SIInstance.windowSize).sum ≤ masterWindowSize P)

theorem MasterNodeTreeOK.mono_q {ω : Type} {R : Round RawMasterSI ω RawCoset} {n : ℕ}
    {q q' : ℕ → ℕ} {P : RawMasterSI} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : MasterNodeTreeOK R n q P T) (hq : ∀ m, q m ≤ q' m) : MasterNodeTreeOK R n q' P T :=
  ⟨h.1, h.2.1, h.2.2.1.trans (hq _), h.2.2.2⟩

/-- **The obligation left to the Section 13 track**: at every good, admitted hinted node of
lines 4c–4d (route 4) or 5–7 (route 5), the full node carrier walks a tree with
`Algo.MasterNodeTreeOK` for the call bound `q45`. -/
def MasterParamRoutes {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) (q45 : ℕ → ℕ) :
    Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) → R.WF (W, some h) →
    (masterHintRoute (W, h) = 4 ∨ masterHintRoute (W, h) = 5) →
      ∃ T, MasterNodeTreeOK R n q45 (W, some h) T

/-- The number of calls of one round of the master carrier on a window of size `n`: line 1
(`Babai.line1RoundCost`), lines 2 and 4b (`Babai.masterRoundCost`), and lines 4c–7 (`q45`). -/
def rawMasterRoundCost (q45 : ℕ → ℕ) (n : ℕ) : ℕ :=
  line1RoundCost n + masterRoundCost n + q45 n

theorem rawMasterRoundCost_mono {q45 : ℕ → ℕ} (hq : Monotone q45) :
    Monotone (rawMasterRoundCost q45) := by
  intro a b hab
  have h1 := line1RoundCost_mono hab
  have h2 := masterRoundCost_mono hab
  have h3 := hq hab
  unfold rawMasterRoundCost
  omega

theorem masterHintRoute_mem (p : MasterHintInput) :
    masterHintRoute p = 1 ∨ masterHintRoute p = 2 ∨ masterHintRoute p = 3 ∨
      masterHintRoute p = 4 ∨ masterHintRoute p = 5 := by
  unfold masterHintRoute
  split_ifs <;> simp

section Tree
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

/-- **Every good node walks a tree with what the recursion needs**: line 1 at a node without
hint, lines 2, 4a, 4b at a hinted node of those routes, and the parameter carriers at lines
4c–7. -/
theorem masterNodeFull_treeOK_at {a b n : ℕ} {q45 : ℕ → ℕ} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hTc : TopwpCap e f) (hTo : Top4wCap e f u v)
    (P : RawMasterSI) (hP : MasterNodeGood n P)
    (hWF : (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)).WF P)
    (h45 : ∀ (W : RawWinSI) (h : RawMasterHint), P = (W, some h) →
      (masterHintRoute (W, h) = 4 ∨ masterHintRoute (W, h) = 5) →
      ∃ T, MasterNodeTreeOK (masterAdmittedRound a b
        (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E)) n q45 (W, some h) T) :
    ∃ T, MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n (rawMasterRoundCost q45) P T := by
  obtain ⟨W, o⟩ := P
  obtain ⟨⟨hdeg, hW, hinv⟩, hgood⟩ := hP
  have hsize : (decWinSI n W).windowSize = W.1.length := ncard_winSet W.1 hW.1 hW.2.1
  have hwin : masterWindowSize ((W, o) : RawMasterSI) = W.1.length := rfl
  cases o with
  | none =>
    refine ⟨masterLine1Tree hW hinv hc hs, masterNodeFull_line1_matchGood hW hinv hc hs hcap,
      masterLine1Tree_run hW hinv hc hs, ?_, fun hch => ?_⟩
    · have := masterLine1Tree_calls_length hW hinv hc hs
      rw [hsize] at this
      rw [hwin]
      unfold rawMasterRoundCost
      omega
    · have := masterLine1Tree_chain hW hinv hc hs hch.2
      rw [hsize] at this
      rw [hwin]
      exact this
  | some h =>
    have hg := hgood h rfl
    have hnot : ¬ MasterChainRuleNode ((W, some h) : RawMasterSI) := not_masterChainRuleNode_hint
    rcases masterHintRoute_mem (W, h) with hr | hr | hr | hr | hr
    · obtain ⟨T, hm, hrun, hlen⟩ := masterNodeFull_hint_line2_matchGood (cameron := cameron)
        (e := e) (f := f) (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD)
        (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (a := a) (b := b)
        hW hinv hg hr
      refine ⟨T, hm, hrun, ?_, fun hch => absurd hch hnot⟩
      change T.calls.length ≤ rawMasterRoundCost q45 W.1.length
      have hlen' : T.calls.length ≤ Nat.factorial (ellOf W.1.length) * W.1.length := hlen
      unfold rawMasterRoundCost masterRoundCost
      omega
    · obtain ⟨T, hm, hrun, hlen⟩ := masterNodeFull_hint_line4a_matchGood (cameron := cameron)
        (e := e) (f := f) (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD)
        (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (a := a) (b := b)
        hW hinv hg hr
      refine ⟨T, hm, hrun, ?_, fun hch => absurd hch hnot⟩
      omega
    · obtain ⟨T, hm, hrun, hlen⟩ := masterNodeFull_hint_line4b_matchGood (cameron := cameron)
        (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD)
        (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (a := a) (b := b)
        hW hinv hg hr hTc hTo
      refine ⟨T, hm, hrun, ?_, fun hch => absurd hch hnot⟩
      change T.calls.length ≤ rawMasterRoundCost q45 W.1.length
      have hlen' : T.calls.length ≤ 7 * W.1.length := hlen
      unfold rawMasterRoundCost masterRoundCost
      omega
    · obtain ⟨T, hT⟩ := h45 W h rfl (Or.inl hr)
      exact ⟨T, hT.mono_q fun m => by unfold rawMasterRoundCost; omega⟩
    · obtain ⟨T, hT⟩ := h45 W h rfl (Or.inr hr)
      exact ⟨T, hT.mono_q fun m => by unfold rawMasterRoundCost; omega⟩

/-- **Every good node walks a tree with what the recursion needs**, once the rounds of lines
4c–7 are supplied (`Algo.MasterParamRoutes`). -/
theorem masterNodeFull_treeOK {a b n : ℕ} {q45 : ℕ → ℕ} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hTc : TopwpCap e f) (hTo : Top4wCap e f u v)
    (h45 : MasterParamRoutes (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n q45)
    (P : RawMasterSI) (hP : MasterNodeGood n P)
    (hWF : (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)).WF P) :
    ∃ T, MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n (rawMasterRoundCost q45) P T :=
  masterNodeFull_treeOK_at hc hs hcap hTc hTo P hP hWF (fun W h hPW hr => by
    subst hPW
    exact h45 W h hP hWF hr)

variable {a b n : ℕ} {q45 : ℕ → ℕ} (hc : PolyFun cameron) (hs : CameronSpec cameron)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hTc : TopwpCap e f) (hTo : Top4wCap e f u v)
    (h45 : MasterParamRoutes (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n q45)

open scoped Classical in
/-- The tree the recursion reads at a node: at a good, admitted node, one tree with
`Algo.MasterNodeTreeOK` (`Algo.masterNodeFull_treeOK`); elsewhere nothing. -/
noncomputable def masterFullTree (P : RawMasterSI) : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if h : MasterNodeGood n P ∧ (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)).WF P then
    Classical.choose (masterNodeFull_treeOK hc hs hcap hTc hTo h45 P h.1 h.2)
  else .done ∅

theorem masterFullTree_spec (P : RawMasterSI) (hG : MasterNodeGood n P)
    (hW : (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)).WF P) :
    MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n (rawMasterRoundCost q45) P
      (masterFullTree hc hs hcap hTc hTo h45 P) := by
  classical
  unfold masterFullTree
  rw [dif_pos ⟨hG, hW⟩]
  exact Classical.choose_spec (masterNodeFull_treeOK hc hs hcap hTc hTo h45 P hG hW)

/-- **Section 15: the master recursion of the full node carrier.**  At every degree `n`, the
full node carrier meets the obligations of `Algo.MasterRecursion`, with the good nodes of
`Algo.MasterNodeGood`, the children that make the progress of Sec. 11.4, and the call bound
`Algo.rawMasterRoundCost`, once the Section 13 track supplies the rounds of lines 4c–7
(`Algo.MasterParamRoutes`, with a monotone bound `q45`) and the answers of the
dominant-class carrier `GD` are well formed. -/
noncomputable def masterRecursionFull (hq45 : Monotone q45)
    (hGD : ∀ P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s))) :
    MasterRecursion (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n where
  Good := MasterNodeGood n
  Ch P J := MasterNodeGood n J ∧ MasterStepProgress P J
  ρ := masterFullTree hc hs hcap hTc hTo h45
  q := rawMasterRoundCost q45
  impl := fun P hG hW => (masterFullTree_spec hc hs hcap hTc hTo h45 P hG hW).1
  correct := fun P hG hW => (masterFullTree_spec hc hs hcap hTc hTo h45 P hG hW).2.1
  progress := by
    refine ⟨fun _ J hJ => hJ.1, fun P hG => masterWindowSize_eq_of_rawNode hG.1,
      fun P hG _ => ?_, fun P hG hW => (masterFullTree_spec hc hs hcap hTc hTo h45 P hG hW).2.2.1,
      fun P hG hW => ?_⟩
    · obtain ⟨W, o⟩ := P
      cases o with
      | none => exact le_of_eq rfl
      | some h =>
        have : masterParameter ((W, some h) : RawMasterSI) ≤
            masterWindowSize ((W, some h) : RawMasterSI) :=
          masterParameter_le_of_hintGood (hG.2 h rfl)
        omega
    · have hT := masterFullTree_spec hc hs hcap hTc hTo h45 P hG hW
      by_cases hch : MasterChainRuleNode P
      · obtain ⟨h1, hsum⟩ := hT.2.2.2 hch
        exact Or.inr ⟨h1, fun J hJ => hJ.2.1 hch, hsum⟩
      · exact Or.inl fun J hJ => hJ.2.2 hch
  mono := rawMasterRoundCost_mono hq45
  win_le := fun P hG _ => by
    obtain ⟨hdeg, hW, -⟩ := hG.1
    change P.1.1.length ≤ masterDegree P
    rw [hdeg]
    exact length_le_of_nodup_lt hW.1 hW.2.1
  finish_wf := fun P s hG _ => masterNodeFull_finish_wf hGD P s hG.1.1
  root := fun I hI => ⟨⟨masterRoot_rawNode hI, fun h hh => by cases hh⟩,
    masterInputWF_of_checked a b (masterRoot_rawNode hI).2.1⟩

end Tree

set_option synthInstance.maxSize 2048 in
/-- **Theorem 1.1.1 on the RAM, from the master recursion of the full node carrier.**  With a
polynomial-time Cameron recognizer meeting its specification (Theorem 11.2.1 with
Prop. 11.2.5), constants of the line-4b carrier, and, from the Section 13 track, a
dominant-class carrier `GD` with local costs and well-formed answers together with the rounds
of lines 4c–7 at every degree (`Algo.MasterParamRoutes`, with a monotone quasipolynomial call
bound `q45`), the full node carrier solves String Isomorphism in quasipolynomial time. -/
theorem siWorkspaceRoutine_of_masterParamRoutes {TD : Type} [Enc TD]
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {e f u v c tt dd : ℕ} (hTc : TopwpCap e f)
    (hTo : Top4wCap e f u v) {GD : MasterOps TD} (dD : TD)
    (CD : MasterOpsCost masterCapA masterCapB GD) {c' b' t d dc dp E : ℕ} {q45 : ℕ → ℕ}
    (hq45 : Monotone q45) (hq : QuasiPolyBound q45)
    (hGD : ∀ n P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s)))
    (h45 : ∀ n, MasterParamRoutes (masterAdmittedRound masterCapA masterCapB
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n q45) : SIWorkspaceRoutine := by
  obtain ⟨C⟩ := masterNodeFull_runCostQ masterCapA masterCapB masterLine1B masterLine1C₀ hc
    e f u v c tt dd dD CD c' b' t d dc dp E
  obtain ⟨c₁, hc₁⟩ := (quasiPolyBound_line1RoundCost.add quasiPolyBound_masterRoundCost).add hq
  exact siWorkspaceRoutine_of_masterRecursion _ C c₁ fun n =>
    ⟨masterRecursionFull hc hs (masterCap_spec n) hTc hTo (h45 n) hq45 (hGD n), fun m => hc₁ m⟩

end Algo
