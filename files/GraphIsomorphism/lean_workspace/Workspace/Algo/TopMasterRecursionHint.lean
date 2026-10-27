import Workspace.Algo.TopMasterRecursionCameron

/-! # The master recursion at hinted nodes: lines 2, 4a and 4b

Section 15, lines 2–4b: at a node that carries a Johnson hint with its meaning
(`Algo.MasterHintGood`), the Master Algorithm runs line 2 when the Johnson parameter is small
(`m ≤ ℓ(n)`), line 4a when the top action is primitive with `t = 1` and a giant, and line 4b
when it is primitive with small defect.  For the lift-free evaluator the full node carrier must
walk the paper's round with a condition on every child it produces
(`Algo.LoopMatchG`): the child is a good node (`Algo.MasterNodeGood`) that makes the
progress of Sec. 11.4 (`Algo.MasterStepProgress`).

* Line 2 (`Algo.masterNodeFull_hint_line2_matchGood`): the calls are the orbits of the
  kernel of `ϕ`, each of at most half the window (Fact 11.1.8), so the window drops to `4/5`.
* Line 4a (`Algo.masterNodeFull_hint_line4a_matchGood`): no call.
* Line 4b (`Algo.masterNodeFull_hint_line4b_matchGood`): every call has window at most
  `2n/3` (Sec. 13), so again the window drops to `4/5`.

Lines 4c–4d and 5–7 are the parameter carriers of the Section 13 track.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Full
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

/-- At a node with a hint the full node carrier proposes the children of the hinted
carrier. -/
theorem masterNodeFull_child_hint {B C₀ : ℕ} {P : RawMasterSI} (hP : P.2 ≠ none) (j : ℕ)
    (s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState) :
    (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).child (P, j, s) =
      (masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default)
        c' b' t d dc dp E).child (P, j, s.2) := by
  simp only [masterNodeFullOps, masterNodeOps, masterTopOps, MasterOps.pairIte]
  rw [if_neg (fun h => hP ((masterIsLine1_iff P).mp h))]

/-- A hinted node is not a Chain Rule node. -/
theorem not_masterChainRuleNode_hint {W : RawWinSI} {h : RawMasterHint} :
    ¬ MasterChainRuleNode ((W, some h) : RawMasterSI) := fun hc => by cases hc.1

/-- A child of a hinted node with a window of at most `4/5` of the node's makes the progress
of Sec. 11.4 (recurrence (ii)/(v), first form). -/
theorem masterStepProgress_hint_of_window {W : RawWinSI} {h : RawMasterHint} {J : RawMasterSI}
    (h1 : 1 ≤ W.1.length) (h5 : 5 * masterWindowSize J ≤ 4 * W.1.length) :
    MasterStepProgress (W, some h) J :=
  ⟨fun hc => absurd hc not_masterChainRuleNode_hint, fun _ => Or.inl ⟨h1, h5⟩⟩

/-- A checked unhinted child whose decoded window is at most `2/3` of the node's window makes
the progress of Sec. 11.4 from a hinted node. -/
theorem masterNodeGood_of_checked {n : ℕ} {W : RawWinSI} {h : RawMasterHint} {J : RawMasterSI}
    (hdeg : masterDegree J = n) (hJW : AggnCheckedWindowWF n J.1) (hJ2 : J.2 = none)
    (hinvJ : rawIsInvariant (J.1.2.1, J.1.1) = true) (h1 : 1 ≤ W.1.length)
    (h3 : 3 * (decWinSI n J.1).windowSize ≤ 2 * W.1.length) :
    MasterNodeGood n J ∧ MasterStepProgress (W, some h) J := by
  have hJ : MasterRawNode n J :=
    ⟨hdeg, hJW, (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
  refine ⟨⟨hJ, fun h' hh' => by rw [hJ2] at hh'; cases hh'⟩,
    masterStepProgress_hint_of_window h1 ?_⟩
  rw [masterWindowSize_eq_of_rawNode hJ]
  omega

section Node
variable {n : ℕ} {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hW hinv in
/-- **Section 15, line 2, in the full node carrier, with its children.**  At a well-formed
node whose hint has its meaning and whose Johnson parameter is small (`m ≤ ℓ(n)`), the full
node carrier walks the round of line 2 (the Luks descent to the kernel of `ϕ` followed by the
Chain Rule on its orbits), which returns `Iso_G(x,y)` in at most `ℓ(n)!·n` calls, and every
child it produces on the path of the match is a good node with at most half the window. -/
theorem masterNodeFull_hint_line2_matchGood {a b : ℕ} (hg : MasterHintGood (W, h))
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
      T.run = (decWinSI n W).answer ∧
      T.calls.length ≤ Nat.factorial (ellOf W.1.length) * W.1.length := by
  obtain ⟨m, φ, B, hB, hp, hG, -, ⟨L⟩, h2, ht, hkt, -, h64⟩ := hg
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hw := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hkt' : 2 * h.2 < m := hkt
  have h64' : 64 ≤ W.1.length := h64
  have hm : h.2 < m := by omega
  refine ⟨masterHintLine2Tree (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr, ?_,
    masterHintLine2_run (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr,
    masterHintLine2_calls (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr⟩
  have hM := masterTop_hinted_match (B := masterLine1B) (C₀ := masterLine1C₀) (cameron := cameron)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default))
    (p := (W, some h)) (by simp)
    (masterHint_line2_match (e := e) (f := f) (u := u) (v := v)
      (G4 := masterLine4cdOps c tt dd GD dD) (G5 := masterL57Ops c' b' t d dc dp e f E)
      (d4 := (dD, default)) (d5 := default) (p := (W, h)) hr
      (masterHintLine2_match (p := (W, h)) hx hy hw hnd hlt hinv φ hp hB L ht hm hr a b h2))
  refine loopMatchG_of_loopMatch_onCalls (fun K => 2 * K.windowSize ≤ W.1.length) ?_ hM
    (masterHintLine2_half (p := (W, h)) hx hw hnd hlt hinv φ hp hB L ht hm hr hG h2)
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

include hW hinv in
/-- **Section 15, line 4a, in the full node carrier.**  At a well-formed node whose hint has
its meaning and whose route is line 4a, the full node carrier returns `Iso_G(x,y)` from the
leaf of line 4a, with no call. -/
theorem masterNodeFull_hint_line4a_matchGood {a b : ℕ} (hg : MasterHintGood (W, h))
    (hr : masterHintRoute (W, h) = 2) :
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
      T.run = (decWinSI n W).answer ∧ T.calls.length ≤ 0 := by
  obtain ⟨m, φ, B, hB, hp, hG, hϕ, -, -, -, -, -, h64⟩ := hg
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  refine ⟨line4aReduction (decWinSI n W), ?_, run_line4aReduction _, by
    rw [calls_line4aReduction]; exact le_refl 0⟩
  have hM := masterTop_hinted_match (B := masterLine1B) (C₀ := masterLine1C₀) (cameron := cameron)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default))
    (p := (W, some h)) (by simp)
    (masterHint_line4a_match (e := e) (f := f) (u := u) (v := v)
      (G4 := masterLine4cdOps c tt dd GD dD) (G5 := masterL57Ops c' b' t d dc dp e f E)
      (d4 := (dD, default)) (d5 := default) (p := (W, h)) hr
      (masterLine4a_loop (p := (W, h)) a b hx hW.2.2.1 hW.1 hW.2.1 hinv hp hG hϕ h64 hr))
  refine loopMatchG_of_loopMatch_onCalls (fun _ => True) ?_ hM (fun _ _ => trivial)
  intro j s J hJ _
  obtain ⟨hj, -⟩ := masterGuardedChild_some hJ
  exfalso
  have hw0 : (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
      c' b' t d dc dp E).width (W, some h) = 0 := by
    have hl : masterIsLine1 ((W, some h) : RawMasterSI) = false := by
      cases hq : masterIsLine1 ((W, some h) : RawMasterSI)
      · rfl
      · exact absurd ((masterIsLine1_iff _).mp hq) (by simp)
    simp only [masterNodeFullOps, masterNodeOps, masterTopOps, MasterOps.pairIte, hl,
      Bool.false_eq_true, if_false, masterHintL57Ops, masterHintOps,
      masterRouteAt_false (p := (W, h)) (k := 1) (by omega),
      masterRouteAt_true (p := (W, h)) hr, if_true]
    rfl
  omega

include hW hinv in
/-- **Section 15, line 4b, in the full node carrier, with its children.**  At a well-formed
node whose hint has its meaning and whose route is line 4b, the full node carrier walks the
round of line 4b (the giant top-action round of Sec. 13, lifted from the window), which
returns `Iso_G(x,y)` in at most `7n` calls, and every child it produces on the path of the
match is a good node with at most `2n/3` of the window. -/
theorem masterNodeFull_hint_line4b_matchGood {a b : ℕ} (hg : MasterHintGood (W, h))
    (hr : masterHintRoute (W, h) = 3) (hcap : TopwpCap e f) (houter : Top4wCap e f u v) :
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
      T.run = (decWinSI n W).answer ∧ T.calls.length ≤ 7 * W.1.length := by
  obtain ⟨m, φ, B, hB, hp, hG, hϕ, -, -, -, -, -, h64⟩ := hg
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hw := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have h64' : 64 ≤ W.1.length := h64
  obtain ⟨hrun, hlen, hwin⟩ := master4Tree_spec (p := (W, h)) hx.1 hw hnd hlt hinv hp hG hϕ h64 hr
  refine ⟨master4Tree (p := (W, h)) hnd hlt hinv hp hG hϕ h64 hr, ?_, hrun, hlen⟩
  have hM := masterTop_hinted_match (B := masterLine1B) (C₀ := masterLine1C₀) (cameron := cameron)
    (dT := (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default))
    (p := (W, some h)) (by simp)
    (masterHint_line4b_match (e := e) (f := f) (u := u) (v := v)
      (G4 := masterLine4cdOps c tt dd GD dD) (G5 := masterL57Ops c' b' t d dc dp e f E)
      (d4 := (dD, default)) (d5 := default) (p := (W, h)) hr
      (master4b_match (p := (W, h)) a b e f u v hx hy hw hnd hlt hinv hp hG hϕ h64 hr hcap
        houter))
  refine loopMatchG_of_loopMatch_onCalls (fun K => 3 * K.windowSize ≤ 2 * W.1.length) ?_ hM
    hwin
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_hint (by simp)] at hFc
  simp only [masterHintL57Ops, masterHintOps, MasterOps.pairIte,
    masterRouteAt_false (p := (W, h)) (k := 1) (by omega),
    masterRouteAt_false (p := (W, h)) (k := 2) (by omega),
    masterRouteAt_true (p := (W, h)) hr, Bool.false_eq_true, if_false, if_true,
    master4bOps, Option.isSome_some, master4OpenChild] at hFc
  obtain ⟨K, -, rfl⟩ := Option.map_eq_some_iff.mp hFc
  have hJW := aggnCheckedWindow_wf (masterHintGet ((W, some h) : RawMasterSI)).1.2.2.2.1
    (master4OpenRead K)
  have hxl : (masterHintGet ((W, some h) : RawMasterSI)).1.2.2.2.1.length = n := hx.1
  rw [hxl] at hJW
  exact masterNodeGood_of_checked (hdeg.trans hx.1) hJW rfl hinvJ (by omega) hV

end Node
end Full

end Algo
