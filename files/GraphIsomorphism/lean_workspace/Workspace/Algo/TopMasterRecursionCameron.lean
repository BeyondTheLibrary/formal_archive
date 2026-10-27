import Workspace.Algo.TopMasterRecursionLine1

/-! # The master recursion at step 6 of line 1: the Johnson hint of the children

Section 11.3, steps 6–7: at a node where the route test selects step 6, the Master Algorithm
descends from `K` to the subgroup `K₁` of Theorem 11.2.1.  When `G₁ = K₁^Δ` is transitive the
calls are Johnson cases and the round attaches to them the data of step 7
(`Babai.DescentData.johnsonCaseData`); line 2 of the Master Algorithm then processes them.

On the machine the hint is a raw pair `(rows, t)`.  Its meaning at a node is
`Algo.MasterHintGood`, the raw form of `Babai.JohnsonCaseData`: a giant representation
`ϕ : G → S_m` of the group `G` induced on the window, whose images are the stored rows, a
system of imprimitivity `ℬ` of `G` with at least two blocks, labelled by the `t`-subsets of
`[m]` compatibly with `ϕ`, the parameter bounds `1 ≤ t`, `2t < m ≤ |Δ|`, transitivity of `G`,
and the window bound `64 ≤ |Δ|`.

This file proves that the Cameron children of step 6 carry a hint with this meaning
(`Algo.masterCamChild_hintGood`), and that, with the unhinted children of the intransitive
case, every child the carrier produces on the path of the match makes the progress of
Sec. 11.4 (`Algo.masterNodeFull_cameron_matchG`), which is `Babai.DescentData.decreases_branch`
read on the raw nodes.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- **The meaning of a stored Johnson hint** (Sec. 15, lines 2–3; the raw form of
`Babai.JohnsonCaseData`), on the top action `A = ((Δ, G), rows)` of a hinted node and its
parameter `t`, with `G` the group induced on the window `Δ`: there are a giant
representation `ϕ : G → S_m` whose images of the generators are the stored rows (`Algo.RawAction.WF`), and a system of imprimitivity `ℬ`
of `G` with at least two blocks, labelled by the `t`-subsets of `[m]` so that `G` acts on
`ℬ` through `ϕ` (`Algo.MasterHintBlockLink`, Definition 11.4.1).  Moreover `G` is transitive,
`1 ≤ t`, `2t < m`, `m ≤ |Δ|` and `64 ≤ |Δ|`. -/
def MasterHintGoodAt (A : RawAction) (t : ℕ) : Prop :=
  ∃ (m : ℕ) (ϕ : decGroup A.1.1.length A.1.2 →* Perm (Fin m))
    (B : Set (Set (Fin A.1.1.length)))
    (hB : IsSystemOfImprimitivity (decGroup A.1.1.length A.1.2) Set.univ B),
    RawAction.WF A.1.1.length m A ϕ ∧
      IsTransitive (decGroup A.1.1.length A.1.2) ∧ IsGiantRep ϕ ∧
      Nonempty (MasterHintBlockLink (t := t) hB.permutes ϕ) ∧
      (∃ U ∈ B, ∃ V ∈ B, U ≠ V) ∧ 1 ≤ t ∧ 2 * t < m ∧ m ≤ A.1.1.length ∧
      64 ≤ A.1.1.length

/-- The meaning of the hint at a hinted node `p`: `Algo.MasterHintGoodAt` on its top action
`((Δ, G), rows)` and its parameter `t`. -/
def MasterHintGood (p : MasterHintInput) : Prop :=
  MasterHintGoodAt (masterHintTop p).1 p.2.2

/-- **A good node of the master recursion**: a well-formed raw node, whose hint, if any, has
the meaning `Algo.MasterHintGood`. -/
def MasterNodeGood (n : ℕ) (P : RawMasterSI) : Prop :=
  MasterRawNode n P ∧ ∀ h, P.2 = some h → MasterHintGood (P.1, h)

/-- The parameter of a hinted node with a good hint is the Johnson parameter `m` of its
hint, and it is at most the window size. -/
theorem masterParameter_le_of_hintGood {W : RawWinSI} {h : RawMasterHint}
    (hg : MasterHintGood (W, h)) :
    masterParameter ((W, some h) : RawMasterSI) ≤ masterWindowSize ((W, some h) : RawMasterSI) := by
  obtain ⟨m, ϕ, B, hB, hp, -, -, -, -, -, -, hm, -⟩ := hg
  change h.1.1.length ≤ W.1.length
  have h1 : h.1.1.length = m := hp.2.1
  have h2 : m ≤ W.1.length := hm
  omega

/-! ### The Cameron children -/

/-- The preparation of the group frame does not change the top action of a Cameron child. -/
theorem masterCamPrepared_childTop (c : RawCameron) (W : RawWinSI) (u : List ℕ × RawGens)
    (j : ℕ) :
    (masterHintTop (masterCameronChildInput (masterCamPrepared (c, (W, u)), j))).1 =
      (masterHintTop (masterCameronChildInput ((c, (W, u)), j))).1 := rfl

/-- The preparation of the group frame does not change the hint parameter of a Cameron
child. -/
theorem masterCamPrepared_childT (c : RawCameron) (W : RawWinSI) (u : List ℕ × RawGens)
    (j : ℕ) :
    (masterCameronChildInput (masterCamPrepared (c, (W, u)), j)).2.2 =
      (masterCameronChildInput ((c, (W, u)), j)).2.2 := rfl

section Child
variable {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (htr : IsTransitive (decGroup W.1.length (primitiveWindowInput W).1)) (hn : 2 ≤ W.1.length)
    {c : RawCameron} (h : c.WF (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length)
    (hhi : (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
      (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
        wreathProduct (JohnsonS c.k c.t) c.s)
    (hlo : basePower (JohnsonA c.k c.t) c.s ≤
      (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron c h)).toMonoidHom)

include hx hw hnd hlt hinv htr hn h hhi in
/-- **Step 7, transitivity.**  When the computed kernel `K₁` has a single orbit on the
window, the group the Cameron child induces on the window is transitive. -/
theorem masterCamChild_transitive
    (h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1) (j : ℕ) :
    IsTransitive (decGroup W.1.length
      (masterHintTop (masterCameronChildInput ((c, masterWindowBlockInput W), j))).1.1.2) := by
  classical
  have ha := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hi := isInvariant_of_le hinv (camLiftGens_le (p := masterWindowBlockAction W) ha h hhi)
  have hwf := camLiftGens_wf (c := c) ha
  have he := decGroup_rawRestrictGens_of_raw (dom := W.2.2.2.1) hwf hnd hlt hi
  change IsTransitive (decGroup W.1.length
    (rawRestrictGens ((W.2.2.2.1, camLiftGens (c, masterWindowBlockAction W)), W.1)))
  rw [he]
  have hne : Nonempty (winSet n W.1) := by
    obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos (show 0 < W.1.length by omega)
    exact ⟨⟨⟨u, hlt u hu⟩, hu⟩⟩
  have hG : IsTransitive (restrictTo (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) hi) := by
    rw [isTransitive_iff_orbitList_length]
    have hperm := masterOrbitWindows_perm
      (W := (W.1, camLiftGens (c, masterWindowBlockAction W), W.2.2)) hwf hlt hi
    have hl := hperm.length_eq
    rw [masterOrbitWindows, List.length_map] at hl
    rw [← hl]
    exact h1
  exact masterTransitive_of_image (winEquiv n W.1 hnd hlt) _ _
    (topwCompat hnd hlt hi (1 : restrictTo (decGroup n (camLiftGens (c, masterWindowBlockAction W)))
      (winSet n W.1) hi →* Perm (Fin 0))).group_image hG

include hx hw hnd hlt hinv htr hn h hhi hlo in
/-- **Step 7: the hint of a Cameron child has its meaning.**  When `K₁` has a single orbit on
the window, every child the step-6 carrier opens, in the prepared group frame, carries a
Johnson hint with the meaning `Algo.MasterHintGood`: the recovered giant representation
`ϕ : G₁ → S_k` (Theorem 11.2.1 and Prop. 11.2.5), the union blocks `{⋃ C | C ∈ 𝒞}` labelled
by the `t`-subsets of `[k]`, and the bounds `1 ≤ t`, `2t < k ≤ |Δ|`, `64 ≤ |Δ|`. -/
theorem masterCamChild_hintGood (h64 : 64 ≤ W.1.length)
    (h1 : (winOrbits (camLiftGens (c, masterWindowBlockAction W), W.1)).length = 1) (j : ℕ) :
    MasterHintGood (masterCameronChildInput (masterCamPrepared (c, masterWindowBlockInput W), j)) := by
  have hm : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ W.1.length :=
    (blocksWF_rawMinBlocks (rfl : W.1.length = W.1.length) (primitiveWindowInput W).1).length_le
  obtain ⟨hwf, hg, ⟨L⟩⟩ := masterCameronChild_linked hx hw hnd hlt hinv htr hn h hhi hlo j
  unfold MasterHintGood
  rw [masterCamPrepared_childTop, masterCamPrepared_childT]
  exact ⟨c.k, masterCameronChildHom hx hw hnd hlt hinv htr hn h hhi j,
    masterCameronUnionBlocks W c, masterCameronChildSystem hx hw hnd hlt hinv htr hn h hhi hlo j,
    hwf, masterCamChild_transitive hx hw hnd hlt hinv htr hn h hhi h1 j, hg, ⟨L⟩,
    masterCameronChild_two hx hw hnd hlt hinv htr hn h hhi hlo j, h.t_pos, h.k_gt,
    h.bounds.2.2.trans hm, h64⟩

end Child

/-! ### The round of step 6 with its children -/

section FullMatch
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Section 15, line 1, step 6, in the full node carrier, with its children.**  At a
well-formed node without hint where the route test selects step 6, the full node carrier
walks the round of line 1 (`Algo.masterLine1Tree`), and every child it produces on the path
of the match is a good node (`Algo.MasterNodeGood`) that makes the progress of Sec. 11.4.
This is `Babai.DescentData.decreases_branch` on the raw nodes: when `G₁` is transitive the
child keeps the window and carries the Johnson hint of step 7, whose parameter `k ≤ |Δ|`
halves the parameter `2|Δ|` of the node (recurrence (ii)); otherwise the child is an orbit of
`G₁`, of at most half the window (Fact 11.1.8). -/
theorem masterNodeFull_cameron_matchG {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) (hr4 : masterLine1Route W = 4) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1Tree hW hinv hc hs) := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  have hw := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hr : masterReduceRoute masterLine1B masterLine1C₀ W = 4 := hr4
  have H := masterCamRoute_spec hx hw hnd hlt hinv masterLine1_cameron_cutoff hr hc hs
    masterLine1_blocks
  have htr := masterCamRoute_transitive hw hnd hlt hinv hr
  have hn := masterCamRoute_two hw hnd hlt hinv masterLine1_cameron_cutoff hr
  have h64 := masterCamRoute_window hw hnd hlt hinv masterLine1_cameron_cutoff hr
  have hwindow := masterCamRoute_windowSize hw hnd hlt hinv masterLine1_cameron_cutoff hr
  set cc := (masterCamRouteInput cameron (W, none)).1 with hcc
  have hsize : (masterGroupInstance n W).windowSize = W.1.length := ncard_winSet W.1 hnd hlt
  -- the condition on the calls: outside the transitive case, at most half the window
  let V : SIInstance (Fin n) ℕ → Prop := fun K =>
    (winOrbits (camLiftGens (cc, masterWindowBlockAction W), W.1)).length ≠ 1 →
      2 * K.windowSize ≤ W.1.length
  have hcalls : ∀ K ∈ (masterLine1Tree hW hinv hc hs).calls, V K := by
    intro K hK hne
    have h0 : masterLine1Route W ≠ 0 := by omega
    have h1 : masterLine1Route W ≠ 1 := by omega
    have h2 : masterLine1Route W ≠ 2 := by omega
    have h3 : masterLine1Route W ≠ 3 := by omega
    unfold masterLine1Tree masterLine1Case at hK
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
  have hm := masterTop_line1_match (a := a) (b := b) hW hinv hc hs
    (masterHintL57Ops e f u v (masterLine4cdOps c tt dd GD dD) (dD, default) c' b' t d dc dp E)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default) hcap
  refine loopMatchG_of_loopMatch_onCalls V ?_ hm hcalls
  intro j s J hJ hV
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  rw [masterNodeFull_child_line1 rfl] at hFc
  have hnc : ¬ MasterChainRuleNode ((W, none) : RawMasterSI) := fun hch => by
    have := hch.2
    change masterLine1Route W = 2 at this
    omega
  have hpP : masterParameter ((W, none) : RawMasterSI) = 2 * W.1.length := rfl
  simp only [masterLine1Ops, MasterOps.ite, masterRouteIs_false (W := W) (k := 0) (by omega),
    masterRouteIs_false (W := W) (k := 1) (by omega), masterRouteIs_false (W := W) (k := 2)
      (by omega), masterRouteIs_false (W := W) (k := 3) (by omega), Bool.false_eq_true,
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
(`Algo.masterLine1Tree`), and every child it produces on the path of the match is a good
node that makes the progress of Sec. 11.4 (`Babai.Line1Case.decreases_branch`). -/
theorem masterNodeFull_line1_matchGood {a b n : ℕ} {W : RawWinSI}
    (hW : AggnCheckedWindowWF n W) (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hc : PolyFun cameron) (hs : CameronSpec cameron)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E))
      (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, none) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, none)
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).width (W, none)) 0
      ((masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
          c' b' t d dc dp E).init (W, none))
      (masterLine1Tree hW hinv hc hs) := by
  by_cases hr : masterLine1Route W = 4
  · exact masterNodeFull_cameron_matchG hW hinv hc hs hcap hr
  · refine (masterNodeFull_line1_matchG hW hinv hc hs hcap hr).mono ?_
    rintro J ⟨hJ, hJ2, hpr⟩
    exact ⟨⟨hJ, fun h hh => by rw [hJ2] at hh; cases hh⟩, hpr⟩

end FullMatch

end Algo
