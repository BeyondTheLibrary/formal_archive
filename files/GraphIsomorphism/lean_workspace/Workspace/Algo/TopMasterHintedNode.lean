import Workspace.Algo.TopMasterHintedChild
import Workspace.Algo.TopMasterRecursionDom

/-! # The node carrier with the hinted children of Procedure Align, line 11

Section 15, lines 4d and 5–7, with Procedure Align lines 7–11 as repaired in the corrected paper:
in case 3 of a dominant color class the first call of the Chain Rule, on the dominant orbit of
`G*`, keeps the giant representation `ϕ*` and is a Johnson case with parameter `m* ≤ m/2`
(Eq. (73)). The node carrier proposes that call with its hint through
`Algo.MasterOps.withHint`, at both places where Procedure Align runs:

* line 4d with a dominant class: the dominant-class carrier `GD`, with the hints of `H4`;
* lines 5–7: the carrier `Algo.masterL57Ops`, with the hints of `H5`.

`Algo.masterNodeHOps` is this node carrier. It runs every other line as
`Algo.masterNodeFullOps` does, and has the same width, fold state, update and answer; only the
children at the two places above may carry a hint. So every match of the full node carrier at
a node of another route carries over (`Algo.masterNodeH_child_eq`, `Algo.masterNodeH_treeOK`),
and the recursion (`Algo.masterRecursionOfTrees`) and the final routine
(`Algo.siWorkspaceRoutine_of_hintedRoutes`) need, besides the line-1–4b data, only the rounds
of routes 4 and 5 on the new carrier (`Algo.MasterParamRoute`), whose conditions on the
children (`Algo.MasterNodeGood`, `Algo.MasterStepProgress`) already allow a hinted child that
keeps the window and halves the parameter.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- **The node carrier of Section 15 with the hinted children of Procedure Align, line 11**:
`Algo.masterNodeFullOps`, in which the dominant-class carrier `GD` of line 4d proposes its
children with the hints of `H4`, and the carrier of lines 5–7 with the hints of `H5`. -/
noncomputable def masterNodeHOps {TD : Type} (B C₀ : ℕ)
    (cameron : RawGens × List ℕ → Option RawCameron) (e f u v c tt dd : ℕ) (GD : MasterOps TD)
    (dD : TD) (c' b' t d dc dp E : ℕ)
    (H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint) :
    MasterOps (AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState) :=
  masterTopOps B C₀ cameron
    (masterHintOps e f u v (masterLine4cdOps c tt dd (GD.withHint H4) dD)
      ((masterL57Ops c' b' t d dc dp e f E).withHint H5) (dD, default) default)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), default)

section Node
variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}

theorem masterNodeH_width :
    (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5).width =
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).width := by
  simp only [masterNodeHOps, masterNodeFullOps, masterNodeOps, masterHintL57Ops, masterTopOps,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte, MasterOps.withHint_width,
    MasterOps.withHint_init, MasterOps.withHint_combine, MasterOps.withHint_finish]

theorem masterNodeH_init :
    (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5).init =
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).init := by
  simp only [masterNodeHOps, masterNodeFullOps, masterNodeOps, masterHintL57Ops, masterTopOps,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte, MasterOps.withHint_width,
    MasterOps.withHint_init, MasterOps.withHint_combine, MasterOps.withHint_finish]

theorem masterNodeH_combine :
    (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5).combine =
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).combine := by
  simp only [masterNodeHOps, masterNodeFullOps, masterNodeOps, masterHintL57Ops, masterTopOps,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte, MasterOps.withHint_width,
    MasterOps.withHint_init, MasterOps.withHint_combine, MasterOps.withHint_finish]

theorem masterNodeH_finish :
    (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5).finish =
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).finish := by
  simp only [masterNodeHOps, masterNodeFullOps, masterNodeOps, masterHintL57Ops, masterTopOps,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte, MasterOps.withHint_width,
    MasterOps.withHint_init, MasterOps.withHint_combine, MasterOps.withHint_finish]

theorem masterRoute_le_five (P : RawMasterSI) : masterRoute P ≤ 5 := by
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact Nat.zero_le _
  | some h =>
    change masterHintRoute (W, h) ≤ 5
    rcases masterHintRoute_mem (W, h) with hr | hr | hr | hr | hr <;> omega

/-- **Away from the two places of line 11 the two node carriers propose the same children**:
at a node that is not of route 5, and not of route 4 with a dominant class. -/
theorem masterNodeH_child_eq {P : RawMasterSI} (h5 : masterRoute P ≠ 5)
    (h4 : masterRoute P = 4 → masterHasDom c tt dd P = false) (j : ℕ)
    (s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState) :
    (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5).child (P, j, s) =
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).child
        (P, j, s) := by
  have hle := masterRoute_le_five P
  simp only [masterNodeHOps, masterNodeFullOps, masterNodeOps, masterTopOps, masterHintL57Ops,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte]
  split_ifs with h0 h1 h2 h3 h4' hd
  all_goals try (with_reducible rfl)
  · simp only [masterRouteAt, decide_eq_true_eq] at h4'
    rw [h4 h4'] at hd
    exact absurd hd Bool.false_ne_true
  · simp only [masterIsLine1, masterRouteAt, decide_eq_true_eq] at h0 h1 h2 h3 h4'
    omega

/-- **A match of the full node carrier at a node where the children agree is a match of the
hinted node carrier.** -/
theorem masterNodeH_matchG_of_full {a b n : ℕ} {P : RawMasterSI} {C : RawMasterSI → Prop}
    (h5 : masterRoute P ≠ 5) (h4 : masterRoute P = 4 → masterHasDom c tt dd P = false)
    {w j : ℕ} {s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) C
      (fun J => decWinSI n J.1) (fun _ => decCoset n) P w j s T) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) C
      (fun J => decWinSI n J.1) (fun _ => decCoset n) P w j s T := by
  refine LoopMatchG.embed (R := masterAdmittedRound a b
    (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) id ?_
    (fun j s a => congrFun masterNodeH_combine (P, j, s, a))
    (fun s => congrFun masterNodeH_finish (P, s)) hm
  intro j s
  change masterGuardedChild a b _ (P, j, s) = masterGuardedChild a b _ (P, j, s)
  unfold masterGuardedChild
  rw [masterNodeH_width, masterNodeH_child_eq h5 h4]

/-- The same, for the whole obligation of a node. -/
theorem MasterNodeTreeOK.toH {a b n : ℕ} {q : ℕ → ℕ} {P : RawMasterSI}
    (h5 : masterRoute P ≠ 5) (h4 : masterRoute P = 4 → masterHasDom c tt dd P = false)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hT : MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) n q P T) :
    MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n q P T :=
  ⟨masterNodeH_matchG_of_full h5 h4 hT.1, hT.2⟩

/-- **The hinted node carrier has local costs**, once `GD` has and the two hint routines are
quasipolynomial. -/
theorem masterNodeH_cost [Enc TD] (a b : ℕ) (hc : PolyFun cameron) (dD : TD)
    (CD : MasterOpsCost a b GD) (hH4 : QuasiFun H4) (hH5 : QuasiFun H5) :
    Nonempty (MasterOpsCost a b
      (masterNodeHOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) := by
  obtain ⟨C4⟩ := masterLine4cd_cost a b c tt dd dD (CD.withHint hH4)
  obtain ⟨C5⟩ := masterL57_cost a b c' b' t d dc dp e f E
  obtain ⟨CH⟩ := masterHint_cost a b e f u v (dD, default) default C4 (C5.withHint hH5)
  exact masterTop_cost a b B C₀ hc _ CH
end Node

/-! ### The recursion from one tree at every good node -/

section Rec
variable {S : Type} {a b n : ℕ} {F : MasterOps S} {q : ℕ → ℕ}
    (hT : ∀ P, MasterNodeGood n P → (masterAdmittedRound a b F).WF P →
      ∃ T, MasterNodeTreeOK (masterAdmittedRound a b F) n q P T)

open scoped Classical in
/-- The tree the recursion reads at a node: one with `Algo.MasterNodeTreeOK` at a good,
admitted node; nothing elsewhere. -/
noncomputable def masterTreeOf (P : RawMasterSI) : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if h : MasterNodeGood n P ∧ (masterAdmittedRound a b F).WF P then
    Classical.choose (hT P h.1 h.2)
  else .done ∅

theorem masterTreeOf_spec (P : RawMasterSI) (hG : MasterNodeGood n P)
    (hW : (masterAdmittedRound a b F).WF P) :
    MasterNodeTreeOK (masterAdmittedRound a b F) n q P (masterTreeOf hT P) := by
  classical
  unfold masterTreeOf
  rw [dif_pos ⟨hG, hW⟩]
  exact Classical.choose_spec (hT P hG hW)

/-- **Section 15: the master recursion of a node carrier with one tree at every good node.**
The construction of `Algo.masterRecursionFull`, for any carrier `F` whose admitted round walks
a tree with `Algo.MasterNodeTreeOK` at every good, admitted node, with a monotone call bound
and well-formed answers. -/
noncomputable def masterRecursionOfTrees (hq : Monotone q)
    (hfin : ∀ P s, masterDegree P = n → RawCoset.WF n (F.finish (P, s))) :
    MasterRecursion (masterAdmittedRound a b F) n where
  Good := MasterNodeGood n
  Ch P J := MasterNodeGood n J ∧ MasterStepProgress P J
  ρ := masterTreeOf hT
  q := q
  impl := fun P hG hW => (masterTreeOf_spec hT P hG hW).1
  correct := fun P hG hW => (masterTreeOf_spec hT P hG hW).2.1
  progress := by
    refine ⟨fun _ J hJ => hJ.1, fun P hG => masterWindowSize_eq_of_rawNode hG.1,
      fun P hG _ => ?_, fun P hG hW => (masterTreeOf_spec hT P hG hW).2.2.1,
      fun P hG hW => ?_⟩
    · obtain ⟨W, o⟩ := P
      cases o with
      | none => exact le_of_eq rfl
      | some h =>
        have : masterParameter ((W, some h) : RawMasterSI) ≤
            masterWindowSize ((W, some h) : RawMasterSI) :=
          masterParameter_le_of_hintGood (hG.2 h rfl)
        omega
    · have hT' := masterTreeOf_spec hT P hG hW
      by_cases hch : MasterChainRuleNode P
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

/-! ### Every good node of the hinted carrier walks a tree -/

section Tree
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}

/-- **Every good node of the hinted node carrier walks a tree with what the recursion needs**:
lines 1–4b as in the full node carrier, and the rounds of routes 4 and 5 as supplied. -/
theorem masterNodeH_treeOK {a b n : ℕ} {q45 : ℕ → ℕ} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hcap : masterCameronChildBound n ≤ masterInputCap a b n)
    (hTc : TopwpCap e f) (hTo : Top4wCap e f u v)
    (h4 : MasterParamRoute (masterAdmittedRound a b (masterNodeHOps masterLine1B masterLine1C₀
      cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n q45 4)
    (h5 : MasterParamRoute (masterAdmittedRound a b (masterNodeHOps masterLine1B masterLine1C₀
      cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n q45 5)
    (P : RawMasterSI) (hP : MasterNodeGood n P)
    (hWF : (masterAdmittedRound a b (masterNodeHOps masterLine1B masterLine1C₀
      cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)).WF P) :
    ∃ T, MasterNodeTreeOK (masterAdmittedRound a b (masterNodeHOps masterLine1B masterLine1C₀
      cameron e f u v c tt dd GD dD c' b' t d dc dp E H4 H5)) n (rawMasterRoundCost q45) P T := by
  obtain ⟨W, o⟩ := P
  cases o with
  | some h =>
    rcases masterHintRoute_mem (W, h) with hr | hr | hr | hr | hr
    rotate_left 3
    · obtain ⟨T, hT⟩ := h4 W h hP hWF hr
      exact ⟨T, hT.mono_q fun m => by unfold rawMasterRoundCost; omega⟩
    · obtain ⟨T, hT⟩ := h5 W h hP hWF hr
      exact ⟨T, hT.mono_q fun m => by unfold rawMasterRoundCost; omega⟩
    all_goals
      have hr' : masterRoute ((W, some h) : RawMasterSI) = masterHintRoute (W, h) := rfl
      obtain ⟨T, hT⟩ := masterNodeFull_treeOK_at (GD := GD) (dD := dD) (q45 := q45)
        (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (c := c)
        (tt := tt) (dd := dd) (u := u) (v := v)
        hc hs hcap hTc hTo _ hP hWF (fun W' h' hPW hr45 => by
          cases hPW
          omega)
      exact ⟨T, hT.toH (by omega) (fun h4' => by omega)⟩
  | none =>
    obtain ⟨T, hT⟩ := masterNodeFull_treeOK_at (GD := GD) (dD := dD) (q45 := q45)
      (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E) (c := c)
      (tt := tt) (dd := dd) (u := u) (v := v)
      hc hs hcap hTc hTo _ hP hWF (fun W' h' hPW _ => by cases hPW)
    exact ⟨T, hT.toH (by simp [masterRoute]) (fun h4' => by simp [masterRoute] at h4')⟩
end Tree

set_option synthInstance.maxSize 2048 in
/-- **Theorem 1.1.1 on the RAM, with the hinted children of Procedure Align, line 11.** With
a polynomial-time Cameron recognizer meeting its specification, constants of the line-4b
carrier, a dominant-class carrier `GD` with local costs and well-formed answers, two
quasipolynomial hint routines `H4`, `H5` for the hinted calls of line 11 at line 4d and at
lines 5–7, and, at every degree, the rounds of routes 4 and 5 on the hinted node carrier
(`Algo.MasterParamRoute`, with a monotone quasipolynomial call bound `q45`), the hinted node
carrier solves String Isomorphism in quasipolynomial time. -/
theorem siWorkspaceRoutine_of_hintedRoutes {TD : Type} [Enc TD]
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {e f u v c tt dd : ℕ} (hTc : TopwpCap e f)
    (hTo : Top4wCap e f u v) {GD : MasterOps TD} (dD : TD)
    (CD : MasterOpsCost masterCapA masterCapB GD) {c' b' t d dc dp E : ℕ}
    {H4 : (RawMasterSI × ℕ × TD) × RawMasterSI → Option RawMasterHint}
    {H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint}
    (hH4 : QuasiFun H4) (hH5 : QuasiFun H5) {q45 : ℕ → ℕ}
    (hq45 : Monotone q45) (hq : QuasiPolyBound q45)
    (hGD : ∀ n P s, masterDegree P = n → RawCoset.WF n (GD.finish (P, s)))
    (h4 : ∀ n, MasterParamRoute (masterAdmittedRound masterCapA masterCapB
      (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E H4 H5)) n q45 4)
    (h5 : ∀ n, MasterParamRoute (masterAdmittedRound masterCapA masterCapB
      (masterNodeHOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E H4 H5)) n q45 5) : SIWorkspaceRoutine := by
  obtain ⟨C⟩ := masterNodeH_cost (B := masterLine1B) (C₀ := masterLine1C₀) (e := e) (f := f)
    (u := u) (v := v) (tt := tt) (dd := dd) (c' := c') (b' := b') (t := t) (d := d)
    (dc := dc) (dp := dp) (E := E) (c := c) masterCapA masterCapB hc dD CD hH4 hH5
  obtain ⟨c₁, hc₁⟩ := (quasiPolyBound_line1RoundCost.add quasiPolyBound_masterRoundCost).add hq
  exact siWorkspaceRoutine_of_masterRecursion _ C.runCostQ c₁ fun n =>
    ⟨masterRecursionOfTrees
      (masterNodeH_treeOK hc hs (masterCap_spec n) hTc hTo (h4 n) (h5 n))
      (rawMasterRoundCost_mono hq45)
      (fun P s hP => by
        rw [masterNodeH_finish]
        exact masterNodeFull_finish_wf (hGD n) P s hP), fun m => hc₁ m⟩

end Algo
