import Workspace.Algo.TopMasterRecursionDom

/-!
# The master recursion at lines 4c–4d (route 4)

Section 15, lines 4c–4d: at a hinted node whose top action is primitive with a giant
representation and large defect, the Master Algorithm finds the versions of line 4c and runs
Procedure Align (Sec. 14.1) on them (line 4d). The master recursion of the full node carrier
(`Algo.siWorkspaceRoutine_of_masterParamRoutes`) asks, at every good admitted hinted node of
route `4` or `5`, for one tree the carrier walks with good, progressing children, that is
correct and has a bounded number of calls (`Algo.MasterParamRoutes`). This file gives the
route-`4` part.

The obligation is split by route (`Algo.MasterParamRoute`, `Algo.masterParamRoutes_of_route`,
`Workspace/Algo/TopMasterRecursionL57.lean`); this file supplies `MasterParamRoute … 4`.

* `Algo.masterRoute4_treeOK_of_matchG`: a walk of the lift of the round of any
  `Babai.Line4cdData` on the node's window, with good children, is a tree with
  `Algo.MasterNodeTreeOK` whose number of calls is the cost of the data.
* `Algo.masterRoute4_matchG`: a walk of that lift in which every call of the Master's round
  has at most `4|Δ|/5` points (Eq. (72)) has good, progressing children.
* `Algo.masterRoute4_noDom_treeOK`: **no dominant class**. At a good node of route `4` where
  line 6 of Procedure Align finds no dominant color class, the carrier walks the round of
  `Algo.masterNodeFull_line4cd_match` (the loop of Eq. (71)), with at most
  `Algo.masterRoute4Cost` calls.
* `Algo.masterParamRoute4`: route `4`, from the no-dominant case and the dominant-class
  obligation `Algo.MasterRoute4Dom`.
* `Algo.masterRoute4Dom_of_built`: the dominant-class obligation for the carrier
  `GD = Algo.line4dDomOps`, from the match of the Section 13 track
  (`Algo.Line4dDomBuiltMatch`, the statement of `Algo.masterNodeFull_line4cd_dom_match_built`)
  in case 1 and in the cases of lines 7–11 where the round attaches no hint, and at the
  remaining nodes (case 3 with its hinted call) from `Algo.MasterRoute4DomCase3`.
-/

set_option synthInstance.maxSize 4096
set_option quotPrecheck false

namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-! ## The call bound of lines 4c–4d -/

/-- The number of calls of one round of lines 4c–4d on a window of size `n`: the cost that
`Babai.Line4cdDataAt` asks for at the witness `(Algo.line4dQ c tt dd, Babai.c923)` of
Theorem 9.2.3 that the machine meets (`Algo.line4dQ_admissible`). -/
noncomputable def masterRoute4Cost (c tt dd : ℕ) : ℕ → ℕ := line4cdCost (line4dQ c tt dd) c923

theorem masterRoute4Cost_mono (c tt dd : ℕ) : Monotone (masterRoute4Cost c tt dd) :=
  line4cdCost_mono _ _

theorem quasiPolyBound_masterRoute4Cost (c tt dd : ℕ) :
    QuasiPolyBound (masterRoute4Cost c tt dd) :=
  quasiPolyBound_line4cdCost (line4dQ_admissible c tt dd).1 c923

/-! ## A walk of the lifted round of Align is a good tree -/

section Tree

variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {n : ℕ} {W : RawWinSI} {h : RawMasterHint}

/-- The Master's strings of Align at a hinted node, read on the node's window. -/
local notation "ix" => (masterHintTop ((W, h) : MasterHintInput)).2.1
local notation "iy" => (masterHintTop ((W, h) : MasterHintInput)).2.2
local notation "iG" => decGroup W.1.length (masterHintTop ((W, h) : MasterHintInput)).1.1.2

/-- **The lifted round of Align is correct and has the calls of the Master's round.** At a
well-formed node, the lift to the node's domain of the round of a `Babai.Line4cdData` on the
window, shifted by the node's representative (Eq. (59)), returns `Iso_G(x,y)` of the node,
and its calls are the lifts of the calls of the Master's round. -/
theorem masterRoute4_lift_spec (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {par cost : ℕ}
    (D : Line4cdData (Fin W.1.length) ℕ iG (decStrN W.1.length ix) (decStrN W.1.length iy)
      par cost) :
    let T := (top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
      D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A))
    T.run = (decWinSI n W).answer ∧
      T.calls.length ≤ cost ∧
      ∀ J ∈ T.calls, ∃ K ∈ D.shape.red.calls, J.windowSize = K.windowSize := by
  intro T
  have hx := hW.2.2.2.2.2.1
  have hgs := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hgrp := masterLine4b_group (p := ((W, h) : MasterHintInput)) hgs hnd hlt hinv
  have hK : ∀ J ∈ D.shape.red.calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  have hcalls : T.calls = D.shape.red.calls.map
      (topwInstance W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)) := by
    simp only [T, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    exact top4wTree_calls hnd hlt hinv _ _ hK
  refine ⟨?_, ?_, ?_⟩
  · have hix : decStrN W.1.length ix =
        fun i => decStrN n W.2.2.2.1 (winEquiv n W.1 hnd hlt i) :=
      topwRestrictStr_decode hnd hlt _
    have hiy : decStrN W.1.length iy =
        fun i => strAct (decStrN n W.2.2.2.2) (decPerm n W.2.2.1)⁻¹
          (winEquiv n W.1 hnd hlt i) :=
      top4aTarget_restrict hx.1 hnd hlt _ _
    have hval : D.shape.red.run = strIso
        ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
          Set (Perm (Fin W.1.length)))
        (fun i => decStrN n W.2.2.2.1 (winEquiv n W.1 hnd hlt i))
        (fun i => strAct (decStrN n W.2.2.2.2) (decPerm n W.2.2.1)⁻¹
          (winEquiv n W.1 hnd hlt i)) := by
      rw [D.run_red, hgrp, hix, hiy]
    have hrun := top4wTree_run hnd hlt hinv (decStrN n W.2.2.2.1) D.shape.red hK
    rw [hval, topwPreimage_strIso hnd hlt hinv] at hrun
    change (SIReduction.bind _ _).run = _
    rw [SIReduction.run_bind, SIReduction.run_done, hrun]
    change _ = wIso (winSet n W.1) (decCoset n (some (W.2.1, W.2.2.1))) _ _
    rw [decCoset_some, wIso_smul]
    rfl
  · rw [hcalls, List.length_map]
    exact D.calls_length
  · intro J hJ
    rw [hcalls] at hJ
    obtain ⟨K, hKm, rfl⟩ := List.mem_map.mp hJ
    exact ⟨K, hKm, topwInstance_windowSize hnd hlt hinv _ K⟩

/-- **A walk of the lifted round of Align with good children is a good tree**
(`Algo.MasterNodeTreeOK`), with the cost of the data as its number of calls. -/
theorem masterRoute4_treeOK_of_matchG {ω : Type} {R : Round RawMasterSI ω RawCoset}
    (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) {par cost : ℕ} {q : ℕ → ℕ}
    (D : Line4cdData (Fin W.1.length) ℕ iG (decStrN W.1.length ix) (decStrN W.1.length iy)
      par cost) (hq : cost ≤ q W.1.length)
    (hM : LoopMatchG R (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h) (R.width (W, some h)) 0
      (R.init (W, some h))
      ((top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A)))) :
    MasterNodeTreeOK R n q (W, some h)
      ((top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A))) := by
  obtain ⟨hrun, hlen, -⟩ := masterRoute4_lift_spec hW hinv D
  exact ⟨hM, hrun, hlen.trans hq, fun hc => absurd hc not_masterChainRuleNode_hint⟩

/-- **The children of a node of route `4`** in the full node carrier are the children of
lines 4c–4d, read on the node's domain with no hint (`Algo.masterCheckedCall`), provided both
branches of line 6 of Align propose such children. -/
theorem masterRoute4_child {a b : ℕ} (hr : masterHintRoute (W, h) = 4)
    (hGD : masterHasDom c tt dd ((W, some h) : RawMasterSI) = true →
      ∀ z J, GD.child z = some J → ∃ V, J = masterCheckedCall (z.1.1.2.2.2.1, V))
    {j : ℕ} {s : AggnRecomputeState × MasterHintState (TD × AggnRecomputeState) AggnL57GState}
    {J : RawMasterSI}
    (hJ : (masterAdmittedRound a b (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD
      c' b' t d dc dp E)).child ((W, some h), j, s) = some J) :
    (∃ V, J = masterCheckedCall (W.2.2.2.1, V)) ∧
      masterDegree J = masterDegree ((W, some h) : RawMasterSI) ∧
      rawIsInvariant (J.1.2.1, J.1.1) = true := by
  obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
  refine ⟨?_, hdeg, hinvJ⟩
  rw [masterNodeFull_child_hint (by simp)] at hFc
  simp only [masterHintL57Ops, masterHintOps, MasterOps.pairIte,
    masterRouteAt_false (p := (W, h)) (k := 1) (by omega),
    masterRouteAt_false (p := (W, h)) (k := 2) (by omega),
    masterRouteAt_false (p := (W, h)) (k := 3) (by omega),
    masterRouteAt_true (p := (W, h)) hr, Bool.false_eq_true, if_false, if_true,
    masterLine4cdOps] at hFc
  split_ifs at hFc with hsel
  · exact hGD hsel _ _ hFc
  · simp only [line4dOps] at hFc
    obtain ⟨K, -, rfl⟩ := Option.map_eq_some_iff.mp hFc
    exact ⟨_, rfl⟩

/-- A checked child of a hinted node whose decoded window has at most `4/5` of the node's
window is good and makes the progress of Sec. 11.4 (recurrence (ii)/(v), first form). -/
theorem masterNodeGood_of_checked_five {J : RawMasterSI} {V : RawWinSI}
    (hJV : J = masterCheckedCall (W.2.2.2.1, V)) (hxn : W.2.2.2.1.length = n)
    (hdeg : masterDegree J = n) (hinvJ : rawIsInvariant (J.1.2.1, J.1.1) = true)
    (h1 : 1 ≤ W.1.length) (h5 : 5 * (decWinSI n J.1).windowSize ≤ 4 * W.1.length) :
    MasterNodeGood n J ∧ MasterStepProgress (W, some h) J := by
  subst hJV
  have hJW := aggnCheckedWindow_wf W.2.2.2.1 V
  rw [hxn] at hJW
  have hJ : MasterRawNode n (masterCheckedCall (W.2.2.2.1, V)) :=
    ⟨hdeg, hJW, (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
  refine ⟨⟨hJ, fun h' hh' => by cases hh'⟩, masterStepProgress_hint_of_window h1 ?_⟩
  rw [masterWindowSize_eq_of_rawNode hJ]
  exact h5

/-- **Eq. (72) gives good children.** If the full node carrier walks the lift of the round of
a `Babai.Line4cdData` whose every call has at most `4|Δ|/5` points, then every child it
produces on the path of the walk is good and makes progress. -/
theorem masterRoute4_matchG {a b : ℕ} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) (hr : masterHintRoute (W, h) = 4)
    (h1 : 1 ≤ W.1.length)
    (hGD : masterHasDom c tt dd ((W, some h) : RawMasterSI) = true →
      ∀ z J, GD.child z = some J → ∃ V, J = masterCheckedCall (z.1.1.2.2.2.1, V))
    {par cost : ℕ}
    (D : Line4cdData (Fin W.1.length) ℕ iG (decStrN W.1.length ix) (decStrN W.1.length iy)
      par cost)
    (hwin : ∀ K ∈ D.shape.red.calls, 5 * K.windowSize ≤ 4 * W.1.length)
    (hM : LoopMatch (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E))
      (fun J => decWinSI n J.1) (decCoset n) (W, some h)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).width
        (W, some h)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).init
        (W, some h))
      ((top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A)))) :
    LoopMatchG (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E))
      (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).width
        (W, some h)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).init
        (W, some h))
      ((top4wTree W.1 hW.1 hW.2.1 (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
        D.shape.red).bind (fun A => .done (decPerm n W.2.2.1 • A))) := by
  obtain ⟨-, -, hcalls⟩ := masterRoute4_lift_spec hW hinv D
  refine loopMatchG_of_loopMatch_onCalls (fun K => 5 * K.windowSize ≤ 4 * W.1.length) ?_ hM
    ?_
  · intro j s J hJ hV
    obtain ⟨⟨V, hJV⟩, hdeg, hinvJ⟩ := masterRoute4_child hr hGD hJ
    exact masterNodeGood_of_checked_five hJV hW.2.2.2.2.2.1.1 (hdeg.trans hW.2.2.2.2.2.1.1)
      hinvJ h1 hV
  · intro J hJ
    obtain ⟨K, hK, hJK⟩ := hcalls J hJ
    rw [hJK]
    exact hwin K hK

end Tree

/-! ## Route 4 without a dominant class -/

section NoDom

variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {n : ℕ}

/-- **Section 15, lines 4c–4d, at a good node without a dominant class.** At a good node of
route `4` where line 6 of Procedure Align finds no dominant color class, the full node carrier
walks the lift of the round of Align of the Master (`Algo.masterNodeFull_line4cd_match`: the
loop of Eq. (71) over the versions of line 4c), which returns `Iso_G(x,y)` in at most
`Algo.masterRoute4Cost c tt dd |Δ|` calls, each on at most `4|Δ|/5` points (Eq. (72)), so
every child is good and makes progress. -/
theorem masterRoute4_noDom_treeOK {a b : ℕ} (hb : Line4cBounds c tt dd)
    {W : RawWinSI} {h : RawMasterHint} (hg : MasterNodeGood n (W, some h))
    (hr : masterHintRoute (W, h) = 4)
    (hnd' : masterHasDom c tt dd ((W, some h) : RawMasterSI) = false) :
    ∃ T, MasterNodeTreeOK (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) n
      (masterRoute4Cost c tt dd) (W, some h) T := by
  obtain ⟨⟨-, hW, hinv⟩, hgood⟩ := hg
  obtain ⟨m, φ, B', hB, hp, hG, hϕ, -, -, -, -, -, h64⟩ := hgood h rfl
  have h64' : 64 ≤ W.1.length := h64
  obtain ⟨D, hdom, -, hM⟩ := masterNodeFull_line4cd_match (a := a) (b := b) (B := B)
    (C₀ := C₀) (cameron := cameron) (e := e) (f := f) (u := u) (v := v) (GD := GD) (dD := dD)
    (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E)
    (p := (W, h)) hW.2.2.2.2.2.1 hW.2.2.2.2.2.2 hW.2.2.1 hW.1 hW.2.1 hinv hp hG hϕ h64 hr hb
    hnd'
  have hwin : ∀ K ∈ D.shape.red.calls, 5 * K.windowSize ≤ 4 * W.1.length :=
    line4cdData_five_mul_windowSize_of_dom_none D hdom
  refine ⟨_, masterRoute4_treeOK_of_matchG hW hinv D ?_
    (masterRoute4_matchG hW hinv hr (show 1 ≤ W.1.length by omega)
      (fun hd' => by rw [hnd'] at hd'; cases hd') D hwin hM)⟩
  rw [Fintype.card_fin]
  rfl

end NoDom

/-! ## Route 4 -/

section Route

variable {TD : Type} {B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    {n : ℕ}

/-- **The dominant-class part of route `4`**: at every good, admitted node of route `4` where
line 6 of Procedure Align finds a dominant color class, the carrier walks a tree with
`Algo.MasterNodeTreeOK`. -/
def MasterRoute4Dom {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) (q : ℕ → ℕ)
    (c tt dd : ℕ) : Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) → R.WF (W, some h) →
    masterHintRoute (W, h) = 4 → masterHasDom c tt dd ((W, some h) : RawMasterSI) = true →
      ∃ T, MasterNodeTreeOK R n q (W, some h) T

/-- **Section 15, lines 4c–4d: the route-`4` part of `Algo.MasterParamRoutes`.** The case
without a dominant class is `Algo.masterRoute4_noDom_treeOK`; the case with one is the
obligation `Algo.MasterRoute4Dom` of the dominant-class carrier `GD`. -/
theorem masterParamRoute4 {a b : ℕ} (hb : Line4cBounds c tt dd)
    {q : ℕ → ℕ} (hq : ∀ k, masterRoute4Cost c tt dd k ≤ q k)
    (hD : MasterRoute4Dom (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) n q c tt dd) :
    MasterParamRoute (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) n q 4 := by
  intro W h hg hwf hr
  cases hd : masterHasDom c tt dd ((W, some h) : RawMasterSI)
  · obtain ⟨T, hT⟩ := masterRoute4_noDom_treeOK (a := a) (b := b) (B := B) (C₀ := C₀)
      (cameron := cameron) (e := e) (f := f) (u := u) (v := v) (dD := dD) (c' := c') (b' := b')
      (t := t) (d := d) (dc := dc) (dp := dp) (E := E) hb hg hr hd
    exact ⟨T, hT.mono_q hq⟩
  · exact hD W h hg hwf hr hd

/-- The children of the dominant-class carrier of line 4d are read on the node's domain with
no hint. -/
theorem line4dDomOps_child_checked (z : RawMasterSI × ℕ × ADState) (J : RawMasterSI)
    (hJ : (line4dDomOps c tt dd).child z = some J) :
    ∃ V, J = masterCheckedCall (z.1.1.2.2.2.1, V) := by
  simp only [line4dDomOps] at hJ
  obtain ⟨K, -, rfl⟩ := Option.map_eq_some_iff.mp hJ
  exact ⟨_, rfl⟩

/-- **The match of the Section 13 track for line 4d with a dominant class**, as a statement:
at a node of route `4` where line 6 of Procedure Align finds a dominant color class, there is
a round of Procedure Align of the Master (`Babai.Line4cdData`, with the cost that
`Babai.Line4cdDataAt` asks at the witness `(Algo.line4dQ, c923)`) with data `Dd` of lines
7–11, and in case 1 of the repair (`Algo.l57Small`), or whenever the round attaches no hint,
the node carrier with `GD = Algo.line4dDomOps` walks its lift. This is the statement of
`Algo.masterNodeFull_line4cd_dom_match_built` (Section 13 track), which proves it. -/
def Line4dDomBuiltMatch (c tt dd : ℕ) : Prop :=
  ∀ {n m : ℕ} {p : MasterHintInput} (_hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (_hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2) (_hgs : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)},
    RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ →
    IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2) → IsGiantRep ϕ →
    64 ≤ p.1.1.length → masterHintRoute p = 4 → Line4cBounds c tt dd →
    ∀ {a b B C₀ : ℕ} {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ}
      {c' b' t d dc dp E : ℕ}, line4dHasDom c tt dd p = true →
    ∃ D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
        (decStrN p.1.1.length (masterHintTop p).2.1)
        (decStrN p.1.1.length (masterHintTop p).2.2) m
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length))),
      ∃ Dd : AlignDominantRoundData (Fin p.1.1.length), D.shape.dom = some Dd ∧
        ((l57Small (line4dDomHdr c tt dd p) = true ∨ ∀ J, D.shape.hint J = none) →
          LoopMatch (masterAdmittedRound a b
              (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
                c' b' t d dc dp E))
            (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
            ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
              c' b' t d dc dp E).width (p.1, some p.2)) 0
            ((masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
              c' b' t d dc dp E).init (p.1, some p.2))
            ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
              D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))))

/-- **Case 3 of lines 7–11 of Procedure Align, at a node**: where the round
of Align of the Master has a dominant class and attaches the Johnson hint of line 11 to a call
(`Babai.AlignDominantRoundData.hint`: the Chain Rule call on a dominant orbit of `G*`), the
carrier walks a tree with `Algo.MasterNodeTreeOK`. The call with the hint may have the whole
window, so its child must carry the hint on the RAM (a raw hint for the action of `G*` on
`Γ*`) and make progress through its Johnson parameter `m* ≤ m/2` (Eq. (73)); this routine is
the part of the Section 13 track still to come. -/
def MasterRoute4DomCase3 {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) (q : ℕ → ℕ)
    (c tt dd : ℕ) : Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) → R.WF (W, some h) →
    masterHintRoute (W, h) = 4 → masterHasDom c tt dd ((W, some h) : RawMasterSI) = true →
    (∃ (par cost : ℕ)
        (D : Line4cdData (Fin W.1.length) ℕ
          (decGroup W.1.length (masterHintTop ((W, h) : MasterHintInput)).1.1.2)
          (decStrN W.1.length (masterHintTop ((W, h) : MasterHintInput)).2.1)
          (decStrN W.1.length (masterHintTop ((W, h) : MasterHintInput)).2.2) par cost)
        (Dd : AlignDominantRoundData (Fin W.1.length)),
        D.shape.dom = some Dd ∧ ∃ J, D.shape.hint J ≠ none) →
      ∃ T, MasterNodeTreeOK R n q (W, some h) T

/-- **Section 15, lines 4c–4d with a dominant class, for `GD = Algo.line4dDomOps`.** From the
match of the Section 13 track (`Algo.Line4dDomBuiltMatch`): where the Master's round attaches
no hint (case 1, and the cases of lines 7–11 without the hint of line 11), the carrier walks
its lift with at most `Algo.masterRoute4Cost` calls, and every call has at most `4|Δ|/5`
points (Eq. (72)), so every child is good and makes progress. Where the round attaches a hint
(case 3), the tree is `Algo.MasterRoute4DomCase3`. -/
theorem masterRoute4Dom_of_built {a b : ℕ} (hb : Line4cBounds c tt dd)
    (hbuilt : Line4dDomBuiltMatch c tt dd) {q3 : ℕ → ℕ}
    (h3 : MasterRoute4DomCase3 (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E)) n q3 c tt dd) :
    MasterRoute4Dom (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E)) n (fun k => masterRoute4Cost c tt dd k + q3 k) c tt dd := by
  intro W h hg hwf hr hd
  obtain ⟨⟨hdeg, hW, hinv⟩, hgood⟩ := hg
  obtain ⟨m, φ, B', hB, hp, hG, hϕ, -, -, -, -, -, h64⟩ := hgood h rfl
  have h64' : 64 ≤ W.1.length := h64
  obtain ⟨D, Dd, hdom, hM⟩ := hbuilt (p := (W, h)) hW.2.2.2.2.2.1 hW.2.2.2.2.2.2 hW.2.2.1 hW.1
    hW.2.1 hinv hp hG hϕ h64 hr hb (a := a) (b := b) (B := B) (C₀ := C₀) (cameron := cameron)
    (e := e) (f := f) (u := u) (v := v) (c' := c') (b' := b') (t := t) (d := d) (dc := dc)
    (dp := dp) (E := E) hd
  by_cases hnh : ∀ J, D.shape.hint J = none
  · have hwin : ∀ K ∈ D.shape.red.calls, 5 * K.windowSize ≤ 4 * W.1.length :=
      line4cdData_five_mul_windowSize_of_noHint D hnh
    refine ⟨_, (masterRoute4_treeOK_of_matchG hW hinv D ?_
      (masterRoute4_matchG hW hinv hr (show 1 ≤ W.1.length by omega) (fun _ => line4dDomOps_child_checked) D hwin
        (hM (Or.inr hnh)))).mono_q fun k => Nat.le_add_right _ (q3 k)⟩
    rw [Fintype.card_fin]
    rfl
  · simp only [not_forall] at hnh
    obtain ⟨T, hT⟩ := h3 W h ⟨⟨hdeg, hW, hinv⟩, hgood⟩ hwf hr hd ⟨m, _, D, Dd, hdom, hnh⟩
    exact ⟨T, hT.mono_q fun k => Nat.le_add_left _ _⟩

/-- **Section 15, lines 4c–4d: the route-`4` part of `Algo.MasterParamRoutes` for the node
carrier with `GD = Algo.line4dDomOps`**, from the Section 13 match (`Algo.Line4dDomBuiltMatch`)
and the case-3 tree (`Algo.MasterRoute4DomCase3`). The call bound is
`Algo.masterRoute4Cost c tt dd + q3`. -/
theorem masterParamRoute4_line4dDom {a b : ℕ} (hb : Line4cBounds c tt dd)
    (hbuilt : Line4dDomBuiltMatch c tt dd) {q3 : ℕ → ℕ}
    (h3 : MasterRoute4DomCase3 (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E)) n q3 c tt dd) :
    MasterParamRoute (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd (line4dDomOps c tt dd) default
        c' b' t d dc dp E)) n (fun k => masterRoute4Cost c tt dd k + q3 k) 4 :=
  masterParamRoute4 hb (fun _ => Nat.le_add_right _ _)
    (masterRoute4Dom_of_built hb hbuilt h3)

end Route

end Algo
