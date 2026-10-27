import Workspace.Algo.TopMasterRecursionBuild
import Workspace.Algo.TopMasterL57Node
import Workspace.Algo.TopMasterL57CtxGood

/-! # The master recursion at nodes of lines 5–7

Section 15, lines 5–7: at a hinted node that is not a primitive case (route 5), the Master
Algorithm runs Procedure AggregateCertificates on the window, then what its outcome leads to:
Procedure Align at outcomes (1), (2b) and (3) (`Babai.Line57Shape`), or Cor. 12.0.10 at
outcome (2a) (`Babai.line5Case2aFunCoset`).  On the machine this is the round
`Algo.masterL57Round` on the window, lifted to the node's domain (`Algo.masterL57Ops`).

The recursion (`Algo.MasterParamRoutes`) asks, at every good node of route 5, for a tree the
full node carrier walks with a good child that makes the progress of Sec. 11.4 at every call.
This file reduces that obligation to a tree on the window:

* `Algo.masterNodeFull_hint_line57_matchGood`: any tree `T₀` on the window that the round of
  lines 5–7 walks on the node's context (`Algo.masterL57Ctx`, the window's data in its own size,
  with the letters of the two strings renamed), whose calls lie in the window's group as coset
  instances, have letters at most `2|Δ|` and at most `4/5` of the window, and whose value is
  `Iso_{G_Δ}` of the context's strings (that is `Iso_{G_Δ}(x_Δ, y_Δ)`,
  `Algo.masterL57Ctx_strIso`), lifts, with its letters renamed back, to such a tree of the node
  carrier with as many calls;
* `Algo.masterNodeFull_hint_line57Data_matchGood`: the same for the round of a
  `Babai.Line57Data` without a hint (Eq. (72) supplies the window bound);
* `Algo.masterParamRoute5_of_supply`: the obligation of route 5 from such a window tree at
  every good node of route 5 (`Algo.MasterL57Supply`).

The two parameter routes are split (`Algo.MasterParamRoute`,
`Algo.masterParamRoutes_of_route`), so that route 4 (lines 4c–4d) and route 5 can be supplied
separately.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- **The obligation of one parameter route** `k` (`4` for lines 4c–4d, `5` for lines 5–7):
at every good, admitted hinted node of route `k`, the carrier walks a tree with
`Algo.MasterNodeTreeOK`. -/
def MasterParamRoute {ω : Type} (R : Round RawMasterSI ω RawCoset) (n : ℕ) (q45 : ℕ → ℕ)
    (k : ℕ) : Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) → R.WF (W, some h) →
    masterHintRoute (W, h) = k → ∃ T, MasterNodeTreeOK R n q45 (W, some h) T

theorem masterParamRoutes_of_route {ω : Type} {R : Round RawMasterSI ω RawCoset} {n : ℕ}
    {q45 : ℕ → ℕ} (h4 : MasterParamRoute R n q45 4) (h5 : MasterParamRoute R n q45 5) :
    MasterParamRoutes R n q45 :=
  fun W h hg hw hr => hr.elim (h4 W h hg hw) (h5 W h hg hw)

section Full
variable {TD : Type} {cameron : RawGens × List ℕ → Option RawCameron}
    {e f u v c tt dd : ℕ} {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}

section Node
variable {n : ℕ} {W : RawWinSI} {h : RawMasterHint} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hW hinv in
/-- **Section 15, lines 5–7, in the full node carrier, with its children.**  Let `T₀` be a
tree on the window of a good node of route 5 that the round of lines 5–7 walks from the node's
lines-5–7 node, on the node's context (`Algo.masterL57Ctx`: the group `G_Δ` and the two strings
on the window with their letters renamed).  If every call of `T₀` is a coset instance in
`G_Δ` with letters at most `2|Δ|` and a window of at most `4/5` of the points, and `T₀` returns
`Iso_{G_Δ}` of the context's two strings, then the full node carrier walks the lift of `T₀` with
its letters renamed back (`Algo.masterL57Unl`), shifted to the node's frame; that tree returns
`Iso_G(x,y)`, makes as many calls as `T₀`, and every child the carrier produces on it is a good
node whose window is at most `4/5` of the node's. -/
theorem masterNodeFull_hint_line57_matchGood {a b : ℕ}
    (hE : MasterL57EOK c' b' t d dc dp e f E) (hr : masterHintRoute (W, h) = 5)
    (hgd : MasterHintGood (W, h)) (hΔ : 0 < W.1.length)
    (T₀ : SIReduction (Fin W.1.length) ℕ (Set (Perm (Fin W.1.length))))
    (hm : LoopMatch (masterL57Round c' b' t d dc dp e f) (aggnPhaseDecode W.1.length)
      (decCoset W.1.length) (masterL57Enter (W, some h))
      ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (W, some h))) 0
      ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (W, some h))) T₀)
    (hK : ∀ J ∈ T₀.calls, J.K ⊆
      (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length))))
    (hcos : ∀ J ∈ T₀.calls,
      IsCosetInstance (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2) J)
    (hrun : T₀.run = strIso
      (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1))
    (hcalls : ∀ J ∈ T₀.calls, MasterCallLetters (2 * W.1.length + 1) J ∧
      5 * J.windowSize ≤ 4 * W.1.length) :
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
      T.run = (decWinSI n W).answer ∧ T.calls.length = T₀.calls.length := by
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hgs := hW.2.2.1
  have hnd := hW.1
  have hlt := hW.2.1
  have hgrp := masterLine4b_group (p := (W, h)) hgs hnd hlt hinv
  have hgrp' : decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 =
      (winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :=
    (masterL57Ctx_group' W h).trans hgrp
  have hN : W.1.length ≤ W.2.2.2.1.length := by
    rw [hx.1]; exact length_le_of_nodup_lt hnd hlt
  have hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * W.1.length + 1) J :=
    fun J hJ => (hcalls J hJ).1
  have hK' : ∀ J ∈ T₀.calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [← hgrp']
    exact hK
  have hR' : T₀.run ⊆ ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
      Set (Perm (Fin W.1.length))) := by
    rw [hrun, ← hgrp']
    exact fun _ h => h.1
  have hcalls' := masterL57Unl_lifted_calls (p := (W, h)) hx hy hnd hlt hinv hlet
    (fun J hJ => (hcos J hJ).of_K_subset (hK' J hJ))
  have hKU : ∀ J ∈ (masterL57Unl (W, some h) T₀).calls, J.K ⊆
      ((winRestrictHom n W.1 hnd hlt (decGroup n W.2.1) hinv).range :
        Set (Perm (Fin W.1.length))) := by
    rw [masterL57Unl_calls (P := (W, some h)) hN hlet]
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact hK' J₀ hJ₀
  have hsmallT : ∀ J ∈ (top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
      (masterL57Unl (W, some h) T₀)).calls, 5 * J.windowSize ≤ 4 * W.1.length := by
    intro J hJ
    obtain ⟨-, -, K, hKm, hw⟩ := hcalls' J hJ
    rw [hw]
    exact (hcalls K hKm).2
  have hL : ∀ J ∈ (top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
      (masterL57Unl (W, some h) T₀)).calls,
      MasterCallLetters (2 * n + 1) J ∧ J.windowSize < W.1.length ∧
        ∃ G₀ : Subgroup (Perm (Fin n)), IsCosetInstance G₀ J := by
    intro J hJ
    obtain ⟨hl, hc, -⟩ := hcalls' J hJ
    have := hsmallT J hJ
    exact ⟨hl, by omega, _, hc⟩
  have hg : masterL57Guard (W, some h) = true := masterL57Guard_of_good hgd
  have hM := masterNode_line57_match (a := a) (b := b) (B := masterLine1B)
    (C₀ := masterLine1C₀) (cameron := cameron) (u := u) (v := v)
    (G4 := masterLine4cdOps c tt dd GD dD) (d4 := (dD, default)) (p := (W, h))
    (gens := W.2.1.map (decPerm n)) hE hr hg hx.1 (map_encPerm_decPerm hgs).symm hnd hlt hinv
    hm hlet hK' hR' hL
  refine ⟨(top4wTree W.1 hnd hlt (decGroup n W.2.1) hinv (decStrN n W.2.2.2.1)
    (masterL57Unl (W, some h) T₀)).bind (fun A => .done (decPerm n W.2.2.1 • A)), ?_, ?_, ?_⟩
  · refine loopMatchG_of_loopMatch_onCalls (fun K => 5 * K.windowSize ≤ 4 * W.1.length) ?_ hM ?_
    · intro j s J hJ hV
      obtain ⟨-, hFc, -, hdeg, -, hinvJ⟩ := masterGuardedChild_some hJ
      rw [masterNodeFull_child_hint (by simp)] at hFc
      simp only [masterHintL57Ops, masterHintOps, MasterOps.pairIte,
        masterRouteAt_false (p := (W, h)) (k := 1) (by omega),
        masterRouteAt_false (p := (W, h)) (k := 2) (by omega),
        masterRouteAt_false (p := (W, h)) (k := 3) (by omega),
        masterRouteAt_false (p := (W, h)) (k := 4) (by omega), Bool.false_eq_true, if_false,
        masterL57Ops, masterShiftOps, masterWinLiftOps] at hFc
      rw [if_pos hg] at hFc
      obtain ⟨J', -, hJ'⟩ := Option.bind_eq_some_iff.mp hFc
      obtain ⟨V, -, rfl⟩ := Option.map_eq_some_iff.mp hJ'
      have hJW := aggnCheckedWindow_wf W.2.2.2.1 V
      rw [hx.1] at hJW
      have hJ : MasterRawNode n (masterCheckedCall (W.2.2.2.1, V)) :=
        ⟨hdeg.trans hx.1, hJW, (rawIsInvariant_eq_true_iff hJW.2.2.1 hJW.2.1).mp hinvJ⟩
      refine ⟨⟨hJ, fun h' hh' => by cases hh'⟩, masterStepProgress_hint_of_window (by omega) ?_⟩
      rw [masterWindowSize_eq_of_rawNode hJ]
      exact hV
    · intro K hK
      simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hK
      exact hsmallT K hK
  · have hix : decStrN W.1.length (masterHintTop (W, h)).2.1 =
        fun i => decStrN n W.2.2.2.1 (winEquiv n W.1 hnd hlt i) :=
      topwRestrictStr_decode hnd hlt _
    have hiy : decStrN W.1.length (masterHintTop (W, h)).2.2 =
        fun i => strAct (decStrN n W.2.2.2.2) (decPerm n W.2.2.1)⁻¹ (winEquiv n W.1 hnd hlt i) :=
      top4aTarget_restrict hx.1 hnd hlt _ _
    rw [SIReduction.run_bind, SIReduction.run_done, top4wTree_run hnd hlt hinv _ _ hKU,
      masterL57Unl_run (P := (W, some h)) hN hlet, hrun, masterL57Ctx_strIso', hgrp', hix, hiy,
      topwPreimage_strIso hnd hlt hinv]
    change _ = wIso (winSet n W.1) (decCoset n (some (W.2.1, W.2.2.1))) _ _
    rw [decCoset_some, wIso_smul]
    rfl
  · simp only [top4wTree, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
    rw [calls_topwReduction hnd hlt hinv _ _ hKU, List.length_map,
      masterL57Unl_calls (P := (W, some h)) hN hlet, List.length_map]

include hW hinv in
/-- **Section 15, lines 5–7 without a hint, in the full node carrier, with its children.**
The round of a `Babai.Line57Data` without a hint (a reject exit, or Procedure Align without a
dominant color class), on the node's context, meets the hypotheses of
`Algo.masterNodeFull_hint_line57_matchGood`: its calls are coset instances in `G_Δ`
(`calls_coset`) with the letters of the context's strings, which are at most `2|Δ|`, and with
at most `4/5` of the window (Eq. (72), `Algo.line57Data_calls_small`), and it returns
`Iso_{G_Δ}` of the context's strings (`run_red`); so the node carrier walks its lift in at most
`cost` calls. -/
theorem masterNodeFull_hint_line57Data_matchGood {a b : ℕ}
    (hE : MasterL57EOK c' b' t d dc dp e f E) (hr : masterHintRoute (W, h) = 5)
    (hgd : MasterHintGood (W, h)) (hΔ : 0 < W.1.length)
    {m : ℕ} {ϕ : decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 →* Perm (Fin m)}
    {ts par cost : ℕ}
    (D : Line57Data (Fin W.1.length) ℕ (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2)
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
      (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1) ϕ ts par cost)
    (hno : line57NoDom D.shape)
    (hm : LoopMatch (masterL57Round c' b' t d dc dp e f) (aggnPhaseDecode W.1.length)
      (decCoset W.1.length) (masterL57Enter (W, some h))
      ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (W, some h))) 0
      ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (W, some h)))
      (D.shape.red D.enum)) :
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
      T.run = (decWinSI n W).answer ∧ T.calls.length ≤ cost := by
  obtain ⟨T, hT, hrun, hlen⟩ := masterNodeFull_hint_line57_matchGood (cameron := cameron)
    (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD) (a := a) (b := b)
    hW hinv hE hr hgd hΔ (D.shape.red D.enum) hm D.calls_K D.calls_coset D.run_red
    (line57Data_calls_small D hno (masterL57Ctx_letters_x (W, some h))
      (masterL57Ctx_letters_y (W, some h)))
  exact ⟨T, hT, hrun, hlen ▸ D.calls_length⟩

end Node

/-- **What the Section 13 track supplies at a node of route 5**: the round of lines 5–7
walks, from the node's lines-5–7 node, a tree `T₀` on the window with the hypotheses of
`Algo.masterNodeFull_hint_line57_matchGood`, stated on the node's context
(`Algo.masterL57Ctx`: the group `G_Δ`, and the two strings on the window with their letters
renamed), in at most `q45 |Δ|` calls. (The node of lines 5–7 is well formed at every good node,
`Algo.masterL57Guard_of_good`.) -/
def MasterL57Supply (c' b' t d dc dp e f n : ℕ) (q45 : ℕ → ℕ) : Prop :=
  ∀ (W : RawWinSI) (h : RawMasterHint), MasterNodeGood n (W, some h) →
    masterHintRoute (W, h) = 5 →
    ∃ T₀ : SIReduction (Fin W.1.length) ℕ (Set (Perm (Fin W.1.length))),
      LoopMatch (masterL57Round c' b' t d dc dp e f) (aggnPhaseDecode W.1.length)
        (decCoset W.1.length) (masterL57Enter (W, some h))
        ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (W, some h))) 0
        ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (W, some h))) T₀ ∧
      (∀ J ∈ T₀.calls, J.K ⊆
        (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))) ∧
      (∀ J ∈ T₀.calls,
        IsCosetInstance (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2) J) ∧
      T₀.run = strIso
        (decGroup W.1.length (masterL57Ctx (W, some h)).1.1.2 : Set (Perm (Fin W.1.length)))
        (decStrN W.1.length (masterL57Ctx (W, some h)).2.1)
        (decStrN W.1.length (masterL57Ctx (W, some h)).2.2.1) ∧
      (∀ J ∈ T₀.calls, MasterCallLetters (2 * W.1.length + 1) J ∧
        5 * J.windowSize ≤ 4 * W.1.length) ∧
      T₀.calls.length ≤ q45 W.1.length

/-- **The obligation of route 5 from the supply of Section 13.** -/
theorem masterParamRoute5_of_supply {a b n : ℕ} {q45 : ℕ → ℕ}
    (hE : MasterL57EOK c' b' t d dc dp e f E) (hS : MasterL57Supply c' b' t d dc dp e f n q45) :
    MasterParamRoute (masterAdmittedRound a b
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd GD dD
        c' b' t d dc dp E)) n q45 5 := by
  intro W h hG _ hr
  obtain ⟨⟨-, hW, hinv⟩, hgood⟩ := id hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h64⟩ := hgood h rfl
  have h64' : 64 ≤ W.1.length := h64
  obtain ⟨T₀, hm, hK, hcos, hrun, hcalls, hlen⟩ := hS W h hG hr
  obtain ⟨T, hT, hTrun, hTlen⟩ := masterNodeFull_hint_line57_matchGood (cameron := cameron)
    (u := u) (v := v) (c := c) (tt := tt) (dd := dd) (GD := GD) (dD := dD) (a := a) (b := b)
    hW hinv hE hr (hgood h rfl) (lt_of_lt_of_le (by norm_num) h64') T₀ hm hK hcos hrun hcalls
  refine ⟨T, hT, hTrun, ?_, fun hch => absurd hch not_masterChainRuleNode_hint⟩
  change T.calls.length ≤ q45 W.1.length
  rw [hTlen]
  exact hlen

end Full

end Algo
