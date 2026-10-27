/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the calls bounds of
`Explicit.StepBounds` at explicit line-1 thresholds. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeCalls5
import Workspace.Explicit.Line1.Top

/-!
# The calls bounds at explicit line-1 thresholds

`Explicit.exists_calls_bounds` asks `Explicit.ParamsOK p`, whose line-1 thresholds are those of
`Algo.theorem_1_1_1`; only its route-5 part uses them (the count of the tree of lines 5–7 is
matched against the fold of the round at those thresholds). Here the same bounds at
`Explicit.ParamsOKX p`:

* `Explicit.exists_calls_route5_leX`: route 5, with the match carried from `paramsL1 p` to `p`;
* `Explicit.exists_calls_boundsX`: all routes, as `exists_calls_bounds`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv

variable {cam : RawGens × List ℕ → Option RawCameron}

set_option maxHeartbeats 4000000 in
/-- **The calls of the run at a good node of route 5, at explicit line-1 thresholds**: the
port of `Explicit.exists_calls_route5_le` to `Explicit.ParamsOKX`. The tree of lines 5–7 is the
same; the match of the node's fold, found at the thresholds of `paramsL1 p`, is carried to
`p` (`Explicit.loopMatchG_hint_transport`, the node has a hint), and the calls are read off
the recursion `Explicit.masterRecEX` at `p`. Original docstring: at most
`2^{A (log₂ n+2)^3}`, from the tree the round of lines 5–7 walks (`Algo.exists_l57Tree`, through
`Algo.masterL57SupplyH_masterL57Hint`) and its count `Explicit.l57Tree_calls_le`: the two
phases of AggregateCertificates (`2^{O(log² n)}`), the versions of Theorem 9.2.3 times the
windows or cosets of stretch 3 (`2^{O(log³ n)}`), and the polynomial width of the giant branch. -/
theorem exists_calls_route5_leX {p : Params} (ok : ParamsOKX p) (he : SbipExact p.t p.d)
    (hc : PolyFun cam) (hs : CameronSpec cam) :
    ∃ A, ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 →
      masterRoute P = 5 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (A * lg n ^ 3) := by
  obtain ⟨B, C₀, a, b, e, f', u, v, u', v', tt, dd, t, d, dc, dp, E⟩ := p
  obtain ⟨-, htopwp, htop4w, ⟨hu', hv'⟩, hcap, hl4c, hentry, hbip, hphases, hreserve⟩ :=
    id ok.rest
  dsimp only [paramsL1] at hu' hv' htopwp htop4w hcap hl4c hentry hbip hphases hreserve he ⊢
  subst hu' hv'
  obtain ⟨q, hq, hT⟩ := exists_treesX ok hc hs
  obtain ⟨Y, hY⟩ := exists_size_le_of_wf a b
  obtain ⟨S, hSp, hSm, hSs⟩ := polyFun_masterL57Ctx.size.exists_polyBound
  obtain ⟨K, hKp, hKm, hKs⟩ := aggnL57GW_bdd 2 0 t d dc dp (l57UV e f').1 (l57UV e f').2 e f'
  obtain ⟨c₀, d₀, hc₀⟩ := hKp.comp hSp
  obtain ⟨Wc, -, -, hcw⟩ := aggnChecked_width_bound 2
  obtain ⟨Wp, -, -, hpw⟩ := aggnCompareChecked_width_bound 2
  refine ⟨62 + (c₀ + d₀ * (Y + 1)), fun n P f hG hWF hf hr => ?_⟩
  obtain ⟨W, o⟩ := P
  cases o with
  | none => simp [masterRoute] at hr
  | some h =>
  have hr' : masterHintRoute (W, h) = 5 := hr
  obtain ⟨⟨hdeg, hWW, hinv⟩, hgoodAll⟩ := id hG
  have hgood : MasterHintGood (W, h) := hgoodAll h rfl
  -- the tree of lines 5–7 and the tree of the node
  obtain ⟨T₀, hm, hK, hcos, hrun, hlet, -⟩ := masterL57SupplyH_masterL57Hint (E := E) hphases
    htopwp hentry hbip le_rfl hreserve hcw hpw n W h hG hr'
  have hmatch0 : ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam)
        (fun J => MasterNodeGood n J ∧ MasterStepProgress (W, some h) J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h)
        ((masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam).width (W, some h)) 0
        ((masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f', u, v,
          (l57UV e f').1, (l57UV e f').2, tt, dd, t, d, dc, dp, E⟩ cam).init (W, some h)) T ∧
      T.run = (decWinSI n W).answer ∧ T.calls.length = T₀.calls.length :=
    masterNodeH_hint_line57_matchGood hWW hinv (hcap n) hreserve hr' hgood T₀ hm hK hcos hrun
      hlet
  obtain ⟨T, hmT0, -, hlenT⟩ := hmatch0
  have hI2 : ((W, some h) : RawMasterSI).2 ≠ none := by simp
  have hnc : ¬ MasterChainRuleNode ((W, some h) : RawMasterSI) := fun hch => hI2 hch.1
  have hncX : ¬ MasterChainRuleNodeX B C₀ ((W, some h) : RawMasterSI) := fun hch => hI2 hch.1
  set R := (masterRoundE ⟨B, C₀, a, b, e, f', u, v, (l57UV e f').1, (l57UV e f').2, tt, dd, t, d,
    dc, dp, E⟩ cam) with hRdef
  have hmT : LoopMatchG R (fun J => MasterNodeGood n J ∧ MasterStepProgressX B C₀ (W, some h) J)
      (fun J => decWinSI n J.1) (fun _ => decCoset n) (W, some h) (R.width (W, some h)) 0
      (R.init (W, some h)) T := by
    refine loopMatchG_hint_transport hI2 ?_ hmT0
    rintro J ⟨hJ, hpr⟩
    exact ⟨hJ, fun hch => absurd hch hncX, fun _ => hpr.2 hnc⟩
  obtain ⟨-, h2, -⟩ := R.loopAux_eqG
    (rec := R.value f)
    (C := fun J => MasterNodeGood n J ∧ MasterStepProgressX B C₀ (W, some h) J)
    (Good := fun J => (masterRecEX hq n (hT n)).Good J ∧ R.WF J ∧
      R.measure J < R.measure (W, some h))
    (fun j s J hc hC => ⟨hC.1, R.child_wf _ j s J hWF hc, R.child_measure _ j s J hWF hc⟩)
    (fun J hJ => roundValue_eqG R (masterRecEX hq n (hT n)).impl
      (masterRecEX hq n (hT n)).progress.good_child (masterRecEX hq n (hT n)).correct f J
      hJ.1 hJ.2.1 (lt_of_lt_of_le hJ.2.2 (Nat.lt_succ_iff.mp hf)))
    _ _ _ _ hmT
  have hlen : (R.roundCalls f (W, some h)).length = T₀.calls.length := by
    rw [← hlenT, ← h2, List.length_map]
    rfl
  rw [hlen]
  -- Layer A on the context
  obtain ⟨m, ϕ, -, -, hA, hGt, hϕ, -, -, -, -, hmn, h64⟩ := masterL57Ctx_hintFacts hgood
  have hmh : h.1.1.length = m := by
    have e := hA.2.1
    change (List.range h.1.1.length).length = m at e
    rwa [List.length_range] at e
  have hell : ellOf W.1.length < m := by
    rw [← hmh]
    exact ((masterHintRoute_aggregate (W, h)).1 hr').1
  obtain ⟨inst, hcat⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  have hts : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length = testSetSize W.1.length := by
    change (List.range (min (10 + Nat.log 2 W.1.length) W.1.length)).length = _
    rw [List.length_range]
    exact min_eq_left (testSetSize_le_self h64)
  have hS := l57Setting_of_normal (b := 0) (t := t) (d := d) (e := e) (f := f') hphases htopwp
    hentry hbip le_rfl (masterL57Ctx_normal hgood) hA (masterL57Ctx_strWF_x _)
    (masterL57Ctx_strWF_y _) hts hGt hϕ hmn h64 hell hcat
  have hans : ∀ K ∈ T₀.calls, ∃ a : RawCoset, decCoset W.1.length a = K.answer :=
    fun K hK => exists_rawCoset_answer (hcos K hK)
  set X := (m ^ 5 * famBound 2 m + famBound (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length m + 1) * l4Factor W.1.length +
    K (S (Enc.size ((W, some h) : RawMasterSI))) with hX
  have hcount := l57Tree_calls_le hS hm hans X (fun sR hpost =>
    ⟨(l57Calls_post_le hS he hpost).trans (Nat.le_add_right _ _),
      ((hKs (masterL57Ctx ((W, some h) : RawMasterSI)) sR).trans (hKm (hSs _))).trans (Nat.le_add_left _ _)⟩)
  refine hcount.trans ?_
  -- the arithmetic
  have hNn : W.1.length ≤ n := by
    exact length_le_of_nodup_lt hWW.1 hWW.2.1
  have hLN : lg W.1.length ≤ lg n := lg_mono hNn
  have hL2 : 2 ≤ lg n := two_le_lg n
  have hL3 : 1 ≤ lg n ^ 3 := one_le_lg_pow n 3
  have hk5 : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length ≤ 5 * lg W.1.length := by
    rw [hts]; unfold testSetSize lg; omega
  have hkN : (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length ≤ W.1.length := by rw [hts]; exact testSetSize_le_self h64
  have i1 : aggnAggregateWidth 2 (masterL57Ctx ((W, some h) : RawMasterSI)) ≤ 2 ^ (20 * lg n ^ 3) := by
    refine (aggnAggregateWidth_le_arith (masterL57Ctx ((W, some h) : RawMasterSI)) (succ_le_two_pow_lg W.1.length) hmn hkN hk5 (two_le_lg W.1.length)
      (masterL57Ctx_length _) hA.2.1 rfl).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    exact Nat.mul_le_mul_left _ (lg_pow_mono hNn (by norm_num))
  have i2 : m ^ 5 ≤ 2 ^ (5 * lg n ^ 3) := pow_le_two_pow_lg_cube (hmn.trans hNn) 5
  have i3 : famBound 2 m ≤ 2 ^ (48 * lg n ^ 3) :=
    famBound_le (K := 1) (hmn.trans hNn) (by omega)
  have i4 : famBound (masterL57Ctx ((W, some h) : RawMasterSI)).2.2.2.length m ≤ 2 ^ (52 * lg n ^ 3) :=
    famBound_le (K := 5) (hmn.trans hNn) (hk5.trans (Nat.mul_le_mul_left _ hLN))
  have i5 : l4Factor W.1.length ≤ 2 ^ (5 * lg n ^ 3) :=
    (l4Factor_le W.1.length).trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (lg_pow_mono hNn le_rfl)))
  have i6 : K (S (Enc.size ((W, some h) : RawMasterSI))) ≤
      2 ^ ((c₀ + d₀ * (Y + 1)) * lg n ^ 3) := by
    have hsz : Enc.size ((W, some h) : RawMasterSI) ≤ 2 ^ (Y * lg n) := by
      have := hY _ hWF
      rwa [show masterDegree ((W, some h) : RawMasterSI) = n from hdeg] at this
    refine ((hc₀ _).trans (poly_comp_two_pow_lg hsz c₀ d₀)).trans ?_
    have h13 : lg n ≤ lg n ^ 3 := by
      calc lg n = lg n ^ 1 := (pow_one _).symm
        _ ≤ lg n ^ 3 := lg_pow_le_lg_pow (by norm_num) n
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h13)
  exact route5_arith hL3 i1 i2 i3 i4 i5 i6



/-- **The calls of the run at a good node, every route, at explicit line-1 thresholds**: the
port of `Explicit.exists_calls_bounds` to `Explicit.ParamsOKX` (route 5 through
`Explicit.exists_calls_route5_leX`; the other routes never used the thresholds). -/
theorem exists_calls_boundsX {p : Params} (ok : ParamsOKX p) (he4 : SbipExact p.tt p.dd)
    (he5 : SbipExact p.t p.d) (hc : PolyFun cam) (hs : CameronSpec cam) :
    (∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P = 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (6 * (Nat.log 2 n + 2) ^ 4)) ∧
    ∃ Ap, ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
      (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P ≠ 1 →
      ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Ap * (Nat.log 2 n + 2) ^ 3) := by
  obtain ⟨A₀, h₀⟩ := exists_widthE_low_le p cam
  obtain ⟨A₅, h₅⟩ := exists_calls_route5_leX ok he5 hc hs
  refine ⟨fun n P f hG hW _ hr => ?_, ⟨A₀ + 53 + A₅, fun n P f hG hW hf hr => ?_⟩⟩
  · have hdeg : masterDegree P = n := hG.1.1
    refine (length_roundCalls_le_width _ f P).trans ?_
    have := widthE_route1_le (cam := cam) hW hr
    rw [hdeg] at this
    exact this
  · have hdeg : masterDegree P = n := hG.1.1
    have hL3 : lg n ^ 2 ≤ lg n ^ 3 := lg_pow_le_lg_pow (by norm_num) n
    change _ ≤ 2 ^ ((A₀ + 53 + A₅) * lg n ^ 3)
    have hroute : masterRoute P = 0 ∨ masterRoute P = 2 ∨ masterRoute P = 3 ∨
        masterRoute P = 4 ∨ masterRoute P = 5 := by
      obtain ⟨W, o⟩ := P
      cases o with
      | none => exact Or.inl rfl
      | some h =>
        change masterHintRoute (W, h) ≠ 1 at hr
        change masterHintRoute (W, h) = 0 ∨ masterHintRoute (W, h) = 2 ∨
          masterHintRoute (W, h) = 3 ∨ masterHintRoute (W, h) = 4 ∨ masterHintRoute (W, h) = 5
        rcases masterHintRoute_mem (W, h) with h1 | h1 | h1 | h1 | h1 <;> omega
    rcases hroute with h4 | h4 | h4 | h4 | h4
    rotate_left 3
    · refine (length_roundCalls_le_width _ f P).trans ?_
      have := widthE_route4_le (cam := cam) he4 hG hW h4
      rw [hdeg] at this
      exact this.trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    · exact (h₅ n P f hG hW hf h4).trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ (by omega)))
    all_goals
      refine (length_roundCalls_le_width _ f P).trans ?_
      have := h₀ P hW (by omega)
      rw [hdeg] at this
      refine this.trans (Nat.pow_le_pow_right (by norm_num) ?_)
      calc A₀ * lg n ^ 2 ≤ A₀ * lg n ^ 3 := Nat.mul_le_mul_left _ hL3
        _ ≤ (A₀ + 53 + A₅) * lg n ^ 3 := Nat.mul_le_mul_right _ (by omega)

end Explicit
