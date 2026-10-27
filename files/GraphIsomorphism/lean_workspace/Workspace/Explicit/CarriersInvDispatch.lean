/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the node carrier of the Master
(Sec. 15) bounded at the degree under a state invariant, with route 5 as a parameter. Not part
of the faithful formalization.
-/
import Workspace.Explicit.CarriersInv

/-!
# The dispatcher under a state invariant

The version of `Explicit.carrierTN_dispatch` and `Explicit.stateBoundsXR_dispatch` in the
interface of `Explicit.CarriersInv`: the carrier of route 5 comes with its own invariant `J5`.

* The widths of the carriers of routes 0–4, bounded at the degree with exponent 5
  (`Explicit.tn_width_route0` … `Explicit.tn_width_route4`): they are polynomial, except the
  descent (its lists, `Explicit.tn_masterDescLists_sel`) and route 4 (the header of line 4d).
* `Explicit.dispatchJ`: the invariant of the dispatcher, `Explicit.ReachJ` at routes 0–4 and
  `J5` at route 5, side by side (`Explicit.pairJ`).
* `Explicit.carrierTNJ_dispatch`, `Explicit.stateInvXR_dispatch`, and the same for
  `Explicit.masterOpsE`: `Explicit.carrierTNJ_masterOpsE`, `Explicit.stateInvXR_masterOpsE`.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ## Widths -/

section Widths

variable (a b : ℕ) (R : RawMasterSI → Prop)

theorem tn_width_leaf (f : RawWinSI → RawCoset) :
    TN (masterLeafOps f).width (CarrierPre a b R) 5 :=
  (TN.const' 0 _ 5).of_eq (fun _ => rfl)

theorem tn_width_chainLift : TN masterChainLiftOps.width (CarrierPre a b R) 5 := by
  have hW : PolyFun (fun p : RawMasterSI => p.1) := polyFun_fst
  exact (TN.ofPoly ((((hW.comp polyFun_snd).comp polyFun_fst).pair (hW.comp polyFun_fst)).comp
    (polyFun_winOrbits.comp polyFun_length)) _ 5).of_eq (fun _ => rfl)

theorem tn_width_desc {sel : RawMasterSI → MasterDescInput} (hsel : PolyFun sel) :
    TN (masterShiftOps (masterDescOpenOps 3 sel)).width (CarrierPre a b R) 5 :=
  (((tn_masterDescLists_sel a b hsel).comp_poly polyFun_masterDescFoldWidth).of_eq
    (fun _ => rfl)).restrict (fun _ _ h => ⟨h.1, h.2.1⟩)

theorem tn_width_camPrepared {g : RawMasterSI → RawCameron × MasterDescInput}
    (hg : PolyFun g) : TN (masterCamPreparedOps g).width (CarrierPre a b R) 5 :=
  (TN.ofPoly (masterCamSelect_polyFun (fun p => masterCamPrepared (g p))
    (hg.comp polyFun_masterCamPrepared)).1 _ 5).of_eq (fun _ => rfl)

theorem tn_width_route0 (B C₀ : ℕ) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) : TN (masterLine1Ops B C₀ cam).width (CarrierPre a b R) 5 := by
  have h : ∀ k, PolyFun (masterRouteIs B C₀ k) := fun k => polyFun_masterRouteIs B C₀ k
  have w3 := TN.ite (Pre := CarrierPre a b R) (h 3)
    (tn_width_desc a b R polyFun_masterBlockSelect)
    (tn_width_camPrepared a b R (polyFun_masterCamRouteInput hc))
    (fun _ _ h _ => h) (fun _ _ h _ => h)
  have w2 := TN.ite (Pre := CarrierPre a b R) (h 2) (tn_width_chainLift a b R) w3
    (fun _ _ h _ => h) (fun _ _ h _ => h)
  have w1 := TN.ite (Pre := CarrierPre a b R) (h 1) (tn_width_leaf a b R (masterWindowBruteLeaf C₀))
    w2 (fun _ _ h _ => h) (fun _ _ h _ => h)
  exact (TN.ite (Pre := CarrierPre a b R) (h 0) (tn_width_leaf a b R masterWindowTrivialLeaf) w1
    (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq (fun _ => rfl)

theorem tn_width_route3 (e f u v : ℕ) : TN (master4bOps e f u v).width (CarrierPre a b R) 5 :=
  (TN.ofPoly (PolyFun.ite (polyFun_snd.comp polyFun_optionIsSome)
    (polyFun_masterHintGet.comp polyFun_master4OpenWidth) (polyFun_const 0)) _ 5).of_eq
    (fun _ => rfl)

theorem tn_width_route4 (tt dd : ℕ) (ht : tt + 2 ≤ 5) (dD : ADState)
    (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint) :
    TN (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD).width
      (CarrierPre a b R4) 5 := by
  have h1 : TN (fun P => l57Calls (line4dDomHdr 0 tt dd (line4dHint P))) (CarrierPre a b R4) 5 :=
    (tn_domHdrAt tt dd ht a b).comp (TN.l57Calls.mono_k (by norm_num))
      (fun _ _ h => (r4Good_of h).2.2)
  have h2 : TN (fun P => avCalls (line4dHdr 0 tt dd (line4dHint P))) (CarrierPre a b R4) 5 :=
    (tn_hdrAt tt dd ht a b).comp_poly polyFun_avCalls
  exact (TN.iteT (tn_masterHasDom tt dd ht a b) h1 h2).of_eq (fun _ => rfl)

end Widths

/-! ## The routes of the dispatcher -/

section Routes

variable (a b : ℕ)

theorem carrierTNJ_route0 (B C₀ : ℕ) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) (J : StInv AggnRecomputeState) :
    CarrierTNJ a b (masterLine1Ops B C₀ cam) (fun P => masterRoute P = 0) J :=
  (carrierTN_route0 a b B C₀ hc).toJ (tn_width_route0 a b _ B C₀ hc) J

theorem carrierTNJ_route1 (J : StInv AggnRecomputeState) :
    CarrierTNJ a b (masterDescPreparedOps 3) (fun P => masterRoute P = 1) J :=
  (carrierTN_route1 a b).toJ (tn_width_desc a b _ polyFun_masterDescPreparedSelect) J

theorem carrierTNJ_route2 (J : StInv AggnRecomputeState) :
    CarrierTNJ a b (masterLeafOps primitiveWindowLeaf) (fun P => masterRoute P = 2) J :=
  (carrierTN_route2 a b).toJ (tn_width_leaf a b _ _) J

theorem carrierTNJ_route3 (e f u v : ℕ) (J : StInv Top4State) :
    CarrierTNJ a b (master4bOps e f u v) (fun P => masterRoute P = 3) J :=
  (carrierTN_route3 (a := a) (b := b) (e := e) (f := f) (u := u) (v := v)).toJ
    (tn_width_route3 a b _ e f u v) J

theorem carrierTNJ_route4 (tt dd : ℕ) (ht : tt + 2 ≤ 5) (dD : ADState)
    {H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint}
    (hH4 : TN H4 (fun n w => CarrierPre a b R4 n w.1.1) 5)
    (J : StInv (ADState × AggnRecomputeState)) :
    CarrierTNJ a b (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD) R4 J :=
  (CarrierTN.pairIte (tn_masterHasDom tt dd ht a b)
    ((carrierTN_line4dDom tt dd ht a b).withHint hH4) (carrierTN_line4d tt dd ht a b)).toJ
    (tn_width_route4 a b tt dd ht dD H4) J

end Routes

/-! ## The dispatcher -/

/-- **The invariant of the dispatcher**: the states one step from `init` at routes 0–4, and
`J5` at route 5, side by side as in `Explicit.dispatchOps`. -/
def dispatchJ {T5 : Type} [Enc T5] (a b B C₀ : ℕ) (cam : RawGens × List ℕ → Option RawCameron)
    (e f u v tt dd : ℕ) (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint)
    (dD : ADState) (d5 : T5) (J5 : StInv T5) :=
  pairJ masterIsLine1 (masterCamFoldEmbed none)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, (default : Top4State),
      ((dD, (default : AggnRecomputeState)), d5))
    (ReachJ a b (masterLine1Ops B C₀ cam))
    (pairJ (masterRouteAt 1) (masterCamFoldEmbed none)
      (masterCamFoldEmbed none, (default : Top4State), ((dD, (default : AggnRecomputeState)), d5))
      (ReachJ a b (masterDescPreparedOps 3))
      (pairJ (masterRouteAt 2) (masterCamFoldEmbed none)
        ((default : Top4State), ((dD, (default : AggnRecomputeState)), d5))
        (ReachJ a b (masterLeafOps primitiveWindowLeaf))
        (pairJ (masterRouteAt 3) (default : Top4State) ((dD, (default : AggnRecomputeState)), d5)
          (ReachJ a b (master4bOps e f u v))
          (pairJ (masterRouteAt 4) (dD, (default : AggnRecomputeState)) d5
            (ReachJ a b (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD))
            J5))))

section Dispatch

variable (a b : ℕ) {cam : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cam)
  (B C₀ e f u v tt dd : ℕ) (ht : tt + 2 ≤ 5) (dD : ADState)
  {H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint}
  (hH4 : TN H4 (fun n w => CarrierPre a b R4 n w.1.1) 5)
  {T5 : Type} [Enc T5] {G5 : MasterOps T5} {R5 : RawMasterSI → Prop} {J5 : StInv T5} (d5 : T5)

include hc ht hH4 in
/-- **The node carrier of the Master bounded at the degree with exponent 5, under its state
invariant**, with route 5 as a parameter, at the nodes whose routes 4 and 5 are good. -/
theorem carrierTNJ_dispatch (h5 : CarrierTNJ a b G5 R5 J5) :
    CarrierTNJ a b (dispatchOps B C₀ cam e f u v tt dd H4 dD G5 d5) (RouteGood R5)
      (dispatchJ a b B C₀ cam e f u v tt dd H4 dD d5 J5) := by
  have l4 := CarrierTNJ.pairIteR (R := RAbove R5 4) (dS := (dD, default)) (dT := d5)
    (polyFun_masterRouteAt 4)
    (carrierTNJ_route4 a b tt dd ht dD hH4
      (ReachJ a b (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD))) h5
    (fun P h hs => h.1.1 (routeAt_true hs))
    (fun P h hs => rAbove_five h hs)
  have l3 := CarrierTNJ.pairIteR (R := RAbove R5 3) (dS := default) (dT := ((dD, default), d5))
    (polyFun_masterRouteAt 3) (carrierTNJ_route3 a b e f u v (ReachJ a b (master4bOps e f u v))) l4
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  have l2 := CarrierTNJ.pairIteR (R := RAbove R5 2) (dS := masterCamFoldEmbed none)
    (dT := (default, (dD, default), d5))
    (polyFun_masterRouteAt 2)
    (carrierTNJ_route2 a b (ReachJ a b (masterLeafOps primitiveWindowLeaf))) l3
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  have l1 := CarrierTNJ.pairIteR (R := RAbove R5 1) (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, default, (dD, default), d5))
    (polyFun_masterRouteAt 1) (carrierTNJ_route1 a b (ReachJ a b (masterDescPreparedOps 3))) l2
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  exact CarrierTNJ.pairIteR polyFun_masterIsLine1 
    (carrierTNJ_route0 a b B C₀ hc (ReachJ a b (masterLine1Ops B C₀ cam))) l1
    (fun P _ hs => of_decide_eq_true hs)
    (fun P h hs => rAbove_one h hs)

include hc ht in
/-- **The fold states of the Master's node carrier under its state invariant, with an explicit
exponent**, with route 5 as a parameter, at the nodes whose routes 4 and 5 are good. -/
theorem stateInvXR_dispatch {K5 : ℕ} (s5 : StateInvXR a b K5 G5 R5 J5) :
    ∃ K, StateInvXR a b K (dispatchOps B C₀ cam e f u v tt dd H4 dD G5 d5) (RouteGood R5)
      (dispatchJ a b B C₀ cam e f u v tt dd H4 dD d5 J5) := by
  obtain ⟨K4, s4⟩ := stateBoundsXR_route4 tt dd ht a b dD
  obtain ⟨K0, s0⟩ := stateBoundsX_route0 a b B C₀ hc
  obtain ⟨K1, s1⟩ := stateBoundsX_route1 a b
  obtain ⟨K2, s2⟩ := stateBoundsX_route2 a b
  obtain ⟨K3, s3⟩ := stateBoundsX_route3 (a := a) (b := b) (e := e) (f := f) (u := u) (v := v)
  have s4' : StateBoundsXR a b K4
      (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD) R4 := s4
  have l4 := StateInvXR.pairIteR (R := RAbove R5 4) (masterRouteAt 4) (dD, default) d5
    s4'.toInv s5
    (fun P h hs => h.1.1 (routeAt_true hs))
    (fun P h hs => rAbove_five h hs)
  have l3 := StateInvXR.pairIteR (R := RAbove R5 3) (masterRouteAt 3) default
    ((dD, default), d5) (s3.toR (fun _ => True)).toInv l4
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  have l2 := StateInvXR.pairIteR (R := RAbove R5 2) (masterRouteAt 2)
    (masterCamFoldEmbed none) (default, (dD, default), d5) (s2.toR (fun _ => True)).toInv l3
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  have l1 := StateInvXR.pairIteR (R := RAbove R5 1) (masterRouteAt 1)
    (masterCamFoldEmbed none) (masterCamFoldEmbed none, default, (dD, default), d5)
    (s1.toR (fun _ => True)).toInv l2
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  exact ⟨_, StateInvXR.pairIteR masterIsLine1 (masterCamFoldEmbed none)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), d5)
    (s0.toR (fun _ => True)).toInv l1
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_one h hs)⟩

end Dispatch

/-! ## The variant Master -/

/-- The carrier of route 5 in `Explicit.masterOpsE` (lines 5–7 with the hint routine). -/
noncomputable abbrev route5OpsE (p : Params) : MasterOps AggnL57GState :=
  (masterL57Ops 2 0 p.t p.d p.dc p.dp p.e p.f p.E).withHint (hint5E p)

/-- The invariant of `Explicit.masterOpsE`, with `J5` at route 5. -/
noncomputable abbrev dispatchJE (p : Params) (cam : RawGens × List ℕ → Option RawCameron)
    (J5 : StInv AggnL57GState) :=
  dispatchJ p.a p.b p.B p.C₀ cam p.e p.f p.u p.v p.tt p.dd (line4dDomHint 0 p.tt p.dd) default
    default J5

/-- **The node carrier of `Explicit.masterOpsE`, bounded at the degree with exponent 5 under
its state invariant**, given `p.tt ≤ 3` and the bounds of route 5. -/
theorem carrierTNJ_masterOpsE (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop} {J5 : StInv AggnL57GState}
    (h5 : CarrierTNJ p.a p.b (route5OpsE p) R5 J5) :
    CarrierTNJ p.a p.b (masterOpsE p cam) (RouteGood R5) (dispatchJE p cam J5) :=
  carrierTNJ_dispatch p.a p.b hc p.B p.C₀ p.e p.f p.u p.v p.tt p.dd ht default
    (tn_line4dDomHint p.tt p.dd ht p.a p.b) default h5

/-- **The fold states of `Explicit.masterOpsE` under its state invariant, with an explicit
exponent**, given `p.tt ≤ 3` and the state bounds of route 5. -/
theorem stateInvXR_masterOpsE (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop} {J5 : StInv AggnL57GState}
    {K5 : ℕ} (s5 : StateInvXR p.a p.b K5 (route5OpsE p) R5 J5) :
    ∃ K, StateInvXR p.a p.b K (masterOpsE p cam) (RouteGood R5) (dispatchJE p cam J5) :=
  stateInvXR_dispatch p.a p.b hc p.B p.C₀ p.e p.f p.u p.v p.tt p.dd ht default default s5

end Explicit
