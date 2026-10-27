/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the node carrier of the Master
Algorithm (Sec. 15) bounded at the degree, with the carrier of lines 5–7 as a parameter. Not
part of the faithful formalization.
-/
import Workspace.Explicit.CarriersRoute4
import Workspace.Explicit.CarriersLow
import Workspace.Explicit.Interface

/-!
# The dispatcher bounded at the degree

The node carrier `Algo.masterNodeHOps` sends a node to line 1 (route 0), line 2 (route 1),
line 4a (route 2), line 4b (route 3), lines 4c–4d (route 4) or lines 5–7 (route 5) by its route
(`Algo.masterTopOps`, `Algo.masterHintOps`). Here the carrier of route 5 is a parameter `G5`,
with its bounds at the nodes `R5` as hypotheses.

* `Explicit.RouteGood R5 P`: at route 4 the node satisfies `Explicit.R4` (a good hint), at
  route 5 it satisfies `R5`.
* `Explicit.dispatchOps`: the carrier, and `Explicit.masterNodeHOps_eq_dispatch`,
  `Explicit.masterOpsE_eq_dispatch`: `Algo.masterNodeHOps` and `Explicit.masterOpsE` are
  instances (`rfl`).
* `Explicit.carrierTN_dispatch`, `Explicit.stateBoundsXR_dispatch`: the four routines are
  bounded at the degree with exponent 5, and the fold states have size at most
  `2^{K (log₂ n + 2)^5}`, at the nodes with `RouteGood R5`.
* `Explicit.carrierTN_masterOpsE`, `Explicit.stateBoundsXR_masterOpsE`: the same for
  `Explicit.masterOpsE p cam`, given `p.tt ≤ 3` and the bounds of route 5.

Tools: `Explicit.CarrierTN.pairIteR` and `Explicit.StateBoundsXR.pairIteR`, a polynomial branch
test whose two branches need their node predicates only where they are taken.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ## A polynomial branch test with branch predicates -/

namespace CarrierTN

variable {a b : ℕ}

/-- **Two carriers side by side, with a polynomial branch test**; each carrier needs its node
predicate only at the nodes where it is taken. -/
theorem pairIteR {S T : Type} [Enc S] [Enc T] {sel : RawMasterSI → Bool} (hsel : PolyFun sel)
    {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T} {R RF RG : RawMasterSI → Prop}
    (hF : CarrierTN a b F RF) (hG : CarrierTN a b G RG)
    (hRF : ∀ P, R P → sel P = true → RF P) (hRG : ∀ P, R P → sel P = false → RG P) :
    CarrierTN a b (MasterOps.pairIte sel F G dS dT) R := by
  have hPF : ∀ n P, CarrierPre a b R n P → sel P = true → CarrierPre a b RF n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRF P h.2.2 hs⟩
  have hPG : ∀ n P, CarrierPre a b R n P → sel P = false → CarrierPre a b RG n P :=
    fun _ P h hs => ⟨h.1, h.2.1, hRG P h.2.2 hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : TN (fun z : RawMasterSI × ℕ × S × T => F.child (z.1, z.2.1, z.2.2.1))
        (fun n z => CarrierPre a b RF n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (pfst (psnd polyFun_snd))))
        hF.child).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × S × T => G.child (z.1, z.2.1, z.2.2.2))
        (fun n z => CarrierPre a b RG n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (psnd (psnd polyFun_snd))))
        hG.child).restrict (fun _ _ h => h)
    exact (TN.ite (Pre := fun n (z : RawMasterSI × ℕ × S × T) => CarrierPre a b R n z.1)
      (polyFun_fst.comp hsel) h1 h2 (fun n z h hs => hPF n z.1 h hs)
      (fun n z h hs => hPG n z.1 h hs)).of_eq (fun _ => rfl)
  · exact (TN.ite (Pre := CarrierPre a b R) hsel (hF.init.pair (TN.const' dT _ 5))
      ((TN.const' dS _ 5).pair hG.init) hPF hPG).of_eq (fun _ => rfl)
  · have h1 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        F.combine (z.1, z.2.1, z.2.2.1.1, z.2.2.2))
        (fun n z => CarrierPre a b RF n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((pfst (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hF.combine).restrict
        (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        G.combine (z.1, z.2.1, z.2.2.1.2, z.2.2.2))
        (fun n z => CarrierPre a b RG n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((psnd (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hG.combine).restrict
        (fun _ _ h => h)
    exact (TN.ite (Pre := fun n (z : RawMasterSI × ℕ × (S × T) × RawCoset) =>
        CarrierPre a b R n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n)
      (polyFun_fst.comp hsel) (h1.pair (TN.const' dT _ 5)) ((TN.const' dS _ 5).pair h2)
      (fun n z h hs => ⟨hPF n z.1 h.1 hs, h.2⟩) (fun n z h hs => ⟨hPG n z.1 h.1 hs, h.2⟩)).of_eq
      (fun _ => rfl)
  · have h1 : TN (fun z : RawMasterSI × S × T => F.finish (z.1, z.2.1))
        (fun n z => CarrierPre a b RF n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair (pfst polyFun_snd)) hF.finish).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × S × T => G.finish (z.1, z.2.2))
        (fun n z => CarrierPre a b RG n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair (psnd polyFun_snd)) hG.finish).restrict (fun _ _ h => h)
    exact (TN.ite (Pre := fun n (z : RawMasterSI × S × T) => CarrierPre a b R n z.1)
      (polyFun_fst.comp hsel) h1 h2 (fun n z h hs => hPF n z.1 h hs)
      (fun n z h hs => hPG n z.1 h hs)).of_eq (fun _ => rfl)

end CarrierTN

namespace StateBoundsXR

variable {a b : ℕ}

/-- **Two carriers side by side, with branch predicates**: the default states add a constant
to the exponent. -/
theorem pairIteR {S T : Type} [Enc S] [Enc T] (sel : RawMasterSI → Bool) {F : MasterOps S}
    {G : MasterOps T} (dS : S) (dT : T) {K K' : ℕ} {R RF RG : RawMasterSI → Prop}
    (hF : StateBoundsXR a b K F RF) (hG : StateBoundsXR a b K' G RG)
    (hRF : ∀ P, R P → sel P = true → RF P) (hRG : ∀ P, R P → sel P = false → RG P) :
    StateBoundsXR a b (K + K' + (Enc.size dS + Enc.size dT) + 1)
      (MasterOps.pairIte sel F G dS dT) R := by
  have hF' := hF.mono (Nat.le_add_right K K')
  have hG' := hG.mono (Nat.le_add_left K' K)
  have hL : ∀ P : RawMasterSI, 1 ≤ lg (masterDegree P) ^ 5 := fun P => one_le_lg5 _
  have hK : K + K' ≤ K + K' + (Enc.size dS + Enc.size dT) + 1 := by omega
  refine ⟨fun P hP hR => ?_, fun P j s A hP hR hA => ?_, fun P s hP hR => ?_,
    fun P s hP hR => ?_⟩
  · show Enc.size (if sel P then (F.init P, dT) else (dS, G.init P)) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]
      have := Combine.size_pair_le dS (G.init P)
      have h2 := pair_le_two_pow (e := Enc.size dS) (d := Enc.size dS + Enc.size dT)
        (hG'.1 P hP (hRG P hR hs)) (by omega) (hL P)
      omega
    · rw [if_pos rfl]
      have := Combine.size_pair_le (F.init P) dT
      exact this.trans (pair_le_two_pow (hF'.1 P hP (hRF P hR hs)) (by omega) (hL P))
  · show Enc.size (if sel P then (F.combine (P, j, s.1, A), dT)
      else (dS, G.combine (P, j, s.2, A))) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]
      have := Combine.size_pair_le dS (G.combine (P, j, s.2, A))
      have h2 := pair_le_two_pow (e := Enc.size dS) (d := Enc.size dS + Enc.size dT)
        (hG'.2.1 P j s.2 A hP (hRG P hR hs) hA) (by omega) (hL P)
      omega
    · rw [if_pos rfl]
      have := Combine.size_pair_le (F.combine (P, j, s.1, A)) dT
      exact this.trans (pair_le_two_pow (hF'.2.1 P j s.1 A hP (hRF P hR hs) hA) (by omega)
        (hL P))
  · show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]; exact hG.2.2.1 P s.2 hP (hRG P hR hs)
    · rw [if_pos rfl]; exact hF.2.2.1 P s.1 hP (hRF P hR hs)
  · show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    cases hs : sel P
    · rw [if_neg (by decide)]
      exact (hG'.2.2.2 P s.2 hP (hRG P hR hs)).trans (StateBoundsX.two_pow_mono hK _)
    · rw [if_pos rfl]
      exact (hF'.2.2.2 P s.1 hP (hRF P hR hs)).trans (StateBoundsX.two_pow_mono hK _)

end StateBoundsXR

/-! ## Routes -/

theorem masterRoute_le_five (P : RawMasterSI) : masterRoute P ≤ 5 := by
  obtain ⟨W, _ | h⟩ := P
  · simp [masterRoute]
  · show masterHintRoute (W, h) ≤ 5
    unfold masterHintRoute
    split_ifs <;> omega

/-- **The good nodes of routes 4 and 5**: at route 4 the node satisfies `Explicit.R4`, at
route 5 it satisfies `R5`. -/
def RouteGood (R5 : RawMasterSI → Prop) (P : RawMasterSI) : Prop :=
  (masterRoute P = 4 → R4 P) ∧ (masterRoute P = 5 → R5 P)

/-- The node carrier below `RouteGood` at nodes of route at least `k`. -/
def RAbove (R5 : RawMasterSI → Prop) (k : ℕ) (P : RawMasterSI) : Prop :=
  RouteGood R5 P ∧ k ≤ masterRoute P

theorem routeAt_true {k : ℕ} {P : RawMasterSI} (h : masterRouteAt k P = true) :
    masterRoute P = k := of_decide_eq_true h

theorem routeAt_false {k : ℕ} {P : RawMasterSI} (h : masterRouteAt k P = false) :
    masterRoute P ≠ k := of_decide_eq_false h

theorem rAbove_step {R5 : RawMasterSI → Prop} {k : ℕ} {P : RawMasterSI}
    (h : RAbove R5 k P) (hs : masterRouteAt k P = false) : RAbove R5 (k + 1) P := by
  have h1 := routeAt_false hs
  have h2 : k ≤ masterRoute P := h.2
  exact ⟨h.1, by omega⟩

theorem rAbove_five {R5 : RawMasterSI → Prop} {P : RawMasterSI}
    (h : RAbove R5 4 P) (hs : masterRouteAt 4 P = false) : R5 P := by
  have h1 := routeAt_false hs
  have h2 : 4 ≤ masterRoute P := h.2
  have h3 := masterRoute_le_five P
  exact h.1.2 (by omega)

theorem rAbove_one {R5 : RawMasterSI → Prop} {P : RawMasterSI}
    (h : RouteGood R5 P) (hs : masterIsLine1 P = false) : RAbove R5 1 P := by
  have h1 : masterRoute P ≠ 0 := of_decide_eq_false hs
  exact ⟨h, by omega⟩

/-! ## The dispatcher -/

/-- **The node carrier with route 5 as a parameter**: `Algo.masterTopOps` over
`Algo.masterHintOps`, with the carrier of lines 4c–4d at `c = 0` and the hint routine `H4`, as
in `Algo.masterNodeHOps`. -/
abbrev dispatchOps {T5 : Type} (B C₀ : ℕ) (cam : RawGens × List ℕ → Option RawCameron)
    (e f u v tt dd : ℕ) (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint)
    (dD : ADState) (G5 : MasterOps T5) (d5 : T5) :=
  masterTopOps B C₀ cam
    (masterHintOps e f u v (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD)
      G5 (dD, default) d5)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), d5)

/-- **Bridge**: `Algo.masterNodeHOps` at `c = 0` is the dispatcher with
`G5 = (masterL57Ops c' b' t d dc dp e f E).withHint H5`. -/
theorem masterNodeHOps_eq_dispatch (B C₀ : ℕ) (cam : RawGens × List ℕ → Option RawCameron)
    (e f u v tt dd : ℕ) (dD : ADState) (c' b' t d dc dp E : ℕ)
    (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint) :
    masterNodeHOps B C₀ cam e f u v 0 tt dd (line4dDomOps 0 tt dd) dD c' b' t d dc dp E H4 H5 =
      dispatchOps B C₀ cam e f u v tt dd H4 dD
        ((masterL57Ops c' b' t d dc dp e f E).withHint H5) default := rfl

/-- **Bridge**: `Explicit.masterOpsE` is the dispatcher. -/
theorem masterOpsE_eq_dispatch (p : Params) (cam : RawGens × List ℕ → Option RawCameron) :
    masterOpsE p cam = dispatchOps p.B p.C₀ cam p.e p.f p.u p.v p.tt p.dd
      (line4dDomHint 0 p.tt p.dd) default
      ((masterL57Ops 2 0 p.t p.d p.dc p.dp p.e p.f p.E).withHint (hint5E p)) default := rfl

/-- **Bridge**: `Algo.masterFinalOps` at `c = 0` is the dispatcher, at the bounds
`masterLine4TT 0`, `masterLine4DD 0` of line 4c chosen there. -/
theorem masterFinalOps_eq_dispatch (c' b' t d dc dp : ℕ)
    (H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint)
    (H5 : (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint) :
    masterFinalOps 0 c' b' t d dc dp H4 H5 =
      dispatchOps masterLine1B masterLine1C₀ masterCameron masterTopE masterTopF masterTopU
        masterTopV (masterLine4TT 0) (masterLine4DD 0) H4 default
        ((masterL57Ops c' b' t d dc dp masterTopE masterTopF
          (masterL57E c' b' t d dc dp)).withHint H5) default := rfl

section Dispatch

variable (a b : ℕ) {cam : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cam)
  (B C₀ e f u v tt dd : ℕ) (ht : tt + 2 ≤ 5) (dD : ADState)
  {H4 : (RawMasterSI × ℕ × ADState) × RawMasterSI → Option RawMasterHint}
  (hH4 : TN H4 (fun n w => CarrierPre a b R4 n w.1.1) 5)
  {T5 : Type} [Enc T5] {G5 : MasterOps T5} {R5 : RawMasterSI → Prop} (d5 : T5)

include hc ht hH4 in
/-- **The node carrier of the Master bounded at the degree with exponent 5**, with route 5 as
a parameter, at the nodes whose routes 4 and 5 are good. -/
theorem carrierTN_dispatch (h5 : CarrierTN a b G5 R5) :
    CarrierTN a b (dispatchOps B C₀ cam e f u v tt dd H4 dD G5 d5) (RouteGood R5) := by
  have h4 : CarrierTN a b (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD)
      R4 :=
    CarrierTN.pairIte (tn_masterHasDom tt dd ht a b)
      ((carrierTN_line4dDom tt dd ht a b).withHint hH4) (carrierTN_line4d tt dd ht a b)
  have l4 := CarrierTN.pairIteR (R := RAbove R5 4) (dS := (dD, default)) (dT := d5)
    (polyFun_masterRouteAt 4) h4 h5
    (fun P h hs => h.1.1 (routeAt_true hs))
    (fun P h hs => rAbove_five h hs)
  have l3 := CarrierTN.pairIteR (R := RAbove R5 3) (dS := default) (dT := ((dD, default), d5))
    (polyFun_masterRouteAt 3) (carrierTN_route3 (a := a) (b := b) (e := e) (f := f) (u := u)
      (v := v)) l4
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  have l2 := CarrierTN.pairIteR (R := RAbove R5 2) (dS := masterCamFoldEmbed none)
    (dT := (default, (dD, default), d5))
    (polyFun_masterRouteAt 2) (carrierTN_route2 a b) l3
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  have l1 := CarrierTN.pairIteR (R := RAbove R5 1) (dS := masterCamFoldEmbed none)
    (dT := (masterCamFoldEmbed none, default, (dD, default), d5))
    (polyFun_masterRouteAt 1) (carrierTN_route1 a b) l2
    (fun P _ hs => routeAt_true hs)
    (fun P h hs => rAbove_step h hs)
  exact CarrierTN.pairIteR polyFun_masterIsLine1 (carrierTN_route0 a b B C₀ hc) l1
    (fun P _ hs => of_decide_eq_true hs)
    (fun P h hs => rAbove_one h hs)

include hc ht in
/-- **The fold states of the Master's node carrier, with an explicit exponent**, with route 5
as a parameter, at the nodes whose routes 4 and 5 are good. -/
theorem stateBoundsXR_dispatch {K5 : ℕ} (s5 : StateBoundsXR a b K5 G5 R5) :
    ∃ K, StateBoundsXR a b K (dispatchOps B C₀ cam e f u v tt dd H4 dD G5 d5)
      (RouteGood R5) := by
  obtain ⟨K4, s4⟩ := stateBoundsXR_route4 tt dd ht a b dD
  obtain ⟨K0, s0⟩ := stateBoundsX_route0 a b B C₀ hc
  obtain ⟨K1, s1⟩ := stateBoundsX_route1 a b
  obtain ⟨K2, s2⟩ := stateBoundsX_route2 a b
  obtain ⟨K3, s3⟩ := stateBoundsX_route3 (a := a) (b := b) (e := e) (f := f) (u := u) (v := v)
  have s4' : StateBoundsXR a b K4
      (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint H4) dD) R4 := s4
  have l4 := StateBoundsXR.pairIteR (R := RAbove R5 4) (masterRouteAt 4) (dD, default) d5 s4' s5
    (fun P h hs => h.1.1 (routeAt_true hs))
    (fun P h hs => rAbove_five h hs)
  have l3 := StateBoundsXR.pairIteR (R := RAbove R5 3) (masterRouteAt 3) default
    ((dD, default), d5) (s3.toR (fun _ => True)) l4
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  have l2 := StateBoundsXR.pairIteR (R := RAbove R5 2) (masterRouteAt 2)
    (masterCamFoldEmbed none) (default, (dD, default), d5) (s2.toR (fun _ => True)) l3
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  have l1 := StateBoundsXR.pairIteR (R := RAbove R5 1) (masterRouteAt 1)
    (masterCamFoldEmbed none) (masterCamFoldEmbed none, default, (dD, default), d5)
    (s1.toR (fun _ => True)) l2
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_step h hs)
  exact ⟨_, StateBoundsXR.pairIteR masterIsLine1 (masterCamFoldEmbed none)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, (dD, default), d5) (s0.toR (fun _ => True)) l1
    (fun _ _ _ => trivial)
    (fun P h hs => rAbove_one h hs)⟩

end Dispatch

/-! ## The variant Master -/

/-- **The node carrier of `Explicit.masterOpsE`, bounded at the degree with exponent 5**, given
`p.tt ≤ 3` and the bounds of route 5. -/
theorem carrierTN_masterOpsE (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop}
    (h5 : CarrierTN p.a p.b ((masterL57Ops 2 0 p.t p.d p.dc p.dp p.e p.f p.E).withHint
      (hint5E p)) R5) :
    CarrierTN p.a p.b (masterOpsE p cam) (RouteGood R5) :=
  carrierTN_dispatch p.a p.b hc p.B p.C₀ p.e p.f p.u p.v p.tt p.dd ht default
    (tn_line4dDomHint p.tt p.dd ht p.a p.b) default h5

/-- **The fold states of `Explicit.masterOpsE`, with an explicit exponent**, given `p.tt ≤ 3`
and the state bounds of route 5. -/
theorem stateBoundsXR_masterOpsE (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) (ht : p.tt + 2 ≤ 5) {R5 : RawMasterSI → Prop} {K5 : ℕ}
    (s5 : StateBoundsXR p.a p.b K5 ((masterL57Ops 2 0 p.t p.d p.dc p.dp p.e p.f p.E).withHint
      (hint5E p)) R5) :
    ∃ K, StateBoundsXR p.a p.b K (masterOpsE p cam) (RouteGood R5) :=
  stateBoundsXR_dispatch p.a p.b hc p.B p.C₀ p.e p.f p.u p.v p.tt p.dd ht default default s5

end Explicit
