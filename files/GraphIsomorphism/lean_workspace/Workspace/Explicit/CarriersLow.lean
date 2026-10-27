/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the carriers of routes 0–3
bounded at the degree, with explicit state bounds. Not part of the faithful formalization.
-/
import Workspace.Explicit.CarriersLowDesc

/-!
# The carriers of routes 0–3

The carriers of the variant node carrier `Explicit.masterOpsE` at a node of route `k`
(`Algo.masterRoute`):

* route 0 (line 1, Procedure Reduce-to-Johnson, Sec. 11.3): `Algo.masterLine1Ops B C₀ cam`,
  with the trivial and the brute-force leaves (steps 1, 2), the Chain Rule carrier
  `Algo.masterChainLiftOps` (step 3), the block descent `Algo.masterBlockOps` (step 5) and the
  prepared Cameron carrier `Algo.masterCamPreparedOps` (steps 4, 6);
* route 1 (line 2): the descent carrier `Algo.masterDescPreparedOps 3`;
* route 2 (line 4a): the leaf `Algo.masterLeafOps primitiveWindowLeaf`;
* route 3 (line 4b): `Algo.master4bOps e f u v`.

For each: `Explicit.carrierTN_routeK`, the four local routines bounded at the degree with
exponent 5 (`Explicit.CarrierTN`, on admitted nodes of route `k` and degree at most `n`), and
`Explicit.stateBoundsX_routeK`, the size fields of `Algo.MasterOpsCost` with the explicit bound
`2^{K (log₂ n + 2)^5}` (`Explicit.StateBoundsX`).

Only the two descents (line 2 and line 1, step 5) are not polynomial
(`Explicit.carrierTN_desc`). The prepared Cameron carrier is polynomial
(`Algo.masterCamSelect_polyFun`), and so is the answer of line 4b once its solver is the
constant `none` (`Explicit.polyFun_master4OpenFinish`; the existing proof,
`Algo.quasiFun_master4OpenFinish`, goes through `QuasiFun` for a general solver).
No routine needs a fact about reachable fold states or good nodes.
-/

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

/-! ## Leaves -/

section Leaf

variable (a b : ℕ) {f : RawWinSI → RawCoset}

theorem carrierTN_leaf (hf : PolyFun f) (R : RawMasterSI → Prop) :
    CarrierTN a b (masterLeafOps f) R :=
  CarrierTN.ofPoly R (polyFun_const (none : Option RawMasterSI))
    (polyFun_const (masterCamFoldEmbed none)) (polyFun_const (masterCamFoldEmbed none))
    ((polyFun_fst.comp polyFun_fst).comp hf)

theorem stateBoundsX_leaf (hsz : ∀ W, Enc.size (f W) ≤ chainBound W.2.2.2.1.length) :
    ∃ K, StateBoundsX a b K (masterLeafOps f) := by
  have h0 := masterCamFoldEmbed_size none
  rw [size_none] at h0
  obtain ⟨K, hK⟩ := q5_const 96
  refine StateBoundsX.of_three K (fun P _ => ?_) (fun P _ _ _ _ _ => ?_) (fun P s _ => ?_)
  · exact le_trans (by change Enc.size (masterCamFoldEmbed none) ≤ 96; omega) (hK _)
  · exact le_trans (by change Enc.size (masterCamFoldEmbed none) ≤ 96; omega) (hK _)
  · exact (hsz P.1).trans (by
      unfold masterInputCap; change chainBound (masterDegree P) ≤ _; omega)

end Leaf

/-! ## Line 1 -/

section Line1

variable (a b : ℕ)

theorem polyFun_masterChainLift :
    PolyFun masterChainLiftOps.child ∧ PolyFun masterChainLiftOps.init ∧
      PolyFun masterChainLiftOps.combine ∧ PolyFun masterChainLiftOps.finish := by
  have hW : PolyFun (fun p : RawMasterSI => p.1) := polyFun_fst
  have hs : PolyFun (fun s : AggnRecomputeState => s.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((polyFun_fst.comp hW).pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp hs))).comp polyFun_masterChainOpenChild
  · exact (hW.comp polyFun_masterChainOpenInit).comp polyFun_masterCamFoldEmbed
  · exact (((polyFun_fst.comp hW).pair ((polyFun_snd.comp polyFun_fst).pair
      ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp hs).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)))).comp
      polyFun_masterChainOpenCombine).comp polyFun_masterCamFoldEmbed
  · exact ((polyFun_fst.comp hW).pair (polyFun_snd.comp hs)).comp polyFun_masterChainOpenFinish

theorem carrierTN_chainLift (R : RawMasterSI → Prop) : CarrierTN a b masterChainLiftOps R := by
  obtain ⟨hc, hi, hu, hf⟩ := polyFun_masterChainLift
  exact CarrierTN.ofPoly R hc hi hu hf

theorem stateBoundsX_chainLift : ∃ K, StateBoundsX a b K masterChainLiftOps := by
  obtain ⟨K, hK⟩ := ((q5_const 16).mul ((q5_of_polyBound polyBound_chainBound).add
    (q5_const 4))).mono (T := fun n => 16 * (chainBound n + 4)) (fun _ => le_rfl)
  refine StateBoundsX.of_three K (fun p _ => ?_) (fun p j s A _ _ => ?_) (fun p s _ => ?_)
  · have h1 := masterCamFoldEmbed_size (masterChainOpenInit p.1)
    have h2 := masterChainOpenInit_size p.1
    change _ ≤ chainBound (masterDegree p) at h2
    have h3 := hK (masterDegree p)
    change Enc.size (masterCamFoldEmbed (masterChainOpenInit p.1)) ≤ _
    dsimp only at h3
    omega
  · have h1 := masterCamFoldEmbed_size (masterChainOpenCombine (p.1, j, s.2.2.2, A))
    have h2 := masterChainOpenCombine_size p.1 j s.2.2.2 A
    change _ ≤ chainBound (masterDegree p) at h2
    have h3 := hK (masterDegree p)
    change Enc.size (masterCamFoldEmbed (masterChainOpenCombine (p.1, j, s.2.2.2, A))) ≤ _
    dsimp only at h3
    omega
  · have h := masterChainOpenFinish_size p.1 s.2.2.2
    change Enc.size (masterChainOpenFinish (p.1, s.2.2.2)) ≤ _
    change _ ≤ chainBound (masterDegree p) at h
    exact h.trans (by unfold masterInputCap; omega)

theorem carrierTN_block (R : RawMasterSI → Prop) : CarrierTN a b masterBlockOps R :=
  carrierTN_desc a b polyFun_masterBlockSelect R

theorem stateBoundsX_block : ∃ K, StateBoundsX a b K masterBlockOps :=
  stateBoundsX_desc a b polyFun_masterBlockSelect masterBlockSelect_source

/-- The answer of a shifted carrier is polynomial when the carrier's is. -/
theorem polyFun_masterShiftFinish {S : Type} [Enc S] {F : MasterOps S}
    (hf : PolyFun F.finish) : PolyFun (masterShiftOps F).finish := by
  have hx : PolyFun (fun z : RawMasterSI × S => z.1.1.2.2.2.1) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp
      polyFun_snd).comp polyFun_fst)
  have hr : PolyFun (fun z : RawMasterSI × S => z.1.1.2.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  exact (hx.pair (hr.pair hf)).comp polyFun_top3Shift

variable {g : RawMasterSI → RawCameron × MasterDescInput}

theorem carrierTN_camPrepared (hg : PolyFun g) (R : RawMasterSI → Prop) :
    CarrierTN a b (masterCamPreparedOps g) R := by
  obtain ⟨-, hc, hi, hu, hf⟩ :=
    masterCamSelect_polyFun (fun p => masterCamPrepared (g p)) (hg.comp polyFun_masterCamPrepared)
  exact CarrierTN.ofPoly R hc hi hu (polyFun_masterShiftFinish hf)

theorem stateBoundsX_camPrepared (hg : PolyFun g)
    (hsource : ∀ p, (g p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    ∃ K, StateBoundsX a b K (masterCamPreparedOps g) := by
  let f := fun p => masterCamPrepared (g p)
  have hf : PolyFun f := hg.comp polyFun_masterCamPrepared
  have hl : PolyFun (fun p => masterCamLists (f p)) := hf.comp polyFun_masterCamLists
  obtain ⟨r₀, r, hb⟩ := master_size_poly hl.size a b
  obtain ⟨K, hK⟩ := (((q5_const 16).mul ((((q5_poly r₀ r).add
    (q5_of_polyBound polyBound_chainBound)).add (q5_const 4)).add (q5_const 1))).add
    (q5_const 96)).mono
    (T := fun n => 16 * (2 ^ r₀ * (n + 1) ^ r + chainBound n + 4 + 1) + 96) (fun _ => le_rfl)
  have hx : ∀ p, (masterCamLists (f p)).1.2.2.2.1.length = masterDegree p :=
    fun p => congrArg List.length (hsource p)
  refine StateBoundsX.of_three K (fun p hp => ?_) (fun p j s A hp _ => ?_) (fun p s _ => ?_)
  · have h0 := masterCamFoldEmbed_size none
    rw [size_none] at h0
    have h1 := masterDescFoldInit_size (masterCamLists (f p))
    rw [hx] at h1
    have h2 := hb (masterDegree p) p hp le_rfl
    have h3 := hK (masterDegree p)
    dsimp only at h3
    change Enc.size ((masterCamSelectOps f).init p) ≤ _
    dsimp only [masterCamSelectOps]
    split <;> omega
  · have h0 := masterCamFoldEmbed_size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A))
    have h1 := size_top2NormC_le (dom := p.1.2.2.2.1) rfl le_rfl
      (rawCosetJoin (p.1.2.2.2.1, s.2.2.2, A))
    change Enc.size (masterDescJoin (p.1.2.2.2.1, s.2.2.2, A)) ≤ chainBound (masterDegree p) at h1
    have h2 := masterDescFoldCombine_size (masterCamLists (f p)) j s A
    rw [hx] at h2
    have h4 := hb (masterDegree p) p hp le_rfl
    have h3 := hK (masterDegree p)
    dsimp only at h3
    change Enc.size ((masterCamSelectOps f).combine (p, j, s, A)) ≤ _
    dsimp only [masterCamSelectOps]
    split <;> omega
  · exact (masterShiftOps_finish_size _ p s).trans (by unfold masterInputCap; omega)

variable {cam : RawGens × List ℕ → Option RawCameron}

/-- **Route 0 (line 1), bounded at the degree.** -/
theorem carrierTN_route0 (B C₀ : ℕ) (hc : PolyFun cam) :
    CarrierTN a b (masterLine1Ops B C₀ cam) (fun P => masterRoute P = 0) :=
  CarrierTN.ite (polyFun_masterRouteIs B C₀ 0) (carrierTN_leaf a b polyFun_masterWindowTrivialLeaf _) <|
  CarrierTN.ite (polyFun_masterRouteIs B C₀ 1)
    (carrierTN_leaf a b (polyFun_masterWindowBruteLeaf C₀) _) <|
  CarrierTN.ite (polyFun_masterRouteIs B C₀ 2) (carrierTN_chainLift a b _) <|
  CarrierTN.ite (polyFun_masterRouteIs B C₀ 3) (carrierTN_block a b _)
    (carrierTN_camPrepared a b (polyFun_masterCamRouteInput hc) _)

/-- **Route 0 (line 1): explicit state bounds.** -/
theorem stateBoundsX_route0 (B C₀ : ℕ) (hc : PolyFun cam) :
    ∃ K, StateBoundsX a b K (masterLine1Ops B C₀ cam) := by
  obtain ⟨K0, h0⟩ := stateBoundsX_leaf a b (f := masterWindowTrivialLeaf)
    (fun W => masterWindowReturn_size (W, _))
  obtain ⟨K1, h1⟩ := stateBoundsX_leaf a b (f := masterWindowBruteLeaf C₀)
    (fun W => masterWindowReturn_size (W, _))
  obtain ⟨K2, h2⟩ := stateBoundsX_chainLift a b
  obtain ⟨K3, h3⟩ := stateBoundsX_block a b
  obtain ⟨K4, h4⟩ := stateBoundsX_camPrepared a b (polyFun_masterCamRouteInput hc)
    (masterCamRouteInput_source cam)
  exact ⟨_, h0.ite (h1.ite (h2.ite (h3.ite h4)))⟩

end Line1

/-! ## Line 2 -/

/-- **Route 1 (line 2), bounded at the degree.** -/
theorem carrierTN_route1 (a b : ℕ) :
    CarrierTN a b (masterDescPreparedOps 3) (fun P => masterRoute P = 1) :=
  carrierTN_desc a b polyFun_masterDescPreparedSelect _

/-- **Route 1 (line 2): explicit state bounds.** -/
theorem stateBoundsX_route1 (a b : ℕ) : ∃ K, StateBoundsX a b K (masterDescPreparedOps 3) :=
  stateBoundsX_desc a b polyFun_masterDescPreparedSelect (fun _ => rfl)

/-! ## Line 4a -/

/-- **Route 2 (line 4a), bounded at the degree.** -/
theorem carrierTN_route2 (a b : ℕ) :
    CarrierTN a b (masterLeafOps primitiveWindowLeaf) (fun P => masterRoute P = 2) :=
  carrierTN_leaf a b polyFun_primitiveWindowLeaf _

/-- **Route 2 (line 4a): explicit state bounds.** -/
theorem stateBoundsX_route2 (a b : ℕ) :
    ∃ K, StateBoundsX a b K (masterLeafOps primitiveWindowLeaf) :=
  stateBoundsX_leaf a b primitiveWindowLeaf_size

/-! ## Line 4b -/

section Line4b

theorem polyFun_top4FinishP {solve : RawWinSI → RawCoset} (hsolve : PolyFun solve) :
    PolyFun (top4Finish solve) := by
  have hx : PolyFun (fun z : Top4Node × Top4State => top4X z.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_top4X
  have hg : PolyFun (fun z : Top4Node × Top4State => z.2.2.2) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)
  have hh : PolyFun (fun q : RawWinSI × (Top4Node × Top4State) => solve q.1) :=
    polyFun_fst.comp hsolve
  have hsel : PolyFun (fun z : Top4Node × Top4State => (z.1.2, z)) :=
    (polyFun_fst.comp polyFun_snd).pair polyFun_id
  have hresult : PolyFun (fun z : Top4Node × Top4State => z.1.2.elim z.2.2.2 solve) :=
    hsel.comp (PolyFun.optionElim hg hh)
  exact (hx.pair hresult).comp polyFun_top2NormC

theorem polyFun_top4aFinishP {solve : RawWinSI → RawCoset} (hsolve : PolyFun solve) :
    PolyFun (top4aFinish solve) := by
  have hI : PolyFun (fun z : Top4aNode × Top4State => z.1.1) := polyFun_fst.comp polyFun_fst
  have hX := (hI.comp polyFun_fst).comp polyFun_top4X
  have hα : PolyFun (fun z : Top4aNode × Top4State => z.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hflag : PolyFun (fun z : Top4aNode × Top4State => z.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  have hfin := (hI.pair polyFun_snd).comp (polyFun_top4FinishP hsolve)
  have hshift := (hX.pair (hα.pair hfin)).comp polyFun_top3Shift
  have hroot := PolyFun.ite hflag hshift (polyFun_const none)
  exact ((hI.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hroot (polyFun_snd.comp hfin))

theorem polyFun_top4wFinishP {solve : RawWinSI → RawCoset} (hs : PolyFun solve) :
    PolyFun (top4wFinish solve) := by
  have hC : PolyFun (fun z : Top4wNode × Top4State => z.1.1) := polyFun_fst.comp polyFun_fst
  have hP := hC.comp polyFun_snd
  have hOuter := hC.comp polyFun_fst
  have hg := hOuter.comp polyFun_fst
  have hw := (hOuter.comp polyFun_snd).comp polyFun_fst
  have hx := (hOuter.comp polyFun_snd).comp polyFun_snd
  have hanswer := (hP.pair polyFun_snd).comp (polyFun_top4aFinishP hs)
  have hpre := (hg.pair (hw.pair hanswer)).comp polyFun_topwCosetPreimage
  have hchoose := (((polyFun_fst.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hpre (polyFun_fst.comp hs)))
  exact (hx.pair hchoose).comp polyFun_top2NormC

theorem polyFun_master4FinishP {solve : RawWinSI → RawCoset} (hsolve : PolyFun solve) :
    PolyFun (master4Finish solve) := by
  have hI : PolyFun (fun z : Master4Node × Top4State => z.1.1) := polyFun_fst.comp polyFun_fst
  have hx : PolyFun (fun z : Master4Node × Top4State => master4X z.1) :=
    polyFun_fst.comp polyFun_master4X
  have hr : PolyFun (fun z : Master4Node × Top4State => z.1.2) := polyFun_fst.comp polyFun_snd
  have hfin := (hI.pair polyFun_snd).comp (polyFun_top4wFinishP hsolve)
  have hshift := (hx.pair (hr.pair hfin)).comp polyFun_top3Shift
  exact ((hI.comp polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim hshift (polyFun_snd.comp hfin))

/-- **The answer of line 4b is polynomial** (its solver is the constant `none`). -/
theorem polyFun_master4OpenFinish : PolyFun master4OpenFinish :=
  ((polyFun_fst.comp polyFun_master4Enter).pair polyFun_snd).comp
    (polyFun_master4FinishP (polyFun_const none))

variable (a b e f u v : ℕ)

theorem polyFun_master4b :
    PolyFun (master4bOps e f u v).child ∧ PolyFun (master4bOps e f u v).init ∧
      PolyFun (master4bOps e f u v).combine ∧ PolyFun (master4bOps e f u v).finish := by
  have hs : PolyFun (fun P : RawMasterSI => P.2.isSome) := polyFun_snd.comp polyFun_optionIsSome
  have hs1 : PolyFun (fun z : RawMasterSI × ℕ × Top4State => z.1.2.isSome) := polyFun_fst.comp hs
  have hs2 : PolyFun (fun z : RawMasterSI × ℕ × Top4State × RawCoset => z.1.2.isSome) :=
    polyFun_fst.comp hs
  have hg1 : PolyFun (fun z : RawMasterSI × ℕ × Top4State =>
      master4OpenChild e f u v (masterHintGet z.1, z.2.1, z.2.2)) :=
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp
      (polyFun_master4OpenChild e f u v)
  have hg2 : PolyFun (fun z : RawMasterSI × ℕ × Top4State × RawCoset =>
      master4OpenCombine (masterHintGet z.1, z.2.1, z.2.2.1, z.2.2.2)) :=
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp polyFun_master4OpenCombine
  exact ⟨PolyFun.ite hs1 hg1 (polyFun_const none),
    PolyFun.ite hs (polyFun_masterHintGet.comp polyFun_master4OpenInit) (polyFun_const default),
    PolyFun.ite hs2 hg2 (polyFun_const default),
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp polyFun_master4OpenFinish⟩

/-- **Route 3 (line 4b), bounded at the degree.** -/
theorem carrierTN_route3 :
    CarrierTN a b (master4bOps e f u v) (fun P => masterRoute P = 3) := by
  obtain ⟨hc, hi, hu, hf⟩ := polyFun_master4b e f u v
  exact CarrierTN.ofPoly _ hc hi hu hf

/-- **Route 3 (line 4b): explicit state bounds.** -/
theorem stateBoundsX_route3 : ∃ K, StateBoundsX a b K (master4bOps e f u v) := by
  obtain ⟨c, d, hb⟩ := master4Open_uniform_bounds a b
  obtain ⟨K, hK⟩ := ((q5_of_polyBound (polyBound_master4OpenStateBound c d)).add
    (q5_const (Enc.size (default : Top4State)))).mono
    (T := fun n => master4OpenStateBound c d n + Enc.size (default : Top4State))
    (fun _ => le_rfl)
  refine StateBoundsX.of_three K (fun P hP => ?_) (fun P j s A hP _ => ?_) (fun P s _ => ?_)
  · refine le_trans ?_ (hK (masterDegree P))
    change Enc.size (if P.2.isSome then master4OpenInit (masterHintGet P) else default) ≤ _
    obtain ⟨W, o⟩ := P
    cases o with
    | none => exact Nat.le_add_left _ _
    | some h => exact ((hb (W, h) hP).1).trans (Nat.le_add_right _ _)
  · refine le_trans ?_ (hK (masterDegree P))
    change Enc.size (if P.2.isSome then
      master4OpenCombine (masterHintGet P, j, s, A) else default) ≤ _
    obtain ⟨W, o⟩ := P
    cases o with
    | none => exact Nat.le_add_left _ _
    | some h => exact (((hb (W, h) hP).2.1) j s A).trans (Nat.le_add_right _ _)
  · exact (master4OpenFinish_size (masterHintGet P) s).trans (by
      change chainBound (masterDegree P) ≤ _
      unfold masterInputCap; omega)

end Line4b

end Explicit
