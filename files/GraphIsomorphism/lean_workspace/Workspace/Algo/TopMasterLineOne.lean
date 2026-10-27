import Workspace.Algo.TopMasterBlockCase
import Workspace.Algo.TopMasterChainReturnMatch
import Workspace.Algo.TopMasterOpsIte

/-! # Section 15, line 1 on the RAM: one carrier for Procedure Reduce-to-Johnson
At a node without hint, line 1 of the Master Algorithm runs one round of
Procedure Reduce-to-Johnson (Section 11.3). The computed test
`masterReduceRoute` picks its step: 0 for the fixed-string exit of step 1,
1 for the small-group exit of step 2, 2 for the Chain Rule of step 3, 3 for
the block Luks reduction of step 5, and 4 for the Cameron descent of step 6.
The five branch carriers already match their `Line1Case` at a node of their
route. This file puts them on one fold state and one carrier, chosen by the
route test, with one local cost package.

The two constants of the route test are the paper's absolute constants:
`B = n₀` (`Babai.descentThreshold`) bounds the number of blocks below which
step 6 does not apply, and `C₀ = N₀! + 1` (`Babai.bruteForceOrderThreshold`)
is the fixed cutoff of step 2.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The block-count constant of the route test: `n₀` of Section 11.3, step 4. -/
noncomputable def masterLine1B : ℕ := descentThreshold.{0}

/-- The order cutoff of the route test: the fixed cutoff of Section 11.3, step 2. -/
noncomputable def masterLine1C₀ : ℕ := bruteForceOrderThreshold.{0}

theorem masterLine1_one_lt : 1 < masterLine1C₀ := by
  unfold masterLine1C₀ bruteForceOrderThreshold
  have := Nat.factorial_pos bruteForceThreshold.{0}
  omega

theorem masterLine1_cameron_cutoff : (63).factorial < masterLine1C₀ := by
  unfold masterLine1C₀ bruteForceOrderThreshold
  have h1 : (63).factorial ≤ (64).factorial := Nat.factorial_le (by norm_num)
  have h2 : (64).factorial ≤ bruteForceThreshold.{0}.factorial :=
    Nat.factorial_le sixtyFour_le_bruteForceThreshold
  omega

theorem masterLine1_block_cutoff : (max 64 masterLine1B.factorial).factorial < masterLine1C₀ :=
  Nat.lt_succ_self _

theorem masterLine1_blocks : max 25 camDescentThreshold ≤ masterLine1B :=
  cameronThreshold_le_descentThreshold.{0}

/-- The route test at a node: whether it takes the given step. -/
def masterRouteIs (B C₀ k : ℕ) (p : RawMasterSI) : Bool :=
  decide (masterReduceRoute B C₀ p.1 = k)

theorem polyFun_masterRouteIs (B C₀ k : ℕ) : PolyFun (masterRouteIs B C₀ k) :=
  (polyFun_fst.comp (polyFun_masterReduceRoute _ _)).natEq (polyFun_const k)

theorem masterReduceRoute_le_four (B C₀ : ℕ) (W : RawWinSI) : masterReduceRoute B C₀ W ≤ 4 := by
  unfold masterReduceRoute
  split_ifs <;> omega

/-! ### The leaf carriers of steps 1 and 2 -/

/-- A carrier that asks nothing and returns the value `f` computes. -/
def masterLeafOps (f : RawWinSI → RawCoset) : MasterOps AggnRecomputeState where
  width _ := 0
  child _ := none
  init _ := masterCamFoldEmbed none
  combine _ := masterCamFoldEmbed none
  finish z := f z.1.1

/-- The local cost data of a leaf carrier. -/
theorem masterLeafOps_cost (a b : ℕ) {f : RawWinSI → RawCoset} (hf : PolyFun f)
    (hsz : ∀ W, Enc.size (f W) ≤ chainBound W.2.2.2.1.length) :
    Nonempty (MasterOpsCost a b (masterLeafOps f)) := by
  have h0 := masterCamFoldEmbed_size none
  rw [size_none] at h0
  refine ⟨⟨fun _ => 96, fun _ => 0, (polyBound_const 96).quasiPoly, fun _ _ _ => le_rfl,
    (polyBound_const 0).quasiPoly, (polyFun_const 0).quasiFun, (polyFun_const none).quasiFun,
    (polyFun_const _).quasiFun, (polyFun_const _).quasiFun,
    ((polyFun_fst.comp polyFun_fst).comp hf).quasiFun, ?_, ?_, ?_, fun _ _ => le_rfl⟩⟩
  · intro p _
    change Enc.size (masterCamFoldEmbed none) ≤ 96
    omega
  · intro p _ _ _ _ _
    change Enc.size (masterCamFoldEmbed none) ≤ 96
    omega
  · intro p s _
    exact (hsz p.1).trans (by unfold masterInputCap; change chainBound (masterDegree p) ≤ _; omega)

/-- A leaf that matches on its own round matches on the admitted carrier. -/
theorem masterLeafOps_match (a b : ℕ) {f : RawWinSI → RawCoset} {n : ℕ} {W : RawWinSI}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch (masterLeafRound a b f) (decWinSI n) (decCoset n) W 0 0 0 T) :
    LoopMatch (masterAdmittedRound a b (masterLeafOps f)) (fun J => decWinSI n J.1) (decCoset n)
      (W, none) ((masterLeafOps f).width (W, none)) 0 ((masterLeafOps f).init (W, none)) T := by
  cases h with
  | done w j s A hc ha =>
    exact .done _ _ _ A (by
      show masterGuardedChild a b (masterLeafOps f) ((W, none), 0, (masterLeafOps f).init (W, none)) = none
      exact if_neg (lt_irrefl 0)) ha

/-! ### The Chain Rule carrier of step 3 on the common fold state -/

/-- The Chain Rule carrier of step 3, with its coset register embedded in the
common fold state. -/
def masterChainLiftOps : MasterOps AggnRecomputeState where
  width p := (winOrbits (p.1.2.1, p.1.1)).length
  child z := masterChainOpenChild (z.1.1, z.2.1, z.2.2.2.2.2)
  init p := masterCamFoldEmbed (masterChainOpenInit p.1)
  combine z := masterCamFoldEmbed (masterChainOpenCombine (z.1.1, z.2.1, z.2.2.1.2.2.2, z.2.2.2))
  finish z := masterChainOpenFinish (z.1.1, z.2.2.2.2)

/-- The local cost data of the Chain Rule carrier. -/
theorem masterChainLift_cost (a b : ℕ) : Nonempty (MasterOpsCost a b masterChainLiftOps) := by
  have hW : PolyFun (fun p : RawMasterSI => p.1) := polyFun_fst
  have hs : PolyFun (fun s : AggnRecomputeState => s.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  let C := fun n => 16 * (chainBound n + 4)
  have hC : QuasiPolyBound C := (polyBound_const 16).quasiPoly.mul
    (polyBound_chainBound.quasiPoly.add (polyBound_const 4).quasiPoly)
  have hmC : Monotone C := by
    intro i j hij
    have := mono_chainBound hij
    dsimp only [C]
    omega
  have hwid : PolyFun (fun p : RawMasterSI => (winOrbits (p.1.2.1, p.1.1)).length) :=
    ((((polyFun_fst.comp polyFun_snd).comp polyFun_fst).pair (polyFun_fst.comp polyFun_fst)).comp
      polyFun_winOrbits).comp polyFun_length
  have hch : PolyFun (fun z : RawMasterSI × ℕ × AggnRecomputeState =>
      masterChainOpenChild (z.1.1, z.2.1, z.2.2.2.2.2)) :=
    ((polyFun_fst.comp hW).pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp hs))).comp polyFun_masterChainOpenChild
  have hin : PolyFun (fun p : RawMasterSI => masterCamFoldEmbed (masterChainOpenInit p.1)) :=
    (hW.comp polyFun_masterChainOpenInit).comp polyFun_masterCamFoldEmbed
  have hco : PolyFun (fun z : RawMasterSI × ℕ × AggnRecomputeState × RawCoset =>
      masterCamFoldEmbed (masterChainOpenCombine (z.1.1, z.2.1, z.2.2.1.2.2.2, z.2.2.2))) :=
    (((polyFun_fst.comp hW).pair ((polyFun_snd.comp polyFun_fst).pair
      ((((polyFun_snd.comp polyFun_snd).comp polyFun_fst).comp hs).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)))).comp
      polyFun_masterChainOpenCombine).comp polyFun_masterCamFoldEmbed
  have hfi : PolyFun (fun z : RawMasterSI × AggnRecomputeState =>
      masterChainOpenFinish (z.1.1, z.2.2.2.2)) :=
    ((polyFun_fst.comp hW).pair (polyFun_snd.comp hs)).comp polyFun_masterChainOpenFinish
  refine ⟨⟨C, fun n => n, hC, hmC, polyBound_id.quasiPoly, hwid.quasiFun, hch.quasiFun,
    hin.quasiFun, hco.quasiFun, hfi.quasiFun, ?_, ?_, ?_, ?_⟩⟩
  · intro p _
    have h1 := masterCamFoldEmbed_size (masterChainOpenInit p.1)
    have h2 := masterChainOpenInit_size p.1
    change Enc.size (masterCamFoldEmbed (masterChainOpenInit p.1)) ≤ 16 * (chainBound (masterDegree p) + 4)
    change _ ≤ chainBound (masterDegree p) at h2
    omega
  · intro p j s A _ _
    have h1 := masterCamFoldEmbed_size (masterChainOpenCombine (p.1, j, s.2.2.2, A))
    have h2 := masterChainOpenCombine_size p.1 j s.2.2.2 A
    change Enc.size (masterCamFoldEmbed (masterChainOpenCombine (p.1, j, s.2.2.2, A))) ≤
      16 * (chainBound (masterDegree p) + 4)
    change _ ≤ chainBound (masterDegree p) at h2
    omega
  · intro p s _
    have h := masterChainOpenFinish_size p.1 s.2.2.2
    change Enc.size (masterChainOpenFinish (p.1, s.2.2.2)) ≤ _
    change _ ≤ chainBound (masterDegree p) at h
    exact h.trans (by unfold masterInputCap; omega)
  · intro p hp
    exact (length_winOrbits_le _ _).trans hp.2.1

/-! ### One carrier for line 1 -/

/-- **Section 15, line 1, on one carrier.** The route test chooses the step of
Procedure Reduce-to-Johnson; the chosen branch runs on the common fold state. -/
def masterLine1Ops (B C₀ : ℕ) (cameron : RawGens × List ℕ → Option RawCameron) :
    MasterOps AggnRecomputeState :=
  MasterOps.ite (masterRouteIs B C₀ 0) (masterLeafOps masterWindowTrivialLeaf) <|
  MasterOps.ite (masterRouteIs B C₀ 1) (masterLeafOps (masterWindowBruteLeaf C₀)) <|
  MasterOps.ite (masterRouteIs B C₀ 2) masterChainLiftOps <|
  MasterOps.ite (masterRouteIs B C₀ 3) masterBlockOps <|
  masterCamPreparedOps (masterCamRouteInput cameron)

/-- The line-1 carrier has one local cost package at all ambient degrees. -/
theorem masterLine1_cost (a b B C₀ : ℕ) {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) : Nonempty (MasterOpsCost a b (masterLine1Ops B C₀ cameron)) := by
  obtain ⟨C0⟩ := masterLeafOps_cost a b polyFun_masterWindowTrivialLeaf
    (fun W => masterWindowReturn_size (W, _))
  obtain ⟨C1⟩ := masterLeafOps_cost a b (polyFun_masterWindowBruteLeaf C₀)
    (fun W => masterWindowReturn_size (W, _))
  obtain ⟨C2⟩ := masterChainLift_cost a b
  obtain ⟨C3⟩ := masterBlock_cost a b
  obtain ⟨C4⟩ := masterCamPrepared_cost a b (masterCamRouteInput cameron)
    (polyFun_masterCamRouteInput hc) (masterCamRouteInput_source cameron)
  exact ⟨.ite (polyFun_masterRouteIs B C₀ 0) C0 <| .ite (polyFun_masterRouteIs B C₀ 1) C1 <|
    .ite (polyFun_masterRouteIs B C₀ 2) C2 <| .ite (polyFun_masterRouteIs B C₀ 3) C3 C4⟩

/-- The line-1 carrier runs as one raw round at all ambient degrees. -/
theorem masterLine1_runCostQ (a b B C₀ : ℕ) {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterLine1Ops B C₀ cameron))) :=
  (masterLine1_cost a b B C₀ hc).map MasterOpsCost.runCostQ

/-! ### The case and the tree the carrier runs -/

section Case
variable {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron)

/-- The route at the node, with the paper's constants. -/
noncomputable def masterLine1Route (W : RawWinSI) : ℕ :=
  masterReduceRoute masterLine1B masterLine1C₀ W

theorem masterLine1Route_four {W : RawWinSI} (h0 : masterLine1Route W ≠ 0)
    (h1 : masterLine1Route W ≠ 1) (h2 : masterLine1Route W ≠ 2) (h3 : masterLine1Route W ≠ 3) :
    masterLine1Route W = 4 := by
  have := masterReduceRoute_le_four masterLine1B masterLine1C₀ W
  unfold masterLine1Route at *
  omega

/-- **Section 11.3 at the node, as the machine decides it.** The step of
Procedure Reduce-to-Johnson that the route test selects, with the paper's
evidence for that step, at the group frame of the node. -/
noncomputable def masterLine1Case :
    Line1Case (masterGroupInstance n W) (line1Cost (masterGroupInstance n W).windowSize) :=
  if h0 : masterLine1Route W = 0 then
    masterFixedStringCase hW.2.2.1 hW.1 hW.2.1 hinv _ masterLine1B masterLine1C₀ h0
  else if h1 : masterLine1Route W = 1 then
    masterSmallGroupCase hW.2.2.1 hW.1 hW.2.1 hinv _ masterLine1B h1
  else if h2 : masterLine1Route W = 2 then
    masterChainCase hW.2.2.1 hW.1 hW.2.1 hinv h2 _ masterLine1_one_lt
  else if h3 : masterLine1Route W = 3 then
    masterStepFiveCase hW hW.2.2.2.2.2.1.1 hinv masterLine1_block_cutoff h3
  else
    masterCameronLine1Case hW.2.2.2.2.2.1.1 hW.2.2.1 hW.1 hW.2.1 hinv masterLine1_cameron_cutoff
      (masterLine1Route_four h0 h1 h2 h3) hc hs masterLine1_blocks

/-- The shift of Equation (59) back to the node's candidate coset. -/
noncomputable def masterNodeShift (n : ℕ) (W : RawWinSI) :
    Set (Perm (Fin n)) → SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  fun A => .done (decPerm n W.2.2.1 • A)

/-- The tree the line-1 carrier walks at the node: the chosen branch in the
group frame, then the shift back. The exits of steps 1 and 2 return the answer
directly; the other steps return it through their coset form (Remark 11.1.4). -/
noncomputable def masterLine1Tree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if masterLine1Route W ≤ 1 then
    (masterLine1Case hW hinv hc hs).branch.bind (masterNodeShift n W)
  else (masterLine1Case hW hinv hc hs).cosetBranch.bind (masterNodeShift n W)

theorem masterRouteIs_true {k : ℕ} (h : masterLine1Route W = k) :
    masterRouteIs masterLine1B masterLine1C₀ k (W, none) = true := decide_eq_true h

theorem masterRouteIs_false {k : ℕ} (h : masterLine1Route W ≠ k) :
    masterRouteIs masterLine1B masterLine1C₀ k (W, none) = false := decide_eq_false h

/-- **Section 15, line 1, on the RAM.** At a node without hint, the one line-1
carrier runs the step of Procedure Reduce-to-Johnson that the route test
selects, call for call, and returns the answer in the node's own frame. -/
theorem masterLine1_match {a b : ℕ} (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterLine1Ops masterLine1B masterLine1C₀ cameron)) (fun J => decWinSI n J.1)
      (decCoset n) (W, none) ((masterLine1Ops masterLine1B masterLine1C₀ cameron).width (W, none)) 0
      ((masterLine1Ops masterLine1B masterLine1C₀ cameron).init (W, none)) (masterLine1Tree hW hinv hc hs) := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  unfold masterLine1Tree masterLine1Case masterLine1Ops
  by_cases h0 : masterLine1Route W = 0
  · rw [dif_pos h0, if_pos (by omega)]
    refine masterOpsIte_start_pos a b (masterRouteIs_true h0) (masterLeafOps_match a b ?_)
    exact masterFixedStringCase_loop a b _ masterLine1B masterLine1C₀ hx hW.2.2.1 hW.1 hW.2.1
      hinv h0
  rw [dif_neg h0]
  refine masterOpsIte_start_neg a b (masterRouteIs_false h0) ?_
  by_cases h1 : masterLine1Route W = 1
  · rw [dif_pos h1, if_pos (by omega)]
    refine masterOpsIte_start_pos a b (masterRouteIs_true h1) (masterLeafOps_match a b ?_)
    exact masterSmallGroupCase_loop a b _ masterLine1B hx hW.2.2.1 hW.1 hW.2.1 hinv h1
  rw [dif_neg h1, if_neg (by omega)]
  refine masterOpsIte_start_neg a b (masterRouteIs_false h1) ?_
  by_cases h2 : masterLine1Route W = 2
  · rw [dif_pos h2]
    refine masterOpsIte_start_pos a b (masterRouteIs_true h2) ?_
    exact masterAdmittedRound_chain_match a b hW hinv h2 _ masterLine1_one_lt masterCamFoldEmbed
      rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl)
  rw [dif_neg h2]
  refine masterOpsIte_start_neg a b (masterRouteIs_false h2) ?_
  by_cases h3 : masterLine1Route W = 3
  · rw [dif_pos h3]
    exact masterOpsIte_start_pos a b (masterRouteIs_true h3)
      (masterStepFiveCase_loop hW hx hinv masterLine1_block_cutoff h3 a b)
  rw [dif_neg h3]
  refine masterOpsIte_start_neg a b (masterRouteIs_false h3) ?_
  exact masterCameronLine1Case_loop hx hW.2.2.1 hW.1 hW.2.1 hinv masterLine1_cameron_cutoff
    (masterLine1Route_four h0 h1 h2 h3) hc hs masterLine1_blocks hW hcap
end Case
end Algo
