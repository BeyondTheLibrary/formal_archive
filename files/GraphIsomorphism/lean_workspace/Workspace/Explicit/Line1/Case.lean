/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the line-1 threshold.
Not part of the faithful formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Explicit.Line1.Prop1125

/-!
# Line 1 at explicit thresholds

The route test of line 1 (`Algo.masterReduceRoute B C₀`) has two constants: `B`, the number
of blocks from which step 6 of Procedure Reduce-to-Johnson (Sec. 11.3) applies, and `C₀`,
the order cutoff of step 2. `Algo.theorem_1_1_1` runs it at `Algo.masterLine1B`,
`Algo.masterLine1C₀`, which are built from `Classical.choose`s (the thresholds of
Theorem 11.2.1 and Proposition 11.2.5) and have no known value.

The line-1 correctness proofs use only five facts about the two constants
(`Explicit.Line1OK`): `25 ≤ B` (the Cameron recognition step, through
`Explicit.camRecognize_indexX`), `1 < C₀`, `63! < C₀`, `(max 64 B!)! < C₀` and
`C₀ ≤ Babai.bruteForceOrderThreshold` (the order cutoff of the paper's step-2 case
`Babai.Line1Case.smallGroup`). The explicit constants are `B = 25` and
`C₀ = (max 64 25!)! + 1` (the paper's `C₀ = N₀! + 1` with `N₀ = max{64, n₀!}`, at `n₀ = 25`),
`Explicit.line1OK_X`.

This file copies the line-1 part of the correctness proofs from the fixed constants to any
constants with `Explicit.Line1OK` (each copy carries the name of its original with an `X`).
-/

set_option maxHeartbeats 1200000

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv
open scoped Pointwise

/-! ## The two constants -/

/-- What the line-1 correctness proofs use of the constants `B`, `C₀` of the route test. -/
structure Line1OK (B C₀ : ℕ) : Prop where
  b25 : 25 ≤ B
  one_lt : 1 < C₀
  cam : (63).factorial < C₀
  block : (max 64 B.factorial).factorial < C₀
  small : C₀ ≤ bruteForceOrderThreshold.{0}

/-- The explicit block threshold of line 1: `n₀ = 25`, the threshold of Theorem 11.2.3. -/
def line1BX : ℕ := 25

/-- The paper's `N₀ = max{64, n₀!}` (Sec. 11.3, steps 1–2) at `n₀ = 25`. It is irreducible:
its value `(25!)` must never be computed, and neither must `N₀!`. -/
irreducible_def line1N₀X : ℕ := max 64 (Nat.factorial 25)

/-- The explicit order cutoff of line 1: `C₀ = N₀! + 1` with `N₀ = max{64, 25!}`. -/
def line1C₀X : ℕ := line1N₀X.factorial + 1

theorem sixtyFour_le_line1N₀X : 64 ≤ line1N₀X := by
  rw [line1N₀X_def]; exact le_max_left _ _

theorem line1OK_X : Line1OK line1BX line1C₀X where
  b25 := le_rfl
  one_lt := Nat.succ_lt_succ (Nat.factorial_pos _)
  cam := Nat.lt_succ_of_le ((Nat.factorial_le (by norm_num : 63 ≤ 64)).trans
    (Nat.factorial_le sixtyFour_le_line1N₀X))
  block := by
    have h : max 64 (Nat.factorial line1BX) = line1N₀X := by
      rw [line1N₀X_def]; rfl
    rw [h]
    exact Nat.lt_succ_self _
  small := by
    unfold line1C₀X bruteForceOrderThreshold bruteForceThreshold
    have h25 : 25 ≤ descentThreshold.{0} :=
      (le_max_left 25 _).trans (le_max_right _ _)
    have h : line1N₀X ≤ max 64 (Nat.factorial descentThreshold.{0}) := by
      rw [line1N₀X_def]
      exact max_le_max le_rfl (Nat.factorial_le h25)
    exact Nat.add_le_add_right (Nat.factorial_le h) 1

/-! ## Step 6 at `B ≥ 25` -/

section Route
variable {n B C₀ : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : (63).factorial < C₀) (hr : masterReduceRoute B C₀ W = 4)

variable {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hB : 25 ≤ B)

include hx hw hnd hlt hinv hC hr hc hs hB in
/-- **Theorem 11.2.1 at the node, as computed.** On the Cameron route the
recognizer's output is a Cameron structure of the block action, with the
bounds of Definition 11.2.2 and the index bound `|Ḡ : N̄| ≤ m`. -/
theorem masterCamRoute_specX :
    ∃ h : (masterCamRouteInput cameron (W, none)).1.WF
        (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length,
      basePower (JohnsonA (masterCamRouteInput cameron (W, none)).1.k
          (masterCamRouteInput cameron (W, none)).1.t)
          (masterCamRouteInput cameron (W, none)).1.s ≤
        (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
          (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron _ h)).toMonoidHom ∧
      (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
          (masterWindowBlockAction W).2.2).map (permCongrHom (decCameron _ h)).toMonoidHom ≤
        wreathProduct (JohnsonS (masterCamRouteInput cameron (W, none)).1.k
          (masterCamRouteInput cameron (W, none)).1.t) (masterCamRouteInput cameron (W, none)).1.s ∧
      (camNbar _ h).relIndex (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
          (masterWindowBlockAction W).2.2) ≤
        (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length := by
  have htr := masterCamRoute_transitive hw hnd hlt hinv hr
  have hn := masterCamRoute_two hw hnd hlt hinv hC hr
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hprim := masterWindowBlockAction_primitive hw hnd hlt hinv htr hn
  have hm := hB.trans (masterCamRoute_blocks hx hw hnd hlt hinv hC hr)
  have hb := masterCamRoute_order hx hw hnd hlt hinv hC hr
    (le_trans (by norm_num) hB)
  obtain ⟨c, h, he, _, hlo, hhi⟩ := hs _ _ _ hp.2.1 hp.2.2.2.1
    hm hprim hb
  obtain ⟨c', h', he', hidx, _⟩ := camRecognize_indexX cameron hc hs _ _ _
    hp.2.1 hp.2.2.2.1 hm hprim hb
  have hec : c' = c := Option.some.inj (he'.symm.trans he)
  subst c'
  have hget : (masterCamRouteInput cameron (W, none)).1 = c := by
    change (cameron ((masterWindowBlockAction W).2.2, (masterWindowBlockAction W).2.1)).getD
      default = c
    rw [he]
    rfl
  rw [hget]
  exact ⟨h, hlo, hhi, hidx⟩

/-- **§11.3, step 6, from the machine's route.** The live step-6 record at the
group frame of the node, built from the computed blocks, the computed Cameron
structure and the machine's coset and orbit lists. -/
noncomputable def masterCameronDescentDataX : DescentData (masterGroupInstance n W) :=
  masterCamDescentData hx hw hnd hlt hinv (masterCamRoute_transitive hw hnd hlt hinv hr)
    (masterCamRoute_two hw hnd hlt hinv hC hr)
    (masterCamRoute_specX hx hw hnd hlt hinv hC hr hc hs hB).choose
    (masterCamRoute_specX hx hw hnd hlt hinv hC hr hc hs hB).choose_spec.1
    (masterCamRoute_specX hx hw hnd hlt hinv hC hr hc hs hB).choose_spec.2.1
    (masterCamRoute_windowSize hw hnd hlt hinv hC hr)

/-- The index the step-6 case pays: `|K : K₁| = |Ḡ : N̄| ≤ m`. -/
theorem masterCameronDescentData_costX :
    (masterCameronDescentDataX hx hw hnd hlt hinv hC hr hc hs hB).K₁.relIndex
        (masterCameronDescentDataX hx hw hnd hlt hinv hC hr hc hs hB).blocks.K ≤
      (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length := by
  have H := masterCamRoute_specX hx hw hnd hlt hinv hC hr hc hs hB
  have htr := masterCamRoute_transitive hw hnd hlt hinv hr
  have hn := masterCamRoute_two hw hnd hlt hinv hC hr
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv htr hn
  have hK := masterCamDescentData_K₁ hx hw hnd hlt hinv htr hn H.choose H.choose_spec.1
    H.choose_spec.2.1 (masterCamRoute_windowSize hw hnd hlt hinv hC hr)
  change (masterCamDescentData hx hw hnd hlt hinv htr hn H.choose H.choose_spec.1
    H.choose_spec.2.1 (masterCamRoute_windowSize hw hnd hlt hinv hC hr)).K₁.relIndex
      (decGroup n W.2.1) ≤ _
  rw [hK]
  change (decGroup n (camLiftGens (_, masterWindowBlockAction W))).relIndex
    (decGroup n (masterWindowBlockAction W).1.2) ≤ _
  rw [camLiftGens_index hp H.choose H.choose_spec.2.1]
  exact H.choose_spec.2.2

/-- **Section 15, line 1, step 6 from the machine's route.** The paper's
`Line1Case.descent` evidence at the group frame of the node, for any cost
allowance `q` at least the number of blocks. -/
noncomputable def masterCameronCaseX (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q) :
    Line1Case (masterGroupInstance n W) q :=
  .descent (masterCameronDescentDataX hx hw hnd hlt hinv hC hr hc hs hB)
    ((masterCameronDescentData_costX hx hw hnd hlt hinv hC hr hc hs hB).trans hq)

theorem masterCameronCase_cosetBranchX (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q) :
    (masterCameronCaseX hx hw hnd hlt hinv hC hr hc hs hB q hq).cosetBranch =
      (masterCameronDescentDataX hx hw hnd hlt hinv hC hr hc hs hB).cosetBranch := rfl

include hx in
/-- **Section 15, line 1, step 6 on the RAM.** At a Cameron-route node, the
prepared Cameron carrier runs the coset branch of the paper's step-6 case in
the group frame of the node, followed by the shift back to its candidate
coset. -/
theorem masterCameronCase_loopX {a b : ℕ} (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q)
    (hW : AggnCheckedWindowWF n W) (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps (masterCamRouteInput cameron)))
      (fun J => decWinSI n J.1) (decCoset n) (W, none)
      ((masterCamPreparedOps (masterCamRouteInput cameron)).width (W, none)) 0
      ((masterCamPreparedOps (masterCamRouteInput cameron)).init (W, none))
      ((masterCameronCaseX hx hw hnd hlt hinv hC hr hc hs hB q hq).cosetBranch.bind
        (fun A : Set (Perm (Fin n)) => .done (decPerm n W.2.2.1 • A))) := by
  have H := masterCamRoute_specX hx hw hnd hlt hinv hC hr hc hs hB
  exact masterCamPrepared_match_descent hx hw hnd hlt hinv
    (masterCamRoute_transitive hw hnd hlt hinv hr) (masterCamRoute_two hw hnd hlt hinv hC hr)
    H.choose H.choose_spec.1 H.choose_spec.2.1
    (masterCamRoute_windowSize hw hnd hlt hinv hC hr) hW H.choose_spec.2.2 hcap
    (masterCamRouteInput cameron) rfl

/-- The step-6 case at the allowance of `Babai.Line1Choice`. -/
noncomputable def masterCameronLine1CaseX :
    Line1Case (masterGroupInstance n W) (line1Cost (masterGroupInstance n W).windowSize) :=
  masterCameronCaseX hx hw hnd hlt hinv hC hr hc hs hB _
    (masterCamRoute_line1Cost hnd hlt
      ((by norm_num : 1 ≤ 64).trans (masterCamRoute_window hw hnd hlt hinv hC hr)))

include hx in
/-- **Section 15, line 1, step 6 on the RAM, at the allowance of `Babai.Line1Choice`.** -/
theorem masterCameronLine1Case_loopX {a b : ℕ}
    (hW : AggnCheckedWindowWF n W) (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps (masterCamRouteInput cameron)))
      (fun J => decWinSI n J.1) (decCoset n) (W, none)
      ((masterCamPreparedOps (masterCamRouteInput cameron)).width (W, none)) 0
      ((masterCamPreparedOps (masterCamRouteInput cameron)).init (W, none))
      ((masterCameronLine1CaseX hx hw hnd hlt hinv hC hr hc hs hB).cosetBranch.bind
        (fun A : Set (Perm (Fin n)) => .done (decPerm n W.2.2.1 • A))) :=
  masterCameronCase_loopX hx hw hnd hlt hinv hC hr hc hs hB _ _ hW hcap
end Route
/-! ## Step 2 at the cutoff `C₀` -/

/-- `Algo.masterSmallGroupCase` at the cutoff `C₀ ≤ Babai.bruteForceOrderThreshold`. -/
noncomputable def masterSmallGroupCaseX {n : ℕ} {W : RawWinSI} (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) (q B C₀ : ℕ)
    (hC : C₀ ≤ bruteForceOrderThreshold.{0}) (hr : masterReduceRoute B C₀ W = 1) :
    Line1Case (masterGroupInstance n W) q := by
  apply Line1Case.smallGroup (masterGroupData hinv)
  rw [masterGroupData_card hw hnd hlt hinv]
  obtain ⟨_, ho⟩ := (masterReduceRoute_brute B C₀ W).mp hr
  have hgs : RawGens.WF W.1.length (primitiveWindowInput W).1 :=
    rawRestrictGens_wf_of_raw hw hnd hlt hinv
  have he := rawOrder_spec W.1 rfl ((primitiveWindowInput W).1.map (decPerm W.1.length))
  rw [map_encPerm_decPerm hgs] at he
  change rawOrder (W.1, (primitiveWindowInput W).1) < _ at ho
  rw [he] at ho
  exact lt_of_lt_of_le ho hC

/-- `Algo.masterSmallGroupCase_loop` at the cutoff `C₀`. -/
theorem masterSmallGroupCase_loopX (a b q B C₀ : ℕ) {n : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : C₀ ≤ bruteForceOrderThreshold.{0}) (hr : masterReduceRoute B C₀ W = 1) :
    LoopMatch (masterLeafRound a b (masterWindowBruteLeaf C₀))
      (decWinSI n) (decCoset n) W 0 0 0
      ((masterSmallGroupCaseX hw hnd hlt hinv q B C₀ hC hr).branch.bind
        (fun A => .done (decPerm n W.2.2.1 • A))) :=
  .done 0 0 0 _ rfl ((masterWindowBruteLeaf_spec hx hw hnd hlt hinv hr).trans
    (masterGroupInstance_answer hx).symm)

/-! ## The case, the tree and the match of line 1 -/

theorem masterReduceRoute_fourX {B C₀ : ℕ} {W : RawWinSI} (h0 : masterReduceRoute B C₀ W ≠ 0)
    (h1 : masterReduceRoute B C₀ W ≠ 1) (h2 : masterReduceRoute B C₀ W ≠ 2)
    (h3 : masterReduceRoute B C₀ W ≠ 3) : masterReduceRoute B C₀ W = 4 := by
  have := masterReduceRoute_le_four B C₀ W
  omega

theorem masterRouteIs_trueX {B C₀ k : ℕ} {W : RawWinSI} (h : masterReduceRoute B C₀ W = k) :
    masterRouteIs B C₀ k (W, none) = true := decide_eq_true h

theorem masterRouteIs_falseX {B C₀ k : ℕ} {W : RawWinSI} (h : masterReduceRoute B C₀ W ≠ k) :
    masterRouteIs B C₀ k (W, none) = false := decide_eq_false h

section Case
variable {n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {B C₀ : ℕ} (hL : Line1OK B C₀)

/-- `Algo.masterLine1Case` at constants with `Explicit.Line1OK`. -/
noncomputable def masterLine1CaseX :
    Line1Case (masterGroupInstance n W) (line1Cost (masterGroupInstance n W).windowSize) :=
  if h0 : masterReduceRoute B C₀ W = 0 then
    masterFixedStringCase hW.2.2.1 hW.1 hW.2.1 hinv _ B C₀ h0
  else if h1 : masterReduceRoute B C₀ W = 1 then
    masterSmallGroupCaseX hW.2.2.1 hW.1 hW.2.1 hinv _ B C₀ hL.small h1
  else if h2 : masterReduceRoute B C₀ W = 2 then
    masterChainCase hW.2.2.1 hW.1 hW.2.1 hinv h2 _ hL.one_lt
  else if h3 : masterReduceRoute B C₀ W = 3 then
    masterStepFiveCase hW hW.2.2.2.2.2.1.1 hinv hL.block h3
  else
    masterCameronLine1CaseX hW.2.2.2.2.2.1.1 hW.2.2.1 hW.1 hW.2.1 hinv hL.cam
      (masterReduceRoute_fourX h0 h1 h2 h3) hc hs hL.b25

/-- `Algo.masterLine1Tree` at constants with `Explicit.Line1OK`. -/
noncomputable def masterLine1TreeX : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  if masterReduceRoute B C₀ W ≤ 1 then
    (masterLine1CaseX hW hinv hc hs hL).branch.bind (masterNodeShift n W)
  else (masterLine1CaseX hW hinv hc hs hL).cosetBranch.bind (masterNodeShift n W)

/-- `Algo.masterLine1_match` at constants with `Explicit.Line1OK`. -/
theorem masterLine1_matchX {a b : ℕ}
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterLine1Ops B C₀ cameron)) (fun J => decWinSI n J.1)
      (decCoset n) (W, none) ((masterLine1Ops B C₀ cameron).width (W, none)) 0
      ((masterLine1Ops B C₀ cameron).init (W, none)) (masterLine1TreeX hW hinv hc hs hL) := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  unfold masterLine1TreeX masterLine1CaseX masterLine1Ops
  by_cases h0 : masterReduceRoute B C₀ W = 0
  · rw [dif_pos h0, if_pos (by omega)]
    refine masterOpsIte_start_pos a b (masterRouteIs_trueX h0) (masterLeafOps_match a b ?_)
    exact masterFixedStringCase_loop a b _ B C₀ hx hW.2.2.1 hW.1 hW.2.1 hinv h0
  rw [dif_neg h0]
  refine masterOpsIte_start_neg a b (masterRouteIs_falseX h0) ?_
  by_cases h1 : masterReduceRoute B C₀ W = 1
  · rw [dif_pos h1, if_pos (by omega)]
    refine masterOpsIte_start_pos a b (masterRouteIs_trueX h1) (masterLeafOps_match a b ?_)
    exact masterSmallGroupCase_loopX a b _ B C₀ hx hW.2.2.1 hW.1 hW.2.1 hinv hL.small h1
  rw [dif_neg h1, if_neg (by omega)]
  refine masterOpsIte_start_neg a b (masterRouteIs_falseX h1) ?_
  by_cases h2 : masterReduceRoute B C₀ W = 2
  · rw [dif_pos h2]
    refine masterOpsIte_start_pos a b (masterRouteIs_trueX h2) ?_
    exact masterAdmittedRound_chain_match a b hW hinv h2 _ hL.one_lt masterCamFoldEmbed
      rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl)
  rw [dif_neg h2]
  refine masterOpsIte_start_neg a b (masterRouteIs_falseX h2) ?_
  by_cases h3 : masterReduceRoute B C₀ W = 3
  · rw [dif_pos h3]
    exact masterOpsIte_start_pos a b (masterRouteIs_trueX h3)
      (masterStepFiveCase_loop hW hx hinv hL.block h3 a b)
  rw [dif_neg h3]
  refine masterOpsIte_start_neg a b (masterRouteIs_falseX h3) ?_
  exact masterCameronLine1Case_loopX hx hW.2.2.1 hW.1 hW.2.1 hinv hL.cam
    (masterReduceRoute_fourX h0 h1 h2 h3) hc hs hL.b25 hW hcap

/-- `Algo.masterTop_line1_match` at constants with `Explicit.Line1OK`. -/
theorem masterTop_line1_matchX {a b : ℕ} {T : Type} (H : MasterOps T) (dT : T)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterTopOps B C₀ cameron H dT))
      (fun J => decWinSI n J.1) (decCoset n) (W, none)
      ((masterTopOps B C₀ cameron H dT).width (W, none)) 0
      ((masterTopOps B C₀ cameron H dT).init (W, none)) (masterLine1TreeX hW hinv hc hs hL) :=
  masterPairIte_start_pos a b ((masterIsLine1_iff _).mpr rfl)
    (masterLine1_matchX hW hinv hc hs hL hcap)

include hW in
/-- `Algo.masterLine1Tree_run` at constants with `Explicit.Line1OK`. -/
theorem masterLine1Tree_runX :
    (masterLine1TreeX hW hinv hc hs hL).run = (decWinSI n W).answer := by
  have hx : W.2.2.2.1.length = n := hW.2.2.2.2.2.1.1
  have hc' := (masterLine1CaseX hW hinv hc hs hL).run_branch
  have hcos : (masterLine1CaseX hW hinv hc hs hL).cosetBranch.run =
      (masterGroupInstance n W).answer := by
    have h1 : (1 : Perm (Fin n)) ∈ (masterGroupInstance n W).K :=
      (decGroup n W.2.1).one_mem
    rw [← run_alignRed_of_one_mem h1, ← Line1Case.branch_eq_alignRed]
    exact hc'
  unfold masterLine1TreeX
  split_ifs
  · rw [SIReduction.run_bind, hc']
    exact masterGroupInstance_answer hx
  · rw [SIReduction.run_bind, hcos]
    exact masterGroupInstance_answer hx

/-- `Algo.masterLine1Tree_calls_length` at constants with `Explicit.Line1OK`. -/
theorem masterLine1Tree_calls_lengthX :
    (masterLine1TreeX hW hinv hc hs hL).calls.length ≤
      line1RoundCost (decWinSI n W).windowSize := by
  have hb := (masterLine1CaseX hW hinv hc hs hL).calls_length_branch
  have hcb : (masterLine1CaseX hW hinv hc hs hL).cosetBranch.calls.length =
      (masterLine1CaseX hW hinv hc hs hL).branch.calls.length := by
    rw [Line1Case.branch_eq_alignRed, calls_length_alignRed]
  unfold masterLine1TreeX
  split_ifs
  · simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
    exact hb
  · simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
    rw [hcb]
    exact hb

include hW in
/-- `Algo.masterLine1Tree_chain` at constants with `Explicit.Line1OK`. -/
theorem masterLine1Tree_chainX (h2 : masterReduceRoute B C₀ W = 2) :
    1 ≤ (decWinSI n W).windowSize ∧
      ((masterLine1TreeX hW hinv hc hs hL).calls.map SIInstance.windowSize).sum ≤
        (decWinSI n W).windowSize := by
  have h0 : masterReduceRoute B C₀ W ≠ 0 := by omega
  have h1 : masterReduceRoute B C₀ W ≠ 1 := by omega
  unfold masterLine1TreeX masterLine1CaseX
  rw [if_neg (by omega), dif_neg h0, dif_neg h1, dif_pos h2]
  simp only [SIReduction.calls_bind, masterNodeShift, SIReduction.calls_done, List.append_nil]
  obtain ⟨hn, -, hsum⟩ := decreases_chainRuleBranch (masterChainData hW.2.2.1 hW.2.1 hinv)
    ⟨_, (masterChainRoute_nonempty hW.2.2.1 hW.1 hW.2.1 hinv h2 hL.one_lt).choose_spec⟩
    (masterChainRoute_intransitive hW.2.2.1 hW.1 hW.2.1 hinv h2)
  rw [List.map_map] at hsum
  have hf : (HintedInstance.win ∘ fun J : SIInstance (Fin n) ℕ =>
      (⟨J, none⟩ : HintedInstance (Fin n) ℕ)) = SIInstance.windowSize := rfl
  rw [hf] at hsum
  refine ⟨hn, ?_⟩
  have e := sum_windowSize_calls_alignRed (masterGroupInstance n W)
    (masterChainCase hW.2.2.1 hW.1 hW.2.1 hinv h2 (line1Cost (masterGroupInstance n W).windowSize)
      hL.one_lt).cosetBranch
  rw [← e]
  exact hsum

end Case

end Explicit
