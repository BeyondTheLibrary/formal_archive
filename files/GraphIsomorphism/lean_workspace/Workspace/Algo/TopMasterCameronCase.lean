import Workspace.Algo.TopMasterCameronStepSixMatch
import Workspace.Algo.TopMasterWindowRecognize
import Workspace.Algo.TopMasterReduceBounds

/-! # The Cameron route supplies the step-6 case of line 1
Section 11.3, step 6 applies when the group induced on the window is
transitive and its action on the minimal blocks is large. The machine's
route test says exactly this. The cited Cameron routine then returns the
Cameron structure of the block action (Theorem 11.2.1). This file turns
the route test and that output into the `Line1Case.descent` evidence of the
paper, and shows that the prepared Cameron carrier runs its coset branch.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The input of step 6 at a raw node: the Cameron structure the recognizer
returns on the computed block action, and the node's block input. -/
def masterCamRouteInput (cameron : RawGens × List ℕ → Option RawCameron)
    (P : RawMasterSI) : RawCameron × MasterDescInput :=
  ((cameron ((masterWindowBlockAction P.1).2.2, (masterWindowBlockAction P.1).2.1)).getD default,
    masterWindowBlockInput P.1)

theorem polyFun_masterCamRouteInput {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) : PolyFun (masterCamRouteInput cameron) := by
  have hin : PolyFun (fun P : RawMasterSI =>
      ((masterWindowBlockAction P.1).2.2, (masterWindowBlockAction P.1).2.1)) :=
    polyFun_fst.comp (((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_snd).pair
      ((polyFun_masterWindowBlockAction.comp polyFun_snd).comp polyFun_fst))
  have hget : PolyFun (fun P : RawMasterSI =>
      (cameron ((masterWindowBlockAction P.1).2.2, (masterWindowBlockAction P.1).2.1)).getD
        default) :=
    (((hin.comp hc).pair polyFun_id).comp
      (PolyFun.optionElim (polyFun_const default) polyFun_fst)).of_eq
        (fun P => by
          cases cameron ((masterWindowBlockAction P.1).2.2, (masterWindowBlockAction P.1).2.1) <;>
            rfl)
  exact hget.pair (polyFun_fst.comp polyFun_masterWindowBlockInput)

theorem masterCamRouteInput_source (cameron : RawGens × List ℕ → Option RawCameron)
    (P : RawMasterSI) : (masterCamRouteInput cameron P).2.1.2.2.2.1 = P.1.2.2.2.1 := rfl

section Route
variable {n B C₀ : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hC : (63).factorial < C₀) (hr : masterReduceRoute B C₀ W = 4)

include hw hnd hlt hinv hC hr in
/-- The route test of step 6 leaves a window of at least 64 points: the
small-group exit of step 2 was not taken. -/
theorem masterCamRoute_window : 64 ≤ W.1.length :=
  masterReduceRoute_large_window (N := 63) hw hnd hlt hinv hC (by rw [hr]; decide) (by rw [hr]; decide)

include hw hnd hlt hinv hr in
/-- The route test of step 6 includes the transitivity test of step 3. -/
theorem masterCamRoute_transitive :
    IsTransitive (decGroup W.1.length (primitiveWindowInput W).1) := by
  obtain ⟨_, _, ht, _, _⟩ := (masterReduceRoute_cameron B C₀ W).mp hr
  exact (rawIsTransitive_eq_true_iff (rawRestrictGens_wf_of_raw hw hnd hlt hinv) rfl).mp ht

include hw hnd hlt hinv hC hr in
theorem masterCamRoute_two : 2 ≤ W.1.length :=
  le_trans (by norm_num) (masterCamRoute_window hw hnd hlt hinv hC hr)

include hx hw hnd hlt hinv hC hr in
/-- The route test of step 6 bounds the number of blocks from below by `B`. -/
theorem masterCamRoute_blocks :
    B ≤ (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length := by
  obtain ⟨_, _, _, hm, _⟩ := (masterReduceRoute_cameron B C₀ W).mp hr
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv
    (masterCamRoute_transitive hw hnd hlt hinv hr) (masterCamRoute_two hw hnd hlt hinv hC hr)
  change B ≤ (masterWindowBlockAction W).2.1.length at hm
  rw [hp.2.1] at hm
  exact hm

include hx hw hnd hlt hinv hC hr in
/-- **Section 11.3, steps 5–6.** On the Cameron route the block action is
large: `m^{1 + log₂ m} ≤ |Ḡ|`, the negation of the test of step 5. -/
theorem masterCamRoute_order (hB : 1 ≤ B) :
    ((rawMinBlocks ((primitiveWindowInput W).1, W.1)).length : ℝ) ^
      (1 + Real.logb 2 (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length) ≤
      Nat.card (decGroup (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length
        (masterWindowBlockAction W).2.2) := by
  have hp := masterWindowBlockAction_wf hx hw hnd hlt hinv
    (masterCamRoute_transitive hw hnd hlt hinv hr) (masterCamRoute_two hw hnd hlt hinv hC hr)
  have ho := masterReduceRoute_cameron_order hx hw hnd hlt hinv
    (masterCamRoute_two hw hnd hlt hinv hC hr) hB hr
  change ((masterWindowBlockAction W).2.1.length : ℝ) ^
      (1 + Real.logb 2 (masterWindowBlockAction W).2.1.length) ≤
    Nat.card (decGroup (masterWindowBlockAction W).2.1.length (masterWindowBlockAction W).2.2) at ho
  rw [hp.2.1] at ho
  exact ho

variable {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) (hB : max 25 camDescentThreshold ≤ B)

include hx hw hnd hlt hinv hC hr hc hs hB in
/-- **Theorem 11.2.1 at the node, as computed.** On the Cameron route the
recognizer's output is a Cameron structure of the block action, with the
bounds of Definition 11.2.2 and the index bound `|Ḡ : N̄| ≤ m`. -/
theorem masterCamRoute_spec :
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
    ((le_trans (by norm_num) (le_max_left 25 camDescentThreshold)).trans hB)
  obtain ⟨c, h, he, _, hlo, hhi⟩ := hs _ _ _ hp.2.1 hp.2.2.2.1
    ((le_max_left _ _).trans hm) hprim hb
  obtain ⟨c', h', he', hidx, _⟩ := camRecognize_index cameron hc hs _ _ _
    hp.2.1 hp.2.2.2.1 ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) hprim hb
  have hec : c' = c := Option.some.inj (he'.symm.trans he)
  subst c'
  have hget : (masterCamRouteInput cameron (W, none)).1 = c := by
    change (cameron ((masterWindowBlockAction W).2.2, (masterWindowBlockAction W).2.1)).getD
      default = c
    rw [he]
    rfl
  rw [hget]
  exact ⟨h, hlo, hhi, hidx⟩

include hw hnd hlt hinv hC hr in
theorem masterCamRoute_windowSize : 64 ≤ (masterGroupInstance n W).windowSize := by
  change 64 ≤ (winSet n W.1).ncard
  rw [ncard_winSet W.1 hnd hlt]
  exact masterCamRoute_window hw hnd hlt hinv hC hr

/-- **§11.3, step 6, from the machine's route.** The live step-6 record at the
group frame of the node, built from the computed blocks, the computed Cameron
structure and the machine's coset and orbit lists. -/
noncomputable def masterCameronDescentData : DescentData (masterGroupInstance n W) :=
  masterCamDescentData hx hw hnd hlt hinv (masterCamRoute_transitive hw hnd hlt hinv hr)
    (masterCamRoute_two hw hnd hlt hinv hC hr)
    (masterCamRoute_spec hx hw hnd hlt hinv hC hr hc hs hB).choose
    (masterCamRoute_spec hx hw hnd hlt hinv hC hr hc hs hB).choose_spec.1
    (masterCamRoute_spec hx hw hnd hlt hinv hC hr hc hs hB).choose_spec.2.1
    (masterCamRoute_windowSize hw hnd hlt hinv hC hr)

/-- The index the step-6 case pays: `|K : K₁| = |Ḡ : N̄| ≤ m`. -/
theorem masterCameronDescentData_cost :
    (masterCameronDescentData hx hw hnd hlt hinv hC hr hc hs hB).K₁.relIndex
        (masterCameronDescentData hx hw hnd hlt hinv hC hr hc hs hB).blocks.K ≤
      (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length := by
  have H := masterCamRoute_spec hx hw hnd hlt hinv hC hr hc hs hB
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
noncomputable def masterCameronCase (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q) :
    Line1Case (masterGroupInstance n W) q :=
  .descent (masterCameronDescentData hx hw hnd hlt hinv hC hr hc hs hB)
    ((masterCameronDescentData_cost hx hw hnd hlt hinv hC hr hc hs hB).trans hq)

theorem masterCameronCase_cosetBranch (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q) :
    (masterCameronCase hx hw hnd hlt hinv hC hr hc hs hB q hq).cosetBranch =
      (masterCameronDescentData hx hw hnd hlt hinv hC hr hc hs hB).cosetBranch := rfl

include hx in
/-- **Section 15, line 1, step 6 on the RAM.** At a Cameron-route node, the
prepared Cameron carrier runs the coset branch of the paper's step-6 case in
the group frame of the node, followed by the shift back to its candidate
coset. -/
theorem masterCameronCase_loop {a b : ℕ} (q : ℕ)
    (hq : (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤ q)
    (hW : AggnCheckedWindowWF n W) (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps (masterCamRouteInput cameron)))
      (fun J => decWinSI n J.1) (decCoset n) (W, none)
      ((masterCamPreparedOps (masterCamRouteInput cameron)).width (W, none)) 0
      ((masterCamPreparedOps (masterCamRouteInput cameron)).init (W, none))
      ((masterCameronCase hx hw hnd hlt hinv hC hr hc hs hB q hq).cosetBranch.bind
        (fun A : Set (Perm (Fin n)) => .done (decPerm n W.2.2.1 • A))) := by
  have H := masterCamRoute_spec hx hw hnd hlt hinv hC hr hc hs hB
  exact masterCamPrepared_match_descent hx hw hnd hlt hinv
    (masterCamRoute_transitive hw hnd hlt hinv hr) (masterCamRoute_two hw hnd hlt hinv hC hr)
    H.choose H.choose_spec.1 H.choose_spec.2.1
    (masterCamRoute_windowSize hw hnd hlt hinv hC hr) hW H.choose_spec.2.2 hcap
    (masterCamRouteInput cameron) rfl
include hnd hlt in
/-- The number of blocks is within the line-1 allowance `line1Cost |Δ|` of
`Babai.Line1Choice`. -/
theorem masterCamRoute_line1Cost (hn : 1 ≤ W.1.length) :
    (rawMinBlocks ((primitiveWindowInput W).1, W.1)).length ≤
      line1Cost (masterGroupInstance n W).windowSize := by
  have hsize : (masterGroupInstance n W).windowSize = W.1.length := ncard_winSet W.1 hnd hlt
  rw [hsize]
  exact (blocksWF_rawMinBlocks (rfl : W.1.length = W.1.length) (primitiveWindowInput W).1).length_le.trans
    (self_le_line1Cost hn)

/-- The step-6 case at the allowance of `Babai.Line1Choice`. -/
noncomputable def masterCameronLine1Case :
    Line1Case (masterGroupInstance n W) (line1Cost (masterGroupInstance n W).windowSize) :=
  masterCameronCase hx hw hnd hlt hinv hC hr hc hs hB _
    (masterCamRoute_line1Cost hnd hlt
      ((by norm_num : 1 ≤ 64).trans (masterCamRoute_window hw hnd hlt hinv hC hr)))

include hx in
/-- **Section 15, line 1, step 6 on the RAM, at the allowance of `Babai.Line1Choice`.** -/
theorem masterCameronLine1Case_loop {a b : ℕ}
    (hW : AggnCheckedWindowWF n W) (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterCamPreparedOps (masterCamRouteInput cameron)))
      (fun J => decWinSI n J.1) (decCoset n) (W, none)
      ((masterCamPreparedOps (masterCamRouteInput cameron)).width (W, none)) 0
      ((masterCamPreparedOps (masterCamRouteInput cameron)).init (W, none))
      ((masterCameronLine1Case hx hw hnd hlt hinv hC hr hc hs hB).cosetBranch.bind
        (fun A : Set (Perm (Fin n)) => .done (decPerm n W.2.2.1 • A))) :=
  masterCameronCase_loop hx hw hnd hlt hinv hC hr hc hs hB _ _ hW hcap
end Route
end Algo
