/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the cost data of a round whose well-formedness test is only sound.
-/
import Workspace.Algo.RoundQ

/-!
# A round whose well-formedness test is only sound

`Algo.Round.RunCostQ` (`Workspace/Algo/RoundQ.lean`) asks for a routine `wfCheck` with

```
wfCheck I = true ↔ R.WF I
```

at **every** instance.  The master round of Sec. 15 cannot supply that.  Its nodes carry
facts that are not properties of the raw node alone: the stored index of a descent node is a
subgroup index, the action data of a local-certificate node is required to extend to a
homomorphism, a child of a top-action node is required to be a window instance the parent
built.  `Workspace/Algo/WFTestsSI.lean` goes through these clause by clause.  None of them is
decided by a polynomial routine reading the node, so the `←` direction of the `↔` is out of
reach.

**What the packaging really needs.**  Read where each direction is used.

* `→` (*soundness*, `wfCheck I = true → R.WF I`) is used, in contrapositive form, in
  `Algo.Round.size_iterateQ_le` and `Algo.Round.size_runQ_le`: on an instance that is *not*
  well formed the test must say `false`, so that the loop is not entered and the size bounds
  hold on **all** inputs, junk included.
* `←` (*completeness*, `R.WF I → wfCheck I = true`) is used in exactly one place,
  `Algo.Round.runQ_eq_evaluate`, to know that the loop *is* entered on a well-formed
  instance.  Everything downstream of it — `Algo.Round.runQ_eq_answer` — inherits it from
  there.

So completeness is needed only at the instances the final theorem actually feeds the round,
and there it is available as a hypothesis: the root is `Algo.rawNormSI (Algo.rawOfSI a)`, and
`Algo.wftRootCheck_rawNormSI_rawOfSI` says that it passes the test.

This file therefore repeats `Algo.Round.RunCostQ` with the `↔` replaced by the `→`, and
carries the invariant of `Workspace/Algo/RoundQ.lean` across.  Nothing else changes: the size
invariant never mentions the test, so its proofs are the proofs of
`Workspace/Algo/RoundQ.lean` word for word.

## Main definitions

* `Algo.Round.RunCostQS` — the cost data with a **sound** test;
* `Algo.Round.stepCountQS`, `Algo.Round.runQS` — the evaluator as a total function;
* `Algo.Round.FrameOkQS`, `Algo.Round.RetOkQS`, `Algo.Round.StateOkQS` — the size invariant.

## Main results

* `Algo.Round.RunCostQ.toRunCostQS` — a complete test is in particular a sound one;
* `Algo.Round.runQS_eq_evaluate` — **under the hypothesis that the root passes the test**;
* `Algo.Round.stateOkQS_iterate`, `Algo.Round.size_stateQS_le`, `Algo.Round.retOkQS_le`.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

/-! ## The cost data -/

/-- **The cost data of a round whose well-formedness test is only sound.**

Field for field `Algo.Round.RunCostQ`, with `wfCheck_eq_true` replaced by `wfCheck_sound`.
A test that says `true` on a junk instance would break the size bounds, because the loop
would be entered on an instance no bound covers; a test that says `false` on a well-formed
instance only makes the routine answer `none` there, which the correctness statement
excludes by hypothesis. -/
structure RunCostQS [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α) extends CostQ R where
  /-- The domain size is read off the raw instance by a routine. -/
  polyFun_ground : PolyFun R.ground
  /-- A test for well-formedness. -/
  wfCheck : ι → Bool
  polyFun_wfCheck : PolyFun wfCheck
  /-- **The test is sound**: what it accepts is well formed.  It need not accept everything
  that is well formed. -/
  wfCheck_sound : ∀ I, wfCheck I = true → R.WF I
  /-- A bound on the measure, hence on the depth of the stack. -/
  measureBound : ℕ → ℕ
  polyBound_measureBound : PolyBound measureBound
  mono_measureBound : Monotone measureBound
  measure_le : ∀ I, R.WF I → R.measure I ≤ measureBound (R.ground I)

variable [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

/-- **A complete test is a sound one.**  So every round already packaged with
`Algo.Round.RunCostQ` is packaged with the weaker interface as well, and nothing already
built has to be redone. -/
def RunCostQ.toRunCostQS {R : Round ι ω α} (C : RunCostQ R) : RunCostQS R where
  toCostQ := C.toCostQ
  polyFun_ground := C.polyFun_ground
  wfCheck := C.wfCheck
  polyFun_wfCheck := C.polyFun_wfCheck
  wfCheck_sound := fun I h => (C.wfCheck_eq_true I).1 h
  measureBound := C.measureBound
  polyBound_measureBound := C.polyBound_measureBound
  mono_measureBound := C.mono_measureBound
  measure_le := C.measure_le

/-! ## The evaluator as a total function -/

/-- The number of steps the machine runs: the round count on an instance that passes the
test, and none at all on one that fails it. -/
def stepCountQS (R : Round ι ω α) (C : RunCostQS R) (c : ℕ) (I : ι) : ℕ :=
  if C.wfCheck I then roundCount c (R.ground I) else 0

/-- **The evaluator as a total function of a raw instance.** -/
def runQS (R : Round ι ω α) (C : RunCostQS R) (c : ℕ) (I : ι) : Option α :=
  ((R.stepDFS)^[R.stepCountQS C c I] (R.startState I)).2

/-- **On an instance that passes the test** the routine is the evaluator of
`Workspace/Algo/Evaluator.lean`, run for `Algo.Round.roundCount` steps.  Against
`Algo.Round.runQ_eq_evaluate` the hypothesis `R.WF I` has become `C.wfCheck I = true`, which
is the stronger of the two: soundness gives `R.WF I` back. -/
theorem runQS_eq_evaluate (C : RunCostQS R) (c : ℕ) (I : ι) (hI : C.wfCheck I = true) :
    R.runQS C c I = R.evaluate (roundCount c (R.ground I)) I := by
  rw [runQS, stepCountQS, if_pos hI, evaluate_eq_iterate]

/-- The step count vanishes on an instance that fails the test. -/
theorem stepCountQS_of_check_false (C : RunCostQS R) (c : ℕ) (I : ι)
    (hI : C.wfCheck I = false) : R.stepCountQS C c I = 0 := by
  rw [stepCountQS, if_neg (by simp [hI])]

/-! ## The size invariant

The three clauses of `Algo.Round.StateOkQ`, repeated.  They do not mention the test, and
neither do their proofs; only the two statements that convert a step count use it, and both
are below. -/

/-- A frame of a reachable stack, at step `t` of a run on a domain of size at most `n`. -/
def FrameOkQS (R : Round ι ω α) (C : RunCostQS R) (n t : ℕ) (fr : Frame ι ω) : Prop :=
  R.WF fr.1 ∧ R.ground fr.1 ≤ n ∧ Enc.size fr.2.2 ≤ C.stateBound (R.ground fr.1) ∧ fr.2.1 ≤ t

/-- The register of a reachable state. -/
def RetOkQS (R : Round ι ω α) (C : RunCostQS R) (n : ℕ) (st : List (Frame ι ω))
    (ret : Option α) : Prop :=
  ∀ a, ret = some a →
    Enc.size a ≤ C.bound (match st with | [] => n | fr :: _ => R.ground fr.1)

/-- The invariant of a reachable state. -/
def StateOkQS (R : Round ι ω α) (C : RunCostQS R) (n t : ℕ) (x : EvalState ι ω α) : Prop :=
  (∀ fr ∈ x.1, R.FrameOkQS C n t fr) ∧ R.RetOkQS C n x.1 x.2

/-- **The answer in the register is polynomially small for the root as well.** -/
theorem retOkQS_le (C : RunCostQS R) (n t : ℕ) (x : EvalState ι ω α)
    (h : R.StateOkQS C n t x) (a : α) (ha : x.2 = some a) : Enc.size a ≤ C.bound n := by
  have h2 := h.2 a ha
  cases hst : x.1 with
  | nil => rw [hst] at h2; exact h2
  | cons fr rest =>
    rw [hst] at h2
    have hfr : R.FrameOkQS C n t fr := h.1 fr (by rw [hst]; exact List.mem_cons_self ..)
    exact le_trans h2 (C.mono_bound hfr.2.1)

/-- **The invariant is preserved by one step.** -/
theorem stateOkQS_stepDFS (C : RunCostQS R) (n t : ℕ) (x : EvalState ι ω α)
    (hstack : R.StackOk x.1) (h : R.StateOkQS C n t x) :
    R.StateOkQS C n (t + 1) (R.stepDFS x) := by
  obtain ⟨st, ret⟩ := x
  obtain ⟨hfr, hret⟩ := h
  have hbump : ∀ fr : Frame ι ω, R.FrameOkQS C n t fr → R.FrameOkQS C n (t + 1) fr :=
    fun fr hf => ⟨hf.1, hf.2.1, hf.2.2.1, Nat.le_succ_of_le hf.2.2.2⟩
  cases st with
  | nil =>
    refine ⟨fun fr hfr' => absurd hfr' (by simp), fun a ha => ?_⟩
    exact hret a ha
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    have hI0 : R.FrameOkQS C n t (I, j, s) := hfr (I, j, s) (List.mem_cons_self ..)
    have hIwf : R.WF I := hI0.1
    cases ret with
    | some a =>
      have hsize : Enc.size a ≤ C.bound (R.ground I) := hret a rfl
      rw [R.stepDFS_some]
      refine ⟨fun fr' hfr' => ?_, fun b hb => absurd hb (by simp)⟩
      rcases List.mem_cons.1 hfr' with rfl | hmem
      · exact ⟨hIwf, hI0.2.1, C.combine_le I j s a hIwf hI0.2.2.1 hsize,
          Nat.succ_le_succ hI0.2.2.2⟩
      · exact hbump fr' (hfr fr' (List.mem_cons_of_mem _ hmem))
    | none =>
      cases hc : R.child (I, j, s) with
      | some J =>
        rw [R.stepDFS_push rest hc]
        refine ⟨fun fr' hfr' => ?_, fun b hb => absurd hb (by simp)⟩
        rcases List.mem_cons.1 hfr' with rfl | hmem
        · exact ⟨R.child_wf I j s J hIwf hc,
            le_trans (R.child_ground I j s J hIwf hc) hI0.2.1,
            C.init_le J (R.child_wf I j s J hIwf hc), Nat.zero_le _⟩
        · exact hbump fr' (hfr fr' hmem)
      | none =>
        rw [R.stepDFS_pop rest hc]
        refine ⟨fun fr' hfr' => ?_, fun b hb => ?_⟩
        · exact hbump fr' (hfr fr' (List.mem_cons_of_mem _ hfr'))
        · have hb' : b = R.finish (I, s) := by simpa using hb.symm
          subst hb'
          have hfin : Enc.size (R.finish (I, s)) ≤ C.bound (R.ground I) :=
            C.finish_le I s hIwf hI0.2.2.1
          cases rest with
          | nil => exact le_trans hfin (C.mono_bound hI0.2.1)
          | cons fr' rest' =>
            exact le_trans hfin (C.mono_bound hstack.2.2.1)

/-- The stack the run starts from satisfies the invariant. -/
theorem stateOkQS_start (C : RunCostQS R) (I : ι) (hI : R.WF I) :
    R.StateOkQS C (R.ground I) 0 (R.startState I) := by
  refine ⟨fun fr hfr => ?_, fun a ha => absurd ha (by simp [startState])⟩
  rw [startState] at hfr
  have : fr = (I, 0, R.init I) := by simpa using hfr
  subst this
  exact ⟨hI, le_refl _, C.init_le I hI, le_refl _⟩

/-- **The invariant holds along the whole run.** -/
theorem stateOkQS_iterate (C : RunCostQS R) (I : ι) (hI : R.WF I) (t : ℕ) :
    R.StateOkQS C (R.ground I) t ((R.stepDFS)^[t] (R.startState I)) := by
  induction t with
  | zero => exact R.stateOkQS_start C I hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.stateOkQS_stepDFS C _ t _ (R.stackOk_iterate hI t) ih

/-! ### From the invariant to the size of the encoding -/

/-- A frame of a reachable stack is quasipolynomially small. -/
theorem size_frameQS_le (C : RunCostQS R) (n t : ℕ) (fr : Frame ι ω)
    (h : R.FrameOkQS C n t fr) :
    Enc.size fr ≤ 2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8 := by
  obtain ⟨I, j, s⟩ := fr
  obtain ⟨hwf, hg, hs, hj⟩ := h
  have h1 : Enc.size ((I, j, s) : Frame ι ω)
      ≤ 2 * Enc.size I + 2 * Enc.size ((j, s) : ℕ × ω) := Combine.size_pair_le _ _
  have h2 : Enc.size ((j, s) : ℕ × ω) ≤ 2 * Enc.size j + 2 * Enc.size s :=
    Combine.size_pair_le _ _
  have h3 : Enc.size I ≤ C.bound n := le_trans (C.size_le I hwf) (C.mono_bound hg)
  have h4 : Enc.size s ≤ C.stateBound n := le_trans hs (C.mono_stateBound hg)
  have h5 : Enc.size j = Nat.size j + 2 := Small.size_nat j
  have h6 : Nat.size j ≤ Nat.size t := Nat.size_le_size hj
  omega

/-- **A reachable state is quasipolynomially small.** -/
theorem size_stateQS_le (C : RunCostQS R) (n t D : ℕ) (x : EvalState ι ω α)
    (h : R.StateOkQS C n t x) (hD : x.1.length ≤ D) :
    Enc.size x ≤ 2 * (1 + D * (2 * (2 * C.bound n + 4 * C.stateBound n
        + 4 * Nat.size t + 8) + 1)) + 2 * (C.bound n + 2) := by
  have h1 : Enc.size x ≤ 2 * Enc.size x.1 + 2 * Enc.size x.2 := by
    have := Combine.size_pair_le x.1 x.2
    simpa using this
  have h2 : Enc.size x.1 ≤ 1 + x.1.length
      * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1) :=
    size_list_le_of_entries x.1 _ (fun fr hfr => R.size_frameQS_le C n t fr (h.1 fr hfr))
  have h3 : x.1.length * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1)
      ≤ D * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1) :=
    Nat.mul_le_mul_right _ hD
  have h4 : Enc.size x.2 ≤ C.bound n + 2 := by
    cases hx : x.2 with
    | none => rw [size_none_eq]; omega
    | some a =>
      rw [size_some_eq]
      have := R.retOkQS_le C n t x h a hx
      omega
  omega

/-! ## The interface is satisfiable

The test round of `Workspace/Algo/EvaluatorRAM.lean`, through
`Algo.Round.RunCostQ.toRunCostQS`. -/

/-- **`Algo.Round.RunCostQS` is satisfiable**, on a round with a genuine recursion. -/
def testRunCostQS : RunCostQS testRound := testRunCostQ.toRunCostQS

end Round

end Algo
