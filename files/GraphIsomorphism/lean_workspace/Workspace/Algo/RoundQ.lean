/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the cost data of a round whose fold state is quasipolynomially large.
-/
import Workspace.Algo.EvaluatorRAM
import Workspace.Machine.QuasiFun

/-!
# A round with a quasipolynomially large fold state

`Algo.Round.Cost` (`Workspace/Algo/Round.lean`) bounds instances, fold states and answers by
one **polynomial** in the domain size, because `RAM.QuasiPolyFun.iterateSetup` asks for a
polynomial bound on the state of the iteration.  One line of Sec. 15 does not fit.

**Line 5, AggregateCertificates (Theorem 13.2.1).**  The node folds the answers of
`C(m,t)·…` certificate calls into: the group `F` (fine — shortened generators), the set of
*full* test sets, the comparison classes, and, in case (3), a `t`-ary relational structure
with `m^t` tuples, where `t = O(log n)`.  All three of the last are of **quasipolynomial**
size, and none of them can be recomputed inside `finish` from a polynomial summary: they are
functions of the answers of the children, and `finish` may not call the solver.  So the fold
state of a line-5 node is quasipolynomially large, and `Algo.Round.Cost` cannot hold for the
master round.

**What stays polynomial.**  Only the state.  The *answers* of the master round are cosets
with shortened generators, and its *instances* are String Isomorphism instances on a window,
both polynomial in the domain size.  That is the whole content of this file: the cost data
is split into two bounds,

* `bound`, **polynomial**, for instances and answers;
* `stateBound`, **quasipolynomial**, for fold states,

and the four routines are `RAM.QuasiFun` rather than `RAM.QuasiPolyFun`
(`Workspace/Machine/QuasiFun.lean`).  `Workspace/Algo/EvaluatorQ.lean` then runs the
evaluator with `RAM.QuasiFun.iterateSetup` and comes back to `RAM.QuasiPolyFun` at the top,
because the register of the machine — the answer — is bounded by `bound`.

`Algo.Round.RunCost.toRunCostQ` is the promised one-line lemma: a polynomial cost datum is a
quasipolynomial one, so the rounds already built lose nothing.

## Main definitions

* `Algo.Round.CostQ`, `Algo.Round.RunCostQ` — the cost data with the two bounds;
* `Algo.Round.FrameOkQ`, `Algo.Round.RetOkQ`, `Algo.Round.StateOkQ` — the size invariant of a
  reachable state, with the state bounded quasipolynomially and the register polynomially;
* `Algo.Round.stepCountQ`, `Algo.Round.runQ` — the evaluator as a total function.

## Main results

* `Algo.Round.RunCost.toRunCostQ` — a polynomial cost datum is a quasipolynomial one;
* `Algo.Round.stateOkQ_iterate` — the invariant holds along the whole run;
* `Algo.Round.size_stateQ_le` — hence every state of a run is quasipolynomially small, and
* `Algo.Round.retOkQ_le` — the register stays **polynomially** small.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

/-! ## The cost data -/

/-- **The cost data of a round whose fold state is quasipolynomially large.**

This is `Algo.Round.Cost` with one bound split into two.  `bound` is polynomial and governs
the instances and the answers; `stateBound` is quasipolynomial and governs the fold states.
The four routines are `RAM.QuasiFun`, the class of routines whose answer is only
quasipolynomially bounded (`Workspace/Machine/QuasiFun.lean`), because `combine` returns a
fold state.

`finish_le` is the clause that carries the whole design: the answer of a node is bounded by
the **polynomial** `bound`, although the state it is read off is only quasipolynomially
bounded.  For the round of Sec. 15 this says that a node returns a coset with shortened
generators, which is what `RAM.SIWorkspaceRoutine` needs at the top. -/
structure CostQ [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α) where
  /-- The polynomial that bounds instances and answers in terms of the domain size. -/
  bound : ℕ → ℕ
  polyBound_bound : PolyBound bound
  mono_bound : Monotone bound
  /-- The quasipolynomial that bounds the fold states in terms of the domain size. -/
  stateBound : ℕ → ℕ
  quasiPolyBound_stateBound : QuasiPolyBound stateBound
  mono_stateBound : Monotone stateBound
  /-- A bound on the number of children, the paper's multiplicative cost of the round. -/
  widthBound : ℕ → ℕ
  quasiPolyBound_widthBound : QuasiPolyBound widthBound
  quasiFun_child : QuasiFun R.child
  quasiFun_init : QuasiFun R.init
  quasiFun_combine : QuasiFun R.combine
  quasiFun_finish : QuasiFun R.finish
  /-- The domain size is read off the instance, so it is at most its size. -/
  ground_le : ∀ I, R.ground I ≤ Enc.size I
  /-- A well-formed instance is polynomially small in its domain. -/
  size_le : ∀ I, R.WF I → Enc.size I ≤ bound (R.ground I)
  /-- The empty partial answer is quasipolynomially small. -/
  init_le : ∀ I, R.WF I → Enc.size (R.init I) ≤ stateBound (R.ground I)
  /-- **The state does not grow along the fold.** -/
  combine_le : ∀ I j s a, R.WF I → Enc.size s ≤ stateBound (R.ground I) →
    Enc.size a ≤ bound (R.ground I) →
    Enc.size (R.combine (I, j, s, a)) ≤ stateBound (R.ground I)
  /-- **The answer of a node is polynomially small**, although the state is not. -/
  finish_le : ∀ I s, R.WF I → Enc.size s ≤ stateBound (R.ground I) →
    Enc.size (R.finish (I, s)) ≤ bound (R.ground I)
  /-- The out-of-fuel answer is small. -/
  bot_le : ∀ m, Enc.size R.bot ≤ bound m
  /-- The number of children is quasipolynomially bounded. -/
  width_le : ∀ I, R.WF I → R.width I ≤ widthBound (R.ground I)

/-- **What the machine packaging needs**, on top of `Algo.Round.CostQ`: the domain size as a
routine, a well-formedness test, and a polynomial bound on the depth of the stack.  These
three are word for word the extra fields of `Algo.Round.RunCost`; the depth bound stays
polynomial, because the depth is the measure, which is `Babai.MasterStep.rank`, itself
`O(log² n)`. -/
structure RunCostQ [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α) extends CostQ R where
  /-- The domain size is read off the raw instance by a routine. -/
  polyFun_ground : PolyFun R.ground
  /-- A test for well-formedness. -/
  wfCheck : ι → Bool
  polyFun_wfCheck : PolyFun wfCheck
  /-- The test is a test of `WF`. -/
  wfCheck_eq_true : ∀ I, wfCheck I = true ↔ R.WF I
  /-- A bound on the measure, hence on the depth of the stack. -/
  measureBound : ℕ → ℕ
  polyBound_measureBound : PolyBound measureBound
  mono_measureBound : Monotone measureBound
  measure_le : ∀ I, R.WF I → R.measure I ≤ measureBound (R.ground I)

variable [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

/-! ### A polynomial cost datum is a quasipolynomial one

The promised one-line lemma: a round whose fold state is polynomially small satisfies the
weaker interface, with the same bound in both slots.  So the rounds already built
(`Algo.chainRound`, `Algo.impRound`, `Algo.top2Round`, `Algo.lcRound`, …) can be used as
cases of the master round without their cost proofs being redone. -/

/-- **`Algo.Round.Cost` gives `Algo.Round.CostQ`.** -/
def Cost.toCostQ {R : Round ι ω α} (C : Cost R) : CostQ R where
  bound := C.bound
  polyBound_bound := C.polyBound_bound
  mono_bound := C.mono_bound
  stateBound := C.bound
  quasiPolyBound_stateBound := C.polyBound_bound.quasiPoly
  mono_stateBound := C.mono_bound
  widthBound := C.widthBound
  quasiPolyBound_widthBound := C.quasiPolyBound_widthBound
  quasiFun_child := C.quasiPolyFun_child.quasiFun
  quasiFun_init := C.quasiPolyFun_init.quasiFun
  quasiFun_combine := C.quasiPolyFun_combine.quasiFun
  quasiFun_finish := C.quasiPolyFun_finish.quasiFun
  ground_le := C.ground_le
  size_le := C.size_le
  init_le := C.init_le
  combine_le := C.combine_le
  finish_le := C.finish_le
  bot_le := C.bot_le
  width_le := C.width_le

/-- **`Algo.Round.RunCost` gives `Algo.Round.RunCostQ`.** -/
def RunCost.toRunCostQ {R : Round ι ω α} (C : RunCost R) : RunCostQ R where
  toCostQ := C.toCost.toCostQ
  polyFun_ground := C.polyFun_ground
  wfCheck := C.wfCheck
  polyFun_wfCheck := C.polyFun_wfCheck
  wfCheck_eq_true := C.wfCheck_eq_true
  measureBound := C.measureBound
  polyBound_measureBound := C.polyBound_measureBound
  mono_measureBound := C.mono_measureBound
  measure_le := C.measure_le

/-! ## The evaluator as a total function -/

/-- The number of steps the machine runs: the round count on a well-formed instance, and none
at all on an instance that fails the test. -/
def stepCountQ (R : Round ι ω α) (C : RunCostQ R) (c : ℕ) (I : ι) : ℕ :=
  if C.wfCheck I then roundCount c (R.ground I) else 0

/-- **The evaluator as a total function of a raw instance.** -/
def runQ (R : Round ι ω α) (C : RunCostQ R) (c : ℕ) (I : ι) : Option α :=
  ((R.stepDFS)^[R.stepCountQ C c I] (R.startState I)).2

/-- On a well-formed instance the routine is the evaluator of `Workspace/Algo/Evaluator.lean`,
run for `Algo.Round.roundCount` steps. -/
theorem runQ_eq_evaluate (C : RunCostQ R) (c : ℕ) (I : ι) (hI : R.WF I) :
    R.runQ C c I = R.evaluate (roundCount c (R.ground I)) I := by
  rw [runQ, stepCountQ, if_pos ((C.wfCheck_eq_true I).2 hI), evaluate_eq_iterate]

/-! ## The size invariant

The three clauses of `Algo.Round.StateOk`, with the fold state of a frame bounded by
`stateBound` and the register by `bound`.  The register is bounded against the frame it will
be folded into, and `Cost.finish_le` puts it below the **polynomial** bound, which is what
makes the answer of the whole run polynomially small. -/

/-- A frame of a reachable stack, at step `t` of a run on a domain of size at most `n`. -/
def FrameOkQ (R : Round ι ω α) (C : RunCostQ R) (n t : ℕ) (fr : Frame ι ω) : Prop :=
  R.WF fr.1 ∧ R.ground fr.1 ≤ n ∧ Enc.size fr.2.2 ≤ C.stateBound (R.ground fr.1) ∧ fr.2.1 ≤ t

/-- The register of a reachable state: its answer is polynomially small for the frame it will
be folded into, or for the root once the stack is empty. -/
def RetOkQ (R : Round ι ω α) (C : RunCostQ R) (n : ℕ) (st : List (Frame ι ω))
    (ret : Option α) : Prop :=
  ∀ a, ret = some a →
    Enc.size a ≤ C.bound (match st with | [] => n | fr :: _ => R.ground fr.1)

/-- The invariant of a reachable state. -/
def StateOkQ (R : Round ι ω α) (C : RunCostQ R) (n t : ℕ) (x : EvalState ι ω α) : Prop :=
  (∀ fr ∈ x.1, R.FrameOkQ C n t fr) ∧ R.RetOkQ C n x.1 x.2

/-- **The answer in the register is polynomially small for the root as well.**  This is the
clause that `RAM.SIWorkspaceRoutine` needs: the answer of the whole run is a coset with
shortened generators. -/
theorem retOkQ_le (C : RunCostQ R) (n t : ℕ) (x : EvalState ι ω α) (h : R.StateOkQ C n t x)
    (a : α) (ha : x.2 = some a) : Enc.size a ≤ C.bound n := by
  have h2 := h.2 a ha
  cases hst : x.1 with
  | nil => rw [hst] at h2; exact h2
  | cons fr rest =>
    rw [hst] at h2
    have hfr : R.FrameOkQ C n t fr := h.1 fr (by rw [hst]; exact List.mem_cons_self ..)
    exact le_trans h2 (C.mono_bound hfr.2.1)

/-- **The invariant is preserved by one step.**  The proof of `Algo.Round.stateOk_stepDFS`
word for word, with `CostQ.init_le` and `CostQ.combine_le` landing in `stateBound` and
`CostQ.finish_le` in `bound`. -/
theorem stateOkQ_stepDFS (C : RunCostQ R) (n t : ℕ) (x : EvalState ι ω α)
    (hstack : R.StackOk x.1) (h : R.StateOkQ C n t x) :
    R.StateOkQ C n (t + 1) (R.stepDFS x) := by
  obtain ⟨st, ret⟩ := x
  obtain ⟨hfr, hret⟩ := h
  have hbump : ∀ fr : Frame ι ω, R.FrameOkQ C n t fr → R.FrameOkQ C n (t + 1) fr :=
    fun fr hf => ⟨hf.1, hf.2.1, hf.2.2.1, Nat.le_succ_of_le hf.2.2.2⟩
  cases st with
  | nil =>
    refine ⟨fun fr hfr' => absurd hfr' (by simp), fun a ha => ?_⟩
    exact hret a ha
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    have hI0 : R.FrameOkQ C n t (I, j, s) := hfr (I, j, s) (List.mem_cons_self ..)
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
theorem stateOkQ_start (C : RunCostQ R) (I : ι) (hI : R.WF I) :
    R.StateOkQ C (R.ground I) 0 (R.startState I) := by
  refine ⟨fun fr hfr => ?_, fun a ha => absurd ha (by simp [startState])⟩
  rw [startState] at hfr
  have : fr = (I, 0, R.init I) := by simpa using hfr
  subst this
  exact ⟨hI, le_refl _, C.init_le I hI, le_refl _⟩

/-- **The invariant holds along the whole run.** -/
theorem stateOkQ_iterate (C : RunCostQ R) (I : ι) (hI : R.WF I) (t : ℕ) :
    R.StateOkQ C (R.ground I) t ((R.stepDFS)^[t] (R.startState I)) := by
  induction t with
  | zero => exact R.stateOkQ_start C I hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.stateOkQ_stepDFS C _ t _ (R.stackOk_iterate hI t) ih

/-! ### From the invariant to the size of the encoding -/

/-- A frame of a reachable stack: an instance below the polynomial bound, a fold state below
the quasipolynomial one, and an index of at most `Nat.size t` bits. -/
theorem size_frameQ_le (C : RunCostQ R) (n t : ℕ) (fr : Frame ι ω)
    (h : R.FrameOkQ C n t fr) :
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

/-- **A reachable state is quasipolynomially small**: at most `D` frames, each of at most the
size above, plus the register, which is polynomially small. -/
theorem size_stateQ_le (C : RunCostQ R) (n t D : ℕ) (x : EvalState ι ω α)
    (h : R.StateOkQ C n t x) (hD : x.1.length ≤ D) :
    Enc.size x ≤ 2 * (1 + D * (2 * (2 * C.bound n + 4 * C.stateBound n
        + 4 * Nat.size t + 8) + 1)) + 2 * (C.bound n + 2) := by
  have h1 : Enc.size x ≤ 2 * Enc.size x.1 + 2 * Enc.size x.2 := by
    have := Combine.size_pair_le x.1 x.2
    simpa using this
  have h2 : Enc.size x.1 ≤ 1 + x.1.length
      * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1) :=
    size_list_le_of_entries x.1 _ (fun fr hfr => R.size_frameQ_le C n t fr (h.1 fr hfr))
  have h3 : x.1.length * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1)
      ≤ D * (2 * (2 * C.bound n + 4 * C.stateBound n + 4 * Nat.size t + 8) + 1) :=
    Nat.mul_le_mul_right _ hD
  have h4 : Enc.size x.2 ≤ C.bound n + 2 := by
    cases hx : x.2 with
    | none => rw [size_none_eq]; omega
    | some a =>
      rw [size_some_eq]
      have := R.retOkQ_le C n t x h a hx
      omega
  omega

/-! ## The interface is satisfiable

`Algo.Round.testRunCost` (`Workspace/Algo/EvaluatorRAM.lean`) is a cost datum for a round
that really recurses.  Through `Algo.Round.RunCost.toRunCostQ` it is a `Algo.Round.RunCostQ`,
which checks that the new interface is not vacuous and that the bridge really is one line. -/

/-- **`Algo.Round.RunCostQ` is satisfiable**, on a round with a genuine recursion. -/
def testRunCostQ : RunCostQ testRound := testRunCost.toRunCostQ

end Round

end Algo
