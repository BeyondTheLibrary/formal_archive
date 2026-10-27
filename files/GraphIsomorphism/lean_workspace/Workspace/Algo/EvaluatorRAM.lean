/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the depth-first evaluator as a machine routine.
-/
import Workspace.Algo.Evaluator
import Workspace.Machine.ListOps4
import Workspace.Machine.IterateInv
import Workspace.Machine.Final
import Workspace.Machine.Transfer

/-!
# The evaluator as a `RAM.QuasiPolyFun`

`Workspace/Algo/Evaluator.lean` proves that the depth-first evaluator of a computable round
returns the answer of the instance.  That is a statement about a Lean function.  This file
proves that the same function is computed by the machine of `Workspace/Machine/`, within one
quasipolynomial time bound: `Algo.Round.quasiPolyFun_run`.

Three things have to be supplied, and the third one is where the work is.

* **The encodings.**  Nothing to do.  The state of the evaluator is
  `List (ι × ℕ × ω) × Option α`, and `Workspace/Machine/Encoding.lean` gives `RAM.Enc` for
  products, lists, options and `ℕ`, so the instance is the standard one, built from `Enc ι`,
  `Enc ω` and `Enc α`.
* **One step as a routine.**  `Algo.Round.quasiPolyFun_stepDFS`, assembled from the four
  routines of `Algo.Round.Cost` with `RAM.QuasiPolyFun.listCases` and
  `RAM.QuasiPolyFun.optionElim` (`Workspace/Machine/ListOps4.lean`, added for this: the
  dispatchers of `Workspace/Machine/Cases.lean` exist only for `RAM.PolyFun`, and the four
  routines of a round are quasipolynomial).
* **The size of the state.**  `RAM.QuasiPolyFun.iterate` asks for it at *every* state of the
  state type, which a stack machine cannot give: a stack that no run reaches carries no
  invariant, so one step may grow it and the growth compounds over quasipolynomially many
  rounds.  `RAM.QuasiPolyFun.iterateSetup` (`Workspace/Machine/IterateInv.lean`, added for
  this) asks for it only along the orbit of the start state, which is what the invariants
  below deliver.

## Totality

A `RAM.QuasiPolyFun` is a total function of a raw instance, while the bounds of
`Algo.Round.Cost` hold only on well-formed instances.  The gap is closed by running the loop
**zero times** on an instance that fails a well-formedness test: `Algo.Round.stepCount` is the
round count on a well-formed instance and `0` otherwise, so `Algo.Round.run` answers `none`
there and no bound is needed.  The test is new data, `Algo.Round.RunCost.wfCheck`, and it is
honest: a raw instance is a list of lists of naturals, and every well-formedness condition of
Def. 11.1.2 is a polynomial-time test on it.

## Main definitions

* `Algo.Round.startState`, `Algo.Round.stepCount`, `Algo.Round.run` — the evaluator as a total
  function of a raw instance;
* `Algo.Round.RunCost` — the cost data of `Algo.Round.Cost` together with what the packaging
  needs: a routine for the domain size, a well-formedness test, and a polynomial bound on the
  measure (`Babai.MasterStep.rank` is `O(log² n)`, `Babai.MasterStep.johnsonRank_le_rankBound`);
* `Algo.Round.FrameOk`, `Algo.Round.RetOk`, `Algo.Round.StateOk` — the size invariant.

## Main results

* `Algo.Round.quasiPolyFun_stepDFS` — one step is a routine;
* `Algo.Round.stateOk_iterate` — the size invariant holds along the whole run;
* `Algo.Round.size_iterate_le` — hence every state of the run is polynomially small;
* `Algo.Round.quasiPolyFun_run` — **the evaluator is a `RAM.QuasiPolyFun`**;
* `Algo.Round.run_eq_answer` — and it returns the answer of the instance;
* `Algo.Round.testRound`, `Algo.Round.testRun_eq` — the hypotheses are satisfiable, and the
  routine is the evaluator on a round that really recurses.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

/-! ## The round count as a function of the domain size

Two facts about `Algo.Round.roundCount` that the packaging needs: it grows with the domain
size, and it is quasipolynomial, which is the bound `RAM.QuasiPolyFun.iterateSetup` takes on
the number of rounds. -/

/-- The round count grows with the domain size. -/
theorem roundCount_mono (c : ℕ) {m m' : ℕ} (h : m ≤ m') : roundCount c m ≤ roundCount c m' := by
  have hlog : Nat.log 2 m ≤ Nat.log 2 m' := Nat.log_mono_right h
  have : (Nat.log 2 m + 2) ^ (c + 2) ≤ (Nat.log 2 m' + 2) ^ (c + 2) :=
    Nat.pow_le_pow_left (by omega) _
  have h2 : (2 : ℕ) ^ (30 * (Nat.log 2 m + 2) ^ (c + 2))
      ≤ 2 ^ (30 * (Nat.log 2 m' + 2) ^ (c + 2)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [roundCount]
  omega

/-- The round count is quasipolynomial in the domain size. -/
theorem quasiPolyBound_roundCount (c : ℕ) : QuasiPolyBound (fun n => roundCount c n) := by
  refine ⟨c + 7, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hE : 30 * (Nat.log 2 n + 2) ^ (c + 2) + 2 ≤ L ^ (c + 7) := by
    have h1 : (Nat.log 2 n + 2) ^ (c + 2) ≤ L ^ (c + 2) := Nat.pow_le_pow_left (by omega) _
    have h2 : (1 : ℕ) ≤ L ^ (c + 2) := Nat.one_le_pow _ _ (by omega)
    have h3 : (32 : ℕ) ≤ L ^ 5 := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ L ^ 5 := Nat.pow_le_pow_left hL2 5
    have h4 : 32 * L ^ (c + 2) ≤ L ^ 5 * L ^ (c + 2) := Nat.mul_le_mul_right _ (by omega)
    have h5 : L ^ 5 * L ^ (c + 2) = L ^ (c + 7) := by rw [← pow_add]; ring_nf
    omega
  have h2E : (2 : ℕ) ^ (30 * (Nat.log 2 n + 2) ^ (c + 2) + 2) ≤ 2 ^ (L ^ (c + 7)) :=
    Nat.pow_le_pow_right (by norm_num) hE
  have hpow : (2 : ℕ) ^ (30 * (Nat.log 2 n + 2) ^ (c + 2) + 2)
      = 4 * 2 ^ (30 * (Nat.log 2 n + 2) ^ (c + 2)) := by
    rw [pow_add]; ring
  have h1 : (1 : ℕ) ≤ 2 ^ (30 * (Nat.log 2 n + 2) ^ (c + 2)) := Nat.one_le_two_pow
  simp only [roundCount]
  omega

/-- The round count is quasipolynomially large, hence polylogarithmically long: this is the
bound on the *index* stored in a frame, which grows by one at each fold. -/
theorem size_roundCount_le (c m : ℕ) :
    Nat.size (roundCount c m) ≤ 30 * (Nat.log 2 m + 2) ^ (c + 2) + 3 := by
  refine Nat.size_le.2 ?_
  have h1 : (1 : ℕ) ≤ 2 ^ (30 * (Nat.log 2 m + 2) ^ (c + 2)) := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (30 * (Nat.log 2 m + 2) ^ (c + 2) + 3)
      = 8 * 2 ^ (30 * (Nat.log 2 m + 2) ^ (c + 2)) := by
    rw [pow_add]; ring
  simp only [roundCount]
  omega

/-! ## The evaluator as a total function of a raw instance -/

variable [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

/-- The stack the evaluator starts from: one frame for the instance. -/
def startState (R : Round ι ω α) (I : ι) : EvalState ι ω α := ([(I, 0, R.init I)], none)

theorem evaluate_eq_iterate (N : ℕ) (I : ι) :
    R.evaluate N I = ((R.stepDFS)^[N] (R.startState I)).2 := rfl

/-- **What the machine packaging needs of a round**, on top of `Algo.Round.Cost`.

Three things.  The domain size must be a routine, since the number of rounds is computed from
it.  There must be a well-formedness test, because a `RAM.QuasiPolyFun` is a total function
while the bounds of `Algo.Round.Cost` hold only on well-formed instances; the loop is run zero
times on an instance that fails the test.  And the measure — the depth of the stack — must be
polynomially bounded in the domain size; for the round of Sec. 15 the measure is
`Babai.MasterStep.rank`, which is `O(log² n)` by `Babai.MasterStep.johnsonRank_le_rankBound`,
so a polynomial bound is far more than is needed. -/
structure RunCost (R : Round ι ω α) extends Cost R where
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

/-- The number of steps the machine runs: the round count on a well-formed instance, and none
at all on an instance that fails the test. -/
def stepCount (R : Round ι ω α) (C : RunCost R) (c : ℕ) (I : ι) : ℕ :=
  if C.wfCheck I then roundCount c (R.ground I) else 0

/-- **The evaluator as a total function of a raw instance.** -/
def run (R : Round ι ω α) (C : RunCost R) (c : ℕ) (I : ι) : Option α :=
  ((R.stepDFS)^[R.stepCount C c I] (R.startState I)).2

/-- On a well-formed instance the routine is the evaluator of `Workspace/Algo/Evaluator.lean`,
run for `Algo.Round.roundCount` steps. -/
theorem run_eq_evaluate (C : RunCost R) (c : ℕ) (I : ι) (hI : R.WF I) :
    R.run C c I = R.evaluate (roundCount c (R.ground I)) I := by
  rw [run, stepCount, if_pos ((C.wfCheck_eq_true I).2 hI), evaluate_eq_iterate]

/-! ## One step as a routine

`Algo.Round.stepDFS` is a case analysis on the stack, then on the register, then on the answer
of `child`.  Each of the three is one dispatcher of `Workspace/Machine/ListOps4.lean`, and the
four leaves are the four routines of `Algo.Round.Cost`. -/

/-- **One step of the evaluator is a machine routine.** -/
theorem quasiPolyFun_stepDFS (C : RunCost R) : QuasiPolyFun R.stepDFS := by
  -- the empty stack: the state does not move
  have hnil : QuasiPolyFun (fun ret : Option α => (([] : List (Frame ι ω)), ret)) :=
    ((polyFun_const _).pair polyFun_id).quasiPolyFun
  -- the fold: the register is full, so its answer goes into the top frame
  have hfold : QuasiPolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
      (((x.2.1.1, x.2.1.2.1 + 1, R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :: x.2.2,
        (none : Option α)) : EvalState ι ω α)) := by
    have ha : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.1) := polyFun_fst
    have hfr : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.2.1) :=
      polyFun_snd.comp polyFun_fst
    have hI : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.2.1.1) :=
      hfr.comp polyFun_fst
    have hj : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.2.1.2.1) :=
      (hfr.comp polyFun_snd).comp polyFun_fst
    have hs : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.2.1.2.2) :=
      (hfr.comp polyFun_snd).comp polyFun_snd
    have hrest : PolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) => x.2.2) :=
      polyFun_snd.comp polyFun_snd
    have hcomb : QuasiPolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
        R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :=
      (hI.pair (hj.pair (hs.pair ha))).quasiPolyFun.comp C.quasiPolyFun_combine
    have hframe : QuasiPolyFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
        ((x.2.1.1, x.2.1.2.1 + 1, R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :
          Frame ι ω)) :=
      hI.quasiPolyFun.pair ((hj.add (polyFun_const 1)).quasiPolyFun.pair hcomb)
    exact ((hframe.pair hrest.quasiPolyFun).comp polyFun_cons.quasiPolyFun).pair
      (polyFun_const _).quasiPolyFun
  -- the pop: `child` says there is no further subproblem
  have hpop : QuasiPolyFun (fun y : Frame ι ω × List (Frame ι ω) =>
      ((y.2, some (R.finish (y.1.1, y.1.2.2))) : EvalState ι ω α)) := by
    have hI : PolyFun (fun y : Frame ι ω × List (Frame ι ω) => y.1.1) :=
      polyFun_fst.comp polyFun_fst
    have hs : PolyFun (fun y : Frame ι ω × List (Frame ι ω) => y.1.2.2) :=
      (polyFun_fst.comp polyFun_snd).comp polyFun_snd
    exact (polyFun_snd (α := Frame ι ω) (β := List (Frame ι ω))).quasiPolyFun.pair
      (((hI.pair hs).quasiPolyFun.comp C.quasiPolyFun_finish).comp polyFun_some.quasiPolyFun)
  -- the push: `child` produced a subproblem
  have hpush : QuasiPolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
      (((z.1, 0, R.init z.1) :: z.2.1 :: z.2.2, (none : Option α)) : EvalState ι ω α)) := by
    have hJ : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.1) := polyFun_fst
    have hfr : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.2.1) :=
      polyFun_snd.comp polyFun_fst
    have hrest : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    have hframe : QuasiPolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
        ((z.1, 0, R.init z.1) : Frame ι ω)) :=
      hJ.quasiPolyFun.pair ((polyFun_const 0).quasiPolyFun.pair
        (hJ.quasiPolyFun.comp C.quasiPolyFun_init))
    have htail : QuasiPolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
        z.2.1 :: z.2.2) := (hfr.pair hrest).quasiPolyFun.comp polyFun_cons.quasiPolyFun
    exact ((hframe.pair htail).comp polyFun_cons.quasiPolyFun).pair
      (polyFun_const _).quasiPolyFun
  -- the register is empty: ask `child`
  have hask : QuasiPolyFun (fun y : Frame ι ω × List (Frame ι ω) => (R.child y.1, y)) :=
    (polyFun_fst.quasiPolyFun.comp C.quasiPolyFun_child).pair polyFun_id.quasiPolyFun
  have hnone : QuasiPolyFun (fun y : Frame ι ω × List (Frame ι ω) =>
      (match R.child y.1 with
        | some J => (((J, 0, R.init J) :: y.1 :: y.2, none) : EvalState ι ω α)
        | none => (y.2, some (R.finish (y.1.1, y.1.2.2))))) := by
    refine (hask.comp (hpop.optionElim hpush)).of_eq (fun y => ?_)
    cases h : R.child y.1 with
    | none => simp [h]
    | some J => simp [h]
  -- the register decides between the fold and the rest
  have hbody : QuasiPolyFun (fun w : (Frame ι ω × List (Frame ι ω)) × Option α =>
      (match w.2 with
        | some a => (((w.1.1.1, w.1.1.2.1 + 1,
            R.combine (w.1.1.1, w.1.1.2.1, w.1.1.2.2, a)) :: w.1.2, none) : EvalState ι ω α)
        | none =>
            match R.child w.1.1 with
            | some J => ((J, 0, R.init J) :: w.1.1 :: w.1.2, none)
            | none => (w.1.2, some (R.finish (w.1.1.1, w.1.1.2.2))))) := by
    refine ((polyFun_swap (α := Frame ι ω × List (Frame ι ω)) (β := Option α)).quasiPolyFun.comp
      (hnone.optionElim hfold)).of_eq (fun w => ?_)
    cases h : w.2 with
    | none => simp [h]
    | some a => simp [h]
  -- and the stack decides between standing still and the rest
  refine (QuasiPolyFun.listCases hnil hbody).of_eq (fun x => ?_)
  obtain ⟨st, ret⟩ := x
  cases st with
  | nil => rfl
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    cases ret with
    | some a => rfl
    | none =>
      cases hc : R.child (I, j, s) with
      | none => rw [R.stepDFS_pop rest hc]; simp [hc]
      | some J => rw [R.stepDFS_push rest hc]; simp [hc]

/-! ## The size of the state along a run

The invariant of a reachable state.  Three clauses, all needed and none of them implied by the
others: the frames carry well-formed instances of a domain that does not grow, their partial
answers stay below the bound of `Algo.Round.Cost` — this is `Cost.combine_le`, the clause that
says a fold does not grow the state — and their indices are at most the number of steps taken,
which is what bounds the *length of the index*, a number that grows by one at every fold.

The register is bounded against the frame it will be folded into, not against the root: the
answer of a child is below the bound of the *child's* domain (`Cost.finish_le`), and the
bound is monotone, so the fold into the parent has what `Cost.combine_le` asks for. -/

/-- A frame of a reachable stack, at step `t` of a run on a domain of size at most `n`. -/
def FrameOk (R : Round ι ω α) (C : RunCost R) (n t : ℕ) (fr : Frame ι ω) : Prop :=
  R.WF fr.1 ∧ R.ground fr.1 ≤ n ∧ Enc.size fr.2.2 ≤ C.bound (R.ground fr.1) ∧ fr.2.1 ≤ t

/-- The register of a reachable state: its answer is small for the frame it will be folded
into, or for the root once the stack is empty. -/
def RetOk (R : Round ι ω α) (C : RunCost R) (n : ℕ) (st : List (Frame ι ω))
    (ret : Option α) : Prop :=
  ∀ a, ret = some a →
    Enc.size a ≤ C.bound (match st with | [] => n | fr :: _ => R.ground fr.1)

/-- The invariant of a reachable state. -/
def StateOk (R : Round ι ω α) (C : RunCost R) (n t : ℕ) (x : EvalState ι ω α) : Prop :=
  (∀ fr ∈ x.1, R.FrameOk C n t fr) ∧ R.RetOk C n x.1 x.2

/-- The answer in the register is small for the root as well. -/
theorem retOk_le (C : RunCost R) (n t : ℕ) (x : EvalState ι ω α) (h : R.StateOk C n t x)
    (a : α) (ha : x.2 = some a) : Enc.size a ≤ C.bound n := by
  have h2 := h.2 a ha
  cases hst : x.1 with
  | nil => rw [hst] at h2; exact h2
  | cons fr rest =>
    rw [hst] at h2
    have hfr : R.FrameOk C n t fr := h.1 fr (by rw [hst]; exact List.mem_cons_self ..)
    exact le_trans h2 (C.mono_bound hfr.2.1)

/-- **The invariant is preserved by one step.**  The three cases are the three things a step
can do; `Cost.init_le`, `Cost.combine_le` and `Cost.finish_le` are used once each, and the
descending chain `Algo.Round.StackOk` is used once, to know that the domain of the frame just
popped is at most the domain of the frame below it. -/
theorem stateOk_stepDFS (C : RunCost R) (n t : ℕ) (x : EvalState ι ω α)
    (hstack : R.StackOk x.1) (h : R.StateOk C n t x) :
    R.StateOk C n (t + 1) (R.stepDFS x) := by
  obtain ⟨st, ret⟩ := x
  obtain ⟨hfr, hret⟩ := h
  have hbump : ∀ fr : Frame ι ω, R.FrameOk C n t fr → R.FrameOk C n (t + 1) fr :=
    fun fr hf => ⟨hf.1, hf.2.1, hf.2.2.1, Nat.le_succ_of_le hf.2.2.2⟩
  cases st with
  | nil =>
    refine ⟨fun fr hfr' => absurd hfr' (by simp), fun a ha => ?_⟩
    exact hret a ha
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    have hI0 : R.FrameOk C n t (I, j, s) := hfr (I, j, s) (List.mem_cons_self ..)
    have hIwf : R.WF I := hI0.1
    cases ret with
    | some a =>
      -- the fold
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
        -- the push
        rw [R.stepDFS_push rest hc]
        refine ⟨fun fr' hfr' => ?_, fun b hb => absurd hb (by simp)⟩
        rcases List.mem_cons.1 hfr' with rfl | hmem
        · exact ⟨R.child_wf I j s J hIwf hc,
            le_trans (R.child_ground I j s J hIwf hc) hI0.2.1,
            C.init_le J (R.child_wf I j s J hIwf hc), Nat.zero_le _⟩
        · exact hbump fr' (hfr fr' hmem)
      | none =>
        -- the pop
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
theorem stateOk_start (C : RunCost R) (I : ι) (hI : R.WF I) :
    R.StateOk C (R.ground I) 0 (R.startState I) := by
  refine ⟨fun fr hfr => ?_, fun a ha => absurd ha (by simp [startState])⟩
  rw [startState] at hfr
  have : fr = (I, 0, R.init I) := by simpa using hfr
  subst this
  exact ⟨hI, le_refl _, C.init_le I hI, le_refl _⟩

/-- **The invariant holds along the whole run.** -/
theorem stateOk_iterate (C : RunCost R) (I : ι) (hI : R.WF I) (t : ℕ) :
    R.StateOk C (R.ground I) t ((R.stepDFS)^[t] (R.startState I)) := by
  induction t with
  | zero => exact R.stateOk_start C I hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.stateOk_stepDFS C _ t _ (R.stackOk_iterate hI t) ih

/-! ### The depth of the stack

`Algo.Round.length_le_of_stackOk` bounds a stack whose bottom frame is given; to use it on a
reachable stack one has to know that the bottom frame is the root, which is
`Algo.Round.BottomIs`. -/

theorem bottomIs_cons (K : ι) (fr : Frame ι ω) (st : List (Frame ι ω)) (h : st ≠ []) :
    R.BottomIs K (fr :: st) ↔ R.BottomIs K st := by
  cases st with
  | nil => exact absurd rfl h
  | cons fr' rest => exact Iff.rfl

theorem bottomIs_concat (K : ι) : ∀ (L : List (Frame ι ω)) (b : Frame ι ω),
    R.BottomIs K (L ++ [b]) → b.1 = K := by
  intro L
  induction L with
  | nil => intro b hb; exact hb
  | cons fr L ih =>
    intro b hb
    exact ih b ((R.bottomIs_cons K fr (L ++ [b]) (by simp)).1 hb)

/-- **The depth bound for a reachable stack**: a stack of the descending-chain invariant whose
bottom frame is `K` has at most `R.measure K + 1` frames. -/
theorem length_le_of_bottomIs (K : ι) (st : List (Frame ι ω)) (hS : R.StackOk st)
    (hB : R.BottomIs K st) : st.length ≤ R.measure K + 1 := by
  rcases List.eq_nil_or_concat st with rfl | ⟨L, b, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hS hB ⊢
    have hb : b.1 = K := R.bottomIs_concat K L b hB
    have h := R.length_le_of_stackOk L b hS
    rw [hb] at h
    exact h

/-- Every stack the run reaches has at most `R.measure I + 1` frames. -/
theorem length_iterate_le (I : ι) (hI : R.WF I) (t : ℕ) :
    ((R.stepDFS)^[t] (R.startState I)).1.length ≤ R.measure I + 1 :=
  R.length_le_of_bottomIs I _ (R.stackOk_iterate hI t) (R.bottomIs_iterate I t)

/-! ### From the invariant to the size of the encoding -/

/-- A frame of a reachable stack is small: an instance and a partial answer below the bound of
`Algo.Round.Cost`, and an index of at most `Nat.size t` bits. -/
theorem size_frame_le (C : RunCost R) (n t : ℕ) (fr : Frame ι ω) (h : R.FrameOk C n t fr) :
    Enc.size fr ≤ 6 * C.bound n + 4 * Nat.size t + 8 := by
  obtain ⟨I, j, s⟩ := fr
  obtain ⟨hwf, hg, hs, hj⟩ := h
  have h1 : Enc.size ((I, j, s) : Frame ι ω) ≤ 2 * Enc.size I + 2 * Enc.size ((j, s) : ℕ × ω) :=
    Combine.size_pair_le _ _
  have h2 : Enc.size ((j, s) : ℕ × ω) ≤ 2 * Enc.size j + 2 * Enc.size s :=
    Combine.size_pair_le _ _
  have h3 : Enc.size I ≤ C.bound n := le_trans (C.size_le I hwf) (C.mono_bound hg)
  have h4 : Enc.size s ≤ C.bound n := le_trans hs (C.mono_bound hg)
  have h5 : Enc.size j = Nat.size j + 2 := Small.size_nat j
  have h6 : Nat.size j ≤ Nat.size t := Nat.size_le_size hj
  omega

theorem size_none_eq : Enc.size (none : Option α) = 2 := by
  have h : Enc.size (none : Option α) = Enc.size (0 : ℕ) := rfl
  rw [h, Small.size_nat]
  simp

/-- **A reachable state is small**: at most `D` frames, each of at most the size above, plus
the register. -/
theorem size_state_le (C : RunCost R) (n t D : ℕ) (x : EvalState ι ω α)
    (h : R.StateOk C n t x) (hD : x.1.length ≤ D) :
    Enc.size x ≤ 2 * (1 + D * (2 * (6 * C.bound n + 4 * Nat.size t + 8) + 1))
      + 2 * (C.bound n + 2) := by
  have h1 : Enc.size x ≤ 2 * Enc.size x.1 + 2 * Enc.size x.2 := by
    have := Combine.size_pair_le x.1 x.2
    simpa using this
  have h2 : Enc.size x.1 ≤ 1 + x.1.length * (2 * (6 * C.bound n + 4 * Nat.size t + 8) + 1) :=
    size_list_le_of_entries x.1 _ (fun fr hfr => R.size_frame_le C n t fr (h.1 fr hfr))
  have h3 : x.1.length * (2 * (6 * C.bound n + 4 * Nat.size t + 8) + 1)
      ≤ D * (2 * (6 * C.bound n + 4 * Nat.size t + 8) + 1) := Nat.mul_le_mul_right _ hD
  have h4 : Enc.size x.2 ≤ C.bound n + 2 := by
    cases hx : x.2 with
    | none => rw [size_none_eq]; omega
    | some a =>
      rw [size_some_eq]
      have := R.retOk_le C n t x h a hx
      omega
  omega

/-! ## The routine

Everything is in place: one step is a routine, the number of rounds is a routine
(`Algo.Round.polyFun_roundCount`), and every state of a run is polynomially small. -/

/-- The polynomial that bounds every state of a run.  `S` is the size of the start state, which
is what the bound has to be on an instance that fails the well-formedness test. -/
private def statePoly (C : RunCost R) (c : ℕ) (S : ℕ → ℕ) (N : ℕ) : ℕ :=
  S N + (2 * (1 + (C.measureBound N + 1)
      * (2 * (6 * C.bound N + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) + 1))
    + 2 * (C.bound N + 2))

private theorem polyBound_succPow (d : ℕ) : PolyBound (fun n : ℕ => (n + 1) ^ d) :=
  ⟨1, d, fun n => by simp⟩

private theorem polyBound_statePoly (C : RunCost R) (c : ℕ) (S : ℕ → ℕ) (hS : PolyBound S) :
    PolyBound (R.statePoly C c S) := by
  have h1 : PolyBound (fun N => 6 * C.bound N + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) :=
    (((polyBound_const 6).mul C.polyBound_bound).add ((polyBound_const 4).mul
      (((polyBound_const 30).mul (polyBound_succPow (c + 2))).add
        (polyBound_const 3)))).add (polyBound_const 8)
  have h2 : PolyBound (fun N => 2 * (1 + (C.measureBound N + 1)
      * (2 * (6 * C.bound N + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) + 1))) :=
    (polyBound_const 2).mul ((polyBound_const 1).add
      ((C.polyBound_measureBound.add (polyBound_const 1)).mul
        (((polyBound_const 2).mul h1).add (polyBound_const 1))))
  exact hS.add (h2.add ((polyBound_const 2).mul (C.polyBound_bound.add (polyBound_const 2))))

/-- **Every state of a run is polynomially small.**  This is the hypothesis
`RAM.QuasiPolyFun.iterateSetup` takes, and it is why the evaluator pushes one child at a time:
the depth is `R.measure I + 1` and a frame is polynomial in the domain size, so the product is
polynomial, while a stack holding all the children of a frame would be quasipolynomial. -/
theorem size_iterate_le (C : RunCost R) (c : ℕ) (S : ℕ → ℕ)
    (hS : ∀ I : ι, Enc.size (R.startState I) ≤ S (Enc.size I))
    (I : ι) (j : ℕ) (hj : j ≤ R.stepCount C c I) :
    Enc.size ((R.stepDFS)^[j] (R.startState I)) ≤ R.statePoly C c S (Enc.size I) := by
  by_cases hwf : R.WF I
  · have hn : R.ground I ≤ Enc.size I := C.ground_le I
    have hcount : R.stepCount C c I = roundCount c (R.ground I) := by
      rw [stepCount, if_pos ((C.wfCheck_eq_true I).2 hwf)]
    have hok := R.stateOk_iterate C I hwf j
    have hlen := R.length_iterate_le I hwf j
    have hD : ((R.stepDFS)^[j] (R.startState I)).1.length
        ≤ C.measureBound (Enc.size I) + 1 :=
      le_trans hlen (by
        have := C.measure_le I hwf
        have h2 : C.measureBound (R.ground I) ≤ C.measureBound (Enc.size I) :=
          C.mono_measureBound hn
        omega)
    have hmain := R.size_state_le C (R.ground I) j (C.measureBound (Enc.size I) + 1) _ hok hD
    -- the index is short: it is at most the number of rounds
    have hjsize : Nat.size j ≤ 30 * (Enc.size I + 1) ^ (c + 2) + 3 := by
      have h1 : j ≤ roundCount c (R.ground I) := by rw [hcount] at hj; exact hj
      have h2 : Nat.size j ≤ Nat.size (roundCount c (R.ground I)) := Nat.size_le_size h1
      have h3 := size_roundCount_le c (R.ground I)
      have h4 : Nat.log 2 (R.ground I) + 2 ≤ Enc.size I + 1 := by
        rcases Nat.eq_zero_or_pos (R.ground I) with hg | hg
        · have := one_le_size I
          simp [hg]
          omega
        · have := Nat.log_lt_self 2 (Nat.pos_iff_ne_zero.1 hg)
          omega
      have h5 : (Nat.log 2 (R.ground I) + 2) ^ (c + 2) ≤ (Enc.size I + 1) ^ (c + 2) :=
        Nat.pow_le_pow_left h4 _
      omega
    have hb : C.bound (R.ground I) ≤ C.bound (Enc.size I) := C.mono_bound hn
    have hmono : 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (6 * C.bound (R.ground I) + 4 * Nat.size j + 8) + 1))
            + 2 * (C.bound (R.ground I) + 2)
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (6 * C.bound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := by
      have hin : 6 * C.bound (R.ground I) + 4 * Nat.size j + 8
          ≤ 6 * C.bound (Enc.size I) + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8 := by
        omega
      have := Nat.mul_le_mul_left (C.measureBound (Enc.size I) + 1)
        (show 2 * (6 * C.bound (R.ground I) + 4 * Nat.size j + 8) + 1
          ≤ 2 * (6 * C.bound (Enc.size I)
            + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1 by omega)
      omega
    have : Enc.size ((R.stepDFS)^[j] (R.startState I))
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (6 * C.bound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := le_trans hmain hmono
    rw [statePoly]
    omega
  · have hcount : R.stepCount C c I = 0 := by
      rw [stepCount, if_neg (by simpa [C.wfCheck_eq_true I] using hwf)]
    have hj0 : j = 0 := by omega
    subst hj0
    have := hS I
    rw [statePoly]
    simpa using le_trans this (by omega)

/-- **The evaluator is a machine routine.**  One program, one quasipolynomial time bound, for
every raw instance: well-formed or not, the routine halts, and on a well-formed one it is the
evaluator of `Workspace/Algo/Evaluator.lean` run for `Algo.Round.roundCount` steps. -/
theorem quasiPolyFun_run (C : RunCost R) (c : ℕ) : QuasiPolyFun (R.run C c) := by
  -- the start state is a routine
  have hstart : QuasiPolyFun R.startState := by
    have hframe : QuasiPolyFun (fun I : ι => ((I, 0, R.init I) : Frame ι ω)) :=
      polyFun_id.quasiPolyFun.pair
        ((polyFun_const 0).quasiPolyFun.pair C.quasiPolyFun_init)
    have hlist : QuasiPolyFun (fun I : ι => [((I, 0, R.init I) : Frame ι ω)]) :=
      (hframe.pair (polyFun_const _).quasiPolyFun).comp polyFun_cons.quasiPolyFun
    exact (hlist.pair (polyFun_const _).quasiPolyFun).of_eq (fun _ => rfl)
  obtain ⟨S, hSb, hSmono, hSle⟩ := hstart.size.exists_polyBound
  -- the number of rounds is a routine
  have hcount : PolyFun (R.stepCount C c) := by
    refine (PolyFun.ite C.polyFun_wfCheck
      (C.polyFun_ground.comp (polyFun_roundCount c)) (polyFun_const 0)).of_eq (fun _ => rfl)
  -- and it is quasipolynomially bounded in the size of the instance
  have hq : ∀ I : ι, R.stepCount C c I ≤ roundCount c (Enc.size I) := by
    intro I
    rw [stepCount]
    by_cases h : C.wfCheck I
    · rw [if_pos h]
      exact roundCount_mono c (C.ground_le I)
    · rw [if_neg h]
      exact Nat.zero_le _
  refine QuasiPolyFun.iterateSetup (setUp := fun I => (R.stepCount C c I, R.startState I))
    (step := R.stepDFS) (readOff := Prod.snd) (q := fun n => roundCount c n)
    (p := R.statePoly C c S) (hcount.quasiPolyFun.pair hstart) ?_
    polyFun_snd.quasiPolyFun hq (quasiPolyBound_roundCount c) ?_
    (R.polyBound_statePoly C c S hSb)
  · exact ((polyFun_fst.sub (polyFun_const 1)).quasiPolyFun.pair
      (polyFun_snd.quasiPolyFun.comp (R.quasiPolyFun_stepDFS C))).of_eq (fun x => by
        obtain ⟨k, y⟩ := x
        rfl)
  · exact fun I j hj => R.size_iterate_le C c S hSle I j hj

/-! ### The answer of the routine

`Algo.Round.run` returns an `Option α`, the `none` standing for "the machine had no answer": on
a well-formed instance it never happens (`Algo.Round.run_eq_answer`).  An answer of String
Isomorphism is itself an `Option` (Def. 11.1.2: the empty set, or a coset), so the two are
merged before the answer leaves the algorithmic layer. -/

/-- The answer of the routine, with the two `Option`s merged. -/
def runAnswer {β : Type*} [Enc β] (R : Round ι ω (Option β)) (C : RunCost R) (c : ℕ)
    (I : ι) : Option β := (R.run C c I).join

theorem quasiPolyFun_runAnswer {β : Type*} [Enc β] (R : Round ι ω (Option β))
    (C : RunCost R) (c : ℕ) : QuasiPolyFun (R.runAnswer C c) :=
  (R.quasiPolyFun_run C c).comp_poly polyFun_join

theorem runAnswer_of_run_eq {β : Type*} [Enc β] (R : Round ι ω (Option β)) (C : RunCost R)
    (c : ℕ) (I : ι) (a : Option β) (h : R.run C c I = some a) : R.runAnswer C c I = a := by
  rw [runAnswer, h]
  rfl

/-! ## The evaluator against the mathematical layer

`Algo.evaluate_roundCount_eq_answer` runs the machine for `roundCount c₁ n` steps with `n` the
window size of the *decoded* instance.  The routine runs it for `roundCount c₁ (R.ground I)`
steps, with the raw domain size, so the two meet under the hypothesis that the raw domain size
is at least the window size — which is what `ground` is for. -/

variable {Ω : Type u} {A : Type v}

/-- **The routine answers the instance.**  The hypotheses are those of
`Algo.evaluate_roundCount_eq_answer` together with `hwin`: the raw domain size of an instance
is at least the window size of the instance it decodes to.  As there, a raw instance decodes
to an instance `κ` of the recursion of `M` (for Sec. 15, a `Babai.HintedInstance`), and `hlift`
says that the calls of a round decode to what `M.lift` attaches to them. -/
theorem run_eq_answer {κ : Type*} (C : RunCost R) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    ∃ a : α, R.run C c₁ I = some a ∧ decA a = (M.inst (decI I)).answer := by
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hI)
    simpa [roundCount] using this
  obtain ⟨a, ha, hdec⟩ :=
    evaluate_eq_answer R M himpl hgrp hrank hlift hmono c₁ hq f (roundCount c₁ (R.ground I)) I hI
      hf hle
  exact ⟨a, by rw [R.run_eq_evaluate C c₁ I hI]; exact ha, hdec⟩

/-! ## The hypotheses are satisfiable

`Algo.Round.RunCost` is a long list, so here is a round that meets every field, with a genuine
recursion: the instance `1` has two children, both the instance `0`, and the instance `0` is a
leaf.  It is on the raw type `ℕ`, so nothing is hidden in the encodings.

`Algo.Round.rawLeafRound` of `Workspace/Algo/Round.lean` cannot be used for this, for one
reason: its `ground` is `Enc.size`, and the machine has no routine for the length of an
encoding, so it cannot meet `RunCost.polyFun_ground`.  That is a property of that test round,
not of the interface — a real raw instance carries its domain size as the length of a list
(`Algo.RawSI`), and `RAM.polyFun_length` reads it off. -/

/-- A round on the raw type `ℕ`: the instance `1` has two children, both `0`, and `0` is a
leaf.  Everything else is ill-formed. -/
def testRound : Round ℕ ℕ ℕ where
  WF := fun I => I ≤ 1
  ground := fun _ => 0
  measure := fun I => I
  width := fun I => if I = 1 then 2 else 0
  child := fun p => if p.1 = 1 then (if p.2.1 ≤ 1 then some 0 else none) else none
  init := fun _ => 0
  combine := fun p => p.2.2.2
  finish := fun p => p.2
  bot := 0
  child_eq_none := by
    rintro I j s hj
    dsimp only at hj ⊢
    by_cases h : I = 1
    · subst h
      rw [if_pos rfl] at hj ⊢
      rw [if_neg (by omega)]
    · rw [if_neg h]
  child_wf := by
    rintro I j s J _ h
    by_cases hI : I = 1
    · subst hI
      simp only [if_pos rfl] at h
      by_cases hj : j ≤ 1
      · rw [if_pos hj] at h
        cases h
        omega
      · rw [if_neg hj] at h; exact absurd h (by simp)
    · rw [if_neg hI] at h; exact absurd h (by simp)
  child_measure := by
    rintro I j s J hI h
    by_cases hI1 : I = 1
    · subst hI1
      simp only [if_pos rfl] at h
      by_cases hj : j ≤ 1
      · rw [if_pos hj] at h
        cases h
        omega
      · rw [if_neg hj] at h; exact absurd h (by simp)
    · rw [if_neg hI1] at h; exact absurd h (by simp)
  child_ground := by
    rintro I j s J _ _
    exact le_refl _

/-- **`Algo.Round.RunCost` is satisfiable.** -/
def testRunCost : RunCost testRound where
  bound := fun n => n + 3
  polyBound_bound := ⟨4, 1, fun n => by nlinarith [Nat.zero_le n]⟩
  mono_bound := fun _ _ h => by dsimp only; omega
  widthBound := fun _ => 2
  quasiPolyBound_widthBound := (polyBound_const 2).quasiPoly
  quasiPolyFun_child := by
    refine (PolyFun.ite (polyFun_fst.natEq (polyFun_const 1))
      (PolyFun.ite ((polyFun_snd.comp polyFun_fst).le (polyFun_const 1))
        (polyFun_const (some 0)) (polyFun_const none))
      (polyFun_const none)).quasiPolyFun.of_eq (fun p => ?_)
    by_cases h1 : p.1 = 1
    · by_cases h2 : p.2.1 ≤ 1 <;> simp [testRound, h1, h2]
    · simp [testRound, h1]
  quasiPolyFun_init := (polyFun_const 0).quasiPolyFun
  quasiPolyFun_combine :=
    ((polyFun_snd.comp (polyFun_snd.comp polyFun_snd)).quasiPolyFun).of_eq (fun _ => rfl)
  quasiPolyFun_finish := polyFun_snd.quasiPolyFun
  ground_le := fun _ => Nat.zero_le _
  size_le := by
    intro I hI
    have h : Enc.size I = Nat.size I + 2 := Small.size_nat I
    have h2 : Nat.size I ≤ 1 := by
      have : I ≤ 1 := hI
      interval_cases I <;> simp
    dsimp only [testRound]
    omega
  init_le := by
    intro I _
    have h : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; simp
    dsimp only [testRound]
    omega
  combine_le := fun _ _ _ _ _ _ ha => ha
  finish_le := fun _ _ _ hs => hs
  bot_le := by
    intro m
    have h : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; simp
    dsimp only [testRound]
    omega
  width_le := by
    intro I hI
    dsimp only [testRound]
    by_cases h : I = 1 <;> simp [h]
  polyFun_ground := polyFun_const 0
  wfCheck := fun I => decide (I ≤ 1)
  polyFun_wfCheck := polyFun_id.le (polyFun_const 1)
  wfCheck_eq_true := fun I => by simp [testRound]
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_refl _
  measure_le := fun I hI => hI

/-- **The routine is a `RAM.QuasiPolyFun` on a round that really recurses.** -/
theorem quasiPolyFun_testRun (c : ℕ) :
    QuasiPolyFun (testRound.run testRunCost c) :=
  testRound.quasiPolyFun_run testRunCost c

/-- **And it computes the value of the round**, which is not the out-of-fuel answer: the
instance `1` is answered by its two children.  This is the check that the packaging did not
lose the evaluator on the way. -/
theorem testRun_eq (c : ℕ) : testRound.run testRunCost c 1 = some (testRound.value 2 1) := by
  rw [testRound.run_eq_evaluate testRunCost c 1 (by norm_num [testRound])]
  refine testRound.evaluate_eq_value 2 _ 1 (by norm_num [testRound]) (by norm_num [testRound]) ?_
  have h : testRound.subSteps 2 1 = 7 := by decide
  have hg : testRound.ground 1 = 0 := rfl
  rw [h, hg, roundCount, Nat.log_zero_right]
  have hX : 1 ≤ 30 * (0 + 2 : ℕ) ^ (c + 2) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have : (2 : ℕ) ^ 1 ≤ 2 ^ (30 * (0 + 2 : ℕ) ^ (c + 2)) :=
    Nat.pow_le_pow_right (by norm_num) hX
  simp only [pow_one] at this
  omega

end Round

/-! ## The bridge to the final obligation

`RAM.SIWorkspaceRoutine` (`Workspace/Machine/Final.lean`) is the single statement the whole
algorithmic layer owes: one program, one quasipolynomial step bound and one polynomial size
bound solving String Isomorphism for every domain size and every alphabet size.  The theorem
below turns a round of the shape built here into it.

Its hypotheses are exactly what the remaining packages have to deliver.

1. A round `R : Algo.Round Algo.RawSI ω Algo.RawCoset` — the seven lines of Sec. 15 with
   children that are data (package A15, through A7–A14 for the individual reductions).
2. `Algo.Round.RunCost R` — the four routines, the size bounds in terms of the domain size,
   the domain size as a routine, a well-formedness test, and a polynomial bound on the
   measure.
3. `hdec` — for every `n`, `s` and every typed instance `a`, the raw answer the routine
   returns is the encoding of an admissible typed answer.  This is where the mathematical
   layer enters: `Algo.Round.run_eq_answer` says the raw answer decodes to
   `Iso^Δ_K(x,y)`, the decoding maps of `Workspace/Algo/Encodings.lean` turn that into a typed
   answer with the same encoding, and `RAM.Targets.SIRel` is that answer's specification.

Nothing else is needed.  In particular the *size* of the answer, which
`RAM.SIWorkspaceRoutine` also asks for, costs nothing: it is the `RAM.SizeBound` that comes
with `Algo.Round.quasiPolyFun_run`, and an answer with the same encoding has the same size. -/

section Bridge

variable {ω : Type*} [Enc ω]

/-- **One round gives the final obligation.**  The evaluator of the round, transported from the
raw type to the family `SIInput n s` along `Algo.rawOfSI`, is the routine
`RAM.SIWorkspaceRoutine` asks for. -/
theorem siWorkspaceRoutine_of_run (R : Round RawSI ω RawCoset) (C : Round.RunCost R) (c : ℕ)
    (hdec : ∀ (n s : ℕ) (a : Targets.SIInput n s),
      ∃ b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)),
        Enc.encode b = Enc.encode (R.runAnswer C c (rawOfSI a)) ∧ Targets.SIRel n s a b) :
    SIWorkspaceRoutine := by
  obtain ⟨P, T, hT, hP⟩ := (R.quasiPolyFun_runAnswer C c).time
  obtain ⟨S, hSb, hSmono, hSle⟩ := (R.quasiPolyFun_runAnswer C c).size.exists_polyBound
  refine ⟨P, T, S, hT, hSb, hSmono, fun n s => ?_⟩
  refine CleanSolveAt.transfer (e := rawOfSI)
    (R' := fun (r : RawSI) (b' : RawCoset) =>
      b' = R.runAnswer C c r ∧ Enc.size b' ≤ S (Enc.size r))
    (fun a => (encode_si_eq a).symm) ?_ (fun r => ⟨R.runAnswer C c r, ⟨rfl, hSle r⟩, hP r⟩)
  intro a b' hb'
  obtain ⟨b, hbenc, hbrel⟩ := hdec n s a
  have hbb : Enc.encode b = Enc.encode b' := by rw [hbenc, hb'.1]
  have hsize : Enc.size b ≤ S (Enc.size a) := by
    have h1 : Enc.size b = Enc.size b' := size_eq_of_encode_eq hbb
    have h2 : Enc.size (rawOfSI a) = Enc.size a :=
      size_eq_of_encode_eq (encode_si_eq a).symm
    rw [h1, ← h2]
    exact hb'.2
  exact ⟨b, hbb, hbrel, hsize⟩

end Bridge

end Algo
