/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the evaluator of a round whose fold state is quasipolynomially large.
-/
import Workspace.Algo.RoundQ
import Workspace.Algo.NormalizeSI

/-!
# The evaluator with a quasipolynomially large state

`Workspace/Algo/EvaluatorRAM.lean` packages the depth-first evaluator as a
`RAM.QuasiPolyFun`, using `RAM.QuasiPolyFun.iterateSetup`, whose hypothesis on the
intermediate state is a **polynomial** bound.  `Workspace/Algo/RoundQ.lean` explains why the
master round of Sec. 15 cannot meet it: the fold state of a line-5 node holds the full test
sets, the comparison classes and, in case (3), a `t`-ary structure with `m^t` tuples.

This file runs the same evaluator with `RAM.QuasiFun.iterateSetup`
(`Workspace/Machine/QuasiFun.lean`), whose hypothesis on the intermediate state is a
**quasipolynomial** bound.  Nothing changes in the machine: the recursion combinator
`RAM.quasiPolyTimeCleanAt_recursion` already takes a quasipolynomial cost for one round, and
a quasipolynomial cost evaluated at a quasipolynomially bounded state is again
quasipolynomial.  What changes in this file, against `Workspace/Algo/EvaluatorRAM.lean`, is
exactly two things:

* `RAM.QuasiPolyFun` becomes `RAM.QuasiFun` in the assembly of one step and of the whole
  loop;
* the polynomial `Algo.Round.statePoly` becomes the quasipolynomial
  `Algo.Round.statePolyQ`, which is a sum of a quasipolynomial state bound with a polynomial
  depth bound — stack depth `O(log² n)` times a quasipolynomial frame is quasipolynomial.

**And the return to the small class.**  `RAM.SIWorkspaceRoutine` asks for a *polynomially*
bounded answer.  It is recovered from `Algo.Round.CostQ.finish_le`: the answer of a node is
polynomially small, so the register of the machine is polynomially small at every step
(`Algo.Round.retOkQ_le`), and `Algo.Round.sizeBound_runQ` turns that into `RAM.SizeBound`.
`RAM.QuasiFun.quasiPolyFun` then gives back a `RAM.QuasiPolyFun`, which is what every layer
above the machine accepts.

## Main results

* `Algo.Round.quasiFun_stepDFS` — one step is a routine;
* `Algo.Round.size_iterateQ_le` — every state of a run is quasipolynomially small;
* `Algo.Round.quasiFun_runQ` — the evaluator is a `RAM.QuasiFun`;
* `Algo.Round.sizeBound_runQ` — its answer is polynomially small;
* `Algo.Round.quasiPolyFun_runQ` — **hence the evaluator is a `RAM.QuasiPolyFun`**;
* `Algo.Round.runQ_eq_answer` — and it returns the answer of the instance;
* `Algo.siWorkspaceRoutine_of_normQ_run` — one such round gives `RAM.SIWorkspaceRoutine`.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

variable [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

/-! ## One step as a routine -/

/-- **One step of the evaluator is a machine routine.**  The proof of
`Algo.Round.quasiPolyFun_stepDFS` with `RAM.QuasiPolyFun` replaced by `RAM.QuasiFun`
throughout: the three dispatchers and the four leaves are available in both classes. -/
theorem quasiFun_stepDFS_of_routines
    (hchild : QuasiFun R.child) (hinit : QuasiFun R.init)
    (hcombine : QuasiFun R.combine) (hfinish : QuasiFun R.finish) :
    QuasiFun R.stepDFS := by
  have hnil : QuasiFun (fun ret : Option α => (([] : List (Frame ι ω)), ret)) :=
    ((polyFun_const _).pair polyFun_id).quasiFun
  have hfold : QuasiFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
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
    have hcomb : QuasiFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
        R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :=
      (hI.pair (hj.pair (hs.pair ha))).quasiFun.comp hcombine
    have hframe : QuasiFun (fun x : α × (Frame ι ω × List (Frame ι ω)) =>
        ((x.2.1.1, x.2.1.2.1 + 1, R.combine (x.2.1.1, x.2.1.2.1, x.2.1.2.2, x.1)) :
          Frame ι ω)) :=
      hI.quasiFun.pair ((hj.add (polyFun_const 1)).quasiFun.pair hcomb)
    exact ((hframe.pair hrest.quasiFun).comp polyFun_cons.quasiFun).pair
      (polyFun_const _).quasiFun
  have hpop : QuasiFun (fun y : Frame ι ω × List (Frame ι ω) =>
      ((y.2, some (R.finish (y.1.1, y.1.2.2))) : EvalState ι ω α)) := by
    have hI : PolyFun (fun y : Frame ι ω × List (Frame ι ω) => y.1.1) :=
      polyFun_fst.comp polyFun_fst
    have hs : PolyFun (fun y : Frame ι ω × List (Frame ι ω) => y.1.2.2) :=
      (polyFun_fst.comp polyFun_snd).comp polyFun_snd
    exact (polyFun_snd (α := Frame ι ω) (β := List (Frame ι ω))).quasiFun.pair
      (((hI.pair hs).quasiFun.comp hfinish).comp polyFun_some.quasiFun)
  have hpush : QuasiFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
      (((z.1, 0, R.init z.1) :: z.2.1 :: z.2.2, (none : Option α)) : EvalState ι ω α)) := by
    have hJ : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.1) := polyFun_fst
    have hfr : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.2.1) :=
      polyFun_snd.comp polyFun_fst
    have hrest : PolyFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) => z.2.2) :=
      polyFun_snd.comp polyFun_snd
    have hframe : QuasiFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
        ((z.1, 0, R.init z.1) : Frame ι ω)) :=
      hJ.quasiFun.pair ((polyFun_const 0).quasiFun.pair (hJ.quasiFun.comp hinit))
    have htail : QuasiFun (fun z : ι × (Frame ι ω × List (Frame ι ω)) =>
        z.2.1 :: z.2.2) := (hfr.pair hrest).quasiFun.comp polyFun_cons.quasiFun
    exact ((hframe.pair htail).comp polyFun_cons.quasiFun).pair (polyFun_const _).quasiFun
  have hask : QuasiFun (fun y : Frame ι ω × List (Frame ι ω) => (R.child y.1, y)) :=
    (polyFun_fst.quasiFun.comp hchild).pair polyFun_id.quasiFun
  have hnone : QuasiFun (fun y : Frame ι ω × List (Frame ι ω) =>
      (match R.child y.1 with
        | some J => (((J, 0, R.init J) :: y.1 :: y.2, none) : EvalState ι ω α)
        | none => (y.2, some (R.finish (y.1.1, y.1.2.2))))) := by
    refine (hask.comp (hpop.optionElim hpush)).of_eq (fun y => ?_)
    cases h : R.child y.1 with
    | none => simp [h]
    | some J => simp [h]
  have hbody : QuasiFun (fun w : (Frame ι ω × List (Frame ι ω)) × Option α =>
      (match w.2 with
        | some a => (((w.1.1.1, w.1.1.2.1 + 1,
            R.combine (w.1.1.1, w.1.1.2.1, w.1.1.2.2, a)) :: w.1.2, none) : EvalState ι ω α)
        | none =>
            match R.child w.1.1 with
            | some J => ((J, 0, R.init J) :: w.1.1 :: w.1.2, none)
            | none => (w.1.2, some (R.finish (w.1.1.1, w.1.1.2.2))))) := by
    refine ((polyFun_swap (α := Frame ι ω × List (Frame ι ω)) (β := Option α)).quasiFun.comp
      (hnone.optionElim hfold)).of_eq (fun w => ?_)
    cases h : w.2 with
    | none => simp [h]
    | some a => simp [h]
  refine (QuasiFun.listCases hnil hbody).of_eq (fun x => ?_)
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

theorem quasiFun_stepDFS (C : RunCostQ R) : QuasiFun R.stepDFS :=
  R.quasiFun_stepDFS_of_routines C.quasiFun_child C.quasiFun_init
    C.quasiFun_combine C.quasiFun_finish

/-! ## The size of every state of a run -/

/-- The quasipolynomial that bounds every state of a run.  `S` is the size of the start
state. -/
def statePolyQ (C : RunCostQ R) (c : ℕ) (S : ℕ → ℕ) (N : ℕ) : ℕ :=
  S N + (2 * (1 + (C.measureBound N + 1)
      * (2 * (2 * C.bound N + 4 * C.stateBound N
          + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) + 1))
    + 2 * (C.bound N + 2))

private theorem polyBound_succPowQ (d : ℕ) : PolyBound (fun n : ℕ => (n + 1) ^ d) :=
  ⟨1, d, fun n => by simp⟩

theorem quasiPolyBound_statePolyQ (C : RunCostQ R) (c : ℕ) (S : ℕ → ℕ)
    (hS : QuasiPolyBound S) : QuasiPolyBound (R.statePolyQ C c S) := by
  have h1 : QuasiPolyBound (fun N => 2 * C.bound N + 4 * C.stateBound N
      + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) :=
    (((((polyBound_const 2).mul C.polyBound_bound).quasiPoly.add
      ((polyBound_const 4).quasiPoly.mul C.quasiPolyBound_stateBound)).add
      (((polyBound_const 4).mul (((polyBound_const 30).mul (polyBound_succPowQ (c + 2))).add
        (polyBound_const 3))).quasiPoly)).add (polyBound_const 8).quasiPoly)
  have h2 : QuasiPolyBound (fun N => 2 * (1 + (C.measureBound N + 1)
      * (2 * (2 * C.bound N + 4 * C.stateBound N
          + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) + 1))) :=
    (polyBound_const 2).quasiPoly.mul ((polyBound_const 1).quasiPoly.add
      ((C.polyBound_measureBound.add (polyBound_const 1)).quasiPoly.mul
        (((polyBound_const 2).quasiPoly.mul h1).add (polyBound_const 1).quasiPoly)))
  exact hS.add (h2.add ((polyBound_const 2).quasiPoly.mul
    (C.polyBound_bound.add (polyBound_const 2)).quasiPoly))

/-- **Every state of a run is quasipolynomially small.**  This is the hypothesis
`RAM.QuasiFun.iterateSetup` takes.  The depth of the stack is still polynomial — it is the
measure, `Babai.MasterStep.rank`, which is `O(log² n)` — and a frame is quasipolynomial, so
the product is quasipolynomial. -/
theorem size_iterateQ_le (C : RunCostQ R) (c : ℕ) (S : ℕ → ℕ)
    (hS : ∀ I : ι, Enc.size (R.startState I) ≤ S (Enc.size I))
    (I : ι) (j : ℕ) (hj : j ≤ R.stepCountQ C c I) :
    Enc.size ((R.stepDFS)^[j] (R.startState I)) ≤ R.statePolyQ C c S (Enc.size I) := by
  by_cases hwf : R.WF I
  · have hn : R.ground I ≤ Enc.size I := C.ground_le I
    have hcount : R.stepCountQ C c I = roundCount c (R.ground I) := by
      rw [stepCountQ, if_pos ((C.wfCheck_eq_true I).2 hwf)]
    have hok := R.stateOkQ_iterate C I hwf j
    have hlen := R.length_iterate_le I hwf j
    have hD : ((R.stepDFS)^[j] (R.startState I)).1.length
        ≤ C.measureBound (Enc.size I) + 1 :=
      le_trans hlen (by
        have := C.measure_le I hwf
        have h2 : C.measureBound (R.ground I) ≤ C.measureBound (Enc.size I) :=
          C.mono_measureBound hn
        omega)
    have hmain := R.size_stateQ_le C (R.ground I) j (C.measureBound (Enc.size I) + 1) _ hok hD
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
    have hsb : C.stateBound (R.ground I) ≤ C.stateBound (Enc.size I) := C.mono_stateBound hn
    have hmono : 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (R.ground I) + 4 * C.stateBound (R.ground I)
              + 4 * Nat.size j + 8) + 1)) + 2 * (C.bound (R.ground I) + 2)
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := by
      have := Nat.mul_le_mul_left (C.measureBound (Enc.size I) + 1)
        (show 2 * (2 * C.bound (R.ground I) + 4 * C.stateBound (R.ground I)
            + 4 * Nat.size j + 8) + 1
          ≤ 2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
            + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1 by omega)
      omega
    have : Enc.size ((R.stepDFS)^[j] (R.startState I))
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := le_trans hmain hmono
    rw [statePolyQ]
    omega
  · have hcount : R.stepCountQ C c I = 0 := by
      rw [stepCountQ, if_neg (by simpa [C.wfCheck_eq_true I] using hwf)]
    have hj0 : j = 0 := by omega
    subst hj0
    have := hS I
    rw [statePolyQ]
    simpa using le_trans this (by omega)

/-! ## The routine -/

/-- **The evaluator is a machine routine of the quasipolynomially large class.** -/
theorem quasiFun_runQ (C : RunCostQ R) (c : ℕ) : QuasiFun (R.runQ C c) := by
  have hstart : QuasiFun R.startState := by
    have hframe : QuasiFun (fun I : ι => ((I, 0, R.init I) : Frame ι ω)) :=
      polyFun_id.quasiFun.pair ((polyFun_const 0).quasiFun.pair C.quasiFun_init)
    have hlist : QuasiFun (fun I : ι => [((I, 0, R.init I) : Frame ι ω)]) :=
      (hframe.pair (polyFun_const _).quasiFun).comp polyFun_cons.quasiFun
    exact (hlist.pair (polyFun_const _).quasiFun).of_eq (fun _ => rfl)
  obtain ⟨S, hSb, hSmono, hSle⟩ := hstart.size.exists_quasiPolyBound
  have hcount : PolyFun (R.stepCountQ C c) := by
    refine (PolyFun.ite C.polyFun_wfCheck
      (C.polyFun_ground.comp (polyFun_roundCount c)) (polyFun_const 0)).of_eq (fun _ => rfl)
  have hq : ∀ I : ι, R.stepCountQ C c I ≤ roundCount c (Enc.size I) := by
    intro I
    rw [stepCountQ]
    by_cases h : C.wfCheck I
    · rw [if_pos h]
      exact roundCount_mono c (C.ground_le I)
    · rw [if_neg h]
      exact Nat.zero_le _
  refine QuasiFun.iterateSetup (setUp := fun I => (R.stepCountQ C c I, R.startState I))
    (step := R.stepDFS) (readOff := Prod.snd) (q := fun n => roundCount c n)
    (p := R.statePolyQ C c S) (hcount.quasiFun.pair hstart) ?_
    polyFun_snd.quasiFun hq (quasiPolyBound_roundCount c) ?_
    (R.quasiPolyBound_statePolyQ C c S hSb)
  · exact ((polyFun_fst.sub (polyFun_const 1)).quasiFun.pair
      (polyFun_snd.quasiFun.comp (R.quasiFun_stepDFS C))).of_eq (fun x => by
        obtain ⟨k, y⟩ := x
        rfl)
  · exact fun I j hj => R.size_iterateQ_le C c S hSle I j hj

/-- **The answer of the routine is polynomially small.**  On a well-formed instance the
register holds `finish` of some frame, which `Algo.Round.CostQ.finish_le` bounds by the
*polynomial* `bound`; on an instance that fails the test the loop is not run and the answer
is `none`.  This is the clause `RAM.SIWorkspaceRoutine` asks for. -/
theorem size_runQ_le (C : RunCostQ R) (c : ℕ) (I : ι) :
    Enc.size (R.runQ C c I) ≤ C.bound (Enc.size I) + 2 := by
  by_cases hwf : R.WF I
  · have hok := R.stateOkQ_iterate C I hwf (R.stepCountQ C c I)
    cases hx : ((R.stepDFS)^[R.stepCountQ C c I] (R.startState I)).2 with
    | none =>
      have : R.runQ C c I = none := hx
      rw [this, size_none_eq]
      omega
    | some a =>
      have hrun : R.runQ C c I = some a := hx
      have hle : Enc.size a ≤ C.bound (R.ground I) :=
        R.retOkQ_le C (R.ground I) _ _ hok a hx
      have hb : C.bound (R.ground I) ≤ C.bound (Enc.size I) := C.mono_bound (C.ground_le I)
      rw [hrun, size_some_eq]
      omega
  · have hcount : R.stepCountQ C c I = 0 := by
      rw [stepCountQ, if_neg (by simpa [C.wfCheck_eq_true I] using hwf)]
    have : R.runQ C c I = none := by rw [runQ, hcount]; rfl
    rw [this, size_none_eq]
    omega

theorem sizeBound_runQ (C : RunCostQ R) (c : ℕ) : SizeBound (R.runQ C c) := by
  obtain ⟨k, d, hkd⟩ := C.polyBound_bound
  refine ⟨k + 2, d, fun I => ?_⟩
  have h1 := R.size_runQ_le C c I
  have h2 := hkd (Enc.size I)
  have h3 : (1 : ℕ) ≤ (Enc.size I + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have h4 : (k + 2) * (Enc.size I + 1) ^ d
      = k * (Enc.size I + 1) ^ d + 2 * (Enc.size I + 1) ^ d := by ring
  omega

/-- **The evaluator is a `RAM.QuasiPolyFun`**: quasipolynomial time, polynomially small
answer.  This is the class every layer above the machine accepts. -/
theorem quasiPolyFun_runQ (C : RunCostQ R) (c : ℕ) : QuasiPolyFun (R.runQ C c) :=
  (R.quasiFun_runQ C c).quasiPolyFun (R.sizeBound_runQ C c)

/-! ### The answer of the routine -/

/-- The answer of the routine, with the two `Option`s merged. -/
def runAnswerQ {β : Type*} [Enc β] (R : Round ι ω (Option β)) (C : RunCostQ R) (c : ℕ)
    (I : ι) : Option β := (R.runQ C c I).join

theorem quasiPolyFun_runAnswerQ {β : Type*} [Enc β] (R : Round ι ω (Option β))
    (C : RunCostQ R) (c : ℕ) : QuasiPolyFun (R.runAnswerQ C c) :=
  (R.quasiPolyFun_runQ C c).comp_poly polyFun_join

/-! ## The evaluator against the mathematical layer -/

variable {Ω : Type u} {A : Type v}

/-- **The routine answers the instance.**  Word for word `Algo.Round.run_eq_answer`, with
`Algo.Round.RunCost` replaced by `Algo.Round.RunCostQ`: the correctness of the evaluator
never looked at the cost data except through the round count. -/
theorem runQ_eq_answer {κ : Type*} (C : RunCostQ R) {decI : ι → κ}
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
    ∃ a : α, R.runQ C c₁ I = some a ∧ decA a = (M.inst (decI I)).answer := by
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hI)
    simpa [roundCount] using this
  obtain ⟨a, ha, hdec⟩ :=
    evaluate_eq_answer R M himpl hgrp hrank hlift hmono c₁ hq f
      (roundCount c₁ (R.ground I)) I hI hf hle
  exact ⟨a, by rw [R.runQ_eq_evaluate C c₁ I hI]; exact ha, hdec⟩

/-! ## The routine is not vacuous

The test round of `Workspace/Algo/EvaluatorRAM.lean` — the instance `1` has two children,
both the instance `0`, and the instance `0` is a leaf — run through the new packaging. -/

/-- **The quasipolynomial-state evaluator is a `RAM.QuasiPolyFun` on a round that really
recurses.** -/
theorem quasiPolyFun_testRunQ (c : ℕ) :
    QuasiPolyFun (testRound.runQ testRunCostQ c) :=
  testRound.quasiPolyFun_runQ testRunCostQ c

/-- **And it computes the value of the round**, which is not the out-of-fuel answer. -/
theorem testRunQ_eq (c : ℕ) :
    testRound.runQ testRunCostQ c 1 = some (testRound.value 2 1) := by
  rw [testRound.runQ_eq_evaluate testRunCostQ c 1 (by norm_num [testRound])]
  refine testRound.evaluate_eq_value 2 _ 1 (by norm_num [testRound])
    (by norm_num [testRound]) ?_
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

`Algo.siWorkspaceRoutine_of_norm_run` (`Workspace/Algo/FinalBridge.lean`) with
`Algo.Round.RunCost` replaced by `Algo.Round.RunCostQ`.  It is the same proof: all it uses of
the cost data is `RAM.QuasiPolyFun (R.runAnswer …)`, which
`Algo.Round.quasiPolyFun_runAnswerQ` supplies. -/

section Bridge

variable {ω : Type*} [Enc ω]

/-- **One round with a quasipolynomially large fold state gives the final obligation.** -/
theorem siWorkspaceRoutine_of_normQ_run (R : Round RawSI ω RawCoset)
    (C : Round.RunCostQ R) (c : ℕ) (norm : RawSI → RawSI) (hnorm : PolyFun norm)
    (hdec : ∀ (n s : ℕ) (a : Targets.SIInput n s),
      ∃ b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)),
        Enc.encode b = Enc.encode (R.runAnswerQ C c (norm (rawOfSI a))) ∧
          Targets.SIRel n s a b) : SIWorkspaceRoutine := by
  have hrun := hnorm.comp_quasi (R.quasiPolyFun_runAnswerQ C c)
  obtain ⟨P, T, hT, hP⟩ := hrun.time
  obtain ⟨S, hSb, hSmono, hSle⟩ := hrun.size.exists_polyBound
  refine ⟨P, T, S, hT, hSb, hSmono, fun n s => ?_⟩
  refine CleanSolveAt.transfer (e := rawOfSI)
    (R' := fun (r : RawSI) (b' : RawCoset) =>
      b' = R.runAnswerQ C c (norm r) ∧ Enc.size b' ≤ S (Enc.size r))
    (fun a => (encode_si_eq a).symm) ?_
    (fun r => ⟨R.runAnswerQ C c (norm r), ⟨rfl, hSle r⟩, hP r⟩)
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

#print axioms Algo.Round.quasiPolyFun_runQ
#print axioms Algo.siWorkspaceRoutine_of_normQ_run
