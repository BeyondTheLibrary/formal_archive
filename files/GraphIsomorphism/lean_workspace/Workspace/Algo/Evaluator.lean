/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the depth-first evaluator of a computable round.
-/
import Workspace.Algo.Round
import Workspace.Machine.Pow

/-!
# The depth-first evaluator

`Algo.Round.value` (`Workspace/Algo/Round.lean`) is a recursion with two nested fuels, which
is a specification, not a machine.  This file turns it into a **loop with an explicit
stack**, which is what `Workspace/Machine/Recursion.lean` prescribes and what
`RAM.QuasiPolyFun.iterate` can run.

A *frame* is `(instance, index of the next child, state folded so far)`.  The machine state
is a stack of frames together with one return register:

* with the register empty, the machine looks at the top frame and asks `child` for the next
  subproblem; if there is one it **pushes** a fresh frame for it, and if there is none it
  **pops** the frame and puts `finish` of it into the register;
* with the register full, the machine **folds** its content into the frame below with
  `combine`, and advances that frame's index.

When the stack is empty the machine stands still, so iterating it any number of times beyond
the end gives the same state.  That is what lets one fixed round count serve every input.

## Main definitions

* `Algo.Round.stepDFS` — one step;
* `Algo.Round.evaluate` — `stepDFS` iterated `N` times from the one-frame stack;
* `Algo.Round.loopSteps`, `Algo.Round.subSteps` — the exact number of steps a subtree costs;
* `Algo.Round.StackOk`, `Algo.Round.BottomIs` — the two invariants of a reachable stack.

## Main results

* `Algo.Round.evaluate_eq_value` — the evaluator computes `Algo.Round.value`;
* `Algo.Round.evaluate_eq_answer` — hence, for a round that implements a correct
  mathematical round, it computes the answer of the instance, and
  `3 · 2 ^ (30 (log₂ n + 1) ^ (c₁+2)) + 1` steps always suffice;
* `Algo.Round.subSteps_le` — a subtree costs at most `3 · (number of its nodes) + 1` steps;
* `Algo.Round.polyFun_roundCount` — the number of steps is itself a `RAM.PolyFun` of the
  domain size, so it can be written into a register;
* `Algo.Round.stackOk_stepDFS`, `Algo.Round.bottomIs_stepDFS`,
  `Algo.Round.length_le_of_stackOk` — the stack is a strictly descending chain of measures
  whose bottom frame is the root, so it has at most `R.measure I + 1` frames.  With
  `Babai.MasterStep.rank_le` this is the `O(log² n)` depth of
  `Workspace/Algo/DESIGN.md`, item 4.3.

## What is not here

The `RAM.QuasiPolyFun` packaging of `Algo.Round.evaluate`.  Of the three things it needs,
two are here:

* the **round count as a routine**, `Algo.Round.polyFun_roundCount`.  This was the piece
  that used to wait on the arithmetic of the machine layer; `Workspace/Machine/Mul.lean`,
  `Div.lean` and `Pow.lean` now supply `RAM.PolyFun.mul`, `RAM.PolyFun.pow` and
  `RAM.PolyFun.factorial`, and with them the count is a `RAM.PolyFun`;
* the two **stack invariants**, `Algo.Round.StackOk` and `Algo.Round.BottomIs`, and the
  depth bound `Algo.Round.length_le_of_stackOk`.

What is missing is the last step: `RAM.QuasiPolyFun (fun x : ℕ × EvalState => (x.1 - 1,
R.stepDFS x.2))` assembled from the four routines of `Algo.Round.Cost`, and the size bound
`hp` of `RAM.QuasiPolyFun.iterate` for every intermediate state, which is the depth bound
times the frame bound of `Algo.Round.Cost` through `RAM.size_list_le_of_entries`.

Nothing below is a running-time claim.  No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

/-! ## The machine -/

/-- A stack frame: an instance, the index of its next child, and the state folded from the
answers of the earlier children. -/
abbrev Frame (ι ω : Type*) := ι × ℕ × ω

/-- The state of the evaluator: a stack of frames, and one return register. -/
abbrev EvalState (ι ω α : Type*) := List (Frame ι ω) × Option α

/-- **One step of the depth-first evaluator.**  With an empty stack the machine stands
still.  With a full register it folds the returned answer into the frame below.  Otherwise
it asks the top frame for its next child, and either pushes a frame for that child or pops
the frame and returns its answer. -/
def stepDFS (R : Round ι ω α) : EvalState ι ω α → EvalState ι ω α
  | ([], ret) => ([], ret)
  | ((I, j, s) :: rest, some a) => ((I, j + 1, R.combine (I, j, s, a)) :: rest, none)
  | ((I, j, s) :: rest, none) =>
      match R.child (I, j, s) with
      | some J => ((J, 0, R.init J) :: (I, j, s) :: rest, none)
      | none => (rest, some (R.finish (I, s)))

variable (R : Round ι ω α)

@[simp] theorem stepDFS_nil (ret : Option α) : R.stepDFS ([], ret) = ([], ret) := rfl

@[simp] theorem stepDFS_some (I : ι) (j : ℕ) (s : ω) (rest : List (Frame ι ω)) (a : α) :
    R.stepDFS ((I, j, s) :: rest, some a)
      = ((I, j + 1, R.combine (I, j, s, a)) :: rest, none) := rfl

theorem stepDFS_none (I : ι) (j : ℕ) (s : ω) (rest : List (Frame ι ω)) :
    R.stepDFS ((I, j, s) :: rest, none)
      = match R.child (I, j, s) with
        | some J => ((J, 0, R.init J) :: (I, j, s) :: rest, none)
        | none => (rest, some (R.finish (I, s))) := rfl

theorem stepDFS_push {I : ι} {j : ℕ} {s : ω} {J : ι} (rest : List (Frame ι ω))
    (h : R.child (I, j, s) = some J) :
    R.stepDFS ((I, j, s) :: rest, none) = ((J, 0, R.init J) :: (I, j, s) :: rest, none) := by
  rw [R.stepDFS_none, h]

theorem stepDFS_pop {I : ι} {j : ℕ} {s : ω} (rest : List (Frame ι ω))
    (h : R.child (I, j, s) = none) :
    R.stepDFS ((I, j, s) :: rest, none) = (rest, some (R.finish (I, s))) := by
  rw [R.stepDFS_none, h]

/-- Once the stack is empty the machine stands still. -/
theorem iterate_stepDFS_nil (ret : Option α) (t : ℕ) :
    (R.stepDFS)^[t] ([], ret) = ([], ret) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply, R.stepDFS_nil, ih]

/-! ## The number of steps

The machine pays, for each node of the recursion tree, one push, one pop and one fold, and
one extra pop for the root.  These two functions record the count exactly, so that the
correctness proof can say *which* iterate of `stepDFS` is the answer; the bound
`Algo.Round.subSteps_le` then replaces the exact count by `3 · (number of nodes) + 1`. -/

/-- The number of steps the fold over the children of one instance costs, given the cost
`sub` of a subtree. -/
def loopSteps (R : Round ι ω α) (rec : ι → α) (sub : ι → ℕ) : ℕ → ι → ℕ → ω → ℕ
  | 0, _, _, _ => 1
  | w + 1, I, j, s =>
      match R.child (I, j, s) with
      | none => 1
      | some J => 1 + (sub J + (1 + R.loopSteps rec sub w I (j + 1) (R.combine (I, j, s, rec J))))

/-- The number of steps the subtree of one instance costs. -/
def subSteps (R : Round ι ω α) : ℕ → ι → ℕ
  | 0, _ => 0
  | f + 1, I => R.loopSteps (R.value f) (R.subSteps f) (R.width I) I 0 (R.init I)

@[simp] theorem loopSteps_zero (rec : ι → α) (sub : ι → ℕ) (I : ι) (j : ℕ) (s : ω) :
    R.loopSteps rec sub 0 I j s = 1 := rfl

theorem loopSteps_succ_none {rec : ι → α} {sub : ι → ℕ} {w : ℕ} {I : ι} {j : ℕ} {s : ω}
    (h : R.child (I, j, s) = none) : R.loopSteps rec sub (w + 1) I j s = 1 := by
  rw [loopSteps, h]

theorem loopSteps_succ_some {rec : ι → α} {sub : ι → ℕ} {w : ℕ} {I : ι} {j : ℕ} {s : ω}
    {J : ι} (h : R.child (I, j, s) = some J) :
    R.loopSteps rec sub (w + 1) I j s
      = 1 + (sub J + (1 + R.loopSteps rec sub w I (j + 1) (R.combine (I, j, s, rec J)))) := by
  rw [loopSteps, h]

@[simp] theorem subSteps_zero (I : ι) : R.subSteps 0 I = 0 := rfl

@[simp] theorem subSteps_succ (f : ℕ) (I : ι) :
    R.subSteps (f + 1) I
      = R.loopSteps (R.value f) (R.subSteps f) (R.width I) I 0 (R.init I) := rfl

/-! ## Correctness

Two nested inductions, in the same order as in `Algo.Round.value`: the inner one runs over
the children of one instance, the outer one over the measure. -/

/-- **The fold of one instance, on the machine.**  Starting from the frame `(I, j, s)` on
top of `rest`, the machine runs the rest of the fold and leaves `rest` with the value of the
fold in the register.  The hypothesis `hsub` is what the outer induction supplies: a
subtree with a smaller measure is already known to run correctly.

The hypothesis `hw : R.width I ≤ j + w` is the loop invariant of `Algo.Round.loopAux`: it is
what makes the budget `w` run out exactly where `child` says `none`
(`Algo.Round.child_eq_none`), so that the machine and the specification stop together. -/
theorem loop_run (f : ℕ) (I : ι) (hI : R.WF I)
    (hsub : ∀ J, R.WF J → R.measure J < R.measure I → ∀ rest : List (Frame ι ω),
      (R.stepDFS)^[R.subSteps f J] ((J, 0, R.init J) :: rest, none)
        = (rest, some (R.value f J))) :
    ∀ (w j : ℕ) (s : ω), R.width I ≤ j + w → ∀ rest : List (Frame ι ω),
      (R.stepDFS)^[R.loopSteps (R.value f) (R.subSteps f) w I j s] ((I, j, s) :: rest, none)
        = (rest, some (R.loopAux (R.value f) w I j s)) := by
  intro w
  induction w with
  | zero =>
    intro j s hw rest
    have hc : R.child (I, j, s) = none := R.child_eq_none I j s (by omega)
    rw [R.loopSteps_zero, Function.iterate_one, R.stepDFS_pop rest hc, R.loopAux_zero]
  | succ w ih =>
    intro j s hw rest
    cases hc : R.child (I, j, s) with
    | none =>
      rw [R.loopSteps_succ_none hc, Function.iterate_one, R.stepDFS_pop rest hc,
        R.loopAux_succ_none hc]
    | some J =>
      have hJwf : R.WF J := R.child_wf I j s J hI hc
      have hJm : R.measure J < R.measure I := R.child_measure I j s J hI hc
      rw [R.loopSteps_succ_some hc, R.loopAux_succ_some hc]
      -- one push
      rw [Nat.add_comm 1 _, Function.iterate_succ_apply, R.stepDFS_push rest hc]
      -- the subtree of `J`
      rw [Nat.add_comm (R.subSteps f J) _, Function.iterate_add_apply,
        hsub J hJwf hJm ((I, j, s) :: rest)]
      -- one fold
      rw [Nat.add_comm 1 _, Function.iterate_succ_apply, R.stepDFS_some]
      -- the rest of the loop
      exact ih (j + 1) _ (by omega) rest

/-- **A whole subtree, on the machine.**  Induction on the measure: every child of `I` has a
smaller measure, so `Algo.Round.loop_run` applies. -/
theorem sub_run : ∀ (m f : ℕ) (I : ι), R.measure I ≤ m → R.WF I → R.measure I < f →
    ∀ rest : List (Frame ι ω),
      (R.stepDFS)^[R.subSteps f I] ((I, 0, R.init I) :: rest, none)
        = (rest, some (R.value f I)) := by
  intro m
  induction m with
  | zero =>
    intro f I hm hI hf rest
    cases f with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      rw [R.subSteps_succ, R.value_succ]
      exact R.loop_run f I hI (fun J _ hJ => absurd hJ (by omega)) _ 0 _ (by omega) rest
  | succ m ih =>
    intro f I hm hI hf rest
    cases f with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      rw [R.subSteps_succ, R.value_succ]
      refine R.loop_run f I hI (fun J hJwf hJm rest' => ih f J (by omega) hJwf (by omega) rest')
        _ 0 _ (by omega) rest

/-! ## The evaluator -/

/-- **The evaluator**: `N` steps of `Algo.Round.stepDFS` from the one-frame stack, read off
the return register. -/
def evaluate (R : Round ι ω α) (N : ℕ) (I : ι) : Option α :=
  ((R.stepDFS)^[N] ([(I, 0, R.init I)], none)).2

/-- **The evaluator computes `Algo.Round.value`**, as soon as it is given enough steps.
Steps beyond the end change nothing, because the machine stands still on an empty stack. -/
theorem evaluate_eq_value (f N : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f)
    (hN : R.subSteps f I ≤ N) : R.evaluate N I = some (R.value f I) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = R.subSteps f I + d := ⟨N - R.subSteps f I, by omega⟩
  have h := R.sub_run (R.measure I) f I le_rfl hI hf []
  rw [evaluate, Nat.add_comm, Function.iterate_add_apply, h, R.iterate_stepDFS_nil]

/-! ## How many steps are enough

One push, one pop and one fold per node, plus the pop of the root: `3 N + 1` steps for a
recursion tree with `N` nodes. -/

/-- The fold costs one step per child for the push, one for the fold, plus the subtrees,
plus the final pop. -/
theorem loopSteps_eq (rec : ι → α) (sub : ι → ℕ) :
    ∀ (w j : ℕ) (I : ι) (s : ω),
      R.loopSteps rec sub w I j s
        = 1 + 2 * (R.loopCalls rec w I j s).length
          + ((R.loopCalls rec w I j s).map sub).sum := by
  intro w
  induction w with
  | zero => intro j I s; simp
  | succ w ih =>
    intro j I s
    cases hc : R.child (I, j, s) with
    | none => rw [R.loopSteps_succ_none hc, R.loopCalls_succ_none hc]; simp
    | some J =>
      rw [R.loopSteps_succ_some hc, R.loopCalls_succ_some hc, ih (j + 1) I _,
        List.length_cons, List.map_cons, List.sum_cons]
      ring

/-- The sum of `3 g + 1` over a list. -/
theorem sum_map_three_mul_add_one {β : Type*} (L : List β) (g : β → ℕ) :
    (L.map (fun b => 3 * g b + 1)).sum = 3 * (L.map g).sum + L.length := by
  induction L with
  | nil => simp
  | cons b t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **The step count in terms of the node count**: a subtree with `N` nodes costs at most
`3N + 1` steps.  This is the number `RAM.QuasiPolyFun.iterate` has to be given. -/
theorem subSteps_le : ∀ (f : ℕ) (I : ι), R.subSteps f I ≤ 3 * R.nodes f I + 1 := by
  intro f
  induction f with
  | zero => intro I; simp
  | succ f ih =>
    intro I
    rw [R.subSteps_succ, R.loopSteps_eq, R.nodes_succ]
    set L := R.roundCalls f I with hL
    have hsum : (L.map (R.subSteps f)).sum ≤ (L.map (fun J => 3 * R.nodes f J + 1)).sum :=
      List.sum_le_sum (fun J _ => ih J)
    rw [sum_map_three_mul_add_one L (R.nodes f)] at hsum
    have hLdef : R.loopCalls (R.value f) (R.width I) I 0 (R.init I) = L := rfl
    rw [hLdef]
    omega

/-! ## The invariants of the stack

Two facts about every stack the machine can reach: the measures strictly decrease from the
bottom to the top, and the bottom frame is the instance the run was started at.  Together
they bound the number of frames by `R.measure I + 1`, which is `O(log² n)` for the round of
Sec. 15 (`Babai.MasterStep.rank_le`). -/

/-- The stack is a strictly descending chain of measures, with non-growing domains, of
well-formed instances. -/
def StackOk (R : Round ι ω α) : List (Frame ι ω) → Prop
  | [] => True
  | [fr] => R.WF fr.1
  | fr :: fr' :: rest =>
      R.WF fr.1 ∧ R.measure fr.1 < R.measure fr'.1 ∧ R.ground fr.1 ≤ R.ground fr'.1 ∧
        R.StackOk (fr' :: rest)

/-- The bottom frame of the stack carries the instance `I`. -/
def BottomIs (R : Round ι ω α) (I : ι) : List (Frame ι ω) → Prop
  | [] => True
  | [fr] => fr.1 = I
  | _ :: fr :: rest => R.BottomIs I (fr :: rest)

theorem stackOk_tail : ∀ (fr : Frame ι ω) (rest : List (Frame ι ω)),
    R.StackOk (fr :: rest) → R.StackOk rest := by
  intro fr rest h
  cases rest with
  | nil => exact trivial
  | cons fr' rest' => exact h.2.2.2

theorem stackOk_wf_head (fr : Frame ι ω) (rest : List (Frame ι ω))
    (h : R.StackOk (fr :: rest)) : R.WF fr.1 := by
  cases rest with
  | nil => exact h
  | cons fr' rest' => exact h.1

/-- Replacing the index and the state of the top frame does not disturb the invariant: it
only mentions the instances. -/
theorem stackOk_setTop {I : ι} {j j' : ℕ} {s s' : ω} (rest : List (Frame ι ω))
    (h : R.StackOk ((I, j, s) :: rest)) : R.StackOk ((I, j', s') :: rest) := by
  cases rest with
  | nil => exact h
  | cons fr' rest' => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem bottomIs_setTop {K : ι} {I : ι} {j j' : ℕ} {s s' : ω} (rest : List (Frame ι ω))
    (h : R.BottomIs K ((I, j, s) :: rest)) : R.BottomIs K ((I, j', s') :: rest) := by
  cases rest with
  | nil => exact h
  | cons fr' rest' => exact h

/-- **The descending-chain invariant is preserved.** -/
theorem stackOk_stepDFS (st : List (Frame ι ω)) (ret : Option α) (h : R.StackOk st) :
    R.StackOk (R.stepDFS (st, ret)).1 := by
  cases st with
  | nil => exact trivial
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    cases ret with
    | some a => exact R.stackOk_setTop rest h
    | none =>
      cases hc : R.child (I, j, s) with
      | none => rw [R.stepDFS_pop rest hc]; exact R.stackOk_tail _ rest h
      | some J =>
        rw [R.stepDFS_push rest hc]
        have hI : R.WF I := R.stackOk_wf_head (I, j, s) rest h
        exact ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc,
          R.child_ground I j s J hI hc, h⟩

/-- **The bottom frame never changes its instance**, until the stack becomes empty. -/
theorem bottomIs_stepDFS (K : ι) (st : List (Frame ι ω)) (ret : Option α)
    (h : R.BottomIs K st) : R.BottomIs K (R.stepDFS (st, ret)).1 := by
  cases st with
  | nil => exact trivial
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    cases ret with
    | some a => exact R.bottomIs_setTop rest h
    | none =>
      cases hc : R.child (I, j, s) with
      | none =>
        rw [R.stepDFS_pop rest hc]
        cases rest with
        | nil => exact trivial
        | cons fr' rest' => exact h
      | some J => rw [R.stepDFS_push rest hc]; exact h

/-- A strictly descending chain of measures above a frame `fr` is no longer than
`R.measure fr.1`. -/
theorem stackOk_head_length : ∀ (st : List (Frame ι ω)) (a fr : Frame ι ω),
    R.StackOk (a :: (st ++ [fr])) → st.length + 1 + R.measure a.1 ≤ R.measure fr.1 := by
  intro st
  induction st with
  | nil =>
    intro a fr h
    have := h.2.1
    simp only [List.length_nil]
    omega
  | cons b t ih =>
    intro a fr h
    have hab : R.measure a.1 < R.measure b.1 := h.2.1
    have hrest : R.StackOk (b :: (t ++ [fr])) := h.2.2.2
    have := ih b fr hrest
    simp only [List.length_cons]
    omega

/-- **The stack-depth bound.**  A stack satisfying the invariant, whose bottom frame is
`fr`, has at most `R.measure fr.1 + 1` frames.  For the round of Sec. 15 the measure is
`Babai.MasterStep.rank`, so the stack is `O(log² n)` deep on the instances the recursion of
Sec. 15 produces below the top one; see `Workspace/Algo/DESIGN.md`, item 4.3. -/
theorem length_le_of_stackOk (st : List (Frame ι ω)) (fr : Frame ι ω)
    (h : R.StackOk (st ++ [fr])) : (st ++ [fr]).length ≤ R.measure fr.1 + 1 := by
  cases st with
  | nil => simp
  | cons a t =>
    have := R.stackOk_head_length t a fr (by simpa using h)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The stack the evaluator starts from satisfies both invariants. -/
theorem stackOk_init {I : ι} (hI : R.WF I) : R.StackOk [(I, 0, R.init I)] := hI

theorem bottomIs_init (I : ι) : R.BottomIs I [(I, 0, R.init I)] := rfl

/-- Every stack the evaluator reaches satisfies the descending-chain invariant. -/
theorem stackOk_iterate {I : ι} (hI : R.WF I) (t : ℕ) :
    R.StackOk ((R.stepDFS)^[t] ([(I, 0, R.init I)], none)).1 := by
  induction t with
  | zero => exact R.stackOk_init hI
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.stackOk_stepDFS _ _ ih

/-- Every stack the evaluator reaches has the root at its bottom. -/
theorem bottomIs_iterate (I : ι) (t : ℕ) :
    R.BottomIs I ((R.stepDFS)^[t] ([(I, 0, R.init I)], none)).1 := by
  induction t with
  | zero => exact R.bottomIs_init I
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact R.bottomIs_stepDFS I _ _ ih

end Round

/-! ## The round count as a machine routine

`Algo.Round.evaluate_eq_answer` below runs the machine for
`3 · 2 ^ (30 (log₂ n + 1) ^ (c₁+2)) + 1` steps.  `RAM.QuasiPolyFun.iterate` does not take
that number as a constant: it takes it as a **routine** `k` with `RAM.QuasiPolyFun`
`(fun a => (k a, a))`.  So the number has to be computed, from the domain size, by the
machine.  It can be: although its *value* is quasipolynomial, its *encoding* is
`log₂` of it, which is polylogarithmic in `n`, so the routine is even a `RAM.PolyFun`.

This is what `RAM.PolyFun.pow` (`Workspace/Machine/Pow.lean`) is for: powering with an
exponent that a polynomial in the input size bounds.  Here the exponent is
`30 (log₂ n + 2) ^ (c₁+2)`, and `log₂ n + 2 ≤ Enc.size n + 1`, so the polynomial is
`30 · (size + 1) ^ (c₁+2)`. -/

namespace Round

/-- **The number of steps of the evaluator**, as a function of the domain size `n`: three
steps per node of the recursion tree (`Algo.Round.subSteps_le`) with the node bound of
`Babai.Theorem_1_1_1_math_of_masterStep`, plus one. -/
def roundCount (c : ℕ) (n : ℕ) : ℕ := 3 * 2 ^ (30 * (Nat.log 2 n + 2) ^ (c + 2)) + 1

/-- The exponent is polylogarithmic, hence bounded by a polynomial in the encoded size. -/
theorem log_succ_le_size (n : ℕ) : Nat.log 2 n + 1 ≤ Enc.size n := by
  have h : Nat.log 2 n = Nat.size n - 1 := Small.log_two_eq_size_sub_one n
  have h2 : Enc.size n = Nat.size n + 2 := Small.size_nat n
  omega

/-- **The round count is a machine routine.**  It is a `RAM.PolyFun`, not merely a
`RAM.QuasiPolyFun`: the number is quasipolynomially large but polylogarithmically long. -/
theorem polyFun_roundCount (c : ℕ) : PolyFun (fun n : ℕ => roundCount c n) := by
  -- the exponent `E n = 30 (log₂ n + 2) ^ (c+2)`
  have hL : PolyFun (fun n : ℕ => Nat.log 2 n + 2) :=
    polyFun_log2.add (polyFun_const 2)
  have hpow : PolyFun (fun n : ℕ => (Nat.log 2 n + 2) ^ (c + 2)) :=
    hL.pow (polyFun_const (c + 2)) (q := fun _ => c + 2) (fun _ => le_refl _)
      ⟨c + 2, 0, fun _ => by simp⟩
  have hE : PolyFun (fun n : ℕ => 30 * (Nat.log 2 n + 2) ^ (c + 2)) :=
    (polyFun_const 30).mul hpow
  -- the exponent is bounded by the polynomial `30 (size + 1) ^ (c+2)`
  have hq : ∀ n : ℕ, 30 * (Nat.log 2 n + 2) ^ (c + 2) ≤ 30 * (Enc.size n + 1) ^ (c + 2) :=
    fun n => Nat.mul_le_mul_left 30
      (Nat.pow_le_pow_left (by have := log_succ_le_size n; omega) _)
  have h2E : PolyFun (fun n : ℕ => (2 : ℕ) ^ (30 * (Nat.log 2 n + 2) ^ (c + 2))) :=
    (polyFun_const 2).pow hE (q := fun m => 30 * (m + 1) ^ (c + 2)) hq ⟨30, c + 2, fun _ => le_refl _⟩
  exact ((polyFun_const 3).mul h2E).add (polyFun_const 1)

end Round

/-! ## The evaluator against the mathematical layer

Putting `Algo.Round.evaluate_eq_value` together with `Algo.roundValue_eq` and
`Algo.Round.nodes_le_quasiPoly`: a round that implements one round of Sec. 15 is evaluated
correctly by the machine, and one fixed quasipolynomial number of steps serves every
instance. -/

variable {Ω : Type u} {A : Type v}

/-- **The evaluator answers the instance.**  If the raw round `R` implements the round `M`
of Sec. 15, then the machine, run for `3 · 2 ^ (30 (log₂ n + 2) ^ (c₁ + 2)) + 1` steps from
the one-frame stack of a well-formed instance `I`, returns a raw answer that decodes to
`Iso^Δ_K(x,y)`.

The number of steps is the node bound of `Babai.Theorem_1_1_1_math_of_masterStep` times
three, plus one: one push, one pop and one fold per node, plus the pop of the root
(`Algo.Round.subSteps_le`). -/
theorem evaluate_eq_answer {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f N : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f)
    (hN : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1 ≤ N) :
    ∃ a : α, R.evaluate N I = some a ∧ decA a = (M.inst (decI I)).answer := by
  have hnodes : R.nodes f I
      ≤ 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) :=
    R.nodes_le_quasiPoly (decA := decA) M himpl hgrp hrank hlift hmono c₁ hq f I hI hf
  have hsteps : R.subSteps f I ≤ N := by
    have := R.subSteps_le f I
    have h3 : 3 * R.nodes f I
        ≤ 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) :=
      Nat.mul_le_mul_left 3 hnodes
    omega
  exact ⟨R.value f I, R.evaluate_eq_value f N I hI hf hsteps,
    roundValue_eq R himpl (fun I' hI' => M.round_correct (decI I') (hgrp I' hI')) f I hI hf⟩

/-- **The evaluator at its own round count.**  `Algo.Round.evaluate_eq_answer` with
`N = Algo.Round.roundCount c₁ n`, the number `Algo.Round.polyFun_roundCount` computes. -/
theorem evaluate_roundCount_eq_answer {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    ∃ a : α, R.evaluate (Round.roundCount c₁ (M.inst (decI I)).windowSize) I = some a ∧
      decA a = (M.inst (decI I)).answer :=
  evaluate_eq_answer R M himpl hgrp hrank hlift hmono c₁ hq f _ I hI hf (le_refl _)

end Algo
