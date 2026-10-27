/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: one computable round of Procedure String-Isomorphism (Sec. 15).
-/
import Workspace.Algo.Encodings
import Workspace.Machine.PolyFun
import Workspace.Master.Cost

/-!
# The computable round

`Babai.SIReduction` (Sec. 11.1) is the mathematical shape of one round: a decision tree
whose internal nodes are String Isomorphism instances.  Its branches are arbitrary Lean
functions of a `Set (Equiv.Perm Ω)`, so a machine cannot hold one
(`Workspace/Algo/DESIGN.md`, item 4.1).  This file writes the same object with children that
are **data**: an instance has a `j`-th child, the `j`-th child may depend on the answers of
the children before it, and the answers are folded into a state of polynomial size.

## The shape of a round

A round works on three raw types: raw instances `ι`, a raw fold state `ω`, and raw answers
`α`.  It is five plain functions,

```
width   : ι → ℕ                  -- a bound on the number of children
child   : ι × ℕ × ω → Option ι   -- the `j`-th child, given the state folded so far
init    : ι → ω                  -- the empty partial answer
combine : ι × ℕ × ω × α → ω      -- fold one child's answer into the state
finish  : ι × ω → α              -- read the answer off the final state
```

together with the facts that make it legal (`Algo.Round`): `child` stops at `width`, a child
of a well-formed instance is well formed, its measure drops, and its domain does not grow.
`Algo.Round.Cost` adds what the machine layer needs: each of the four routines is a
`RAM.QuasiPolyFun`, and instances, states and answers all stay polynomially small in the
domain size.  The two are separate because the value semantics and the link to the
mathematical layer use none of the cost data, and because a round can then be tested without
choosing an encoding; see the note of 2026-09-21 at the end of `Workspace/Algo/DESIGN.md`.

**Why the children are indexed and not listed.**  `RAM.QuasiPolyFun.iterate` bounds the
intermediate state *polynomially* (`Workspace/Machine/PolyFun.lean`), while a round of
Sec. 15 has quasipolynomially many children.  An evaluator that pushed all the children of a
frame at once would have a quasipolynomially large state and would fall outside the
interface.  With an index, a frame is one instance, one index and one state, all polynomial.
This is risk R2 of `Workspace/Algo/DESIGN.md`, and it is the reason for the whole shape
above.

**Why the state is carried into `child`.**  Luks's Chain Rule
(`Babai.chainReduction`, `Workspace/TopAction/PrelimExtra.lean`) builds its next instance
from the answer to the previous one, and gives up early when an answer is empty.  So `child`
sees the folded state, and may return `none` before the index reaches `width`.

## Main definitions

* `Algo.Round` — the round;
* `Algo.Round.Cost` — the cost data of a round;
* `Algo.Round.loopAux`, `Algo.Round.value` — the value semantics, with a fuel, mirroring
  `Babai.solveFuel`;
* `Algo.Round.loopCalls`, `Algo.Round.roundCalls`, `Algo.Round.nodes` — the children and the
  number of nodes of the recursion tree, mirroring `Babai.roundCalls` and
  `Babai.countCalls`;
* `Algo.LoopMatch`, `Algo.Implements` — the round implements a mathematical reduction.

## Main results

* `Algo.roundValue_eq` — if `R` implements `ρ` and `ρ` is correct then the decoded value of
  `R` is the answer of the instance;
* `Algo.Round.roundCalls_eq` — the children of a round decode to the calls of `ρ`;
* `Algo.Round.nodes_eq_count` — the recursion tree of the round has exactly as many nodes as
  the mathematical recursion of Sec. 15;
* `Algo.Round.nodes_le_quasiPoly` — hence at most `2 ^ (30 (log₂ n + 2) ^ (c₁ + 2))` nodes,
  the bound of `Babai.Theorem_1_1_1_math_of_masterStep`.  This is the number of rounds the
  evaluator of `Workspace/Algo/Evaluator.lean` has to be run for.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM

variable {ι ω α : Type*}

/-! ## The round -/

/-- **One computable round** of Procedure String-Isomorphism (Sec. 15), on raw data.

`child (I, j, s)` is the `j`-th subproblem of the instance `I`, given the state `s` folded
from the answers of the children `0, …, j-1`; `none` means that `I` has no further child.
`finish (I, s)` reads the answer of `I` off the final state.

The four legality fields are exactly what the recursion needs: the loop over the children
terminates (`child_eq_none`), and the recursion over the children terminates and stays
inside the well-formed data of a fixed domain (`child_wf`, `child_measure`,
`child_ground`). -/
structure Round (ι ω α : Type*) where
  /-- The well-formed raw instances.  Every routine is total; nothing is claimed off `WF`. -/
  WF : ι → Prop
  /-- The domain size `n` of a raw instance.  It never grows along the recursion, which is
  what keeps a stack frame polynomially small. -/
  ground : ι → ℕ
  /-- The termination measure, the raw copy of `Babai.MasterStep.rank`. -/
  measure : ι → ℕ
  /-- A bound on the number of children of an instance — the paper's *multiplicative cost*
  of the round.  It is used only in the analysis: the loop stops when `child` says `none`,
  so no machine ever computes `width`. -/
  width : ι → ℕ
  /-- The `j`-th child of `I`, given the state folded from the earlier children. -/
  child : ι × ℕ × ω → Option ι
  /-- The empty partial answer. -/
  init : ι → ω
  /-- Fold the answer of the `j`-th child into the state. -/
  combine : ι × ℕ × ω × α → ω
  /-- Read the answer of the instance off the final state. -/
  finish : ι × ω → α
  /-- The answer returned when the recursion runs out of fuel.  It is never the value of a
  run with enough fuel. -/
  bot : α
  /-- An instance has at most `width I` children. -/
  child_eq_none : ∀ I j s, width I ≤ j → child (I, j, s) = none
  /-- A child of a well-formed instance is well formed. -/
  child_wf : ∀ I j s J, WF I → child (I, j, s) = some J → WF J
  /-- **The measure decreases**: the raw form of `Babai.MasterStep.rank_lt`. -/
  child_measure : ∀ I j s J, WF I → child (I, j, s) = some J → measure J < measure I
  /-- The domain of a child does not grow: the raw form of
  `Babai.MasterStep.windowSize_call_le`. -/
  child_ground : ∀ I j s J, WF I → child (I, j, s) = some J → ground J ≤ ground I

namespace Round

variable (R : Round ι ω α)

/-! ### The cost data

Everything the machine layer needs of a round, and nothing the mathematics needs.  The four
routines are asked to be `RAM.QuasiPolyFun` rather than `RAM.PolyFun` because the rounds of
Sec. 15 lines 4c and 6a run the Extended Design Lemma, whose cost is `n^{O(k)}` with
`k = O(log n)`; a `RAM.PolyFun` is a `RAM.QuasiPolyFun` by `RAM.PolyFun.quasiPolyFun`, so
nothing is lost for the cheap rounds.

One single polynomial `bound` governs the size of instances, states and answers.  Three
separate polynomials would say nothing more: their maximum is again a polynomial.  The
bound is in terms of `ground`, the domain size, **not** in terms of the size of the parent
instance.  That is deliberate: `ground` does not grow along the recursion, so a bound in
terms of `ground` holds at every level, whereas a bound "polynomial in the parent" composed
with itself `O(log² n)` times is only quasipolynomial, and the state of the evaluator would
then be too large for `RAM.QuasiPolyFun.iterate`. -/
structure Cost [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α) where
  /-- The polynomial that bounds instances, states and answers in terms of the domain size. -/
  bound : ℕ → ℕ
  polyBound_bound : PolyBound bound
  mono_bound : Monotone bound
  /-- A bound on the number of children, the paper's multiplicative cost of the round. -/
  widthBound : ℕ → ℕ
  quasiPolyBound_widthBound : QuasiPolyBound widthBound
  quasiPolyFun_child : QuasiPolyFun R.child
  quasiPolyFun_init : QuasiPolyFun R.init
  quasiPolyFun_combine : QuasiPolyFun R.combine
  quasiPolyFun_finish : QuasiPolyFun R.finish
  /-- The domain size is read off the instance, so it is at most its size. -/
  ground_le : ∀ I, R.ground I ≤ Enc.size I
  /-- A well-formed instance is polynomially small in its domain. -/
  size_le : ∀ I, R.WF I → Enc.size I ≤ bound (R.ground I)
  /-- The empty partial answer is small. -/
  init_le : ∀ I, R.WF I → Enc.size (R.init I) ≤ bound (R.ground I)
  /-- **The state does not grow along the fold.**  This is what keeps a frame polynomial
  although the fold has quasipolynomially many steps. -/
  combine_le : ∀ I j s a, R.WF I → Enc.size s ≤ bound (R.ground I) →
    Enc.size a ≤ bound (R.ground I) → Enc.size (R.combine (I, j, s, a)) ≤ bound (R.ground I)
  /-- The answer of an instance is small. -/
  finish_le : ∀ I s, R.WF I → Enc.size s ≤ bound (R.ground I) →
    Enc.size (R.finish (I, s)) ≤ bound (R.ground I)
  /-- The out-of-fuel answer is small. -/
  bot_le : ∀ m, Enc.size R.bot ≤ bound m
  /-- The number of children is quasipolynomially bounded. -/
  width_le : ∀ I, R.WF I → R.width I ≤ widthBound (R.ground I)

/-! ### The value semantics

Two nested recursions, exactly as in the paper: the inner one runs over the children of one
instance, the outer one answers each child by starting over.  Both are on a fuel rather than
on a measure, which is how `Babai.solveFuel` is written and keeps "the algorithm" apart from
"the algorithm terminates". -/

/-- The fold over the children of one instance.  `rec` answers a child, `w` is what is left
of the budget `width I`, `j` is the index of the next child and `s` the state folded so
far. -/
def loopAux (R : Round ι ω α) (rec : ι → α) : ℕ → ι → ℕ → ω → α
  | 0, I, _, s => R.finish (I, s)
  | w + 1, I, j, s =>
      match R.child (I, j, s) with
      | none => R.finish (I, s)
      | some J => R.loopAux rec w I (j + 1) (R.combine (I, j, s, rec J))

/-- The children the fold actually produces. -/
def loopCalls (R : Round ι ω α) (rec : ι → α) : ℕ → ι → ℕ → ω → List ι
  | 0, _, _, _ => []
  | w + 1, I, j, s =>
      match R.child (I, j, s) with
      | none => []
      | some J => J :: R.loopCalls rec w I (j + 1) (R.combine (I, j, s, rec J))

@[simp] theorem loopAux_zero (rec : ι → α) (I : ι) (j : ℕ) (s : ω) :
    R.loopAux rec 0 I j s = R.finish (I, s) := rfl

@[simp] theorem loopCalls_zero (rec : ι → α) (I : ι) (j : ℕ) (s : ω) :
    R.loopCalls rec 0 I j s = [] := rfl

theorem loopAux_succ (rec : ι → α) (w : ℕ) (I : ι) (j : ℕ) (s : ω) :
    R.loopAux rec (w + 1) I j s =
      match R.child (I, j, s) with
      | none => R.finish (I, s)
      | some J => R.loopAux rec w I (j + 1) (R.combine (I, j, s, rec J)) := rfl

theorem loopCalls_succ (rec : ι → α) (w : ℕ) (I : ι) (j : ℕ) (s : ω) :
    R.loopCalls rec (w + 1) I j s =
      match R.child (I, j, s) with
      | none => []
      | some J => J :: R.loopCalls rec w I (j + 1) (R.combine (I, j, s, rec J)) := rfl

theorem loopAux_succ_none {rec : ι → α} {w : ℕ} {I : ι} {j : ℕ} {s : ω}
    (h : R.child (I, j, s) = none) : R.loopAux rec (w + 1) I j s = R.finish (I, s) := by
  rw [R.loopAux_succ, h]

theorem loopAux_succ_some {rec : ι → α} {w : ℕ} {I : ι} {j : ℕ} {s : ω} {J : ι}
    (h : R.child (I, j, s) = some J) :
    R.loopAux rec (w + 1) I j s = R.loopAux rec w I (j + 1) (R.combine (I, j, s, rec J)) := by
  rw [R.loopAux_succ, h]

theorem loopCalls_succ_none {rec : ι → α} {w : ℕ} {I : ι} {j : ℕ} {s : ω}
    (h : R.child (I, j, s) = none) : R.loopCalls rec (w + 1) I j s = [] := by
  rw [R.loopCalls_succ, h]

theorem loopCalls_succ_some {rec : ι → α} {w : ℕ} {I : ι} {j : ℕ} {s : ω} {J : ι}
    (h : R.child (I, j, s) = some J) :
    R.loopCalls rec (w + 1) I j s
      = J :: R.loopCalls rec w I (j + 1) (R.combine (I, j, s, rec J)) := by
  rw [R.loopCalls_succ, h]

/-- **The value of a round**, with `f` levels of recursion: fold over the children of `I`,
answering each child by starting over one level down.  This is the computable copy of
`Babai.solveFuel`. -/
def value (R : Round ι ω α) : ℕ → ι → α
  | 0, _ => R.bot
  | f + 1, I => R.loopAux (R.value f) (R.width I) I 0 (R.init I)

@[simp] theorem value_zero (I : ι) : R.value 0 I = R.bot := rfl

@[simp] theorem value_succ (f : ℕ) (I : ι) :
    R.value (f + 1) I = R.loopAux (R.value f) (R.width I) I 0 (R.init I) := rfl

/-- The children the top round produces, the raw copy of `Babai.roundCalls`. -/
def roundCalls (R : Round ι ω α) (f : ℕ) (I : ι) : List ι :=
  R.loopCalls (R.value f) (R.width I) I 0 (R.init I)

/-- The number of nodes of the recursion tree, the raw copy of `Babai.countCalls`.  This is
the number of subproblems the evaluator of `Workspace/Algo/Evaluator.lean` visits. -/
def nodes (R : Round ι ω α) : ℕ → ι → ℕ
  | 0, _ => 0
  | f + 1, I => (R.roundCalls f I).length + ((R.roundCalls f I).map (R.nodes f)).sum

@[simp] theorem nodes_zero (I : ι) : R.nodes 0 I = 0 := rfl

@[simp] theorem nodes_succ (f : ℕ) (I : ι) :
    R.nodes (f + 1) I
      = (R.roundCalls f I).length + ((R.roundCalls f I).map (R.nodes f)).sum := rfl

/-! ### The children of a well-formed instance -/

/-- Every child produced by the fold is well formed and has a smaller measure. -/
theorem mem_loopCalls (rec : ι → α) {I : ι} (hI : R.WF I) :
    ∀ (w j : ℕ) (s : ω), ∀ J ∈ R.loopCalls rec w I j s, R.WF J ∧ R.measure J < R.measure I := by
  intro w
  induction w with
  | zero => intro j s J hJ; simp at hJ
  | succ w ih =>
    intro j s J hJ
    cases hc : R.child (I, j, s) with
    | none => rw [R.loopCalls_succ_none hc] at hJ; simp at hJ
    | some J' =>
      rw [R.loopCalls_succ_some hc] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩
      · exact ih (j + 1) _ J hJ

/-- Every child of the top round is well formed and has a smaller measure. -/
theorem mem_roundCalls {f : ℕ} {I : ι} (hI : R.WF I) :
    ∀ J ∈ R.roundCalls f I, R.WF J ∧ R.measure J < R.measure I :=
  R.mem_loopCalls _ hI _ _ _

/-- The domain of a child does not grow. -/
theorem ground_mem_loopCalls (rec : ι → α) {I : ι} (hI : R.WF I) :
    ∀ (w j : ℕ) (s : ω), ∀ J ∈ R.loopCalls rec w I j s, R.ground J ≤ R.ground I := by
  intro w
  induction w with
  | zero => intro j s J hJ; simp at hJ
  | succ w ih =>
    intro j s J hJ
    cases hc : R.child (I, j, s) with
    | none => rw [R.loopCalls_succ_none hc] at hJ; simp at hJ
    | some J' =>
      rw [R.loopCalls_succ_some hc] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact R.child_ground I j s J hI hc
      · exact ih (j + 1) _ J hJ

end Round

/-! ## The link to the mathematical layer

A raw round `R` *implements* a mathematical round `ρ` when the fold of `R` walks the decision
tree `ρ (decI I)` step by step: at each point either both stop with the same answer, or both
ask the same instance and, for **any** raw answer that decodes to the true answer of that
instance, the two continue to match.

The quantification over "any raw answer decoding to the true answer" is what makes the
relation usable: the evaluator hands `combine` the value its recursion produced, and all that
is known of that value is what it decodes to.  Matching only at the *true* answer costs
nothing, for the reason given in the header of `Workspace/Master/Procedure.lean`: an oracle
that is right on the instances the tree asks drives it along the same path
(`Babai.SIReduction.callsWith_eq_calls_of_agree`). -/

variable {Ω : Type u} {A : Type v}

open Babai

/-- The fold of `R` from the state `(j, s)` with budget `w` walks the reduction `T`. -/
inductive LoopMatch (R : Round ι ω α) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A (Set (Equiv.Perm Ω)) → Prop where
  /-- Both stop, with the same answer. -/
  | done (w j : ℕ) (s : ω) (a : Set (Equiv.Perm Ω)) (hc : R.child (I, j, s) = none)
      (ha : decA (R.finish (I, s)) = a) : LoopMatch R decI decA I w j s (.done a)
  /-- Both ask the same instance, and continue to match for every raw answer that decodes to
  its true answer. -/
  | call (w j : ℕ) (s : ω) (J : ι)
      (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω)))
      (hc : R.child (I, j, s) = some J)
      (hnext : ∀ a : α, decA a = (decI J).answer →
        LoopMatch R decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer)) :
      LoopMatch R decI decA I (w + 1) j s (.call (decI J) k)

/-- **The raw round `R` implements the mathematical round `ρ`**: on every well-formed
instance, the fold of `R` from the empty state walks the tree `ρ` builds.

The mathematical round runs over an **arbitrary instance type** `κ` with a projection
`inst : κ → Babai.SIInstance Ω A`, not over `Babai.SIInstance Ω A` itself.  That is forced
by the Johnson parameter: it is not determined by the group, so a round has to be handed the
giant representation its parent computed, and the recursion runs over instances *with that
hint*.  The raw side needs no change: a raw
instance `ι` already carries whatever raw data the round wants, the hint included, and
`R.measure`, `R.ground` and `R.WF` are functions of the raw instance with its hint.  Taking
`κ = Babai.SIInstance Ω A` and `inst = id` gives back the unhinted reading. -/
def Implements {κ : Type*} (R : Round ι ω α) (decI : ι → κ) (inst : κ → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω))
    (ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))) : Prop :=
  ∀ I : ι, R.WF I →
    LoopMatch R (fun J => inst (decI J)) decA I (R.width I) 0 (R.init I) (ρ (decI I))

namespace Round

/-- **The fold computes what the tree computes.**  If `rec` answers correctly every instance
`child` can produce from `I`, then the fold of `R` returns the value of the tree it matches,
and produces the same list of calls.

*Proof.*  Induction on the matching derivation.  At a stop, the fold calls `finish`, whether
the budget ran out or `child` said `none`, and that is the value of `.done`.  At a call, `rec`
answers the child correctly, so the induction hypothesis applies to the state after
`combine`, and the tree continues at the same answer. -/
theorem loopAux_eq (R : Round ι ω α) {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} {rec : ι → α} {Good : ι → Prop}
    (hgood : ∀ (j : ℕ) (s : ω) (J : ι), R.child (I, j, s) = some J → Good J)
    (hrec : ∀ J, Good J → decA (rec J) = (decI J).answer) :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatch R decI decA I w j s T →
        decA (R.loopAux rec w I j s) = T.run ∧
          (R.loopCalls rec w I j s).map decI = T.calls := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    cases w with
    | zero => exact ⟨by simpa using ha, by simp⟩
    | succ w =>
      refine ⟨?_, ?_⟩
      · rw [R.loopAux_succ_none hc]; simpa using ha
      · rw [R.loopCalls_succ_none hc]; simp
  | call w j s J k hc hnext ih =>
    have hG : Good J := hgood j s J hc
    have hA : decA (rec J) = (decI J).answer := hrec J hG
    obtain ⟨h1, h2⟩ := ih (rec J) hA
    refine ⟨?_, ?_⟩
    · rw [R.loopAux_succ_some hc, h1, SIReduction.run_call]
    · rw [R.loopCalls_succ_some hc, List.map_cons, h2, SIReduction.calls_call]

end Round

/-- **The round computes the answer.**  If the raw round `R` implements the mathematical
round `ρ`, and `ρ` is a correct round (`Babai.MasterStep.round_correct`), then the value of
`R` with enough fuel decodes to the answer of the instance.

*Proof.*  Induction on the fuel.  With fuel `f + 1` every child has a smaller measure, so by
the induction hypothesis it is answered correctly with fuel `f`, and `Algo.Round.loopAux_eq`
turns the fold into `(ρ (decI I)).run`, which is the answer. -/
theorem roundValue_eq {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (himpl : Implements R decI inst decA ρ)
    (hρ : ∀ I : ι, R.WF I → (ρ (decI I)).run = (inst (decI I)).answer) :
    ∀ (f : ℕ) (I : ι), R.WF I → R.measure I < f →
      decA (R.value f I) = (inst (decI I)).answer := by
  intro f
  induction f with
  | zero => intro I _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hI hf
    obtain ⟨h1, -⟩ :=
      R.loopAux_eq (Good := fun J => R.WF J ∧ R.measure J < R.measure I)
        (fun j s J hc => ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
        (fun J hJ => ih J hJ.1 (lt_of_lt_of_le hJ.2 (Nat.lt_succ_iff.mp hf)))
        _ _ _ _ (himpl I hI)
    rw [R.value_succ, h1, hρ I hI]

namespace Round

/-- **The children of a round are the calls of the reduction.** -/
theorem roundCalls_eq {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (himpl : Implements R decI inst decA ρ)
    (hρ : ∀ I : ι, R.WF I → (ρ (decI I)).run = (inst (decI I)).answer)
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f + 1) :
    (R.roundCalls f I).map (fun J => inst (decI J)) = (ρ (decI I)).calls := by
  obtain ⟨-, h2⟩ :=
    R.loopAux_eq (rec := R.value f) (Good := fun J => R.WF J ∧ R.measure J < R.measure I)
      (fun j s J hc => ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
      (fun J hJ => roundValue_eq R himpl hρ f J hJ.1
        (lt_of_lt_of_le hJ.2 (Nat.lt_succ_iff.mp hf)))
      _ _ _ _ (himpl I hI)
  exact h2

/-! ### The number of nodes

The recursion tree of the raw round has exactly the nodes of the mathematical recursion of
Sec. 15, so the bound of `Babai.Theorem_1_1_1_math_of_masterStep` applies to it unchanged.
This is the number the evaluator must be iterated for.

The three results below run over an arbitrary instance type `κ` with
`inst : κ → Babai.SIInstance Ω A`, as `Algo.Implements` does, because the mathematical round
of Sec. 15 runs on hinted instances.  What they ask in addition is that a raw child decodes
to the *lift* of the instance the tree asks for. -/

/-- **The recursion tree of the round is the recursion tree of Sec. 15.**

The mathematical round runs on hinted instances (`Babai.MasterStep`, the corrected paper
hinted instances), so a raw child must decode to the *lift* of the instance the tree asks
for; that is the hypothesis `hlift`.  It says no more than that the raw child carries the
hint its parent attaches to it, which is how a raw round is built.

*Proof.*  Induction on the fuel.  On the mathematical side the calls of a round against the
recursion one level down are the calls against the true oracle, because the recursion one
level down is correct at every call (`Babai.MasterStep.solve_eq_answer` and
`Babai.SIReduction.callsWith_eq_calls_of_agree`).  On the raw side
`Algo.Round.roundCalls_eq` says the children decode to those same calls, and the induction
hypothesis matches the subtrees term by term. -/
theorem nodes_eq_count {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J))) :
    ∀ (f : ℕ) (I : ι), R.WF I → R.measure I < f → R.nodes f I = M.count f (decI I) := by
  intro f
  induction f with
  | zero => intro I _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hI hf
    have hgrpI : IsGroupInstance (M.inst (decI I)) := hgrp I hI
    have hrankI : M.rank (decI I) < f + 1 := lt_of_le_of_lt (hrank I hI) hf
    -- the mathematical round asks the same instances against the recursion below
    have hagree : ∀ J : SIInstance Ω A,
        (∃ _ : J ∈ (M.step (decI I)).calls,
          IsGroupInstance (M.inst (M.lift (decI I) J)) ∧
            M.rank (M.lift (decI I) J) < M.rank (decI I)) →
        solveFuel M.step M.lift f (M.lift (decI I) J) = J.answer := by
      rintro J ⟨hJ, hg, hr⟩
      have h1 := M.solve_eq_answer f (M.lift (decI I) J) hg (by omega)
      rw [show solveFuel M.step M.lift f (M.lift (decI I) J)
          = M.solve f (M.lift (decI I) J) from rfl, h1, M.lift_inst (decI I) J hJ]
    obtain ⟨hcalls, -⟩ :=
      SIReduction.callsWith_eq_calls_of_agree
        (O := fun J => solveFuel M.step M.lift f (M.lift (decI I) J))
        hagree (M.step (decI I))
        (fun J hJ => ⟨hJ, by
            rw [M.lift_inst (decI I) J hJ]
            exact M.calls_isGroupInstance (decI I) hgrpI J hJ,
          M.rank_lt (decI I) hgrpI J hJ⟩)
    have hround : Babai.roundCalls M.step M.lift f (decI I) = (M.step (decI I)).calls :=
      hcalls
    -- the raw children decode to those instances
    have hmap : (R.roundCalls f I).map (fun J => M.inst (decI J)) = (M.step (decI I)).calls :=
      R.roundCalls_eq himpl (fun I' hI' => M.round_correct (decI I') (hgrp I' hI')) f I hI hf
    -- the subtrees agree term by term
    have hsum : ((R.roundCalls f I).map (R.nodes f)).sum
        = (((R.roundCalls f I).map (fun J => M.inst (decI J))).map
            (fun J => countCalls M.step M.lift f (M.lift (decI I) J))).sum := by
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro J hJ
      obtain ⟨hJwf, hJm⟩ := R.mem_roundCalls hI J hJ
      have hL : M.lift (decI I) (M.inst (decI J)) = decI J := (hlift f I J hI hJ).symm
      show R.nodes f J = countCalls M.step M.lift f (M.lift (decI I) (M.inst (decI J)))
      rw [hL]
      exact ih J hJwf (by omega)
    have hlen : (R.roundCalls f I).length = (M.step (decI I)).calls.length := by
      rw [← hmap, List.length_map]
    rw [R.nodes_succ, MasterStep.count, countCalls_succ, hround, ← hmap, hsum, hlen, ← hmap,
      List.length_map]

/-- The recursion tree of the round has at most `n² (q+1)^{johnsonRank}` nodes, the bound of
`Babai.MasterStep.count_le`. -/
theorem nodes_le_costBound {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (n₀ : ℕ) (f : ℕ) (I : ι) (hI : R.WF I)
    (hn : (M.inst (decI I)).windowSize ≤ n₀) (hf : R.measure I < f) :
    R.nodes f I ≤ M.costBound (M.roundCost n₀ + 1) (decI I) := by
  rw [R.nodes_eq_count (decA := decA) M himpl hgrp hrank hlift f I hI hf]
  exact M.count_le n₀ hmono f (decI I) (hgrp I hI) hn (lt_of_le_of_lt (hrank I hI) hf)

/-- **The bound the evaluator needs.**  The recursion tree of a round whose multiplicative
cost is quasipolynomial has at most `2 ^ (30 (log₂ n + 2) ^ (c₁ + 2))` nodes, where `n` is the
window size of the instance.  This is the count of
`Babai.Theorem_1_1_1_math_of_masterStep`, now stated for the *raw* instance and its raw
measure, which is the form `Workspace/Algo/Evaluator.lean` iterates on.

*Proof.*  `Algo.Round.nodes_le_costBound` at `n₀ = n`, then the same arithmetic as in
`Babai.Theorem_1_1_1_math_of_masterStep` (`Workspace/Master/Cost.lean`): `q + 1 ≤
2^{L^{c₁}+1}` with `L = log₂ n + 2`, `johnsonRank ≤ 14 L²` and `n² ≤ 2^{2L}`. -/
theorem nodes_le_quasiPoly {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    R.nodes f I ≤ 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) := by
  set n := (M.inst (decI I)).windowSize with hn
  set L := Nat.log 2 n + 2 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hcount : R.nodes f I ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank (decI I) := by
    have := R.nodes_le_costBound (decA := decA) M himpl hgrp hrank hlift hmono n f I hI
      (le_refl _) hf
    rwa [MasterStep.costBound, MasterStep.win, ← hn] at this
  have hQ : M.roundCost n + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
    have h := hq n
    have h2 : (2 : ℕ) ^ (L ^ c₁) + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (L ^ c₁) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [← hLdef] at h
    omega
  have hrk : M.johnsonRank (decI I) ≤ 14 * L ^ 2 := by
    have h := M.johnsonRank_le_rankBound (decI I)
    rw [MasterStep.rankBound, MasterStep.win, ← hn] at h
    refine le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    omega
  have hn2 : n ^ 2 ≤ 2 ^ (2 * L) := by
    have hlt : n < 2 ^ L :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) n)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc n ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
      _ = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  calc R.nodes f I ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank (decI I) := hcount
    _ ≤ 2 ^ (2 * L) * (2 ^ (L ^ c₁ + 1)) ^ (14 * L ^ 2) :=
        Nat.mul_le_mul hn2 ((Nat.pow_le_pow_left hQ _).trans
          (Nat.pow_le_pow_right Nat.one_le_two_pow hrk))
    _ = 2 ^ (2 * L + (L ^ c₁ + 1) * (14 * L ^ 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (30 * L ^ (c₁ + 2)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have hle : L ^ 2 ≤ L ^ (c₁ + 2) := Nat.pow_le_pow_right hL1 (by omega)
        have hle1 : L ≤ L ^ 2 := by nlinarith
        have hexp : (L ^ c₁ + 1) * (14 * L ^ 2) = 14 * (L ^ c₁ * L ^ 2) + 14 * L ^ 2 := by
          ring
        rw [hexp, ← pow_add]
        omega

end Round

/-! ## Two placeholder rounds

The interface above is worth nothing if no round meets it, so here are two that do.  They
are stated for `ι = Babai.SIInstance Ω A` with `decI = id` and `decA = id`, which is the
extreme case where "raw" and "typed" coincide: it tests the *shape* of the interface, not
the encodings.  The second one has two children, and its second child depends on the answer
to the first, which is the sequential dependency the Chain Rule needs.

`Algo.rawLeafRound` then checks that `Algo.Round.Cost` is satisfiable on genuinely raw
types. -/

/-- A round with no children: it answers the instance outright.  Sec. 15 line 4a is of this
shape ("if `t = 1` then find `Iso_G(x,y)`, exit"). -/
noncomputable def leafRound (ans : SIInstance Ω A → Set (Equiv.Perm Ω)) :
    Round (SIInstance Ω A) ℕ (Set (Equiv.Perm Ω)) where
  WF := fun _ => True
  ground := fun I => I.windowSize
  measure := fun _ => 0
  width := fun _ => 0
  child := fun _ => none
  init := fun _ => 0
  combine := fun p => p.2.2.1
  finish := fun p => ans p.1
  bot := ∅
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := fun _ _ _ _ _ h => by simp at h
  child_measure := fun _ _ _ _ _ h => by simp at h
  child_ground := fun _ _ _ _ _ h => by simp at h

/-- The leaf round implements the reduction that answers at once. -/
theorem implements_leafRound (ans : SIInstance Ω A → Set (Equiv.Perm Ω)) :
    Implements (leafRound ans) id id id (fun I => .done (ans I)) := by
  intro I _
  exact LoopMatch.done _ _ _ _ rfl rfl

/-- **The link theorem is not vacuous on the leaf round**: one level of recursion already
returns the answer. -/
theorem leafRound_value (ans : SIInstance Ω A → Set (Equiv.Perm Ω))
    (hans : ∀ I : SIInstance Ω A, ans I = I.answer) (f : ℕ) (hf : 0 < f)
    (I : SIInstance Ω A) : (leafRound ans).value f I = I.answer :=
  roundValue_eq (leafRound ans) (implements_leafRound ans)
    (fun Im _ => hans Im) f I trivial hf

/-- Two children, the second one chosen from the answer to the first.  This is the shape of
Luks's Chain Rule (`Babai.chainReduction`) and of every adaptive round of Secs. 12–14. -/
noncomputable def twoCallRound (WF : SIInstance Ω A → Prop) (μ : SIInstance Ω A → ℕ)
    (c₁ : SIInstance Ω A → SIInstance Ω A)
    (c₂ : SIInstance Ω A → Set (Equiv.Perm Ω) → SIInstance Ω A)
    (g : SIInstance Ω A → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω))
    (hwf₁ : ∀ I, WF I → WF (c₁ I)) (hwf₂ : ∀ I a, WF I → WF (c₂ I a))
    (hμ₁ : ∀ I, WF I → μ (c₁ I) < μ I) (hμ₂ : ∀ I a, WF I → μ (c₂ I a) < μ I)
    (hn₁ : ∀ I, WF I → (c₁ I).windowSize ≤ I.windowSize)
    (hn₂ : ∀ I a, WF I → (c₂ I a).windowSize ≤ I.windowSize) :
    Round (SIInstance Ω A) (Set (Equiv.Perm Ω) × Set (Equiv.Perm Ω))
      (Set (Equiv.Perm Ω)) where
  WF := WF
  ground := fun I => I.windowSize
  measure := μ
  width := fun _ => 2
  child := fun p =>
    match p.2.1 with
    | 0 => some (c₁ p.1)
    | 1 => some (c₂ p.1 p.2.2.1)
    | _ => none
  init := fun _ => (∅, ∅)
  combine := fun p =>
    match p.2.1 with
    | 0 => (p.2.2.2, p.2.2.1.2)
    | _ => (p.2.2.1.1, p.2.2.2)
  finish := fun p => g p.1 p.2.1 p.2.2
  bot := ∅
  child_eq_none := by
    rintro I (_ | _ | j) s hj
    · omega
    · omega
    · rfl
  child_wf := by
    rintro I (_ | _ | j) s J hI h
    · cases h; exact hwf₁ I hI
    · cases h; exact hwf₂ I _ hI
    · exact absurd (show (none : Option (SIInstance Ω A)) = some J from h) (by simp)
  child_measure := by
    rintro I (_ | _ | j) s J hI h
    · cases h; exact hμ₁ I hI
    · cases h; exact hμ₂ I _ hI
    · exact absurd (show (none : Option (SIInstance Ω A)) = some J from h) (by simp)
  child_ground := by
    rintro I (_ | _ | j) s J hI h
    · cases h; exact hn₁ I hI
    · cases h; exact hn₂ I _ hI
    · exact absurd (show (none : Option (SIInstance Ω A)) = some J from h) (by simp)

/-- The mathematical reduction the two-call round implements: ask `c₁ I`, then ask the
instance `c₂` builds from that answer, then assemble with `g`. -/
noncomputable def twoCallReduction (c₁ : SIInstance Ω A → SIInstance Ω A)
    (c₂ : SIInstance Ω A → Set (Equiv.Perm Ω) → SIInstance Ω A)
    (g : SIInstance Ω A → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω))
    (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .call (c₁ I) (fun a₁ => .call (c₂ I a₁) (fun a₂ => .done (g I a₁ a₂)))

/-- **The two-call round implements the two-call reduction**, sequential dependency
included. -/
theorem implements_twoCallRound (WF : SIInstance Ω A → Prop) (μ : SIInstance Ω A → ℕ)
    (c₁ : SIInstance Ω A → SIInstance Ω A)
    (c₂ : SIInstance Ω A → Set (Equiv.Perm Ω) → SIInstance Ω A)
    (g : SIInstance Ω A → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω))
    (hwf₁ hwf₂ hμ₁ hμ₂ hn₁ hn₂) :
    Implements (twoCallRound WF μ c₁ c₂ g hwf₁ hwf₂ hμ₁ hμ₂ hn₁ hn₂) id id id
      (twoCallReduction c₁ c₂ g) := by
  intro I _
  refine LoopMatch.call 1 0 (∅, ∅) (c₁ I)
    (fun a₁ => .call (c₂ I a₁) (fun a₂ => .done (g I a₁ a₂))) rfl ?_
  intro a₁ ha₁
  have ha₁' : a₁ = (c₁ I).answer := ha₁
  subst ha₁'
  refine LoopMatch.call 0 1 ((c₁ I).answer, ∅) (c₂ I (c₁ I).answer)
    (fun a₂ => .done (g I (c₁ I).answer a₂)) rfl ?_
  intro a₂ ha₂
  have ha₂' : a₂ = (c₂ I (c₁ I).answer).answer := ha₂
  subst ha₂'
  exact LoopMatch.done _ _ _ _ rfl rfl

/-- **The link theorem is not vacuous on the two-call round.** -/
theorem twoCallRound_value (WF : SIInstance Ω A → Prop) (μ : SIInstance Ω A → ℕ)
    (c₁ : SIInstance Ω A → SIInstance Ω A)
    (c₂ : SIInstance Ω A → Set (Equiv.Perm Ω) → SIInstance Ω A)
    (g : SIInstance Ω A → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω) → Set (Equiv.Perm Ω))
    (hwf₁ hwf₂ hμ₁ hμ₂ hn₁ hn₂)
    (hg : ∀ I : SIInstance Ω A, g I (c₁ I).answer (c₂ I (c₁ I).answer).answer = I.answer)
    (f : ℕ) (I : SIInstance Ω A) (hI : WF I) (hf : μ I < f) :
    (twoCallRound WF μ c₁ c₂ g hwf₁ hwf₂ hμ₁ hμ₂ hn₁ hn₂).value f I = I.answer :=
  roundValue_eq _ (implements_twoCallRound WF μ c₁ c₂ g hwf₁ hwf₂ hμ₁ hμ₂ hn₁ hn₂)
    (fun Im _ => hg Im) f I hI hf

/-! ### A round on raw types, with its cost data

`Algo.Round.Cost` is a long list of hypotheses, so here is a round that meets all of them.
It is the trivial round on `Algo.RawSI`: no children, and the answer `none`.  What it checks
is that the fields are jointly satisfiable and that the `RAM.QuasiPolyFun` requirements are
in a form the combinators of `Workspace/Machine/` can discharge. -/

/-- The trivial round on raw String Isomorphism instances. -/
def rawLeafRound : Round RawSI ℕ RawCoset where
  WF := fun _ => True
  ground := fun I => Enc.size I
  measure := fun _ => 0
  width := fun _ => 0
  child := fun _ => none
  init := fun _ => 0
  combine := fun p => p.2.2.1
  finish := fun _ => none
  bot := none
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := fun _ _ _ _ _ h => by simp at h
  child_measure := fun _ _ _ _ _ h => by simp at h
  child_ground := fun _ _ _ _ _ h => by simp at h

/-- **`Algo.Round.Cost` is satisfiable.** -/
def rawLeafCost : Round.Cost rawLeafRound where
  bound := fun n => n + Enc.size (0 : ℕ) + Enc.size (none : RawCoset)
  polyBound_bound := by
    refine ⟨Enc.size (0 : ℕ) + Enc.size (none : RawCoset) + 1, 1, fun n => ?_⟩
    have : n + 1 ≤ (n + 1) ^ 1 := by simp
    nlinarith [Nat.zero_le n]
  mono_bound := by
    intro a b hab
    dsimp only
    omega
  widthBound := fun _ => 0
  quasiPolyBound_widthBound := (PolyBound.mono ⟨0, 0, fun _ => by simp⟩ (fun _ => le_refl 0)).quasiPoly
  quasiPolyFun_child := (quasiPolyFun_const _)
  quasiPolyFun_init := (quasiPolyFun_const _)
  quasiPolyFun_combine :=
    ((polyFun_snd.comp (polyFun_snd.comp polyFun_fst)).quasiPolyFun).of_eq (fun _ => rfl)
  quasiPolyFun_finish := (quasiPolyFun_const _)
  ground_le := fun _ => le_refl _
  size_le := fun _ _ => by dsimp only [rawLeafRound]; omega
  init_le := fun _ _ => by dsimp only [rawLeafRound]; omega
  combine_le := fun _ _ _ _ _ hs _ => hs
  finish_le := fun _ _ _ _ => by dsimp only [rawLeafRound]; omega
  bot_le := fun _ => by dsimp only [rawLeafRound]; omega
  width_le := fun _ _ => le_refl _

end Algo
