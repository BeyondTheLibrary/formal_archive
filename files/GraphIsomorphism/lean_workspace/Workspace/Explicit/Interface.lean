/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the interface between
part 1 (costs inside a node) and part 2 (the recursion across nodes and the assembly).
See `Workspace/Explicit/DESIGN.md`, Sec. 5.

This file is not part of the faithful formalization. It only defines things; nothing is
proved here.
-/
import Workspace.Algo.TopMasterClose

/-!
# The interface of the explicit running time

* `Explicit.Params`: the numeric parameters that `Algo.masterFinalOps` takes by
  `Classical.choose`, as explicit data.
* `Explicit.masterOpsE`, `Explicit.masterRoundE`: the variant Master round at these
  parameters. It is `Algo.masterFinalOps` with `c = 0`, `c' = 2`, `b' = 0` (the constants of
  `Algo.theorem_1_1_1`), the hint routines `Algo.line4dDomHint` and `Algo.masterL57Hint`, and
  every chosen constant replaced by a field of `Params`.
* `Explicit.countE`: the step count of the variant top evaluator.
* `Explicit.ParamsOK`: the specifications the existing correctness proofs ask of the
  parameters (owner: part 1).
* `Explicit.CleanComputePW`: clean time bounded pointwise, not through the input size.
* `Explicit.StepBounds`: what part 1 proves about one node, with explicit numeric fields.

Part 2 proves the final theorem from `ParamsOK` and `StepBounds`. Tier 1 of the project is
`∃ sb : StepBounds …` (numeric fields existential); tier 2 gives the numeric fields as
closed expressions in the constants of the Cameron routine.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-! ## The variant program -/

/-- The numeric parameters of the Master's node carrier, explicit. Each field replaces one
`Classical.choose` of `Algo.masterFinalOps` / `Algo.siWorkspaceRoutine`:

* `B`, `C₀`: `Algo.masterLine1B`, `Algo.masterLine1C₀` (line 1, Sec. 11.3);
* `a`, `b`: `Algo.masterCapA`, `Algo.masterCapB` (admission caps);
* `e`, `f`, `u`, `v`: `Algo.masterTopE`, `Algo.masterTopF`, `Algo.masterTopU`,
  `Algo.masterTopV` (window caps);
* `u'`, `v'`: `Algo.l57UV e f` (the window caps of the hint of lines 5–7; the round of
  lines 5–7 itself always runs with `Algo.l57UV e f`);
* `tt`, `dd`: the fuel exponent and state cap of `Algo.sbipRun` (Sec. 9) at line 4c,
  `Algo.masterLine4TT 0`, `Algo.masterLine4DD 0`;
* `t`, `d`: the same for lines 5–7 (`Algo.exists_l57Constants`);
* `dc`, `dp`: `Algo.exists_aggnPhasesOK 2`;
* `E`: `Algo.masterL57E` (reserve exponent of lines 5–7). -/
structure Params where
  B : ℕ
  C₀ : ℕ
  a : ℕ
  b : ℕ
  e : ℕ
  f : ℕ
  u : ℕ
  v : ℕ
  u' : ℕ
  v' : ℕ
  tt : ℕ
  dd : ℕ
  t : ℕ
  d : ℕ
  dc : ℕ
  dp : ℕ
  E : ℕ

/-- The hint routine of lines 5–7 at the parameters `p`. -/
noncomputable abbrev hint5E (p : Params) :
    (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI → Option RawMasterHint :=
  masterL57Hint 2 0 p.t p.d p.dc p.dp p.u' p.v' p.e p.f

/-- The node carrier of the variant Master: `Algo.masterNodeHOps` at explicit parameters. -/
noncomputable abbrev masterOpsE (p : Params) (cam : RawGens × List ℕ → Option RawCameron) :=
  masterNodeHOps p.B p.C₀ cam p.e p.f p.u p.v 0 p.tt p.dd
    (line4dDomOps 0 p.tt p.dd) default 2 0 p.t p.d p.dc p.dp p.E
    (line4dDomHint 0 p.tt p.dd) (hint5E p)

/-- The state type of the variant round. -/
abbrev StateE : Type :=
  AggnRecomputeState × MasterHintState (ADState × AggnRecomputeState) AggnL57GState

/-- **The variant Master round.** -/
noncomputable abbrev masterRoundE (p : Params) (cam : RawGens × List ℕ → Option RawCameron) :
    Round.{0, 0, 0} RawMasterSI StateE RawCoset :=
  masterAdmittedRound p.a p.b (masterOpsE p cam)

/-- The state of the depth-first evaluator of the variant round. -/
abbrev EvalStateE : Type := Round.EvalState RawMasterSI StateE RawCoset

/-- **The step count of the variant top evaluator**: `3·2^{K·(log₂ n + 2)^5} + 1`. -/
def countE (K n : ℕ) : ℕ := 3 * 2 ^ (K * (Nat.log 2 n + 2) ^ 5) + 1

/-! ## The specifications of the parameters -/

/-- **The specifications of the parameters** (rows 6–11 of the table of `DESIGN.md`): what
the existing correctness lemmas ask of the constants they receive. Owner: part 1. -/
structure ParamsOK (p : Params) : Prop where
  /-- Line 1 at the thresholds of `Algo.theorem_1_1_1` (tier 1; these thresholds come from
  Theorem 11.2.1 and Proposition 11.2.5 and only enter the constant `C`). -/
  line1 : p.B = masterLine1B ∧ p.C₀ = masterLine1C₀
  topwp : TopwpCap p.e p.f
  top4w : Top4wCap p.e p.f p.u p.v
  /-- The window caps of the hint of lines 5–7 are the ones the round of lines 5–7 runs with
  (`Algo.masterL57Round` takes `Algo.l57UV e f`; tier 1). -/
  l57 : p.u' = (l57UV p.e p.f).1 ∧ p.v' = (l57UV p.e p.f).2
  cap : ∀ n, masterCameronChildBound n ≤ masterInputCap p.a p.b n
  l4c : Line4cBounds 0 p.tt p.dd
  l57entry : AggnRestoredEntryGood 2 0 p.t p.d
  l57bip : BipInputRunCanonical 0 p.t p.d
  phases : AggnPhasesOK 2 p.dc p.dp
  reserve : MasterL57EOK 2 0 p.t p.d p.dc p.dp p.e p.f p.E

/-! ## Pointwise clean time -/

/-- **Clean time, pointwise**: started in `initMemAt K (encode a)`, `P` halts within `τ a`
steps in `initMemAt K (encode (f a))`. `RAM.CleanComputeAt` is the case `τ = T ∘ Enc.size`. -/
def CleanComputePW (K : ℕ) {α β : Type*} [Enc α] [Enc β] (P : Program) (f : α → β)
    (τ : α → ℕ) : Prop :=
  ∀ a : α, RunsTo P (fun m => m = initMemAt K (Enc.encode a))
    (fun m' => m' = initMemAt K (Enc.encode (f a))) (τ a)

theorem cleanComputePW_of_cleanComputeAt {K : ℕ} {α β : Type*} [Enc α] [Enc β] {P : Program}
    {f : α → β} {T : ℕ → ℕ} (h : CleanComputeAt K P f T) :
    CleanComputePW K P f (fun a => T (Enc.size a)) := h

/-! ## What part 1 delivers -/

/-- **The explicit costs of one node of the variant round.** All numeric fields are explicit
in tier 2 (closed expressions in the constants of the Cameron routine), existential in tier 1.

* sizes: the fields of `Algo.Round.RunCostQ`, with explicit bounds; the states of a run
  through the invariant (`inv_size`, R4);
* calls: at a good node of degree `n`, the run makes at most `2^{Aw (log₂ n+2)^4}` calls at
  route 1 (line 2, `m ≤ ℓ = (log n)^3`), at most `2^{Ap (log₂ n+2)^3}` elsewhere (R3);
* one DFS step (with the loop counter), on every state satisfying the invariant `Inv n` of
  a run from a root of degree `n`, in time quasipolynomial in `n` and polynomial in the size
  of the state: `2^{As (log₂ n+2)^5}·(size+1)^ds`;
* the polynomial routines around the loop: the entry (normalization and root), `ground`,
  the well-formedness test, `init`, and the read-off. -/
structure StepBounds (p : Params) (cam : RawGens × List ℕ → Option RawCameron) where
  /-- The cost data of the round (sizes, routines, widths). -/
  cost : Round.RunCostQ (masterRoundE p cam)
  kB : ℕ
  dB : ℕ
  bound_le : ∀ n, cost.bound n ≤ 2 ^ kB * (n + 1) ^ dB
  kM : ℕ
  dM : ℕ
  measure_le : ∀ n, cost.measureBound n ≤ 2 ^ kM * (n + 1) ^ dM
  Aw : ℕ
  /-- The calls of the run at a good node of route 1 (line 2). Interface change R3: the calls
  of the run, not the width, which is only fuel. -/
  calls_line2 : ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
    (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P = 1 →
    ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Aw * (Nat.log 2 n + 2) ^ 4)
  Ap : ℕ
  /-- The calls of the run at every other good node. -/
  calls_other : ∀ (n : ℕ) (P : RawMasterSI) (f : ℕ), MasterNodeGood n P →
    (masterRoundE p cam).WF P → (masterRoundE p cam).measure P < f + 1 → masterRoute P ≠ 1 →
    ((masterRoundE p cam).roundCalls f P).length ≤ 2 ^ (Ap * (Nat.log 2 n + 2) ^ 3)
  As : ℕ
  ds : ℕ
  /-- A whole-state invariant of the runs, defined by part 1 (interface change R1): the
  indexed degree is the degree of the root of the run. -/
  Inv : ℕ → EvalStateE → Prop
  /-- The invariant starts at good roots (interface change R5). -/
  inv_start : ∀ I, (masterRoundE p cam).WF I → MasterNodeGood (masterDegree I) I →
    Inv (masterDegree I) ((masterRoundE p cam).startState I)
  inv_step : ∀ n x, Inv n x → Inv n ((masterRoundE p cam).stepDFS x)
  kS : ℕ
  /-- The states of the run are quasipolynomially small (interface change R4, in place of a
  bound on `cost.stateBound`, which covers all states and has no explicit exponent). -/
  inv_size : ∀ n x, Inv n x → Enc.size x ≤ 2 ^ (kS * (Nat.log 2 n + 2) ^ 5)
  step : ∃ Q : Program, ∀ (n k : ℕ) (x : EvalStateE), Inv n x →
    RunsTo Q (fun m => m = initMemAt 16 (Enc.encode ((k, x) : ℕ × EvalStateE)))
      (fun m' => m' = initMemAt 16
        (Enc.encode ((k - 1, (masterRoundE p cam).stepDFS x) : ℕ × EvalStateE)))
      (2 ^ (As * (Nat.log 2 n + 2) ^ 5) * (Enc.size ((k, x) : ℕ × EvalStateE) + 1) ^ ds)
  kP : ℕ
  dP : ℕ
  entry : ∃ Q : Program, CleanComputeAt 16 Q (fun I : RawSI => masterRoot (rawNormSI I))
    (fun N => 2 ^ kP * (N + 1) ^ dP)
  entry_size : ∀ I : RawSI, Enc.size (masterRoot (rawNormSI I)) ≤ 2 ^ kP * (Enc.size I + 1) ^ dP
  ground : ∃ Q : Program, CleanComputeAt 16 Q (masterRoundE p cam).ground
    (fun N => 2 ^ kP * (N + 1) ^ dP)
  wfCheck : ∃ Q : Program, CleanComputeAt 16 Q cost.wfCheck (fun N => 2 ^ kP * (N + 1) ^ dP)
  /-- The fold state of a root, at nodes without a hint only (interface change R5). -/
  init : ∃ Q : Program, Wf Q ∧ ∀ J : RawMasterSI, (masterRoundE p cam).WF J → J.2 = none →
    RunsTo Q (fun m => m = initMemAt 16 (Enc.encode J))
      (fun m' => m' = initMemAt 16 (Enc.encode ((masterRoundE p cam).init J)))
      (2 ^ (As * (Nat.log 2 (Enc.size J) + 2) ^ 5) * (Enc.size J + 1) ^ ds)
  readOff : ∃ Q : Program, CleanComputeAt 16 Q (fun x : ℕ × EvalStateE => x.2.2.join)
    (fun N => 2 ^ kP * (N + 1) ^ dP)

end Explicit
