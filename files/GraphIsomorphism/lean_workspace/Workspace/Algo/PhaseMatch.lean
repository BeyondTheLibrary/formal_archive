/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: how a round built from several phases is matched with its
mathematical reduction, one phase at a time.
-/
import Workspace.Algo.Round

/-!
# A phase rule for `Algo.LoopMatch`

`Algo.LoopMatch` (`Workspace/Algo/Round.lean`) says that the fold of a raw round walks a
mathematical reduction.  It has two rules: both sides stop, or both sides make the same
call.  A reduction built by `Babai.SIReduction.bind` — first do this, then with the value do
that — has no rule of its own, so every multi-phase round so far (the imprimitive round, the
two top rounds, the local certificate round) re-proved the sequencing by hand, inside one
induction on the whole budget.  This file proves the sequencing once.

## The two relations

`Algo.LoopMatchK` is `Algo.LoopMatch` for a reduction that *returns a value* instead of
ending the fold.  Its statement is: from `(w, j, s)` the fold of `R` at the instance `I`
walks the reduction `T`, and when `T` stops with a value `v` the fold stands at some
`(w', j', s')` with `Q v w' j' s'`.  The quantification over raw answers is the one of
`Algo.LoopMatch.call`: a child may return **any** raw answer that decodes to the true answer
of the child instance.  `Algo.loopMatchK_run` proves that this reading is the right one.

`Algo.PhaseMatch R decI decA I c j s T P` is the form used in practice:

```
∀ r, LoopMatchK R decI decA I (c + r) j s T (fun b w' j' s' => r ≤ w' ∧ P b j' s')
```

"the phase `T` makes at most `c` calls, and it leaves the fold at a state satisfying `P`".
The leftover budget `r` is universally quantified, so phases compose by adding their call
bounds (`Algo.phaseMatch_bind`), and the budget of a whole round is the sum of the per-phase
bounds.  This is the shape a `Round.width` field wants.

## Main results

* `Algo.loopMatch_bind`, `Algo.loopMatchK_bind` — the bind rule, in the two forms;
* `Algo.phaseMatch_done`, `Algo.phaseMatch_call`, `Algo.phaseMatch_bind` — the same for
  phases, with the call budget;
* `Algo.loopMatch_of_phaseMatch` — a phase that ends the round;
* `Algo.phaseMatch_fold`, `Algo.phaseMatch_iter` — the iteration rules: a loop over a list
  of jobs, and a loop on a counter, with an invariant carried from one job to the next;
* `Algo.loopMatchK_embed`, `Algo.phaseMatch_embed` — the rules survive the embedding of a
  sub-round into a master round, the one of `Algo.loopMatch_embed`
  (`Workspace/Algo/A15Compose.lean`);
* `Algo.loopMatch_mono`, `Algo.phaseMatch_mono` — a larger budget is allowed;
* `Algo.loopMatchK_run`, `Algo.phaseMatch_calls_length_le` — what the budget means: with a
  correct child oracle, a phase cannot make more calls than its bound.

Nothing here mentions Sec. 12: the rules are about `Algo.Round` and `Babai.SIReduction`
only.

No axiom, no `sorry`.
-/

universe u v w w'

namespace Algo

open Babai

variable {ι ω α ι' ω' : Type*} {Ω : Type u} {A : Type v} {β : Type w} {γ : Type w'}

/-! ## `bind` of a reduction that returns its own value -/

/-- Binding with `done` changes nothing. -/
theorem bind_done (T : SIReduction Ω A β) : T.bind (fun b => .done b) = T := by
  induction T with
  | done b => rfl
  | call I k ih => exact congrArg (SIReduction.call I) (funext fun a => ih a)

/-! ## The fold of a round walks a reduction that returns a value -/

/-- **The fold of `R` from `(w, j, s)` walks the reduction `T`, and stops at `Q`.**

Same reading as `Algo.LoopMatch`, except that `T` returns a value of type `β` instead of
ending the round: when `T` stops with a value `b`, the fold stands at some state, and `Q`
is what is known of the value, of the remaining budget, of the index and of the state.
`Algo.LoopMatch` is the special case where the fold stops as well.

All arguments of the constructors are explicit, so that `induction h with | done … | call …`
binds them (see `lean_knowledge.md`). -/
inductive LoopMatchK (R : Round ι ω α) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A β → (β → ℕ → ℕ → ω → Prop) → Prop where
  /-- The reduction stops with the value `b`, and the fold is where `Q` says. -/
  | done (w j : ℕ) (s : ω) (b : β) (Q : β → ℕ → ℕ → ω → Prop) (hq : Q b w j s) :
      LoopMatchK R decI decA I w j s (.done b) Q
  /-- Both ask the same instance, and continue to match for every raw answer that decodes
  to its true answer. -/
  | call (w j : ℕ) (s : ω) (J : ι) (k : Set (Equiv.Perm Ω) → SIReduction Ω A β)
      (Q : β → ℕ → ℕ → ω → Prop) (hc : R.child (I, j, s) = some J)
      (hnext : ∀ a : α, decA a = (decI J).answer →
        LoopMatchK R decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer) Q) :
      LoopMatchK R decI decA I (w + 1) j s (.call (decI J) k) Q

variable {R : Round ι ω α} {decI : ι → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
  {I : ι}

/-! ### Weakening -/

/-- **A larger budget is allowed.**  `Algo.LoopMatch.done` accepts any budget, so only the
calls have to be counted. -/
theorem loopMatch_mono : ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
    LoopMatch R decI decA I w j s T → ∀ {w' : ℕ}, w ≤ w' →
      LoopMatch R decI decA I w' j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => intro w' _; exact LoopMatch.done w' j s a hc ha
  | call w j s J k hc hnext ih =>
    intro w' hw
    obtain ⟨w'', rfl⟩ : ∃ w'', w' = w'' + 1 := ⟨w' - 1, by omega⟩
    exact LoopMatch.call w'' j s J k hc fun a ha => ih a ha (by omega)

/-- **A larger budget and a weaker conclusion are allowed.**  The budget grows by `d`, so
the remaining budget at the stop grows by `d` too. -/
theorem loopMatchK_weaken {Q Q' : β → ℕ → ℕ → ω → Prop} (d : ℕ)
    (hQ : ∀ b w' j' s', Q b w' j' s' → Q' b (w' + d) j' s') :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchK R decI decA I w j s T Q → LoopMatchK R decI decA I (w + d) j s T Q' := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact LoopMatchK.done (w + d) j s b Q' (hQ b w j s hq)
  | call w j s J k Q hc hnext ih =>
    rw [show w + 1 + d = w + d + 1 by omega]
    exact LoopMatchK.call (w + d) j s J k Q' hc fun a ha => ih a ha hQ

/-- Weakening the conclusion alone. -/
theorem loopMatchK_mono_Q {Q Q' : β → ℕ → ℕ → ω → Prop}
    (hQ : ∀ b w' j' s', Q b w' j' s' → Q' b w' j' s') {w j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : LoopMatchK R decI decA I w j s T Q) :
    LoopMatchK R decI decA I w j s T Q' := by
  have := loopMatchK_weaken (R := R) (decI := decI) (decA := decA) (I := I) (Q := Q)
    (Q' := Q') 0 (fun b w' j' s' hb => by simpa using hQ b w' j' s' hb) h
  simpa using this

/-! ### The bind rule -/

/-- **The bind rule.**  A phase `T` that leaves the fold at `Q`, followed by a continuation
that matches from every state `Q` allows, matches `T.bind k`.

*Proof.*  Induction on the derivation for `T`.  At a stop, `(.done b).bind k = k b` and the
hypothesis applies to the state the fold has reached.  At a call, `bind` pushes into the
continuation of the call, so the same child is asked and the induction hypothesis gives the
rest. -/
theorem loopMatch_bind {Q : β → ℕ → ℕ → ω → Prop}
    {k : β → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hk : ∀ (b : β) (w' j' : ℕ) (s' : ω), Q b w' j' s' →
      LoopMatch R decI decA I w' j' s' (k b)) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchK R decI decA I w j s T Q → LoopMatch R decI decA I w j s (T.bind k) := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact hk b w j s hq
  | call w j s J k' Q hc hnext ih =>
    exact LoopMatch.call w j s J (fun a => (k' a).bind k) hc fun a ha => ih a ha hk

/-- **The bind rule, phases composing.**  Same as `Algo.loopMatch_bind`, with a reduction
that returns a value again, so that a round of three phases is matched by two applications
of this rule and one of `Algo.loopMatch_bind`. -/
theorem loopMatchK_bind {Q : β → ℕ → ℕ → ω → Prop} {Q' : γ → ℕ → ℕ → ω → Prop}
    {k : β → SIReduction Ω A γ}
    (hk : ∀ (b : β) (w' j' : ℕ) (s' : ω), Q b w' j' s' →
      LoopMatchK R decI decA I w' j' s' (k b) Q') :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β},
      LoopMatchK R decI decA I w j s T Q →
        LoopMatchK R decI decA I w j s (T.bind k) Q' := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact hk b w j s hq
  | call w j s J k' Q hc hnext ih =>
    exact LoopMatchK.call w j s J (fun a => (k' a).bind k) Q' hc fun a ha => ih a ha hk

/-! ### What the budget means

With a child oracle that answers correctly, a matching derivation for `T` uses exactly
`T.calls.length` of the budget, and the state it reaches satisfies `Q` at the value `T.run`.
This is the counterpart of `Algo.LoopMatch.calls_length_le` (`Workspace/Algo/TopWindow.lean`)
and it is why the budget of a round can be read off the call bounds of its phases.  The
oracle is needed because a raw answer decoding to a given answer set need not exist. -/

/-- **A phase consumes its calls, and stops where `Q` says.** -/
theorem loopMatchK_run (rec : ι → α) (hrec : ∀ J, decA (rec J) = (decI J).answer)
    {Q : β → ℕ → ℕ → ω → Prop} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β}, LoopMatchK R decI decA I w j s T Q →
      T.calls.length ≤ w ∧
        ∃ s' : ω, Q T.run (w - T.calls.length) (j + T.calls.length) s' := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact ⟨by simp, s, by simpa using hq⟩
  | call w j s J k Q hc hnext ih =>
    obtain ⟨h1, s', h2⟩ := ih (rec J) (hrec J)
    refine ⟨by rw [SIReduction.calls_call, List.length_cons]; omega, s', ?_⟩
    rw [SIReduction.calls_call, List.length_cons, SIReduction.run_call]
    have he1 : w + 1 - ((k (decI J).answer).calls.length + 1)
        = w - (k (decI J).answer).calls.length := by omega
    have he2 : j + ((k (decI J).answer).calls.length + 1)
        = j + 1 + (k (decI J).answer).calls.length := by omega
    rw [he1, he2]
    exact h2

/-! ## Phases with a call bound

`Algo.PhaseMatch R decI decA I c j s T P` is the working form: the phase `T` starts at
`(j, s)`, makes at most `c` calls, and leaves the fold at a state satisfying `P`.  The
leftover budget is universally quantified, which is what makes the bounds add up. -/

/-- **A phase with a call bound.**  From any budget `c + r` the phase `T` walks the fold,
leaving at least `r` of the budget and a state satisfying `P`. -/
def PhaseMatch (R : Round ι ω α) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (I : ι) (c j : ℕ) (s : ω) (T : SIReduction Ω A β)
    (P : β → ℕ → ω → Prop) : Prop :=
  ∀ r : ℕ, LoopMatchK R decI decA I (c + r) j s T (fun b w' j' s' => r ≤ w' ∧ P b j' s')

/-- A phase that does nothing. -/
theorem phaseMatch_done {P : β → ℕ → ω → Prop} {j : ℕ} {s : ω} {b : β} (hp : P b j s) :
    PhaseMatch R decI decA I 0 j s (.done b) P := by
  intro r
  exact LoopMatchK.done (0 + r) j s b _ ⟨by omega, hp⟩

/-- A phase that starts with one call. -/
theorem phaseMatch_call {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω} {J : ι}
    {k : Set (Equiv.Perm Ω) → SIReduction Ω A β} (hc : R.child (I, j, s) = some J)
    (hnext : ∀ a : α, decA a = (decI J).answer →
      PhaseMatch R decI decA I c (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer) P) :
    PhaseMatch R decI decA I (c + 1) j s (.call (decI J) k) P := by
  intro r
  have he : c + 1 + r = c + r + 1 := by omega
  rw [he]
  exact LoopMatchK.call (c + r) j s J k _ hc fun a ha => hnext a ha r

/-- **A larger call bound is allowed.** -/
theorem phaseMatch_mono {P : β → ℕ → ω → Prop} {c c' j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : PhaseMatch R decI decA I c j s T P) (hc : c ≤ c') :
    PhaseMatch R decI decA I c' j s T P := by
  intro r
  have he : c' + r = c + ((c' - c) + r) := by omega
  rw [he]
  exact loopMatchK_mono_Q (fun b w' j' s' hb => ⟨by omega, hb.2⟩) (h ((c' - c) + r))

/-- Weakening what is known of the state at the end of a phase. -/
theorem phaseMatch_weaken {P P' : β → ℕ → ω → Prop} {c j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : PhaseMatch R decI decA I c j s T P)
    (hP : ∀ b j' s', P b j' s' → P' b j' s') : PhaseMatch R decI decA I c j s T P' :=
  fun r => loopMatchK_mono_Q (fun b _w' j' s' hb => ⟨hb.1, hP b j' s' hb.2⟩) (h r)

/-- **Two phases one after the other**: the call bounds add up. -/
theorem phaseMatch_bind {P : β → ℕ → ω → Prop} {P' : γ → ℕ → ω → Prop} {c₁ c₂ j : ℕ}
    {s : ω} {T : SIReduction Ω A β} {k : β → SIReduction Ω A γ}
    (h : PhaseMatch R decI decA I c₁ j s T P)
    (hk : ∀ (b : β) (j' : ℕ) (s' : ω), P b j' s' →
      PhaseMatch R decI decA I c₂ j' s' (k b) P') :
    PhaseMatch R decI decA I (c₁ + c₂) j s (T.bind k) P' := by
  intro r
  have he : c₁ + c₂ + r = c₁ + (c₂ + r) := by omega
  rw [he]
  refine loopMatchK_bind (Q := fun b w' j' s' => c₂ + r ≤ w' ∧ P b j' s') ?_ (h (c₂ + r))
  rintro b w' j' s' ⟨hw, hp⟩
  have he' : w' = c₂ + (w' - c₂) := by omega
  rw [he']
  exact loopMatchK_mono_Q (fun b' w'' j'' s'' hb => ⟨by omega, hb.2⟩) (hk b j' s' hp (w' - c₂))

/-- **A phase that ends the round.**  If the state at the end of the phase is one where the
round has no further child and `finish` reads off the value of the phase, then the whole
fold matches the phase. -/
theorem loopMatch_of_phaseMatch {P : Set (Equiv.Perm Ω) → ℕ → ω → Prop} {c j w : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : PhaseMatch R decI decA I c j s T P)
    (hfin : ∀ (b : Set (Equiv.Perm Ω)) (j' : ℕ) (s' : ω), P b j' s' →
      R.child (I, j', s') = none ∧ decA (R.finish (I, s')) = b)
    (hw : c ≤ w) : LoopMatch R decI decA I w j s T := by
  have hb := loopMatch_bind (k := fun b => (.done b : SIReduction Ω A (Set (Equiv.Perm Ω))))
    (Q := fun b w' j' s' => w - c ≤ w' ∧ P b j' s')
    (fun b w' j' s' hb => LoopMatch.done w' j' s' b (hfin b j' s' hb.2).1
      (hfin b j' s' hb.2).2) (h (w - c))
  rw [bind_done] at hb
  exact loopMatch_mono hb (by omega)

/-- **The call bound is a real bound.**  With a correct child oracle, a phase makes at most
`c` calls. -/
theorem phaseMatch_calls_length_le (rec : ι → α)
    (hrec : ∀ J, decA (rec J) = (decI J).answer) {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω}
    {T : SIReduction Ω A β} (h : PhaseMatch R decI decA I c j s T P) :
    T.calls.length ≤ c := by
  have := (loopMatchK_run rec hrec (h 0)).1
  omega

/-! ## Iteration

A phase which is a loop over a list of jobs, or a loop on a counter: an invariant is carried
from one job to the next, and the call bounds of the jobs add up.  This is the shape of
`Algo.cosetChain` (the Chain Rule over the orbits), of `Babai.SIReduction.sequence`, and of
the job loops of `Algo.top2Round` and `Algo.top3Round`. -/

/-- The reduction that runs one job after another, handing the value of each job to the
next.  `Babai.SIReduction.sequence` and `Algo.cosetChain` are of this shape. -/
def phaseFold (step : β → γ → SIReduction Ω A β) : β → List γ → SIReduction Ω A β
  | b, [] => .done b
  | b, g :: gs => (step b g).bind fun b' => phaseFold step b' gs

@[simp] theorem phaseFold_nil (step : β → γ → SIReduction Ω A β) (b : β) :
    phaseFold step b [] = .done b := rfl

theorem phaseFold_cons (step : β → γ → SIReduction Ω A β) (b : β) (g : γ)
    (gs : List γ) :
    phaseFold step b (g :: gs) = (step b g).bind fun b' => phaseFold step b' gs := rfl

/-- **The iteration rule over a list of jobs.**  `Inv gs b j s` is the invariant *before*
the jobs `gs`, with the value carried so far, the index of the fold and its state.  One job
costs `cost g` calls, so the whole loop costs the sum. -/
theorem phaseMatch_fold {step : β → γ → SIReduction Ω A β} {cost : γ → ℕ}
    {Inv : List γ → β → ℕ → ω → Prop}
    (hstep : ∀ (g : γ) (gs : List γ) (b : β) (j : ℕ) (s : ω), Inv (g :: gs) b j s →
      PhaseMatch R decI decA I (cost g) j s (step b g) fun b' j' s' => Inv gs b' j' s') :
    ∀ (gs : List γ) (b : β) (j : ℕ) (s : ω), Inv gs b j s →
      PhaseMatch R decI decA I ((gs.map cost).sum) j s (phaseFold step b gs)
        fun b' j' s' => Inv [] b' j' s' := by
  intro gs
  induction gs with
  | nil => intro b j s hb; simpa using phaseMatch_done (R := R) (decI := decI) hb
  | cons g gs ih =>
    intro b j s hb
    rw [phaseFold_cons, List.map_cons, List.sum_cons]
    exact phaseMatch_bind (hstep g gs b j s hb) fun b' j' s' hb' => ih b' j' s' hb'

/-- Every job costs the same: the loop costs the number of jobs times that. -/
theorem phaseMatch_fold_const {step : β → γ → SIReduction Ω A β} {c : ℕ}
    {Inv : List γ → β → ℕ → ω → Prop}
    (hstep : ∀ (g : γ) (gs : List γ) (b : β) (j : ℕ) (s : ω), Inv (g :: gs) b j s →
      PhaseMatch R decI decA I c j s (step b g) fun b' j' s' => Inv gs b' j' s')
    (gs : List γ) (b : β) (j : ℕ) (s : ω) (hb : Inv gs b j s) :
    PhaseMatch R decI decA I (gs.length * c) j s (phaseFold step b gs)
      fun b' j' s' => Inv [] b' j' s' := by
  have h := phaseMatch_fold (cost := fun _ => c) hstep gs b j s hb
  simpa [List.map_const', List.sum_replicate, Nat.smul_one_eq_cast] using h

/-- The reduction that runs `m` jobs, numbered `i`, `i+1`, …, handing the value of each job
to the next.  This is the shape of a loop on a bounded counter. -/
def phaseIter (step : ℕ → β → SIReduction Ω A β) : ℕ → ℕ → β → SIReduction Ω A β
  | 0, _, b => .done b
  | m + 1, i, b => (step i b).bind fun b' => phaseIter step m (i + 1) b'

@[simp] theorem phaseIter_zero (step : ℕ → β → SIReduction Ω A β) (i : ℕ) (b : β) :
    phaseIter step 0 i b = .done b := rfl

theorem phaseIter_succ (step : ℕ → β → SIReduction Ω A β) (m i : ℕ) (b : β) :
    phaseIter step (m + 1) i b = (step i b).bind fun b' => phaseIter step m (i + 1) b' := rfl

/-- **The iteration rule on a counter.**  `Inv i b j s` is the invariant before job `i`.
The loop runs the jobs `i`, …, `n - 1`, each at a cost of `c` calls. -/
theorem phaseMatch_iter {step : ℕ → β → SIReduction Ω A β} {c n : ℕ}
    {Inv : ℕ → β → ℕ → ω → Prop}
    (hstep : ∀ (i : ℕ) (b : β) (j : ℕ) (s : ω), i < n → Inv i b j s →
      PhaseMatch R decI decA I c j s (step i b) fun b' j' s' => Inv (i + 1) b' j' s') :
    ∀ (m i : ℕ), i + m = n → ∀ (b : β) (j : ℕ) (s : ω), Inv i b j s →
      PhaseMatch R decI decA I (m * c) j s (phaseIter step m i b)
        fun b' j' s' => Inv n b' j' s' := by
  intro m
  induction m with
  | zero =>
    intro i hi b j s hb
    have : i = n := by omega
    subst this
    simpa using phaseMatch_done (R := R) (decI := decI) hb
  | succ m ih =>
    intro i hi b j s hb
    rw [phaseIter_succ, show (m + 1) * c = c + m * c by ring]
    exact phaseMatch_bind (hstep i b j s (by omega) hb)
      fun b' j' s' hb' => ih (i + 1) (by omega) b' j' s' hb'

/-! ## The rules survive an embedding

`Algo.loopMatch_embed` (`Workspace/Algo/A15Compose.lean`) transports a matching derivation of
a sub-round `R` into one of a master round `M`, along an embedding `e` of instances and `u`
of states.  The same transport works for `Algo.LoopMatchK` and `Algo.PhaseMatch`, and it
needs one hypothesis less: `finish` plays no part, because a phase does not end the round.
The state at the end of the transported phase is an embedded state, which is what the
conclusion records. -/

/-- **A phase of a sub-round is a phase of the master round.** -/
theorem loopMatchK_embed {M : Round ι' ω' α} {decI' : ι' → SIInstance Ω A}
    (e : ι → ι') (u : ω → ω') (I : ι) {Q : β → ℕ → ℕ → ω → Prop}
    (hdec : ∀ J : ι, decI' (e J) = decI J)
    (hchild : ∀ (j : ℕ) (s : ω), M.child (e I, j, u s) = (R.child (I, j, s)).map e)
    (hcomb : ∀ (j : ℕ) (s : ω) (a : α),
      M.combine (e I, j, u s, a) = u (R.combine (I, j, s, a))) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β}, LoopMatchK R decI decA I w j s T Q →
      LoopMatchK M decI' decA (e I) w j (u s) T
        fun b w' j' s' => ∃ s₀ : ω, s' = u s₀ ∧ Q b w' j' s₀ := by
  intro w j s T h
  induction h with
  | done w j s b Q hq => exact LoopMatchK.done w j (u s) b _ ⟨s, rfl, hq⟩
  | call w j s J k Q hc hnext ih =>
    have hcM : M.child (e I, j, u s) = some (e J) := by rw [hchild j s, hc]; rfl
    have hJ : decI' (e J) = decI J := hdec J
    refine (hJ ▸ LoopMatchK.call (R := M) (decI := decI') (decA := decA) (I := e I)
      w j (u s) (e J) k _ hcM ?_)
    intro a ha
    have ha' : decA a = (decI J).answer := by rw [← hJ]; exact ha
    have hstep := ih a ha'
    rw [hcomb j s a]
    exact hJ ▸ hstep

/-- **A phase with its call bound survives an embedding.** -/
theorem phaseMatch_embed {M : Round ι' ω' α} {decI' : ι' → SIInstance Ω A}
    (e : ι → ι') (u : ω → ω') (I : ι) {P : β → ℕ → ω → Prop} {c j : ℕ} {s : ω}
    {T : SIReduction Ω A β}
    (hdec : ∀ J : ι, decI' (e J) = decI J)
    (hchild : ∀ (j : ℕ) (s : ω), M.child (e I, j, u s) = (R.child (I, j, s)).map e)
    (hcomb : ∀ (j : ℕ) (s : ω) (a : α),
      M.combine (e I, j, u s, a) = u (R.combine (I, j, s, a)))
    (h : PhaseMatch R decI decA I c j s T P) :
    PhaseMatch M decI' decA (e I) c j (u s) T
      fun b j' s' => ∃ s₀ : ω, s' = u s₀ ∧ P b j' s₀ := by
  intro r
  refine loopMatchK_mono_Q ?_ (loopMatchK_embed e u I hdec hchild hcomb (h r))
  rintro b w' j' s' ⟨s₀, rfl, hw, hp⟩
  exact ⟨hw, s₀, rfl, hp⟩

end Algo
