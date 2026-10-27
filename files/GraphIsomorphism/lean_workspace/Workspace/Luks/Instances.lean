/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1: the model of the algorithmic statements — String Isomorphism *instances*
and *reductions*.
-/
import Workspace.Luks.Framework

/-!
# String Isomorphism instances and reductions

Definition 11.1.2 (the String Isomorphism problem) and Definition 11.1.3 (window
isomorphism) give the objects that every algorithmic statement of Sections 12–13 calls an
"instance of String Isomorphism": a set `K ⊆ S(Ω)` of candidate permutations (a group or a
coset), a window `Δ ⊆ Ω`, and a pair of strings.  This file packages them, once, for all
later sections.

* `Babai.SIInstance`: an instance.  `Babai.SIInstance.answer` is `Iso^Δ_K(x,y)`
  (`Babai.wIso`), `Babai.SIInstance.windowSize` is `|Δ|`.
* `Babai.SIReduction`: a *reduction*, a decision tree whose internal nodes are calls to
  String Isomorphism.  `SIReduction.run` is the explicit function that turns the answers
  into the answer of the original question, `SIReduction.calls` is the list of instances
  that the reduction actually produces, so `SIReduction.calls.length` is the number of
  recursive calls and the window sizes of `SIReduction.calls` are the window sizes of the
  recursive calls.  The calls may be *adaptive* (the Chain Rule chooses the next instance
  using the previous answer), which is why a list of instances would not do.
* `Babai.SIReduction.runWith` / `Babai.SIReduction.callsWith`: the same two functions
  relative to an arbitrary *oracle* `O : SIInstance Ω A → Set (Equiv.Perm Ω)`.  These are
  the forms a RAM program with recursive calls realizes: the program does not know the
  answers, it only knows how to build the next instance from the answers it has been
  given.  `run` and `calls` are the special case `O = SIInstance.answer`
  (`Babai.SIReduction.runWith_answer`, `Babai.SIReduction.callsWith_answer`).

The *running time* ("at polynomial cost per instance") is **not** modelled here; see the
pending entries for Sections 12 and 13 in the corrected paper.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise


/-- A String Isomorphism *instance* in the vocabulary of §11.1: a set `K ⊆ S(Ω)` of
candidate permutations (a group or a coset), a window `Δ ⊆ Ω`, and a pair of strings.  Its
answer is the set `Iso^Δ_K(x,y)` of window isomorphisms (`Babai.wIso`). -/
structure SIInstance (Ω : Type u) (A : Type v) where
  /-- The group (or coset) `K ⊆ S(Ω)` of candidate permutations. -/
  K : Set (Equiv.Perm Ω)
  /-- The window `Δ ⊆ Ω`. -/
  Δ : Set Ω
  /-- The first string. -/
  x : Ω → A
  /-- The second string. -/
  y : Ω → A

namespace SIInstance

variable {Ω : Type u} {A : Type v}

/-- The answer to an instance: `Iso^Δ_K(x,y)`. -/
def answer (I : SIInstance Ω A) : Set (Equiv.Perm Ω) := wIso I.Δ I.K I.x I.y

/-- The *window size* of an instance, the quantity the paper's cost statements bound
("String Isomorphism with window size `≤ n/k`"). -/
noncomputable def windowSize (I : SIInstance Ω A) : ℕ := I.Δ.ncard

/-- An instance *with respect to* a group `N`: the paper's "instances of String
Isomorphism with respect to `N`" (Prop. 12.0.5). -/
def IsWithRespectTo (I : SIInstance Ω A) (N : Set (Equiv.Perm Ω)) : Prop := I.K = N

end SIInstance

/-- A *reduction*: a decision tree whose internal nodes are calls to String Isomorphism.
`done a` returns the value `a`; `call I k` asks for the answer to the instance `I` and
continues with `k` applied to that answer.

This is what the paper's "we can achieve the following by recursively calling `N`
instances of String Isomorphism …" means, minus the running time: the calls are the
recursive instances, and the whole tree is the explicit function that turns their answers
into the answer to the original question.  The calls may be *adaptive* (the Chain Rule
chooses the next instance using the previous answer), which is why a list of instances
would not do. -/
inductive SIReduction (Ω : Type u) (A : Type v) (α : Type w) : Type (max u v w)
  /-- Return a value without further calls. -/
  | done (a : α) : SIReduction Ω A α
  /-- Call String Isomorphism on the instance `I` and continue with its answer. -/
  | call (I : SIInstance Ω A) (k : Set (Equiv.Perm Ω) → SIReduction Ω A α) :
      SIReduction Ω A α

namespace SIReduction

universe w'

variable {Ω : Type u} {A : Type v} {α : Type w} {β : Type w'}

/-- The value the reduction computes: the explicit function of the answers to the
instances it calls. -/
def run : SIReduction Ω A α → α
  | .done a => a
  | .call I k => (k I.answer).run

/-- The list of instances the reduction actually produces (its executed calls).  Its
length is the number of recursive calls; the window sizes of its entries are the window
sizes of the recursive calls. -/
def calls : SIReduction Ω A α → List (SIInstance Ω A)
  | .done _ => []
  | .call I k => I :: (k I.answer).calls

@[simp] theorem run_done (a : α) : (SIReduction.done (Ω := Ω) (A := A) a).run = a := rfl

@[simp] theorem calls_done (a : α) :
    (SIReduction.done (Ω := Ω) (A := A) a).calls = [] := rfl

@[simp] theorem run_call (I : SIInstance Ω A) (k : Set (Equiv.Perm Ω) → SIReduction Ω A α) :
    (SIReduction.call I k).run = (k I.answer).run := rfl

@[simp] theorem calls_call (I : SIInstance Ω A)
    (k : Set (Equiv.Perm Ω) → SIReduction Ω A α) :
    (SIReduction.call I k).calls = I :: (k I.answer).calls := rfl

/-- Sequential composition: run `R`, then continue with `g` applied to its value. -/
def bind : SIReduction Ω A β → (β → SIReduction Ω A α) → SIReduction Ω A α
  | .done b, g => g b
  | .call I k, g => .call I (fun a => (k a).bind g)

@[simp] theorem run_bind (R : SIReduction Ω A β) (g : β → SIReduction Ω A α) :
    (R.bind g).run = (g R.run).run := by
  induction R with
  | done b => rfl
  | call I k ih => simpa using ih I.answer

@[simp] theorem calls_bind (R : SIReduction Ω A β) (g : β → SIReduction Ω A α) :
    (R.bind g).calls = R.calls ++ (g R.run).calls := by
  induction R with
  | done b => simp [bind, calls, run]
  | call I k ih => simpa [bind, calls, run] using ih I.answer

/-- Run a list of reductions one after another and collect their values.  This is what a
round does when the paper says *"run the routine for all test sets"*: the runs are
independent, so the list is fixed in advance, and the values are handed on together. -/
def sequence : List (SIReduction Ω A β) → SIReduction Ω A (List β)
  | [] => .done []
  | S :: rest => S.bind fun b => (sequence rest).bind fun bs => .done (b :: bs)

@[simp] theorem sequence_nil :
    sequence ([] : List (SIReduction Ω A β)) = .done [] := rfl

theorem sequence_cons (S : SIReduction Ω A β) (rest : List (SIReduction Ω A β)) :
    sequence (S :: rest) = S.bind fun b => (sequence rest).bind fun bs => .done (b :: bs) :=
  rfl

/-- The value of a list of reductions is the list of their values. -/
@[simp] theorem run_sequence (L : List (SIReduction Ω A β)) :
    (sequence L).run = L.map run := by
  induction L with
  | nil => rfl
  | cons S rest ih => simp [sequence_cons, ih]

/-- The calls of a list of reductions are the calls of its members, one list after the
other. -/
@[simp] theorem calls_sequence (L : List (SIReduction Ω A β)) :
    (sequence L).calls = (L.map calls).flatten := by
  induction L with
  | nil => rfl
  | cons S rest ih => simp [sequence_cons, ih]

/-- Every call of a list of reductions is a call of one of its members. -/
theorem mem_calls_sequence {L : List (SIReduction Ω A β)} {I : SIInstance Ω A}
    (h : I ∈ (sequence L).calls) : ∃ S ∈ L, I ∈ S.calls := by
  rw [calls_sequence, List.mem_flatten] at h
  obtain ⟨l, hl, hI⟩ := h
  obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hl
  exact ⟨S, hS, hI⟩

/-- A list of reductions each of which makes at most `k` calls makes at most
`L.length * k` calls. -/
theorem calls_length_sequence_le {L : List (SIReduction Ω A β)} {k : ℕ}
    (h : ∀ S ∈ L, S.calls.length ≤ k) : (sequence L).calls.length ≤ L.length * k := by
  induction L with
  | nil => simp
  | cons S rest ih =>
    rw [calls_sequence, List.map_cons, List.flatten_cons, List.length_append]
    have h1 : S.calls.length ≤ k := h S List.mem_cons_self
    have h2 : ((rest.map calls).flatten).length ≤ rest.length * k := by
      have := ih fun T hT => h T (List.mem_cons_of_mem _ hT)
      rwa [calls_sequence] at this
    rw [List.length_cons]
    calc S.calls.length + ((rest.map calls).flatten).length
        ≤ k + rest.length * k := Nat.add_le_add h1 h2
      _ = (rest.length + 1) * k := by ring

/-- Substituting a sub-reduction for every call: this is how a reduction to instances
with respect to `N` is composed with a reduction of each `N`-instance to smaller
instances (Cor. 12.0.6: Prop. 12.0.5 followed by the Chain Rule). -/
def expand (f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction Ω A α → SIReduction Ω A α
  | .done a => .done a
  | .call I k => (f I).bind (fun ans => (k ans).expand f)

/-- If every sub-reduction computes the answer to the instance it replaces, then
substitution does not change the value computed. -/
theorem run_expand {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ I, (f I).run = I.answer) (R : SIReduction Ω A α) :
    (R.expand f).run = R.run := by
  induction R with
  | done a => rw [expand]
  | call I k ih =>
    rw [expand, run_bind, hf I, run_call]
    exact ih I.answer

/-- The calls of a substituted reduction: the calls of the sub-reductions, concatenated
along the executed path. -/
theorem calls_expand_length_le {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ I, (f I).run = I.answer) {c : ℕ} (hc : ∀ I, (f I).calls.length ≤ c)
    (R : SIReduction Ω A α) : (R.expand f).calls.length ≤ R.calls.length * c := by
  induction R with
  | done a => rw [expand]; simp
  | call I k ih =>
    rw [expand, calls_bind, List.length_append, hf I, calls_call, List.length_cons]
    have := ih I.answer
    calc (f I).calls.length + ((k I.answer).expand f).calls.length
        ≤ c + (k I.answer).calls.length * c := Nat.add_le_add (hc I) this
      _ = ((k I.answer).calls.length + 1) * c := by ring

/-- Every call of a substituted reduction is a call of one of the sub-reductions. -/
theorem mem_calls_expand {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ I, (f I).run = I.answer) {P : SIInstance Ω A → Prop}
    (hP : ∀ I J, J ∈ (f I).calls → P J) (R : SIReduction Ω A α) :
    ∀ J ∈ (R.expand f).calls, P J := by
  induction R with
  | done a => rw [expand]; simp
  | call I k ih =>
    rw [expand, calls_bind, hf I]
    intro J hJ
    rcases List.mem_append.1 hJ with h | h
    · exact hP I J h
    · exact ih I.answer J h

/-- Substitution by a *one-call* sub-reduction: when `f I` asks exactly one instance `g I`
and returns the answer to `I`, the calls of the substituted reduction are the calls of `R`,
each replaced by `g` of it.  This is the shape of an alignment step (Remark 11.1.4): the
call with respect to a coset is replaced by the call with respect to the group, and the
answer is translated back. -/
theorem calls_expand_eq_map {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (hf : ∀ I, (f I).run = I.answer) {g : SIInstance Ω A → SIInstance Ω A}
    (hg : ∀ I, (f I).calls = [g I]) (R : SIReduction Ω A α) :
    (R.expand f).calls = R.calls.map g := by
  induction R with
  | done a => rw [expand]; simp
  | call I k ih => rw [expand, calls_bind, hf I, hg I, calls_call, List.map_cons, ih]; rfl

/-- `run_expand` under a hypothesis needed only for the instances that are actually
called: `P` holds of every call of `R`, and `f` is correct on instances satisfying `P`. -/
theorem run_expand_of_calls {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    {P : SIInstance Ω A → Prop} (hf : ∀ I, P I → (f I).run = I.answer) :
    ∀ R : SIReduction Ω A α, (∀ I ∈ R.calls, P I) → (R.expand f).run = R.run := by
  intro R
  induction R with
  | done a => intro _; rw [expand]
  | call I k ih =>
    intro hR
    have hPI : P I := hR I (by simp [calls])
    rw [expand, run_bind, hf I hPI, run_call]
    exact ih I.answer (fun J hJ => hR J (by simp [calls, hJ]))

theorem calls_expand_length_le_of_calls
    {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    {P : SIInstance Ω A → Prop} (hf : ∀ I, P I → (f I).run = I.answer) {c : ℕ}
    (hc : ∀ I, P I → (f I).calls.length ≤ c) :
    ∀ R : SIReduction Ω A α, (∀ I ∈ R.calls, P I) →
      (R.expand f).calls.length ≤ R.calls.length * c := by
  intro R
  induction R with
  | done a => intro _; rw [expand]; simp [calls]
  | call I k ih =>
    intro hR
    have hPI : P I := hR I (by simp [calls])
    rw [expand, calls_bind, List.length_append, hf I hPI, calls_call, List.length_cons]
    have hrest := ih I.answer (fun J hJ => hR J (by simp [calls, hJ]))
    calc (f I).calls.length + ((k I.answer).expand f).calls.length
        ≤ c + (k I.answer).calls.length * c := Nat.add_le_add (hc I hPI) hrest
      _ = ((k I.answer).calls.length + 1) * c := by ring

theorem mem_calls_expand_of_calls
    {f : SIInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))}
    {P : SIInstance Ω A → Prop} (hf : ∀ I, P I → (f I).run = I.answer)
    {Q : SIInstance Ω A → Prop} (hQ : ∀ I, P I → ∀ J ∈ (f I).calls, Q J) :
    ∀ R : SIReduction Ω A α, (∀ I ∈ R.calls, P I) →
      ∀ J ∈ (R.expand f).calls, Q J := by
  intro R
  induction R with
  | done a => intro _; rw [expand]; simp [calls]
  | call I k ih =>
    intro hR
    have hPI : P I := hR I (by simp [calls])
    rw [expand, calls_bind, hf I hPI]
    intro J hJ
    rcases List.mem_append.1 hJ with h | h
    · exact hQ I hPI J h
    · exact ih I.answer (fun J' hJ' => hR J' (by simp [calls, hJ'])) J h

/-- A straight-line (non-adaptive) sequence of calls: ask the instances `Is` in turn and
apply `k` to the list of answers. -/
def seqCalls : List (SIInstance Ω A) → (List (Set (Equiv.Perm Ω)) → α) → SIReduction Ω A α
  | [], k => .done (k [])
  | I :: rest, k => .call I (fun a => seqCalls rest (fun as => k (a :: as)))

@[simp] theorem calls_seqCalls (Is : List (SIInstance Ω A))
    (k : List (Set (Equiv.Perm Ω)) → α) : (seqCalls Is k).calls = Is := by
  induction Is generalizing k with
  | nil => rfl
  | cons I rest ih => simpa [seqCalls, calls] using ih _

@[simp] theorem run_seqCalls (Is : List (SIInstance Ω A))
    (k : List (Set (Equiv.Perm Ω)) → α) :
    (seqCalls Is k).run = k (Is.map SIInstance.answer) := by
  induction Is generalizing k with
  | nil => rfl
  | cons I rest ih => simpa [seqCalls, run] using ih _

/-! ### Oracle-relative semantics

A reduction describes a program that makes recursive calls to String Isomorphism.  The
program itself never sees the true answers; it only builds each instance from the answers
it has been handed so far.  `runWith O` and `callsWith O` run the tree against an
arbitrary *oracle* `O`, and `run`/`calls` are the case where the oracle answers correctly.
This is the shape a RAM program with recursive calls realizes (`Workspace/Machine/`), and
it is what makes the call accounting a statement about the program rather than about the
value it happens to return. -/

/-- The value the reduction computes when the calls are answered by the oracle `O`. -/
def runWith (O : SIInstance Ω A → Set (Equiv.Perm Ω)) : SIReduction Ω A α → α
  | .done a => a
  | .call I k => (k (O I)).runWith O

/-- The list of instances the reduction produces when the calls are answered by the
oracle `O`. -/
def callsWith (O : SIInstance Ω A → Set (Equiv.Perm Ω)) :
    SIReduction Ω A α → List (SIInstance Ω A)
  | .done _ => []
  | .call I k => I :: (k (O I)).callsWith O

@[simp] theorem runWith_done (O : SIInstance Ω A → Set (Equiv.Perm Ω)) (a : α) :
    (SIReduction.done (Ω := Ω) (A := A) a).runWith O = a := rfl

@[simp] theorem callsWith_done (O : SIInstance Ω A → Set (Equiv.Perm Ω)) (a : α) :
    (SIReduction.done (Ω := Ω) (A := A) a).callsWith O = [] := rfl

@[simp] theorem runWith_call (O : SIInstance Ω A → Set (Equiv.Perm Ω)) (I : SIInstance Ω A)
    (k : Set (Equiv.Perm Ω) → SIReduction Ω A α) :
    (SIReduction.call I k).runWith O = (k (O I)).runWith O := rfl

@[simp] theorem callsWith_call (O : SIInstance Ω A → Set (Equiv.Perm Ω))
    (I : SIInstance Ω A) (k : Set (Equiv.Perm Ω) → SIReduction Ω A α) :
    (SIReduction.call I k).callsWith O = I :: (k (O I)).callsWith O := rfl

/-- For the true oracle, `runWith` is `run`. -/
@[simp] theorem runWith_answer (R : SIReduction Ω A α) :
    R.runWith SIInstance.answer = R.run := by
  induction R with
  | done a => rfl
  | call I k ih => rw [runWith_call, run_call]; exact ih I.answer

/-- For the true oracle, `callsWith` is `calls`. -/
@[simp] theorem callsWith_answer (R : SIReduction Ω A α) :
    R.callsWith SIInstance.answer = R.calls := by
  induction R with
  | done a => rfl
  | call I k ih => rw [callsWith_call, calls_call]; exact congrArg _ (ih I.answer)

end SIReduction

/-- `R` *reduces* the instance `I`, with value in `α` described by `spec`: the reduction
computes `spec I.answer`… stated in the two forms the paper uses, namely "find
`Iso_G(x,y)`" (`α = Set (S(Ω))`) and "decide … and if so find" (`α = Option (Set (S(Ω)))`).
Here we only record the shape: `R.run` is the answer. -/
def SIReduction.Computes {Ω : Type u} {A : Type v} {α : Type w}
    (R : SIReduction Ω A α) (a : α) : Prop := R.run = a

end Babai
