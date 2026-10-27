/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the master round of Sec. 15 as a family of node kinds.
-/
import Workspace.Algo.A15Compose
import Workspace.Algo.RoundQ

/-!
# The master round as a family of node kinds

`Workspace/Algo/Round.lean` gives one computable round, and the evaluator runs **one** round
and nothing else.  The rounds of Secs. 11–15 are many.  The note "A15 session 0" at the end of
`Workspace/Algo/DESIGN.md` proposed to write the master round as a tag with a product of
options and a hand-written ten-way dispatch.  That would make every package edit the same
`match`.  This file replaces the hand-written dispatch by a *family*.

## What a kind is

Fix the master node type `N`, the master fold state `S`, the answer type `α`, and the three
global predicates the round needs: `WF`, `ground`, `measure`.  A **kind** (`Algo.A15.Kind`)
is one case of the dispatch:

* its own instance type `ι` and fold state `ω`, each with an `RAM.Enc`;
* an injection `e : ι → N` of its instances into master nodes and a projection
  `proj : N → Option ι` with `proj (e i) = some i`, and the same pair `u`, `projω` for the
  states;
* the four routines `width`, `child`, `init`, `combine`, `finish`, where
  `child : ι × ℕ × ω → Option N` returns a **master** node, so a kind may call any kind,
  itself included;
* the four laws `Algo.Round` asks, in the form they take when the children are master nodes.

The nodes of the kind that the master round ever meets are exactly the `e i`: that is the
field `eq_e_of_proj`, which says a *well-formed* node whose projection is `some i` is `e i`.
Nothing is asked of junk nodes.

## What the family is

`Algo.A15.famRound bot botS ks` takes a **list** of kinds and produces one
`Algo.Round N S α`.  Every routine dispatches by *first match*: the first kind of the list
whose `proj` is `some` at the node runs, and if no kind claims the node the routine answers
with a harmless default (`none` for `child`, `botS` for `init`, the unchanged state for
`combine`, `bot` for `finish`, `0` for `width`).  The four laws are proved once, by induction
on the list, from the per-kind laws.

**Why a list and not a binary sum.**  A binary step "add one kind to a master round" would
change the node type at each step, so a kind added early could not call a kind added late:
its `child` returns a node of the *old* type.  The master round of Sec. 15 has calls in both
directions — the Chain Rule calls the Sec. 15 dispatch, which calls the Chain Rule — so the
node type has to be fixed before any kind is written.  With a list, `N` and `S` are
parameters and every kind's `child` lands in the same `N`.  This also keeps the `RAM.Enc`
instances out of the combinator: there is one `Enc N`, one `Enc S`, one `Enc α`, whatever the
kinds are, instead of a tower of nested sums.

## The master measure

Item 7 of the session-0 note: `measure x = rank x * K (ground x) + local x`.  The combinator
does **not** fix this; it takes `measure` as a parameter and each kind proves that its
children drop it.  `Algo.A15.measureOfRank` is the recipe, and
`Algo.A15.measureOfRank_lt` is the arithmetic that discharges `child_measure` from
"the rank drops, or the rank stays and the local measure drops".

## Main definitions

* `Algo.A15.Kind` — one case of the master dispatch;
* `Algo.A15.famWidth`, `famChild`, `famInit`, `famCombine`, `famFinish` — the dispatch;
* `Algo.A15.famRound` — the master round;
* `Algo.A15.measureOfRank` — the measure recipe of item 7.

## Main results

* `Algo.A15.famRound` itself: the four laws of `Algo.Round`, proved once;
* `Algo.A15.famWidth_eq` … `Algo.A15.famFinish_eq` — the five equations a package needs in
  order to apply `Algo.implements_embed` to its own kind;
* `Algo.A15.measureOfRank_lt`, `Algo.A15.le_measureOfRank`.

No axiom, no `sorry`.
-/

namespace Algo.A15

open RAM Babai

/-! ## One kind -/

/-- **One case of the master dispatch.**

`WF`, `ground` and `measure` are the master round's, not the kind's: a child of a kind is a
master node of any kind, so its well-formedness, its domain size and its measure have to be
read at the master level.  The kind's own reading of them is the restriction along `e`, which
is `Algo.A15.Kind.WFι` and `Algo.A15.Kind.groundι` below. -/
structure Kind (N S α : Type) (WF : N → Prop) (ground measure : N → ℕ) where
  /-- The kind's own raw instance type. -/
  ι : Type
  /-- The kind's own raw fold state. -/
  ω : Type
  /-- The encoding of the kind's instances. -/
  encι : Enc ι
  /-- The encoding of the kind's fold states. -/
  encω : Enc ω
  /-- The kind's instances as master nodes. -/
  e : ι → N
  /-- Reading a master node as an instance of this kind. -/
  proj : N → Option ι
  /-- The kind's fold states as master states. -/
  u : ω → S
  /-- Reading a master state as a state of this kind. -/
  projω : S → Option ω
  /-- `proj` is a left inverse of `e`. -/
  proj_e : ∀ i, proj (e i) = some i
  /-- `projω` is a left inverse of `u`. -/
  projω_u : ∀ w, projω (u w) = some w
  /-- A **well-formed** master node of this kind is one of the kind's own instances.  Nothing
  is asked of junk nodes. -/
  eq_e_of_proj : ∀ x i, WF x → proj x = some i → x = e i
  /-- A bound on the number of children. -/
  width : ι → ℕ
  /-- The `j`-th child, a master node: a kind may call any kind. -/
  child : ι × ℕ × ω → Option N
  /-- The empty partial answer. -/
  init : ι → ω
  /-- Fold one child's answer into the state. -/
  combine : ι × ℕ × ω × α → ω
  /-- Read the answer off the final state. -/
  finish : ι × ω → α
  /-- An instance has at most `width i` children.  This holds for **every** state, junk
  included, because the master round's `child_eq_none` does. -/
  child_eq_none : ∀ i j w, width i ≤ j → child (i, j, w) = none
  /-- A child of a well-formed instance is a well-formed master node. -/
  child_wf : ∀ i j w y, WF (e i) → child (i, j, w) = some y → WF y
  /-- The master measure drops at a child. -/
  child_measure : ∀ i j w y, WF (e i) → child (i, j, w) = some y → measure y < measure (e i)
  /-- The domain of a child does not grow. -/
  child_ground : ∀ i j w y, WF (e i) → child (i, j, w) = some y → ground y ≤ ground (e i)

variable {N S α : Type} {WF : N → Prop} {ground measure : N → ℕ}

/-- The encoding of a kind's instances, as an instance. -/
instance instEncKindι (k : Kind N S α WF ground measure) : Enc k.ι := k.encι

/-- The encoding of a kind's fold states, as an instance. -/
instance instEncKindω (k : Kind N S α WF ground measure) : Enc k.ω := k.encω

namespace Kind

variable (k : Kind N S α WF ground measure)

/-- The kind's own reading of the master well-formedness. -/
def WFι (i : k.ι) : Prop := WF (k.e i)

/-- The kind's own reading of the master domain size. -/
def groundι (i : k.ι) : ℕ := ground (k.e i)

/-- The kind's own reading of the master measure. -/
def measureι (i : k.ι) : ℕ := measure (k.e i)

theorem e_injective : Function.Injective k.e := by
  intro a b h
  have h1 : k.proj (k.e a) = k.proj (k.e b) := congrArg k.proj h
  rw [k.proj_e a, k.proj_e b] at h1
  exact Option.some.inj h1

theorem u_injective : Function.Injective k.u := by
  intro a b h
  have h1 : k.projω (k.u a) = k.projω (k.u b) := congrArg k.projω h
  rw [k.projω_u a, k.projω_u b] at h1
  exact Option.some.inj h1

end Kind

/-! ## The dispatch

Each routine walks the list and stops at the first kind that claims the node.  A node no kind
claims gets a harmless default, which is what a `RAM.PolyFun`/`RAM.QuasiFun` needs: the
routines are total and cheap on junk. -/

/-- The width of a master node: the width its kind gives it, and `0` if no kind claims it. -/
def famWidth : List (Kind N S α WF ground measure) → N → ℕ
  | [], _ => 0
  | k :: r, x =>
      match k.proj x with
      | none => famWidth r x
      | some i => k.width i

/-- The `j`-th child of a master node. -/
def famChild : List (Kind N S α WF ground measure) → N × ℕ × S → Option N
  | [], _ => none
  | k :: r, p =>
      match k.proj p.1 with
      | none => famChild r p
      | some i =>
          match k.projω p.2.2 with
          | none => none
          | some w => k.child (i, p.2.1, w)

/-- The empty partial answer of a master node. -/
def famInit (botS : S) : List (Kind N S α WF ground measure) → N → S
  | [], _ => botS
  | k :: r, x =>
      match k.proj x with
      | none => famInit botS r x
      | some i => k.u (k.init i)

/-- Folding one child's answer into a master state. -/
def famCombine : List (Kind N S α WF ground measure) → N × ℕ × S × α → S
  | [], p => p.2.2.1
  | k :: r, p =>
      match k.proj p.1 with
      | none => famCombine r p
      | some i =>
          match k.projω p.2.2.1 with
          | none => p.2.2.1
          | some w => k.u (k.combine (i, p.2.1, w, p.2.2.2))

/-- Reading the answer of a master node off its final state. -/
def famFinish (bot : α) : List (Kind N S α WF ground measure) → N × S → α
  | [], _ => bot
  | k :: r, p =>
      match k.proj p.1 with
      | none => famFinish bot r p
      | some i =>
          match k.projω p.2 with
          | none => bot
          | some w => k.finish (i, w)

/-! ### The dispatch step by step

The `Option.elim` form of each equation above.  These are the shapes
`RAM.QuasiFun.optionElim` takes, and they are what `Workspace/Algo/A15KindsCost.lean` runs
the induction on. -/

theorem famWidth_cons (k : Kind N S α WF ground measure)
    (r : List (Kind N S α WF ground measure)) (x : N) :
    famWidth (k :: r) x = (k.proj x).elim (famWidth r x) (fun i => k.width i) := by
  cases h : k.proj x <;> simp [famWidth, h]

theorem famChild_cons (k : Kind N S α WF ground measure)
    (r : List (Kind N S α WF ground measure)) (x : N) (j : ℕ) (s : S) :
    famChild (k :: r) (x, j, s)
      = (k.proj x).elim (famChild r (x, j, s))
          (fun i => (k.projω s).elim none (fun w => k.child (i, j, w))) := by
  cases h : k.proj x <;> cases h2 : k.projω s <;> simp [famChild, h, h2]

theorem famInit_cons (botS : S) (k : Kind N S α WF ground measure)
    (r : List (Kind N S α WF ground measure)) (x : N) :
    famInit botS (k :: r) x
      = (k.proj x).elim (famInit botS r x) (fun i => k.u (k.init i)) := by
  cases h : k.proj x <;> simp [famInit, h]

theorem famCombine_cons (k : Kind N S α WF ground measure)
    (r : List (Kind N S α WF ground measure)) (x : N) (j : ℕ) (s : S) (a : α) :
    famCombine (k :: r) (x, j, s, a)
      = (k.proj x).elim (famCombine r (x, j, s, a))
          (fun i => (k.projω s).elim s (fun w => k.u (k.combine (i, j, w, a)))) := by
  cases h : k.proj x <;> cases h2 : k.projω s <;> simp [famCombine, h, h2]

theorem famFinish_cons (bot : α) (k : Kind N S α WF ground measure)
    (r : List (Kind N S α WF ground measure)) (x : N) (s : S) :
    famFinish bot (k :: r) (x, s)
      = (k.proj x).elim (famFinish bot r (x, s))
          (fun i => (k.projω s).elim bot (fun w => k.finish (i, w))) := by
  cases h : k.proj x <;> cases h2 : k.projω s <;> simp [famFinish, h, h2]

/-! ## The laws of the master round

Each is an induction on the list.  At a kind that claims the node the per-kind law applies,
after `eq_e_of_proj` has identified the node with `e i`; at a kind that does not, the
induction hypothesis applies; at the end of the list the default answers. -/

theorem famChild_eq_none (ks : List (Kind N S α WF ground measure)) (x : N) (j : ℕ) (s : S)
    (hj : famWidth ks x ≤ j) : famChild ks (x, j, s) = none := by
  induction ks with
  | nil => rfl
  | cons k r ih =>
      rw [famWidth_cons] at hj
      rw [famChild_cons]
      cases h : k.proj x with
      | none => rw [h] at hj; exact ih hj
      | some i =>
          rw [h] at hj
          cases h2 : k.projω s with
          | none => rfl
          | some w => exact k.child_eq_none i j w hj

theorem famChild_wf (ks : List (Kind N S α WF ground measure)) {x : N} {j : ℕ} {s : S} {y : N}
    (hx : WF x) (h : famChild ks (x, j, s) = some y) : WF y := by
  induction ks with
  | nil => exact absurd h (by simp [famChild])
  | cons k r ih =>
      rw [famChild_cons] at h
      cases hp : k.proj x with
      | none => rw [hp] at h; exact ih h
      | some i =>
          rw [hp] at h
          cases h2 : k.projω s with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some w =>
              rw [h2] at h
              have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
              exact k.child_wf i j w y (hxe ▸ hx) h

theorem famChild_measure (ks : List (Kind N S α WF ground measure)) {x : N} {j : ℕ} {s : S}
    {y : N} (hx : WF x) (h : famChild ks (x, j, s) = some y) : measure y < measure x := by
  induction ks with
  | nil => exact absurd h (by simp [famChild])
  | cons k r ih =>
      rw [famChild_cons] at h
      cases hp : k.proj x with
      | none => rw [hp] at h; exact ih h
      | some i =>
          rw [hp] at h
          cases h2 : k.projω s with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some w =>
              rw [h2] at h
              have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
              have := k.child_measure i j w y (hxe ▸ hx) h
              rw [hxe]; exact this

theorem famChild_ground (ks : List (Kind N S α WF ground measure)) {x : N} {j : ℕ} {s : S}
    {y : N} (hx : WF x) (h : famChild ks (x, j, s) = some y) : ground y ≤ ground x := by
  induction ks with
  | nil => exact absurd h (by simp [famChild])
  | cons k r ih =>
      rw [famChild_cons] at h
      cases hp : k.proj x with
      | none => rw [hp] at h; exact ih h
      | some i =>
          rw [hp] at h
          cases h2 : k.projω s with
          | none => rw [h2] at h; exact absurd h (by simp)
          | some w =>
              rw [h2] at h
              have hxe : x = k.e i := k.eq_e_of_proj x i hx hp
              have := k.child_ground i j w y (hxe ▸ hx) h
              rw [hxe]; exact this

/-- **The master round of a family of kinds.**  Every routine dispatches by first match, and
the four laws of `Algo.Round` are the four lemmas above. -/
def famRound (bot : α) (botS : S) (ks : List (Kind N S α WF ground measure)) :
    Round N S α where
  WF := WF
  ground := ground
  measure := measure
  width := famWidth ks
  child := famChild ks
  init := famInit botS ks
  combine := famCombine ks
  finish := famFinish bot ks
  bot := bot
  child_eq_none := fun I j s hj => famChild_eq_none ks I j s hj
  child_wf := fun _ _ _ _ hI h => famChild_wf ks hI h
  child_measure := fun _ _ _ _ hI h => famChild_measure ks hI h
  child_ground := fun _ _ _ _ hI h => famChild_ground ks hI h

@[simp] theorem famRound_WF (bot : α) (botS : S) (ks : List (Kind N S α WF ground measure)) :
    (famRound bot botS ks).WF = WF := rfl

@[simp] theorem famRound_ground (bot : α) (botS : S)
    (ks : List (Kind N S α WF ground measure)) : (famRound bot botS ks).ground = ground := rfl

@[simp] theorem famRound_measure (bot : α) (botS : S)
    (ks : List (Kind N S α WF ground measure)) :
    (famRound bot botS ks).measure = measure := rfl

/-! ## The five equations a package needs

`Algo.implements_embed` (`Workspace/Algo/A15Compose.lean`) transfers a package's `LoopMatch`
to the master round once the master round is known to *be* the package's round on the image
of `e`.  For a family those five equations are not a new proof obligation: they hold as soon
as the kind is the **first** kind of the list that claims the node.  `Algo.A15.Misses` is that
condition, and the five lemmas below are the equations.

This is the whole point of the interface.  A package adds a kind by appending it to the list
and proving `Misses` for the kinds in front of it, which is a statement about projections
only — usually one `rfl` per kind in front. -/

/-- No kind of the list claims the node. -/
def Misses (ks : List (Kind N S α WF ground measure)) (x : N) : Prop :=
  ∀ k ∈ ks, k.proj x = none

theorem misses_nil (x : N) : Misses ([] : List (Kind N S α WF ground measure)) x :=
  fun _ h => absurd h (by simp)

theorem famWidth_eq (pre : List (Kind N S α WF ground measure))
    (k : Kind N S α WF ground measure) (post : List (Kind N S α WF ground measure))
    (i : k.ι) (hmiss : Misses pre (k.e i)) :
    famWidth (pre ++ k :: post) (k.e i) = k.width i := by
  induction pre with
  | nil => rw [List.nil_append, famWidth_cons, k.proj_e i]; rfl
  | cons k' r ih =>
      rw [List.cons_append, famWidth_cons, hmiss k' (by simp)]
      exact ih (fun k'' h => hmiss k'' (by simp [h]))

theorem famInit_eq (botS : S) (pre : List (Kind N S α WF ground measure))
    (k : Kind N S α WF ground measure) (post : List (Kind N S α WF ground measure))
    (i : k.ι) (hmiss : Misses pre (k.e i)) :
    famInit botS (pre ++ k :: post) (k.e i) = k.u (k.init i) := by
  induction pre with
  | nil => rw [List.nil_append, famInit_cons, k.proj_e i]; rfl
  | cons k' r ih =>
      rw [List.cons_append, famInit_cons, hmiss k' (by simp)]
      exact ih (fun k'' h => hmiss k'' (by simp [h]))

theorem famChild_eq (pre : List (Kind N S α WF ground measure))
    (k : Kind N S α WF ground measure) (post : List (Kind N S α WF ground measure))
    (i : k.ι) (j : ℕ) (w : k.ω) (hmiss : Misses pre (k.e i)) :
    famChild (pre ++ k :: post) (k.e i, j, k.u w) = k.child (i, j, w) := by
  induction pre with
  | nil => rw [List.nil_append, famChild_cons]; simp only [k.proj_e i, k.projω_u w]; rfl
  | cons k' r ih =>
      rw [List.cons_append, famChild_cons]
      simp only [hmiss k' (by simp)]
      exact ih (fun k'' h => hmiss k'' (by simp [h]))

theorem famCombine_eq (pre : List (Kind N S α WF ground measure))
    (k : Kind N S α WF ground measure) (post : List (Kind N S α WF ground measure))
    (i : k.ι) (j : ℕ) (w : k.ω) (a : α) (hmiss : Misses pre (k.e i)) :
    famCombine (pre ++ k :: post) (k.e i, j, k.u w, a) = k.u (k.combine (i, j, w, a)) := by
  induction pre with
  | nil => rw [List.nil_append, famCombine_cons]; simp only [k.proj_e i, k.projω_u w]; rfl
  | cons k' r ih =>
      rw [List.cons_append, famCombine_cons]
      simp only [hmiss k' (by simp)]
      exact ih (fun k'' h => hmiss k'' (by simp [h]))

theorem famFinish_eq (bot : α) (pre : List (Kind N S α WF ground measure))
    (k : Kind N S α WF ground measure) (post : List (Kind N S α WF ground measure))
    (i : k.ι) (w : k.ω) (hmiss : Misses pre (k.e i)) :
    famFinish bot (pre ++ k :: post) (k.e i, k.u w) = k.finish (i, w) := by
  induction pre with
  | nil => rw [List.nil_append, famFinish_cons]; simp only [k.proj_e i, k.projω_u w]; rfl
  | cons k' r ih =>
      rw [List.cons_append, famFinish_cons]
      simp only [hmiss k' (by simp)]
      exact ih (fun k'' h => hmiss k'' (by simp [h]))

/-! ## The measure recipe of item 7

`measure x = rank x * K (ground x) + local x`, with `K` monotone and `local x < K (ground x)`
at every node.  A child either drops `rank` — and `ground` does not grow, so `K` does not
grow, and `rank' K + local' ≤ rank' K + K - 1 < rank K` — or keeps `rank` and drops `local`. -/

/-- The master measure of item 7 of the session-0 note. -/
def measureOfRank (rank : N → ℕ) (K : ℕ → ℕ) (loc : N → ℕ) (gr : N → ℕ) (x : N) : ℕ :=
  rank x * K (gr x) + loc x

/-- **The measure of item 7 drops at a child.** -/
theorem measureOfRank_lt {rank : N → ℕ} {K : ℕ → ℕ} {loc gr : N → ℕ} (hK : Monotone K)
    {x y : N} (hg : gr y ≤ gr x) (hloc : loc y < K (gr y))
    (h : rank y < rank x ∨ (rank y = rank x ∧ loc y < loc x)) :
    measureOfRank rank K loc gr y < measureOfRank rank K loc gr x := by
  have hKle : K (gr y) ≤ K (gr x) := hK hg
  have hmul : rank y * K (gr y) ≤ rank y * K (gr x) := Nat.mul_le_mul_left _ hKle
  rcases h with hlt | ⟨heq, hll⟩
  · have hstep : rank y + 1 ≤ rank x := hlt
    have h1 : (rank y + 1) * K (gr x) ≤ rank x * K (gr x) :=
      Nat.mul_le_mul_right _ hstep
    have h2 : (rank y + 1) * K (gr x) = rank y * K (gr x) + K (gr x) := by ring
    have h3 : loc y < K (gr x) := lt_of_lt_of_le hloc hKle
    simp only [measureOfRank]
    omega
  · simp only [measureOfRank, heq]
    have : rank x * K (gr y) ≤ rank x * K (gr x) := Nat.mul_le_mul_left _ hKle
    omega

/-- **The rank is below the measure of item 7**, which is what
`Algo.Round.runQ_eq_answer` asks of `hrank`. -/
theorem le_measureOfRank {rank : N → ℕ} {K : ℕ → ℕ} {loc gr : N → ℕ} (x : N)
    (hK : 1 ≤ K (gr x)) : rank x ≤ measureOfRank rank K loc gr x := by
  have : rank x * 1 ≤ rank x * K (gr x) := Nat.mul_le_mul_left _ hK
  simp only [measureOfRank]
  omega

end Algo.A15
