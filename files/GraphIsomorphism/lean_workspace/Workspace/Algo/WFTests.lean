/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: machine tests for the well-formedness predicates on raw data.
-/
import Workspace.Algo.Perm
import Workspace.Machine.ListOps5
import Workspace.Machine.Mul

/-!
# Well-formedness tests on the RAM

`Algo.Round.RunCost.wfCheck` (`Workspace/Algo/EvaluatorRAM.lean`) and
`Algo.Round.RunCostQ.wfCheck` (`Workspace/Algo/RoundQ.lean`) ask for a **routine** that tests
the well-formedness predicate of a round.  Until now no package had one: every `WF` predicate
of the tree was decidable, but no `RAM.PolyFun` said that its test runs in polynomial time.
This file builds the missing tests, from the bottom up.

Every routine here is **total** and every `RAM.PolyFun` statement holds on *all* inputs, junk
included.  No loop is keyed on `List.range m` for a machine natural `m`: the only loops are
over lists that are part of the input, either directly (`RAM.PolyFun.filterParam`) or through
`RAM.dedupG`.

## Main definitions

* `Algo.wftAll` — "every entry of the list passes the test", with a fixed first argument;
* `Algo.wftNodup` — the test for `List.Nodup` on `List ℕ`;
* `Algo.wftAllLt` — the test "every entry is below the bound";
* `Algo.wftIsPermOf`, `Algo.wftIsGensOf`, `Algo.wftIsStrOf` — the tests for
  `Algo.RawPerm.WF`, `Algo.RawGens.WF` and `Algo.RawStr.WF`, with the degree given as an
  argument rather than read off the length.

## Main results

Each test comes with `… = true ↔ <the predicate>` and a `RAM.PolyFun` statement.

## Why the degree is an argument

`Algo.rawIsPerm` (`Workspace/Algo/Perm.lean`) already tests `Algo.RawPerm.WF l.length l`: the
degree is the length of the list being tested.  That is not enough for a round, whose nodes
carry several lists that must all have the *same* degree, read off one domain witness.  So
every test below takes the degree `n` as its first component, and the caller supplies it, for
instance as `I.2.1.length` for a raw instance of String Isomorphism.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM

/-! ## Boolean glue

Two combinators that were missing: the conjunction of two routines, and "every entry of a
list passes a test whose first argument is held fixed". -/

/-- **The conjunction of two routines is a routine.** -/
theorem wftPolyFun_and {γ : Type*} [Enc γ] {f g : γ → Bool} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun x => f x && g x) :=
  (PolyFun.ite hf hg (polyFun_const false)).of_eq (fun x => by
    cases h : f x <;> simp [h])

/-- **The negation of a routine is a routine.** -/
theorem wftPolyFun_not {γ : Type*} [Enc γ] {f : γ → Bool} (hf : PolyFun f) :
    PolyFun (fun x => !f x) :=
  (PolyFun.ite hf (polyFun_const false) (polyFun_const true)).of_eq (fun x => by
    cases h : f x <;> simp [h])

/-- **Every entry of the list passes the test**, with the first argument of the test held
fixed.  This is `List.all` with a parameter. -/
def wftAll {γ α : Type*} (q : γ × α → Bool) (p : γ × List α) : Bool :=
  p.2.all (fun a => q (p.1, a))

@[simp] theorem wftAll_eq_true_iff {γ α : Type*} (q : γ × α → Bool) (p : γ × List α) :
    wftAll q p = true ↔ ∀ a ∈ p.2, q (p.1, a) = true := by
  simp [wftAll]

/-- The filter form of `Algo.wftAll`, which is the shape the machine combinators take. -/
private theorem wftAll_eq_isEmpty {γ α : Type*} (q : γ × α → Bool) (c : γ) :
    ∀ l : List α, (l.filter (fun a => !q (c, a))).isEmpty = l.all (fun a => q (c, a))
  | [] => rfl
  | a :: t => by
      by_cases h : q (c, a) = true
      · simp [List.filter_cons, h, wftAll_eq_isEmpty q c t]
      · simp only [Bool.not_eq_true] at h
        simp [List.filter_cons, h]

/-- **`Algo.wftAll` is a routine** whenever the test is.  The loop is over the list that is
part of the input. -/
theorem wftPolyFun_all {γ α : Type*} [Enc α] [Enc γ] {q : γ × α → Bool} (hq : PolyFun q) :
    PolyFun (wftAll q) := by
  refine ((PolyFun.filterParam (wftPolyFun_not hq)).comp polyFun_isEmpty).of_eq (fun p => ?_)
  exact wftAll_eq_isEmpty q p.1 p.2

/-! ## Repetition-free lists

The test deduplicates the list and compares lengths.  `RAM.dedupG`
(`Workspace/Machine/ListOps5.lean`) is a fold over the list itself, so it is a routine, and
its answer has no repetition and the same entries as the list.  A list with no repetition is
therefore as long as its deduplication, and a list with a repetition is strictly longer. -/

/-- **The test for `List.Nodup` on `List ℕ`.** -/
def wftNodup (l : List ℕ) : Bool := decide ((dedupG (([] : List ℕ), l)).length = l.length)

/-- **The specification of `Algo.wftNodup`.** -/
theorem wftNodup_eq_true_iff (l : List ℕ) : wftNodup l = true ↔ l.Nodup := by
  classical
  have hnd : (dedupG (([] : List ℕ), l)).Nodup := nodup_dedupG l
  have hmem : ∀ k : ℕ, k ∈ dedupG (([] : List ℕ), l) ↔ k ∈ l := mem_dedupG_nil l
  have hfin : (dedupG (([] : List ℕ), l)).toFinset = l.toFinset := by
    ext k; simp [hmem k]
  have hcard : (dedupG (([] : List ℕ), l)).length = l.toFinset.card := by
    rw [← hfin, List.toFinset_card_of_nodup hnd]
  rw [wftNodup, decide_eq_true_iff, hcard]
  constructor
  · intro h
    have hlen : l.dedup.length = l.length := by rw [← List.card_toFinset]; exact h
    exact List.dedup_eq_self.1 (List.Sublist.eq_of_length (List.dedup_sublist l) hlen)
  · intro h
    exact List.toFinset_card_of_nodup h

/-- **`Algo.wftNodup` is a routine.** -/
theorem wftPolyFun_nodup : PolyFun wftNodup := by
  have h1 : PolyFun (fun l : List ℕ => (dedupG (([] : List ℕ), l)).length) :=
    (((polyFun_const ([] : List ℕ)).pair polyFun_id).comp
      (polyFun_dedupG polyFun_natEq)).comp polyFun_length
  exact h1.natEq polyFun_length

/-! ## Entries below a bound -/

/-- The test "this number is below the bound". -/
def wftLt (z : ℕ × ℕ) : Bool := decide (z.2 < z.1)

theorem wftPolyFun_lt : PolyFun wftLt :=
  ((polyFun_snd.add (polyFun_const 1)).le polyFun_fst).of_eq (fun z => rfl)

/-- **The test "every entry of the list is below the bound".**  The bound is the first
component. -/
def wftAllLt (p : ℕ × List ℕ) : Bool := wftAll wftLt p

/-- **The specification of `Algo.wftAllLt`.** -/
theorem wftAllLt_eq_true_iff (n : ℕ) (l : List ℕ) :
    wftAllLt (n, l) = true ↔ ∀ a ∈ l, a < n := by
  simp [wftAllLt, wftLt]

theorem wftPolyFun_allLt : PolyFun wftAllLt := wftPolyFun_all wftPolyFun_lt

/-! ## Raw permutations

`Algo.RawPerm.WF n l` is "`l` has `n` entries, all below `n`, with no repetition".  The three
clauses are tested separately, so that the degree `n` may come from elsewhere in the node. -/

/-- **The test for `Algo.RawPerm.WF`**, with the degree given as the first component. -/
def wftIsPermOf (p : ℕ × RawPerm) : Bool :=
  decide (p.2.length = p.1) && wftAllLt p && wftNodup p.2

/-- **The specification of `Algo.wftIsPermOf`.** -/
theorem wftIsPermOf_eq_true_iff (n : ℕ) (l : RawPerm) :
    wftIsPermOf (n, l) = true ↔ RawPerm.WF n l := by
  rw [wftIsPermOf, RawPerm.WF]
  simp only [Bool.and_eq_true, decide_eq_true_iff, wftAllLt_eq_true_iff,
    wftNodup_eq_true_iff, and_assoc]

theorem wftPolyFun_isPermOf : PolyFun wftIsPermOf :=
  wftPolyFun_and (wftPolyFun_and ((polyFun_snd.comp polyFun_length).natEq polyFun_fst)
    wftPolyFun_allLt) (polyFun_snd.comp wftPolyFun_nodup)

/-! ## Lists of raw generators -/

/-- **The test for `Algo.RawGens.WF`**, with the degree given as the first component. -/
def wftIsGensOf (p : ℕ × RawGens) : Bool := wftAll wftIsPermOf p

/-- **The specification of `Algo.wftIsGensOf`.** -/
theorem wftIsGensOf_eq_true_iff (n : ℕ) (gs : RawGens) :
    wftIsGensOf (n, gs) = true ↔ RawGens.WF n gs := by
  rw [wftIsGensOf, RawGens.WF, wftAll_eq_true_iff]
  exact forall₂_congr (fun g _ => wftIsPermOf_eq_true_iff n g)

theorem wftPolyFun_isGensOf : PolyFun wftIsGensOf := wftPolyFun_all wftPolyFun_isPermOf

/-! ## Raw strings

`Algo.RawStr.WF n s x` is "`x` has `n` letters, all below `s`".  Both `n` and `s` are given
as arguments: for the normalized input of Sec. 15 the alphabet bound is `2n`, and for a
letter that arrives from elsewhere it is whatever the caller knows. -/

/-- **The test for `Algo.RawStr.WF`**, with the domain size and the alphabet size given as
the two halves of the first component. -/
def wftIsStrOf (p : (ℕ × ℕ) × RawStr) : Bool :=
  decide (p.2.length = p.1.1) && wftAllLt (p.1.2, p.2)

/-- **The specification of `Algo.wftIsStrOf`.** -/
theorem wftIsStrOf_eq_true_iff (n s : ℕ) (x : RawStr) :
    wftIsStrOf ((n, s), x) = true ↔ RawStr.WF n s x := by
  rw [wftIsStrOf, RawStr.WF]
  simp only [Bool.and_eq_true, decide_eq_true_iff, wftAllLt_eq_true_iff]

theorem wftPolyFun_isStrOf : PolyFun wftIsStrOf :=
  wftPolyFun_and ((polyFun_snd.comp polyFun_length).natEq (polyFun_fst.comp polyFun_fst))
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp wftPolyFun_allLt)

end Algo
