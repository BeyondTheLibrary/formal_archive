/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: machine tests for the well-formedness predicates of the rounds.
-/
import Workspace.Algo.WFTests
import Workspace.Algo.NormalizeSI

/-!
# The tests for `Algo.NormSIWF`, `Algo.WinWF`, and the root of the master round

`Workspace/Algo/WFTests.lean` tests the three predicates on raw lists.  This file puts them
together into the two predicates the rounds use, and gives the root test of Sec. 15.

## Main definitions

* `Algo.wftNormSI` — the test for `Algo.NormSIWF` (`Workspace/Algo/NormalizeSI.lean`);
* `Algo.wftWinWF` — the test for `Algo.WinWF` (`Workspace/Algo/Luks.lean`);
* `Algo.wftRootCheck` — the root test of the master round, on `Algo.RawSI`.

## Main results

* `Algo.wftNormSI_eq_true_iff`, `Algo.wftWinWF_eq_true_iff` — the two tests are tests;
* `Algo.wftPolyFun_normSI`, `Algo.wftPolyFun_winWF`, `Algo.wftPolyFun_rootCheck` — they are
  routines, on all inputs;
* `Algo.wftRootCheck_rawNormSI_rawOfSI` — **the normalized form of a typed input passes the
  root test**, which is what the final theorem feeds the master round.

## What is testable and what is not

`Algo.WinWF` and `Algo.NormSIWF` are entirely syntactic: every clause is a length, a bound on
the entries, the absence of repetition, or the already-Boolean invariance test
`Algo.rawIsInvariant`.  So the well-formedness of a *window* node is a genuine test.

The well-formedness predicates of the rounds built on top of a window are not, and the
section "The rounds" at the end of this file records, round by round, which clauses are tests
and which are facts about the data.  Nothing is faked: no test is claimed for a clause that
has none.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets

/-! ## The normalized input of String Isomorphism

`Algo.NormSIWF n I` has four clauses: the generators are permutations of the domain, there
are at most `n²` of them, and the two strings have `n` letters, each below `2n`.  All four
are tests. -/

/-- **The test for `Algo.NormSIWF`**, with the domain size given as the first component. -/
def wftNormSI (p : ℕ × RawSI) : Bool :=
  wftIsGensOf (p.1, p.2.1) && decide (p.2.1.length ≤ p.1 * p.1) &&
    wftIsStrOf ((p.1, 2 * p.1), p.2.2.1) && wftIsStrOf ((p.1, 2 * p.1), p.2.2.2)

/-- **The specification of `Algo.wftNormSI`.** -/
theorem wftNormSI_eq_true_iff (n : ℕ) (I : RawSI) :
    wftNormSI (n, I) = true ↔ NormSIWF n I := by
  rw [wftNormSI, NormSIWF]
  simp only [Bool.and_eq_true, decide_eq_true_iff, wftIsGensOf_eq_true_iff,
    wftIsStrOf_eq_true_iff, and_assoc]

theorem wftPolyFun_normSI : PolyFun wftNormSI := by
  have hn : PolyFun (fun p : ℕ × RawSI => p.1) := polyFun_fst
  have hg : PolyFun (fun p : ℕ × RawSI => p.2.1) := polyFun_snd.comp polyFun_fst
  have hx : PolyFun (fun p : ℕ × RawSI => p.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun p : ℕ × RawSI => p.2.2.2) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have halph : PolyFun (fun p : ℕ × RawSI => ((p.1, 2 * p.1) : ℕ × ℕ)) :=
    hn.pair ((polyFun_const 2).mul hn)
  exact wftPolyFun_and (wftPolyFun_and
    (wftPolyFun_and ((hn.pair hg).comp wftPolyFun_isGensOf)
      ((hg.comp polyFun_length).le (hn.mul hn)))
    ((halph.pair hx).comp wftPolyFun_isStrOf))
    ((halph.pair hy).comp wftPolyFun_isStrOf)

/-! ## The root test of the master round

The root node of Sec. 15 is a raw instance of String Isomorphism whose domain witness is the
length of its first string.  The test is `Algo.NormSIWF` at that degree, and nothing more:
the master round asks for no further syntax at the root, because the root's group, window and
representative are the whole domain, all of `G`, and the identity, which the round builds
itself.  The final theorem hands the round `Algo.rawNormSI (Algo.rawOfSI a)`, and
`Algo.rawNormSI_rawOfSI_wf` says exactly that this passes. -/

/-- **The root test.**  The degree is the length of the first string. -/
def wftRootCheck (I : RawSI) : Bool := wftNormSI (I.2.1.length, I)

/-- **The specification of `Algo.wftRootCheck`.** -/
theorem wftRootCheck_eq_true_iff (I : RawSI) :
    wftRootCheck I = true ↔ NormSIWF I.2.1.length I :=
  wftNormSI_eq_true_iff _ _

theorem wftPolyFun_rootCheck : PolyFun wftRootCheck := by
  have hx : PolyFun (fun I : RawSI => I.2.1.length) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_length
  exact (hx.pair polyFun_id).comp wftPolyFun_normSI

/-- **The normalized form of a typed input passes the root test.**  This is the clause the
final theorem needs: the master round is fed `Algo.rawNormSI (Algo.rawOfSI a)`, and the test
at its root says `true`. -/
theorem wftRootCheck_rawNormSI_rawOfSI {n s : ℕ} (a : SIInput n s) :
    wftRootCheck (rawNormSI (rawOfSI a)) = true := by
  have hlen : (rawNormSI (rawOfSI a)).2.1.length = n := by
    rw [rawNormSI_length_left]
    exact length_encStr _
  rw [wftRootCheck_eq_true_iff, hlen]
  exact rawNormSI_rawOfSI_wf a

/-! ## Window instances

`Algo.WinWF n I` has eight clauses.  Two are string lengths, two say that the window is a
repetition-free list of points of the domain, three are the generators and the
representative, and the last is the already-Boolean invariance test `Algo.rawIsInvariant`
of Def. 11.1.3.  All eight are tests, so the well-formedness of a window node of the Chain
Rule (Prop. 11.1.7) is decided in polynomial time on every input. -/

/-- **The test for `Algo.WinWF`**, with the domain size given as the first component. -/
def wftWinWF (p : ℕ × RawWinSI) : Bool :=
  decide (p.2.2.2.2.1.length = p.1) && decide (p.2.2.2.2.2.length = p.1) &&
    wftNodup p.2.1 && wftAllLt (p.1, p.2.1) &&
    wftIsGensOf (p.1, p.2.2.1) && decide (p.2.2.1.length ≤ p.1 * p.1) &&
    wftIsPermOf (p.1, p.2.2.2.1) && rawIsInvariant (p.2.2.1, p.2.1)

/-- **The specification of `Algo.wftWinWF`.** -/
theorem wftWinWF_eq_true_iff (n : ℕ) (I : RawWinSI) :
    wftWinWF (n, I) = true ↔ WinWF n I := by
  rw [wftWinWF, WinWF]
  simp only [Bool.and_eq_true, decide_eq_true_iff, wftNodup_eq_true_iff,
    wftAllLt_eq_true_iff, wftIsGensOf_eq_true_iff, wftIsPermOf_eq_true_iff, and_assoc]

theorem wftPolyFun_winWF : PolyFun wftWinWF := by
  have hn : PolyFun (fun p : ℕ × RawWinSI => p.1) := polyFun_fst
  have hd : PolyFun (fun p : ℕ × RawWinSI => p.2.1) := polyFun_snd.comp polyFun_fst
  have hg : PolyFun (fun p : ℕ × RawWinSI => p.2.2.1) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have hσ : PolyFun (fun p : ℕ × RawWinSI => p.2.2.2.1) :=
    ((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hx : PolyFun (fun p : ℕ × RawWinSI => p.2.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hy : PolyFun (fun p : ℕ × RawWinSI => p.2.2.2.2.2) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_snd
  exact wftPolyFun_and (wftPolyFun_and (wftPolyFun_and (wftPolyFun_and
    (wftPolyFun_and (wftPolyFun_and
      (wftPolyFun_and ((hx.comp polyFun_length).natEq hn)
        ((hy.comp polyFun_length).natEq hn))
      (hd.comp wftPolyFun_nodup))
      ((hn.pair hd).comp wftPolyFun_allLt))
    ((hn.pair hg).comp wftPolyFun_isGensOf))
    ((hg.comp polyFun_length).le (hn.mul hn)))
    ((hn.pair hσ).comp wftPolyFun_isPermOf))
    ((hg.pair hd).comp polyFun_rawIsInvariant)

/-! ## The rounds

What follows is a reading of the `WF` predicate of every round already built, split into the
part that is a test and the part that is a fact about the data.  Only the first part gets a
routine; the second is not faked.

**`Algo.chainRound` (`Workspace/Algo/Luks.lean`, Prop. 11.1.7).**  `WF = Algo.WinWF n`, which
is `Algo.wftWinWF` above.  Entirely a test.

**`Algo.descentRound` (`Workspace/Algo/Descent.lean`).**  `Algo.DescWF n I` is `Algo.WinWF`
on `I.1`, plus, when `I.2 = some (d, idx)`: `d.Nodup` and `∀ x ∈ d, x < n` — both tests,
`Algo.wftNodup` and `Algo.wftAllLt` — and `idx = Algo.winCosetIndex n x d (Algo.descGens n
I.1)`.  The last clause is **not** a test: `winCosetIndex` is the index `|G : G_(Δ_H)|` of a
pointwise stabilizer, which is as large as `n^|d|`, so no routine can compute it and compare
in polynomial time.  It is a fact about the data, placed there by the parent that built the
node.

**`Algo.impRound` (`Workspace/Algo/Imprimitive.lean`, Thm. 11.1.9).**  `Algo.ImpWF n I` is
`Algo.WinWF` on `I.1`, plus, when `I.2 = some (bl, idx)`: `Algo.BlocksWF n bl` — a test, it
says the blocks are a repetition-free partition of the domain into lists of points — and
`Algo.BlockData n bl (descGens n I.1)`, and `idx = Algo.blockCosetIndex …`.  `BlockData` says
that the assignment "generator ↦ its action on the blocks" extends to a homomorphism.  That
is a fact about the data, not a test: see the paragraph on `Algo.ImgsOf` below.
`blockCosetIndex` is again a subgroup index, so again not a test.

**`Algo.top1Round` (`Workspace/Algo/TopRound.lean`, Prop. 12.0.5).**  `Algo.Top1WF n I` is
`I.1.1.1.1.length = n` — a test — and "when the node stores a child `q`, there is an index
`j` below the width with `q = Algo.topLiftChild (Algo.top1Request (I.1, j))`".  The second
clause is a **bounded** existential, so it is decidable by a scan over the children of the
node; but the number of children is only bounded by the round's `widthBound`, which is
quasipolynomial, so the scan is a `RAM.QuasiFun`, not a `RAM.PolyFun`.  It is therefore not
admissible as a `wfCheck`, which must be polynomial.

**`Algo.top2Round`, `Algo.top3Round` (`Workspace/Algo/TopWindowRound.lean`,
`Workspace/Algo/TopThreeRound.lean`).**  `0 < n` and `I.1.1.1.1.length = n` are tests.  The
remaining clause, "when the node stores a window instance `W`, there are `t`, `i` and a coset
`c : RawGens × RawPerm` with `W = Algo.top2Leaf I.1 t i c`", quantifies over `c`
**unboundedly**: `c` is the answer of a sibling call, which the node does not carry.  So it
is not decidable at the node at all, let alone in polynomial time.

**`Algo.lcRound` (`Workspace/Algo/LocalCertRound.lean`, Thm. 7.5.1).**  `Algo.LCWF n I` is
`Algo.WinWF` on `I.1`, plus, when `I.2 = some (td, idx)`: `td.1.length ≤ n`, `∀ u ∈ td.1,
u < n` and `Algo.RawGens.WF td.1.length td.2` — all three tests, the last one being
`Algo.wftIsGensOf (td.1.length, td.2)` — and the two clauses
`∃ ψ, Algo.ImgsOf (descGens n I.1) (lcImgs td) ψ` and `idx = Algo.actCosetIndex …`, neither of
which is a test.

**On `Algo.ImgsOf`.**  `ImgsOf gens imgs ψ` says that `ψ` is a homomorphism from the group
generated by `gens` that sends the `i`-th generator to the `i`-th image.  Deciding
`∃ ψ, ImgsOf gens imgs ψ` is deciding whether the assignment "generator ↦ image" extends to a
homomorphism, that is, whether every relation among the generators holds among the images.
A finite check of that shape needs a presentation of `⟨gens⟩` on those generators, and the
shortest presentation of a permutation group on a given generating set can be exponentially
long, so no polynomial test of this shape is available with the tools of `Workspace/Algo/`.
There is a different route — decide the membership problem in the graph of the map inside the
direct product `⟨gens⟩ × ⟨imgs⟩`, by Sims's algorithm, which is polynomial — but no part of
`Workspace/Algo/` builds a strong generating set, so it is not available here either.  The
honest reading is the one the docstring of `Algo.LCWF` already gives: this clause is data
about the input, in the sense of Prop. 2.2.6's convention, and the parent that built the node
supplies it. -/

end Algo
