/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Cited results of Section 10 (Alternating quotients of a permutation group).
-/
import Workspace.AltQuotients.Defs

/-!
# Cited results, Section 10

Results that version 2.5 cites from the literature without proof, for Section 10.  Each is
an `axiom`, stated exactly as the paper states it: same hypotheses, same conclusion,
nothing added, nothing dropped, not specialized to our use.  See `CITED.md` (entries
C8–C13) and `PLAN.md` (decision 1).

Two axioms, for one cited result and Schreier's Hypothesis:

| Paper | `CITED.md` | Lean |
|---|---|---|
| `A_k` involved in `GL(s,p)` (proof of Lemma 10.2.5) | C10 | `Babai.le_add_two_of_involved_GL` |
| Schreier's Hypothesis (proof of Lemma 10.2.5) | C11 | `Babai.schreierHypothesis` |

Not axiomatized:

* **[DiM, Thm. 5.2A] and [DiM, Thm. 5.2B]** (C12, cited by Theorem 10.4.2): they were
  axioms; they are now proved, with the same statements, along Dixon–Mortimer §5.2
  (`Babai.dixonMortimer_5_2A` in `Workspace/AltQuotients/DM52/Main52A.lean`,
  `Babai.dixonMortimer_5_2B` in `Workspace/AltQuotients/DM52/Main52B.lean`; see the section
  note below);

* **Theorem 10.2.4** (C9): it was an axiom; it is now proved, with the same statement,
  along Dixon–Mortimer, §§4.3, 4.5–4.7 (`Babai.theorem_10_2_4` in
  `Workspace/AltQuotients/ONanScott.lean`);
* **Fact 10.2.2 (ii)** (C8): it was an axiom; it is now proved, with the same statement,
  along Dixon–Mortimer, Thms. 4.3A (ii) and 4.3B (`Babai.fact_10_2_2_ii` in
  `Workspace/AltQuotients/SocleFact.lean`);
* **Fact 10.2.2 (i)** ("the socle of any group is a direct product of simple groups"):
  cited, but used in no proof of the paper — Lemma 10.2.5 and §11.2 both use part (ii),
  which applies because the group there is primitive.  So it gets no axiom and is
  recorded as a statement only (`Babai.Fact_10_2_2_i_statement` in
  `Workspace/AltQuotients/PrimitiveQuotient.lean`);

* **Theorem 10.4.2** (Jordan–Liebeck) itself: the paper cites it from
  `[DiM, Thm. 5.2A,B]`; Theorem 10.4.2 is *proved* from those two theorems (`Babai.theorem_10_4_2` in
  `Workspace/AltQuotients/SmallIndex.lean`) — with the exceptional cases of the source,
  which the paper drops, restored; its uniqueness half is proved from Observation 10.4.1,
  as the paper says;
* **Proposition 10.5.4** (C13), a purely algorithmic claim ("we can find the standard
  blocks in each `G`-orbit in polynomial time", proof "Standard").  Its mathematical
  content is Theorem 10.5.1 (e), recorded as a statement-only item
  (`Babai.Proposition_10_5_4_statement`).  The running-time half is proved on the RAM:
  `Algo.proposition_10_5_4` in `Workspace/Algo/StdBlocksProved.lean` (it was an axiom by a
  decision of the user until then);
* **Remark 10.1.2** and **Lemma 10.1.3** (Meierfrankenfeld) and **Remark 10.2.7** (Pyber):
  cited but used in no proof of the paper (Lemma 10.1.3 is offered as an alternative route
  to Lemma 10.1.1, which the paper proves in full), so they are statement-only `def`s in
  `Workspace/AltQuotients/Subdirect.lean` and `.../PrimitiveQuotient.lean`;
* the simplicity of `A_k` for `k ≥ 5` and the bound "the largest proper subgroup of `A_k`
  has index `k`" (proof of Cor. 10.3.7): the paper uses these as background, with **no**
  citation, so they get no axiom.  They are proved:
  `Babai.isSimpleGroup_alternatingGroup` in `Workspace/Prelim/AlternatingSimple.lean` and
  the index bound in `Workspace/Prelim/AlternatingIndex.lean` (see
  `Workspace/AltQuotients/PrelimExtra.lean`).
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Fact 10.2.2: structure of the socle

Neither part is an axiom.  Part (i) is used in no proof of the paper (`PLAN.md`,
Decision 4); it is `Babai.Fact_10_2_2_i_statement` in
`Workspace/AltQuotients/PrimitiveQuotient.lean`.  Part (ii) is proved:
`Babai.fact_10_2_2_ii` in `Workspace/AltQuotients/SocleFact.lean`. -/

/-! ### Theorem 10.2.4

Not an axiom any more: it is proved, with the same statement, along Dixon–Mortimer §§4.3,
4.5–4.7 (`Babai.theorem_10_2_4` in `Workspace/AltQuotients/ONanScott.lean`). -/

/-! ### `A_k` involved in `GL(s, p)` -/

/-- **`A_k` involved in `GL(s,p)`**, §10.2, inside the proof of Lemma 10.2.5 (Case 1, the
affine case).

Quoted from the paper:

> Moreover `A_k` is involved in `GL(s, p)`.  It is shown in [BaPS, Prop. 1.22] that if
> `A_k` is involved in `GL(s, p)` then, combining a result of Feit and Tits [FeT] with
> [KlL, Prop. 5.3.7], for `k ≥ 9` it follows that `k ≤ s + 2`.

**Citation.** `[BaPS, Prop. 1.22]` = László Babai, Péter P. Pálfy, Jan Saxl, *On the
number of `p`-regular elements in finite simple groups*, LMS J. Comput. Math. **12**
(2009), 82–119, Prop. 1.22 — itself a rendering of `[FeT]` = Walter Feit, Jacques Tits,
*Projective representations of minimum degree of group extensions*, Canad. J. Math. **30**
(1978), 1092–1102, combined with `[KlL, Prop. 5.3.7]` = Peter Kleidman, Martin Liebeck,
*The Subgroup Structure of the Finite Classical Groups*, LMS Lecture Note Ser. 129, CUP
1990, Prop. 5.3.7.  The acknowledgments of the paper confirm that `k ≤ s + 2` is the
paper's rendering of that result.

**Used where.** Lemma 10.2.5, Case 1, to reach the contradiction
`k ≤ s + 2 ≤ 2 + log_p n < k`.

**"Involved".** The paper never defines the word; `Babai.Involved A B` is the standard
usage, "`A` is a quotient of a subgroup of `B`" (`A` is a *section* of `B`), here stated
as "some subgroup of `B` admits an epimorphism onto `A`".

**Warning (consistency).** `p` is a prime and `GL(s,p)` is over the field with `p`
elements (`Matrix.GeneralLinearGroup (Fin s) (ZMod p)`); the hypothesis `p.Prime` is the
paper's context (`N ≅ ℤ_p^s`, `G/N ≤ GL(s,p)`), not an addition.  For `s = 0` the group
`GL(0,p)` is trivial, so no `A_k` with `k ≥ 9` is involved and the axiom is vacuous
there. -/
axiom le_add_two_of_involved_GL {k s p : ℕ} (hp : p.Prime) (hk : 9 ≤ k)
    (h : Involved (alternatingGroup (Fin k)) (Matrix.GeneralLinearGroup (Fin s) (ZMod p))) :
    k ≤ s + 2

/-! ### Schreier's Hypothesis -/

/-- **Schreier's Hypothesis**, §1.2.2 and §10.2 (before Lemma 10.2.5).

Quoted from the paper:

> Another ingredient where we rely on CFSG occurs in the proof of Lemma 10.2.5 that
> depends on "Schreier's Hypothesis" (that the outer automorphisms group of a finite
> simple group is solvable), a consequence of CFSG.  (§1.2.2)

and at the point of use:

> The proof depends on the CFSG through "Schreier's Hypothesis" (a known consequence of
> the CFSG) which states that the outer automorphism group of every finite simple group is
> solvable.  (§10.2)

**Citation.** None given: the paper states it as a known consequence of the Classification
of Finite Simple Groups.  It is one of the two places (§16.1) where the paper relies on
the CFSG.

**Used where.** Lemma 10.2.5, Case 2: "`Pker(G)/N ≤ Out(R₁) × ⋯ × Out(R_s)` is solvable by
Schreier's Hypothesis" — and hence in everything that rests on Lemma 10.2.5: Lemmas
10.3.1, 10.3.3, Theorem 10.3.5, Theorem 10.5.1, Procedure LocalCertificates (§13.1).

Unlike Theorem 2.2.5 (b), which carries the hypothesis explicitly because the paper does,
Lemma 10.2.5 uses Schreier's Hypothesis unconditionally, so it is asserted here.
`Babai.SchreierHypothesis` (`Workspace/Prelim/SchreierHypothesis.lean`) is
`∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], IsSolvable (Out S)` with
`Out S = MulAut S ⧸ Inn S`.

**Warning (consistency).** The statement is usually quoted for *nonabelian* finite simple
groups; for the abelian ones, `Out(ℤ_p) = ℤ_{p-1}` is abelian, hence solvable, so the
statement as printed is true for all finite simple groups and needs no repair.  The axiom
is universe-polymorphic, which is no strengthening: `Babai.schreierHypothesis_iff` proves
that the statement at one universe implies it at every other. -/
axiom schreierHypothesis : SchreierHypothesis.{u}

/-! ### [DiM, Thm. 5.2A,B]: subgroups of small index in `A_n` and `S_n`

Not axioms any more.  Babai's Theorem 10.4.2 (Jordan–Liebeck) says: "We cite from the
version given in [DiM, Thm. 5.2A,B]", but drops the exceptional cases of those two theorems,
which makes his statement false (see the corrected paper "Theorem 10.4.2
(Jordan–Liebeck): the cited theorem is mis-transcribed").  So the two theorems of the source
were the axioms, verbatim; they are now proved with the same statements:
`Babai.dixonMortimer_5_2A` (`Workspace/AltQuotients/DM52/Main52A.lean`, along the proof of
[DiM, pp. 147–149] and Exercises 5.2.1–5.2.6 for the primitive groups of degree at most `14`)
and `Babai.dixonMortimer_5_2B` (`Workspace/AltQuotients/DM52/Main52B.lean`, from Theorem 5.2A
applied to `G ∩ A`, the exercise of [DiM, p. 150]).  Babai's Theorem 10.4.2 with its
exceptional cases restored is proved from them in `Workspace/AltQuotients/SmallIndex.lean`
(`Babai.theorem_10_4_2`).  The docstrings of the two theorems keep the quotations and the
citation.

`[DiM]` = John D. Dixon, Brian Mortimer, *Permutation Groups*, Graduate Texts in
Mathematics 163, Springer 1996; Theorem 5.2A is on p. 147 and Theorem 5.2B on
pp. 150–151.  The named groups of the exceptional cases are defined in
`Workspace/AltQuotients/NamedGroups.lean`.

**The Remark of the source is part of the meaning of case (iii)** (p. 147 after Thm 5.2A,
p. 151 after Thm 5.2B): "In part (iii) of the theorem, the groups are listed only with the
minimum `r` for which they satisfy the hypotheses of the theorem."  So a listed group also
satisfies the hypotheses for every larger admissible `r` — for instance `PSL₃(2) ≤ A₇` has
index `15 < 35 = C(7,3)`, and for `r = 3` neither (i) nor (ii) holds — and clause (iii) is
therefore stated as "`(n, |index|, G)` is one of the listed cases and `r` is **at least**
the listed `r`".  Stated with `r =` the listed value the theorems would be false.

**Notation.** `A_(Δ)` is the pointwise and `A_{Δ}`, `S_{Δ}` the setwise stabilizer
(`Babai.pointwiseStabilizer`, `Babai.setwiseStabilizer`; Eqs. (11), (12)).  "`G` is
imprimitive on `Ω`" is Dixon–Mortimer's usage (§1.5): transitive and not primitive; their
"primitive" (transitive, and the only blocks are the singletons and `Ω`) is the project's
`Babai.IsPrimitive`, which adds `|G| ≥ 2` — no difference here, since a transitive group
on `n ≥ 5` points has order at least `5`.  "imprimitive with two blocks of size `m`" is
transitivity together with the preservation of a partition of `Ω` into two halves
(`Babai.PreservesHalvingPartition`).  `1 ≤ r ≤ n/2` is `1 ≤ r` and `2 * r ≤ Nat.card Ω`
(non-strict, unlike Babai's `r < n/2`). -/

end Babai
