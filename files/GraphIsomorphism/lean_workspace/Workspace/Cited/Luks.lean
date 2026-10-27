/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Cited results of Section 11 (Algorithmic setup).
-/
import Workspace.Luks.Defs

/-!
# Cited results, Section 11

Results that version 2.5 cites from the literature without proof, for Section 11.  Each is
an `axiom`, stated exactly as the paper states it: same hypotheses, same conclusion,
nothing added, nothing dropped, not specialized to our use.  See `CITED.md` (entries C14,
C15, C16) and `PLAN.md` (decision 1).

This file contains **one** axiom, Theorem 11.2.3 (Cameron, Maróti).  The other cited
items of Section 11 get no axiom in this file:

* `[Ba86]` (C14), "every minimal set of generators has `≤ 2n` elements": the paper uses it
  only to say that a permutation group is represented concisely; no proof and no cost
  estimate of Section 11 uses the bound.  It is recorded as the statement-only
  `Babai.Theorem_Ba86_minimal_generating_sets_statement` in `Workspace/Luks/Framework.lean`.
* C16, "Cameron groups can be recognized and their structure mapped out in polynomial
  time (and even in NC [BaLS])": purely algorithmic.  By a decision of the user it is an
  axiom on the RAM, `Babai.cameronStructure_polyTime`, in its own file
  `Workspace/Cited/CameronRecognition.lean` (it needs the machine layer, which this file
  must not import); see the corrected paper.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

/-- §11.2, **Theorem 11.2.3** (Cameron, Maróti).

Quoted from the paper:

> **Theorem 11.2.3** (Cameron [Cam81], Maróti [Mar]).  For `n ≥ 25`, if `G` is primitive
> and `|G| ≥ n^{1+log₂ n}` then `G` is a Cameron group.

The paper gives no proof.  "Cameron group" is Definition 11.2.2, transcribed as
`Babai.IsCameronGroup` (the parameters `s, t, k` are existentially quantified here, as in
the paper's "`G` is a Cameron group").

**Citation.** `[Cam81]` = Peter J. Cameron: *Finite permutation groups and finite simple
groups*, Bull. London Math. Soc. **13** (1981), 1–22.  `[Mar]` = Attila Maróti: *On the
orders of primitive groups*, J. Algebra **258** (2002), no. 2, 631–640.  The paper gives
no theorem number in either source.

**CFSG.** The paper states in §1.2.3 and §16.1 that this result depends on the
Classification of Finite Simple Groups.

**Used where.** Theorem 11.2.1 ("The mathematical part of this result is an immediate
consequence of Cameron's classification of large primitive groups which we state below"),
hence Procedure Reduce-to-Johnson (§11.3), hence line 1 of the Master Algorithm (§15).

**Consistency.**  `IsPrimitive` is the paper's primitivity (`|G| ≥ 2` and no nontrivial
blocks), not Mathlib's `IsPreprimitive`; for `n ≥ 25` the two agree.  The threshold
`n ≥ 25` and the bound `|G| ≥ n^{1+log₂ n}` are as printed, with `log₂` the binary
logarithm (`Real.logb 2`) and the power a real power (`Real.rpow`).  For `n = 25` the
bound reads `|G| ≥ 25^{1+log₂ 25} ≈ 1.6·10⁸`, which only the giants `S₂₅` and `A₂₅`
satisfy among the primitive groups of degree `25`; both are Cameron groups with
`s = t = 1`, `k = 25`. -/
axiom Theorem_11_2_3 {Ω : Type*} [Fintype Ω] (G : Subgroup (Equiv.Perm Ω))
    (hn : 25 ≤ Fintype.card Ω) (hprim : IsPrimitive G)
    (hcard : (Fintype.card Ω : ℝ) ^ (1 + Real.logb 2 (Fintype.card Ω)) ≤ (Nat.card G : ℝ)) :
    ∃ s t k : ℕ, IsCameronGroup G s t k

end Babai
