/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Cited results of Section 2 (Preliminaries).
-/
import Workspace.Prelim.PermGroups

/-!
# Cited results, Section 2

Results that version 2.5 cites from the literature without proof, for Section 2.  Each is
an `axiom`, stated exactly as the paper states it: same hypotheses, same conclusion,
nothing added, nothing dropped, not specialized to our use.  See `CITED.md` (entry C1) and
`PLAN.md` (decision 1).

This file contains one axiom, Theorem 2.2.4 (a).  Theorem 2.2.4 (b) and Theorem 2.2.5 are
cited but never used in a proof or algorithm of version 2.5, so they are recorded as
statement-only `def`s in `Workspace/Prelim/PermGroups.lean` and get no axiom.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

/-- **Theorem 2.2.4 (a)** (Degree of transitivity), §2.2.2.

Quoted from the paper:

> **Theorem 2.2.4** (Degree of transitivity).  Let `G ≤ S_n` be `t`-transitive.  Assume
> `G` is not a giant.  Then
> (a) (Curtis, Kantor, Seitz [CuKS])  `t ≤ 5`.

Immediately after Theorem 2.2.5 the paper adds: "These results depend on the
Classification of Finite Simple Groups (CFSG)."  The paper gives no proof.

**Citation.** `[CuKS]` = Charles W. Curtis, William M. Kantor, and Gary M. Seitz: *The
2-transitive permutation representations of the finite Chevalley groups*, Trans. Amer.
Math. Soc. **218** (1976), 1–59.  The paper gives no theorem number.

**Used where.** Sec. 13.2 (AggregateCertificates, Theorem 13.2.1), item 2b: "(: so
`1 ≤ d ≤ 5` by Theorem 2.2.4 :)", to bound the number of individualized points by
`d - 1 ≤ 4`.  This is the only use of Theorems 2.2.4 and 2.2.5 in a proof or algorithm of
version 2.5.

**Warning (consistency).** The consistency of this axiom depends on `t`-transitivity being
the paper's notion, `Babai.IsMultiplyTransitive`, which is "the induced action on ordered
`t`-tuples of distinct elements is transitive" with the paper's "transitive" = *exactly one
orbit*.  In particular it forces `t ≤ |Ω|` (`Babai.le_card_of_multiplyTransitive`).  With
Mathlib's `MulAction.IsMultiplyPretransitive` instead, which is vacuously true whenever
`t > |Ω|`, the statement would be **false**: the trivial group on `3` points is not a
giant and would be `6`-transitive.  See the test section at the end of this file.  So this
axiom must never be restated in terms of `IsMultiplyPretransitive`. -/
axiom degtrans_le_five {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {G : Subgroup (Equiv.Perm Ω)} (hG : ¬ IsGiant G)
    {t : ℕ} (htrans : IsMultiplyTransitive G t) : t ≤ 5

/-! ### Test: the axiom is not vacuously inconsistent

The would-be counterexample to Theorem 2.2.4 (a) under Mathlib's weaker notion is the
trivial group on `3` points with `t = 6`: it is `6`-pretransitive in Mathlib's sense
(there are no injective `6`-tuples in a `3`-element set, so the condition is vacuous), but
it is *not* `6`-transitive in the paper's sense, which is what the axiom uses. -/

section Test

/-- The trivial group on `3` points is `6`-pretransitive in Mathlib's sense. -/
example : IsMultiplyPretransitive (⊥ : Subgroup (Equiv.Perm (Fin 3))) (Fin 3) 6 :=
  ⟨fun x _ => absurd (Function.Embedding.nonempty_iff_card_le.1 ⟨x⟩) (by simp)⟩

/-- But it is not `6`-transitive in the paper's sense, so it is not a counterexample to
`Babai.degtrans_le_five`. -/
example : ¬ IsMultiplyTransitive (⊥ : Subgroup (Equiv.Perm (Fin 3))) 6 := by
  intro h
  have := le_card_of_multiplyTransitive h
  simp at this

end Test

end Babai
