/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: the Design Lemma as a reduction at a multiplicative cost (§6).
-/
import Workspace.DesignLemma.Main
import Workspace.Functors.Equivariant
import Mathlib.Data.Fintype.CardEmbedding

/-!
# §8.1 as a reduction at a multiplicative cost

Theorem 8.1.2 says that *"we can find a value `ℓ ≤ k − 1` and a string
`x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ` distinct vertices such that by individualizing each `x_j` we
obtain …"*.  In the language of §6 (`Babai.FindsAtMultCost`) this is a reduction whose
tuple of "versions" of the input is the family of individualized strings: the
multiplicative cost is the number of admissible strings.

This file contains the part of that restatement that does not depend on the shape of the
categories of §9: the count of admissible strings (`card_shortDistinctStrings_le`), which
is the cost bound `n^k` of Theorem 8.1.2 and of Theorem 9.2.3, and the list of what is
still missing.

## The cost

The admissible strings are the strings of `ℓ ≤ k − 1` distinct vertices, that is, the
injective maps `Fin ℓ → Ω` for `ℓ < k`.  Their number is
`∑_{ℓ < k} n(n−1)…(n−ℓ+1) ≤ ∑_{ℓ < k} n^ℓ ≤ n^k`, the last step for `n ≥ 2`.  (For `n ≤ 1`
the bound `n^k` is false: with `n = 1` and `k ≥ 2` there are two admissible strings, the
empty one and the one-letter one, while `n^k = 1`.  Theorem 8.1.2 assumes `2k ≤ n`, so
`n ≥ 4`.)

## The `FindsAtMultCost` form

The restatement itself is `Babai.designLemma_finds` (`Workspace/DesignLemma/Reduction.lean`):
with `C := KAryInputs Ω k α` of `Workspace/SplitOrJohnson/`,

```
FindsAtMultCost C (DesignOutcomes Ω) (fun X => X.car.ncard ^ k)
  (fun X Z => IsDesignOutcome α X.car Z)
```

proved by `Babai.FindsAtMultCost.of_outcomes_sub` with the family `Babai.designOut` of the
outcomes at the strings at which Procedure "Design Lemma" returns.  Three pieces feed it:

1. *A bridge from `RelStructure` to `KAryRelStruct`.*  The objects of `KAryStructures Ω k`
   (`Workspace/SplitOrJohnson/Defs.lean`) are pairs `⟨X, h⟩` with `X : RelStructure ↥s` and
   `h : X.IsKAry k`, while §5 and §8 work with `KAryRelStruct ↥s C k` for a fixed color
   type `C`.  `Babai.RelStructure.toKAry` (`Workspace/DesignLemma/Bridge.lean`) takes
   `C := ℕ`, the *same* for every object, the color `i` naming the `i`-th relation of the
   list and the empty relation for `i ≥ r`.  The padding by empty relations is preserved by
   every bijection, so `Aut` is unchanged (`toKAry_aut`) and the defect hypothesis of
   Theorems 8.1.2 and 8.1.5 carries over (`defect_toKAry`); Def. 2.3.4 in the two readings
   agree (`toKAry_iso`).

2. *An outcome category.*  It is `Babai.DesignOutcomes`
   (`Workspace/SplitOrJohnson/ExtendedDesign.lean`), with the property
   `Babai.IsDesignOutcome`; outcomes (a) and (b) are merged into the first summand, as
   Observation 7.1.4 allows.  Both summands are `ℕ`-colorings and their morphisms preserve
   the color *labels*, while the colorings of §5 and §8 take values in an abstract type;
   `Babai.natRank` (`Workspace/DesignLemma/NatRank.lean`) is the naming, and
   `Babai.PartitionStructure.ofNatColoring` turns it into a partition structure in the
   sense of Def. 3.1.1.

3. *The outcome as a function of the input and the string.*  `Babai.designOutcome` makes
   no choice: the coloring is the vertex coloring of `X.kWL.restrTo hl x`, the dominant
   class is `dominantClass`, the equipartition is `designPartition`, and the configuration
   is the subconfiguration of `(X_x⃗)^{(2)}` induced on the dominant class.  Its
   equivariance is `Babai.designOut_equiv`, which goes through
   `Babai.KAryRelStruct.kWL_iso_restrTo` and the transport of the `k`-WL color type
   (`Babai.KAryPartStruct.designOutcomeOf_cast`).

The running-time clause of Theorem 8.1.2 (*"in time `n^{O(k)}`"*) is a separate matter and
is still pending; it belongs to the RAM model of `Workspace/Machine/`.
-/

open scoped Classical

namespace Babai

open Finset

/-- The admissible strings of Theorem 8.1.2: a length `ℓ ≤ k − 1` together with a string of
`ℓ` distinct vertices.  (`ℓ < k` is the paper's `ℓ ≤ k − 1`; `k ≥ 2` there.) -/
abbrev ShortDistinctStrings (Ω : Type*) (k : ℕ) : Type _ :=
  Σ l : Fin k, {x : Str Ω l // Str.Distinct x}

/-- Strings of `l` distinct vertices are injections `Fin l → Ω`. -/
def strDistinctEquivEmbedding (Ω : Type*) (l : ℕ) :
    {x : Str Ω l // Str.Distinct x} ≃ (Fin l ↪ Ω) where
  toFun x := ⟨x.1, x.2⟩
  invFun g := ⟨g, g.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `∑_{l < k} n^l + 1 ≤ n^k` for `n ≥ 2`: the geometric sum. -/
theorem sum_pow_lt_succ_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (∑ l ∈ Finset.range k, n ^ l) + 1 ≤ n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (∑ l ∈ Finset.range (k + 1), n ^ l) + 1
        = ((∑ l ∈ Finset.range k, n ^ l) + 1) + n ^ k := by
      rw [Finset.sum_range_succ]; omega
    have h2 : n ^ k + n ^ k ≤ n ^ (k + 1) := by
      have : n ^ k * 2 ≤ n ^ k * n := Nat.mul_le_mul_left _ hn
      rw [pow_succ]
      omega
    omega

/-- The multiplicative cost of Theorem 8.1.2: the number of strings of at most `k − 1`
distinct vertices is at most `n^k`, where `n = |Ω|`.

The count is `∑_{ℓ < k} n(n−1)…(n−ℓ+1)`, one summand per length; each summand is at most
`n^ℓ`, and `∑_{ℓ < k} n^ℓ ≤ n^k` for `n ≥ 2` (`sum_pow_lt_succ_le`).  The hypothesis
`n ≥ 2` cannot be dropped: for `n = 1` and `k ≥ 2` there are two admissible strings and
`n^k = 1`.  Theorem 8.1.2 assumes `2 ≤ k ≤ n/2`. -/
theorem card_shortDistinctStrings_le (Ω : Type*) [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    (hn : 2 ≤ Fintype.card Ω) :
    Fintype.card (ShortDistinctStrings Ω k) ≤ Fintype.card Ω ^ k := by
  classical
  have hcard : Fintype.card (ShortDistinctStrings Ω k)
      = ∑ l : Fin k, Fintype.card {x : Str Ω l // Str.Distinct x} :=
    Fintype.card_sigma
  have hemb : ∀ l : ℕ, Fintype.card {x : Str Ω l // Str.Distinct x}
      ≤ Fintype.card Ω ^ l := by
    intro l
    have h1 : Fintype.card {x : Str Ω l // Str.Distinct x} = Fintype.card (Fin l ↪ Ω) :=
      Fintype.card_congr (strDistinctEquivEmbedding Ω l)
    rw [h1, Fintype.card_embedding_eq]
    simpa using Nat.descFactorial_le_pow (Fintype.card Ω) l
  have hsum : ∑ l : Fin k, Fintype.card {x : Str Ω l // Str.Distinct x}
      ≤ ∑ l ∈ Finset.range k, Fintype.card Ω ^ l := by
    rw [← Finset.sum_range fun l => Fintype.card {x : Str Ω l // Str.Distinct x}]
    exact Finset.sum_le_sum fun l _ => hemb l
  have hgeom := sum_pow_lt_succ_le hn k
  omega

end Babai
