/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.2, Theorem 9.2.3 (Extended Design Lemma): the pieces of the combination of the
Design Lemma (§8) with Theorem 9.2.1.
-/
import Workspace.SplitOrJohnson.Minor
import Workspace.DesignLemma.Bridge
import Workspace.DesignLemma.NatRank

/-!
# §9.2 Theorem 9.2.3: the Design Lemma combined with Theorem 9.2.1

*"Combining the Design Lemma and Theorem 9.2.1 we obtain our overall combinatorial
partitioning tool"* (version 2.5, line 4027).  The paper states Theorem 9.2.3 without a
proof; the combination is the following, and this file supplies its three pieces.

Let `X` be an admissible input of Theorem 9.2.3 on the vertex set `Ω`, `n = |Ω|`, and let
`3/4 ≤ α < 1`.

1. *The hypotheses of the Design Lemma hold.*  Theorem 8.1.2 asks for `1/2 ≤ α < 1`,
   `2 ≤ k ≤ n/2` and symmetry defect `≥ 1 − α`; Theorem 9.2.3 gives `3/4 ≤ α < 1`,
   `2 ≤ k ≤ n/4` and symmetry defect `> 1 − α`, which is more.  This is
   `Babai.KAryInputs.two_le`, `.two_mul_le_card` and `.defect_ge`, the last one through
   the bridge `Babai.RelStructure.toKAry` (the two readings of "`k`-ary relational
   structure" have the same automorphism group).

2. *Outcomes (a) and (b) of the Design Lemma are outcome (a) of Theorem 9.2.3.*  In both
   cases the Design Lemma returns a canonical coloring of `Ω`; taking each color class as
   one block gives a colored partition, and Observation 7.1.4
   (`Babai.ColoredPartition.isAlphaPartition_of`) says that it is a colored
   `α`-partition, because in case (a) no color class has size `> αn`, and in case (b) the
   only class of size `> n/2` is the dominant class `C`, which the Design Lemma
   partitions nontrivially.

3. *Outcome (c) goes to Theorem 9.2.1, at the threshold `β = αn/|C|`.*  The Design Lemma
   returns a UPCC on the dominant class `C`, with `|C| > αn`.  Theorem 9.2.1 is applied to
   it with the threshold parameter

   `β = αn/|C|`,

   which satisfies `2/3 ≤ β < 1` (`Babai.designBeta_bounds`): `β < 1` because `|C| > αn`,
   and `β ≥ α ≥ 3/4` because `|C| ≤ n`.  With this `β` both outcomes of Theorem 9.2.1
   have exactly the size Theorem 9.2.3 asks for, since `β|C| = αn`: a colored
   `β`-partition of `C` has blocks of size `≤ β|C| = αn`, and an embedded Johnson scheme
   on a subset of `C` of size `≥ β|C|` has size `≥ αn`.  The transfer to `Ω` — adding
   `Ω \ C` as one block of a new color — is the transfer clause of Lemma 9.3.1
   (`Babai.lemma_9_3_1_transfer`) with the roles of the two thresholds as above; here it
   is `Babai.theorem_9_2_3_transfer`.

   The choice `β = αn/|C|` is the same device as the `α = βn/d₂` of Lemma 9.3.1.

## Numbering map

| Paper | Lean |
|---|---|
| the hypotheses of Thm. 8.1.2 hold for an input of Thm. 9.2.3 | `Babai.KAryInputs.two_le`, `.two_mul_le_card`, `.defect_ge` |
| *"`β = αn/|C|`"*, the threshold handed to Thm. 9.2.1 | `Babai.designBeta`, `Babai.designBeta_bounds` |
| the transfer of a solution for `C` to a solution for `Ω` | `Babai.theorem_9_2_3_transfer` |
| the category of the outcomes of Theorem 8.1.2 that §9 uses | `Babai.DesignOutcomes`, `Babai.IsDesignOutcome` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### 1. The hypotheses of the Design Lemma -/

namespace KAryInputs

variable {k : ℕ} {α : ℝ}

/-- Theorem 9.2.3: *"`2 ≤ k`"*. -/
theorem two_le (X : Pt (KAryInputs Ω k α)) : 2 ≤ k := X.obj.2.1

/-- Theorem 9.2.3 asks for `k ≤ n/4`, Theorem 8.1.2 for `k ≤ n/2`. -/
theorem two_mul_le_card (X : Pt (KAryInputs Ω k α)) (inst : Fintype ↥X.car) :
    2 * k ≤ @Fintype.card ↥X.car inst := by
  have h := X.obj.2.2.1
  have hc : @Fintype.card ↥X.car inst = X.car.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  omega

/-- Theorem 9.2.3 asks for relative symmetry defect `> 1 − α`, Theorem 8.1.2 for `≥ 1 − α`.
The defect is read through the bridge `Babai.RelStructure.toKAry`, which does not change
the automorphism group. -/
theorem defect_ge (X : Pt (KAryInputs Ω k α)) :
    (1 : ℝ) - α ≤ ((@defect _ (Fintype.ofFinite _) (Classical.decEq _)
      (X.obj.1.1.toKAry X.obj.1.2).Aut : ℚ) : ℝ) := by
  have h : (1 : ℝ) - α <
      ((@structDefect _ _ _ (Fintype.ofFinite _) (Classical.decEq _) X.obj.1.1 : ℚ) : ℝ) :=
    X.obj.2.2.2
  rw [@RelStructure.defect_toKAry _ _ (Fintype.ofFinite _) (Classical.decEq _)]
  exact le_of_lt h

end KAryInputs

/-! ### 3. The threshold `β = αn/|C|` handed to Theorem 9.2.1 -/

/-- §9.2, the proof of Theorem 9.2.3: the threshold parameter handed to Theorem 9.2.1 for
the UPCC on the dominant class `C`, namely `β = αn/|C|`.  It is chosen so that
`β|C| = αn`, which makes both outcomes of Theorem 9.2.1 for `C` outcomes of Theorem 9.2.3
for `Ω`. -/
noncomputable def designBeta (α : ℝ) (V C : Set Ω) : ℝ :=
  α * (V.ncard : ℝ) / (C.ncard : ℝ)

omit [Fintype Ω] [DecidableEq Ω] in
/-- `β|C| = αn`: the defining property of `β = αn/|C|`.  (`|C| > αn ≥ 0` forces
`|C| ≠ 0`.) -/
theorem designBeta_mul {α : ℝ} (hα : 0 ≤ α) {V C : Set Ω}
    (hlt : α * (V.ncard : ℝ) < (C.ncard : ℝ)) :
    designBeta α V C * (C.ncard : ℝ) = α * (V.ncard : ℝ) := by
  have h0 : (0 : ℝ) ≤ α * (V.ncard : ℝ) := by positivity
  have hc : (C.ncard : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt h0 hlt)
  exact div_mul_cancel₀ _ hc

omit [DecidableEq Ω] in
/-- `2/3 ≤ β < 1`: the hypothesis of Theorem 9.2.1 for the threshold `β = αn/|C|`.
`β < 1` is `|C| > αn`, and `β ≥ α ≥ 3/4 > 2/3` is `|C| ≤ n`. -/
theorem designBeta_bounds {α : ℝ} (hα : 3 / 4 ≤ α) {V C : Set Ω} (hC : C ⊆ V)
    (hlt : α * (V.ncard : ℝ) < (C.ncard : ℝ)) :
    2 / 3 ≤ designBeta α V C ∧ designBeta α V C < 1 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have h0 : (0 : ℝ) ≤ α * (V.ncard : ℝ) := by positivity
  have hcpos : (0 : ℝ) < (C.ncard : ℝ) := lt_of_le_of_lt h0 hlt
  have hCV : C.ncard ≤ V.ncard := Set.ncard_le_ncard hC (Set.toFinite _)
  have hCV' : (C.ncard : ℝ) ≤ (V.ncard : ℝ) := by exact_mod_cast hCV
  have hvpos : (0 : ℝ) < (V.ncard : ℝ) := lt_of_lt_of_le hcpos hCV'
  refine ⟨?_, ?_⟩
  · -- `αn/|C| ≥ αn/n = α`
    have h1 : α * (V.ncard : ℝ) / (V.ncard : ℝ) ≤ α * (V.ncard : ℝ) / (C.ncard : ℝ) :=
      div_le_div_of_nonneg_left h0 hcpos hCV'
    rw [mul_div_assoc, div_self (ne_of_gt hvpos), mul_one] at h1
    unfold designBeta
    linarith
  · exact (div_lt_one hcpos).2 hlt

/-- §9.2, the proof of Theorem 9.2.3: the transfer of a solution for the dominant class
`C` to a solution for the whole vertex set `V`.

This is the transfer clause of Lemma 9.3.1 (`Babai.lemma_9_3_1_transfer`) with the pair of
thresholds `(β, α) = (αn/|C|, α)`, for which the required equality `β|C| = α|V|` is the
definition of `β`.  In objective (a) the extra block is `V \ C`, of size
`|V| − |C| < (1 − α)|V| ≤ α|V|` since `α ≥ 1/2`; in objective (b) the Johnson scheme is
already large enough, since `β|C| = α|V|`. -/
theorem theorem_9_2_3_transfer {α : ℝ} (hα : 3 / 4 ≤ α) {V C : Set Ω} (hC : C ⊆ V)
    (hlt : α * (V.ncard : ℝ) < (C.ncard : ℝ)) {Z : Pt (SplitOutcomes Ω)}
    (hZ : IsSplitOutcome (designBeta α V C) C Z) :
    ∃ Z' : Pt (SplitOutcomes Ω), IsSplitOutcome α V Z' := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have h0 : (0 : ℝ) ≤ α * (V.ncard : ℝ) := by positivity
  have hcpos : (0 : ℝ) < (C.ncard : ℝ) := lt_of_le_of_lt h0 hlt
  refine lemma_9_3_1_transfer hC ?_ (by linarith) (designBeta_mul hα0 hlt) hZ
  exact le_of_lt ((div_lt_one hcpos).2 hlt)

/-! ### The category of the outcomes of Theorem 8.1.2 that §9 uses -/

/-- §8.1, Theorem 8.1.2, in the form §9 consumes it: the outcome is *either* a colored
partition of the vertex set *or* a UPCC canonically embedded on the dominant color class.

Outcomes (a) and (b) of Theorem 8.1.2 are both a canonical coloring of `Ω`, which becomes
a colored partition of `Ω` (in case (b) the dominant class carries the canonical
equipartition); they are the first summand.  Outcome (c) is the second summand: the UPCC
on the dominant class.

*The coloring of outcome (c).*  Theorem 8.1.2 (c) returns the coloring of `Ω` as well as
the UPCC.  §9 does not use it: in the proof of Theorem 9.2.3 the partition of `Ω` outside
the dominant class is rebuilt from scratch by the transfer of Lemma 9.3.1
(`Babai.extendPartition`), which puts `Ω \ C` into a single block of a new color.  So the
second summand carries only the UPCC. -/
def DesignOutcomes (Ω : Type) : Cat.{0, 0} Ω :=
  Cat.sum (ColoredPartitions Ω ℕ) (UPCCs Ω)

/-- §8.1, Theorem 8.1.2, in the form §9 consumes it: the property of the outcome, for the
vertex set `W` and the threshold parameter `α`.

Case (a)/(b): the outcome lives on all of `W` and is a colored `α`-partition (Def. 7.1.1).
Case (c): the outcome lives on a subset of `W` — the dominant color class — of size
`> α|W|`, and is a UPCC by the definition of `Babai.UPCCs`. -/
def IsDesignOutcome (α : ℝ) (W : Set Ω) (Z : Pt (DesignOutcomes Ω)) : Prop :=
  match Z.obj with
  | Sum.inl P => Z.car = W ∧ letI : Fintype ↥Z.car := Fintype.ofFinite _;
      P.IsAlphaPartition α
  | Sum.inr _ => Z.car ⊆ W ∧ α * (W.ncard : ℝ) < (Z.car.ncard : ℝ)

end Babai
