/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: the block design case `case_9_7`, assembled from its four branches.
-/
import Workspace.SplitOrJohnson.BlockDesignCase2
import Workspace.SplitOrJohnson.BlockDesignCase3

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The assembly -/

open BlkBlockDesignInputs in
/-- Case 3a of §9.7 at the common cost of `Babai.case_9_7`: the branch condition
`d₁ ≤ (7/3) log₂ n₁` is carried by the object, and `Babai.case_9_7_exp_3a` turns it into
`d₁ + 2 ≤ 7(⌊log₂ n₁⌋+1)/3 + 2`. -/
theorem case_9_7_case3a' :
    FindsAtMultCost
      ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
        (fun s X => ¬ Case2P s X.1)).full (fun s X => Case3aP s X.1.1)) (Out97 Ω)
      (fun X => cost97 ⟨X.car, X.obj.1.1.1⟩)
      (fun X Z => Good97 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  refine case_9_7_case3a.mono (fun X => ?_) (fun _ _ h => h)
  have hcase : (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).IsCase3a := X.obj.2
  have hexp := case_9_7_exp_3a hcase
  rw [show cost97 (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))
      = BlkBlockDesignInputs.numBlocks (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω)) ^
        (7 * (Nat.log 2 (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).n₁ + 1)
          / 3 + 2) from by rw [cost97, v₁_ncard]]
  exact pow_le_pow_exp (by omega) (by omega)

open BlkBlockDesignInputs in
/-- Case 3b of §9.7 at the common cost of `Babai.case_9_7`, by
`Babai.case_9_7_exp_3b`. -/
theorem case_9_7_case3b' :
    FindsAtMultCost
      ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
        (fun s X => ¬ Case2P s X.1)).full (fun s X => ¬ Case3aP s X.1.1)) (Out97 Ω)
      (fun X => cost97 ⟨X.car, X.obj.1.1.1⟩)
      (fun X Z => Good97 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  refine case_9_7_case3b.mono (fun X => ?_) (fun _ _ h => h)
  have hexp := case_9_7_exp_3b
    (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).n₁
  rw [show cost97 (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))
      = BlkBlockDesignInputs.numBlocks (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω)) ^
        (7 * (Nat.log 2 (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).n₁ + 1)
          / 3 + 2) from by rw [cost97, v₁_ncard]]
  exact pow_le_pow_exp (by omega) (by omega)

open BlkBlockDesignInputs in
/-- §9.7 (block design case).  *"Assumptions: no twins in `V₁`, `X₂` is the clique
configuration (rank-2)."*  (Version 2.5, lines 4234-4290.)

At the multiplicative cost of the Design Lemma — *"Apply the Design lemma to `H`, viewed as
a `d₁`-ary relational structure.  (Multiplicative cost `n₂^{d₁} < n₂^{(7/3) log₂ n₁}`.)"*,
Case 3a — the block design case either finishes Theorem 9.2.2 on `V₁` or makes major
progress in the sense of §9.5.

The threshold `α` and the number `n₂` in the outcome are those **of the input**
(`Babai.BlkBlockDesignInputs.alpha`, `Babai.BlkBlockDesignInputs.numBlocks`).  An earlier
form of this statement had `α` and a bound `N` on the measure as parameters of the theorem;
that form could not be applied at step 9 of §9.4, where `α` is `Babai.alphaNew` of the
input, and for `N = 0` it asked for more than §9.7 gives.

The exponent is `7 (⌊log₂ n₁⌋ + 1)/3 + 2`.  The paper's `d₁ ≤ (7/3) log₂ n₁` is with the
real logarithm, and `log₂ n₁ ≤ ⌊log₂ n₁⌋ + 1`.  The two extra factors `n₂` are the
multiplicative cost of Procedure Reduce-Part2-by-Color (at most `n₂`) and of §9.8
(*"The multiplicative cost is `n₂`"*), which Case 3a2 calls.

The proof is the case distinction of §9.7 — Case 1, Case 2, Case 3a, Case 3b — glued by
`Babai.FindsAtMultCost.cases`, whose hypothesis that the branch condition is an isomorphism
invariant is `Babai.BlkBlockDesignInputs.case1P_congr`,
`Babai.BlkBlockDesignInputs.case2P_congr` and
`Babai.BlkBlockDesignInputs.case3aP_congr` (all proved).  The four branches are
`Babai.case_9_7_case1`, `Babai.case_9_7_case2`, `Babai.case_9_7_case3a'` and
`Babai.case_9_7_case3b'`; all four are proved. -/
theorem case_9_7 :
    FindsAtMultCost (BlkBlockDesignInputs Ω)
      (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω))
      (fun X => BlkBlockDesignInputs.numBlocks X ^
        (7 * (Nat.log 2 (BlkBlockDesignInputs.V₁ X).ncard + 1) / 3 + 2))
      (fun X Z => IsBlkDesignOutcome (BlkBlockDesignInputs.alpha X)
        (BlkBlockDesignInputs.V₁ X) (BlkBlockDesignInputs.numBlocks X) Z) := by
  have h3 := FindsAtMultCost.cases
    (C := (((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
      (fun s X => ¬ Case2P s X.1)))
    (P := fun s X => Case3aP s X.1.1)
    (costp := fun Z => cost97 ⟨Z.car, Z.obj.1.1⟩)
    (costn := fun Z => cost97 ⟨Z.car, Z.obj.1.1⟩)
    (Good := fun Z W => Good97 ⟨Z.car, Z.obj.1.1⟩ W)
    (fun {X Y} h hx => case3aP_congr (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) h hx)
    case_9_7_case3a' case_9_7_case3b'
  have h3' := h3.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  have h2 := FindsAtMultCost.cases
    (C := ((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)))
    (P := fun s X => Case2P s X.1)
    (costp := fun Z => cost97 ⟨Z.car, Z.obj.1⟩)
    (costn := fun Z => cost97 ⟨Z.car, Z.obj.1⟩)
    (Good := fun Z W => Good97 ⟨Z.car, Z.obj.1⟩ W)
    (fun {X Y} h hx => case2P_congr (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) h hx)
    case_9_7_case2 h3'
  have h2' := h2.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  have h1 := FindsAtMultCost.cases
    (C := BlkBlockDesignInputs Ω) (P := Case1P)
    (costp := cost97) (costn := cost97) (Good := Good97)
    (fun {X Y} h hx => case1P_congr h hx) case_9_7_case1 h2'
  exact h1.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

end Babai
