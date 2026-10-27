/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 9 and the assembly: one turn of Procedure Bipartite Split-or-Johnson,
the recursion of Section 9.5, and Theorem 9.2.2.
-/
import Workspace.SplitOrJohnson.BlockDesignAssemble
import Workspace.SplitOrJohnson.Step9
import Workspace.SplitOrJohnson.Step9Func
import Workspace.SplitOrJohnson.Step9Design

/-!
# §9.4, step 9, and the assembly of Theorem 9.2.2

Version 2.5, lines 4126-4182 of `babai-gi-source/quasi25.txt`.

| Paper | Lean |
|---|---|
| §9.4, steps 5-9 | `Babai.steps_9_4_5_to_9` |
| §9.4, steps 3-9 | `Babai.steps_9_4_3_to_9` |
| §9.4, one turn of the procedure | `Babai.procedure_9_4_turn` |
| Theorem 9.2.2 in the category of §9.4-§9.8 | `Babai.theorem_9_2_2_blocks` |
| Theorem 9.2.2 (Bipartite Split-or-Johnson) | `Babai.theorem_9_2_2` |
| Theorem 9.2.2 for a fixed `α` (the printed statement) | `Babai.theorem_9_2_2_at` |

## Why these statements live here and not with their definitions

Step 9 of §9.4 branches into the three cases of §9.6, §9.7 and §9.8, that is into
`Babai.lemma_9_6_1` (`Workspace/SplitOrJohnson/Imprimitive.lean`), `Babai.case_9_7` and
`Babai.case_9_8` (`Workspace/SplitOrJohnson/BlkCases.lean`).  Those modules import the
definitions of §9.2 and of §9.4, so the *statements* of the procedure and of Theorem 9.2.2
have to stand above them.  Only the statements moved here; every definition stays in
`Workspace/SplitOrJohnson/BipSplit.lean` and `Workspace/SplitOrJohnson/Main.lean`.  See the
entry on §9.4, steps 5-9 in the corrected paper.

## The constants are absolute

The constant `C₀` of steps 1 and 2 and the cost function `q` of Theorem 9.2.2 do not
depend on the ground set: in every statement of this file the ambient type `Ω` is bound
**inside** the existential, as `∃ C₀, ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], …`.  With
`Ω` bound first the statement would be vacuous, because for a fixed finite `Ω` a constant
function is a quasipolynomial bound on every input.  See the entry on the absolute
constants in the corrected paper.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### §9.4, step 9: the three branches

Each branch of step 9 calls its case, hands the instance the case returns back to the
recursion of §9.5, and transfers the solution to `(α, V₁)`.  The three are stated on the
full subcategories `Babai.Step9ImpInputs`, `Babai.Step9DesignInputs` and
`Babai.Step9UPCCInputs` of `Babai.BipBlockInputs` cut out by what the turn knows at step 9
(`Babai.Step9Cond`) and by the branch condition; the three functors
`Babai.step9ImpFunc`, `Babai.step9DesignFunc` and `Babai.step9UPCCFunc` carry an object to
the input of its case. -/

/-- §9.4, step 9(i).  **The branch of §9.6.**  `Babai.lemma_9_6_1` is applied through
`Babai.step9ImpFunc`; it returns either a colored `1/2`-partition of `W₁`, which is a
colored `α`-partition of `V₁` after the extension by `V₁ \ W₁`
(`Babai.transfer_finds_on`), or a bipartite graph on `W₁` with at most half as many blocks,
which is an admissible input of Theorem 9.2.2 for the threshold `α_new` of step 5
(`Babai.isThm922Input_of_halved`) and of strictly smaller measure, so the recursion `hrec`
applies to it.  The cost is `Babai.caseCost_mul_cost_9_4_le_of_halved`.

This is `Babai.step9_halvedBranch`, the branch that §9.6 and §9.8 share. -/
theorem branch_9_4_9_imprimitive (C₀ N : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost (Step9ImpInputs Ω N) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) :=
  step9_halvedBranch C₀ N (fun X => X.obj.2.1) hrec
    ((FindsAtMultCost.precomp (step9ImpFunc N) (step9ImpFunc_isCanonicalEmbedding N)
      lemma_9_6_1).mono (fun _ => le_rfl) (fun _ _ h => h))

/-- §9.4, step 9(ii).  **The branch of §9.7** (the block design case).

The branch splits once more, on whether the **input of the pass** carries the hint
(`Babai.HasHintAt`), which is an isomorphism invariant (`Babai.hasHintAt_congr`), so the
split is into full subcategories.

* The input carries the hint: §9.7 is not called.  The blocks that step 8 leaves form a
  clique of the hint, so there are at most `n₂/2` of them — the argument of Case 3a2 of
  §9.7 — and the recursion runs on the instance step 8 leaves
  (`Babai.branch_9_4_9_design_hint`).
* The input has no hint: §9.7 is called through `Babai.step9DesignFunc`, at a cost below
  one turn (`Babai.caseCost_9_7_le_turnCost`).  Its outcome `Babai.IsBlkDesignOutcome` is a
  solution for `(α_new, W₁)`, which transfers to `(α, V₁)`, or a smaller instance that
  already carries `α_new' |V₁'| = α_new |W₁|` and either `10 n₂' ≤ 9 n₂` or the hint; the
  recursion `hrec` applies to it and `Babai.caseCost_mul_costRec_9_7_le` pays for the call,
  using the bit `1` of the input (`Babai.branch_9_4_9_design_nohint`).

Why the first branch does not call §9.7: a pass that starts from a hinted instance and only
gains the hint again would not make the progress that §9.5 asks for.  See entries 88 and 94
of the corrected paper. -/
theorem branch_9_4_9_design (C₀ N : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost (Step9DesignInputs Ω N) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  classical
  refine (FindsAtMultCost.cases (C := Step9DesignInputs Ω N)
    (P := fun s Y => HasHintAt ⟨s, Y.1⟩)
    (costp := fun X => cost_9_4 C₀ (step9Base X))
    (costn := fun X => cost_9_4 C₀ (step9Base X))
    (Good := fun X Z => Good_9_2_2 (step9Base X) Z)
    (fun {_ _} h hx => hasHintAt_congr (by exact h) hx) ?_ ?_).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  · exact FindsAtMultCost.precomp
      (show Func ((Step9DesignInputs Ω N).full fun s Y => HasHintAt ⟨s, Y.1⟩)
          (DesignHintInputs Ω N) from
        fullOfBase _ (fun A => A.1.1) (fun h => h) (fun A => ⟨A.1.2, A.2⟩))
      (fullOfBase_isCanonicalEmbedding
        (D := (Step9DesignInputs Ω N).full fun s Y => HasHintAt ⟨s, Y.1⟩)
        _ (fun A => A.1.1) (fun h => h) (fun A => ⟨A.1.2, A.2⟩))
      (branch_9_4_9_design_hint C₀ N hrec)
  · exact FindsAtMultCost.precomp
      (show Func ((Step9DesignInputs Ω N).full fun s Y => ¬ HasHintAt ⟨s, Y.1⟩)
          (DesignNoHintInputs Ω N) from
        fullOfBase _ (fun A => A.1.1) (fun h => h) (fun A => ⟨A.1.2, A.2⟩))
      (fullOfBase_isCanonicalEmbedding
        (D := (Step9DesignInputs Ω N).full fun s Y => ¬ HasHintAt ⟨s, Y.1⟩)
        _ (fun A => A.1.1) (fun h => h) (fun A => ⟨A.1.2, A.2⟩))
      (branch_9_4_9_design_nohint N C₀ hrec)

/-- §9.4, step 9(iii).  **The branch of §9.8.**  `Babai.case_9_8` is applied through
`Babai.step9UPCCFunc`; its outcome is `Babai.IsBlkImprimitiveOutcome`, the outcome of
§9.6, so this branch is `Babai.step9_halvedBranch` again, with `Babai.case_9_8` in place of
`Babai.lemma_9_6_1`. -/
theorem branch_9_4_9_upcc (C₀ N : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost (Step9UPCCInputs Ω N) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) :=
  step9_halvedBranch C₀ N (fun X => X.obj.2.1) hrec
    ((FindsAtMultCost.precomp (step9UPCCFunc N) (step9UPCCFunc_isCanonicalEmbedding N)
      case_9_8).mono (fun _ => le_rfl) (fun _ _ h => h))

/-! ### §9.4, steps 5-9 -/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- §9.4, steps 5-9, **for a fixed constant `C₀`**: the case distinction of steps 6 and 9,
glued by `Babai.FindsAtMultCost.cases`.  The four branches are `Babai.step_9_4_6` (the
imprimitive exit of step 6) and the three branches of step 9,
`Babai.branch_9_4_9_imprimitive`, `Babai.branch_9_4_9_design` and
`Babai.branch_9_4_9_upcc`, each reached through `Babai.fullOfBase`, which collapses the
tower of full subcategories that steps 1, 2, 4, 6 and 9 have cut out into the one full
subcategory of `Babai.BipBlockInputs` that the branch is stated on.

The constant `C₀` stays a variable here; `Babai.steps_9_4_5_to_9` picks a value for it. -/
theorem steps_9_4_5_to_9_at (C₀ N : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost
      ((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩)
      (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1.1⟩ Z) := by
  classical
  -- step 6: is `X₁` imprimitive?
  refine (FindsAtMultCost.cases
    (C := (((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩)
    (P := fun s Y => Step6Imprimitive ⟨s, Y.1.1.1.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1.1.1.1⟩ W)
    (fun {_ _} h hx => step6Imprimitive_congr (by exact h) hx)
    (step_9_4_6 Ω C₀ N) ?_).mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  -- step 9, branch (i): is `X₂` imprimitive?
  refine (FindsAtMultCost.cases
    (C := ((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
        fun s Y => ¬ Step6Imprimitive ⟨s, Y.1.1.1.1⟩)
    (P := fun s Y => Step9Imprimitive ⟨s, Y.1.1.1.1.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1.1.1.1.1⟩ W)
    (fun {_ _} h hx => step9Imprimitive_congr (by exact h) hx)
    ?_ ?_).mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  · -- case (i): §9.6
    exact FindsAtMultCost.precomp
      (show Func ((((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
            fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
            fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
            fun s Y => ¬ Step6Imprimitive ⟨s, Y.1.1.1.1⟩).full
            fun s Y => Step9Imprimitive ⟨s, Y.1.1.1.1.1⟩) (Step9ImpInputs Ω N) from
        fullOfBase _ (fun A => A.1.1.1.1.1.1) (fun h => h)
          (fun A => ⟨⟨A.1.1.1.1.1.2, A.1.1.2, A.1.2⟩, A.2⟩))
      (fullOfBase_isCanonicalEmbedding _ _ _ _)
      (branch_9_4_9_imprimitive C₀ N hrec)
  -- step 9, branch (ii): is `X₂` the clique configuration?
  refine (FindsAtMultCost.cases
    (C := (((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
        fun s Y => ¬ Step6Imprimitive ⟨s, Y.1.1.1.1⟩).full
        fun s Y => ¬ Step9Imprimitive ⟨s, Y.1.1.1.1.1⟩)
    (P := fun s Y => Step9Clique ⟨s, Y.1.1.1.1.1.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1.1.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1.1.1.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1.1.1.1.1.1⟩ W)
    (fun {_ _} h hx => step9Clique_congr (by exact h) hx)
    ?_ ?_).mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  · -- case (ii): §9.7
    exact FindsAtMultCost.precomp
      (show Func (((((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
            fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
            fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
            fun s Y => ¬ Step6Imprimitive ⟨s, Y.1.1.1.1⟩).full
            fun s Y => ¬ Step9Imprimitive ⟨s, Y.1.1.1.1.1⟩).full
            fun s Y => Step9Clique ⟨s, Y.1.1.1.1.1.1⟩) (Step9DesignInputs Ω N) from
        fullOfBase _ (fun A => A.1.1.1.1.1.1.1) (fun h => h)
          (fun A => ⟨⟨A.1.1.1.1.1.1.2, A.1.1.1.2, A.1.1.2⟩, A.1.2, A.2⟩))
      (fullOfBase_isCanonicalEmbedding _ _ _ _)
      (branch_9_4_9_design C₀ N hrec)
  · -- case (iii): §9.8
    exact FindsAtMultCost.precomp
      (show Func (((((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
            fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
            fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
            fun s Y => ¬ Step6Imprimitive ⟨s, Y.1.1.1.1⟩).full
            fun s Y => ¬ Step9Imprimitive ⟨s, Y.1.1.1.1.1⟩).full
            fun s Y => ¬ Step9Clique ⟨s, Y.1.1.1.1.1.1⟩) (Step9UPCCInputs Ω N) from
        fullOfBase _ (fun A => A.1.1.1.1.1.1.1) (fun h => h)
          (fun A => ⟨⟨A.1.1.1.1.1.1.2, A.1.1.1.2, A.1.1.2⟩, A.1.2, A.2⟩))
      (fullOfBase_isCanonicalEmbedding _ _ _ _)
      (branch_9_4_9_upcc C₀ N hrec)




/-- §9.4, steps 5-9 together with the three cases of §9.6, §9.7 and §9.8: the body of
Procedure Bipartite Split-or-Johnson on the instances that steps 1, 2 and 4 do not dispose
of, that is on those for which `n₁ > C₀`, `n₂ > C₀ log n₁`, and some vertex-color class of
`V₁` has more than `α n₁` points.

The proof is `Babai.steps_9_4_5_to_9_at`, with the constant `C₀ = 1`; every value works
for the estimates of steps 5-9, the constant of step 1 only having to be large enough for
step 2.

## No new category is needed: everything is a function of the input

The earlier plan was to build a category of *(bipartite graph with blocks, threshold,
coloring)*, because from step 5 on the paper restricts the coherent configuration `X`
instead of refining the restricted graph again, so the coloring looked like data that has
to be carried.  It is not.  Every object that steps 5 to 8 produce is a **function of the
object of this category alone**:

* the coloring of step 3 is `Babai.VColBipBlk.wlColor` of the input, a function of it;
* `W₁` is `Babai.dominantClass`, a function of the input
  (`Babai.dominantClass_image` is its canonicity), so the point set `W₁ ∪ V₂` of step 5 is
  `Babai.step5Set` and the restricted graph is `Babai.step5Obj`, both functions of the
  input, and the restricted *configuration* is the restriction of `wlColor` of the input;
* the color class `D_j` of step 7 and the constituent `Rᵢ` of step 8 are chosen by the
  colors of that same coloring, so they too are functions of the input; and the second WL
  refinement of step 8 is a function of the object it is applied to.

So steps 5 to 8 are one functor out of a full subcategory of *this* category, cut out by
the branch conditions of steps 6 and 7, into the input category of one of the three cases
of step 9, and the chain is `Babai.FindsAtMultCost.cases` for the branches and
`Babai.FindsAtMultCost.precomp` for the functor, exactly as steps 3 and 4 were.  This is
the cheaper of the two routes and it is the one taken here.

## What is proved of steps 5 to 9

Step 5 is **done** at the level of the objects:

* the update of the threshold, `α ← α n₁ / |W₁|`: `Babai.alphaNew`, with
  `Babai.claim_9_4_step5_at` for `2/3 ≤ α_new < 1`, `α_new |W₁| = α n₁` and `|W₁| ≥ 2`;
* the induced substructure `X[W₁ ∪ V₂]`: `Babai.step5Obj`, built with
  `Babai.VColBipBlk.restrictTo`, which is also what step 7 needs;
* `V₁ ← W₁` (`Babai.step5Obj_V₁_ncard`) and `n₂` unchanged
  (`Babai.step5Obj_numBlocks`);
* **the restricted instance is admissible**: `Babai.step5Obj_isThm922Input`.  The one
  delicate point, the symmetry defect, comes from
  `Babai.VColBipBlk.restrictTo_twin_imp` (a set of twins of the restriction is a set of
  twins of `X`) together with `Babai.ncard_le_alphaNew_mul_dominantClass`
  (a set of twins of `X` inside `V₁` has at most `α n₁ = α_new |W₁|` points).

What is missing is the rest of the chain:

* step 6 branches on the imprimitivity of `X₁`, and its Claim (the negative branch leaves a
  **uniprimitive** `X₁`, by the Large clique lemma 3.4.25),
* step 7 restricts `V₂` to the first vertex-color class `D_j` with `X[V₁, D_j]` nontrivial
  (the restriction is `Babai.VColBipBlk.restrictTo` again, with a different `s'`),
* step 8 replaces the coloring by the first constituent `Rᵢ` involved in `X₁₂` and refines
  again, with its Claim *"there are no `X`-twins in `V₁`"*,
* step 9 branches into `Babai.lemma_9_6_1`, `Babai.case_9_7` and `Babai.case_9_8` and
  composes the recursion hypothesis `rec` with `Babai.FindsAtMultCost.comp_dep`.

The cost accounting is item 9 of the docstring of `Babai.steps_9_4_3_to_9`.

## What is proved of step 9

The two pieces of bookkeeping that step 9 needs, and that do not depend on steps 6-8, are
proved in `Workspace/SplitOrJohnson/Step9.lean`:

* `Babai.isThm922Input_of_halved`: **the graph returned by §9.6 or by §9.8 is an admissible
  input of Theorem 9.2.2 for the threshold the procedure already carries.**  Those two
  cases keep `V₁` whole, so `α` does not change; `|V₂| < α|V₁|` survives because `n₂` has
  at least halved, and `1 - α ≤ 1/3 ≤ 1/2 ≤ defect₁` because `α ≥ 2/3`.  This is the only
  place in step 9 that uses the lower bound on the threshold.
* `Babai.caseCost_mul_cost_9_4_le`: **one turn pays for the recursive call it makes**, on
  `Babai.turnCost_mul_costFun_le` and `Babai.turnCost_mono`
  (`Workspace/SplitOrJohnson/Depth.lean`).  The cost of the §9.7 branch is below one turn
  by `Babai.caseCost_9_7_le_turnCost`, which is `Babai.designCost_le_turnCost` with the two
  extra factors `n₂` of `Babai.case_9_7` allowed for.

The `Y.car ⊆ X.car` that the cost accounting needs is **not** part of the outcome
predicates `Babai.IsBlkImprimitiveOutcome` and `Babai.IsBlkDesignOutcome`; it comes from
the composition itself.  `Babai.FindsAtMultCost.comp_dep` runs the second step on
`Babai.PairCatOf`, whose objects carry `sub_subset : sub ⊆ car`, so the recursive call is
made along `Babai.pairSndFunc`, a canonical embedding, and the instance handed to `rec`
lives on a subset of `□X`.  `Babai.FindsAtMultCost.comp` alone would not do: its cost
hypothesis quantifies over *every* `Y` with `Good₁ X Y`, and nothing there bounds `□Y`.

That the multiplicative cost of every branch is at least `1` is automatic: the `Case`
heading of §9.6, §9.7 and §9.8 contains `Babai.IsBipartiteCase.link_nontrivial`, which
makes `V₂` nonempty, so `n₂ ≥ 1` and `Babai.FindsAtMultCost.one_le_cost` is respected.

## Three obstacles

1. **Module layering.**  *Resolved.*  This is the module that was asked for: it stands
   above `Workspace/SplitOrJohnson/BlkCases.lean`, and holds the statements only.
2. **The threshold of `Babai.case_9_7`.**  *Resolved.*  `Babai.case_9_7` is now stated on
   `Babai.BlkBlockDesignInputs`, whose objects carry `α`.  Step 9 can supply what that
   category asks for: `α = Babai.alphaNew X` with `2/3 ≤ α < 1`
   (`Babai.claim_9_4_step5_at`) and `n₂ < α |V₁|`, because step 5 leaves `n₂` unchanged
   (`Babai.step5Obj_numBlocks`) and `α_new |W₁| = α n₁`, and steps 7 and 8 only shrink
   `n₂` and keep `V₁`.
3. **The transfer of a solution is stated for the wrong pair of sets.**  *Resolved.*
   `Babai.transfer_finds` (`Workspace/SplitOrJohnson/Sec92.lean`) carries a solution for a
   subset `W ⊆ □X` back to a solution for `□X`, because that is what Theorem 9.2.1 needs.
   Step 9 has to carry a solution for `V₁_new ⊆ V₁` back to a solution for `V₁`, and `V₁`
   is a proper subset of `□X` — the points of the blocks are in `□X` too.
   `Babai.transfer_finds_on` (`Workspace/SplitOrJohnson/Step9.lean`) is the same theorem
   with `□X` replaced by an isomorphism-invariant `V : Pt C → Set Ω` with `V X ⊆ □X`, and
   `Babai.transfer_finds` is its case `V X = □X`.

## The bridge from the coloring of step 3 to the configuration the three cases ask for

*Done*, in `Workspace/SplitOrJohnson/WLConfig.lean*.  The field
`Babai.IsBipartiteCase.coherent` asks for a `Babai.PartitionStructure` on the vertex set
`𝒱₁ ∪ 𝒞` whose `natColor` **is** the coloring the object carries.  It is
`Babai.VColBipBlk.wlConfig`, the ordered integer naming
(`Babai.PartitionStructure.ofNamedColoring`) of the named WL coloring on the vertices;
it is coherent (`Babai.VColBipBlk.wlConfig_isCoherent`), and
`Babai.VColBipBlk.exists_wlConfig` is the field `coherent` itself, once `X₁` and `X₂` are
homogeneous — which is what steps 5 and 7 arrange.  Three things were needed:

* Observation 3.3.4 (vertex-color awareness) and Observation 3.3.2 (*"a stable subset
  induces a coherent configuration"*) for *colorings* rather than for configurations
  (`Babai.WL.diag_fst_eq_of_eq`, `Babai.WL.isCoherentColoring_restrict`).  The second is
  also the restriction `X ← X[W₁ ∪ V₂]` of step 5 and `X ← X[V₁ ∪ D_j]` of step 7
  (`Babai.VColBipBlk.wlRestrictedConfig_coherent`);
* the vertex set is stable (`Babai.VColBipBlk.isStableSet_vtx`): the refinement refines the
  initial coloring, which already tells a vertex from a non-vertex;
* **the coloring the objects of §9.6-§9.8 carry is `Babai.VColBipBlk.wlCaseColor`, not
  `Babai.VColBipBlk.wlColor`.**  The two differ by the shift `+ 1` that `wlColor` puts on
  the colors of pairs of vertices to keep them apart from the padding color `0`
  (`Babai.VColBipBlk.wlColor_eq_wlCaseColor_succ`), so they have the same color classes on
  the vertices.  A `natColor` cannot carry that shift: its values are the elements of
  `Fin rank` and every color is used (Def. 3.1.1), so the color `0` is attained.  With
  `wlCaseColor` the padding color `0` is also a genuine color, which costs nothing: every
  construction of §9.6-§9.8 reads the coloring on the vertex set only
  (`Babai.BlkImprimitiveObj.isIso_of_vertexColor`).

So what is left of steps 5-9 is steps 6, 7 and 8 at the level of the objects: the branch
conditions (*"`X₁` is imprimitive"*, *"`X₂` is not homogeneous"*), the two restrictions,
the replacement of the coloring by one constituent and the second WL refinement, and the
three functors from the result into `Babai.BlkImprimitiveCases`,
`Babai.BlkBlockDesignInputs` and `Babai.BlkUPCCCases`.  Building those functors means
producing, from `Babai.VColBipBlk.wlColor`, the `Babai.PartitionStructure` that
`Babai.IsBipartiteCase` asks for, and proving the `Case` headings from
`Babai.claim_9_4_step6`, `Babai.claim_9_4_step7` and `Babai.claim_9_4_step8`. -/
theorem steps_9_4_5_to_9 :
    ∃ C₀ : ℕ, ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ),
      FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
          (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
          (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z) →
      FindsAtMultCost
        ((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
          fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
          fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩)
        (SplitOutcomes Ω)
        (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1.1⟩)
        (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1.1⟩ Z) := by
  refine ⟨1, fun Ω _ _ N hrec => ?_⟩
  exact steps_9_4_5_to_9_at 1 N hrec

/-- §9.4, steps 3-9 together with the three cases of §9.6, §9.7 and §9.8.  This is the
body of Procedure Bipartite Split-or-Johnson on the instances that steps 1 and 2 do not
dispose of: `n₁ > C₀` and `n₂ > C₀ log n₁`.

*"3. Apply WL refinement to `X`. … 4. If all vertex-color classes in `V₁` have size
`≤ αn₁` then return the colored partition of `V₁`, exit. 5. Let `W₁ ⊆ V₁` be the dominant
color class … 6. If `X₁` is imprimitive, return the connected components of the first
disconnected off-diagonal color, exit … 7. If `X₂` is not homogeneous … 8. Let `i` be the
smallest index such that `Rᵢ` is involved in `X₁₂`.  Replace `X ← (V₁, V₂; Rᵢ)` … 9. We
need to consider the following cases: (i) `X₂` is imprimitive: Section 9.6; (ii) `X₂` is
the clique configuration … Section 9.7; (iii) `X₂` is uniprimitive: Section 9.8."*
(Version 2.5, lines 4126-4172.)

The absolute constant `C₀` of steps 1 and 2 is chosen here: it is the threshold above
which the estimates of steps 3-9 hold.  Its existence is part of the statement, which is
why `C₀` is bound here and not in `step_9_4_1` and `step_9_4_2`, where every value works.

The hypothesis `rec` is the recursive call allowed by §9.5: Theorem 9.2.2 may be applied to
instances of strictly smaller measure.

The pieces of the three cases that are already proved are: §9.4 itself
(`Babai.claim_9_4_step2`, `Babai.claim_9_4_step5`, `Babai.claim_9_4_step6`,
`Babai.claim_9_4_step7`, `Babai.claim_9_4_step8`), §9.6 (`Babai.lemma_9_6_1`, proved in
full, together with `Babai.imprimitiveCase_split`, `Babai.case_9_6_1_step2`,
`Babai.lemma_9_6_2`), §9.7 (`Babai.case_9_7_1`, `Babai.case_9_7_2`, `Babai.case_9_7_3a1`,
`Babai.case_9_7_3a2`, `Babai.case_9_7_3b_t_le`), §9.8 (`Babai.claim_9_8`), and
Lemma 9.3.2 (`Babai.lemma_9_3_2`, `Babai.reducePart2ByColor_spec`).

**Partly proved.**  Steps 3 and 4 are proved here (`Babai.VColBipBlk.wlColor`,
`Babai.step_9_4_4`), and the case distinction of step 4 is what this theorem now is; what
remains is `Babai.steps_9_4_5_to_9`.

Steps 5-9 are a chain of *transformations* of the input, not a single
family of outcomes, so the proof is a composition of reductions, one per step.  The chain
below is the plan; each arrow is a `Babai.Func` together with a
`Babai.FindsAtMultCost.precomp` (a canonical embedding costs nothing) or a
`Babai.FindsAtMultCost.cases` (a branch), and the last arrow is a
`Babai.FindsAtMultCost.comp_dep` with the recursion hypothesis `rec`.

*The chain.*  Write `D₀` for the input category
`((BipBlockInputsAt Ω N).full ¬IsSmallPart₁ C₀).full ¬IsSmallPart₂ C₀`.

1. **Step 3 (WL refinement).**  *Proved*, in `Workspace/SplitOrJohnson/WLColor.lean`.  It
   needs no new category: the coloring `c = Babai.VColBipBlk.wlColor` of the coherent
   configuration `X` on the vertex set *"points of `V₁` plus blocks"* is a **function of
   the object**, so step 3 adds no data and costs `1`.  The coloring is coherent
   (`Babai.VColBipBlk.isCoherentColoring_wlRaw`) and canonical
   (`Babai.VColBipBlk.wlColor_map`, Eq. (26)), it refines the input
   (`Babai.VColBipBlk.f_eq_of_wlColor_eq`,
   `Babai.VColBipBlk.wlColor_ne_of_part₁_blocks`), and its labels are natural numbers, as
   the categories of §9.6-§9.8 require.  Two points had to be arranged for that: the
   refinement runs a number of rounds fixed in advance for the whole ambient set
   (`Babai.wlRounds`), so that the color type does not depend on the input, and the colors
   are named by `Babai.WL.namedIter`, which ranks tags at each round. Isomorphisms preserve
   these tags and their ranks.
2. **Step 4 (branch).**  *Proved*: `Babai.step_9_4_4`, glued by
   `Babai.FindsAtMultCost.cases` on `Babai.AllClassesSmall` — *"all vertex-color classes in
   `V₁` have size `≤ αn₁`"*.  In the positive branch the outcome is the colored partition
   of `V₁` into the vertex-color classes of `c`, which is a colored `α`-partition by the
   branch condition; this is `Babai.kerPartition` with the coloring
   `Babai.VColBipBlk.wlDiag` and costs `1`.  In the negative branch
   `Babai.claim_9_4_step5` gives the dominant class.
3. **Step 5 (restriction to `W₁`).**  `Func D₄ D₅` onto the subset `W₁ ∪ V₂` of `□X`, with
   `α ← α n₁ / |W₁|`; `Babai.claim_9_4_step5` says the new threshold is again in
   `[3/4, 1)` and that `α_new |W₁| = α n₁`, which is what carries a colored
   `α_new`-partition of `W₁` back to a colored `α`-partition of `V₁` (Lemma 9.3.1's
   bookkeeping).  Cost `1`.
4. **Step 6 (branch).**  `Babai.FindsAtMultCost.cases` on *"`X₁` is imprimitive"*.  In the
   positive branch the outcome is the components of `Babai.blockColor` of the restriction
   of `c` to `V₁`, a colored `1/2`-partition by Prop. 3.4.4 and hence a colored
   `α`-partition; `Babai.claim_9_4_step6` is the Claim that the negative branch leaves a
   **uniprimitive** `X₁` (Large clique lemma).  Cost `1`.
5. **Step 7 (restriction of `V₂`).**  `Func D₆ D₇` onto `V₁ ∪ D_j`, for the smallest `j`
   with `X[V₁, D_j]` nontrivial; `Babai.claim_9_4_step7` is *"such a `j` exists"*.  Cost
   `1`.  `n₂` does not increase.
6. **Step 8 (one constituent).**  `Func D₇ D₈` replacing `c` by the constituent `Rᵢ` for
   the smallest `i` involved in `X₁₂`, followed by WL refinement again (same renumbering
   as in step 1); `Babai.claim_9_4_step8` is the Claim *"there are no `X`-twins in `V₁`"*.
   Cost `1`.  The objects of `D₈` are exactly the inputs of the three cases: `X₁` a UPCC,
   `X₂` homogeneous, `X₁₂` nontrivial.
7. **Step 9 (three cases).**  Two nested `Babai.FindsAtMultCost.cases` on *"`X₂` is
   imprimitive"* and *"`X₂` is the clique configuration"*, and then
   `Babai.FindsAtMultCost.precomp` with the forgetful functors `D₈ → BlkImprimitiveCases`,
   `D₈ → BlkBlockDesignCases`, `D₈ → BlkUPCCCases` into `Babai.lemma_9_6_1` (cost `n₂`),
   `Babai.case_9_7` (cost `n₂^{⌊(7/3) log₂ n₁⌋+1}`) and `Babai.case_9_8` (cost `n₂`).
8. **The recursive call.**  The outcome of §9.6 and §9.8 is
   `Babai.IsBlkImprimitiveOutcome`: either a colored `1/2`-partition of `V₁`, which is a
   colored `α`-partition because `α ≥ 3/4`, or a new object of `BipBlockInputs Ω` with
   `2 |W₂| ≤ n₂`, hence `measure_9_5 < N` (`Babai.measure_9_5`), and symmetry defect
   `≥ 1/2` on `V₁`.  The outcome of §9.7 is `Babai.IsBlkDesignOutcome`, which already
   carries `measure_9_5 < N`.  In both cases `rec` applies to the new object, and
   `Babai.FindsAtMultCost.comp_dep` composes; the transfer of a solution for the new `V₁`
   back to a solution for the old one is the bookkeeping of steps 5 and 7
   (`α_new |V₁_new| = α |V₁|`, `V₁_new ⊆ V₁`).
9. **The cost.**  Steps 3-8 cost `1` each, step 9 costs at most
   `Babai.turnCost □X` (`Babai.designCost_le_turnCost` for the §9.7 branch, and
   `n₂ ≤ □X` for the other two), and the recursive call costs
   `cost_9_4 C₀` at an object with `n₂_new ≤ n₂/2`, hence with
   `steps09 n₂_new + 1 ≤ steps09 n₂`.  So the product is at most
   `turnCost n · constFactor C₀ · turnCost n ^ steps09 n₂ = cost_9_4 C₀ X`, which is the
   cost claimed.  The absolute constant `C₀` is fixed here; `C₀ = 1` works for the
   estimates above, the constant of the paper's step 1 only having to be large enough for
   step 2. -/
theorem steps_9_4_3_to_9 :
    ∃ C₀ : ℕ, ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ),
      FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
          (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
          (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z) →
      FindsAtMultCost
        (((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
          fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩)
        (SplitOutcomes Ω)
        (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1⟩)
        (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  obtain ⟨C₀, h59⟩ := steps_9_4_5_to_9
  refine ⟨C₀, fun Ω _ _ N hrec => ?_⟩
  -- step 4: are all vertex-color classes of `V₁` small?  A canonical case distinction.
  have hP : ∀ {X Y : Pt (((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩)},
      ((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).IsoP X Y).Nonempty →
        AllClassesSmall ⟨X.car, X.obj.1.1.1⟩ → AllClassesSmall ⟨Y.car, Y.obj.1.1.1⟩ := by
    rintro X Y ⟨φ, hφ⟩ hx
    exact allClassesSmall_congr ⟨φ, hφ⟩ hx
  exact (FindsAtMultCost.cases
    (C := ((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
      fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩)
    (P := fun s Y => AllClassesSmall ⟨s, Y.1.1.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1.1.1⟩ W)
    hP (step_9_4_4 C₀ N) (h59 Ω N hrec)).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

/-! ### One turn of the procedure -/

/-- §9.4.  **One turn of Procedure Bipartite Split-or-Johnson.**  On the inputs of measure
exactly `N`, given the recursion on the inputs of smaller measure, the procedure finds the
outcome of Theorem 9.2.2.  It is the case distinction of steps 1, 2 and 3-9, glued by
`Babai.FindsAtMultCost.cases`; the three branches are `Babai.step_9_4_1`,
`Babai.step_9_4_2` and `Babai.steps_9_4_3_to_9`. -/
theorem procedure_9_4_turn :
    ∃ C₀ : ℕ, ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ),
      FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
          (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
          (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z) →
      FindsAtMultCost (BipBlockInputsAt Ω N) (SplitOutcomes Ω)
        (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
        (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z) := by
  obtain ⟨C₀, h39⟩ := steps_9_4_3_to_9
  refine ⟨C₀, fun Ω _ _ N hrec => ?_⟩
  -- the inner case distinction, inside `n₁ > C₀`: is `n₂ ≤ C₀ log n₁`?
  have hP₂ : ∀ {X Y : Pt ((BipBlockInputsAt Ω N).full
        fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩)},
      (((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).IsoP X Y).Nonempty
        → IsSmallPart₂ C₀ ⟨X.car, X.obj.1.1⟩ → IsSmallPart₂ C₀ ⟨Y.car, Y.obj.1.1⟩ := by
    rintro X Y ⟨φ, hφ⟩ hx
    have hiso : ((BipBlockInputs Ω).IsoP ⟨X.car, X.obj.1.1⟩ ⟨Y.car, Y.obj.1.1⟩).Nonempty :=
      ⟨φ, hφ⟩
    rw [IsSmallPart₂, ← BipBlockInputs.numBlocks_congr hiso,
      ← BipBlockInputs.n₁_congr hiso]
    exact hx
  have hinner := (FindsAtMultCost.cases
    (C := (BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩)
    (P := fun s Y => IsSmallPart₂ C₀ ⟨s, Y.1.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1.1⟩ W)
    hP₂ (step_9_4_2 C₀ N) (h39 Ω N hrec)).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  -- the outer case distinction: is `n₁ ≤ C₀`?
  have hP₁ : ∀ {X Y : Pt (BipBlockInputsAt Ω N)},
      ((BipBlockInputsAt Ω N).IsoP X Y).Nonempty →
        IsSmallPart₁ C₀ ⟨X.car, X.obj.1⟩ → IsSmallPart₁ C₀ ⟨Y.car, Y.obj.1⟩ := by
    rintro X Y ⟨φ, hφ⟩ hx
    have hiso : ((BipBlockInputs Ω).IsoP ⟨X.car, X.obj.1⟩ ⟨Y.car, Y.obj.1⟩).Nonempty :=
      ⟨φ, hφ⟩
    rw [IsSmallPart₁, ← BipBlockInputs.n₁_congr hiso]
    exact hx
  exact (FindsAtMultCost.cases
    (C := BipBlockInputsAt Ω N)
    (P := fun s Y => IsSmallPart₁ C₀ ⟨s, Y.1⟩)
    (costp := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1⟩)
    (costn := fun Z => cost_9_4 C₀ ⟨Z.car, Z.obj.1⟩)
    (Good := fun Z W => Good_9_2_2 ⟨Z.car, Z.obj.1⟩ W)
    hP₁ (step_9_4_1 C₀ N) hinner).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

/-! ### Theorem 9.2.2 in the wider category -/

/-- Theorem 9.2.2 (Bipartite Split-or-Johnson) **in the wider category**.  *"Let
`X = (V₁, V₂; E, f)` be a vertex-colored bipartite graph with `|V₁| ≥ 2` and let
`2/3 ≤ α < 1` be a threshold parameter.  Assume `|V₂| < α|V₁|`.  Assume moreover that the
symmetry defect of `X` on `V₁` is at least `1 - α`.  Then at quasipolynomial multiplicative
cost we can find either (a) a canonical colored `α`-partition of `V₁`, or (b) a canonically
embedded nontrivial Johnson scheme on a subset of `V₁` of size `≥ α|V₁|`.  (The time bounds
do not depend on `α`.)"*  (Version 2.5, lines 4019-4025.)

The only change is the category: a vertex of `V₂` is a block of points, `|V₂|` is the
number of blocks, and the hypotheses are read in the bipartite graph whose second part is
the set of blocks.  This is what the recursion of §9.4-§9.8 needs, because step 2(ii) of
Procedure ImprimitiveCase (§9.6) returns the contracted graph, whose vertices of the second
part are blocks.  See the module docstring of `Workspace/SplitOrJohnson/BipBlocks.lean` and
the entry for Lemma 9.6.1 in the corrected paper.

The printed Theorem 9.2.2 is the case of singleton blocks and follows along the
singleton-block embedding; see `Babai.theorem_9_2_2`.

The proof is the recursion of §9.5 (`Babai.FindsAtMultCost.strongInduction`) on the measure
`Babai.measure_9_5`, whose step is one turn of the procedure
(`Babai.procedure_9_4_turn`). -/
theorem theorem_9_2_2_blocks :
    ∃ q : ℕ → ℕ, RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
        FindsAtMultCost (BipBlockInputs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
          (fun X Z => IsSplitOutcome (BipBlockInputs.alpha X) (BipBlockInputs.V₁ X) Z) := by
  obtain ⟨C₀, hturn⟩ := procedure_9_4_turn
  refine ⟨costBound_9_4 C₀, quasiPolyBound_costBound_9_4 C₀, ?_⟩
  intro Ω _ _
  refine (FindsAtMultCost.strongInduction (C := BipBlockInputs Ω) (K := SplitOutcomes Ω)
    (cost := cost_9_4 C₀) (Good := Good_9_2_2)
    measure_9_5 (fun h => measure_9_5_congr h) (2 * Fintype.card Ω + 2)
    measure_9_5_lt (fun N hrec => hturn Ω N hrec)).mono
    (fun X => cost_9_4_le C₀ X) (fun _ _ h => h)


/-! ### Theorem 9.2.2 -/

/-- Theorem 9.2.2 (Bipartite Split-or-Johnson).  *"Let `X = (V₁, V₂; E, f)` be a
vertex-colored bipartite graph with `|V₁| ≥ 2` and let `2/3 ≤ α < 1` be a threshold
parameter.  Assume `|V₂| < α|V₁|`.  Assume moreover that the symmetry defect of `X` on
`V₁` is at least `1 - α`.  Then at quasipolynomial multiplicative cost we can find either
(a) a canonical colored `α`-partition of `V₁`, or (b) a canonically embedded nontrivial
Johnson scheme on a subset of `V₁` of size `≥ α|V₁|`.  (The time bounds do not depend on
`α`.)"*  (Version 2.5, lines 4019–4025.)

The hypotheses on `X` and on `α` are the defining conditions of the input category
`BipInputs Ω`, whose objects carry `α` as data; the conclusion is about `V₁`, so the set
to be split in `IsSplitOutcome` is `BipInputs.V₁ X` and the threshold is
`BipInputs.alpha X`.

*How the printed statement is recovered.*  Fixing `α` means passing to the full
subcategory `BipInputsAt Ω α` of the objects whose threshold is `α`; its morphisms are
exactly the isomorphisms of the underlying vertex-colored bipartite graphs, so it is the
category of the printed statement.  `Babai.FindsAtMultCost.full` restricts the reduction
to it, giving `Babai.theorem_9_2_2_at`, which is the printed statement verbatim.  The
parenthetical *"(The time bounds do not depend on `α`.)"* is the quantifier over `q`
standing outside, here automatically, since `q` does not see `α` at all.

*The cost function is absolute.*  The quantifier over `q` also stands outside the
quantifier over the ambient type `Ω`, so one and the same `q` serves every ground set.
Were `Ω` fixed first, a constant function of `|Ω|` would satisfy the bound and the
statement would say nothing about growth in `n`; see the entry on the absolute constants
in the corrected paper.

*How it is proved.*  The recursion of §9.4-§9.8 runs in the wider category
`Babai.BipBlockInputs`, in which a vertex of `V₂` is a block of points, because step 2(ii)
of Procedure ImprimitiveCase (§9.6) returns the contracted graph, whose second part is a
set of blocks (see `Workspace/SplitOrJohnson/BipBlocks.lean` and the entry for Lemma 9.6.1
in the corrected paper).  The printed statement is the case of singleton blocks, and follows
from `Babai.theorem_9_2_2_blocks` along the canonical embedding `Babai.bipToBlk`, which
keeps the underlying set, `α` and `V₁`. -/
theorem theorem_9_2_2 :
    ∃ q : ℕ → ℕ, RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
        FindsAtMultCost (BipInputs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
          (fun X Z => IsSplitOutcome (BipInputs.alpha X) (BipInputs.V₁ X) Z) := by
  obtain ⟨q, hq, h⟩ := theorem_9_2_2_blocks
  refine ⟨q, hq, ?_⟩
  intro Ω _ _
  -- `bipToBlk` keeps the underlying set, the threshold `α` and the first part `V₁`, so
  -- the cost bound and the property found are literally the same.
  exact (FindsAtMultCost.precomp bipToBlk bipToBlk_isCanonicalEmbedding (h Ω)).mono
    (fun _ => le_rfl) (fun _ _ hZ => hZ)

/-- Theorem 9.2.2, for a **fixed** threshold parameter `α`: the printed statement.  It is
`theorem_9_2_2` restricted to the full subcategory `BipInputsAt Ω α` of the inputs whose
threshold is `α` (`FindsAtMultCost.full`).  The hypotheses `2/3 ≤ α < 1` are part of the
input category, so they appear here only to make the statement match the printed one. -/
theorem theorem_9_2_2_at :
    ∃ q : ℕ → ℕ, RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (α : ℝ), 2 / 3 ≤ α → α < 1 →
        FindsAtMultCost (BipInputsAt Ω α) (SplitOutcomes Ω) (fun X => q X.car.ncard)
          (fun X Z => IsSplitOutcome α (BipInputs.V₁ ⟨X.car, X.obj.1⟩) Z) := by
  obtain ⟨q, hq, h⟩ := theorem_9_2_2
  refine ⟨q, hq, fun Ω _ _ α _ _ => ?_⟩
  refine ((h Ω).full (C := BipInputs Ω) fun _ X => X.1.2 = α).mono (fun _ => le_rfl) ?_
  intro X Z hZ
  have hα : BipInputs.alpha ⟨X.car, X.obj.1⟩ = α := X.obj.2
  rwa [hα] at hZ


end Babai
