/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 3: the Design Lemma applied to the neighborhood hypergraph
(Cases 3a and 3b).
-/
import Workspace.SplitOrJohnson.Step97Select
import Workspace.SplitOrJohnson.BlockDesignSkel

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Case 3a: the Design Lemma on the blocks

Case 3a is run on the fiber `{d' = N}` of the inputs of Case 3 (`Babai.Case3aFiber`), where
the arity of the Design Lemma is the constant `N`; the fibers are glued by
`Babai.FindsAtMultCost.ofFibers`.  On a fiber the run is the composition of two steps.

* **Step 1** (`Babai.blkDesign_step1`), *"Apply the Design lemma to `H`, viewed as a
  `d₁`-ary relational structure.  (Multiplicative cost `n₂^{d₁}`.)"*  The Design Lemma is a
  reduction over the ambient type `Set Ω`, where the blocks are points
  (`Babai.BlkCaseObj.blkAmb`); `Babai.NormalRed.comap` carries it back to `Ω`, and its
  category of versions is a category over `Ω` whose objects are *the input together with
  one version of the Design Lemma's answer on `V₂`*.
* **Step 2** (`Babai.blkDesign_step2`), the two sub-cases 3a1 and 3a2, which turn
  that answer into an outcome of §9.7.  Multiplicative cost `n₂²`.
-/

open BlkBlockDesignInputs in
/-- §9.7, Case 3a, step 1.  *"Apply the Design lemma to `H`, viewed as a `d₁`-ary
relational structure.  (Multiplicative cost `n₂^{d₁}`.)"*  (Version 2.5, lines 4277–4280.)

The Design Lemma is applied at the rank `N = d'` (`Babai.BlkCaseObj.d'`), to the
hypergraph on the blocks that `Babai.BlkDesignSetup.func` makes a functor of the input into
`Babai.DesignInputs (Set Ω) N (3/4)` — the admissible inputs of Theorem 8.1.2, whose three
hypotheses are checked in `Babai.BlkCaseObj.designObj` for Case 3a and in
`Babai.BlkCaseObj.skelDesignObj` for Case 3b.  What is found is one
*version* of the Design Lemma's answer, at the multiplicative cost of that answer, which is
`|V₂|^N = n₂^{d'}`.

The outcome category is the category of versions of `Babai.NormalRed.comap`, whose objects
carry the input as well; that is what lets step 2 use `V₁`, `α` and `n₂` of the input. -/
theorem blkDesign_step1 {N : ℕ} (S : BlkDesignSetup Ω N)
    (N' : NormalRed (DesignInputs (Set Ω) N (3 / 4)))
    (hcost : ∀ X : Pt (DesignInputs (Set Ω) N (3 / 4)),
      (N'.versions X).Finite ∧ (N'.versions X).ncard ≤ X.car.ncard ^ N) :
    FindsAtMultCost S.C (NormalRed.comap S.func N').D
      (fun X => numBlocks (S.bbdPt X) ^ N)
      (fun X Y => comapBBD Y = S.bbdPt X) := by
  refine FindsAtMultCost.of_normal (NormalRed.comap S.func N')
    (Func.id _) (Func.id_isCanonicalEmbedding _) (fun X => ?_) (fun X A hA => ?_)
  · obtain ⟨hfin, heq⟩ := NormalRed.ncard_versions_comap S.func N' X
      (hcost (S.func.obj X)).1
    refine ⟨hfin, ?_⟩
    rw [heq]
    have hle := (hcost (S.func.obj X)).2
    have hcar : (S.func.obj X).car.ncard = numBlocks (S.bbdPt X) :=
      (S.obj X).ncard_blkAmb
    rwa [hcar] at hle
  · obtain ⟨X₀, a⟩ := A
    have hX : X₀ = X.obj := hA
    subst hX
    rfl

open BlkBlockDesignInputs in
/-- §9.7, **Cases 3a1 and 3a2**, the two sub-cases of Case 3a.  (Version 2.5,
lines 4281–4294.)

*"Case 3a1.  The Design lemma returns a canonical colored `3/4`-partition of `V₂`.  Apply
Cor. ??.  Significant progress is made in time, polynomial in `n₁`, namely, `n₂` is reduced
to `≤ 3n₂/4`.  If a multiplicative cost of `m` is incurred, the progress is more
significant: `n₂` is reduced to `≤ n₂/m` (`2 ≤ m ≤ n₂/2`).*

*Case 3a2.  The Design lemma returns a UPCC `Y` canonically embedded on a subset `W ⊆ V₂`
with `|W| ≥ (3/4)n₂`.  Apply Reduce-Part2-by-Color to the partition `(W, V₂ ∖ W)`.  If the
procedure selects `V₂ ∖ W`, significant progress (`n₂` reduced to `≤ n₂/4`).  If it selects
`W`, go to Sec. 9.8.  Let `U ⊆ V₂` be the part selected, and `(X₂)_new` the homogeneous
coherent configuration obtained on `U`.  If `(X₂)_new` is a UPCC, exit, significant
progress.  If `(X₂)_new` is not a UPCC, i. e., it has rank 2, then `U` was a clique in `Y`
and therefore `|U| ≤ |W|/2 ≤ n₂/2` by Prop. 2.4.11, a significant reduction of `|V₂|."*

The hypothesis is the conclusion of the Design Lemma at a version: `G'` is the canonical
embedding that reads the answer off a version, and `hgood` says that the answer is an
outcome of Theorem 8.1.2 for the threshold `3/4` on `V₂` — *"a canonical colored
`3/4`-partition of `V₂`"* (first summand of `Babai.DesignOutcomes`) or *"a UPCC canonically
embedded on a subset `W ⊆ V₂` with `|W| ≥ (3/4)n₂`"* (second summand).  The statement is
made for an arbitrary normalized form `N'` of the Design Lemma, which is what step 1
produces.

The cost `n₂²` is one call of Procedure Reduce-Part2-by-Color (cost `n₂`, Case 3a2 and,
through Cor. 3.4.10 of the original's fill, Case 3a1) and one call of §9.8 (cost `n₂`,
*"If it selects `W`, go to Sec. 9.8"*).

**Proved.**  The proof is one call of the common exit of §9.7,
`Babai.findsAtMultCost_restrictHint` (`Workspace/SplitOrJohnson/BlkExit.lean`), at the
selected part `Babai.designSel` and the hint `Babai.designHint`
(`Workspace/SplitOrJohnson/Step97Select.lean`).  The mathematics of the two sub-cases is
`Babai.case_9_7_3a1` and `Babai.case_9_7_3a2` (`Workspace/SplitOrJohnson/BlockDesign.lean`).

*What the exit is applied to* (`Workspace/SplitOrJohnson/BlkRestrict.lean`).  The exit
*"significant progress: `n₂` is reduced"* is built once, for all three branches of §9.7
that take it:

* `Babai.BlkCaseObj.blkFam` reads a set of blocks back off the ambient type `Set Ω` — the
  carrier of the UPCC of Case 3a2, or a color class of the colored `3/4`-partition of
  Case 3a1, is a subset of `Babai.BlkCaseObj.blkAmb` — as a sub-family of
  `Babai.BlkCaseObj.blocks`, with `Babai.BlkCaseObj.ncard_blkFam` and
  `Babai.BlkCaseObj.blkFam_union_cover` for the pair `(W, V₂ ∖ W)`;
* `Babai.BlkCaseObj.linkGraph` is the bipartite graph `X = (V₁, V₂; Rᵢ)` of §9.7 as an
  object of `Babai.VColBipBlk`, with `Babai.BlkCaseObj.linkGraph_noTwins` (*"no twins in
  `V₁`"*, through `Babai.BlkCaseObj.nbhd_injective`);
* `Babai.reducePart2ByColorBlk` and `Babai.reducePart2ByColorBlk_spec` are Procedure
  Reduce-Part2-by-Color and Lemma 9.3.2 for that graph;
* `Babai.restrictObj`, `Babai.restrictObj_pred` and `Babai.good97_restrict` turn the
  selected part `U` into an object of `Babai.BipBlockInputs` and, when `10|U| ≤ 9n₂`, into
  an outcome `Babai.Good97`.

*The exits that re-enter §9.6 or §9.8 now have an outcome.*  Of the four sub-branches of
Case 3a, the two that reduce `n₂` on the spot are closed by `Babai.good97_restrict` (or by
`Babai.good97_restrict_hint_small`): Case 3a2 with `V₂ ∖ W` selected, where `|U| ≤ n₂/4`,
and Case 3a1 with a selected class of at most `3n₂/4` blocks.  The other two —
*"apply Procedure ImprimitiveCase"* (Case 3a1, selected class larger than `3n₂/4`) and
*"go to Sec. 9.8"* (Case 3a2, `W` selected) — **return the restricted instance with the
hint set**, which is the third kind of major progress of §9.5, *"`X₂` moves from clique to
UPCC while `n₂` does not increase"*.  Entries 88 and 94 of the corrected paper the
repair; what it needs is now built:

* `Babai.VColBipBlk.restrictBlkHint`, `Babai.restrictObjHint`,
  `Babai.restrictObjHint_pred`, `Babai.restrictOutcomeHint`, `Babai.good97_restrict_hint`
  and `Babai.good97_restrict_hint_small`
  (`Workspace/SplitOrJohnson/BlkRestrictHint.lean`): the restriction to a sub-family `U`
  of the blocks with a given coloring `c` of the ordered pairs of blocks of `U` attached
  as the hint.  It is an admissible input of Theorem 9.2.2 under exactly the hypotheses of
  `Babai.restrictObj_pred`, because the symmetry defect of `V₁` does not see the hint
  (`Babai.VColBipBlk.symDefect₁_congr`); it is canonical when `c` is
  (`Babai.VColBipBlk.restrictBlkHint_isIsoTo`); and it has `|U|` blocks.
* The two constructors of the hint (`Workspace/SplitOrJohnson/HintBuild.lean`).  Case 3a2:
  a UPCC is homogeneous of rank `≥ 3`
  (`Babai.PartitionStructure.isHomogeneous_and_rank_of_isUniprimitive`).  Cases 3a1 and
  3b: `Babai.eqvConfig`, the rank-`3` homogeneous coherent configuration of a partition
  into classes of one common size `≥ 2`, with at least two classes
  (`Babai.eqvConfig_isCoherent`, `Babai.eqvConfig_isHomogeneous`).  Either of them is a
  hint through `Babai.hintColoring` and
  `Babai.VColBipBlk.hasHint_restrictBlkHint`.  The hint is not vacuous:
  `Babai.HintExample.X_hasHint` is an object with four blocks in two pairs.
* `Babai.colorSplit` (`Workspace/SplitOrJohnson/ColorSplit.lean`): **which two parts
  Procedure Reduce-Part2-by-Color is applied to in Case 3a1**, where what the Design Lemma
  hands over is a coloring of `V₂` with any number of classes and the procedure takes only
  two parts.  The first part is the class of the least color whose class is at least a
  quarter of the blocks, if there is one, and otherwise the union of the classes of the
  colors up to the least `k` that makes that union a quarter.  Then the second part is at
  most `3n₂/4` (`Babai.four_mul_ncard_compl_colorSplit_le`) and the first part is at most
  `3n₂/4` or is a single color class (`Babai.colorSplit_alternative`) — which is exactly
  what the original's sentence *"if color class selected is greater than `3n₂/4`, this
  color class is equipartitioned"* presupposes.  The choice is canonical
  (`Babai.colorSplit_image`), because it names the part by color values only.

*The bookkeeping that glues these together* is
`Workspace/SplitOrJohnson/Step97Design.lean` and
`Workspace/SplitOrJohnson/Step97Select.lean`:

1. (`Workspace/SplitOrJohnson/Step97Design.lean`): reading the Design Lemma's
   answer off a version is `Babai.designAnswer`, with
   `Babai.designAnswer_isDesignOutcome`; a morphism of
   `(NormalRed.comap S.func N').D` becomes a morphism of `N'.D`
   (`Babai.comapVerHom`) whose underlying map is `Babai.BlkCaseObj.blkAmbEquiv`, and
   `hG'.map_restrict` then gives `Babai.mem_designAnswer_image`;
2. for the carrier: `Babai.blkFam_designAnswer_image` and
   `Babai.blkFam_compl_designAnswer_image` are the hypothesis `hU` of
   `Babai.VColBipBlk.restrictBlk_isIsoTo` and
   `Babai.VColBipBlk.restrictBlkHint_isIsoTo` for the two parts `(W, V₂ ∖ W)`; the same
   for the *coloring* carried on the answer — the UPCC coloring of Case 3a2 and the
   colored partition of Case 3a1 — is `Babai.designHint_image`, and for the part handed
   to Procedure Reduce-Part2-by-Color `Babai.designFirst_image` and
   `Babai.designSel_image`;
3. in Case 3a1, the refinement of Prop. 7.1.3
   (`Babai.ColoredPartition.equipartRefine`), which makes the returned colored
   `3/4`-partition an **equipartition** with the same blocks
   (`Babai.ColoredPartition.block_equipartRefine`), so that the blocks inside the selected
   class have one common size — the hypothesis `hm` of `Babai.eqvConfig`; that the size is
   `≥ 2` is admissibility (Def. 7.1.1) and that there are at least two classes is
   `ρ(Π) ≤ (3/4)n₂ < |C|`.  This is `Babai.hasHint_designSel_eqv`, and Case 3a2's hint is
   `Babai.hasHint_designSel_upcc`.  The choice between the two kinds of progress is
   `Babai.designSel_prog`.

The cost `n₂²` stays; it is an upper bound.  It was meant to pay for the calls of §9.6 and
§9.8 made inside this step, and those calls now happen in the **next** turn of the
recursion, which the hint bit of `Babai.measure_9_5` pays for (entry 94 of
the corrected paper). -/
theorem blkDesign_step2 {N : ℕ} (S : BlkDesignSetup Ω N)
    (N' : NormalRed (DesignInputs (Set Ω) N (3 / 4)))
    (G' : Func N'.D (DesignOutcomes (Set Ω))) (hG' : G'.IsCanonicalEmbedding)
    (hgood : ∀ (X : Pt (DesignInputs (Set Ω) N (3 / 4))) (A : N'.D.Obj X.car),
      N'.base A = X.obj → IsDesignOutcome (3 / 4) X.car (G'.obj ⟨X.car, A⟩)) :
    FindsAtMultCost (NormalRed.comap S.func N').D (Out97 Ω)
      (fun Y => numBlocks (comapBBD Y) ^ 2)
      (fun Y Z => Good97 (comapBBD Y) Z) := by
  classical
  refine findsAtMultCost_restrictHint (C := (NormalRed.comap S.func N').D)
    (bbd := fun Y => (comapBBD Y).obj)
    (Sel := fun Y => designSel G' Y) (Hint := fun Y => designHint G' Y)
    (fun {Y Z f} hf => S.hbbd hf.choose) (fun Y => designSel_subset G' Y)
    (fun Y => S.n₂_lt_n₁ (comapFib Y)) (fun Y => designSel_symDefect Y)
    (fun {Y Z f} hf B => designSel_image hG' ⟨f, hf⟩ B)
    (fun {Y Z f} hf A B hA hB => designHint_image hG' ⟨f, hf⟩ hA.1 hB.1)
    (fun Y => designSel_prog hG' hgood Y) _ (fun Y => ?_)
  exact Nat.one_le_pow _ _ (one_le_numBlocks (comapBBD Y))

open BlkBlockDesignInputs in
/-- §9.7, Case 3 on a fiber of the rank: step 1 composed with step 2.  The cost is
`n₂^N · n₂² = n₂^{N+2}`. -/
theorem blkDesign_fiber {N : ℕ} (S : BlkDesignSetup Ω N) :
    FindsAtMultCost S.C (Out97 Ω)
      (fun X => numBlocks (S.bbdPt X) ^ (N + 2))
      (fun X Z => Good97 (S.bbdPt X) Z) := by
  obtain ⟨N', G', hG'emb, hcost, hgood⟩ :=
    (designLemma_finds_designInputs (Ω := Set Ω) (k := N) (α := 3 / 4)
      (by norm_num) (by norm_num)).exists_normal
  have h1 := blkDesign_step1 S N' hcost
  have h2 := blkDesign_step2 S N' G' hG'emb hgood
  have hcomp := h1.comp h2 (fun X Y hXY => by rw [hXY])
  refine hcomp.mono (fun X => ?_) (fun X Z => ?_)
  · rw [← pow_add]
  · rintro ⟨Y, hY, hg⟩
    rwa [hY] at hg

open BlkBlockDesignInputs in
/-- §9.7, Case 3a on the fiber `{d' = N}`: step 1 composed with step 2.  The cost is
`n₂^N · n₂² = n₂^{d'+2}`. -/
theorem case_9_7_case3a_fiber (N : ℕ) :
    FindsAtMultCost (Case3aFiber Ω N) (Out97 Ω)
      (fun X => numBlocks (Case3aFiber.bbd X) ^ ((Case3aFiber.obj X).d' + 2))
      (fun X Z => Good97 (Case3aFiber.bbd X) Z) :=
  (blkDesign_fiber (case3aSetup Ω N)).mono
    (fun X => by rw [Case3aFiber.d'_eq X]; exact le_rfl) (fun _ _ h => h)

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open BlkBlockDesignInputs in
/-- Case 3a of §9.7.  *"`d₁ ≤ (7/3) log₂ n₁`.  Apply the Design lemma to `H`, viewed as a
`d₁`-ary relational structure.  (Multiplicative cost `n₂^{d₁} < n₂^{(7/3)log₂ n₁}`.)"*,
with its two sub-cases 3a1 and 3a2.  (Version 2.5, lines 4276–4294.)

The cost is `n₂^{d₁}` for the Design Lemma call, times `n₂` for Procedure
Reduce-Part2-by-Color and `n₂` for the call of §9.8 in Case 3a2.

**Proved.**  The proof is

* `Babai.FindsAtMultCost.ofFibers` for the invariant `d'`, which is an isomorphism
  invariant (`Babai.BlkCaseObj.IsMorphOn.d'_eq`) and bounded by `|Ω|` because the blocks
  are non-empty and pairwise disjoint (`Babai.BlkCaseObj.n₂_le_card`).  On the fiber
  `{d' = N}` (`Babai.Case3aFiber`) the arity of the Design Lemma is the constant `N`,
  which is what the fixed-arity statement of Theorem 8.1.2 needs;
* on a fiber, `Babai.case_9_7_case3a_fiber`: step 1
  (`Babai.case_9_7_case3a_step1`, the Design Lemma call, cost `n₂^{d'}`) composed with
  step 2 (the two sub-cases, cost `n₂²`) by `Babai.FindsAtMultCost.comp`.

**The transfer of the Design Lemma to the blocks** is
`Workspace/SplitOrJohnson/BlockDesignHyper.lean`.  `Babai.designLemma_finds_designInputs`
is a reduction over the ambient type `Set Ω`, where a block is a **point**
(`Babai.BlkCaseObj.blkAmb`); `Babai.NormalRed.comap` (`Workspace/Functors/Ambient.lean`)
pulls it back along the functor `Babai.BlkDesignSetup.func`, which in Case 3a assigns to an input of §9.7 the
neighborhood hypergraph `H` read as a `d'`-ary relational structure
(`Babai.BlkCaseObj.nbhdStruct`).  The three hypotheses of Theorem 8.1.2 are checked in
`Babai.BlkCaseObj.designObj`:

* *"`2 ≤ k`"* and *"`k ≤ n/2`"* at the rank `d' = min(d₁, n₂ − d₁)`
  (`Babai.BlkCaseObj.two_le_d'`, `Babai.BlkCaseObj.two_mul_d'_le_n₂`).  §9.7 checks
  neither, and `d₁` itself need not satisfy the second; `H` is therefore complemented when
  `d₁ > n₂/2`, which changes neither the automorphism group nor the twins nor the defect
  (`Babai.Hypergraph.compl`, `Babai.Hypergraph.aut_compl`).  See the entry *"§9.7 Case 3:
  the Design Lemma is applied at rank `d₁` without checking `d₁ ≤ n₂/2`"* in
  the corrected paper;
* *"symmetry defect `≥ 1 − α`"*, here `≥ 1/4`, is Case 3 itself, *"the relative symmetry
  defect of `H` is `≥ 1/2`"*: `Babai.BlkCaseObj.IsHTwin` is the twin relation of `Aut(H)`
  (`Babai.BlkCaseObj.twinOrEq_iff_isHTwin`), so the negation of Case 2 bounds every twin
  equivalence class of `Aut(H)` by `n₂/2`, and `Babai.defect_ge_of_twinClass_ncard_le`
  (Obs. 2.3.12) turns that into the defect bound
  (`Babai.BlkCaseObj.defect_nbhdHg_ge`).

`Babai.BlkDesignSetup.func` is a `Babai.Func.IsBlockFunc`
(`Babai.BlkDesignSetup.func_isBlockFunc`): a
morphism acts on the assigned object by `B ↦ f(B)`, which is what makes the way back of
`Babai.FindsAtMultCost.of_comap` available to step 2.

*Note on the transfer, for whoever wrote the first version of this note.*  The obvious
route — apply
`Babai.designLemma_finds` with the ambient type `Set Ω`, so that `H` is an honest `d₁`-ary
structure on `blocks ⊆ Set Ω`, and transfer the resulting `Babai.FindsAtMultCost` back
along the assignment "block `B` ↦ `φ '' B`" — does **not** go through as a change of
ambient type alone.  `Babai.FindsAtMultCost C H cost Good` quantifies over a category
`D : Cat.{0,0} Ω` of tuples **over the same ambient type `Ω` as `C`**, and the objects of
the tuple category produced over `Set Ω` live on subsets of `Set Ω`; they cannot be read as
objects over `Ω`.  So a transfer lemma has to rebuild the reduction rather than reuse it:
the workable shape is a `Babai.NormalRed` of the source category whose extra datum at `X`
is a member of the tuple of the `Set Ω`-reduction at the assigned object (this is a type
over `X.car`, so it is legal).  This is what `Babai.NormalRed.comap` does, and step 1 uses
it with the category of versions itself as the intermediate outcome category, so that the
input is still available to step 2. -/
theorem case_9_7_case3a :
    FindsAtMultCost
      ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
        (fun s X => ¬ Case2P s X.1)).full (fun s X => Case3aP s X.1.1)) (Out97 Ω)
      (fun X => BlkBlockDesignInputs.numBlocks ⟨X.car, X.obj.1.1.1⟩ ^
        ((obj₀ ⟨X.car, X.obj.1.1.1⟩).d' + 2))
      (fun X Z => Good97 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  refine FindsAtMultCost.ofFibers
    (C := (((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
      (fun s X => ¬ Case2P s X.1)).full (fun s X => Case3aP s X.1.1))
    (fun X => (obj₀ ⟨X.car, X.obj.1.1.1⟩).d')
    (fun {X Y} h => ?_) (Fintype.card Ω) (fun X => ?_) (fun N => case_9_7_case3a_fiber N)
  · obtain ⟨φ, hφ⟩ := h
    exact ((isMorphOn_of_iso (X := ⟨X.car, X.obj.1.1.1⟩)
      (Y := ⟨Y.car, Y.obj.1.1.1⟩) hφ).d'_eq).symm
  · exact le_trans (le_trans (BlkCaseObj.d'_le_d₁ _) (BlkCaseObj.d₁_le_numBlocks _))
      (BlkCaseObj.n₂_le_card _)

open BlkBlockDesignInputs in
/-- Case 3b of §9.7.  *"`d₁ > 7/3 log₂ n₁`.  Let `t = ⌈(7/4) log₂ n₁⌉`.  So `t ≤ (3/4)d₁`.
By Lemma 2.5.12, the symmetry defect of the `t`-skeleton `H^{(t)}` of `H` is greater than
`1/4`.  Let us apply the Design lemma to `H^{(t)}`.  If the result is a `3/4`-partition of
`V₂`, ********* an application of Reduce-Part2-by-Color and if necessary, an application of
the imprimitive case.  Else (the result is a UPCC on a subset of `V₂` of size `≥ (3/4)n₂`
(significant progress, exit)."*  (Version 2.5, lines 4295–4301.)

The `*****` is filled from version 2.5's own words (entry 37 of the corrected paper); the
original exits on the partition instead, and version 2.5 governs.  The printed
`t ≤ (3/4)d₁` is false for a positive fraction of the `n₁` and is relaxed to
`t ≤ ⌈(3/4)d₁⌉` (entry 42 of the corrected paper, `Babai.case_9_7_3b_t_le`), which is what
`Babai.Hypergraph.skeleton_defect` (Lemma 2.5.12) needs.

The branch condition is the negation of `Babai.BlkCaseObj.IsCase3a`, which is now read on
`d' = min(d₁, n₂ − d₁)` rather than on `d₁` (see the docstring of
`Babai.BlkCaseObj.d'`).  So here `d' > (7/3) log₂ n₁`, the `t`-skeleton is taken of the
`d'`-uniform hypergraph (`H` or its bipartite complement), and `2t ≤ (3/2)d' ≤ n₂` by
`Babai.BlkCaseObj.two_mul_d'_le_n₂`, which is the hypothesis `k ≤ n/2` of
Theorem 8.1.2.

The cost is `n₂^t` for the Design Lemma call on the `t`-skeleton, times `n₂` for
Reduce-Part2-by-Color and `n₂` for Procedure ImprimitiveCase (§9.6, `Babai.lemma_9_6_1`).

**Proved.**  Case 3b is Case 3a with one hypergraph exchanged for another, so it runs on
the **same** machinery: `Babai.BlkDesignSetup` is the data of a Design Lemma call on the
blocks — the category of inputs, the object of §9.7 under an input, and the `N`-ary
relational structure on the blocks that the Design Lemma is applied to — and
`Babai.blkDesign_fiber` (`Babai.blkDesign_step1` composed with `Babai.blkDesign_step2`)
runs the call and the exit for an arbitrary such setup.  Case 3a instantiates it with `H`
itself at the rank `d'` (`Babai.case3aSetup`), Case 3b with the `t`-skeleton of `H` at the
rank `t` (`Babai.case3bSetup`).  So Case 3b's two exits are Case 3a's, through
`Babai.designSel`, `Babai.designHint` and `Babai.findsAtMultCost_restrictHint`; see the
docstring of `Babai.case_9_7_case3a_step2` for the pieces.

The *input* of the call is built in `Workspace/SplitOrJohnson/BlockDesignSkel.lean`:

* `Babai.BlkCaseObj.tSkel` is `t = ⌈(7/4) log₂ n₁⌉`, with the two bounds the branch needs,
  `Babai.BlkCaseObj.tSkel_le_ceil_d'` (*"`t ≤ (3/4)d₁`"*, at the rank `d'` and with the
  ceiling of entry 42 of the corrected paper) and `Babai.BlkCaseObj.tSkel_lt`;
* `Babai.BlkCaseObj.skeleton_defect_nbhdHg` is Lemma 2.5.12 at the input, *"the symmetry
  defect of the `t`-skeleton `H^{(t)}` of `H` is greater than `1/4`"*.  Lemma 2.5.12 asks
  for a **nontrivial regular** hypergraph, neither of which §9.7 checks:
  `Babai.BlkCaseObj.nbhdHg_not_trivialUniform` reads nontriviality off the negation of
  Case 1 (a trivial uniform hypergraph has `Aut(H) = S(V₂)`, which is Case 1), and
  `Babai.BlkCaseObj.nbhdHg_isRegular` is the semiregularity of the link — the degree of a
  block in `H` is its in-degree in the constituent `Babai.BlkCaseObj.linkColor`, which by
  Obs. 3.3.5 (`Babai.BipCaseData.ncard_inNbhd_eq`) depends only on the vertex color;
* `Babai.BlkCaseObj.skelDesignObj` is the `t`-skeleton as an **admissible input of
  Theorem 8.1.2** at the rank `t` and the threshold `3/4`;
* `Babai.BlkCaseObj.map_skelStruct` makes it a **functor** of the input: the hyperedges of
  the skeleton correspond under `Babai.BlkCaseObj.blkAmbEquiv` because the hyperedges of
  `H` do (`Babai.BlkCaseObj.nbhdHg_edgeSet_image`) and a `t`-set lies inside a hyperedge
  exactly if its image does (`Babai.Hypergraph.mem_skeleton_edgeSet_image`).

The fibering is over `t`, which is an isomorphism invariant because `n₁` is
(`Babai.BlkCaseObj.IsMorphOn.tSkel_eq`) and is bounded by `|Ω|` because `2t ≤ n₂ ≤ |Ω|`
(`Babai.BlkCaseObj.two_mul_tSkel_le_n₂`, `Babai.BlkCaseObj.n₂_le_card`). -/
theorem case_9_7_case3b :
    FindsAtMultCost
      ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
        (fun s X => ¬ Case2P s X.1)).full (fun s X => ¬ Case3aP s X.1.1)) (Out97 Ω)
      (fun X => BlkBlockDesignInputs.numBlocks ⟨X.car, X.obj.1.1.1⟩ ^
        (⌈7 / 4 * Real.logb 2 ((obj₀ ⟨X.car, X.obj.1.1.1⟩).n₁ : ℝ)⌉₊ + 2))
      (fun X Z => Good97 ⟨X.car, X.obj.1.1.1⟩ Z) := by
  refine FindsAtMultCost.ofFibers
    (C := (((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
      (fun s X => ¬ Case2P s X.1)).full (fun s X => ¬ Case3aP s X.1.1))
    (fun X => (obj₀ ⟨X.car, X.obj.1.1.1⟩).tSkel)
    (fun {X Y} h => ?_) (Fintype.card Ω) (fun X => ?_)
    (fun N => (blkDesign_fiber (case3bSetup Ω N)).mono (fun X => ?_) (fun _ _ h => h))
  · obtain ⟨φ, hφ⟩ := h
    exact ((isMorphOn_of_iso (X := ⟨X.car, X.obj.1.1.1⟩)
      (Y := ⟨Y.car, Y.obj.1.1.1⟩) hφ).tSkel_eq).symm
  · have hlt : (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).n₂
        < (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).n₁ :=
      numBlocks_lt_n₁ ⟨X.car, X.obj.1.1.1⟩
    have h2 := (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).two_mul_tSkel_le_n₂
      hlt X.obj.2
    have h3 := BlkCaseObj.n₂_le_card
      (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω)))
    show (obj₀ (⟨X.car, X.obj.1.1.1⟩ : Pt (BlkBlockDesignInputs Ω))).tSkel ≤ Fintype.card Ω
    omega
  · show numBlocks ((case3bSetup Ω N).bbdPt X) ^ (N + 2)
      ≤ numBlocks ((case3bSetup Ω N).bbdPt X) ^ ((Case3bFiber.obj X).tSkel + 2)
    rw [Case3bFiber.tSkel_eq X]


end Babai
