/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: the common exit of Cases 2, 3a1, 3a2 and 3b — the input restricted to the
part that Procedure Reduce-Part2-by-Color selects, with the hint attached.
-/
import Workspace.SplitOrJohnson.BlkRestrictHint
import Workspace.SplitOrJohnson.BlkSymIso

/-!
# §9.7  The common exit

Version 2.5, lines 4252-4301.

Three of the four branches of §9.7 end in the same way: a canonical sub-family `U` of the
blocks is selected, a structure found on it is attached as the hint, and the restricted
input `X[V₁, U]` is handed back.  `Babai.restrictObjHint` and
`Babai.good97_restrict_hint` build that object and prove it an outcome
(`Workspace/SplitOrJohnson/BlkRestrictHint.lean`).  What is left is the bookkeeping of a
reduction: one outcome per input, carried onto the outcome at the other object by every
isomorphism.  `Babai.findsAtMultCost_restrictHint` does that bookkeeping once, for every
branch that ends this way.

| Paper | Lean |
|---|---|
| the outcome as an object on a subset of `□X` | `Babai.restrictOutcomeSub` |
| *"significant progress"* / *"`X₂` moves from clique to UPCC"*, as a reduction | `Babai.findsAtMultCost_restrictHint` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open BlkBlockDesignInputs in
/-- §9.7.  The outcome of the common exit, as an object of `Babai.Out97` **on a subset of
`□X`** — here on `□X` itself, since the restriction keeps the whole point set.  This is
`Babai.restrictOutcomeHint` in the form `Babai.FindsAtMultCost.of_outcomes_sub`
consumes. -/
noncomputable def restrictOutcomeSub (X : Pt (BlkBlockDesignInputs Ω))
    {U : Set (Set ↥X.car)} (c : Set ↥X.car → Set ↥X.car → ℕ)
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨X.car, subset_rfl⟩,
    Sum.inr ⟨restrictObjHint X U c, restrictObjHint_pred X c hU h3 hdef⟩⟩

open BlkBlockDesignInputs in
/-- §9.7.  **The common exit of Cases 2, 3a1, 3a2 and 3b, as a reduction.**

The data are: a category `C` of inputs, each carrying an input of §9.7 (`bbd`) whose
isomorphisms are the isomorphisms of `C` (`hbbd`); a canonical sub-family `Sel Y` of the
blocks (`hSelIso`), which is what Procedure Reduce-Part2-by-Color selects; and a canonical
coloring `Hint Y` of the ordered pairs of the kept blocks (`hHintIso`), which is the
structure found on `Sel Y`.

The conclusion is the reduction that returns the restricted input `X[V₁, Sel Y]` with the
hint.  It is an outcome of §9.7 (`Babai.IsBlkDesignOutcome`) by `hprog`, which is the
disjunction of the two remaining kinds of major progress of §9.5: *"`n₂` is significantly
reduced"* (`10|U| ≤ 9n₂`) or *"`X₂` moves from clique to UPCC while `n₂` does not
increase"* (`|U| ≤ n₂` and the hint).

There is one outcome, so any cost `≥ 1` pays for it. -/
theorem findsAtMultCost_restrictHint {C : Cat.{0, 0} Ω}
    (bbd : ∀ Y : Pt C, (BlkBlockDesignInputs Ω).Obj Y.car)
    (Sel : ∀ Y : Pt C, Set (Set ↥Y.car))
    (Hint : ∀ Y : Pt C, Set ↥Y.car → Set ↥Y.car → ℕ)
    (hbbd : ∀ {Y Z : Pt C} {f : ↥Y.car ≃ ↥Z.car}, f ∈ C.IsoP Y Z →
      f ∈ (BlkBlockDesignInputs Ω).IsoP ⟨Y.car, bbd Y⟩ ⟨Z.car, bbd Z⟩)
    (hSub : ∀ Y : Pt C, Sel Y ⊆ (obj₀ ⟨Y.car, bbd Y⟩).blocks)
    (hn : ∀ Y : Pt C, (obj₀ ⟨Y.car, bbd Y⟩).n₂ < (obj₀ ⟨Y.car, bbd Y⟩).n₁)
    (hdef : ∀ Y : Pt C,
      letI : Fintype ↥Y.car := Fintype.ofFinite _
      letI : DecidableEq ↥Y.car := Classical.decEq _
      (((obj₀ ⟨Y.car, bbd Y⟩).n₁ : ℚ) - 1) / 2 ≤
        ((obj₀ ⟨Y.car, bbd Y⟩).linkGraph.restrictBlk (Sel Y)).symDefect₁)
    (hSelIso : ∀ {Y Z : Pt C} {f : ↥Y.car ≃ ↥Z.car}, f ∈ C.IsoP Y Z →
      ∀ B : Set ↥Y.car, f '' B ∈ Sel Z ↔ B ∈ Sel Y)
    (hHintIso : ∀ {Y Z : Pt C} {f : ↥Y.car ≃ ↥Z.car}, f ∈ C.IsoP Y Z →
      ∀ A B : Set ↥Y.car, A ∈ (obj₀ ⟨Y.car, bbd Y⟩).blocks ∩ Sel Y →
        B ∈ (obj₀ ⟨Y.car, bbd Y⟩).blocks ∩ Sel Y →
        Hint Z (f '' A) (f '' B) = Hint Y A B)
    (hprog : ∀ Y : Pt C,
      letI : Fintype ↥Y.car := Fintype.ofFinite _
      letI : DecidableEq ↥Y.car := Classical.decEq _
      10 * (Sel Y).ncard ≤ 9 * numBlocks ⟨Y.car, bbd Y⟩ ∨
        ((Sel Y).ncard ≤ numBlocks ⟨Y.car, bbd Y⟩ ∧
          ((obj₀ ⟨Y.car, bbd Y⟩).linkGraph.restrictBlkHint (Sel Y) (Hint Y)).HasHint))
    (cost : Pt C → ℕ) (hcost : ∀ Y : Pt C, 1 ≤ cost Y) :
    FindsAtMultCost C (Out97 Ω) cost (fun Y Z => Good97 ⟨Y.car, bbd Y⟩ Z) := by
  classical
  have h3 : ∀ Y : Pt C, 3 ≤ (obj₀ ⟨Y.car, bbd Y⟩).n₁ := fun Y => by
    have := BlkCaseObj.five_le_n₁ (obj₀ ⟨Y.car, bbd Y⟩) (hn Y)
    omega
  refine FindsAtMultCost.of_outcomes_sub
    (fun Y => {restrictOutcomeSub ⟨Y.car, bbd Y⟩ (Hint Y) (hSub Y) (h3 Y) (hdef Y)})
    (fun Y => ⟨_, rfl⟩) (fun Y => Set.finite_singleton _) (fun Y => ?_)
    (fun {Y Z f} hf W hW => ?_) (fun Y W hW => ?_)
  · rw [Set.ncard_singleton]; exact hcost Y
  · -- the restricted input with the hint is carried onto the restricted input with the
    -- hint: the sub-family and the hint are both canonical
    rw [Set.mem_singleton_iff] at hW
    subst hW
    refine ⟨restrictOutcomeSub ⟨Z.car, bbd Z⟩ (Hint Z) (hSub Z) (h3 Z) (hdef Z), rfl, ?_⟩
    refine ⟨f, fun x => rfl, ?_, ?_⟩
    · exact (hbbd hf).1
    · have hm : (obj₀ (⟨Y.car, bbd Y⟩ : Pt (BlkBlockDesignInputs Ω))).IsMorphOn
          (obj₀ (⟨Z.car, bbd Z⟩ : Pt (BlkBlockDesignInputs Ω))) f :=
        isMorphOn_of_iso (hbbd hf)
      exact VColBipBlk.restrictBlkHint_isIsoTo (BlkCaseObj.linkGraph_isIsoTo hm)
        (hSelIso hf) (hHintIso hf)
  · -- the two remaining kinds of major progress of §9.5
    rw [Set.mem_singleton_iff] at hW
    subst hW
    rcases hprog Y with hsmall | ⟨hle, hhint⟩
    · exact good97_restrict_hint_small ⟨Y.car, bbd Y⟩ (Hint Y) (hSub Y) (h3 Y) (hdef Y)
        hsmall
    · exact good97_restrict_hint ⟨Y.car, bbd Y⟩ (Hint Y) (hSub Y) (h3 Y) (hdef Y) hle
        hhint

end Babai
