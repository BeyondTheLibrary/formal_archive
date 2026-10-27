/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 9(ii): the block design case, and the pass that starts from a hinted
instance.
-/
import Workspace.SplitOrJohnson.BlockDesignAssemble
import Workspace.SplitOrJohnson.Step9Hint

/-!
# §9.4, step 9(ii): the branch of §9.7

Version 2.5, lines 4166–4172 (§9.4, step 9), 4176–4181 (§9.5) and 4281–4294 (§9.7,
Case 3a2).

The branch splits once more, on whether the **input of the pass** carries the hint
(`Babai.HasHintAt`).  The split is into full subcategories, because the hint is an
isomorphism invariant (`Babai.hasHintAt_congr`).

* **The input carries the hint.**  §9.7 is not called.  The pass has already made the
  progress that §9.5 asks for: the blocks that step 8 leaves form a clique of the hint, so
  there are at most `n₂/2` of them (`Babai.two_mul_step8NumBlocks_le_of_hint`, the argument
  of Case 3a2), and the instance step 8 leaves is an admissible input of Theorem 9.2.2 for
  the threshold `α_new` of step 5 (`Babai.step8Obj_isThm922Input`).  So the recursion is
  called on it directly.
* **The input has no hint.**  §9.7 is called (`Babai.case_9_7`, through
  `Babai.step9DesignFunc`).  Its outcome is a solution for `(α_new, W₁)`, or an instance
  with `10 n₂' ≤ 9 n₂`, or an instance with `n₂' ≤ n₂` that carries the hint.  In the last
  two the recursion is called on the instance, and the input bit `1` pays for the turn
  (`Babai.caseCost_mul_costRec_9_7_le`).

Both branches end in the transfer of a solution from `(α_new, W₁)` to `(α, V₁)`, which is
`Babai.step9_transfer'`.

| Paper | Lean |
|---|---|
| §9.4, step 9(ii), the hinted input | `Babai.branch_9_4_9_design_hint` |
| §9.4, step 9(ii), the input without the hint | `Babai.branch_9_4_9_design_nohint` |
-/

namespace Babai

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The transfer, in the form both branches need -/

/-- §9.4, step 9.  **A solution for a pair `(γ, W)` with `W ⊆ W₁` and `γ|W| = α_new |W₁|`
is a solution for `(α, V₁)`.**  This is `Babai.step9_transfer` with the pair the previous
step actually produced: §9.7 may return a solution for the instance *it* handed back, whose
first part is a subset of `W₁`. -/
theorem step9_transfer' {Q : ∀ s : Set Ω, (BipBlockInputs Ω).Obj s → Prop}
    (hsmall : ∀ X : Pt ((BipBlockInputs Ω).full Q), ¬ AllClassesSmall (step9Base X))
    {cost : Pt ((BipBlockInputs Ω).full Q) → ℕ}
    (h : FindsAtMultCost ((BipBlockInputs Ω).full Q) (SplitOutcomes Ω) cost
      (fun X Z => ∃ (γ : ℝ) (W : Set Ω), W ⊆ step8V₁ (step9Base X) ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ)
          = alphaNew (step9Base X) * ((step8V₁ (step9Base X)).ncard : ℝ) ∧
        IsSplitOutcome γ W Z)) :
    FindsAtMultCost ((BipBlockInputs Ω).full Q) (SplitOutcomes Ω) cost
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  classical
  have hVsub : ∀ X : Pt ((BipBlockInputs Ω).full Q),
      BipBlockInputs.V₁ (step9Base X) ⊆ X.car := fun X => V₁_subset_car (step9Base X)
  have hViso : ∀ {X Y : Pt ((BipBlockInputs Ω).full Q)}
      (f : Hom ((BipBlockInputs Ω).full Q) X Y) (x : ↥X.car),
      ((f.1 x : Ω)) ∈ BipBlockInputs.V₁ (step9Base Y)
        ↔ (x : Ω) ∈ BipBlockInputs.V₁ (step9Base X) := by
    intro X Y f x
    exact mem_V₁_iff_of_isoP (X := step9Base X) (Y := step9Base Y) f.2 x
  have htr := transfer_finds_on (C := (BipBlockInputs Ω).full Q)
    (Good := fun X Z => ∃ (γ : ℝ) (W : Set Ω), W ⊆ step8V₁ (step9Base X) ∧ γ ≤ 1 ∧
      γ * (W.ncard : ℝ)
        = alphaNew (step9Base X) * ((step8V₁ (step9Base X)).ncard : ℝ) ∧
      IsSplitOutcome γ W Z)
    (V := fun X => BipBlockInputs.V₁ (step9Base X)) hVsub hViso
    (fun X => BipBlockInputs.alpha (step9Base X))
    (fun X => by
      have : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha (step9Base X) := (step9Base X).obj.2.1
      linarith)
    (fun X Z hZ => by
      obtain ⟨γ, W, hWsub, hγ, heq, hs⟩ := hZ
      exact ⟨γ, W, hWsub.trans (step8V₁_subset (step9Base X)), hγ,
        by rw [heq, alphaNew_mul_step8V₁ (hsmall X)], hs⟩)
  refine (h.comp_dep htr (c₂' := fun _ => 1) (fun _ => le_rfl)).mono
    (fun X => by simp) (fun X Z hZ => ?_)
  obtain ⟨p, hp, hgood⟩ := hZ
  have h1 : IsSplitOutcome (BipBlockInputs.alpha (step9Base (pairFst p)))
      (BipBlockInputs.V₁ (step9Base (pairFst p))) Z := hgood
  rw [hp] at h1
  exact h1

/-! ### The two full subcategories of step 9(ii) -/

/-- §9.4, step 9(ii).  What the turn knows at step 9 in the clique branch. -/
def Step9DesignCond (N : ℕ) (X : Pt (BipBlockInputs Ω)) : Prop :=
  Step9Cond N X ∧ ¬ Step9Imprimitive X ∧ Step9Clique X

/-- §9.4, step 9(ii).  The inputs of the clique branch **that carry the hint**. -/
def DesignHintInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y => Step9DesignCond N ⟨s, Y⟩ ∧ HasHintAt ⟨s, Y⟩

/-- §9.4, step 9(ii).  The inputs of the clique branch **without the hint**. -/
def DesignNoHintInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  (BipBlockInputs Ω).full fun s Y => Step9DesignCond N ⟨s, Y⟩ ∧ ¬ HasHintAt ⟨s, Y⟩

/-! ### The hinted input: the pass has already halved `n₂` -/

section Hint

variable (N : ℕ)

theorem hint_two_mul_le (X : Pt (DesignHintInputs Ω N)) :
    2 * step8NumBlocks (step9Base X) ≤ BipBlockInputs.numBlocks (step9Base X) :=
  two_mul_step8NumBlocks_le_of_hint _ X.obj.2.1.1.2.1 X.obj.2.1.2.2 X.obj.2.2

/-- Being an admissible input of Theorem 9.2.2 does not depend on which `Fintype` and
`DecidableEq` instances the point set carries: they are subsingletons.  This is needed
because `Babai.step8Obj_isThm922Input` carries the instances derived from `DecidableEq Ω`,
while the category `Babai.BipBlockInputs` carries the classical ones. -/
theorem isThm922Input_inst_irrel {s : Type} (Y : VColBipBlk s ℕ)
    (f₁ f₂ : Fintype s) (d₁ d₂ : DecidableEq s) (α : ℝ)
    (h : @VColBipBlk.IsThm922Input s ℕ _ Y f₁ d₁ α) :
    @VColBipBlk.IsThm922Input s ℕ _ Y f₂ d₂ α := by
  rwa [Subsingleton.elim f₂ f₁, Subsingleton.elim d₂ d₁]

/-- §9.4, steps 5–8.  **The instance step 8 leaves is an admissible input of
Theorem 9.2.2** for the threshold `α_new` of step 5. -/
theorem hint_step8Adm (X : Pt (DesignHintInputs Ω N)) :
    letI : Fintype ↥(step7Set (step9Base X)) := Fintype.ofFinite _
    letI : DecidableEq ↥(step7Set (step9Base X)) := Classical.decEq _
    (2 : ℝ) / 3 ≤ alphaNew (step9Base X) ∧ alphaNew (step9Base X) < 1 ∧
      (step8Obj (step9Base X)).IsThm922Input (alphaNew (step9Base X)) :=
  ⟨twothirds_le_alphaNew X.obj.2.1.1.2.1, alphaNew_lt_one X.obj.2.1.1.2.1,
    isThm922Input_inst_irrel (step8Obj (step9Base X)) (Fintype.ofFinite _)
      (Fintype.ofFinite _) _ (Classical.decEq _) _
      (@step8Obj_isThm922Input _ _ _ (step9Base X) X.obj.2.1.1.2.1 (Fintype.ofFinite _))⟩

/-- §9.4, step 9(ii), the hinted input.  **The instance the recursion is called on**: the
graph `(W₁, D; R_i)` that step 8 leaves, with the threshold `α_new` of step 5. -/
noncomputable def hintStep8Func : Func (DesignHintInputs Ω N) (BipBlockInputs Ω) where
  obj X := ⟨step7Set (step9Base X),
    ⟨(step8Obj (step9Base X), alphaNew (step9Base X)), hint_step8Adm N X⟩⟩
  map {A B} f := ⟨step7Equiv (X := step9Base A) (Y := step9Base B) f.2,
    alphaNew_congr ⟨f.1, f.2⟩, step8Obj_isIsoTo f.2⟩
  map_id _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)
  map_trans _ _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)

theorem hintStep8Func_isCanonicalEmbedding :
    (hintStep8Func (Ω := Ω) N).IsCanonicalEmbedding := by
  constructor
  case car_subset => intro X; exact step7Set_subset (step9Base X)
  case map_restrict => intro X Y f x; rfl

/-- §9.5.  **The measure drops.**  The instance has at most `n₂/2` blocks, so its measure
is at most `n₂ + 1`, and the measure of the input is `2 n₂` — the input carries the hint,
so its bit is `0` — which is larger because `n₂ ≥ 2`. -/
theorem hintStep8Func_measure (X : Pt (DesignHintInputs Ω N)) :
    measure_9_5 ((hintStep8Func N).obj X) < N := by
  have hsmall := X.obj.2.1.1.2.1
  have hN : 2 * BipBlockInputs.numBlocks (step9Base X) + hintBit (step9Base X) = N :=
    X.obj.2.1.1.1
  have hbit0 : hintBit (step9Base X) = 0 := (hintBit_eq_zero_iff _).2 X.obj.2.2
  have hn₂ : 2 ≤ BipBlockInputs.numBlocks (step9Base X) :=
    two_le_numBlocks_of_step9 hsmall
  have h2 : 2 * BipBlockInputs.numBlocks ((hintStep8Func N).obj X)
      ≤ BipBlockInputs.numBlocks (step9Base X) := hint_two_mul_le N X
  have hbit := hintBit_le_one ((hintStep8Func N).obj X)
  have hgoal : measure_9_5 ((hintStep8Func N).obj X)
      = 2 * BipBlockInputs.numBlocks ((hintStep8Func N).obj X)
        + hintBit ((hintStep8Func N).obj X) := rfl
  omega

/-- §9.4, step 9(ii), the hinted input.  **The turn pays for the recursive call**, because
`n₂` has at least halved (`Babai.caseCost_mul_cost_9_4_le`). -/
theorem hintStep8Func_cost (C₀ : ℕ) (X : Pt (DesignHintInputs Ω N)) :
    cost_9_4 C₀ ((hintStep8Func N).obj X) ≤ cost_9_4 C₀ (step9Base X) := by
  have hsmall := X.obj.2.1.1.2.1
  have h2 : 2 * BipBlockInputs.numBlocks ((hintStep8Func N).obj X)
      ≤ BipBlockInputs.numBlocks (step9Base X) := hint_two_mul_le N X
  have hkey := caseCost_mul_cost_9_4_le (C₀ := C₀) (k := 1)
    (Y := (hintStep8Func N).obj X) (X := step9Base X)
    (step7Set_subset _) (one_le_turnCost _)
    (lt_of_lt_of_le (by norm_num) (two_le_numBlocks_of_step9 hsmall))
    (by omega)
  simpa using hkey

/-- §9.4, step 9(ii), **the branch of a hinted input**.  §9.7 is not called: the pass has
already made the progress of §9.5, so the recursion runs on the instance step 8 leaves and
the solution is transferred to `(α, V₁)`. -/
theorem branch_9_4_9_design_hint (C₀ N : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost (DesignHintInputs Ω N) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  refine step9_transfer' (fun X => X.obj.2.1.1.2.1) ?_
  refine (FindsAtMultCost.precomp
      ((hintStep8Func N).intoFull _ (fun X => hintStep8Func_measure N X))
      (Func.intoFull_isCanonicalEmbedding (hintStep8Func_isCanonicalEmbedding N) _ _)
      hrec).mono (fun X => hintStep8Func_cost N C₀ X) (fun X Z hZ => ?_)
  have hZ' : IsSplitOutcome (alphaNew (step9Base X)) (step8V₁ (step9Base X)) Z := hZ
  exact ⟨alphaNew (step9Base X), step8V₁ (step9Base X), subset_rfl,
    le_of_lt (alphaNew_lt_one X.obj.2.1.1.2.1), rfl, hZ'⟩

end Hint

/-! ### The input without the hint: §9.7 is called -/

/-- §9.4, step 9(ii).  The outcome of §9.7 (`Babai.IsBlkDesignOutcome`), read at an input
of the branch: the pair to be split is `(α_new, W₁)` and the number of blocks is the one
the instance of step 8 has. -/
def DesignGood (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ)
    (X : Pt (DesignNoHintInputs Ω N))
    (Z : Pt (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω))) : Prop :=
  IsBlkDesignOutcome (alphaNew (step9Base X)) (step8V₁ (step9Base X))
    (step8NumBlocks (step9Base X)) Z

/-- §9.4, step 9(ii).  The pairs *(input of the pass, outcome of §9.7)*: the category the
second stage of the branch runs on, so that the recursive call may look at the input. -/
def Step9DesignPairs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  PairCatOf (DesignNoHintInputs Ω N) (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω))
    (DesignGood Ω N)

section NoHint

variable (N : ℕ)

/-- The input of the pass, read at a pair. -/
def designBase (p : Pt (Step9DesignPairs Ω N)) : Pt (BipBlockInputs Ω) := step9Base (pairFst p)

/-- §9.4, step 9(ii).  **The functor from the inputs without the hint into the inputs of
§9.7**: `Babai.step9DesignFunc`, precomposed with the embedding of this branch into the
category step 9(ii) runs on. -/
noncomputable def noHintDesignFunc :
    Func (DesignNoHintInputs Ω N) (BlkBlockDesignInputs Ω) :=
  (show Func (DesignNoHintInputs Ω N) (Step9DesignInputs Ω N) from
      fullOfBase _ (fun A => A.1) (fun h => h) (fun A => A.2.1)).comp (step9DesignFunc N)

theorem noHintDesignFunc_isCanonicalEmbedding :
    (noHintDesignFunc (Ω := Ω) N).IsCanonicalEmbedding :=
  Func.IsCanonicalEmbedding.comp
    (fullOfBase_isCanonicalEmbedding (D := DesignNoHintInputs Ω N) _ (fun A => A.1)
      (fun h => h) (fun A => A.2.1))
    (step9DesignFunc_isCanonicalEmbedding N)

/-- §9.4, step 9(ii).  **§9.7 is called on the instance step 8 leaves, at multiplicative
cost below one turn** (`Babai.caseCost_9_7_le_turnCost`).  Its two parameters are below
`|□X|`: the first part of the instance is inside `V₁` and so inside `□X`, and the number of
blocks does not grow after step 5. -/
theorem noHint_case :
    FindsAtMultCost (DesignNoHintInputs Ω N)
      (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω))
      (fun X => turnCost (step9Base X).car.ncard) (DesignGood Ω N) := by
  refine (FindsAtMultCost.precomp (noHintDesignFunc N)
    (noHintDesignFunc_isCanonicalEmbedding N) case_9_7).mono (fun X => ?_) (fun X Z h => h)
  refine caseCost_9_7_le_turnCost ?_ ?_
  · exact Set.ncard_le_ncard
      ((step8V₁_subset (step9Base X)).trans (V₁_subset_car (step9Base X)))
      (Set.toFinite _)
  · exact le_trans (step8NumBlocks_le (step9Base X))
      (BipBlockInputs.numBlocks_le_ncard (step9Base X))

/-- §9.4, step 9(ii).  The branch on which §9.7 finished Theorem 9.2.2 for `(α_new, W₁)`:
the outcome itself.  Word for word `Babai.halvedLeftFunc`, except that the left summand is
already the category of the outcomes. -/
noncomputable def designLeftFunc :
    Func ((Step9DesignPairs Ω N).full fun _ p => (p.snd).isLeft) (SplitOutcomes Ω) :=
  (((Cat.fullIncl (Step9DesignPairs Ω N) (fun _ p => (p.snd).isLeft)).comp
      (pairSndFunc (DesignNoHintInputs Ω N)
        (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω)) (DesignGood Ω N))).intoFull
      (Cat.sumIsLeft (SplitOutcomes Ω) (BipBlockInputs Ω))
      (fun X => X.obj.2)).comp
    (Cat.sumLeftProj (SplitOutcomes Ω) (BipBlockInputs Ω))

theorem designLeftFunc_isCanonicalEmbedding :
    (designLeftFunc (Ω := Ω) N).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (Step9DesignPairs Ω N) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    (Cat.sumLeftProj_isCanonicalEmbedding _ _)

/-- §9.4, step 9(ii).  The branch on which §9.7 handed back a smaller instance: that
instance.  Word for word `Babai.halvedRightGraph`, except that the instance already carries
its threshold. -/
noncomputable def designRightFunc :
    Func ((Step9DesignPairs Ω N).full fun _ p => ¬ (p.snd).isLeft) (BipBlockInputs Ω) :=
  (((Cat.fullIncl (Step9DesignPairs Ω N) (fun _ p => ¬ (p.snd).isLeft)).comp
      (pairSndFunc (DesignNoHintInputs Ω N)
        (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω)) (DesignGood Ω N))).intoFull
      (Cat.sumIsRight (SplitOutcomes Ω) (BipBlockInputs Ω))
      (fun X => Sum.not_isLeft.mp X.obj.2)).comp
    (Cat.sumRightProj (SplitOutcomes Ω) (BipBlockInputs Ω))

theorem designRightFunc_isCanonicalEmbedding :
    (designRightFunc (Ω := Ω) N).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (Step9DesignPairs Ω N) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    (Cat.sumRightProj_isCanonicalEmbedding _ _)

/-- §9.4, step 9(ii).  **What §9.7 guarantees on the branch where it handed back an
instance**: its first part is inside `W₁`, the product `α|V₁|` is the one of `(α_new, W₁)`,
and either `n₂` is significantly reduced or the instance carries the hint. -/
theorem designRight_spec (p : Pt ((Step9DesignPairs Ω N).full fun _ p => ¬ (p.snd).isLeft)) :
    BipBlockInputs.V₁ ((designRightFunc N).obj p)
        ⊆ step8V₁ (designBase N ⟨p.car, p.obj.1⟩) ∧
      BipBlockInputs.alpha ((designRightFunc N).obj p)
          * ((BipBlockInputs.V₁ ((designRightFunc N).obj p)).ncard : ℝ)
        = alphaNew (designBase N ⟨p.car, p.obj.1⟩)
          * ((step8V₁ (designBase N ⟨p.car, p.obj.1⟩)).ncard : ℝ) ∧
      (10 * BipBlockInputs.numBlocks ((designRightFunc N).obj p)
          ≤ 9 * step8NumBlocks (designBase N ⟨p.car, p.obj.1⟩) ∨
        (BipBlockInputs.numBlocks ((designRightFunc N).obj p)
            ≤ step8NumBlocks (designBase N ⟨p.car, p.obj.1⟩) ∧
          hintBit ((designRightFunc N).obj p) = 0)) := by
  have hgood := p.obj.1.good
  have hr : (p.obj.1.snd).isRight := Sum.not_isLeft.mp p.obj.2
  have hs : p.obj.1.snd = Sum.inr (p.obj.1.snd.getRight hr) :=
    Sum.eq_right_getRight_of_isRight hr
  rw [DesignGood, IsBlkDesignOutcome, hs] at hgood
  obtain ⟨h1, h2, h3⟩ := hgood
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h | ⟨hle, hhint⟩
  · exact Or.inl h
  · exact Or.inr ⟨hle, (hintBit_eq_zero_iff _).2 hhint⟩

/-- §9.5.  **The measure drops.**  The input has no hint, so its measure is `2 n₂ + 1`.
If `n₂` is significantly reduced then the new `n₂` is smaller, because `10 n₂' ≤ 9 n₂` and
`n₂ ≥ 2`; if the instance carries the hint then its bit is `0` and its `n₂` is at most the
old one. -/
theorem designRight_measure (p : Pt ((Step9DesignPairs Ω N).full fun _ p => ¬ (p.snd).isLeft)) :
    measure_9_5 ((designRightFunc N).obj p) < N := by
  obtain ⟨-, -, h3⟩ := designRight_spec N p
  have hsmall : ¬ AllClassesSmall (designBase N ⟨p.car, p.obj.1⟩) :=
    (pairFst (⟨p.car, p.obj.1⟩ : Pt (Step9DesignPairs Ω N))).obj.2.1.1.2.1
  have hN : measure_9_5 (designBase N ⟨p.car, p.obj.1⟩) = N :=
    (pairFst (⟨p.car, p.obj.1⟩ : Pt (Step9DesignPairs Ω N))).obj.2.1.1.1
  have hbit1 : hintBit (designBase N ⟨p.car, p.obj.1⟩) = 1 :=
    hintBit_eq_one_of_not _ (pairFst (⟨p.car, p.obj.1⟩ : Pt (Step9DesignPairs Ω N))).obj.2.2
  have hmeas : measure_9_5 (designBase N ⟨p.car, p.obj.1⟩)
      = 2 * BipBlockInputs.numBlocks (designBase N ⟨p.car, p.obj.1⟩)
        + hintBit (designBase N ⟨p.car, p.obj.1⟩) := rfl
  have hle8 : step8NumBlocks (designBase N ⟨p.car, p.obj.1⟩)
      ≤ BipBlockInputs.numBlocks (designBase N ⟨p.car, p.obj.1⟩) := step8NumBlocks_le _
  have hn₂ : 2 ≤ BipBlockInputs.numBlocks (designBase N ⟨p.car, p.obj.1⟩) :=
    two_le_numBlocks_of_step9 hsmall
  have hbitY := hintBit_le_one ((designRightFunc N).obj p)
  have hgoal : measure_9_5 ((designRightFunc N).obj p)
      = 2 * BipBlockInputs.numBlocks ((designRightFunc N).obj p)
        + hintBit ((designRightFunc N).obj p) := rfl
  rcases h3 with h | ⟨hle, hbit0⟩
  · omega
  · omega

/-- §9.4, step 9(ii).  **The cost of the recursive call is `Babai.costRec_9_7` at the
input**, in both kinds of progress. -/
theorem designRight_cost (C₀ : ℕ)
    (p : Pt ((Step9DesignPairs Ω N).full fun _ p => ¬ (p.snd).isLeft)) :
    cost_9_4 C₀ ((designRightFunc N).obj p)
      ≤ costRec_9_7 C₀ (designBase N ⟨p.car, p.obj.1⟩) := by
  obtain ⟨-, -, h3⟩ := designRight_spec N p
  have hle8 : step8NumBlocks (designBase N ⟨p.car, p.obj.1⟩)
      ≤ BipBlockInputs.numBlocks (designBase N ⟨p.car, p.obj.1⟩) := step8NumBlocks_le _
  rcases h3 with h | ⟨hle, hbit0⟩
  · exact cost_9_4_le_costRec_9_7_of_reduced p.obj.1.sub_subset (by omega)
  · exact cost_9_4_le_costRec_9_7_of_hint p.obj.1.sub_subset (by omega) hbit0

/-- §9.4, step 9(ii), **the branch of an input without the hint**.  §9.7 is called on the
instance step 8 leaves (`Babai.noHint_case`).  Either it finishes Theorem 9.2.2 for
`(α_new, W₁)`, or it hands back an admissible instance of smaller measure
(`Babai.designRight_measure`), on which the recursion `hrec` is called; a solution for that
instance is a solution for `(α_new, W₁)`, because its first part is inside `W₁` and the
product `α|V₁|` is unchanged (`Babai.designRight_spec`).  Both cases end in
`Babai.step9_transfer'`.

The turn pays for the call because the input has no hint, so its bit is `1`
(`Babai.caseCost_mul_costRec_9_7_le`), and the cost of §9.7 itself is below one turn.

The assembly is the three-stage `Babai.FindsAtMultCost.comp_dep` chain of
`Babai.step9_halvedBranch`: the case, then the case distinction by the side of the sum on
the pairs *(input, outcome)*, then the transfer. -/
theorem branch_9_4_9_design_nohint (C₀ : ℕ)
    (hrec : FindsAtMultCost ((BipBlockInputs Ω).full fun s Y => measure_9_5 ⟨s, Y⟩ < N)
      (SplitOutcomes Ω) (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1⟩ Z)) :
    FindsAtMultCost (DesignNoHintInputs Ω N) (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ (step9Base X))
      (fun X Z => Good_9_2_2 (step9Base X) Z) := by
  classical
  -- §9.7 finished Theorem 9.2.2 for `(α_new, W₁)`
  have hleft : FindsAtMultCost ((Step9DesignPairs Ω N).full fun _ p => (p.snd).isLeft)
      (SplitOutcomes Ω) (fun _ => 1)
      (fun p Z => ∃ (γ : ℝ) (W : Set Ω),
        W ⊆ step8V₁ (designBase N ⟨p.car, p.obj.1⟩) ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ)
          = alphaNew (designBase N ⟨p.car, p.obj.1⟩)
            * ((step8V₁ (designBase N ⟨p.car, p.obj.1⟩)).ncard : ℝ) ∧
        IsSplitOutcome γ W Z) := by
    refine FindsAtMultCost.of_canonicalEmbedding (designLeftFunc N)
      (designLeftFunc_isCanonicalEmbedding N) (fun p => ?_)
    have hgood := p.obj.1.good
    have hl : (p.obj.1.snd).isLeft := p.obj.2
    have hs : p.obj.1.snd = Sum.inl (p.obj.1.snd.getLeft hl) :=
      Sum.eq_left_getLeft_of_isLeft hl
    rw [DesignGood, IsBlkDesignOutcome, hs] at hgood
    have hsmall : ¬ AllClassesSmall (designBase N ⟨p.car, p.obj.1⟩) :=
      (pairFst (⟨p.car, p.obj.1⟩ : Pt (Step9DesignPairs Ω N))).obj.2.1.1.2.1
    exact ⟨alphaNew (designBase N ⟨p.car, p.obj.1⟩),
      step8V₁ (designBase N ⟨p.car, p.obj.1⟩), subset_rfl,
      le_of_lt (alphaNew_lt_one hsmall), rfl, hgood⟩
  -- §9.7 handed back a smaller instance: the recursion of §9.5
  have hright : FindsAtMultCost ((Step9DesignPairs Ω N).full fun _ p => ¬ (p.snd).isLeft)
      (SplitOutcomes Ω) (fun p => costRec_9_7 C₀ (designBase N ⟨p.car, p.obj.1⟩))
      (fun p Z => ∃ (γ : ℝ) (W : Set Ω),
        W ⊆ step8V₁ (designBase N ⟨p.car, p.obj.1⟩) ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ)
          = alphaNew (designBase N ⟨p.car, p.obj.1⟩)
            * ((step8V₁ (designBase N ⟨p.car, p.obj.1⟩)).ncard : ℝ) ∧
        IsSplitOutcome γ W Z) := by
    refine (FindsAtMultCost.precomp
      ((designRightFunc N).intoFull _ (fun p => designRight_measure N p))
      (Func.intoFull_isCanonicalEmbedding (designRightFunc_isCanonicalEmbedding N) _ _)
      hrec).mono (fun p => designRight_cost N C₀ p) (fun p Z hZ => ?_)
    obtain ⟨hsub, heq, -⟩ := designRight_spec N p
    exact ⟨BipBlockInputs.alpha ((designRightFunc N).obj p),
      BipBlockInputs.V₁ ((designRightFunc N).obj p), hsub,
      le_of_lt ((designRightFunc N).obj p).obj.2.2.1, heq, hZ⟩
  -- the two branches, glued
  have hmid0 := FindsAtMultCost.cases (C := Step9DesignPairs Ω N)
    (P := fun _ p => (p.snd).isLeft)
    (costp := fun _ => 1)
    (costn := fun p => costRec_9_7 C₀ (designBase N p))
    (Good := fun p Z => ∃ (γ : ℝ) (W : Set Ω), W ⊆ step8V₁ (designBase N p) ∧ γ ≤ 1 ∧
      γ * (W.ncard : ℝ)
        = alphaNew (designBase N p) * ((step8V₁ (designBase N p)).ncard : ℝ) ∧
      IsSplitOutcome γ W Z)
    (fun {X Y} h hp => pairSnd_isLeft_iso h hp) hleft hright
  -- the case, then the two branches
  have hmid := (noHint_case N).comp_dep hmid0
    (c₂' := fun X => costRec_9_7 C₀ (step9Base X))
    (fun p => max_le (one_le_costRec_9_7 _ _) le_rfl)
  refine step9_transfer' (fun X => X.obj.2.1.1.2.1) (hmid.mono (fun X => ?_) (fun X Z hZ => ?_))
  · exact caseCost_mul_costRec_9_7_le le_rfl
      (lt_of_lt_of_le (by norm_num) (two_le_numBlocks_of_step9 X.obj.2.1.1.2.1))
      (hintBit_eq_one_of_not _ X.obj.2.2)
  · obtain ⟨p, hp, h1⟩ := hZ
    have h2 : ∃ (γ : ℝ) (W : Set Ω), W ⊆ step8V₁ (step9Base (pairFst p)) ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ)
          = alphaNew (step9Base (pairFst p))
            * ((step8V₁ (step9Base (pairFst p))).ncard : ℝ) ∧
        IsSplitOutcome γ W Z := h1
    rw [hp] at h2
    exact h2

end NoHint

end Babai
