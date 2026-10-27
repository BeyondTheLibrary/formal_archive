/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 9: the bookkeeping that lets the three cases of Sections 9.6, 9.7 and 9.8
hand their output back to the recursion of Section 9.5.
-/
import Workspace.SplitOrJohnson.BlkCases
import Workspace.Functors.PairProj
import Workspace.Functors.SumProj

/-!
# §9.4, step 9: the two pieces of bookkeeping

Step 9 of Procedure Bipartite Split-or-Johnson calls one of the three cases of §9.6, §9.7
and §9.8 and, when the case does not exit with goal (a) or (b), hands the instance it
returns back to Theorem 9.2.2.  Three things have to be checked before that call:

* **the returned instance is admissible.**  §9.6 and §9.8 return a bipartite graph with
  blocks (`Babai.IsBlkImprimitiveOutcome`) and say only that the symmetry defect of `V₁` in
  it is at least `1/2` and that the number of blocks has at least halved.  The threshold
  `α` is the one the procedure carries, and it is unchanged by those two cases, because
  they keep `V₁` whole.  `Babai.isThm922Input_of_halved` is the check.
* **the turn pays for the call.**  `Babai.caseCost_mul_cost_9_4_le` is the cost accounting
  of item 9 of the plan in the docstring of `Babai.steps_9_4_3_to_9`, built on
  `Babai.turnCost_mul_costFun_le` (`Workspace/SplitOrJohnson/Depth.lean`).
* **a solution for the smaller instance is a solution for `V₁`.**  This is the transfer
  clause of Lemma 9.3.1, for the set to be split `V₁`, which is a proper subset of the
  point set `□X`: `Babai.transfer_finds_on`.

| Paper | Lean |
|---|---|
| §9.4, step 9: the outcome of §9.6/§9.8 is an admissible input | `Babai.isThm922Input_of_halved` |
| §9.4, step 9: one turn pays for the recursive call | `Babai.caseCost_mul_cost_9_4_le` |
| §9.7, Case 3a: the cost of the block design case is below one turn | `Babai.caseCost_9_7_le_turnCost` |
| Lemma 9.3.1, the transfer clause, for a set to be split inside `□X` | `Babai.transfer_finds_on` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The outcome of §9.6 and of §9.8 is an admissible input of Theorem 9.2.2

The two cases return, in their second branch, *"a canonical bipartite graph
`Y = (V₁, W₂; F)` such that `|W₂| ≤ |V₂|/2` such that the symmetry defect of `V₁` in `Y` is
`≥ 1/2`"* (Lemma 9.6.1; §9.8 says the same, *"reduces `n₂` by half while maintaining
symmetry defect `≥ 1/2` in each part"*).  Neither of them changes `V₁`, so the threshold
`α` that the procedure carries is unchanged, and the three hypotheses of Theorem 9.2.2 hold
for `Y` and that same `α`. -/

omit [Fintype Ω] [DecidableEq Ω] in
/-- §9.4, step 9.  **The graph returned by §9.6 or by §9.8 is an admissible input of
Theorem 9.2.2 for the threshold the procedure already carries.**

* *"`|V₁| ≥ 2`"*: `V₁` is not touched by either case.
* *"`|V₂| < α|V₁|`"*: the number of blocks has at least halved, so it is at most the old
  `n₂`, which is already `< α|V₁|`.
* *"the symmetry defect of `X` on `V₁` is at least `1 - α`"*: the case guarantees a defect
  of at least `1/2`, and `1 - α ≤ 1/3 ≤ 1/2` because `α ≥ 2/3`.

The hypothesis `α ≥ 2/3` is where the paper's lower bound on the threshold parameter is
used; this is the only place in step 9 that needs it. -/
theorem isThm922Input_of_halved {t : Set Ω} [Fintype ↥t] [DecidableEq ↥t]
    (Y : VColBipBlk ↥t ℕ) {α : ℝ} {V₁ : Set Ω} {n₂ : ℕ}
    (hα : 2 / 3 ≤ α) (hV : Subtype.val '' Y.V₁ = V₁) (hcard : 2 ≤ V₁.ncard)
    (hn₂ : (n₂ : ℝ) < α * (V₁.ncard : ℝ)) (hhalf : 2 * Y.numBlocks ≤ n₂)
    (hdef : 1 / 2 ≤ Y.defect₁) :
    Y.IsThm922Input α := by
  have hVcard : Y.V₁.ncard = V₁.ncard := by
    rw [← hV, Set.ncard_image_of_injective _ Subtype.val_injective]
  refine ⟨by rw [hVcard]; exact hcard, ?_, ?_⟩
  · -- `n₂_new ≤ n₂ < α |V₁|`
    have h1 : Y.numBlocks ≤ n₂ := le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) hhalf
    have h1' : (Y.numBlocks : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h1
    rw [hVcard]
    linarith
  · -- `1 - α ≤ 1/3 ≤ 1/2 ≤ defect₁`
    have hdef' : (1 : ℝ) / 2 ≤ (Y.defect₁ : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hdef
      simpa using this
    linarith

/-! ### One turn pays for the recursive call -/

/-- §9.4, step 9, and §9.5.  **The cost accounting of one turn.**  The instance `Y` that a
case of step 9 hands back to the recursion lives on a subset of the point set of `X` and
has a *significantly reduced* `n₂` (§9.5), so the multiplicative cost of the case, which is
at most `Babai.turnCost`, times the cost of the recursion on `Y`, is at most the cost of
the recursion on `X`.

The hypothesis `0 < n₂` is free: when `n₂ = 0` every branch of step 9 costs `0`
(`Babai.BlkImprimitiveCases.numBlocks` is the cost of §9.6 and of §9.8, and the exponent of
§9.7 is at least `2`), so the product is `0`. -/
theorem caseCost_mul_cost_9_4_le {C₀ : ℕ} {X Y : Pt (BipBlockInputs Ω)} {k : ℕ}
    (hcar : Y.car ⊆ X.car) (hk : k ≤ turnCost X.car.ncard)
    (hn₂ : 0 < BipBlockInputs.numBlocks X)
    (hred : 10 * BipBlockInputs.numBlocks Y ≤ 9 * BipBlockInputs.numBlocks X) :
    k * cost_9_4 C₀ Y ≤ cost_9_4 C₀ X := by
  have hncard : Y.car.ncard ≤ X.car.ncard :=
    Set.ncard_le_ncard hcar (Set.toFinite _)
  calc k * cost_9_4 C₀ Y
      = constFactor C₀
          * (k * costFun Y.car.ncard (BipBlockInputs.numBlocks Y) (hintBit Y)) := by
        rw [cost_9_4]; ring
    _ ≤ constFactor C₀
          * (turnCost X.car.ncard
              * costFun Y.car.ncard (BipBlockInputs.numBlocks Y) (hintBit Y)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ ≤ constFactor C₀
          * costFun X.car.ncard (BipBlockInputs.numBlocks X) (hintBit X) :=
        Nat.mul_le_mul_left _
          (turnCost_mul_costFun_le hncard hn₂ hred (hintBit_le_one Y))
    _ = cost_9_4 C₀ X := rfl

/-- §9.4, step 9.  The special case of `Babai.caseCost_mul_cost_9_4_le` in which the number
of blocks at least halves, which is what §9.6 and §9.8 give (*"`|W₂| ≤ |V₂|/2`"*). -/
theorem caseCost_mul_cost_9_4_le_of_halved {C₀ : ℕ} {X Y : Pt (BipBlockInputs Ω)} {k : ℕ}
    (hcar : Y.car ⊆ X.car) (hk : k ≤ turnCost X.car.ncard)
    (hn₂ : 0 < BipBlockInputs.numBlocks X)
    (hhalf : 2 * BipBlockInputs.numBlocks Y ≤ BipBlockInputs.numBlocks X) :
    k * cost_9_4 C₀ Y ≤ cost_9_4 C₀ X :=
  caseCost_mul_cost_9_4_le hcar hk hn₂ (by omega)

/-! ### The cost of the recursive call, expressed at the input

`Babai.FindsAtMultCost.comp_dep` asks for the cost of the second step as a function of the
**input** of the first step, while the recursive call of step 9 is made on the instance the
case returned.  `Babai.costRec_9_4` is that bound: the cost of the recursion on an instance
that lives inside `□X` and whose `n₂` has at least halved. -/

/-- The cost of the recursion grows with the number of points and with `n₂`. -/
theorem costFun_mono {n n' n₂ n₂' b b' : ℕ} (hn : n ≤ n') (h₂ : n₂ ≤ n₂') (hb : b ≤ b') :
    costFun n n₂ b ≤ costFun n' n₂' b' :=
  le_trans (Nat.pow_le_pow_left (turnCost_mono hn) _)
    (Nat.pow_le_pow_right (one_le_turnCost n')
      (by have := steps09_mono _ _ h₂; omega))

/-- One turn costs at least `n`: individualizing one point of the input is within the
budget of a turn. -/
theorem self_le_turnCost (n : ℕ) : n ≤ turnCost n := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : Nat.log 2 n + 1 ≤ turnConst * (Nat.log 2 n + 2) ^ 2 := by
    have h : Nat.log 2 n + 1 ≤ 4 * (Nat.log 2 n + 2) ^ 2 := by nlinarith [sq_nonneg (Nat.log 2 n)]
    simpa [turnConst] using h
  exact le_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2))

/-- The multiplicative cost `n₂` of §9.6 and of §9.8 is within the budget of one turn. -/
theorem numBlocks_le_turnCost (X : Pt (BipBlockInputs Ω)) :
    BipBlockInputs.numBlocks X ≤ turnCost X.car.ncard :=
  le_trans (BipBlockInputs.numBlocks_le_ncard X) (self_le_turnCost _)

/-- §9.4, step 9.  **The cost of the recursive call, read at the input.**  The instance a
case of §9.6 or §9.8 returns lives inside `□X` and has at most `n₂/2` blocks, so this
bounds the cost of the recursion on it. -/
noncomputable def costRec_9_4 (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : ℕ :=
  constFactor C₀ * costFun X.car.ncard (BipBlockInputs.numBlocks X / 2) 1

theorem one_le_costRec_9_4 (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : 1 ≤ costRec_9_4 C₀ X := by
  simpa using Nat.mul_le_mul (one_le_constFactor C₀)
    (Nat.one_le_pow _ _ (one_le_turnCost _))

theorem cost_9_4_le_costRec_9_4 {C₀ : ℕ} {X Y : Pt (BipBlockInputs Ω)}
    (hcar : Y.car ⊆ X.car)
    (hhalf : 2 * BipBlockInputs.numBlocks Y ≤ BipBlockInputs.numBlocks X) :
    cost_9_4 C₀ Y ≤ costRec_9_4 C₀ X :=
  Nat.mul_le_mul_left _
    (costFun_mono (Set.ncard_le_ncard hcar (Set.toFinite _)) (by omega)
      (hintBit_le_one Y))

/-- §9.4, step 9.  **One turn pays for the recursive call**, with the cost of the call
read at the input (`Babai.costRec_9_4`). -/
theorem caseCost_mul_costRec_9_4_le {C₀ k : ℕ} {X : Pt (BipBlockInputs Ω)}
    (hk : k ≤ turnCost X.car.ncard) (hn₂ : 0 < BipBlockInputs.numBlocks X) :
    k * costRec_9_4 C₀ X ≤ cost_9_4 C₀ X := by
  calc k * costRec_9_4 C₀ X
      = constFactor C₀
          * (k * costFun X.car.ncard (BipBlockInputs.numBlocks X / 2) 1) := by
        rw [costRec_9_4]; ring
    _ ≤ constFactor C₀
          * (turnCost X.car.ncard
              * costFun X.car.ncard (BipBlockInputs.numBlocks X / 2) 1) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ ≤ constFactor C₀
          * costFun X.car.ncard (BipBlockInputs.numBlocks X) (hintBit X) :=
        Nat.mul_le_mul_left _
          (turnCost_mul_costFun_le le_rfl hn₂ (by omega) le_rfl)
    _ = cost_9_4 C₀ X := rfl

/-! ### The cost of the recursive call of §9.7

§9.7 makes two kinds of progress (§9.5): *"`n₂` is significantly reduced"*, and *"`X₂`
moves from clique to UPCC while `n₂` does not increase"*.  The two give different bounds on
the cost of the recursion on the instance handed back, and `Babai.costRec_9_7` is the
larger of them, read at the input. -/

/-- §9.4, step 9(ii).  **The cost of the recursive call of §9.7, read at the input.**  The
instance §9.7 hands back either has at most `0.9 n₂` blocks, or has at most `n₂` blocks and
carries the hint. -/
noncomputable def costRec_9_7 (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : ℕ :=
  constFactor C₀ *
    max (costFun X.car.ncard (9 * BipBlockInputs.numBlocks X / 10) 1)
      (costFun X.car.ncard (BipBlockInputs.numBlocks X) 0)

theorem one_le_costRec_9_7 (C₀ : ℕ) (X : Pt (BipBlockInputs Ω)) : 1 ≤ costRec_9_7 C₀ X := by
  have h1 : 1 ≤ costFun X.car.ncard (9 * BipBlockInputs.numBlocks X / 10) 1 :=
    Nat.one_le_pow _ _ (one_le_turnCost _)
  have h2 := Nat.le_max_left (costFun X.car.ncard (9 * BipBlockInputs.numBlocks X / 10) 1)
    (costFun X.car.ncard (BipBlockInputs.numBlocks X) 0)
  exact le_trans (by simpa using Nat.mul_le_mul (one_le_constFactor C₀) h1)
    (Nat.mul_le_mul_left _ h2)

/-- §9.5, the first kind of progress: *"`n₂` is significantly reduced"*. -/
theorem cost_9_4_le_costRec_9_7_of_reduced {C₀ : ℕ} {X Y : Pt (BipBlockInputs Ω)}
    (hcar : Y.car ⊆ X.car)
    (hred : 10 * BipBlockInputs.numBlocks Y ≤ 9 * BipBlockInputs.numBlocks X) :
    cost_9_4 C₀ Y ≤ costRec_9_7 C₀ X := by
  refine le_trans (Nat.mul_le_mul_left _ ?_) (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
  exact costFun_mono (Set.ncard_le_ncard hcar (Set.toFinite _)) (by omega)
    (hintBit_le_one Y)

/-- §9.5, the third kind of progress: *"`X₂` moves from clique to UPCC while `n₂` does not
increase"*. -/
theorem cost_9_4_le_costRec_9_7_of_hint {C₀ : ℕ} {X Y : Pt (BipBlockInputs Ω)}
    (hcar : Y.car ⊆ X.car)
    (hle : BipBlockInputs.numBlocks Y ≤ BipBlockInputs.numBlocks X)
    (hbit : hintBit Y = 0) :
    cost_9_4 C₀ Y ≤ costRec_9_7 C₀ X := by
  refine le_trans (Nat.mul_le_mul_left _ ?_) (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
  rw [hbit]
  exact costFun_mono (Set.ncard_le_ncard hcar (Set.toFinite _)) hle le_rfl

/-- §9.4, step 9(ii).  **One turn pays for the recursive call of §9.7.**  The input of the
pass has no hint, so its bit is `1` and the odd summand of the exponent of
`Babai.costFun` is available: it pays for the turn that only gains the hint
(`Babai.turnCost_mul_costFun_le_of_hint`). -/
theorem caseCost_mul_costRec_9_7_le {C₀ k : ℕ} {X : Pt (BipBlockInputs Ω)}
    (hk : k ≤ turnCost X.car.ncard) (hn₂ : 0 < BipBlockInputs.numBlocks X)
    (hbit : hintBit X = 1) : k * costRec_9_7 C₀ X ≤ cost_9_4 C₀ X := by
  have h1 : turnCost X.car.ncard
      * costFun X.car.ncard (9 * BipBlockInputs.numBlocks X / 10) 1
      ≤ costFun X.car.ncard (BipBlockInputs.numBlocks X) 1 :=
    turnCost_mul_costFun_le le_rfl hn₂ (by omega) le_rfl
  have h2 : turnCost X.car.ncard * costFun X.car.ncard (BipBlockInputs.numBlocks X) 0
      ≤ costFun X.car.ncard (BipBlockInputs.numBlocks X) 1 :=
    turnCost_mul_costFun_le_of_hint le_rfl le_rfl
  calc k * costRec_9_7 C₀ X
      = constFactor C₀ * (k * max (costFun X.car.ncard
          (9 * BipBlockInputs.numBlocks X / 10) 1)
          (costFun X.car.ncard (BipBlockInputs.numBlocks X) 0)) := by
        rw [costRec_9_7]; ring
    _ ≤ constFactor C₀ * (turnCost X.car.ncard * max (costFun X.car.ncard
          (9 * BipBlockInputs.numBlocks X / 10) 1)
          (costFun X.car.ncard (BipBlockInputs.numBlocks X) 0)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk)
    _ ≤ constFactor C₀ * costFun X.car.ncard (BipBlockInputs.numBlocks X) 1 := by
        refine Nat.mul_le_mul_left _ ?_
        rcases max_cases (costFun X.car.ncard (9 * BipBlockInputs.numBlocks X / 10) 1)
          (costFun X.car.ncard (BipBlockInputs.numBlocks X) 0) with ⟨he, -⟩ | ⟨he, -⟩
        · rw [he]; exact h1
        · rw [he]; exact h2
    _ = cost_9_4 C₀ X := by rw [cost_9_4, hbit]

/-! ### The transfer of a solution, for a set to be split that is not the whole point set

Lemma 9.3.1 transfers a solution of Theorem 9.2.2 for a subset `W` of the set `V` that is
to be split back to a solution for `V`: a Johnson scheme is kept as it is, and a colored
partition of `W` is extended by the one block `V \ W` (`Babai.extendPartition`).

`Babai.transfer_finds` (`Workspace/SplitOrJohnson/Sec92.lean`) is this construction for
`V = □X`, which is what Theorem 9.2.1 needs: there the set to be split is the whole vertex
set.  In §9.4 the set to be split is `V₁`, a **proper** subset of `□X`, since the points
that lie in blocks are in `□X` too, so steps 5, 7 and 9 need the same construction for an
isomorphism-invariant `V : Pt C → Set Ω` with `V X ⊆ □X`.  That is what this section
provides; `Babai.transfer_finds` is the case `V X = X.car`. -/

section TransferOn

variable (C : Cat.{0, 0} Ω) (Good : Pt C → Pt (SplitOutcomes Ω) → Prop) (V : Pt C → Set Ω)
  (hVsub : ∀ X : Pt C, V X ⊆ X.car)
  (hViso : ∀ {X Y : Pt C} (f : Hom C X Y) (x : ↥X.car),
    ((f.1 x : Ω)) ∈ V Y ↔ (x : Ω) ∈ V X)

variable {C V}

/-- The restriction of a morphism `f : X → Y` of `C` to the sets to be split.  It is
well defined because `V` is isomorphism-invariant (`hViso`). -/
def restrictEquivOn {X Y : Pt C} (f : Hom C X Y) : ↥(V X) ≃ ↥(V Y) where
  toFun z := ⟨(f.1 ⟨(z : Ω), hVsub X z.2⟩ : Ω), (hViso f _).2 z.2⟩
  invFun w := ⟨(f.1.symm ⟨(w : Ω), hVsub Y w.2⟩ : Ω), by
    refine (hViso f (f.1.symm ⟨(w : Ω), hVsub Y w.2⟩)).1 ?_
    rw [Equiv.apply_symm_apply]
    exact w.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

omit [Fintype Ω] [DecidableEq Ω] in
@[simp] theorem restrictEquivOn_val {X Y : Pt C} (f : Hom C X Y) (z : ↥(V X)) :
    ((restrictEquivOn hVsub hViso f z : ↥(V Y)) : Ω)
      = (f.1 ⟨(z : Ω), hVsub X z.2⟩ : Ω) := rfl

variable (C V)

open scoped Classical in
/-- The transfer on the branch where the previous step returned a colored partition of the
subset `W`: extend it to `V X` by the single block `V X \ W` (`Babai.extendPartition`).
Word for word `Babai.transferExtendFunc`, with `□X` replaced by `V X`. -/
noncomputable def transferExtendFuncOn
    (hsub : ∀ (X : Pt C) (Z : Pt (SplitOutcomes Ω)), Good X Z → Z.car ⊆ V X) :
    Func ((PairCatOf C (SplitOutcomes Ω) Good).full (fun _ r => (r.snd).isLeft))
      (SplitOutcomes Ω) where
  obj r := ⟨V (pairFst ⟨r.car, r.obj.1⟩),
    Sum.inl (extendPartition (V (pairFst ⟨r.car, r.obj.1⟩)) r.obj.1.sub
      (r.obj.1.snd.getLeft r.obj.2))⟩
  map {p q} f :=
    let f' : Hom (PairCatOf C (SplitOutcomes Ω) Good)
      ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩ := ⟨f.1, f.2⟩
    let fc : Hom C (pairFst (⟨p.car, p.obj.1⟩ : Pt (PairCatOf C (SplitOutcomes Ω) Good)))
      (pairFst (⟨q.car, q.obj.1⟩ : Pt (PairCatOf C (SplitOutcomes Ω) Good))) :=
      ⟨f.1, f.2.1⟩
    ⟨restrictEquivOn hVsub hViso fc,
      extendPartition.mem_iso (hsub _ _ p.obj.1.good) (hsub _ _ q.obj.1.good)
        (restrictEquivOn hVsub hViso fc)
        (pairSndMap f') (fun x => pairSndMap_spec f' x)
        (Cat.sum_iso_left p.obj.2 q.obj.2 (pairSndMap_mem f'))⟩
  map_id _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)
  map_trans _ _ := Subtype.ext (Equiv.ext fun _ => Subtype.ext rfl)

theorem transferExtendFuncOn_isCanonicalEmbedding
    (hsub : ∀ (X : Pt C) (Z : Pt (SplitOutcomes Ω)), Good X Z → Z.car ⊆ V X) :
    (transferExtendFuncOn C Good V hVsub hViso hsub).IsCanonicalEmbedding where
  car_subset _ := hVsub _
  map_restrict _ _ := rfl

/-- The transfer on the branch where the previous step returned a Johnson scheme: keep it.
This is `Babai.transferKeepFunc`; it does not mention the set to be split. -/
noncomputable def transferKeepFuncOn :
    Func ((PairCatOf C (SplitOutcomes Ω) Good).full (fun _ r => ¬ (r.snd).isLeft))
      (SplitOutcomes Ω) :=
  (Cat.fullIncl (PairCatOf C (SplitOutcomes Ω) Good) _).comp
    (pairSndFunc C (SplitOutcomes Ω) Good)

omit [Fintype Ω] [DecidableEq Ω] in
theorem transferKeepFuncOn_isCanonicalEmbedding :
    (transferKeepFuncOn C Good).IsCanonicalEmbedding :=
  Func.IsCanonicalEmbedding.comp
    (Cat.fullIncl_isCanonicalEmbedding _ _) (pairSndFunc_isCanonicalEmbedding _ _ _)

variable {C Good V}

include hVsub hViso in
/-- The transfer clause of Lemma 9.3.1 as a canonical construction, at multiplicative cost
`1`, **for a set to be split that need not be the whole point set**: if the previous step
found a solution for a threshold `γ` and a subset `W ⊆ V X` with `γ|W| = β|V X|`, then
objective (a) or (b) for `(β, V X)` is found canonically.

`Babai.transfer_finds` is the case `V X = □X`; the proof is the same, and the two branches
are `Babai.transferExtendFuncOn` and `Babai.transferKeepFuncOn`. -/
theorem transfer_finds_on (β : Pt C → ℝ) (hβ : ∀ X : Pt C, 1 / 2 ≤ β X)
    (hGood : ∀ (X : Pt C) (Z : Pt (SplitOutcomes Ω)), Good X Z →
      ∃ (γ : ℝ) (W : Set Ω), W ⊆ V X ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ) = β X * ((V X).ncard : ℝ) ∧ IsSplitOutcome γ W Z) :
    FindsAtMultCost (PairCatOf C (SplitOutcomes Ω) Good) (SplitOutcomes Ω) (fun _ => 1)
      (fun r Z => IsSplitOutcome (β (pairFst r)) (V (pairFst r)) Z) := by
  classical
  have hsub : ∀ (X : Pt C) (Z : Pt (SplitOutcomes Ω)), Good X Z → Z.car ⊆ V X := by
    intro X Z hZ
    obtain ⟨γ, W, hWsub, -, -, hsplit⟩ := hGood X Z hZ
    rcases hZs : Z.obj with P | J
    · rw [IsSplitOutcome, hZs] at hsplit
      exact hsplit.1 ▸ hWsub
    · rw [IsSplitOutcome, hZs] at hsplit
      exact hsplit.1.trans hWsub
  refine (FindsAtMultCost.cases (P := fun _ r => (r.snd).isLeft) (costp := fun _ => 1)
    (costn := fun _ => 1)
    (Good := fun r Z => IsSplitOutcome (β (pairFst r)) (V (pairFst r)) Z)
    (fun {X Y} h hp => pairSnd_isLeft_iso h hp) ?_ ?_).mono (fun _ => le_of_eq (max_self 1))
      (fun _ _ h => h)
  · -- objective (a): extend the partition by the block `V X \ W`
    refine FindsAtMultCost.of_canonicalEmbedding
      (transferExtendFuncOn C Good V hVsub hViso hsub)
      (transferExtendFuncOn_isCanonicalEmbedding C Good V hVsub hViso hsub) (fun r => ?_)
    obtain ⟨γ, W, hWsub, hγ1, hγβ, hsplit⟩ := hGood _ _ r.obj.1.good
    set P := r.obj.1.snd.getLeft r.obj.2 with hP
    have hs : r.obj.1.snd = Sum.inl P := Sum.eq_left_getLeft_of_isLeft r.obj.2
    rw [IsSplitOutcome, hs] at hsplit
    obtain ⟨hcarW, hPγ⟩ := hsplit
    have hsubW : r.obj.1.sub = W := hcarW
    refine ⟨rfl, ?_⟩
    subst hsubW
    exact extendPartition.isAlphaPartition (hsub _ _ r.obj.1.good) (Fintype.ofFinite _)
      (Fintype.ofFinite _) P hγ1 (hβ _) hγβ hPγ
  · -- objective (b): keep the Johnson scheme
    refine FindsAtMultCost.of_canonicalEmbedding (transferKeepFuncOn C Good)
      (transferKeepFuncOn_isCanonicalEmbedding C Good) (fun r => ?_)
    obtain ⟨γ, W, hWsub, hγ1, hγβ, hsplit⟩ := hGood _ _ r.obj.1.good
    set J := r.obj.1.snd.getRight (Sum.not_isLeft.mp r.obj.2) with hJ
    have hs : r.obj.1.snd = Sum.inr J :=
      Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp r.obj.2)
    have hgoal : (transferKeepFuncOn C Good).obj r = ⟨r.obj.1.sub, Sum.inr J⟩ := by
      rw [← hs]; rfl
    rw [IsSplitOutcome, hs] at hsplit
    obtain ⟨hsubW, hle⟩ := hsplit
    rw [IsSplitOutcome, hgoal]
    exact ⟨hsubW.trans hWsub, hγβ ▸ hle⟩

end TransferOn

end Babai
