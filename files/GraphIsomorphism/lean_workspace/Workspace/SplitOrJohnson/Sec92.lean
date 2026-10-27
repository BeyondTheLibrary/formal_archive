/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.2: Theorem 9.2.1 (UPCC Split-or-Johnson) and Theorem 9.2.3 (Extended Design
Lemma).
-/
import Workspace.SplitOrJohnson.ExtendedDesign
import Workspace.SplitOrJohnson.Turn
import Workspace.DesignLemma.Reduction
import Workspace.Functors.PairProj
import Workspace.Functors.SumProj

/-!
# §9.2 Theorems 9.2.1 and 9.2.3

Version 2.5, lines 4013–4035 of `babai-gi-source/quasi25.txt`.

The two theorems stand here rather than in `Workspace/SplitOrJohnson/Main.lean` because
they are proved from Lemma 9.3.1 (§9.3), which is built on top of that file.

| Paper | Lean |
|---|---|
| Theorem 9.2.1 (UPCC Split-or-Johnson), on the inputs that carry `β` | `Babai.theorem_9_2_1` |
| Theorem 9.2.1 for a fixed `β`: the printed statement | `Babai.theorem_9_2_1_at` |
| Lemma 9.3.1 on the inputs that carry `β` | `Babai.lemma_9_3_1_thr` |
| the transfer of a solution for `X̄` to one for `X`, as a functor | `Babai.transfer_finds` |
| Theorem 9.2.3 (Extended Design Lemma) | `Babai.theorem_9_2_3` |
| Theorem 9.2.3 from the Design Lemma in the form of §6 | `Babai.theorem_9_2_3_of_designLemma` |
| *"`β = αn/|C|`"*, outcome (c) as an input of Thm. 9.2.1 | `Babai.designStage2Thr` |

## The threshold parameter as object data

Theorem 9.2.1 is stated on `Babai.UPCCInputs`, the category of UPCCs that carry their
threshold parameter `β` as data; `Babai.theorem_9_2_1_at` is the printed statement, on the
category `Babai.UPCCs` of UPCCs with `β` a parameter of the statement, and it follows by
composing with `Babai.upccAttachBeta`.  The reason is the one recorded in the corrected paper
for Theorem 9.2.3: the `β` that Theorem 9.2.3 hands to Theorem 9.2.1 is `β = αn/|C|`, a
function of the input.  The parenthetical *"(The time bounds do not depend on `β`.)"* is
the quantifier over the cost function `q` standing outside — here automatically, since `q`
does not see `β` at all.

## The route of the proof of Theorem 9.2.1

The paper proves Theorem 9.2.1 by Lemma 9.3.1 followed by Theorem 9.2.2.  In the language
of §6 this is a chain of three canonical reductions:

1. `Babai.lemma_9_3_1_thr`, at multiplicative cost `n`: individualize one vertex, and
   either return a colored `β`-partition of `V` or return the semiregular bipartite graph
   `X̄` with its threshold parameter `α = βn/d₂`.
2. On the pairs *(input, outcome of step 1)*, a canonical case distinction
   (`Babai.FindsAtMultCost.cases`): if step 1 returned a partition, return it, at cost `1`;
   if it returned `X̄`, apply Theorem 9.2.2 to `X̄`, at quasipolynomial cost.
3. On the pairs *(step 2's input, the object step 2 found)*, at cost `1`: carry the
   solution back to `V`.  This is the transfer clause of Lemma 9.3.1
   (`Babai.lemma_9_3_1_transfer`) made into a functor: a Johnson scheme is kept as it is,
   and a colored partition of `W` is extended by the single block `V \ W`
   (`Babai.extendPartition`).

The two links of the chain are `Babai.FindsAtMultCost.comp_dep`, which lets a later step
see the input of an earlier one, as step 3 must.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]


/-! ### Step 1: Lemma 9.3.1 on the inputs that carry their threshold -/

/-- Lemma 9.3.1 (`Babai.lemma_9_3_1`) on the category `Babai.UPCCInputs`, whose objects
carry their threshold parameter `β`.

Nothing changes in the proof: the family of outcomes of Lemma 9.3.1 is built from the
coloring, the individualized vertex and `β` alone (`Babai.upccOutcome`), so it can be read
off each object separately; a morphism of `UPCCInputs` keeps `β`, so the equivariance of
the family (`Babai.upccOutcome_iso`) applies verbatim. -/
theorem lemma_9_3_1_thr :
    FindsAtMultCost (UPCCInputs Ω) (Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω))
      (fun X => X.car.ncard)
      (fun X Z => IsUPCCToBipOutcome (UPCCInputs.beta X) (upccThrForget.obj X) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => Set.range fun x : ↥X.car => upccOutcome (UPCCInputs.beta X) X.obj.1.1 x)
    (fun X => ?_) (fun X => Set.finite_range _) (fun X => ?_) (fun {X Y f} hf Z hZ => ?_)
    (fun X Z hZ => ?_)
  · -- a UPCC has a vertex, so there is at least one outcome
    have h2 := upcc_two_le_ncard X.obj.2.2.2
    obtain ⟨x, hx⟩ : X.car.Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    exact ⟨_, ⟨x, hx⟩, rfl⟩
  · -- at most `n` outcomes: one for each vertex
    show (Set.range fun x : ↥X.car => upccOutcome (UPCCInputs.beta X) X.obj.1.1 x).ncard
      ≤ X.car.ncard
    rw [← Set.image_univ]
    have h1 := Set.ncard_image_le (s := (Set.univ : Set ↥X.car))
      (f := fun x : ↥X.car => upccOutcome (UPCCInputs.beta X) X.obj.1.1 x) Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_coe_set_eq] at h1
  · obtain ⟨x, rfl⟩ := hZ
    have hβ : UPCCInputs.beta X = UPCCInputs.beta Y := hf.1
    have hiso : f ∈ (UPCCs Ω).IsoP (upccThrForget.obj X) (upccThrForget.obj Y) := hf.2
    have key := upccOutcome_iso (Ω := Ω) (UPCCInputs.beta X) X.obj.2.1 hiso x
    refine ⟨upccOutcome (UPCCInputs.beta Y) Y.obj.1.1 (f x), ⟨f x, rfl⟩, ?_⟩
    rw [← hβ]
    exact key
  · obtain ⟨x, rfl⟩ := hZ
    exact upccOutcome_good (Ω := Ω) (UPCCInputs.beta X) X.obj.2.1
      (upccThrForget.obj X) x

/-! ### A monotone quasipolynomial bound

Step 2 applies Theorem 9.2.2 to a graph living on a **subset** of the vertex set, so its
cost `q(|V₁|)` has to be bounded by `q(n)`.  Every quasipolynomial function is below a
monotone one of the same kind, namely the bound `2^{(log₂ n + 2)^c}` itself. -/

/-- Every quasipolynomially bounded function is bounded by a monotone quasipolynomially
bounded one. -/
theorem quasiPolyBound_exists_monotone {q : ℕ → ℕ} (hq : RAM.QuasiPolyBound q) :
    ∃ q' : ℕ → ℕ, RAM.QuasiPolyBound q' ∧ Monotone q' ∧ ∀ n, q n ≤ q' n := by
  obtain ⟨c, hc⟩ := hq
  refine ⟨fun n => 2 ^ ((Nat.log 2 n + 2) ^ c), ⟨c, fun _ => le_rfl⟩, ?_, hc⟩
  intro m n hmn
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_left (by simpa using Nat.log_mono_right hmn) c)


/-! ### The transfer of a solution, as a canonical construction

Both Theorem 9.2.1 and Theorem 9.2.3 end the same way.  A subset `W` of the vertex set `V`
has been produced, with a threshold `γ` for `W` such that `γ|W| = β|V|`, and the previous
step has found a solution for `(γ, W)`; the solution has to be carried to `V`.  The paper
does this in the transfer clause of Lemma 9.3.1: a Johnson scheme on a subset of `W` is
already large enough, since `γ|W| = β|V|`, and a colored `γ`-partition of `W` becomes a
colored `β`-partition of `V` when `V \ W` is added as one block of a new color.

`Babai.lemma_9_3_1_transfer` says that a solution exists; §6 needs the solution to be a
**functor** of the input, which is what this section provides. -/

section Transfer

variable (C : Cat.{0, 0} Ω) (Good : Pt C → Pt (SplitOutcomes Ω) → Prop)

/-- The transfer on the branch where the previous step returned a colored partition of
`W`: extend it to `V` by the single block `V \ W` (`Babai.extendPartition`).  It is
canonical by `Babai.extendPartition.mem_iso`. -/
noncomputable def transferExtendFunc :
    Func ((PairCatOf C (SplitOutcomes Ω) Good).full (fun _ r => (r.snd).isLeft))
      (SplitOutcomes Ω) where
  obj r := ⟨r.car,
    Sum.inl (extendPartition r.car r.obj.1.sub (r.obj.1.snd.getLeft r.obj.2))⟩
  map {p q} f :=
    let f' : Hom (PairCatOf C (SplitOutcomes Ω) Good)
      ⟨p.car, p.obj.1⟩ ⟨q.car, q.obj.1⟩ := ⟨f.1, f.2⟩
    ⟨f.1, extendPartition.mem_iso p.obj.1.sub_subset q.obj.1.sub_subset f.1
      (pairSndMap f') (fun x => pairSndMap_spec f' x)
      (Cat.sum_iso_left p.obj.2 q.obj.2 (pairSndMap_mem f'))⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem transferExtendFunc_isCanonicalEmbedding :
    (transferExtendFunc C Good).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- The transfer on the branch where the previous step returned a Johnson scheme: keep
it. -/
noncomputable def transferKeepFunc :
    Func ((PairCatOf C (SplitOutcomes Ω) Good).full (fun _ r => ¬ (r.snd).isLeft))
      (SplitOutcomes Ω) :=
  (Cat.fullIncl (PairCatOf C (SplitOutcomes Ω) Good) _).comp
    (pairSndFunc C (SplitOutcomes Ω) Good)

theorem transferKeepFunc_isCanonicalEmbedding :
    (transferKeepFunc C Good).IsCanonicalEmbedding :=
  Func.IsCanonicalEmbedding.comp
    (Cat.fullIncl_isCanonicalEmbedding _ _) (pairSndFunc_isCanonicalEmbedding _ _ _)

variable {C Good}

/-- The transfer clause of Lemma 9.3.1 as a canonical construction, at multiplicative cost
`1`: if the previous step found a solution for a threshold `γ` and a subset `W ⊆ V` with
`γ|W| = β|V|`, then objective (a) or (b) for `(β, V)` is found canonically.

Objective (b) is kept as it is: the Johnson scheme sits on a subset of `W` of size
`≥ γ|W| = β|V|`.  Objective (a) is extended by the block `V \ W`, which has
`|V| − |W| ≤ (1 − β)|V| ≤ β|V|` elements because `γ ≤ 1` and `β ≥ 1/2`
(`Babai.extendPartition.isAlphaPartition`). -/
theorem transfer_finds (β : Pt C → ℝ) (hβ : ∀ X : Pt C, 1 / 2 ≤ β X)
    (hGood : ∀ (X : Pt C) (Z : Pt (SplitOutcomes Ω)), Good X Z →
      ∃ (γ : ℝ) (W : Set Ω), W ⊆ X.car ∧ γ ≤ 1 ∧
        γ * (W.ncard : ℝ) = β X * (X.car.ncard : ℝ) ∧ IsSplitOutcome γ W Z) :
    FindsAtMultCost (PairCatOf C (SplitOutcomes Ω) Good) (SplitOutcomes Ω) (fun _ => 1)
      (fun r Z => IsSplitOutcome (β (pairFst r)) (pairFst r).car Z) := by
  refine (FindsAtMultCost.cases (P := fun _ r => (r.snd).isLeft) (costp := fun _ => 1)
    (costn := fun _ => 1)
    (Good := fun r Z => IsSplitOutcome (β (pairFst r)) (pairFst r).car Z)
    (fun {X Y} h hp => pairSnd_isLeft_iso h hp) ?_ ?_).mono (fun _ => le_of_eq (max_self 1))
      (fun _ _ h => h)
  · -- objective (a): extend the partition by the block `V \ W`
    refine FindsAtMultCost.of_canonicalEmbedding (transferExtendFunc C Good)
      (transferExtendFunc_isCanonicalEmbedding C Good) (fun r => ?_)
    obtain ⟨γ, W, hWsub, hγ1, hγβ, hsplit⟩ := hGood _ _ r.obj.1.good
    set P := r.obj.1.snd.getLeft r.obj.2 with hP
    have hs : r.obj.1.snd = Sum.inl P := Sum.eq_left_getLeft_of_isLeft r.obj.2
    rw [hs] at hsplit
    obtain ⟨hcarW, hPγ⟩ := hsplit
    have hsubW : r.obj.1.sub = W := hcarW
    refine ⟨rfl, ?_⟩
    subst hsubW
    exact extendPartition.isAlphaPartition r.obj.1.sub_subset (Fintype.ofFinite _)
      (Fintype.ofFinite _) P hγ1 (hβ _) hγβ hPγ
  · -- objective (b): keep the Johnson scheme
    refine FindsAtMultCost.of_canonicalEmbedding (transferKeepFunc C Good)
      (transferKeepFunc_isCanonicalEmbedding C Good) (fun r => ?_)
    obtain ⟨γ, W, hWsub, hγ1, hγβ, hsplit⟩ := hGood _ _ r.obj.1.good
    set J := r.obj.1.snd.getRight (Sum.not_isLeft.mp r.obj.2) with hJ
    have hs : r.obj.1.snd = Sum.inr J :=
      Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp r.obj.2)
    have hgoal : (transferKeepFunc C Good).obj r = ⟨r.obj.1.sub, Sum.inr J⟩ := by
      rw [← hs]; rfl
    rw [hs] at hsplit
    obtain ⟨hsubW, hle⟩ := hsplit
    rw [hgoal]
    exact ⟨hsubW.trans hWsub, hγβ ▸ hle⟩

end Transfer

/-! ### The three steps of the proof of Theorem 9.2.1 -/

/-- The outcome category of Lemma 9.3.1: a colored partition of `V`, or an admissible
input of Theorem 9.2.2 (with its own threshold parameter). -/
abbrev UpccBipSum (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  Cat.sum (ColoredPartitions Ω ℕ) (BipInputs Ω)

/-- The category of pairs *(input of Theorem 9.2.1, outcome of Lemma 9.3.1)*, on which
steps 2 and 3 live. -/
abbrev UpccPairs (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  PairCatOf (UPCCInputs Ω) (UpccBipSum Ω)
    (fun X Z => IsUPCCToBipOutcome (UPCCInputs.beta X) (upccThrForget.obj X) Z)

/-- What step 2 guarantees: a solution of the corresponding part of Theorem 9.2.2 for the
instance that Lemma 9.3.1 produced, together with the two numbers — the threshold `α` and
the set `W` to be split — for which Lemma 9.3.1 promises `α|W| = βn`.

The two numbers are existentially quantified rather than read off the outcome of step 1,
because that is all the transfer of step 3 uses; they are `(β, V)` when Lemma 9.3.1
achieved objective (a) and `(α, V₁)` when it produced the bipartite graph `X̄`. -/
def UpccStage2 (p : Pt (UpccPairs Ω)) (Z : Pt (SplitOutcomes Ω)) : Prop :=
  ∃ (α : ℝ) (W : Set Ω), W ⊆ p.car ∧ α ≤ 1 ∧
    α * (W.ncard : ℝ) = UPCCInputs.beta (pairFst p) * (p.car.ncard : ℝ) ∧
    IsSplitOutcome α W Z

/-- The case distinction of step 2: Lemma 9.3.1 achieved objective (a), i.e. it returned a
colored `β`-partition of `V`. -/
def upccIsPart : ∀ s : Set Ω, (UpccPairs Ω).Obj s → Prop := fun _ p => p.snd.isLeft

/-- "Lemma 9.3.1 returned a colored partition" is invariant under isomorphism: there are no
morphisms between the two summands of `Babai.Cat.sum`. -/
theorem upccIsPart_iso {p q : Pt (UpccPairs Ω)} (h : ((UpccPairs Ω).IsoP p q).Nonempty)
    (hp : upccIsPart p.car p.obj) : upccIsPart q.car q.obj := by
  obtain ⟨f, -, g, -, hH⟩ := h
  show (q.obj.snd).isLeft
  have hp' : (p.obj.snd).isLeft := hp
  rcases hps : p.obj.snd with P | Y
  · rcases hqs : q.obj.snd with Q | Y'
    · simp
    · rw [hps, hqs] at hH
      exact absurd hH (Set.notMem_empty g)
  · rw [hps] at hp'
    simp at hp'

/-! #### Step 2 -/

/-- Step 2 on the branch where Lemma 9.3.1 achieved objective (a): the colored
`β`-partition it returned, as an outcome of Theorem 9.2.1.  Nothing is computed; the
functor is the projection to the object found, read in the first summand. -/
noncomputable def upccStage2Left :
    Func ((UpccPairs Ω).full upccIsPart) (SplitOutcomes Ω) :=
  (((Cat.fullIncl (UpccPairs Ω) upccIsPart).comp
      (pairSndFunc (UPCCInputs Ω) (UpccBipSum Ω) _)).intoFull
        (Cat.sumIsLeft (ColoredPartitions Ω ℕ) (BipInputs Ω))
        (fun X => X.obj.2)).comp
    ((Cat.sumLeftProj (ColoredPartitions Ω ℕ) (BipInputs Ω)).comp
      (Cat.sumLeftIncl (ColoredPartitions Ω ℕ) (JohnsonSchemes Ω)))

theorem upccStage2Left_isCanonicalEmbedding :
    (upccStage2Left (Ω := Ω)).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (UpccPairs Ω) upccIsPart)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    ((Cat.sumLeftProj_isCanonicalEmbedding _ _).comp
      (Cat.sumLeftIncl_isCanonicalEmbedding _ _))

/-- Step 2 on the branch where Lemma 9.3.1 produced the bipartite graph `X̄`: the
admissible input of Theorem 9.2.2 that it produced, as a functor. -/
noncomputable def upccStage2Right :
    Func ((UpccPairs Ω).full (fun s p => ¬ upccIsPart s p)) (BipInputs Ω) :=
  (((Cat.fullIncl (UpccPairs Ω) (fun s p => ¬ upccIsPart s p)).comp
      (pairSndFunc (UPCCInputs Ω) (UpccBipSum Ω) _)).intoFull
        (Cat.sumIsRight (ColoredPartitions Ω ℕ) (BipInputs Ω))
        (fun X => Sum.not_isLeft.mp X.obj.2)).comp
    (Cat.sumRightProj (ColoredPartitions Ω ℕ) (BipInputs Ω))

theorem upccStage2Right_isCanonicalEmbedding :
    (upccStage2Right (Ω := Ω)).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (UpccPairs Ω) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    (Cat.sumRightProj_isCanonicalEmbedding _ _)

/-! #### The two branches of step 2, and the two branches of step 3 -/

/-- Step 2 on the branch where Lemma 9.3.1 achieved objective (a): at multiplicative cost
`1`, the colored `β`-partition of `V` that Lemma 9.3.1 returned is already a solution of
Theorem 9.2.1, with the pair `(α, W) = (β, V)`. -/
theorem upccStage2_left_finds :
    FindsAtMultCost ((UpccPairs Ω).full upccIsPart) (SplitOutcomes Ω) (fun _ => 1)
      (fun p Z => UpccStage2 ⟨p.car, p.obj.1⟩ Z) := by
  refine FindsAtMultCost.of_canonicalEmbedding upccStage2Left
    upccStage2Left_isCanonicalEmbedding (fun p => ?_)
  refine ⟨UPCCInputs.beta (pairFst ⟨p.car, p.obj.1⟩), p.car, subset_rfl,
    le_of_lt (pairFst (⟨p.car, p.obj.1⟩ : Pt (UpccPairs Ω))).obj.2.2.1, rfl, ?_⟩
  set P := p.obj.1.snd.getLeft p.obj.2 with hP
  have hs : p.obj.1.snd = Sum.inl P := Sum.eq_left_getLeft_of_isLeft p.obj.2
  have hgood := p.obj.1.good
  rw [hs] at hgood
  exact hgood

/-- Step 2 on the branch where Lemma 9.3.1 produced the bipartite graph `X̄`: apply
Theorem 9.2.2 to `X̄`.  The pair `(α, W)` is the threshold parameter of `X̄` and its first
part `V₁`, for which Lemma 9.3.1 guarantees `α|V₁| = βn`. -/
theorem upccStage2_right_finds (q : ℕ → ℕ) (hmono : Monotone q)
    (h22 : FindsAtMultCost (BipInputs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
      (fun X Z => IsSplitOutcome (BipInputs.alpha X) (BipInputs.V₁ X) Z)) :
    FindsAtMultCost ((UpccPairs Ω).full (fun s p => ¬ upccIsPart s p)) (SplitOutcomes Ω)
      (fun p => q p.car.ncard) (fun p Z => UpccStage2 ⟨p.car, p.obj.1⟩ Z) := by
  refine (h22.precomp upccStage2Right upccStage2Right_isCanonicalEmbedding).mono
    (fun p => hmono (Set.ncard_le_ncard p.obj.1.sub_subset (Set.toFinite _)))
    (fun p Z hZ => ?_)
  set Y := p.obj.1.snd.getRight (Sum.not_isLeft.mp p.obj.2) with hY
  have hs : p.obj.1.snd = Sum.inr Y :=
    Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp p.obj.2)
  have hgood := p.obj.1.good
  rw [hs] at hgood
  obtain ⟨-, -, -, hα1, hαβ⟩ := hgood
  refine ⟨BipInputs.alpha (upccStage2Right.obj p), BipInputs.V₁ (upccStage2Right.obj p),
    (Subtype.coe_image_subset _ _).trans p.obj.1.sub_subset, hα1, ?_, hZ⟩
  have hcard : (BipInputs.V₁ (upccStage2Right.obj p)).ncard = (Y.1.1.V₁).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  rw [hcard]
  exact hαβ

/-! ### Theorem 9.2.1 -/

/-- Theorem 9.2.1 (UPCC Split-or-Johnson).  *"Let `X = (V; R₁,…,R_r)` be a UPCC with `n`
vertices and let `2/3 ≤ β < 1` be a threshold parameter.  Then at quasipolynomial
multiplicative cost we can find either (a) a canonical colored `β`-partition of `V`, or
(b) a canonically embedded nontrivial Johnson scheme on a subset of `V` of size `≥ βn`.
(The time bounds do not depend on `β`.)"*  (Version 2.5, lines 4013–4018.)

The input category is `Babai.UPCCInputs`, the UPCCs that carry their threshold parameter
`β` as data, with `2/3 ≤ β < 1` part of the admissibility condition; `β` is then
`Babai.UPCCInputs.beta X`.  For a fixed `β` this is the printed statement, which is
`Babai.theorem_9_2_1_at`.

`n` is the number of vertices of the input, so the cost bound is `q(n)` with `q`
quasipolynomial, and the size condition of (b) is `|W| ≥ βn`, both inside
`FindsAtMultCost` and `IsSplitOutcome`. -/
theorem theorem_9_2_1 :
    ∃ q : ℕ → ℕ, RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω],
      FindsAtMultCost (UPCCInputs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
        (fun X Z => IsSplitOutcome (UPCCInputs.beta X) X.car Z) := by
  obtain ⟨q, hq, h22⟩ := theorem_9_2_2
  obtain ⟨q', hq', hmono, hqq'⟩ := quasiPolyBound_exists_monotone hq
  refine ⟨fun n => n * (1 + q' n),
    RAM.QuasiPolyBound.mul RAM.polyBound_id.quasiPoly
      ((RAM.polyBound_const 1).quasiPoly.add hq'), ?_⟩
  intro Ω _ _
  have h22' : FindsAtMultCost (BipInputs Ω) (SplitOutcomes Ω) (fun X => q' X.car.ncard)
      (fun X Z => IsSplitOutcome (BipInputs.alpha X) (BipInputs.V₁ X) Z) :=
    (h22 Ω).mono (fun X => hqq' _) (fun _ _ h => h)
  -- Step 2: a canonical case distinction on the outcome of Lemma 9.3.1.
  have h2 := FindsAtMultCost.cases (C := UpccPairs Ω) (P := upccIsPart)
    (costp := fun _ => 1) (costn := fun p => q' p.car.ncard) (Good := UpccStage2)
    (fun {X Y} h hp => upccIsPart_iso h hp)
    upccStage2_left_finds (upccStage2_right_finds q' hmono h22')
  -- Step 3: the transfer, a canonical case distinction on what step 2 found.
  have h3 := transfer_finds (C := UpccPairs Ω) (Good := UpccStage2)
    (fun p => UPCCInputs.beta (pairFst p)) (fun p => by
      have h : (2 : ℝ) / 3 ≤ UPCCInputs.beta (pairFst p) := (pairFst p).obj.2.1
      linarith)
    (fun p Z h => h)
  -- Steps 2 and 3, then step 1: the multiplicative costs multiply.
  have h23 := h2.comp_dep h3 (c₂' := fun _ => 1) (fun r => le_rfl)
  have h := (lemma_9_3_1_thr (Ω := Ω)).comp_dep h23
    (c₂' := fun X => max 1 (q' X.car.ncard) * 1) (fun p => le_rfl)
  refine h.mono (fun X => ?_) (fun X Z hZ => ?_)
  · refine Nat.mul_le_mul_left _ ?_
    show max 1 (q' X.car.ncard) * 1 ≤ 1 + q' X.car.ncard
    omega
  · obtain ⟨p, hp, r, hr, hgood⟩ := hZ
    have h1 : IsSplitOutcome (UPCCInputs.beta (pairFst (pairFst r)))
        (pairFst (pairFst r)).car Z := hgood
    rw [hr, hp] at h1
    exact h1

/-- Theorem 9.2.1 for a **fixed** threshold parameter `β`: the printed statement, on the
category `Babai.UPCCs` of UPCCs.  It is `theorem_9_2_1` composed with
`Babai.upccAttachBeta`, the functor that attaches the constant `β` to a UPCC; that functor
does not move the underlying set and is the identity on morphisms, so the cost and the
property found are literally the same.

The quantifier over the cost function `q` stands outside the quantifier over `β`: this is
the paper's *"(The time bounds do not depend on `β`.)"* -/
theorem theorem_9_2_1_at :
    ∃ q : ℕ → ℕ, RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (β : ℝ), 2 / 3 ≤ β → β < 1 →
        FindsAtMultCost (UPCCs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
          (fun X Z => IsSplitOutcome β X.car Z) := by
  obtain ⟨q, hq, h⟩ := theorem_9_2_1
  exact ⟨q, hq, fun Ω _ _ β hβ hβ1 =>
    (h Ω).precomp (upccAttachBeta β hβ hβ1) (upccAttachBeta_isCanonicalEmbedding β hβ hβ1)⟩

/-! ### Theorem 9.2.3 from the Design Lemma

*"Combining the Design Lemma and Theorem 9.2.1 we obtain our overall combinatorial
partitioning tool"* (version 2.5, line 4027).  This section is that combination: it proves
Theorem 9.2.3 **from** the Design Lemma in the form of §6, that is, from a reduction at
multiplicative cost `n^k` finding an outcome of Theorem 8.1.2 (`Babai.DesignOutcomes`,
`Babai.IsDesignOutcome`).  That restatement is `Babai.designLemma_finds`
(`Workspace/DesignLemma/Reduction.lean`).

The chain is the same as for Theorem 9.2.1: the Design Lemma, then a canonical case
distinction on its outcome — outcomes (a) and (b) are already a colored `α`-partition of
`Ω`, outcome (c) hands the UPCC on the dominant class `C` to Theorem 9.2.1 at the
threshold `β = αn/|C|` (`Babai.designBeta`) — then the transfer `Babai.transfer_finds`. -/

/-- A UPCC together with a threshold parameter read off the object it comes from, as an
admissible input of Theorem 9.2.1.  The threshold has to be invariant under the morphisms
of the source category, which is what `hβ` says; for Theorem 9.2.3 it is `β = αn/|C|`, a
function of the two cardinalities. -/
def Func.withUpccParam {A : Cat.{0, 0} Ω} (F : Func A (UPCCs Ω)) (β : Pt A → ℝ)
    (hβ : ∀ {X Y : Pt A}, Hom A X Y → β X = β Y)
    (hadm : ∀ X : Pt A, 2 / 3 ≤ β X ∧ β X < 1) : Func A (UPCCInputs Ω) where
  obj X := ⟨(F.obj X).car,
    ⟨((F.obj X).obj.1, β X), ⟨(hadm X).1, (hadm X).2, (F.obj X).obj.2⟩⟩⟩
  map f := ⟨(F.map f).1, ⟨hβ f, (F.map f).2⟩⟩
  map_id X := by
    apply Subtype.ext
    have h : (F.map (Hom.id X)).1 = (Hom.id (F.obj X)).1 :=
      congrArg Subtype.val (F.map_id X)
    exact h
  map_trans f g := by
    apply Subtype.ext
    have h : (F.map (f.trans g)).1 = ((F.map f).trans (F.map g)).1 :=
      congrArg Subtype.val (F.map_trans f g)
    exact h

omit [Fintype Ω] [DecidableEq Ω] in
theorem Func.withUpccParam_isCanonicalEmbedding {A : Cat.{0, 0} Ω} {F : Func A (UPCCs Ω)}
    (hF : F.IsCanonicalEmbedding) (β : Pt A → ℝ)
    (hβ : ∀ {X Y : Pt A}, Hom A X Y → β X = β Y)
    (hadm : ∀ X : Pt A, 2 / 3 ≤ β X ∧ β X < 1) :
    (F.withUpccParam β hβ hadm).IsCanonicalEmbedding where
  car_subset X := hF.car_subset X
  map_restrict f x := hF.map_restrict f x

/-- The category of pairs *(input of Theorem 9.2.3, outcome of the Design Lemma)*. -/
abbrev DesignPairs (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ) : Cat.{0, 0} Ω :=
  PairCatOf (KAryInputs Ω k α) (DesignOutcomes Ω) (fun X Z => IsDesignOutcome α X.car Z)

/-- The case distinction after the Design Lemma: outcome (a) or (b), a canonical coloring
of `Ω`, as opposed to outcome (c), the UPCC on the dominant class. -/
def designIsPart (k : ℕ) (α : ℝ) : ∀ s : Set Ω, (DesignPairs Ω k α).Obj s → Prop :=
  fun _ p => p.snd.isLeft

/-- What the step after the Design Lemma guarantees: a solution for some threshold `γ` and
some subset `W` with `γ|W| = αn`, which the transfer `Babai.transfer_finds` turns into a
solution of Theorem 9.2.3.  For outcomes (a) and (b) the pair is `(α, Ω)`, for outcome (c)
it is `(αn/|C|, C)`. -/
def DesignStage2 (k : ℕ) (α : ℝ) (p : Pt (DesignPairs Ω k α)) (Z : Pt (SplitOutcomes Ω)) :
    Prop :=
  ∃ (γ : ℝ) (W : Set Ω), W ⊆ p.car ∧ γ ≤ 1 ∧
    γ * (W.ncard : ℝ) = α * (p.car.ncard : ℝ) ∧ IsSplitOutcome γ W Z

/-- Outcomes (a) and (b) of the Design Lemma: the canonical colored `α`-partition of `Ω`,
as an outcome of Theorem 9.2.3. -/
noncomputable def designStage2Left (k : ℕ) (α : ℝ) :
    Func ((DesignPairs Ω k α).full (designIsPart k α)) (SplitOutcomes Ω) :=
  (((Cat.fullIncl (DesignPairs Ω k α) (designIsPart k α)).comp
      (pairSndFunc (KAryInputs Ω k α) (DesignOutcomes Ω) _)).intoFull
        (Cat.sumIsLeft (ColoredPartitions Ω ℕ) (UPCCs Ω)) (fun X => X.obj.2)).comp
    ((Cat.sumLeftProj (ColoredPartitions Ω ℕ) (UPCCs Ω)).comp
      (Cat.sumLeftIncl (ColoredPartitions Ω ℕ) (JohnsonSchemes Ω)))

theorem designStage2Left_isCanonicalEmbedding (k : ℕ) (α : ℝ) :
    (designStage2Left (Ω := Ω) k α).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (DesignPairs Ω k α) (designIsPart k α))
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    ((Cat.sumLeftProj_isCanonicalEmbedding _ _).comp
      (Cat.sumLeftIncl_isCanonicalEmbedding _ _))

/-- Outcome (c) of the Design Lemma: the UPCC on the dominant class. -/
noncomputable def designStage2Upcc (k : ℕ) (α : ℝ) :
    Func ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p)) (UPCCs Ω) :=
  (((Cat.fullIncl (DesignPairs Ω k α) (fun s p => ¬ designIsPart k α s p)).comp
      (pairSndFunc (KAryInputs Ω k α) (DesignOutcomes Ω) _)).intoFull
        (Cat.sumIsRight (ColoredPartitions Ω ℕ) (UPCCs Ω))
        (fun X => Sum.not_isLeft.mp X.obj.2)).comp
    (Cat.sumRightProj (ColoredPartitions Ω ℕ) (UPCCs Ω))

theorem designStage2Upcc_isCanonicalEmbedding (k : ℕ) (α : ℝ) :
    (designStage2Upcc (Ω := Ω) k α).IsCanonicalEmbedding :=
  (Func.intoFull_isCanonicalEmbedding (Func.IsCanonicalEmbedding.comp
      (Cat.fullIncl_isCanonicalEmbedding (DesignPairs Ω k α) _)
      (pairSndFunc_isCanonicalEmbedding _ _ _)) _ _).comp
    (Cat.sumRightProj_isCanonicalEmbedding _ _)

/-- Outcome (c) of the Design Lemma: the dominant class `C` is a subset of `Ω` with
`|C| > αn`.  (Theorem 8.1.2 (c) and `Babai.IsDesignOutcome`.) -/
theorem designPair_upcc_data {k : ℕ} {α : ℝ}
    (p : Pt ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p))) :
    p.obj.1.sub ⊆ p.car ∧ α * (p.car.ncard : ℝ) < (p.obj.1.sub.ncard : ℝ) := by
  have hgood := p.obj.1.good
  set U := p.obj.1.snd.getRight (Sum.not_isLeft.mp p.obj.2) with hU
  have hs : p.obj.1.snd = Sum.inr U :=
    Sum.eq_right_getRight_of_isRight (Sum.not_isLeft.mp p.obj.2)
  rw [hs] at hgood
  exact hgood

/-- The threshold `β = αn/|C|` is the same for isomorphic pairs: it is a function of the
two cardinalities `n = |Ω|` and `|C|`, and a morphism of pairs is a bijection of the
vertex sets carrying `C` onto `C'`. -/
theorem designBeta_hom_eq {k : ℕ} {α : ℝ}
    {X Y : Pt ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p))}
    (f : Hom ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p)) X Y) :
    designBeta α X.car X.obj.1.sub = designBeta α Y.car Y.obj.1.sub := by
  obtain ⟨-, g, -, -⟩ := f.2
  unfold designBeta
  rw [ncard_eq_of_equiv f.1, ncard_eq_of_equiv g]

/-- Outcome (c) of the Design Lemma, as an admissible input of Theorem 9.2.1: the UPCC on
the dominant class together with the threshold `β = αn/|C|`, which satisfies `2/3 ≤ β < 1`
by `Babai.designBeta_bounds`. -/
noncomputable def designStage2Thr (k : ℕ) (α : ℝ) (hα : 3 / 4 ≤ α) :
    Func ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p)) (UPCCInputs Ω) :=
  (designStage2Upcc k α).withUpccParam (fun p => designBeta α p.car p.obj.1.sub)
    (fun f => designBeta_hom_eq f)
    (fun p => designBeta_bounds hα (designPair_upcc_data p).1 (designPair_upcc_data p).2)

theorem designStage2Thr_isCanonicalEmbedding (k : ℕ) (α : ℝ) (hα : 3 / 4 ≤ α) :
    (designStage2Thr (Ω := Ω) k α hα).IsCanonicalEmbedding :=
  Func.withUpccParam_isCanonicalEmbedding (designStage2Upcc_isCanonicalEmbedding k α) _ _ _

/-- The step after the Design Lemma, on the branch of outcomes (a) and (b): at
multiplicative cost `1`, the canonical colored `α`-partition of `Ω` that the Design Lemma
returned is already a solution, with the pair `(γ, W) = (α, Ω)`. -/
theorem designStage2_left_finds (k : ℕ) (α : ℝ) (hα1 : α < 1) :
    FindsAtMultCost ((DesignPairs Ω k α).full (designIsPart k α)) (SplitOutcomes Ω)
      (fun _ => 1) (fun p Z => DesignStage2 k α ⟨p.car, p.obj.1⟩ Z) := by
  refine FindsAtMultCost.of_canonicalEmbedding (designStage2Left k α)
    (designStage2Left_isCanonicalEmbedding k α) (fun p => ?_)
  refine ⟨α, p.car, subset_rfl, le_of_lt hα1, rfl, ?_⟩
  set P := p.obj.1.snd.getLeft p.obj.2 with hP
  have hs : p.obj.1.snd = Sum.inl P := Sum.eq_left_getLeft_of_isLeft p.obj.2
  have hgood := p.obj.1.good
  rw [hs] at hgood
  exact hgood

/-- The step after the Design Lemma, on the branch of outcome (c): apply Theorem 9.2.1 to
the UPCC on the dominant class `C`, at the threshold `β = αn/|C|`.  The pair is
`(γ, W) = (αn/|C|, C)`, and `γ|W| = αn` is `Babai.designBeta_mul`. -/
theorem designStage2_right_finds (k : ℕ) (α : ℝ) (hα : 3 / 4 ≤ α) (q : ℕ → ℕ)
    (hmono : Monotone q)
    (h921 : FindsAtMultCost (UPCCInputs Ω) (SplitOutcomes Ω) (fun X => q X.car.ncard)
      (fun X Z => IsSplitOutcome (UPCCInputs.beta X) X.car Z)) :
    FindsAtMultCost ((DesignPairs Ω k α).full (fun s p => ¬ designIsPart k α s p))
      (SplitOutcomes Ω) (fun p => q p.car.ncard)
      (fun p Z => DesignStage2 k α ⟨p.car, p.obj.1⟩ Z) := by
  refine (h921.precomp (designStage2Thr k α hα)
    (designStage2Thr_isCanonicalEmbedding k α hα)).mono
    (fun p => hmono (Set.ncard_le_ncard p.obj.1.sub_subset (Set.toFinite _)))
    (fun p Z hZ => ?_)
  obtain ⟨hsub, hlt⟩ := designPair_upcc_data p
  have hα0 : (0 : ℝ) ≤ α := by linarith
  exact ⟨designBeta α p.car p.obj.1.sub, p.obj.1.sub, hsub,
    le_of_lt (designBeta_bounds hα hsub hlt).2, designBeta_mul hα0 hlt, hZ⟩

/-- Theorem 9.2.3 **from the Design Lemma in the form of §6**: given a reduction at
multiplicative cost `n^k` that finds an outcome of Theorem 8.1.2 canonically
(`Babai.DesignOutcomes`, `Babai.IsDesignOutcome`), Theorem 9.2.3 follows.

This is the combination the paper announces at line 4027; the hypothesis is exactly
Theorem 8.1.2 restated as a `Babai.FindsAtMultCost`, namely `Babai.designLemma_finds`.  The chain is: the Design Lemma, a canonical case distinction
on its outcome (outcomes (a) and (b) are a colored `α`-partition of `Ω`; outcome (c) goes
to Theorem 9.2.1 at the threshold `β = αn/|C|`), then the transfer
`Babai.transfer_finds`.  The cost is `n^k · max(1, q(n)) ≤ q'(n)·n^{1·k}` with
`q'(n) = 1 + q(n)` quasipolynomial. -/
theorem theorem_9_2_3_of_designLemma
    (hDL : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ), 3 / 4 ≤ α → α < 1 →
      FindsAtMultCost (KAryInputs Ω k α) (DesignOutcomes Ω) (fun X => X.car.ncard ^ k)
        (fun X Z => IsDesignOutcome α X.car Z)) :
    ∃ (q : ℕ → ℕ) (c : ℕ), RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ), 3 / 4 ≤ α → α < 1 →
        FindsAtMultCost (KAryInputs Ω k α) (SplitOutcomes Ω)
          (fun X => q X.car.ncard * X.car.ncard ^ (c * k))
          (fun X Z => IsSplitOutcome α X.car Z) := by
  obtain ⟨q, hq, h921⟩ := theorem_9_2_1
  obtain ⟨q', hq', hmono, hqq'⟩ := quasiPolyBound_exists_monotone hq
  refine ⟨fun n => 1 + q' n, 1, (RAM.polyBound_const 1).quasiPoly.add hq', ?_⟩
  intro Ω _ _ k α hα hα1
  have h921' : FindsAtMultCost (UPCCInputs Ω) (SplitOutcomes Ω) (fun X => q' X.car.ncard)
      (fun X Z => IsSplitOutcome (UPCCInputs.beta X) X.car Z) :=
    (h921 Ω).mono (fun X => hqq' _) (fun _ _ h => h)
  -- the canonical case distinction on the outcome of the Design Lemma
  have h2 := FindsAtMultCost.cases (C := DesignPairs Ω k α) (P := designIsPart k α)
    (costp := fun _ => 1) (costn := fun p => q' p.car.ncard) (Good := DesignStage2 k α)
    (fun {X Y} h hp => pairSnd_isLeft_iso h hp)
    (designStage2_left_finds k α hα1) (designStage2_right_finds k α hα q' hmono h921')
  -- the transfer of the solution to `Ω`
  have h3 := transfer_finds (C := DesignPairs Ω k α) (Good := DesignStage2 k α)
    (fun _ => α) (fun _ => by linarith) (fun p Z h => h)
  have h23 := h2.comp_dep h3 (c₂' := fun _ => 1) (fun r => le_rfl)
  have h := (hDL Ω k α hα hα1).comp_dep h23
    (c₂' := fun X => max 1 (q' X.car.ncard) * 1) (fun p => le_rfl)
  refine h.mono (fun X => ?_) (fun X Z hZ => ?_)
  · show X.car.ncard ^ k * (max 1 (q' X.car.ncard) * 1)
      ≤ (1 + q' X.car.ncard) * X.car.ncard ^ (1 * k)
    have h1 : max 1 (q' X.car.ncard) * 1 ≤ 1 + q' X.car.ncard := by omega
    calc X.car.ncard ^ k * (max 1 (q' X.car.ncard) * 1)
        ≤ X.car.ncard ^ k * (1 + q' X.car.ncard) := Nat.mul_le_mul_left _ h1
      _ = (1 + q' X.car.ncard) * X.car.ncard ^ (1 * k) := by
          rw [one_mul, Nat.mul_comm]
  · obtain ⟨p, hp, r, hr, hgood⟩ := hZ
    have h1 : IsSplitOutcome α (pairFst r).car Z := hgood
    have hcar : p.car = X.car := congrArg Pt.car hp
    rw [hr, hcar] at h1
    exact h1

/-! ### Theorem 9.2.3 -/

/-- Theorem 9.2.3 (Extended Design Lemma).  *"Let `3/4 ≤ α < 1` be a threshold parameter.
Let `X = (Ω, R)` be a `k`-ary relational structure with `n` vertices, `2 ≤ k ≤ n/4`, and
relative strong symmetry defect `> 1 - α`.  Then at a multiplicative cost of `q(n)n^{O(k)}`,
where `q(n)` is a quasipolynomial function, we can find either (a) a canonical colored
`α`-partition of the vertex set, or (b) a canonically embedded nontrivial Johnson scheme
on a subset `W ⊆ Ω` of size `|W| ≥ αn`.  (The time bounds do not depend on `α`.)"*
(Version 2.5, lines 4029–4035.)

`n^{O(k)}` is `n^(c*k)` for an absolute constant `c`, quantified — like `q` — outside `α`
and `k`, since the bound is uniform.  Both are also quantified outside the ambient type
`Ω`: they are absolute constants, so one pair `(q, c)` serves every ground set.  With `Ω`
fixed first the statement would say nothing, because for a fixed finite `Ω` a constant
function is a quasipolynomial bound on every input; see the entry on the absolute
constants in the corrected paper. -/
theorem theorem_9_2_3 :
    ∃ (q : ℕ → ℕ) (c : ℕ), RAM.QuasiPolyBound q ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (α : ℝ), 3 / 4 ≤ α → α < 1 →
        FindsAtMultCost (KAryInputs Ω k α) (SplitOutcomes Ω)
          (fun X => q X.car.ncard * X.car.ncard ^ (c * k))
          (fun X Z => IsSplitOutcome α X.car Z) := by
  -- `Babai.theorem_9_2_3_of_designLemma` (below the Design Lemma in the form of §6)
  -- derives this statement from Theorem 8.1.2 restated as a reduction in the sense of §6,
  -- which is `Babai.designLemma_finds` (`Workspace/DesignLemma/Reduction.lean`).
  -- Theorem 9.2.3 asks for `3/4 ≤ α`, Theorem 8.1.2 for `1/2 ≤ α`, which is less.
  exact theorem_9_2_3_of_designLemma
    (fun _ _ _ _ _ hα hα1 => designLemma_finds (by linarith) hα1)


end Babai
