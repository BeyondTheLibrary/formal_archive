/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.7 and 9.8: the two remaining cases of step 9 of Procedure Bipartite
Split-or-Johnson, stated in the wider category of §9.4-§9.8.
-/
import Workspace.SplitOrJohnson.Imprimitive
import Workspace.SplitOrJohnson.BipSplit
import Workspace.SplitOrJohnson.BlkDictionary

/-!
# §9.7, §9.8  The block design case and the UPCC case

Step 9 of §9.4 splits into three cases: `X₂` imprimitive (§9.6, `Babai.lemma_9_6_1`), `X₂`
the clique configuration (§9.7, the *block design case*), and `X₂` uniprimitive (§9.8).
This file states the two remaining cases in the same wider category as §9.6, in which a
vertex of `V₂` is a **block** of points (see
`Workspace/SplitOrJohnson/BipBlocks.lean` and the entry for Lemma 9.6.1 in
the corrected paper).

The inputs are the objects of §9.6 with a different `Case` heading, so the object, the
category and the canonicity lemma are written once here, with the `Case` as a parameter
(`Babai.BlkCaseObj`, `Babai.BlkCases`).

| Paper | Lean |
|---|---|
| §9.7, *"Assumptions: no twins in `V₁`, `X₂` is the clique configuration"* | `Babai.IsBlockDesignCase` |
| §9.8, *"Case: Both `X₁` and `X₂` are UPCCs; the link `X₁₂` is nontrivial"* | `Babai.IsUPCCCase` |
| §9.7, the block design case | `Babai.case_9_7` (`Workspace/SplitOrJohnson/BlockDesignAssemble.lean`) |
| §9.8, the Claim on Procedure Reduce-by-UPCC | `Babai.case_9_8` |
| the vertex set "points of `V₁` plus blocks" | `Babai.BlkCaseObj.vtxSet`, `.vc` |
| §9.8, Procedure Reduce-by-UPCC, branch condition of step 2 | `Babai.UPCCSplits` |
| §9.8, step 2, the `x`-local coloring of `V₁` | `Babai.case_9_8_step1` |
| §9.8, step 3, the dominant color `m` | `Babai.BlkCaseObj.mColor` |
| §9.8, step 3, the non-dominant off-diagonal color `ℓ` of `X₂` | `Babai.BlkCaseObj.lColor` |
| §9.8, step 3, the local constituent `Y = X_m[R_m⁻(x), R_ℓ(x)]` | `Babai.BlkCaseObj.upccBip`, `Babai.case_9_8_step2` |

`Babai.case_9_7` lives in `Workspace/SplitOrJohnson/BlockDesignAssemble.lean`.  `Babai.case_9_8` is proved,
except for one named piece of step 3 of Procedure Reduce-by-UPCC
(`Babai.BlkCaseObj.upccStep2_local_twins`).
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Twins of the coherent configuration of step 3 of §9.4 -/

/-- Definition 2.3.4 for an edge-colored structure: the permutations of the vertex set that
preserve the coloring.  This is `Aut(X)` for the coherent configuration `X` of step 3 of
§9.4, read on its coloring. -/
def ColorAut {V : Type*} (c : V → V → ℕ) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ x y, c (σ x) (σ y) = c x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := (ha (b x) (b y)).trans (hb x y)
  inv_mem' {a} ha x y := by simpa using (ha (a.symm x) (a.symm y)).symm

/-! ### The two `Case` headings -/

/-- The *Case* of §9.7 (block design case).  *"Assumptions: no twins in `V₁`, `X₂` is the
clique configuration (rank-2)."*  The remaining assumptions of step 9 of §9.4 — `X₁` is a
UPCC and the link `X₁₂` is nontrivial — are `Babai.IsBipartiteCase`. -/
structure IsBlockDesignCase {V : Type} [DecidableEq V] (c : V → V → ℕ) (V₁ V₂ : Set V) :
    Prop extends IsBipartiteCase c V₁ V₂ where
  /-- *"`X₂` is the clique configuration (rank-2)"* (Def. 3.1.8), with the color classes of
  `c` on `V₂` as its color classes; see `Babai.IsBipartiteCase.upcc₁` for why the naming of
  the colors is not prescribed. -/
  clique₂ : ∃ X : PartitionStructure ↥V₂, X.IsCoherent ∧ X.IsHomogeneous ∧ X.rank = 2 ∧
    ∀ x y x' y' : ↥V₂,
      X.natColor x y = X.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)
  /-- *"no twins in `V₁`"* (Def. 2.3.9, for `Aut(X)`). -/
  noTwins₁ : ∀ x ∈ V₁, ∀ y ∈ V₁, ¬ IsTwin (ColorAut c) x y

/-- The *Case* of §9.8 (UPCC case).  *"Case: Both `X₁` and `X₂` are UPCCs; the link `X₁₂`
is nontrivial."*  That `X₁` is a UPCC and that the link is nontrivial are already part of
`Babai.IsBipartiteCase`; what §9.8 adds is that `X₂` is a UPCC too. -/
structure IsUPCCCase {V : Type} (c : V → V → ℕ) (V₁ V₂ : Set V) : Prop
    extends IsBipartiteCase c V₁ V₂ where
  /-- *"`X₂` is a UPCC"* (Def. 3.2.1), with the color classes of `c` on `V₂` as its color
  classes; see `Babai.IsBipartiteCase.upcc₁` for why the naming of the colors is not
  prescribed. -/
  upcc₂ : ∃ X : PartitionStructure ↥V₂, X.IsCoherent ∧ X.IsUniprimitive ∧
    ∀ x y x' y' : ↥V₂,
      X.natColor x y = X.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)

/-- §9.7.  The `Case` of §9.7 read on the vertex set *"points of `V₁` plus blocks"*, as
`Babai.IsImprimitiveCaseOn` reads the `Case` of §9.6. -/
def IsBlockDesignCaseOn {s : Set Ω} (c : Set ↥s → Set ↥s → ℕ) (𝒱₁ 𝒞 : Set (Set ↥s)) :
    Prop :=
  letI : DecidableEq ↥(𝒱₁ ∪ 𝒞) := Classical.decEq _
  IsBlockDesignCase (V := ↥(𝒱₁ ∪ 𝒞)) (fun u v => c (u : Set ↥s) (v : Set ↥s))
    {u | (u : Set ↥s) ∈ 𝒱₁} {u | (u : Set ↥s) ∈ 𝒞}

/-- §9.8.  The `Case` of §9.8 read on the vertex set *"points of `V₁` plus blocks"*. -/
def IsUPCCCaseOn {s : Set Ω} (c : Set ↥s → Set ↥s → ℕ) (𝒱₁ 𝒞 : Set (Set ↥s)) : Prop :=
  IsUPCCCase (V := ↥(𝒱₁ ∪ 𝒞)) (fun u v => c (u : Set ↥s) (v : Set ↥s))
    {u | (u : Set ↥s) ∈ 𝒱₁} {u | (u : Set ↥s) ∈ 𝒞}

/-! ### The `Case` of the paper builds the `Case` of this file

As `Babai.isBipartiteCase_induced` and `Babai.isImprimitiveCase_induced` do for §9.4 and
§9.6: the hypotheses are the paper's words about the configurations `X₁ = X[V₁]` and
`X₂ = X[V₂]` induced by the ambient coherent configuration on its two vertex-color
classes. -/

/-- §9.7.  The `Case` of §9.7 in the paper's own words: the `Case` of §9.4 step 9, the
induced configuration `X₂ = X[V₂]` is the clique configuration (homogeneous of rank 2),
and `V₁` has no twins. -/
theorem isBlockDesignCase_induced {V : Type} [Fintype V] [DecidableEq V]
    (X : PartitionStructure V) (hX : X.IsCoherent) {i j : Fin X.rank}
    [Fintype ↥(X.vertexClass i)] [Fintype ↥(X.vertexClass j)]
    (hij : i ≠ j) (hcover : ∀ x : V, x ∈ X.vertexClass i ∨ x ∈ X.vertexClass j)
    (huni₁ : (X.induced (X.vertexClass i)).IsUniprimitive)
    (hhom₂ : (X.induced (X.vertexClass j)).IsHomogeneous)
    (hrank₂ : (X.induced (X.vertexClass j)).rank = 2)
    (hnoTwins : ∀ x ∈ X.vertexClass i, ∀ y ∈ X.vertexClass i,
      ¬ IsTwin (ColorAut X.natColor) x y)
    {x₁ x₂ : ↥(X.vertexClass i)} {y₁ y₂ : ↥(X.vertexClass j)}
    (hlink : X.natColor (x₁ : V) (y₁ : V) ≠ X.natColor (x₂ : V) (y₂ : V)) :
    IsBlockDesignCase X.natColor (X.vertexClass i) (X.vertexClass j) where
  toIsBipartiteCase := isBipartiteCase_induced X hX hij hcover huni₁ hlink
  clique₂ := ⟨X.induced (X.vertexClass j),
    X.induced_isCoherent hX (X.isStable_vertexClass j), hhom₂, hrank₂,
    X.natColor_induced_eq_iff (X.vertexClass j)⟩
  noTwins₁ := hnoTwins

/-- §9.8.  The `Case` of §9.8 in the paper's own words: the `Case` of §9.4 step 9, and in
addition the induced configuration `X₂ = X[V₂]` is a UPCC. -/
theorem isUPCCCase_induced {V : Type} [Fintype V] (X : PartitionStructure V)
    (hX : X.IsCoherent) {i j : Fin X.rank}
    [Fintype ↥(X.vertexClass i)] [Fintype ↥(X.vertexClass j)]
    (hij : i ≠ j) (hcover : ∀ x : V, x ∈ X.vertexClass i ∨ x ∈ X.vertexClass j)
    (huni₁ : (X.induced (X.vertexClass i)).IsUniprimitive)
    (huni₂ : (X.induced (X.vertexClass j)).IsUniprimitive)
    {x₁ x₂ : ↥(X.vertexClass i)} {y₁ y₂ : ↥(X.vertexClass j)}
    (hlink : X.natColor (x₁ : V) (y₁ : V) ≠ X.natColor (x₂ : V) (y₂ : V)) :
    IsUPCCCase X.natColor (X.vertexClass i) (X.vertexClass j) where
  toIsBipartiteCase := isBipartiteCase_induced X hX hij hcover huni₁ hlink
  upcc₂ := ⟨X.induced (X.vertexClass j),
    X.induced_isCoherent hX (X.isStable_vertexClass j), huni₂,
    X.natColor_induced_eq_iff (X.vertexClass j)⟩

/-! ### The objects and the category, with the `Case` as a parameter

Word for word `Babai.BlkImprimitiveObj` and `Babai.BlkImprimitiveCases`, with the `Case`
of §9.6 replaced by an arbitrary condition on the coloring and the two parts.  See the
docstrings there for why the coloring is a total function on subsets and why its padding
outside the vertex set is normalized to the color `0`. -/

/-- §9.7, §9.8.  An input of one of the remaining cases of step 9 of §9.4 on the point set
`s`: the first part `V₁` (a set of points), the family of blocks that are the vertices of
`V₂`, and the coloring `c` of the coherent configuration `X` of step 3 of §9.4 on the
vertex set *"points of `V₁` plus blocks"*, subject to the `Case` heading `Case`. -/
structure BlkCaseObj (s : Set Ω)
    (Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop) where
  /-- The membership predicate of the first part `V₁`. -/
  part₁ : ↥s → Prop
  /-- The second part: a vertex of `V₂` is one of these blocks. -/
  blocks : Set (Set ↥s)
  /-- A block is nonempty. -/
  blocks_nonempty : ∀ B ∈ blocks, B.Nonempty
  /-- Two different blocks are disjoint. -/
  blocks_disjoint : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' → Disjoint B B'
  /-- A block consists of points outside the first part. -/
  blocks_off₁ : ∀ B ∈ blocks, ∀ x ∈ B, ¬ part₁ x
  /-- The edge coloring of the coherent configuration of step 3 of §9.4, indexed by the
  vertices: a point `x` of `V₁` is the singleton `{x}`, a vertex of `V₂` is a block. -/
  c : Set ↥s → Set ↥s → ℕ
  /-- Normalization of the padding outside the vertex set, as in
  `Babai.BlkImprimitiveObj.c_off`. -/
  c_off : ∀ A B, ¬ (IsVertexOn part₁ blocks A ∧ IsVertexOn part₁ blocks B) → c A B = 0
  /-- The `Case` heading. -/
  case : Case c {A | ∃ x, part₁ x ∧ A = {x}} blocks

/-- §9.7, §9.8.  The category of the inputs of one of the remaining cases: morphisms are
the bijections of the point set that carry the first part to the first part, blocks to
blocks, and the coloring to itself. -/
def BlkCases (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (Case : ∀ s : Set Ω, (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop) :
    Cat.{0, 0} Ω where
  Obj s := BlkCaseObj s (Case s)
  Iso X Y := {φ | (∀ x, Y.part₁ (φ x) ↔ X.part₁ x)
    ∧ (∀ B, φ '' B ∈ Y.blocks ↔ B ∈ X.blocks)
    ∧ (∀ A B, Y.c (φ '' A) (φ '' B) = X.c A B)}
  refl_mem X := ⟨fun _ => Iff.rfl, fun B => by simp, fun A B => by simp⟩
  symm_mem {_ _ _ _ φ} hφ :=
    ⟨fun x => by simpa using (hφ.1 (φ.symm x)).symm,
     fun B => by
       have := (hφ.2.1 (φ.symm '' B)).symm
       rwa [Equiv.image_symm_image] at this,
     fun A B => by
       have := (hφ.2.2 (φ.symm '' A) (φ.symm '' B)).symm
       rwa [Equiv.image_symm_image, Equiv.image_symm_image] at this⟩
  trans_mem {_ _ _ _ _ _ φ ψ} hφ hψ :=
    ⟨fun x => (hψ.1 (φ x)).trans (hφ.1 x),
     fun B => by
       have himg : (φ.trans ψ) '' B = ψ '' (φ '' B) := by rw [← Set.image_comp]; rfl
       rw [himg]
       exact (hψ.2.1 (φ '' B)).trans (hφ.2.1 B),
     fun A B => by
       have himgA : (φ.trans ψ) '' A = ψ '' (φ '' A) := by rw [← Set.image_comp]; rfl
       have himgB : (φ.trans ψ) '' B = ψ '' (φ '' B) := by rw [← Set.image_comp]; rfl
       rw [himgA, himgB]
       exact (hψ.2.2 (φ '' A) (φ '' B)).trans (hφ.2.2 A B)⟩
  faithful {s X Y} hid := by
    obtain ⟨p, Bs, hn, hd, ho, c, hcoff, hcase⟩ := X
    obtain ⟨p', Bs', hn', hd', ho', c', hcoff', hcase'⟩ := Y
    obtain ⟨k1, k2, k3⟩ := hid
    simp only [Equiv.coe_refl, Set.image_id', id_eq] at k1 k2 k3
    have hp : p' = p := funext fun x => propext (k1 x)
    subst hp
    have hB : Bs' = Bs := Set.ext k2
    subst hB
    have hc : c' = c := funext fun A => funext fun B => k3 A B
    subst hc
    rfl

/-- §9.7, §9.8.  The padding of `c` does not restrict the morphisms, exactly as in
`Babai.BlkImprimitiveObj.isIso_of_vertexColor`. -/
theorem BlkCaseObj.isIso_of_vertexColor {s t : Set Ω}
    {Case : ∀ s : Set Ω, (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    {X : BlkCaseObj s (Case s)} {Y : BlkCaseObj t (Case t)} {φ : ↥s ≃ ↥t}
    (hp : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x)
    (hb : ∀ B, φ '' B ∈ Y.blocks ↔ B ∈ X.blocks)
    (hc : ∀ A B, IsVertexOn X.part₁ X.blocks A → IsVertexOn X.part₁ X.blocks B →
      Y.c (φ '' A) (φ '' B) = X.c A B) :
    φ ∈ (BlkCases Ω Case).Iso X Y := by
  refine ⟨hp, hb, fun A B => ?_⟩
  by_cases hA : IsVertexOn X.part₁ X.blocks A
  · by_cases hB : IsVertexOn X.part₁ X.blocks B
    · exact hc A B hA hB
    · rw [X.c_off A B (fun h => hB h.2),
        Y.c_off _ _ (fun h => hB ((isVertexOn_image_iff hp hb B).1 h.2))]
  · rw [X.c_off A B (fun h => hA h.1),
      Y.c_off _ _ (fun h => hA ((isVertexOn_image_iff hp hb A).1 h.1))]

/-- The first part `V₁` of an input, as a subset of the ambient type. -/
def BlkCases.V₁ {Case : ∀ s : Set Ω, (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) →
    Set (Set ↥s) → Prop} (X : Pt (BlkCases Ω Case)) : Set Ω :=
  Subtype.val '' {x | X.obj.part₁ x}

/-- `n₂ = |V₂|`: the number of blocks of an input. -/
noncomputable def BlkCases.numBlocks {Case : ∀ s : Set Ω, (Set ↥s → Set ↥s → ℕ) →
    Set (Set ↥s) → Set (Set ↥s) → Prop} (X : Pt (BlkCases Ω Case)) : ℕ :=
  X.obj.blocks.ncard

/-! ### §9.7, the block design case -/

/-- §9.7, §9.8.  The inputs of one of the remaining cases **together with the threshold
`α`** of Theorem 9.2.2.  §9.7 uses the current value of `α` (*"If all `c'`-color classes
have size less than `αn₁`, return this coloring"*, Case 2), and step 5 of §9.4 has updated
it to `α n₁/|W₁|`, which depends on the input.  So `α` is data of the object, exactly as in
`Babai.VColBlkThr`; an isomorphism preserves it. -/
def BlkCasesThr (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (Case : ∀ s : Set Ω, (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop) :
    Cat.{0, 0} Ω where
  Obj s := BlkCaseObj s (Case s) × ℝ
  Iso X Y := {φ | X.2 = Y.2 ∧ φ ∈ (BlkCases Ω Case).Iso X.1 Y.1}
  refl_mem X := ⟨rfl, (BlkCases Ω Case).refl_mem X.1⟩
  symm_mem hf := ⟨hf.1.symm, (BlkCases Ω Case).symm_mem hf.2⟩
  trans_mem hf hg := ⟨hf.1.trans hg.1, (BlkCases Ω Case).trans_mem hf.2 hg.2⟩
  faithful hid := Prod.ext ((BlkCases Ω Case).faithful hid.2) hid.1

/-- §9.7.  The category of the inputs of the block design case: the `Case` of §9.7, the
threshold `α`, and the two numeric invariants of Theorem 9.2.2 that the procedure of §9.4
maintains up to step 9: *"`2/3 ≤ α < 1`"* and *"`|V₂| < α|V₁|`"*. -/
def BlkBlockDesignInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  (BlkCasesThr Ω fun _ c 𝒱₁ 𝒞 => IsBlockDesignCaseOn c 𝒱₁ 𝒞).full fun _ X =>
    2 / 3 ≤ X.2 ∧ X.2 < 1 ∧
      (X.1.blocks.ncard : ℝ) < X.2 * (({x | X.1.part₁ x} : Set _).ncard : ℝ)

/-- The threshold `α` of an input of the block design case. -/
def BlkBlockDesignInputs.alpha (X : Pt (BlkBlockDesignInputs Ω)) : ℝ := X.obj.1.2

/-- The first part `V₁` of an input of the block design case, as a subset of the ambient
type. -/
def BlkBlockDesignInputs.V₁ (X : Pt (BlkBlockDesignInputs Ω)) : Set Ω :=
  Subtype.val '' {x | X.obj.1.1.part₁ x}

/-- `n₂ = |V₂|`: the number of blocks of an input of the block design case. -/
noncomputable def BlkBlockDesignInputs.numBlocks (X : Pt (BlkBlockDesignInputs Ω)) : ℕ :=
  X.obj.1.1.blocks.ncard

/-- §9.7.  The outcome of the block design case.  §9.7 either finishes Theorem 9.2.2 for
`V₁` — Case 1 embeds a Johnson scheme `J(n₂, d₁)` on `V₁`, goal (b); Cases 2 and 3a1 return
a colored partition of `V₁`, goal (a) — or it hands back a smaller instance of
Theorem 9.2.2 whose solutions are solutions for the original `V₁` in the sense of
Lemma 9.3.1: the new first part is inside the old one and `α_new |V₁_new| = α |V₁|`.

The instance handed back makes the major progress of §9.5 (version 2.5, lines 4176–4181)
in one of its two remaining kinds.  Either *"`n₂` is significantly reduced"*, that is,
`n₂_new ≤ 0.9 n₂`.  Or *"`X₂` moves from clique to UPCC while `n₂` does not increase"*:
the instance carries the hint (`Babai.VColBipBlk.HasHint`), the homogeneous coherent
configuration of rank `≥ 3` that the Design Lemma found on its blocks (Cases 3a1, 3a2 and
3b), and its `n₂` is at most the old one.  The next turn starts from the hint and reduces
`n₂` (`Babai.VColBipBlk.two_mul_ncard_le_of_hint` in the clique branch, §9.6 and §9.8 in the
other two).  The cost `Babai.cost_9_4` pays one `Babai.turnCost` per significant reduction
of `n₂` and one more for the turn that only gains the hint
(`Babai.turnCost_mul_costFun_le_of_hint`).  See entries 88 and 94 of the corrected paper. -/
def IsBlkDesignOutcome (α : ℝ) (V₁ : Set Ω) (n₂ : ℕ)
    (Z : Pt (Cat.sum (SplitOutcomes Ω) (BipBlockInputs Ω))) : Prop :=
  match Z.obj with
  | Sum.inl W => IsSplitOutcome α V₁ ⟨Z.car, W⟩
  | Sum.inr Y =>
      BipBlockInputs.V₁ ⟨Z.car, Y⟩ ⊆ V₁ ∧
      BipBlockInputs.alpha ⟨Z.car, Y⟩ * ((BipBlockInputs.V₁ ⟨Z.car, Y⟩).ncard : ℝ)
        = α * (V₁.ncard : ℝ) ∧
      (10 * BipBlockInputs.numBlocks (⟨Z.car, Y⟩ : Pt (BipBlockInputs Ω)) ≤ 9 * n₂ ∨
        (BipBlockInputs.numBlocks (⟨Z.car, Y⟩ : Pt (BipBlockInputs Ω)) ≤ n₂ ∧
          Y.1.1.HasHint))

/-! `Babai.case_9_7`, the block design case itself, is stated and assembled in
`Workspace/SplitOrJohnson/BlockDesignCase.lean`, which needs the constructions of this file
and of `Workspace/SplitOrJohnson/BlockDesign.lean`. -/

/-! ### §9.8, the UPCC case -/

/-- §9.8.  The category of the inputs of the UPCC case. -/
def BlkUPCCCases (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  BlkCases Ω fun _ c 𝒱₁ 𝒞 => IsUPCCCaseOn c 𝒱₁ 𝒞

/-! ### The vertex set of the configuration of step 3 of §9.4

Word for word `Babai.BlkImprimitiveObj.sglSet`, `.vtxSet`, `.vc`, `.Pt₁`, `.vtxOfPt` and
`.vtxOfBlk`, for an object of `Babai.BlkCases` with an arbitrary `Case` heading. -/

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  (X : BlkCaseObj s Case)

/-- §9.7, §9.8.  `𝒱₁`: the singletons of the points of the first part, which are the
vertices of `V₁`. -/
def sglSet : Set (Set ↥s) := {A | ∃ x, X.part₁ x ∧ A = {x}}

/-- §9.7, §9.8.  The vertex set of the coherent configuration `X` of step 3 of §9.4: the
singletons of the points of `V₁` together with the blocks. -/
def vtxSet : Set (Set ↥s) := X.sglSet ∪ X.blocks

/-- §9.7, §9.8.  The coloring of that configuration, read on its vertex set. -/
def vc : ↥X.vtxSet → ↥X.vtxSet → ℕ := fun u v => X.c (u : Set ↥s) (v : Set ↥s)

/-- The first part, as a set of points. -/
def Pt₁ : Set ↥s := {x | X.part₁ x}

/-- The vertex of `V₁` at a point of the first part. -/
def vtxOfPt (x : ↥X.Pt₁) : ↥X.vtxSet := ⟨{(x : ↥s)}, Or.inl ⟨(x : ↥s), x.2, rfl⟩⟩

/-- The vertex of `V₂` at a block. -/
def vtxOfBlk (B : ↥X.blocks) : ↥X.vtxSet := ⟨(B : Set ↥s), Or.inr B.2⟩

/-- The vertex of `V₂` at a block, as a bijection of the blocks with the second vertex
class (`Babai.BlkImprimitiveObj.blkEquiv` for an arbitrary `Case`). -/
def blkEquiv : ↥X.blocks ≃ ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} where
  toFun B := ⟨X.vtxOfBlk B, B.2⟩
  invFun u := ⟨((u : ↥X.vtxSet) : Set ↥s), u.2⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (Subtype.ext rfl)

end BlkCaseObj

/-! ### §9.8, the objects of the UPCC case -/

/-- §9.8.  An input of the UPCC case: an object of `Babai.BlkUPCCCases`. -/
abbrev UPCCObj (s : Set Ω) : Type :=
  BlkCaseObj s (fun c 𝒱₁ 𝒞 => IsUPCCCaseOn c 𝒱₁ 𝒞)

namespace BlkCaseObj

variable {s : Set Ω} (X : UPCCObj s)

/-- §9.8.  The `Case` of §9.8, read on the vertex set. -/
theorem upccCase' : IsUPCCCase X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}
    {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := X.case

/-- §9.8.  There is at least one vertex in `V₂`: the link `X₁₂` is nontrivial, so it has
an edge, whose second endpoint is a vertex of `V₂`, that is a block. -/
theorem upccBlocks_nonempty : X.blocks.Nonempty := by
  obtain ⟨-, y₁, -, -, -⟩ := X.upccCase'.toIsBipartiteCase.link_nontrivial
  exact ⟨(y₁.1 : Set ↥s), y₁.2⟩

end BlkCaseObj

/-! ### Procedure Reduce-by-UPCC, step 2: the branch condition and the local coloring

*"2. If there is no `α`-dominant color in `X₁₂`, return the `x`-local coloring `c_x` of
`V₁` (set `c_x(y) = c(x,y)` for all `y ∈ V₁`), exit.  (Each `c_x`-class in `V₁` has
relative size `≤ α`; goal (a) achieved.)"*  (Version 2.5, lines 4325-4326.)

**The threshold is `α = 1/2` here.**  Procedure Reduce-by-UPCC runs with the threshold
parameter `α` of the surrounding Theorem 9.2.2, and step 3 uses of the dominant color `m`
only that it is `(1/2)`-dominant (*"the first of these inequalities follows because `m` is
`α`-dominant and therefore dominant"*, Claim of §9.8).  So the procedure may be run with
`α = 1/2` throughout: step 2 then returns a colored `1/2`-partition of `V₁`, which is what
the outcome `Babai.IsBlkImprimitiveOutcome` of the Claim asks for, and step 3 is unchanged.

**The condition is read at one vertex of `V₂`.**  *"the color `j` is `α`-dominant if
`|R_j| > α n₁ n₂`"* is a condition on the whole constituent; by the semiregularity of the
constituents of the link (Prop. 3.4.5, `Babai.PartitionStructure.ncard_rel_eq`) it says
exactly that the in-degree `|R_j(x) ∩ V₁|` at one — hence at every — vertex `x ∈ V₂`
exceeds `α n₁`.  The branch condition below is the latter form, read at every vertex of
`V₂`; this is the same condition, and needs no appeal to §3.4. -/

/-- Procedure Reduce-by-UPCC, **the branch condition of step 2**: *"there is no
`α`-dominant color in `X₁₂`"*, with `α = 1/2` and read at each vertex of `V₂` (see the
section docstring).  `x ↦ c(B, {x})` is the `B`-local coloring of `V₁`. -/
def UPCCSplits {s : Set Ω} (X : UPCCObj s) : Prop :=
  ∀ B ∈ X.blocks, ∀ k : ℕ,
    2 * {x : ↥s | X.part₁ x ∧ X.c B {x} = k}.ncard ≤ {x : ↥s | X.part₁ x}.ncard

/-- Procedure Reduce-by-UPCC, step 2.  The outcome for the individualized vertex `B` of
`V₂`: the partition of `V₁` into the classes of the local coloring `x ↦ c(B, {x})`. -/
def upccStep1Outcome {s : Set Ω} (X : UPCCObj s) (B : Set ↥s) :
    (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s :=
  kerOutcomeL (VColBlkGraphs Ω ℕ) {x | X.part₁ x} (fun x => X.c B {x})

/-- The branch condition of step 2 is an isomorphism invariant. -/
theorem upccSplits_congr {X Y : Pt (BlkUPCCCases Ω)}
    (h : ((BlkUPCCCases Ω).IsoP X Y).Nonempty)
    (hX : UPCCSplits X.obj) : UPCCSplits Y.obj := by
  obtain ⟨φ, hp, hb, hc⟩ := h
  intro B' hB' k
  have hBmem : φ.symm '' B' ∈ X.obj.blocks := by
    rw [← hb (φ.symm '' B'), Equiv.image_symm_image]; exact hB'
  have hset : {y : ↥Y.car | Y.obj.part₁ y ∧ Y.obj.c B' {y} = k}
      = φ '' {x : ↥X.car | X.obj.part₁ x ∧ X.obj.c (φ.symm '' B') {x} = k} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨φ.symm y, ⟨(hp (φ.symm y)).1 (by simpa using h1), ?_⟩, by simp⟩
      have := hc (φ.symm '' B') {φ.symm y}
      rw [Set.image_singleton, Equiv.apply_symm_apply, Equiv.image_symm_image] at this
      rw [← this]; exact h2
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨(hp x).2 h1, ?_⟩
      have := hc (φ.symm '' B') {x}
      rw [Set.image_singleton, Equiv.image_symm_image] at this
      rw [this]; exact h2
  have hpart : {y : ↥Y.car | Y.obj.part₁ y} = φ '' {x : ↥X.car | X.obj.part₁ x} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hy
      exact ⟨φ.symm y, (hp (φ.symm y)).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩; exact (hp x).2 hx
  rw [hset, hpart, Set.ncard_image_of_injective _ φ.injective,
    Set.ncard_image_of_injective _ φ.injective]
  exact hX _ hBmem k

/-- `⌊n/2⌋ ≤ n/2` after casting to the reals: the threshold `1/2`. -/
private theorem cast_div_two_le' (n : ℕ) : ((n / 2 : ℕ) : ℝ) ≤ 1 / 2 * (n : ℝ) := by
  have h2 : 2 * (n / 2) ≤ n := by omega
  have hR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  linarith

/-- §9.8, **step 2 of Procedure Reduce-by-UPCC**.  *"If there is no `α`-dominant color in
`X₁₂`, return the `x`-local coloring `c_x` of `V₁` … (Each `c_x`-class in `V₁` has relative
size `≤ α`; goal (a) achieved.)"*  (Version 2.5, lines 4325-4326, with `α = 1/2`; see the
section docstring.)

The multiplicative cost is the choice of the individualized vertex `x ∈ V₂` of step 1, that
is of a block: `n₂`, the cost of the Claim of §9.8.  Each class of the returned partition
has at most `n₁/2` points, which is the branch condition, so the partition is a colored
`1/2`-partition of `V₁` (`Babai.reduceByUPCC_localColoring_small` is the same statement for
a coherent configuration and a general `α`). -/
theorem case_9_8_step1 :
    FindsAtMultCost ((BlkUPCCCases Ω).full fun _ X => UPCCSplits X)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkCases.numBlocks ⟨X.car, X.obj.1⟩)
      (fun X Z => IsBlkImprimitiveOutcome (BlkCases.V₁ ⟨X.car, X.obj.1⟩)
        (BlkCases.numBlocks ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => (fun B => upccStep1Outcome X.obj.1 B) '' X.obj.1.blocks)
    (fun X => ?_) (fun X => Set.toFinite _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · obtain ⟨B, hB⟩ := X.obj.1.upccBlocks_nonempty
    exact ⟨_, ⟨B, hB, rfl⟩⟩
  · exact Set.ncard_image_le (Set.toFinite _)
  · obtain ⟨B, hB, rfl⟩ := hZ
    obtain ⟨hp, hb, hc⟩ := hf
    refine ⟨upccStep1Outcome Y.obj.1 (f '' B), ⟨f '' B, (hb B).2 hB, rfl⟩, ?_⟩
    refine kerOutcomeL_mem_subIso _ f (fun x => (hp x)) (fun x => ?_)
    have := hc B {x}
    rwa [Set.image_singleton] at this
  · obtain ⟨B, hB, rfl⟩ := hZ
    refine ⟨rfl, ?_⟩
    refine kerPartition_isAlphaPartition _ _ _
      (k := {x : ↥X.car | X.obj.1.part₁ x}.ncard / 2) (fun x hx => ?_) ?_
    · have hbr := X.obj.2 B hB (X.obj.1.c B {x})
      have : {y : ↥X.car | y ∈ {x : ↥X.car | X.obj.1.part₁ x} ∧
          X.obj.1.c B {y} = X.obj.1.c B {x}}
          = {y : ↥X.car | X.obj.1.part₁ y ∧ X.obj.1.c B {y} = X.obj.1.c B {x}} := rfl
      rw [this]
      omega
    · exact cast_div_two_le' _

/-! ### Procedure Reduce-by-UPCC, step 3

*"3. Else, let `m ∈ J` be the dominant color in `X₁₂`.  Let `ℓ` be the first non-dominant
off-diagonal color in `X₂`, so `R_ℓ(x) ⊆ V₂` and `|R_ℓ(x)| < n₂/2`.  Let `Y` be the local
constituent `Y = X_m[R_m⁻(x), R_ℓ(x)]` (the edges in color `m` connecting the
`m`-in-neighbors of `x` to the `ℓ`-out-neighbors of `x`).  Replace `X ← Y`.  This implies
the following updates: `V₁ ← R_m⁻(x)`, the corresponding update of `α`, and
`V₂ ← R_ℓ(x)`."*  (Version 2.5, lines 4327-4332.)

The canonical choices, all read off the coloring of the object:

* `Babai.BlkCaseObj.mColor B₀`, the smallest color of the link that at the individualized
  vertex `B₀ ∈ V₂` covers more than half of `V₁` — the dominant color `m`, written in the
  direction `V₂ → V₁`, which is the direction of the paper's `R_m⁻(x)`;
* `Babai.BlkCaseObj.lColor B₀`, the smallest color of `X₂` that occurs at `B₀` toward
  another vertex of `V₂` and covers at most half of `V₂` — the color `ℓ`.  Its existence
  is `Babai.BlkCaseObj.exists_isSmallColor₂`, which is where *"uni"* is used.

**`V₁` is kept, and marked.**  The paper sets `V₁ ← R_m⁻(x)`, a *proper* subset of `V₁`
(`n₁/2 < |R_m⁻(x)| < n₁`).  The outcome of the Claim of §9.8 is stated — like the outcome
of Lemma 9.6.1, which it shares — as a bipartite graph *on `V₁`*, so the graph returned
here keeps all of `V₁` and marks `R_m⁻(x)` by the vertex coloring `f` of
`Babai.VColBipBlk`; the points outside `R_m⁻(x)` are isolated.  The symmetry defect of
`V₁` in the marked graph is still `≥ 1/2`: a set of twins is monochromatic for `f`, so it
either lies in `R_m⁻(x)`, where it is a set of twins of the paper's `Y` and therefore has
at most `|R_m⁻(x)|/2` points, or it lies in `V₁ \ R_m⁻(x)`, which has fewer than `n₁/2`
points because `m` is dominant (`Babai.BlkCaseObj.upccBip_defect₁`).  Passing to `R_m⁻(x)`
and updating `α` is then what steps 4 and 5 of §9.4 do with the returned graph.  See the
entry for the Claim of §9.8 in the corrected paper. -/

namespace BlkCaseObj

variable {s : Set Ω} (X : UPCCObj s)

/-- §9.8.  `R_k⁻(B) ∩ V₁`: the points of `V₁` joined to the vertex `B` of `V₂` in the color
`k` of the link (read in the direction `V₂ → V₁`). -/
def linkClass (B : Set ↥s) (k : ℕ) : Set ↥s := {x | X.part₁ x ∧ X.c B {x} = k}

/-- §9.8.  `R_k(B)`: the vertices of `V₂` joined to `B` in the color `k` of `X₂`. -/
def blkClass (B : Set ↥s) (k : ℕ) : Set (Set ↥s) := {B' | B' ∈ X.blocks ∧ X.c B B' = k}

/-- §9.8.  *"`m ∈ J` is the dominant color in `X₁₂`"*, read at the individualized vertex
`B` of `V₂`: the color covers more than half of `V₁` at `B`. -/
def IsBigColor₂ (B : Set ↥s) (k : ℕ) : Prop :=
  {x : ↥s | X.part₁ x}.ncard < 2 * (X.linkClass B k).ncard

/-- §9.8.  *"`ℓ` is the first non-dominant off-diagonal color in `X₂`"*, read at the
individualized vertex `B`: the color occurs at `B` toward another vertex of `V₂`
(off-diagonal, and `R_ℓ(B) ≠ ∅`) and covers at most half of `V₂` (non-dominant, which by
the semiregularity of the constituents of `X₂` is `|R_ℓ(B)| ≤ n₂/2`). -/
def IsSmallColor₂ (B : Set ↥s) (k : ℕ) : Prop :=
  (∃ B' ∈ X.blocks, B' ≠ B ∧ X.c B B' = k) ∧
    2 * (X.blkClass B k).ncard ≤ X.blocks.ncard

open scoped Classical in
/-- §9.8, step 3.  The canonical choice of the dominant color `m` at the individualized
vertex `B`: the smallest color of the link that covers more than half of `V₁` at `B`.
Taking the smallest label is what makes the choice canonical, as in
`Babai.BlkImprimitiveObj.jColor`. -/
noncomputable def mColor (B : Set ↥s) : ℕ :=
  if h : ∃ k, X.IsBigColor₂ B k then Nat.find h else 0

open scoped Classical in
/-- §9.8, step 3.  The canonical choice of the color `ℓ` at the individualized vertex `B`:
*"the first non-dominant off-diagonal color in `X₂`"*. -/
noncomputable def lColor (B : Set ↥s) : ℕ :=
  if h : ∃ k, X.IsSmallColor₂ B k then Nat.find h else 0

/-- §9.8, step 3.  **The returned bipartite graph** `Y = X_m[R_m⁻(x), R_ℓ(x)]`, as an
object of `Babai.VColBlkGraphs`: the vertices of the second part are the blocks of
`R_ℓ(B₀)`, the first part is `V₁` with `R_m⁻(B₀)` marked by the coloring `f`, and the edges
are the pairs of color `m` from a marked point to such a block. -/
noncomputable def upccBip (B₀ : Set ↥s) : VColBipBlk ↥s ℕ where
  part₁ := X.part₁
  blocks := X.blkClass B₀ (X.lColor B₀)
  blocks_nonempty := fun B hB => X.blocks_nonempty B hB.1
  blocks_disjoint := fun B hB B' hB' hne => X.blocks_disjoint B hB.1 B' hB'.1 hne
  blocks_off₁ := fun B hB x hx => X.blocks_off₁ B hB.1 x hx
  E := {p | X.part₁ p.1 ∧ X.c B₀ {p.1} = X.mColor B₀ ∧
    p.2 ∈ X.blkClass B₀ (X.lColor B₀) ∧ X.c p.2 {p.1} = X.mColor B₀}
  E_sub := fun p hp => ⟨hp.1, hp.2.2.1⟩
  f := fun x => if X.c B₀ {x} = X.mColor B₀ then 1 else 0
  g := fun _ => 0
  g_off := fun _ _ => rfl
  -- No hint: the outcome of §9.8 halves `n₂`, so it needs none.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

@[simp] theorem upccBip_V₁ (B₀ : Set ↥s) : (X.upccBip B₀).V₁ = {x | X.part₁ x} := rfl

@[simp] theorem upccBip_numBlocks (B₀ : Set ↥s) :
    (X.upccBip B₀).numBlocks = (X.blkClass B₀ (X.lColor B₀)).ncard := rfl

end BlkCaseObj

/-! ### The two facts of §9.8 that step 3 rests on -/

/-- §9.8, step 3.  *"we need 'uni' (not a clique) to guarantee that a non-dominant
off-diagonal color `ℓ` exists in `X₂`"* (Claim of §9.8, version 2.5, line 4342).

The argument is `Babai.PartitionStructure.exists_nondominant_offDiagonal` for the
configuration `X₂` of the field `upcc₂` of the `Case`, which is homogeneous, so its single
vertex class is everything: it gives an off-diagonal color `ℓ` of `X₂` with
`|R_ℓ| ≤ n₂²/2`.  That `Fin`-indexed color is translated into the `ℕ`-color `k` of the
coloring `c` of the object along
`Babai.BlkCaseObj.blkEquiv : ↥X.blocks ≃ ↥{u | ↑u ∈ X.blocks}`, and the two counting steps
turn `|R_ℓ| ≤ n₂²/2` into `2|R_ℓ(B₀)| ≤ n₂` (`Babai.PartitionStructure.ncard_rel_eq` and
the constancy of the out-degree on a vertex class) and `R_ℓ ≠ ∅` into `R_ℓ(B₀) ≠ ∅` (the
same constancy). -/
theorem BlkCaseObj.exists_isSmallColor₂ {s : Set Ω} (X : UPCCObj s) {B₀ : Set ↥s}
    (hB₀ : B₀ ∈ X.blocks) : ∃ k, X.IsSmallColor₂ B₀ k := by
  classical
  obtain ⟨P, hcoh, huni, hnat⟩ := X.upccCase'.upcc₂
  letI : Fintype ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := Fintype.ofFinite _
  set e := X.blkEquiv with he
  set b₀ : ↥X.blocks := ⟨B₀, hB₀⟩ with hb₀
  set x₀ := e b₀ with hx₀
  -- the color classes of `X₂` are the color classes of the input on `V₂`
  have hkey : ∀ w w' : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks},
      X.c B₀ ((w : ↥X.vtxSet) : Set ↥s) = X.c B₀ ((w' : ↥X.vtxSet) : Set ↥s)
        ↔ P.natColor x₀ w = P.natColor x₀ w' := fun w w' => (hnat x₀ w x₀ w').symm
  have hhom : P.IsHomogeneous := huni.1.1
  set i : Fin P.rank := P.vcolor x₀ with hi
  have hvc : P.vertexClass i = Set.univ := by
    ext u
    exact iff_of_true (hhom u x₀) trivial
  -- "uni": a non-dominant off-diagonal color of `X₂`
  obtain ⟨l, hloff, hlnd⟩ := P.exists_nondominant_offDiagonal huni.2 hvc
  -- the color `ℓ` occurs at `B₀`: the out-degree of a color is constant on a vertex class
  obtain ⟨⟨u, v⟩, huv⟩ := P.rel_nonempty l
  have huv' : P.color u v = l := huv
  have htail : P.tailColor l = i := by rw [← P.vcolor_fst_eq hcoh huv']; exact hhom u x₀
  have hdeg : P.outDegC l x₀ = P.outDegC l u :=
    P.outDegC_eq_of_vcolor_eq hcoh l (hhom x₀ u)
  have hupos : 0 < (P.nbr l u).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨v, huv'⟩
  have hx₀pos : 0 < (P.nbr l x₀).ncard := by
    rw [← PartitionStructure.outDegC_eq_ncard, hdeg, PartitionStructure.outDegC_eq_ncard]
    exact hupos
  obtain ⟨w, hw⟩ := (Set.ncard_pos (Set.toFinite _)).1 hx₀pos
  have hwcol : P.color x₀ w = l := hw
  -- the `Fin`-color `ℓ` of `X₂` is named by the `ℕ`-color that the input gives to `(B₀, w)`
  refine ⟨X.c B₀ ((w : ↥X.vtxSet) : Set ↥s), ?_, ?_⟩
  · -- the color occurs at `B₀` toward another vertex of `V₂`
    refine ⟨((w : ↥X.vtxSet) : Set ↥s), w.2, ?_, rfl⟩
    -- `w ≠ B₀`, because `ℓ` is off-diagonal
    intro hcon
    have hwx : w = x₀ := Subtype.ext (Subtype.ext hcon)
    have hdg : P.color x₀ x₀ = l := hwx ▸ hwcol
    have hmem : (x₀, x₀) ∈ P.rel l ∩ diag _ := ⟨hdg, rfl⟩
    rw [hloff] at hmem
    exact hmem
  · -- the color covers at most half of `V₂`
    -- `R_ℓ(B₀)` in the two readings
    have hpre : {u : ↥X.blocks | X.c B₀ (u : Set ↥s) = X.c B₀ ((w : ↥X.vtxSet) : Set ↥s)}
        = e ⁻¹' (P.nbr l x₀) := by
      ext u
      show X.c B₀ (u : Set ↥s) = X.c B₀ ((w : ↥X.vtxSet) : Set ↥s) ↔ P.color x₀ (e u) = l
      rw [← hwcol]
      exact (hkey (e u) w).trans (P.natColor_eq_iff x₀ (e u) x₀ w)
    have hblk : X.blkClass B₀ (X.c B₀ ((w : ↥X.vtxSet) : Set ↥s))
        = Subtype.val ''
          {u : ↥X.blocks | X.c B₀ (u : Set ↥s) = X.c B₀ ((w : ↥X.vtxSet) : Set ↥s)} := by
      ext B
      simp only [BlkCaseObj.blkClass, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨B, h1⟩, h2, rfl⟩
      · rintro ⟨u, hu, rfl⟩; exact ⟨u.2, hu⟩
    have himg : (e ⁻¹' (P.nbr l x₀)).ncard = (P.nbr l x₀).ncard := by
      rw [← Set.ncard_image_of_injective _ e.injective,
        Set.image_preimage_eq _ e.surjective]
    have hcard : (X.blkClass B₀ (X.c B₀ ((w : ↥X.vtxSet) : Set ↥s))).ncard
        = (P.nbr l x₀).ncard := by
      rw [hblk, Set.ncard_image_of_injective _ Subtype.val_injective, hpre, himg]
    -- `n₂` in the two readings
    have hn₂ : (P.vertexClass i).ncard = X.blocks.ncard := by
      rw [hvc, Set.ncard_univ, Nat.card_congr e.symm, Nat.card_coe_set_eq]
    -- `|R_ℓ| = n₂ · |R_ℓ(B₀)|`
    have hdeg' : P.outDegOf l = (P.nbr l x₀).ncard := by
      rw [← P.outDegC_eq_outDegOf hcoh l (by rw [htail]; exact hhom x₀ x₀),
        PartitionStructure.outDegC_eq_ncard]
    have hrel : (P.rel l).ncard = X.blocks.ncard * (P.nbr l x₀).ncard := by
      rw [P.ncard_rel_eq hcoh l, htail, hn₂, hdeg']
    -- non-dominance
    have hnd : ((P.rel l).ncard : ℝ)
        ≤ 1 / 2 * ((P.vertexClass i).ncard : ℝ) * ((P.vertexClass i).ncard : ℝ) :=
      not_lt.1 hlnd
    rw [hrel, hn₂] at hnd
    have hpos : 0 < X.blocks.ncard := by
      rw [← hn₂, hvc, Set.ncard_univ]
      have : Nonempty ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := ⟨x₀⟩
      exact Nat.card_pos
    have hposR : (0 : ℝ) < (X.blocks.ncard : ℝ) := by exact_mod_cast hpos
    have hfin : 2 * ((P.nbr l x₀).ncard : ℝ) ≤ (X.blocks.ncard : ℝ) := by
      push_cast at hnd
      nlinarith [hnd, hposR]
    rw [hcard]
    exact_mod_cast hfin

/-- §9.8, step 3.  **The symmetry defect of the local constituent.**  *"Summarizing, `Y` is
a nontrivial semiregular bipartite graph; therefore its symmetry defect is `≥ 1/2`
(Prop. 2.4.30)"* (Claim of §9.8, version 2.5, lines 4343-4344), read on the part
`R_m⁻(B₀)` of `Y = X_m[R_m⁻(B₀), R_ℓ(B₀)]`: a set `T` of points of `R_m⁻(B₀)` whose members
have the same `m`-neighborhood inside `R_ℓ(B₀)` — that is, a set of twins of `Y` — has at
most `|R_m⁻(B₀)|/2` points.

This is `Babai.upcc_local_twins` (`Workspace/SplitOrJohnson/BlkDictionary.lean`), which is
`Babai.claim_9_8` for an input whose colors are natural numbers, read on the vertex set
*"points of `V₁` plus blocks"* (`Babai.BlkCaseObj.vtxSet`, `Babai.BlkCaseObj.vc`): the
`Case` of §9.8 holds there (`Babai.BlkCaseObj.upccCase'`), a point `x` of `V₁` is the
vertex `{x}` and a vertex of `V₂` is a block, so `R_m⁻(B₀)` and `R_ℓ(B₀)` are the sets
`Babai.BlkCaseObj.linkClass` and `Babai.BlkCaseObj.blkClass` read on the vertices.  The
proof below is that change of index, one cardinality at a time. -/
theorem BlkCaseObj.upccStep2_local_twins {s : Set Ω} (X : UPCCObj s) {B₀ : Set ↥s}
    (hB₀ : B₀ ∈ X.blocks) (hm : X.IsBigColor₂ B₀ (X.mColor B₀))
    (hl : X.IsSmallColor₂ B₀ (X.lColor B₀)) {T : Set ↥s}
    (hT : T ⊆ X.linkClass B₀ (X.mColor B₀))
    (htwin : ∀ x ∈ T, ∀ y ∈ T, ∀ B ∈ X.blkClass B₀ (X.lColor B₀),
      (X.c B {x} = X.mColor B₀ ↔ X.c B {y} = X.mColor B₀)) :
    2 * T.ncard ≤ (X.linkClass B₀ (X.mColor B₀)).ncard := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  set m : ℕ := X.mColor B₀ with hmdef
  set l : ℕ := X.lColor B₀ with hldef
  set V₁v : Set ↥X.vtxSet := {u | (u : Set ↥s) ∈ X.sglSet} with hV₁v
  set V₂v : Set ↥X.vtxSet := {u | (u : Set ↥s) ∈ X.blocks} with hV₂v
  set b₀ : ↥X.vtxSet := ⟨B₀, Or.inr hB₀⟩ with hb₀def
  -- the singleton map `x ↦ {x}` is injective, and it is how a point of `V₁` is a vertex
  have hsgl : Function.Injective (fun x : ↥s => ({x} : Set ↥s)) := by
    intro a b hab
    exact Set.singleton_eq_singleton_iff.1 hab
  -- `V₁` and its `m`-class at `B₀`, read on the vertices
  have himg₁ : Subtype.val '' V₁v = (fun x : ↥s => ({x} : Set ↥s)) '' {x : ↥s | X.part₁ x} := by
    ext A
    simp only [Set.mem_image, hV₁v, Set.mem_setOf_eq, BlkCaseObj.sglSet]
    constructor
    · rintro ⟨u, ⟨x, hx, hux⟩, rfl⟩
      exact ⟨x, hx, hux.symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨{x}, Or.inl ⟨x, hx, rfl⟩⟩, ⟨x, hx, rfl⟩, rfl⟩
  have hcard₁ : V₁v.ncard = {x : ↥s | X.part₁ x}.ncard := by
    rw [← Set.ncard_image_of_injective V₁v Subtype.val_injective, himg₁,
      Set.ncard_image_of_injective _ hsgl]
  have himgM : Subtype.val '' {u | u ∈ V₁v ∧ X.vc b₀ u = m}
      = (fun x : ↥s => ({x} : Set ↥s)) '' X.linkClass B₀ m := by
    ext A
    simp only [Set.mem_image, Set.mem_setOf_eq, hV₁v, BlkCaseObj.sglSet,
      BlkCaseObj.linkClass]
    constructor
    · rintro ⟨u, ⟨⟨x, hx, hux⟩, hcu⟩, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, hux.symm⟩
      have : X.c B₀ ((u : Set ↥s)) = m := hcu
      rwa [hux] at this
    · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
      exact ⟨⟨{x}, Or.inl ⟨x, hx, rfl⟩⟩, ⟨⟨x, hx, rfl⟩, hcx⟩, rfl⟩
  have hcardM : {u | u ∈ V₁v ∧ X.vc b₀ u = m}.ncard = (X.linkClass B₀ m).ncard := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himgM,
      Set.ncard_image_of_injective _ hsgl]
  -- `V₂` and its `ℓ`-class at `B₀`, read on the vertices
  have himg₂ : Subtype.val '' V₂v = X.blocks := by
    ext A
    simp only [Set.mem_image, hV₂v, Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hA; exact ⟨⟨A, Or.inr hA⟩, hA, rfl⟩
  have hcard₂ : V₂v.ncard = X.blocks.ncard := by
    rw [← Set.ncard_image_of_injective V₂v Subtype.val_injective, himg₂]
  have himgL : Subtype.val '' {u | u ∈ V₂v ∧ X.vc b₀ u = l} = X.blkClass B₀ l := by
    ext A
    simp only [Set.mem_image, Set.mem_setOf_eq, hV₂v, BlkCaseObj.blkClass]
    constructor
    · rintro ⟨u, ⟨hu, hcu⟩, rfl⟩; exact ⟨hu, hcu⟩
    · rintro ⟨hA, hcA⟩; exact ⟨⟨A, Or.inr hA⟩, ⟨hA, hcA⟩, rfl⟩
  have hcardL : {u | u ∈ V₂v ∧ X.vc b₀ u = l}.ncard = (X.blkClass B₀ l).ncard := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himgL]
  -- the set of twins, read on the vertices
  set T' : Set ↥X.vtxSet := {u | ∃ x ∈ T, (u : Set ↥s) = {x}} with hT'def
  have himgT : Subtype.val '' T' = (fun x : ↥s => ({x} : Set ↥s)) '' T := by
    ext A
    simp only [Set.mem_image, Set.mem_setOf_eq, hT'def]
    constructor
    · rintro ⟨u, ⟨x, hx, hux⟩, rfl⟩
      exact ⟨x, hx, hux.symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨{x}, Or.inl ⟨x, (hT hx).1, rfl⟩⟩, ⟨x, hx, rfl⟩, rfl⟩
  have hcardT : T'.ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T' Subtype.val_injective, himgT,
      Set.ncard_image_of_injective _ hsgl]
  -- the hypotheses of `Babai.upcc_local_twins`
  have hb₀ : b₀ ∈ V₂v := hB₀
  have hmv : V₁v.ncard < 2 * {u | u ∈ V₁v ∧ X.vc b₀ u = m}.ncard := by
    rw [hcard₁, hcardM]; exact hm
  have hl₁ : ∃ b ∈ V₂v, b ≠ b₀ ∧ X.vc b₀ b = l := by
    obtain ⟨B', hB', hne, hcB'⟩ := hl.1
    refine ⟨⟨B', Or.inr hB'⟩, hB', ?_, hcB'⟩
    intro hcon
    exact hne (congrArg (fun u : ↥X.vtxSet => (u : Set ↥s)) hcon)
  have hl₂ : 2 * {b | b ∈ V₂v ∧ X.vc b₀ b = l}.ncard ≤ V₂v.ncard := by
    rw [hcardL, hcard₂]; exact hl.2
  have hTv : T' ⊆ {u | u ∈ V₁v ∧ X.vc b₀ u = m} := by
    rintro u ⟨x, hx, hux⟩
    obtain ⟨hx₁, hxm⟩ := hT hx
    refine ⟨⟨x, hx₁, hux⟩, ?_⟩
    show X.c B₀ ((u : Set ↥s)) = m
    rw [hux]; exact hxm
  have htwinv : ∀ u ∈ T', ∀ v ∈ T', ∀ b, b ∈ V₂v → X.vc b₀ b = l →
      (X.vc b u = m ↔ X.vc b v = m) := by
    rintro u ⟨x, hx, hux⟩ v ⟨y, hy, hvy⟩ b hb hbl
    have hblk : (b : Set ↥s) ∈ X.blkClass B₀ l := ⟨hb, hbl⟩
    have := htwin x hx y hy (b : Set ↥s) hblk
    show X.c ((b : Set ↥s)) ((u : Set ↥s)) = m ↔ X.c ((b : Set ↥s)) ((v : Set ↥s)) = m
    rw [hux, hvy]
    exact this
  -- the Claim of §9.8, for the `ℕ`-colored input
  have hfin := upcc_local_twins (c := X.vc) (V₁ := V₁v) (V₂ := V₂v)
    X.upccCase'.toIsBipartiteCase X.upccCase'.upcc₂ hb₀ hmv hl₁ hl₂ hTv htwinv
  rw [hcardT, hcardM] at hfin
  exact hfin

/-! ### The symmetry defect of the returned graph -/

namespace BlkCaseObj

variable {s : Set Ω} (X : UPCCObj s)

/-- The dominant color at `B₀` is the canonical one, once one exists. -/
theorem isBigColor₂_mColor {B₀ : Set ↥s} (hbig : ∃ k, X.IsBigColor₂ B₀ k) :
    X.IsBigColor₂ B₀ (X.mColor B₀) := by
  classical
  rw [BlkCaseObj.mColor, dif_pos hbig]
  exact Nat.find_spec hbig

/-- The color `ℓ` at `B₀` is the canonical one; it exists by
`Babai.BlkCaseObj.exists_isSmallColor₂`. -/
theorem isSmallColor₂_lColor {B₀ : Set ↥s} (hB₀ : B₀ ∈ X.blocks) :
    X.IsSmallColor₂ B₀ (X.lColor B₀) := by
  classical
  rw [BlkCaseObj.lColor, dif_pos (X.exists_isSmallColor₂ hB₀)]
  exact Nat.find_spec (X.exists_isSmallColor₂ hB₀)

/-- An edge of the returned graph from a marked point is an `m`-colored pair. -/
theorem mem_upccBip_E_iff {B₀ : Set ↥s} {x : ↥s} (hx : x ∈ X.linkClass B₀ (X.mColor B₀))
    {B : Set ↥s} (hB : B ∈ X.blkClass B₀ (X.lColor B₀)) :
    (x, B) ∈ (X.upccBip B₀).E ↔ X.c B {x} = X.mColor B₀ :=
  ⟨fun h => h.2.2.2, fun h => ⟨hx.1, hx.2, hB, h⟩⟩

/-- The marked points are exactly the points of `R_m⁻(B₀)`. -/
theorem upccBip_f_eq_one_iff {B₀ : Set ↥s} (x : ↥s) :
    (X.upccBip B₀).f x = 1 ↔ X.c B₀ {x} = X.mColor B₀ := by
  classical
  show (if X.c B₀ {x} = X.mColor B₀ then 1 else 0) = 1 ↔ _
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

open scoped Classical in
/-- §9.8, step 3.  **The symmetry defect of `V₁` in the returned graph is at least
`1/2`.**  (Claim of §9.8, version 2.5, lines 4333-4336.)

A set of twins of `V₁` has one `f`-color (`Babai.VColBipBlk.isTwin_iff`), so it lies
either inside `R_m⁻(B₀)` or inside its complement in `V₁`.  In the first case its members
have the same `m`-neighborhood among the blocks of `R_ℓ(B₀)`, so it has at most
`|R_m⁻(B₀)|/2 ≤ n₁/2` points (`Babai.BlkCaseObj.upccStep2_local_twins`).  In the second
case it has at most `n₁ - |R_m⁻(B₀)| ≤ n₁/2` points, because `m` is dominant at `B₀`. -/
theorem upccBip_defect₁ {B₀ : Set ↥s} (hB₀ : B₀ ∈ X.blocks)
    (hbig : ∃ k, X.IsBigColor₂ B₀ k) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    1 / 2 ≤ (X.upccBip B₀).defect₁ := by
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  have hm : X.IsBigColor₂ B₀ (X.mColor B₀) := X.isBigColor₂_mColor hbig
  have hl : X.IsSmallColor₂ B₀ (X.lColor B₀) := X.isSmallColor₂_lColor hB₀
  set n : ℕ := {x : ↥s | X.part₁ x}.ncard with hn
  set a : ℕ := (X.linkClass B₀ (X.mColor B₀)).ncard with ha
  have hsub : X.linkClass B₀ (X.mColor B₀) ⊆ {x : ↥s | X.part₁ x} := fun x hx => hx.1
  have han : a ≤ n := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hna : n < 2 * a := hm
  -- every set of twins of `V₁` has at most `n/2` points
  have hkey : ∀ T : Finset ↥s, (∀ x ∈ T, X.part₁ x) →
      IsTwinSet (X.upccBip B₀).Aut (↑T : Set ↥s) → 2 * T.card ≤ n := by
    intro T hpart htw
    -- the twin conditions, read on the graph
    have hpair : ∀ x ∈ T, ∀ y ∈ T, (X.upccBip B₀).f x = (X.upccBip B₀).f y ∧
        ∀ B ∈ X.blkClass B₀ (X.lColor B₀),
          ((x, B) ∈ (X.upccBip B₀).E ↔ (y, B) ∈ (X.upccBip B₀).E) := by
      intro x hx y hy
      rcases eq_or_ne x y with rfl | hne
      · exact ⟨rfl, fun _ _ => Iff.rfl⟩
      · exact (VColBipBlk.isTwin_iff _ (hpart x hx) (hpart y hy) hne).1
          (htw x hx y hy hne)
    by_cases hmark : ∃ x ∈ T, X.c B₀ {x} = X.mColor B₀
    · obtain ⟨x₀, hx₀T, hx₀m⟩ := hmark
      -- all of `T` is marked, so `T ⊆ R_m⁻(B₀)`
      have hTsub : (↑T : Set ↥s) ⊆ X.linkClass B₀ (X.mColor B₀) := by
        intro y hy
        refine ⟨hpart y hy, ?_⟩
        have hf := (hpair x₀ hx₀T y hy).1
        rw [(X.upccBip_f_eq_one_iff x₀).2 hx₀m] at hf
        exact (X.upccBip_f_eq_one_iff y).1 hf.symm
      have htwin : ∀ x ∈ (↑T : Set ↥s), ∀ y ∈ (↑T : Set ↥s),
          ∀ B ∈ X.blkClass B₀ (X.lColor B₀),
          (X.c B {x} = X.mColor B₀ ↔ X.c B {y} = X.mColor B₀) := by
        intro x hx y hy B hB
        have h := (hpair x hx y hy).2 B hB
        rw [X.mem_upccBip_E_iff (hTsub hx) hB, X.mem_upccBip_E_iff (hTsub hy) hB] at h
        exact h
      have := X.upccStep2_local_twins hB₀ hm hl hTsub htwin
      rw [Set.ncard_coe_finset] at this
      omega
    · -- no point of `T` is marked, so `T` and `R_m⁻(B₀)` are disjoint subsets of `V₁`
      push_neg at hmark
      have hdisj : Disjoint (↑T : Set ↥s) (X.linkClass B₀ (X.mColor B₀)) := by
        rw [Set.disjoint_left]
        intro z hz hz'
        exact hmark z hz hz'.2
      have hunion : (↑T : Set ↥s) ∪ X.linkClass B₀ (X.mColor B₀) ⊆ {x : ↥s | X.part₁ x} :=
        Set.union_subset (fun z hz => hpart z hz) hsub
      have hcard : (↑T : Set ↥s).ncard + a ≤ n := by
        rw [ha, ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
        exact Set.ncard_le_ncard hunion (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hcard
      omega
  -- hence the absolute symmetricity is at most `n/2`
  have hsym : 2 * (X.upccBip B₀).symmetricity₁ ≤ n := by
    have hle : (X.upccBip B₀).symmetricity₁ ≤ n / 2 := by
      refine Finset.sup_le fun T hT => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      have := hkey T hT.1 hT.2
      omega
    omega
  -- and the relative symmetry defect of `V₁` is at least `1/2`
  have hnpos : 0 < n := by omega
  have hV₁ : (X.upccBip B₀).V₁.ncard = n := rfl
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
  have hsymQ : 2 * ((X.upccBip B₀).symmetricity₁ : ℚ) ≤ (n : ℚ) := by exact_mod_cast hsym
  show (1 : ℚ) / 2 ≤ 1 - ((X.upccBip B₀).symmetricity₁ : ℚ) / ((X.upccBip B₀).V₁.ncard : ℚ)
  rw [hV₁]
  have hdiv : ((X.upccBip B₀).symmetricity₁ : ℚ) / (n : ℚ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hnQ (by norm_num : (0:ℚ) < 2)]
    linarith
  linarith

end BlkCaseObj

/-! ### Step 3 under a morphism

Every ingredient of step 3 is built from the coloring and the two parts alone, so a
morphism of `Babai.BlkUPCCCases` carries each of them to its counterpart.  These lemmas
are condition (ii) of Definition 6.0.1 for the construction, one piece at a time. -/

section Transport

variable {s t : Set Ω} {X : UPCCObj s} {Y : UPCCObj t} {φ : ↥s ≃ ↥t}
  (hφ : φ ∈ (BlkUPCCCases Ω).Iso X Y)

include hφ

/-- A morphism carries the first part onto the first part. -/
theorem upcc_part₁_image : {y : ↥t | Y.part₁ y} = φ '' {x : ↥s | X.part₁ x} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    exact ⟨φ.symm y, (hφ.1 (φ.symm y)).1 (by simpa using hy), by simp⟩
  · rintro ⟨x, hx, rfl⟩; exact (hφ.1 x).2 hx

/-- A morphism carries the blocks onto the blocks. -/
theorem upcc_blocks_image : Y.blocks = (fun A : Set ↥s => φ '' A) '' X.blocks := by
  ext B
  simp only [Set.mem_image]
  constructor
  · intro hB
    refine ⟨φ.symm '' B, ?_, Equiv.image_symm_image φ B⟩
    have h := hφ.2.1 (φ.symm '' B)
    rw [Equiv.image_symm_image] at h
    exact h.1 hB
  · rintro ⟨A, hA, rfl⟩
    exact (hφ.2.1 A).2 hA

/-- The color of a link edge from a block to a point is preserved. -/
theorem upcc_c_blk_singleton (B : Set ↥s) (x : ↥s) : Y.c (φ '' B) {φ x} = X.c B {x} := by
  have h := hφ.2.2 B {x}
  rwa [Set.image_singleton] at h

/-- The local color classes of `V₁` are carried to the local color classes. -/
theorem upcc_linkClass_map (B : Set ↥s) (k : ℕ) :
    Y.linkClass (φ '' B) k = φ '' X.linkClass B k := by
  ext y
  simp only [BlkCaseObj.linkClass, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨φ.symm y, ⟨(hφ.1 (φ.symm y)).1 (by simpa using h1), ?_⟩, by simp⟩
    have h3 := upcc_c_blk_singleton hφ B (φ.symm y)
    rw [Equiv.apply_symm_apply] at h3
    rw [← h3]; exact h2
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(hφ.1 x).2 h1, by rw [upcc_c_blk_singleton hφ B x]; exact h2⟩

/-- The color classes of `X₂` are carried to the color classes of `X₂`. -/
theorem upcc_blkClass_map (B : Set ↥s) (k : ℕ) :
    Y.blkClass (φ '' B) k = (fun A : Set ↥s => φ '' A) '' X.blkClass B k := by
  ext C
  simp only [BlkCaseObj.blkClass, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨φ.symm '' C, ⟨?_, ?_⟩, Equiv.image_symm_image φ C⟩
    · have h := hφ.2.1 (φ.symm '' C)
      rw [Equiv.image_symm_image] at h
      exact h.1 h1
    · have h3 := hφ.2.2 B (φ.symm '' C)
      rw [Equiv.image_symm_image] at h3
      rw [← h3]; exact h2
  · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
    exact ⟨(hφ.2.1 A).2 h1, by rw [hφ.2.2 B A]; exact h2⟩

/-- The branch condition of step 3 is an isomorphism invariant, color label by color
label. -/
theorem upcc_isBigColor₂_map (B : Set ↥s) (k : ℕ) :
    Y.IsBigColor₂ (φ '' B) k ↔ X.IsBigColor₂ B k := by
  unfold BlkCaseObj.IsBigColor₂
  rw [upcc_part₁_image hφ, upcc_linkClass_map hφ,
    Set.ncard_image_of_injective _ φ.injective,
    Set.ncard_image_of_injective _ φ.injective]

/-- The dominant color `m` is an isomorphism invariant. -/
theorem upcc_mColor_map (B : Set ↥s) : Y.mColor (φ '' B) = X.mColor B := by
  classical
  by_cases h : ∃ k, X.IsBigColor₂ B k
  · have h' : ∃ k, Y.IsBigColor₂ (φ '' B) k := by
      obtain ⟨k, hk⟩ := h; exact ⟨k, (upcc_isBigColor₂_map hφ B k).2 hk⟩
    rw [BlkCaseObj.mColor, BlkCaseObj.mColor, dif_pos h, dif_pos h']
    exact le_antisymm (Nat.find_le ((upcc_isBigColor₂_map hφ B _).2 (Nat.find_spec h)))
      (Nat.find_le ((upcc_isBigColor₂_map hφ B _).1 (Nat.find_spec h')))
  · have h' : ¬ ∃ k, Y.IsBigColor₂ (φ '' B) k := by
      rintro ⟨k, hk⟩; exact h ⟨k, (upcc_isBigColor₂_map hφ B k).1 hk⟩
    rw [BlkCaseObj.mColor, BlkCaseObj.mColor, dif_neg h, dif_neg h']

/-- The defining condition of the color `ℓ` is an isomorphism invariant. -/
theorem upcc_isSmallColor₂_map (B : Set ↥s) (k : ℕ) :
    Y.IsSmallColor₂ (φ '' B) k ↔ X.IsSmallColor₂ B k := by
  have himg : Function.Injective (fun A : Set ↥s => φ '' A) :=
    Set.image_injective.2 φ.injective
  have hb : Y.blocks.ncard = X.blocks.ncard := by
    rw [upcc_blocks_image hφ, Set.ncard_image_of_injective _ himg]
  have hcl : (Y.blkClass (φ '' B) k).ncard = (X.blkClass B k).ncard := by
    rw [upcc_blkClass_map hφ, Set.ncard_image_of_injective _ himg]
  unfold BlkCaseObj.IsSmallColor₂
  rw [hb, hcl]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro ⟨C, hC, hne, hcol⟩
    refine ⟨φ.symm '' C, ?_, ?_, ?_⟩
    · have h := hφ.2.1 (φ.symm '' C)
      rw [Equiv.image_symm_image] at h
      exact h.1 hC
    · intro hc
      exact hne (by rw [← Equiv.image_symm_image φ C, hc])
    · have h3 := hφ.2.2 B (φ.symm '' C)
      rw [Equiv.image_symm_image] at h3
      rw [← h3]; exact hcol
  · rintro ⟨A, hA, hne, hcol⟩
    exact ⟨φ '' A, (hφ.2.1 A).2 hA, fun hc => hne (himg hc), by rw [hφ.2.2 B A]; exact hcol⟩

/-- The color `ℓ` is an isomorphism invariant. -/
theorem upcc_lColor_map (B : Set ↥s) : Y.lColor (φ '' B) = X.lColor B := by
  classical
  by_cases h : ∃ k, X.IsSmallColor₂ B k
  · have h' : ∃ k, Y.IsSmallColor₂ (φ '' B) k := by
      obtain ⟨k, hk⟩ := h; exact ⟨k, (upcc_isSmallColor₂_map hφ B k).2 hk⟩
    rw [BlkCaseObj.lColor, BlkCaseObj.lColor, dif_pos h, dif_pos h']
    exact le_antisymm (Nat.find_le ((upcc_isSmallColor₂_map hφ B _).2 (Nat.find_spec h)))
      (Nat.find_le ((upcc_isSmallColor₂_map hφ B _).1 (Nat.find_spec h')))
  · have h' : ¬ ∃ k, Y.IsSmallColor₂ (φ '' B) k := by
      rintro ⟨k, hk⟩; exact h ⟨k, (upcc_isSmallColor₂_map hφ B k).1 hk⟩
    rw [BlkCaseObj.lColor, BlkCaseObj.lColor, dif_neg h, dif_neg h']

/-- §9.8, step 3.  **The returned graph is carried to the returned graph** of the
individualized image vertex: the canonicity of step 3. -/
theorem upccBip_isIsoTo (B₀ : Set ↥s) :
    (X.upccBip B₀).IsIsoTo (Y.upccBip (φ '' B₀)) φ where
  part₁ x := hφ.1 x
  blocks B := by
    show φ '' B ∈ Y.blkClass (φ '' B₀) (Y.lColor (φ '' B₀))
      ↔ B ∈ X.blkClass B₀ (X.lColor B₀)
    rw [upcc_lColor_map hφ, upcc_blkClass_map hφ]
    exact (Set.image_injective.2 φ.injective).mem_set_image
  edges x B := by
    show (Y.part₁ (φ x) ∧ Y.c (φ '' B₀) {φ x} = Y.mColor (φ '' B₀) ∧
        φ '' B ∈ Y.blkClass (φ '' B₀) (Y.lColor (φ '' B₀)) ∧
        Y.c (φ '' B) {φ x} = Y.mColor (φ '' B₀))
      ↔ (X.part₁ x ∧ X.c B₀ {x} = X.mColor B₀ ∧
        B ∈ X.blkClass B₀ (X.lColor B₀) ∧ X.c B {x} = X.mColor B₀)
    rw [upcc_c_blk_singleton hφ B₀ x, upcc_c_blk_singleton hφ B x, upcc_mColor_map hφ,
      upcc_lColor_map hφ, upcc_blkClass_map hφ]
    refine and_congr (hφ.1 x) (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
    exact (Set.image_injective.2 φ.injective).mem_set_image
  color₁ x := by
    show (if Y.c (φ '' B₀) {φ x} = Y.mColor (φ '' B₀) then 1 else 0)
      = (if X.c B₀ {x} = X.mColor B₀ then 1 else 0)
    rw [upcc_c_blk_singleton hφ B₀ x, upcc_mColor_map hφ]
  color₂ _ := rfl
  hint _ _ := rfl

end Transport

/-! ### The outcomes of step 3 -/

open scoped Classical in
/-- §9.8, step 3.  **The outcomes of step 3**: one returned graph per individualized
vertex `x ∈ V₂` at which the link has a dominant color.

`Babai.FindsAtMultCost.of_outcomes_sub` asks that *every* member of the family be a
solution, and the symmetry defect of the returned graph is `≥ 1/2` exactly when the link
has a dominant color at the individualized vertex; so the family of the individualized
vertices is filtered by that condition, which is a condition on the object alone and is
therefore invariant under isomorphisms.  (By the semiregularity of the constituents of the
link the condition in fact holds at every vertex of `V₂` as soon as it holds at one, but
the filter avoids the appeal to §3.4.) -/
noncomputable def BlkCaseObj.upccStep2Out {s : Set Ω} (X : UPCCObj s) :
    Set ((Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s) :=
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  (fun B₀ : Set ↥s =>
      (⟨⟨s, subset_rfl⟩, Sum.inr (X.upccBip B₀)⟩ :
        (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s)) ''
    {B₀ | B₀ ∈ X.blocks ∧ ∃ k, X.IsBigColor₂ B₀ k}

/-- §9.8, **step 3 of Procedure Reduce-by-UPCC**.  *"Else, let `m ∈ J` be the dominant
color in `X₁₂` … Let `Y` be the local constituent `Y = X_m[R_m⁻(x), R_ℓ(x)]` … return
`X`."*  (Version 2.5, lines 4327-4332.)

The Claim of §9.8 for this branch: *"reduces `n₂` by half while maintaining symmetry defect
`≥ 1/2`"*, at the multiplicative cost `n₂` of the individualized vertex of `V₂`.  The
halving is the defining property of the color `ℓ`
(`Babai.BlkCaseObj.isSmallColor₂_lColor`), and the symmetry defect is
`Babai.BlkCaseObj.upccBip_defect₁`. -/
theorem case_9_8_step2 :
    FindsAtMultCost ((BlkUPCCCases Ω).full fun _ X => ¬ UPCCSplits X)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkCases.numBlocks ⟨X.car, X.obj.1⟩)
      (fun X Z => IsBlkImprimitiveOutcome (BlkCases.V₁ ⟨X.car, X.obj.1⟩)
        (BlkCases.numBlocks ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => X.obj.1.upccStep2Out)
    (fun X => ?_) (fun X => Set.Finite.image _ (Set.toFinite _)) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · -- non-empty: the branch condition fails, so some vertex of `V₂` has a dominant color
    have hns := X.obj.2
    unfold UPCCSplits at hns
    push_neg at hns
    obtain ⟨B, hB, k, hk⟩ := hns
    exact ⟨_, ⟨B, ⟨hB, ⟨k, hk⟩⟩, rfl⟩⟩
  · -- cost: one outcome per vertex of `V₂`
    refine le_trans (Set.ncard_image_le (Set.toFinite _)) ?_
    exact Set.ncard_le_ncard (fun _ h => h.1) (Set.toFinite _)
  · obtain ⟨B₀, ⟨hB₀, hbig⟩, rfl⟩ := hZ
    refine ⟨_, ⟨f '' B₀, ⟨(hf.2.1 B₀).2 hB₀, ?_⟩, rfl⟩, ⟨f, fun _ => rfl, ?_⟩⟩
    · obtain ⟨k, hk⟩ := hbig
      exact ⟨k, (upcc_isBigColor₂_map hf B₀ k).2 hk⟩
    · exact upccBip_isIsoTo hf B₀
  · obtain ⟨B₀, ⟨hB₀, hbig⟩, rfl⟩ := hZ
    letI : Fintype ↥X.car := Fintype.ofFinite _
    letI : DecidableEq ↥X.car := Classical.decEq _
    refine ⟨rfl, ?_, X.obj.1.upccBip_defect₁ hB₀ hbig⟩
    exact (X.obj.1.isSmallColor₂_lColor hB₀).2

/-- §9.8 (UPCC case).  *"Claim.  Procedure Reduce-by-UPCC makes significant progress.
Specifically, it either achieves goal (a) or reduces `n₂` by half while maintaining
symmetry defect `≥ 1/2` in each part.  The multiplicative cost is `n₂`."*  (Version 2.5,
lines 4318-4322.)

The two outcomes have the same shape as the two outcomes of Lemma 9.6.1 — a canonical
colored `1/2`-partition of `V₁`, or a canonical bipartite graph on `V₁` and at most `n₂/2`
blocks in which the symmetry defect of `V₁` is at least `1/2` — so the outcome predicate is
`Babai.IsBlkImprimitiveOutcome`, the one of §9.6.

The proof is the case distinction of Procedure Reduce-by-UPCC on its branch condition
`Babai.UPCCSplits` (*"if there is no `α`-dominant color in `X₁₂`"*, with `α = 1/2`): the
two branches are `Babai.case_9_8_step1` (step 2 of the procedure, the `x`-local coloring of
`V₁`) and `Babai.case_9_8_step2` (step 3, the local constituent).  The running time is
pending. -/
theorem case_9_8 :
    FindsAtMultCost (BlkUPCCCases Ω)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkCases.numBlocks X)
      (fun X Z => IsBlkImprimitiveOutcome (BlkCases.V₁ X) (BlkCases.numBlocks X) Z) := by
  refine (FindsAtMultCost.cases
    (C := BlkUPCCCases Ω)
    (P := fun _ X => UPCCSplits X)
    (costp := fun Z => BlkCases.numBlocks Z)
    (costn := fun Z => BlkCases.numBlocks Z)
    (Good := fun Z W => IsBlkImprimitiveOutcome (BlkCases.V₁ Z) (BlkCases.numBlocks Z) W)
    (fun h hx => upccSplits_congr h hx) case_9_8_step1 case_9_8_step2).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

end Babai
