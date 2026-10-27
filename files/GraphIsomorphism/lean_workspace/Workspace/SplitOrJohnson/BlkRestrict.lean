/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: restricting an input of the block design case to a sub-family of its blocks.
-/
import Workspace.SplitOrJohnson.BlockDesignCase
import Workspace.SplitOrJohnson.Minor

/-!
# §9.7  The input restricted to a sub-family of its blocks

Three of the four exits of §9.7 — Case 2 (*"If `V₂ ∖ C` is selected, we have made
significant progress (reduced `|V₂|` by half)"*), Cases 3a1 and 3a2, and Case 3b — return
*the same kind of object*: the input of §9.7 with its second part `V₂` cut down to a
canonical sub-family `U` of its blocks, read as an admissible input of Theorem 9.2.2
(`Babai.BipBlockInputs`).  This file builds that object once, together with the three facts
the exits need of it.

| Paper | Lean |
|---|---|
| the bipartite graph `X = (V₁, V₂; Rᵢ)` that §9.7 reads the neighborhoods in | `Babai.BlkCaseObj.linkGraph` |
| the induced subgraph `X[V₁, U]` | `Babai.VColBipBlk.restrictBlk` |
| Lemma 9.3.2 for such a graph | `Babai.lemma_9_3_2_blk` |
| Procedure Reduce-Part2-by-Color for such a graph | `Babai.reducePart2ByColorBlk` |
| the restricted input as an object of Theorem 9.2.2 | `Babai.restrictObj` |
| *"significant progress: `|V₂|` reduced"* | `Babai.good97_restrict` |

## What is proved here

1. `Babai.BlkCaseObj.linkGraph` reads an object of §9.7 as a vertex-colored bipartite
   graph whose second part is the family of blocks (`Babai.VColBipBlk`): the edges are the
   pairs `(x, B)` with `x ∈ V₁`, `B` a block and `c({x}, B) = Rᵢ`, the constituent that
   `Babai.BlkCaseObj.nbhd` reads (`Babai.BlkCaseObj.linkColor`); the point coloring is
   `x ↦ c({x}, {x})` and the block coloring is `B ↦ c(B, B)`, the vertex coloring of the
   coherent configuration of step 3 of §9.4.
2. `Babai.VColBipBlk.restrictBlk` is the induced subgraph `X[V₁, U]` on a sub-family `U`
   of the blocks, `Babai.lemma_9_3_2_blk` is Lemma 9.3.2 for it, and
   `Babai.reducePart2ByColorBlk` is Procedure Reduce-Part2-by-Color.  The proof of
   Lemma 9.3.2 is the paper's, through the twin characterisation
   `Babai.VColBipBlk.isTwin_iff`.
3. `Babai.BlkCaseObj.linkGraph_isIsoTo` and `Babai.VColBipBlk.restrictBlk_isIsoTo` make
   both constructions functorial: an isomorphism of inputs that carries `U` to `U'` is an
   isomorphism of the restricted objects.  This is the shape
   `Babai.FindsAtMultCost.of_outcomes_sub` consumes.
4. `Babai.restrictObj_pred` and `Babai.good97_restrict`: with
   `10|U| ≤ 9n₂` the restricted object is an outcome of §9.7 (`Babai.Good97`).

## The symmetry defect that Reduce-Part2-by-Color leaves

Procedure Reduce-Part2-by-Color keeps the **absolute** symmetry defect of `V₁` at
`≥ (n₁ − 1)/2`, so the relative defect at `≥ (n₁ − 1)/(2n₁) = 1/2 − 1/(2n₁)`, which is
below the `1/2` that Prop. 2.4.30 gives elsewhere.  The input of Theorem 9.2.2 asks for
`≥ 1 − α`, and `α ≥ 2/3` on the category of §9.7, so `1 − α ≤ 1/3` and
`1/2 − 1/(2n₁) ≥ 1/3` as soon as `n₁ ≥ 3` (`Babai.defect_of_symDefect_ge`).  In §9.7 the
Cases 2 and 3 have `n₁ ≥ 5`: there `n₂ < n₁` gives `d₁ + 2 ≤ n₂`
(`Babai.BlkCaseObj.two_le_d₁_and_add_two_le`), hence `n₂ ≥ 4` and `n₁ ≥ 5`.  This is not a
correction; the paper never states the arithmetic.
-/

namespace Babai

/-! ### The absolute symmetry defect of `V₁`, for a graph whose second part is blocks

Word for word `Babai.VColBip.symDefect₁` and its two companions in
`Workspace/SplitOrJohnson/Minor.lean`, with the vertices of `V₂` replaced by the blocks. -/

namespace VColBipBlk

variable {s : Type} {κ : Type} [Zero κ] (X : VColBipBlk s κ)

/-- Definition 2.4.29.  *"`|Ωᵢ ∖ Tᵢ|` is the absolute symmetry defect of `Ωᵢ` in `X`."*
The case `i = 1`, as a rational number (`symmetricity₁ ≤ |V₁|`, so nothing is truncated). -/
noncomputable def symDefect₁ [Fintype s] [DecidableEq s] : ℚ :=
  (X.V₁.ncard : ℚ) - (X.symmetricity₁ : ℚ)

variable {X}

open scoped Classical in
/-- A set of twins inside `V₁` is no larger than the symmetricity of `V₁`. -/
theorem card_le_symmetricity₁ [Fintype s] [DecidableEq s] {T : Finset s}
    (hT₁ : ∀ x ∈ T, X.part₁ x) (hT : IsTwinSet X.Aut (↑T : Set s)) :
    T.card ≤ X.symmetricity₁ := by
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hT₁, hT⟩

open scoped Classical in
/-- The symmetricity of `V₁` is attained by a set of twins inside `V₁`. -/
theorem exists_twinSet_card_eq_symmetricity₁ [Fintype s] [DecidableEq s] :
    ∃ T : Finset s, (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s) ∧
      T.card = X.symmetricity₁ := by
  have hne : (Finset.univ.filter fun T : Finset s =>
      (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by simp, ?_⟩
    intro x hx
    simp at hx
  obtain ⟨T, hT, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  exact ⟨T, hT.1, hT.2, hsup.symm⟩

/-! ### The induced subgraph on a sub-family of the blocks -/

open scoped Classical in
/-- Definition 2.4.25, for a graph whose second part is a family of blocks: the induced
subgraph `X[V₁, U]`, whose second part is the sub-family `U` of the blocks and whose edges
are the edges of `X` that end in `U`.

Unlike `Babai.VColBip.restrict₂`, the vertices of the second part outside `U` are dropped
and not kept as isolated vertices: `Babai.VColBipBlk.numBlocks` is what the measure of
progress of §9.5 counts, so the exits of §9.7 need it to be `|U|`.  The twins of `V₁` are
the same either way, because a point of `V₁` is joined to no block outside `U`. -/
noncomputable def restrictBlk (U : Set (Set s)) : VColBipBlk s κ where
  part₁ := X.part₁
  blocks := X.blocks ∩ U
  blocks_nonempty B hB := X.blocks_nonempty B hB.1
  blocks_disjoint B hB B' hB' hne := X.blocks_disjoint B hB.1 B' hB'.1 hne
  blocks_off₁ B hB := X.blocks_off₁ B hB.1
  E := {p | p ∈ X.E ∧ p.2 ∈ U}
  E_sub p hp := ⟨(X.E_sub p hp.1).1, (X.E_sub p hp.1).2, hp.2⟩
  f := X.f
  g := fun B => if B ∈ U then X.g B else 0
  g_off B hB := by
    by_cases h : B ∈ U
    · rw [if_pos h]
      exact X.g_off B fun hb => hB ⟨hb, h⟩
    · rw [if_neg h]
  -- The hint is restricted to the kept blocks and padded by `0` elsewhere.
  h := fun A B => if A ∈ U ∧ B ∈ U then X.h A B else 0
  h_off A B hAB := by
    by_cases hU : A ∈ U ∧ B ∈ U
    · rw [if_pos hU]
      rcases hAB with hA | hB
      · exact X.h_off A B (Or.inl fun hb => hA ⟨hb, hU.1⟩)
      · exact X.h_off A B (Or.inr fun hb => hB ⟨hb, hU.2⟩)
    · rw [if_neg hU]

@[simp] theorem restrictBlk_part₁ (U : Set (Set s)) :
    (X.restrictBlk U).part₁ = X.part₁ := rfl

@[simp] theorem restrictBlk_V₁ (U : Set (Set s)) : (X.restrictBlk U).V₁ = X.V₁ := rfl

@[simp] theorem restrictBlk_blocks (U : Set (Set s)) :
    (X.restrictBlk U).blocks = X.blocks ∩ U := rfl

@[simp] theorem restrictBlk_f (U : Set (Set s)) : (X.restrictBlk U).f = X.f := rfl

theorem mem_restrictBlk_E {U : Set (Set s)} {p : s × Set s} :
    p ∈ (X.restrictBlk U).E ↔ p ∈ X.E ∧ p.2 ∈ U := Iff.rfl

/-- The number of blocks of the restriction is `|U|`, as soon as `U` is a sub-family of the
blocks. -/
theorem restrictBlk_numBlocks {U : Set (Set s)} (hU : U ⊆ X.blocks) :
    (X.restrictBlk U).numBlocks = U.ncard := by
  rw [numBlocks, restrictBlk_blocks, Set.inter_eq_self_of_subset_right hU]

variable [DecidableEq s]

/-- The step *"all vertices in `D₁ ∩ D₂` are twins in `X`"* of the proof of Lemma 9.3.2,
for a graph whose second part is a family of blocks: a pair of points of `V₁` that is a
pair of twins in both `X[V₁, U₁]` and `X[V₁, U₂]` is a pair of twins in `X`, as soon as
`U₁ ∪ U₂` covers the blocks.

The proof is the twin characterisation `Babai.VColBipBlk.isTwin_iff` read three times:
twins have the same color and the same neighboring blocks, and every block lies in `U₁` or
in `U₂`. -/
theorem isTwin_of_isTwin_restrictBlk {U₁ U₂ : Set (Set s)} (hcov : X.blocks ⊆ U₁ ∪ U₂)
    {x x' : s} (hx : X.part₁ x) (hx' : X.part₁ x')
    (h₁ : IsTwin (X.restrictBlk U₁).Aut x x') (h₂ : IsTwin (X.restrictBlk U₂).Aut x x') :
    IsTwin X.Aut x x' := by
  have hne : x ≠ x' := h₁.1
  obtain ⟨hf, hnb₁⟩ := ((X.restrictBlk U₁).isTwin_iff hx hx' hne).1 h₁
  obtain ⟨-, hnb₂⟩ := ((X.restrictBlk U₂).isTwin_iff hx hx' hne).1 h₂
  refine (X.isTwin_iff hx hx' hne).2 ⟨hf, fun B hB => ?_⟩
  rcases hcov hB with hU | hU
  · have := hnb₁ B ⟨hB, hU⟩
    simpa only [mem_restrictBlk_E, and_iff_left hU] using this
  · have := hnb₂ B ⟨hB, hU⟩
    simpa only [mem_restrictBlk_E, and_iff_left hU] using this

end VColBipBlk

/-! ### Lemma 9.3.2 and Procedure Reduce-Part2-by-Color, for such a graph -/

variable {s : Type} [Fintype s] [DecidableEq s] {κ : Type} [Zero κ]

/-- Lemma 9.3.2, for a graph whose second part is a family of blocks.  *"In at least one of
`X₁` and `X₂`, the symmetry defect of `V₁` is at least `(n₁ − 1)/2`."*  (Version 2.5,
lines 4085–4090.)

Here `Xⱼ = X[V₁, Uⱼ]` for a covering `V₂ = U₁ ∪ U₂` of the blocks, and `X` has no twins in
`V₁`, as in the input of Procedure Reduce-Part2-by-Color.

Paper's proof: *"Assume for a contradiction that for `j = 1, 2` there exists a twin
equivalence class `Dⱼ ⊆ V₁` of size `|Dⱼ| ≥ 1 + (n₁/2)` in `Xⱼ`.  It follows that
`|D₁ ∩ D₂| ≥ 2`.  On the other hand, all vertices in `Dⱼ` are twins with respect to `Cⱼ`;
therefore all vertices in `D₁ ∩ D₂` are twins in `X`.  Since `X` has no twins, we infer
`|D₁ ∩ D₂| ≤ 1`, a contradiction."* -/
theorem lemma_9_3_2_blk (X : VColBipBlk s κ)
    (hno : ∀ x, X.part₁ x → ∀ y, X.part₁ y → ¬ IsTwin X.Aut x y)
    {U₁ U₂ : Set (Set s)} (hcov : X.blocks ⊆ U₁ ∪ U₂) :
    ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrictBlk U₁).symDefect₁ ∨
      ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrictBlk U₂).symDefect₁ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  set n₁ := X.V₁.ncard with hn₁
  have hbig : ∀ U : Set (Set s), (X.restrictBlk U).symDefect₁ < ((n₁ : ℚ) - 1) / 2 →
      (n₁ : ℚ) + 1 < 2 * ((X.restrictBlk U).symmetricity₁ : ℚ) := by
    intro U hU
    have hV : (X.restrictBlk U).V₁.ncard = n₁ := by rw [hn₁, VColBipBlk.restrictBlk_V₁]
    rw [VColBipBlk.symDefect₁, hV] at hU
    linarith
  have hb₁ := hbig U₁ h₁
  have hb₂ := hbig U₂ h₂
  obtain ⟨D₁, hD₁p, hD₁t, hD₁c⟩ :=
    VColBipBlk.exists_twinSet_card_eq_symmetricity₁ (X := X.restrictBlk U₁)
  obtain ⟨D₂, hD₂p, hD₂t, hD₂c⟩ :=
    VColBipBlk.exists_twinSet_card_eq_symmetricity₁ (X := X.restrictBlk U₂)
  set V : Finset s := Finset.univ.filter fun x => X.part₁ x with hV
  have hVcard : V.card = n₁ := by
    rw [hn₁]
    have hVV : X.V₁ = (↑V : Set s) := by
      ext x; simp [hV, VColBipBlk.V₁]
    rw [hVV, Set.ncard_coe_finset]
  have hsub₁ : D₁ ⊆ V := by
    intro x hx
    simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hD₁p x hx
  have hsub₂ : D₂ ⊆ V := by
    intro x hx
    simp only [hV, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hD₂p x hx
  have hcard : n₁ + 2 ≤ D₁.card + D₂.card := by
    have e₁ : (n₁ : ℚ) + 1 < 2 * (D₁.card : ℚ) := by rw [hD₁c]; exact hb₁
    have e₂ : (n₁ : ℚ) + 1 < 2 * (D₂.card : ℚ) := by rw [hD₂c]; exact hb₂
    have : (n₁ : ℚ) + 1 < (D₁.card : ℚ) + D₂.card := by linarith
    exact_mod_cast this
  have hunion : (D₁ ∪ D₂).card ≤ n₁ := by
    rw [← hVcard]
    exact Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
  have hinter : 2 ≤ (D₁ ∩ D₂).card := by
    have := Finset.card_union_add_card_inter D₁ D₂
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hinter
  have hxp : X.part₁ x := hD₁p x (Finset.mem_inter.1 hx).1
  have hyp : X.part₁ y := hD₁p y (Finset.mem_inter.1 hy).1
  have ht₁ := hD₁t x (by simpa using (Finset.mem_inter.1 hx).1) y
    (by simpa using (Finset.mem_inter.1 hy).1) hxy
  have ht₂ := hD₂t x (by simpa using (Finset.mem_inter.1 hx).2) y
    (by simpa using (Finset.mem_inter.1 hy).2) hxy
  exact hno x hxp y hyp (X.isTwin_of_isTwin_restrictBlk hcov hxp hyp ht₁ ht₂)

open scoped Classical in
/-- Procedure Reduce-Part2-by-Color, for a graph whose second part is a family of blocks.
(Version 2.5, lines 4076–4084.)

> *Input:*  A colored bipartite graph `X = (V₁, V₂; E, f)` where `|V₂| < α|V₁|` such that
> there are no twins in `V₁`; a partition `V₂ = C₁ ∪ C₂` where each `Cⱼ` is a union of
> color classes.
> *Output:* `j ∈ {1,2}` such that in the induced colored bipartite subgraph
> `Xⱼ = X[V₁, Cⱼ]` the symmetry defect of `V₁` is `≥ (n₁ − 1)/2` where `n₁ = |V₁|`.

The procedure is a function of the graph and the two parts: it returns the part selected,
which is how §9.7 uses it (*"if `V₂ ∖ C` is selected …"*).  It is total; the two hypotheses
of the input specification enter only in `Babai.reducePart2ByColorBlk_spec`, which is
Lemma 9.3.2.  The condition *"each `Cⱼ` is a union of color classes"* is not used by the
output condition; it is what makes the selected part canonical. -/
noncomputable def reducePart2ByColorBlk (X : VColBipBlk s κ) (U₁ U₂ : Set (Set s)) :
    Set (Set s) :=
  if ((X.V₁.ncard : ℚ) - 1) / 2 ≤ (X.restrictBlk U₁).symDefect₁ then U₁ else U₂

/-- Procedure Reduce-Part2-by-Color: the output condition, by Lemma 9.3.2. -/
theorem reducePart2ByColorBlk_spec (X : VColBipBlk s κ)
    (hno : ∀ x, X.part₁ x → ∀ y, X.part₁ y → ¬ IsTwin X.Aut x y)
    {U₁ U₂ : Set (Set s)} (hcov : X.blocks ⊆ U₁ ∪ U₂) :
    ((X.V₁.ncard : ℚ) - 1) / 2 ≤
      (X.restrictBlk (reducePart2ByColorBlk X U₁ U₂)).symDefect₁ := by
  classical
  unfold reducePart2ByColorBlk
  split_ifs with h
  · exact h
  · exact (lemma_9_3_2_blk X hno hcov).resolve_left h

/-- Procedure Reduce-Part2-by-Color returns one of the two parts. -/
theorem reducePart2ByColorBlk_mem (X : VColBipBlk s κ) (U₁ U₂ : Set (Set s)) :
    reducePart2ByColorBlk X U₁ U₂ = U₁ ∨ reducePart2ByColorBlk X U₁ U₂ = U₂ := by
  classical
  unfold reducePart2ByColorBlk; split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The absolute symmetry defect that Procedure Reduce-Part2-by-Color leaves, read as a
relative defect: `1 − symmetricity/n₁ ≥ (n₁ − 1)/(2n₁) ≥ 1/3` for `n₁ ≥ 3`.

The input of Theorem 9.2.2 asks for a relative symmetry defect `≥ 1 − α`, and the category
of §9.7 has `α ≥ 2/3`, so `1/3` is enough.  See the module docstring for why `n₁ ≥ 3`
holds in Cases 2 and 3 of §9.7. -/
theorem defect_of_symDefect_ge {X : VColBipBlk s κ} (hn₁ : 3 ≤ X.V₁.ncard)
    (h : ((X.V₁.ncard : ℚ) - 1) / 2 ≤ X.symDefect₁) : (1 : ℚ) / 3 ≤ X.defect₁ := by
  have hn : (3 : ℚ) ≤ (X.V₁.ncard : ℚ) := by exact_mod_cast hn₁
  have hpos : (0 : ℚ) < (X.V₁.ncard : ℚ) := by linarith
  rw [VColBipBlk.symDefect₁] at h
  have hs : (X.symmetricity₁ : ℚ) ≤ ((X.V₁.ncard : ℚ) + 1) / 2 := by linarith
  rw [VColBipBlk.defect₁]
  have hle : (X.symmetricity₁ : ℚ) / (X.V₁.ncard : ℚ) ≤ 2 / 3 := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The bipartite graph of §9.7, read as an object of `Babai.VColBipBlk`

§9.7 works inside the bipartite graph `X = (V₁, V₂; Rᵢ)` that step 8 of §9.4 picks out of
the link: `Rᵢ` is the constituent `Babai.BlkCaseObj.linkColor`, and the neighborhood of a
point `v ∈ V₁` in it is `Babai.BlkCaseObj.nbhd v`, the hyperedge `X(v)` of the hypergraph
`H`.  The same graph, read as an object of `Babai.VColBipBlk`, is what the three exits of
§9.7 hand back — restricted to a sub-family of the blocks.

The two colorings are the vertex coloring of the coherent configuration of step 3 of §9.4:
a point `x ∈ V₁` gets `c({x}, {x})` and a block `B` gets `c(B, B)`.  They are preserved by
a morphism of §9.7 (the field `col` of `Babai.BlkCaseObj.IsMorphOn`), and adding them can
only *raise* the symmetry defect of `V₁`, so nothing below is weakened by them. -/

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

open scoped Classical in
/-- §9.7.  *"the bipartite graph `X = (V₁, V₂; Rᵢ)`"* that §9.7 reads the neighborhoods in,
as an object of `Babai.VColBipBlk`: the second part is the family of blocks, and `(x, B)`
is an edge exactly when `x ∈ V₁`, `B` is a block, and `c({x}, B)` is the constituent
`Babai.BlkCaseObj.linkColor`. -/
noncomputable def linkGraph (X : BlkCaseObj s Case) : VColBipBlk ↥s ℕ where
  part₁ := X.part₁
  blocks := X.blocks
  blocks_nonempty := X.blocks_nonempty
  blocks_disjoint := X.blocks_disjoint
  blocks_off₁ := X.blocks_off₁
  E := {p | X.part₁ p.1 ∧ p.2 ∈ X.blocks ∧ X.c {p.1} p.2 = X.linkColor}
  E_sub p hp := ⟨hp.1, hp.2.1⟩
  f := fun x => X.c {x} {x}
  g := fun B => if B ∈ X.blocks then X.c B B else 0
  g_off B hB := by rw [if_neg hB]
  -- No hint is attached here: the outcomes of §9.7 that this graph serves are the ones
  -- that reduce `n₂`, and they need none.  The third outcome of §9.5, *"`X₂` moves from
  -- clique to UPCC"*, is the one that will set `h`; see the entry on §9.7 Cases 3a1, 3a2
  -- and 3b in the corrected paper.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

@[simp] theorem linkGraph_part₁ (X : BlkCaseObj s Case) :
    X.linkGraph.part₁ = X.part₁ := rfl

@[simp] theorem linkGraph_blocks (X : BlkCaseObj s Case) :
    X.linkGraph.blocks = X.blocks := rfl

@[simp] theorem linkGraph_V₁ (X : BlkCaseObj s Case) :
    X.linkGraph.V₁ = {x | X.part₁ x} := rfl

@[simp] theorem linkGraph_numBlocks (X : BlkCaseObj s Case) :
    X.linkGraph.numBlocks = X.n₂ := rfl

/-- The edges of `Babai.BlkCaseObj.linkGraph` are the neighborhoods
`Babai.BlkCaseObj.nbhd`. -/
theorem mem_linkGraph_E (X : BlkCaseObj s Case) (x : ↥s) (B : Set ↥s) :
    (x, B) ∈ X.linkGraph.E ↔ X.part₁ x ∧ B ∈ X.nbhd x := Iff.rfl

/-- §9.7.  *"This hypergraph has no multiple edges because there are no twins in `V₁`"*, in
the form Procedure Reduce-Part2-by-Color asks for: the bipartite graph
`X = (V₁, V₂; Rᵢ)` has no twins in `V₁`.

Two twins of `V₁` have the same neighboring blocks
(`Babai.VColBipBlk.nbhd_eq_of_isTwin`), hence the same `Babai.BlkCaseObj.nbhd`, hence are
equal by `Babai.BlkCaseObj.nbhd_injective` (Theorem 3.4.11 applied to the constituent
`Rᵢ`). -/
theorem linkGraph_noTwins (X : BlkDesignObj s) :
    ∀ x, X.linkGraph.part₁ x → ∀ y, X.linkGraph.part₁ y →
      ¬ IsTwin X.linkGraph.Aut x y := by
  classical
  intro x hx y hy htw
  refine htw.1 (X.nbhd_injective hx hy ?_)
  ext B
  constructor
  · intro hB
    have := (VColBipBlk.nbhd_eq_of_isTwin (X := X.linkGraph) hx hy htw
      (B := B) (X.nbhd_subset_blocks x hB)).1 ⟨hx, hB⟩
    exact this.2
  · intro hB
    have := (VColBipBlk.nbhd_eq_of_isTwin (X := X.linkGraph) hx hy htw
      (B := B) (X.nbhd_subset_blocks y hB)).2 ⟨hy, hB⟩
    exact this.2

end BlkCaseObj

/-! ### Functoriality -/

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- An isomorphism of inputs of §9.7 is an isomorphism of the bipartite graphs
`X = (V₁, V₂; Rᵢ)`: it preserves the two parts, the blocks, the constituent
`Babai.BlkCaseObj.linkColor` (`Babai.BlkCaseObj.IsMorphOn.linkColor_eq`) and the two
colorings (the field `col`). -/
theorem linkGraph_isIsoTo (h : X.IsMorphOn Y φ) : X.linkGraph.IsIsoTo Y.linkGraph φ := by
  classical
  refine ⟨h.part₁, h.blocks, fun x B => ?_, fun x => ?_, fun B => ?_, fun _ _ => rfl⟩
  · show (Y.part₁ (φ x) ∧ φ '' B ∈ Y.blocks ∧ Y.c {φ x} (φ '' B) = Y.linkColor)
      ↔ (X.part₁ x ∧ B ∈ X.blocks ∧ X.c {x} B = X.linkColor)
    rw [h.part₁ x, h.blocks B, h.c_singleton x B, h.linkColor_eq]
  · show Y.c {φ x} {φ x} = X.c {x} {x}
    have := h.c_singleton x {x}
    rwa [Set.image_singleton] at this
  · show (if φ '' B ∈ Y.blocks then Y.c (φ '' B) (φ '' B) else 0)
      = (if B ∈ X.blocks then X.c B B else 0)
    by_cases hB : B ∈ X.blocks
    · rw [if_pos ((h.blocks B).2 hB), if_pos hB, h.col B B]
    · rw [if_neg (fun hc => hB ((h.blocks B).1 hc)), if_neg hB]

end BlkCaseObj

namespace VColBipBlk

variable {s t : Type} {κ : Type} [Zero κ] {X : VColBipBlk s κ} {Y : VColBipBlk t κ}
  {φ : s ≃ t}

open scoped Classical in
/-- An isomorphism of graphs that carries the sub-family `U` of the blocks onto `U'` is an
isomorphism of the induced subgraphs `X[V₁, U]` and `Y[V₁, U']`.  This is what makes the
exits of §9.7 canonical: the sub-family they select is defined canonically, so it is
carried onto the sub-family selected at the other object. -/
theorem restrictBlk_isIsoTo (h : X.IsIsoTo Y φ) {U : Set (Set s)} {U' : Set (Set t)}
    (hU : ∀ B : Set s, φ '' B ∈ U' ↔ B ∈ U) :
    (X.restrictBlk U).IsIsoTo (Y.restrictBlk U') φ := by
  refine ⟨h.part₁, fun B => ?_, fun x B => ?_, h.color₁, fun B => ?_, fun A B => ?_⟩
  · show (φ '' B ∈ Y.blocks ∧ φ '' B ∈ U') ↔ (B ∈ X.blocks ∧ B ∈ U)
    rw [h.blocks B, hU B]
  · show ((φ x, φ '' B) ∈ Y.E ∧ φ '' B ∈ U') ↔ ((x, B) ∈ X.E ∧ B ∈ U)
    rw [h.edges x B, hU B]
  · show (if φ '' B ∈ U' then Y.g (φ '' B) else 0) = (if B ∈ U then X.g B else 0)
    by_cases hB : B ∈ U
    · rw [if_pos ((hU B).2 hB), if_pos hB, h.color₂ B]
    · rw [if_neg (fun hc => hB ((hU B).1 hc)), if_neg hB]
  · show (if φ '' A ∈ U' ∧ φ '' B ∈ U' then Y.h (φ '' A) (φ '' B) else 0)
      = (if A ∈ U ∧ B ∈ U then X.h A B else 0)
    by_cases hAB : A ∈ U ∧ B ∈ U
    · rw [if_pos ⟨(hU A).2 hAB.1, (hU B).2 hAB.2⟩, if_pos hAB, h.hint A B]
    · rw [if_neg (fun hc => hAB ⟨(hU A).1 hc.1, (hU B).1 hc.2⟩), if_neg hAB]

end VColBipBlk

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The restricted input as an admissible input of Theorem 9.2.2, and as an outcome

The three exits of §9.7 that read *"significant progress: `|V₂|` reduced"* return the
bipartite graph `X = (V₁, V₂; Rᵢ)` restricted to a canonical sub-family `U` of the blocks,
with the threshold `α` unchanged (the first part `V₁` is unchanged, so Lemma 9.3.1 asks for
nothing).  `Babai.restrictObj` is that object and `Babai.good97_restrict` is the exit. -/

open BlkBlockDesignInputs in
/-- §9.7.  The input of §9.7 restricted to a sub-family `U` of its blocks: the bipartite
graph `X[V₁, U]`, with the threshold `α` of the input. -/
noncomputable def restrictObj (X : Pt (BlkBlockDesignInputs Ω)) (U : Set (Set ↥X.car)) :
    VColBipBlk ↥X.car ℕ × ℝ :=
  ((obj₀ X).linkGraph.restrictBlk U, alpha X)

open BlkBlockDesignInputs in
/-- §9.7.  **The restricted input is an admissible input of Theorem 9.2.2** for the same
threshold `α`, that is, an object of `Babai.BipBlockInputs`.

The three hypotheses of Theorem 9.2.2 are: *"`|V₁| ≥ 2`"*, which is `n₁ ≥ 3`; *"`|V₂| <
α|V₁|`"*, which is `|U| ≤ n₂ < αn₁`; and *"the symmetry defect of `X` on `V₁` is at least
`1 − α`"*, which is what Procedure Reduce-Part2-by-Color leaves, read as a relative defect
(`Babai.defect_of_symDefect_ge`; see the module docstring). -/
theorem restrictObj_pred (X : Pt (BlkBlockDesignInputs Ω)) {U : Set (Set ↥X.car)}
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁) :
    letI : Fintype ↥X.car := Fintype.ofFinite _
    letI : DecidableEq ↥X.car := Classical.decEq _
    2 / 3 ≤ (restrictObj X U).2 ∧ (restrictObj X U).2 < 1 ∧
      (restrictObj X U).1.IsThm922Input (restrictObj X U).2 := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨hα, hα1, hlt⟩ := X.obj.2
  refine ⟨hα, hα1, ?_, ?_, ?_⟩
  · -- `|V₁| ≥ 2`
    show 2 ≤ ({x | (obj₀ X).part₁ x} : Set ↥X.car).ncard
    exact le_trans (by norm_num) h3
  · -- `|V₂| < α|V₁|`, because `|U| ≤ n₂`
    have hnb : (restrictObj X U).1.numBlocks = U.ncard :=
      VColBipBlk.restrictBlk_numBlocks hU
    have hle : U.ncard ≤ (obj₀ X).blocks.ncard := Set.ncard_le_ncard hU (Set.toFinite _)
    have hle' : ((U.ncard : ℕ) : ℝ) ≤ (((obj₀ X).blocks.ncard : ℕ) : ℝ) := by
      exact_mod_cast hle
    rw [hnb]
    exact lt_of_le_of_lt hle' hlt
  · -- the symmetry defect
    have hdef' : (1 : ℚ) / 3 ≤ (restrictObj X U).1.defect₁ :=
      defect_of_symDefect_ge (X := (obj₀ X).linkGraph.restrictBlk U)
        (by exact h3) hdef
    have hdef'' : (1 : ℝ) / 3 ≤ (((restrictObj X U).1.defect₁ : ℚ) : ℝ) := by
      simpa using (Rat.cast_le (K := ℝ)).2 hdef'
    have hα' : (2 : ℝ) / 3 ≤ (restrictObj X U).2 := hα
    show 1 - (restrictObj X U).2 ≤ (((restrictObj X U).1.defect₁ : ℚ) : ℝ)
    linarith

open BlkBlockDesignInputs in
/-- §9.7.  The outcome that the three exits *"significant progress: `|V₂|` reduced"* return:
the restricted input, as an object of `Babai.Out97`. -/
noncomputable def restrictOutcome (X : Pt (BlkBlockDesignInputs Ω)) {U : Set (Set ↥X.car)}
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁) :
    Pt (Out97 Ω) :=
  ⟨X.car, Sum.inr ⟨restrictObj X U, restrictObj_pred X hU h3 hdef⟩⟩

open BlkBlockDesignInputs in
/-- §9.7.  **The outcome lemma.**  *"Significant progress: `n₂` is reduced."*  With
`10|U| ≤ 9n₂` the restricted input is an outcome of §9.7 in the sense of
`Babai.IsBlkDesignOutcome`: its first part is the first part of the input (so it is
contained in it, and `α_new |V₁_new| = α |V₁|` holds with `α_new = α`), and the number of
blocks has dropped by the factor of §9.5. -/
theorem good97_restrict (X : Pt (BlkBlockDesignInputs Ω)) {U : Set (Set ↥X.car)}
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁)
    (hprog : 10 * U.ncard ≤ 9 * numBlocks X) :
    Good97 X (restrictOutcome X hU h3 hdef) := by
  refine ⟨subset_rfl, rfl, Or.inl ?_⟩
  show 10 * ((obj₀ X).linkGraph.restrictBlk U).numBlocks ≤ 9 * numBlocks X
  rw [VColBipBlk.restrictBlk_numBlocks (X := (obj₀ X).linkGraph) hU]
  exact hprog

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Reading a set of blocks back off the ambient type `Set Ω`

Case 3 of §9.7 hands `H` to the Design Lemma over the ambient type `Set Ω`, where a block
is a **point** (`Babai.BlkCaseObj.blkAmb`, `Workspace/SplitOrJohnson/BlockDesignHyper.lean`).
What comes back — the carrier of a UPCC on `W ⊆ V₂`, or a color class of a colored
`3/4`-partition of `V₂` — is therefore a set of points of `Set Ω`, and the exits of §9.7
need it as a sub-family of `Babai.BlkCaseObj.blocks`.  `Babai.BlkCaseObj.blkFam` is that
reading; it loses nothing, because `B ↦ Subtype.val '' B` is injective on the blocks. -/

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- §9.7, Case 3.  A set of blocks read on the ambient type `Set Ω`, read back as a
sub-family of `Babai.BlkCaseObj.blocks`. -/
def blkFam (X : BlkCaseObj s Case) (W : Set (Set Ω)) : Set (Set ↥s) :=
  {B | B ∈ X.blocks ∧ Subtype.val '' B ∈ W}

theorem blkFam_subset (X : BlkCaseObj s Case) (W : Set (Set Ω)) :
    X.blkFam W ⊆ X.blocks := fun _ hB => hB.1

theorem mem_blkFam (X : BlkCaseObj s Case) (W : Set (Set Ω)) (B : Set ↥s) :
    B ∈ X.blkFam W ↔ B ∈ X.blocks ∧ Subtype.val '' B ∈ W := Iff.rfl

theorem blkFam_mono (X : BlkCaseObj s Case) {W W' : Set (Set Ω)} (h : W ⊆ W') :
    X.blkFam W ⊆ X.blkFam W' := fun _ hB => ⟨hB.1, h hB.2⟩

/-- `Babai.BlkCaseObj.blkFam` of the complement is the complement of
`Babai.BlkCaseObj.blkFam`, inside the blocks.  This is the second part `V₂ ∖ W` of the
partition `(W, V₂ ∖ W)` that Cases 3a2 and 2 hand to Procedure Reduce-Part2-by-Color. -/
theorem blkFam_compl (X : BlkCaseObj s Case) (W : Set (Set Ω)) :
    X.blkFam Wᶜ = X.blocks \ X.blkFam W := by
  ext B
  constructor
  · rintro ⟨hB, hW⟩
    exact ⟨hB, fun hc => hW hc.2⟩
  · rintro ⟨hB, hW⟩
    exact ⟨hB, fun hc => hW ⟨hB, hc⟩⟩

/-- The two parts `W` and `V₂ ∖ W` cover the blocks. -/
theorem blkFam_union_cover (X : BlkCaseObj s Case) (W : Set (Set Ω)) :
    X.blocks ⊆ X.blkFam W ∪ X.blkFam Wᶜ := by
  intro B hB
  by_cases hW : Subtype.val '' B ∈ W
  · exact Or.inl ⟨hB, hW⟩
  · exact Or.inr ⟨hB, hW⟩

/-- Reading a set of blocks back off the ambient type loses nothing: if every member of `W`
is a block read on `Set Ω`, then `|blkFam W| = |W|`. -/
theorem ncard_blkFam (X : BlkCaseObj s Case) {W : Set (Set Ω)}
    (hW : ∀ A ∈ W, ∃ B ∈ X.blocks, Subtype.val '' B = A) :
    (X.blkFam W).ncard = W.ncard := by
  have himg : (fun B : Set ↥s => Subtype.val '' B) '' X.blkFam W = W := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩; exact hB.2
    · intro hA
      obtain ⟨B, hB, rfl⟩ := hW A hA
      exact ⟨B, ⟨hB, hA⟩, rfl⟩
  calc (X.blkFam W).ncard
      = ((fun B : Set ↥s => Subtype.val '' B) '' X.blkFam W).ncard :=
        (Set.ncard_image_of_injective _
          (Set.image_injective.2 Subtype.val_injective)).symm
    _ = W.ncard := by rw [himg]

end BlkCaseObj

end Babai

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- §9.7, Cases 2 and 3: **`n₁ ≥ 5`**.  `H` is simple (*"no multiple edges because there
are no twins in `V₁`"*) and uniform of rank `d₁`, so `n₁ ≤ C(n₂, d₁)`; with the standing
hypothesis `n₂ < αn₁ < n₁` of Theorem 9.2.2 this gives `2 ≤ d₁` and `d₁ + 2 ≤ n₂`
(`Babai.BlkCaseObj.two_le_d₁_and_add_two_le`), hence `n₂ ≥ 4` and `n₁ ≥ 5`.

This is what `Babai.restrictObj_pred` needs (`3 ≤ n₁`, so that the symmetry defect left by
Procedure Reduce-Part2-by-Color is at least `1/3 ≥ 1 − α`).  The paper never states the
arithmetic; see the module docstring. -/
theorem BlkCaseObj.five_le_n₁ {s : Set Ω} (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) :
    5 ≤ X.n₁ := by
  obtain ⟨h1, h2⟩ := X.two_le_d₁_and_add_two_le hlt
  omega

end Babai
