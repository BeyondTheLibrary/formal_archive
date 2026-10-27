/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.6: the imprimitive case (Lemma 9.6.1, Procedure ImprimitiveCase, Lemma 9.6.2).
-/
import Workspace.SplitOrJohnson.UPCCCase
import Workspace.SplitOrJohnson.KerPart
import Workspace.Coherent.Constituents
import Workspace.SplitOrJohnson.BlockSystem
import Workspace.SplitOrJohnson.WLColor

/-!
# §9.6 Imprimitive case

Version 2.5, lines 4183–4232 of `babai-gi-source/quasi25.txt`.

> *Case: `X₂` is a homogeneous, imprimitive coherent configuration; `X₁` is a UPCC; the
> link `X₁₂` is nontrivial.  In particular, there are no `Rᵢ`-twins in `V₁` with respect to
> any of the constituents `Rᵢ` of `X₁₂`.*

| Paper | Lean |
|---|---|
| Lemma 9.6.1 | `Babai.lemma_9_6_1` |
| Procedure ImprimitiveCase, step 1 | `Babai.imprimitiveCase_split` |
| Procedure ImprimitiveCase, step 2, the contraction `Y` | `Babai.contractedBip` |
| Lemma 9.6.2 | `Babai.lemma_9_6_2` |
| Subclaim of Lemma 9.6.2 (`Cᵢ × Bᵢ ⊆ R_j`) | `Babai.subclaim_9_6_2` |
| Claim of Lemma 9.6.2 (`Y` is not complete) | `Babai.claim_9_6_2` |

## What is formalized here

The combinatorial core of §9.6 — the Subclaim, the Claim and the conclusion of
Lemma 9.6.2 — is stated and proved for the data the paper actually uses: the coloring
`c : V₁ × V₂ → J` of the link, its in-degrees `d_j` (constant by the homogeneity of `X₂`),
the blocks `Bᵢ` of the disconnected color `R₂` of `X₂`, and the twin classes `Cᵢ ⊆ V₁` of
the bipartite graphs `Zᵢ = X(V₁, Bᵢ; R_j)`.  The surrounding statements (Lemma 9.6.1, the
procedure) are stated in terms of these data as well.
-/

namespace Babai

/-! ### Three facts about the symmetry defect of a bipartite graph

These are Definition 2.4.29 read backwards: they turn the branch condition of step 2 of
Procedure ImprimitiveCase (*"the symmetry defect of `V₁` in `Zᵢ` is less than `1/2`"*) into
the large twin class `Cᵢ` that the proof of Lemma 9.6.2 uses. -/

namespace BipGraph

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

open scoped Classical in
/-- Definition 2.4.29.  The absolute symmetricity of `Ω₁` is **attained**: some set of
twins in `Ω₁` has exactly that many elements.  (`symmetricity₁` is a supremum over a
nonempty finite family, the empty set being a set of twins.) -/
theorem exists_twinSet_card_eq_symmetricity₁ (X : BipGraph A B) :
    ∃ T : Finset A, IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A)) ∧
      T.card = X.symmetricity₁ := by
  have hne : (Finset.univ.filter fun T : Finset A =>
      IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A))).Nonempty :=
    ⟨∅, by simp [IsTwinSet]⟩
  obtain ⟨T, hT, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨T, (Finset.mem_filter.1 hT).2, hsup.symm⟩

open scoped Classical in
/-- Definition 2.4.29.  A symmetry defect of `Ω₁` below `1/2` means that more than half of
`Ω₁` is a set of twins.  This is where *"there is a (unique) `Zᵢ`-twin equivalence class
`Cᵢ ⊆ V₁` such that `|Cᵢ| > n₁/2`"* (proof of Lemma 9.6.2) comes from. -/
theorem lt_two_mul_symmetricity₁_of_defect_lt_half {X : BipGraph A B}
    (h : X.defect₁ < 1 / 2) : Fintype.card A < 2 * X.symmetricity₁ := by
  have hdef : X.defect₁ = 1 - (X.symmetricity₁ : ℚ) / (Fintype.card A : ℚ) := rfl
  rw [hdef] at h
  rcases Nat.eq_zero_or_pos (Fintype.card A) with h0 | hpos
  · rw [h0] at h
    simp only [Nat.cast_zero, div_zero, sub_zero] at h
    norm_num at h
  · have hn : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hpos
    have h2 : (1 : ℚ) / 2 < (X.symmetricity₁ : ℚ) / (Fintype.card A : ℚ) := by linarith
    rw [lt_div_iff₀ hn] at h2
    have h3 : (Fintype.card A : ℚ) < 2 * (X.symmetricity₁ : ℚ) := by linarith
    exact_mod_cast h3

open scoped Classical in
/-- Definition 2.3.9 for a bipartite graph: two points of a set of twins of `Ω₁` have the
same neighborhood.  (*"The vertices of `Cᵢ` are twins in `Zᵢ`"*, proof of the Subclaim of
Lemma 9.6.2.) -/
theorem twinSet₁_nbhd_iff {X : BipGraph A B} {T : Set A}
    (hT : IsTwinSet X.Aut ((fun a => Sum.inl a) '' T)) {x x' : A} (hx : x ∈ T)
    (hx' : x' ∈ T) (y : B) : (x, y) ∈ X.E ↔ (x', y) ∈ X.E := by
  by_cases hxx : x = x'
  · subst hxx; exact Iff.rfl
  · have htwin : IsTwin X.Aut (Sum.inl x) (Sum.inl x') :=
      hT _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ (by simp [hxx])
    exact Set.ext_iff.1 ((isTwin_inl_iff_aux X x x' hxx).1 htwin) y

open scoped Classical in
/-- Definition 2.4.29, read without the automorphism group.  By
`Babai.BipGraph.isTwin_inl_iff_aux` a set of twins in `Ω₁` is exactly a set of vertices
with pairwise equal neighbourhoods, so the absolute symmetricity of `Ω₁` is the largest
size of such a set.  This is the form in which the symmetry defect of §9.6 is compared
between the paper's bipartite graphs and the objects of `Babai.VColBlkGraphs`. -/
theorem symmetricity₁_eq_sup (X : BipGraph A B) :
    X.symmetricity₁ = (Finset.univ.filter fun T : Finset A =>
      ∀ x ∈ T, ∀ y ∈ T, ∀ b : B, ((x, b) ∈ X.E ↔ (y, b) ∈ X.E)).sup Finset.card := by
  classical
  refine congrArg (fun u => Finset.sup u Finset.card) ?_
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hT x hx y hy b
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    · have h := (isTwin_inl_iff_aux X x y hxy).1
        (hT _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ (by simp [hxy]))
      exact Set.ext_iff.1 h b
  · intro hT
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := fun h => hne (by rw [h])
    exact (isTwin_inl_iff_aux X x y hxy).2 (Set.ext fun b => hT x hx y hy b)

/-- Definition 2.4.29.  The absolute symmetricity of `Ω₁` only depends on the bipartite
graph up to bijections of the two parts. -/
theorem symmetricity₁_congr {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A']
    [DecidableEq B'] {X : BipGraph A B} {Y : BipGraph A' B'} (e : A ≃ A') (d : B ≃ B')
    (h : ∀ (a : A) (b : B), (e a, d b) ∈ Y.E ↔ (a, b) ∈ X.E) :
    Y.symmetricity₁ = X.symmetricity₁ := by
  classical
  rw [symmetricity₁_eq_sup, symmetricity₁_eq_sup]
  refine le_antisymm (Finset.sup_le fun T hT => ?_) (Finset.sup_le fun T hT => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    refine le_trans (le_of_eq (Finset.card_map e.symm.toEmbedding).symm)
      (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx y hy b
    simp only [Finset.mem_map_equiv] at hx hy
    have hx' : e x ∈ T := by simpa using hx
    have hy' : e y ∈ T := by simpa using hy
    rw [← h x b, ← h y b]
    exact hT _ hx' _ hy' (d b)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    refine le_trans (le_of_eq (Finset.card_map e.toEmbedding).symm)
      (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx y hy b
    simp only [Finset.mem_map_equiv] at hx hy
    have hx' : e.symm x ∈ T := hx
    have hy' : e.symm y ∈ T := hy
    have hb : ∀ z : A', (z, b) ∈ Y.E ↔ (e.symm z, d.symm b) ∈ X.E := by
      intro z
      have := h (e.symm z) (d.symm b)
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    rw [hb x, hb y]
    exact hT _ hx' _ hy' (d.symm b)

/-- Definition 2.4.29.  The relative symmetry defect of `Ω₁` only depends on the bipartite
graph up to bijections of the two parts. -/
theorem defect₁_congr {A' B' : Type*} [Fintype A'] [Fintype B'] [DecidableEq A']
    [DecidableEq B'] {X : BipGraph A B} {Y : BipGraph A' B'} (e : A ≃ A') (d : B ≃ B')
    (h : ∀ (a : A) (b : B), (e a, d b) ∈ Y.E ↔ (a, b) ∈ X.E) : Y.defect₁ = X.defect₁ := by
  unfold BipGraph.defect₁ BipGraph.relSymmetricity₁
  rw [symmetricity₁_congr e d h, Fintype.card_congr e.symm]

end BipGraph

/-! ### The symmetry defect of an object of `Babai.VColBlkGraphs`

Lemma 9.6.1 returns an object of `Babai.VColBlkGraphs`, while `Babai.case_9_6_1_step2`
computes the symmetry defect of a `Babai.BipGraph`.  The two agree: the outcomes of step 2
of Procedure ImprimitiveCase carry **no vertex coloring** (the graphs `Zᵢ` and `Y` of the
paper are plain bipartite graphs), and for a constant point coloring the twins of `V₁` in
the object are exactly the twins of `V₁` in the bipartite graph whose second part is the
set of blocks (`Babai.VColBipBlk.isTwin_iff`). -/

namespace VColBipBlk

variable {s : Type} [Fintype s] [DecidableEq s]

/-- The first part of an object is a finite set of points. -/
noncomputable instance fintypeV₁ (X : VColBipBlk s ℕ) : Fintype ↥X.V₁ := Fintype.ofFinite _

/-- The second part of an object is a finite family of blocks. -/
noncomputable instance fintypeBlocks (X : VColBipBlk s ℕ) : Fintype ↥X.blocks :=
  Fintype.ofFinite _

/-- §9.6.  The bipartite graph of an object of `Babai.VColBlkGraphs`: the first part is
`V₁` and the second part is the set of blocks. -/
def toBip (X : VColBipBlk s ℕ) : BipGraph ↥X.V₁ ↥X.blocks :=
  ⟨{p | ((p.1 : s), (p.2 : Set s)) ∈ X.E}⟩

open scoped Classical in
/-- Definition 2.4.29 for an object of `Babai.VColBlkGraphs` with a constant point
coloring, read without the automorphism group (`Babai.VColBipBlk.isTwin_iff`). -/
theorem symmetricity₁_eq_sup (X : VColBipBlk s ℕ) (hf : ∀ x y : s, X.f x = X.f y) :
    X.symmetricity₁ = (Finset.univ.filter fun T : Finset s =>
      (∀ x ∈ T, X.part₁ x) ∧
        ∀ x ∈ T, ∀ y ∈ T, ∀ B ∈ X.blocks, ((x, B) ∈ X.E ↔ (y, B) ∈ X.E)).sup
      Finset.card := by
  classical
  refine congrArg (fun u => Finset.sup u Finset.card) ?_
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hT⟩
    refine ⟨hp, fun x hx y hy B hB => ?_⟩
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    · exact ((X.isTwin_iff (hp x hx) (hp y hy) hxy).1 (hT x hx y hy hxy)).2 B hB
  · rintro ⟨hp, hT⟩
    refine ⟨hp, fun x hx y hy hxy => ?_⟩
    exact (X.isTwin_iff (hp x hx) (hp y hy) hxy).2 ⟨hf x y, fun B hB => hT x hx y hy B hB⟩

/-- §9.6.  The absolute symmetricity of `V₁` in an object with a constant point coloring
is the absolute symmetricity of `V₁` in its bipartite graph. -/
theorem symmetricity₁_toBip (X : VColBipBlk s ℕ) (hf : ∀ x y : s, X.f x = X.f y) :
    X.toBip.symmetricity₁ = X.symmetricity₁ := by
  classical
  rw [BipGraph.symmetricity₁_eq_sup, X.symmetricity₁_eq_sup hf]
  refine le_antisymm (Finset.sup_le fun T hT => ?_) (Finset.sup_le fun T hT => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    refine le_trans (le_of_eq (Finset.card_map (Function.Embedding.subtype _)).symm)
      (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro x hx
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨z, -, rfl⟩ := hx
      exact z.2
    · rintro x hx y hy B hB
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx hy
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact hT z hz w hw ⟨B, hB⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    obtain ⟨hp, hpair⟩ := hT
    have hcard : T.card = (T.subtype (fun x => x ∈ X.V₁)).card := by
      rw [Finset.card_subtype]
      exact (congrArg Finset.card (Finset.filter_true_of_mem (fun x hx => hp x hx))).symm
    refine le_trans (le_of_eq hcard) (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro x hx y hy B
    simp only [Finset.mem_subtype] at hx hy
    exact hpair _ hx _ hy (B : Set s) B.2

open scoped Classical in
/-- §9.6.  An isomorphism of objects with constant point colorings does not decrease the
absolute symmetricity of `V₁`.  By `Babai.VColBipBlk.symmetricity₁_eq_sup` that number is
the largest size of a set of points of `V₁` with pairwise equal sets of neighbouring
blocks, and an isomorphism carries such a set to such a set. -/
theorem symmetricity₁_le_of_isoTo {s t : Type} [Fintype s] [DecidableEq s] [Fintype t]
    [DecidableEq t] {X : VColBipBlk s ℕ} {Y : VColBipBlk t ℕ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) (hf : ∀ x y : s, X.f x = X.f y) (hf' : ∀ x y : t, Y.f x = Y.f y) :
    X.symmetricity₁ ≤ Y.symmetricity₁ := by
  classical
  rw [X.symmetricity₁_eq_sup hf, Y.symmetricity₁_eq_sup hf']
  refine Finset.sup_le fun T hT => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨hp, hpair⟩ := hT
  refine le_trans (le_of_eq (Finset.card_map φ.toEmbedding).symm)
    (Finset.le_sup (f := Finset.card) ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro y hy
    simp only [Finset.mem_map_equiv] at hy
    simpa using (h.part₁ (φ.symm y)).2 (hp _ hy)
  · intro y hy y' hy' B hB
    simp only [Finset.mem_map_equiv] at hy hy'
    have himg : φ '' (φ.symm '' B) = B := Equiv.image_symm_image φ B
    have hB₀ : φ.symm '' B ∈ X.blocks := (h.blocks (φ.symm '' B)).1 (by rw [himg]; exact hB)
    have hy₀ : ((y, B) ∈ Y.E) ↔ ((φ.symm y, φ.symm '' B) ∈ X.E) := by
      have := h.edges (φ.symm y) (φ.symm '' B)
      rwa [Equiv.apply_symm_apply, himg] at this
    have hy₀' : ((y', B) ∈ Y.E) ↔ ((φ.symm y', φ.symm '' B) ∈ X.E) := by
      have := h.edges (φ.symm y') (φ.symm '' B)
      rwa [Equiv.apply_symm_apply, himg] at this
    rw [hy₀, hy₀']
    exact hpair _ hy _ hy' _ hB₀

/-- §9.6.  An isomorphism of objects with constant point colorings preserves the relative
symmetry defect of `V₁`.  This is what makes the filter of
`Babai.BlkImprimitiveObj.step2Out` an isomorphism invariant. -/
theorem defect₁_of_isoTo {s t : Type} [Fintype s] [DecidableEq s] [Fintype t]
    [DecidableEq t] {X : VColBipBlk s ℕ} {Y : VColBipBlk t ℕ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) (hf : ∀ x y : s, X.f x = X.f y) (hf' : ∀ x y : t, Y.f x = Y.f y) :
    Y.defect₁ = X.defect₁ := by
  have hsym : Y.symmetricity₁ = X.symmetricity₁ :=
    le_antisymm (symmetricity₁_le_of_isoTo h.symm hf' hf)
      (symmetricity₁_le_of_isoTo h hf hf')
  have hV : Y.V₁ = φ '' X.V₁ := by
    ext y
    simp only [VColBipBlk.V₁, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hy
      exact ⟨φ.symm y, (h.part₁ (φ.symm y)).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩; exact (h.part₁ x).2 hx
  unfold VColBipBlk.defect₁
  rw [hsym, hV, Set.ncard_image_of_injective _ φ.injective]

/-- §9.6.  The relative symmetry defect of `V₁` in an object with a constant point
coloring is the relative symmetry defect of `V₁` in its bipartite graph.  This is what
lets `Babai.case_9_6_1_step2` be read as a statement about the outcomes of Lemma 9.6.1. -/
theorem defect₁_toBip (X : VColBipBlk s ℕ) (hf : ∀ x y : s, X.f x = X.f y) :
    X.toBip.defect₁ = X.defect₁ := by
  unfold BipGraph.defect₁ BipGraph.relSymmetricity₁ VColBipBlk.defect₁
  rw [symmetricity₁_toBip X hf]
  congr 2
  rw [Set.ncard_eq_toFinset_card' X.V₁, Set.toFinset_card]

end VColBipBlk

/-! ### The contracted bipartite graph of step 2(ii) -/

variable {A B ι J : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype ι] [DecidableEq ι]

/-- Procedure ImprimitiveCase, step 2(ii).  *"Let `h ∈ J`, `h ≠ j`.  Let
`Y = (V₁, [m]; R_h)` where `(x,i) ∈ R_h` if `(∃y ∈ Bᵢ)((x,y) ∈ R_h)`."*

`blocks : V₂ → [m]` records the block `Bᵢ` of each vertex of `V₂`, and `c` is the coloring
of the link `V₁ × V₂`. -/
def contractedBip (c : A → B → J) (h : J) (blocks : B → ι) : BipGraph A ι :=
  ⟨{p | ∃ y, blocks y = p.2 ∧ c p.1 y = h}⟩

/-- Subclaim of Lemma 9.6.2.  *"`Cᵢ × Bᵢ ⊆ R_j`."*

Paper's proof: *"The vertices of `Cᵢ` are twins in `Zᵢ`.  In other words, for each
`x ∈ Bᵢ` the set `Cᵢ × {x}` is monochromatic (has a single color), i.e.
`Cᵢ × {x} ⊆ R_ℓ` for some `ℓ ∈ J`.  It follows that `d_ℓ > n₁/2`.  Therefore `ℓ = j`,
proving the Subclaim."*

*What "twins in `Zᵢ`" means.*  `Zᵢ = X(V₁, Bᵢ; R_j)` is the **bipartite graph with edge set
`R_j`**, so twinness in `Zᵢ` is equality of the `R_j`-neighborhoods inside `Bᵢ`:
`c x y = j ↔ c x' y = j` for `y ∈ Bᵢ`.  This is `hCtwin`, and it is all that Procedure
ImprimitiveCase supplies.  (The paper's intermediate phrase *"the set `Cᵢ × {y}` is
monochromatic"* asserts more than twinness in a two-colored `Zᵢ` gives, and is not needed:
the argument below runs directly from the `R_j`-neighborhoods.)

Proof: if some `x ∈ Cᵢ` had `c x y ≠ j` for some `y ∈ Bᵢ`, then by `hCtwin` no vertex of
`Cᵢ` would be an `R_j`-neighbor of `y`, so the two disjoint sets `Cᵢ` and `R_j(y) ∩ V₁`
would have more than `n₁/2` elements each. -/
theorem subclaim_9_6_2 (c : A → B → J) (j : J) (d : J → ℕ)
    (hd : ∀ (k : J) (y : B), {x : A | c x y = k}.ncard = d k)
    (hdj : Fintype.card A < 2 * d j) (C : ι → Set A) (blocks : B → ι)
    (hCsize : ∀ i, Fintype.card A < 2 * (C i).ncard)
    (hCtwin : ∀ (i : ι), ∀ x ∈ C i, ∀ x' ∈ C i, ∀ y : B, blocks y = i →
      (c x y = j ↔ c x' y = j))
    (i : ι) {x : A} (hx : x ∈ C i) {y : B} (hy : blocks y = i) : c x y = j := by
  classical
  by_contra hne
  -- no vertex of `Cᵢ` is an `R_j`-neighbor of `y`
  have hdisj : Disjoint (C i) {x' : A | c x' y = j} := by
    rw [Set.disjoint_left]
    intro z hz hzj
    exact hne ((hCtwin i z hz x hx y hy).1 hzj)
  -- but both sets have more than half of `V₁`
  have hunion : (C i).ncard + {x' : A | c x' y = j}.ncard ≤ Fintype.card A := by
    rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    have : ((C i) ∪ {x' : A | c x' y = j}).ncard ≤ (Set.univ : Set A).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  rw [hd j y] at hunion
  have := hCsize i
  omega

/-- Claim of Lemma 9.6.2.  *"`Y` is not complete."*

Paper's proof: *"For each `i ≤ m` there is a (unique) `Zᵢ`-twin equivalence class
`Cᵢ ⊆ V₁` such that `|Cᵢ| > n₁/2`.  [Subclaim: `Cᵢ × Bᵢ ⊆ R_j`.]  Now `Y` is not complete
because it has no edge from `i` to `Cᵢ`."* -/
theorem claim_9_6_2 (c : A → B → J) (j h : J) (hjh : h ≠ j) (d : J → ℕ)
    (hd : ∀ (k : J) (y : B), {x : A | c x y = k}.ncard = d k)
    (hdj : Fintype.card A < 2 * d j) (C : ι → Set A) (blocks : B → ι)
    (hCsize : ∀ i, Fintype.card A < 2 * (C i).ncard)
    (hCtwin : ∀ (i : ι), ∀ x ∈ C i, ∀ x' ∈ C i, ∀ y : B, blocks y = i →
      (c x y = j ↔ c x' y = j))
    (i : ι) : (contractedBip c h blocks).E ≠ Set.univ := by
  classical
  -- `Cᵢ` is non-empty: it has more than half of the (non-empty) set `V₁`
  have hCne : (C i).Nonempty := by
    rcases Set.eq_empty_or_nonempty (C i) with hem | hne
    · have := hCsize i
      rw [hem, Set.ncard_empty] at this
      omega
    · exact hne
  obtain ⟨x, hx⟩ := hCne
  intro hcompl
  have hmem : (x, i) ∈ (contractedBip c h blocks).E := by rw [hcompl]; trivial
  obtain ⟨y, hy, hcy⟩ := hmem
  exact hjh (hcy ▸ subclaim_9_6_2 c j d hd hdj C blocks hCsize hCtwin i hx hy)

/-- Lemma 9.6.2.  *"In subcase (ii) of item 2 (contracting the blocks), `V₁` has symmetry
defect `≥ 1/2` in the contracted bipartite graph `Y`."*  (Version 2.5, lines 4218–4231.)

Paper's proof: *"`Y` is semiregular by Cor. 3.4.9.  Moreover `R_h` is not empty because
`R_h` is not empty.  [Claim: `Y` is not complete.]  Since `Y` is semiregular, nonempty and
not complete, we infer by Prop. 2.4.30 that `Y` has symmetry defect `≥ 1/2`, as
claimed."*

The semiregularity of `Y` (Theorem 3.4.9, contraction) and the non-emptiness of `R_h` are
hypotheses here, exactly as the paper takes them from §3.4; the content of the lemma is the
Claim together with Prop. 2.4.30.  The conclusion is stated for both parts, as
Prop. 2.4.30 gives it. -/
theorem lemma_9_6_2 (c : A → B → J) (j h : J) (hjh : h ≠ j) (d : J → ℕ)
    (hd : ∀ (k : J) (y : B), {x : A | c x y = k}.ncard = d k)
    (hdj : Fintype.card A < 2 * d j) (C : ι → Set A) (blocks : B → ι)
    (hCsize : ∀ i, Fintype.card A < 2 * (C i).ncard)
    (hCtwin : ∀ (i : ι), ∀ x ∈ C i, ∀ x' ∈ C i, ∀ y : B, blocks y = i →
      (c x y = j ↔ c x' y = j))
    (hne : (contractedBip c h blocks).E ≠ ∅)
    (hsr : (contractedBip c h blocks).IsSemiregular) (i : ι) :
    1 / 2 ≤ (contractedBip c h blocks).defect₁ ∧
      1 / 2 ≤ (contractedBip c h blocks).defect₂ := by
  refine BipGraph.defect_ge_half ?_ hsr
  rintro (hE | hE)
  · exact hne hE
  · exact claim_9_6_2 c j h hjh d hd hdj C blocks hCsize hCtwin i hE

/-! ### Step 2 of Procedure ImprimitiveCase: one of the two branches keeps the defect -/

/-- Procedure ImprimitiveCase, step 2.  *"For `i = 1, …, m` let `Zᵢ = X(V₁, Bᵢ; R_j)`."*
The bipartite graph on `V₁` and the block `Bᵢ`, with the edges of color `j`. -/
def blockGraph (c : A → B → J) (j : J) (blocks : B → ι) (i : ι) :
    BipGraph A {y : B // blocks y = i} := ⟨{p | c p.1 (p.2 : B) = j}⟩

/-- Lemma 9.6.1, step 2 of Procedure ImprimitiveCase.  *"We shall see that one of these is
always possible without reducing the symmetry defect on `V₁` below `1/2`."*

Either some `Zᵢ` has symmetry defect at least `1/2` on `V₁`, which is branch 2(i)
(*"`Y ← Zᵢ`"*), or the contracted graph of branch 2(ii) has symmetry defect at least `1/2`
on `V₁`.

Paper's proof: if branch 2(i) does not apply then the symmetry defect of `V₁` in every
`Zᵢ` is less than `1/2`, so *"for each `i ≤ m` there is a (unique) `Zᵢ`-twin equivalence
class `Cᵢ ⊆ V₁` such that `|Cᵢ| > n₁/2`"*
(`BipGraph.lt_two_mul_symmetricity₁_of_defect_lt_half` together with
`BipGraph.exists_twinSet_card_eq_symmetricity₁`); the vertices of `Cᵢ` are twins in `Zᵢ`,
so they have the same `R_j`-neighborhood in `Bᵢ`
(`BipGraph.twinSet₁_nbhd_iff`); and then Lemma 9.6.2 applies.

Uniqueness of `Cᵢ` is not needed and is not stated: any set of twins with more than `n₁/2`
elements does the work, and by `BipGraph.exists_twinSet_card_eq_symmetricity₁` a largest
one is such a set.

As in `lemma_9_6_2`, the semiregularity of the contraction (Cor. 3.4.9) and the
non-emptiness of `R_h` are hypotheses, exactly as the paper takes them from §3.4. -/
theorem case_9_6_1_step2 [DecidableEq B] (c : A → B → J) (j h : J) (hjh : h ≠ j) (d : J → ℕ)
    (hd : ∀ (k : J) (y : B), {x : A | c x y = k}.ncard = d k)
    (hdj : Fintype.card A < 2 * d j) (blocks : B → ι)
    (hEne : (contractedBip c h blocks).E ≠ ∅)
    (hsr : (contractedBip c h blocks).IsSemiregular) :
    (∃ i : ι, 1 / 2 ≤ (blockGraph c j blocks i).defect₁) ∨
      (1 / 2 ≤ (contractedBip c h blocks).defect₁ ∧
        1 / 2 ≤ (contractedBip c h blocks).defect₂) := by
  classical
  by_cases hex : ∃ i : ι, 1 / 2 ≤ (blockGraph c j blocks i).defect₁
  · exact Or.inl hex
  push_neg at hex
  right
  -- Some block index exists: the contraction has an edge.
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hEne
  -- For each `i`, a largest set of `Zᵢ`-twins in `V₁`; it has more than `n₁/2` elements.
  have hC : ∀ i : ι, ∃ T : Finset A,
      IsTwinSet (blockGraph c j blocks i).Aut ((fun a => Sum.inl a) '' (↑T : Set A)) ∧
      Fintype.card A < 2 * T.card := by
    intro i
    obtain ⟨T, hT, hTcard⟩ :=
      (blockGraph c j blocks i).exists_twinSet_card_eq_symmetricity₁
    exact ⟨T, hT, by
      rw [hTcard]
      exact BipGraph.lt_two_mul_symmetricity₁_of_defect_lt_half (hex i)⟩
  choose T hT hTcard using hC
  refine lemma_9_6_2 c j h hjh d hd hdj (fun i => (↑(T i) : Set A)) blocks ?_ ?_ hEne hsr p.2
  · intro i
    rw [Set.ncard_coe_finset]
    exact hTcard i
  · intro i x hx x' hx' y hy
    exact BipGraph.twinSet₁_nbhd_iff (hT i) hx hx' (⟨y, hy⟩ : {y : B // blocks y = i})

/-! ### Step 1 of Procedure ImprimitiveCase -/

/-- Procedure ImprimitiveCase, step 1.  *"If `(∀j ∈ J)(d_j ≤ n₁/2)` then individualize
some `x ∈ V₂`.  This splits `V₁` into color classes of size `d_j`.  Return this partition
of `V₁`, exit.  (: canonical colored `1/2`-partition of `V₁` found :)"*

The blocks of the returned partition of `V₁` are the color classes `R_j(x) ∩ V₁` of the
`x`-local coloring, and the assertion is that each of them has size `d_j ≤ n₁/2`. -/
theorem imprimitiveCase_split (c : A → B → J) (d : J → ℕ)
    (hd : ∀ (k : J) (y : B), {x : A | c x y = k}.ncard = d k)
    (hsmall : ∀ k : J, 2 * d k ≤ Fintype.card A) (y : B) (k : J) :
    2 * {x : A | c x y = k}.ncard ≤ Fintype.card A := by
  rw [hd k y]; exact hsmall k

/-! ### Lemma 9.6.1 -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The situation of §9.6, §9.7 and §9.8: a coherent configuration `X` on `V₁ ∪ V₂` with
two vertex-color classes (Def. 3.4.24, bihomogeneous), whose link `X₁₂` is nontrivial.
The `Case` headings of the three subsections add conditions on `X₁` and `X₂`.

*"the link `X₁₂` is nontrivial"* is Def. 3.4.20 for the induced bipartite configuration:
at least two colors occur on `V₁ × V₂`. -/
structure IsBipartiteCase {V : Type} (c : V → V → ℕ) (V₁ V₂ : Set V) : Prop where
  /-- `c` is the coloring of a coherent configuration. -/
  coherent : ∃ X : PartitionStructure V, X.IsCoherent ∧ X.natColor = c ∧
    ∃ i j : Fin X.rank, i ≠ j ∧ V₁ = X.vertexClass i ∧ V₂ = X.vertexClass j ∧
      (∀ x : V, x ∈ V₁ ∨ x ∈ V₂)
  /-- *"`X₁` is a UPCC"*: a coherent uniprimitive configuration on `V₁` whose **color
  classes** are the color classes of `c` on `V₁`.

  The color classes and not the color *labels*: the labels of a `PartitionStructure` run
  over `{0, …, rank-1}` (field `color_surjective`, Def. 3.1.1), so asking
  `X.natColor x y = c x y` on `V₁`, on `V₂` and on the whole vertex set at once is
  contradictory (`Babai.partNaming_false`).  A configuration and its coloring are the same
  thing up to the naming of the colors, which is what the paper means by *"`X₁`"*. -/
  upcc₁ : ∃ X : PartitionStructure ↥V₁, X.IsCoherent ∧ X.IsUniprimitive ∧
    ∀ x y x' y' : ↥V₁,
      X.natColor x y = X.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)
  /-- *"the link `X₁₂` is nontrivial"*: at least two colors occur on `V₁ × V₂`. -/
  link_nontrivial : ∃ (x₁ : ↥V₁) (y₁ : ↥V₂) (x₂ : ↥V₁) (y₂ : ↥V₂),
    c (x₁ : V) (y₁ : V) ≠ c (x₂ : V) (y₂ : V)

/-- The *Case* of §9.6: in addition, *"`X₂` is a homogeneous, imprimitive coherent
configuration"*. -/
structure IsImprimitiveCase {V : Type} (c : V → V → ℕ) (V₁ V₂ : Set V) : Prop
    extends IsBipartiteCase c V₁ V₂ where
  /-- *"`X₂` is a homogeneous, imprimitive coherent configuration"*, with the color classes
  of `c` on `V₂` as its color classes; see `Babai.IsBipartiteCase.upcc₁` for why the naming
  of the colors is not prescribed. -/
  imprimitive₂ : ∃ X : PartitionStructure ↥V₂, X.IsCoherent ∧ X.IsHomogeneous ∧
    ¬ X.IsPrimitive ∧ ∀ x y x' y' : ↥V₂,
      X.natColor x y = X.natColor x' y' ↔ c (x : V) (y : V) = c (x' : V) (y' : V)

/-! ### Lemma 9.6.1 in the wider category of §9.4-§9.8

Version 2.5, lines 4190-4193.  The recursion of §9.4-§9.8 runs in the category
`Babai.BipBlockInputs`, in which a vertex of `V₂` is a **block** of points
(`Workspace/SplitOrJohnson/BipBlocks.lean`).  So the coherent configuration `X` of step 3
of §9.4 lives on the vertex set *"points of `V₁` plus blocks"*, and Lemma 9.6.1 is stated
there: its input is a coloring of the pairs of such vertices, and the bipartite graph it
returns in the second branch is an object of `Babai.VColBlkGraphs`, which is where the
contracted graph of step 2(ii) lives.

**How the vertices are indexed.**  A vertex is a subset of `□X`: a point `x ∈ V₁` is the
singleton `{x}`, and a vertex of `V₂` is a block.  The coloring is therefore a function
`c : Set ↥s → Set ↥s → ℕ`, total, with a padding outside the vertex set that no
construction reads and that every isomorphism preserves — the same convention as the block
coloring `g` of `Babai.VColBipBlk`, and for the same reason (faithfulness of `□`, §6).  -/

/-- §9.6.  The `Case` of §9.6 read on the vertex set *"points of `V₁` plus blocks"*: the
vertices are the members of `𝒱₁ ∪ 𝒞`, where `𝒱₁` is the set of singletons of the points of
`V₁` and `𝒞` is the family of blocks. -/
def IsImprimitiveCaseOn {s : Set Ω} (c : Set ↥s → Set ↥s → ℕ)
    (𝒱₁ 𝒞 : Set (Set ↥s)) : Prop :=
  IsImprimitiveCase (V := ↥(𝒱₁ ∪ 𝒞)) (fun u v => c (u : Set ↥s) (v : Set ↥s))
    {u | (u : Set ↥s) ∈ 𝒱₁} {u | (u : Set ↥s) ∈ 𝒞}

/-- §9.6.  An input of Lemma 9.6.1 on the point set `s`: the first part `V₁` (a set of
points), the family of blocks that are the vertices of `V₂`, and the coloring `c` of the
coherent configuration `X` of step 3 of §9.4 on the vertex set "points of `V₁` plus
blocks", subject to the `Case` of §9.6.

The two parts are data of the object, so a morphism carries `V₁` onto `V₁` and the blocks
onto the blocks; since they are vertex-color classes of a coherent configuration, a
color-preserving bijection does this anyway, and carrying them as data is the cheapest way
to say so. -/
structure BlkImprimitiveObj (s : Set Ω) where
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
  /-- Normalization of the padding: outside the vertex set the coloring is the fixed
  color `0`.  The same normalization as `Babai.VColBipBlk.g_off`, and for the same reason:
  without it the padding would be free data and would enter the automorphism group, which
  is where the symmetry defect of §9.6 is read. -/
  c_off : ∀ A B, ¬ (IsVertexOn part₁ blocks A ∧ IsVertexOn part₁ blocks B) → c A B = 0
  /-- The `Case` of §9.6. -/
  case : IsImprimitiveCaseOn c {A | ∃ x, part₁ x ∧ A = {x}} blocks

/-- §9.6.  The category of the inputs of Lemma 9.6.1 in the wider category: morphisms are
the bijections of the point set that carry the first part to the first part, blocks to
blocks, and the coloring to itself. -/
def BlkImprimitiveCases (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω where
  Obj s := BlkImprimitiveObj s
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

/-- §9.6.  **The padding of `c` does not restrict the morphisms.**  A bijection of the
point sets that carries the first part to the first part, blocks to blocks and the
coloring to itself *on the vertices* is a morphism of `Babai.BlkImprimitiveCases`.

This is the counterpart of `Babai.VColBipBlk.isTwin_iff` for the category of §9.6: the
automorphism group of an object is the automorphism group of the coherent configuration on
the vertex set "points of `V₁` plus blocks", and nothing more. -/
theorem BlkImprimitiveObj.isIso_of_vertexColor {s t : Set Ω} {X : BlkImprimitiveObj s}
    {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}
    (hp : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x)
    (hb : ∀ B, φ '' B ∈ Y.blocks ↔ B ∈ X.blocks)
    (hc : ∀ A B, IsVertexOn X.part₁ X.blocks A → IsVertexOn X.part₁ X.blocks B →
      Y.c (φ '' A) (φ '' B) = X.c A B) :
    φ ∈ (BlkImprimitiveCases Ω).Iso X Y := by
  refine ⟨hp, hb, fun A B => ?_⟩
  by_cases hA : IsVertexOn X.part₁ X.blocks A
  · by_cases hB : IsVertexOn X.part₁ X.blocks B
    · exact hc A B hA hB
    · rw [X.c_off A B (fun h => hB h.2),
        Y.c_off _ _ (fun h => hB ((isVertexOn_image_iff hp hb B).1 h.2))]
  · rw [X.c_off A B (fun h => hA h.1),
      Y.c_off _ _ (fun h => hA ((isVertexOn_image_iff hp hb A).1 h.1))]

/-- The first part `V₁` of an input of Lemma 9.6.1, as a subset of the ambient type. -/
def BlkImprimitiveCases.V₁ (X : Pt (BlkImprimitiveCases Ω)) : Set Ω :=
  Subtype.val '' {x | X.obj.part₁ x}

/-- `n₂ = |V₂|`: the **number of blocks** of an input of Lemma 9.6.1.  This is the
multiplicative cost of Lemma 9.6.1, and what §9.5 measures. -/
noncomputable def BlkImprimitiveCases.numBlocks (X : Pt (BlkImprimitiveCases Ω)) : ℕ :=
  X.obj.blocks.ncard

/-- The outcome of Lemma 9.6.1 for the first part `V₁` and the number `n₂` of blocks:
*"a canonical colored `1/2`-partition of `V₁`"*, or *"a canonical bipartite graph
`Y = (V₁, W₂; F)` such that `|W₂| ≤ |V₂|/2` such that the symmetry defect of `V₁` in `Y` is
`≥ 1/2`"*.

In the second branch `Y` is an object of the wider category, so `|W₂|` is its number of
blocks.  Both branches of step 2 of Procedure ImprimitiveCase land here: branch 2(i)
returns `Zᵢ`, whose blocks are the points of one block `Bᵢ` read as singletons, and branch
2(ii) returns the contraction, whose blocks are the `Bᵢ` themselves
(`Babai.VColBipBlk.contract`). -/
def IsBlkImprimitiveOutcome (V₁ : Set Ω) (n₂ : ℕ)
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))) : Prop :=
  match Z.obj with
  | Sum.inl P => Z.car = V₁ ∧ letI : Fintype ↥Z.car := Fintype.ofFinite _;
      P.IsAlphaPartition (1 / 2)
  | Sum.inr Y => letI : Fintype ↥Z.car := Fintype.ofFinite _;
      letI : DecidableEq ↥Z.car := Classical.decEq _
      Subtype.val '' Y.V₁ = V₁ ∧ 2 * Y.numBlocks ≤ n₂ ∧ 1 / 2 ≤ Y.defect₁

/-! ### Step 1 of Procedure ImprimitiveCase, in the wider category

*"1. If `(∀j ∈ J)(d_j ≤ n₁/2)` then individualize some `x ∈ V₂`.  This splits `V₁` into
color classes of size `d_j`.  Return this partition of `V₁`, exit."*

Individualizing a vertex of `V₂` is the choice of a block `B` of the input, and the
returned partition of `V₁` is the partition into the classes of the coloring
`x ↦ c({x}, B)` (`Babai.kerPartition`).  There is one outcome per vertex of `V₂`, which is
the multiplicative cost `n₂` of step 1. -/

/-- The colored partition of a subset `W`, read as an outcome of a category
`Babai.Cat.sum (Babai.ColoredPartitions Ω ℕ) D`.  Word for word `Babai.kerOutcome`, whose
second summand is fixed to the Johnson schemes of §9.2; §9.6 needs the same construction
with the bipartite graphs of the wider category as the second summand. -/
def kerOutcomeL (D : Cat.{0, 0} Ω) {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) D)).Obj s :=
  ⟨⟨Subtype.val '' W, by rintro z ⟨w, -, rfl⟩; exact w.2⟩, Sum.inl (kerPartition W col)⟩

@[simp] theorem kerOutcomeL_car (D : Cat.{0, 0} Ω) {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    (kerOutcomeL D W col).1.1 = Subtype.val '' W := rfl

/-- §6.  Condition (ii) of Definition 6.0.1 for `Babai.kerOutcomeL`, as
`Babai.kerOutcome_mem_subIso` for `Babai.kerOutcome`. -/
theorem kerOutcomeL_mem_subIso (D : Cat.{0, 0} Ω) {s t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s}
    {W' : Set ↥t} (h : ∀ x, φ x ∈ W' ↔ x ∈ W) {col : ↥s → ℕ} {col' : ↥t → ℕ}
    (hc : ∀ x, col' (φ x) = col x) :
    φ ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) D)).Iso
      (kerOutcomeL D W col) (kerOutcomeL D W' col') :=
  ⟨subEquiv φ h, fun _ => rfl, kerPartition_mem_iso φ h hc⟩

/-- `⌊n/2⌋ ≤ n/2` after casting to the reals: the threshold `1/2` of Lemma 9.6.1. -/
private theorem cast_div_two_le (n : ℕ) : ((n / 2 : ℕ) : ℝ) ≤ 1 / 2 * (n : ℝ) := by
  have h2 : 2 * (n / 2) ≤ n := by omega
  have hR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  linarith

/-- Procedure ImprimitiveCase, **the branch condition of step 1**: *"`(∀j ∈ J)(d_j ≤
n₁/2)`"*.

`d_j` is the in-degree of a vertex `y ∈ V₂` in the color `j` of the link, that is the
number of points of `V₁` joined to `y` in color `j`; it does not depend on `y` by the
homogeneity of `X₂`, but the condition is stated for every vertex, which is the same
condition and needs no homogeneity.  A color `j` outside `J` contributes an empty class, so
quantifying over all of `ℕ` rather than over `J` adds nothing. -/
def ImprimitiveSplits {s : Set Ω} (X : BlkImprimitiveObj s) : Prop :=
  ∀ B ∈ X.blocks, ∀ k : ℕ,
    2 * {x : ↥s | X.part₁ x ∧ X.c {x} B = k}.ncard ≤ {x : ↥s | X.part₁ x}.ncard

/-- Procedure ImprimitiveCase, step 1.  The outcome for the individualized vertex `B` of
`V₂`: the partition of `V₁` into the classes of the coloring `x ↦ c({x}, B)`. -/
def imprimitiveStep1Outcome {s : Set Ω} (X : BlkImprimitiveObj s) (B : Set ↥s) :
    (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s :=
  kerOutcomeL (VColBlkGraphs Ω ℕ) {x | X.part₁ x} (fun x => X.c {x} B)

/-- §9.6.  There is at least one vertex in `V₂`: the link `X₁₂` is nontrivial, so it has an
edge, whose second endpoint is a vertex of `V₂`, that is a block. -/
theorem BlkImprimitiveObj.blocks_nonempty' {s : Set Ω} (X : BlkImprimitiveObj s) :
    X.blocks.Nonempty := by
  obtain ⟨-, y₁, -, -, -⟩ := X.case.toIsBipartiteCase.link_nontrivial
  exact ⟨(y₁.1 : Set ↥s), y₁.2⟩

/-- The branch condition of step 1 is an isomorphism invariant. -/
theorem imprimitiveSplits_congr {X Y : Pt (BlkImprimitiveCases Ω)}
    (h : ((BlkImprimitiveCases Ω).IsoP X Y).Nonempty)
    (hX : ImprimitiveSplits X.obj) : ImprimitiveSplits Y.obj := by
  obtain ⟨φ, hp, hb, hc⟩ := h
  intro B' hB' k
  have hBmem : φ.symm '' B' ∈ X.obj.blocks := by
    rw [← hb (φ.symm '' B'), Equiv.image_symm_image]; exact hB'
  have hset : {y : ↥Y.car | Y.obj.part₁ y ∧ Y.obj.c {y} B' = k}
      = φ '' {x : ↥X.car | X.obj.part₁ x ∧ X.obj.c {x} (φ.symm '' B') = k} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨φ.symm y, ⟨(hp (φ.symm y)).1 (by simpa using h1), ?_⟩, by simp⟩
      have := hc {φ.symm y} (φ.symm '' B')
      rw [Set.image_singleton, Equiv.apply_symm_apply, Equiv.image_symm_image] at this
      rw [← this]; exact h2
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨(hp x).2 h1, ?_⟩
      have := hc {x} (φ.symm '' B')
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

/-- Lemma 9.6.1, **the branch of step 1 of Procedure ImprimitiveCase**.  *"If
`(∀j ∈ J)(d_j ≤ n₁/2)` then individualize some `x ∈ V₂`.  This splits `V₁` into color
classes of size `d_j`.  Return this partition of `V₁`, exit.  (: canonical colored
`1/2`-partition of `V₁` found :)"*  (Version 2.5, lines 4204-4206.)

The multiplicative cost is the choice of the individualized vertex of `V₂`, that is of a
block: `n₂`, the cost of Lemma 9.6.1.  Each class of the returned partition has at most
`n₁/2` points, which is the branch condition (`Babai.imprimitiveCase_split` is the same
statement for the abstract data), so the partition is a colored `1/2`-partition of
`V₁`. -/
theorem lemma_9_6_1_step1 :
    FindsAtMultCost ((BlkImprimitiveCases Ω).full fun _ X => ImprimitiveSplits X)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkImprimitiveCases.numBlocks ⟨X.car, X.obj.1⟩)
      (fun X Z => IsBlkImprimitiveOutcome (BlkImprimitiveCases.V₁ ⟨X.car, X.obj.1⟩)
        (BlkImprimitiveCases.numBlocks ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => (fun B => imprimitiveStep1Outcome X.obj.1 B) '' X.obj.1.blocks)
    (fun X => ?_) (fun X => Set.toFinite _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · obtain ⟨B, hB⟩ := X.obj.1.blocks_nonempty'
    exact ⟨_, ⟨B, hB, rfl⟩⟩
  · -- one outcome per vertex of `V₂`
    exact Set.ncard_image_le (Set.toFinite _)
  · obtain ⟨B, hB, rfl⟩ := hZ
    obtain ⟨hp, hb, hc⟩ := hf
    refine ⟨imprimitiveStep1Outcome Y.obj.1 (f '' B), ⟨f '' B, (hb B).2 hB, rfl⟩, ?_⟩
    refine kerOutcomeL_mem_subIso _ f (fun x => (hp x)) (fun x => ?_)
    have := hc {x} B
    rwa [Set.image_singleton] at this
  · obtain ⟨B, hB, rfl⟩ := hZ
    refine ⟨rfl, ?_⟩
    refine kerPartition_isAlphaPartition _ _ _
      (k := {x : ↥X.car | X.obj.1.part₁ x}.ncard / 2) (fun x hx => ?_) ?_
    · have hbr := X.obj.2 B hB (X.obj.1.c {x} B)
      have : {y : ↥X.car | y ∈ {x : ↥X.car | X.obj.1.part₁ x} ∧
          X.obj.1.c {y} B = X.obj.1.c {x} B}
          = {y : ↥X.car | X.obj.1.part₁ y ∧ X.obj.1.c {y} B = X.obj.1.c {x} B} := rfl
      rw [this]
      omega
    · exact cast_div_two_le _

/-! ### Step 2 of Procedure ImprimitiveCase, in the wider category

*"else (: for some `j ∈ J` we have `d_j > n₁/2` :)  Let `B₁, …, B_m` be the connected
components of a disconnected non-diagonal color in `X₂`, say `R₂`.  For `i = 1, …, m` let
`Zᵢ = X(V₁, Bᵢ; R_j)`.  (i) if `(∃i)(`the symmetry defect of `V₁` in `Zᵢ` is `≥ 1/2)` then
`Y ← Zᵢ` … (ii) else let `h ∈ J`, `h ≠ j`, and let `Y = (V₁, [m]; R_h)` …"*
(Version 2.5, lines 4207–4216.)

Everything below is defined from the coloring `c` of the object and its two parts alone,
because the coherent configurations that `Babai.IsImprimitiveCaseOn` asserts are obtained
by choice and are not natural in the object (the pattern of
`Workspace/SplitOrJohnson/UpccToBip.lean`).  The canonical choices are:

* `Babai.BlkImprimitiveObj.c₂`, the coloring of `X₂`: the coloring of the object read on
  the blocks, which are the vertices of `V₂`;
* `Babai.blockColor` of that coloring — *"say `R₂`"*, the smallest disconnected
  non-diagonal color — and `Babai.blockOf`, which give the groups
  `Babai.BlkImprimitiveObj.group` of blocks, that is the `B₁, …, B_m`;
* `Babai.BlkImprimitiveObj.jColor`, the smallest color `j` of the link with `d_j > n₁/2`,
  which exists exactly when the branch condition of step 1 fails;
* `Babai.BlkImprimitiveObj.hColor`, the smallest color of the link other than `j`, which
  exists because the link is nontrivial, and which is the `h` of step 2(ii).

A *vertex* of `V₂` of the input is a block `B ∈ X.blocks`; a *group* is a set of such
blocks, one of the `Bᵢ` of the paper.  The two outcomes are

* `Babai.BlkImprimitiveObj.blkZ X G` — the graph `Zᵢ` of step 2(i), whose blocks are the
  members of the group `G`; and
* `Babai.BlkImprimitiveObj.blkContr X` — the contracted graph `Y` of step 2(ii), whose
  blocks are the unions of the groups.

Both carry the constant vertex colorings `f = 0` and `g = 0`: the paper's `Zᵢ` and `Y` are
plain bipartite graphs, and by `Babai.VColBipBlk.defect₁_toBip` the symmetry defect of the
object is then the symmetry defect of the bipartite graph, which is what
`Babai.case_9_6_1_step2` computes. -/

namespace BlkImprimitiveObj

variable {s : Set Ω} (X : BlkImprimitiveObj s)

/-! #### The vertex set of the configuration of step 3 of §9.4

The field `case` of `Babai.BlkImprimitiveObj` is a statement about the coloring read on
the vertex set *"points of `V₁` plus blocks"*.  The definitions below name that vertex
set and that coloring, and the lemmas after them are the two facts from §3.3 that §9.6
uses over and over: a vertex lies in `V₁` or in `V₂` according to its diagonal color
(Def. 3.1.6 for a bihomogeneous configuration), and the color of an edge determines the
vertex colors of its two ends (Obs. 3.3.4). -/

/-- §9.6.  `𝒱₁`: the singletons of the points of the first part, which are the vertices of
`V₁`. -/
def sglSet : Set (Set ↥s) := {A | ∃ x, X.part₁ x ∧ A = {x}}

/-- §9.6.  The vertex set of the coherent configuration `X` of step 3 of §9.4: the
singletons of the points of `V₁` together with the blocks. -/
def vtxSet : Set (Set ↥s) := X.sglSet ∪ X.blocks

/-- §9.6.  The coloring of that configuration, read on its vertex set. -/
def vc : ↥X.vtxSet → ↥X.vtxSet → ℕ := fun u v => X.c (u : Set ↥s) (v : Set ↥s)

/-- The first part, as a set of points. -/
def Pt₁ : Set ↥s := {x | X.part₁ x}

/-- The `Case` of §9.6, read on the vertex set. -/
theorem case' : IsImprimitiveCase X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet}
    {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := X.case

/-- The vertex of `V₁` at a point of the first part. -/
def vtxOfPt (x : ↥X.Pt₁) : ↥X.vtxSet := ⟨{(x : ↥s)}, Or.inl ⟨(x : ↥s), x.2, rfl⟩⟩

/-- The vertex of `V₂` at a block. -/
def vtxOfBlk (B : ↥X.blocks) : ↥X.vtxSet := ⟨(B : Set ↥s), Or.inr B.2⟩

@[simp] theorem vtxOfPt_coe (x : ↥X.Pt₁) :
    ((X.vtxOfPt x : ↥X.vtxSet) : Set ↥s) = {(x : ↥s)} := rfl

@[simp] theorem vtxOfBlk_coe (B : ↥X.blocks) :
    ((X.vtxOfBlk B : ↥X.vtxSet) : Set ↥s) = (B : Set ↥s) := rfl

theorem vtxOfPt_injective : Function.Injective X.vtxOfPt := by
  intro x y h
  have : ({(x : ↥s)} : Set ↥s) = {(y : ↥s)} := congrArg Subtype.val h
  exact Subtype.ext (Set.singleton_eq_singleton_iff.1 this)

theorem vtxOfBlk_injective : Function.Injective X.vtxOfBlk := by
  intro B B' h
  have : (B : Set ↥s) = (B' : Set ↥s) := congrArg (fun u : ↥X.vtxSet => (u : Set ↥s)) h
  exact Subtype.ext this

/-- A singleton of a point of `V₁` is not a block: a block avoids the first part. -/
theorem singleton_notMem_blocks {x : ↥s} (hx : X.part₁ x) :
    ({x} : Set ↥s) ∉ X.blocks := fun h => X.blocks_off₁ _ h x rfl hx

theorem vtxOfPt_notMem_blocks (x : ↥X.Pt₁) :
    ((X.vtxOfPt x : ↥X.vtxSet) : Set ↥s) ∉ X.blocks := X.singleton_notMem_blocks x.2

theorem vtxOfBlk_mem_blocks (B : ↥X.blocks) :
    ((X.vtxOfBlk B : ↥X.vtxSet) : Set ↥s) ∈ X.blocks := B.2

/-- A vertex that is not a block is the singleton of a point of the first part. -/
theorem exists_vtxOfPt {u : ↥X.vtxSet} (hu : (u : Set ↥s) ∉ X.blocks) :
    ∃ x : ↥X.Pt₁, X.vtxOfPt x = u := by
  rcases u.2 with ⟨x, hx, hux⟩ | h
  · exact ⟨⟨x, hx⟩, Subtype.ext hux.symm⟩
  · exact absurd h hu

@[simp] theorem vc_pt_blk (x : ↥X.Pt₁) (B : ↥X.blocks) :
    X.vc (X.vtxOfPt x) (X.vtxOfBlk B) = X.c {(x : ↥s)} (B : Set ↥s) := rfl

/-- The coloring of the vertex set is the coloring of a coherent configuration: this is
the hypothesis of Cor. 3.4.9 (N8) and of Obs. 3.3.5 (N7). -/
theorem vc_isCoherentColoring :
    ∃ P : PartitionStructure ↥X.vtxSet, P.IsCoherent ∧ P.natColor = X.vc := by
  obtain ⟨P, hP, hnat, -⟩ := X.case'.toIsBipartiteCase.coherent
  exact ⟨P, hP, hnat⟩

/-- **A vertex lies in `V₂` according to its diagonal color.**  Def. 3.1.6 for the
bihomogeneous configuration of §9.6: `V₁` and `V₂` are the two vertex-color classes, so
two vertices have the same diagonal color exactly when they lie in the same part. -/
theorem vc_diag_eq_iff (u v : ↥X.vtxSet) :
    X.vc u u = X.vc v v ↔ ((u : Set ↥s) ∈ X.blocks ↔ (v : Set ↥s) ∈ X.blocks) := by
  obtain ⟨P, hP, hnat, i, j, hij, hV₁, hV₂, -⟩ := X.case'.toIsBipartiteCase.coherent
  have hval : ∀ w : ↥X.vtxSet, X.vc w w = (P.vcolor w : ℕ) := by
    intro w; rw [← hnat]; rfl
  have hmem₂ : ∀ w : ↥X.vtxSet, ((w : Set ↥s) ∈ X.blocks ↔ P.vcolor w = j) := by
    intro w
    have : w ∈ {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} ↔ w ∈ P.vertexClass j := by
      rw [hV₂]
    exact this
  have hmem₁ : ∀ w : ↥X.vtxSet, ((w : Set ↥s) ∈ X.sglSet ↔ P.vcolor w = i) := by
    intro w
    have : w ∈ {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet} ↔ w ∈ P.vertexClass i := by
      rw [hV₁]
    exact this
  rw [hval u, hval v]
  constructor
  · intro h
    have hvc : P.vcolor u = P.vcolor v := Fin.ext h
    rw [hmem₂ u, hmem₂ v, hvc]
  · intro h
    by_cases hu : (u : Set ↥s) ∈ X.blocks
    · have hv : (v : Set ↥s) ∈ X.blocks := h.1 hu
      rw [(hmem₂ u).1 hu, (hmem₂ v).1 hv]
    · have hv : (v : Set ↥s) ∉ X.blocks := fun hc => hu (h.2 hc)
      have hu' : (u : Set ↥s) ∈ X.sglSet := u.2.resolve_right hu
      have hv' : (v : Set ↥s) ∈ X.sglSet := v.2.resolve_right hv
      rw [(hmem₁ u).1 hu', (hmem₁ v).1 hv']

/-- Observation 3.3.4.  The color of an edge determines the vertex color of its tail. -/
theorem vc_tail_eq {u v u' v' : ↥X.vtxSet} (h : X.vc u v = X.vc u' v') :
    X.vc u u = X.vc u' u' := by
  obtain ⟨P, hP, hnat, -⟩ := X.case'.toIsBipartiteCase.coherent
  have h' : P.natColor u v = P.natColor u' v' := by rw [hnat]; exact h
  have hc : P.color u v = P.color u' v' := (P.natColor_eq_iff _ _ _ _).1 h'
  have h1 : P.vcolor u = P.tailColor (P.color u v) := P.vcolor_fst_eq hP rfl
  have h2 : P.vcolor u' = P.tailColor (P.color u' v') := P.vcolor_fst_eq hP rfl
  have hv : P.vcolor u = P.vcolor u' := by rw [h1, h2, hc]
  rw [← hnat]
  exact congrArg Fin.val hv

/-- Observation 3.3.4.  The color of an edge determines the vertex color of its head. -/
theorem vc_head_eq {u v u' v' : ↥X.vtxSet} (h : X.vc u v = X.vc u' v') :
    X.vc v v = X.vc v' v' := by
  obtain ⟨P, hP, hnat, -⟩ := X.case'.toIsBipartiteCase.coherent
  have h' : P.natColor u v = P.natColor u' v' := by rw [hnat]; exact h
  have hc : P.color u v = P.color u' v' := (P.natColor_eq_iff _ _ _ _).1 h'
  have h1 : P.vcolor v = P.headColor (P.color u v) := P.vcolor_snd_eq hP rfl
  have h2 : P.vcolor v' = P.headColor (P.color u' v') := P.vcolor_snd_eq hP rfl
  have hv : P.vcolor v = P.vcolor v' := by rw [h1, h2, hc]
  rw [← hnat]
  exact congrArg Fin.val hv

/-- §9.6.  The coloring of `X₂`: the coloring of the object read on the vertices of `V₂`,
which are the blocks. -/
def c₂ : ↥X.blocks → ↥X.blocks → ℕ := fun u v => X.c (u : Set ↥s) (v : Set ↥s)

/-- §9.6.  *"Let `B₁, …, B_m` be the connected components of a disconnected non-diagonal
color in `X₂`, say `R₂`."*  The group `Bᵢ` of blocks containing the block `B`. -/
def group (B : ↥X.blocks) : Set ↥X.blocks := blockOf X.c₂ B

/-- §9.6.  The set of groups `{B₁, …, B_m}`. -/
def groups : Set (Set ↥X.blocks) := Set.range X.group

/-! #### Proposition 3.4.4 for the groups

*"Let `B₁, …, B_m` be the connected components of a disconnected non-diagonal color in
`X₂`, say `R₂`."*  The configuration `X₂` is the field `imprimitive₂` of the `Case`, which
lives on the second vertex class; `Babai.BlkImprimitiveObj.c₂` is the same coloring read
on the blocks.  The bijection `Babai.BlkImprimitiveObj.blkEquiv` between the two carries
the canonical color and the components (`Babai.blockColor_map`, `Babai.blockOf_map`), so
Prop. 3.4.4 for `X₂` gives the two size bounds of step 2: every group has at least two
blocks, and there are at least two groups of equal size. -/

/-- The vertex of `V₂` at a block, as a bijection of the blocks with the second vertex
class. -/
def blkEquiv : ↥X.blocks ≃ ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} where
  toFun B := ⟨X.vtxOfBlk B, B.2⟩
  invFun u := ⟨((u : ↥X.vtxSet) : Set ↥s), u.2⟩
  left_inv _ := rfl
  right_inv u := Subtype.ext (Subtype.ext rfl)

/-- The coloring `Babai.BlkImprimitiveObj.vc` of the vertices, read on the second vertex
class.  This is the coloring that the field `imprimitive₂` of the `Case` names the color
classes of; `Babai.BlkImprimitiveObj.c₂` is the same coloring read on the blocks. -/
def vc₂ : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} →
    ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} → ℕ :=
  fun u v => X.vc (u : ↥X.vtxSet) (v : ↥X.vtxSet)

/-- The coloring of the second vertex class and the coloring
`Babai.BlkImprimitiveObj.c₂` on the blocks agree under
`Babai.BlkImprimitiveObj.blkEquiv`. -/
theorem vc₂_blkEquiv (u v : ↥X.blocks) : X.vc₂ (X.blkEquiv u) (X.blkEquiv v) = X.c₂ u v :=
  rfl

/-- §9.6.  *"a disconnected non-diagonal color in `X₂`"* exists: `X₂` is homogeneous and
not primitive (`Babai.exists_isDisconnectedColor`), read on the blocks.

The field `imprimitive₂` gives the color *classes* of `X₂`, not the color labels, so the
disconnected color of `X₂` is carried to the coloring of the input by
`Babai.exists_isDisconnectedColor_congr` and then to the blocks by
`Babai.isDisconnectedColor_map`. -/
theorem exists_disconnected_c₂ : ∃ k, IsDisconnectedColor X.c₂ k := by
  classical
  obtain ⟨P₂, hcoh, hhom, hprim, hnat⟩ := X.case'.imprimitive₂
  have hker : SameKernel P₂.natColor X.vc₂ := fun a b a' b' => hnat a b a' b'
  obtain ⟨k, hk⟩ := (exists_isDisconnectedColor_congr hker).1
    (exists_isDisconnectedColor hhom hprim)
  exact ⟨k, (isDisconnectedColor_map X.blkEquiv (X.vc₂_blkEquiv) k).1 hk⟩

/-- Proposition 3.4.4.  Every group has at least two blocks. -/
theorem group_nontrivial (B : ↥X.blocks) : (X.group B).Nontrivial := by
  classical
  obtain ⟨P₂, hcoh, hhom, hprim, hnat⟩ := X.case'.imprimitive₂
  letI : Fintype ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := Fintype.ofFinite _
  letI : DecidableEq ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := Classical.decEq _
  have hker : SameKernel X.vc₂ P₂.natColor := fun a b a' b' => (hnat a b a' b').symm
  have hex : ∃ k, IsDisconnectedColor X.vc₂ k :=
    (exists_isDisconnectedColor_congr hker.symm).1 (exists_isDisconnectedColor hhom hprim)
  have hnt := blockOf_nontrivial_of_sameKernel hcoh hhom hker hex (X.blkEquiv B)
  rw [blockOf_map X.blkEquiv (X.vc₂_blkEquiv) B] at hnt
  obtain ⟨p, hp, q, hq, hpq⟩ := hnt
  obtain ⟨p', hp', rfl⟩ := hp
  obtain ⟨q', hq', rfl⟩ := hq
  exact ⟨p', hp', q', hq', fun hc => hpq (congrArg X.blkEquiv hc)⟩

/-- Proposition 3.4.4.  The groups form an equipartition of the set of blocks. -/
theorem groups_isEquipartition : IsEquipartition X.groups where
  nonempty := by rintro A ⟨B, rfl⟩; exact ⟨B, mem_blockOf_self _ _⟩
  pairwiseDisjoint := by
    rintro A ⟨B, rfl⟩ A' ⟨B', rfl⟩ hne
    rcases (colorDigraph X.c₂ (blockColor X.c₂)).weakComponent_eq_or_disjoint B B' with h | h
    · exact absurd h hne
    · exact h
  covers := by
    ext B
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    exact ⟨X.group B, ⟨B, rfl⟩, mem_blockOf_self _ _⟩
  equal_size := by
    classical
    obtain ⟨P₂, hcoh, hhom, hprim, hnat⟩ := X.case'.imprimitive₂
    letI : Fintype ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := Fintype.ofFinite _
    letI : DecidableEq ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} := Classical.decEq _
    have hker : SameKernel X.vc₂ P₂.natColor := fun a b a' b' => (hnat a b a' b').symm
    have hex : ∃ k, IsDisconnectedColor X.vc₂ k :=
      (exists_isDisconnectedColor_congr hker.symm).1 (exists_isDisconnectedColor hhom hprim)
    have hequi := isEquipartition_blocks_of_sameKernel hcoh hhom hker hex
    rintro A ⟨B, rfl⟩ A' ⟨B', rfl⟩
    have h1 := hequi.equal_size _ (blockOf_mem_blocks X.vc₂ (X.blkEquiv B))
      _ (blockOf_mem_blocks X.vc₂ (X.blkEquiv B'))
    rw [blockOf_map X.blkEquiv (X.vc₂_blkEquiv) B,
      blockOf_map X.blkEquiv (X.vc₂_blkEquiv) B',
      Set.ncard_image_of_injective _ X.blkEquiv.injective,
      Set.ncard_image_of_injective _ X.blkEquiv.injective] at h1
    exact h1

/-- Proposition 3.4.4.  There are at least two groups: the canonical color is
disconnected. -/
theorem exists_group_ne : ∃ G ∈ X.groups, ∃ G' ∈ X.groups, G ≠ G' :=
  (colorDigraph X.c₂ (blockColor X.c₂)).exists_ne_weakComponents
    (blockColor_spec X.exists_disconnected_c₂).2.2

/-- §9.6, step 2(ii).  The union of the blocks of a group: one vertex of the contracted
graph `Y`. -/
def groupUnion (B : ↥X.blocks) : Set ↥s := ⋃ C ∈ X.group B, (C : Set ↥s)

/-- §9.6.  *"for some `j ∈ J` we have `d_j > n₁/2`"*.  The colors of the link that occur
on more than half of `V₁` at some vertex of `V₂`. -/
def IsBigColor (k : ℕ) : Prop :=
  ∃ B ∈ X.blocks,
    {x : ↥s | X.part₁ x}.ncard < 2 * {x : ↥s | X.part₁ x ∧ X.c {x} B = k}.ncard

open scoped Classical in
/-- §9.6.  The canonical choice of the color `j` of step 2: the smallest color of the link
that occurs on more than half of `V₁` at some vertex of `V₂`.  Taking the smallest label
is what makes the choice canonical, as in `Babai.blockColor`. -/
noncomputable def jColor : ℕ := if h : ∃ k, X.IsBigColor k then Nat.find h else 0

/-- §9.6.  *"Let `h ∈ J`, `h ≠ j`."*  A color of the link other than `j`. -/
def IsOtherColor (k : ℕ) : Prop :=
  k ≠ X.jColor ∧ ∃ x, X.part₁ x ∧ ∃ B ∈ X.blocks, X.c {x} B = k

open scoped Classical in
/-- §9.6, step 2(ii).  The canonical choice of the color `h`: the smallest color of the
link other than `j`.  It exists because the link is nontrivial. -/
noncomputable def hColor : ℕ := if h : ∃ k, X.IsOtherColor k then Nat.find h else 0

/-- §9.6, step 2(i).  The bipartite graph `Zᵢ = X(V₁, Bᵢ; R_j)` for the group `G`, as an
object of `Babai.VColBlkGraphs`: the first part is `V₁`, the vertices of the second part
are the blocks of the group `G`, and the edges are the pairs of color `j`. -/
def blkZ (G : Set ↥X.blocks) : VColBipBlk ↥s ℕ where
  part₁ := X.part₁
  blocks := Subtype.val '' G
  blocks_nonempty := by rintro B ⟨C, -, rfl⟩; exact X.blocks_nonempty _ C.2
  blocks_disjoint := by
    rintro B ⟨C, -, rfl⟩ B' ⟨C', -, rfl⟩ hne
    exact X.blocks_disjoint _ C.2 _ C'.2 hne
  blocks_off₁ := by rintro B ⟨C, -, rfl⟩ x hx; exact X.blocks_off₁ _ C.2 x hx
  E := {p | p.2 ∈ Subtype.val '' G ∧ X.part₁ p.1 ∧ X.c {p.1} p.2 = X.jColor}
  E_sub := fun p hp => ⟨hp.2.1, hp.1⟩
  f := fun _ => 0
  g := fun _ => 0
  g_off := fun _ _ => rfl
  -- No hint: the outcome of §9.6 halves `n₂`, and a contraction inherits nothing from the
  -- structure on the old blocks anyway.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

/-- The blocks of a group are pairwise disjoint as sets of points, so two group unions are
equal or disjoint. -/
theorem groupUnion_disjoint {B B' : ↥X.blocks} (hne : X.groupUnion B ≠ X.groupUnion B') :
    Disjoint (X.groupUnion B) (X.groupUnion B') := by
  have hgr : X.group B ≠ X.group B' := by
    intro hcon
    exact hne (by unfold groupUnion; rw [hcon])
  have hdisj : Disjoint (X.group B) (X.group B') := by
    rcases (colorDigraph X.c₂ (blockColor X.c₂)).weakComponent_eq_or_disjoint B B' with h | h
    · exact absurd h hgr
    · exact h
  rw [Set.disjoint_left]
  rintro x hx hx'
  simp only [groupUnion, Set.mem_iUnion, exists_prop] at hx hx'
  obtain ⟨C, hC, hxC⟩ := hx
  obtain ⟨C', hC', hxC'⟩ := hx'
  have hCC' : (C : Set ↥s) ≠ (C' : Set ↥s) := by
    intro hcon
    have : C = C' := Subtype.ext hcon
    subst this
    exact (Set.disjoint_left.1 hdisj hC) hC'
  exact (Set.disjoint_left.1 (X.blocks_disjoint _ C.2 _ C'.2 hCC')) hxC hxC'

/-- §9.6, step 2(ii).  The contracted bipartite graph `Y = (V₁, [m]; R_h)`, as an object
of `Babai.VColBlkGraphs`: the vertices of the second part are the unions of the groups,
and `x` is joined to such a union when some block inside it is joined to `x` in the color
`h`. -/
def blkContr : VColBipBlk ↥s ℕ where
  part₁ := X.part₁
  blocks := Set.range X.groupUnion
  blocks_nonempty := by
    rintro C ⟨B, rfl⟩
    obtain ⟨x, hx⟩ := X.blocks_nonempty _ B.2
    exact ⟨x, Set.mem_biUnion (mem_blockOf_self X.c₂ B) hx⟩
  blocks_disjoint := by
    rintro C ⟨B, rfl⟩ C' ⟨B', rfl⟩ hne
    exact X.groupUnion_disjoint hne
  blocks_off₁ := by
    rintro C ⟨B, rfl⟩ x hx
    simp only [groupUnion, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨D, -, hxD⟩ := hx
    exact X.blocks_off₁ _ D.2 x hxD
  E := {p | p.2 ∈ Set.range X.groupUnion ∧ X.part₁ p.1 ∧
    ∃ B ∈ X.blocks, B ⊆ p.2 ∧ X.c {p.1} B = X.hColor}
  E_sub := fun p hp => ⟨hp.2.1, hp.1⟩
  f := fun _ => 0
  g := fun _ => 0
  g_off := fun _ _ => rfl
  -- No hint: the outcome of §9.6 halves `n₂`, and a contraction inherits nothing from the
  -- structure on the old blocks anyway.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

@[simp] theorem blkZ_V₁ (G : Set ↥X.blocks) : (X.blkZ G).V₁ = {x | X.part₁ x} := rfl

@[simp] theorem blkContr_V₁ : X.blkContr.V₁ = {x | X.part₁ x} := rfl

/-- §9.6, step 2.  The two branches of step 2, as a family of candidate outcomes: the
graphs `Zᵢ` of branch 2(i), one for each group `Bᵢ`, and the contracted graph `Y` of
branch 2(ii). -/
def step2Cands : Set (VColBipBlk ↥s ℕ) := X.blkZ '' X.groups ∪ {X.blkContr}

open scoped Classical in
/-- Section 9.6, step 2(i): at least one block restriction keeps the required defect. -/
def hasGoodBlock : Prop :=
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  ∃ G ∈ X.groups, 1 / 2 ≤ (X.blkZ G).defect₁

open scoped Classical in
/-- Section 9.6, step 2: use the passing block restrictions if any exist.
Only when all of them fail may the contraction be returned. -/
noncomputable def step2Out :
    Set ((Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s) :=
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  (fun Y : VColBipBlk ↥s ℕ =>
      (⟨⟨s, subset_rfl⟩, Sum.inr Y⟩ :
        (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Obj s)) ''
    {Y ∈ X.step2Cands | 1 / 2 ≤ Y.defect₁ ∧
      (X.hasGoodBlock → Y ∈ X.blkZ '' X.groups)}

end BlkImprimitiveObj

/-- The candidates of step 2 form a finite family: one graph per group, and the
contraction. -/
theorem step2Cands_finite {s : Set Ω} (X : BlkImprimitiveObj s) : X.step2Cands.Finite :=
  Set.Finite.union (Set.Finite.image _ (Set.toFinite _)) (Set.finite_singleton _)

/-- Every candidate of step 2 has the same first part `V₁` as the input. -/
theorem step2Cands_V₁ {s : Set Ω} {X : BlkImprimitiveObj s} {Y : VColBipBlk ↥s ℕ}
    (hY : Y ∈ X.step2Cands) : Y.V₁ = {x | X.part₁ x} := by
  rcases hY with ⟨G, -, rfl⟩ | rfl
  · rfl
  · rfl

/-! ### The three facts about step 2 that Lemma 9.6.1 needs -/

/-! ### The data that `Babai.case_9_6_1_step2` asks for

Step 2 of Procedure ImprimitiveCase is `Babai.case_9_6_1_step2` for the coloring
`c(x, B) = X.c {x} B` of the link, the color `j = jColor`, the color `h = hColor`, and the
map `B ↦ Bᵢ` that sends a block to its group.  The lemmas below supply its hypotheses:
`d_j` (the in-degree, constant by Obs. 3.3.5), `h ≠ j` and the non-emptiness of `R_h`
(the link is nontrivial), and the semiregularity of the contraction (Cor. 3.4.9). -/

namespace BlkImprimitiveObj

variable {s : Set Ω} (X : BlkImprimitiveObj s)

/-- §9.6.  *"`J = {c(x,y) | x ∈ V₁, y ∈ V₂}`"*: the colors that occur on the link. -/
def HasLinkColor (k : ℕ) : Prop := ∃ x, X.part₁ x ∧ ∃ B ∈ X.blocks, X.c {x} B = k

theorem hasLinkColor_of_vtx {u : ↥X.vtxSet} (hu : (u : Set ↥s) ∈ X.sglSet)
    {v : ↥X.vtxSet} (hv : (v : Set ↥s) ∈ X.blocks) : X.HasLinkColor (X.vc u v) := by
  obtain ⟨x, hx, hux⟩ := hu
  exact ⟨x, hx, (v : Set ↥s), hv, by rw [← hux]; rfl⟩

/-- §9.6.  *"`|J| ≥ 2` because the coloring of `V₁ × V₂` is a refinement of `E`"*: the link
is nontrivial, so some color of the link is not the color `j`. -/
theorem exists_isOtherColor : ∃ k, X.IsOtherColor k := by
  obtain ⟨x₁, y₁, x₂, y₂, hne⟩ := X.case'.toIsBipartiteCase.link_nontrivial
  have h₁ : X.HasLinkColor (X.vc (x₁ : ↥X.vtxSet) (y₁ : ↥X.vtxSet)) :=
    X.hasLinkColor_of_vtx x₁.2 y₁.2
  have h₂ : X.HasLinkColor (X.vc (x₂ : ↥X.vtxSet) (y₂ : ↥X.vtxSet)) :=
    X.hasLinkColor_of_vtx x₂.2 y₂.2
  by_cases hj : X.vc (x₁ : ↥X.vtxSet) (y₁ : ↥X.vtxSet) = X.jColor
  · exact ⟨_, fun hc => hne (hj.trans hc.symm), h₂⟩
  · exact ⟨_, hj, h₁⟩

/-- §9.6, step 2(ii).  The canonical color `h` is a color of the link other than `j`. -/
theorem isOtherColor_hColor : X.IsOtherColor X.hColor := by
  classical
  rw [BlkImprimitiveObj.hColor, dif_pos X.exists_isOtherColor]
  exact Nat.find_spec X.exists_isOtherColor

/-- §9.6, step 2.  If step 1 does not apply then the canonical color `j` is one for which
*"`d_j > n₁/2`"*. -/
theorem isBigColor_jColor (hsplit : ¬ ImprimitiveSplits X) : X.IsBigColor X.jColor := by
  classical
  have hex : ∃ k, X.IsBigColor k := by
    unfold ImprimitiveSplits at hsplit
    push_neg at hsplit
    obtain ⟨B, hB, k, hk⟩ := hsplit
    exact ⟨k, B, hB, hk⟩
  rw [BlkImprimitiveObj.jColor, dif_pos hex]
  exact Nat.find_spec hex

/-- Counting inside the first part is counting points of the first part. -/
theorem ncard_pt₁_setOf (p : ↥s → Prop) :
    {x : ↥X.Pt₁ | p (x : ↥s)}.ncard = {x : ↥s | X.part₁ x ∧ p x}.ncard := by
  have himg : Subtype.val '' {x : ↥X.Pt₁ | p (x : ↥s)} = {x : ↥s | X.part₁ x ∧ p x} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨z, h1⟩, h2, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The tail of an edge of a color of the link lies in the first part. -/
theorem notMem_blocks_of_link {k : ℕ} (hk : X.HasLinkColor k) {u v : ↥X.vtxSet}
    (hv : (v : Set ↥s) ∈ X.blocks) (huv : X.vc u v = k) : (u : Set ↥s) ∉ X.blocks := by
  obtain ⟨x₀, hx₀, C₀, hC₀, hcol⟩ := hk
  have h0 : X.vc (X.vtxOfPt ⟨x₀, hx₀⟩) (X.vtxOfBlk ⟨C₀, hC₀⟩) = k := hcol
  have hdiag := X.vc_tail_eq (huv.trans h0.symm)
  have h2 := (X.vc_diag_eq_iff u (X.vtxOfPt ⟨x₀, hx₀⟩)).1 hdiag
  exact fun hcon => X.vtxOfPt_notMem_blocks ⟨x₀, hx₀⟩ (h2.1 hcon)

/-- The head of an edge of a color of the link is a block. -/
theorem mem_blocks_of_link {k : ℕ} (hk : X.HasLinkColor k) {u v : ↥X.vtxSet}
    (huv : X.vc u v = k) : (v : Set ↥s) ∈ X.blocks := by
  obtain ⟨x₀, hx₀, C₀, hC₀, hcol⟩ := hk
  have h0 : X.vc (X.vtxOfPt ⟨x₀, hx₀⟩) (X.vtxOfBlk ⟨C₀, hC₀⟩) = k := hcol
  have hdiag := X.vc_head_eq (huv.trans h0.symm)
  exact ((X.vc_diag_eq_iff v (X.vtxOfBlk ⟨C₀, hC₀⟩)).1 hdiag).2 hC₀

/-- The in-neighbourhood of a block in a color of the link, read on the vertex set. -/
theorem inNbhd_vtx_eq {k : ℕ} (hk : X.HasLinkColor k) (b : ↥X.blocks) :
    {u : ↥X.vtxSet | X.vc u (X.vtxOfBlk b) = k}
      = X.vtxOfPt '' {x : ↥X.Pt₁ | X.c {(x : ↥s)} (b : Set ↥s) = k} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hu
    obtain ⟨x, hx⟩ := X.exists_vtxOfPt (X.notMem_blocks_of_link hk b.2 hu)
    exact ⟨x, by rw [← hx] at hu; exact hu, hx⟩
  · rintro ⟨x, hx, rfl⟩; exact hx

/-- §9.6, step 2.  The group of a block, read as a vertex of the contracted graph `Y`. -/
def grpOf (b : ↥X.blocks) : ↥X.groups := ⟨X.group b, ⟨b, rfl⟩⟩

theorem mem_group_iff_grpOf_eq {b b' : ↥X.blocks} :
    b' ∈ X.group b ↔ X.grpOf b' = X.grpOf b := by
  constructor
  · intro h
    exact Subtype.ext
      ((colorDigraph X.c₂ (blockColor X.c₂)).weakComponent_eq_of_mem h)
  · intro h
    have hgg : X.group b' = X.group b := congrArg Subtype.val h
    rw [← hgg]
    exact mem_blockOf_self _ _

theorem exists_grpOf (i : ↥X.groups) : ∃ b : ↥X.blocks, X.grpOf b = i := by
  obtain ⟨b, hb⟩ := i.2
  exact ⟨b, Subtype.ext hb⟩

/-- §9.6, step 2.  The coloring of the link `V₁ × V₂`: the `c` of
`Babai.case_9_6_1_step2`. -/
def linkColor (x : ↥X.Pt₁) (b : ↥X.blocks) : ℕ := X.c {(x : ↥s)} (b : Set ↥s)

/-- §9.6.  Every edge of the color of `X₂` whose components are the blocks has both ends
in `V₂`.  This is what lets the blocks be computed in the whole vertex set. -/
theorem edgesInside_blockColor :
    EdgesInside X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks} (blockColor X.c₂) := by
  obtain ⟨-, ⟨u₁, v₁, huv₁⟩, -⟩ := blockColor_spec X.exists_disconnected_c₂
  have h0 : X.vc (X.vtxOfBlk u₁) (X.vtxOfBlk v₁) = blockColor X.c₂ := huv₁
  intro u v huv
  constructor
  · exact ((X.vc_diag_eq_iff u (X.vtxOfBlk u₁)).1 (X.vc_tail_eq (huv.trans h0.symm))).2 u₁.2
  · exact ((X.vc_diag_eq_iff v (X.vtxOfBlk v₁)).1 (X.vc_head_eq (huv.trans h0.symm))).2 v₁.2

/-- §9.6.  The block `Bᵢ` of a block, computed in the whole vertex set, is the group of
that block. -/
theorem weakComponent_vtxOfBlk (b : ↥X.blocks) :
    (colorDigraph X.vc (blockColor X.c₂)).weakComponent (X.vtxOfBlk b)
      = X.vtxOfBlk '' X.group b := by
  have hres : ∀ u v : ↥X.blocks,
      restrictColor X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks}
          (X.blkEquiv u) (X.blkEquiv v) = X.c₂ u v := fun _ _ => rfl
  have hbc : blockColor (restrictColor X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks})
      = blockColor X.c₂ := blockColor_map X.blkEquiv hres
  have hbo : blockOf (restrictColor X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks})
      (X.blkEquiv b) = X.blkEquiv '' X.group b := blockOf_map X.blkEquiv hres b
  have key : (colorDigraph (restrictColor X.vc {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks})
      (blockColor X.c₂)).weakComponent (X.blkEquiv b) = X.blkEquiv '' X.group b := by
    rwa [blockOf, hbc] at hbo
  have himg := image_weakComponent_restrictColor (k := blockColor X.c₂)
    X.edgesInside_blockColor (X.blkEquiv b)
  rw [key] at himg
  have hcoe : ((X.blkEquiv b : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks}) : ↥X.vtxSet)
      = X.vtxOfBlk b := rfl
  rw [hcoe] at himg
  rw [← himg, Set.image_image]
  rfl

/-- §9.6, step 2.  The out-degree of a point of `V₁` in the contracted graph is the number
of blocks `Bᵢ` that it meets in the color `h`: the quantity of Lemma 3.4.8. -/
theorem degA_contractedBip (a : ↥X.Pt₁) :
    {C ∈ (colorDigraph X.vc (blockColor X.c₂)).weakComponents |
        ∃ z ∈ C, X.vc (X.vtxOfPt a) z = X.hColor}.ncard
      = (contractedBip X.linkColor X.hColor X.grpOf).degA a := by
  have hlink : X.HasLinkColor X.hColor := X.isOtherColor_hColor.2
  have hset : {C ∈ (colorDigraph X.vc (blockColor X.c₂)).weakComponents |
      ∃ z ∈ C, X.vc (X.vtxOfPt a) z = X.hColor}
      = (fun i : ↥X.groups => X.vtxOfBlk '' (i : Set ↥X.blocks)) ''
        {i : ↥X.groups | (a, i) ∈ (contractedBip X.linkColor X.hColor X.grpOf).E} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨p, rfl⟩, z, hz, hcol⟩
      have hzb : (z : Set ↥s) ∈ X.blocks := X.mem_blocks_of_link hlink hcol
      have hzeq : X.vtxOfBlk ⟨(z : Set ↥s), hzb⟩ = z := Subtype.ext rfl
      refine ⟨X.grpOf ⟨(z : Set ↥s), hzb⟩, ⟨⟨(z : Set ↥s), hzb⟩, rfl, ?_⟩, ?_⟩
      · show X.c {(a : ↥s)} (z : Set ↥s) = X.hColor
        rw [← hzeq] at hcol
        exact hcol
      · show X.vtxOfBlk '' X.group ⟨(z : Set ↥s), hzb⟩ = _
        rw [← X.weakComponent_vtxOfBlk, hzeq]
        exact ((colorDigraph X.vc (blockColor X.c₂)).weakComponent_eq_of_mem hz)
    · rintro ⟨i, ⟨b, hb, hcol⟩, rfl⟩
      have hi : (i : Set ↥X.blocks) = X.group b := (congrArg Subtype.val hb).symm
      refine ⟨⟨X.vtxOfBlk b, ?_⟩, X.vtxOfBlk b, ⟨b, ?_, rfl⟩, hcol⟩
      · rw [X.weakComponent_vtxOfBlk, hi]
      · rw [hi]; exact mem_blockOf_self _ _
  rw [hset, Set.ncard_image_of_injective]
  · rfl
  · intro i i' hii
    exact Subtype.ext ((Set.image_injective.2 X.vtxOfBlk_injective) hii)

/-- §9.6, step 2.  The in-degree of a vertex of the contracted graph is the number of
points of `V₁` that meet the corresponding block `Bᵢ` in the color `h`: the quantity of
Lemma 3.4.6. -/
theorem degB_contractedBip (b : ↥X.blocks) :
    {u : ↥X.vtxSet | ∃ z ∈ (colorDigraph X.vc (blockColor X.c₂)).weakComponent
        (X.vtxOfBlk b), X.vc u z = X.hColor}.ncard
      = (contractedBip X.linkColor X.hColor X.grpOf).degB (X.grpOf b) := by
  have hlink : X.HasLinkColor X.hColor := X.isOtherColor_hColor.2
  have hset : {u : ↥X.vtxSet | ∃ z ∈ (colorDigraph X.vc (blockColor X.c₂)).weakComponent
      (X.vtxOfBlk b), X.vc u z = X.hColor}
      = X.vtxOfPt '' {x : ↥X.Pt₁ |
        (x, X.grpOf b) ∈ (contractedBip X.linkColor X.hColor X.grpOf).E} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨z, hz, hcol⟩
      rw [X.weakComponent_vtxOfBlk] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨x, hx⟩ := X.exists_vtxOfPt (X.notMem_blocks_of_link hlink y.2 hcol)
      refine ⟨x, ⟨y, X.mem_group_iff_grpOf_eq.1 hy, ?_⟩, hx⟩
      show X.c {(x : ↥s)} (y : Set ↥s) = X.hColor
      rw [← hx] at hcol
      exact hcol
    · rintro ⟨x, ⟨y, hy, hcol⟩, rfl⟩
      refine ⟨X.vtxOfBlk y, ?_, hcol⟩
      rw [X.weakComponent_vtxOfBlk]
      exact ⟨y, X.mem_group_iff_grpOf_eq.2 hy, rfl⟩
  rw [hset, Set.ncard_image_of_injective _ X.vtxOfPt_injective]
  rfl

/-- Lemma 9.6.2.  *"`Y` is semiregular by Cor. 3.4.9."*  (Version 2.5, line 4220.)  The
two degrees of the contracted graph are the two quantities of Lemmas 3.4.6 and 3.4.8, and
(N8) says that both are constant. -/
theorem contractedBip_isSemiregular :
    (contractedBip X.linkColor X.hColor X.grpOf).IsSemiregular := by
  classical
  letI : Fintype ↥X.vtxSet := Fintype.ofFinite _
  letI : DecidableEq ↥X.vtxSet := Classical.decEq _
  obtain ⟨x₀, hx₀, C₀, hC₀, hcol₀⟩ := X.isOtherColor_hColor.2
  obtain ⟨-, ⟨u₁, v₁, huv₁⟩, -⟩ := blockColor_spec X.exists_disconnected_c₂
  have hblkdiag : ∀ b : ↥X.blocks, X.vc (X.vtxOfBlk b) (X.vtxOfBlk b)
      = X.vc (X.vtxOfBlk ⟨C₀, hC₀⟩) (X.vtxOfBlk ⟨C₀, hC₀⟩) :=
    fun b => (X.vc_diag_eq_iff _ _).2 (iff_of_true b.2 hC₀)
  have hptdiag : ∀ x : ↥X.Pt₁, X.vc (X.vtxOfPt x) (X.vtxOfPt x)
      = X.vc (X.vtxOfPt ⟨x₀, hx₀⟩) (X.vtxOfPt ⟨x₀, hx₀⟩) :=
    fun x => (X.vc_diag_eq_iff _ _).2
      (iff_of_false (X.vtxOfPt_notMem_blocks x) (X.vtxOfPt_notMem_blocks _))
  have hd : X.vc (X.vtxOfPt ⟨x₀, hx₀⟩) (X.vtxOfPt ⟨x₀, hx₀⟩)
      ≠ X.vc (X.vtxOfBlk ⟨C₀, hC₀⟩) (X.vtxOfBlk ⟨C₀, hC₀⟩) := by
    intro hc
    exact X.vtxOfPt_notMem_blocks ⟨x₀, hx₀⟩ (((X.vc_diag_eq_iff _ _).1 hc).2 hC₀)
  obtain ⟨hdegA, hdegB⟩ := natColor_contraction_degrees X.vc_isCoherentColoring hd
    (hblkdiag u₁) (hblkdiag v₁) (huv₁ : X.vc (X.vtxOfBlk u₁) (X.vtxOfBlk v₁) = blockColor X.c₂)
    (rfl) (hblkdiag ⟨C₀, hC₀⟩) (hcol₀ : X.vc (X.vtxOfPt ⟨x₀, hx₀⟩)
      (X.vtxOfBlk ⟨C₀, hC₀⟩) = X.hColor)
  constructor
  · refine ⟨(contractedBip X.linkColor X.hColor X.grpOf).degA ⟨x₀, hx₀⟩, fun a => ?_⟩
    have h := hdegA (X.vtxOfPt a) (X.vtxOfPt ⟨x₀, hx₀⟩) (hptdiag a) rfl
    rw [X.degA_contractedBip a, X.degA_contractedBip ⟨x₀, hx₀⟩] at h
    exact h
  · refine ⟨(contractedBip X.linkColor X.hColor X.grpOf).degB (X.grpOf ⟨C₀, hC₀⟩),
      fun i => ?_⟩
    obtain ⟨b, rfl⟩ := X.exists_grpOf i
    have h := hdegB (X.vtxOfBlk b) (X.vtxOfBlk ⟨C₀, hC₀⟩) (hblkdiag b) rfl
    rw [X.degB_contractedBip b, X.degB_contractedBip ⟨C₀, hC₀⟩] at h
    exact h

/-- §9.6.  *"Let `d_j` be the in-degree of `y ∈ V₂` in color `j ∈ J`.  (`d_j` does not
depend on `y` because of the homogeneity of `X₂`.)"*  (Version 2.5, line 4199.)  This is
(N7): the blocks are the points of one vertex-color class of the configuration, so they
all have the same in-degree in every color. -/
theorem inDeg₁_const (k : ℕ) (B B' : ↥X.blocks) :
    {x : ↥s | X.part₁ x ∧ X.c {x} (B : Set ↥s) = k}.ncard
      = {x : ↥s | X.part₁ x ∧ X.c {x} (B' : Set ↥s) = k}.ncard := by
  classical
  by_cases hk : X.HasLinkColor k
  · rw [← X.ncard_pt₁_setOf (fun x => X.c {x} (B : Set ↥s) = k),
      ← X.ncard_pt₁_setOf (fun x => X.c {x} (B' : Set ↥s) = k)]
    have h1 := X.inNbhd_vtx_eq hk B
    have h2 := X.inNbhd_vtx_eq hk B'
    have hdiag : X.vc (X.vtxOfBlk B) (X.vtxOfBlk B) = X.vc (X.vtxOfBlk B') (X.vtxOfBlk B') :=
      (X.vc_diag_eq_iff _ _).2 (iff_of_true B.2 B'.2)
    have hN7 := natColor_inDeg_eq_of_diag_eq' X.vc_isCoherentColoring hdiag k
    rw [h1, h2, Set.ncard_image_of_injective _ X.vtxOfPt_injective,
      Set.ncard_image_of_injective _ X.vtxOfPt_injective] at hN7
    exact hN7
  · have hempty : ∀ C : ↥X.blocks, {x : ↥s | X.part₁ x ∧ X.c {x} (C : Set ↥s) = k} = ∅ := by
      intro C
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro x ⟨h1, h2⟩
      exact hk ⟨x, h1, (C : Set ↥s), C.2, h2⟩
    rw [hempty B, hempty B']

theorem grpOf_eq_of_mem {i : ↥X.groups} {b : ↥X.blocks} (hb : b ∈ (i : Set ↥X.blocks)) :
    X.grpOf b = i := by
  obtain ⟨b₀, hb₀⟩ := X.exists_grpOf i
  have hi : (i : Set ↥X.blocks) = X.group b₀ := (congrArg Subtype.val hb₀).symm
  rw [hi] at hb
  rw [X.mem_group_iff_grpOf_eq.1 hb, hb₀]

/-- §9.6, step 2(i).  The blocks of the graph `Zᵢ` are the blocks of the group `Bᵢ`. -/
noncomputable def groupBlkEquiv (i : ↥X.groups) :
    {y : ↥X.blocks // X.grpOf y = i} ≃ ↥(Subtype.val '' (i : Set ↥X.blocks)) :=
  Equiv.ofBijective
    (fun y => ⟨((y.1 : ↥X.blocks) : Set ↥s), ⟨y.1, by
      have hi : (i : Set ↥X.blocks) = X.group y.1 := (congrArg Subtype.val y.2).symm
      rw [hi]; exact mem_blockOf_self _ _, rfl⟩⟩)
    ⟨fun y y' h => Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(Subtype.val '' (i : Set ↥X.blocks)) => (z : Set ↥s)) h)),
     by
      rintro ⟨C, b, hb, rfl⟩
      exact ⟨⟨b, X.grpOf_eq_of_mem hb⟩, rfl⟩⟩

/-- §9.6, step 2(ii).  The union of the blocks of a group. -/
def grpUnion (i : ↥X.groups) : Set ↥s := ⋃ C ∈ (i : Set ↥X.blocks), (C : Set ↥s)

theorem groupUnion_eq_grpUnion (b : ↥X.blocks) : X.groupUnion b = X.grpUnion (X.grpOf b) := rfl

/-- Two groups with the same union are equal: the blocks are nonempty and pairwise
disjoint. -/
theorem grpUnion_injective : Function.Injective X.grpUnion := by
  have hsub : ∀ i i' : ↥X.groups, X.grpUnion i = X.grpUnion i' →
      (i : Set ↥X.blocks) ⊆ (i' : Set ↥X.blocks) := by
    intro i i' hU C hC
    obtain ⟨z, hz⟩ := X.blocks_nonempty _ C.2
    have hzU : z ∈ X.grpUnion i := Set.mem_biUnion hC hz
    rw [hU] at hzU
    simp only [grpUnion, Set.mem_iUnion, exists_prop] at hzU
    obtain ⟨C', hC', hzC'⟩ := hzU
    have : (C : Set ↥s) = (C' : Set ↥s) := by
      by_contra hne
      exact (Set.disjoint_left.1 (X.blocks_disjoint _ C.2 _ C'.2 hne)) hz hzC'
    rwa [Subtype.ext this]
  intro i i' hU
  exact Subtype.ext (Set.Subset.antisymm (hsub i i' hU) (hsub i' i hU.symm))

/-- §9.6, step 2(ii).  The vertices of the contracted graph `Y` are the groups. -/
noncomputable def grpUnionEquiv : ↥X.groups ≃ ↥(Set.range X.groupUnion) :=
  Equiv.ofBijective (fun i => ⟨X.grpUnion i, by
      obtain ⟨b, rfl⟩ := X.exists_grpOf i
      exact ⟨b, rfl⟩⟩)
    ⟨fun i i' h => X.grpUnion_injective (congrArg Subtype.val h),
     by rintro ⟨A, b, rfl⟩; exact ⟨X.grpOf b, rfl⟩⟩

/-- §9.6, step 2(i).  The graph `Zᵢ` of a group, as an object of `Babai.VColBlkGraphs`,
has the same symmetry defect on `V₁` as the bipartite graph of
`Babai.case_9_6_1_step2`: the two differ only in how the second part is indexed. -/
theorem defect₁_blkZ [Fintype ↥s] [DecidableEq ↥s] [Fintype ↥X.Pt₁] [DecidableEq ↥X.Pt₁]
    [Fintype ↥X.blocks] [DecidableEq ↥X.blocks] [Fintype ↥X.groups] [DecidableEq ↥X.groups]
    (i : ↥X.groups) :
    (X.blkZ (i : Set ↥X.blocks)).defect₁
      = (blockGraph X.linkColor X.jColor X.grpOf i).defect₁ := by
  rw [← VColBipBlk.defect₁_toBip _ (fun _ _ => rfl)]
  refine BipGraph.defect₁_congr (Equiv.setCongr rfl) (X.groupBlkEquiv i) ?_
  intro a y
  constructor
  · rintro ⟨-, -, hcol⟩
    exact hcol
  · intro hcol
    refine ⟨⟨y.1, ?_, rfl⟩, a.2, hcol⟩
    have hi : (i : Set ↥X.blocks) = X.group y.1 := (congrArg Subtype.val y.2).symm
    rw [hi]; exact mem_blockOf_self _ _

/-- §9.6, step 2(ii).  The contracted graph, as an object of `Babai.VColBlkGraphs`, has
the same symmetry defect on `V₁` as `Babai.contractedBip`. -/
theorem defect₁_blkContr [Fintype ↥s] [DecidableEq ↥s] [Fintype ↥X.Pt₁] [DecidableEq ↥X.Pt₁]
    [Fintype ↥X.blocks] [DecidableEq ↥X.blocks] [Fintype ↥X.groups] [DecidableEq ↥X.groups] :
    X.blkContr.defect₁ = (contractedBip X.linkColor X.hColor X.grpOf).defect₁ := by
  rw [← VColBipBlk.defect₁_toBip _ (fun _ _ => rfl)]
  refine BipGraph.defect₁_congr (Equiv.setCongr rfl) X.grpUnionEquiv ?_
  intro a i
  constructor
  · rintro ⟨-, -, D, hD, hsub, hcol⟩
    obtain ⟨z, hz⟩ := X.blocks_nonempty _ hD
    have hzU : z ∈ X.grpUnion i := hsub hz
    simp only [grpUnion, Set.mem_iUnion, exists_prop] at hzU
    obtain ⟨C, hC, hzC⟩ := hzU
    have hDC : D = (C : Set ↥s) := by
      by_contra hne
      exact (Set.disjoint_left.1 (X.blocks_disjoint _ hD _ C.2 hne)) hz hzC
    refine ⟨C, X.grpOf_eq_of_mem hC, ?_⟩
    show X.c {((a : ↥X.Pt₁) : ↥s)} ((C : ↥X.blocks) : Set ↥s) = X.hColor
    rw [← hDC]
    exact hcol
  · rintro ⟨y, hy, hcol⟩
    have hi : (i : Set ↥X.blocks) = X.group y := (congrArg Subtype.val hy).symm
    have hyi : y ∈ (i : Set ↥X.blocks) := by rw [hi]; exact mem_blockOf_self _ _
    refine ⟨?_, a.2, (y : Set ↥s), y.2, ?_, hcol⟩
    · obtain ⟨b, rfl⟩ := X.exists_grpOf i
      exact ⟨b, rfl⟩
    · intro z hz
      exact Set.mem_biUnion hyi hz

end BlkImprimitiveObj

/-- Both candidates of step 2 carry the constant point coloring: the paper's `Zᵢ` and `Y`
are plain bipartite graphs. -/
theorem step2Cands_f_const {s : Set Ω} {X : BlkImprimitiveObj s} {W : VColBipBlk ↥s ℕ}
    (hW : W ∈ X.step2Cands) (x y : ↥s) : W.f x = W.f y := by
  rcases hW with ⟨G, -, rfl⟩ | rfl <;> rfl

/-- §9.6, step 2.  **One of the two branches keeps the symmetry defect.**  This is
`Babai.case_9_6_1_step2` read for the candidates of step 2.

*The proof* is that lemma after a translation, in three pieces:

* the identification of `Babai.case_9_6_1_step2`'s data with the data here: `A` is `V₁`,
  `B` is `Babai.BlkImprimitiveObj.blocks` (a vertex of `V₂` is a block), `ι` is the set of
  groups and `blocks : B → ι` is `Babai.BlkImprimitiveObj.grpOf`; the graphs then match by
  `Babai.VColBipBlk.defect₁_toBip` (the object and its bipartite graph have the same
  symmetry defect on `V₁`, because `f` and `g` are constant) together with
  `Babai.BipGraph.defect₁_congr` (the second parts are in bijection: the blocks of a group
  versus the group itself, `Babai.BlkImprimitiveObj.groupBlkEquiv`, and the unions of the
  groups versus the groups, `Babai.BlkImprimitiveObj.grpUnionEquiv`); this is
  `Babai.BlkImprimitiveObj.defect₁_blkZ` and `Babai.BlkImprimitiveObj.defect₁_blkContr`;
* the hypothesis `hdj` of `Babai.case_9_6_1_step2`, *"for some `j ∈ J` we have
  `d_j > n₁/2`"*, which is the branch condition `¬ ImprimitiveSplits`
  (`Babai.BlkImprimitiveObj.isBigColor_jColor`) together with
  `Babai.natColor_inDeg_eq_of_diag_eq'` (N7), which is what makes `d_j` independent of the
  vertex of `V₂` (`Babai.BlkImprimitiveObj.inDeg₁_const`);
* the hypothesis `hEne`, *"`R_h` is not empty"*, which holds by the choice of
  `Babai.BlkImprimitiveObj.hColor` as a color that occurs on the link
  (`Babai.BlkImprimitiveObj.isOtherColor_hColor`), and the hypothesis `hsr`, the
  semiregularity of the contraction (Cor. 3.4.9).  The latter is
  `Babai.BlkImprimitiveObj.contractedBip_isSemiregular`, which is
  `Babai.natColor_contraction_degrees` (N8) read on the vertex set "points of `V₁` plus
  blocks" through `Babai.image_weakComponent_restrictColor`, which says that the blocks
  may be computed inside `V₂` or in the whole vertex set with the same result. -/
theorem step2Cands_exists_defect {s : Set Ω} (X : BlkImprimitiveObj s)
    (hsplit : ¬ ImprimitiveSplits X) :
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    ∃ Y ∈ X.step2Cands, 1 / 2 ≤ Y.defect₁ := by
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  letI : Fintype ↥X.Pt₁ := Fintype.ofFinite _
  letI : DecidableEq ↥X.Pt₁ := Classical.decEq _
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  letI : DecidableEq ↥X.blocks := Classical.decEq _
  letI : Fintype ↥X.groups := Fintype.ofFinite _
  letI : DecidableEq ↥X.groups := Classical.decEq _
  obtain ⟨B₀, hB₀⟩ := X.blocks_nonempty'
  -- *"`d_j` does not depend on `y`"*: the in-degree in the color `k` is the same at every
  -- block (N7)
  have hd : ∀ (k : ℕ) (y : ↥X.blocks),
      {x : ↥X.Pt₁ | X.linkColor x y = k}.ncard
        = {x : ↥X.Pt₁ | X.linkColor x ⟨B₀, hB₀⟩ = k}.ncard := by
    intro k y
    show {x : ↥X.Pt₁ | X.c {(x : ↥s)} (y : Set ↥s) = k}.ncard
      = {x : ↥X.Pt₁ | X.c {(x : ↥s)} B₀ = k}.ncard
    rw [X.ncard_pt₁_setOf (fun x => X.c {x} (y : Set ↥s) = k),
      X.ncard_pt₁_setOf (fun x => X.c {x} (B₀ : Set ↥s) = k)]
    exact X.inDeg₁_const k y ⟨B₀, hB₀⟩
  -- *"for some `j ∈ J` we have `d_j > n₁/2`"*: the branch condition of step 1 fails
  obtain ⟨Bj, hBj, hlt⟩ := X.isBigColor_jColor hsplit
  have hdj : Fintype.card ↥X.Pt₁
      < 2 * {x : ↥X.Pt₁ | X.linkColor x ⟨B₀, hB₀⟩ = X.jColor}.ncard := by
    have hc1 : Fintype.card ↥X.Pt₁ = {x : ↥s | X.part₁ x}.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      rfl
    have hc2 : {x : ↥X.Pt₁ | X.linkColor x ⟨B₀, hB₀⟩ = X.jColor}.ncard
        = {x : ↥s | X.part₁ x ∧ X.c {x} Bj = X.jColor}.ncard := by
      show {x : ↥X.Pt₁ | X.c {(x : ↥s)} B₀ = X.jColor}.ncard
        = {x : ↥s | X.part₁ x ∧ X.c {x} Bj = X.jColor}.ncard
      rw [X.ncard_pt₁_setOf (fun x => X.c {x} B₀ = X.jColor)]
      exact X.inDeg₁_const X.jColor ⟨B₀, hB₀⟩ ⟨Bj, hBj⟩
    rw [hc1, hc2]
    exact hlt
  -- *"`R_h` is not empty"*
  obtain ⟨x₀, hx₀, C₀, hC₀, hcol₀⟩ := X.isOtherColor_hColor.2
  have hEne : (contractedBip X.linkColor X.hColor X.grpOf).E ≠ ∅ := by
    intro hE
    have hmem : ((⟨x₀, hx₀⟩ : ↥X.Pt₁), X.grpOf ⟨C₀, hC₀⟩)
        ∈ (contractedBip X.linkColor X.hColor X.grpOf).E := ⟨⟨C₀, hC₀⟩, rfl, hcol₀⟩
    rw [hE] at hmem
    exact hmem
  rcases case_9_6_1_step2 X.linkColor X.jColor X.hColor X.isOtherColor_hColor.1
      (fun k => {x : ↥X.Pt₁ | X.linkColor x ⟨B₀, hB₀⟩ = k}.ncard) hd hdj X.grpOf hEne
      X.contractedBip_isSemiregular with ⟨i, hi⟩ | ⟨h1, -⟩
  · refine ⟨X.blkZ (i : Set ↥X.blocks), Or.inl ⟨(i : Set ↥X.blocks), i.2, rfl⟩, ?_⟩
    rw [X.defect₁_blkZ i]
    exact hi
  · refine ⟨X.blkContr, Or.inr rfl, ?_⟩
    rw [X.defect₁_blkContr]
    exact h1

/-- §9.6, step 2.  **The outcome is at most half the size of the input.**  Branch 2(i)
returns a group `Bᵢ`, of size `n₂/m ≤ n₂/2`, and branch 2(ii) returns the `m ≤ n₂/2`
groups.

Both bounds are Prop. 3.4.4 for the block system of `X₂`
(`Babai.blockOf_equipartition`, `Babai.blockOf_nontrivial`, `Babai.exists_blockOf_ne`):
there are at least two groups and every group has at least two blocks.  These facts are
stated for a `Babai.PartitionStructure` on the vertex set of `X₂`, which is the field
`imprimitive₂` of `Babai.IsImprimitiveCase`; they are carried to
`Babai.BlkImprimitiveObj.c₂`, the coloring read on the blocks, along the bijection "a
vertex of `V₂` is a block" (`Babai.BlkImprimitiveObj.blkEquiv`), using
`Babai.blockColor_map` and `Babai.blockOf_map`.  The result is
`Babai.BlkImprimitiveObj.groups_isEquipartition`,
`Babai.BlkImprimitiveObj.group_nontrivial` and `Babai.BlkImprimitiveObj.exists_group_ne`,
and the counting is `Babai.two_mul_ncard_le_of_isEquipartition` and
`Babai.two_mul_ncard_parts_le`. -/
theorem step2Cands_two_mul_numBlocks_le {s : Set Ω} (X : BlkImprimitiveObj s)
    (Y : VColBipBlk ↥s ℕ) (hY : Y ∈ X.step2Cands) : 2 * Y.numBlocks ≤ X.blocks.ncard := by
  classical
  have hcard : Nat.card ↥X.blocks = X.blocks.ncard := Nat.card_coe_set_eq _
  rcases hY with ⟨G, hG, rfl⟩ | rfl
  · -- branch 2(i): the outcome is one group `Bᵢ`, of size `n₂/m ≤ n₂/2`
    obtain ⟨A, hA, A', hA', hne⟩ := X.exists_group_ne
    obtain ⟨G', hG'mem, hG'ne⟩ : ∃ G' ∈ X.groups, G ≠ G' := by
      rcases eq_or_ne A G with rfl | h
      · exact ⟨A', hA', hne⟩
      · exact ⟨A, hA, fun hc => h hc.symm⟩
    have hbound := two_mul_ncard_le_of_isEquipartition X.groups_isEquipartition hG
      hG'mem hG'ne
    rw [hcard] at hbound
    have hnb : (X.blkZ G).numBlocks = G.ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    rw [hnb]
    exact hbound
  · -- branch 2(ii): the outcome is the `m ≤ n₂/2` groups
    have hle : (Set.range X.groupUnion).ncard ≤ X.groups.ncard := by
      have himg : Set.range X.groupUnion
          = (fun G : Set ↥X.blocks => ⋃ C ∈ G, (C : Set ↥s)) '' X.groups := by
        rw [BlkImprimitiveObj.groups, ← Set.range_comp]
        rfl
      rw [himg]
      exact Set.ncard_image_le (Set.toFinite _)
    have hbound : 2 * X.groups.ncard ≤ X.blocks.ncard := by
      have := two_mul_ncard_parts_le (T := ↥X.blocks) (P := X.groups)
        X.groups_isEquipartition.pairwiseDisjoint (by rintro A ⟨B, rfl⟩; exact X.group_nontrivial B)
      rwa [hcard] at this
    have hnb : X.blkContr.numBlocks = (Set.range X.groupUnion).ncard := rfl
    rw [hnb]
    omega

/-- §9.6, step 2.  **The multiplicative cost is at most `n₂`.**  The family has `m + 1`
members — one per group, and the contraction — and `m + 1 ≤ n₂` because every group has at
least two blocks, so `2m ≤ n₂`, and `n₂ ≥ 2`.

Same ingredients as `Babai.step2Cands_two_mul_numBlocks_le`: Prop. 3.4.4 for
`Babai.BlkImprimitiveObj.c₂`. -/
theorem step2Cands_ncard_le {s : Set Ω} (X : BlkImprimitiveObj s) :
    X.step2Cands.ncard ≤ X.blocks.ncard := by
  classical
  have hcard : Nat.card ↥X.blocks = X.blocks.ncard := Nat.card_coe_set_eq _
  have hm2 : 1 < X.groups.ncard := by
    rw [Set.one_lt_ncard (Set.toFinite _)]
    obtain ⟨A, hA, A', hA', hne⟩ := X.exists_group_ne
    exact ⟨A, hA, A', hA', hne⟩
  have hbound : 2 * X.groups.ncard ≤ X.blocks.ncard := by
    have := two_mul_ncard_parts_le (T := ↥X.blocks) (P := X.groups)
      X.groups_isEquipartition.pairwiseDisjoint (by rintro A ⟨B, rfl⟩; exact X.group_nontrivial B)
    rwa [hcard] at this
  have hstep : X.step2Cands.ncard ≤ (X.blkZ '' X.groups).ncard + ({X.blkContr} : Set _).ncard :=
    Set.ncard_union_le _ _
  have h1 : (X.blkZ '' X.groups).ncard ≤ X.groups.ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h2 : ({X.blkContr} : Set (VColBipBlk ↥s ℕ)).ncard = 1 := Set.ncard_singleton _
  omega

/-! ### Step 2 under a morphism: the transport of the whole construction

Every ingredient of step 2 is built from the coloring and the two parts alone, so a
morphism of `Babai.BlkImprimitiveCases` carries each of them to its counterpart.  These
lemmas are condition (ii) of Definition 6.0.1 for the construction, one piece at a time;
`Babai.step2Out_equivariant` puts them together. -/

section Transport

variable {s t : Set Ω} {X : BlkImprimitiveObj s} {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}

/-- A morphism carries the blocks of the input bijectively to the blocks of the target. -/
def blkEquivOfIso (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) : ↥X.blocks ≃ ↥Y.blocks where
  toFun B := ⟨φ '' (B : Set ↥s), (hφ.2.1 (B : Set ↥s)).2 B.2⟩
  invFun B := ⟨φ.symm '' (B : Set ↥t), by
    have h := hφ.2.1 (φ.symm '' (B : Set ↥t))
    rw [Equiv.image_symm_image] at h
    exact h.1 B.2⟩
  left_inv B := Subtype.ext (Equiv.symm_image_image φ _)
  right_inv B := Subtype.ext (Equiv.image_symm_image φ _)

@[simp] theorem blkEquivOfIso_coe (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (B : ↥X.blocks) :
    ((blkEquivOfIso hφ B : ↥Y.blocks) : Set ↥t) = φ '' (B : Set ↥s) := rfl

/-- The coloring of `X₂` is carried to the coloring of `X₂` of the target. -/
theorem c₂_blkEquivOfIso (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (u v : ↥X.blocks) :
    Y.c₂ (blkEquivOfIso hφ u) (blkEquivOfIso hφ v) = X.c₂ u v := hφ.2.2 _ _

/-- The groups are carried to the groups: `Babai.blockOf_map` for the coloring of `X₂`. -/
theorem group_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (B : ↥X.blocks) :
    Y.group (blkEquivOfIso hφ B) = (blkEquivOfIso hφ) '' X.group B :=
  blockOf_map (blkEquivOfIso hφ) (c₂_blkEquivOfIso hφ) B

theorem groups_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    Y.groups = (fun G : Set ↥X.blocks => (blkEquivOfIso hφ) '' G) '' X.groups := by
  ext G
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨X.group ((blkEquivOfIso hφ).symm u), ⟨_, rfl⟩, ?_⟩
    show (blkEquivOfIso hφ) '' X.group ((blkEquivOfIso hφ).symm u) = Y.group u
    rw [← group_map hφ ((blkEquivOfIso hφ).symm u), Equiv.apply_symm_apply]
  · rintro ⟨G', ⟨B, rfl⟩, rfl⟩
    exact ⟨blkEquivOfIso hφ B, group_map hφ B⟩

/-- A morphism carries the first part onto the first part. -/
theorem part₁_image (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    {y : ↥t | Y.part₁ y} = φ '' {x : ↥s | X.part₁ x} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    exact ⟨φ.symm y, (hφ.1 (φ.symm y)).1 (by simpa using hy), by simp⟩
  · rintro ⟨x, hx, rfl⟩; exact (hφ.1 x).2 hx

/-- The color of a link edge is preserved. -/
theorem c_singleton (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (x : ↥s) (B : Set ↥s) :
    Y.c {φ x} (φ '' B) = X.c {x} B := by
  have h := hφ.2.2 {x} B
  rwa [Set.image_singleton] at h

/-- The color classes of the link at a block are carried to the color classes at the image
block. -/
theorem colorClass_image (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (B : Set ↥s) (k : ℕ) :
    {y : ↥t | Y.part₁ y ∧ Y.c {y} (φ '' B) = k}
      = φ '' {x : ↥s | X.part₁ x ∧ X.c {x} B = k} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨φ.symm y, ⟨(hφ.1 (φ.symm y)).1 (by simpa using h1), ?_⟩, by simp⟩
    have h3 := c_singleton hφ (φ.symm y) B
    rw [Equiv.apply_symm_apply] at h3
    rw [← h3]; exact h2
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(hφ.1 x).2 h1, by rw [c_singleton hφ x B]; exact h2⟩

/-- The branch condition of step 2, *"for some `j ∈ J` we have `d_j > n₁/2`"*, is an
isomorphism invariant, color label by color label. -/
theorem isBigColor_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (k : ℕ) :
    Y.IsBigColor k ↔ X.IsBigColor k := by
  constructor
  · rintro ⟨B, hB, hlt⟩
    refine ⟨φ.symm '' B, ?_, ?_⟩
    · have h := hφ.2.1 (φ.symm '' B)
      rw [Equiv.image_symm_image] at h
      exact h.1 hB
    · have hB' : B = φ '' (φ.symm '' B) := (Equiv.image_symm_image φ B).symm
      rw [hB', colorClass_image hφ, Set.ncard_image_of_injective _ φ.injective] at hlt
      rwa [part₁_image hφ, Set.ncard_image_of_injective _ φ.injective] at hlt
  · rintro ⟨B, hB, hlt⟩
    refine ⟨φ '' B, (hφ.2.1 B).2 hB, ?_⟩
    rw [colorClass_image hφ, Set.ncard_image_of_injective _ φ.injective,
      part₁_image hφ, Set.ncard_image_of_injective _ φ.injective]
    exact hlt

/-- The canonical color `j` of step 2 is an isomorphism invariant. -/
theorem jColor_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) : Y.jColor = X.jColor := by
  classical
  by_cases h : ∃ k, X.IsBigColor k
  · have h' : ∃ k, Y.IsBigColor k := by
      obtain ⟨k, hk⟩ := h; exact ⟨k, (isBigColor_map hφ k).2 hk⟩
    rw [BlkImprimitiveObj.jColor, BlkImprimitiveObj.jColor, dif_pos h, dif_pos h']
    exact le_antisymm (Nat.find_le ((isBigColor_map hφ _).2 (Nat.find_spec h)))
      (Nat.find_le ((isBigColor_map hφ _).1 (Nat.find_spec h')))
  · have h' : ¬ ∃ k, Y.IsBigColor k := by
      rintro ⟨k, hk⟩; exact h ⟨k, (isBigColor_map hφ k).1 hk⟩
    rw [BlkImprimitiveObj.jColor, BlkImprimitiveObj.jColor, dif_neg h, dif_neg h']

/-- The colors of the link other than `j` are the same color labels for the two objects. -/
theorem isOtherColor_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (k : ℕ) :
    Y.IsOtherColor k ↔ X.IsOtherColor k := by
  unfold BlkImprimitiveObj.IsOtherColor
  rw [jColor_map hφ]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨y, hy, B, hB, hcol⟩
    refine ⟨φ.symm y, (hφ.1 (φ.symm y)).1 (by simpa using hy), φ.symm '' B, ?_, ?_⟩
    · have h := hφ.2.1 (φ.symm '' B)
      rw [Equiv.image_symm_image] at h
      exact h.1 hB
    · have h3 := c_singleton hφ (φ.symm y) (φ.symm '' B)
      rw [Equiv.apply_symm_apply, Equiv.image_symm_image] at h3
      rw [← h3]; exact hcol
  · rintro ⟨x, hx, B, hB, hcol⟩
    exact ⟨φ x, (hφ.1 x).2 hx, φ '' B, (hφ.2.1 B).2 hB, by rw [c_singleton hφ x B]; exact hcol⟩

/-- The canonical color `h` of step 2(ii) is an isomorphism invariant. -/
theorem hColor_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) : Y.hColor = X.hColor := by
  classical
  by_cases h : ∃ k, X.IsOtherColor k
  · have h' : ∃ k, Y.IsOtherColor k := by
      obtain ⟨k, hk⟩ := h; exact ⟨k, (isOtherColor_map hφ k).2 hk⟩
    rw [BlkImprimitiveObj.hColor, BlkImprimitiveObj.hColor, dif_pos h, dif_pos h']
    exact le_antisymm (Nat.find_le ((isOtherColor_map hφ _).2 (Nat.find_spec h)))
      (Nat.find_le ((isOtherColor_map hφ _).1 (Nat.find_spec h')))
  · have h' : ¬ ∃ k, Y.IsOtherColor k := by
      rintro ⟨k, hk⟩; exact h ⟨k, (isOtherColor_map hφ k).1 hk⟩
    rw [BlkImprimitiveObj.hColor, BlkImprimitiveObj.hColor, dif_neg h, dif_neg h']

/-- The blocks of a group, as sets of points, are carried to the blocks of the image
group. -/
theorem val_image_group_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y)
    (G : Set ↥X.blocks) :
    (Subtype.val '' ((blkEquivOfIso hφ) '' G) : Set (Set ↥t))
      = (fun A : Set ↥s => φ '' A) '' (Subtype.val '' G) := by
  ext A
  simp only [Set.mem_image]
  constructor
  · rintro ⟨u, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨(C : Set ↥s), ⟨C, hC, rfl⟩, rfl⟩
  · rintro ⟨A₀, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨blkEquivOfIso hφ C, ⟨C, hC, rfl⟩, rfl⟩

/-- Step 2(i).  The graph `Zᵢ` of a group is carried to the graph `Zᵢ` of the image
group. -/
theorem blkZ_isIsoTo (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (G : Set ↥X.blocks) :
    (X.blkZ G).IsIsoTo (Y.blkZ ((blkEquivOfIso hφ) '' G)) φ where
  part₁ x := hφ.1 x
  blocks B := by
    show φ '' B ∈ (Subtype.val '' ((blkEquivOfIso hφ) '' G) : Set (Set ↥t))
      ↔ B ∈ (Subtype.val '' G : Set (Set ↥s))
    rw [val_image_group_map hφ G]
    exact (Set.image_injective.2 φ.injective).mem_set_image
  edges x B := by
    show (φ '' B ∈ (Subtype.val '' ((blkEquivOfIso hφ) '' G) : Set (Set ↥t))
        ∧ Y.part₁ (φ x) ∧ Y.c {φ x} (φ '' B) = Y.jColor)
      ↔ (B ∈ (Subtype.val '' G : Set (Set ↥s))
        ∧ X.part₁ x ∧ X.c {x} B = X.jColor)
    rw [val_image_group_map hφ G, c_singleton hφ x B, jColor_map hφ]
    refine and_congr ?_ (and_congr (hφ.1 x) Iff.rfl)
    exact (Set.image_injective.2 φ.injective).mem_set_image
  color₁ _ := rfl
  color₂ _ := rfl
  hint _ _ := rfl

/-- Step 2(ii).  The union of a group is carried to the union of the image group. -/
theorem groupUnion_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) (B : ↥X.blocks) :
    Y.groupUnion (blkEquivOfIso hφ B) = φ '' X.groupUnion B := by
  ext z
  simp only [BlkImprimitiveObj.groupUnion, Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨C, hC, hz⟩
    rw [group_map hφ B] at hC
    obtain ⟨D, hD, rfl⟩ := hC
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, ⟨D, hD, hw⟩, rfl⟩
  · rintro ⟨w, ⟨D, hD, hw⟩, rfl⟩
    refine ⟨blkEquivOfIso hφ D, ?_, ⟨w, hw, rfl⟩⟩
    rw [group_map hφ B]
    exact ⟨D, hD, rfl⟩

theorem range_groupUnion_map (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    Set.range Y.groupUnion = (fun A : Set ↥s => φ '' A) '' Set.range X.groupUnion := by
  ext A
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨X.groupUnion ((blkEquivOfIso hφ).symm u), ⟨_, rfl⟩, ?_⟩
    rw [← groupUnion_map hφ, Equiv.apply_symm_apply]
  · rintro ⟨A₀, ⟨B, rfl⟩, rfl⟩
    exact ⟨blkEquivOfIso hφ B, groupUnion_map hφ B⟩

/-- Step 2(ii).  The contracted graph is carried to the contracted graph. -/
theorem blkContr_isIsoTo (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    X.blkContr.IsIsoTo Y.blkContr φ where
  part₁ x := hφ.1 x
  blocks B := by
    show φ '' B ∈ Set.range Y.groupUnion ↔ B ∈ Set.range X.groupUnion
    rw [range_groupUnion_map hφ]
    exact (Set.image_injective.2 φ.injective).mem_set_image
  edges x B := by
    show (φ '' B ∈ Set.range Y.groupUnion ∧ Y.part₁ (φ x)
        ∧ ∃ D ∈ Y.blocks, D ⊆ φ '' B ∧ Y.c {φ x} D = Y.hColor)
      ↔ (B ∈ Set.range X.groupUnion ∧ X.part₁ x
        ∧ ∃ D ∈ X.blocks, D ⊆ B ∧ X.c {x} D = X.hColor)
    have hb : φ '' B ∈ Set.range Y.groupUnion ↔ B ∈ Set.range X.groupUnion := by
      rw [range_groupUnion_map hφ]
      exact (Set.image_injective.2 φ.injective).mem_set_image
    refine and_congr hb (and_congr (hφ.1 x) ?_)
    constructor
    · rintro ⟨D, hD, hsub, hcol⟩
      refine ⟨φ.symm '' D, ?_, ?_, ?_⟩
      · have h := hφ.2.1 (φ.symm '' D)
        rw [Equiv.image_symm_image] at h
        exact h.1 hD
      · have : φ '' (φ.symm '' D) ⊆ φ '' B := by rw [Equiv.image_symm_image]; exact hsub
        exact (Set.image_subset_image_iff φ.injective).1 this
      · have h3 := c_singleton hφ x (φ.symm '' D)
        rw [Equiv.image_symm_image] at h3
        rw [← h3, ← hColor_map hφ]; exact hcol
    · rintro ⟨D, hD, hsub, hcol⟩
      refine ⟨φ '' D, (hφ.2.1 D).2 hD, Set.image_mono hsub, ?_⟩
      rw [c_singleton hφ x D, hColor_map hφ]; exact hcol
  color₁ _ := rfl
  color₂ _ := rfl
  hint _ _ := rfl

end Transport

/-- The branch test is preserved by the same block map as the graphs. -/
theorem hasGoodBlock_map {s t : Set Ω} {X : BlkImprimitiveObj s}
    {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}
    (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    Y.hasGoodBlock ↔ X.hasGoodBlock := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  have hd (G : Set ↥X.blocks) :
      (Y.blkZ ((blkEquivOfIso hφ) '' G)).defect₁ = (X.blkZ G).defect₁ :=
    VColBipBlk.defect₁_of_isoTo (blkZ_isIsoTo hφ G)
      (fun _ _ => rfl) (fun _ _ => rfl)
  change (∃ G ∈ Y.groups, 1 / 2 ≤ (Y.blkZ G).defect₁) ↔ _
  rw [groups_map hφ]
  constructor
  · rintro ⟨_, ⟨G, hG, rfl⟩, hdef⟩
    exact ⟨G, hG, (hd G) ▸ hdef⟩
  · rintro ⟨G, hG, hdef⟩
    exact ⟨_, ⟨G, hG, rfl⟩, (hd G).symm ▸ hdef⟩

/-- Section 9.6, step 2: both the test and the selected family transport
along isomorphisms of the input coloring. -/
theorem step2Out_equivariant {s t : Set Ω} {X : BlkImprimitiveObj s}
    {Y : BlkImprimitiveObj t} {φ : ↥s ≃ ↥t}
    (hφ : φ ∈ (BlkImprimitiveCases Ω).Iso X Y) :
    ∀ Z ∈ X.step2Out, ∃ Z' ∈ Y.step2Out,
      φ ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Iso Z Z' := by
  classical
  letI : Fintype ↥s := Fintype.ofFinite _
  letI : DecidableEq ↥s := Classical.decEq _
  letI : Fintype ↥t := Fintype.ofFinite _
  letI : DecidableEq ↥t := Classical.decEq _
  rintro _ ⟨W, ⟨hW, hdef, hbranch⟩, rfl⟩
  have hZ (G : Set ↥X.blocks) (hG : G ∈ X.groups)
      (hdef : 1 / 2 ≤ (X.blkZ G).defect₁) :
      ∃ Z' ∈ Y.step2Out,
        φ ∈ (Cat.sub (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))).Iso
          ⟨⟨s, subset_rfl⟩, Sum.inr (X.blkZ G)⟩ Z' := by
    have hG' : (blkEquivOfIso hφ) '' G ∈ Y.groups := by
      rw [groups_map hφ]; exact ⟨G, hG, rfl⟩
    have hz : Y.blkZ ((blkEquivOfIso hφ) '' G) ∈ Y.blkZ '' Y.groups :=
      ⟨_, hG', rfl⟩
    refine ⟨_, ⟨_, ⟨Or.inl hz, ?_, fun _ => hz⟩, rfl⟩,
      ⟨φ, fun _ => rfl, blkZ_isIsoTo hφ G⟩⟩
    rw [VColBipBlk.defect₁_of_isoTo (blkZ_isIsoTo hφ G)
      (fun _ _ => rfl) (fun _ _ => rfl)]
    exact hdef
  by_cases hg : X.hasGoodBlock
  · obtain ⟨G, hG, rfl⟩ := hbranch hg
    exact hZ G hG hdef
  · rcases hW with ⟨G, hG, rfl⟩ | rfl
    · exact hZ G hG hdef
    · refine ⟨_, ⟨Y.blkContr, ⟨Or.inr rfl, ?_, ?_⟩, rfl⟩,
        ⟨φ, fun _ => rfl, blkContr_isIsoTo hφ⟩⟩
      · rw [VColBipBlk.defect₁_of_isoTo (blkContr_isIsoTo hφ)
          (fun _ _ => rfl) (fun _ _ => rfl)]
        exact hdef
      · intro hy
        exact (hg ((hasGoodBlock_map hφ).1 hy)).elim

/-- Lemma 9.6.1, **the branch of step 2 of Procedure ImprimitiveCase**.  *"else (: for some
`j ∈ J` we have `d_j > n₁/2` :) For `i = 1, …, m` let `Zᵢ = X(V₁, Bᵢ; R_j)`.  (i) if
`(∃i)(the symmetry defect of `V₁` in `Zᵢ` is `≥ 1/2`) then `Y ← Zᵢ` … (ii) … Let
`Y = (V₁, [m]; R_h)` … return `Y`."*  (Version 2.5, lines 4207-4216.)

The block restrictions are tested first. If any passes, the family contains
exactly the passing restrictions. Otherwise it contains the contraction.
The existence theorem `step2Cands_exists_defect` proves that this last graph
passes the defect test. Each selected graph has at most half as many blocks,
by `step2Cands_two_mul_numBlocks_le`. The number of choices is bounded by
`step2Cands_ncard_le`. -/
theorem lemma_9_6_1_step2 :
    FindsAtMultCost ((BlkImprimitiveCases Ω).full fun _ X => ¬ ImprimitiveSplits X)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkImprimitiveCases.numBlocks ⟨X.car, X.obj.1⟩)
      (fun X Z => IsBlkImprimitiveOutcome (BlkImprimitiveCases.V₁ ⟨X.car, X.obj.1⟩)
        (BlkImprimitiveCases.numBlocks ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => X.obj.1.step2Out)
    (fun X => ?_) (fun X => ?_) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · -- non-empty: one of the two branches keeps the symmetry defect
    by_cases hg : X.obj.1.hasGoodBlock
    · obtain ⟨G, hG, hdef⟩ := hg
      exact ⟨_, ⟨X.obj.1.blkZ G,
        ⟨Or.inl ⟨G, hG, rfl⟩, hdef, fun _ => ⟨G, hG, rfl⟩⟩, rfl⟩⟩
    · obtain ⟨Y, hY, hdef⟩ := step2Cands_exists_defect X.obj.1 X.obj.2
      exact ⟨_, ⟨Y, ⟨hY, hdef, fun h => (hg h).elim⟩, rfl⟩⟩
  · exact Set.Finite.image _ ((step2Cands_finite X.obj.1).subset (fun _ h => h.1))
  · -- cost: `m + 1 ≤ n₂`
    refine le_trans (Set.ncard_image_le
      ((step2Cands_finite X.obj.1).subset (fun _ h => h.1))) ?_
    exact le_trans (Set.ncard_le_ncard (fun _ h => h.1) (step2Cands_finite X.obj.1))
      (step2Cands_ncard_le X.obj.1)
  · exact step2Out_equivariant (X := X.obj.1) (Y := Y.obj.1) hf Z hZ
  · obtain ⟨Y, ⟨hY, hdef, _⟩, rfl⟩ := hZ
    refine ⟨?_, step2Cands_two_mul_numBlocks_le X.obj.1 Y hY, hdef⟩
    rw [step2Cands_V₁ hY]
    rfl

/-- Lemma 9.6.1.  *"Under the assumptions stated in 'Case' above, we can either return a
canonical colored `1/2`-partition of `V₁` at a multiplicative cost of `< n₂`, or return, at
only additive polynomial cost (no multiplicative cost) a canonical bipartite graph
`Y = (V₁, W₂; F)` such that `|W₂| ≤ |V₂|/2` such that the symmetry defect of `V₁` in `Y` is
`≥ 1/2`."*  (Version 2.5, lines 4190-4193.)

The statement is in the wider category of §9.4-§9.8: a vertex of `V₂` is a block, so `n₂`
is the number of blocks, and the graph `Y` returned in the second branch is an object of
`Babai.VColBlkGraphs`.  This is what lets step 2(ii) return the contracted graph; see the
entry for Lemma 9.6.1 in the corrected paper.

**The cost bound is `≤ n₂`, not `< n₂` and not `0`.**  The lemma's wording does not match
its own Procedure ImprimitiveCase: step 1 *individualizes* a point of `V₂`, which costs
exactly `n₂`, and step 2(i) says *"This involves choosing `i` at a multiplicative cost of
`m`"* with `2 ≤ m ≤ n₂/2`, so the second branch is not free either.  The three branches of
the procedure cost `n₂` (step 1), `m ≤ n₂/2` (step 2(i)) and `1` (step 2(ii)), so `n₂`
bounds them all; `FindsAtMultCost` takes one cost function of the input object, and the
branch is not a function of the object alone (it depends on the color `j` and the block
system chosen inside the procedure), so the single bound `n₂` is what is stated.  See the
entry for Lemma 9.6.1 in the corrected paper.

The additive polynomial cost is a running-time claim and is pending.

The proof is the case distinction of Procedure ImprimitiveCase on its branch condition
`Babai.ImprimitiveSplits` (*"if `(∀j ∈ J)(d_j ≤ n₁/2)`"*): the two branches are
`Babai.lemma_9_6_1_step1` and `Babai.lemma_9_6_1_step2`, both proved. -/
theorem lemma_9_6_1 :
    FindsAtMultCost (BlkImprimitiveCases Ω)
      (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))
      (fun X => BlkImprimitiveCases.numBlocks X)
      (fun X Z => IsBlkImprimitiveOutcome (BlkImprimitiveCases.V₁ X)
        (BlkImprimitiveCases.numBlocks X) Z) := by
  refine (FindsAtMultCost.cases
    (C := BlkImprimitiveCases Ω)
    (P := fun _ X => ImprimitiveSplits X)
    (costp := fun Z => BlkImprimitiveCases.numBlocks Z)
    (costn := fun Z => BlkImprimitiveCases.numBlocks Z)
    (Good := fun Z W => IsBlkImprimitiveOutcome (BlkImprimitiveCases.V₁ Z)
      (BlkImprimitiveCases.numBlocks Z) W)
    (fun h hx => imprimitiveSplits_congr h hx) lemma_9_6_1_step1 lemma_9_6_1_step2).mono
    (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

end Babai
