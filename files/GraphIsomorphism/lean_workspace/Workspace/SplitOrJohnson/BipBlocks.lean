/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.4-9.8: the wider category in which the recursion of Procedure Bipartite
Split-or-Johnson runs, in which the second part of a bipartite graph is a family of blocks.
-/
import Workspace.SplitOrJohnson.Defs
import Workspace.Functors.Induction

/-!
# §9.4-§9.8: bipartite graphs whose second part is a family of blocks

Version 2.5, lines 4183-4232 of `babai-gi-source/quasi25.txt` (§9.6) and the procedure of
§9.4.

## Why this category

Procedure ImprimitiveCase, step 2(ii) (§9.6) returns the contracted graph

> *"Let `h ∈ J`, `h ≠ j`.  Let `Y = (V₁, [m]; R_h)` where `(x,i) ∈ R_h` if
> `(∃y ∈ Bᵢ)((x,y) ∈ R_h)`."*

The second part of `Y` is the set of blocks `B₁, …, B_m` of a block system of `V₂`.  In our
encoding every object of a `Babai.Cat Ω` lives on a subset of the one ambient type `Ω`, and
`Babai.FindsAtMultCost` asks the object found to be *canonically embedded*, so the second
part would have to be a subset of `V₂` of size `m` chosen canonically.  A block has no
canonical element, so that subset does not exist (see the entry for Lemma 9.6.1 in
the corrected paper).

The repair keeps every printed statement and widens the category instead.  An object of
`Babai.VColBipBlk` is a bipartite graph whose

* first part `V₁` is a set of **points** of the ambient set, as before;
* second part is a family `blocks` of pairwise disjoint nonempty sets of points, all
  disjoint from `V₁`: **a vertex of `V₂` is a block**;
* edges join a point of `V₁` to a block;
* vertex colors are `f` on the points and `g` on the blocks;
* a **hint** `h` colors the ordered pairs of blocks.

The number of vertices of the second part is the number of blocks (`numBlocks`), which is
the `n₂` that §9.5 measures.  An honest vertex-colored bipartite graph is the case of
singleton blocks (`Babai.VColBip.toBlk`), and contracting a block system of `V₂` replaces
the blocks by their unions (`Babai.VColBipBlk.contract`), so the construction of step 2(ii)
stays inside the category.

The outputs of Theorem 9.2.2 all live on `V₁`, which consists of points in both categories,
so the outcome category `Babai.SplitOutcomes` is unchanged.

## The block coloring, and why it is normalized

`g` is a function on **all** subsets, and a morphism preserves it on all subsets.  On the
blocks it is the paper's coloring of the vertices of `V₂`; on the other subsets it is a
padding that no construction reads.  Carrying `g` as a total function is what makes the
underlying-set functor faithful (§6).

The padding is **normalized**: `g B = 0` for every `B` that is not a block (field
`g_off`).  Without this the padding would be free data, and it enters the automorphism
group, hence the symmetry defect of `V₁` (Def. 2.4.29), which is a hypothesis of
Theorem 9.2.2.  An arbitrary padding can destroy every pair of twins of `V₁`: the
transposition of two points `x, x'` of `V₁` moves a subset `B` that contains `x` and not
`x'`, and if `g` separates `B` from its image then the transposition is not an
automorphism, however similar `x` and `x'` are in the graph.  Then the hypothesis *"the
symmetry defect of `X` on `V₁` is at least `1 - α`"* would hold for the object while
failing for the bipartite graph that the paper's procedure sees.

With the normalization the automorphism group is the paper's one:
`Babai.VColBipBlk.isTwin_iff` says that two points of `V₁` are twins exactly when they
have the same color and the same set of neighboring blocks.

For the singleton blocks of `Babai.VColBip.toBlk` the color of a block `{y}` is the color
`f y` of the point `y`, and the padding is `0`.

## The hint on the pairs of blocks

§9.5 counts as major progress *"`X₂` moves from clique to UPCC while `n₂` does not
increase"*.  For that the object handed to the next turn has to carry the structure that
§9.7 found on `V₂` — in Case 3a1 the equipartition of the dominant color class, in
Case 3a2 the UPCC `Y` on the selected part.  The field `h` is that structure: a coloring
of the *ordered* pairs of blocks, padded by `0` on every pair one of whose members is not
a block (`h_off`), preserved by every morphism (`IsIsoTo.hint`), read by the initial
coloring of step 3 (`Babai.VColBipBlk.initColor`) and kept by the restrictions of steps 5,
7 and 8.  A contraction (`contract`) does not inherit it, and a plain bipartite graph
(`Babai.VColBip.toBlk`) does not carry it: `h = 0` there, and for `h = 0` the coloring of
step 3 has the same color classes as before the repair
(`Babai.VColBipBlk.initColor_eq_iff_of_hint_zero`), so **the printed Theorem 9.2.2 is the
case `h = 0`**.  See the entry on §9.7 Cases 3a1, 3a2 and 3b in the corrected paper.

Both directions `h A B` and `h B A` are read by step 3, so axiom (ii) of Def. 3.1.2 (the
coloring determines the color of the transposed pair) still holds.

## Numbering map

| Paper | Lean |
|---|---|
| bipartite graph whose second part is a set of blocks (§9.6, step 2(ii)) | `Babai.VColBipBlk` |
| `n₂ = |V₂|`, the number of blocks (§9.5) | `Babai.VColBipBlk.numBlocks` |
| symmetry defect of `V₁` (Def. 2.4.29) | `Babai.VColBipBlk.defect₁` |
| points as singleton blocks | `Babai.VColBip.toBlk` |
| contracting a block system of `V₂` (§9.6, step 2(ii)) | `Babai.VColBipBlk.contract` |
| the hint on the pairs of blocks (§9.5, §9.7) | `Babai.VColBipBlk.h` |
| Theorem 9.2.2 in the wider category | `Babai.theorem_9_2_2_blocks` (`Workspace/SplitOrJohnson/BipSplit.lean`) |
-/

namespace Babai

universe u v

/-! ### The objects -/

/-- §9.6, Procedure ImprimitiveCase step 2(ii).  A vertex-colored bipartite graph
`X = (V₁, V₂; E, f)` **whose second part is a family of blocks**: `V₁` is a set of points
of `s`, and a vertex of `V₂` is one of the pairwise disjoint nonempty sets `B ∈ blocks`,
each of them disjoint from `V₁`.  Edges join a point of `V₁` to a block.  `f` colors the
points, `g` colors the blocks and `h` colors the ordered pairs of blocks (see the module
docstring for the padding of `g` and of `h`, and for what the hint `h` is for).

The paper's bipartite graphs are the case of singleton blocks (`Babai.VColBip.toBlk`). -/
structure VColBipBlk (s : Type u) (κ : Type v) [Zero κ] where
  /-- The membership predicate of the first part `V₁`. -/
  part₁ : s → Prop
  /-- The second part: a vertex of `V₂` is one of these blocks. -/
  blocks : Set (Set s)
  /-- A block is nonempty. -/
  blocks_nonempty : ∀ B ∈ blocks, B.Nonempty
  /-- Two different blocks are disjoint. -/
  blocks_disjoint : ∀ B ∈ blocks, ∀ B' ∈ blocks, B ≠ B' → Disjoint B B'
  /-- A block consists of points outside the first part. -/
  blocks_off₁ : ∀ B ∈ blocks, ∀ x ∈ B, ¬ part₁ x
  /-- `E ⊆ V₁ × V₂`: an edge joins a point of the first part to a block. -/
  E : Set (s × Set s)
  /-- Every edge goes from a point of the first part to a block. -/
  E_sub : ∀ p ∈ E, part₁ p.1 ∧ p.2 ∈ blocks
  /-- The coloring of the points. -/
  f : s → κ
  /-- The coloring of the blocks. -/
  g : Set s → κ
  /-- Normalization of the padding: outside the blocks `g` is the fixed color `0`.  See
  the module docstring: without it the padding would enter the automorphism group and
  falsify the symmetry defect of `V₁`. -/
  g_off : ∀ B, B ∉ blocks → g B = 0
  /-- §9.5, §9.7.  **The hint**: a coloring of the *ordered pairs of blocks*.  It is the
  structure on `V₂` that a previous turn of the procedure found — in §9.7, Case 3a1 the
  equipartition of the dominant color class, in Case 3a2 the UPCC `Y` on the selected part
  — and that the recursion must not forget.  The initial coloring of step 3 reads it
  (`Babai.VColBipBlk.initColor`), and steps 5, 7 and 8 keep it.  Theorem 9.2.2 as printed
  is the case `h = 0`. -/
  h : Set s → Set s → κ
  /-- Normalization of the padding of the hint: a pair one of whose members is not a block
  gets the fixed color `0`.  The reason is the one behind `g_off`: free padding would
  enter the automorphism group and falsify the symmetry defect of `V₁`. -/
  h_off : ∀ A B, A ∉ blocks ∨ B ∉ blocks → h A B = 0

namespace VColBipBlk

variable {s t r : Type u} {κ : Type v} [Zero κ]

/-- Definition 2.3.4 for these graphs: a bijection of the point sets that carries the first
part to the first part, blocks to blocks, edges to edges, and both colorings to
themselves. -/
structure IsIsoTo (X : VColBipBlk s κ) (Y : VColBipBlk t κ) (φ : s ≃ t) : Prop where
  /-- The first part goes to the first part. -/
  part₁ : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x
  /-- Blocks go to blocks. -/
  blocks : ∀ B, φ '' B ∈ Y.blocks ↔ B ∈ X.blocks
  /-- Edges go to edges. -/
  edges : ∀ x B, (φ x, φ '' B) ∈ Y.E ↔ (x, B) ∈ X.E
  /-- The coloring of the points is preserved. -/
  color₁ : ∀ x, Y.f (φ x) = X.f x
  /-- The coloring of the blocks is preserved. -/
  color₂ : ∀ B, Y.g (φ '' B) = X.g B
  /-- The hint, the coloring of the ordered pairs of blocks, is preserved. -/
  hint : ∀ A B, Y.h (φ '' A) (φ '' B) = X.h A B

namespace IsIsoTo

theorem refl (X : VColBipBlk s κ) : X.IsIsoTo X (Equiv.refl s) where
  part₁ _ := Iff.rfl
  blocks B := by simp
  edges x B := by simp
  color₁ _ := rfl
  color₂ B := by simp
  hint A B := by simp

theorem symm {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) : Y.IsIsoTo X φ.symm where
  part₁ y := by simpa using (h.part₁ (φ.symm y)).symm
  blocks B := by
    -- `φ '' (φ.symm '' B) = B`
    have := (h.blocks (φ.symm '' B)).symm
    rwa [Equiv.image_symm_image] at this
  edges y B := by
    have := (h.edges (φ.symm y) (φ.symm '' B)).symm
    rwa [Equiv.apply_symm_apply, Equiv.image_symm_image] at this
  color₁ y := by simpa using (h.color₁ (φ.symm y)).symm
  color₂ B := by
    have := (h.color₂ (φ.symm '' B)).symm
    rwa [Equiv.image_symm_image] at this
  hint A B := by
    have := (h.hint (φ.symm '' A) (φ.symm '' B)).symm
    rwa [Equiv.image_symm_image, Equiv.image_symm_image] at this

theorem trans {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {Z : VColBipBlk r κ}
    {φ : s ≃ t} {ψ : t ≃ r} (h : X.IsIsoTo Y φ) (k : Y.IsIsoTo Z ψ) :
    X.IsIsoTo Z (φ.trans ψ) where
  part₁ x := (k.part₁ (φ x)).trans (h.part₁ x)
  blocks B := by
    have : (φ.trans ψ) '' B = ψ '' (φ '' B) := by
      rw [← Set.image_comp]; rfl
    rw [this]
    exact (k.blocks (φ '' B)).trans (h.blocks B)
  edges x B := by
    have : (φ.trans ψ) '' B = ψ '' (φ '' B) := by
      rw [← Set.image_comp]; rfl
    rw [this]
    exact (k.edges (φ x) (φ '' B)).trans (h.edges x B)
  color₁ x := (k.color₁ (φ x)).trans (h.color₁ x)
  color₂ B := by
    have : (φ.trans ψ) '' B = ψ '' (φ '' B) := by
      rw [← Set.image_comp]; rfl
    rw [this]
    exact (k.color₂ (φ '' B)).trans (h.color₂ B)
  hint A B := by
    have hA : (φ.trans ψ) '' A = ψ '' (φ '' A) := by rw [← Set.image_comp]; rfl
    have hB : (φ.trans ψ) '' B = ψ '' (φ '' B) := by rw [← Set.image_comp]; rfl
    rw [hA, hB]
    exact (k.hint (φ '' A) (φ '' B)).trans (h.hint A B)

end IsIsoTo

variable (X : VColBipBlk s κ)

/-- The first part `V₁`, a set of points. -/
def V₁ : Set s := {x | X.part₁ x}

/-- §9.5.  `n₂ = |V₂|`: the **number of blocks**.  This is what the measure of progress of
§9.5 counts, and what step 2 of Procedure ImprimitiveCase halves. -/
noncomputable def numBlocks : ℕ := X.blocks.ncard

/-- The set of points that lie in some block: the union of the second part. -/
def support₂ : Set s := ⋃₀ X.blocks

/-- Definition 2.3.4.  The automorphism group: the permutations of the point set that are
isomorphisms of `X` with itself. -/
def Aut : Subgroup (Equiv.Perm s) where
  carrier := {σ | X.IsIsoTo X σ}
  one_mem' := IsIsoTo.refl X
  mul_mem' {a b} ha hb := IsIsoTo.trans (φ := b) (ψ := a) hb ha
  inv_mem' {_a} ha := IsIsoTo.symm ha

end VColBipBlk

/-! ### Twins of `V₁`

The normalization `g_off` of the block coloring is exactly what makes the automorphism
group of an object see only the bipartite graph: two points of `V₁` are twins (Def. 2.3.9)
when, and only when, they have the same color and the same set of neighboring blocks. -/

namespace VColBipBlk

variable {s : Type u} {κ : Type v} [Zero κ] [DecidableEq s]

/-- A transposition of two points outside `B` fixes `B` setwise. -/
private theorem swap_image_eq_self {x x' : s} {B : Set s} (hx : x ∉ B) (hx' : x' ∉ B) :
    (Equiv.swap x x') '' B = B := by
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [Equiv.swap_apply_of_ne_of_ne (fun h => hx (by rw [← h]; exact hw))
      (fun h => hx' (by rw [← h]; exact hw))]
  · intro hz
    exact ⟨z, hz,
      Equiv.swap_apply_of_ne_of_ne (fun h => hx (by rw [← h]; exact hz))
        (fun h => hx' (by rw [← h]; exact hz))⟩

/-- A block contains no point of `V₁`, so the transposition of two points of `V₁` fixes
every block setwise. -/
theorem swap_image_block {X : VColBipBlk s κ} {x x' : s} (hx : X.part₁ x)
    (hx' : X.part₁ x') {B : Set s} (hB : B ∈ X.blocks) :
    (Equiv.swap x x') '' B = B :=
  swap_image_eq_self (fun h => X.blocks_off₁ B hB x h hx)
    (fun h => X.blocks_off₁ B hB x' h hx')

/-- The transposition of two points of `V₁` permutes the blocks (it fixes each of them). -/
theorem swap_image_mem_blocks_iff {X : VColBipBlk s κ} {x x' : s} (hx : X.part₁ x)
    (hx' : X.part₁ x') (B : Set s) :
    (Equiv.swap x x') '' B ∈ X.blocks ↔ B ∈ X.blocks := by
  constructor
  · intro h
    have h2 : (Equiv.swap x x') '' ((Equiv.swap x x') '' B) = (Equiv.swap x x') '' B :=
      swap_image_block hx hx' h
    have h3 : (Equiv.swap x x') '' ((Equiv.swap x x') '' B) = B := by
      rw [Set.image_image]; simp
    rw [h3] at h2
    exact h2 ▸ h
  · intro h
    rw [swap_image_block hx hx' h]; exact h

/-- §9.6.  **The twins of `V₁`.**  Two different points of the first part are twins
(Def. 2.3.9) exactly when they have the same color and the same set of neighboring blocks.

This is the reading of the symmetry defect of `V₁` (Def. 2.4.29) that Theorem 9.2.2 and
the procedure of §9.4 need: the defect of the object is the defect of the bipartite graph
whose second part is the set of blocks.  The normalization `g_off` is what makes the
"only if" direction give no more than this; see the module docstring. -/
theorem isTwin_iff (X : VColBipBlk s κ) {x x' : s} (hx : X.part₁ x) (hx' : X.part₁ x')
    (hne : x ≠ x') :
    IsTwin X.Aut x x' ↔
      X.f x = X.f x' ∧ ∀ B ∈ X.blocks, ((x, B) ∈ X.E ↔ (x', B) ∈ X.E) := by
  constructor
  · rintro ⟨-, hmem⟩
    have hiso : X.IsIsoTo X (Equiv.swap x x') := hmem
    refine ⟨?_, fun B hB => ?_⟩
    · have := hiso.color₁ x
      rw [Equiv.swap_apply_left] at this
      exact this.symm
    · have := hiso.edges x B
      rw [Equiv.swap_apply_left, swap_image_block hx hx' hB] at this
      exact this.symm
  · rintro ⟨hf, hnb⟩
    refine ⟨hne, ?_⟩
    show X.IsIsoTo X (Equiv.swap x x')
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      rcases eq_or_ne z x with rfl | h1
      · rw [Equiv.swap_apply_left]; exact iff_of_true hx' hx
      rcases eq_or_ne z x' with rfl | h2
      · rw [Equiv.swap_apply_right]; exact iff_of_true hx hx'
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · exact swap_image_mem_blocks_iff hx hx'
    · intro z B
      by_cases hB : B ∈ X.blocks
      · rw [swap_image_block hx hx' hB]
        rcases eq_or_ne z x with rfl | h1
        · rw [Equiv.swap_apply_left]; exact (hnb B hB).symm
        rcases eq_or_ne z x' with rfl | h2
        · rw [Equiv.swap_apply_right]; exact hnb B hB
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      · have hB' : (Equiv.swap x x') '' B ∉ X.blocks := by
          rw [swap_image_mem_blocks_iff hx hx']; exact hB
        exact iff_of_false (fun h => hB' (X.E_sub _ h).2) (fun h => hB (X.E_sub _ h).2)
    · intro z
      rcases eq_or_ne z x with rfl | h1
      · rw [Equiv.swap_apply_left]; exact hf.symm
      rcases eq_or_ne z x' with rfl | h2
      · rw [Equiv.swap_apply_right]; exact hf
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · intro B
      by_cases hB : B ∈ X.blocks
      · rw [swap_image_block hx hx' hB]
      · have hB' : (Equiv.swap x x') '' B ∉ X.blocks := by
          rw [swap_image_mem_blocks_iff hx hx']; exact hB
        rw [X.g_off _ hB', X.g_off _ hB]
    · -- the hint: the transposition of two points of `V₁` fixes every block, so it
      -- preserves `h` on the pairs of blocks; on the other pairs both sides are the
      -- padding color `0`.
      intro A B
      by_cases hA : A ∈ X.blocks
      · by_cases hB : B ∈ X.blocks
        · rw [swap_image_block hx hx' hA, swap_image_block hx hx' hB]
        · have hB' : (Equiv.swap x x') '' B ∉ X.blocks := by
            rw [swap_image_mem_blocks_iff hx hx']; exact hB
          rw [X.h_off _ _ (Or.inr hB'), X.h_off _ _ (Or.inr hB)]
      · have hA' : (Equiv.swap x x') '' A ∉ X.blocks := by
          rw [swap_image_mem_blocks_iff hx hx']; exact hA
        rw [X.h_off _ _ (Or.inl hA'), X.h_off _ _ (Or.inl hA)]

end VColBipBlk

namespace VColBipBlk

variable {s t r : Type u} {κ : Type v} [Zero κ] (X : VColBipBlk s κ)

open scoped Classical in
/-- Definition 2.4.29.  *"Let `Tᵢ` be a largest set of twins in `Ωᵢ`.  We say that `|Tᵢ|`
is the absolute symmetricity of `Ωᵢ` in `X`."*  The case `i = 1`: a largest set of twins
inside the first part.  Twins are twins with respect to `Aut(X)` (Def. 2.3.9). -/
noncomputable def symmetricity₁ [Fintype s] [DecidableEq s] : ℕ :=
  (Finset.univ.filter fun T : Finset s =>
    (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)).sup Finset.card

/-- Definition 2.4.29.  *"`1 - |Tᵢ|/|Ωᵢ|` is the relative symmetry defect of `Ωᵢ` in
`X`."*  The case `i = 1`.

Two points of `V₁` are twins exactly when they have the same color and the same set of
neighboring **blocks** (`Babai.VColBipBlk.isTwin_iff`), so this is the symmetry defect
read in the bipartite graph whose second part is the set of blocks, as the design of §9.6
requires. -/
noncomputable def defect₁ [Fintype s] [DecidableEq s] : ℚ :=
  1 - (X.symmetricity₁ : ℚ) / (X.V₁.ncard : ℚ)

/-- The hypotheses that Theorem 9.2.2 puts on its input for the threshold `α`, read in the
bipartite graph whose second part is the set of blocks: *"`|V₁| ≥ 2`"*, *"`|V₂| < α|V₁|`"*
(with `|V₂|` the number of blocks) and *"the symmetry defect of `X` on `V₁` is at least
`1 - α`"*. -/
def IsThm922Input [Fintype s] [DecidableEq s] (α : ℝ) : Prop :=
  2 ≤ X.V₁.ncard ∧ (X.numBlocks : ℝ) < α * X.V₁.ncard ∧ 1 - α ≤ (X.defect₁ : ℝ)

end VColBipBlk

/-! ### The categories -/

/-- §9.4-§9.8.  The category of vertex-colored bipartite graphs whose second part is a
family of blocks: morphisms are the bijections of the point set that carry the first part
to the first part, blocks to blocks, edges to edges and colors to colors. -/
def VColBlkGraphs (Ω : Type u) (κ : Type v) [Zero κ] : Cat.{u, max u v} Ω where
  Obj s := VColBipBlk ↥s κ
  Iso X Y := {φ | X.IsIsoTo Y φ}
  refl_mem X := VColBipBlk.IsIsoTo.refl X
  symm_mem hf := VColBipBlk.IsIsoTo.symm hf
  trans_mem hf hg := VColBipBlk.IsIsoTo.trans hf hg
  faithful {s X Y} hid := by
    obtain ⟨p, Bs, hn, hd, ho, E, hE, f, g, hgoff, hh, hhoff⟩ := X
    obtain ⟨p', Bs', hn', hd', ho', E', hE', f', g', hgoff', hh', hhoff'⟩ := Y
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hid
    simp only [Equiv.coe_refl, Set.image_id', id_eq] at k1 k2 k3 k4 k5 k6
    have hp : p' = p := funext fun x => propext (k1 x)
    subst hp
    have hB : Bs' = Bs := Set.ext k2
    subst hB
    have hEE : E' = E := Set.ext fun q => by simpa using k3 q.1 q.2
    subst hEE
    have hf : f' = f := funext k4
    subst hf
    have hg : g' = g := funext k5
    subst hg
    have hhh : hh' = hh := funext fun A => funext fun B => k6 A B
    subst hhh
    rfl

/-- §9.2, Theorem 9.2.2, in the wider category: the objects carry their threshold
parameter `α`, exactly as `Babai.VColBipThr` does (see its docstring for why the parameter
is data of the object). -/
def VColBlkThr (Ω : Type) : Cat.{0, 0} Ω where
  Obj s := VColBipBlk ↥s ℕ × ℝ
  Iso X Y := {φ | X.2 = Y.2 ∧ φ ∈ (VColBlkGraphs Ω ℕ).Iso X.1 Y.1}
  refl_mem X := ⟨rfl, (VColBlkGraphs Ω ℕ).refl_mem X.1⟩
  symm_mem hf := ⟨hf.1.symm, (VColBlkGraphs Ω ℕ).symm_mem hf.2⟩
  trans_mem hf hg := ⟨hf.1.trans hg.1, (VColBlkGraphs Ω ℕ).trans_mem hf.2 hg.2⟩
  faithful hid := Prod.ext ((VColBlkGraphs Ω ℕ).faithful hid.2) hid.1

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- §9.4-§9.8.  The admissible inputs of Theorem 9.2.2 in the wider category: a
vertex-colored bipartite graph whose second part is a family of blocks, together with its
threshold parameter `α`, subject to *"`2/3 ≤ α < 1`"*, *"`|V₁| ≥ 2`"*, *"`|V₂| < α|V₁|`"*
and *"the symmetry defect of `X` on `V₁` is at least `1 - α`"*, all read in the bipartite
graph whose second part is the set of blocks. -/
def BipBlockInputs (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  (VColBlkThr Ω).full fun s X =>
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    2 / 3 ≤ X.2 ∧ X.2 < 1 ∧ X.1.IsThm922Input X.2

/-- The threshold parameter `α` of an admissible input. -/
def BipBlockInputs.alpha (X : Pt (BipBlockInputs Ω)) : ℝ := X.obj.1.2

/-- The first part `V₁` of an admissible input, as a subset of the ambient type. -/
def BipBlockInputs.V₁ (X : Pt (BipBlockInputs Ω)) : Set Ω := Subtype.val '' X.obj.1.1.V₁

/-! ### Points as singleton blocks -/

namespace VColBip

variable {s : Type u}

open scoped Classical in
/-- The embedding of the paper's vertex-colored bipartite graphs into the wider category:
**a point of `V₂` becomes the singleton block containing it**.  The color of a block is
`sSup (f '' B)`, which on a block `{y}` is the color `f y` of the point `y`; outside the
blocks the coloring is the fixed color `0`, as the normalization `g_off` demands. -/
noncomputable def toBlk (X : VColBip s ℕ) : VColBipBlk s ℕ where
  part₁ := X.part₁
  blocks := {B | ∃ y, ¬ X.part₁ y ∧ B = {y}}
  blocks_nonempty := by rintro B ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  blocks_disjoint := by
    rintro B ⟨y, -, rfl⟩ B' ⟨y', -, rfl⟩ hne
    have : y ≠ y' := fun h => hne (by rw [h])
    simpa [Set.disjoint_singleton] using this
  blocks_off₁ := by rintro B ⟨y, hy, rfl⟩ x hx; rwa [hx]
  E := {p | ∃ y, ¬ X.part₁ y ∧ p.2 = {y} ∧ (p.1, y) ∈ X.E}
  E_sub := by
    rintro p ⟨y, hy, hp2, hpy⟩
    exact ⟨(X.E_sub _ hpy).1, ⟨y, hy, hp2⟩⟩
  f := X.f
  g := fun B => if ∃ y, ¬ X.part₁ y ∧ B = {y} then sSup (X.f '' B) else 0
  g_off := by
    intro B hB
    simp only [Set.mem_setOf_eq] at hB
    exact if_neg hB
  -- A bipartite graph carries no hint: `h = 0`.  This is the case of Theorem 9.2.2 as
  -- printed.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

variable (X : VColBip s ℕ)

/-- The color of a block of `toBlk X`. -/
theorem toBlk_g_of_mem {B : Set s} (hB : B ∈ X.toBlk.blocks) :
    X.toBlk.g B = sSup (X.f '' B) := by
  classical
  exact if_pos hB

@[simp] theorem toBlk_part₁ (x : s) : X.toBlk.part₁ x ↔ X.part₁ x := Iff.rfl

@[simp] theorem toBlk_V₁ : X.toBlk.V₁ = X.V₁ := rfl

/-- An edge of `toBlk X` from `x` to the singleton block `{y}` is exactly an edge of `X`
from `x` to `y`. -/
@[simp] theorem mem_toBlk_E_singleton (x y : s) :
    (x, ({y} : Set s)) ∈ X.toBlk.E ↔ (x, y) ∈ X.E := by
  constructor
  · rintro ⟨y', -, hy', hE⟩
    have : y' = y := by
      have : ({y} : Set s) = {y'} := hy'
      simpa [Set.singleton_eq_singleton_iff] using this.symm
    rwa [this] at hE
  · intro hE
    exact ⟨y, (X.E_sub _ hE).2, rfl, hE⟩

/-- The blocks of `toBlk X` are the singletons of the points of the second part. -/
theorem toBlk_blocks_eq : X.toBlk.blocks = (fun y => ({y} : Set s)) '' X.V₂ := by
  ext B
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

/-- `|V₂|` in the wider category (the number of blocks) is `|V₂|` in the paper's category
(the number of points of the second part). -/
theorem toBlk_numBlocks : X.toBlk.numBlocks = X.V₂.ncard := by
  rw [VColBipBlk.numBlocks, toBlk_blocks_eq]
  exact Set.ncard_image_of_injective _ fun a b h => by
    simpa [Set.singleton_eq_singleton_iff] using h

/-- A bijection that preserves the two parts carries the singleton blocks onto the
singleton blocks. -/
theorem toBlk_blocks_map {s t : Type u} {X : VColBip s ℕ} {Y : VColBip t ℕ} {φ : s ≃ t}
    (hp : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x) (B : Set s) :
    φ '' B ∈ Y.toBlk.blocks ↔ B ∈ X.toBlk.blocks := by
  constructor
  · rintro ⟨z, hz, hBz⟩
    refine ⟨φ.symm z, ?_, ?_⟩
    · rw [← hp (φ.symm z), Equiv.apply_symm_apply]; exact hz
    · have : φ.symm '' (φ '' B) = φ.symm '' ({z} : Set t) := by rw [hBz]
      rwa [Equiv.symm_image_image, Set.image_singleton] at this
  · rintro ⟨y, hy, rfl⟩
    refine ⟨φ y, ?_, ?_⟩
    · rw [hp y]; exact hy
    · rw [Set.image_singleton]

/-- An isomorphism of vertex-colored bipartite graphs is an isomorphism of the graphs with
singleton blocks.  This is what makes "points as singleton blocks" a functor. -/
theorem toBlk_isIsoTo {s t : Type u} {X : VColBip s ℕ} {Y : VColBip t ℕ} {φ : s ≃ t}
    (hp : ∀ x, Y.part₁ (φ x) ↔ X.part₁ x)
    (hE : ∀ x y, (φ x, φ y) ∈ Y.E ↔ (x, y) ∈ X.E)
    (hf : ∀ x, Y.f (φ x) = X.f x) :
    X.toBlk.IsIsoTo Y.toBlk φ where
  part₁ := hp
  blocks := toBlk_blocks_map hp
  edges x B := by
    constructor
    · rintro ⟨z, hz, hBz, hzE⟩
      have hBz' : φ '' B = ({z} : Set t) := hBz
      refine ⟨φ.symm z, ?_, ?_, ?_⟩
      · rw [← hp (φ.symm z), Equiv.apply_symm_apply]; exact hz
      · have : φ.symm '' (φ '' B) = φ.symm '' ({z} : Set t) := by rw [hBz']
        rwa [Equiv.symm_image_image, Set.image_singleton] at this
      · rw [← hE x (φ.symm z), Equiv.apply_symm_apply]; exact hzE
    · rintro ⟨y, hy, rfl, hyE⟩
      refine ⟨φ y, ?_, ?_, ?_⟩
      · rw [hp y]; exact hy
      · rw [Set.image_singleton]
      · rw [hE x y]; exact hyE
  color₁ := hf
  color₂ B := by
    by_cases hB : B ∈ X.toBlk.blocks
    · rw [toBlk_g_of_mem _ ((toBlk_blocks_map hp B).2 hB), toBlk_g_of_mem _ hB]
      have hcomp : Y.f ∘ (φ : s → t) = X.f := funext hf
      rw [← Set.image_comp, hcomp]
    · rw [Y.toBlk.g_off _ (fun h => hB ((toBlk_blocks_map hp B).1 h)), X.toBlk.g_off _ hB]
  hint _ _ := rfl

/-- The automorphism group does not change when the points of the second part are read as
singleton blocks.  So neither does the symmetry defect of `V₁`. -/
theorem toBlk_aut : X.toBlk.Aut = X.Aut := by
  ext σ
  constructor
  · rintro ⟨hp, -, hE, hf, -, -⟩
    refine ⟨hp, fun x y => ?_, hf⟩
    have h := hE x {y}
    rw [Set.image_singleton, mem_toBlk_E_singleton, mem_toBlk_E_singleton] at h
    exact h
  · rintro ⟨hp, hE, hf⟩
    exact toBlk_isIsoTo hp hE hf

theorem toBlk_symmetricity₁ [Fintype s] [DecidableEq s] :
    X.toBlk.symmetricity₁ = X.symmetricity₁ := by
  classical
  unfold VColBipBlk.symmetricity₁ VColBip.symmetricity₁
  rw [toBlk_aut]
  rfl

theorem toBlk_defect₁ [Fintype s] [DecidableEq s] : X.toBlk.defect₁ = X.defect₁ := by
  unfold VColBipBlk.defect₁ VColBip.defect₁
  rw [toBlk_symmetricity₁]
  rfl

/-- The hypotheses of Theorem 9.2.2 are the same in the two categories: the singleton-block
embedding keeps `V₁`, keeps `|V₂|` and keeps the symmetry defect of `V₁`. -/
theorem toBlk_isThm922Input [Fintype s] [DecidableEq s] (α : ℝ) :
    X.toBlk.IsThm922Input α ↔ X.IsThm922Input α := by
  unfold VColBipBlk.IsThm922Input VColBip.IsThm922Input
  rw [toBlk_numBlocks, toBlk_defect₁]
  exact Iff.rfl

end VColBip

/-! ### The wider category is not degenerate -/

/-- An object of the wider category that is **not** of the form `toBlk`: on three points,
with `V₁ = {0}` and one block `{1, 2}` of size two.  Every block of a `toBlk` is a
singleton, so this object is outside the image of the singleton-block embedding. -/
example : ∃ X : VColBipBlk (Fin 3) ℕ, ∀ Y : VColBip (Fin 3) ℕ, X ≠ Y.toBlk := by
  classical
  refine ⟨{ part₁ := fun x => x = 0
            blocks := {({1, 2} : Set (Fin 3))}
            blocks_nonempty := by rintro B rfl; exact ⟨1, by simp⟩
            blocks_disjoint := by rintro B rfl B' rfl h; exact absurd rfl h
            blocks_off₁ := by
              rintro B rfl x hx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
              rcases hx with rfl | rfl <;> decide
            E := ∅
            E_sub := by simp
            f := fun _ => 0
            g := fun _ => 0
            g_off := fun _ _ => rfl
            h := fun _ _ => 0
            h_off := fun _ _ _ => rfl }, ?_⟩
  intro Y hXY
  have hmem : ({1, 2} : Set (Fin 3)) ∈ Y.toBlk.blocks := by
    rw [← hXY]; exact rfl
  obtain ⟨y, -, hy⟩ := hmem
  have h1 : (1 : Fin 3) ∈ ({y} : Set (Fin 3)) := by rw [← hy]; simp
  have h2 : (2 : Fin 3) ∈ ({y} : Set (Fin 3)) := by rw [← hy]; simp
  simp only [Set.mem_singleton_iff] at h1 h2
  exact absurd (h1.trans h2.symm) (by decide)

/-! ### Contracting a block system of the second part -/

namespace VColBipBlk

variable {s t : Type u} {κ : Type v} [Zero κ]

/-- §9.6, Procedure ImprimitiveCase step 2(ii).  *"Let `Y = (V₁, [m]; R_h)` where
`(x,i) ∈ R_h` if `(∃y ∈ Bᵢ)((x,y) ∈ R_h)`."*

Contracting a block system of the second part: the new vertices of `V₂` are the members of
the family `𝒞`, each of them a union of old blocks, and `x` is joined to `C ∈ 𝒞` when `x`
is joined to some old block inside `C`.  The first part, its coloring and the edge rule are
unchanged; the new blocks get the coloring `gc`.

The operation stays inside the category, which is the point of the wider category: with the
paper's category the new vertex set would have to be a canonical transversal of the block
system, and there is none. -/
def contract (X : VColBipBlk s κ) (𝒞 : Set (Set s))
    (hne : ∀ C ∈ 𝒞, C.Nonempty)
    (hdisj : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint C C')
    (hoff : ∀ C ∈ 𝒞, ∀ x ∈ C, ¬ X.part₁ x)
    (gc : Set s → κ) (hgc : ∀ C, C ∉ 𝒞 → gc C = 0) : VColBipBlk s κ where
  part₁ := X.part₁
  blocks := 𝒞
  blocks_nonempty := hne
  blocks_disjoint := hdisj
  blocks_off₁ := hoff
  E := {p | p.2 ∈ 𝒞 ∧ ∃ B ∈ X.blocks, B ⊆ p.2 ∧ (p.1, B) ∈ X.E}
  E_sub := by
    rintro p ⟨hC, B, -, -, hE⟩
    exact ⟨(X.E_sub _ hE).1, hC⟩
  f := X.f
  g := gc
  g_off := hgc
  -- A contraction does not inherit the hint: the new vertices of `V₂` are unions of old
  -- blocks, and the paper's structure on the old blocks says nothing about them.
  h := fun _ _ => 0
  h_off := fun _ _ _ => rfl

@[simp] theorem contract_blocks (X : VColBipBlk s κ) (𝒞 : Set (Set s)) (hne hdisj hoff)
    (gc : Set s → κ) (hgc) : (X.contract 𝒞 hne hdisj hoff gc hgc).blocks = 𝒞 := rfl

@[simp] theorem contract_V₁ (X : VColBipBlk s κ) (𝒞 : Set (Set s)) (hne hdisj hoff)
    (gc : Set s → κ) (hgc) : (X.contract 𝒞 hne hdisj hoff gc hgc).V₁ = X.V₁ := rfl

/-- §9.6.  The contraction commutes with isomorphisms: if `φ` is an isomorphism `X → Y` and
carries the contracted family `𝒞` onto `𝒟` and the new coloring `gc` onto `gd`, then `φ` is
an isomorphism of the two contracted graphs.  This is the canonicity of step 2(ii). -/
theorem contract_isIsoTo {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}
    (h : X.IsIsoTo Y φ) {𝒞 : Set (Set s)} {𝒟 : Set (Set t)}
    (hne hdisj hoff) (kne kdisj koff) {gc : Set s → κ} {gd : Set t → κ} (hgc) (hgd)
    (hfam : ∀ C, φ '' C ∈ 𝒟 ↔ C ∈ 𝒞) (hg : ∀ C, gd (φ '' C) = gc C) :
    (X.contract 𝒞 hne hdisj hoff gc hgc).IsIsoTo (Y.contract 𝒟 kne kdisj koff gd hgd) φ where
  part₁ := h.part₁
  blocks := hfam
  edges x C := by
    show (φ '' C ∈ 𝒟 ∧ ∃ B' ∈ Y.blocks, B' ⊆ φ '' C ∧ (φ x, B') ∈ Y.E) ↔
      (C ∈ 𝒞 ∧ ∃ B ∈ X.blocks, B ⊆ C ∧ (x, B) ∈ X.E)
    refine and_congr (hfam C) ?_
    constructor
    · rintro ⟨B', hB', hsub, hE⟩
      refine ⟨φ.symm '' B', ?_, ?_, ?_⟩
      · rw [← h.blocks (φ.symm '' B'), Equiv.image_symm_image]; exact hB'
      · have : φ.symm '' B' ⊆ φ.symm '' (φ '' C) := Set.image_mono hsub
        rwa [Equiv.symm_image_image] at this
      · rw [← h.edges x (φ.symm '' B'), Equiv.image_symm_image]; exact hE
    · rintro ⟨B, hB, hsub, hE⟩
      exact ⟨φ '' B, (h.blocks B).2 hB, Set.image_mono hsub, (h.edges x B).2 hE⟩
  color₁ := h.color₁
  color₂ := hg
  hint _ _ := rfl

end VColBipBlk

end Babai
