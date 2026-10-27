/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Cases 3a1 and 3b: which two parts Procedure Reduce-Part2-by-Color is applied
to, when what is handed to it is a *coloring* of `V₂` with many color classes.
-/
import Workspace.SplitOrJohnson.Defs

/-!
# §9.7, Cases 3a1 and 3b: the canonical two-part split of a colored set

Version 2.5, lines 4281-4284 and 4295-4301; the original, `babai-gi.tex`, lines 3981-3992
(entries 36 and 37 of the corrected paper).

Case 3a1 reads, in the original's words:

> *"Apply Reduce-Part2-by-Color to the coloring.  If color class selected is greater than
> `3n₂/4`, this color class is equipartitioned; apply Procedure ImprimitiveCase (Sec. 9.6).
> In either case, significant progress: `n₂` reduced to `≤ 3n₂/4`."*

Procedure Reduce-Part2-by-Color (§9.3, version 2.5 lines 4076-4084) takes **two** parts,
each a union of color classes, and returns one of them.  The Design Lemma hands over a
coloring with any number of classes, so the two parts have to be chosen, and the choice
has to make the sentence true: *the selected part is either at most `3n₂/4`, or it is one
color class*.  The paper does not say which choice; this file makes one, canonically.

## The choice

Let `n` be the number of points and `col` the coloring.

* If some color class `C` has `n ≤ 4|C|`, take for the first part the class of the **least
  such color**.  Its complement is then at most `3n/4`.  The class itself is either at most
  `3n/4`, or it is the dominant class, which is the second alternative of the sentence
  above.
* Otherwise every class is smaller than `n/4`.  Take for the first part
  `{x | col x ≤ k}` for the **least `k`** with `n ≤ 4|{x | col x ≤ k}|`.  By minimality the
  points of color `< k` are fewer than `n/4`, and the class of color `k` is fewer than
  `n/4`, so the first part is smaller than `n/2 ≤ 3n/4`; and its complement is at most
  `3n/4` because the part is at least `n/4`.

Both rules name the part by **color values**, which a color-preserving bijection preserves,
so the choice is canonical (`Babai.colorSplit_image`).

## Numbering map

| Paper | Lean |
|---|---|
| the first of the two parts handed to Reduce-Part2-by-Color (Cases 3a1, 3b) | `Babai.colorSplit` |
| *"the selected part is `≤ 3n₂/4`, or it is one color class"* | `Babai.colorSplit_alternative`, `Babai.four_mul_ncard_compl_colorSplit_le` |
| the choice is canonical | `Babai.colorSplit_image` |
-/

namespace Babai

variable {α β : Type} [Fintype α] [Fintype β]

/-- The color class of `k`. -/
def colorClassOf (col : α → ℕ) (k : ℕ) : Set α := {x | col x = k}

/-- The union of the color classes of the colors `≤ k`. -/
def colorBelow (col : α → ℕ) (k : ℕ) : Set α := {x | col x ≤ k}

theorem exists_colorBelow (col : α → ℕ) :
    ∃ k, Fintype.card α ≤ 4 * (colorBelow col k).ncard := by
  classical
  refine ⟨Finset.univ.sup col, ?_⟩
  have huniv : colorBelow col (Finset.univ.sup col) = Set.univ :=
    Set.eq_univ_of_forall fun x =>
      (show col x ≤ Finset.univ.sup col from Finset.le_sup (Finset.mem_univ x))
  rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
  omega

open scoped Classical in
/-- §9.7, Cases 3a1 and 3b.  **The first of the two parts handed to Procedure
Reduce-Part2-by-Color.**  See the module docstring: the color class of the least color
whose class is at least a quarter of the points, if there is one; otherwise the union of
the classes of the colors up to the least `k` for which that union is at least a quarter of
the points. -/
noncomputable def colorSplit (col : α → ℕ) : Set α :=
  if h : ∃ k, Fintype.card α ≤ 4 * (colorClassOf col k).ncard then
    colorClassOf col (Nat.find h)
  else
    colorBelow col (Nat.find (exists_colorBelow col))

/-- The first part is at least a quarter of the points. -/
theorem card_le_four_mul_colorSplit (col : α → ℕ) :
    Fintype.card α ≤ 4 * (colorSplit col).ncard := by
  classical
  unfold colorSplit
  split_ifs with h
  · exact Nat.find_spec h
  · exact Nat.find_spec (exists_colorBelow col)

/-- The complement of the first part is at most three quarters of the points: this is the
progress made when Procedure Reduce-Part2-by-Color selects the *second* part. -/
theorem four_mul_ncard_compl_colorSplit_le (col : α → ℕ) :
    4 * ((colorSplit col)ᶜ).ncard ≤ 3 * Fintype.card α := by
  have h := card_le_four_mul_colorSplit col
  have hsum := Set.ncard_add_ncard_compl (colorSplit col)
  rw [Nat.card_eq_fintype_card] at hsum
  omega

open scoped Classical in
/-- §9.7, Cases 3a1 and 3b.  **The first part is small, or it is one color class.**  This
is what makes the sentence *"if color class selected is greater than `3n₂/4`, this color
class is equipartitioned"* applicable: whichever of the two parts Procedure
Reduce-Part2-by-Color selects, it is either at most three quarters of the points, or it is
a single color class. -/
theorem colorSplit_alternative (col : α → ℕ) :
    4 * (colorSplit col).ncard ≤ 3 * Fintype.card α ∨
      ∃ k, colorSplit col = colorClassOf col k := by
  classical
  unfold colorSplit
  split_ifs with h
  · exact Or.inr ⟨Nat.find h, rfl⟩
  · -- every class is smaller than a quarter; the least `k` is positive, and the part is
    -- the union of two pieces each smaller than a quarter
    push_neg at h
    refine Or.inl ?_
    set k := Nat.find (exists_colorBelow col) with hk
    have hsmall : ∀ j, 4 * (colorClassOf col j).ncard < Fintype.card α := h
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `k = 0`: the part is the class of `0`, which the case assumption bounds
      have hzero : colorBelow col k = colorClassOf col 0 := by
        rw [hk0]
        ext x
        simp only [colorBelow, colorClassOf, Set.mem_setOf_eq]
        omega
      have := hsmall 0
      rw [hzero]
      omega
    · -- `k ≥ 1`: minimality bounds the colors `< k`, and the class of `k` is small
      have hmin : ¬ (Fintype.card α ≤ 4 * (colorBelow col (k - 1)).ncard) :=
        Nat.find_min (exists_colorBelow col) (by omega)
      push_neg at hmin
      have hsplit : colorBelow col k
          = colorBelow col (k - 1) ∪ colorClassOf col k := by
        ext x
        simp only [colorBelow, colorClassOf, Set.mem_union, Set.mem_setOf_eq]
        omega
      have hdisj : Disjoint (colorBelow col (k - 1)) (colorClassOf col k) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        have h1 : col x ≤ k - 1 := hx
        have h2 : col x = k := hx'
        omega
      have hcard : (colorBelow col k).ncard
          = (colorBelow col (k - 1)).ncard + (colorClassOf col k).ncard := by
        rw [hsplit, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      have := hsmall k
      omega

/-! ### Canonicity -/

open scoped Classical in
/-- §9.7.  **The choice of the two parts is canonical.**  A bijection that preserves the
coloring carries the first part onto the first part, because the rule names it by color
values only. -/
theorem colorSplit_image {col : α → ℕ} {col' : β → ℕ} (e : α ≃ β)
    (hcol : ∀ x, col' (e x) = col x) :
    e '' colorSplit col = colorSplit col' := by
  classical
  have hclass : ∀ k, e '' colorClassOf col k = colorClassOf col' k := by
    intro k
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show col' (e x) = k
      rw [hcol x]; exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      show col (e.symm y) = k
      rw [← hcol (e.symm y), e.apply_symm_apply]
      exact hy
  have hbelow : ∀ k, e '' colorBelow col k = colorBelow col' k := by
    intro k
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show col' (e x) ≤ k
      rw [hcol x]; exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      show col (e.symm y) ≤ k
      rw [← hcol (e.symm y), e.apply_symm_apply]
      exact hy
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hncard : ∀ k, (colorClassOf col k).ncard = (colorClassOf col' k).ncard := by
    intro k
    rw [← hclass k, Set.ncard_image_of_injective _ e.injective]
  have hncard' : ∀ k, (colorBelow col k).ncard = (colorBelow col' k).ncard := by
    intro k
    rw [← hbelow k, Set.ncard_image_of_injective _ e.injective]
  unfold colorSplit
  by_cases h : ∃ k, Fintype.card α ≤ 4 * (colorClassOf col k).ncard
  · have h' : ∃ k, Fintype.card β ≤ 4 * (colorClassOf col' k).ncard := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by rw [← hcard, ← hncard k]; exact hk⟩
    rw [dif_pos h, dif_pos h']
    have : Nat.find h = Nat.find h' := by
      refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
      · rw [hncard, hcard]; exact Nat.find_spec h'
      · rw [← hncard, ← hcard]; exact Nat.find_spec h
    rw [this, hclass]
  · have h' : ¬ ∃ k, Fintype.card β ≤ 4 * (colorClassOf col' k).ncard := by
      rintro ⟨k, hk⟩
      exact h ⟨k, by rw [hcard, hncard k]; exact hk⟩
    rw [dif_neg h, dif_neg h']
    have : Nat.find (exists_colorBelow col) = Nat.find (exists_colorBelow col') := by
      refine le_antisymm (Nat.find_le ?_) (Nat.find_le ?_)
      · rw [hncard', hcard]; exact Nat.find_spec (exists_colorBelow col')
      · rw [← hncard', ← hcard]; exact Nat.find_spec (exists_colorBelow col)
    rw [this, hbelow]

end Babai
