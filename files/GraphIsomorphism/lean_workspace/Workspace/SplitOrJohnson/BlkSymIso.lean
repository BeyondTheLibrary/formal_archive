/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.3: the symmetry defect of `V₁` is an isomorphism invariant, and Procedure
Reduce-Part2-by-Color is canonical.
-/
import Workspace.SplitOrJohnson.BlkRestrict

/-!
# §9.3  Procedure Reduce-Part2-by-Color is canonical

Version 2.5, lines 4076-4090.

The exits of §9.7 return the input restricted to *the part that Procedure
Reduce-Part2-by-Color selects* (`Babai.reducePart2ByColorBlk`).  For that exit to be an
outcome of a reduction, the selected part has to be carried onto the selected part by
every isomorphism of the input.  The procedure decides by comparing the absolute symmetry
defect of `V₁` in `X[V₁, U₁]` with `(n₁ − 1)/2`, so all that is needed is that the
symmetry defect of `V₁` is an isomorphism invariant, which this file proves.

| Paper | Lean |
|---|---|
| twins of `V₁` are carried to twins of `V₁` | `Babai.VColBipBlk.isTwin_iff_of_isIsoTo` |
| Def. 2.4.29: the symmetricity of `V₁` is an invariant | `Babai.VColBipBlk.symmetricity₁_eq_of_isIsoTo` |
| Def. 2.4.29: the symmetry defect of `V₁` is an invariant | `Babai.VColBipBlk.symDefect₁_eq_of_isIsoTo` |
| the selected part is carried onto the selected part | `Babai.reducePart2ByColorBlk_image` |
-/

namespace Babai

namespace VColBipBlk

variable {s t : Type} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
  {κ : Type} [Zero κ] {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}

/-- Definition 2.3.9.  **An isomorphism carries the twins of `V₁` to the twins of `V₁`.**
Two points of `V₁` are twins exactly when they have the same color and the same
neighboring blocks (`Babai.VColBipBlk.isTwin_iff`), and an isomorphism preserves the color
of a point, the blocks and the edges. -/
theorem isTwin_iff_of_isIsoTo (h : X.IsIsoTo Y φ) {x x' : s} (hx : X.part₁ x)
    (hx' : X.part₁ x') (hne : x ≠ x') :
    IsTwin Y.Aut (φ x) (φ x') ↔ IsTwin X.Aut x x' := by
  have hne' : φ x ≠ φ x' := fun hc => hne (φ.injective hc)
  rw [Y.isTwin_iff ((h.part₁ x).2 hx) ((h.part₁ x').2 hx') hne', X.isTwin_iff hx hx' hne]
  refine and_congr ?_ ?_
  · rw [h.color₁ x, h.color₁ x']
  · constructor
    · intro hh B hB
      have hmem := hh (φ '' B) ((h.blocks B).2 hB)
      rwa [h.edges x B, h.edges x' B] at hmem
    · intro hh B' hB'
      have hB : φ.symm '' B' ∈ X.blocks := by
        have hb := h.blocks (φ.symm '' B')
        rw [Equiv.image_symm_image] at hb
        exact hb.1 hB'
      have hmem := hh _ hB
      rw [← h.edges x (φ.symm '' B'), ← h.edges x' (φ.symm '' B'),
        Equiv.image_symm_image] at hmem
      exact hmem

open scoped Classical in
/-- One half of `Babai.VColBipBlk.symmetricity₁_eq_of_isIsoTo`: the image of a largest set
of twins of `V₁` is a set of twins of `V₁`. -/
theorem symmetricity₁_le_of_isIsoTo (h : X.IsIsoTo Y φ) :
    X.symmetricity₁ ≤ Y.symmetricity₁ := by
  classical
  obtain ⟨T, hT₁, hT, hTc⟩ := exists_twinSet_card_eq_symmetricity₁ (X := X)
  have hcard : (T.image φ).card = T.card := Finset.card_image_of_injective _ φ.injective
  have hle : (T.image φ).card ≤ Y.symmetricity₁ := by
    refine card_le_symmetricity₁ (X := Y) (fun y hy => ?_) (fun y hy y' hy' hne => ?_)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact (h.part₁ x).2 (hT₁ x hx)
    · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy hy'
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      have hxx' : x ≠ x' := fun hc => hne (by rw [hc])
      exact (isTwin_iff_of_isIsoTo h (hT₁ x hx) (hT₁ x' hx') hxx').2
        (hT x (by simpa using hx) x' (by simpa using hx') hxx')
  rw [hcard, hTc] at hle
  exact hle

/-- Definition 2.4.29.  **The symmetricity of `V₁` is an isomorphism invariant.** -/
theorem symmetricity₁_eq_of_isIsoTo (h : X.IsIsoTo Y φ) :
    X.symmetricity₁ = Y.symmetricity₁ :=
  le_antisymm (symmetricity₁_le_of_isIsoTo h) (symmetricity₁_le_of_isIsoTo h.symm)

/-- Definition 2.4.29.  **The absolute symmetry defect of `V₁` is an isomorphism
invariant.** -/
theorem symDefect₁_eq_of_isIsoTo (h : X.IsIsoTo Y φ) : X.symDefect₁ = Y.symDefect₁ := by
  rw [symDefect₁, symDefect₁, symmetricity₁_eq_of_isIsoTo h, V₁_ncard_eq_of_isIsoTo h]

end VColBipBlk

variable {s t : Type} [Fintype s] [DecidableEq s] [Fintype t] [DecidableEq t]
  {κ : Type} [Zero κ] {X : VColBipBlk s κ} {Y : VColBipBlk t κ} {φ : s ≃ t}

/-- §9.3.  **Procedure Reduce-Part2-by-Color is canonical.**  An isomorphism that carries
the first part onto the first part and the second part onto the second part carries the
*selected* part onto the selected part, because the procedure decides by the absolute
symmetry defect of `V₁` in the first of the two restrictions
(`Babai.VColBipBlk.symDefect₁_eq_of_isIsoTo`).

This is what makes the exits of §9.7 that return the selected part canonical. -/
theorem reducePart2ByColorBlk_image (h : X.IsIsoTo Y φ) {U₁ U₂ : Set (Set s)}
    {U₁' U₂' : Set (Set t)} (hU₁ : ∀ B : Set s, φ '' B ∈ U₁' ↔ B ∈ U₁)
    (hU₂ : ∀ B : Set s, φ '' B ∈ U₂' ↔ B ∈ U₂) (B : Set s) :
    φ '' B ∈ reducePart2ByColorBlk Y U₁' U₂' ↔ B ∈ reducePart2ByColorBlk X U₁ U₂ := by
  classical
  have hV : Y.V₁.ncard = X.V₁.ncard := (VColBipBlk.V₁_ncard_eq_of_isIsoTo h).symm
  have hd : (Y.restrictBlk U₁').symDefect₁ = (X.restrictBlk U₁).symDefect₁ :=
    (VColBipBlk.symDefect₁_eq_of_isIsoTo (VColBipBlk.restrictBlk_isIsoTo h hU₁)).symm
  unfold reducePart2ByColorBlk
  rw [hV, hd]
  split_ifs
  · exact hU₁ B
  · exact hU₂ B

end Babai
