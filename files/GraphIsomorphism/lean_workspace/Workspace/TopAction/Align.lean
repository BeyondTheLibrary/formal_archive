/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: the part of Procedure Align (Sec. 14.1) that Corollary 12.0.10 uses.
-/
import Workspace.TopAction.TopAction2

/-!
# The fragment of Procedure Align used by Cor. 12.0.10

Corollary 12.0.10 says

> Apply items 1 to 6 of Procedure Align (Sec. 14.1) with `X(x) := C_x` and `X(y) := C_y`.
> The result is that
> * if `|C_x| ≠ |C_y|` then isomorphism is rejected
> * else `y` is updated so now `C_x = C_y = C`
> * from the coloring `(C, Γ \ C)` of `Γ` we infer a canonical coloring of `Ω`; one of the
>   color classes is `Ω(C)`; and we begin the application of the Chain Rule with this color
>   class.

Procedure Align itself belongs to Section 14, which is not formalized yet.  This file
states **only** what Cor. 12.0.10 uses from it, as facts about strings and color classes:

* `Babai.IsCanonicalColoring`: what "canonical coloring of `Γ` with respect to the string"
  means concretely for the purposes of this section — the coloring is carried along by `ϕ`
  under the action of `G` on strings.  (Section 6 has the general categorical notion,
  `Babai.IsCanonicalVertexColoring`; the concrete equivariance below is what the proof
  uses, and Section 14 can reuse it.)
* `Babai.Align_reject`: "if `|C_x| ≠ |C_y|` then isomorphism is rejected" — in fact
  `Iso_G(x,y) = ∅`.
* `Babai.Align_shift`: "else `y` is updated so now `C_x = C_y = C`" — there is a `σ ∈ G`
  such that the shifted string `y^{σ⁻¹}` has color class `C_x`, and `Iso_G(x,y)` is
  recovered from `Iso_G(x, y^{σ⁻¹})` by the shift identity Eq. (57).

The third bullet (the induced canonical coloring of `Ω` and the class `Ω(C)`) is a
statement about the standard blocks of Theorem 10.5.1; it is stated in
`Workspace/TopAction/TopAction4.lean`, where it is used.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type u} {A : Type v} {Γ κ : Type*} {G : Subgroup (Equiv.Perm Ω)}

/-- A *canonical coloring of `Γ` with respect to the string*: an assignment `col z` of a
coloring of `Γ` to each string `z : Ω → Σ`, canonical in the sense that a `G`-shift of the
string shifts the coloring by the corresponding permutation of `Γ`.

Concretely, for `σ ∈ G` the color of `γ^{σ^ϕ}` in `col(z^σ)` is the color of `γ` in
`col(z)`.  This is the only consequence of canonicity that Cor. 12.0.10 uses. -/
def IsCanonicalColoring (ϕ : G →* Equiv.Perm Γ) (col : (Ω → A) → Γ → κ) : Prop :=
  ∀ (z : Ω → A) (σ : G) (γ : Γ), col (strAct z (σ : Equiv.Perm Ω)) (ϕ σ γ) = col z γ

/-- The color class of color `c` in the canonical coloring of `Γ` with respect to `z`. -/
def colorClass (col : (Ω → A) → Γ → κ) (z : Ω → A) (c : κ) : Set Γ :=
  {γ | col z γ = c}

/-- Canonicity transports color classes along isomorphisms: if `τ` is a `G`-isomorphism of
`x` and `y` then `τ^ϕ` maps the color class of `c` for `x` onto the color class of `c` for
`y`. -/
theorem image_colorClass_of_isIso {ϕ : G →* Equiv.Perm Γ}
    {col : (Ω → A) → Γ → κ} (hcol : IsCanonicalColoring ϕ col) {x y : Ω → A}
    {τ : Equiv.Perm Ω} (hτG : τ ∈ G) (hxy : strAct x τ = y) (c : κ) :
    (ϕ ⟨τ, hτG⟩) '' colorClass col x c = colorClass col y c := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    have h := hcol x ⟨τ, hτG⟩ δ
    rw [hxy] at h
    simpa [colorClass, h] using hδ
  · intro hγ
    refine ⟨(ϕ ⟨τ, hτG⟩)⁻¹ γ, ?_, by simp⟩
    have h := hcol x ⟨τ, hτG⟩ ((ϕ ⟨τ, hτG⟩)⁻¹ γ)
    rw [hxy] at h
    rw [show (ϕ ⟨τ, hτG⟩) ((ϕ ⟨τ, hτG⟩)⁻¹ γ) = γ from by simp] at h
    show col x ((ϕ ⟨τ, hτG⟩)⁻¹ γ) = c
    rw [← h]
    exact hγ

/-- Procedure Align, items 1–2, in the form Cor. 12.0.10 uses: **"if `|C_x| ≠ |C_y|` then
isomorphism is rejected"**.  Indeed, if the two color classes have different sizes then
there is no `G`-isomorphism at all. -/
theorem Align_reject [Finite Γ] {ϕ : G →* Equiv.Perm Γ} {col : (Ω → A) → Γ → κ}
    (hcol : IsCanonicalColoring ϕ col) {x y : Ω → A} (c : κ)
    (hne : (colorClass col x c).ncard ≠ (colorClass col y c).ncard) :
    strIso (G : Set (Equiv.Perm Ω)) x y = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro τ hτ
  refine hne ?_
  rw [← image_colorClass_of_isIso hcol hτ.1 hτ.2 c]
  exact (Set.ncard_image_of_injective _ (ϕ ⟨τ, hτ.1⟩).injective).symm

/-- Procedure Align, items 2–3, in the form Cor. 12.0.10 uses: **"else `y` is updated so
now `C_x = C_y = C`"**.

Given `σ ∈ G` whose image `σ^ϕ` carries the color class of `c` for `x` onto the one for
`y` (this is the `G^ϕ`-isomorphism of the two colorings that item 2 (i) produces, lifted
by item 2 (ii)), the shifted string `y' = y^{σ⁻¹}` has the same color class of `c` as `x`,
and `Iso_G(x,y)` is the paper's **right** coset `Iso_G(x,y')σ` of Eq. (57), i.e. Lean's left
translate `σ • Iso_G(x,y')`. -/
theorem Align_shift {ϕ : G →* Equiv.Perm Γ} {col : (Ω → A) → Γ → κ}
    (hcol : IsCanonicalColoring ϕ col) (x y : Ω → A) (c : κ) (σ : G)
    (hσ : (ϕ σ) '' colorClass col x c = colorClass col y c) :
    colorClass col (strAct y (σ : Equiv.Perm Ω)⁻¹) c = colorClass col x c ∧
      strIso (G : Set (Equiv.Perm Ω)) x y =
        (σ : Equiv.Perm Ω) • strIso (G : Set (Equiv.Perm Ω)) x
          (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
  constructor
  · -- `col(y^{σ⁻¹})` is `col(y)` pulled back along `σ^ϕ`
    ext γ
    have hkey : col (strAct y (σ : Equiv.Perm Ω)⁻¹) γ = col y (ϕ σ γ) := by
      have := hcol (strAct y (σ : Equiv.Perm Ω)⁻¹) σ γ
      rw [← strAct_mul y (σ : Equiv.Perm Ω)⁻¹ (σ : Equiv.Perm Ω)] at this
      simp only [mul_inv_cancel, strAct_one] at this
      exact this.symm
    simp only [colorClass, Set.mem_setOf_eq, hkey]
    constructor
    · intro h
      have hmem : ϕ σ γ ∈ colorClass col y c := h
      rw [← hσ] at hmem
      obtain ⟨δ, hδ, hδγ⟩ := hmem
      have : δ = γ := (ϕ σ).injective hδγ
      rw [← this]
      exact hδ
    · intro h
      have : ϕ σ γ ∈ colorClass col y c := by rw [← hσ]; exact ⟨γ, h, rfl⟩
      exact this
  · -- the shift identity, Eq. (57)
    have hGσ : (σ : Equiv.Perm Ω) • (G : Set (Equiv.Perm Ω)) = (G : Set (Equiv.Perm Ω)) := by
      ext τ
      rw [mem_perm_smul_set, SetLike.mem_coe, SetLike.mem_coe]
      constructor
      · intro h
        have : τ = (σ : Equiv.Perm Ω) * ((σ : Equiv.Perm Ω)⁻¹ * τ) := by group
        rw [this]; exact mul_mem σ.2 h
      · intro h; exact mul_mem (inv_mem σ.2) h
    have := strIso_smul (G : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) x y
    rwa [hGσ] at this

end Babai
