/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, steps 7 and 8: the object and the coloring they produce are functions of the
input, so an isomorphism of the inputs carries one to the other.
-/
import Workspace.SplitOrJohnson.Step8Claim

/-!
# §9.4, steps 7 and 8 are canonical

Version 2.5, lines 4152-4165 of `babai-gi-source/quasi25.txt`.

Steps 5 to 8 of §9.4 are one functor out of the category of the inputs into the input
category of one of the three cases of step 9 (see the docstring of
`Babai.steps_9_4_5_to_9`).  A functor needs two halves: the object, which is built in
`Workspace/SplitOrJohnson/Step78.lean` and `Workspace/SplitOrJohnson/Step8.lean`, and the
morphisms, which is this file.

Everything here is the same statement repeated down the construction: *if `φ` is an
isomorphism of the two inputs, then `φ` carries the object of the one step to the object of
the other*.  The chain is

* `Babai.step7Support_image`, `Babai.mem_step7Set_iff` — the new point set `W₁ ∪ D_j` is
  canonical, because `W₁` is (`Babai.dominantClass_image`) and `D_j` is
  (`Babai.step7Blocks_image`);
* `Babai.step7Equiv` — hence `φ` restricts to a bijection of the new point sets;
* `Babai.step8Obj_isIsoTo` — the graph `(V₁, V₂; R_i)` of step 8 is carried to the graph of
  step 8 of the other input: the parts and the colorings are inherited from `φ`, and the
  edges match because the chosen constituent is canonical (`Babai.step8Color_congr`) and
  the coloring of step 3 is (`Babai.VColBipBlk.wlCaseColor_map`);
* `Babai.step8VtxIso` — so `φ` carries the vertex set of the new graph onto the vertex set
  of the other;
* `Babai.step8Raw_map` — and the **second WL refinement commutes with it**, by Eq. (26)
  (`Babai.WL.iso_iter`), exactly as the first one did in step 3
  (`Babai.VColBipBlk.wlRaw_map`);
* `Babai.step8CaseColor`, `Babai.step8CaseColor_map` — the `ℕ`-named coloring that the
  case categories of §9.6-§9.8 carry, and its canonicity.

| Paper | Lean |
|---|---|
| §9.4, step 7, the point set `W₁ ∪ D_j` is canonical | `Babai.mem_step7Set_iff` |
| §9.4, steps 7-8, the restriction of a morphism | `Babai.step7Equiv` |
| §9.4, step 8, `(V₁, V₂; R_i)` is canonical | `Babai.step8Obj_isIsoTo` |
| §9.4, step 8, Eq. (26) for the second refinement | `Babai.step8Raw_map` |
| §9.4, step 8, the coloring the case categories carry | `Babai.step8CaseColor` |
| §9.4, step 8, that coloring is canonical | `Babai.step8CaseColor_map` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open VColBipBlk

/-! ### A general fact about the canonical `ℕ`-naming of a coloring -/

namespace PartitionStructure

variable {V W K : Type*} [Finite V] [Finite W]

/-- The `Babai.natRank` naming of a coloring is canonical: a bijection of the vertex sets
that preserves the coloring preserves the names. This lemma retains the legacy abstract
naming interface. Section 9 now uses the named refinement instead. -/
theorem natColor_ofNatColoring_map {d : V → V → K} {d' : W → W → K} (e : V ≃ W)
    (h : ∀ x y : V, d' (e x) (e y) = d x y) (x y : V) :
    (ofNatColoring d').natColor (e x) (e y) = (ofNatColoring d).natColor x y := by
  have hcodes : natCodes d' = natCodes d := by
    ext c
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      refine ⟨(e.symm a, e.symm b), ?_⟩
      have hab := h (e.symm a) (e.symm b)
      simp only [Equiv.apply_symm_apply] at hab
      exact hab.symm
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨(e a, e b), h a b⟩
  rw [natColor_ofNatColoring, natColor_ofNatColoring, hcodes, h]

end PartitionStructure

/-! ### §9.4, step 7: the new point set is canonical -/

section Step7Set

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 7.  **The points covered by the blocks of `D_j` form a canonical set.** -/
theorem step7Support_image (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step7Support Y = φ '' step7Support X := by
  have hblk := step7Blocks_image hφ
  ext z
  constructor
  · rintro ⟨B, hB, hzB⟩
    rw [hblk] at hB
    obtain ⟨B₀, hB₀, rfl⟩ := hB
    obtain ⟨w, hw, rfl⟩ := hzB
    exact ⟨w, ⟨B₀, hB₀, hw⟩, rfl⟩
  · rintro ⟨w, ⟨B₀, hB₀, hw⟩, rfl⟩
    exact ⟨φ '' B₀, by rw [hblk]; exact ⟨B₀, hB₀, rfl⟩, ⟨w, hw, rfl⟩⟩

/-- §9.4, step 7.  **The new point set `W₁ ∪ D_j` is canonical**: a morphism of the inputs
carries it onto the new point set of the image. -/
theorem mem_step7Set_iff (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (z : ↥X.car) :
    ((φ z : ↥Y.car) : Ω) ∈ step7Set Y ↔ (z : Ω) ∈ step7Set X := by
  have hkey : ∀ {X' Y' : Pt (BipBlockInputs Ω)} {ψ : ↥X'.car ≃ ↥Y'.car},
      ψ ∈ (BipBlockInputs Ω).IsoP X' Y' → ∀ w : ↥X'.car,
        (w : Ω) ∈ step7Set X' → ((ψ w : ↥Y'.car) : Ω) ∈ step7Set Y' := by
    rintro X' Y' ψ hψ w ⟨w', hw', hww⟩
    have hw2 : w' = w := Subtype.ext hww
    subst hw2
    refine ⟨ψ w', ?_, rfl⟩
    rcases hw' with hd | hs
    · exact Or.inl (by rw [dominantClass_image hψ]; exact ⟨w', hd, rfl⟩)
    · exact Or.inr (by rw [step7Support_image hψ]; exact ⟨w', hs, rfl⟩)
  refine ⟨fun h => ?_, hkey hφ z⟩
  have := hkey ((BipBlockInputs Ω).symm_mem hφ) (φ z) h
  rwa [Equiv.symm_apply_apply] at this

/-- §9.4, steps 7 and 8.  **The restriction of a morphism to the new point sets.** -/
noncomputable def step7Equiv (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    ↥(step7Set X) ≃ ↥(step7Set Y) where
  toFun z := ⟨((φ ⟨(z : Ω), step7Set_subset X z.2⟩ : ↥Y.car) : Ω),
    (mem_step7Set_iff hφ _).2 z.2⟩
  invFun w := ⟨((φ.symm ⟨(w : Ω), step7Set_subset Y w.2⟩ : ↥X.car) : Ω), by
    have h := (mem_step7Set_iff hφ (φ.symm ⟨(w : Ω), step7Set_subset Y w.2⟩)).1
    simp only [Equiv.apply_symm_apply] at h
    exact h w.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

@[simp] theorem step7Equiv_val (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (z : ↥(step7Set X)) :
    ((step7Equiv hφ z : ↥(step7Set Y)) : Ω)
      = ((φ ⟨(z : Ω), step7Set_subset X z.2⟩ : ↥Y.car) : Ω) := rfl

/-- The restriction of a morphism and the two inclusions commute. -/
theorem incl_step7Equiv (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (z : ↥(step7Set X)) :
    VColBipBlk.incl (step7Set_subset Y) (step7Equiv hφ z)
      = φ (VColBipBlk.incl (step7Set_subset X) z) := rfl

/-- The restriction of a morphism and the two inclusions commute, on subsets. -/
theorem incl_image_step7Equiv (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y)
    (A : Set ↥(step7Set X)) :
    VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' A)
      = φ '' (VColBipBlk.incl (step7Set_subset X) '' A) := by
  ext w
  constructor
  · rintro ⟨-, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨VColBipBlk.incl (step7Set_subset X) z, ⟨z, hz, rfl⟩, (incl_step7Equiv hφ z).symm⟩
  · rintro ⟨-, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨step7Equiv hφ z, ⟨z, hz, rfl⟩, incl_step7Equiv hφ z⟩

end Step7Set

/-! ### §9.4, step 8: the graph `(V₁, V₂; R_i)` is canonical -/

section Step8Obj

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 8.  **The graph `(V₁, V₂; R_i)` is a function of the input**: a morphism of
the inputs restricts to an isomorphism of the two graphs of step 8.

The parts and the two colorings are inherited from the morphism, through the restriction
of step 7.  The edges match because the constituent that step 8 keeps is chosen by the
canonical name of its color: the chosen name is the same for the two inputs
(`Babai.step8Color_congr`) and a morphism preserves the names
(`Babai.VColBipBlk.wlCaseColor_map`). -/
theorem step8Obj_isIsoTo (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    (step8Obj X).IsIsoTo (step8Obj Y) (step7Equiv hφ) := by
  classical
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  have hcol : step8Color X = step8Color Y := step8Color_congr ⟨φ, hφ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the first part
    intro x
    show (step7Obj Y).part₁ (step7Equiv hφ x) ↔ (step7Obj X).part₁ x
    rw [step7Obj_part₁_iff, step7Obj_part₁_iff, incl_step7Equiv hφ x,
      dominantClass_image hφ]
    constructor
    · rintro ⟨w, hw, hwx⟩
      rwa [φ.injective hwx] at hw
    · intro hx
      exact ⟨_, hx, rfl⟩
  · -- the blocks
    intro B
    show VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B) ∈ (Y.obj.1.1).blocks
      ↔ VColBipBlk.incl (step7Set_subset X) '' B ∈ (X.obj.1.1).blocks
    rw [incl_image_step7Equiv hφ B]
    exact hg.blocks _
  · -- the edges
    intro x B
    constructor
    · rintro ⟨hp, hB, hc⟩
      refine ⟨?_, ?_, ?_⟩
      · show (step7Obj X).part₁ x
        have : (step7Obj Y).part₁ (step7Equiv hφ x) := hp
        rw [step7Obj_part₁_iff, incl_step7Equiv hφ x, dominantClass_image hφ] at this
        obtain ⟨w, hw, hwx⟩ := this
        rw [step7Obj_part₁_iff]
        rwa [φ.injective hwx] at hw
      · show VColBipBlk.incl (step7Set_subset X) '' B ∈ (X.obj.1.1).blocks
        have : VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B)
            ∈ (Y.obj.1.1).blocks := hB
        rw [incl_image_step7Equiv hφ B] at this
        exact (hg.blocks _).1 this
      · have := hc
        rw [show VColBipBlk.incl (step7Set_subset Y) (step7Equiv hφ x)
              = φ (VColBipBlk.incl (step7Set_subset X) x) from incl_step7Equiv hφ x,
          show VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B)
              = φ '' (VColBipBlk.incl (step7Set_subset X) '' B) from
            incl_image_step7Equiv hφ B,
          ← Set.image_singleton (f := φ), VColBipBlk.wlCaseColor_map hg, ← hcol] at this
        exact this
    · rintro ⟨hp, hB, hc⟩
      refine ⟨?_, ?_, ?_⟩
      · show (step7Obj Y).part₁ (step7Equiv hφ x)
        rw [step7Obj_part₁_iff, incl_step7Equiv hφ x, dominantClass_image hφ]
        exact ⟨_, (step7Obj_part₁_iff X x).1 hp, rfl⟩
      · show VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B)
          ∈ (Y.obj.1.1).blocks
        rw [incl_image_step7Equiv hφ B]
        exact (hg.blocks _).2 hB
      · show VColBipBlk.wlCaseColor Y.obj.1.1
          ({VColBipBlk.incl (step7Set_subset Y) (step7Equiv hφ x)} : Set ↥Y.car)
          (VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B)) = step8Color Y
        rw [show VColBipBlk.incl (step7Set_subset Y) (step7Equiv hφ x)
              = φ (VColBipBlk.incl (step7Set_subset X) x) from incl_step7Equiv hφ x,
          show VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B)
              = φ '' (VColBipBlk.incl (step7Set_subset X) '' B) from
            incl_image_step7Equiv hφ B,
          ← Set.image_singleton (f := φ), VColBipBlk.wlCaseColor_map hg, ← hcol]
        exact hc
  · -- the coloring of the points
    intro x
    show (Y.obj.1.1).f (VColBipBlk.incl (step7Set_subset Y) (step7Equiv hφ x))
      = (X.obj.1.1).f (VColBipBlk.incl (step7Set_subset X) x)
    rw [incl_step7Equiv hφ x]
    exact hg.color₁ _
  · -- the coloring of the blocks
    intro B
    show (if VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B) ∈ (Y.obj.1.1).blocks
        then (Y.obj.1.1).g (VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B))
        else 0)
      = if VColBipBlk.incl (step7Set_subset X) '' B ∈ (X.obj.1.1).blocks
        then (X.obj.1.1).g (VColBipBlk.incl (step7Set_subset X) '' B) else 0
    rw [incl_image_step7Equiv hφ B]
    by_cases hB : VColBipBlk.incl (step7Set_subset X) '' B ∈ (X.obj.1.1).blocks
    · rw [if_pos ((hg.blocks _).2 hB), if_pos hB, hg.color₂]
    · rw [if_neg (fun hc => hB ((hg.blocks _).1 hc)), if_neg hB]
  · -- the hint: it is inherited along the restriction of step 7, so the morphism of the
    -- inputs preserves it.
    intro A B
    show (Y.obj.1.1).h (VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' A))
        (VColBipBlk.incl (step7Set_subset Y) '' (step7Equiv hφ '' B))
      = (X.obj.1.1).h (VColBipBlk.incl (step7Set_subset X) '' A)
        (VColBipBlk.incl (step7Set_subset X) '' B)
    rw [incl_image_step7Equiv hφ A, incl_image_step7Equiv hφ B]
    exact hg.hint _ _

/-- §9.4, step 8.  The morphism carries the vertices of the new graph onto the vertices of
the new graph of the image. -/
theorem step8Vtx_image_iff (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (A : Set ↥(step7Set X)) :
    step7Equiv hφ '' A ∈ (step8Obj Y).vtx ↔ A ∈ (step8Obj X).vtx :=
  isVertexOn_image_iff (fun x => (step8Obj_isIsoTo hφ).part₁ x)
    (fun B => (step8Obj_isIsoTo hφ).blocks B) A

/-- §9.4, step 8.  **The bijection of the vertex sets of the two graphs of step 8.** -/
noncomputable def step8VtxIso (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    ↥((step8Obj X).vtx) ≃ ↥((step8Obj Y).vtx) where
  toFun A := ⟨step7Equiv hφ '' (A : Set ↥(step7Set X)), (step8Vtx_image_iff hφ _).2 A.2⟩
  invFun B := ⟨(step7Equiv hφ).symm '' (B : Set ↥(step7Set Y)), by
    have h := (step8Vtx_image_iff hφ ((step7Equiv hφ).symm '' (B : Set ↥(step7Set Y)))).1
    rw [Equiv.image_symm_image] at h
    exact h B.2⟩
  left_inv A := Subtype.ext (Equiv.symm_image_image _ _)
  right_inv B := Subtype.ext (Equiv.image_symm_image _ _)

@[simp] theorem step8VtxIso_val (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y)
    (A : ↥((step8Obj X).vtx)) :
    ((step8VtxIso hφ A : ↥((step8Obj Y).vtx)) : Set ↥(step7Set Y))
      = step7Equiv hφ '' (A : Set ↥(step7Set X)) := rfl

/-- §9.4, step 8, Eq. (26) for the **second** WL refinement: *"Update `X ← WL refinement of
`X`"* is canonical.

The refinement is run on the vertex set of the new graph, the morphism carries that vertex
set onto the vertex set of the image (`Babai.step8VtxIso`) and preserves the coloring that
is refined (`Babai.VColBipBlk.initColor_map`, for the isomorphism
`Babai.step8Obj_isIsoTo`), so `Babai.WL.iso_iter` carries the refinement along. -/
theorem step8Raw_map (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (u v : ↥((step8Obj X).vtx)) :
    step8Raw Y (step8VtxIso hφ u) (step8VtxIso hφ v) = step8Raw X u v := by
  have hinit : step8VtxIso hφ ∈ WL.Iso
      (fun a b : ↥((step8Obj X).vtx) =>
        VColBipBlk.initColor (step8Obj X) (a : Set ↥(step7Set X)) (b : Set ↥(step7Set X)))
      (fun a b : ↥((step8Obj Y).vtx) =>
        VColBipBlk.initColor (step8Obj Y) (a : Set ↥(step7Set Y)) (b : Set ↥(step7Set Y))) := by
    intro a b
    show VColBipBlk.initColor (step8Obj Y) (step7Equiv hφ '' (a : Set ↥(step7Set X)))
        (step7Equiv hφ '' (b : Set ↥(step7Set X)))
      = VColBipBlk.initColor (step8Obj X) (a : Set ↥(step7Set X)) (b : Set ↥(step7Set X))
    exact VColBipBlk.initColor_map (step8Obj_isIsoTo hφ) _ _
  have hiter : step8VtxIso hφ ∈ WL.Iso (step8Raw X) (step8Raw Y) := by
    rw [step8Raw, step8Raw, WL.iso_iter]
    exact hinit
  exact hiter u v

end Step8Obj

/-! ### §9.4, step 8: the coloring that the case categories carry -/

section CaseColor

variable (X : Pt (BipBlockInputs Ω))

open scoped Classical in
/-- §9.4, step 8.  **The coloring of the coherent configuration after step 8, named by
natural numbers.**  On a pair of vertices it is the named WL color of the
color of the second WL refinement, that is the `natColor` of `Babai.step8Config`; off the
vertex set it is the fixed color `0`, the normalization that `Babai.BlkCaseObj.c_off` and
`Babai.BlkImprimitiveObj.c_off` demand.

This is `Babai.VColBipBlk.wlCaseColor` of step 3 one step further on: there is no shift by
one, for the reason given in the module docstring of
`Workspace/SplitOrJohnson/WLConfig.lean`. -/
noncomputable def step8CaseColor (X : Pt (BipBlockInputs Ω))
    (A B : Set ↥(step7Set X)) : ℕ :=
  if h : A ∈ (step8Obj X).vtx ∧ B ∈ (step8Obj X).vtx then
    (step8Config X).natColor ⟨A, h.1⟩ ⟨B, h.2⟩ else 0

theorem step8CaseColor_off {A B : Set ↥(step7Set X)}
    (h : ¬ (IsVertexOn (step8Obj X).part₁ (step8Obj X).blocks A ∧
      IsVertexOn (step8Obj X).part₁ (step8Obj X).blocks B)) :
    step8CaseColor X A B = 0 := by
  classical
  have h' : ¬ (A ∈ (step8Obj X).vtx ∧ B ∈ (step8Obj X).vtx) := h
  rw [step8CaseColor, dif_neg h']

/-- §9.4, step 8.  On the vertices the coloring **is** the `natColor` of the configuration
`Babai.step8Config`; this is the equation that the field `Babai.IsBipartiteCase.coherent`
asks for. -/
theorem step8CaseColor_vtx (u v : ↥((step8Obj X).vtx)) :
    step8CaseColor X (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X))
      = (step8Config X).natColor u v := by
  classical
  rw [step8CaseColor, dif_pos ⟨u.2, v.2⟩]

variable {X}

/-- §9.4, step 8.  **The coloring after step 8 is canonical.**  The input isomorphism preserves the integer names at every round, by
`Babai.VColBipBlk.wlCaseColor_map`. -/
theorem step8CaseColor_map {Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (A B : Set ↥(step7Set X)) :
    step8CaseColor Y (step7Equiv hφ '' A) (step7Equiv hφ '' B) = step8CaseColor X A B := by
  classical
  by_cases h : A ∈ (step8Obj X).vtx ∧ B ∈ (step8Obj X).vtx
  · have hA : step7Equiv hφ '' A ∈ (step8Obj Y).vtx := (step8Vtx_image_iff hφ A).2 h.1
    have hB : step7Equiv hφ '' B ∈ (step8Obj Y).vtx := (step8Vtx_image_iff hφ B).2 h.2
    rw [step8CaseColor, step8CaseColor, dif_pos ⟨hA, hB⟩, dif_pos h]
    have hval : ∀ (u : ↥((step8Obj X).vtx)) (hu : step7Equiv hφ '' (u : Set ↥(step7Set X))
        ∈ (step8Obj Y).vtx),
        (⟨step7Equiv hφ '' (u : Set ↥(step7Set X)), hu⟩ : ↥((step8Obj Y).vtx))
          = step8VtxIso hφ u := fun _ _ => Subtype.ext rfl
    rw [hval ⟨A, h.1⟩ hA, hval ⟨B, h.2⟩ hB]
    rw [step8Config, step8Config, VColBipBlk.natColor_wlConfig,
      VColBipBlk.natColor_wlConfig]
    exact VColBipBlk.wlCaseColor_map (step8Obj_isIsoTo hφ) A B
  · have h' : ¬ (step7Equiv hφ '' A ∈ (step8Obj Y).vtx
        ∧ step7Equiv hφ '' B ∈ (step8Obj Y).vtx) := by
      intro hc
      exact h ⟨(step8Vtx_image_iff hφ A).1 hc.1, (step8Vtx_image_iff hφ B).1 hc.2⟩
    rw [step8CaseColor, step8CaseColor, dif_neg h', dif_neg h]

end CaseColor

end Babai
