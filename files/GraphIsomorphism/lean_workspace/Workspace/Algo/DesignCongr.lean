/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the test of Procedure "Design Lemma" depends on the coloring only
through its color classes (§8.2).
-/
import Workspace.Algo.DesignRaw

/-!
# §8.2 — the test depends only on the color classes

Every routine of the algorithmic layer is specified by the *classes* of the coloring it
computes, never by the names of the colors: `Algo.rawPipeline_spec` says that the table of
line 01 has the color classes of `F3 ∘ F2 ∘ F1`, not that its colors *are* those of the
mathematical functor (the routine renames every color by its rank, §4.1.1).

To read the specification of the whole procedure in the language of §8 — "the procedure returns
at `x⃗`, where `X` is the `k`-ary coherent configuration `F3(F2(F1(X₀)))`" — we therefore need
that `Babai.KAryPartStruct.Returns` is invariant under a change of the color names.  That is
what this file proves.  Everything the test of lines 04–08 looks at is class data:

* lines 04–05 compare the *sizes* of the vertex-color classes with `αn`;
* line 06 names the dominant class, which is a set of vertices;
* line 07 counts the colors the `2`-skeleton realizes on it, which is the *rank* of the induced
  configuration.

## Main results

* `Algo.returns_congr`, `Algo.returnsAt_congr` — lines 03–08 depend only on the classes;
* `Algo.procedure_eq_none_congr` — and so does the whole mathematical procedure.

No axiom and no `sorry`.
-/

namespace Algo

open Babai

/-! ## The rank of a partition structure is the number of realized colors -/

/-- The rank of a partition structure is the number of values its coloring realizes.  This is
`PartitionStructure.color_surjective` read backwards. -/
theorem rank_eq_card_image {Δ : Type*} [Fintype Δ] (P : PartitionStructure Δ) :
    (Finset.univ.image fun q : Δ × Δ => P.color q.1 q.2).card = P.rank := by
  have hu : (Finset.univ.image fun q : Δ × Δ => P.color q.1 q.2) = Finset.univ := by
    refine Finset.eq_univ_of_forall (fun i => ?_)
    obtain ⟨x, y, hxy⟩ := P.color_surjective i
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_univ _, hxy⟩
  rw [hu, Finset.card_univ, Fintype.card_fin]

/-- Counting the realized colors is the same whether they are read as elements of `Fin r` or as
naturals; the naturals are needed because `Algo.card_image_congr_of_iff` asks for an inhabited
target and `Fin 0` is empty. -/
theorem card_image_val {β : Type*} [Fintype β] {r : ℕ} (f : β → Fin r) :
    (Finset.univ.image (fun b => (f b : ℕ))).card = (Finset.univ.image f).card := by
  classical
  rw [show Finset.univ.image (fun b => (f b : ℕ))
      = (Finset.univ.image f).image Fin.val from (Finset.image_image ..).symm]
  exact Finset.card_image_of_injective _ Fin.val_injective

section Structures

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The induced rank depends on the coloring only through its classes.** -/
theorem induced_rank_congr_classes {P Q : PartitionStructure Ω}
    (h : ∀ u v u' v' : Ω, P.color u v = P.color u' v' ↔ Q.color u v = Q.color u' v')
    (Δ : Set Ω) [Fintype Δ] : (P.induced Δ).rank = (Q.induced Δ).rank := by
  classical
  rw [← rank_eq_card_image (P.induced Δ), ← rank_eq_card_image (Q.induced Δ),
    ← card_image_val (fun q : Δ × Δ => (P.induced Δ).color q.1 q.2),
    ← card_image_val (fun q : Δ × Δ => (Q.induced Δ).color q.1 q.2)]
  refine card_image_congr_of_iff (Finset.univ : Finset (↥Δ × ↥Δ)) _ _ (fun q₁ _ q₂ _ => ?_)
  simp only [Fin.val_inj]
  rw [PartitionStructure.induced_color_eq_iff, PartitionStructure.induced_color_eq_iff]
  exact h _ _ _ _

/-- **Line 07 depends on the coloring only through its classes.** -/
theorem isCliqueOn_congr_classes {P Q : PartitionStructure Ω}
    (h : ∀ u v u' v' : Ω, P.color u v = P.color u' v' ↔ Q.color u v = Q.color u' v')
    (Δ : Set Ω) : P.IsCliqueOn Δ ↔ Q.IsCliqueOn Δ := by
  classical
  rw [PartitionStructure.IsCliqueOn, PartitionStructure.IsCliqueOn,
    induced_rank_congr_classes h Δ]

variable {C D : Type*} {m : ℕ}

/-- Two `k`-ary partition structures with the same color classes have the same vertex-color
classes, class by class. -/
theorem vclass_vcolor_congr {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω D m}
    (h : ∀ u v : Str Ω m, Y.color u = Y.color v ↔ Y'.color u = Y'.color v) (v : Ω) :
    Y.vclass (Y.vcolor v) = Y'.vclass (Y'.vcolor v) := by
  ext w
  exact h (fun _ => w) (fun _ => v)

/-- Lines 04–05 need only be tested at the *realized* colors: an unrealized color has an empty
class, and the empty class is dominant only when no class is. -/
theorem noDominantColor_iff_vertices {α : ℝ} (Y : KAryPartStruct Ω C m) :
    KAryPartStruct.NoDominantColor α Y
      ↔ ∀ v : Ω, ((Y.vclass (Y.vcolor v)).ncard : ℝ) ≤ α * (Fintype.card Ω : ℝ) := by
  constructor
  · intro h v; exact h _
  · intro h i
    by_cases hi : ∃ v : Ω, Y.vcolor v = i
    · obtain ⟨v, rfl⟩ := hi; exact h v
    · have he : Y.vclass i = (∅ : Set Ω) := by
        ext w
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hw
        exact hi ⟨w, hw⟩
      rw [he, Set.ncard_empty, Nat.cast_zero]
      rcases isEmpty_or_nonempty Ω with hΩ | hΩ
      · have hc : Fintype.card Ω = 0 := Fintype.card_eq_zero
        rw [hc, Nat.cast_zero, mul_zero]
      · obtain ⟨v⟩ := hΩ
        have h1 := h v
        have h2 : (1 : ℝ) ≤ ((Y.vclass (Y.vcolor v)).ncard : ℝ) := by
          have hpos : 0 < (Y.vclass (Y.vcolor v)).ncard :=
            (Set.ncard_pos (Set.toFinite _)).2 ⟨v, rfl⟩
          exact_mod_cast hpos
        linarith

/-- **Lines 04–05 depend on the coloring only through its classes.** -/
theorem noDominantColor_congr {α : ℝ} {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω D m}
    (h : ∀ u v : Str Ω m, Y.color u = Y.color v ↔ Y'.color u = Y'.color v) :
    KAryPartStruct.NoDominantColor α Y ↔ KAryPartStruct.NoDominantColor α Y' := by
  rw [noDominantColor_iff_vertices, noDominantColor_iff_vertices]
  exact forall_congr' (fun v => by rw [vclass_vcolor_congr h v])

/-- **Line 06 depends on the coloring only through its classes.** -/
theorem hasDominantClass_congr {α : ℝ} {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω D m}
    (h : ∀ u v : Str Ω m, Y.color u = Y.color v ↔ Y'.color u = Y'.color v) :
    KAryPartStruct.HasDominantClass α Y ↔ KAryPartStruct.HasDominantClass α Y' := by
  rw [← KAryPartStruct.not_noDominantColor_iff, ← KAryPartStruct.not_noDominantColor_iff,
    noDominantColor_congr h]

/-- **The dominant class `C(x⃗)` depends on the coloring only through its classes.** -/
theorem dominantClass_congr {α : ℝ} {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω D m}
    (h : ∀ u v : Str Ω m, Y.color u = Y.color v ↔ Y'.color u = Y'.color v) :
    KAryPartStruct.dominantClass α Y = KAryPartStruct.dominantClass α Y' := by
  ext v
  show IsDominant α (Y.vclass (Y.vcolor v)) ↔ IsDominant α (Y'.vclass (Y'.vcolor v))
  rw [vclass_vcolor_congr h v]

/-- The `2`-skeleton depends on the coloring only through its classes. -/
theorem skel2_color_congr {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω D m}
    (h : ∀ u v : Str Ω m, Y.color u = Y.color v ↔ Y'.color u = Y'.color v) (hm : 2 ≤ m)
    (u v u' v' : Ω) :
    (Y.skel2 hm).color u v = (Y.skel2 hm).color u' v'
      ↔ (Y'.skel2 hm).color u v = (Y'.skel2 hm).color u' v' := by
  rw [KAryPartStruct.skel2_color_eq_iff, KAryPartStruct.skel2_color_eq_iff,
    KAryPartStruct.skeletonColor, KAryPartStruct.skeletonColor,
    KAryPartStruct.skeletonColor, KAryPartStruct.skeletonColor]
  exact h _ _

end Structures

section Returns

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {C D : Type*} {k l : ℕ}

/-- The restriction `X_x⃗` of §5.2.1 depends on the coloring only through its classes. -/
theorem restrTo_color_congr {X : KAryPartStruct Ω C k} {X' : KAryPartStruct Ω D k}
    (h : ∀ u v : Str Ω k, X.color u = X.color v ↔ X'.color u = X'.color v) (hl : l ≤ k)
    (x : Str Ω l) (u v : Str Ω (k - l)) :
    (X.restrTo hl x).color u = (X.restrTo hl x).color v
      ↔ (X'.restrTo hl x).color u = (X'.restrTo hl x).color v := by
  rw [KAryPartStruct.restrTo_color, KAryPartStruct.restrTo_color,
    KAryPartStruct.restrTo_color, KAryPartStruct.restrTo_color]
  exact h _ _

/-- **Lines 03–08 depend on the coloring only through its classes.**  The test the procedure
performs at a string is the same for two `k`-ary partition structures with the same color
classes — which is all a routine that renames the colors (§4.1.1) can preserve. -/
theorem returns_congr {α : ℝ} {X : KAryPartStruct Ω C k} {X' : KAryPartStruct Ω D k}
    (h : ∀ u v : Str Ω k, X.color u = X.color v ↔ X'.color u = X'.color v) (hl : l ≤ k)
    (x : Str Ω l) :
    KAryPartStruct.Returns α X hl x ↔ KAryPartStruct.Returns α X' hl x := by
  have hr := restrTo_color_congr h hl x
  refine and_congr Iff.rfl (or_congr (noDominantColor_congr hr) ?_)
  refine exists_congr (fun h2 => and_congr (hasDominantClass_congr hr) (not_congr ?_))
  rw [dominantClass_congr hr]
  exact isCliqueOn_congr_classes
    (fun u v u' v' => skel2_color_congr hr (by omega) u v u' v') _

/-- **Line 03 depends on the coloring only through its classes.** -/
theorem returnsAt_congr {α : ℝ} {X : KAryPartStruct Ω C k} {X' : KAryPartStruct Ω D k}
    (h : ∀ u v : Str Ω k, X.color u = X.color v ↔ X'.color u = X'.color v) (l : ℕ) :
    KAryPartStruct.ReturnsAt α X l ↔ KAryPartStruct.ReturnsAt α X' l :=
  exists_congr (fun hlk => exists_congr (fun x => returns_congr h hlk.le x))

/-- **The mathematical procedure fails on one structure exactly when it fails on any structure
with the same color classes.** -/
theorem procedure_eq_none_congr {α : ℝ} {X : KAryPartStruct Ω C k} {X' : KAryPartStruct Ω D k}
    (h : ∀ u v : Str Ω k, X.color u = X.color v ↔ X'.color u = X'.color v) :
    X.procedure α = none ↔ X'.procedure α = none := by
  classical
  rw [KAryPartStruct.procedure, KAryPartStruct.procedure]
  by_cases hex : ∃ l, KAryPartStruct.ReturnsAt α X l
  · have hex' : ∃ l, KAryPartStruct.ReturnsAt α X' l :=
      ⟨hex.choose, (returnsAt_congr h _).1 hex.choose_spec⟩
    rw [dif_pos hex, dif_pos hex']
    simp
  · have hex' : ¬ ∃ l, KAryPartStruct.ReturnsAt α X' l := by
      rintro ⟨l, hl⟩
      exact hex ⟨l, (returnsAt_congr h l).2 hl⟩
    rw [dif_neg hex, dif_neg hex']

end Returns

end Algo
