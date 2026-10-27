/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, line 4: the coloring of `Γ` that the outcome of Theorem 9.2.3 carries, and
line 6's dominant color class.
-/
import Workspace.Master.DesignVersions
import Workspace.Master.AlignClasses

/-!
# The coloring `(Δ₁, …, Δ_k)` of line 4, read off the outcome

> 4. (: Each of our structures has an underlying coloring – possibly trivial :)
>    Let `(Δ₁, …, Δ_k)` be the coloring of `X(x)` (the `Δ_j` are the color classes); so `Γ`
>    is the disjoint union of the `Δ_j`.
> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j)`.
> 7. (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>    relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then …

Sec. 14 says what the structures look like: *"a canonical coloring of `Γ` with an
additional canonical structure on some of the color classes"*.  So the `Δ_j` of line 4 are
the **color classes**, and the additional structure — an equipartition or a Johnson scheme —
sits on the dominant one.  In particular the `Δ_j` are *not* the blocks of a colored
partition: the blocks are the `Y` of line 7 (A), and it is the blocks, not the color
classes, that Definition 7.1.1 bounds by `αn`.

`Babai.alignColor` is that coloring, read off an outcome of Theorem 9.2.3
(`Babai.IsSplitOutcome`):

* case (a), a colored `α`-partition `Π` of `Γ`: the coloring of `Π`, refined by
  Proposition 7.1.3 (`Babai.ColoredPartition.equipartRefine`, which encodes the size of the
  block in the color) so that it is a colored **equi**partition, as line 7 (A) needs;
* case (b), a Johnson scheme on `W ⊆ Γ` with `|W| ≥ αm`: the two-coloring `(W, Γ ∖ W)`.

`Babai.alignColor_aut` is line 4's *"canonical"*: an automorphism of the outcome preserves
the coloring, which is the hypothesis `hstab` of `Babai.isInvariant_omegaColorClass`.

`Babai.ColoredPartition.alphaPartition_trichotomy` is what line 6 rests on: in a colored
`α`-partition every color class is small (`≤ m/2`), or nontrivially partitioned, or a single
block — and a single block has at most `αm` points by Definition 7.1.1.  So a dominant class
is nontrivially partitioned, and if there is none then every class has at most `αm` points,
which is the case `Babai.ncard_omegaColorClass_le_of_alpha` covers.

This is part of piece (iii) of Mismatch 2 in `Workspace/Master/DESIGN.md`.
-/

namespace Babai

open Equiv

universe u

/-! ### The trichotomy for a colored `α`-partition -/

section Trichotomy

variable {Λ : Type*} [Fintype Λ] {κ : Type*} (P : ColoredPartition Λ κ)

/-- A color class all of whose points are equivalent to `x` lies in the block of `x`. -/
theorem colorClass_subset_block {i : κ} {x : Λ}
    (hsingle : ∀ y, P.color y = i → P.part y x) : P.colorClass i ⊆ P.block x :=
  fun y hy => hsingle y hy

/-- §7.1, **the trichotomy of Observation 7.1.4**, in the direction line 6 needs: in a
colored `α`-partition every color class either has at most half of the points, or is
partitioned into at least two blocks, or is a single block and then has at most `αm`
points.

*Proof.*  The three cases are: the class is not dominant; it contains two points in
different blocks; it does not, so it is contained in the block of any of its points
(`Babai.colorClass_subset_block`), and every block has at most `ρ(Π) ≤ αm` points by
Definition 7.1.1.  The empty class is covered by the third case, since `0 ≤ ρ(Π)`.
Admissibility is not used here; it is used in
`Babai.ColoredPartition.two_le_ncard_block_of_two_blocks`, which is what turns "at least two
blocks" into line 7 (A)'s *"nontrivial"*. -/
theorem ColoredPartition.alphaPartition_trichotomy {α : ℝ} (hP : P.IsAlphaPartition α)
    (i : κ) :
    2 * (P.colorClass i).ncard ≤ Fintype.card Λ ∨
      (∃ x y : Λ, P.color x = i ∧ P.color y = i ∧ ¬ P.part y x) ∨
      ((P.colorClass i).ncard : ℝ) ≤ α * Fintype.card Λ := by
  by_cases hdom : 2 * (P.colorClass i).ncard ≤ Fintype.card Λ
  · exact Or.inl hdom
  by_cases htwo : ∃ x y : Λ, P.color x = i ∧ P.color y = i ∧ ¬ P.part y x
  · exact Or.inr (Or.inl htwo)
  refine Or.inr (Or.inr ?_)
  push_neg at htwo
  rcases Set.eq_empty_or_nonempty (P.colorClass i) with he | ⟨x, hx⟩
  · rw [he, Set.ncard_empty, Nat.cast_zero]
    exact le_trans (Nat.cast_nonneg _) hP.2
  · have hsub : P.colorClass i ⊆ P.block x :=
      colorClass_subset_block P fun y hy => htwo x y hx hy
    have h1 : (P.colorClass i).ncard ≤ P.rho :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (P.ncard_block_le_rho x)
    calc ((P.colorClass i).ncard : ℝ) ≤ (P.rho : ℝ) := Nat.cast_le.2 h1
      _ ≤ α * Fintype.card Λ := hP.2

/-- §14.1, line 7 (A), *"nontrivial"*: if a color class contains two points in different
blocks then **every** block inside it has at least two points.

This is where admissibility (Definition 7.1.1) is used: the class has at least the two
points, so admissibility applies to it. -/
theorem ColoredPartition.two_le_ncard_block_of_two_blocks (hadm : P.IsAdmissible) {i : κ}
    {x y : Λ} (hx : P.color x = i) (hy : P.color y = i) (hne : ¬ P.part y x) {z : Λ}
    (hz : P.color z = i) : 2 ≤ (P.block z).ncard := by
  refine hadm z ?_
  have hxy : x ≠ y := by
    rintro rfl
    exact hne (P.part.refl x)
  have hsub : ({x, y} : Set Λ) ⊆ P.colorClass (P.color z) := by
    rw [hz]
    rintro w (rfl | rfl)
    · exact hx
    · exact hy
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hxy] at this

end Trichotomy

/-! ### The coloring of `Γ` an outcome carries -/

section AlignColor

variable {m : ℕ}

/-- §14.1, line 4: the colors of the coloring `(Δ₁, …, Δ_k)` that an outcome of
Theorem 9.2.3 carries.  In case (a) a color is the color of the colored partition together
with the size of the block (Proposition 7.1.3); in case (b) it is the answer to *"is this
vertex in the Johnson scheme?"*. -/
abbrev AlignColor : Type := (ℕ × ℕ) ⊕ Bool

/-- `↥(□Z) ≃ Γ` when the outcome lives on all of `Γ`. -/
def carEquiv {Z : Pt (SplitOutcomes (Fin m))} (h : Z.car = Set.univ) : ↥Z.car ≃ Fin m :=
  (Equiv.setCongr h).trans (Equiv.Set.univ (Fin m))

@[simp] theorem carEquiv_apply {Z : Pt (SplitOutcomes (Fin m))} (h : Z.car = Set.univ)
    (x : ↥Z.car) : (carEquiv h x : Fin m) = (x : Fin m) := rfl

theorem carEquiv_symm_apply {Z : Pt (SplitOutcomes (Fin m))} (h : Z.car = Set.univ)
    (γ : Fin m) (hγ : γ ∈ Z.car) : (carEquiv h).symm γ = ⟨γ, hγ⟩ := Subtype.ext rfl

open scoped Classical in
/-- §14.1, **line 4**: the coloring of `Γ` that an outcome of Theorem 9.2.3 carries. -/
noncomputable def alignColor (Z : Pt (SplitOutcomes (Fin m))) (γ : Fin m) : AlignColor :=
  match Z.obj with
  | Sum.inl P =>
      if h : γ ∈ Z.car then Sum.inl (P.equipartRefine.color ⟨γ, h⟩) else Sum.inl (0, 0)
  | Sum.inr _ => Sum.inr (decide (γ ∈ Z.car))

open scoped Classical in
/-- Case (a): the coloring is the refined coloring of the colored partition. -/
theorem alignColor_inl (s : Set (Fin m)) (P : ColoredPartition ↥s ℕ) {γ : Fin m}
    (hγ : γ ∈ s) :
    alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))) γ
      = Sum.inl (P.equipartRefine.color ⟨γ, hγ⟩) := by
  simp only [alignColor]
  rw [dif_pos hγ]

open scoped Classical in
/-- Case (b): the coloring is the two-coloring `(W, Γ ∖ W)`. -/
theorem alignColor_inr (s : Set (Fin m)) (J : (JohnsonSchemes (Fin m)).Obj s) (γ : Fin m) :
    alignColor (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) γ
      = Sum.inr (decide (γ ∈ s)) := by
  simp only [alignColor]

/-! ### Line 4: the coloring is canonical -/

/-- §14.1, **line 4**, *"canonical"*: an automorphism of the outcome preserves the coloring.

This is the hypothesis `hstab` of `Babai.isInvariant_omegaColorClass`, and hence what makes
the color classes of `Ω` invariant under `G₁ = ϕ⁻¹(Aut(X(x)))`.

*Proof.*  In case (b) the underlying set of the Johnson scheme is carried onto itself, which
is all the two-coloring says.  In case (a) a morphism of colored partitions preserves the
color and the blocks, hence also the refined coloring — that is Proposition 7.1.3's
functoriality (`Babai.equipartRefineFunc`). -/
theorem alignColor_aut (Z : Pt (SplitOutcomes (Fin m))) (π : Equiv.Perm (Fin m))
    (hcar : Z.car = π '' Z.car)
    (hiso : permHom π Z Z hcar ∈ (SplitOutcomes (Fin m)).IsoP Z Z) (γ : Fin m) :
    alignColor Z (π γ) = alignColor Z γ := by
  classical
  obtain ⟨s, o⟩ := Z
  have hmem : ∀ δ : Fin m, π δ ∈ s ↔ δ ∈ s := by
    intro δ
    constructor
    · intro hδ
      have : π δ ∈ π '' s := by rw [← hcar]; exact hδ
      obtain ⟨e, he, hee⟩ := this
      rwa [π.injective hee] at he
    · intro hδ
      have : π δ ∈ π '' s := ⟨δ, hδ, rfl⟩
      rw [← hcar] at this
      exact this
  cases o with
  | inr J =>
    have h := hmem γ
    simp only [alignColor_inr, h]
  | inl P =>
    by_cases hγ : γ ∈ s
    · have hπγ : π γ ∈ s := (hmem γ).2 hγ
      rw [alignColor_inl s P hπγ, alignColor_inl s P hγ]
      refine congrArg Sum.inl ?_
      -- `permHom π Z Z hcar` is a morphism of colored partitions, so it is a morphism of
      -- their refinements (Proposition 7.1.3)
      set f : Hom (ColoredPartitions (Fin m) ℕ) (⟨s, P⟩ : Pt (ColoredPartitions (Fin m) ℕ))
          (⟨s, P⟩ : Pt (ColoredPartitions (Fin m) ℕ)) :=
        ⟨permHom π (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))
          ⟨s, Sum.inl P⟩ hcar, hiso⟩ with hf
      have hmap := ((equipartRefineFunc (Fin m) ℕ).map f).2.1 (⟨γ, hγ⟩ : ↥s)
      have hval : ((permHom π (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))
          ⟨s, Sum.inl P⟩ hcar) (⟨γ, hγ⟩ : ↥s) : ↥s) = ⟨π γ, hπγ⟩ := Subtype.ext rfl
      rw [hf] at hmap
      show P.equipartRefine.color ⟨π γ, hπγ⟩ = P.equipartRefine.color ⟨γ, hγ⟩
      rw [← hval]
      exact hmap
    · have hπγ : π γ ∉ s := fun h => hγ ((hmem γ).1 h)
      simp only [alignColor]
      rw [dif_neg hπγ, dif_neg hγ]

end AlignColor

/-! ### Line 6: the dominant color class -/

section Dominant

variable {m : ℕ}

/-- The color classes of `Babai.alignColor`, as a `Finset` of `Γ`, are the color classes of
the colored partition, carried to `Γ`. -/
theorem card_colorSet_alignColor_inl {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) (j : ℕ × ℕ) :
    (colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inl j)).card = (P.equipartRefine.colorClass j).ncard := by
  classical
  set Z : Pt (SplitOutcomes (Fin m)) := ⟨s, Sum.inl P⟩ with hZ
  set e : ↥s ≃ Fin m := carEquiv (Z := Z) hs with he
  have hcoe : (↑(colorSet (alignColor Z) (Sum.inl j)) : Set (Fin m))
      = e '' (P.equipartRefine.colorClass j) := by
    ext γ
    have hγ : γ ∈ s := by rw [hs]; trivial
    constructor
    · intro hmem
      simp only [colorSet, Finset.coe_filter, Set.mem_setOf_eq] at hmem
      refine ⟨⟨γ, hγ⟩, ?_, rfl⟩
      have := hmem.2
      rw [alignColor_inl s P hγ, Sum.inl.injEq] at this
      exact this
    · rintro ⟨x, hx, rfl⟩
      simp only [colorSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      have hxv : ((e x : Fin m)) = (x : Fin m) := rfl
      have hx' : (x : Fin m) ∈ s := x.2
      rw [show (e x : Fin m) = (x : Fin m) from rfl, alignColor_inl s P hx']
      refine congrArg Sum.inl ?_
      rw [show (⟨(x : Fin m), hx'⟩ : ↥s) = x from Subtype.ext rfl]
      exact hx
  have hcard : (colorSet (alignColor Z) (Sum.inl j)).card
      = (↑(colorSet (alignColor Z) (Sum.inl j)) : Set (Fin m)).ncard :=
    (Set.ncard_coe_finset _).symm
  rw [hcard, hcoe, Set.ncard_image_of_injective _ e.injective]

/-- `|Γ| = m` read on the underlying set of an outcome that lives on all of `Γ`. -/
theorem card_car_eq {s : Set (Fin m)} (hs : s = Set.univ) :
    letI : Fintype ↥s := Fintype.ofFinite _
    Fintype.card ↥s = m := by
  letI : Fintype ↥s := Fintype.ofFinite _
  have h1 : Nat.card ↥s = s.ncard := Nat.card_coe_set_eq s
  rw [Nat.card_eq_fintype_card] at h1
  rw [h1, hs, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- §14.1, **line 7**: the structure the outcome puts on the dominant color class — a
nontrivial equipartition of it (case (a), line 7 (A)) or a Johnson scheme on it (case (b),
line 7 (B)). -/
def DominantStructure (Z : Pt (SplitOutcomes (Fin m))) (i : AlignColor) : Prop :=
  (∃ (P : ColoredPartition ↥Z.car ℕ) (j : ℕ × ℕ), Z.obj = Sum.inl P ∧ i = Sum.inl j ∧
      (∃ x y : ↥Z.car, P.equipartRefine.color x = j ∧ P.equipartRefine.color y = j ∧
        ¬ P.part y x) ∧
      (∀ z : ↥Z.car, P.equipartRefine.color z = j → 2 ≤ (P.block z).ncard)) ∨
  (i = Sum.inr true ∧ (∃ J : (JohnsonSchemes (Fin m)).Obj Z.car, Z.obj = Sum.inr J) ∧
    ((colorSet (alignColor Z) i : Finset (Fin m)) : Set (Fin m)) = Z.car)

/-- The class of the color `true` in case (b) is the vertex set of the Johnson scheme. -/
theorem colorSet_alignColor_inr (s : Set (Fin m)) (J : (JohnsonSchemes (Fin m)).Obj s) :
    ((colorSet (alignColor (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inr true) : Finset (Fin m)) : Set (Fin m)) = s := by
  classical
  ext γ
  simp only [colorSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
    alignColor_inr s J γ, Sum.inr.injEq, decide_eq_true_eq]

/-- Colors of the other shape do not occur in case (a). -/
theorem colorSet_alignColor_inl_other (s : Set (Fin m)) (P : ColoredPartition ↥s ℕ)
    (b : Bool) :
    colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inr b) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun γ hγ => ?_
  simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  by_cases h : γ ∈ s
  · rw [alignColor_inl s P h] at hγ
    simp at hγ
  · simp only [alignColor, dif_neg h] at hγ
    simp at hγ

/-- Colors of the other shape do not occur in case (b). -/
theorem colorSet_alignColor_inr_other (s : Set (Fin m)) (J : (JohnsonSchemes (Fin m)).Obj s)
    (j : ℕ × ℕ) :
    colorSet (alignColor (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) (Sum.inl j) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun γ hγ => ?_
  simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [alignColor_inr s J γ] at hγ
  simp at hγ

/-- §14.1, **lines 4-7**: an outcome of Theorem 9.2.3 either colors `Γ` with classes of at
most `αm` vertices — and then the Chain Rule of line 5 runs on classes of `Ω` of at most
`max(2/3, α)·n` points (`Babai.ncard_omegaColorClass_le_of_alpha`) — or it has a dominant
color class (line 6) carrying an extra structure (line 7).

*Proof.*  In case (a) the trichotomy
`Babai.ColoredPartition.alphaPartition_trichotomy` leaves, for each color, either a class of
at most half of `Γ` — which is at most `αm` because `α ≥ 1/2` — or a class of at most `αm`,
or a class with two blocks; a class with two blocks that is also dominant is the second
alternative, and if there is none, every class is at most `αm`.  In case (b) the vertex set
`W` of the Johnson scheme has `|W| ≥ αm > m/2`, so its color is dominant — unless `m = 0`,
when every class is empty. -/
theorem alignColor_cases {α : ℝ} (hα : 1 / 2 < α) {Z : Pt (SplitOutcomes (Fin m))}
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) Z) :
    (∀ i : AlignColor, ((colorSet (alignColor Z) i).card : ℝ) ≤ α * m) ∨
      ∃ i : AlignColor, m < 2 * (colorSet (alignColor Z) i).card ∧
        DominantStructure Z i := by
  classical
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  obtain ⟨s, o⟩ := Z
  cases o with
  | inr J =>
    -- case (b): the vertex set of the Johnson scheme is the dominant class
    obtain ⟨hsub, hbig⟩ := hZ
    have hcard : ((colorSet (alignColor (⟨s, Sum.inr J⟩ :
        Pt (SplitOutcomes (Fin m)))) (Sum.inr true)).card : ℝ) = (s.ncard : ℝ) := by
      have := colorSet_alignColor_inr s J
      rw [← Set.ncard_coe_finset, this]
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hbig
    rcases Nat.eq_zero_or_pos m with hmz | hmpos
    · refine Or.inl fun i => ?_
      have h := Finset.card_le_univ (colorSet (alignColor (⟨s, Sum.inr J⟩ :
        Pt (SplitOutcomes (Fin m)))) i)
      rw [Fintype.card_fin] at h
      have h0 : (colorSet (alignColor (⟨s, Sum.inr J⟩ :
        Pt (SplitOutcomes (Fin m)))) i).card = 0 := by omega
      rw [h0]
      simpa using mul_nonneg hα0 hm0
    · refine Or.inr ⟨Sum.inr true, ?_, Or.inr ⟨rfl, ⟨J, rfl⟩, colorSet_alignColor_inr s J⟩⟩
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have h1 : (m : ℝ) < 2 * (s.ncard : ℝ) := by nlinarith
      have h2 : (m : ℝ) < 2 * ((colorSet (alignColor (⟨s, Sum.inr J⟩ :
          Pt (SplitOutcomes (Fin m)))) (Sum.inr true)).card : ℝ) := by rw [hcard]; exact h1
      exact_mod_cast h2
  | inl P =>
    -- case (a): the colored `α`-partition
    obtain ⟨hs, hP⟩ := hZ
    letI : Fintype ↥s := Fintype.ofFinite _
    have hcardS : Fintype.card ↥s = m := card_car_eq hs
    have hPa : P.IsAlphaPartition α := hP
    have hcard : ∀ j : ℕ × ℕ, (colorSet (alignColor (⟨s, Sum.inl P⟩ :
        Pt (SplitOutcomes (Fin m)))) (Sum.inl j)).card
        = (P.equipartRefine.colorClass j).ncard :=
      fun j => card_colorSet_alignColor_inl hs P j
    have hPequi : P.equipartRefine.IsAlphaPartition α := by
      refine ⟨P.isAdmissible_equipartRefine hPa.1, ?_⟩
      rw [ColoredPartition.rho_equipartRefine]
      exact hPa.2
    by_cases hdom : ∃ j : ℕ × ℕ, m < 2 * (P.equipartRefine.colorClass j).ncard ∧
        ∃ x y : ↥s, P.equipartRefine.color x = j ∧ P.equipartRefine.color y = j ∧
          ¬ P.part y x
    · obtain ⟨j, hj, x, y, hx, hy, hxy⟩ := hdom
      refine Or.inr ⟨Sum.inl j, by rw [hcard j]; exact hj, Or.inl ⟨P, j, rfl, rfl,
        ⟨x, y, hx, hy, hxy⟩, fun z hz => ?_⟩⟩
      have := P.equipartRefine.two_le_ncard_block_of_two_blocks
        (P.isAdmissible_equipartRefine hPa.1) hx hy hxy hz
      rwa [ColoredPartition.block_equipartRefine] at this
    · refine Or.inl fun i => ?_
      cases i with
      | inr b => rw [colorSet_alignColor_inl_other s P b]; simpa using mul_nonneg hα0 hm0
      | inl j =>
        rw [hcard j]
        push Not at hdom
        rcases P.equipartRefine.alphaPartition_trichotomy hPequi j with h | h | h
        · -- not dominant: at most `m/2 ≤ αm`
          rw [hcardS] at h
          have : 2 * ((P.equipartRefine.colorClass j).ncard : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast (by omega : 2 * (P.equipartRefine.colorClass j).ncard ≤ m)
          nlinarith
        · -- two blocks, so by `hdom` not dominant
          obtain ⟨x, y, hx, hy, hxy⟩ := h
          have hnd := hdom j
          have hnd' : ¬ m < 2 * (P.equipartRefine.colorClass j).ncard := by
            intro hlt
            exact hxy (hnd hlt x y hx hy)
          have : 2 * ((P.equipartRefine.colorClass j).ncard : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast (by omega : 2 * (P.equipartRefine.colorClass j).ncard ≤ m)
          nlinarith
        · rwa [hcardS] at h

end Dominant



/-! ### Line 4: the index type of the coloring -/

section Idx

variable {m : ℕ}

/-- §14.1, line 4: the colors that actually occur.  This is the index type `ι` of
`Babai.omegaColorClass`, which has to be finite: `Babai.AlignColor` itself is infinite, but
a coloring of `Γ` uses only finitely many of its values.  It is canonical, because an
isomorphism of outcomes preserves `Babai.alignColor` (`Babai.alignColor_aut`). -/
abbrev AlignIdx (Z : Pt (SplitOutcomes (Fin m))) : Type := ↥(Set.range (alignColor Z))

/-- §14.1, line 4: the coloring of `Γ`, with the colors that occur for its index type. -/
noncomputable def alignIdx (Z : Pt (SplitOutcomes (Fin m))) : Fin m → AlignIdx Z :=
  Set.rangeFactorization (alignColor Z)

@[simp] theorem alignIdx_coe (Z : Pt (SplitOutcomes (Fin m))) (γ : Fin m) :
    ((alignIdx Z γ : AlignIdx Z) : AlignColor) = alignColor Z γ := rfl

theorem nonempty_alignIdx {Z : Pt (SplitOutcomes (Fin m))} (h : 0 < m) :
    Nonempty (AlignIdx Z) := ⟨alignIdx Z ⟨0, h⟩⟩

/-- §14.1, line 4, *"canonical"*, for `Babai.alignIdx`. -/
theorem alignIdx_aut (Z : Pt (SplitOutcomes (Fin m))) (π : Equiv.Perm (Fin m))
    (hcar : Z.car = π '' Z.car)
    (hiso : permHom π Z Z hcar ∈ (SplitOutcomes (Fin m)).IsoP Z Z) (γ : Fin m) :
    alignIdx Z (π γ) = alignIdx Z γ :=
  Subtype.ext (alignColor_aut Z π hcar hiso γ)

/-- The color classes of `Babai.alignIdx` are those of `Babai.alignColor`. -/
theorem colorSet_alignIdx (Z : Pt (SplitOutcomes (Fin m))) (i : AlignIdx Z) :
    colorSet (alignIdx Z) i = colorSet (alignColor Z) (i : AlignColor) := by
  ext γ
  simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => by rw [← alignIdx_coe Z γ, h], fun h => Subtype.ext (by rw [alignIdx_coe]; exact h)⟩

end Idx

/-! ### Lines 4 and 6: the list of color classes of `Ω`, dominant window first -/

section ClassList

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
  {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- §14.1, **line 5**: the list of color classes of `Ω` the Chain Rule runs over. -/
noncomputable def omegaColorClasses (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι) :
    List (Set Ω) :=
  (Finset.univ.image fun u : Ω => omegaColorClass ϕ c (omegaColor ϕ c u)).toList

open scoped Classical in
theorem mem_omegaColorClasses {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι} {S : Set Ω} :
    S ∈ omegaColorClasses ϕ c ↔ ∃ u : Ω, S = omegaColorClass ϕ c (omegaColor ϕ c u) := by
  classical
  rw [omegaColorClasses, Finset.mem_toList, Finset.mem_image]
  exact ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ u, hu.symm⟩⟩

open scoped Classical in
/-- Every class in the list is a class. -/
theorem forall_mem_omegaColorClasses {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι}
    {P : Set Ω → Prop} (h : ∀ v : ι → ℕ, P (omegaColorClass ϕ c v)) :
    ∀ S ∈ omegaColorClasses ϕ c, P S := by
  intro S hS
  obtain ⟨u, rfl⟩ := mem_omegaColorClasses.1 hS
  exact h _

open scoped Classical in
/-- §14.1, line 4: *"`Ω` is the disjoint union of the `Ω_i`"* — the part the Chain Rule
needs. -/
theorem iUnion_omegaColorClasses (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι) :
    (⋃ S ∈ omegaColorClasses (Ω := Ω) ϕ c, S) = (Set.univ : Set Ω) := by
  refine Set.eq_univ_of_forall fun u => ?_
  exact Set.mem_biUnion (mem_omegaColorClasses.2 ⟨u, rfl⟩) (omegaColorClass_cover ϕ c u)

open scoped Classical in
/-- §14.1, **line 6**: the same list with the dominant window first, so that the Chain Rule
starts with it. -/
noncomputable def omegaColorClassesDomFirst (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι)
    (S₀ : Set Ω) : List (Set Ω) :=
  S₀ :: (omegaColorClasses ϕ c).erase S₀

theorem omegaColorClassesDomFirst_eq_cons (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι)
    (S₀ : Set Ω) :
    omegaColorClassesDomFirst ϕ c S₀ = S₀ :: (omegaColorClasses ϕ c).erase S₀ := rfl

open scoped Classical in
theorem omegaColorClassesDomFirst_perm {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι}
    {S₀ : Set Ω} (h : S₀ ∈ omegaColorClasses ϕ c) :
    (omegaColorClassesDomFirst ϕ c S₀).Perm (omegaColorClasses ϕ c) :=
  (List.perm_cons_erase h).symm

open scoped Classical in
theorem mem_omegaColorClassesDomFirst {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι}
    {S₀ S : Set Ω} (h : S₀ ∈ omegaColorClasses ϕ c) :
    S ∈ omegaColorClassesDomFirst ϕ c S₀ ↔ S ∈ omegaColorClasses ϕ c :=
  (omegaColorClassesDomFirst_perm h).mem_iff

open scoped Classical in
theorem length_omegaColorClassesDomFirst {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι}
    {S₀ : Set Ω} (h : S₀ ∈ omegaColorClasses ϕ c) :
    (omegaColorClassesDomFirst ϕ c S₀).length = (omegaColorClasses (Ω := Ω) ϕ c).length :=
  (omegaColorClassesDomFirst_perm h).length_eq

open scoped Classical in
theorem iUnion_omegaColorClassesDomFirst {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι}
    {S₀ : Set Ω} (h : S₀ ∈ omegaColorClasses ϕ c) :
    (⋃ S ∈ omegaColorClassesDomFirst ϕ c S₀, S) = (Set.univ : Set Ω) := by
  rw [← iUnion_omegaColorClasses ϕ c]
  ext u
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨S, hS, hu⟩ => ⟨S, (mem_omegaColorClassesDomFirst h).1 hS, hu⟩,
    fun ⟨S, hS, hu⟩ => ⟨S, (mem_omegaColorClassesDomFirst h).2 hS, hu⟩⟩

end ClassList

/-! ### From the action of `S(Γ)` on the outcomes to line 4's canonicity -/

section Smul

variable {Γ : Type} {C : Cat.{0, 0} Γ} [MulAction (Equiv.Perm Γ) (Pt C)]

/-- A permutation that fixes an object of a transportable category is an automorphism of
it. -/
theorem isoP_of_smul_eq (hC : IsCatAction C) {π : Equiv.Perm Γ} {Z : Pt C} (h : π • Z = Z) :
    ∃ hcar : Z.car = π '' Z.car, permHom π Z Z hcar ∈ C.IsoP Z Z := by
  have h1 : Z.car = π '' Z.car := by rw [← hC.car_smul π Z, h]
  refine ⟨h1, ?_⟩
  have key : ∀ (W : Pt C) (_ : W = Z) (hc : W.car = π '' Z.car),
      permHom π Z W hc ∈ C.IsoP Z W → permHom π Z Z h1 ∈ C.IsoP Z Z := by
    rintro W rfl hc hmem
    exact hmem
  exact key (π • Z) h (hC.car_smul π Z) (hC.iso_smul π Z)

end Smul

section Invariance

variable {m : ℕ} [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

/-- §14.1, line 4, *"canonical"*, in the form the Chain Rule uses: a permutation of `Γ` that
fixes the outcome preserves its coloring. -/
theorem alignIdx_smul (hK : IsCatAction (SplitOutcomes (Fin m)))
    {π : Equiv.Perm (Fin m)} {Z : Pt (SplitOutcomes (Fin m))} (h : π • Z = Z) (γ : Fin m) :
    alignIdx Z (π γ) = alignIdx Z γ := by
  obtain ⟨hcar, hiso⟩ := isoP_of_smul_eq hK h
  exact alignIdx_aut Z π hcar hiso γ

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}

/-- §14.1, **lines 4 and 5**: the color classes of `Ω` are invariant under
`G₁ = ϕ⁻¹(Aut(X'))`, which is the hypothesis `hinv` of
`Babai.run_designAlignReduction`. -/
theorem isInvariant_omegaColorClass_alignIdx (hK : IsCatAction (SplitOutcomes (Fin m)))
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (Z : Pt (SplitOutcomes (Fin m))) (v : AlignIdx Z → ℕ) :
    IsInvariant (preimageSubgroup ϕ (structAut Z))
      (omegaColorClass (Ω := Ω) ϕ (alignIdx Z) v) := by
  refine isInvariant_omegaColorClass ϕ hϕ hk (alignIdx Z) v _
    (preimageSubgroup_le ϕ (structAut Z)) ?_
  intro τ hτ γ
  obtain ⟨hτG, hτA⟩ := mem_preimageSubgroup.1 hτ
  exact alignIdx_smul hK (mem_structAut.1 hτA) γ

/-- §14.1, lines 4 and 5, for the whole list of classes. -/
theorem isInvariant_omegaColorClasses_alignIdx (hK : IsCatAction (SplitOutcomes (Fin m)))
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (Z : Pt (SplitOutcomes (Fin m))) :
    ∀ Δ ∈ omegaColorClasses (Ω := Ω) ϕ (alignIdx Z),
      IsInvariant (preimageSubgroup ϕ (structAut Z)) Δ :=
  forall_mem_omegaColorClasses fun v =>
    isInvariant_omegaColorClass_alignIdx hK ϕ hϕ hk Z v

/-- §14.1, lines 4 and 5, for the list of classes with the dominant window first. -/
theorem isInvariant_omegaColorClassesDomFirst_alignIdx
    (hK : IsCatAction (SplitOutcomes (Fin m))) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (Z : Pt (SplitOutcomes (Fin m))) {S₀ : Set Ω}
    (hS₀ : S₀ ∈ omegaColorClasses (Ω := Ω) ϕ (alignIdx Z)) :
    ∀ Δ ∈ omegaColorClassesDomFirst (Ω := Ω) ϕ (alignIdx Z) S₀,
      IsInvariant (preimageSubgroup ϕ (structAut Z)) Δ := by
  intro Δ hΔ
  exact isInvariant_omegaColorClasses_alignIdx hK ϕ hϕ hk Z Δ
    ((mem_omegaColorClassesDomFirst hS₀).1 hΔ)

/-- §14.1, **line 5, the progress** in the first alternative of
`Babai.alignColor_cases`: if the outcome has no dominant color class then every class of
`Ω` has at most `max(2/3, α)·n` points.  This is Corollary 7.2.2 lifted to `Ω`
(`Babai.ncard_omegaColorClass_le_of_alpha`). -/
theorem ncard_omegaColorClasses_le_of_alpha (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht2 : 2 ≤ t) (h2t : 2 * t ≤ m)
    (Z : Pt (SplitOutcomes (Fin m))) {α : ℝ} (hα1 : α < 1)
    (hsmall : ∀ i : AlignColor, ((colorSet (alignColor Z) i).card : ℝ) ≤ α * m) :
    ∀ Δ ∈ omegaColorClasses (Ω := Ω) ϕ (alignIdx Z),
      (Δ.ncard : ℝ) ≤ max (2 / 3) α * (Fintype.card Ω : ℝ) := by
  haveI : Nonempty (AlignIdx Z) := nonempty_alignIdx (by omega)
  refine forall_mem_omegaColorClasses fun v => ?_
  refine ncard_omegaColorClass_le_of_alpha hG ϕ hϕ hk hm3 ht ht2 h2t (alignIdx Z) hα1
    (fun i => ?_) v
  rw [colorSet_alignIdx]
  exact hsmall _

/-- §14.1-14.2, **line 5, the progress of Eq. (72)** in the first alternative of
`Babai.alignColor_cases`: if the outcome has no dominant color class then *every* color
class of `Ω` has at most `2n/3` points, which is the hypothesis `hΔs` of
`Babai.decreases_designAlignReduction`.

`3α² ≤ 2` holds for both thresholds the paper uses, `α = 3/4` (Theorem 9.2.3) and `α = 4/5`
(Sec. 13); see `Babai.three_mul_card_tupleClass_le_of_sq`. -/
theorem three_mul_ncard_omegaColorClasses_le (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht2 : 2 ≤ t) (h2t : 2 * t ≤ m)
    (Z : Pt (SplitOutcomes (Fin m))) {α : ℝ} (hα0 : 0 ≤ α) (hα2 : 3 * α ^ 2 ≤ 2)
    (hsmall : ∀ i : AlignColor, ((colorSet (alignColor Z) i).card : ℝ) ≤ α * m) :
    ∀ Δ ∈ omegaColorClasses (Ω := Ω) ϕ (alignIdx Z),
      3 * Δ.ncard ≤ 2 * Fintype.card Ω := by
  haveI : Nonempty (AlignIdx Z) := nonempty_alignIdx (by omega)
  refine forall_mem_omegaColorClasses fun v => ?_
  refine three_mul_ncard_omegaColorClass_le_of_sq hG ϕ hϕ hk hm3 ht ht2 h2t (alignIdx Z)
    hα0 hα2 (fun i => ?_) v
  rw [colorSet_alignIdx]
  exact hsmall _

/-- §14.1-14.2, **line 5, the progress of Eq. (72) at the threshold `4/5`** in the first
alternative of `Babai.alignColor_cases`: if the outcome has no dominant color class then
every color class of `Ω` has at most `4n/5` points.

Unlike `Babai.three_mul_ncard_omegaColorClasses_le` this needs only `t ≥ 1`, which is what
lines 5–7a have: Lemma 7.2.1 (b) gives `α^t ≤ α` for every `t ≥ 1`, and `5α ≤ 4` holds for
the threshold `α = 4/5` of Theorem 13.2.1 and for the `α = 3/4` of Theorem 9.2.3.  See
the corrected paper entry on Sec. 15 lines 5–7a and Sec. 14.2 Eqs. (72)–(73). -/
theorem five_mul_ncard_omegaColorClasses_le (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m)
    (Z : Pt (SplitOutcomes (Fin m))) {α : ℝ} (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4)
    (hsmall : ∀ i : AlignColor, ((colorSet (alignColor Z) i).card : ℝ) ≤ α * m) :
    ∀ Δ ∈ omegaColorClasses (Ω := Ω) ϕ (alignIdx Z),
      5 * Δ.ncard ≤ 4 * Fintype.card Ω := by
  haveI : Nonempty (AlignIdx Z) := nonempty_alignIdx (by omega)
  refine forall_mem_omegaColorClasses fun v => ?_
  refine five_mul_ncard_omegaColorClass_le_of_le hG ϕ hϕ hk hm3 ht ht1 h2t (alignIdx Z)
    hα0 hα45 (fun i => ?_) v
  rw [colorSet_alignIdx]
  exact hsmall _

end Invariance

end Babai
