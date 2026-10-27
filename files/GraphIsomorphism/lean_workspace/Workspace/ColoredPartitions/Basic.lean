/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 7.1: Colored α-partitions.
-/
import Workspace.Functors.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Archimedean

/-!
# §7.1 Breaking symmetry: colored α-partitions

## Numbering map

| Paper | Lean |
|---|---|
| Definition 7.1.1, colored partition | `Babai.ColoredPartition` |
| Definition 7.1.1, colored equipartition | `Babai.ColoredPartition.IsEquipartition` |
| Definition 7.1.1, admissible | `Babai.ColoredPartition.IsAdmissible` |
| Definition 7.1.1, `ρ(Π)` | `Babai.ColoredPartition.rho` |
| Definition 7.1.1, colored `α`-partition | `Babai.ColoredPartition.IsAlphaPartition` |
| §7.1, the category `ColoredPartitions` | `Babai.ColoredPartitions` |
| Definition 7.1.2 | `Babai.IsCanonicalColoredPartition` |
| Proposition 7.1.3 | `Babai.ColoredPartition.equipartRefine`, `.isEquipartition_equipartRefine`, `.block_equipartRefine`, `.isAdmissible_equipartRefine`, `Babai.equipartRefineFunc` |
| Observation 7.1.4 | `Babai.ColoredPartition.isAlphaPartition_of` |
-/

universe u v

namespace Babai

/-- Definition 7.1.1.  *"A colored partition of a set `Ω` is a coloring of the elements of
`Ω` along with a partition of each color class."*

A partition of each color class is the same thing as an equivalence relation on `Ω` whose
classes lie inside the color classes, which is the field `part_le_color`. -/
structure ColoredPartition (Ω : Type u) (κ : Type v) where
  /-- The coloring of the elements of `Ω`. -/
  color : Ω → κ
  /-- The partition of each color class, as an equivalence relation on `Ω`. -/
  part : Setoid Ω
  /-- Each block lies inside a color class. -/
  part_le_color : ∀ {x y : Ω}, part x y → color x = color y

namespace ColoredPartition

variable {Ω : Type u} {κ : Type v} (P : ColoredPartition Ω κ)

@[ext] theorem ext {P P' : ColoredPartition Ω κ} (hc : P.color = P'.color)
    (hp : P.part = P'.part) : P = P' := by
  revert hc hp
  obtain ⟨c, p, hcp⟩ := P
  obtain ⟨c', p', hcp'⟩ := P'
  intro hc hp
  simp only at hc hp
  subst hc; subst hp; rfl

/-- The color class `C_i` of the color `c`. -/
def colorClass (c : κ) : Set Ω := {x | P.color x = c}

/-- The block `B_{ij}` of the colored partition containing `x`. -/
def block (x : Ω) : Set Ω := {y | P.part y x}

theorem mem_block_self (x : Ω) : x ∈ P.block x := P.part.refl x

theorem block_subset_colorClass (x : Ω) : P.block x ⊆ P.colorClass (P.color x) :=
  fun _ hy => P.part_le_color hy

theorem colorClass_subset_colorClass {x y : Ω} (h : P.color x = P.color y) :
    P.colorClass (P.color x) = P.colorClass (P.color y) := by rw [h]

theorem block_eq_of_part {x y : Ω} (h : P.part x y) : P.block x = P.block y :=
  Set.ext fun _ => ⟨fun hz => P.part.trans hz h, fun hz => P.part.trans hz (P.part.symm h)⟩

theorem block_disjoint {x y : Ω} (h : ¬ P.part x y) : Disjoint (P.block x) (P.block y) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h (P.part.trans (P.part.symm hz) hz')

/-- Definition 7.1.1.  *"We say that this is a colored equipartition if all blocks within
the same color class have equal size."* -/
def IsEquipartition : Prop :=
  ∀ x y : Ω, P.color x = P.color y → (P.block x).ncard = (P.block y).ncard

/-- Definition 7.1.1.  *"We say that `Π` is admissible if for each color class `C_i` of
size `|C_i| ≥ 2`, all the blocks of `C_i` have size `|B_{ij}| ≥ 2`."* -/
def IsAdmissible : Prop :=
  ∀ x : Ω, 2 ≤ (P.colorClass (P.color x)).ncard → 2 ≤ (P.block x).ncard

/-- Definition 7.1.1.  *"Let `ρ(Π) = max_{i,j} |B_{ij}|`."* -/
noncomputable def rho [Fintype Ω] : ℕ := Finset.univ.sup fun x => (P.block x).ncard

theorem ncard_block_le_rho [Fintype Ω] (x : Ω) : (P.block x).ncard ≤ P.rho :=
  Finset.le_sup (f := fun x => (P.block x).ncard) (Finset.mem_univ x)

theorem rho_le [Fintype Ω] {n : ℕ} (h : ∀ x : Ω, (P.block x).ncard ≤ n) : P.rho ≤ n :=
  Finset.sup_le fun x _ => h x

/-- Definition 7.1.1.  *"For `0 < α ≤ 1`, a colored `α`-partition is an admissible colored
partition `Π` such that `ρ(Π) ≤ αn` where `n = |Ω|`."*  (The bounds `0 < α ≤ 1` are
hypotheses on `α` in the places where the notion is used, not part of the condition on
`Π`.) -/
def IsAlphaPartition [Fintype Ω] (α : ℝ) : Prop :=
  P.IsAdmissible ∧ (P.rho : ℝ) ≤ α * (Fintype.card Ω)

end ColoredPartition

/-! ### The category `ColoredPartitions` -/

/-- §7.1.  *"The category `ColoredPartitions` has as its objects sets with a colored
partition.  The morphisms are the bijection that preserve color and preserve the given
equivalence relation (partition) in each color class."* -/
def ColoredPartitions (Ω : Type u) (κ : Type v) : Cat.{u, max u v} Ω where
  Obj s := ColoredPartition ↥s κ
  Iso P P' := {f | (∀ x, P'.color (f x) = P.color x) ∧ ∀ x y, P.part x y ↔ P'.part (f x) (f y)}
  refl_mem _ := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
  symm_mem := by
    rintro s t P P' f ⟨hc, hp⟩
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · rw [← hc (f.symm x), Equiv.apply_symm_apply]
    · rw [hp (f.symm x) (f.symm y), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  trans_mem := by
    rintro s t r P P' P'' f g ⟨hc, hp⟩ ⟨hc', hp'⟩
    exact ⟨fun x => by rw [Equiv.trans_apply, hc', hc],
      fun x y => by rw [Equiv.trans_apply, Equiv.trans_apply, hp x y, hp']⟩
  faithful := by
    rintro s P P' ⟨hc, hp⟩
    exact ColoredPartition.ext (funext fun x => (hc x).symm) (Setoid.ext fun x y => hp x y)

/-- Definition 7.1.2.  *"A canonical colored partition of objects of a category `C` is a
canonical embedding of objects from the category `ColoredPartitions` onto the objects of
`C`."* -/
def IsCanonicalColoredPartition {Ω : Type u} {κ : Type v} (C : Cat.{u, v} Ω)
    (F : Func C (ColoredPartitions Ω κ)) : Prop :=
  F.IsCanonicalEmbeddingOnto

namespace ColoredPartition

variable {Ω : Type u} {κ : Type v} (P : ColoredPartition Ω κ)

/-! ### Proposition 7.1.3 -/

/-- Proposition 7.1.3.  *"Given a colored partition, one can canonically refine it to a
colored equipartition."*  Proof: *"Encode the size of each block in the color of its
elements."* -/
noncomputable def equipartRefine : ColoredPartition Ω (κ × ℕ) where
  color x := (P.color x, (P.block x).ncard)
  part := P.part
  part_le_color h := by
    rw [Prod.mk.injEq]
    exact ⟨P.part_le_color h, by rw [P.block_eq_of_part h]⟩

/-- Proposition 7.1.3.  *"the blocks will not change"*. -/
@[simp] theorem block_equipartRefine (x : Ω) : P.equipartRefine.block x = P.block x := rfl

/-- Proposition 7.1.3.  *"Here refinement means refining the colors"*: the new coloring
determines the old one. -/
theorem color_equipartRefine (x : Ω) : (P.equipartRefine.color x).1 = P.color x := rfl

/-- Proposition 7.1.3.  The refinement is a colored equipartition. -/
theorem isEquipartition_equipartRefine : P.equipartRefine.IsEquipartition := by
  intro x y h
  have := congrArg Prod.snd h
  simpa using this

/-- Proposition 7.1.3.  *"so if the partition was admissible, it remains admissible."*

The new color classes are contained in the old ones.  A new color class of size `≥ 2` is
contained in an old color class of size `≥ 2`, so admissibility of `Π` applies, and the
blocks are the same. -/
theorem isAdmissible_equipartRefine [Finite Ω] (h : P.IsAdmissible) : P.equipartRefine.IsAdmissible := by
  intro x hx
  refine h x (le_trans hx (Set.ncard_le_ncard ?_ (Set.toFinite _)))
  intro y hy
  exact congrArg Prod.fst hy

/-- Proposition 7.1.3.  `ρ` is unchanged, the blocks being unchanged. -/
@[simp] theorem rho_equipartRefine [Fintype Ω] : P.equipartRefine.rho = P.rho := rfl

end ColoredPartition

/-- Proposition 7.1.3.  The refinement is *canonical*: it is the object map of a functor
`ColoredPartitions → ColoredPartitions`, which moreover is a canonical embedding onto, so
it is a canonical colored partition of the objects of `ColoredPartitions` in the sense of
Definition 7.1.2.  (A morphism preserves the coloring and the blocks, hence also the
refined coloring "old color together with the size of the block".) -/
noncomputable def equipartRefineFunc (Ω : Type u) (κ : Type v) :
    Func (ColoredPartitions Ω κ) (ColoredPartitions Ω (κ × ℕ)) where
  obj X := ⟨X.car, X.obj.equipartRefine⟩
  map {X Y} f := by
    refine ⟨f.1, fun x => ?_, fun x y => f.2.2 x y⟩
    have himg : Y.obj.block (f.1 x) = f.1 '' (X.obj.block x) := by
      ext z
      constructor
      · intro hz
        refine ⟨f.1.symm z, ?_, by simp⟩
        have hz' : Y.obj.part (f.1 (f.1.symm z)) (f.1 x) := by simpa using hz
        exact (f.2.2 (f.1.symm z) x).2 hz'
      · rintro ⟨w, hw, rfl⟩
        exact (f.2.2 w x).1 hw
    have hblock : (Y.obj.block (f.1 x)).ncard = (X.obj.block x).ncard := by
      rw [himg, Set.ncard_image_of_injective _ f.1.injective]
    exact Prod.ext (f.2.1 x) hblock
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem isCanonicalColoredPartition_equipartRefineFunc (Ω : Type u) (κ : Type v) :
    (equipartRefineFunc Ω κ).IsCanonicalEmbeddingOnto where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl
  car_eq _ := rfl

namespace ColoredPartition

variable {Ω : Type u} {κ : Type v} [Fintype Ω] (P : ColoredPartition Ω κ)

/-! ### Observation 7.1.4 -/

theorem ncard_colorClass_le (c : κ) : (P.colorClass c).ncard ≤ Fintype.card Ω := by
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using
    Set.ncard_le_ncard (Set.subset_univ (P.colorClass c)) (Set.toFinite _)

theorem ncard_colorClass_add_ncard_colorClass_le {c c' : κ} (h : c ≠ c') :
    (P.colorClass c).ncard + (P.colorClass c').ncard ≤ Fintype.card Ω := by
  have hdisj : Disjoint (P.colorClass c) (P.colorClass c') := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact h (hx ▸ hx'.symm ▸ rfl)
  rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using
    Set.ncard_le_ncard (Set.subset_univ (P.colorClass c ∪ P.colorClass c')) (Set.toFinite _)

/-- §7.1.  *"the unique color-class of size `> n/2`"*: there is at most one such class. -/
theorem colorClass_dominant_unique {c c' : κ}
    (hc : Fintype.card Ω < 2 * (P.colorClass c).ncard)
    (hc' : Fintype.card Ω < 2 * (P.colorClass c').ncard) : c = c' := by
  by_contra h
  have := P.ncard_colorClass_add_ncard_colorClass_le h
  omega

/-- If two distinct blocks lie in one color class, each has at most half the size of that
class. -/
theorem two_mul_ncard_block_le {x y : Ω} (hxy : ¬ P.part y x) (hc : P.color y = P.color x)
    (hequi : P.IsEquipartition) :
    2 * (P.block x).ncard ≤ (P.colorClass (P.color x)).ncard := by
  have hsub : P.block x ∪ P.block y ⊆ P.colorClass (P.color x) := by
    refine Set.union_subset (P.block_subset_colorClass x) ?_
    rw [← hc]; exact P.block_subset_colorClass y
  have hdisj : Disjoint (P.block x) (P.block y) := P.block_disjoint fun h => hxy (P.part.symm h)
  have heq : (P.block y).ncard = (P.block x).ncard := hequi y x hc
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), heq] at this
  omega

/-- Observation 7.1.4.  *"Let `α ≥ 1/2`.  A colored equipartition is an `α`-partition if
either each color class has size `≤ αn`, or the unique color-class of size `> n/2` (the
'dominant color class') is nontrivially partitioned (at least two blocks, the blocks have
size `≥ 2`)."*

Admissibility is part of being a colored `α`-partition (Definition 7.1.1) and does not
follow from the stated hypotheses, so it is assumed here; see the corrected paper. -/
theorem isAlphaPartition_of {α : ℝ} (hα : 1 / 2 ≤ α) (hequi : P.IsEquipartition)
    (hadm : P.IsAdmissible)
    (h : (∀ c : κ, ((P.colorClass c).ncard : ℝ) ≤ α * Fintype.card Ω) ∨
      (∃ x : Ω, Fintype.card Ω < 2 * (P.colorClass (P.color x)).ncard ∧
        ∃ y : Ω, P.color y = P.color x ∧ ¬ P.part y x)) :
    P.IsAlphaPartition α := by
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  refine ⟨hadm, ?_⟩
  have key : ∀ z : Ω, ((P.block z).ncard : ℝ) ≤ α * Fintype.card Ω := by
    intro z
    rcases h with h | ⟨x, hx, y, hcy, hxy⟩
    · refine le_trans ?_ (h (P.color z))
      exact_mod_cast Set.ncard_le_ncard (P.block_subset_colorClass z) (Set.toFinite _)
    · -- the dominant class is nontrivially partitioned
      have hhalf : 2 * (P.block z).ncard ≤ Fintype.card Ω := by
        by_cases hz : P.color z = P.color x
        · -- `z` lies in the dominant class, which has at least two blocks, and all its
          -- blocks have the same size because `P` is an equipartition
          have h1 : 2 * (P.block x).ncard ≤ (P.colorClass (P.color x)).ncard :=
            P.two_mul_ncard_block_le hxy hcy hequi
          have hzx : (P.block z).ncard = (P.block x).ncard := hequi z x hz
          have h2 : (P.colorClass (P.color x)).ncard ≤ Fintype.card Ω :=
            P.ncard_colorClass_le _
          omega
        · have h1 : (P.block z).ncard ≤ (P.colorClass (P.color z)).ncard :=
            Set.ncard_le_ncard (P.block_subset_colorClass z) (Set.toFinite _)
          have h2 := P.ncard_colorClass_add_ncard_colorClass_le (c := P.color z)
            (c' := P.color x) hz
          omega
      have : ((P.block z).ncard : ℝ) ≤ (1 / 2) * Fintype.card Ω := by
        have : (2 : ℝ) * (P.block z).ncard ≤ Fintype.card Ω := by exact_mod_cast hhalf
        linarith
      exact le_trans this (by nlinarith)
  have hαn : (0 : ℝ) ≤ α * Fintype.card Ω := by nlinarith
  have hfloor : P.rho ≤ ⌊α * (Fintype.card Ω : ℝ)⌋₊ :=
    P.rho_le fun z => Nat.le_floor (key z)
  calc (P.rho : ℝ) ≤ (⌊α * (Fintype.card Ω : ℝ)⌋₊ : ℝ) := Nat.cast_le.2 hfloor
    _ ≤ α * Fintype.card Ω := Nat.floor_le hαn

end ColoredPartition

end Babai
