/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: the canonical equipartition of outcome (b) of Theorem 8.1.2.
-/
import Workspace.DesignLemma.Defs
import Workspace.Coherent.Constituents
import Mathlib.SetTheory.Cardinal.Order

/-!
# §8.1, outcome (b): the canonical equipartition

Version 2.5, §8.1, end of the "Proof of equivalence": *"Otherwise, `X*[C]` is imprimitive;
the connected components of its first disconnected non-diagonal constituent form the
required canonical equipartition (Prop. 3.4.4)."*

This file names that equipartition (`KAryPartStruct.designPartition`) and proves that it
commutes with isomorphisms, also between *different* vertex sets.

## What "first" means here

The paper numbers the colors of a configuration by `[r]` (Def. 3.1.1), and the numbering
produced by WL refinement is canonical because the colors are sorted lexicographically
(§5.4.1).  So "the first disconnected non-diagonal constituent" is: among the colors that
are off-diagonal on `C` and whose constituent is disconnected, the least one.

In the formalization a color is an element of an abstract type `C`, which carries no
order.  We select the least element in the canonical well-ordering `WellOrderingRel` of
the type `C` (Mathlib's well-ordering theorem).  The only property of "first" that the
paper uses is that the choice is *canonical*: it must depend on nothing but the set of
candidate colors, so that isomorphic inputs get corresponding constituents.  A selection
made by a well-ordering of the color type has exactly this property: the candidate sets of
two isomorphic inputs are literally the same subset of `C` (an isomorphism preserves
colors, `Iso`), so the two selections are equal (`designColor_canonical`).  Across
different vertex sets the color types differ by a transport (`§5.4.1`,
`Workspace/Higher/WLCanonical.lean`), and a well-ordering is carried along a transport
(`designPartition_cast`).

## Numbering map

| Paper | Lean |
|---|---|
| §8.1, "its first disconnected non-diagonal constituent" | `Babai.KAryPartStruct.designColor`, `.designDigraph` |
| §8.1, "form the required canonical equipartition" | `.designPartition`, `.designPartition_isEquipartitionOn` |
| §8.1, "canonical" | `.designPartition_canonical` |
-/

open scoped Classical

universe u

namespace Babai

/-! ### Transporting weak components along an isomorphism of digraphs -/

namespace Digraph

variable {Ω Ω' : Type*}

@[simp] theorem symmetrization_adj (X : Digraph Ω) (u v : Ω) :
    X.symmetrization.Adj u v ↔ X.Adj u v ∨ X.Adj v u := Iff.rfl

/-- An adjacency-preserving map carries walks to walks: accessibility is preserved. -/
theorem accessible_map {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X.Adj u v → X'.Adj (e u) (e v)) {u v : Ω} (hacc : X.Accessible u v) :
    X'.Accessible (e u) (e v) := by
  refine X.accessible_rel (r := fun a b => X'.Accessible (e a) (e b)) ?_ ?_ ?_ hacc
  · intro x
    exact (X'.accessible_iff_reflTransGen _ _).2 Relation.ReflTransGen.refl
  · intro a b c hab hbc
    rw [accessible_iff_reflTransGen] at hab hbc ⊢
    exact hab.trans hbc
  · intro a b hab
    exact (X'.accessible_iff_reflTransGen _ _).2
      (Relation.ReflTransGen.single (h a b hab))

/-- An isomorphism of digraphs preserves accessibility in both directions. -/
theorem accessible_congr {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X'.Adj (e u) (e v) ↔ X.Adj u v) (u v : Ω) :
    X'.Accessible (e u) (e v) ↔ X.Accessible u v := by
  constructor
  · intro hacc
    have hback : ∀ a b : Ω', X'.Adj a b → X.Adj (e.symm a) (e.symm b) := by
      intro a b hab
      refine (h (e.symm a) (e.symm b)).1 ?_
      simpa using hab
    have := accessible_map e.symm hback hacc
    simpa using this
  · exact accessible_map e (fun a b hab => (h a b).2 hab)

/-- An isomorphism of digraphs is an isomorphism of their symmetrizations. -/
theorem symmetrization_adj_congr {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X'.Adj (e u) (e v) ↔ X.Adj u v) (u v : Ω) :
    X'.symmetrization.Adj (e u) (e v) ↔ X.symmetrization.Adj u v := by
  rw [symmetrization_adj, symmetrization_adj, h, h]

/-- An isomorphism of digraphs carries weak components to weak components. -/
theorem weakComponent_image {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X'.Adj (e u) (e v) ↔ X.Adj u v) (u : Ω) :
    X'.weakComponent (e u) = e '' X.weakComponent u := by
  have hsym := symmetrization_adj_congr e h
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨e.symm w, ⟨?_, ?_⟩, by simp⟩
    · refine (accessible_congr e hsym u (e.symm w)).1 ?_
      simpa using h1
    · refine (accessible_congr e hsym (e.symm w) u).1 ?_
      simpa using h2
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    exact ⟨(accessible_congr e hsym u v).2 h1, (accessible_congr e hsym v u).2 h2⟩

/-- An isomorphism of digraphs carries the set of weak components to the set of weak
components. -/
theorem weakComponents_image {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X'.Adj (e u) (e v) ↔ X.Adj u v) :
    X'.weakComponents = (fun A : Set Ω => e '' A) '' X.weakComponents := by
  ext A
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨X.weakComponent (e.symm w), ⟨e.symm w, rfl⟩, ?_⟩
    have hw := weakComponent_image e h (e.symm w)
    rw [Equiv.apply_symm_apply] at hw
    exact hw.symm
  · rintro ⟨B, ⟨u, rfl⟩, rfl⟩
    exact ⟨e u, weakComponent_image e h u⟩

/-- Weak connectivity is an isomorphism invariant. -/
theorem isWeaklyConnected_congr {X : Digraph Ω} {X' : Digraph Ω'} (e : Ω ≃ Ω')
    (h : ∀ u v : Ω, X'.Adj (e u) (e v) ↔ X.Adj u v) :
    X'.IsWeaklyConnected ↔ X.IsWeaklyConnected := by
  have hsym := symmetrization_adj_congr e h
  constructor
  · intro hc u v
    exact (accessible_congr e hsym u v).1 (hc (e u) (e v))
  · intro hc u v
    have := (accessible_congr e hsym (e.symm u) (e.symm v)).2 (hc _ _)
    simpa using this

end Digraph

/-! ### Canonicity relative to `x⃗` -/

namespace KAryPartStruct

variable {Ω Ω' C : Type*} {k l m : ℕ}

/-- Recasting the arity along `k = k'` does not change the isomorphisms. -/
theorem recast_canonical (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k)
    {k' : ℕ} (h : k = k') {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) :
    f ∈ Iso (X.recast h) (Y.recast h) := by
  subst h; exact hf

/-- Proposition 5.2.6 (b) for `restrTo`: *"the assignment `X ↦ X_x⃗` is canonical relative
to `x⃗`"*.  An isomorphism `f : X → Y` is an isomorphism `X_x⃗ → Y_{x⃗^f}`. -/
theorem restrTo_canonical (X : KAryPartStruct Ω C k) (Y : KAryPartStruct Ω' C k)
    (hl : l ≤ k) (x : Str Ω l) {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) :
    f ∈ Iso (X.restrTo hl x) (Y.restrTo hl (tupleMap f x)) :=
  restrict_canonical _ _ x (recast_canonical X Y (Nat.add_sub_cancel' hl).symm hf)

/-- The vertex-coloring is canonical: an isomorphism `f : Y → Y'` carries the
vertex-coloring of `Y` to that of `Y'`. -/
theorem vcolor_canonical (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') (v : Ω) : Y'.vcolor (f v) = Y.vcolor v := by
  have := hf (fun _ => v)
  simpa [vcolor, tupleMap] using this

/-- The vertex-color classes are canonical. -/
theorem vclass_canonical (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') (i : C) : f '' Y.vclass i = Y'.vclass i := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    show Y'.vcolor (f v) = i
    rw [vcolor_canonical Y Y' hf v]
    exact hv
  · intro hw
    refine ⟨f.symm w, ?_, by simp⟩
    show Y.vcolor (f.symm w) = i
    rw [← vcolor_canonical Y Y' hf (f.symm w)]
    simpa using hw

/-- Dominance is canonical: a class of `Y` is dominant exactly if its image is a dominant
class of `Y'`. -/
theorem dominantClass_canonical [Fintype Ω] [Fintype Ω'] {α : ℝ}
    (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') :
    f '' dominantClass α Y = dominantClass α Y' := by
  have hcard : (Fintype.card Ω : ℝ) = (Fintype.card Ω' : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr f)
  have hdom : ∀ v : Ω, IsDominant α (Y.vclass (Y.vcolor v))
      ↔ IsDominant α (Y'.vclass (Y'.vcolor (f v))) := by
    intro v
    have himg : f '' Y.vclass (Y.vcolor v) = Y'.vclass (Y'.vcolor (f v)) := by
      rw [vclass_canonical Y Y' hf, vcolor_canonical Y Y' hf v]
    have hn : (Y.vclass (Y.vcolor v)).ncard = (Y'.vclass (Y'.vcolor (f v))).ncard := by
      rw [← himg, Set.ncard_image_of_injective _ f.injective]
    unfold IsDominant
    rw [hn, hcard]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hdom v).1 hv
  · intro hw
    refine ⟨f.symm w, ?_, by simp⟩
    have := (hdom (f.symm w)).2
    simp only [Equiv.apply_symm_apply] at this
    exact this hw

/-- Outcome (i) is canonical: `Y` has no dominant color exactly if `Y'` has none. -/
theorem noDominantColor_canonical [Fintype Ω] [Fintype Ω'] {α : ℝ}
    (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') :
    NoDominantColor α Y ↔ NoDominantColor α Y' := by
  have hcard : (Fintype.card Ω : ℝ) = (Fintype.card Ω' : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr f)
  have hn : ∀ i : C, (Y.vclass i).ncard = (Y'.vclass i).ncard := by
    intro i
    rw [← vclass_canonical Y Y' hf i, Set.ncard_image_of_injective _ f.injective]
  unfold NoDominantColor
  constructor
  · intro h i
    rw [← hn i, ← hcard]
    exact h i
  · intro h i
    rw [hn i, hcard]
    exact h i

/-- The extended coloring is canonical. -/
theorem skeletonColor_canonical (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') (hp : 0 < l) (hlm : l ≤ m) (z : Str Ω l) :
    Y'.skeletonColor hp hlm (tupleMap f z) = Y.skeletonColor hp hlm z := by
  have hpad : Str.pad hp m (tupleMap (f : Ω → Ω') z) = tupleMap f (Str.pad hp m z) := rfl
  show Y'.color (Str.pad hp m (tupleMap (f : Ω → Ω') z)) = Y.color (Str.pad hp m z)
  rw [hpad]
  exact hf _

end KAryPartStruct

namespace PartitionStructure

variable {Ω Ω' : Type*}

/-- An isomorphism of classical partition structures with *different* color sets: `f`
carries the coloring of `S` to the coloring of `T`, i.e. it maps the color classes of `S`
onto those of `T`.  (Def. 3.1.1 numbers the colors by `[r]`, so an isomorphism of
partition structures cannot be asked to preserve the names of the colors; this is the
form in which the outputs of `ofColoring` are compared.) -/
def IsColorIso (S : PartitionStructure Ω) (T : PartitionStructure Ω') (f : Ω ≃ Ω') : Prop :=
  ∀ u v u' v' : Ω, (S.color u v = S.color u' v' ↔ T.color (f u) (f v) = T.color (f u') (f v'))

end PartitionStructure

namespace KAryPartStruct

variable {Ω Ω' C : Type*} {m : ℕ}

/-- Outcome (ii) is canonical: the classical coherent configuration `X* = Y^{(2)}` is
canonical, i.e. an isomorphism `f : Y → Y'` carries `Y^{(2)}` to `Y'^{(2)}`. -/
theorem skel2_canonical [Fintype Ω] [Fintype Ω'] [DecidableEq Ω] [DecidableEq Ω']
    (Y : KAryPartStruct Ω C m) (Y' : KAryPartStruct Ω' C m) (hm : 2 ≤ m)
    {f : Ω ≃ Ω'} (hf : f ∈ Iso Y Y') :
    (Y.skel2 hm).IsColorIso (Y'.skel2 hm) f := by
  intro u v u' v'
  rw [skel2_color_eq_iff, skel2_color_eq_iff]
  have key : ∀ a b : Ω, Y'.skeletonColor (by norm_num) hm ![f a, f b]
      = Y.skeletonColor (by norm_num) hm ![a, b] := by
    intro a b
    have h : (tupleMap (f : Ω → Ω') ![a, b]) = ![f a, f b] := by
      funext j
      fin_cases j <;> rfl
    rw [← h]
    exact skeletonColor_canonical Y Y' hf _ hm _
  rw [key, key]

end KAryPartStruct

/-! ### Equipartitions of a subset -/

section Equipartition

variable {Ω : Type*}

/-- Definition 3.4.3 relativized to a subset: *"an equipartition of a set `Ω` is a
partition of `Ω` into blocks of equal size"*, here a partition of `Δ ⊆ Ω` whose blocks are
subsets of `Ω`.  (`Babai.IsEquipartition` is the case `Δ = Ω`.) -/
structure IsEquipartitionOn (P : Set (Set Ω)) (Δ : Set Ω) : Prop where
  /-- the blocks are subsets of `Δ` -/
  subset : ∀ A ∈ P, A ⊆ Δ
  /-- the blocks are nonempty -/
  nonempty : ∀ A ∈ P, A.Nonempty
  /-- distinct blocks are disjoint -/
  pairwiseDisjoint : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B
  /-- the blocks cover `Δ` -/
  covers : ⋃₀ P = Δ
  /-- the blocks have equal size -/
  equal_size : ∀ A ∈ P, ∀ B ∈ P, A.ncard = B.ncard

/-- §2.2.1: a partition is *nontrivial* if it is neither the partition into singletons nor
the partition with a single block. -/
def IsNontrivialPartition (P : Set (Set Ω)) : Prop :=
  (∃ A ∈ P, ∃ B ∈ P, A ≠ B) ∧ ∀ A ∈ P, A.Nontrivial

/-- Transporting an equipartition of a subtype `↥Δ` to an equipartition of the subset
`Δ ⊆ Ω` along the injection `Subtype.val`.  The blocks produced in case (b) of
Theorem 8.1.2 are the connected components of a constituent of `X*[C]`, which live on
`↥C`; the theorem asks for a partition of `C` by subsets of `Ω`. -/
theorem isEquipartitionOn_image {Δ : Set Ω} (P : Set (Set Δ))
    (hP : IsEquipartition P) (h2 : ∃ A ∈ P, ∃ B ∈ P, A ≠ B)
    (hnt : ∀ A ∈ P, A.Nontrivial) :
    IsEquipartitionOn ((fun A : Set Δ => (Subtype.val '' A)) '' P) Δ ∧
      IsNontrivialPartition ((fun A : Set Δ => (Subtype.val '' A)) '' P) := by
  classical
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨A, -, rfl⟩
    rintro z ⟨⟨w, hw⟩, -, rfl⟩
    exact hw
  · rintro _ ⟨A, hA, rfl⟩
    exact (hP.nonempty A hA).image _
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    have hne : A ≠ B := fun hc => hAB (by rw [hc])
    exact Set.disjoint_image_of_injective Subtype.val_injective (hP.pairwiseDisjoint A hA B hB hne)
  · ext z
    constructor
    · rintro ⟨_, ⟨A, -, rfl⟩, ⟨⟨w, hw⟩, -, rfl⟩⟩
      exact hw
    · intro hz
      have hmem : (⟨z, hz⟩ : Δ) ∈ ⋃₀ P := by rw [hP.covers]; trivial
      obtain ⟨A, hA, hzA⟩ := hmem
      exact ⟨Subtype.val '' A, ⟨A, hA, rfl⟩, ⟨⟨z, hz⟩, hzA, rfl⟩⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hP.equal_size A hA B hB
  · obtain ⟨A, hA, B, hB, hAB⟩ := h2
    exact ⟨Subtype.val '' A, ⟨A, hA, rfl⟩, Subtype.val '' B, ⟨B, hB, rfl⟩, fun hc =>
      hAB (Set.image_injective.2 Subtype.val_injective hc)⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact (hnt A hA).image Subtype.val_injective

end Equipartition

/-! ### Choosing the first element of a set of colors -/

/-- The least element of `{c | P c}` in the canonical well-ordering `WellOrderingRel` of
the color type, or `none` when there is no such element.  This is how the paper's *"the
first …"* (§8.1) is read here; see the note at the head of this file.  The value depends
on nothing but the predicate `P`, which is what makes the choice canonical
(`firstOf` is a function of `P`, so equal predicates give equal values). -/
noncomputable def firstOf {C : Type*} (P : C → Prop) : Option C :=
  if h : ∃ c : C, P c then
    some ((IsWellFounded.wf (r := (WellOrderingRel : C → C → Prop))).min {c : C | P c} h)
  else none

theorem firstOf_isSome {C : Type*} {P : C → Prop} (h : ∃ c : C, P c) :
    ∃ c : C, firstOf P = some c ∧ P c := by
  refine ⟨_, by rw [firstOf, dif_pos h], ?_⟩
  exact (IsWellFounded.wf (r := (WellOrderingRel : C → C → Prop))).min_mem _ h

theorem firstOf_spec {C : Type*} {P : C → Prop} {c : C} (h : firstOf P = some c) : P c := by
  by_cases hex : ∃ c : C, P c
  · obtain ⟨c', hc', hd⟩ := firstOf_isSome hex
    rw [hc'] at h
    exact (Option.some.inj h) ▸ hd
  · rw [firstOf, dif_neg hex] at h
    exact absurd h (by simp)

namespace KAryPartStruct

variable {Ω Ω' C : Type*} {m : ℕ}

/-! ### The constituents of `X* = Y^{(2)}` on the dominant class -/

/-- The color of the ordered pair `(u,v)` in `X* = Y^{(2)}`: the extended color
`c^{(2)}(uv)` of §5.1.4.  The configuration `skel2` is this coloring renumbered by `[r]`
(Def. 3.1.1), so the constituents of `X*` are the classes of `pairColor`. -/
def pairColor (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) (u v : Ω) : C :=
  Y.skeletonColor (by norm_num) hm ![u, v]

theorem skel2_color_eq_iff' [Fintype Ω] (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (u v u' v' : Ω) :
    (Y.skel2 hm).color u v = (Y.skel2 hm).color u' v'
      ↔ Y.pairColor hm u v = Y.pairColor hm u' v' :=
  Y.skel2_color_eq_iff hm u v u' v'

variable [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

/-- The color-`c` constituent of `X*[C]`, as a digraph on the dominant class: the pairs of
vertices of the dominant class whose `X*`-color is `c`. -/
def designDigraph (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) (c : C) :
    Digraph ↥(dominantClass α Y) :=
  ⟨{p | Y.pairColor hm p.1 p.2 = c}⟩

@[simp] theorem designDigraph_adj (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) (c : C)
    (u v : ↥(dominantClass α Y)) :
    (designDigraph α Y hm c).Adj u v ↔ Y.pairColor hm (u : Ω) (v : Ω) = c := Iff.rfl

/-- §8.1: a color that names a *disconnected non-diagonal constituent* of `X*[C]`.  It is
realized on the dominant class, it is off-diagonal there (Def. 3.1.3: no pair `(u,u)` has
this color), and its constituent digraph is not weakly connected. -/
def IsDesignColor (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) (c : C) : Prop :=
  (∃ u v : ↥(dominantClass α Y), Y.pairColor hm (u : Ω) (v : Ω) = c) ∧
    (∀ u : ↥(dominantClass α Y), Y.pairColor hm (u : Ω) (u : Ω) ≠ c) ∧
    ¬ (designDigraph α Y hm c).IsWeaklyConnected

/-- §8.1: *"the first disconnected non-diagonal constituent"* of `X*[C]`.  "First" is with
respect to the canonical well-ordering of the color type; see the note at the head of this
file.  The value is `none` when `X*[C]` has no disconnected non-diagonal constituent. -/
noncomputable def designColor (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) : Option C :=
  firstOf (IsDesignColor α Y hm)

theorem designColor_eq_some (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (h : ∃ c : C, IsDesignColor α Y hm c) :
    ∃ c : C, designColor α Y hm = some c ∧ IsDesignColor α Y hm c :=
  firstOf_isSome h

theorem isDesignColor_of_designColor {α : ℝ} {Y : KAryPartStruct Ω C m} {hm : 2 ≤ m}
    {c : C} (h : designColor α Y hm = some c) : IsDesignColor α Y hm c :=
  firstOf_spec h

/-- §8.1, outcome (b) of Theorem 8.1.2: *"the connected components of its first
disconnected non-diagonal constituent"*, as a family of subsets of `Ω`.  It is empty when
`X*[C]` has no disconnected non-diagonal constituent (in which case outcome (b) is not the
outcome reached). -/
noncomputable def designPartition (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) :
    Set (Set Ω) :=
  (designColor α Y hm).elim ∅
    fun c => (fun A : Set ↥(dominantClass α Y) => Subtype.val '' A) ''
      (designDigraph α Y hm c).weakComponents

theorem designPartition_of_eq_some {α : ℝ} {Y : KAryPartStruct Ω C m} {hm : 2 ≤ m} {c : C}
    (h : designColor α Y hm = some c) :
    designPartition α Y hm
      = (fun A : Set ↥(dominantClass α Y) => Subtype.val '' A) ''
          (designDigraph α Y hm c).weakComponents := by
  rw [designPartition, h]
  rfl


theorem designPartition_of_eq_none {α : ℝ} {Y : KAryPartStruct Ω C m} {hm : 2 ≤ m}
    (h : designColor α Y hm = none) : designPartition α Y hm = ∅ := by
  rw [designPartition, h]
  rfl

/-! ### Outcome (b): the components of the first disconnected constituent -/

/-- The color-`c` constituent of `X*[C]` in the sense of Def. 3.1.1 (a color of the
induced configuration `X*[C]`) is the digraph `designDigraph` of the underlying color
`c = c^{(2)}(u₀v₀)` of `X*`. -/
theorem extConstituent_eq_designDigraph (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (u₀ v₀ : ↥(dominantClass α Y)) :
    ((Y.skel2 hm).induced (dominantClass α Y)).extConstituent
        (((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀)
      = designDigraph α Y hm (Y.pairColor hm (u₀ : Ω) (v₀ : Ω)) := by
  refine congrArg Digraph.mk ?_
  ext p
  show ((Y.skel2 hm).induced (dominantClass α Y)).color p.1 p.2
      = ((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀
    ↔ Y.pairColor hm (p.1 : Ω) (p.2 : Ω) = Y.pairColor hm (u₀ : Ω) (v₀ : Ω)
  rw [PartitionStructure.induced_color_eq_iff, skel2_color_eq_iff']

/-- If `X*[C]` has a disconnected non-diagonal constituent then it has a design color, so
that `designColor` selects one (§8.1, *"`X*[C]` is imprimitive"*). -/
theorem exists_isDesignColor (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    {j : Fin ((Y.skel2 hm).induced (dominantClass α Y)).rank}
    (hoff : ((Y.skel2 hm).induced (dominantClass α Y)).IsOffDiagonalColor j)
    (hdisc : ¬ (((Y.skel2 hm).induced (dominantClass α Y)).extConstituent j).IsWeaklyConnected) :
    ∃ c : C, IsDesignColor α Y hm c := by
  classical
  have hj : ((Y.skel2 hm).induced (dominantClass α Y)).color
      (((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).1
      (((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).2 = j :=
    ((Y.skel2 hm).induced (dominantClass α Y)).color_colorWitness j
  have hEq : ((Y.skel2 hm).induced (dominantClass α Y)).extConstituent j
      = designDigraph α Y hm (Y.pairColor hm
          ((((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).1 : Ω)
          ((((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).2 : Ω)) := by
    have h0 := extConstituent_eq_designDigraph α Y hm
      (((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).1
      (((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).2
    rwa [hj] at h0
  refine ⟨Y.pairColor hm ((((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).1 : Ω)
      ((((Y.skel2 hm).induced (dominantClass α Y)).colorWitness j).2 : Ω),
    ⟨_, _, rfl⟩, ?_, ?_⟩
  · intro u hu
    have hmem : ((u, u) : ↥(dominantClass α Y) × ↥(dominantClass α Y))
        ∈ (((Y.skel2 hm).induced (dominantClass α Y)).extConstituent j).E := by
      rw [hEq]; exact hu
    exact Set.eq_empty_iff_forall_notMem.1 hoff (u, u) ⟨hmem, rfl⟩
  · rw [← hEq]
    exact hdisc


/-- §8.1, outcome (b) of Theorem 8.1.2: *"the connected components of its first
disconnected non-diagonal constituent form the required canonical equipartition
(Prop. 3.4.4)"*.  The hypotheses on `X*[C]` are those established in the proof of
Theorem 8.1.2: the dominant class is a vertex-color class of `X*`, so `X*[C]` is a
homogeneous coherent configuration (Obs. 3.3.2). -/
theorem designPartition_isEquipartitionOn (α : ℝ) (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (hZcoh : ((Y.skel2 hm).induced (dominantClass α Y)).IsCoherent)
    (hZhom : ((Y.skel2 hm).induced (dominantClass α Y)).IsHomogeneous)
    (hex : ∃ c : C, IsDesignColor α Y hm c) :
    IsEquipartitionOn (designPartition α Y hm) (dominantClass α Y) ∧
      IsNontrivialPartition (designPartition α Y hm) := by
  classical
  obtain ⟨c, hc, hdc⟩ := designColor_eq_some α Y hm hex
  obtain ⟨u₀, v₀, huv⟩ := hdc.1
  have hEq : ((Y.skel2 hm).induced (dominantClass α Y)).extConstituent
      (((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀)
      = designDigraph α Y hm c := by
    rw [extConstituent_eq_designDigraph α Y hm u₀ v₀, huv]
  have hoff : ((Y.skel2 hm).induced (dominantClass α Y)).IsOffDiagonalColor
      (((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀) := by
    rw [PartitionStructure.IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp1, hp2⟩
    have hp2' : p.1 = p.2 := hp2
    have hcol : Y.pairColor hm (p.1 : Ω) (p.2 : Ω) = c := by
      have hmem : p ∈ (((Y.skel2 hm).induced (dominantClass α Y)).extConstituent
          (((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀)).E := hp1
      rw [hEq] at hmem
      exact hmem
    rw [← hp2'] at hcol
    exact hdc.2.1 p.1 hcol
  have hdisc : ¬ (((Y.skel2 hm).induced (dominantClass α Y)).extConstituent
      (((Y.skel2 hm).induced (dominantClass α Y)).color u₀ v₀)).IsWeaklyConnected := by
    rw [hEq]; exact hdc.2.2
  obtain ⟨heq, htwo, hnt⟩ :=
    PartitionStructure.homogeneous_disconnected_weakComponents _ hZcoh hZhom _ hoff hdisc
  rw [hEq] at heq htwo hnt
  rw [designPartition_of_eq_some hc]
  exact isEquipartitionOn_image _ heq htwo hnt

/-! ### Canonicity of the design partition -/

section Canonical

variable {α : ℝ} {Y : KAryPartStruct Ω C m} {Y' : KAryPartStruct Ω' C m} {hm : 2 ≤ m}
  {f : Ω ≃ Ω'}

/-- The color of a pair in `X* = Y^{(2)}` is canonical. -/
theorem pairColor_canonical (hf : f ∈ Iso Y Y') (u v : Ω) :
    Y'.pairColor hm (f u) (f v) = Y.pairColor hm u v := by
  have h : (tupleMap (f : Ω → Ω') ![u, v]) = ![f u, f v] := by
    funext j
    fin_cases j <;> rfl
  show Y'.skeletonColor (by norm_num) hm ![f u, f v] = _
  rw [← h]
  exact skeletonColor_canonical Y Y' hf _ hm _

theorem mem_dominantClass_congr (hf : f ∈ Iso Y Y') (u : Ω) :
    u ∈ dominantClass α Y ↔ f u ∈ dominantClass α Y' := by
  rw [← dominantClass_canonical Y Y' hf]
  constructor
  · intro h
    exact ⟨u, h, rfl⟩
  · rintro ⟨v, hv, hfv⟩
    rwa [f.injective hfv] at hv

/-- The isomorphism `f` restricted to the dominant class. -/
def domEquiv (hf : f ∈ Iso Y Y') :
    ↥(dominantClass α Y) ≃ ↥(dominantClass α Y') :=
  Equiv.subtypeEquiv f (fun u => mem_dominantClass_congr (α := α) hf u)

@[simp] theorem domEquiv_val (hf : f ∈ Iso Y Y') (u : ↥(dominantClass α Y)) :
    ((domEquiv (α := α) hf u : ↥(dominantClass α Y')) : Ω') = f (u : Ω) := rfl

@[simp] theorem domEquiv_symm_val (hf : f ∈ Iso Y Y') (u' : ↥(dominantClass α Y')) :
    f ((((domEquiv (α := α) hf).symm u' : ↥(dominantClass α Y)) : Ω)) = (u' : Ω') := by
  have h := domEquiv_val (α := α) hf ((domEquiv (α := α) hf).symm u')
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem designDigraph_adj_canonical (hf : f ∈ Iso Y Y') (c : C)
    (u v : ↥(dominantClass α Y)) :
    (designDigraph α Y' hm c).Adj (domEquiv (α := α) hf u) (domEquiv (α := α) hf v)
      ↔ (designDigraph α Y hm c).Adj u v := by
  show Y'.pairColor hm (f (u : Ω)) (f (v : Ω)) = c ↔ Y.pairColor hm (u : Ω) (v : Ω) = c
  rw [pairColor_canonical hf]

/-- The design colors of `Y` and of `Y'` are the same colors. -/
theorem isDesignColor_canonical (hf : f ∈ Iso Y Y') (c : C) :
    IsDesignColor α Y' hm c ↔ IsDesignColor α Y hm c := by
  have hadj := designDigraph_adj_canonical (α := α) (hm := hm) hf c
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · rintro ⟨u', v', h⟩
      refine ⟨(domEquiv (α := α) hf).symm u', (domEquiv (α := α) hf).symm v', ?_⟩
      rw [← pairColor_canonical (hm := hm) hf]
      simpa using h
    · rintro ⟨u, v, h⟩
      exact ⟨domEquiv (α := α) hf u, domEquiv (α := α) hf v, by
        rw [domEquiv_val, domEquiv_val, pairColor_canonical hf]; exact h⟩
  · constructor
    · intro h u hu
      exact h (domEquiv (α := α) hf u) (by rw [domEquiv_val, pairColor_canonical hf]; exact hu)
    · intro h u' hu'
      refine h ((domEquiv (α := α) hf).symm u') ?_
      rw [← pairColor_canonical (hm := hm) hf]
      simpa using hu'
  · exact not_congr (Digraph.isWeaklyConnected_congr _ hadj)

/-- §8.1: the choice of the first disconnected non-diagonal constituent is canonical. -/
theorem designColor_canonical (hf : f ∈ Iso Y Y') :
    designColor α Y' hm = designColor α Y hm := by
  have h : IsDesignColor α Y' hm = IsDesignColor α Y hm :=
    funext fun c => propext (isDesignColor_canonical hf c)
  rw [designColor, designColor, h]

/-- §8.1, outcome (b) of Theorem 8.1.2: the equipartition is canonical.  An isomorphism
`f : Y → Y'` carries the blocks of the design partition of `Y` onto the blocks of the
design partition of `Y'`. -/
theorem designPartition_canonical (hf : f ∈ Iso Y Y') :
    designPartition α Y' hm = (fun A : Set Ω => f '' A) '' designPartition α Y hm := by
  classical
  rcases h : designColor α Y hm with _ | c
  · rw [designPartition_of_eq_none h,
      designPartition_of_eq_none (by rw [designColor_canonical (α := α) (hm := hm) hf]; exact h)]
    simp
  · rw [designPartition_of_eq_some h,
      designPartition_of_eq_some (by rw [designColor_canonical (α := α) (hm := hm) hf]; exact h),
      Digraph.weakComponents_image (domEquiv (α := α) hf)
        (designDigraph_adj_canonical (α := α) (hm := hm) hf c),
      Set.image_image, Set.image_image]
    refine congrArg (fun g => g '' (designDigraph α Y hm c).weakComponents) ?_
    funext A
    rw [Set.image_image, Set.image_image]
    rfl

end Canonical

/-! ### Transport along an equality of color types

Across *different* vertex sets the `k`-WL color type depends on `|Ω|`
(`Workspace/Higher/WLCanonical.lean`), so the two structures to be compared have color
types that are equal only propositionally.  These lemmas move every object of
Theorems 8.1.2 and 8.1.5 along such an equality. -/

section Cast

variable {C₁ C₂ : Type u} {α : ℝ} {l k : ℕ}

theorem eq_of_color_cast {Y₁ Y₂ : KAryPartStruct Ω C₁ m}
    (hcol : ∀ x, Y₂.color x = Y₁.color x) : Y₂ = Y₁ := by
  cases Y₁; cases Y₂
  exact congrArg KAryPartStruct.mk (funext hcol)

/-- The restriction of the transported structure is the transport of the restriction. -/
theorem restrTo_color_cast (hC : C₁ = C₂) {X₁ : KAryPartStruct Ω C₁ k}
    {X₂ : KAryPartStruct Ω C₂ k} (hcol : ∀ x, X₂.color x = cast hC (X₁.color x))
    (hl : l ≤ k) (x : Str Ω l) (y : Str Ω (k - l)) :
    (X₂.restrTo hl x).color y = cast hC ((X₁.restrTo hl x).color y) := by
  rw [restrTo_color, restrTo_color, hcol]

variable {Y₁ : KAryPartStruct Ω C₁ m} {Y₂ : KAryPartStruct Ω C₂ m} {hm : 2 ≤ m}

theorem vcolor_cast (hC : C₁ = C₂) (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x))
    (u v : Ω) : Y₂.vcolor u = Y₂.vcolor v ↔ Y₁.vcolor u = Y₁.vcolor v := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  exact Iff.rfl

theorem dominantClass_cast (hC : C₁ = C₂) (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    dominantClass α Y₂ = dominantClass α Y₁ := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  rfl

theorem noDominantColor_cast (hC : C₁ = C₂)
    (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    NoDominantColor α Y₂ ↔ NoDominantColor α Y₁ := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  exact Iff.rfl

theorem hasDominantClass_cast (hC : C₁ = C₂)
    (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    HasDominantClass α Y₂ ↔ HasDominantClass α Y₁ := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  exact Iff.rfl

theorem skel2_cast (hC : C₁ = C₂) (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    Y₂.skel2 hm = Y₁.skel2 hm := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  rfl

theorem designPartition_cast (hC : C₁ = C₂)
    (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    designPartition α Y₂ hm = designPartition α Y₁ hm := by
  subst hC
  obtain rfl : Y₂ = Y₁ := eq_of_color_cast hcol
  rfl

end Cast

end KAryPartStruct

end Babai
