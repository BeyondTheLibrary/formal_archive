/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: Functors, canonical constructions.
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.CategoryTheory.Groupoid

/-!
# §6 Functors, canonical constructions

## The encoding of the paper's categories

The paper: *"The only type of category we consider will be Brandt groupoids, i.e.,
categories in which every morphism is invertible.  Our categories will be concrete, i.e.,
the objects `X` have an underlying set `□(X)` and the morphisms are mappings between the
objects (bijections in our case). ... We assume `□` is faithful, i.e., if objects `X` and
`Y` have the same underlying set `□(X) = □(Y)` and the identity map on this set is a
morphism between `X` and `Y` then `X = Y`."*

We therefore do **not** use `CategoryTheory.Groupoid`: there, a morphism is an abstract
arrow, while every sentence of §6 speaks about the underlying set of an object and about
morphisms *as bijections between underlying sets* (a canonical embedding is a functor for
which `F(f)` *is the restriction of `f`*).  Encoding that on top of Mathlib's
`ConcreteCategory` would need a forgetful functor plus a faithfulness axiom plus coercions
back and forth, and the key definitions would be stated about the image of `F` under the
forgetful functor rather than about `F` itself.

Instead `Babai.Cat Ω` is a bespoke structure: all points live in an ambient type `Ω`, an
object carries its underlying set `s : Set Ω` as an *index*

  `Obj : Set Ω → Type v`,   `Iso : Obj s → Obj t → Set (↥s ≃ ↥t)`,

so that "the underlying set of `X`" is literally a `Set Ω`, morphisms are literally
bijections between underlying sets, composition is `Equiv.trans`, inversion is
`Equiv.symm`, and the paper's faithfulness is the axiom `faithful` verbatim.  Indexing the
objects by their underlying set (rather than carrying `□ : Obj → Set Ω` as a field) makes
`□(X) = □(Y)` a *definitional* equality wherever the paper needs it, which is what makes
Definition 6.0.1 (where all objects of a tuple share their underlying set) painless.

The paper adds: *"In fact, we can limit ourselves to categories where all objects have the
same underlying set, so all morphisms are permutations."*  That is the special case where
`Obj s` is empty for all but one `s`; we do not impose it, because a canonical embedding
`F` has `□(F(X)) ⊆ □(X)` with `□(F(X))` varying with `X`, so the categories that are the
*targets* of canonical embeddings do have objects on many underlying sets.
`Babai.Cat.Aut` shows the "morphisms are permutations" reading: `Aut X` is a subgroup of
`Equiv.Perm ↥(□X)`.

A `CategoryTheory.Groupoid` instance on `Babai.Pt C` is provided (`Babai.Cat.groupoid`) as
a bridge to Mathlib; nothing else in this development uses it.

## Numbering map

| Paper | Lean |
|---|---|
| concrete faithful Brandt groupoid | `Babai.Cat` |
| `□(X)`, `X ∈ C` | `Babai.Pt.car`, `Babai.Pt` |
| `Iso(X,Y)` | `Babai.Cat.IsoP`, bundled as `Babai.Hom` |
| `Aut(X)` | `Babai.Cat.Aut` |
| canonical assignment / construction | `Babai.IsCanonicalAssignment` |
| canonical embedding | `Babai.Func.IsCanonicalEmbedding` |
| canonical subset | `Babai.IsCanonicalSubset` |
| canonical embedding *onto* | `Babai.Func.IsCanonicalEmbeddingOnto` |
| canonical vertex-coloring | `Babai.IsCanonicalVertexColoring` |
| canonical partition | `Babai.IsCanonicalPartition` |
| `Sets`, `ColoredSets`, `PartitionedSets` | `Babai.Sets`, `Babai.ColoredSets`, `Babai.PartitionedSets` |
| `G`-isomorphisms of strings | `Babai.GStrings` |
| restriction of `Aut(X)` is a subgroup of `Aut(F(X))` | `Babai.Func.autHom`, `Babai.Func.IsCanonicalEmbedding.autHom_apply`, `.restriction_le_aut` |
| a canonical subset is `Aut(X)`-invariant | `Babai.IsCanonicalSubset.aut_invariant` |
| the vertex set of a canonically embedded object is a canonical subset | `Babai.Func.IsCanonicalEmbedding.isCanonicalSubset` |
| composition of functors, the functor `□` | `Babai.Func.comp`, `Babai.forget` |
-/

universe u u' u'' v v' v''

namespace Babai

/-- §6.  A *category* in the sense of the paper: a concrete, faithful Brandt groupoid whose
points all lie in the ambient type `Ω`.

*"The objects `X` have an underlying set `□(X)` and the morphisms are mappings between the
objects (bijections in our case) ... every morphism is invertible ... `□` is faithful,
i.e., if objects `X` and `Y` have the same underlying set `□(X) = □(Y)` and the identity
map on this set is a morphism between `X` and `Y` then `X = Y`."*

The underlying set of an object is the index `s : Set Ω` of the type `Obj s` it lives in. -/
structure Cat (Ω : Type u) where
  /-- The objects with underlying set `s`. -/
  Obj : Set Ω → Type v
  /-- `Iso X Y` is the set of morphisms `X → Y`; each is a bijection `□X → □Y`. -/
  Iso : ∀ {s t : Set Ω}, Obj s → Obj t → Set (↥s ≃ ↥t)
  /-- The identity of `□X` is a morphism `X → X`. -/
  refl_mem : ∀ {s : Set Ω} (X : Obj s), Equiv.refl ↥s ∈ Iso X X
  /-- Every morphism is invertible. -/
  symm_mem : ∀ {s t : Set Ω} {X : Obj s} {Y : Obj t} {f : ↥s ≃ ↥t},
    f ∈ Iso X Y → f.symm ∈ Iso Y X
  /-- Morphisms compose. -/
  trans_mem : ∀ {s t r : Set Ω} {X : Obj s} {Y : Obj t} {Z : Obj r} {f : ↥s ≃ ↥t}
    {g : ↥t ≃ ↥r}, f ∈ Iso X Y → g ∈ Iso Y Z → f.trans g ∈ Iso X Z
  /-- `□` is faithful. -/
  faithful : ∀ {s : Set Ω} {X Y : Obj s}, Equiv.refl ↥s ∈ Iso X Y → X = Y

namespace Cat

variable {Ω : Type u}

/-- §6.  An object of `C` together with its underlying set: the paper's `X ∈ C`. -/
structure _root_.Babai.Pt (C : Cat Ω) where
  /-- The underlying set `□(X)` of the object. -/
  car : Set Ω
  /-- The object itself. -/
  obj : C.Obj car

/-- §6.  `Iso(X,Y)`, the set of `X → Y` morphisms. -/
def IsoP (C : Cat Ω) (X Y : Pt C) : Set (↥X.car ≃ ↥Y.car) := C.Iso X.obj Y.obj

/-- §6.  `Aut(X) = Iso(X,X)`.  Since a morphism is a bijection of underlying sets, this is
a group of permutations of `□(X)`. -/
def Aut (C : Cat Ω) (X : Pt C) : Subgroup (Equiv.Perm ↥X.car) where
  carrier := C.IsoP X X
  mul_mem' {f g} hf hg := by
    rw [Equiv.Perm.mul_def]; exact C.trans_mem hg hf
  one_mem' := C.refl_mem X.obj
  inv_mem' hf := C.symm_mem hf

@[simp] theorem mem_aut_iff {C : Cat Ω} {X : Pt C} {f : Equiv.Perm ↥X.car} :
    f ∈ C.Aut X ↔ f ∈ C.IsoP X X := Iff.rfl

theorem faithful_pt {C : Cat Ω} {X Y : Pt C} (h : X.car = Y.car)
    (hid : Equiv.setCongr h ∈ C.IsoP X Y) : X = Y := by
  revert hid
  obtain ⟨s, X⟩ := X
  obtain ⟨t, Y⟩ := Y
  simp only at h
  subst h
  intro hid
  exact congrArg (Pt.mk s) (C.faithful hid)

end Cat

/-! ### Morphisms as a bundled type -/

/-- §6.  A morphism `X → Y` of `C`: a bijection `□X → □Y` that lies in `Iso(X,Y)`. -/
def Hom {Ω : Type u} (C : Cat Ω) (X Y : Pt C) : Type u :=
  {f : ↥X.car ≃ ↥Y.car // f ∈ C.IsoP X Y}

namespace Hom

variable {Ω : Type u} {C : Cat Ω} {X Y Z : Pt C}

instance : CoeFun (Hom C X Y) fun _ => ↥X.car → ↥Y.car := ⟨fun f => f.1⟩

@[ext] theorem ext {f g : Hom C X Y} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (Equiv.ext h)

/-- The identity morphism of `X`. -/
def id (X : Pt C) : Hom C X X := ⟨Equiv.refl _, C.refl_mem X.obj⟩

/-- Composition of morphisms, in the paper's order: `f.trans g` is "first `f`, then `g`",
which the paper writes `fg`. -/
def trans (f : Hom C X Y) (g : Hom C Y Z) : Hom C X Z :=
  ⟨f.1.trans g.1, C.trans_mem f.2 g.2⟩

/-- The inverse morphism. -/
def symm (f : Hom C X Y) : Hom C Y X := ⟨f.1.symm, C.symm_mem f.2⟩

@[simp] theorem id_apply (X : Pt C) (x : ↥X.car) : Hom.id X x = x := rfl
@[simp] theorem trans_apply (f : Hom C X Y) (g : Hom C Y Z) (x : ↥X.car) :
    (f.trans g) x = g (f x) := rfl
@[simp] theorem symm_apply_apply (f : Hom C X Y) (x : ↥X.car) : f.symm (f x) = x :=
  f.1.symm_apply_apply x
@[simp] theorem apply_symm_apply (f : Hom C X Y) (y : ↥Y.car) : f (f.symm y) = y :=
  f.1.apply_symm_apply y

theorem trans_symm (f : Hom C X Y) : f.trans f.symm = Hom.id X := by ext x; simp
theorem symm_trans (f : Hom C X Y) : f.symm.trans f = Hom.id Y := by ext x; simp

/-- An automorphism of `X`, as an element of the group `Aut(X)`. -/
def toAut (f : Hom C X X) : C.Aut X := ⟨f.1, f.2⟩

end Hom

/-! ### Functors -/

/-- §6.  A functor between two of the paper's categories. -/
structure Func {Ω : Type u} {Ω' : Type u'} (C : Cat.{u, v} Ω) (D : Cat.{u', v'} Ω') where
  /-- The object map. -/
  obj : Pt C → Pt D
  /-- The morphism map. -/
  map : ∀ {X Y : Pt C}, Hom C X Y → Hom D (obj X) (obj Y)
  /-- Functors preserve identities. -/
  map_id : ∀ X : Pt C, map (Hom.id X) = Hom.id (obj X)
  /-- Functors preserve composition. -/
  map_trans : ∀ {X Y Z : Pt C} (f : Hom C X Y) (g : Hom C Y Z),
    map (f.trans g) = (map f).trans (map g)

namespace Func

variable {Ω : Type u} {Ω' : Type u'} {C : Cat.{u, v} Ω} {D : Cat.{u', v'} Ω'}

theorem map_symm (F : Func C D) {X Y : Pt C} (f : Hom C X Y) :
    F.map f.symm = (F.map f).symm := by
  have h : (F.map f).trans (F.map f.symm) = Hom.id (F.obj X) := by
    rw [← F.map_trans, Hom.trans_symm, F.map_id]
  refine Hom.ext fun y => ?_
  have h2 := congrArg (fun g : Hom D (F.obj X) (F.obj X) => g ((F.map f).symm y)) h
  simp only [Hom.trans_apply, Hom.apply_symm_apply, Hom.id_apply] at h2
  exact h2

/-- §6.  The map that a functor induces on automorphism groups: it sends `σ ∈ Aut(X)` to
the permutation `F(σ)` of `□(F(X))`. -/
def autHom (F : Func C D) (X : Pt C) : C.Aut X →* Equiv.Perm ↑(F.obj X).car where
  toFun σ := (F.map (⟨σ.1, σ.2⟩ : Hom C X X)).1
  map_one' := congrArg Subtype.val (F.map_id X)
  map_mul' σ τ := by
    have h : (⟨(σ * τ : Equiv.Perm ↑X.car), (σ * τ).2⟩ : Hom C X X)
        = Hom.trans (⟨τ.1, τ.2⟩ : Hom C X X) (⟨σ.1, σ.2⟩ : Hom C X X) := rfl
    simp only [Subgroup.coe_mul] at *
    rw [h, F.map_trans]
    rfl

theorem range_autHom_le (F : Func C D) (X : Pt C) :
    (F.autHom X).range ≤ D.Aut (F.obj X) := by
  rintro _ ⟨σ, rfl⟩
  exact (F.map (⟨σ.1, σ.2⟩ : Hom C X X)).2

end Func

/-- §6.  *"Given two categories `C` and `D`, a mapping `F₀ : C → D` is canonical if it is
the mapping of objects from a functor `F : C → D`.  ...  In such a case we refer to `F₀` as
a canonical assignment (or, most often, a canonical construction)."* -/
def IsCanonicalAssignment {Ω : Type u} {Ω' : Type u'} (C : Cat.{u, v} Ω) (D : Cat.{u', v'} Ω')
    (F₀ : Pt C → Pt D) : Prop :=
  ∃ F : Func C D, F.obj = F₀

/-! ### Canonical embeddings -/

namespace Func

variable {Ω : Type u} {C : Cat.{u, v} Ω} {D : Cat.{u, v'} Ω}

/-- §6.  *"A canonical embedding of objects from category `D` into objects from category
`C` is a functor `F : C → D` such that for every object `X ∈ C` we have `□(F(X)) ⊆ □(X)`
and for each morphism `f : X → Y` the mapping `F(f) : F(X) → F(Y)` is the restriction of
`f` to `□(F(X))`."* -/
structure IsCanonicalEmbedding (F : Func C D) : Prop where
  /-- `□(F(X)) ⊆ □(X)`. -/
  car_subset : ∀ X : Pt C, (F.obj X).car ⊆ X.car
  /-- `F(f)` is the restriction of `f`. -/
  map_restrict : ∀ {X Y : Pt C} (f : Hom C X Y) (x : ↥(F.obj X).car),
    ((F.map f x : Ω)) = (f ⟨(x : Ω), car_subset X x.2⟩ : Ω)

/-- §6.  *"We say that `F` is a canonical embedding of objects from `D` onto objects from
`C` if `□(F(X)) = □(X)` for all `X ∈ C`."* -/
structure IsCanonicalEmbeddingOnto (F : Func C D) : Prop extends IsCanonicalEmbedding F where
  /-- `□(F(X)) = □(X)`. -/
  car_eq : ∀ X : Pt C, (F.obj X).car = X.car

namespace IsCanonicalEmbedding

variable {F : Func C D}

/-- §6.  For a canonical embedding the homomorphism `Func.autHom` really is *restriction*:
`F(σ)` agrees with `σ` on `□(F(X)) ⊆ □(X)`. -/
theorem autHom_apply (hF : F.IsCanonicalEmbedding) (X : Pt C) (σ : C.Aut X)
    (x : ↑(F.obj X).car) :
    ((F.autHom X σ x : Ω)) = ((σ.1 ⟨(x : Ω), hF.car_subset X x.2⟩ : ↑X.car) : Ω) :=
  hF.map_restrict (⟨σ.1, σ.2⟩ : Hom C X X) x

/-- §6.  *"If `F` is a canonical embedding then the restriction of `Aut(X)` to `□(F(X))` is
a subgroup of `Aut(F(X))`."*  By `autHom_apply` the homomorphism `Func.autHom` *is* the
restriction map; its range is therefore a subgroup, and that subgroup is contained in
`Aut(F(X))`. -/
theorem restriction_le_aut (_hF : F.IsCanonicalEmbedding) (X : Pt C) :
    (F.autHom X).range ≤ D.Aut (F.obj X) :=
  F.range_autHom_le X

end IsCanonicalEmbedding

end Func

/-! ### The categories `Sets`, `ColoredSets`, `PartitionedSets` -/

/-- §6.  The category `Sets`: objects are the sets themselves, morphisms all bijections. -/
def Sets (Ω : Type u) : Cat.{u, v} Ω where
  Obj _ := PUnit
  Iso _ _ := Set.univ
  refl_mem _ := trivial
  symm_mem _ := trivial
  trans_mem _ _ := trivial
  faithful _ := rfl

/-- §6.  The category `ColoredSets` of sets with vertices colored by `κ`; morphisms are the
color-preserving bijections. -/
def ColoredSets (Ω : Type u) (κ : Type v) : Cat.{u, max u v} Ω where
  Obj s := ↥s → κ
  Iso c d := {f | ∀ x, d (f x) = c x}
  refl_mem _ _ := rfl
  symm_mem {_ _ _ _ f} hf y := by simpa using (hf (f.symm y)).symm
  trans_mem hf hg x := by simpa using (hg (_)).trans (hf x)
  faithful hid := funext fun x => (hid x).symm

/-- §6.  The category `PartitionedSets` of sets with a partition (equivalence relation);
morphisms are the bijections preserving the equivalence relation. -/
def PartitionedSets (Ω : Type u) : Cat.{u, u} Ω where
  Obj s := Setoid ↥s
  Iso P Q := {f | ∀ x y, P x y ↔ Q (f x) (f y)}
  refl_mem _ _ _ := Iff.rfl
  symm_mem {_ _ _ _ f} hf x y := by
    simpa using (hf (f.symm x) (f.symm y)).symm
  trans_mem hf hg x y := (hf x y).trans (hg _ _)
  faithful hid := Setoid.ext fun x y => hid x y

/-- Composition of functors. -/
def Func.comp {Ω : Type u} {Ω' : Type u'} {Ω'' : Type u''} {C : Cat.{u, v} Ω}
    {D : Cat.{u', v'} Ω'} {E : Cat.{u'', v''} Ω''} (F : Func C D) (G : Func D E) :
    Func C E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_id X := by rw [F.map_id, G.map_id]
  map_trans f g := by rw [F.map_trans, G.map_trans]

/-- §6.  The forgetful functor to `Sets`: it is the functor `□` itself. -/
def forget {Ω : Type u} (C : Cat.{u, v} Ω) : Func C (Sets.{u, v'} Ω) where
  obj X := ⟨X.car, PUnit.unit⟩
  map f := ⟨f.1, trivial⟩
  map_id _ := rfl
  map_trans _ _ := rfl

/-- §6.  *"A canonical subset of objects in `C` is a canonical embedding of objects from
the category `Sets` into the objects of `C`."*  The subset assigned to `X` is the
underlying set `□(F(X))`. -/
def IsCanonicalSubset {Ω : Type u} (C : Cat.{u, v} Ω) (S : Pt C → Set Ω) : Prop :=
  ∃ F : Func C (Sets.{u, v} Ω), F.IsCanonicalEmbedding ∧ ∀ X, (F.obj X).car = S X

/-- §6.  *"A canonical vertex-coloring of objects in `C` is a canonical embedding of
objects from `ColoredSets` onto the objects of `C` (all vertices receive a color)."* -/
def IsCanonicalVertexColoring {Ω : Type u} (C : Cat.{u, v} Ω) (κ : Type v')
    (F : Func C (ColoredSets.{u, v'} Ω κ)) : Prop :=
  F.IsCanonicalEmbeddingOnto

/-- §6.  *"A canonical partition of objects in `C` is a canonical embedding of objects from
`PartitionedSets` onto the objects of `C` (all vertices belong to some block of the
partition)."* -/
def IsCanonicalPartition {Ω : Type u} (C : Cat.{u, v} Ω)
    (F : Func C (PartitionedSets.{u} Ω)) : Prop :=
  F.IsCanonicalEmbeddingOnto

/-- §6.  *"Note that the vertex set of a canonically embedded object is a canonical
subset."*  Composing a canonical embedding `F : C → D` with the forgetful functor `□` of
`D` gives a canonical embedding of `Sets` into `C` whose underlying sets are those of the
objects `F(X)`. -/
theorem Func.IsCanonicalEmbedding.isCanonicalSubset {Ω : Type u} {C : Cat.{u, v} Ω}
    {D : Cat.{u, v'} Ω} {F : Func C D} (hF : F.IsCanonicalEmbedding) :
    IsCanonicalSubset C fun X => (F.obj X).car :=
  ⟨F.comp (forget D), ⟨hF.car_subset, fun f x => hF.map_restrict f x⟩, fun _ => rfl⟩

/-- §6.  *"In particular, a canonical subset of `□(X)` is invariant under `Aut(X)`."* -/
theorem IsCanonicalSubset.aut_invariant {Ω : Type u} {C : Cat.{u, v} Ω} {S : Pt C → Set Ω}
    (hS : IsCanonicalSubset C S) (X : Pt C) {σ : Equiv.Perm ↥X.car} (hσ : σ ∈ C.Aut X)
    (x : ↥X.car) : ((σ x : Ω)) ∈ S X ↔ ((x : Ω)) ∈ S X := by
  obtain ⟨F, hF, hcar⟩ := hS
  have key : ∀ (τ : Equiv.Perm ↥X.car), τ ∈ C.Aut X → ∀ y : ↥X.car,
      ((y : Ω)) ∈ (F.obj X).car → ((τ y : Ω)) ∈ (F.obj X).car := by
    intro τ hτ y hy
    have := (F.autHom X ⟨τ, hτ⟩ ⟨(y : Ω), hy⟩).2
    rwa [hF.autHom_apply X ⟨τ, hτ⟩ ⟨(y : Ω), hy⟩] at this
  rw [← hcar X]
  constructor
  · intro h
    have := key σ⁻¹ ((C.Aut X).inv_mem hσ) (σ x) h
    simpa using this
  · exact key σ hσ x

/-! ### The category of `G`-isomorphisms of strings

*"A group `G ≤ S(Ω)` defines the category of `G`-isomorphisms of strings on the domain `Ω`;
the natural notation for this category ... would seem to be `GStrings`."*

By §11.1, a string over `Ω` is a map `x : Ω → Σ`, and `σ ∈ S(Ω)` is a `G`-isomorphism of
`x, y` if `σ ∈ G` and `x^σ = y`, where `x^σ(i) = x(i^{σ⁻¹})`.  With the left-action
convention of `Workspace.Prelim.PermGroups` (the paper's `i^σ` is Lean's `σ i`), the
paper's `x^σ` is `x ∘ σ⁻¹`.  All objects have the same underlying set `Ω` (as
`Set.univ`), so all morphisms are permutations, as in the paper's remark. -/
def GStrings {Ω : Type u} (G : Subgroup (Equiv.Perm Ω)) (Alph : Type v) : Cat.{u, max u v} Ω where
  Obj s := {x : Ω → Alph // s = Set.univ}
  Iso {s t} x y :=
    {f | ∃ σ : Equiv.Perm Ω, σ ∈ G ∧
      (∀ a : ↥s, ((f a : Ω)) = σ (a : Ω)) ∧ (x.1 ∘ (σ⁻¹ : Equiv.Perm Ω)) = y.1}
  refl_mem x := ⟨1, G.one_mem, fun _ => rfl, by simp⟩
  symm_mem {s t X Y f} := by
    rintro ⟨σ, hσ, hf, hxy⟩
    refine ⟨σ⁻¹, G.inv_mem hσ, ?_, ?_⟩
    · intro a
      have h1 : ((f (f.symm a) : Ω)) = σ ((f.symm a : Ω)) := hf _
      rw [Equiv.apply_symm_apply] at h1
      rw [h1]; simp
    · rw [← hxy]; ext a; simp
  trans_mem {s t r X Y Z f g} := by
    rintro ⟨σ, hσ, hf, hxy⟩ ⟨τ, hτ, hg, hyz⟩
    refine ⟨τ * σ, G.mul_mem hτ hσ, ?_, ?_⟩
    · intro a; rw [Equiv.trans_apply, hg, hf]; rfl
    · rw [← hyz, ← hxy]; ext a; simp [Function.comp]
  faithful {s X Y} := by
    rintro ⟨σ, hσ, hf, hxy⟩
    have hs : s = Set.univ := X.2
    have hσid : ∀ a : Ω, σ a = a := by
      intro a
      have ha : a ∈ s := by rw [hs]; trivial
      have := hf ⟨a, ha⟩
      simpa using this.symm
    have : σ = 1 := Equiv.ext hσid
    subst this
    have : X.1 = Y.1 := by simpa using hxy
    exact Subtype.ext this

/-! ### Bridge to Mathlib's `CategoryTheory.Groupoid` -/

/-- Bridge.  A category in the sense of the paper is a groupoid in Mathlib's sense, with
objects the pairs (underlying set, object) and morphisms the paper's isomorphisms.  This
instance is only a sanity check; the rest of the development works with `Babai.Cat`
directly, because §6 speaks about morphisms as bijections of underlying sets. -/
instance Cat.groupoid {Ω : Type u} (C : Cat.{u, v} Ω) : CategoryTheory.Groupoid (Pt C) where
  Hom X Y := Hom C X Y
  id X := Hom.id X
  comp f g := Hom.trans f g
  id_comp _ := Hom.ext fun _ => rfl
  comp_id _ := Hom.ext fun _ => rfl
  assoc _ _ _ := Hom.ext fun _ => rfl
  inv f := Hom.symm f
  inv_comp f := Hom.symm_trans f
  comp_inv f := Hom.trans_symm f

end Babai
