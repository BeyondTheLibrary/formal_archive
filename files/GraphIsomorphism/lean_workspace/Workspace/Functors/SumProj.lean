/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 6: the two summand projections of a disjoint union of categories.
-/
import Workspace.Functors.Compose

/-!
# §6 The summands of `Cat.sum`, as functors

The outcome of a step of §9 is *either* one kind of object *or* another
(`Babai.Cat.sum`), and the next step treats the two kinds differently
(`Babai.FindsAtMultCost.cases`).  On the branch where the outcome is of the second kind,
the next step has to be applied to that second component; this file makes the passage to a
summand a functor on the full subcategory of the objects that lie in that summand.

There are no morphisms between the two summands (`Babai.Cat.sum`), so each of the two
full subcategories is closed under isomorphism and the projection is an isomorphism of
categories onto the summand.  Both projections are canonical embeddings: they do not move
the underlying set and act on morphisms by the identity.
-/

namespace Babai

namespace Cat

universe u v

variable {Ω : Type u} (C D : Cat.{u, v} Ω)

/-- The full subcategory of `Cat.sum C D` on the objects that lie in the first summand. -/
def sumIsLeft : ∀ s : Set Ω, (Cat.sum C D).Obj s → Prop := fun _ Z => Z.isLeft

/-- The full subcategory of `Cat.sum C D` on the objects that lie in the second
summand. -/
def sumIsRight : ∀ s : Set Ω, (Cat.sum C D).Obj s → Prop := fun _ Z => Z.isRight

variable {C D}

theorem sum_iso_left {s t : Set Ω} {Z : (Cat.sum C D).Obj s} {W : (Cat.sum C D).Obj t}
    (hZ : Z.isLeft) (hW : W.isLeft) {f : ↥s ≃ ↥t} (hf : f ∈ (Cat.sum C D).Iso Z W) :
    f ∈ C.Iso (Z.getLeft hZ) (W.getLeft hW) := by
  cases Z with
  | inl Z => cases W with
    | inl W => exact hf
    | inr W => exact absurd hW (by simp)
  | inr Z => exact absurd hZ (by simp)

theorem sum_iso_right {s t : Set Ω} {Z : (Cat.sum C D).Obj s} {W : (Cat.sum C D).Obj t}
    (hZ : Z.isRight) (hW : W.isRight) {f : ↥s ≃ ↥t} (hf : f ∈ (Cat.sum C D).Iso Z W) :
    f ∈ D.Iso (Z.getRight hZ) (W.getRight hW) := by
  cases Z with
  | inl Z => exact absurd hZ (by simp)
  | inr Z => cases W with
    | inl W => exact absurd hW (by simp)
    | inr W => exact hf

variable (C D)

/-- §6.  The first summand, as a functor on the full subcategory of the objects that lie
in it. -/
def sumLeftProj : Func ((Cat.sum C D).full (sumIsLeft C D)) C where
  obj X := ⟨X.car, X.obj.1.getLeft X.obj.2⟩
  map f := ⟨f.1, sum_iso_left _ _ f.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

/-- §6.  The second summand, as a functor on the full subcategory of the objects that lie
in it. -/
def sumRightProj : Func ((Cat.sum C D).full (sumIsRight C D)) D where
  obj X := ⟨X.car, X.obj.1.getRight X.obj.2⟩
  map f := ⟨f.1, sum_iso_right _ _ f.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem sumLeftProj_isCanonicalEmbedding :
    (sumLeftProj C D).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

theorem sumRightProj_isCanonicalEmbedding :
    (sumRightProj C D).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

@[simp] theorem sumLeftProj_car (X : Pt ((Cat.sum C D).full (sumIsLeft C D))) :
    ((sumLeftProj C D).obj X).car = X.car := rfl

@[simp] theorem sumRightProj_car (X : Pt ((Cat.sum C D).full (sumIsRight C D))) :
    ((sumRightProj C D).obj X).car = X.car := rfl

/-- §6.  The first summand, as a functor into the disjoint union: an object of `C` is an
object of `Cat.sum C D`, and a morphism is itself. -/
def sumLeftIncl : Func C (Cat.sum C D) where
  obj X := ⟨X.car, Sum.inl X.obj⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

/-- §6.  The second summand, as a functor into the disjoint union. -/
def sumRightIncl : Func D (Cat.sum C D) where
  obj X := ⟨X.car, Sum.inr X.obj⟩
  map f := ⟨f.1, f.2⟩
  map_id _ := Subtype.ext rfl
  map_trans _ _ := Subtype.ext rfl

theorem sumLeftIncl_isCanonicalEmbedding :
    (sumLeftIncl C D).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

theorem sumRightIncl_isCanonicalEmbedding :
    (sumRightIncl C D).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

end Cat

universe u v

/-- §6.  The inclusion of a full subcategory is a canonical embedding: it moves neither the
underlying set nor the morphisms. -/
theorem Cat.fullIncl_isCanonicalEmbedding {Ω : Type u} (C : Cat.{u, v} Ω)
    (P : ∀ s : Set Ω, C.Obj s → Prop) : (C.fullIncl P).IsCanonicalEmbedding where
  car_subset _ := subset_rfl
  map_restrict _ _ := rfl

/-- §6.  A functor whose image lies in a full subcategory, read as a functor into that full
subcategory.  Morphisms are unchanged, so this is the same functor with a smaller target.

It is what lets a later step of §9 be applied on the branch of a canonical case
distinction: the branch is a full subcategory of the pairs, and the object found there
lies in one summand of `Babai.Cat.sum`. -/
def Func.intoFull {Ω : Type u} {A B : Cat.{u, v} Ω} (F : Func A B)
    (Q : ∀ s : Set Ω, B.Obj s → Prop)
    (h : ∀ X : Pt A, Q (F.obj X).car (F.obj X).obj) : Func A (B.full Q) where
  obj X := ⟨(F.obj X).car, ⟨(F.obj X).obj, h X⟩⟩
  map f := ⟨(F.map f).1, (F.map f).2⟩
  map_id X := Subtype.ext (congrArg Subtype.val (F.map_id X))
  map_trans f g := Subtype.ext (congrArg Subtype.val (F.map_trans f g))

theorem Func.intoFull_isCanonicalEmbedding {Ω : Type u} {A B : Cat.{u, v} Ω} {F : Func A B}
    (hF : F.IsCanonicalEmbedding) (Q : ∀ s : Set Ω, B.Obj s → Prop)
    (h : ∀ X : Pt A, Q (F.obj X).car (F.obj X).obj) :
    (F.intoFull Q h).IsCanonicalEmbedding where
  car_subset X := hF.car_subset X
  map_restrict f x := hF.map_restrict f x

end Babai

