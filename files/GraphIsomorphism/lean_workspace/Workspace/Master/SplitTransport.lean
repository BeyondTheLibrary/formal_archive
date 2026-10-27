/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4c: the outcomes of Theorem 9.2.3 move along a permutation of `Γ`.
-/
import Workspace.Master.Versions
import Workspace.SplitOrJohnson.Defs

/-!
# The outcome category of Theorem 9.2.3 is transportable

`Babai.exists_canonicalVersions` asks for an action of `S(Γ)` on the objects of the output
category which is the category's own (`Babai.IsCatAction`).  A category in which every
object can be pushed forward along every permutation carries exactly one such action
(`Babai.Cat.transportAction`), so all that has to be checked for Theorem 9.2.3 is that its
output category `Babai.SplitOutcomes` — a colored partition or a Johnson scheme — is
transportable.

Pushing forward is in each case the obvious thing: move the underlying set by `π` and read
the colors, the partition or the edge colors back through `π⁻¹`.  What has to be said is
that the result is again an object of the category, which for Johnson schemes means that a
Johnson coloring stays a Johnson coloring (the labelling `↥s ≃ Γ^{(t)}` is composed with
`π⁻¹`).

`Babai.isCatAction_splitOutcomes` is the conclusion: an action of `S(Γ)` on
`Pt (SplitOutcomes Γ)` which is the category's own.
-/

namespace Babai

open Equiv

universe u

section Builder

variable {Γ : Type}

/-- The bijection `s ≃ π(s)` that a permutation induces. -/
noncomputable def permImage (π : Equiv.Perm Γ) (s : Set Γ) : ↥s ≃ ↥(π '' s) :=
  Equiv.Set.image (π : Γ → Γ) s π.injective

@[simp] theorem permImage_apply (π : Equiv.Perm Γ) (s : Set Γ) (x : ↥s) :
    ((permImage π s x : ↥(π '' s)) : Γ) = π (x : Γ) := rfl

/-- A bijection `↥s ≃ ↥(π '' s)` that acts as `π` is `Babai.permImage`. -/
theorem eq_permImage {π : Equiv.Perm Γ} {s : Set Γ} (f : ↥s ≃ ↥(π '' s))
    (hf : ∀ x, ((f x : ↥(π '' s)) : Γ) = π (x : Γ)) : f = permImage π s :=
  Equiv.ext fun x => Subtype.ext (by rw [hf x, permImage_apply])

/-- **How transportability is checked**: give a pushforward of every object along every
permutation for which the induced bijection is a morphism. -/
theorem Cat.isTransportable_of {C : Cat.{0, 0} Γ}
    (T : ∀ (π : Equiv.Perm Γ) (X : Pt C), C.Obj (π '' X.car))
    (hT : ∀ (π : Equiv.Perm Γ) (X : Pt C), permImage π X.car ∈ C.Iso X.obj (T π X)) :
    C.IsTransportable := by
  intro π X
  refine ⟨⟨π '' X.car, T π X⟩, rfl, ?_⟩
  have hf : permHom π X (⟨π '' X.car, T π X⟩ : Pt C) rfl = permImage π X.car :=
    eq_permImage _ fun x => rfl
  rw [hf]
  exact hT π X

end Builder

/-! ### The two kinds of outcome -/

section Outcomes

variable {Γ : Type}

/-- A colored partition, pushed forward along a permutation: the colors and the partition
are read back through the inverse bijection. -/
def ColoredPartition.pushforward {s t : Type} (e : s ≃ t) {κ : Type}
    (P : ColoredPartition s κ) : ColoredPartition t κ where
  color y := P.color (e.symm y)
  part := Setoid.comap e.symm P.part
  part_le_color h := P.part_le_color h

/-- §7.1: the category of colored partitions is transportable. -/
theorem isTransportable_coloredPartitions {κ : Type} :
    (ColoredPartitions.{0, 0} Γ κ).IsTransportable := by
  refine Cat.isTransportable_of
    (fun π X => ColoredPartition.pushforward (permImage π X.car) X.obj) ?_
  intro π X
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · show X.obj.color ((permImage π X.car).symm ((permImage π X.car) x)) = X.obj.color x
    rw [Equiv.symm_apply_apply]
  · show X.obj.part x y ↔ X.obj.part ((permImage π X.car).symm ((permImage π X.car) x))
      ((permImage π X.car).symm ((permImage π X.car) y))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- §9.2: the category of Johnson schemes is transportable.  A Johnson coloring stays one:
the labelling by the `t`-subsets of `[k]` is read back through the inverse bijection. -/
theorem isTransportable_johnsonSchemes : (JohnsonSchemes.{0} Γ).IsTransportable := by
  refine Cat.isTransportable_of
    (fun π X => ⟨fun a b => X.obj.1 ((permImage π X.car).symm a)
      ((permImage π X.car).symm b), ?_⟩) ?_
  · obtain ⟨k, t, φ, ht, hk, hφ⟩ := X.obj.2
    exact ⟨k, t, (permImage π X.car).symm.trans φ, ht, hk, fun a b => hφ _ _⟩
  · intro π X
    show ∀ a b, X.obj.1 ((permImage π X.car).symm ((permImage π X.car) a))
      ((permImage π X.car).symm ((permImage π X.car) b)) = X.obj.1 a b
    intro a b
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The disjoint union of two transportable categories is transportable. -/
theorem Cat.isTransportable_sum {C D : Cat.{0, 0} Γ} (hC : C.IsTransportable)
    (hD : D.IsTransportable) : (Cat.sum C D).IsTransportable := by
  intro π X
  obtain ⟨s, Z⟩ := X
  cases Z with
  | inl P =>
    obtain ⟨Y, hY, hiso⟩ := hC π ⟨s, P⟩
    refine ⟨⟨Y.car, Sum.inl Y.obj⟩, hY, ?_⟩
    show permHom π (⟨s, Sum.inl P⟩ : Pt (Cat.sum C D)) ⟨Y.car, Sum.inl Y.obj⟩ hY ∈
      C.Iso P Y.obj
    have he : permHom π (⟨s, Sum.inl P⟩ : Pt (Cat.sum C D)) ⟨Y.car, Sum.inl Y.obj⟩ hY
        = permHom π (⟨s, P⟩ : Pt C) Y hY := Equiv.ext fun x => Subtype.ext rfl
    rw [he]
    exact hiso
  | inr J =>
    obtain ⟨Y, hY, hiso⟩ := hD π ⟨s, J⟩
    refine ⟨⟨Y.car, Sum.inr Y.obj⟩, hY, ?_⟩
    show permHom π (⟨s, Sum.inr J⟩ : Pt (Cat.sum C D)) ⟨Y.car, Sum.inr Y.obj⟩ hY ∈
      D.Iso J Y.obj
    have he : permHom π (⟨s, Sum.inr J⟩ : Pt (Cat.sum C D)) ⟨Y.car, Sum.inr Y.obj⟩ hY
        = permHom π (⟨s, J⟩ : Pt D) Y hY := Equiv.ext fun x => Subtype.ext rfl
    rw [he]
    exact hiso

/-- §9.2: **the outcome category of Theorems 9.2.1–9.2.3 is transportable**. -/
theorem isTransportable_splitOutcomes : (SplitOutcomes.{0} Γ).IsTransportable :=
  Cat.isTransportable_sum isTransportable_coloredPartitions isTransportable_johnsonSchemes

/-- §9.2, §14.2: **`S(Γ)` acts on the outcomes of Theorem 9.2.3**, and the action is the
category's own (`Babai.IsCatAction`), which is what
`Babai.exists_canonicalVersions_on` asks for. -/
theorem exists_isCatAction_splitOutcomes :
    ∃ inst : MulAction (Equiv.Perm Γ) (Pt (SplitOutcomes.{0} Γ)),
      @IsCatAction Γ (SplitOutcomes Γ) inst :=
  ⟨Cat.transportAction isTransportable_splitOutcomes,
    isCatAction_transportAction isTransportable_splitOutcomes⟩

end Outcomes

end Babai
