/-
Auxiliary lemmas for the formalization of §4 and §5 of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Nothing here is from the paper; these are Mathlib-level facts that the §4/§5 files need
and that the files of §2 and §3 do not provide.
-/
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators

namespace Babai

open scoped Classical in
/-- `Set.ncard` of a set-builder set over a finite type, as a `Finset.card`. -/
theorem ncard_setOf {α : Type*} [Fintype α] (p : α → Prop) :
    {x | p x}.ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

open scoped Classical in
/-- Counting a finite set by the fibers of a map into a finite type. -/
theorem ncard_fiberwise {α β : Type*} [Fintype α] [Fintype β] (p : α → Prop) (f : α → β)
    (Q : β → Prop) (hf : ∀ x, p x → Q (f x)) :
    {x | p x}.ncard = ∑ b ∈ Finset.univ.filter Q, {x | p x ∧ f x = b}.ncard := by
  rw [ncard_setOf]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := f) (s := Finset.univ.filter p) (t := Finset.univ.filter Q)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hf x (by simpa using hx)⟩)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ncard_setOf]
  congr 1
  ext x
  simp

open scoped Classical in
/-- Two maps out of a finite type whose fibers have equal sizes still have fibers of equal
sizes after composition with an arbitrary map.  (The index type `β` is not assumed finite,
so the fibers are collected over the image, which is finite because `α` is.) -/
theorem ncard_fiber_comp_congr {α β γ : Type*} [Finite α] (f g : α → β) (F : β → γ)
    (h : ∀ b : β, {x | f x = b}.ncard = {x | g x = b}.ncard) (c : γ) :
    {x | F (f x) = c}.ncard = {x | F (g x) = c}.ncard := by
  cases nonempty_fintype α
  set T : Finset β :=
    ((Finset.univ.image f) ∪ (Finset.univ.image g)).filter (fun b => F b = c) with hT
  have key : ∀ e : α → β, (∀ x : α, e x ∈ (Finset.univ.image f) ∪ (Finset.univ.image g)) →
      {x | F (e x) = c}.ncard = ∑ b ∈ T, {x | e x = b}.ncard := by
    intro e he
    rw [ncard_setOf]
    rw [Finset.card_eq_sum_card_fiberwise (f := e)
      (s := Finset.univ.filter (fun x => F (e x) = c)) (t := T)
      (fun x hx => Finset.mem_filter.2 ⟨he x, by simpa using hx⟩)]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : F b = c := (Finset.mem_filter.1 hb).2
    rw [ncard_setOf]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hx => hx.2, fun hx => ⟨by rw [hx]; exact hb', hx⟩⟩
  rw [key f (fun x => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))),
    key g (fun x => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))]
  exact Finset.sum_congr rfl fun b _ => h b

end Babai
