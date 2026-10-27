/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: orbit–stabilizer bounds.
-/
import Workspace.AltQuotients.DM52.Recog

/-!
# Orbit–stabilizer bounds

Two forms of the orbit–stabilizer theorem for groups of permutations, used to compute and
bound the orders of the small primitive groups in [DiM, Thm. 5.2A,B].
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

/-- The orbit–stabilizer theorem for a transitive group: `|G| = n · |G_a|`. -/
theorem card_eq_card_mul_stabilizer {α : Type*} [Fintype α] {G : Subgroup (Perm α)}
    (hG : IsPretransitive G α) (a : α) :
    Nat.card G = Fintype.card α * Nat.card (G ⊓ stabilizer (Perm α) a : Subgroup _) := by
  rw [card_eq_ncard_orbit_mul G a, MulAction.orbit_eq_univ, Set.ncard_univ,
    Nat.card_eq_fintype_card]

/-- Orbit–stabilizer upper bound: if `G` maps `a` into `S`, then `|G| ≤ |S| · |G_a|`. -/
theorem card_le_card_mul_of_mapsTo {α : Type*} [Finite α] (G : Subgroup (Perm α)) (a : α)
    (S : Finset α) (hS : ∀ g ∈ G, g a ∈ S) :
    Nat.card G ≤ S.card * Nat.card (G ⊓ stabilizer (Perm α) a : Subgroup _) := by
  rw [card_eq_ncard_orbit_mul G a]
  apply Nat.mul_le_mul_right
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
  rintro b ⟨⟨g, hg⟩, rfl⟩
  exact hS g hg

end Babai.DM52
