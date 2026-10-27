/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: recognizing the exceptional primitive groups.
-/
import Workspace.AltQuotients.DM52.Transport

/-!
# Recognition tools for the small primitive groups

The exceptional primitive groups of [DiM, Thm. 5.2A,B] (degrees `5` to `9`) are recognized
as follows.  After Sylow's theorem has fixed the order of `G` and placed the normalizer of a
Sylow subgroup inside `G`, we relabel the points so that `G` contains some explicit
permutations; then we exhibit one more element `g ∈ G` from an explicit finite list of
candidates.  Every candidate either lies in the model group, or some word in `g` and the
known elements is a `3`-cycle (which a primitive group `G ≠ A` cannot contain, by Jordan's
theorem) or an element of order `5` (when `5 ∤ |G|`).  The subgroup generated is then large
enough, by the orbit–stabilizer theorem, to be all of `G`.

This file provides the words, the forbidden elements, and the orbit–stabilizer bound.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

section Words

variable {α : Type*}

/-- Relabeling by a permutation `σ` of the domain itself: `g ∈ σ G σ⁻¹ ↔ σ⁻¹ g σ ∈ G`. -/
theorem mem_relabel_perm (σ : Perm α) {G : Subgroup (Perm α)} {g : Perm α} :
    g ∈ relabel σ G ↔ σ⁻¹ * g * σ ∈ G := by
  rw [mem_relabel]
  have : (σ : α ≃ α).symm.permCongr g = σ⁻¹ * g * σ := by
    ext x; simp [Perm.mul_apply, Perm.inv_def]
  rw [this]

/-- Relabeling twice. -/
theorem relabel_relabel_perm (σ τ : Perm α) (G : Subgroup (Perm α)) :
    relabel σ (relabel τ G) = relabel (σ * τ) G := by
  ext g
  rw [mem_relabel_perm, mem_relabel_perm, mem_relabel_perm]
  simp [mul_assoc]

/-- The value of the word `w` (a list of indices) in the list `gens` of permutations; an index
out of range stands for the identity. -/
def evalWord (gens : List (Perm α)) (w : List ℕ) : Perm α :=
  (w.map fun i => gens.getD i 1).prod

/-- A word in elements of `G` lies in `G`. -/
theorem evalWord_mem {G : Subgroup (Perm α)} {gens : List (Perm α)}
    (h : ∀ x ∈ gens, x ∈ G) (w : List ℕ) : evalWord gens w ∈ G := by
  unfold evalWord
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  rw [List.getD_eq_getElem?_getD]
  cases h' : gens[i]? with
  | none => exact G.one_mem
  | some y => exact h y (List.mem_of_getElem? h')

end Words

section Forbidden

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Some word in `gens` is a `3`-cycle (has support of size `3`). -/
def Bad3 (gens : List (Perm α)) (words : List (List ℕ)) : Prop :=
  ∃ w ∈ words, (evalWord gens w).support.card = 3

instance (gens : List (Perm α)) (words : List (List ℕ)) : Decidable (Bad3 gens words) := by
  unfold Bad3; infer_instance

/-- Some word in `gens` is a `3`-cycle or an element of order `5`. -/
def Bad35 (gens : List (Perm α)) (words : List (List ℕ)) : Prop :=
  ∃ w ∈ words, (evalWord gens w).support.card = 3 ∨
    (evalWord gens w ≠ 1 ∧ evalWord gens w ^ 5 = 1)

instance (gens : List (Perm α)) (words : List (List ℕ)) : Decidable (Bad35 gens words) := by
  unfold Bad35; infer_instance

/-- **Jordan's theorem for `3`-cycles** ([DiM, Theorem 3.3A]): a primitive group containing
a `3`-cycle contains `Alt(α)`. -/
theorem support_card_ne_three {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) {g : Perm α} (hg : g ∈ G) : g.support.card ≠ 3 :=
  fun h => hA (alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
    (card_support_eq_three_iff.mp h) hg)

omit [Fintype α] [DecidableEq α] in
/-- Lagrange: if `5 ∤ |G|`, no element of `G` has order `5`. -/
theorem not_order_five {G : Subgroup (Perm α)} (h5 : ¬ 5 ∣ Nat.card G) {g : Perm α}
    (hg : g ∈ G) : ¬ (g ≠ 1 ∧ g ^ 5 = 1) := by
  rintro ⟨h1, h2⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ho : orderOf g = 5 := orderOf_eq_prime h2 h1
  apply h5
  rw [← ho, ← Subgroup.orderOf_mk g hg]
  exact orderOf_dvd_natCard _

theorem not_bad3 {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) {gens : List (Perm α)} (h : ∀ x ∈ gens, x ∈ G)
    (words : List (List ℕ)) : ¬ Bad3 gens words := by
  rintro ⟨w, -, hw⟩
  exact support_card_ne_three hG hA (evalWord_mem h w) hw

theorem not_bad35 {G : Subgroup (Perm α)} (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) (h5 : ¬ 5 ∣ Nat.card G) {gens : List (Perm α)}
    (h : ∀ x ∈ gens, x ∈ G) (words : List (List ℕ)) : ¬ Bad35 gens words := by
  rintro ⟨w, -, hw | hw⟩
  · exact support_card_ne_three hG hA (evalWord_mem h w) hw
  · exact not_order_five h5 (evalWord_mem h w) hw

end Forbidden

section OrbitStabilizer

variable {α : Type*}

/-- Orbit–stabilizer: `|H| = |a^H| · |H_a|`. -/
theorem card_eq_ncard_orbit_mul (H : Subgroup (Perm α)) [Finite H] (a : α) :
    Nat.card H = (orbit H a).ncard * Nat.card (H ⊓ stabilizer (Perm α) a : Subgroup _) := by
  have h1 := MulAction.index_stabilizer H a
  have h2 := (stabilizer H a).card_mul_index
  have h3 : stabilizer H a = (stabilizer (Perm α) a).subgroupOf H := by
    ext h; simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]; rfl
  rw [h3, card_subgroupOf, inf_comm] at h2
  rw [← h2, ← h1, h3, mul_comm]

/-- Orbit–stabilizer lower bound: if every point of `S` is an image of `a` under `H`, and
`|H_a| ≥ k`, then `|H| ≥ |S| k`. -/
theorem card_le_card_of_orbit [Finite α] (H : Subgroup (Perm α)) (a : α) (S : Finset α)
    (hS : ∀ b ∈ S, ∃ h ∈ H, h a = b) {k : ℕ}
    (hk : k ≤ Nat.card (H ⊓ stabilizer (Perm α) a : Subgroup _)) :
    S.card * k ≤ Nat.card H := by
  classical
  rw [card_eq_ncard_orbit_mul H a]
  apply Nat.mul_le_mul _ hk
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro b hb
  obtain ⟨h, hh, rfl⟩ := hS b hb
  exact ⟨⟨h, hh⟩, rfl⟩

/-- A finset of elements of `H` has at most `|H|` elements. -/
theorem le_card_of_finset {G : Type*} [Group G] {H : Subgroup G} [Finite H] (s : Finset G)
    (hs : ∀ x ∈ s, x ∈ H) : s.card ≤ Nat.card H := by
  rw [← Set.ncard_coe_finset]
  have : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  rw [this]
  exact Set.ncard_le_ncard (fun x hx => hs x hx) (Set.toFinite _)

/-- A subgroup contained in a finset has at most that many elements. -/
theorem card_le_of_subset_finset {G : Type*} [Group G] {H : Subgroup G} (s : Finset G)
    (hs : ∀ x ∈ H, x ∈ s) : Nat.card H ≤ s.card := by
  rw [← Set.ncard_coe_finset]
  have : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
  rw [this]
  exact Set.ncard_le_ncard (fun x hx => hs x hx) (Finset.finite_toSet _)

end OrbitStabilizer

section Iso

variable {α : Type*}

/-- An injective hom onto `G` gives `G ≃* H`. -/
noncomputable def mulEquivOfRangeEq {H : Type*} [Group H] (f : H →* Perm α)
    (hf : Function.Injective f) {G : Subgroup (Perm α)} (h : f.range = G) : G ≃* H :=
  (MulEquiv.subgroupCongr h.symm).trans (MonoidHom.ofInjective hf).symm

end Iso

end Babai.DM52
