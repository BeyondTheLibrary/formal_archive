/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.1: Resilience of Johnson schemes, the combinatorial step of Proposition 9.1.1.
-/
import Workspace.SplitOrJohnson.Defs

/-!
# §9.1 The combinatorial step of Proposition 9.1.1

Proposition 9.1.1 is *"an immediate consequence of Corollary 9.1.3"*.  Corollary 9.1.3
gives a set `Y` of vertices of relative size `> 1 - ε` on which a subgroup of the
automorphism group acts primitively; the step from there to *"there is no canonical
`(1-ε)`-partition"* is the lemma of this file, `Babai.exists_ncard_block_ge_of_primitive_on`:
a colored partition invariant under a group that acts primitively on `Y` has a block that
contains all of `Y`, hence `ρ(Π) ≥ |Y| > (1-ε)n`.

The paper leaves this step unsaid, and it is not quite immediate: primitivity alone also
allows the partition to cut `Y` into singletons.  That case is killed by *admissibility*
(Def. 7.1.1: *"if a color class has `≥ 2` blocks then all its blocks have size `≥ 2`"*)
together with `2|Y| > n`: each block meeting `Y` would meet it in one point and would have
a second point outside `Y`, so `|Y| ≤ n - |Y|`.  Both `2|Y| > n` and `|Y| ≥ 2` come from
`|Y| > (1-ε)n` with `ε ≤ 1/3`.
-/

namespace Babai

open ColoredPartition

/-- The combinatorial step of Proposition 9.1.1 (§9.1).  Let `Π` be an admissible colored
partition of a finite set `V`, invariant under a group `H ≤ S(V)`, and let `Y ⊆ V` be an
`H`-invariant set on which `H` acts transitively and primitively, with `|Y| ≥ 2` and
`2|Y| > |V|`.  Then some block of `Π` is at least as large as `Y`.

Proof.  Fix `y₀ ∈ Y`.  The set `B = B(y₀) ∩ Y` is nonempty, contained in `Y`, and is a
block of imprimitivity for `H` on `Y`: for `σ ∈ H` the image `σ(B)` is `B(σy₀) ∩ Y`, and
two blocks of a partition are equal or disjoint.  By primitivity `B = Y` — which is the
conclusion — or `B = {y₀}`.  In the second case transitivity gives `B(y) ∩ Y = {y}` for
every `y ∈ Y`; all points of `Y` have the same color, so the color class of `y₀` contains
`Y` and has `≥ 2` elements, so admissibility gives `|B(y)| ≥ 2`, so each `B(y)` has a
point outside `Y`.  Different `y` give different points (the blocks are disjoint), so
`|Y| ≤ |V| - |Y|`, against `2|Y| > |V|`.

The hypothesis `hprim` is the paper's primitivity of the action on `Y` (§2.2.1), stated
for the subsets of `Y`: a nonempty block of imprimitivity inside `Y` is `Y` or a
singleton. -/
theorem exists_ncard_block_ge_of_primitive_on
    {V : Type*} [Fintype V] [DecidableEq V] {κ : Type*} (P : ColoredPartition V κ)
    (H : Subgroup (Equiv.Perm V)) (Y : Set V)
    (hcolor : ∀ σ ∈ H, ∀ x : V, P.color (σ x) = P.color x)
    (hpart : ∀ σ ∈ H, ∀ x y : V, P.part x y → P.part (σ x) (σ y))
    (hYinv : ∀ σ ∈ H, ∀ x ∈ Y, σ x ∈ Y)
    (htrans : ∀ x ∈ Y, ∀ y ∈ Y, ∃ σ ∈ H, σ x = y)
    (hprim : ∀ B : Set V, B ⊆ Y → B.Nonempty →
      (∀ σ ∈ H, (σ : Equiv.Perm V) '' B = B ∨ ((σ : Equiv.Perm V) '' B) ∩ B = ∅) →
      B = Y ∨ ∃ x, B = {x})
    (hadm : P.IsAdmissible) (hY2 : 2 ≤ Y.ncard)
    (hcard : Fintype.card V < 2 * Y.ncard) :
    ∃ x : V, Y.ncard ≤ (P.block x).ncard := by
  classical
  -- `Y` is nonempty, since `|Y| ≥ 2`.
  obtain ⟨y₀, hy₀⟩ : Y.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h] at hY2
    simp at hY2
  -- the image of a block of `Π` under `σ ∈ H` is a block of `Π`
  have himg_block : ∀ σ ∈ H, ∀ x : V, (σ : Equiv.Perm V) '' P.block x = P.block (σ x) := by
    intro σ hσ x
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨y, hy, rfl⟩
      exact hpart σ hσ y x hy
    · intro z hz
      refine ⟨σ.symm z, ?_, σ.apply_symm_apply z⟩
      have h := hpart σ⁻¹ (Subgroup.inv_mem H hσ) z (σ x) hz
      simpa [Equiv.Perm.inv_def] using h
  -- `Y` is invariant, as a set
  have himg_Y : ∀ σ ∈ H, (σ : Equiv.Perm V) '' Y = Y := by
    intro σ hσ
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨y, hy, rfl⟩
      exact hYinv σ hσ y hy
    · intro z hz
      refine ⟨σ.symm z, ?_, σ.apply_symm_apply z⟩
      have h := hYinv σ⁻¹ (Subgroup.inv_mem H hσ) z hz
      simpa [Equiv.Perm.inv_def] using h
  -- the image of `B(x) ∩ Y` is `B(σx) ∩ Y`
  have himg : ∀ σ ∈ H, ∀ x : V,
      (σ : Equiv.Perm V) '' (P.block x ∩ Y) = P.block (σ x) ∩ Y := by
    intro σ hσ x
    rw [Set.image_inter (σ : Equiv.Perm V).injective, himg_block σ hσ x, himg_Y σ hσ]
  -- `B(y) ∩ Y` is a block of imprimitivity inside `Y`
  have hblockY : ∀ y ∈ Y, P.block y ∩ Y = Y ∨ P.block y ∩ Y = {y} := by
    intro y hy
    have hsub : P.block y ∩ Y ⊆ Y := Set.inter_subset_right
    have hne : (P.block y ∩ Y).Nonempty := ⟨y, P.mem_block_self y, hy⟩
    have hbl : ∀ σ ∈ H, (σ : Equiv.Perm V) '' (P.block y ∩ Y) = P.block y ∩ Y ∨
        ((σ : Equiv.Perm V) '' (P.block y ∩ Y)) ∩ (P.block y ∩ Y) = ∅ := by
      intro σ hσ
      rw [himg σ hσ y]
      by_cases hp : P.part (σ y) y
      · left; rw [P.block_eq_of_part hp]
      · right
        have hd : Disjoint (P.block (σ y)) (P.block y) := P.block_disjoint hp
        rw [Set.eq_empty_iff_forall_notMem]
        rintro z ⟨⟨hz1, -⟩, hz2, -⟩
        exact (Set.disjoint_left.1 hd) hz1 hz2
    rcases hprim _ hsub hne hbl with h | ⟨x, hx⟩
    · exact Or.inl h
    · right
      have hymem : y ∈ ({x} : Set V) := hx ▸ ⟨P.mem_block_self y, hy⟩
      rw [Set.mem_singleton_iff] at hymem
      rw [hx, hymem]
  -- either some block contains `Y` (the conclusion), or every block meets `Y` in a point
  by_cases hbig : ∃ y ∈ Y, P.block y ∩ Y = Y
  · obtain ⟨y, -, hy⟩ := hbig
    refine ⟨y, Set.ncard_le_ncard ?_ (Set.toFinite _)⟩
    rw [← hy]
    exact Set.inter_subset_left
  · exfalso
    rw [not_exists] at hbig
    simp only [not_and] at hbig
    have hsing : ∀ y ∈ Y, P.block y ∩ Y = {y} := by
      intro y hy
      rcases hblockY y hy with h | h
      · exact absurd h (hbig y hy)
      · exact h
    -- all points of `Y` have the same color, so the color class of `y` contains `Y`
    have hcol : ∀ y ∈ Y, P.color y = P.color y₀ := by
      intro y hy
      obtain ⟨σ, hσ, hσy⟩ := htrans y hy y₀ hy₀
      rw [← hσy, hcolor σ hσ y]
    have hclass : ∀ y ∈ Y, Y ⊆ P.colorClass (P.color y) := by
      intro y hy z hz
      show P.color z = P.color y
      rw [hcol z hz, hcol y hy]
    -- admissibility gives a second point in each block, and it lies outside `Y`
    have hex : ∀ y ∈ Y, ∃ z, z ∈ P.block y ∧ z ≠ y := by
      intro y hy
      have h2 : 2 ≤ (P.colorClass (P.color y)).ncard :=
        le_trans hY2 (Set.ncard_le_ncard (hclass y hy) (Set.toFinite _))
      have hb2 : 2 ≤ (P.block y).ncard := hadm y h2
      obtain ⟨z, hz, hz'⟩ := Set.exists_ne_of_one_lt_ncard (s := P.block y) (by omega) y
      exact ⟨z, hz, hz'⟩
    choose! f hf1 hf2 using hex
    have hfY : ∀ y ∈ Y, f y ∈ Yᶜ := by
      intro y hy hmem
      have : f y ∈ P.block y ∩ Y := ⟨hf1 y hy, hmem⟩
      rw [hsing y hy, Set.mem_singleton_iff] at this
      exact hf2 y hy this
    have hinj : Set.InjOn f Y := by
      intro y hy y' hy' h
      have h1 : f y ∈ P.block y := hf1 y hy
      have h2 : f y ∈ P.block y' := h ▸ hf1 y' hy'
      have hpp : P.part y y' := P.part.trans (P.part.symm h1) h2
      have : y' ∈ P.block y ∩ Y := ⟨P.part.symm hpp, hy'⟩
      rw [hsing y hy, Set.mem_singleton_iff] at this
      exact this.symm
    have hle : Y.ncard ≤ (Yᶜ : Set V).ncard :=
      Set.ncard_le_ncard_of_injOn f hfY hinj (Set.toFinite _)
    have hsum : Y.ncard + (Yᶜ : Set V).ncard = Nat.card V := Set.ncard_add_ncard_compl Y
    have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
    omega

end Babai
