/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.5 and 9.7: a concrete object that carries the hint.
-/
import Workspace.SplitOrJohnson.BlkRestrictHint

/-!
# §9.5, §9.7: the hint is not vacuous

`Babai.VColBipBlk.HasHint` (`Workspace/SplitOrJohnson/Hint.lean`) is the third kind of
major progress of §9.5, *"`X₂` moves from clique to UPCC while `n₂` does not increase"*.
This file exhibits one object that has it, so that the outcome
`Babai.good97_restrict_hint` is not about the empty set of objects.

The example is the smallest instance of Cases 3a1 and 3b: **four blocks in two pairs**.
The blocks are the four singletons of `Fin 4`, the equivalence relation pairs `0` with `1`
and `2` with `3`, and the hint is the coloring of `Babai.eqvConfig` for it — three colors,
*"equal"*, *"the other member of the pair"*, *"the other pair"*.  Its two provisos hold:
the classes have the common size `2 ≥ 2`, and there are two of them (`2 < 4`).
-/

namespace Babai

namespace HintExample

/-- The pairing of `Fin 4`: `0 ∼ 1` and `2 ∼ 3`. -/
def pair (i j : Fin 4) : Prop := (i : ℕ) / 2 = (j : ℕ) / 2

instance : DecidableRel pair := fun i j => Nat.decEq _ _

theorem pair_equivalence : Equivalence pair :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

theorem pair_filter_card (x : Fin 4) :
    (Finset.univ.filter fun y : Fin 4 => pair x y).card = 2 := by
  revert x; decide

theorem pair_class_ncard (x : Fin 4) : ({y | pair x y} : Set (Fin 4)).ncard = 2 := by
  have hset : ({y | pair x y} : Set (Fin 4))
      = ↑(Finset.univ.filter fun y : Fin 4 => pair x y) := by
    ext y; simp
  rw [hset, Set.ncard_coe_finset, pair_filter_card]

/-- The three-color configuration of the pairing: a homogeneous coherent configuration of
rank `3` on four points (`Babai.eqvConfig`). -/
noncomputable def P : PartitionStructure (Fin 4) :=
  eqvConfig pair_equivalence pair_class_ncard (by norm_num) (by simp)

theorem P_isCoherent : P.IsCoherent :=
  eqvConfig_isCoherent pair_equivalence pair_class_ncard (by norm_num) (by simp)

theorem P_isHomogeneous : P.IsHomogeneous :=
  eqvConfig_isHomogeneous pair_equivalence pair_class_ncard (by norm_num) (by simp)

theorem P_rank : P.rank = 3 := rfl

/-- The four blocks: the singletons of `Fin 4`. -/
def blk : Set (Set (Fin 4)) := Set.range (fun i : Fin 4 => ({i} : Set (Fin 4)))

theorem sgl_injective : Function.Injective (fun i : Fin 4 => ({i} : Set (Fin 4))) :=
  fun _ _ h => Set.singleton_eq_singleton_iff.1 h

/-- The four blocks, identified with the four points of `Fin 4`. -/
noncomputable def e : Fin 4 ≃ ↥blk := Equiv.ofInjective _ sgl_injective

/-- The configuration of the pairing, read on the blocks. -/
noncomputable def Pblk : PartitionStructure ↥blk := P.transport e

/-- §9.5, §9.7.  **An object of `Babai.VColBipBlk` with four blocks in two pairs.**  Its
first part is empty, it has no edges, and its hint is the coloring of the rank-`3`
configuration `Babai.HintExample.Pblk`. -/
noncomputable def X : VColBipBlk (Fin 4) ℕ where
  part₁ := fun _ => False
  blocks := blk
  blocks_nonempty := by
    rintro B ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  blocks_disjoint := by
    rintro B ⟨i, rfl⟩ B' ⟨j, rfl⟩ hne
    rw [Set.disjoint_singleton]
    exact fun h => hne (by rw [h])
  blocks_off₁ := by
    rintro B - x - h
    exact h
  E := ∅
  E_sub := by rintro p ⟨⟩
  f := fun _ => 0
  g := fun _ => 0
  g_off := fun _ _ => rfl
  h := hintColoring blk Pblk
  h_off := fun A B hAB => hintColoring_off blk Pblk hAB

@[simp] theorem X_blocks : X.blocks = blk := rfl

/-- §9.5, §9.7.  **The hint is not vacuous.**  The object `Babai.HintExample.X` has
`Babai.VColBipBlk.HasHint`: its hint is the coloring of a homogeneous coherent
configuration of rank `3` on its four blocks. -/
theorem X_hasHint : X.HasHint :=
  VColBipBlk.hasHint_of_structure Pblk
    (PartitionStructure.transport_isCoherent e P_isCoherent)
    (PartitionStructure.transport_isHomogeneous e P_isHomogeneous)
    (le_of_eq (rfl : (3 : ℕ) = Pblk.rank))
    (fun A B => hintColoring_apply blk Pblk A B)

/-- The example has four blocks, so `Babai.VColBipBlk.two_le_numBlocks_of_hasHint` is not
the whole content of the hint. -/
theorem X_numBlocks : X.numBlocks = 4 := by
  classical
  have : blk = ↑((Finset.univ : Finset (Fin 4)).image fun i => ({i} : Set (Fin 4))) := by
    ext B; simp [blk, eq_comm]
  show blk.ncard = 4
  rw [this, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ sgl_injective, Finset.card_univ]
  rfl

end HintExample

end Babai
