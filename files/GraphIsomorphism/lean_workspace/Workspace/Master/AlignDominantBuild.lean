/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, line 7: the data of lines 7–11, read off the outcome of Theorem 9.2.3 on the
dominant color class.
-/
import Workspace.Master.AlignNumbering
import Workspace.Master.AlignOutcome

/-!
# Line 7: from the outcome of Theorem 9.2.3 to the data of lines 7–11

> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j)`.
> 7. (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>    relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then identify
>    `Δ_j` with `(Γ* choose t*)`, `|Γ*| = m*`, and let `Y` denote this Johnson scheme
> 8. let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural epimorphism

`Babai.alignColor_cases` (`Workspace/Master/AlignOutcome.lean`) splits an outcome of
Theorem 9.2.3 into the undominated case and the dominant case, and in the dominant case it
hands over a `Babai.DominantStructure`: the extra structure of line 7 on the dominant color
class.  This file turns that structure into the data of lines 7–11, that is, into a
`Babai.AlignDominantABlocks` or a `Babai.AlignDominantBBlocks`.

## The group `H` of line 8

The paper's `H` is `Aut(Y)`, the automorphism group of the structure *induced on `Δ_j`*,
and line 9 takes `G* = ϕ⁻¹(H)` inside the group current at line 9, which after line 3's
*"Update: … `G ← G₁`"* is `G₁ = ϕ⁻¹(Aut(X'))`.  So the paper's `G*` is

  `{τ ∈ G₁ | ϕ(τ) ∈ Aut(Y)} = G₁`,

because `Aut(X') ≤ Aut(Y)` (`Workspace/Master/DESIGN.md`, "Line 9 of Procedure Align").

`Babai.AlignDominant` computes `G* = ϕ⁻¹(H)` inside its own group `G`, and it asks that
group to be transitive with `ϕ` *giant* — which `G₁` is not.  So here `G` is the group of
line 4c (transitive, `ϕ` giant, Theorem 10.5.1 available) and

  **`H` is `Aut(X')`, not `Aut(Y)`**,

which gives `G* = ϕ⁻¹(Aut(X')) = G₁`, the group the Chain Rule call is made with respect
to, and the same `ϕ* = ψ ∘ ϕ|_{G*}`, because the `ψ` used here is the natural epimorphism
of line 8 restricted to `Aut(X') ≤ Aut(Y)`.  Nothing is lost: what line 8 asks of `ψ` is
that it be *onto* `S(Γ*)`, and it already is onto from `Aut(X')`.  In case (A) that is the
gluing argument of `Babai.surjective_equipartitionPsi` together with the observation that a
permutation of `Γ` which permutes the blocks inside one color class and fixes everything
else preserves the whole colored partition; in case (B) it is
`Babai.surjective_johnsonSchemePsi` together with the same observation for the two-coloring
`(W, Γ ∖ W)`.  This is recorded in the corrected paper.

## The numbering of `Γ*`

`Γ*` is here the honest set of blocks (case (A)) or the vertex set of the Johnson scheme
(case (B)); `Workspace/Master/AlignNumbering.lean` numbers it by `Fin m*`, and its module
docstring says why the numbering is harmless.
-/

universe u

namespace Babai

open Equiv MulAction

/-! ## Line 7 (A): the blocks of a colored partition inside one color class -/

section Blocks

variable {m : ℕ} {κ : Type} (R : ColoredPartition (Fin m) κ) (j : κ)

/-- §14.1, **line 7 (A)**: `Γ*`, *"the set of blocks"* — the blocks of the colored
partition `R` that lie inside the color class `j`. -/
abbrev domBlocks : Type := {S : Set (Fin m) // ∃ γ, R.color γ = j ∧ S = R.block γ}

noncomputable instance : Fintype (domBlocks R j) := Fintype.ofFinite _

open scoped Classical in
/-- The block map `Γ → Γ*`.  Off the color class it is junk, as line 7 (A) allows: only
the restriction to `Δ_j` is the equivalence relation `Y`. -/
noncomputable def domBlockMap {R : ColoredPartition (Fin m) κ} {j : κ} {γ₀ : Fin m}
    (h₀ : R.color γ₀ = j) : Fin m → domBlocks R j := fun γ =>
  if h : R.color γ = j then ⟨R.block γ, γ, h, rfl⟩ else ⟨R.block γ₀, γ₀, h₀, rfl⟩

variable {R j}
variable {γ₀ : Fin m}

open scoped Classical in
theorem domBlockMap_of_mem (h₀ : R.color γ₀ = j) {γ : Fin m} (h : R.color γ = j) :
    (domBlockMap h₀ γ : Set (Fin m)) = R.block γ := by
  unfold domBlockMap
  rw [dif_pos h]

theorem mem_domBlockMap_self (h₀ : R.color γ₀ = j) {γ : Fin m} (h : R.color γ = j) :
    γ ∈ (domBlockMap h₀ γ : Set (Fin m)) := by
  rw [domBlockMap_of_mem h₀ h]; exact R.mem_block_self γ

/-- A point of the color class lies in exactly one block, its own. -/
theorem domBlockMap_eq_iff (h₀ : R.color γ₀ = j) {γ : Fin m} (hγ : R.color γ = j)
    (b : domBlocks R j) :
    domBlockMap h₀ γ = b ↔ γ ∈ (b : Set (Fin m)) := by
  constructor
  · rintro rfl; exact mem_domBlockMap_self h₀ hγ
  · intro hmem
    obtain ⟨S, δ, hδ, rfl⟩ := b
    refine Subtype.ext ?_
    rw [domBlockMap_of_mem h₀ hγ]
    exact R.block_eq_of_part hmem

/-- The points of the color class that lie in a given block are the block. -/
theorem colorClass_inter_domBlockMap (h₀ : R.color γ₀ = j) (b : domBlocks R j) :
    R.colorClass j ∩ (domBlockMap h₀) ⁻¹' {b} = (b : Set (Fin m)) := by
  ext γ
  constructor
  · rintro ⟨hγ, hb⟩
    exact (domBlockMap_eq_iff h₀ hγ b).1 hb
  · intro hmem
    obtain ⟨S, δ, hδ, rfl⟩ := b
    have hpart : R.part γ δ := hmem
    have hγ : R.color γ = j := by rw [R.part_le_color hpart]; exact hδ
    exact ⟨hγ, (domBlockMap_eq_iff h₀ hγ _).2 hmem⟩

/-- In a colored *equi*partition every block of the color class has the same size. -/
theorem ncard_domBlocks (h₀ : R.color γ₀ = j) (hequi : R.IsEquipartition)
    (b : domBlocks R j) :
    (b : Set (Fin m)).ncard = (R.block γ₀).ncard := by
  obtain ⟨S, δ, hδ, rfl⟩ := b
  exact hequi δ γ₀ (by rw [hδ, h₀])

open scoped Classical in
/-- **The color class is the disjoint union of its blocks**: `|Δ_j| = |Γ*|·b`, with `b` the
common size of a block.  This is what makes `2|Γ*| ≤ |Δ_j|` when the blocks are nontrivial,
which is Eq. (73) in case (A) (`Babai.Align_equipartition_param_halved`). -/
theorem ncard_colorClass_eq_mul (h₀ : R.color γ₀ = j) (hequi : R.IsEquipartition) :
    (R.colorClass j).ncard
      = Fintype.card (domBlocks R j) * (R.block γ₀).ncard := by
  classical
  have hmaps : Set.MapsTo (domBlockMap h₀)
      ((R.colorClass j).toFinset : Set (Fin m)) (Finset.univ : Finset (domBlocks R j)) :=
    fun a _ => Finset.mem_univ _
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ b : domBlocks R j,
      {a ∈ (R.colorClass j).toFinset | domBlockMap h₀ a = b}.card = (R.block γ₀).ncard := by
    intro b
    have hcoe : (({a ∈ (R.colorClass j).toFinset | domBlockMap h₀ a = b} : Finset (Fin m)) :
        Set (Fin m)) = (b : Set (Fin m)) := by
      rw [← colorClass_inter_domBlockMap h₀ b]
      ext γ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_toFinset, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Set.ncard_coe_finset, hcoe, ncard_domBlocks h₀ hequi b]
  rw [Set.ncard_eq_toFinset_card', hsum, Finset.sum_congr rfl (fun b _ => hfib b),
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Blocks

/-! ## Line 8 in case (A): the automorphism group of the colored partition and its action
on the blocks

The `H` of line 8 is `Aut(X')`, the automorphism group of the whole colored partition
(see the module docstring for why, and the corrected paper).  Its action on the blocks inside
the dominant color class is the `ψ` of line 8: it is `Babai.equipartitionPsi` for the block
map of the color class, read through the restriction `H → S(Δ_j)`, and it is onto because
a permutation of the blocks inside one color class, glued from bijections between blocks
and extended by the identity, preserves colors and preserves the partition. -/

section PartAut

variable {m : ℕ} {κ : Type}

/-- §14.1, line 8, case (A): **the automorphism group of a colored partition** — the
permutations of `Γ` that preserve the coloring and the partition.  This is `Aut(X')` for
the structure `X'` of line 7 (A). -/
def partAut (R : ColoredPartition (Fin m) κ) : Subgroup (Equiv.Perm (Fin m)) where
  carrier := {h | (∀ γ, R.color (h γ) = R.color γ) ∧
    (∀ γ δ, R.part (h γ) (h δ) ↔ R.part γ δ)}
  one_mem' := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro a b ⟨hac, hap⟩ ⟨hbc, hbp⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · show R.color (a (b γ)) = R.color γ
      rw [hac (b γ), hbc γ]
    · show R.part (a (b γ)) (a (b δ)) ↔ R.part γ δ
      rw [hap (b γ) (b δ), hbp γ δ]
  inv_mem' := by
    rintro a ⟨hac, hap⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · have h := hac (a⁻¹ γ)
      rw [show a (a⁻¹ γ) = γ from by simp] at h
      exact h.symm
    · have h := hap (a⁻¹ γ) (a⁻¹ δ)
      rw [show a (a⁻¹ γ) = γ from by simp, show a (a⁻¹ δ) = δ from by simp] at h
      exact h.symm

theorem mem_partAut {R : ColoredPartition (Fin m) κ} {h : Equiv.Perm (Fin m)} :
    h ∈ partAut R ↔ (∀ γ, R.color (h γ) = R.color γ) ∧
      (∀ γ δ, R.part (h γ) (h δ) ↔ R.part γ δ) := Iff.rfl

variable {R : ColoredPartition (Fin m) κ} {j : κ}

/-- An automorphism of the colored partition carries the color class `Δ_j` onto itself.
This is the field `stab` of `Babai.AlignDominantABlocks`. -/
theorem isInvariant_colorClass : IsInvariant (partAut R) (R.colorClass j) := by
  intro h hh
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    show R.color (h δ) = j
    rw [(mem_partAut.1 hh).1 δ]; exact hδ
  · intro hγ
    refine ⟨h⁻¹ γ, ?_, by simp⟩
    have := (mem_partAut.1 hh).1 (h⁻¹ γ)
    rw [show h (h⁻¹ γ) = γ from by simp] at this
    show R.color (h⁻¹ γ) = j
    rw [← this]; exact hγ

/-- An automorphism of the colored partition carries blocks onto blocks. -/
theorem image_block_partAut {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R) (δ : Fin m) :
    h '' R.block δ = R.block (h δ) := by
  ext γ
  constructor
  · rintro ⟨ε, hε, rfl⟩
    exact ((mem_partAut.1 hh).2 ε δ).2 hε
  · intro hγ
    refine ⟨h⁻¹ γ, ?_, by simp⟩
    have := (mem_partAut.1 hh).2 (h⁻¹ γ) δ
    rw [show h (h⁻¹ γ) = γ from by simp] at this
    exact this.1 hγ

variable {γ₀ : Fin m}

/-- The action of an automorphism on the blocks of the color class, as a map. -/
noncomputable def domBlockAct {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R) :
    domBlocks R j → domBlocks R j := fun b =>
  ⟨h '' (b : Set (Fin m)), by
    obtain ⟨S, δ, hδ, rfl⟩ := b
    exact ⟨h δ, by rw [(mem_partAut.1 hh).1 δ]; exact hδ, image_block_partAut hh δ⟩⟩

@[simp] theorem domBlockAct_val {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R)
    (b : domBlocks R j) :
    (domBlockAct hh b : Set (Fin m)) = h '' (b : Set (Fin m)) := rfl

/-- The action of an automorphism on the blocks of the color class, as a permutation.
This is the `β` of `Babai.equipartitionAut`. -/
noncomputable def domBlockPerm {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R) :
    Equiv.Perm (domBlocks R j) where
  toFun := domBlockAct hh
  invFun := domBlockAct ((partAut R).inv_mem hh)
  left_inv b := by
    refine Subtype.ext ?_
    show (h⁻¹ : Equiv.Perm (Fin m)) '' (h '' (b : Set (Fin m))) = (b : Set (Fin m))
    rw [← Set.image_comp]
    simp
  right_inv b := by
    refine Subtype.ext ?_
    show h '' ((h⁻¹ : Equiv.Perm (Fin m)) '' (b : Set (Fin m))) = (b : Set (Fin m))
    rw [← Set.image_comp]
    simp

@[simp] theorem domBlockPerm_val {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R)
    (b : domBlocks R j) :
    ((domBlockPerm hh b : domBlocks R j) : Set (Fin m)) = h '' (b : Set (Fin m)) := rfl

/-- The block map moves by the induced permutation of the blocks. -/
theorem domBlockMap_apply_perm (h₀ : R.color γ₀ = j) {h : Equiv.Perm (Fin m)}
    (hh : h ∈ partAut R) {γ : Fin m} (hγ : R.color γ = j) :
    domBlockMap h₀ (h γ) = domBlockPerm hh (domBlockMap h₀ γ) := by
  refine Subtype.ext ?_
  have hhγ : R.color (h γ) = j := by rw [(mem_partAut.1 hh).1 γ]; exact hγ
  rw [domBlockMap_of_mem h₀ hhγ, domBlockPerm_val hh, domBlockMap_of_mem h₀ hγ,
    image_block_partAut hh γ]

/-- For two points of the color class, being in the same block is being in the same
member of `Γ*`. -/
theorem part_iff_domBlockMap_eq (h₀ : R.color γ₀ = j) {γ δ : Fin m} (hγ : R.color γ = j)
    (hδ : R.color δ = j) : R.part γ δ ↔ domBlockMap h₀ γ = domBlockMap h₀ δ := by
  constructor
  · intro hp
    exact Subtype.ext (by rw [domBlockMap_of_mem h₀ hγ, domBlockMap_of_mem h₀ hδ,
      R.block_eq_of_part hp])
  · intro he
    have : γ ∈ (domBlockMap h₀ δ : Set (Fin m)) := by
      rw [← he]; exact mem_domBlockMap_self h₀ hγ
    rw [domBlockMap_of_mem h₀ hδ] at this
    exact this

end PartAut

/-! ## Line 8 in case (A): `ψ : H → S(Γ*)` and the fact that it is onto -/

section Psi

variable {m : ℕ} {κ : Type} {R : ColoredPartition (Fin m) κ} {j : κ} {γ₀ : Fin m}

/-- The block map, read on the color class `Δ_j`.  This is the `f : Δ → Γ*` of
`Babai.equipartitionAut`. -/
noncomputable def domBlockRestr (h₀ : R.color γ₀ = j) :
    ↥(R.colorClass j) → domBlocks R j := fun d => domBlockMap h₀ (d : Fin m)

theorem surjective_domBlockRestr (h₀ : R.color γ₀ = j) :
    Function.Surjective (domBlockRestr (j := j) h₀) := by
  rintro ⟨S, δ, hδ, rfl⟩
  exact ⟨⟨δ, hδ⟩, Subtype.ext (domBlockMap_of_mem h₀ hδ)⟩

theorem coe_restrictHom_partAut {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R)
    (d : ↥(R.colorClass j)) :
    ((restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass ⟨h, hh⟩ d :
      ↥(R.colorClass j)) : Fin m) = h (d : Fin m) := rfl

/-- The restriction of an automorphism of the colored partition to the color class is an
automorphism of the equipartition of that class. -/
theorem restrictHom_mem_equipartitionAut (h₀ : R.color γ₀ = j) {h : Equiv.Perm (Fin m)}
    (hh : h ∈ partAut R) :
    restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass ⟨h, hh⟩
      ∈ equipartitionAut (domBlockRestr h₀) := by
  refine ⟨domBlockPerm hh, fun d => ?_⟩
  show domBlockMap h₀ ((restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass
    ⟨h, hh⟩ d : ↥(R.colorClass j)) : Fin m) = domBlockPerm hh (domBlockMap h₀ (d : Fin m))
  rw [coe_restrictHom_partAut hh d]
  exact domBlockMap_apply_perm h₀ hh d.2

/-- §14.1, **line 8, case (A)**: *"`ψ : H → S(Γ*)` the natural epimorphism"* — the action of
an automorphism of the colored partition on the blocks of the dominant color class. -/
noncomputable def domPsi (h₀ : R.color γ₀ = j) :
    partAut R →* Equiv.Perm (domBlocks R j) :=
  (equipartitionPsi (surjective_domBlockRestr h₀)).comp
    (MonoidHom.codRestrict
      (restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass)
      (equipartitionAut (domBlockRestr h₀))
      (fun σ => restrictHom_mem_equipartitionAut h₀ σ.2))

/-- `ψ(h)` is the permutation of the blocks that `h` induces. -/
theorem domPsi_apply (h₀ : R.color γ₀ = j) {h : Equiv.Perm (Fin m)} (hh : h ∈ partAut R) :
    domPsi h₀ ⟨h, hh⟩ = domBlockPerm hh := by
  refine equipartition_beta_unique (surjective_domBlockRestr h₀)
    (σ := restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass ⟨h, hh⟩)
    (equipartitionPsi_spec (surjective_domBlockRestr h₀)
      ⟨_, restrictHom_mem_equipartitionAut h₀ hh⟩) (fun d => ?_)
  show domBlockMap h₀ ((restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass
    ⟨h, hh⟩ d : ↥(R.colorClass j)) : Fin m) = domBlockPerm hh (domBlockMap h₀ (d : Fin m))
  rw [coe_restrictHom_partAut hh d]
  exact domBlockMap_apply_perm h₀ hh d.2

/-- §14.1, line 8, case (A), the field `psi_block` of `Babai.AlignDominantABlocks`. -/
theorem domBlockMap_psi (h₀ : R.color γ₀ = j) (h : partAut R) {d : Fin m}
    (hd : d ∈ R.colorClass j) :
    domBlockMap h₀ ((h : Equiv.Perm (Fin m)) d) = domPsi h₀ h (domBlockMap h₀ d) := by
  obtain ⟨h, hh⟩ := h
  rw [domPsi_apply h₀ hh]
  exact domBlockMap_apply_perm h₀ hh hd

/-- The fibres of the block map over the color class all have the common block size. -/
theorem card_fiber_domBlockRestr (h₀ : R.color γ₀ = j) (hequi : R.IsEquipartition)
    (b : domBlocks R j) :
    Nat.card {d : ↥(R.colorClass j) // domBlockRestr h₀ d = b} = (R.block γ₀).ncard := by
  have e := Equiv.subtypeSubtypeEquivSubtypeInter
    (p := fun x : Fin m => x ∈ R.colorClass j) (q := fun x => domBlockMap h₀ x = b)
  show Nat.card {d : ↥(R.colorClass j) // domBlockMap h₀ (d : Fin m) = b} = _
  rw [Nat.card_congr e]
  have hset : {x : Fin m | x ∈ R.colorClass j ∧ domBlockMap h₀ x = b}
      = (b : Set (Fin m)) := by
    rw [← colorClass_inter_domBlockMap h₀ b]
    rfl
  have : Nat.card {x : Fin m // x ∈ R.colorClass j ∧ domBlockMap h₀ x = b}
      = {x : Fin m | x ∈ R.colorClass j ∧ domBlockMap h₀ x = b}.ncard :=
    Nat.card_coe_set_eq _
  rw [this, hset, ncard_domBlocks h₀ hequi b]

open scoped Classical in
/-- §14.1, **line 8, case (A)**: *"the natural epimorphism"* really is an epimorphism.

*Proof.*  `Babai.surjective_equipartitionPsi` realizes a permutation `β` of the blocks by a
permutation `σ` of the color class, glued from bijections between a block and its image;
the blocks have equal size because the partition is a colored equipartition.  Extend `σ` by
the identity outside the color class (`Equiv.Perm.ofSubtype`).  The extension preserves the
coloring — it moves the color class into itself and fixes everything else — and it preserves
the partition: inside the class two points are in the same block exactly when their blocks
agree, and `β` is injective; a block never meets two color classes, so no pair with one
point inside and one outside the class is in the same block. -/
theorem surjective_domPsi (h₀ : R.color γ₀ = j) (hequi : R.IsEquipartition) :
    Function.Surjective (domPsi h₀) := by
  classical
  intro β
  have hf := surjective_domBlockRestr (j := j) h₀
  have hcard : ∀ b b' : domBlocks R j,
      Fintype.card {d : ↥(R.colorClass j) // domBlockRestr h₀ d = b}
        = Fintype.card {d : ↥(R.colorClass j) // domBlockRestr h₀ d = b'} := by
    intro b b'
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      card_fiber_domBlockRestr h₀ hequi b, card_fiber_domBlockRestr h₀ hequi b']
  obtain ⟨σ, hσ⟩ := surjective_equipartitionPsi hf hcard β
  -- the glued permutation of the color class, extended by the identity
  set τ : Equiv.Perm (Fin m) := Equiv.Perm.ofSubtype (σ : Equiv.Perm ↥(R.colorClass j))
    with hτ
  have hmem : ∀ γ (hγ : γ ∈ R.colorClass j),
      τ γ = ((σ : Equiv.Perm ↥(R.colorClass j)) ⟨γ, hγ⟩ : Fin m) := by
    intro γ hγ
    rw [hτ]
    exact Equiv.Perm.ofSubtype_apply_of_mem _ hγ
  have hnot : ∀ γ, γ ∉ R.colorClass j → τ γ = γ := by
    intro γ hγ
    rw [hτ]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hγ
  have hstay : ∀ γ (hγ : γ ∈ R.colorClass j), τ γ ∈ R.colorClass j := by
    intro γ hγ
    rw [hmem γ hγ]
    exact ((σ : Equiv.Perm ↥(R.colorClass j)) ⟨γ, hγ⟩).2
  -- the block map moves by `β`
  have hblk : ∀ γ (hγ : γ ∈ R.colorClass j),
      domBlockMap h₀ (τ γ) = β (domBlockMap h₀ γ) := by
    intro γ hγ
    have h1 := equipartitionPsi_spec hf σ ⟨γ, hγ⟩
    rw [hσ] at h1
    show domBlockMap h₀ (τ γ) = β (domBlockRestr h₀ ⟨γ, hγ⟩)
    rw [← h1, hmem γ hγ]
    rfl
  have hτmem : τ ∈ partAut R := by
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · by_cases hγ : γ ∈ R.colorClass j
      · have h1 : R.color (τ γ) = j := hstay γ hγ
        have h2 : R.color γ = j := hγ
        rw [h1, h2]
      · rw [hnot γ hγ]
    · by_cases hγ : γ ∈ R.colorClass j <;> by_cases hδ : δ ∈ R.colorClass j
      · rw [part_iff_domBlockMap_eq h₀ (hstay γ hγ) (hstay δ hδ),
          part_iff_domBlockMap_eq h₀ hγ hδ, hblk γ hγ, hblk δ hδ]
        exact ⟨fun h => β.injective h, fun h => congrArg β h⟩
      · have h1 : ¬ R.part γ δ := fun hp => hδ (by
          show R.color δ = j
          rw [← R.part_le_color hp]; exact hγ)
        have h2 : ¬ R.part (τ γ) (τ δ) := fun hp => hδ (by
          show R.color δ = j
          rw [← hnot δ hδ, ← R.part_le_color hp]
          exact hstay γ hγ)
        exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      · have h1 : ¬ R.part γ δ := fun hp => hγ (by
          show R.color γ = j
          rw [R.part_le_color hp]; exact hδ)
        have h2 : ¬ R.part (τ γ) (τ δ) := fun hp => hγ (by
          show R.color γ = j
          rw [← hnot γ hγ, R.part_le_color hp]
          exact hstay δ hδ)
        exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      · rw [hnot γ hγ, hnot δ hδ]
  refine ⟨⟨τ, hτmem⟩, ?_⟩
  refine equipartition_beta_unique hf
    (σ := restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass ⟨τ, hτmem⟩)
    (equipartitionPsi_spec hf ⟨_, restrictHom_mem_equipartitionAut h₀ hτmem⟩) (fun d => ?_)
  show domBlockMap h₀ ((restrictHom (partAut R) (R.colorClass j) isInvariant_colorClass
    ⟨τ, hτmem⟩ d : ↥(R.colorClass j)) : Fin m) = β (domBlockMap h₀ (d : Fin m))
  rw [coe_restrictHom_partAut hτmem d]
  exact hblk (d : Fin m) d.2

end Psi

/-! ## Line 7 (A): the data of lines 7-11 -/

section BuildA

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {κ : Type}

/-- §14.1, **lines 6-8, case (A)**: the data of Procedure Align on the dominant window,
built from a colored equipartition of `Γ` with a dominant color class.

`Γ*` is the set of blocks inside the dominant class (`Babai.domBlocks`), `H` is the
automorphism group of the colored partition (`Babai.partAut`; see the module docstring for
why `Aut(X')` and not `Aut(Y)`), and `ψ` is its action on those blocks
(`Babai.domPsi`, onto by `Babai.surjective_domPsi`).

Eq. (73) in this case, `2|Γ*| ≤ m`, is `Babai.Align_equipartition_param_halved`: the color
class is the disjoint union of its blocks, each of at least two points, and it lies inside
`Γ`. -/
noncomputable def alignDominantABlocks_of (G : Subgroup (Equiv.Perm Ω)) (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ) (ht : ∀ u : Ω, tPoint ϕ u = t)
    {R : ColoredPartition (Fin m) κ} (hequi : R.IsEquipartition) {j : κ} {γ₀ : Fin m}
    (h₀ : R.color γ₀ = j) (hdom : m < 2 * (R.colorClass j).ncard)
    (hblk2 : 2 ≤ (R.block γ₀).ncard)
    (htwo : ∃ γ δ, R.color γ = j ∧ R.color δ = j ∧ ¬ R.part δ γ) :
    AlignDominantABlocks Ω where
  G := G
  transitive := hG
  m := m
  ϕ := ϕ
  giant := hgiant
  veryLarge := hvl
  t := t
  t_const := ht
  Δj := R.colorClass j
  dominant := hdom
  H := partAut R
  stab := fun h hh => isInvariant_colorClass h hh
  B := domBlocks R j
  fintypeB := inferInstance
  ψB := domPsi h₀
  ψB_surj := surjective_domPsi h₀ hequi
  blockSize := (R.block γ₀).ncard
  blockSize_two := hblk2
  blockB := domBlockMap h₀
  block_card := fun b => by
    rw [colorClass_inter_domBlockMap h₀ b, ncard_domBlocks h₀ hequi b]
  psi_block := fun h d hd => domBlockMap_psi h₀ h hd
  ms_two := by
    obtain ⟨γ, δ, hγ, hδ, hne⟩ := htwo
    have hne' : domBlockMap h₀ δ ≠ domBlockMap h₀ γ := fun he =>
      hne ((part_iff_domBlockMap_eq h₀ hδ hγ).2 he)
    exact Fintype.one_lt_card_iff.2 ⟨domBlockMap h₀ δ, domBlockMap h₀ γ, hne'⟩
  param_halved := by
    have hcount := ncard_colorClass_eq_mul h₀ hequi
    have hle : (R.colorClass j).ncard ≤ m := by
      have h := Set.ncard_le_ncard (Set.subset_univ (R.colorClass j))
        (Set.toFinite (Set.univ : Set (Fin m)))
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have hmul : Fintype.card (domBlocks R j) * 2
        ≤ Fintype.card (domBlocks R j) * (R.block γ₀).ncard :=
      Nat.mul_le_mul_left _ hblk2
    omega

end BuildA

/-! ## From the outcome of Theorem 9.2.3 to the data of case (A)

`Babai.DominantStructure` in case (a) is a colored partition `P` on `□X' = Γ` together with
a color `j` of its equipartition refinement (Prop. 7.1.3) whose class contains two points in
different blocks and all of whose blocks have at least two points.  This section moves `P`
from `□X'` to `Γ` and identifies the automorphism group of the resulting colored partition
with `Aut(X')`. -/

section OutcomeA

variable {m : ℕ}

/-- `↥s ≃ Γ` for an outcome that lives on all of `Γ`. -/
def alignUnivEquiv {s : Set (Fin m)} (hs : s = Set.univ) : ↥s ≃ Fin m :=
  (Equiv.setCongr hs).trans (Equiv.Set.univ (Fin m))

@[simp] theorem alignUnivEquiv_apply {s : Set (Fin m)} (hs : s = Set.univ) (x : ↥s) :
    alignUnivEquiv hs x = (x : Fin m) := rfl

theorem alignUnivEquiv_symm {s : Set (Fin m)} (hs : s = Set.univ) (γ : Fin m) (hγ : γ ∈ s) :
    (alignUnivEquiv hs).symm γ = ⟨γ, hγ⟩ := Subtype.ext rfl

/-- The block of a pushed-forward colored partition is the image of the block. -/
theorem block_pushforward {s t : Type} (e : s ≃ t) {κ : Type} (P : ColoredPartition s κ)
    (y : t) : (ColoredPartition.pushforward e P).block y = e '' P.block (e.symm y) := by
  ext z
  constructor
  · intro hz
    refine ⟨e.symm z, hz, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    show P.part (e.symm (e w)) (e.symm y)
    rw [Equiv.symm_apply_apply]
    exact hw

/-- §14.1, line 4, case (a): the colored equipartition the outcome puts on `Γ`, the
refinement of Proposition 7.1.3 read through `□X' = Γ`. -/
noncomputable def alignPart {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) : ColoredPartition (Fin m) (ℕ × ℕ) :=
  ColoredPartition.pushforward (alignUnivEquiv hs) P.equipartRefine

theorem alignPart_color {s : Set (Fin m)} (hs : s = Set.univ) (P : ColoredPartition ↥s ℕ)
    (γ : Fin m) (hγ : γ ∈ s) :
    (alignPart hs P).color γ = P.equipartRefine.color ⟨γ, hγ⟩ := by
  show P.equipartRefine.color ((alignUnivEquiv hs).symm γ) = _
  rw [alignUnivEquiv_symm hs γ hγ]

theorem alignPart_part {s : Set (Fin m)} (hs : s = Set.univ) (P : ColoredPartition ↥s ℕ)
    {γ δ : Fin m} (hγ : γ ∈ s) (hδ : δ ∈ s) :
    (alignPart hs P).part γ δ ↔ P.part ⟨γ, hγ⟩ ⟨δ, hδ⟩ := by
  show P.part ((alignUnivEquiv hs).symm γ) ((alignUnivEquiv hs).symm δ) ↔ _
  rw [alignUnivEquiv_symm hs γ hγ, alignUnivEquiv_symm hs δ hδ]

theorem ncard_block_alignPart {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) (γ : Fin m) (hγ : γ ∈ s) :
    ((alignPart hs P).block γ).ncard = (P.block ⟨γ, hγ⟩).ncard := by
  rw [alignPart, block_pushforward, Set.ncard_image_of_injective _ (alignUnivEquiv hs).injective,
    alignUnivEquiv_symm hs γ hγ]
  rfl

/-- The refinement of Proposition 7.1.3 is a colored equipartition, and so is its image on
`Γ`. -/
theorem isEquipartition_alignPart {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) : (alignPart hs P).IsEquipartition := by
  intro γ δ h
  have hγ : γ ∈ s := by rw [hs]; trivial
  have hδ : δ ∈ s := by rw [hs]; trivial
  rw [alignPart_color hs P γ hγ, alignPart_color hs P δ hδ] at h
  rw [ncard_block_alignPart hs P γ hγ, ncard_block_alignPart hs P δ hδ]
  exact P.isEquipartition_equipartRefine ⟨γ, hγ⟩ ⟨δ, hδ⟩ h

/-- §14.1, line 4: the color classes of `Babai.alignColor` are the color classes of
`Babai.alignPart`. -/
theorem colorSet_alignColor_eq_colorClass {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) (j : ℕ × ℕ) :
    ((colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inl j) : Finset (Fin m)) : Set (Fin m)) = (alignPart hs P).colorClass j := by
  classical
  ext γ
  have hγ : γ ∈ s := by rw [hs]; trivial
  simp only [colorSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
    alignColor_inl s P hγ, Sum.inl.injEq]
  show P.equipartRefine.color ⟨γ, hγ⟩ = j ↔ (alignPart hs P).color γ = j
  rw [alignPart_color hs P γ hγ]

/-- §14.1, lines 8-9: **`Aut(X')` is the automorphism group of the colored partition**.

This is what makes the `G*` of line 9 the group `G₁` of line 2 (iv): `G* = ϕ⁻¹(H)` with
`H = Aut(X')` is `ϕ⁻¹(Aut(X'))`, which is `G₁`.

*Proof.*  A permutation `π` of `Γ` fixes the outcome exactly when it is a morphism of the
outcome to itself (`Babai.isoP_of_smul_eq` and `Babai.IsCatAction.eq_smul`), and in case
(a) a morphism of the outcome to itself is exactly a permutation preserving the coloring
and the partition.  The refined coloring of Proposition 7.1.3 adds the size of the block,
which a permutation preserving the partition preserves as well. -/
theorem structAut_eq_partAut
    [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) :
    structAut (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))) = partAut (alignPart hs P) := by
  ext π
  have hmem : ∀ γ : Fin m, γ ∈ s := fun γ => by rw [hs]; trivial
  have hcar : (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))).car
      = π '' (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))).car := by
    show s = π '' s
    rw [hs, Set.image_univ, Equiv.range_eq_univ]
  set Z : Pt (SplitOutcomes (Fin m)) := ⟨s, Sum.inl P⟩ with hZ
  set f : ↥s ≃ ↥s := permHom π Z Z hcar with hfdef
  have hfval : ∀ x : ↥s, ((f x : ↥s) : Fin m) = π (x : Fin m) := fun _ => rfl
  have hfx : ∀ (γ : Fin m), f ⟨γ, hmem γ⟩ = ⟨π γ, hmem (π γ)⟩ := fun γ => Subtype.ext rfl
  constructor
  · intro hπ
    obtain ⟨hcar', hiso⟩ := isoP_of_smul_eq hK (mem_structAut.1 hπ)
    have hiso' : (∀ x : ↥s, P.color (f x) = P.color x) ∧
        ∀ x y : ↥s, P.part x y ↔ P.part (f x) (f y) := hiso
    -- a morphism carries blocks onto blocks, so it preserves their size
    have hblk : ∀ x : ↥s, P.block (f x) = f '' P.block x := by
      intro x
      ext z
      constructor
      · intro hz
        refine ⟨f.symm z, ?_, by simp⟩
        have := (hiso'.2 (f.symm z) x).2 (by rw [Equiv.apply_symm_apply]; exact hz)
        exact this
      · rintro ⟨w, hw, rfl⟩
        exact (hiso'.2 w x).1 hw
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · rw [alignPart_color hs P (π γ) (hmem _), alignPart_color hs P γ (hmem γ)]
      show (P.color ⟨π γ, hmem _⟩, (P.block ⟨π γ, hmem _⟩).ncard)
        = (P.color ⟨γ, hmem γ⟩, (P.block ⟨γ, hmem γ⟩).ncard)
      rw [← hfx γ, hiso'.1 ⟨γ, hmem γ⟩, hblk ⟨γ, hmem γ⟩,
        Set.ncard_image_of_injective _ f.injective]
    · rw [alignPart_part hs P (hmem (π γ)) (hmem (π δ)), alignPart_part hs P (hmem γ) (hmem δ)]
      rw [← hfx γ, ← hfx δ]
      exact (hiso'.2 ⟨γ, hmem γ⟩ ⟨δ, hmem δ⟩).symm
  · intro hπ
    obtain ⟨hcol, hpart⟩ := mem_partAut.1 hπ
    have hiso : f ∈ (SplitOutcomes (Fin m)).IsoP Z Z := by
      refine ⟨fun x => ?_, fun x y => ?_⟩
      · have h := hcol (x : Fin m)
        rw [alignPart_color hs P (π (x : Fin m)) (hmem _),
          alignPart_color hs P (x : Fin m) (hmem _)] at h
        have h1 := congrArg Prod.fst h
        show P.color (f x) = P.color x
        have hx : (⟨(x : Fin m), hmem (x : Fin m)⟩ : ↥s) = x := Subtype.ext rfl
        have hfx' : f x = ⟨π (x : Fin m), hmem _⟩ := Subtype.ext rfl
        rw [hfx', ← hx]
        exact h1
      · have h := hpart (x : Fin m) (y : Fin m)
        rw [alignPart_part hs P (hmem _) (hmem _), alignPart_part hs P (hmem _) (hmem _)] at h
        have hx : (⟨(x : Fin m), hmem (x : Fin m)⟩ : ↥s) = x := Subtype.ext rfl
        have hy : (⟨(y : Fin m), hmem (y : Fin m)⟩ : ↥s) = y := Subtype.ext rfl
        have hfx' : f x = ⟨π (x : Fin m), hmem _⟩ := Subtype.ext rfl
        have hfy' : f y = ⟨π (y : Fin m), hmem _⟩ := Subtype.ext rfl
        rw [hfx', hfy', ← hx, ← hy] at *
        exact h.symm
    exact mem_structAut.2 (hK.eq_smul hcar hiso).symm

/-- §14.1, **lines 6-8, case (A)**: the data of Procedure Align on the dominant window,
built from the outcome of Theorem 9.2.3 itself.

The hypotheses are what `Babai.alignColor_cases` hands over in the dominant case together
with case (a) of `Babai.DominantStructure`: the outcome is a colored partition of all of
`Γ`, the color `j` of the refinement of Proposition 7.1.3 is dominant, its class contains
two points in different blocks, and every block inside it has at least two points. -/
noncomputable def alignDominantABlocks_ofOutcome {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (G : Subgroup (Equiv.Perm Ω)) (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hgiant : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ)
    (ht : ∀ u : Ω, tPoint ϕ u = t) {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) {j : ℕ × ℕ}
    (hdom : m < 2 * (colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inl j)).card)
    {x y : ↥s} (hx : P.equipartRefine.color x = j) (hy : P.equipartRefine.color y = j)
    (hxy : ¬ P.part y x)
    (hblk : ∀ z : ↥s, P.equipartRefine.color z = j → 2 ≤ (P.block z).ncard) :
    AlignDominantABlocks Ω := by
  classical
  refine alignDominantABlocks_of G hG ϕ hgiant hvl t ht (isEquipartition_alignPart hs P)
    (γ₀ := (x : Fin m)) (j := j) ?_ ?_ ?_ ?_
  · rw [alignPart_color hs P (x : Fin m) x.2]
    rw [show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
    exact hx
  · have hcard : ((colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
        (Sum.inl j)).card) = ((alignPart hs P).colorClass j).ncard := by
      rw [← Set.ncard_coe_finset, colorSet_alignColor_eq_colorClass hs P j]
    rw [← hcard]; exact hdom
  · rw [ncard_block_alignPart hs P (x : Fin m) x.2,
      show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
    exact hblk x hx
  · refine ⟨(x : Fin m), (y : Fin m), ?_, ?_, ?_⟩
    · rw [alignPart_color hs P (x : Fin m) x.2,
        show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
      exact hx
    · rw [alignPart_color hs P (y : Fin m) y.2,
        show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl]
      exact hy
    · rw [alignPart_part hs P y.2 x.2, show (⟨(y : Fin m), y.2⟩ : ↥s) = y from Subtype.ext rfl,
        show (⟨(x : Fin m), x.2⟩ : ↥s) = x from Subtype.ext rfl]
      exact hxy

/-- What `Babai.alignDominantABlocks_ofOutcome` is made of: the ambient data is the one
handed in, the dominant class is the color class of `Babai.alignColor`, and the group `H`
of line 8 is `Aut(X')`, so that `G* = ϕ⁻¹(H)` is the group `G₁` of line 2 (iv). -/
theorem alignDominantABlocks_ofOutcome_spec {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    (G : Subgroup (Equiv.Perm Ω)) (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hgiant : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ)
    (ht : ∀ u : Ω, tPoint ϕ u = t) {s : Set (Fin m)} (hs : s = Set.univ)
    (P : ColoredPartition ↥s ℕ) {j : ℕ × ℕ}
    (hdom : m < 2 * (colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
      (Sum.inl j)).card)
    {x y : ↥s} (hx : P.equipartRefine.color x = j) (hy : P.equipartRefine.color y = j)
    (hxy : ¬ P.part y x)
    (hblk : ∀ z : ↥s, P.equipartRefine.color z = j → 2 ≤ (P.block z).ncard) :
    letI D := alignDominantABlocks_ofOutcome G hG ϕ hgiant hvl t ht hs P hdom hx hy hxy hblk
    D.G = G ∧ D.m = m ∧ D.ϕ = ϕ ∧ D.t = t ∧
      D.Δj = ((colorSet (alignColor (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m))))
        (Sum.inl j) : Finset (Fin m)) : Set (Fin m)) ∧
      D.toAlignDominantA.toAlignDominant.Gs
        = preimageSubgroup ϕ (structAut (⟨s, Sum.inl P⟩ : Pt (SplitOutcomes (Fin m)))) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (alignPart hs P).colorClass j = _
    rw [colorSet_alignColor_eq_colorClass hs P j]
  · show preimageSubgroup ϕ (partAut (alignPart hs P)) = _
    rw [structAut_eq_partAut hK hs P]

end OutcomeA

/-! ## Line 7 (B): the Johnson scheme on the dominant color class

In case (b) the outcome is a Johnson coloring of a subset `W ⊆ Γ`, and line 4's coloring is
the two-coloring `(W, Γ ∖ W)`, whose class of the color `true` is `W`
(`Babai.colorSet_alignColor_inr`).  So the dominant class `Δ_j` is `W` itself.

`Babai.IsJohnsonColoring` carries only the *existence* of an identification
`φ : ↥W ≃ (Γ* choose t*)` with `Γ* = [k]`; the identification is therefore chosen, exactly
as `Workspace/Master/AlignNumbering.lean` chooses the numbering of `Γ*`, and for the same
reason the choice is harmless: it is made once per call of Procedure Align, both strings
are read through the same `(G*, ϕ*)`, and another identification changes neither `G*`, nor
the window, nor the answer. -/

section OutcomeB

variable {m : ℕ} [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]

variable {s : Set (Fin m)}

/-- An automorphism of the outcome permutes the vertex set of the Johnson scheme. -/
theorem isInvariant_structAut_inr (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) :
    IsInvariant (structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) s := by
  intro π hπ
  obtain ⟨hcar, -⟩ := isoP_of_smul_eq hK (mem_structAut.1 hπ)
  exact (show s = π '' s from hcar).symm

/-- An automorphism of the outcome preserves the Johnson coloring on its vertex set. -/
theorem structAut_inr_preserves (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s)
    (π : structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) (x y : ↥s) :
    J.1 (restrictHom _ s (isInvariant_structAut_inr hK J) π x)
        (restrictHom _ s (isInvariant_structAut_inr hK J) π y)
      = J.1 x y := by
  obtain ⟨hcar, hiso⟩ := isoP_of_smul_eq hK (mem_structAut.1 π.2)
  have hiso' : ∀ u v : ↥s,
      J.1
        (permHom (π : Equiv.Perm (Fin m)) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
          ⟨s, Sum.inr J⟩ hcar u)
        (permHom (π : Equiv.Perm (Fin m)) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
          ⟨s, Sum.inr J⟩ hcar v) = J.1 u v := hiso
  have hx : restrictHom _ s (isInvariant_structAut_inr hK J) π x
      = permHom (π : Equiv.Perm (Fin m)) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
        ⟨s, Sum.inr J⟩ hcar x := Subtype.ext rfl
  have hy : restrictHom _ s (isInvariant_structAut_inr hK J) π y
      = permHom (π : Equiv.Perm (Fin m)) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
        ⟨s, Sum.inr J⟩ hcar y := Subtype.ext rfl
  rw [hx, hy]
  exact hiso' x y

section Psi

variable {k ts : ℕ}

omit [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))] in
theorem isJohnsonGraphParams_of (hts : 2 ≤ ts) (hk : 2 * ts + 1 ≤ k) :
    IsJohnsonGraphParams (Fin k) ts :=
  ⟨hts, by rw [Fintype.card_fin]; exact hk⟩

/-- The restriction of an automorphism of the outcome to the vertex set, read through the
identification `Δ_j = (Γ* choose t*)`, is an automorphism of the Johnson scheme. -/
theorem mem_aut_johnsonScheme_of_structAut (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) (φ : ↥s ≃ binom (Fin k) ts)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (π : structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) :
    (Equiv.permCongrHom φ).toMonoidHom
        (restrictHom _ s (isInvariant_structAut_inr hK J) π)
      ∈ (johnsonScheme (Fin k) ts).Aut := by
  intro S T
  refine (PartitionStructure.ofColoring_color_eq_iff
    (fun S T : binom (Fin k) ts => ((S : Finset (Fin k)) \ (T : Finset (Fin k))).card)
    _ _ S T).2 ?_
  have hS : (Equiv.permCongrHom φ).toMonoidHom
      (restrictHom _ s (isInvariant_structAut_inr hK J) π) S
      = φ (restrictHom _ s (isInvariant_structAut_inr hK J) π (φ.symm S)) := rfl
  have hT : (Equiv.permCongrHom φ).toMonoidHom
      (restrictHom _ s (isInvariant_structAut_inr hK J) π) T
      = φ (restrictHom _ s (isInvariant_structAut_inr hK J) π (φ.symm T)) := rfl
  rw [hS, hT, ← hφ, structAut_inr_preserves hK J π (φ.symm S) (φ.symm T), hφ,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- §14.1, **line 8, case (B)**: *"`ψ : H → S(Γ*)` the natural epimorphism"* — the
permutation of `Γ*` that an automorphism of the outcome induces on the Johnson scheme. -/
noncomputable def johnsonPsiOf (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts)
    (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card) :
    structAut (Γ := Fin m) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
      →* Equiv.Perm (Fin k) :=
  (johnsonSchemePsi ts (isJohnsonGraphParams_of hts hk)).comp
    (MonoidHom.codRestrict
      ((Equiv.permCongrHom φ).toMonoidHom.comp
        (restrictHom _ s (isInvariant_structAut_inr hK J)))
      (johnsonScheme (Fin k) ts).Aut
      (fun π => mem_aut_johnsonScheme_of_structAut hK J φ hφ π))

/-- `ψ(h)` acting on `t*`-sets is what `h` does on the vertex set. -/
theorem tAction_johnsonPsiOf (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts)
    (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (π : structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) :
    tAction ts (johnsonPsiOf hK J φ hts hk hφ π)
      = (Equiv.permCongrHom φ).toMonoidHom
          (restrictHom _ s (isInvariant_structAut_inr hK J) π) := by
  have h := (permEquivAutJohnsonScheme ts (isJohnsonGraphParams_of hts hk)).apply_symm_apply
    (⟨_, mem_aut_johnsonScheme_of_structAut hK J φ hφ π⟩ :
      (johnsonScheme (Fin k) ts).Aut)
  exact congrArg Subtype.val h

open scoped Classical in
/-- §14.1, **line 8, case (B)**: the map really is an epimorphism.

*Proof.*  Every permutation `π` of `Γ*` acts on the `t*`-subsets, and that action is an
automorphism of the Johnson scheme (Prop. 3.2.11).  Read back through the identification
`Δ_j = (Γ* choose t*)` and extended by the identity outside `Δ_j`
(`Equiv.Perm.ofSubtype`), it is an automorphism of the outcome, because it carries `Δ_j`
onto itself and preserves the edge colors `|S ∖ T|`; and `ψ` sends it to `π`, because `ψ`
undoes `π ↦ π^{(t*)}` (`Babai.johnsonSchemePsi_tAction`). -/
theorem surjective_johnsonPsiOf (hK : IsCatAction (SplitOutcomes (Fin m)))
    (J : (JohnsonSchemes (Fin m)).Obj s) (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts)
    (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card) :
    Function.Surjective (johnsonPsiOf hK J φ hts hk hφ) := by
  classical
  intro π
  set g : Equiv.Perm ↥s := (Equiv.permCongrHom φ).symm (tAction ts π) with hg
  have hgφ : ∀ x : ↥s, φ (g x) = tAction ts π (φ x) := by
    intro x
    have : (Equiv.permCongrHom φ).toMonoidHom g = tAction ts π := by
      rw [hg]; exact (Equiv.permCongrHom φ).apply_symm_apply _
    have h2 : (Equiv.permCongrHom φ).toMonoidHom g (φ x) = tAction ts π (φ x) := by rw [this]
    show φ (g x) = tAction ts π (φ x)
    rw [← h2]
    show φ (g x) = φ (g (φ.symm (φ x)))
    rw [Equiv.symm_apply_apply]
  set h : Equiv.Perm (Fin m) := Equiv.Perm.ofSubtype g with hh
  have hmem : ∀ (γ : Fin m) (hγ : γ ∈ s), h γ = ((g ⟨γ, hγ⟩ : ↥s) : Fin m) := by
    intro γ hγ
    rw [hh]; exact Equiv.Perm.ofSubtype_apply_of_mem _ hγ
  have hcar : (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))).car
      = h '' (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))).car := by
    show s = h '' s
    ext γ
    constructor
    · intro hγ
      refine ⟨((g.symm ⟨γ, hγ⟩ : ↥s) : Fin m), (g.symm ⟨γ, hγ⟩).2, ?_⟩
      rw [hmem _ (g.symm ⟨γ, hγ⟩).2]
      show ((g (g.symm ⟨γ, hγ⟩) : ↥s) : Fin m) = γ
      rw [Equiv.apply_symm_apply]
    · rintro ⟨δ, hδ, rfl⟩
      rw [hmem δ hδ]
      exact (g ⟨δ, hδ⟩).2
  have hiso : permHom h (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
      ⟨s, Sum.inr J⟩ hcar ∈ (SplitOutcomes (Fin m)).IsoP ⟨s, Sum.inr J⟩ ⟨s, Sum.inr J⟩ := by
    intro x y
    have hx : permHom h (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ⟨s, Sum.inr J⟩ hcar x
        = g x := Subtype.ext (by show h (x : Fin m) = _; rw [hmem _ x.2])
    have hy : permHom h (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) ⟨s, Sum.inr J⟩ hcar y
        = g y := Subtype.ext (by show h (y : Fin m) = _; rw [hmem _ y.2])
    show J.1 _ _ = J.1 x y
    rw [hx, hy, hφ (g x) (g y), hφ x y, hgφ x, hgφ y, tAction_apply_coe, tAction_apply_coe,
      ← Finset.image_sdiff _ _ π.injective, Finset.card_image_of_injective _ π.injective]
  have hstab : h ∈ structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))) :=
    mem_structAut.2 (hK.eq_smul hcar hiso).symm
  refine ⟨⟨h, hstab⟩, ?_⟩
  -- `ψ` undoes `π ↦ π^{(t*)}`
  have hrestr : restrictHom _ s (isInvariant_structAut_inr hK J) ⟨h, hstab⟩ = g := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show h (x : Fin m) = ((g x : ↥s) : Fin m)
    rw [hmem _ x.2]
  have hconj : (Equiv.permCongrHom φ).toMonoidHom
      (restrictHom _ s (isInvariant_structAut_inr hK J) ⟨h, hstab⟩) = tAction ts π := by
    rw [hrestr, hg]
    exact (Equiv.permCongrHom φ).apply_symm_apply _
  show johnsonSchemePsi ts (isJohnsonGraphParams_of hts hk) ⟨_, _⟩ = π
  have := johnsonSchemePsi_tAction ts (isJohnsonGraphParams_of hts hk) π
    (by rw [← hconj]; exact mem_aut_johnsonScheme_of_structAut hK J φ hφ ⟨h, hstab⟩)
  rw [← this]
  congr 1
  exact Subtype.ext hconj

end Psi

/-! ### The data of lines 7-11 in case (B) -/

section BuildB

open scoped Classical in
/-- §14.1, line 7 (B): the identification of `Δ_j` with `(Γ* choose t*)`, as a map to
subsets of `Γ*`.  Off `Δ_j` it is junk, as line 7 (B) allows. -/
noncomputable def johnsonLabel {k ts : ℕ} (φ : ↥s ≃ binom (Fin k) ts) :
    Fin m → Set (Fin k) := fun d =>
  if h : d ∈ s then ((φ ⟨d, h⟩ : Finset (Fin k)) : Set (Fin k)) else ∅

open scoped Classical in
omit [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))] in
theorem johnsonLabel_of_mem {k ts : ℕ} (φ : ↥s ≃ binom (Fin k) ts) {d : Fin m}
    (h : d ∈ s) : johnsonLabel φ d = ((φ ⟨d, h⟩ : Finset (Fin k)) : Set (Fin k)) := by
  unfold johnsonLabel
  rw [dif_pos h]

/-- §14.1, **lines 6-8, case (B)**: the data of Procedure Align on the dominant window,
built from a Johnson scheme on the dominant color class.

`Γ*` is `[m*] = Fin k`, `H` is `Aut(X')` (see the module docstring), and `ψ` is
`Babai.johnsonPsiOf`, onto by `Babai.surjective_johnsonPsiOf`.

Eq. (73) in this case is `Babai.Align_johnson_param_halved`: `|Δ_j| = C(m*,t*)` with
`t* ≥ 2` and `m* ≥ 2t*+1`, and `|Δ_j| ≤ m`, so `2m* < m` once `m ≥ 12` — which the test of
line 2 of Sec. 15 (`m > ℓ(n) = (log₂ n)³` with `n ≥ 64`) gives. -/
noncomputable def alignDominantBBlocks_of {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    (G : Subgroup (Equiv.Perm Ω)) (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hgiant : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ)
    (ht : ∀ u : Ω, tPoint ϕ u = t) (J : (JohnsonSchemes (Fin m)).Obj s) {k ts : ℕ}
    (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts) (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (hdom : m < 2 * s.ncard) (hm12 : 12 ≤ m) :
    AlignDominantBBlocks Ω where
  G := G
  transitive := hG
  m := m
  ϕ := ϕ
  giant := hgiant
  veryLarge := hvl
  t := t
  t_const := ht
  Δj := s
  dominant := hdom
  H := structAut (Γ := Fin m) (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))
  stab := fun h hh => isInvariant_structAut_inr hK J h hh
  B := Fin k
  fintypeB := inferInstance
  ψB := johnsonPsiOf hK J φ hts hk hφ
  ψB_surj := surjective_johnsonPsiOf hK J φ hts hk hφ
  param_halved := by
    have hcard : k.choose ts = s.ncard := by
      have h1 : Nat.card ↥s = Nat.card (binom (Fin k) ts) := Nat.card_congr φ
      rw [Nat.card_coe_set_eq] at h1
      rw [h1, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]
    have hle : s.ncard ≤ m := by
      have h := Set.ncard_le_ncard (Set.subset_univ s) (Set.toFinite (Set.univ : Set (Fin m)))
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    have h2 := Align_johnson_param_halved hts hk hm12 (by rw [hcard]; exact hle)
    rw [Fintype.card_fin]
    omega
  ts := ts
  ts_two := hts
  ms_ge := by rw [Fintype.card_fin]; exact hk
  labelB := johnsonLabel φ
  label_ncard := fun d hd => by
    rw [johnsonLabel_of_mem φ hd, Set.ncard_coe_finset]
    exact (φ ⟨d, hd⟩).2
  label_inj := fun d hd d' hd' he => by
    rw [johnsonLabel_of_mem φ hd, johnsonLabel_of_mem φ hd'] at he
    have : φ ⟨d, hd⟩ = φ ⟨d', hd'⟩ := Subtype.ext (Finset.coe_injective he)
    exact congrArg Subtype.val (φ.injective this)
  label_surj := by
    classical
    intro T hT
    have hTfin : T.Finite := Set.toFinite T
    have hcardT : hTfin.toFinset.card = ts := by
      rw [← Set.ncard_eq_toFinset_card T hTfin]; exact hT
    set d := ((φ.symm ⟨hTfin.toFinset, hcardT⟩ : ↥s) : Fin m) with hd
    refine ⟨d, (φ.symm ⟨hTfin.toFinset, hcardT⟩).2, ?_⟩
    rw [johnsonLabel_of_mem φ (φ.symm ⟨hTfin.toFinset, hcardT⟩).2,
      show (⟨d, (φ.symm ⟨hTfin.toFinset, hcardT⟩).2⟩ : ↥s)
        = φ.symm ⟨hTfin.toFinset, hcardT⟩ from Subtype.ext rfl,
      Equiv.apply_symm_apply]
    exact hTfin.coe_toFinset
  psi_label := by
    intro h d hd
    have hhd : (h : Equiv.Perm (Fin m)) d ∈ s := by
      have hmem : (h : Equiv.Perm (Fin m)) d ∈ (h : Equiv.Perm (Fin m)) '' s := ⟨d, hd, rfl⟩
      rw [isInvariant_structAut_inr hK J (h : Equiv.Perm (Fin m)) h.2] at hmem
      exact hmem
    rw [johnsonLabel_of_mem φ hhd, johnsonLabel_of_mem φ hd]
    have hrestr : (⟨(h : Equiv.Perm (Fin m)) d, hhd⟩ : ↥s)
        = restrictHom _ s (isInvariant_structAut_inr hK J) h ⟨d, hd⟩ := Subtype.ext rfl
    have hconj : φ (restrictHom _ s (isInvariant_structAut_inr hK J) h ⟨d, hd⟩)
        = tAction ts (johnsonPsiOf hK J φ hts hk hφ h) (φ ⟨d, hd⟩) := by
      rw [tAction_johnsonPsiOf hK J φ hts hk hφ h]
      show _ = φ ((restrictHom _ s (isInvariant_structAut_inr hK J) h) (φ.symm (φ ⟨d, hd⟩)))
      rw [Equiv.symm_apply_apply]
    rw [hrestr, hconj, tAction_apply_coe, Finset.coe_image]

/-- What `Babai.alignDominantBBlocks_of` is made of: the dominant class is the vertex set of
the Johnson scheme, which is the class of the color `true` of `Babai.alignColor`, and the
group `G*` of line 9 is `ϕ⁻¹(Aut(X')) = G₁`. -/
theorem alignDominantBBlocks_of_spec {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    (G : Subgroup (Equiv.Perm Ω)) (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hgiant : IsGiantRep ϕ) (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ)
    (ht : ∀ u : Ω, tPoint ϕ u = t) (J : (JohnsonSchemes (Fin m)).Obj s) {k ts : ℕ}
    (φ : ↥s ≃ binom (Fin k) ts) (hts : 2 ≤ ts) (hk : 2 * ts + 1 ≤ k)
    (hφ : ∀ x y : ↥s, J.1 x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card)
    (hdom : m < 2 * s.ncard) (hm12 : 12 ≤ m) :
    letI D := alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J φ hts hk hφ hdom hm12
    D.G = G ∧ D.m = m ∧ D.ϕ = ϕ ∧ D.t = t ∧
      D.Δj = ((colorSet (alignColor (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m))))
        (Sum.inr true) : Finset (Fin m)) : Set (Fin m)) ∧
      D.toAlignDominantB.toAlignDominant.Gs
        = preimageSubgroup ϕ (structAut (⟨s, Sum.inr J⟩ : Pt (SplitOutcomes (Fin m)))) :=
  ⟨rfl, rfl, rfl, rfl, (colorSet_alignColor_inr s J).symm, rfl⟩

end BuildB

end OutcomeB

end Babai
