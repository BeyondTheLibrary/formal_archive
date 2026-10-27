/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.5 and 9.7: the two ways §9.7 builds the hint of `Babai.VColBipBlk.HasHint`.
-/
import Workspace.SplitOrJohnson.Hint

/-!
# §9.7: building the hint

Version 2.5, lines 4281-4301 (§9.7, Cases 3a1, 3a2 and 3b) and lines 4176-4181 (§9.5).

`Babai.VColBipBlk.HasHint` (`Workspace/SplitOrJohnson/Hint.lean`) asks for a **homogeneous
coherent configuration of rank at least `3`** on the set of blocks whose color classes are
those of the hint coloring `h`.  §9.7 produces such a configuration in exactly two ways.

* **Case 3a2**: *"The Design lemma returns a UPCC `Y` canonically embedded on a subset
  `W ⊆ V₂`."*  A UPCC is uniprimitive, hence homogeneous and of rank `≥ 3` (Def. 3.2.1), so
  its own coloring is a hint.  This is `Babai.hasHint_of_upccColoring`.

* **Cases 3a1 and 3b**: *"If color class selected is greater than `3n₂/4`, this color class
  is equipartitioned"* (the original, `babai-gi.tex`, lines 3981-3992; entry 36 of
  the corrected paper).  The structure left on the selected class is a partition of it into
  blocks of one common size.  `Babai.eqvConfig` is the configuration of such a partition:
  three relations, *"equal"*, *"different, same class"* and *"different classes"*.  It is
  homogeneous and coherent of rank exactly `3`, provided there are at least two classes and
  the classes have one common size `≥ 2`.

## Why the two provisos hold in Case 3a1

The selected part is one color class `C` of a colored `3/4`-partition `Π` of `V₂` with
`|C| > (3/4)n₂`.

* *One common size.*  A colored partition is made an **equipartition** by Prop. 7.1.3
  (`Babai.ColoredPartition.equipartRefine`), which only refines the coloring and keeps
  every block (`Babai.ColoredPartition.block_equipartRefine`); §9.7 is run on that
  refinement.  See `Workspace/SplitOrJohnson/BlkRestrictHint.lean`.
* *Size `≥ 2`.*  `Π` is admissible (Def. 7.1.1), so a color class of size `≥ 2` has all its
  blocks of size `≥ 2`; and `|C| > (3/4)n₂ ≥ 2` in Cases 2 and 3 of §9.7, where `n₂ ≥ 4`
  (`Babai.BlkCaseObj.two_le_d₁_and_add_two_le`).
* *At least two classes.*  A single block would have size `|C| > (3/4)n₂ ≥ ρ(Π)`,
  contradicting `ρ(Π) ≤ (3/4)n₂` (Def. 7.1.1).

## Numbering map

| Paper | Lean |
|---|---|
| the configuration of a partition into classes of one size (Cases 3a1, 3b) | `Babai.eqvConfig` |
| it is a homogeneous coherent configuration of rank `3` | `Babai.eqvConfig_isCoherent`, `.isHomogeneous`, `.rank` |
| the hint coloring of a configuration on the blocks | `Babai.hintColoring` |
| a UPCC is a hint (Case 3a2) | `Babai.hasHint_of_upccColoring` |
| an equipartition of the blocks is a hint (Cases 3a1, 3b) | `Babai.hasHint_of_eqv` |
-/

namespace Babai

/-! ### Carrying a partition structure along a bijection -/

namespace PartitionStructure

/-- A partition structure read through a bijection of the vertex sets.  (The same
construction as `Babai.PartitionStructure.congrEquiv` of `Workspace/DesignLemma/`, which
stands above §9.4-§9.8 in the import order and cannot be used here.) -/
def transport {β γ : Type} (P : PartitionStructure β) (e : β ≃ γ) : PartitionStructure γ where
  rank := P.rank
  color x y := P.color (e.symm x) (e.symm y)
  color_surjective i := by
    obtain ⟨x, y, hxy⟩ := P.color_surjective i
    exact ⟨e x, e y, by simpa using hxy⟩

@[simp] theorem transport_rank {β γ : Type} (P : PartitionStructure β) (e : β ≃ γ) :
    (P.transport e).rank = P.rank := rfl

@[simp] theorem transport_color {β γ : Type} (P : PartitionStructure β) (e : β ≃ γ)
    (x y : γ) : (P.transport e).color x y = P.color (e.symm x) (e.symm y) := rfl

theorem transport_isCoherent {β γ : Type}
    {P : PartitionStructure β} (e : β ≃ γ) (h : P.IsCoherent) :
    (P.transport e).IsCoherent := by
  classical
  refine ⟨⟨fun x y z hxyz => e.symm.injective (h.diag _ _ _ hxyz),
    fun u v x y huv => h.converse _ _ _ _ huv⟩, ?_⟩
  obtain ⟨p, hp⟩ := h.intersection
  refine ⟨p, fun i j k x y hxy => ?_⟩
  have hset : {z : γ | (P.transport e).color x z = i ∧ (P.transport e).color z y = j}
      = e '' {z : β | P.color (e.symm x) z = i ∧ P.color z (e.symm y) = j} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e.symm z, ⟨h1, h2⟩, by simp⟩
    · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
  rw [hset, Set.ncard_image_of_injective _ e.injective]
  exact hp i j k _ _ hxy

theorem transport_isHomogeneous {β γ : Type} {P : PartitionStructure β} (e : β ≃ γ)
    (h : P.IsHomogeneous) : (P.transport e).IsHomogeneous := fun x y => h _ _

end PartitionStructure

/-! ### The configuration of a partition into classes of one common size

§9.7, Cases 3a1 and 3b.  *"this color class is equipartitioned"*: the structure the paper
hands on is an equivalence relation `R` on the selected class whose classes all have the
same size `m ≥ 2`, and which has at least two classes.  Its three relations are *"equal"*,
*"different, same class"* and *"different classes"*. -/

section Eqv

variable {β : Type} [Fintype β] [DecidableEq β]

/-- The three-color edge coloring of an equivalence relation `R`: `0` on the diagonal, `1`
on a pair of different points of one class, `2` on a pair of points of different classes. -/
def eqvColor (R : β → β → Prop) [DecidableRel R] (x y : β) : Fin 3 :=
  if x = y then 0 else if R x y then 1 else 2

variable (R : β → β → Prop) [DecidableRel R]

@[simp] theorem eqvColor_self (x : β) : eqvColor R x x = 0 := by simp [eqvColor]

theorem eqvColor_eq_zero_iff (x y : β) : eqvColor R x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    rw [eqvColor, if_neg hne] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem eqvColor_eq_one_iff (x y : β) : eqvColor R x y = 1 ↔ x ≠ y ∧ R x y := by
  constructor
  · intro h
    by_cases hne : x = y
    · rw [hne, eqvColor_self] at h; exact absurd h (by decide)
    · rw [eqvColor, if_neg hne] at h
      by_cases hr : R x y
      · exact ⟨hne, hr⟩
      · rw [if_neg hr] at h; exact absurd h (by decide)
  · rintro ⟨hne, hr⟩
    rw [eqvColor, if_neg hne, if_pos hr]

theorem eqvColor_eq_two_iff (x y : β) : eqvColor R x y = 2 ↔ x ≠ y ∧ ¬ R x y := by
  constructor
  · intro h
    by_cases hne : x = y
    · rw [hne, eqvColor_self] at h; exact absurd h (by decide)
    · rw [eqvColor, if_neg hne] at h
      by_cases hr : R x y
      · rw [if_pos hr] at h; exact absurd h (by decide)
      · exact ⟨hne, hr⟩
  · rintro ⟨hne, hr⟩
    rw [eqvColor, if_neg hne, if_neg hr]

variable {R}

theorem eqvColor_comm (hR : Equivalence R) (x y : β) :
    eqvColor R x y = eqvColor R y x := by
  unfold eqvColor
  by_cases hxy : x = y
  · subst hxy; rfl
  · rw [if_neg hxy, if_neg (Ne.symm hxy)]
    by_cases h : R x y
    · rw [if_pos h, if_pos (hR.symm h)]
    · rw [if_neg h, if_neg (fun hc => h (hR.symm hc))]

/-- The class of `x`. -/
def cls (R : β → β → Prop) (x : β) : Set β := {y | R x y}

theorem mem_cls_self (hR : Equivalence R) (x : β) : x ∈ cls R x := hR.refl x

theorem cls_eq (hR : Equivalence R) {x y : β} (h : R x y) : cls R x = cls R y :=
  Set.ext fun _ => ⟨fun hz => hR.trans (hR.symm h) hz, fun hz => hR.trans h hz⟩

theorem notMem_cls {x y : β} (h : ¬ R x y) : y ∉ cls R x := h

theorem cls_disjoint (hR : Equivalence R) {x y : β} (h : ¬ R x y) :
    Disjoint (cls R x) (cls R y) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact h (hR.trans hz (hR.symm hz'))

/-! The three out-neighbourhoods of the coloring. -/

theorem setOut_zero (x : β) : {z | eqvColor R x z = 0} = {x} := by
  ext z; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [eqvColor_eq_zero_iff]; exact eq_comm

theorem setOut_one (x : β) : {z | eqvColor R x z = 1} = cls R x \ {x} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  rw [eqvColor_eq_one_iff]
  exact ⟨fun h => ⟨h.2, fun hc => h.1 hc.symm⟩, fun h => ⟨fun hc => h.2 hc.symm, h.1⟩⟩

theorem setOut_two (hR : Equivalence R) (x : β) :
    {z | eqvColor R x z = 2} = (cls R x)ᶜ := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [eqvColor_eq_two_iff]
  exact ⟨fun h => h.2, fun h => ⟨fun hc => h (hc ▸ mem_cls_self hR x), h⟩⟩

theorem setIn_zero (hR : Equivalence R) (y : β) : {z | eqvColor R z y = 0} = {y} := by
  rw [← setOut_zero (R := R) y]
  ext z; simp only [Set.mem_setOf_eq]; rw [eqvColor_comm hR z y]

theorem setIn_one (hR : Equivalence R) (y : β) :
    {z | eqvColor R z y = 1} = cls R y \ {y} := by
  rw [← setOut_one (R := R) y]
  ext z; simp only [Set.mem_setOf_eq]; rw [eqvColor_comm hR z y]

theorem setIn_two (hR : Equivalence R) (y : β) :
    {z | eqvColor R z y = 2} = (cls R y)ᶜ := by
  rw [← setOut_two hR (R := R) y]
  ext z; simp only [Set.mem_setOf_eq]; rw [eqvColor_comm hR z y]

/-! The counting facts. -/

theorem ncard_cls_diff (hR : Equivalence R) {m : ℕ}
    (hm : ∀ x : β, (cls R x).ncard = m) (x : β) : (cls R x \ {x}).ncard = m - 1 := by
  rw [Set.ncard_diff_singleton_of_mem (mem_cls_self hR x), hm]

theorem ncard_cls_compl {m : ℕ} (hm : ∀ x : β, (cls R x).ncard = m) (x : β) :
    ((cls R x)ᶜ).ncard = Fintype.card β - m := by
  have hsum := Set.ncard_add_ncard_compl (cls R x)
  rw [hm x, Nat.card_eq_fintype_card] at hsum
  omega

end Eqv

/-! ### `eqvConfig`: the configuration itself -/

section EqvConfig

variable {β : Type} [Fintype β] [DecidableEq β] {R : β → β → Prop} [DecidableRel R]
  {m : ℕ}

/-- §9.7, Cases 3a1 and 3b.  **The coherent configuration of an equipartition.**  Let `R`
be an equivalence relation on `β` all of whose classes have the same size `m ≥ 2`, with at
least two classes (`m < |β|`).  The three relations *"equal"*, *"different, same class"*
and *"different classes"* form a homogeneous coherent configuration of rank `3`.

This is the structure that Cases 3a1 and 3b of §9.7 leave on the selected color class:
*"this color class is equipartitioned"* (the original, `babai-gi.tex`, lines 3981-3992). -/
def eqvConfig (hR : Equivalence R) (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m)
    (h2m : 2 ≤ m) (hlt : m < Fintype.card β) : PartitionStructure β where
  rank := 3
  color := eqvColor R
  color_surjective i := by
    -- `β` is nonempty because `2 ≤ m < |β|`
    have hne : Nonempty β := by
      rw [← Fintype.card_pos_iff]; omega
    obtain ⟨x⟩ := hne
    rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) i with rfl | rfl | rfl
    · exact ⟨x, x, by simp⟩
    · -- the class of `x` has at least two points
      have h1 : 1 < ({y | R x y} : Set β).ncard := by rw [hm x]; omega
      obtain ⟨y, hy, z, hz, hyz⟩ :=
        Set.one_lt_ncard_iff_nontrivial.1 (by simpa using h1)
      exact ⟨y, z, (eqvColor_eq_one_iff R y z).2 ⟨hyz, hR.trans (hR.symm hy) hz⟩⟩
    · -- the class of `x` is not everything
      have hsub : ({y | R x y} : Set β) ≠ Set.univ := by
        intro hc
        have : ({y | R x y} : Set β).ncard = Fintype.card β := by
          rw [hc, Set.ncard_univ, Nat.card_eq_fintype_card]
        rw [hm x] at this; omega
      obtain ⟨y, hy⟩ : ∃ y, y ∉ ({z | R x z} : Set β) := by
        by_contra hcon
        push_neg at hcon
        exact hsub (Set.eq_univ_of_forall hcon)
      exact ⟨x, y, (eqvColor_eq_two_iff R x y).2
        ⟨fun hc => hy (hc ▸ hR.refl x), hy⟩⟩

@[simp] theorem eqvConfig_rank (hR : Equivalence R)
    (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m) (h2m : 2 ≤ m)
    (hlt : m < Fintype.card β) : (eqvConfig hR hm h2m hlt).rank = 3 := rfl

@[simp] theorem eqvConfig_color (hR : Equivalence R)
    (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m) (h2m : 2 ≤ m)
    (hlt : m < Fintype.card β) (x y : β) :
    (eqvConfig hR hm h2m hlt).color x y = eqvColor R x y := rfl

theorem eqvConfig_isHomogeneous (hR : Equivalence R)
    (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m) (h2m : 2 ≤ m)
    (hlt : m < Fintype.card β) : (eqvConfig hR hm h2m hlt).IsHomogeneous := by
  intro x y
  show eqvColor R x x = eqvColor R y y
  simp

theorem eqvConfig_isConfiguration (hR : Equivalence R)
    (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m) (h2m : 2 ≤ m)
    (hlt : m < Fintype.card β) : (eqvConfig hR hm h2m hlt).IsConfiguration where
  diag x y z h := by
    have h' : eqvColor R x y = eqvColor R z z := h
    rw [eqvColor_self] at h'
    exact (eqvColor_eq_zero_iff R x y).1 h'
  converse u v x y h := by
    have h' : eqvColor R u v = eqvColor R x y := h
    show eqvColor R v u = eqvColor R y x
    rw [eqvColor_comm hR v u, eqvColor_comm hR y x]
    exact h'


/-- §9.7, Cases 3a1 and 3b.  The intersection numbers of `Babai.eqvConfig` (Def. 3.1.11):
`p i j k` is the number of `z` with `c(x,z) = i` and `c(z,y) = j` for a pair `(x,y)` of
color `k`.  Here `m` is the common size of a class and `n` the number of points. -/
def pTable (m n : ℕ) (i j k : Fin 3) : ℕ :=
  if k = 0 then (if i ≠ j then 0 else if i = 0 then 1 else if i = 1 then m - 1 else n - m)
  else if k = 1 then
    (if i = 0 then (if j = 1 then 1 else 0)
     else if i = 1 then (if j = 0 then 1 else if j = 1 then m - 2 else 0)
     else (if j = 2 then n - m else 0))
  else
    (if i = 0 then (if j = 2 then 1 else 0)
     else if i = 1 then (if j = 2 then m - 1 else 0)
     else (if j = 0 then 1 else if j = 1 then m - 1 else n - 2 * m))

/-- §9.7, Cases 3a1 and 3b.  The count of Def. 3.1.11 for the three-color coloring of an
equivalence relation whose classes all have size `m`: it depends on `(x, y)` only through
the color `eqvColor R x y`, which is axiom (iii) of a coherent configuration. -/
theorem inter_ncard_eq_pTable (hR : Equivalence R)
    (hm : ∀ x : β, (cls R x).ncard = m) (h2m : 2 ≤ m) (i j : Fin 3) (x y : β) :
    ({z | eqvColor R x z = i} ∩ {z | eqvColor R z y = j}).ncard
      = pTable m (Fintype.card β) i j (eqvColor R x y) := by
  classical
  have hzero : ∀ S T : Set β, S ∩ T = ∅ → (S ∩ T).ncard = 0 := by
    intro S T h; rw [h]; simp
  have hd1 : ∀ w : β, (cls R w \ {w}).ncard = m - 1 := ncard_cls_diff hR hm
  have hcp : ∀ w : β, ((cls R w)ᶜ).ncard = Fintype.card β - m := ncard_cls_compl hm
  by_cases hxy : x = y
  · -- `k = 0`
    subst hxy
    rw [eqvColor_self]
    rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) i with rfl | rfl | rfl <;>
      rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) j with rfl | rfl | rfl
    all_goals try rw [setOut_zero (R := R)]
    all_goals try rw [setOut_one (R := R)]
    all_goals try rw [setOut_two hR (R := R)]
    all_goals try rw [setIn_zero hR (R := R)]
    all_goals try rw [setIn_one hR (R := R)]
    all_goals try rw [setIn_two hR (R := R)]
    · rw [Set.inter_self, Set.ncard_singleton]; simp [pTable]
    · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by simp))]; simp [pTable]
    · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by
        simp [mem_cls_self hR x]))]
      simp [pTable]
    · rw [hzero _ _ (Set.inter_singleton_eq_empty.2 (by simp))]; simp [pTable]
    · rw [Set.inter_self, hd1]; simp [pTable]
    · rw [hzero _ _ (Set.eq_empty_iff_forall_notMem.2 (by
        rintro z ⟨hz1, hz2⟩; exact hz2 hz1.1))]
      simp [pTable]
    · rw [hzero _ _ (Set.inter_singleton_eq_empty.2 (by
        simp [mem_cls_self hR x]))]
      simp [pTable]
    · rw [hzero _ _ (Set.eq_empty_iff_forall_notMem.2 (by
        rintro z ⟨hz1, hz2⟩; exact hz1 hz2.1))]
      simp [pTable]
    · rw [Set.inter_self, hcp]; simp [pTable]
  · by_cases hr : R x y
    · -- `k = 1`
      rw [(eqvColor_eq_one_iff R x y).2 ⟨hxy, hr⟩]
      have hcls : cls R x = cls R y := cls_eq hR hr
      have hyx : y ∈ cls R x := hr
      have hxy' : x ∈ cls R y := hR.symm hr
      rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) i with rfl | rfl | rfl <;>
        rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) j with rfl | rfl | rfl
      all_goals try rw [setOut_zero (R := R)]
      all_goals try rw [setOut_one (R := R)]
      all_goals try rw [setOut_two hR (R := R)]
      all_goals try rw [setIn_zero hR (R := R)]
      all_goals try rw [setIn_one hR (R := R)]
      all_goals try rw [setIn_two hR (R := R)]
      · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by simp [hxy]))]; simp [pTable]
      · rw [Set.inter_eq_self_of_subset_left
          (Set.singleton_subset_iff.2 (show x ∈ cls R y \ {y} from ⟨hxy', by simp [hxy]⟩)),
          Set.ncard_singleton]
        simp [pTable]
      · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by simp [hxy']))]; simp [pTable]
      · rw [Set.inter_eq_self_of_subset_right
          (Set.singleton_subset_iff.2
            (show y ∈ cls R x \ {x} from ⟨hyx, by simp [Ne.symm hxy]⟩)),
          Set.ncard_singleton]
        simp [pTable]
      · rw [← hcls]
        have hset : (cls R x \ {x}) ∩ (cls R x \ {y}) = (cls R x \ {x}) \ {y} := by
          ext z
          simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        rw [hset, Set.ncard_diff_singleton_of_mem
          (show y ∈ cls R x \ {x} from ⟨hyx, by simp [Ne.symm hxy]⟩), hd1]
        have : m - 1 - 1 = m - 2 := by omega
        rw [this]; simp [pTable]
      · rw [← hcls, hzero _ _ (Set.eq_empty_iff_forall_notMem.2 (by
          rintro z ⟨hz1, hz2⟩; exact hz2 hz1.1))]
        simp [pTable]
      · rw [hzero _ _ (Set.inter_singleton_eq_empty.2 (by simp [hyx]))]; simp [pTable]
      · rw [← hcls, hzero _ _ (Set.eq_empty_iff_forall_notMem.2 (by
          rintro z ⟨hz1, hz2⟩; exact hz1 hz2.1))]
        simp [pTable]
      · rw [← hcls, Set.inter_self, hcp]; simp [pTable]
    · -- `k = 2`
      rw [(eqvColor_eq_two_iff R x y).2 ⟨hxy, hr⟩]
      have hd : Disjoint (cls R x) (cls R y) := cls_disjoint hR hr
      have hynx : y ∉ cls R x := hr
      have hxny : x ∉ cls R y := fun hc => hr (hR.symm hc)
      have hsub : cls R x ⊆ (cls R y)ᶜ := by
        intro z hz hz'
        exact (Set.disjoint_left.1 hd) hz hz'
      have hsub' : cls R y ⊆ (cls R x)ᶜ := by
        intro z hz hz'
        exact (Set.disjoint_left.1 hd) hz' hz
      rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) i with rfl | rfl | rfl <;>
        rcases (by decide : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2) j with rfl | rfl | rfl
      all_goals try rw [setOut_zero (R := R)]
      all_goals try rw [setOut_one (R := R)]
      all_goals try rw [setOut_two hR (R := R)]
      all_goals try rw [setIn_zero hR (R := R)]
      all_goals try rw [setIn_one hR (R := R)]
      all_goals try rw [setIn_two hR (R := R)]
      · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by simp [hxy]))]; simp [pTable]
      · rw [hzero _ _ (Set.singleton_inter_eq_empty.2 (by simp [hxny]))]; simp [pTable]
      · rw [Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.2 hxny),
          Set.ncard_singleton]
        simp [pTable]
      · rw [hzero _ _ (Set.inter_singleton_eq_empty.2 (by simp [hynx]))]; simp [pTable]
      · rw [hzero _ _ (Set.eq_empty_iff_forall_notMem.2 (by
          rintro z ⟨hz1, hz2⟩; exact (Set.disjoint_left.1 hd) hz1.1 hz2.1))]
        simp [pTable]
      · rw [Set.inter_eq_self_of_subset_left
          (fun z hz => hsub hz.1), hd1]
        simp [pTable]
      · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.2 hynx),
          Set.ncard_singleton]
        simp [pTable]
      · rw [Set.inter_eq_self_of_subset_right (fun z hz => hsub' hz.1), hd1]
        simp [pTable]
      · have hun : (cls R x)ᶜ ∩ (cls R y)ᶜ = (cls R x ∪ cls R y)ᶜ := by
          rw [Set.compl_union]
        have hcard : (cls R x ∪ cls R y).ncard = 2 * m := by
          rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _), hm, hm]; omega
        have hsum := Set.ncard_add_ncard_compl (cls R x ∪ cls R y)
        rw [hcard, Nat.card_eq_fintype_card] at hsum
        rw [hun]
        have : ((cls R x ∪ cls R y)ᶜ).ncard = Fintype.card β - 2 * m := by omega
        rw [this]; simp [pTable]

/-- §9.7, Cases 3a1 and 3b.  **`Babai.eqvConfig` is a coherent configuration**
(Def. 3.1.11).  The intersection numbers are `Babai.pTable`, and
`Babai.inter_ncard_eq_pTable` is the verification of axiom (iii). -/
theorem eqvConfig_isCoherent (hR : Equivalence R)
    (hm : ∀ x : β, ({y | R x y} : Set β).ncard = m) (h2m : 2 ≤ m)
    (hlt : m < Fintype.card β) : (eqvConfig hR hm h2m hlt).IsCoherent := by
  refine ⟨eqvConfig_isConfiguration hR hm h2m hlt, ?_⟩
  have hm' : ∀ x : β, (cls R x).ncard = m := hm
  refine ⟨fun i j k => pTable m (Fintype.card β) i j k, fun i j k x y hxy => ?_⟩
  have hxy' : eqvColor R x y = k := hxy
  subst hxy'
  exact inter_ncard_eq_pTable hR hm' h2m i j x y

end EqvConfig

end Babai

namespace Babai

/-! ### The hint coloring of a configuration on the blocks -/

open scoped Classical in
/-- §9.5, §9.7.  The hint coloring `h` attached to a partition structure `P` on a family
`U` of blocks: the color labels of `P`, read as natural numbers (Def. 3.1.1) and padded by
`0` outside `U`.  This is the coloring that Cases 3a1, 3a2 and 3b of §9.7 leave on the
ordered pairs of blocks of the part they return. -/
noncomputable def hintColoring {s : Type} (U : Set (Set s)) (P : PartitionStructure ↥U)
    (A B : Set s) : ℕ :=
  if hA : A ∈ U then (if hB : B ∈ U then (P.color ⟨A, hA⟩ ⟨B, hB⟩ : ℕ) else 0) else 0

open scoped Classical in
theorem hintColoring_apply {s : Type} (U : Set (Set s)) (P : PartitionStructure ↥U)
    (A B : ↥U) : hintColoring U P (A : Set s) (B : Set s) = (P.color A B : ℕ) := by
  rw [hintColoring, dif_pos A.2, dif_pos B.2]

open scoped Classical in
/-- The hint coloring is `0` off `U`. -/
theorem hintColoring_off {s : Type} (U : Set (Set s)) (P : PartitionStructure ↥U)
    {A B : Set s} (h : A ∉ U ∨ B ∉ U) : hintColoring U P A B = 0 := by
  rcases h with h | h
  · rw [hintColoring, dif_neg h]
  · rw [hintColoring]
    by_cases hA : A ∈ U
    · rw [dif_pos hA, dif_neg h]
    · rw [dif_neg hA]

/-- §9.5, §9.7.  **A configuration whose color labels are the hint is a hint.**  This is
`Babai.VColBipBlk.HasHint` in the form the two constructors below supply it: the hint
coloring of the object *is* the `ℕ`-valued coloring of a homogeneous coherent
configuration of rank `≥ 3` on the blocks.  The kernel condition of `HasHint` follows,
because `Fin.val` is injective. -/
theorem VColBipBlk.hasHint_of_structure {s : Type} [Fintype s] [DecidableEq s]
    {X : VColBipBlk s ℕ} (P : PartitionStructure ↥X.blocks) (hco : P.IsCoherent)
    (hhom : P.IsHomogeneous) (hrank : 3 ≤ P.rank)
    (hh : ∀ A B : ↥X.blocks, X.h (A : Set s) (B : Set s) = (P.color A B : ℕ)) :
    X.HasHint := by
  refine ⟨P, hco, hhom, hrank, fun A B A' B' => ?_⟩
  rw [hh A B, hh A' B']
  exact ⟨fun h => by rw [h], fun h => Fin.val_injective h⟩

/-- A uniprimitive coherent configuration is homogeneous and has rank `≥ 3`
(Def. 3.2.1): this is why the UPCC of §9.7, Case 3a2 is a hint. -/
theorem PartitionStructure.isHomogeneous_and_rank_of_isUniprimitive {β : Type}
    {P : PartitionStructure β} (h : P.IsUniprimitive) :
    P.IsHomogeneous ∧ 3 ≤ P.rank := ⟨h.1.1, h.2⟩

end Babai
