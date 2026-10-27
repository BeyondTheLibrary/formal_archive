/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, steps 1 and 2: the colored partition of `V₁` whose blocks are the classes of a
coloring of the vertices.
-/
import Workspace.SplitOrJohnson.Defs
import Workspace.Functors.Equivariant

/-!
# §9.4  The colored partition returned by steps 1 and 2

Steps 1 and 2 of Procedure Bipartite Split-or-Johnson (§9.4) both return a colored
partition of `V₁` of the same shape: a coloring `col` of the vertices is computed, and the
blocks of the returned partition are exactly the color classes of `col`.

Reading the blocks as the color classes is what makes the partition *admissible*
(Def. 7.1.1: a block of a color class of size `≥ 2` must have size `≥ 2`), because a block
and its color class are then the same set.

This file builds that partition once and for all:

* `Babai.kerPartition W col` is the colored partition of `W` with color `col` and with the
  color classes as blocks;
* `Babai.kerPartition_isAlphaPartition` turns a bound on the size of the color classes
  into *"this is a colored `α`-partition"* (Def. 7.1.1);
* `Babai.kerPartition_mem_subIso` is its canonicity: a bijection of the vertex sets that
  carries `W` onto `W'` and `col'` onto `col` is a morphism of the two partitions, read in
  the category `Babai.Cat.sub (Babai.SplitOutcomes Ω)` in which an outcome of §9 lives.

## Indexing

An object of a `Babai.Cat Ω` on `s` has its points in `↥s`, while an outcome of §9 lives on
a **subset of `Ω`**.  A subset `W ⊆ ↥s` is therefore carried to the subset
`Subtype.val '' W ⊆ Ω`, and `Babai.liftPt` moves a point of `Subtype.val '' W` back to the
point of `↥s` it came from.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Moving between `W ⊆ ↥s` and `Subtype.val '' W ⊆ Ω` -/

/-- The point of `↥s` underlying a point of the image `Subtype.val '' W`. -/
def liftPt {s : Set Ω} {W : Set ↥s} (z : ↥(Subtype.val '' W)) : ↥s :=
  ⟨(z : Ω), by obtain ⟨w, -, hw⟩ := z.2; exact hw ▸ w.2⟩

@[simp] theorem liftPt_val {s : Set Ω} {W : Set ↥s} (z : ↥(Subtype.val '' W)) :
    ((liftPt z : ↥s) : Ω) = (z : Ω) := rfl

theorem liftPt_mem {s : Set Ω} {W : Set ↥s} (z : ↥(Subtype.val '' W)) : liftPt z ∈ W := by
  obtain ⟨w, hw, hwz⟩ := z.2
  have hz : liftPt z = w := Subtype.ext hwz.symm
  rw [hz]; exact hw

theorem liftPt_injective {s : Set Ω} {W : Set ↥s} :
    Function.Injective (liftPt (W := W)) :=
  fun a b h =>
    Subtype.ext (show (a : Ω) = (b : Ω) from congrArg (fun u : ↥s => (u : Ω)) h)

/-- The point of `Subtype.val '' W` coming from a point of `W`. -/
def mkPt {s : Set Ω} {W : Set ↥s} {x : ↥s} (hx : x ∈ W) : ↥(Subtype.val '' W) :=
  ⟨(x : Ω), ⟨x, hx, rfl⟩⟩

@[simp] theorem liftPt_mkPt {s : Set Ω} {W : Set ↥s} {x : ↥s} (hx : x ∈ W) :
    liftPt (mkPt hx) = x := rfl

/-- The image of `W` inside `Ω` has as many points as `W`. -/
theorem ncard_image_val {s : Set Ω} (W : Set ↥s) :
    (Subtype.val '' W).ncard = W.ncard :=
  Set.ncard_image_of_injective _ Subtype.val_injective

theorem card_image_val {s : Set Ω} (W : Set ↥s) (iF : Fintype ↥(Subtype.val '' W)) :
    (@Fintype.card ↥(Subtype.val '' W) iF : ℕ) = W.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ncard_image_val]

/-! ### The colored partition whose blocks are the color classes -/

/-- §9.4, steps 1 and 2.  The colored partition of `W` whose color is `col` and whose
blocks are the color classes of `col`.

Taking the blocks to be the color classes is what the paper's *"return the colored
partition of `V₁`"* means after a refinement: each block is one class of the refinement. -/
def kerPartition {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    ColoredPartition ↥(Subtype.val '' W) ℕ where
  color z := col (liftPt z)
  part := Setoid.ker fun z => col (liftPt z)
  part_le_color h := h

@[simp] theorem kerPartition_color {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ)
    (z : ↥(Subtype.val '' W)) : (kerPartition W col).color z = col (liftPt z) := rfl

/-- A block of `Babai.kerPartition` is a color class, which is what makes the partition
admissible (Def. 7.1.1). -/
theorem kerPartition_block {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ)
    (z : ↥(Subtype.val '' W)) :
    (kerPartition W col).block z
      = (kerPartition W col).colorClass ((kerPartition W col).color z) := rfl

/-- Definition 7.1.1.  A partition whose blocks are the color classes is admissible. -/
theorem kerPartition_isAdmissible {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    (kerPartition W col).IsAdmissible := fun z h => by
  rw [kerPartition_block]; exact h

/-- A block of `Babai.kerPartition` has at most as many points as the corresponding color
class of `col` inside `W`. -/
theorem kerPartition_ncard_block_le {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ)
    (z : ↥(Subtype.val '' W)) :
    ((kerPartition W col).block z).ncard
      ≤ {y : ↥s | y ∈ W ∧ col y = col (liftPt z)}.ncard := by
  refine Set.ncard_le_ncard_of_injOn liftPt (fun y hy => ⟨liftPt_mem y, hy⟩)
    (fun _ _ _ _ hab => liftPt_injective hab) (Set.toFinite _)

/-- Definition 7.1.1.  If every color class of `col` inside `W` has at most `k` points and
`k ≤ α|W|`, then `Babai.kerPartition W col` is a colored `α`-partition of `W`. -/
theorem kerPartition_isAlphaPartition {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ)
    (iF : Fintype ↥(Subtype.val '' W)) {α : ℝ} {k : ℕ}
    (h : ∀ x ∈ W, {y : ↥s | y ∈ W ∧ col y = col x}.ncard ≤ k)
    (hk : (k : ℝ) ≤ α * (W.ncard : ℝ)) :
    @ColoredPartition.IsAlphaPartition _ _ (kerPartition W col) iF α := by
  refine ⟨kerPartition_isAdmissible W col, ?_⟩
  have hrho : @ColoredPartition.rho _ _ (kerPartition W col) iF ≤ k := by
    refine ColoredPartition.rho_le _ fun z => ?_
    exact (kerPartition_ncard_block_le W col z).trans (h _ (liftPt_mem z))
  have hrhoR : (@ColoredPartition.rho _ _ (kerPartition W col) iF : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hrho
  rw [card_image_val W iF]
  linarith

/-! ### Canonicity -/

/-- The restriction of a bijection `φ : ↥s ≃ ↥t` that carries `W` onto `W'`, read between
the images of `W` and `W'` inside `Ω`. -/
def subEquiv {s t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) :
    ↥(Subtype.val '' W) ≃ ↥(Subtype.val '' W') where
  toFun z := ⟨(φ (liftPt z) : Ω), ⟨φ (liftPt z), (h _).2 (liftPt_mem z), rfl⟩⟩
  invFun w := ⟨(φ.symm (liftPt w) : Ω),
    ⟨φ.symm (liftPt w), by
      rw [← h (φ.symm (liftPt w)), Equiv.apply_symm_apply]; exact liftPt_mem w, rfl⟩⟩
  left_inv z := by
    refine Subtype.ext ?_
    show ((φ.symm (liftPt (⟨(φ (liftPt z) : Ω), _⟩ : ↥(Subtype.val '' W'))) : ↥s) : Ω)
      = (z : Ω)
    have hl : liftPt (⟨(φ (liftPt z) : Ω), ⟨φ (liftPt z), (h _).2 (liftPt_mem z), rfl⟩⟩ :
        ↥(Subtype.val '' W')) = φ (liftPt z) := Subtype.ext rfl
    rw [hl, Equiv.symm_apply_apply]
    rfl
  right_inv w := by
    refine Subtype.ext ?_
    have hl : liftPt (⟨(φ.symm (liftPt w) : Ω), ⟨φ.symm (liftPt w), by
        rw [← h (φ.symm (liftPt w)), Equiv.apply_symm_apply]; exact liftPt_mem w, rfl⟩⟩ :
        ↥(Subtype.val '' W)) = φ.symm (liftPt w) := Subtype.ext rfl
    show ((φ (liftPt (⟨(φ.symm (liftPt w) : Ω), _⟩ : ↥(Subtype.val '' W))) : ↥t) : Ω)
      = (w : Ω)
    rw [hl, Equiv.apply_symm_apply]
    rfl

@[simp] theorem liftPt_subEquiv {s t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (z : ↥(Subtype.val '' W)) :
    liftPt (subEquiv φ h z) = φ (liftPt z) := Subtype.ext rfl

/-- §7.1.  **Canonicity of `Babai.kerPartition`.**  A bijection that carries `W` onto `W'`
and the coloring `col'` back to `col` is a morphism of the two colored partitions. -/
theorem kerPartition_mem_iso {s t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) {col : ↥s → ℕ} {col' : ↥t → ℕ}
    (hc : ∀ x, col' (φ x) = col x) :
    subEquiv φ h ∈
      (ColoredPartitions Ω ℕ).Iso (kerPartition W col) (kerPartition W' col') := by
  refine ⟨fun z => ?_, fun z w => ?_⟩
  · show col' (liftPt (subEquiv φ h z)) = col (liftPt z)
    rw [liftPt_subEquiv]; exact hc _
  · show (col (liftPt z) = col (liftPt w))
      ↔ (col' (liftPt (subEquiv φ h z)) = col' (liftPt (subEquiv φ h w)))
    rw [liftPt_subEquiv, liftPt_subEquiv, hc, hc]

/-- §6, §9.  `Babai.kerPartition` as an outcome of §9: an object of `Babai.SplitOutcomes`
on the subset `Subtype.val '' W` of `□X`. -/
def kerOutcome {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    (Cat.sub (SplitOutcomes Ω)).Obj s :=
  ⟨⟨Subtype.val '' W, by rintro z ⟨w, -, rfl⟩; exact w.2⟩, Sum.inl (kerPartition W col)⟩

@[simp] theorem kerOutcome_car {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ) :
    (kerOutcome W col).1.1 = Subtype.val '' W := rfl

/-- §6.  Condition (ii) of Definition 6.0.1 for the outcomes of steps 1 and 2: a morphism
of the inputs carries the colored partition of one to the colored partition of the
other. -/
theorem kerOutcome_mem_subIso {s t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) {col : ↥s → ℕ} {col' : ↥t → ℕ}
    (hc : ∀ x, col' (φ x) = col x) :
    φ ∈ (Cat.sub (SplitOutcomes Ω)).Iso (kerOutcome W col) (kerOutcome W' col') :=
  ⟨subEquiv φ h, fun _ => rfl, kerPartition_mem_iso φ h hc⟩

end Babai
