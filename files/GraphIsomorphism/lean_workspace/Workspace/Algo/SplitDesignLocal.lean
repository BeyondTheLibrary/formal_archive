import Workspace.Algo.SplitDesignCases
import Workspace.SplitOrJohnson.BlkDominant
import Workspace.Algo.SplitBipAlpha

/-! # Section 9.7, Case 2: local degrees and the dominant class

We intersect each neighborhood with the union of the large twin classes.
The size of this intersection is the paper's color c'. Its equal-color
classes determine the strict small-class exit and the dominant class.
-/
namespace Algo
open Babai RAM

def designLocalRow (z : RawUpccCase × ℕ) : List ℕ :=
  (splitNeighborhoodRow (designBip z.1,z.2)).filter
    (fun i => decide (i ∈ designBigPositions z.1))

def designLocalSize (z : RawUpccCase × ℕ) : ℕ := (designLocalRow z).length

def designLocalColors (r : RawUpccCase) : RawLab :=
  (List.range r.2.1.length).map (fun i => designLocalSize (r,i))

def designLocalClass (z : RawUpccCase × ℕ) : List ℕ :=
  (List.range z.1.2.1.length).filter
    (fun j => decide (designLocalSize (z.1,j) = designLocalSize z))

theorem polyFun_designLocalRow : PolyFun designLocalRow := by
  have hm := ((polyFun_fst.comp polyFun_designBip).pair polyFun_snd).comp
    polyFun_splitNeighborhoodRow
  have hp : PolyFun (fun z : List ℕ × ℕ => decide (z.2 ∈ z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp (polyFun_listMem polyFun_natEq)
  exact ((polyFun_fst.comp polyFun_designBigPositions).pair hm).comp (PolyFun.filterParam hp)

theorem polyFun_designLocalSize : PolyFun designLocalSize :=
  polyFun_designLocalRow.comp polyFun_length

theorem polyFun_designLocalColors : PolyFun designLocalColors :=
  (polyFun_id.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_rangeLength)).comp
    (PolyFun.mapParam polyFun_designLocalSize)

theorem polyFun_designLocalClass : PolyFun designLocalClass := by
  have hp : PolyFun (fun z : (RawUpccCase × ℕ) × ℕ =>
      decide (designLocalSize (z.1.1,z.2) = designLocalSize z.1)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_designLocalSize).natEq
      (polyFun_fst.comp polyFun_designLocalSize)
  exact (polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp
    polyFun_rangeLength)).comp (PolyFun.filterParam hp)

abbrev RawDesignLocal := RawUpccCase × (ℕ × ℕ)

def designDomTest (z : RawDesignLocal × ℕ) : Bool :=
  decide (z.1.2.1 * z.1.1.2.1.length ≤ z.1.2.2 * (designLocalClass (z.1.1,z.2)).length)

def designDomPositions (z : RawDesignLocal) : List ℕ :=
  (List.range z.1.2.1.length).filter (fun i => designDomTest (z,i))

def designSmall (z : RawDesignLocal) : Bool := (designDomPositions z).isEmpty

theorem polyFun_designDomTest : PolyFun designDomTest := by
  have hp : PolyFun (fun z : RawDesignLocal × ℕ => z.1.2) := polyFun_fst.comp polyFun_snd
  have hn : PolyFun (fun z : RawDesignLocal × ℕ => z.1.1.2.1.length) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  have hc : PolyFun (fun z : RawDesignLocal × ℕ => (designLocalClass (z.1.1,z.2)).length) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
    polyFun_designLocalClass).comp polyFun_length
  exact ((hp.comp polyFun_fst).mul hn).le ((hp.comp polyFun_snd).mul hc)

theorem polyFun_designDomPositions : PolyFun designDomPositions :=
  (polyFun_id.pair (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp
    polyFun_rangeLength)).comp (PolyFun.filterParam polyFun_designDomTest)

theorem polyFun_designSmall : PolyFun designSmall := polyFun_designDomPositions.comp polyFun_isEmpty

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designLocalRow_mem (x : ↥X.Pt₁) (B : ↥X.blocks) :
    (e₂ B).val ∈ designLocalRow (r,e₁ x) ↔ B.val ∈ X.nbhd x.val ∩ X.bigTwin := by
  simp only [designLocalRow,List.mem_filter,decide_eq_true_eq,
    designRow_mem h e₁ he₁ e₂ he₂,designBigPositions_spec h e₁ he₁ e₂ he₂,Set.mem_inter_iff]

theorem designLocalSize_spec (x : ↥X.Pt₁) : designLocalSize (r,e₁ x) = X.localSize x.val := by
  have hh := splitNamedCount (fun B : ↥X.blocks => (e₂ B).val)
    (fun B C hh => e₂.injective (Fin.ext hh)) (List.range r.2.2.length) List.nodup_range
    (fun i => by
      simp only [List.mem_range]
      exact ⟨fun hi => ⟨e₂.symm ⟨i,hi⟩,congrArg Fin.val (e₂.apply_symm_apply _)⟩,
        fun ⟨B,hB⟩ => hB ▸ (e₂ B).isLt⟩)
    (fun i => decide (i ∈ designLocalRow (r,e₁ x)))
  have he : (List.range r.2.2.length).filter (fun i => decide (i ∈ designLocalRow (r,e₁ x))) =
      designLocalRow (r,e₁ x) := by
    simp only [designLocalRow,splitNeighborhoodRow,List.filter_filter]
    apply List.filter_congr
    intro i hi
    simp [designBip,List.mem_range.1 hi]
  rw [he] at hh
  change (designLocalRow (r,e₁ x)).length = _
  rw [hh]
  have hs : {B : ↥X.blocks | decide ((e₂ B).val ∈ designLocalRow (r,e₁ x)) = true} =
      {B : ↥X.blocks | B.val ∈ X.nbhd x.val ∩ X.bigTwin} := by
    ext B
    simp only [Set.mem_setOf_eq,decide_eq_true_eq]
    exact designLocalRow_mem h e₁ he₁ e₂ he₂ x B
  rw [hs]
  exact X.ncard_coe_blocks (Set.inter_subset_left.trans (X.nbhd_subset_blocks _))

/-- The returned colors are precisely the local neighborhood sizes. -/
theorem designLocalColors_spec (x : ↥X.Pt₁) :
    labAt (designLocalColors r) (e₁ x) = X.localSize x.val := by
  simp only [labAt,designLocalColors]
  rw [show ((List.range r.2.1.length).map (fun i => designLocalSize (r,i))).getD (e₁ x) 0 =
    designLocalSize (r,e₁ x) by simp [(e₁ x).isLt]]
  exact designLocalSize_spec h e₁ he₁ e₂ he₂ x

/-- Every raw color class has the paper's exact cardinality. -/
theorem designLocalClass_size (x : ↥X.Pt₁) :
    (designLocalClass (r,e₁ x)).length = (X.localSizeClass x.val).ncard := by
  have hh := splitNamedCount (fun y : ↥X.Pt₁ => (e₁ y).val)
    (fun y z hh => e₁.injective (Fin.ext hh)) (List.range r.2.1.length) List.nodup_range
    (fun i => by
      simp only [List.mem_range]
      exact ⟨fun hi => ⟨e₁.symm ⟨i,hi⟩,congrArg Fin.val (e₁.apply_symm_apply _)⟩,
        fun ⟨y,hy⟩ => hy ▸ (e₁ y).isLt⟩)
    (fun j => decide (designLocalSize (r,j) = designLocalSize (r,e₁ x)))
  change (designLocalClass (r,e₁ x)).length = _ at hh
  rw [hh]
  have he : Subtype.val '' {y : ↥X.Pt₁ |
      decide (designLocalSize (r,e₁ y) = designLocalSize (r,e₁ x)) = true} =
        X.localSizeClass x.val := by
    ext y
    simp only [Set.mem_image,Set.mem_setOf_eq,decide_eq_true_eq,
      designLocalSize_spec h e₁ he₁ e₂ he₂,BlkCaseObj.localSizeClass]
    exact ⟨fun ⟨z,hz,hzy⟩ => hzy ▸ ⟨z.property,hz⟩,
      fun ⟨hy,hcol⟩ => ⟨⟨y,hy⟩,hcol,rfl⟩⟩
  rw [← he,Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The inclusive integer comparison is the dominant-class test in Case 2. -/
theorem designDomTest_spec (p : ℕ × ℕ) (hb : 0 < p.2) (x : ↥X.Pt₁) :
    designDomTest ((r,p),e₁ x) = true ↔ x.val ∈ X.domClass (sbipAlphaValue p) := by
  rw [designDomTest,decide_eq_true_eq,designLocalClass_size h e₁ he₁ e₂ he₂]
  dsimp only
  rw [designLeft_length e₁]
  change _ ↔ X.part₁ x.val ∧ _
  rw [and_iff_right (show X.part₁ x.val from x.property),sbipAlphaValue,div_mul_eq_mul_div,
    div_le_iff₀ (show (0:ℝ) < p.2 by exact_mod_cast hb)]
  rw [mul_comm ((X.localSizeClass x.val).ncard : ℝ)]
  exact_mod_cast Iff.rfl

theorem designDomPositions_spec (p : ℕ × ℕ) (hb : 0 < p.2) (x : ↥X.Pt₁) :
    (e₁ x).val ∈ designDomPositions (r,p) ↔ x.val ∈ X.domClass (sbipAlphaValue p) := by
  simp only [designDomPositions,List.mem_filter,List.mem_range,(e₁ x).isLt,true_and]
  exact designDomTest_spec h e₁ he₁ e₂ he₂ p hb x

/-- The early exit is strict, as printed in the paper. Equality enters the dominant branch. -/
theorem designSmall_spec (p : ℕ × ℕ) (hb : 0 < p.2) :
    designSmall (r,p) = true ↔ ∀ x : ↥X.Pt₁,
      ((X.localSizeClass x.val).ncard : ℝ) < sbipAlphaValue p * X.n₁ := by
  rw [designSmall,List.isEmpty_iff,List.eq_nil_iff_forall_not_mem]
  constructor
  · intro hh x
    apply lt_of_not_ge
    intro hx
    exact hh (e₁ x) ((designDomPositions_spec h e₁ he₁ e₂ he₂ p hb x).2 ⟨x.property,hx⟩)
  · intro hh i hi
    have hil := List.mem_range.1 (List.mem_of_mem_filter hi)
    let x := e₁.symm ⟨i,hil⟩
    have hx : x.val ∈ X.domClass (sbipAlphaValue p) :=
      (designDomPositions_spec h e₁ he₁ e₂ he₂ p hb x).1 (by
        simpa only [x,Equiv.apply_symm_apply] using hi)
    exact (not_le_of_gt (hh x)) hx.2

end Specification
end Algo
