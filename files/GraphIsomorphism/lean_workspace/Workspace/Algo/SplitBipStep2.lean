import Workspace.Algo.SplitNumberings
import Workspace.Algo.SplitBipRestrict
import Workspace.Machine.ListSum

/-! # Section 9.4, step 2 on the RAM

Individualize the second part. A first-part point receives its old color
paired with the set of numbered neighbors, represented as a binary mask.
This is the exact color `blkColor` used by `step_9_4_2`.
The numbering family follows the pseudocode's full individualization.
-/

namespace Algo
open Babai RAM RAM.Targets

/-- The domain witness caps the exponent even on malformed input. -/
def sbipMaskBit (z : List ℕ × ℕ) : ℕ := 2 ^ min z.2 z.1.length

def sbipMask (p : List ℕ × List ℕ) : ℕ :=
  (((List.range p.1.length).filter (fun i => decide (i ∈ p.2))).map
    (fun i => sbipMaskBit (p.1, i))).sum

theorem polyFun_sbipMaskBit : PolyFun sbipMaskBit := by
  apply PolyFun.pow (polyFun_const 2)
    ((polyFun_snd.pair (polyFun_fst.comp polyFun_length)).comp polyFun_min)
    (q := id) _ polyBound_id
  intro z
  exact (min_le_right _ _).trans ((length_le_size _).trans (size_fst_le' z))

theorem polyFun_sbipMask : PolyFun sbipMask := by
  have hp : PolyFun (fun z : (List ℕ × List ℕ) × ℕ => decide (z.2 ∈ z.1.2)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp (polyFun_listMem polyFun_natEq)
  have hl := (polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam hp)
  exact (((polyFun_fst.pair hl).comp (PolyFun.mapParam polyFun_sbipMaskBit)).comp
    polyFun_listSum)

theorem sbipMask_spec (dom selected : List ℕ) :
    sbipMask (dom, selected) =
      ∑ i ∈ (Finset.range dom.length).filter (fun i => i ∈ selected), 2 ^ i := by
  unfold sbipMask
  have he : (((List.range dom.length).filter (fun i => decide (i ∈ selected))).map
      (fun i => sbipMaskBit (dom, i))) =
      (((List.range dom.length).filter (fun i => decide (i ∈ selected))).map
        (fun i => 2 ^ i)) := by
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    simp only [sbipMaskBit, min_eq_left hi'.le]
  rw [he, ← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter]
  have hr : (List.range dom.length).toFinset = Finset.range dom.length := by
    ext i
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [hr]
  simp only [decide_eq_true_eq]

/-- First and second parts with adjacency rows, first-part colors, and a numbering. -/
abbrev RawSbipStep2 := (RawUpccBip × RawLab) × RawPerm

def sbipMatrixEntry (z : RawUpccBip × (ℕ × ℕ)) : ℕ :=
  (z.1.2.2.getD z.2.1 []).getD z.2.2 0

theorem polyFun_sbipMatrixEntry : PolyFun sbipMatrixEntry := by
  have hr : PolyFun (fun z : RawUpccBip × (ℕ × ℕ) => z.1.2.2.getD z.2.1 []) :=
    (((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
    (polyFun_snd.comp polyFun_fst)).pair (polyFun_const ([] : List ℕ))).comp polyFun_getD)
  exact ((hr.pair (polyFun_snd.comp polyFun_snd)).pair (polyFun_const 0)).comp polyFun_getD

/-- The numbers of the neighbors of one first-part point. -/
def sbipStep2Neighbors (z : RawSbipStep2 × ℕ) : List ℕ :=
  ((List.range z.1.1.1.2.1.length).filter
    (fun j => decide (sbipMatrixEntry (z.1.1.1, (z.2, j)) ≠ 0))).map
      (fun j => z.1.2.getD j 0)

theorem polyFun_sbipStep2Neighbors : PolyFun sbipStep2Neighbors := by
  have hg : PolyFun (fun z : (RawSbipStep2 × ℕ) × ℕ => z.1.1.1.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_fst)
  have he := (hg.pair ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp
    polyFun_sbipMatrixEntry
  have ht := wftPolyFun_not (he.natEq (polyFun_const 0))
  have hd : PolyFun (fun z : RawSbipStep2 × ℕ => List.range z.1.1.1.2.1.length) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp
      polyFun_fst).comp polyFun_rangeLength)
  have hf := (polyFun_id.pair hd).comp (PolyFun.filterParam ht)
  have hget : PolyFun (fun z : RawPerm × ℕ => z.1.getD z.2 0) :=
    ((polyFun_fst.pair polyFun_snd).pair (polyFun_const 0)).comp polyFun_getD
  exact ((((polyFun_fst.comp polyFun_snd).pair hf).comp (PolyFun.mapParam hget))).of_eq
    (fun z => by simp only [sbipStep2Neighbors, decide_not, ne_eq, id_eq]; rfl)

def sbipStep2Color (z : RawSbipStep2 × ℕ) : ℕ :=
  Nat.pair (z.1.1.2.getD z.2 0) (sbipMask (z.1.1.1.2.1, sbipStep2Neighbors z))

theorem polyFun_sbipStep2Color : PolyFun sbipStep2Color := by
  have hc : PolyFun (fun z : RawSbipStep2 × ℕ => z.1.1.2.getD z.2 0) :=
    (((((polyFun_fst.comp polyFun_fst).comp polyFun_snd).pair polyFun_snd).pair
    (polyFun_const 0)).comp polyFun_getD)
  have hd : PolyFun (fun z : RawSbipStep2 × ℕ => z.1.1.1.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact (hc.pair ((hd.pair polyFun_sbipStep2Neighbors).comp polyFun_sbipMask)).comp
    polyFun_upccNatPair

def sbipStep2 (p : RawSbipStep2) : RawLab × RawLab :=
  let l := (List.range p.1.1.1.length).map (fun i => sbipStep2Color (p, i))
  (l, l)

theorem polyFun_sbipStep2 : PolyFun sbipStep2 := by
  have hl : PolyFun (fun p : RawSbipStep2 =>
      (List.range p.1.1.1.length).map (fun i => sbipStep2Color (p, i))) :=
    (polyFun_id.pair (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp
      polyFun_rangeLength)).comp (PolyFun.mapParam polyFun_sbipStep2Color)
  exact hl.pair hl

def sbipStep2Versions (c : ℕ) (p : RawUpccBip × RawLab) : List (RawLab × RawLab) :=
  (sbipNumberings c (p.1.1, p.1.2.1)).map (fun row => sbipStep2 (p, row))

theorem quasiFun_sbipStep2Versions (c : ℕ) : QuasiFun (sbipStep2Versions c) :=
  (polyFun_id.quasiFun.pair (((polyFun_fst.comp polyFun_fst).pair
    ((polyFun_fst.comp polyFun_snd).comp polyFun_fst)).comp_quasiFun
      (quasiFun_sbipNumberings c))).comp_poly (PolyFun.mapParam polyFun_sbipStep2)

theorem sbipStep2_get (p : RawSbipStep2) (i : Fin p.1.1.1.length) :
    labAt (sbipStep2 p).1 i = sbipStep2Color (p, i) := by
  simp [sbipStep2, labAt, i.isLt]

@[simp] theorem sbipStep2_lengths (p : RawSbipStep2) :
    (sbipStep2 p).1.length = p.1.1.1.length ∧ (sbipStep2 p).2.length = p.1.1.1.length := by
  simp [sbipStep2]

section Specification

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) {r : RawSbipStep2}
    (e₁ : ↥G.V₁ ≃ Fin r.1.1.1.length) (e₂ : ↥G.blocks ≃ Fin r.1.1.2.1.length)

open scoped Classical in
noncomputable def sbipBlockNumbering (B : Set ↥s) : ℕ :=
  if h : B ∈ G.blocks then (decPerm r.1.1.2.1.length r.2 (e₂ ⟨B, h⟩)).val else 0

theorem sbipBlockNumbering_valid : IsBlockNumbering G (sbipBlockNumbering G e₂) := by
  have hn : r.1.1.2.1.length = G.numBlocks := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq, VColBipBlk.numBlocks] using
      (Nat.card_congr e₂).symm
  refine ⟨fun B hB => dif_neg hB, ?_, ?_⟩
  · intro B hB C hC he
    have hh : decPerm _ r.2 (e₂ ⟨B, hB⟩) = decPerm _ r.2 (e₂ ⟨C, hC⟩) := by
      apply Fin.ext
      simpa only [sbipBlockNumbering, dif_pos hB, dif_pos hC] using he
    exact congrArg Subtype.val (e₂.injective ((decPerm _ r.2).injective hh))
  · intro B hB
    simp only [sbipBlockNumbering, dif_pos hB]
    rw [← hn]
    exact (decPerm _ r.2 (e₂ ⟨B, hB⟩)).isLt

theorem sbipBlockNumbering_get (hr : RawPerm.WF r.1.1.2.1.length r.2) (B : ↥G.blocks) :
    sbipBlockNumbering G e₂ B.val = r.2.getD (e₂ B) 0 := by
  simp only [sbipBlockNumbering, dif_pos B.property, decPerm_val_of_wf hr]
  exact (List.getD_eq_getElem _ 0 (by simpa only [hr.length] using (e₂ B).isLt)).symm

/-- Every mathematical block numbering is represented by the enumerated raw family. -/
theorem sbipBlockNumbering_complete {c : ℕ}
    (hg : r.1.1.2.1.length ≤ guardBound c r.1.1.1.length)
    (σ : Set ↥s → ℕ) (hσ : IsBlockNumbering G σ) :
    ∃ row ∈ sbipNumberings c (r.1.1.1, r.1.1.2.1),
      sbipBlockNumbering G (r := (r.1, row)) e₂ = σ := by
  have hcard : r.1.1.2.1.length = G.numBlocks := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq, VColBipBlk.numBlocks] using
      (Nat.card_congr e₂).symm
  obtain ⟨row, hrow, he⟩ := sbipNumberings_realizes e₂ (fun B => σ B.val)
    (fun B C hBC => Subtype.ext (hσ.2.1 B.property C.property hBC))
    (fun B => by rw [hcard]; exact hσ.2.2 B.val B.property) hg
  refine ⟨row, hrow, funext fun B => ?_⟩
  by_cases hB : B ∈ G.blocks
  · simpa only [sbipBlockNumbering, dif_pos hB] using he ⟨B, hB⟩
  · simp only [sbipBlockNumbering, dif_neg hB, hσ.1 B hB]

variable (hr : RawPerm.WF r.1.1.2.1.length r.2)
    (hedge : ∀ (x : ↥G.V₁) (B : ↥G.blocks),
      sbipMatrixEntry (r.1.1, ((e₁ x).val, (e₂ B).val)) ≠ 0 ↔ (x.val, B.val) ∈ G.E)

include hr hedge in
theorem sbipStep2Neighbors_spec (x : ↥G.V₁) (i : ℕ) :
    i ∈ sbipStep2Neighbors (r, (e₁ x).val) ↔
      ∃ B ∈ G.blocks, sbipBlockNumbering G e₂ B = i ∧ (x.val, B) ∈ G.E := by
  simp only [sbipStep2Neighbors, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j, ⟨hj, he⟩, hjr⟩
    let B := e₂.symm ⟨j, hj⟩
    have heB : e₂ B = ⟨j, hj⟩ := e₂.apply_symm_apply _
    refine ⟨B.val, B.property, ?_, ?_⟩
    · rw [sbipBlockNumbering_get G e₂ hr B, heB]
      exact hjr
    · apply (hedge x B).1
      simpa only [heB] using he
  · rintro ⟨B, hB, hi, he⟩
    refine ⟨(e₂ ⟨B, hB⟩).val, ⟨(e₂ ⟨B, hB⟩).isLt, (hedge x ⟨B, hB⟩).2 he⟩, ?_⟩
    rw [← sbipBlockNumbering_get G e₂ hr ⟨B, hB⟩]
    exact hi

include hr hedge in
/-- Exact color names, not only equality of color classes. -/
theorem sbipStep2Color_spec
    (hcolor : ∀ x : ↥G.V₁, r.1.2.getD (e₁ x) 0 = G.f x.val) (x : ↥G.V₁) :
    sbipStep2Color (r, (e₁ x).val) = blkColor G (sbipBlockNumbering G e₂) x.val := by
  have hn : r.1.1.2.1.length = G.numBlocks := by
    simpa only [Nat.card_fin, Nat.card_coe_set_eq, VColBipBlk.numBlocks] using
      (Nat.card_congr e₂).symm
  rw [sbipStep2Color, hcolor x, sbipMask_spec, blkColor]
  congr 1
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_range,
      sbipStep2Neighbors_spec G e₁ e₂ hr hedge, hn]
  · intro i hi; rfl

include hr hedge in
theorem sbipStep2_spec
    (hcolor : ∀ x : ↥G.V₁, r.1.2.getD (e₁ x) 0 = G.f x.val) (x y : ↥G.V₁) :
    labAt (sbipStep2 r).1 (e₁ x) =
      (kerPartition G.V₁ (blkColor G (sbipBlockNumbering G e₂))).color (mkPt x.property) ∧
    (LabRel (sbipStep2 r).2 (e₁ x) (e₁ y) ↔
      (kerPartition G.V₁ (blkColor G (sbipBlockNumbering G e₂))).part
        (mkPt x.property) (mkPt y.property)) := by
  have hc (u : ↥G.V₁) : labAt (sbipStep2 r).1 (e₁ u) =
      blkColor G (sbipBlockNumbering G e₂) u.val := by
    rw [sbipStep2_get]
    exact sbipStep2Color_spec G e₁ e₂ hr hedge hcolor u
  refine ⟨hc x, ?_⟩
  change labAt (sbipStep2 r).1 (e₁ x) = labAt (sbipStep2 r).1 (e₁ y) ↔ _
  rw [hc x, hc y]
  rfl

end Specification

theorem sbipStep2_good {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) {r : RawSbipStep2}
    (e : ↥X.obj.1.1.blocks ≃ Fin r.1.1.2.1.length) :
    Good_9_2_2 X ⟨Subtype.val '' X.obj.1.1.V₁,
      Sum.inl (kerPartition X.obj.1.1.V₁ (blkColor X.obj.1.1
        (sbipBlockNumbering X.obj.1.1 e)))⟩ := by
  classical
  obtain ⟨hα, hα1, h2, hlt, hdef⟩ := X.obj.2
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  have hn : 0 < X.obj.1.1.V₁.ncard := by omega
  refine ⟨rfl, kerPartition_isAlphaPartition _ _ _
    (fun x hx => blkColor_class_le X.obj.1.1 (sbipBlockNumbering_valid _ e) hx) ?_⟩
  exact symmetricity₁_le_alpha X.obj.1.1 hn hdef

theorem sbipStep2Versions_width {C : ℕ} (p : RawUpccBip × RawLab)
    (hn : p.1.2.1.length ≤ C * Nat.log 2 p.1.1.length) :
    (sbipStep2Versions (C + 1) p).length ≤ p.1.2.1.length ^ p.1.2.1.length := by
  rw [sbipStep2Versions, List.length_map]
  exact length_sbipNumberings_le (sbip_log_guard hn)

end Algo

#print axioms Algo.quasiFun_sbipStep2Versions
#print axioms Algo.sbipStep2Color_spec
#print axioms Algo.sbipStep2_spec
#print axioms Algo.sbipStep2_good
#print axioms Algo.sbipBlockNumbering_complete
