import Workspace.Algo.SplitDesignRank
import Workspace.Algo.AlignJohnson

/-! # Section 9.7, Case 1: the labelled Johnson scheme

The labels are neighborhoods, complemented when their size exceeds half
the second part. The paper proves that all subsets of that size occur.
Together with the absence of twins in the first part, this gives exactly
the well-formed Johnson encoding required by Align.
-/
namespace Algo
open Babai RAM

/-- The first-part names carry the Johnson scheme. -/
def designJohnson (r : RawUpccCase) : RawJohnson :=
  (r.2.1,designRank r,designLabels r)

theorem polyFun_designJohnson : PolyFun designJohnson :=
  (polyFun_snd.comp polyFun_fst).pair (polyFun_designRank.pair polyFun_designLabels)

theorem designLabel_sorted (r : RawUpccCase) (i : ℕ) :
    (designLabel (r,i)).SortedLT := by
  unfold designLabel
  split
  · exact (List.pairwise_lt_range.filter _).sortedLT
  · exact (List.pairwise_lt_range.filter _).sortedLT

theorem designLabel_lt (r : RawUpccCase) (i : ℕ) (a : ℕ)
    (ha : a ∈ designLabel (r,i)) : a < r.2.2.length := by
  unfold designLabel at ha
  split at ha
  · exact (mem_splitNeighborhoodRow _ _ _).1 ha |>.1
  · exact (designComplementRow_mem _ _ _).1 ha |>.1

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

open scoped Classical in
/-- The finite-set label has exactly the complement convention of the proof. -/
theorem designLabel_set (x : ↥X.Pt₁) :
    rawJSet r.2.2.length (designLabel (r,e₁ x)) =
      if 2 * X.d₁ ≤ X.n₂ then (X.label x.val).image e₂
      else Finset.univ \ (X.label x.val).image e₂ := by
  classical
  ext i
  obtain ⟨B,rfl⟩ := e₂.surjective i
  rw [mem_rawJSet,designLabel_mem h e₁ he₁ e₂ he₂]
  have hb : e₂ B ∈ (X.label x.val).image e₂ ↔ B.val ∈ X.nbhd x.val := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨C,hC,hCB⟩
      have : C = B := e₂.injective hCB
      subst C
      simpa only [BlkCaseObj.label,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hC
    · intro hB
      exact ⟨B,by simpa only [BlkCaseObj.label,Set.Finite.mem_toFinset,Set.mem_setOf_eq] using hB,rfl⟩
  split <;> simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,hb]

theorem designLabel_length (x : ↥X.Pt₁) :
    (designLabel (r,e₁ x)).length = X.d' := by
  classical
  rw [← card_rawJSet (designLabel_sorted r _).nodup (designLabel_lt r _),
    designLabel_set h e₁ he₁ e₂ he₂]
  have hd : X.d₁ ≤ X.n₂ := X.d₁_le_numBlocks
  split
  next hs =>
    rw [Finset.card_image_of_injective _ e₂.injective,X.card_label,X.nbhd_ncard_eq_d₁ x.property]
    exact (min_eq_left (by omega)).symm
  next hs =>
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
      Finset.card_image_of_injective _ e₂.injective,X.card_label,X.nbhd_ncard_eq_d₁ x.property,
      designRight_length e₂]
    exact (min_eq_right (by omega)).symm

/-- Distinct first-part points retain distinct labels, in either rank convention. -/
theorem designLabel_injective : Function.Injective (fun x : ↥X.Pt₁ => designLabel (r,e₁ x)) := by
  intro x y hxy
  dsimp only at hxy
  apply Subtype.ext
  apply X.nbhd_injective x.property y.property
  ext B
  by_cases hB : B ∈ X.blocks
  · have hh : (e₂ ⟨B,hB⟩).val ∈ designLabel (r,e₁ x) ↔
        (e₂ ⟨B,hB⟩).val ∈ designLabel (r,e₁ y) := by rw [hxy]
    rw [designLabel_mem h e₁ he₁ e₂ he₂,designLabel_mem h e₁ he₁ e₂ he₂] at hh
    split at hh
    · exact hh
    · exact not_iff_not.mp hh
  · exact iff_of_false (fun hb => hB (X.nbhd_subset_blocks _ hb))
      (fun hb => hB (X.nbhd_subset_blocks _ hb))

theorem designLabels_nodup : (designLabels r).Nodup := by
  apply List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  let x := e₁.symm ⟨i,List.mem_range.1 hi⟩
  let y := e₁.symm ⟨j,List.mem_range.1 hj⟩
  have he : x = y := designLabel_injective h e₁ he₁ e₂ he₂ (by
    simpa only [x,y,Equiv.apply_symm_apply] using hij)
  simpa only [x,y,Equiv.apply_symm_apply] using congrArg (fun z => (e₁ z).val) he

omit h he₁ he₂ in
/-- Case 1 supplies every subset of the common rank, exactly once. -/
theorem designCase1_card (hcase : X.IsCase1) : X.n₁ = X.n₂.choose X.d' := by
  classical
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  have hb : Fintype.card ↥X.blocks = X.n₂ := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]; rfl
  have hc : X.n₁ = X.n₂.choose X.d₁ := by
    have hc := Nat.card_congr (X.labelEquiv hcase)
    rw [Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Fintype.card_finset_len,hb] at hc
    exact hc
  rw [hc,BlkCaseObj.d']
  by_cases hd : X.d₁ ≤ X.n₂ - X.d₁
  · rw [min_eq_left hd]
  · rw [min_eq_right (by omega)]
    exact (Nat.choose_symm (show X.d₁ ≤ X.n₂ from X.d₁_le_numBlocks)).symm

/-- The computed encoding meets every field of Align's Johnson contract. -/
theorem designJohnson_wf (hw : r.WF) (hlt : X.n₂ < X.n₁) (hcase : X.IsCase1) :
    RawJohnson.WF r.1.1.length X.n₂ X.d' (designJohnson r) := by
  have hparam : 2 * X.d' + 1 ≤ X.n₂ := by
    have hd : X.d₁ ≤ X.n₂ := X.d₁_le_numBlocks
    have hh := X.numBlocks_ne_two_mul_d₁ hcase
    change X.n₂ ≠ 2 * X.d₁ at hh
    rw [BlkCaseObj.d']
    omega
  refine ⟨X.two_le_d' hlt,hparam,designRank_spec h e₁ he₁ e₂ he₂,
    ?_,hw.left_nodup,designLabels_length r,?_,?_,?_,designLabels_nodup h e₁ he₁ e₂ he₂,?_⟩
  · intro w hw'
    exact (hw.table.domMem _).1 ((hw.cover _).1 (List.mem_append_left _ hw'))
  · intro row hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.1 hr
    exact designLabel_sorted r i
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 hr
    have hh := designLabel_length h e₁ he₁ e₂ he₂ (e₁.symm ⟨i,List.mem_range.1 hi⟩)
    simpa only [Equiv.apply_symm_apply] using hh
  · intro row hr a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.1 hr
    rw [← designRight_length e₂]
    exact designLabel_lt r i a ha
  · change (designLabels r).length = _
    rw [designLabels_length,designLeft_length e₁]
    exact designCase1_card hcase

/-- The stored first-part name retrieves its actual neighborhood label. -/
theorem designJohnson_row (hleft : r.2.1.Nodup) (x : ↥X.Pt₁) :
    rawJRow (designJohnson r,name₁ x) = designLabel (r,e₁ x) := by
  have hh := rawJ_lookup_zip r.2.1 (designLabels r) (e₁ x) (name₁ x)
    (designLabel (r,e₁ x)) hleft (designLabels_length r).symm
    (by rw [List.getElem?_eq_getElem (e₁ x).isLt,he₁ x])
    (by simp [designLabels,(e₁ x).isLt])
  exact congrArg (fun o => o.getD []) hh

/-- The decoded Johnson colors equal the paper's neighborhood-difference colors. -/
theorem designJohnson_color (hleft : r.2.1.Nodup) (x y : ↥X.Pt₁) :
    rawJDiff (designJohnson r,(name₁ x,name₁ y)) = X.johnsonColor x.val y.val := by
  classical
  have hrow := designJohnson_row h e₁ he₁ e₂ he₂ hleft
  have hnd : (rawJRow (designJohnson r,name₁ x)).Nodup := by
    rw [hrow]; exact (designLabel_sorted r _).nodup
  have hlt : ∀ a ∈ rawJRow (designJohnson r,name₁ x), a < r.2.2.length := by
    rw [hrow]; exact designLabel_lt r _
  rw [rawJDiff_eq_card hnd hlt,hrow,hrow,
    designLabel_set h e₁ he₁ e₂ he₂,designLabel_set h e₁ he₁ e₂ he₂]
  split
  · rw [← Finset.image_sdiff _ _ e₂.injective,Finset.card_image_of_injective _ e₂.injective,
      X.card_label_sdiff]
  · have he (A B : Finset (Fin r.2.2.length)) :
        (Finset.univ \ A) \ (Finset.univ \ B) = B \ A := by
      ext i
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
      tauto
    rw [he,← Finset.image_sdiff _ _ e₂.injective,Finset.card_image_of_injective _ e₂.injective]
    have hc : (X.label y.val).card = (X.label x.val).card := by
      rw [X.card_label,X.card_label,X.nbhd_ncard_eq_d₁ y.property,X.nbhd_ncard_eq_d₁ x.property]
    rw [Finset.card_sdiff_comm hc,X.card_label_sdiff]

end Specification
end Algo
