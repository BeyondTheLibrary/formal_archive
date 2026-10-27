import Workspace.Algo.SplitDesignTrace

/-! # Section 9.7: the two tests inside the dominant class

First test for two distinct equal traces. If none exist, test the boundary
at which complementary traces must be paired (recorded repair 83).
-/
namespace Algo
open Babai RAM

def designDomTwinTest (z : RawDesignLocal × (ℕ × ℕ)) : Bool :=
  decide (z.2.1 ≠ z.2.2) &&
    decide (designLocalRow (z.1.1,z.2.1) = designLocalRow (z.1.1,z.2.2))

def designDomTwins (z : RawDesignLocal) : List (ℕ × ℕ) :=
  ((designDomPositions z).product (designDomPositions z)).filter
    (fun q => designDomTwinTest (z,q))

def designHasDomTwins (z : RawDesignLocal) : Bool := !(designDomTwins z).isEmpty

def designDomBoundaryTest (z : RawDesignLocal × ℕ) : Bool :=
  decide ((designBigPositions z.1.1).length = 2 * designLocalSize (z.1.1,z.2))

def designDomBoundary (z : RawDesignLocal) : Bool :=
  !((designDomPositions z).filter (fun i => designDomBoundaryTest (z,i))).isEmpty

theorem polyFun_designDomTwinTest : PolyFun designDomTwinTest := by
  have hx : PolyFun (fun z : RawDesignLocal × (ℕ × ℕ) => designLocalRow (z.1.1,z.2.1)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_fst)).comp polyFun_designLocalRow
  have hy : PolyFun (fun z : RawDesignLocal × (ℕ × ℕ) => designLocalRow (z.1.1,z.2.2)) :=
    ((polyFun_fst.comp polyFun_fst).pair (polyFun_snd.comp polyFun_snd)).comp polyFun_designLocalRow
  exact polyFun_rawJAnd (polyFun_snd.comp polyFun_upccNatNe)
    ((hx.pair hy).comp polyFun_listNatEq)

theorem polyFun_designDomTwins : PolyFun designDomTwins :=
  (polyFun_id.pair ((polyFun_designDomPositions.pair polyFun_designDomPositions).comp
    GIReduction.polyFun_product)).comp (PolyFun.filterParam polyFun_designDomTwinTest)

theorem polyFun_designHasDomTwins : PolyFun designHasDomTwins :=
  polyFun_rawJNot (polyFun_designDomTwins.comp polyFun_isEmpty)

theorem polyFun_designDomBoundaryTest : PolyFun designDomBoundaryTest :=
  (((polyFun_fst.comp polyFun_fst).comp polyFun_designBigPositions).comp polyFun_length).natEq
    ((polyFun_const 2).mul (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp
      polyFun_designLocalSize))

theorem polyFun_designDomBoundary : PolyFun designDomBoundary :=
  polyFun_rawJNot (((polyFun_id.pair polyFun_designDomPositions).comp
    (PolyFun.filterParam polyFun_designDomBoundaryTest)).comp polyFun_isEmpty)

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designBigPositions_size : (designBigPositions r).length = X.bigTwin.ncard := by
  have hh := splitNamedCount (fun B : ↥X.blocks => (e₂ B).val)
    (fun B C hh => e₂.injective (Fin.ext hh)) (List.range r.2.2.length) List.nodup_range
    (fun i => by
      simp only [List.mem_range]
      exact ⟨fun hi => ⟨e₂.symm ⟨i,hi⟩,congrArg Fin.val (e₂.apply_symm_apply _)⟩,
        fun ⟨B,hB⟩ => hB ▸ (e₂ B).isLt⟩)
    (fun i => designBigTest (r,i))
  change (designBigPositions r).length = _ at hh
  rw [hh]
  have hs : {B : ↥X.blocks | designBigTest (r,e₂ B) = true} =
      {B : ↥X.blocks | B.val ∈ X.bigTwin} := by
    ext B
    exact designBigTest_spec h e₁ he₁ e₂ he₂ B
  rw [hs]
  exact X.ncard_coe_blocks X.bigTwin_subset_blocks

theorem designDomTwins_mem (p : ℕ × ℕ) (hb : 0 < p.2) (x y : ↥X.Pt₁) :
    ((e₁ x).val,(e₁ y).val) ∈ designDomTwins (r,p) ↔
      x.val ∈ X.domClass (sbipAlphaValue p) ∧ y.val ∈ X.domClass (sbipAlphaValue p) ∧
      x ≠ y ∧ X.nbhd x.val ∩ X.bigTwin = X.nbhd y.val ∩ X.bigTwin := by
  simp only [designDomTwins,List.mem_filter,designDomTwinTest,Bool.and_eq_true,
    decide_eq_true_eq]
  rw [show ((e₁ x).val,(e₁ y).val) ∈ (designDomPositions (r,p)).product
      (designDomPositions (r,p)) ↔ (e₁ x).val ∈ designDomPositions (r,p) ∧
        (e₁ y).val ∈ designDomPositions (r,p) by simp [List.product]]
  rw [designDomPositions_spec h e₁ he₁ e₂ he₂ p hb,
    designDomPositions_spec h e₁ he₁ e₂ he₂ p hb,designLocalRow_eq h e₁ he₁ e₂ he₂]
  have he : (e₁ x).val = (e₁ y).val ↔ x = y := by
    exact ⟨fun hh => e₁.injective (Fin.ext hh),fun hh => hh ▸ rfl⟩
  simp only [ne_eq,he]
  tauto

theorem designHasDomTwins_spec (p : ℕ × ℕ) (hb : 0 < p.2) :
    designHasDomTwins (r,p) = true ↔
      ∃ u ∈ X.domClass (sbipAlphaValue p), ∃ v ∈ X.domClass (sbipAlphaValue p),
        u ≠ v ∧ X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin := by
  rw [designHasDomTwins,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  constructor
  · intro hne
    obtain ⟨⟨i,j⟩,hij⟩ := List.exists_mem_of_ne_nil _ hne
    have hm := List.mem_of_mem_filter hij
    have hm' : i ∈ designDomPositions (r,p) ∧ j ∈ designDomPositions (r,p) := by
      simpa [List.product] using hm
    let x := e₁.symm ⟨i,List.mem_range.1 (List.mem_of_mem_filter hm'.1)⟩
    let y := e₁.symm ⟨j,List.mem_range.1 (List.mem_of_mem_filter hm'.2)⟩
    have hh := (designDomTwins_mem h e₁ he₁ e₂ he₂ p hb x y).1 (by
      simpa only [x,y,Equiv.apply_symm_apply] using hij)
    exact ⟨x.val,hh.1,y.val,hh.2.1,fun he => hh.2.2.1 (Subtype.ext he),hh.2.2.2⟩
  · rintro ⟨u,hu,v,hv,huv,ht⟩
    have hh := (designDomTwins_mem h e₁ he₁ e₂ he₂ p hb ⟨u,hu.1⟩ ⟨v,hv.1⟩).2
      ⟨hu,hv,fun hh => huv (congrArg Subtype.val hh),ht⟩
    exact List.ne_nil_of_mem hh

theorem designDomBoundaryTest_spec (p : ℕ × ℕ) (x : ↥X.Pt₁) :
    designDomBoundaryTest ((r,p),e₁ x) = true ↔ X.bigTwin.ncard = 2 * X.localSize x.val := by
  rw [designDomBoundaryTest,decide_eq_true_eq,designBigPositions_size h e₁ he₁ e₂ he₂,
    designLocalSize_spec h e₁ he₁ e₂ he₂]

theorem designDomBoundary_spec (p : ℕ × ℕ) (hb : 0 < p.2) :
    designDomBoundary (r,p) = true ↔ ∃ x ∈ X.domClass (sbipAlphaValue p),
      X.bigTwin.ncard = 2 * X.localSize x := by
  rw [designDomBoundary,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  constructor
  · intro hh
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hh
    obtain ⟨him,hit⟩ := List.mem_filter.1 hi
    let x := e₁.symm ⟨i,List.mem_range.1 (List.mem_of_mem_filter him)⟩
    refine ⟨x.val,(designDomPositions_spec h e₁ he₁ e₂ he₂ p hb x).1 (by
      simpa only [x,Equiv.apply_symm_apply] using him),?_⟩
    exact (designDomBoundaryTest_spec h e₁ he₁ e₂ he₂ p x).1 (by
      simpa only [x,Equiv.apply_symm_apply] using hit)
  · rintro ⟨x,hx,hh⟩
    exact List.ne_nil_of_mem (List.mem_filter.2
      ⟨(designDomPositions_spec h e₁ he₁ e₂ he₂ p hb ⟨x,hx.1⟩).2 hx,
        (designDomBoundaryTest_spec h e₁ he₁ e₂ he₂ p ⟨x,hx.1⟩).2 hh⟩)

/-- A positive computed twin test certifies the returned partition's size and admissibility. -/
theorem designDomPartition_good (p : ℕ × ℕ) (hb : 0 < p.2)
    (hd : X.DomHyp (sbipAlphaValue p)) (ht : designHasDomTwins (r,p) = true)
    (iF : Fintype ↥(Subtype.val '' X.Pt₁)) :
    @ColoredPartition.IsAlphaPartition _ _
      (labPartition X.Pt₁ X.localSize (X.domLab (sbipAlphaValue p))) iF (sbipAlphaValue p) := by
  obtain ⟨u,hu,v,hv,huv,htr⟩ := (designHasDomTwins_spec h e₁ he₁ e₂ he₂ p hb).1 ht
  exact hd.domLabPartition_isAlphaPartition iF hu hv huv htr

end Specification
end Algo
