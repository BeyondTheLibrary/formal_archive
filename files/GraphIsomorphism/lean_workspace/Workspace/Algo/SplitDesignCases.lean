import Workspace.Algo.SplitDesignHypergraph
import Workspace.SplitOrJohnson.BlkTwinClass

/-! # Section 9.7: the first two branch tests

The large-class scan keeps every block in every qualifying twin class.
This preserves the two-class tie handled by the formalized proof.
-/
namespace Algo
open Babai RAM

/-- Case 1 tests all pairs of second-part vertices. -/
def designCase1 (r : RawUpccCase) : Bool :=
  upccCaseAllB splitLabTest (designTwins r,
    (List.range r.2.2.length).product (List.range r.2.2.length))

theorem polyFun_designCase1 : PolyFun designCase1 := by
  have hp : PolyFun (fun r : RawUpccCase => List.range r.2.2.length) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength
  exact (polyFun_designTwins.pair ((hp.pair hp).comp GIReduction.polyFun_product)).comp
    (upccCasePoly_all polyFun_splitLabTest)

/-- The inclusive half-size test of Case 2. -/
def designBigTest (z : RawUpccCase × ℕ) : Bool :=
  decide (z.1.2.2.length ≤ 2 * classSizeRaw (designTwins z.1,z.2))

theorem polyFun_designBigTest : PolyFun designBigTest :=
  ((((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_length).le
    ((polyFun_const 2).mul (((polyFun_fst.comp polyFun_designTwins).pair polyFun_snd).comp
      polyFun_classSizeRaw)))

/-- All positions in large twin classes, including both classes in a tie. -/
def designBigPositions (r : RawUpccCase) : List ℕ :=
  (List.range r.2.2.length).filter (fun i => designBigTest (r,i))

theorem polyFun_designBigPositions : PolyFun designBigPositions :=
  (polyFun_id.pair ((polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength)).comp
    (PolyFun.filterParam polyFun_designBigTest)

def designCase2 (r : RawUpccCase) : Bool := !(designBigPositions r).isEmpty

theorem polyFun_designCase2 : PolyFun designCase2 :=
  polyFun_rawJNot (polyFun_designBigPositions.comp polyFun_isEmpty)

/-- All second-part blocks lie in qualifying classes precisely in the tie branch. -/
def designTie (r : RawUpccCase) : Bool :=
  decide ((designBigPositions r).length = r.2.2.length)

theorem polyFun_designTie : PolyFun designTie :=
  (polyFun_designBigPositions.comp polyFun_length).natEq
    ((polyFun_snd.comp polyFun_snd).comp polyFun_length)

section Specification
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B, r.2.2[(e₂ B).val] = name₂ B)
include h he₁ he₂

theorem designCase1_spec : designCase1 r = true ↔ X.IsCase1 := by
  have hp (i j : ℕ) : (i,j) ∈ (List.range r.2.2.length).product
      (List.range r.2.2.length) ↔ i < r.2.2.length ∧ j < r.2.2.length := by
    simp [List.product]
  simp only [designCase1,upccCaseAllB_spec,Prod.forall,hp,
    splitLabTest,decide_eq_true_eq]
  constructor
  · intro hh B hB C hC
    exact (designTwins_spec h e₁ he₁ e₂ he₂ ⟨B,hB⟩ ⟨C,hC⟩).1
      (hh _ _ ⟨(e₂ ⟨B,hB⟩).isLt,(e₂ ⟨C,hC⟩).isLt⟩)
  · intro hh i j hij
    let B := e₂.symm ⟨i,hij.1⟩
    let C := e₂.symm ⟨j,hij.2⟩
    have ht := (designTwins_spec h e₁ he₁ e₂ he₂ B C).2 (hh _ B.property _ C.property)
    simpa only [B,C,Equiv.apply_symm_apply] using ht

/-- Count the paper's class through the block position bijection. -/
theorem designTwinSize (B : ↥X.blocks) :
    classSizeRaw (designTwins r,e₂ B) = (X.twinClass B.val).ncard := by
  rw [classSizeRaw_spec_of_length (designTwins_length r)]
  have he : labSet r.2.2.length (designTwins r) (e₂ B) =
      e₂ '' {C : ↥X.blocks | C.val ∈ X.twinClass B.val} := by
    ext i
    obtain ⟨C,rfl⟩ := e₂.surjective i
    rw [mem_image_equiv e₂]
    simp only [labSet,Set.mem_setOf_eq,Equiv.symm_apply_apply]
    rw [designTwins_spec h e₁ he₁ e₂ he₂ C B]
    exact ⟨fun hh => ⟨C.property,X.isHTwin_symm hh⟩,fun hh => X.isHTwin_symm hh.2⟩
  rw [he,Set.ncard_image_of_injective _ e₂.injective]
  exact X.ncard_coe_blocks (X.twinClass_subset_blocks _)

theorem designBigTest_spec (B : ↥X.blocks) :
    designBigTest (r,e₂ B) = true ↔ B.val ∈ X.bigTwin := by
  rw [designBigTest,decide_eq_true_eq,designTwinSize h e₁ he₁ e₂ he₂,
    designRight_length e₂]
  exact (and_iff_right B.property).symm

theorem designBigPositions_spec (B : ↥X.blocks) :
    (e₂ B).val ∈ designBigPositions r ↔ B.val ∈ X.bigTwin := by
  simp only [designBigPositions,List.mem_filter,List.mem_range,(e₂ B).isLt,true_and]
  exact designBigTest_spec h e₁ he₁ e₂ he₂ B

omit h he₁ he₂ in
/-- A large class exists exactly when the union of large classes is nonempty. -/
theorem designCase2_math : X.IsCase2 ↔ X.bigTwin.Nonempty := by
  constructor
  · rintro ⟨C,hsub,hsize,hpair,hmax⟩
    have hne : C.Nonempty := by
      by_contra hh
      rw [Set.not_nonempty_iff_eq_empty] at hh
      rw [hh,Set.ncard_empty] at hsize
      have hz : X.blocks.ncard = 0 := by omega
      have hblocks : X.blocks.Nonempty := BlkBlockDesignInputs.blocks_nonempty_of_case X.case
      have := (Set.ncard_pos (Set.toFinite _)).2 hblocks
      omega
    obtain ⟨B,hB⟩ := hne
    have he : X.twinClass B = C := by
      apply Set.Subset.antisymm
      · intro D hD; exact hmax B hB D hD.1 hD.2
      · intro D hD; exact ⟨hsub hD,hpair B hB D hD⟩
    exact ⟨B,hsub hB,by rw [he]; exact hsize⟩
  · rintro ⟨B,hB⟩
    refine ⟨X.twinClass B,X.twinClass_subset_blocks _,hB.2,?_,?_⟩
    · intro C hC D hD
      exact X.isHTwin_trans (X.isHTwin_symm hC.2) hD.2
    · intro C hC D hD ht
      exact ⟨hD,X.isHTwin_trans hC.2 ht⟩

theorem designCase2_spec : designCase2 r = true ↔ X.IsCase2 := by
  rw [designCase2,designCase2_math (X := X)]
  simp only [Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.isEmpty_iff,
    List.eq_nil_iff_forall_not_mem,not_forall,not_not]
  constructor
  · rintro ⟨i,hi⟩
    have hb := (List.mem_range.1 (List.mem_of_mem_filter hi))
    let B := e₂.symm ⟨i,hb⟩
    refine ⟨B.val,(designBigPositions_spec h e₁ he₁ e₂ he₂ B).1 ?_⟩
    simpa only [B,Equiv.apply_symm_apply] using hi
  · rintro ⟨B,hB⟩
    exact ⟨e₂ ⟨B,hB.1⟩,(designBigPositions_spec h e₁ he₁ e₂ he₂ ⟨B,hB.1⟩).2 hB⟩

theorem designTie_spec : designTie r = true ↔ X.bigTwin = X.blocks := by
  rw [designTie,decide_eq_true_eq]
  have hh : (designBigPositions r).length = r.2.2.length ↔
      ∀ B : ↥X.blocks, B.val ∈ X.bigTwin := by
    change ((List.range r.2.2.length).filter (fun i => designBigTest (r,i))).length = _ ↔ _
    conv_lhs => rhs; rw [← (List.length_range (n := r.2.2.length))]
    rw [List.length_filter_eq_length_iff]
    constructor
    · intro ht B
      exact (designBigTest_spec h e₁ he₁ e₂ he₂ B).1
        (ht (e₂ B) (List.mem_range.2 (e₂ B).isLt))
    · intro ht i hi
      let B := e₂.symm ⟨i,List.mem_range.1 hi⟩
      have hb := (designBigTest_spec h e₁ he₁ e₂ he₂ B).2 (ht B)
      simpa only [B,Equiv.apply_symm_apply] using hb
  rw [hh]
  exact ⟨fun ht => Set.Subset.antisymm X.bigTwin_subset_blocks (fun B hB => ht ⟨B,hB⟩),
    fun ht B => ht.symm ▸ B.property⟩

end Specification
end Algo
