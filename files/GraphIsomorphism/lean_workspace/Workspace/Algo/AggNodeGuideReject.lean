import Workspace.Algo.AggNodeGuideCoverage

/-! Rejection by the computed guide constructor is sound. The proof uses
the paper's class canonicity, including the actual source representative
routine and both raw checks. -/
set_option quotPrecheck false
namespace Algo
open RAM RAM.Targets Babai Equiv

section
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState} {tbl : RawAggCompareTable}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ tbl)
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
local notation "X" => (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
local notation "D" => localGuideData ϕ C.2.2.2.length X hset ht ((Nat.card_fin m).symm ▸ htm)
local notation "name" => (fun b : Bool => (Subtype.val : ↥(fixedGamma ϕ (X b) C.2.2.2.length) → Fin m))
local notation "names" => (fun b : Bool => (aggnAggregateData ((C,s),b)).2.2)
local notation "rows" => (fun b : Bool => aggnGuideRows c (C.2.2.2,C.2.1,names b))
local notation "reps" => aggnGuideReps ((C.1,tbl),rows false)
local notation "side" => (fun b : Bool => aggnGuideSideRows c ((C.2.2.2,C.2.1),names b))
local notation "relctx" => (fun b : Bool => ((C.1,tbl),b,side b))
include hC hs htbl hset ht htm

/-- A morphism of the paper's category forces every target class to meet the source. -/
theorem aggnGuideCovered_of_mor
    (f : ↥(fixedGamma ϕ (X false) C.2.2.2.length) ≃ ↥(fixedGamma ϕ (X true) C.2.2.2.length))
    (hf : f ∈ (D).morC false true) :
    aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true := by
  apply (aggnGuideCovered_classes hC hs htbl hset ht htm true).mpr
  intro v
  let u := v.trans f.symm.toEmbedding
  obtain ⟨row,hr,hrow⟩ := aggnGuideReps_tuple_complete hC hs htbl hset ht htm u
  have he : u.trans f.toEmbedding = v :=
    Function.Embedding.ext (fun i => f.apply_symm_apply (v i))
  have hc := (D).mkClass_comp hf u
  rw [he] at hc
  exact ⟨row,hr,by simpa only [hc] using hrow⟩

/-- The cardinality and class-coverage checks accept every actual category morphism. -/
theorem aggnGuideBuild_of_mor
    (f : ↥(fixedGamma ϕ (X false) C.2.2.2.length) ≃ ↥(fixedGamma ϕ (X true) C.2.2.2.length))
    (hf : f ∈ (D).morC false true) :
    ∃ out,aggnGuideBuild ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl)) = some out := by
  have he := ((aggnAggregateGuideEquiv hC hs false).trans f).trans
    (aggnAggregateGuideEquiv hC hs true).symm
  have hlen : (names false).length = (names true).length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr he
  have hcover := aggnGuideCovered_of_mor hC hs htbl hset ht htm f hf
  refine ⟨(aggnGuideEnter ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl),false),
    aggnGuideEnter ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl),true)),?_⟩
  apply if_pos
  simp only [Bool.and_eq_true]
  exact ⟨decide_eq_true hlen,hcover⟩

/-- Failure of either actual raw check rules out every morphism in the paper's category. -/
theorem aggnGuideBuild_reject
    (hno : aggnGuideBuild ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl)) = none) :
    (D).morC false true = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨out,hout⟩ := aggnGuideBuild_of_mor hC hs htbl hset ht htm f hf
  rw [hno] at hout
  cases hout

end

/-- The full constructor's rejection excludes a string isomorphism in the input group. -/
theorem aggnAggregateGuide_reject {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] (hno : aggnAggregateGuide c (C,s) = none) :
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  obtain ⟨f,hf,_⟩ := exists_mem_guideMorC ϕ C.2.2.2.length
    (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) false true ⟨σ,hσ.1⟩ hσ.2
  have he := aggnGuideBuild_reject hC hs htbl hset ht htm hno
  change f ∈ (localGuideData ϕ C.2.2.2.length
    (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) hset ht
    ((Nat.card_fin m).symm ▸ htm)).morC false true at hf
  rw [he] at hf
  exact hf

end Algo
