import Workspace.Algo.AggNodeGuideStructure

/-! Transport the paper's canonical guide to the actual computed vertex
and relation orders. Class numbering is common to both outputs. -/
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

/-- The guide on the actual fixed set, in the computed relation order. -/
noncomputable def aggnGuideClassStruct (b : Bool) :
    RelStructure ↥(fixedGamma ϕ (X b) C.2.2.2.length) where
  numRel := (reps).length
  arity _ := C.2.2.2.length
  rel j := (D).classRel b (aggnGuideRepClass hC hs hset ht htm j)

/-- Compact vertex numbering gives exactly the guide with computed relation labels. -/
theorem aggnGuideNumberedStruct_map (b : Bool) :
    (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).map
      (aggnAggregateGuideEquiv hC hs b) = aggnGuideClassStruct hC hs hset ht htm (tbl := tbl) b := by
  apply (RelStructure.map_eq_iff _ (aggnAggregateGuideEquiv hC hs b) _).mpr
  intro j v
  exact (aggnGuideNumberedStruct_rel hC hs htbl hset ht htm b j v).symm

/-- Computed relation order has exactly the automorphism group of the paper's guide. -/
theorem aggnGuideClassStruct_aut (b : Bool)
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true) :
    (aggnGuideClassStruct hC hs hset ht htm (tbl := tbl) b).Aut = ((D).guideStruct b).Aut := by
  ext σ
  rw [RelStructure.mem_aut_iff,RelStructure.mem_aut_iff]
  constructor
  · intro h j v
    obtain ⟨i,hi⟩ := aggnGuideRepClass_surjective hC hs htbl hset ht htm hcov
      ((Finite.equivFin (D).Class).symm j)
    have hh := h i v
    change (tupleMap σ v ∈ (D).classRel b (aggnGuideRepClass hC hs hset ht htm i) ↔
      v ∈ (D).classRel b (aggnGuideRepClass hC hs hset ht htm i)) at hh
    rw [hi] at hh
    exact hh
  · intro h i v
    have hh := h (Finite.equivFin (D).Class (aggnGuideRepClass hC hs hset ht htm i)) v
    simpa only [LocalGuideData.guideStruct,Equiv.symm_apply_apply] using hh

/-- A category morphism preserves every class in the same computed order. -/
theorem aggnGuideClassStruct_map (b b' : Bool)
    (f : ↥(fixedGamma ϕ (X b) C.2.2.2.length) ≃ ↥(fixedGamma ϕ (X b') C.2.2.2.length))
    (hf : f ∈ (D).morC b b') :
    (aggnGuideClassStruct hC hs hset ht htm (tbl := tbl) b).map f =
      aggnGuideClassStruct hC hs hset ht htm (tbl := tbl) b' := by
  have hp := (RelStructure.map_eq_iff ((D).guideStruct b) f _).mp ((D).guideStruct_map hf)
  apply (RelStructure.map_eq_iff _ f _).mpr
  intro j v
  have hh := hp (Finite.equivFin (D).Class (aggnGuideRepClass hC hs hset ht htm j)) v
  simpa only [LocalGuideData.guideStruct,Equiv.symm_apply_apply] using hh

/-- The actual numbered structures are canonical through their explicit vertex lists. -/
theorem aggnGuideNumberedStruct_map_mor (b b' : Bool)
    (f : ↥(fixedGamma ϕ (X b) C.2.2.2.length) ≃ ↥(fixedGamma ϕ (X b') C.2.2.2.length))
    (hf : f ∈ (D).morC b b') :
    (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).map
      (((aggnAggregateGuideEquiv hC hs b).trans f).trans (aggnAggregateGuideEquiv hC hs b').symm) =
      aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b' := by
  apply RelStructure.map_injective (aggnAggregateGuideEquiv hC hs b')
  dsimp only
  rw [RelStructure.map_map,aggnGuideNumberedStruct_map hC hs htbl hset ht htm b']
  have he : ((aggnAggregateGuideEquiv hC hs b') : _ → _) ∘
      ((((aggnAggregateGuideEquiv hC hs b).trans f).trans
        (aggnAggregateGuideEquiv hC hs b').symm) : _ → _) =
      (f : _ → _) ∘ ((aggnAggregateGuideEquiv hC hs b) : _ → _) := by
    funext a
    exact (aggnAggregateGuideEquiv hC hs b').apply_symm_apply _
  rw [he,← RelStructure.map_map,aggnGuideNumberedStruct_map hC hs htbl hset ht htm b]
  exact aggnGuideClassStruct_map hC hs htbl hset ht htm b b' f hf

end
end Algo
