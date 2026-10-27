import Workspace.Algo.AggNodeGuideCoverage

/-! The actual source representatives number all classes of the two-object
local guide whenever the computed target coverage check succeeds. -/
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

omit htbl in
/-- The class denoted by a stored representative. This is specification data only. -/
noncomputable def aggnGuideRepClass (i : Fin (reps).length) : (D).Class :=
  (aggnGuideReps_class_exists hC hs hset ht htm (List.getElem_mem i.isLt)).choose

omit htbl in
theorem aggnGuideRepClass_spec (i : Fin (reps).length) :
    aggnGuideClassKey D name false ((reps)[i.val]) = {aggnGuideRepClass hC hs hset ht htm i} :=
  (aggnGuideReps_class_exists hC hs hset ht htm (List.getElem_mem i.isLt)).choose_spec

/-- Different stored indices denote different classes. -/
theorem aggnGuideRepClass_injective :
    Function.Injective (aggnGuideRepClass hC hs hset ht htm (tbl := tbl)) := by
  intro i j hij
  have he := aggnGuideReps_class_unique hC hs htbl hset ht htm
    (List.getElem_mem i.isLt) (List.getElem_mem j.isLt)
    ((aggnGuideRepClass_spec hC hs hset ht htm i).trans
      ((congrArg (fun Q : (D).Class => ({Q} : Set (D).Class)) hij).trans
        (aggnGuideRepClass_spec hC hs hset ht htm j).symm))
  exact Fin.ext ((List.Nodup.getElem_inj_iff (aggnGuideReps_nodup hC)).mp he)

/-- Successful target coverage supplies every class of the two-object guide. -/
theorem aggnGuideRepClass_surjective
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true) :
    Function.Surjective (aggnGuideRepClass hC hs hset ht htm (tbl := tbl)) := by
  intro Q
  refine Quotient.inductionOn Q ?_
  rintro ⟨b,u⟩
  have hr : ∃ row ∈ reps,aggnGuideClassKey D name false row = {(D).mkClass ⟨b,u⟩} := by
    cases b with
    | false => exact aggnGuideReps_tuple_complete hC hs htbl hset ht htm u
    | true => exact (aggnGuideCovered_classes hC hs htbl hset ht htm true).mp hcov u
  obtain ⟨row,hr,hQ⟩ := hr
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
  refine ⟨⟨i,hi⟩,?_⟩
  exact Set.singleton_injective ((aggnGuideRepClass_spec hC hs hset ht htm ⟨i,hi⟩).symm.trans hQ)

/-- Relation labels biject with precisely the paper's quotient classes. -/
noncomputable def aggnGuideClassEquiv
    (hcov : aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),true)) = true) :
    Fin (reps).length ≃ (D).Class :=
  Equiv.ofBijective (aggnGuideRepClass hC hs hset ht htm)
    ⟨aggnGuideRepClass_injective hC hs htbl hset ht htm,
      aggnGuideRepClass_surjective hC hs htbl hset ht htm hcov⟩

end
end Algo
