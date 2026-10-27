import Workspace.Algo.AggNodeGuideClassKey

/-! # The computed representatives are exactly the source guide classes

The comparison table decides equality of the paper's classes. We use that
fact for the actual guarded tuple enumeration and first-representative
routine. No extra class test or choice of a default class is assumed.
-/
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
local notation "rows" => (fun b : Bool =>
  aggnGuideRows c (C.2.2.2,C.2.1,(aggnAggregateData ((C,s),b)).2.2))
local notation "reps" => aggnGuideReps ((C.1,tbl),rows false)
include hC hs htbl

/-- Exact class equality on every pair of actual enumerated rows. -/
theorem aggnGuideTuple_key_spec (b : Bool) {u v : List ℕ}
    (hu : u ∈ rows false) (hv : v ∈ rows b) :
    aggnGuideTuple ((C.1,tbl),(b,u,v)) = true ↔
      aggnGuideClassKey D name false u = aggnGuideClassKey D name b v := by
  obtain ⟨u,rfl⟩ := aggnAggregateGuideRows_complete hC hs false hu
  obtain ⟨v,rfl⟩ := aggnAggregateGuideRows_complete hC hs b hv
  apply (aggnGuideTuple_class_spec hC htbl hset ht htm b u v).trans
  rw [aggnGuideClassKey_name D name (b := false) Subtype.val_injective u,
    aggnGuideClassKey_name D name (b := b) Subtype.val_injective v]
  simp only [Set.singleton_eq_singleton_iff]

/-- Every source tuple meets one of the actual stored representatives. -/
theorem aggnGuideReps_class_complete {row : List ℕ} (hr : row ∈ rows false) :
    ∃ u ∈ reps,aggnGuideClassKey D name false u = aggnGuideClassKey D name false row :=
  aggnClassReps_complete (f := aggnGuideClassKey D name false) (fun _ ha _ hb => aggnGuideTuple_key_spec hC hs htbl hset ht htm false ha hb) hr

/-- No two stored representatives denote the same source class. -/
theorem aggnGuideReps_class_unique {u v : List ℕ} (hu : u ∈ reps) (hv : v ∈ reps)
    (he : aggnGuideClassKey D name false u = aggnGuideClassKey D name false v) : u = v :=
  aggnClassReps_unique (f := aggnGuideClassKey D name false) (fun _ ha _ hb => aggnGuideTuple_key_spec hC hs htbl hset ht htm false ha hb) hu hv he

/-- Each source class represented by a mathematical tuple has a stored representative. -/
theorem aggnGuideReps_tuple_complete
    (u : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ (X false) C.2.2.2.length)) :
    ∃ row ∈ reps,aggnGuideClassKey D name false row = {(D).mkClass ⟨false,u⟩} := by
  obtain ⟨row,hr,he⟩ := aggnGuideReps_class_complete hC hs htbl hset ht htm
    (aggnAggregateGuideRows_name hC hs false u)
  refine ⟨row,hr,he.trans ?_⟩
  exact aggnGuideClassKey_name D name (b := false) Subtype.val_injective u

omit htbl in
/-- Every stored representative has a legitimate source tuple, so its key is a singleton. -/
theorem aggnGuideReps_class_exists {row : List ℕ} (hr : row ∈ reps) :
    ∃ Q : (D).Class,aggnGuideClassKey D name false row = {Q} := by
  obtain ⟨u,rfl⟩ := aggnAggregateGuideRows_complete hC hs false (aggnClassReps_mem.mp hr).1
  exact ⟨(D).mkClass ⟨false,u⟩,aggnGuideClassKey_name D name (b := false) Subtype.val_injective u⟩

omit hs htbl in
/-- Distinct rows remain distinct in the computed representative list. -/
theorem aggnGuideReps_nodup : (reps).Nodup :=
  aggnClassReps_nodup (aggnGuideRows_nodup hC.guard (aggnAggregateGuide_names hC false).1)

end
end Algo
