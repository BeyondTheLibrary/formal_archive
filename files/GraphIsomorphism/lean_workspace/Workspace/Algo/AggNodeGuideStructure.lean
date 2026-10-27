import Workspace.Algo.AggNodeGuideClassEquiv

/-! The computed Case 3 relations are exactly the paper's guide classes.
Both vertex numbering and relation numbering are explicit. -/
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

/-- Each actual relation row has precisely the paper's class membership,
under the explicit compact-vertex bijection and computed source index. -/
theorem aggnGuideIndexedRel_spec (b : Bool) (j : Fin (reps).length)
    (v : Fin C.2.2.2.length → Fin (names b).length) :
    aggnTupleName v ∈ (aggnGuideRelations (relctx b,reps)).getD j.val [] ↔
      (fun i => aggnAggregateGuideEquiv hC hs b (v i)) ∈
        (D).classRel b (aggnGuideRepClass hC hs hset ht htm j) := by
  have hlen : j.val < (aggnGuideRelations (relctx b,reps)).length := by
    simpa only [aggnGuideRelations_length] using j.isLt
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [aggnGuideRelations,List.getElem_map]
  change aggnTupleName v ∈ aggnGuideRel (relctx b,(reps)[j.val]) ↔ _
  classical
  by_cases hi : Function.Injective v
  · let u : Fin C.2.2.2.length ↪ Fin (names b).length := ⟨v,hi⟩
    have hm := aggnGuideSideRows_name hC.guard u
    have htst := aggnGuideRelTest_key_spec hC hs htbl hset ht htm b (List.getElem_mem j.isLt) u
    rw [aggnGuideRepClass_spec hC hs hset ht htm j,Set.singleton_eq_singleton_iff] at htst
    change _ ↔ (u.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding :
      Fin C.2.2.2.length → ↥(fixedGamma ϕ (X b) C.2.2.2.length)) ∈ _
    rw [LocalGuideData.mem_classRel]
    exact (aggnGuideRel_mem.trans (and_iff_right hm)).trans (htst.trans eq_comm)
  · constructor
    · intro hmem
      have hn := ((aggnGuideRows_mem hC.guard).mp (aggnGuideRel_mem.mp hmem).1).2.2
      have hin : Function.Injective v := by
        intro i k hik
        exact (List.nodup_ofFn.mp hn) (congrArg Fin.val hik)
      exact (hi hin).elim
    · rintro ⟨u,he,_⟩
      apply (hi ?_).elim
      intro i k hik
      exact u.injective ((congrFun he i).trans ((congrArg (aggnAggregateGuideEquiv hC hs b) hik).trans
        (congrFun he k).symm))

/-- A decoder with the actual computed number of relations and arity. -/
def aggnGuideNumberedStruct (b : Bool) : RelStructure (Fin (names b).length) where
  numRel := (reps).length
  arity _ := C.2.2.2.length
  rel j := {v | aggnTupleName v ∈ (aggnGuideRelations (relctx b,reps)).getD j.val []}

/-- The returned numbered relations are the guide classes with their computed labels. -/
theorem aggnGuideNumberedStruct_rel (b : Bool) (j : Fin (reps).length)
    (v : Fin C.2.2.2.length → Fin (names b).length) :
    v ∈ (aggnGuideNumberedStruct (C := C) (s := s) (tbl := tbl) b).rel j ↔
      (fun i => aggnAggregateGuideEquiv hC hs b (v i)) ∈
        (D).classRel b (aggnGuideRepClass hC hs hset ht htm j) :=
  aggnGuideIndexedRel_spec hC hs htbl hset ht htm b j v

end
end Algo
