import Workspace.Algo.AggNodeGuideRepClasses
import Workspace.Algo.AggNodeGuidePositions

/-! # The target coverage test has its paper meaning

Every compact tuple is pulled back through the computed fixed-set list.
The actual coverage test therefore says that each target guide class is
represented by a source tuple. The source representatives are complete
by the comparison-table proof, rather than by a new invariant.
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
local notation "names" => (fun b : Bool => (aggnAggregateData ((C,s),b)).2.2)
local notation "rows" => (fun b : Bool => aggnGuideRows c (C.2.2.2,C.2.1,names b))
local notation "reps" => aggnGuideReps ((C.1,tbl),rows false)
local notation "side" => (fun b : Bool => aggnGuideSideRows c ((C.2.2.2,C.2.1),names b))
local notation "relctx" => (fun b : Bool => ((C.1,tbl),b,side b))
include hC hs htbl hset ht htm

/-- The actual compact-row test is equality with the source guide class. -/
theorem aggnGuideRelTest_key_spec (b : Bool) {u : List ℕ} (hu : u ∈ reps)
    (v : Fin C.2.2.2.length ↪ Fin (names b).length) :
    aggnGuideRelTest ((relctx b,u),aggnTupleName v) = true ↔
      aggnGuideClassKey D name false u =
        {(D).mkClass ⟨b,v.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding⟩} := by
  change aggnGuideTuple ((C.1,tbl),(b,u,rawRestrictStr (names b,aggnTupleName v))) = true ↔ _
  rw [aggnAggregateGuide_tuple_pullback hC hs b]
  apply (aggnGuideTuple_key_spec hC hs htbl hset ht htm b
    (aggnClassReps_mem.mp hu).1
    (aggnAggregateGuideRows_name hC hs b (v.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding))).trans
  rw [aggnGuideClassKey_name D name (b := b) Subtype.val_injective
    (v.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding)]

/-- Exact interpretation of the computed coverage check in compact coordinates. -/
theorem aggnGuideCovered_positions (b : Bool) :
    aggnGuideCovered (relctx b,reps) = true ↔
      ∀ v : Fin C.2.2.2.length ↪ Fin (names b).length,
        ∃ u ∈ reps,aggnGuideClassKey D name false u =
          {(D).mkClass ⟨b,v.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding⟩} := by
  rw [aggnGuideCovered_spec]
  constructor
  · intro h v
    obtain ⟨u,hu,hv⟩ := h _ (aggnGuideSideRows_name hC.guard v)
    exact ⟨u,hu,(aggnGuideRelTest_key_spec hC hs htbl hset ht htm b hu v).mp hv⟩
  · intro h row hr
    obtain ⟨v,rfl⟩ := aggnGuideSideRows_complete hC.guard hr
    obtain ⟨u,hu,hv⟩ := h v
    exact ⟨u,hu,(aggnGuideRelTest_key_spec hC hs htbl hset ht htm b hu v).mpr hv⟩

/-- The list check covers exactly the mathematical classes on the selected side. -/
theorem aggnGuideCovered_classes (b : Bool) :
    aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),b)) = true ↔
      ∀ v : Fin C.2.2.2.length ↪ ↥(fixedGamma ϕ (X b) C.2.2.2.length),
        ∃ u ∈ reps,aggnGuideClassKey D name false u = {(D).mkClass ⟨b,v⟩} := by
  have hat : aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),b) = (relctx b,reps) := by
    cases b <;> rfl
  rw [hat,aggnGuideCovered_positions hC hs htbl hset ht htm b]
  constructor
  · intro h v
    let e := aggnAggregateGuideEquiv hC hs b
    obtain ⟨u,hu,hv⟩ := h (v.trans e.symm.toEmbedding)
    have he : (v.trans e.symm.toEmbedding).trans
        (aggnAggregateGuideEquiv hC hs b).toEmbedding = v :=
      Function.Embedding.ext (fun i => e.apply_symm_apply (v i))
    exact ⟨u,hu,by rwa [he] at hv⟩
  · intro h v
    exact h (v.trans (aggnAggregateGuideEquiv hC hs b).toEmbedding)

/-- Source coverage is always established by the actual representative routine. -/
theorem aggnGuideCovered_source :
    aggnGuideCovered (aggnGuideAt (aggnGuidePrepare c ((C,s),tbl),false)) = true :=
  (aggnGuideCovered_classes hC hs htbl hset ht htm false).mpr
    (aggnGuideReps_tuple_complete hC hs htbl hset ht htm)

end
end Algo
