import Workspace.Algo.AggNodeAggregateMatch

/-! # Reading the aggregate group from the completed carrier

The preliminary phases retain separate stores for both strings. Each store
now supplies the group `F`, its action on the giant domain, and the fixed
points used by the three cases of Section 13.2.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The original-domain group, its giant image, and that image's fixed points. -/
abbrev AggnAggregateData := RawGens × RawGens × List ℕ

def aggnAggregateData (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : AggnAggregateData :=
  let store := aggnStoreAt z.1.2.1.2.1 z.2
  (rawF (z.1.1.1.1.1, store), aggFGamma (z.1.1.1, store), aggFixedGamma (z.1.1.1, store))

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_aggregateData : PolyFun aggnAggregateData := by
  have hz : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z) := polyFun_id
  have hC := pfst (pfst hz)
  have hs := psnd (pfst hz)
  have hstores := pfst (psnd (pfst hs))
  have hstore := PolyFun.ite (psnd hz) (psnd hstores) (pfst hstores)
  have hA := pfst hC
  have hF := (((pfst (pfst hA)).pair hstore).comp aggPolyFun_F)
  have hFG := (hA.pair hstore).comp aggPolyFun_FGamma
  have hD := (hA.pair hstore).comp aggPolyFun_fixedGamma
  exact (hF.pair (hFG.pair hD)).of_eq (fun z => by
    unfold aggnAggregateData aggnStoreAt
    cases z.2 <;> rfl)

/-- The action boundary accepts every well-formed raw encoding. -/
theorem aggnFGamma_spec {n m t : ℕ} {A : RawAction}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)} {x : Fin n → ℕ} {store : RawAggStore}
    (hA : RawAction.WF n m A ϕ) (hs : AggStoreFor ϕ x t store)
    (hall : AggComplete m t store) :
    decGroup m (aggFGamma (A, store)) = bigFGamma ϕ x t := by
  have h := aggFGamma_spec hA.1 hA.2.1 hA.2.2.2.2 hs hall
  simpa only [map_encPerm_decPerm hA.2.2.1, map_encPerm_decPerm hA.2.2.2.1] using h

theorem aggnFixedGamma_spec {n m t : ℕ} {A : RawAction}
    {ϕ : decGroup n A.1.2 →* Perm (Fin m)} {x : Fin n → ℕ} {store : RawAggStore}
    (hA : RawAction.WF n m A ϕ) (hs : AggStoreFor ϕ x t store)
    (hall : AggComplete m t store) :
    winSet m (aggFixedGamma (A, store)) = fixedGamma ϕ x t := by
  have h := aggFixedGamma_spec hA.1 hA.2.1 hA.2.2.2.2 hs hall
  simpa only [map_encPerm_decPerm hA.2.2.1, map_encPerm_decPerm hA.2.2.2.1] using h

/-- Both stores yield the exact groups and fixed sets of the paper. -/
theorem aggnAggregateData_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    decGroup n (aggnAggregateData ((C, s), b)).1 =
        bigF ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
    decGroup m (aggnAggregateData ((C, s), b)).2.1 =
        bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
    winSet m (aggnAggregateData ((C, s), b)).2.2 =
        fixedGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length := by
  obtain ⟨hstore, hcomplete, _⟩ := hs b
  exact ⟨aggF_spec hC.action.1 hstore hcomplete,
    aggnFGamma_spec hC.action hstore hcomplete,
    aggnFixedGamma_spec hC.action hstore hcomplete⟩

end Algo
