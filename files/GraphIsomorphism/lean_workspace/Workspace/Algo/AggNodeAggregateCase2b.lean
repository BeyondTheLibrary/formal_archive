import Workspace.Algo.AggNodeCase2bFacts

/-! # Case 2b directly from the completed aggregate stores -/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

def aggnAggregateImage (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : List ℕ × RawGens :=
  (z.1.1.1.2.1,(aggnAggregateData z).2.1)

def aggnAggregateCase2b (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : List AggnRawConstituent :=
  aggnCase2bFamily (aggnAggregateImage z)

theorem aggnPolyFun_aggregateImage : PolyFun aggnAggregateImage := by
  have hd : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1.1.2.1) :=
    ((((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst)
  exact hd.pair ((aggnPolyFun_aggregateData.comp polyFun_snd).comp polyFun_fst)

theorem aggnPolyFun_aggregateCase2b : PolyFun aggnAggregateCase2b :=
  aggnPolyFun_aggregateImage.comp aggnPolyFun_case2bFamily

theorem aggnAggregate_case2b_tests {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hcase : aggnAggregateDispatch (C,s) = 2) (hgiant : aggnAggregateGiantBranch (C,s) = false) :
    aggnCase2 (aggnAggregateImage ((C,s),false)) = true ∧
      aggnCase2a (aggnAggregateImage ((C,s),false)) = false := by
  have hw : RawGens.WF m (aggnAggregateData ((C,s),false)).2.1 := wf_tidyGens hC.action.2.1 _
  have h2 := (aggnCase2_spec hC.action.2.1 hw).mpr
    ((aggnAggregateCase_spec hC.action.2.1 hw).2.1.mp hcase)
  refine ⟨h2,?_⟩
  change (aggnCase2 _ && aggnCase2a _) = false at hgiant
  rw [h2,Bool.true_and] at hgiant
  exact hgiant

/-- The constructor reads precisely the paper's family for either completed store. -/
theorem aggnAggregateCase2b_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool)
    (hm : 217 ≤ m)
    (h2 : aggnCase2 (aggnAggregateImage ((C,s),b)) = true)
    (hg : aggnCase2a (aggnAggregateImage ((C,s),b)) = false) :
    {q | ∃ r ∈ aggnAggregateCase2b ((C,s),b),aggnDecodeConstituent m r = q} =
      case2bFamily (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length) := by
  have hw : RawGens.WF m (aggnAggregateData ((C,s),b)).2.1 := wf_tidyGens hC.action.2.1 _
  have h6 : 6 ≤ (aggnLargeOrbitPoints (aggnAggregateImage ((C,s),b))).length := by
    obtain ⟨_,_,h⟩ := aggnLargeOrbitPoints_orbit hC.action.2.1 hw h2
    change 6 ≤ (aggnLargeOrbitPoints (C.1.2.1,(aggnAggregateData ((C,s),b)).2.1)).length
    omega
  rw [← (aggnAggregateData_spec hC hs b).2.1]
  exact aggnCase2bFamily_spec hC.action.2.1 hw h2 hg h6

/-- The actual source branch has nonempty admissible outputs and at most `m^5` choices. -/
theorem aggnAggregateCase2b_source_facts {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false) :
    (∃ r,r ∈ aggnAggregateCase2b ((C,s),false)) ∧
      (∀ r ∈ aggnAggregateCase2b ((C,s),false),Case2bOk (3/4 : ℝ) (aggnDecodeConstituent m r) ∧
        11*m ≤ 15*(winSet m r.1).ncard) ∧
      (aggnAggregateCase2b ((C,s),false)).length ≤ m^5 := by
  obtain ⟨h2,hg⟩ := aggnAggregate_case2b_tests hC hcase hgiant
  exact aggnCase2bFamily_facts hC.action.2.1 (wf_tidyGens hC.action.2.1 _) hm h2 hg

end Algo
