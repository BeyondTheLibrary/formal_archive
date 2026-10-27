import Workspace.Algo.AggNodeConstituentAdmission
import Workspace.Algo.AggNodeCaseOneOutcome

/-! Aggregate continuations retain the original-name dictionary beside each
numbered relational input. Case 2b enumerates all chosen constituents; Case 3
retains the exact successful pair. Recursive answers can therefore use one
shared polynomial restoration routine before Procedure Align.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev AggnDesignEntry := List ℕ × AmbientPIn

def aggnConstituentEntry (p : List ℕ × AggnRawConstituent) : AggnDesignEntry :=
  (p.2.1,aggnConstituentEnter p)

def aggnCase2bEntries (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : List AggnDesignEntry :=
  (aggnAggregateCase2b z).map fun q => aggnConstituentEntry (z.1.1.2.1,q)

def aggnGuideEntryPair (p : (AggnPhaseCtx × AggnAggregateState) × (AmbientPIn × AmbientPIn)) :
    AggnDesignEntry × AggnDesignEntry :=
  (((aggnAggregateData (p.1,false)).2.2,p.2.1),((aggnAggregateData (p.1,true)).2.2,p.2.2))

def aggnGuideEntries (c : ℕ) (z : AggnPhaseCtx × AggnAggregateState) :
    Option (AggnDesignEntry × AggnDesignEntry) :=
  (aggnAggregateGuide c z).map fun out => aggnGuideEntryPair (z,out)

theorem aggnPolyFun_constituentEntry : PolyFun aggnConstituentEntry :=
  (polyFun_snd.comp polyFun_fst).pair aggnPolyFun_constituentEnter

theorem aggnPolyFun_case2bEntries : PolyFun aggnCase2bEntries := by
  have hC : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1) :=
    polyFun_fst.comp polyFun_fst
  exact (((hC.comp polyFun_snd).comp polyFun_fst).pair aggnPolyFun_aggregateCase2b).comp
    (PolyFun.mapParam aggnPolyFun_constituentEntry)

theorem aggnPolyFun_guideEntryPair : PolyFun aggnGuideEntryPair := by
  have hx : PolyFun (fun p : (AggnPhaseCtx × AggnAggregateState) × (AmbientPIn × AmbientPIn) =>
      aggnAggregateData (p.1,false)) := ((polyFun_fst.pair (polyFun_const false)).comp aggnPolyFun_aggregateData)
  have hy : PolyFun (fun p : (AggnPhaseCtx × AggnAggregateState) × (AmbientPIn × AmbientPIn) =>
      aggnAggregateData (p.1,true)) := ((polyFun_fst.pair (polyFun_const true)).comp aggnPolyFun_aggregateData)
  exact (((hx.comp polyFun_snd).comp polyFun_snd).pair
    (polyFun_snd.comp polyFun_fst)).pair
    (((hy.comp polyFun_snd).comp polyFun_snd).pair (polyFun_snd.comp polyFun_snd))

theorem aggnQuasiFun_guideEntries (c : ℕ) : QuasiFun (aggnGuideEntries c) := by
  have hb : PolyFun (fun p : (AmbientPIn × AmbientPIn) × (AggnPhaseCtx × AggnAggregateState) =>
      some (aggnGuideEntryPair (p.2,p.1))) :=
    (polyFun_swap.comp aggnPolyFun_guideEntryPair).comp polyFun_some
  exact (((aggnQuasiFun_aggregateGuide c).pair polyFun_id.quasiFun).comp_poly
    (PolyFun.optionElim (polyFun_const none) hb)).of_eq (fun z => by
      cases h : aggnAggregateGuide c z <;> simp [aggnGuideEntries,h])

theorem aggnCase2bEntries_mem {C : AggnPhaseCtx} {s : AggnAggregateState} {b : Bool}
    {a : AggnDesignEntry} : a ∈ aggnCase2bEntries ((C,s),b) ↔
      ∃ q ∈ aggnAggregateCase2b ((C,s),b),a = (q.1,aggnConstituentEnter (C.2.1,q)) := by
  simp only [aggnCase2bEntries,List.mem_map,aggnConstituentEntry]
  constructor <;> rintro ⟨q,hq,he⟩ <;> exact ⟨q,hq,he.symm⟩

/-- The entry carries the local degree and original degree separately, and
all the source branch's actual entries satisfy the recursive admission bound. -/
theorem aggnCase2bEntries_admissible {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false)
    {a : AggnDesignEntry} (ha : a ∈ aggnCase2bEntries ((C,s),false)) :
    a.1.Nodup ∧ (∀ u ∈ a.1,u < m) ∧ 11*m ≤ 15*a.1.length ∧
      a.2.1 = ([0,1],C.2.1,List.range a.1.length) ∧
      4*2 ≤ a.1.length ∧ (1/4 : ℝ) < (defect (decRel a.1.length 2 a.2.2).Aut : ℝ) := by
  obtain ⟨q,hq,rfl⟩ := aggnCase2bEntries_mem.mp ha
  obtain ⟨hnd,hlt,hlarge,_,hsize,hdef⟩ := aggnAggregateConstituent_admissible hC hm hcase hgiant hq
  exact ⟨hnd,hlt,hlarge,rfl,hsize,hdef⟩

theorem aggnCase2bEntries_nonempty {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false) :
    (∃ a,a ∈ aggnCase2bEntries ((C,s),false)) ∧ (aggnCase2bEntries ((C,s),false)).length ≤ m^5 := by
  obtain ⟨⟨q,hq⟩,_,hlen⟩ := aggnAggregateCase2b_source_facts hC hm hcase hgiant
  exact ⟨⟨_,aggnCase2bEntries_mem.mpr ⟨q,hq,rfl⟩⟩,by simpa [aggnCase2bEntries] using hlen⟩

/-- Case 3's checked output is retained without recomputation or changed labels. -/
theorem aggnGuideEntries_some {c : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out) :
    aggnGuideEntries c (C,s) = some
      (((aggnAggregateData ((C,s),false)).2.2,out.1),((aggnAggregateData ((C,s),true)).2.2,out.2)) := by
  simp only [aggnGuideEntries,hout,Option.map_some,aggnGuideEntryPair]

/-- Both successful guide entries derive their own recursive admission facts. -/
theorem aggnGuideEntries_admissible {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (hcase : aggnAggregateDispatch (C,s) = 3)
    (b : Bool) :
    let a := cond b (aggnGuideEntryPair ((C,s),out)).2 (aggnGuideEntryPair ((C,s),out)).1
    a.1.Nodup ∧ (∀ u ∈ a.1,u < m) ∧ 11*m ≤ 15*a.1.length ∧
      a.2.1 = (C.2.2.2,C.2.1,List.range a.1.length) ∧
      2 ≤ C.2.2.2.length ∧ 4*C.2.2.2.length ≤ a.1.length ∧
      (1/2 : ℚ) < defect (decRel a.1.length C.2.2.2.length a.2.2).Aut := by
  have hn := aggnAggregateGuide_names (s := s) hC b
  have hl := aggnAggregateGuide_large hC hout hcase b
  have hf := (aggnAggregateGuide_rows hC.guard hout b).1
  have ha := aggnAggregateGuide_admissible hC hs htbl hset ht htm hout hcase b
  have hsmall : 11*m ≤ 15*(aggnAggregateData ((C,s),b)).2.2.length := by omega
  cases b <;> exact ⟨hn.1,hn.2,hsmall,hf,ha⟩

end Algo
