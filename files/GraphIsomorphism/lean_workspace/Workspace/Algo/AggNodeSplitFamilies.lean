import Workspace.Algo.AggNodeSplitEntries

/-! The aggregate continuations materialize every computed split family.
Case 2b concatenates the families of all selected constituents. Case 3
solves both successfully checked relational inputs. The giant-domain
witness is retained when restoring answers for Align. -/
namespace Algo
open Babai RAM RAM.Targets Equiv
set_option synthInstance.maxSize 2048

def aggnCase2bSplitFamily (c b t d : ℕ)
    (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : List RawAlignOutcome :=
  (aggnCase2bEntries z).flatMap (fun a =>
    aggnRestoredEntryFamily c b t d (z.1.1.1.2.1,a))

def aggnGuideSplitPair (c b t d : ℕ)
    (z : (AggnPhaseCtx × AggnAggregateState) × (AggnDesignEntry × AggnDesignEntry)) :
    List RawAlignOutcome × List RawAlignOutcome :=
  (aggnRestoredEntryFamily c b t d (z.1.1.1.2.1,z.2.1),
    aggnRestoredEntryFamily c b t d (z.1.1.1.2.1,z.2.2))

def aggnGuideSplitFamilies (c b t d : ℕ) (z : AggnPhaseCtx × AggnAggregateState) :
    Option (List RawAlignOutcome × List RawAlignOutcome) :=
  (aggnGuideEntries c z).map (fun out => aggnGuideSplitPair c b t d (z,out))

theorem aggnQuasiFun_case2bSplitFamily (c b t d : ℕ) : QuasiFun (aggnCase2bSplitFamily c b t d) := by
  have hdom : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1.1.2.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  exact ((hdom.pair aggnPolyFun_case2bEntries).comp_quasiFun
    (aggnQuasiFun_mapParam (aggnQuasiFun_restoredEntryFamily c b t d))).comp_poly polyFun_flatten

theorem aggnQuasiFun_guideSplitPair (c b t d : ℕ) : QuasiFun (aggnGuideSplitPair c b t d) := by
  have hdom : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × (AggnDesignEntry × AggnDesignEntry) =>
      z.1.1.1.2.1) :=
    (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  exact ((hdom.pair (polyFun_snd.comp polyFun_fst)).comp_quasiFun
    (aggnQuasiFun_restoredEntryFamily c b t d)).pair
      ((hdom.pair (polyFun_snd.comp polyFun_snd)).comp_quasiFun
        (aggnQuasiFun_restoredEntryFamily c b t d))

theorem aggnQuasiFun_guideSplitFamilies (c b t d : ℕ) : QuasiFun (aggnGuideSplitFamilies c b t d) := by
  have hs := (polyFun_swap.comp_quasiFun (aggnQuasiFun_guideSplitPair c b t d)).comp_poly polyFun_some
  exact (((aggnQuasiFun_guideEntries c).pair polyFun_id.quasiFun).comp
    (QuasiFun.optionElim (polyFun_const none).quasiFun hs)).of_eq (fun z => by
      cases he : aggnGuideEntries c z <;> simp [aggnGuideSplitFamilies,he])

def AggnSplitFamilyGood (m : ℕ) (A : List RawAlignOutcome) : Prop :=
  (∃ o,o ∈ A) ∧ ∀ o ∈ A,∃ (β : ℝ) (Z : Pt (SplitOutcomes (Fin m))),
    decAlignOutcome m o = some Z ∧ 1/2 < β ∧ 0 ≤ β ∧ 5*β ≤ 4 ∧ IsSplitOutcome β Set.univ Z

def AggnRestoredEntryGood (c b t d : ℕ) : Prop :=
  ∀ m dom (a : AggnDesignEntry),dom.length = m →
    a.1.Nodup → (∀ u ∈ a.1,u < m) → 11*m ≤ 15*a.1.length →
    ExtendedInputRep (c+1) a.1.length (a.2,(3,4)) →
    AggnSplitFamilyGood m (aggnRestoredEntryFamily c b t d (dom,a))

theorem aggnCase2bSplitFamily_valid {c b t d n m : ℕ}
    (hsolver : AggnRestoredEntryGood c b t d) {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    (hm : 217 ≤ m) (hcase : aggnAggregateDispatch (C,s) = 2)
    (hgiant : aggnAggregateGiantBranch (C,s) = false) :
    AggnSplitFamilyGood m (aggnCase2bSplitFamily c b t d ((C,s),false)) := by
  have hg (a : AggnDesignEntry) (ha : a ∈ aggnCase2bEntries ((C,s),false)) :
      AggnSplitFamilyGood m (aggnRestoredEntryFamily c b t d (C.1.2.1,a)) := by
    obtain ⟨hnd,hlt,hlarge,_⟩ := aggnCase2bEntries_admissible hC hm hcase hgiant ha
    exact hsolver m C.1.2.1 a hC.action.2.1 hnd hlt hlarge
      (aggnCase2bEntries_split_input hC hm hcase hgiant ha)
  constructor
  · obtain ⟨a,ha⟩ := (aggnCase2bEntries_nonempty hC hm hcase hgiant).1
    obtain ⟨o,ho⟩ := (hg a ha).1
    exact ⟨o,List.mem_flatMap.2 ⟨a,ha,ho⟩⟩
  · intro o ho
    obtain ⟨a,ha,ho⟩ := List.mem_flatMap.1 ho
    exact (hg a ha).2 o ho

theorem aggnGuideSplitPair_valid {c b t d n m : ℕ}
    (hsolver : AggnRestoredEntryGood c b t d) {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (hcase : aggnAggregateDispatch (C,s) = 3)
    (side : Bool) :
    let A := aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out))
    AggnSplitFamilyGood m (cond side A.2 A.1) := by
  let a := cond side (aggnGuideEntryPair ((C,s),out)).2 (aggnGuideEntryPair ((C,s),out)).1
  obtain ⟨hnd,hlt,hlarge,_⟩ := aggnGuideEntries_admissible hC hs htbl hset ht htm hout hcase side
  have hh := hsolver m C.1.2.1 a hC.action.2.1 hnd hlt hlarge
    (aggnGuideEntries_split_input hC hs htbl hset ht htm hout hcase side)
  cases side <;> exact hh

theorem aggnGuideSplitFamilies_some {c b t d : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out) :
    aggnGuideSplitFamilies c b t d (C,s) =
      some (aggnGuideSplitPair c b t d ((C,s),aggnGuideEntryPair ((C,s),out))) := by
  simp only [aggnGuideSplitFamilies,aggnGuideEntries,hout,Option.map_some]

/-- The same fixed evaluators serve every aggregate continuation. -/
theorem exists_aggnSplitFamilies (c b : ℕ) :
    ∃ t d,AggnRestoredEntryGood c b t d ∧
      QuasiFun (aggnCase2bSplitFamily c b t d) ∧ QuasiFun (aggnGuideSplitFamilies c b t d) := by
  obtain ⟨t,d,_,hgood⟩ := exists_aggnRestoredEntryFamily_valid c b
  exact ⟨t,d,hgood,aggnQuasiFun_case2bSplitFamily c b t d,aggnQuasiFun_guideSplitFamilies c b t d⟩

end Algo
