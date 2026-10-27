import Workspace.Algo.AggNodeCase2bTransport

/-! # The continuation of Theorem 13.2.1 is canonical, and its lists are bounded

This file collects, for the whole continuation `aggnContinuation`, what Procedure Align
(Sec. 14.1) asks of the versions it receives:

* **canonicity** (`aggnContinuation_transport`): at every exit that lists versions (tags
  `1`, `3`, `4`), each `σ ∈ Iso_G(x,y)` carries every listed version of `x` along `ϕ(σ)` to a
  listed version of `y`. Outcome (1) is `aggnCaseOneOutcome_canonical`; outcomes (2b) and (3)
  are `aggnContinuation_three_transport` and `aggnContinuation_four_transport`, under the
  RAM canonicity of Theorem 9.2.3 (`AggnEntryFamilyCanonical`);
* **the length of the lists**: one version at outcome (1); at outcome (2b) at most `m^5`
  members times the number of versions of Theorem 9.2.3 per member (the multiplicative cost
  `m^{d−1}(m−1) ≤ m^5` of Sec. 13.2, item 2b, weakened as in `Babai.case2b_cost_le`); at
  outcome (3) the number of versions of Theorem 9.2.3 of each structure.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

section Spec
variable {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
include hC hs

/-- At tag `1` the version of `y` is the version of `x` moved by `ϕ(σ)`. -/
theorem aggnContinuation_one_transport {b t d : ℕ} (h1 : (aggnContinuation c b t d (C,s)).1 = 1)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ (aggnContinuation c b t d (C,s)).2.1) :
    ∃ o' ∈ (aggnContinuation c b t d (C,s)).2.2, RawSplitOutcomeIso m (ϕ σ) o o' := by
  have hd := (aggnContinuation_tag c b t d (C,s)).1.mp h1
  rw [aggnContinuation_of_one hd] at ho ⊢
  simp only [aggnContCaseOne,List.mem_singleton] at ho ⊢
  subst ho
  refine ⟨_,rfl,?_⟩
  obtain ⟨inst,hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  have hc := aggnCaseOneOutcome_canonical hK hC hs σ hσ
  rw [aggnCaseOneOutcome_decode hC hs false] at hc
  simp only [Option.map_some] at hc
  exact ⟨_,_,aggnCaseOneOutcome_decode hC hs false,hc,SplitOutcomeIso.of_eq_smul hK rfl⟩

/-- §13.2 and §15, lines 6a–7a: **the versions the continuation lists are canonical.** At
every exit that lists versions, every `σ ∈ Iso_G(x,y)` carries each listed version of `x`
along `ϕ(σ)` to a listed version of `y`. The hypotheses of outcome (3) are those of the
local-guide construction (`aggnAggregateGuide_canonical`). -/
theorem aggnContinuation_transport {b t d : ℕ} (hcan : AggnEntryFamilyCanonical c b t d)
    (hm : 217 ≤ m)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)]
    (htag : (aggnContinuation c b t d (C,s)).1 ∈ ({1,3,4} : Finset ℕ))
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1)
    {o : RawAlignOutcome} (ho : o ∈ (aggnContinuation c b t d (C,s)).2.1) :
    ∃ o' ∈ (aggnContinuation c b t d (C,s)).2.2, RawSplitOutcomeIso m (ϕ σ) o o' := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at htag
  rcases htag with h | h | h
  · exact aggnContinuation_one_transport hC hs h σ hσ ho
  · exact aggnContinuation_three_transport hC hs hcan hm h σ hσ ho
  · exact aggnContinuation_four_transport hC hs htbl hset ht htm hcan h σ hσ ho

omit hC hs in
/-- At tag `1` each list has exactly one version. -/
theorem aggnContinuation_one_length {b t d : ℕ} (h1 : (aggnContinuation c b t d (C,s)).1 = 1) :
    (aggnContinuation c b t d (C,s)).2.1.length = 1 ∧
      (aggnContinuation c b t d (C,s)).2.2.length = 1 := by
  rw [aggnContinuation_of_one ((aggnContinuation_tag c b t d (C,s)).1.mp h1)]
  exact ⟨rfl,rfl⟩

end Spec

/-- The number of versions at outcome (2b): at most `m^5` members, each with at most `L`
versions of Theorem 9.2.3. -/
theorem aggnCase2bSplitFamily_length_le {c b t d n m L : ℕ} {C : AggnPhaseCtx}
    {s : AggnAggregateState} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hm : 217 ≤ m) {side : Bool}
    (hb : aggnSideCase2b ((C,s),side) = true)
    (hL : ∀ a ∈ aggnCase2bEntries ((C,s),side), (aggnEntrySplitFamily c b t d a).length ≤ L) :
    (aggnCase2bSplitFamily c b t d ((C,s),side)).length ≤ m^5 * L := by
  unfold aggnCase2bSplitFamily
  rw [List.length_flatMap]
  have hsum : ((aggnCase2bEntries ((C,s),side)).map (fun a =>
      (aggnRestoredEntryFamily c b t d (C.1.2.1,a)).length)).sum ≤
      (aggnCase2bEntries ((C,s),side)).length * L := by
    have h := List.sum_le_card_nsmul
      ((aggnCase2bEntries ((C,s),side)).map (fun a =>
        (aggnRestoredEntryFamily c b t d (C.1.2.1,a)).length)) L (by
        intro x hx
        obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hx
        simpa [aggnRestoredEntryFamily,aggnRestoreFamily] using hL a ha)
    simpa using h
  exact hsum.trans (Nat.mul_le_mul_right _ (aggnCase2bEntries_side_nonempty hC hm hb).2)

/-- The number of versions at outcome (3): each structure contributes its versions of
Theorem 9.2.3, one restored answer per computed answer. -/
theorem aggnGuideSplitPair_length (c b t d : ℕ)
    (p : (AggnPhaseCtx × AggnAggregateState) × (AggnDesignEntry × AggnDesignEntry)) :
    (aggnGuideSplitPair c b t d p).1.length = (aggnEntrySplitFamily c b t d p.2.1).length ∧
      (aggnGuideSplitPair c b t d p).2.length = (aggnEntrySplitFamily c b t d p.2.2).length := by
  simp [aggnGuideSplitPair,aggnRestoredEntryFamily,aggnRestoreFamily]

end Algo
