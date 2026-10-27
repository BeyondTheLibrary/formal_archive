import Workspace.Algo.AggNodeAggregateReadOff

/-! # The three tests in Section 13.2

Count the fixed points and compute the orbit of each point. These give
exactly the paper's first two conditions. If both fail, the existing
arithmetic lemma proves that the fixed set has more than four fifths of
the giant domain. All tests are polynomial routines on their raw inputs.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- Points whose orbit exceeds four fifths of the supplied domain. -/
def aggnLargeOrbitPoints (p : List ℕ × RawGens) : List ℕ :=
  (List.range p.1.length).filter (fun u => decide (4 * p.1.length < 5 * (rawOrbit (p.2, u)).length))

def aggnCase2 (p : List ℕ × RawGens) : Bool := !(aggnLargeOrbitPoints p).isEmpty

def aggnCase1 (p : List ℕ × RawGens) : Bool :=
  decide (p.1.length ≤ 5 * (p.1.length - (aggFixed p).length)) && (aggnLargeOrbitPoints p).isEmpty

/-- The paper's ordered dispatch, numbered as in Section 13.2. -/
def aggnAggregateCase (p : List ℕ × RawGens) : ℕ :=
  if aggnCase1 p then 1 else if aggnCase2 p then 2 else 3

private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

theorem aggnPolyFun_largeOrbitPoints : PolyFun aggnLargeOrbitPoints := by
  have hm : PolyFun (fun z : (List ℕ × RawGens) × ℕ => z.1.1.length) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_length
  have ho : PolyFun (fun z : (List ℕ × RawGens) × ℕ => (rawOrbit (z.1.2, z.2)).length) :=
    (((polyFun_fst.comp polyFun_snd).pair polyFun_snd).comp polyFun_rawOrbit).comp polyFun_length
  have ht := (((polyFun_const 4).mul hm).pair ((polyFun_const 5).mul ho)).comp plt
  exact ((polyFun_id.pair (polyFun_fst.comp polyFun_rangeLength)).comp
    (PolyFun.filterParam ht)).of_eq (fun _ => rfl)

theorem aggnPolyFun_case2 : PolyFun aggnCase2 :=
  (PolyFun.ite (aggnPolyFun_largeOrbitPoints.comp polyFun_isEmpty)
    (polyFun_const false) (polyFun_const true)).of_eq (fun p => by
      unfold aggnCase2
      cases (aggnLargeOrbitPoints p).isEmpty <;> rfl)

theorem aggnPolyFun_case1 : PolyFun aggnCase1 := by
  have hm : PolyFun (fun p : List ℕ × RawGens => p.1.length) := polyFun_fst.comp polyFun_length
  have hd := aggPolyFun_fixed.comp polyFun_length
  have hmove := (hm.pair hd).comp polyFun_sub
  have ht := (hm.pair ((polyFun_const 5).mul hmove)).comp polyFun_le
  exact wftPolyFun_and ht (aggnPolyFun_largeOrbitPoints.comp polyFun_isEmpty)

theorem aggnPolyFun_aggregateCase : PolyFun aggnAggregateCase :=
  PolyFun.ite aggnPolyFun_case1 (polyFun_const 1)
    (PolyFun.ite aggnPolyFun_case2 (polyFun_const 2) (polyFun_const 3))

theorem aggnOrbit_length {m : ℕ} {gs : RawGens} (hw : RawGens.WF m gs) (u : Fin m) :
    (rawOrbit (gs, u.val)).length = (orbit (decGroup m gs) u : Set (Fin m)).ncard := by
  have h := ncard_winSet (rawOrbit (gs, u.val)) (nodup_rawOrbit gs u.val)
    (fun v hv => ((mem_rawOrbit_iff hw u.isLt v).mp hv).1)
  rw [winSet_rawOrbit hw u] at h
  exact h.symm

theorem aggnFixed_length {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    (aggFixed (dom, gs)).length = (fixedSet (decGroup m gs)).ncard := by
  have hnd : (aggFixed (dom, gs)).Nodup := List.Nodup.filter _ List.nodup_range
  have hlt : ∀ u ∈ aggFixed (dom, gs), u < m := by
    intro u hu
    simpa only [hd] using List.mem_range.mp (List.mem_filter.mp hu).1
  rw [← ncard_winSet _ hnd hlt, aggFixed_spec hd hw]

theorem aggnLargeOrbitPoints_mem {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) (u : Fin m) :
    u.val ∈ aggnLargeOrbitPoints (dom, gs) ↔
      4 * m < 5 * (orbit (decGroup m gs) u : Set (Fin m)).ncard := by
  simp only [aggnLargeOrbitPoints, List.mem_filter, List.mem_range, hd, decide_eq_true_eq,
    aggnOrbit_length hw u, and_iff_right u.isLt]

theorem aggnCase2_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnCase2 (dom, gs) = true ↔ Case2 (decGroup m gs) := by
  rw [aggnCase2, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ h
    have hum : u < m := by simpa only [hd] using List.mem_range.mp (List.mem_filter.mp hu).1
    exact ⟨⟨u, hum⟩, by simpa only [Fintype.card_fin] using
      (aggnLargeOrbitPoints_mem hd hw ⟨u, hum⟩).mp hu⟩
  · rintro ⟨u, hu⟩ hn
    have hm := (aggnLargeOrbitPoints_mem hd hw u).mpr (by simpa using hu)
    simp [hn] at hm

theorem aggnCase1_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    aggnCase1 (dom, gs) = true ↔ Case1 (decGroup m gs) := by
  have hs := ncard_movedSet_add_ncard_fixedSet (decGroup m gs)
  simp only [Fintype.card_fin] at hs
  have he : m - (aggFixed (dom, gs)).length = (movedSet (decGroup m gs)).ncard := by
    rw [aggnFixed_length hd hw]
    omega
  have hnot : (aggnLargeOrbitPoints (dom, gs)).isEmpty = true ↔ ¬ Case2 (decGroup m gs) := by
    rw [← aggnCase2_spec hd hw, aggnCase2]
    cases (aggnLargeOrbitPoints (dom, gs)).isEmpty <;> simp
  simp only [aggnCase1, Bool.and_eq_true, decide_eq_true_eq, hd, he, hnot, Case1, Case2,
    Fintype.card_fin, not_exists, Nat.not_lt]

theorem aggnAggregateCase_spec {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs) :
    (aggnAggregateCase (dom, gs) = 1 ↔ Case1 (decGroup m gs)) ∧
    (aggnAggregateCase (dom, gs) = 2 ↔ Case2 (decGroup m gs)) ∧
    (aggnAggregateCase (dom, gs) = 3 ↔
      ¬ Case1 (decGroup m gs) ∧ ¬ Case2 (decGroup m gs)) := by
  have h12 : Case1 (decGroup m gs) → ¬ Case2 (decGroup m gs) := by
    rintro ⟨_, h⟩ ⟨u, hu⟩
    exact Nat.not_lt_of_ge (h u) hu
  unfold aggnAggregateCase
  split
  next h1 =>
    have hc := (aggnCase1_spec hd hw).mp h1
    simp [hc, h12 hc]
  next h1 =>
    have hc : ¬ Case1 (decGroup m gs) := fun h => h1 ((aggnCase1_spec hd hw).mpr h)
    split
    next h2 => simp [hc, (aggnCase2_spec hd hw).mp h2]
    next h2 =>
      have hc2 : ¬ Case2 (decGroup m gs) := fun h => h2 ((aggnCase2_spec hd hw).mpr h)
      simp [hc, hc2]

theorem aggnAggregateCase_three_fixed {m : ℕ} {dom : List ℕ} {gs : RawGens}
    (hd : dom.length = m) (hw : RawGens.WF m gs)
    (h : aggnAggregateCase (dom, gs) = 3) :
    4 * m < 5 * (aggFixed (dom, gs)).length := by
  obtain ⟨h1, h2⟩ := (aggnAggregateCase_spec hd hw).2.2.mp h
  simpa only [Fintype.card_fin, aggnFixed_length hd hw] using four_mul_lt_five_mul_fixed (decGroup m gs) h1 h2

/-- Read the dispatch from the source store retained by the combined phase. -/
def aggnAggregateDispatch (z : AggnPhaseCtx × AggnAggregateState) : ℕ :=
  aggnAggregateCase (z.1.1.2.1, (aggnAggregateData (z, false)).2.1)

theorem aggnPolyFun_aggregateDispatch : PolyFun aggnAggregateDispatch := by
  have hdom : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z.1.1.2.1) :=
    ((polyFun_fst.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hgs := ((((polyFun_id.pair (polyFun_const false)).comp aggnPolyFun_aggregateData).comp
    polyFun_snd).comp polyFun_fst)
  exact (hdom.pair hgs).comp aggnPolyFun_aggregateCase

theorem aggnAggregateDispatch_spec {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) :
    (aggnAggregateDispatch (C, s) = 1 ↔ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length)) ∧
    (aggnAggregateDispatch (C, s) = 2 ↔ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length)) ∧
    (aggnAggregateDispatch (C, s) = 3 ↔
      ¬ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length)) := by
  have hw : RawGens.WF m (aggnAggregateData ((C, s), false)).2.1 :=
    wf_tidyGens hC.action.2.1 _
  have h := aggnAggregateCase_spec hC.action.2.1 hw
  rw [(aggnAggregateData_spec hC hs false).2.1] at h
  exact h

end Algo
