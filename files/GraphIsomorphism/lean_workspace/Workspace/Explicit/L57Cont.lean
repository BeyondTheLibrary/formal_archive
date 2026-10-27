/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the continuation of
Procedure AggregateCertificates (Theorem 13.2.1, Sec. 13.2) at lines 5–7 of the Master
(Sec. 15), bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.L57Compare

/-!
# The continuation of lines 5–7, bounded at the degree

After the two phases, the round of lines 5–7 reads the dispatch of Theorem 13.2.1 off the
stores (`Algo.aggnContinuation`). Its quasipolynomial work is

* the guarded tuple table on the context and on the fixed set `D` (the guide of case 3), and
* the Extended Design Lemma (Theorem 9.2.3, `Algo.extendedSplitFamily`) on the design entries
  of cases 2b and 3.

The entries are inputs of the machine of Theorem 9.2.3 (`Explicit.TN.ExtPre`) by their shape
alone: their domain is `0, …, k-1` with `k` at most the size of `Γ`, the guard witness is the
string of the context, and the arity is `2` (case 2b) or the list of the context (case 3).
The guard holds once the string has at least two letters and the list of the context is within
the guard (`Explicit.ContCtxOK`).
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-- The context of the continuation at degree `n`: the context of the phases, a string of at
least two letters, and the list of the context within the guard of the entries. -/
def ContCtxOK (c n : ℕ) (C : AggnPhaseCtx) : Prop :=
  CtxOK n C ∧ 2 ≤ C.2.1.length ∧ C.2.2.2.length ≤ guardBound (c + 1) C.2.1.length

/-! ## Shapes of the entries -/

theorem length_aggFixed_le (p : List ℕ × RawGens) : (aggFixed p).length ≤ p.1.length :=
  (List.length_filter_le _ _).trans (List.length_range ▸ le_rfl)

theorem case2bFamily_length_le {p : List ℕ × RawGens} {q : AggnRawConstituent}
    (hq : q ∈ aggnCase2bFamily p) : q.1.length ≤ p.1.length := by
  unfold aggnCase2bFamily at hq
  obtain ⟨S, -, hS⟩ := List.mem_flatMap.1 hq
  unfold aggnCase2bAt at hS
  obtain ⟨R, -, rfl⟩ := List.mem_map.1 hS
  exact (List.length_filter_le _ _).trans ((List.length_filter_le _ _).trans
    (List.length_range ▸ le_rfl))

theorem size_three_four' : Enc.size ((3, 4) : ℕ × ℕ) ≤ 64 := size_three_four

/-- An entry on the domain `0, …, k-1`, with the guard witness `x` and an arity within the guard,
at threshold `3/4`, is an input of the machine of Theorem 9.2.3 at every degree bounding `k`,
`|x|` and `64`. -/
theorem extPre_of_shape {c N k : ℕ} {ks x : List ℕ} {R : RawRelStruct}
    (hg : ks.length ≤ guardBound c x.length) (hk : k ≤ N) (hx : x.length ≤ N) (h64 : 64 ≤ N) :
    TN.ExtPre c N (((ks, x, List.range k), R), (3, 4)) := by
  refine ⟨⟨k, hk, ⟨List.nodup_range, fun i => ?_, hg, by change 0 < 4; norm_num, ?_⟩⟩,
    size_three_four'.trans h64, hx⟩
  · change i ∈ List.range k ↔ i < k
    exact List.mem_range
  · change (3 : ℝ) / 4 ≤ ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)
    norm_num

theorem extPre_case2bEntry {c n : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState} {b : Bool}
    (hC : ContCtxOK c n C) {a : AggnDesignEntry} (ha : a ∈ aggnCase2bEntries ((C, s), b)) :
    TN.ExtPre (c + 1) (n + 64) (a.2, (3, 4)) := by
  obtain ⟨q, hq, rfl⟩ := aggnCase2bEntries_mem.1 ha
  -- the family must be given: unifying it unfolds `Algo.aggnCase2bFamily` first
  have hl : q.1.length ≤ (aggnAggregateImage ((C, s), b)).1.length :=
    case2bFamily_length_le (p := aggnAggregateImage ((C, s), b)) hq
  change q.1.length ≤ C.1.2.1.length at hl
  have hg : ([0, 1] : List ℕ).length ≤ guardBound (c + 1) C.2.1.length := aggnGuard_two hC.2.1
  have h1 : q.1.length ≤ n + 64 := by have := hC.1.2.2; omega
  have h2 : C.2.1.length ≤ n + 64 := by have := hC.1.1; omega
  exact extPre_of_shape (c := c + 1) (N := n + 64) (R := [aggnConstituentRel q]) hg h1 h2
    (by omega)

theorem aggregateData_fixed_length (z : (AggnPhaseCtx × AggnAggregateState) × Bool) :
    (aggnAggregateData z).2.2.length ≤ z.1.1.1.2.1.length :=
  length_aggFixed_le (z.1.1.1.2.1, aggFGamma (z.1.1.1, aggnStoreAt z.1.2.1.2.1 z.2))

/-- The two relational structures of the guide of case 3 are inputs of Theorem 9.2.3: their
domain is `0, …, |D| - 1`, with `D` a fixed set of `Γ`, and their arity is the list of the
context. -/
theorem extPre_guideOut {c n : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    (hC : ContCtxOK c n C) {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C, s) = some out) :
    TN.ExtPre (c + 1) (n + 64) (out.1, (3, 4)) ∧ TN.ExtPre (c + 1) (n + 64) (out.2, (3, 4)) := by
  unfold aggnAggregateGuide at hout
  obtain ⟨-, -, rfl⟩ := aggnGuideBuild_some hout
  have hx := aggregateData_fixed_length ((C, s), false)
  have hy := aggregateData_fixed_length ((C, s), true)
  change _ ≤ C.1.2.1.length at hx hy
  have h2 : C.2.1.length ≤ n + 64 := by have := hC.1.1; omega
  constructor
  · exact extPre_of_shape (c := c + 1) (N := n + 64) hC.2.2
      (hx.trans (by have := hC.1.2.2; omega)) h2 (by omega)
  · exact extPre_of_shape (c := c + 1) (N := n + 64) hC.2.2
      (hy.trans (by have := hC.1.2.2; omega)) h2 (by omega)

/-! ## The Extended Design Lemma on one entry -/

namespace TN

variable {c b t d : ℕ}

theorem aggnEntrySplitFamily (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnEntrySplitFamily c b t d) (fun n a => ExtPre (c + 1) n (a.2, (3, 4))) 5 := by
  have h := poly_comp ((polyFun_snd : PolyFun (fun a : AggnDesignEntry => a.2)).pair
    (polyFun_const ((3, 4) : ℕ × ℕ)))
    (extendedSplitFamily (c + 1) b t d 5 (by omega) (by omega) ht)
  exact h.of_eq (fun _ => rfl)

theorem aggnRestoredEntryFamily (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnRestoredEntryFamily c b t d)
      (fun n p => ExtPre (c + 1) n (p.2.2, (3, 4))) 5 :=
  (((ofPoly (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)) _ _).pair
    (poly_comp polyFun_snd (aggnEntrySplitFamily hc hb ht))).comp_poly
      aggnPolyFun_restoreFamily).of_eq (fun _ => rfl)

/-- The same at degree `n + 64`, bounded at degree `n`. -/
theorem aggnRestoredEntryFamily64 (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnRestoredEntryFamily c b t d)
      (fun n p => ExtPre (c + 1) (n + 64) (p.2.2, (3, 4))) 5 :=
  (aggnRestoredEntryFamily hc hb ht).scale 6 1 (fun n p hp => ⟨n + 64, by
    have : n + 64 ≤ 2 ^ 6 * (n + 1) := by norm_num; omega
    simpa using this, hp⟩)

/-! ## Case 2b -/

theorem aggnContCase2b (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnContCase2b c b t d) (fun n z => ContCtxOK c n z.1) 5 := by
  have hfam : TN (Algo.aggnCase2bSplitFamily c b t d)
      (fun n (z : (AggnPhaseCtx × AggnAggregateState) × Bool) => ContCtxOK c n z.1.1) 5 := by
    have hdom : PolyFun (fun z : (AggnPhaseCtx × AggnAggregateState) × Bool => z.1.1.1.2.1) :=
      (((polyFun_fst.comp polyFun_fst).comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
    have h := (poly_comp (hdom.pair aggnPolyFun_case2bEntries)
      (flatMapParam (aggnRestoredEntryFamily64 (d := d) hc hb ht))).restrict
      (Pre' := fun n (z : (AggnPhaseCtx × AggnAggregateState) × Bool) => ContCtxOK c n z.1.1)
      (fun n z hz a ha => by
        obtain ⟨⟨C, s⟩, b⟩ := z
        exact extPre_case2bEntry hz ha)
    exact h.of_eq (fun _ => rfl)
  have hx : TN (fun z : AggnPhaseCtx × AggnAggregateState =>
      aggnCase2bSplitFamily c b t d (z, false)) (fun n z => ContCtxOK c n z.1) 5 :=
    poly_comp ((polyFun_id : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z)).pair
      (polyFun_const false)) hfam
  have hy : TN (fun z : AggnPhaseCtx × AggnAggregateState =>
      aggnCase2bSplitFamily c b t d (z, true)) (fun n z => ContCtxOK c n z.1) 5 :=
    poly_comp ((polyFun_id : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z)).pair
      (polyFun_const true)) hfam
  exact ((const' 3 _ _).pair (hx.pair hy)).of_eq (fun _ => rfl)

/-! ## Case 3: the guide -/

theorem aggnCompareTable (c : ℕ) :
    TN (Algo.aggnCompareTable c) (fun n z => CtxOK n z.1) (c + 1) :=
  ((poly_comp polyFun_fst (aggnCompareJobs c)).pair
    (ofPoly (polyFun_snd.comp polyFun_reverse) _ _)).comp_poly polyFun_zip

theorem aggnGuideRows (c : ℕ) : TN (Algo.aggnGuideRows c) (AggTablePre c) (c + 1) :=
  ((aggTable c).comp_poly (polyFun_snd.comp (PolyFun.map polyFun_fst))).comp_poly
    (PolyFun.filter wftPolyFun_nodup)

theorem aggnGuideSideRows (c : ℕ) :
    TN (Algo.aggnGuideSideRows c)
      (fun n (p : (List ℕ × List ℕ) × List ℕ) => p.1.2.length ≤ n ∧ p.2.length ≤ n) (c + 1) := by
  have h := poly_comp (((polyFun_fst.comp polyFun_fst).pair ((polyFun_fst.comp polyFun_snd).pair
    (polyFun_snd.comp polyFun_rangeLength))) :
      PolyFun (fun p : (List ℕ × List ℕ) × List ℕ => (p.1.1, p.1.2, List.range p.2.length)))
    (aggnGuideRows c)
  exact ((ofPoly polyFun_snd _ _).pair (h.restrict (fun n p hp =>
    ⟨hp.1, fun _ => by simpa only [List.length_range] using hp.2⟩))).of_eq (fun _ => rfl)

theorem aggnGuidePrepare (c : ℕ) :
    TN (Algo.aggnGuidePrepare c) (fun n p => CtxOK n p.1.1) (c + 1) := by
  let X := AggnGuidePrepareInput
  have hi : PolyFun (fun p : X => p) := polyFun_id
  have hC := pfst (pfst hi)
  have hks := psnd (psnd (psnd hC))
  have hx := pfst (psnd hC)
  have hctx := (pfst hC).pair (psnd hi)
  have hDx := psnd (psnd (((pfst hi).pair (polyFun_const false)).comp aggnPolyFun_aggregateData))
  have hDy := psnd (psnd (((pfst hi).pair (polyFun_const true)).comp aggnPolyFun_aggregateData))
  have hlx : ∀ p : X, (aggnAggregateData (p.1, false)).2.2.length ≤ p.1.1.1.2.1.length :=
    fun p => aggregateData_fixed_length (p.1, false)
  have hly : ∀ p : X, (aggnAggregateData (p.1, true)).2.2.length ≤ p.1.1.1.2.1.length :=
    fun p => aggregateData_fixed_length (p.1, true)
  have hrows := (poly_comp (hks.pair (hx.pair hDx)) (aggnGuideRows c)).restrict
    (Pre' := fun n (p : X) => CtxOK n p.1.1)
    (fun n p hp => ⟨hp.1, fun _ => (hlx p).trans hp.2.2⟩)
  have hsx := (poly_comp ((hks.pair hx).pair hDx) (aggnGuideSideRows c)).restrict
    (Pre' := fun n (p : X) => CtxOK n p.1.1) (fun n p hp => ⟨hp.1, (hlx p).trans hp.2.2⟩)
  have hsy := (poly_comp ((hks.pair hx).pair hDy) (aggnGuideSideRows c)).restrict
    (Pre' := fun n (p : X) => CtxOK n p.1.1) (fun n p hp => ⟨hp.1, (hly p).trans hp.2.2⟩)
  exact ((ofPoly hctx _ _).pair (((ofPoly hctx _ _).pair hrows).comp_poly aggnPolyFun_guideReps
    |>.pair (hsx.pair hsy))).of_eq (fun _ => rfl)

theorem aggnAggregateGuide (c : ℕ) :
    TN (Algo.aggnAggregateGuide c) (fun n z => CtxOK n z.1) (c + 1) := by
  let Z := AggnPhaseCtx × AggnAggregateState
  have hi : PolyFun (fun p : Z => p) := polyFun_id
  have htable := poly_comp ((pfst hi).pair (pfst (psnd (psnd (psnd (psnd hi))))))
    (aggnCompareTable c)
  have hp := ((ofPoly hi (fun n (z : Z) => CtxOK n z.1) (c + 1)).pair htable).comp
    (aggnGuidePrepare c) (fun _ _ h => h)
  exact ((ofPoly ((psnd (psnd (psnd (pfst hi)))).pair (pfst (psnd (pfst hi)))) _ _).pair
    hp).comp_poly aggnPolyFun_guideBuild |>.of_eq (fun _ => rfl)

variable {c b t d : ℕ}

theorem aggnGuideSplitFamilies (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnGuideSplitFamilies c b t d) (fun n z => ContCtxOK c n z.1) 5 := by
  let Z := AggnPhaseCtx × AggnAggregateState
  have hG : TN (fun z : Z => (Algo.aggnAggregateGuide c z, z)) (fun n z => ContCtxOK c n z.1) 5 :=
    (((aggnAggregateGuide c).mono_k (by omega)).restrict (fun _ _ h => h.1)).pair (id' _ _)
  have hR := aggnRestoredEntryFamily64 (d := d) hc hb ht
  have hsome : TN (fun q : (AmbientPIn × AmbientPIn) × Z =>
      some (aggnGuideSplitPair c b t d (q.2, aggnGuideEntryPair (q.2, q.1))))
      (fun n q => ContCtxOK c n q.2.1 ∧ Algo.aggnAggregateGuide c q.2 = some q.1) 5 := by
    have hdom : PolyFun (fun q : (AmbientPIn × AmbientPIn) × Z => q.2.1.1.2.1) :=
      pfst (psnd (pfst (pfst polyFun_snd)))
    have hDx : PolyFun (fun q : (AmbientPIn × AmbientPIn) × Z =>
        (aggnAggregateData (q.2, false)).2.2) :=
      psnd (psnd ((polyFun_snd.pair (polyFun_const false)).comp aggnPolyFun_aggregateData))
    have hDy : PolyFun (fun q : (AmbientPIn × AmbientPIn) × Z =>
        (aggnAggregateData (q.2, true)).2.2) :=
      psnd (psnd ((polyFun_snd.pair (polyFun_const true)).comp aggnPolyFun_aggregateData))
    have h1 := (poly_comp (hdom.pair (hDx.pair (pfst polyFun_fst))) hR).restrict
      (Pre' := fun n (q : (AmbientPIn × AmbientPIn) × Z) =>
        ContCtxOK c n q.2.1 ∧ Algo.aggnAggregateGuide c q.2 = some q.1)
      (fun n q hq => (extPre_guideOut hq.1 hq.2).1)
    have h2 := (poly_comp (hdom.pair (hDy.pair (psnd polyFun_fst))) hR).restrict
      (Pre' := fun n (q : (AmbientPIn × AmbientPIn) × Z) =>
        ContCtxOK c n q.2.1 ∧ Algo.aggnAggregateGuide c q.2 = some q.1)
      (fun n q hq => (extPre_guideOut hq.1 hq.2).2)
    exact ((h1.pair h2).comp_poly polyFun_some).of_eq (fun _ => rfl)
  have hm := hG.comp (optionElim (Pre := fun n (q : Option (AmbientPIn × AmbientPIn) × Z) =>
      ContCtxOK c n q.2.1 ∧ q.1 = Algo.aggnAggregateGuide c q.2)
    (const' none (fun _ _ => True) _) hsome (fun _ _ _ => trivial)
    (fun n x z h => ⟨h.1, h.2.symm⟩)) (fun _ _ h => ⟨h, rfl⟩)
  exact hm.of_eq (fun z => by
    simp only [Algo.aggnGuideSplitFamilies, Algo.aggnGuideEntries]
    cases Algo.aggnAggregateGuide c z <;> rfl)

theorem aggnContCase3 (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnContCase3 c b t d) (fun n z => ContCtxOK c n z.1) 5 := by
  let Z := AggnPhaseCtx × AggnAggregateState
  have hm := ((aggnGuideSplitFamilies (d := d) hc hb ht).pair (id' _ _)).comp
    (optionElim (Pre := fun n (q : Option (List RawAlignOutcome × List RawAlignOutcome) × Z) =>
      True) (const' ((6, [], []) : AggnContOut) (fun _ _ => True) _)
      (ofPoly ((polyFun_const 4).pair (polyFun_fst))
        (fun _ (_ : (List RawAlignOutcome × List RawAlignOutcome) × Z) => True) _)
      (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)) (fun _ _ _ => trivial)
  exact hm.of_eq (fun z => by
    unfold Algo.aggnContCase3
    cases Algo.aggnGuideSplitFamilies c b t d z <;> rfl)

/-! ## The dispatch -/

private theorem polyFun_dispatchIs (k : ℕ) :
    PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => decide (aggnAggregateDispatch z = k)) :=
  (aggnPolyFun_aggregateDispatch.pair (polyFun_const k)).comp polyFun_natEq

/-- **Theorem 13.2.1 on the RAM** (`Algo.aggnContinuation`), bounded at the degree. -/
theorem aggnContinuation (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnContinuation c b t d) (fun n z => ContCtxOK c n z.1) 5 := by
  have h2b := aggnContCase2b (d := d) hc hb ht
  have h3 := aggnContCase3 (d := d) hc hb ht
  have hk (k : ℕ) : TN (fun _ : AggnPhaseCtx × AggnAggregateState => ((k, [], []) : AggnContOut))
      (fun n z => ContCtxOK c n z.1) 5 := const' _ _ _
  have hrej := TN.ite aggnPolyFun_rejectCase (hk 0) h2b (fun _ _ h _ => h) (fun _ _ h _ => h)
  have hgi := TN.ite aggnPolyFun_aggregateGiantBranch (hk 2) hrej (fun _ _ h _ => h)
    (fun _ _ h _ => h)
  have hdef := TN.ite aggnPolyFun_rejectDefect (hk 5) h3 (fun _ _ h _ => h) (fun _ _ h _ => h)
  have h2 := TN.ite (polyFun_dispatchIs 2) hgi hdef (fun _ _ h _ => h) (fun _ _ h _ => h)
  have h1 := TN.ite (polyFun_dispatchIs 1) (ofPoly aggnPolyFun_contCaseOne _ _) h2
    (fun _ _ _ _ => trivial) (fun _ _ h _ => h)
  exact h1.of_eq (fun _ => rfl)

end TN

end Explicit
