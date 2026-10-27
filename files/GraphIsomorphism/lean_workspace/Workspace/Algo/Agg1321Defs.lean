/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the steps of Procedure AggregateCertificates (§13.2) outside the
two phases, with the tuple tables supplied as inputs.
-/
import Workspace.Algo.Agg1321Iter
import Workspace.Algo.AggregatePhasesRAM
import Workspace.Algo.AggNodeContinuation
import Workspace.Algo.AggNodeAggregateCase2b

/-!
# The steps of Theorem 13.2.1 around the two phases

The Master chain computes the test sets of §13.2 and the tuple domains of the local guide
(the proof of Theorem 13.2.1, case (3)) with tables that are cut off when
`t > (log₂ n + 1)^c`, the Master's restriction on `t`. For Theorem 13.2.1 as a standalone
routine, `t` is arbitrary. The only step whose cost depends on `t` beyond a polynomial is the
enumeration of `t`-tuples (`Algo.tuplesOf`). So this file restates each step of the chain
with the tuple tables passed in as inputs; `Workspace/Algo/Agg1321Iter.lean` enumerates the
tables for every `t`, and every other step is polynomial time (`PolyFun`).

The steps, in the order of the proof of Theorem 13.2.1:

* `a13Rows`: the test sets `T ⊆ Γ`, `|T| = t`, as the increasing `t`-tuples of `Γ`;
* `a13Prepare`: the inputs of the `2·C(m,t)` runs of LocalCertificates (the jobs and the
  initial states `G_T`) and of the `2·C(m,t)²` runs of CompareLocalCertificates (the jobs,
  the states and the transporter cosets of line 01);
* `a13Collect`: the two stores of certificates, the table of comparison answers, and the
  fixed-point sets `D(x)`, `D(y)` read off from `F(x)^Γ`, `F(y)^Γ`;
* `a13Final`: the case analysis (1), (2a), (2b), (3) with its outputs (`a13Report`).

Each restated step equals the chain's step whenever the chain's guard holds, and the guard
holds for `c = t` (`Algo.aggnPhaseRows_eq_a13Rows`, `Algo.a13GuidePrepare_eq`); so the
chain's correctness lemmas apply at `c = t`.
-/

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000

namespace Algo
open RAM RAM.Targets Babai
open Equiv (Perm)

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem a13PolyFun_product {α β : Type*} [Enc α] [Enc β] :
    PolyFun (fun p : List α × List β => p.1.product p.2) := by
  have h : PolyFun (fun p : List β × α => p.1.map (fun b => (p.2, b))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam (polyFun_fst.pair polyFun_snd))
  exact ((polyFun_snd.pair polyFun_fst).comp h.flatMapParam).of_eq (fun _ => rfl)

/-! ### The test sets and the inputs of the two phases -/

/-- §13.2: the test sets `T ⊆ Γ` with `|T| = t`, given all `t`-tuples of `[m]`: the tuples
that are increasing lists (`Algo.aggNormalizeRow`). -/
def a13Rows (p : AggnPhaseCtx × List (List ℕ)) : List (List ℕ) :=
  p.2.filter (fun row => decide (row = aggNormalizeRow (p.1.1.2.1, row)))

/-- §13.2: one run of LocalCertificates for each string `x`, `y` and each test set. -/
def a13Jobs (rows : List (List ℕ)) : List AggnJob :=
  [false, true].flatMap fun b => rows.map (fun row => (b, row))

/-- §13.2: one run of CompareLocalCertificates for each `x' ∈ {x, y}` and each pair of test
sets. -/
def a13CJobs (rows : List (List ℕ)) : List AggnCompareJob :=
  [false, true].flatMap fun b => rows.flatMap fun row => rows.map fun row' => (b, row, row')

/-- The context kept across the two phases: the input and the two lists of jobs. -/
abbrev A13Ctx := AggnPhaseCtx × List AggnJob × List AggnCompareJob

/-- §13.2, before the two phases: the jobs and the prepared inputs of all runs. -/
def a13Prepare (p : AggnPhaseCtx × List (List ℕ)) :
    A13Ctx × (List RawLCLoop × List RawPCLoop) :=
  ((p.1, a13Jobs (a13Rows p), a13CJobs (a13Rows p)),
    ((a13Jobs (a13Rows p)).map (aggnJobLoop p.1),
      (a13CJobs (a13Rows p)).map (aggnCompareCtx p.1)))

/-! ### After the two phases -/

/-- The store entries written by the certificate runs, in the order of the runs. -/
def a13Writes (p : AggnPhaseCtx × List AggnJob × List RawLCOut) : List AggnWrite :=
  (p.2.1.zip p.2.2).map (fun w => (w.1, aggPack ((aggnJobLoop p.1 w.1).1.1, w.1.2, w.2)))

/-- The two stores of certificates, one for `x` and one for `y`. -/
def a13Stores (ws : List AggnWrite) : AggnStores :=
  (((ws.filter (fun w => !w.1.1)).map Prod.snd).reverse,
    ((ws.filter (fun w => w.1.1)).map Prod.snd).reverse)

theorem a13Stores_eq (ws : List AggnWrite) : a13Stores ws = aggnApplyEntries ws ([], []) := by
  have hf := aggnApplyEntries_at ws ([], []) false
  have ht := aggnApplyEntries_at ws ([], []) true
  simp only [aggnStoreAt, cond_false, cond_true, List.append_nil, aggnWritesAt] at hf ht
  refine Prod.ext ?_ ?_
  · rw [hf, a13Stores]
    show List.reverse _ = _
    congr 2
    apply List.filter_congr
    intro w _
    cases w.1.1 <;> rfl
  · rw [ht, a13Stores]
    show List.reverse _ = _
    congr 2
    apply List.filter_congr
    intro w _
    cases w.1.1 <;> rfl

/-- The state after the two phases, as the chain's correctness lemmas read it: the two stores
and the list of comparison answers (latest first). -/
def a13State (p : AggnStores × List RawCoset) : AggnAggregateState :=
  (([], p.1, 0, default), 0, ([], p.2, 0, default))

/-- The context of the case analysis and the inputs of the three tuple tables of case (3). -/
abbrev A13Mid := ((AggnPhaseCtx × AggnAggregateState) × RawAggCompareTable) ×
  ((List ℕ × ℕ) × ((List ℕ × ℕ) × (List ℕ × ℕ)))

/-- §13.2, after the two phases: the stores, the comparison table, and the inputs of the
tuple tables on `D(x)`, on `[|D(x)|]` and on `[|D(y)|]`. -/
def a13Collect (p : A13Ctx × (List RawLCOut × List RawCoset)) : A13Mid :=
  let C := p.1.1
  let s := a13State (a13Stores (a13Writes (C, p.1.2.1, p.2.1)), p.2.2.reverse)
  let Dx := (aggnAggregateData ((C, s), false)).2.2
  let Dy := (aggnAggregateData ((C, s), true)).2.2
  (((C, s), p.1.2.2.zip p.2.2),
    ((Dx, C.2.2.2.length), ((List.range Dx.length, C.2.2.2.length),
      (List.range Dy.length, C.2.2.2.length))))

/-! ### The case analysis -/

/-- The three tuple tables of case (3). -/
abbrev A13Tabs := List (List ℕ) × List (List ℕ) × List (List ℕ)

/-- `Algo.aggnGuidePrepare` with the tuple tables supplied. -/
def a13GuidePrepare (p : AggnGuidePrepareInput × A13Tabs) : AggnGuidePrepared :=
  let Dx := (aggnAggregateData (p.1.1, false)).2.2
  let Dy := (aggnAggregateData (p.1.1, true)).2.2
  let ctx := (p.1.1.1.1, p.1.2)
  let rows := p.2.1.filter wftNodup
  (ctx, aggnGuideReps (ctx, rows), (Dx, p.2.2.1.filter wftNodup),
    (Dy, p.2.2.2.filter wftNodup))

/-- §13.2, case (3): the local guide, `Algo.aggnAggregateGuide` with the tables supplied. -/
def a13Guide (p : AggnGuidePrepareInput × A13Tabs) : Option (AmbientPIn × AmbientPIn) :=
  aggnGuideBuild ((p.1.1.1.2.2.2, p.1.1.1.2.1), a13GuidePrepare p)

/-- The exit taken, in the order of the paper's tests (the same codes as
`Algo.aggnContinuation`): `1` case (1); `2` case (2a); `0` reject in case (2); `3` case (2b);
`5` reject in case (3) because `|D(x)| ≠ |D(y)|`; `4` case (3) with the local guide; `6`
reject in case (3) by the local guide. -/
def a13Tag (p : (AggnPhaseCtx × AggnAggregateState) × Option (AmbientPIn × AmbientPIn)) : ℕ :=
  if decide (aggnAggregateDispatch p.1 = 1) then 1
  else if decide (aggnAggregateDispatch p.1 = 2) then
    if aggnAggregateGiantBranch p.1 then 2
    else if aggnRejectCase p.1 then 0
    else 3
  else if aggnRejectDefect p.1 then 5
  else if p.2.isSome then 4
  else 6

/-- The output of Theorem 13.2.1 for the pair `(x, y)`: the exit taken; `F(z)`, `F(z)^Γ` and
`D(z)` for `z = x, y`; the orbit partitions of case (1); the large orbits of case (2); the
families of case (2b); the pair of `t`-ary structures of case (3). -/
abbrev A13Out := ℕ × (AggnAggregateData × AggnAggregateData) × (RawColPart × RawColPart) ×
  (List ℕ × List ℕ) × (List AggnRawConstituent × List AggnRawConstituent) ×
  Option (AmbientPIn × AmbientPIn)

/-- The output, from the state after the two phases and the result of the local guide. -/
def a13Report (p : (AggnPhaseCtx × AggnAggregateState) × Option (AmbientPIn × AmbientPIn)) :
    A13Out :=
  (a13Tag p, (aggnAggregateData (p.1, false), aggnAggregateData (p.1, true)),
    (aggnAggregatePartition (p.1, false), aggnAggregatePartition (p.1, true)),
    (aggnAggregateMajority (p.1, false), aggnAggregateMajority (p.1, true)),
    (aggnAggregateCase2b (p.1, false), aggnAggregateCase2b (p.1, true)), p.2)

/-- §13.2: the case analysis, from the state, the comparison table and the tuple tables. -/
def a13Final (p : AggnGuidePrepareInput × A13Tabs) : A13Out :=
  a13Report (p.1.1, a13Guide p)

/-! ### Polynomial time -/

theorem polyFun_a13Rows : PolyFun a13Rows := by
  have hf : PolyFun (fun z : List ℕ × List ℕ => decide (z.2 = aggNormalizeRow z)) :=
    (polyFun_snd.pair aggPolyFun_normalizeRow).comp polyFun_listNatEq
  have hΓ : PolyFun (fun p : AggnPhaseCtx × List (List ℕ) => p.1.1.2.1) :=
    pfst (psnd (pfst polyFun_fst))
  exact ((hΓ.pair polyFun_snd).comp (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

theorem polyFun_a13Jobs : PolyFun a13Jobs := by
  have hf := PolyFun.map (α := List ℕ) ((polyFun_const false).pair polyFun_id)
  have ht := PolyFun.map (α := List ℕ) ((polyFun_const true).pair polyFun_id)
  exact ((hf.pair ht).comp polyFun_append).of_eq (fun rows => by
    simp only [a13Jobs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl)

theorem polyFun_a13CJobs : PolyFun a13CJobs := by
  have hp := (polyFun_id.pair polyFun_id).comp (a13PolyFun_product (α := List ℕ) (β := List ℕ))
  have hf := hp.comp (PolyFun.map ((polyFun_const false).pair polyFun_id))
  have ht := hp.comp (PolyFun.map ((polyFun_const true).pair polyFun_id))
  exact ((hf.pair ht).comp polyFun_append).of_eq (fun rows => by
    simp only [a13CJobs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.product, List.map_flatMap, List.map_map]
    rfl)

theorem polyFun_a13Prepare : PolyFun a13Prepare := by
  have hC : PolyFun (fun p : AggnPhaseCtx × List (List ℕ) => p.1) := polyFun_fst
  have hj := polyFun_a13Rows.comp polyFun_a13Jobs
  have hk := polyFun_a13Rows.comp polyFun_a13CJobs
  have hl1 := (hC.pair hj).comp (PolyFun.mapParam aggnPolyFun_jobLoop)
  have hl2 := (hC.pair hk).comp (PolyFun.mapParam aggnPolyFun_compareCtx)
  exact ((hC.pair (hj.pair hk)).pair (hl1.pair hl2)).of_eq (fun _ => rfl)

theorem polyFun_a13Writes : PolyFun a13Writes := by
  have hC : PolyFun (fun p : AggnPhaseCtx × List AggnJob × List RawLCOut => p.1) := polyFun_fst
  have hs : PolyFun (fun p : AggnPhaseCtx × List AggnJob × List RawLCOut => p.2) := polyFun_snd
  have hz := ((pfst hs).pair (psnd hs)).comp (polyFun_zip (α := AggnJob) (β := RawLCOut))
  have he : PolyFun (fun q : AggnPhaseCtx × (AggnJob × RawLCOut) =>
      ((q.2.1, aggPack ((aggnJobLoop q.1 q.2.1).1.1, q.2.1.2, q.2.2)) : AggnWrite)) := by
    have hq : PolyFun (fun q : AggnPhaseCtx × (AggnJob × RawLCOut) => q) := polyFun_id
    have hloop := ((pfst hq).pair (pfst (psnd hq))).comp aggnPolyFun_jobLoop
    exact (pfst (psnd hq)).pair
      (((pfst (pfst hloop)).pair ((psnd (pfst (psnd hq))).pair
        (psnd (psnd hq)))).comp aggPolyFun_pack)
  exact ((hC.pair hz).comp (PolyFun.mapParam he)).of_eq (fun _ => rfl)

theorem polyFun_a13Stores : PolyFun a13Stores := by
  have hb : PolyFun (fun w : AggnWrite => w.1.1) := pfst polyFun_fst
  have hnb : PolyFun (fun w : AggnWrite => !w.1.1) :=
    (PolyFun.ite hb (polyFun_const false) (polyFun_const true)).of_eq (fun w => by
      cases w.1.1 <;> rfl)
  have hx := ((PolyFun.filter hnb).comp (PolyFun.map polyFun_snd)).comp polyFun_reverse
  have hy := ((PolyFun.filter hb).comp (PolyFun.map polyFun_snd)).comp polyFun_reverse
  exact hx.pair hy

theorem polyFun_a13State : PolyFun a13State :=
  ((((polyFun_const ([] : List AggnJob)).pair (polyFun_fst.pair
    ((polyFun_const 0).pair (polyFun_const default)))).pair ((polyFun_const 0).pair
    ((polyFun_const ([] : List AggnCompareJob)).pair (polyFun_snd.pair
      ((polyFun_const 0).pair (polyFun_const default))))))).of_eq (fun _ => rfl)

theorem polyFun_a13Collect : PolyFun a13Collect := by
  have hi : PolyFun (fun p : A13Ctx × (List RawLCOut × List RawCoset) => p) := polyFun_id
  have hC := pfst (pfst hi)
  have hw := (hC.pair ((pfst (psnd (pfst hi))).pair (pfst (psnd hi)))).comp polyFun_a13Writes
  have hs := ((hw.comp polyFun_a13Stores).pair ((psnd (psnd hi)).comp polyFun_reverse)).comp
    polyFun_a13State
  have hz := hC.pair hs
  have hDx := psnd (psnd ((hz.pair (polyFun_const false)).comp aggnPolyFun_aggregateData))
  have hDy := psnd (psnd ((hz.pair (polyFun_const true)).comp aggnPolyFun_aggregateData))
  have htbl := ((psnd (psnd (pfst hi))).pair (psnd (psnd hi))).comp
    (polyFun_zip (α := AggnCompareJob) (β := RawCoset))
  have ht := (psnd (psnd (psnd hC))).comp polyFun_length
  exact ((hz.pair htbl).pair ((hDx.pair ht).pair (((hDx.comp polyFun_rangeLength).pair ht).pair
    ((hDy.comp polyFun_rangeLength).pair ht)))).of_eq (fun _ => rfl)

theorem polyFun_a13GuidePrepare : PolyFun a13GuidePrepare := by
  have hi : PolyFun (fun p : AggnGuidePrepareInput × A13Tabs => p) := polyFun_id
  have hq := pfst hi
  have hctx := (pfst (pfst (pfst hq))).pair (psnd hq)
  have hDx := psnd (psnd (((pfst hq).pair (polyFun_const false)).comp
    aggnPolyFun_aggregateData))
  have hDy := psnd (psnd (((pfst hq).pair (polyFun_const true)).comp
    aggnPolyFun_aggregateData))
  have hr1 := (pfst (psnd hi)).comp (PolyFun.filter wftPolyFun_nodup)
  have hr2 := (pfst (psnd (psnd hi))).comp (PolyFun.filter wftPolyFun_nodup)
  have hr3 := (psnd (psnd (psnd hi))).comp (PolyFun.filter wftPolyFun_nodup)
  exact (hctx.pair (((hctx.pair hr1).comp aggnPolyFun_guideReps).pair
    ((hDx.pair hr2).pair (hDy.pair hr3)))).of_eq (fun _ => rfl)

theorem polyFun_a13Guide : PolyFun a13Guide := by
  have hC : PolyFun (fun p : AggnGuidePrepareInput × A13Tabs => p.1.1.1) :=
    pfst (pfst polyFun_fst)
  exact (((psnd (psnd (psnd hC))).pair (pfst (psnd hC))).pair
    polyFun_a13GuidePrepare).comp aggnPolyFun_guideBuild

private theorem polyFun_dispatchIs (k : ℕ) :
    PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => decide (aggnAggregateDispatch z = k)) :=
  (aggnPolyFun_aggregateDispatch.pair (polyFun_const k)).comp polyFun_natEq

theorem polyFun_a13Tag : PolyFun a13Tag := by
  have hz : PolyFun (fun p : (AggnPhaseCtx × AggnAggregateState) ×
      Option (AmbientPIn × AmbientPIn) => p.1) := polyFun_fst
  have hsome : PolyFun (fun p : (AggnPhaseCtx × AggnAggregateState) ×
      Option (AmbientPIn × AmbientPIn) => p.2.isSome) :=
    ((polyFun_snd.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const false)
      (polyFun_const true))).of_eq (fun p => by cases p.2 <;> rfl)
  exact PolyFun.ite (hz.comp (polyFun_dispatchIs 1)) (polyFun_const 1)
    (PolyFun.ite (hz.comp (polyFun_dispatchIs 2))
      (PolyFun.ite (hz.comp aggnPolyFun_aggregateGiantBranch) (polyFun_const 2)
        (PolyFun.ite (hz.comp aggnPolyFun_rejectCase) (polyFun_const 0) (polyFun_const 3)))
      (PolyFun.ite (hz.comp aggnPolyFun_rejectDefect) (polyFun_const 5)
        (PolyFun.ite hsome (polyFun_const 4) (polyFun_const 6))))

theorem polyFun_a13Report : PolyFun a13Report := by
  have hz : PolyFun (fun p : (AggnPhaseCtx × AggnAggregateState) ×
      Option (AmbientPIn × AmbientPIn) => p.1) := polyFun_fst
  have hb (b : Bool) := hz.pair (polyFun_const b)
  exact polyFun_a13Tag.pair
    ((((hb false).comp aggnPolyFun_aggregateData).pair ((hb true).comp aggnPolyFun_aggregateData)).pair
    ((((hb false).comp aggnPolyFun_aggregatePartition).pair
      ((hb true).comp aggnPolyFun_aggregatePartition)).pair
    ((((hb false).comp aggnPolyFun_aggregateMajority).pair
      ((hb true).comp aggnPolyFun_aggregateMajority)).pair
    ((((hb false).comp aggnPolyFun_aggregateCase2b).pair
      ((hb true).comp aggnPolyFun_aggregateCase2b)).pair polyFun_snd))))

theorem polyFun_a13Final : PolyFun a13Final := by
  have h1 : PolyFun (fun p : AggnGuidePrepareInput × A13Tabs => (p.1.1, a13Guide p)) :=
    (pfst polyFun_fst).pair polyFun_a13Guide
  exact (h1.comp polyFun_a13Report).of_eq (fun _ => rfl)

/-! ### Agreement with the Master chain when its guard holds -/

theorem aggnPhaseRows_eq_a13Rows {c : ℕ} {C : AggnPhaseCtx}
    (hg : C.2.2.2.length ≤ guardBound c C.2.1.length) :
    aggnPhaseRows c C = a13Rows (C, tuplesOf (List.range C.1.2.1.length) C.2.2.2.length) := by
  unfold aggnPhaseRows aggTestSetsOn a13Rows
  rw [aggTable_of_guard (a := (C.2.2.2, C.2.1, List.range C.1.2.1.length)) hg, keys_tupleTable]

theorem aggnGuideRows_of_guard {c : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) :
    aggnGuideRows c (ks, dom, D) = (tuplesOf D ks.length).filter wftNodup := by
  rw [aggnGuideRows, aggTable_of_guard (a := (ks, dom, D)) hg, keys_tupleTable]

/-- The three tuple tables of case (3), for a state after the two phases. -/
def a13GuideTabs (z : AggnPhaseCtx × AggnAggregateState) : A13Tabs :=
  (tuplesOf (aggnAggregateData (z, false)).2.2 z.1.2.2.2.length,
    tuplesOf (List.range (aggnAggregateData (z, false)).2.2.length) z.1.2.2.2.length,
    tuplesOf (List.range (aggnAggregateData (z, true)).2.2.length) z.1.2.2.2.length)

theorem a13GuidePrepare_eq {c : ℕ} (q : AggnGuidePrepareInput)
    (hg : q.1.1.2.2.2.length ≤ guardBound c q.1.1.2.1.length) :
    a13GuidePrepare (q, a13GuideTabs q.1) = aggnGuidePrepare c q := by
  unfold a13GuidePrepare aggnGuidePrepare aggnGuideSideRows a13GuideTabs
  simp only [aggnGuideRows_of_guard hg]

theorem a13Guide_eq_of_table {c : ℕ} (z : AggnPhaseCtx × AggnAggregateState)
    (hg : z.1.2.2.2.length ≤ guardBound c z.1.2.1.length) :
    a13Guide ((z, aggnCompareTable c (z.1, z.2.2.2.2.1)), a13GuideTabs z) =
      aggnAggregateGuide c z := by
  rw [a13Guide, a13GuidePrepare_eq (z, aggnCompareTable c (z.1, z.2.2.2.2.1)) hg,
    aggnAggregateGuide]

end Algo
