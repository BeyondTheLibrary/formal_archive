import Workspace.Algo.AggNodeCheckedScan

/-! # The certificate scan, initialization, and combine on the RAM

The scan below is exactly `aggnPhaseScan`. Its machine proof prepares the
supplied jobs and applies the bounded traversal. This preserves the first
active job and the original store order. All routines are bounded on every
raw input, with no hypothesis about states or recursive answers.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-- Prepare one row and its possible no-call store entry. -/
def aggnReadyJob (c : ℕ) (p : AggnPhaseCtx × AggnJob) : AggnReadyRow :=
  let v := aggnCertOpen c (aggnJobLoop p.1 p.2)
  (p.2, v, aggPack (v.1.1.1, p.2.2, aggnCertOut v))

theorem aggnQuasiFun_readyJob (c : ℕ) : QuasiFun (aggnReadyJob c) := by
  have hpack : PolyFun (fun p : AggnJob × AggnCertState =>
      (p.1, p.2, aggPack (p.2.1.1.1, p.1.2, aggnCertOut p.2))) := by
    have hp : PolyFun (fun p : AggnJob × AggnCertState => p) := polyFun_id
    have ha := pfst hp
    have hv := psnd hp
    have he := ((pfst (pfst (pfst hv))).pair ((psnd ha).pair
      ((pfst hv).comp lcwPolyFun_out))).comp aggPolyFun_pack
    exact ha.pair (hv.pair he)
  have hv := aggnPolyFun_jobLoop.comp_quasiFun (aggnQuasiFun_certOpen c)
  exact (polyFun_snd.quasiFun.pair hv).comp_poly hpack

/-- The prepared traversal returns exactly the existing phase scan. -/
theorem aggnReadyJob_scan (c : ℕ) (C : AggnPhaseCtx) :
    ∀ jobs stores,
      aggnReadyScan (aggnCertOpen c (([], []), ([], [], [])))
        (jobs.map fun a => aggnReadyJob c (C, a)) stores = aggnPhaseScan c C jobs stores := by
  intro jobs
  induction jobs with
  | nil => intro stores; rfl
  | cons a rest ih =>
    intro stores
    simp only [List.map_cons, aggnReadyScan, aggnReadyJob, aggnPhaseScan]
    split
    · simp only [List.map_map, Function.comp_def]
      congr 2
      exact List.map_id rest
    · exact ih _

/-- Scanning all supplied jobs has an unconditional quasipolynomial machine bound. -/
theorem aggnQuasiFun_phaseScan (c : ℕ) :
    QuasiFun (fun z : AggnPhaseCtx × List AggnJob × AggnStores => aggnPhaseScan c z.1 z.2.1 z.2.2) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × List AggnJob × AggnStores => z) := polyFun_id
  have hprep := ((pfst hz).pair (pfst (psnd hz))).comp_quasiFun
    (aggnQuasiFun_mapParam (aggnQuasiFun_readyJob c))
  have hm := (hprep.pair (psnd (psnd hz)).quasiFun).comp_poly
    (aggnPolyFun_readyScan (aggnCertOpen c (([], []), ([], [], []))))
  exact hm.of_eq (fun z => aggnReadyJob_scan c z.1 z.2.1 z.2.2)

theorem aggnQuasiFun_phaseJobs (c : ℕ) : QuasiFun (aggnPhaseJobs c) := by
  have hC : PolyFun (fun C : AggnPhaseCtx => C) := polyFun_id
  have hrows := ((psnd (psnd (psnd hC))).pair
    ((pfst (psnd hC)).pair (pfst (psnd (pfst hC))))).comp_quasiFun (aggQuasiFun_testSetsOn c)
  have hf := hrows.comp_poly (PolyFun.map ((polyFun_const false).pair polyFun_id))
  have ht := hrows.comp_poly (PolyFun.map ((polyFun_const true).pair polyFun_id))
  exact ((hf.pair ht).comp_poly polyFun_append).of_eq (fun C => by
    simp only [aggnPhaseJobs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      aggnPhaseRows]
    rfl)

theorem aggnQuasiFun_phaseInit (c n : ℕ) : QuasiFun (aggnCheckedRound c n).init := by
  have hC : PolyFun (fun I : AggnPhaseNode => I.1) := polyFun_fst
  have hj := hC.comp_quasiFun (aggnQuasiFun_phaseJobs c)
  have hi := hC.quasiFun.pair (hj.pair (quasiFun_const (([], []) : AggnStores)))
  have hr := hi.comp (aggnQuasiFun_phaseScan c)
  exact hr.of_eq (fun _ => rfl)

/-- The checked node bound gives an initial-state bound uniform in the parent degree.
This is an initialization bound, not a closure assertion for arbitrary combines. -/
theorem aggnCheckedInit_size_bound (c : ℕ) :
    ∃ B : ℕ → ℕ, QuasiPolyBound B ∧ Monotone B ∧
      ∀ (n : ℕ) I, (aggnCheckedRound c n).WF I →
        Enc.size ((aggnCheckedRound c n).init I) ≤ B ((aggnCheckedRound c n).ground I) := by
  obtain ⟨S, hS, hmono, hs⟩ := (aggnQuasiFun_phaseInit c 0).size.exists_quasiPolyBound
  refine ⟨fun k => S (aggnCheckedBound k), hS.comp_poly aggnPolyBound_checked,
    fun a b hab => hmono _ _ (aggnMono_checkedBound hab), ?_⟩
  intro n I hI
  exact (hs I).trans (hmono _ _ (aggnCheckedRound_size c n I hI))

theorem aggnQuasiFun_phasePack (c : ℕ) :
    QuasiFun (fun z : AggnPhaseCtx × AggnJob × List AggnJob × AggnStores × ℕ × AggnCertState =>
      aggnPhasePack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  let X := AggnPhaseCtx × AggnJob × List AggnJob × AggnStores × ℕ × AggnCertState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst hz
  have ha := pfst (psnd hz)
  have hr := pfst (psnd (psnd hz))
  have hs := pfst (psnd (psnd (psnd hz)))
  have hj := pfst (psnd (psnd (psnd (psnd hz))))
  have hv := psnd (psnd (psnd (psnd (psnd hz))))
  have ht := (pfst hv).comp polyFun_lcCond
  have hthen := ((ha.pair hr).comp polyFun_cons).pair (hs.pair (hj.pair hv))
  have hstore := (ha.pair (hv.pair hs)).comp aggnPolyFun_storeJob
  have helse := (hC.pair (hr.pair hstore)).comp_quasiFun (aggnQuasiFun_phaseScan c)
  exact (QuasiFun.ite ht hthen.quasiFun helse).of_eq (fun _ => rfl)

/-- Combining an answer has a quasipolynomial machine bound, including on malformed states. -/
theorem aggnQuasiFun_phaseCombine (c : ℕ) : QuasiFun (aggnPhaseCombine c) := by
  let X := AggnPhaseNode × ℕ × AggnPhaseState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst (pfst hz)
  have hs := pfst (psnd (psnd hz))
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hstores := pfst (psnd hs)
  have hnil := (hC.pair ((polyFun_const ([] : List AggnJob)).pair hstores)).comp_quasiFun
    (aggnQuasiFun_phaseScan c)
  have hcons : QuasiFun (fun z : (AggnJob × List AggnJob) × X =>
      aggnPhasePack c z.2.1.1 z.1.1 z.1.2 z.2.2.2.1.2.1 (z.2.2.2.1.2.2.1 + 1)
        (aggnCertCombine c ((aggnJobLoop z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2))) := by
    have hctx : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.1.1) := polyFun_snd.comp hC
    have hjob : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.1.1) := pfst polyFun_fst
    have hrest : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.1.2) := psnd polyFun_fst
    have hstore : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.2.2.1.2.1) :=
      polyFun_snd.comp hstores
    have hidx : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.2.2.1.2.2.1) :=
      polyFun_snd.comp hj
    have hloop := (hctx.pair hjob).comp aggnPolyFun_jobLoop
    have hinput := (hloop.pair (polyFun_const (none : Option RawWinSI))).pair
      (hidx.pair ((polyFun_snd.comp hv).pair (polyFun_snd.comp ha)))
    have hnext := hinput.comp_quasiFun (aggnQuasiFun_certCombine c)
    have hidx' := (hidx.pair (polyFun_const 1)).comp polyFun_add
    have hpack := hctx.quasiFun.pair (hjob.quasiFun.pair (hrest.quasiFun.pair
      (hstore.quasiFun.pair (hidx'.quasiFun.pair hnext))))
    have hm := hpack.comp (aggnQuasiFun_phasePack c)
    exact hm.of_eq (fun z => by dsimp only)
  have hm := (((pfst hs).pair hz).comp_quasiFun (QuasiFun.listCases hnil hcons))
  exact hm.of_eq (fun z => by unfold aggnPhaseCombine; cases z.2.2.1.1 <;> rfl)

theorem aggnQuasiFun_checkedCombine (c n : ℕ) : QuasiFun (aggnCheckedRound c n).combine :=
  aggnQuasiFun_phaseCombine c

theorem aggnPolyFun_checkedFinish (c n : ℕ) : PolyFun (aggnCheckedRound c n).finish :=
  polyFun_const none

end Algo
