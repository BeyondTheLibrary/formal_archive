import Workspace.Algo.AggNodeCertRun
import Workspace.Algo.AggNodeCertInit
import Workspace.Algo.AggNodeCertEnum
import Workspace.Algo.AggregateReadOff

/-! # The certificate phase in one node

The pending list contains all source test sets, then all target test sets.
Finishing a certificate stores its output and scans to the next active job
before the next child is requested. The scan is bounded by its input list.
-/
namespace Algo
open Babai Equiv
open scoped Classical

abbrev AggnPhaseCtx := RawAction × RawStr × RawStr × List ℕ
abbrev AggnJob := Bool × List ℕ
abbrev AggnStores := RawAggStore × RawAggStore
abbrev AggnPhaseState := List AggnJob × AggnStores × ℕ × AggnCertState
abbrev AggnPhaseNode := AggnPhaseCtx × Option RawWinSI

def aggnJobLoop (C : AggnPhaseCtx) (a : AggnJob) : RawLCLoop :=
  ((cond a.1 C.2.2.1 C.2.1, a.2), aggnInitialState (C.1, a.2))

def aggnPhaseRows (c : ℕ) (C : AggnPhaseCtx) : List (List ℕ) :=
  aggTestSetsOn c (C.2.2.2, C.2.1, C.1.2.1)

def aggnPhaseJobs (c : ℕ) (C : AggnPhaseCtx) : List AggnJob :=
  [false, true].flatMap fun b => (aggnPhaseRows c C).map (fun row => (b, row))

def aggnStoreJob (a : AggnJob) (v : AggnCertState) (stores : AggnStores) : AggnStores :=
  let e := aggPack (v.1.1.1, a.2, aggnCertOut v)
  if a.1 then (stores.1, e :: stores.2) else (e :: stores.1, stores.2)

/-- Scan only the stored list, including jobs whose whole run has no calls. -/
def aggnPhaseScan (c : ℕ) (C : AggnPhaseCtx) : List AggnJob → AggnStores → AggnPhaseState
  | [], stores => ([], stores, 0, aggnCertOpen c (([], []), ([], [], [])))
  | a :: rest, stores =>
    let v := aggnCertOpen c (aggnJobLoop C a)
    if lcCond v.1 then (a :: rest, stores, 0, v)
    else aggnPhaseScan c C rest (aggnStoreJob a v stores)

def aggnPhasePack (c : ℕ) (C : AggnPhaseCtx) (a : AggnJob) (rest : List AggnJob)
    (stores : AggnStores) (j : ℕ) (v : AggnCertState) : AggnPhaseState :=
  if lcCond v.1 then (a :: rest, stores, j, v)
  else aggnPhaseScan c C rest (aggnStoreJob a v stores)

theorem aggnPhaseScan_cons (c : ℕ) (C : AggnPhaseCtx) (a : AggnJob)
    (rest : List AggnJob) (stores : AggnStores) :
    aggnPhaseScan c C (a :: rest) stores =
      aggnPhasePack c C a rest stores 0 (aggnCertOpen c (aggnJobLoop C a)) := by
  rfl

def aggnPhaseWidth (c : ℕ) (C : AggnPhaseCtx) : ℕ :=
  (aggnPhaseJobs c C).length *
    (C.2.1.length * (Nat.factorial C.2.2.2.length * C.2.1.length))

def aggnPhaseChild (c : ℕ) (z : AggnPhaseNode × ℕ × AggnPhaseState) : Option AggnPhaseNode :=
  z.1.2.elim
    (if z.2.1 < aggnPhaseWidth c z.1.1 then
      match z.2.2.1 with
      | [] => none
      | a :: _ =>
        (aggnCertChild ((aggnJobLoop z.1.1 a, none), z.2.2.2.2.1, z.2.2.2.2.2)).map
          (fun J => (z.1.1, J.2))
    else none) (fun _ => none)

def aggnPhaseCombine (c : ℕ) (z : AggnPhaseNode × ℕ × AggnPhaseState × RawCoset) :
    AggnPhaseState :=
  match z.2.2.1.1 with
  | [] => aggnPhaseScan c z.1.1 [] z.2.2.1.2.1
  | a :: rest => aggnPhasePack c z.1.1 a rest z.2.2.1.2.1 (z.2.2.1.2.2.1 + 1)
      (aggnCertCombine c ((aggnJobLoop z.1.1 a, none), z.2.2.1.2.2.1,
        z.2.2.1.2.2.2, z.2.2.2))

noncomputable def aggnPhaseDecode (n : ℕ) (I : AggnPhaseNode) : SIInstance (Fin n) ℕ :=
  I.2.elim (decWinSI n ([], [], [], I.1.2.1, I.1.2.2.1)) (decWinSI n)

theorem aggnPhaseChild_some {c : ℕ} {z : AggnPhaseNode × ℕ × AggnPhaseState}
    {J : AggnPhaseNode} (h : aggnPhaseChild c z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) := by
  cases ho : z.1.2 with
  | some W => simp [aggnPhaseChild, ho] at h
  | none =>
    simp only [aggnPhaseChild, ho, Option.elim_none] at h
    split at h
    next hg =>
      split at h
      next => simp at h
      next a rest he =>
        obtain ⟨J', hJ', he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨_, W, hW⟩ := aggnCertChild_some hJ'
        rw [hW] at he
        exact ⟨rfl, W, he.symm⟩
    next => simp at h

/-- A phase carrier with window children, ready for the master embedding. -/
def aggnPhaseRound (c n : ℕ) : Round AggnPhaseNode AggnPhaseState RawCoset where
  WF := fun I => I.1.2.1.length = n
  ground := fun I => I.1.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnPhaseWidth c I.1) (fun _ => 0)
  child := aggnPhaseChild c
  init := fun I => aggnPhaseScan c I.1 (aggnPhaseJobs c I.1) ([], [])
  combine := aggnPhaseCombine c
  finish := fun _ => none
  bot := none
  child_eq_none := by
    intro I j v hj
    cases ho : I.2 with
    | some W => simp [aggnPhaseChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      simp only [aggnPhaseChild, ho, Option.elim_none]
      exact if_neg (Nat.not_lt.mpr hj)
  child_wf := by
    intro I j v J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnPhaseChild_some hJ
    exact hI
  child_measure := by
    intro I j v J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnPhaseChild_some hJ
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j v J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnPhaseChild_some hJ
    exact le_rfl

/-- The source child test records both activity and its local call bound. -/
theorem aggnCertChild_active {z : AggnCertNode × ℕ × AggnCertState} {J : AggnCertNode}
    (h : aggnCertChild z = some J) :
    lcCond z.2.2.1 = true ∧ z.2.1 < aggnCertWidth z.1.1 := by
  have ho := (aggnCertChild_some h).1
  simp only [aggnCertChild, ho, Option.elim_none] at h
  split at h
  next hg => exact hg
  next => simp at h

/-- A whole local run can advance the outer cursor at its endpoint. -/
theorem aggnPhase_sim_run (c n : ℕ) (C : AggnPhaseCtx) (a : AggnJob)
    (rest : List AggnJob) (stores : AggnStores) (start : ℕ)
    (hwidth : start + aggnCertWidth (aggnJobLoop C a) ≤ aggnPhaseWidth c C)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ (Set (Fin n) × Subgroup (Perm (Fin n)))}
    {Q : (Set (Fin n) × Subgroup (Perm (Fin n))) → ℕ → AggnCertState → Prop}
    (h : PhaseMatch (aggnCertRound c n (fun _ => none)) (aggnCertDecode n) (decCoset n)
      (aggnJobLoop C a, none) fuel 0 (aggnCertOpen c (aggnJobLoop C a)) S Q) :
    PhaseMatch (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel start (aggnPhaseScan c C (a :: rest) stores) S
      (fun b j v => ∃ j' v', Q b j' v' ∧ j = start + j' ∧
        v = aggnPhasePack c C a rest stores j' v') := by
  let Rel := fun jR vR jM vM => jM = start + jR ∧
    vM = aggnPhasePack c C a rest stores jR vR
  apply aggnPhaseMatch_sim (R := aggnCertRound c n (fun _ => none))
    (decI := aggnCertDecode n) (I := (aggnJobLoop C a, none)) Rel ?_ h
    ⟨by omega, aggnPhaseScan_cons c C a rest stores⟩
  intro jR vR jM vM hr J hJ
  obtain ⟨hj, rfl⟩ := hr
  dsimp only [aggnCertRound] at hJ
  have ha := aggnCertChild_active (z := ((aggnJobLoop C a, none), jR, vR)) hJ
  dsimp only at ha
  have hglobal : jM < aggnPhaseWidth c C := by omega
  refine ⟨(C, J.2), ?_, ?_, ?_⟩
  · dsimp only [aggnPhaseRound]
    rw [aggnPhasePack, if_pos ha.1]
    simp only [aggnPhaseChild, Option.elim_none, if_pos hglobal]
    rw [hJ]
    rfl
  · obtain ⟨_, W, hW⟩ := aggnCertChild_some hJ
    rw [hW]
    rfl
  · intro ans
    refine ⟨by omega, ?_⟩
    dsimp only [aggnPhaseRound, aggnCertRound]
    rw [aggnPhasePack, if_pos ha.1]
    rfl


section Correctness
variable {c n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

structure AggnPhaseCtxWF (c n m : ℕ) (C : AggnPhaseCtx)
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) : Prop where
  action : RawAction.WF n m C.1 ϕ
  source : C.2.1.length = n
  target : C.2.2.1.length = n
  degree : m ≤ n
  arity : C.2.2.2.length ≤ n
  guard : C.2.2.2.length ≤ guardBound c C.2.1.length

theorem aggnJob_mem {a : AggnJob} : a ∈ aggnPhaseJobs c C ↔ a.2 ∈ aggnPhaseRows c C := by
  rcases a with ⟨b, row⟩
  cases b <;> simp [aggnPhaseJobs]

theorem aggnJob_data (hC : AggnPhaseCtxWF c n m C ϕ) {a : AggnJob}
    (ha : a ∈ aggnPhaseJobs c C) :
    a.2.Nodup ∧ (∀ u ∈ a.2, u < m) ∧ a.2.length = C.2.2.2.length ∧ a.2.SortedLE := by
  have hm : C.1.2.1.length ≤ C.2.1.length := by rw [hC.action.2.1, hC.source]; exact hC.degree
  have hr := aggnJob_mem.mp ha
  have hw := aggRowOn_wf hC.guard hm hr
  have he := ((aggMem_testSetsOn hC.guard hm).mp hr).2
  refine ⟨hw.1, ?_, hw.2.2, ?_⟩
  · simpa only [hC.action.2.1] using hw.2.1
  · rw [he]
    exact (List.pairwise_lt_range.filter _).imp (fun h => h.le) |>.sortedLE

/-- The context passed to one local-certificate run. -/
def aggnJobCtx (hC : AggnPhaseCtxWF c n m C ϕ) {a : AggnJob}
    (ha : a ∈ aggnPhaseJobs c C) : LCCtxWF n m (aggnJobLoop C a).1.1 a.2 := by
  have hd := aggnJob_data hC ha
  refine ⟨?_, hd.1, hd.2.1, fun u hu => (hd.2.1 u hu).trans_le hC.degree, ?_⟩
  · cases hb : a.1 <;> simp [aggnJobLoop, hb, hC.source, hC.target]
  · rw [hd.2.2.1]; exact hC.arity

def aggnJobWidth (C : AggnPhaseCtx) : ℕ :=
  C.2.1.length * (Nat.factorial C.2.2.2.length * C.2.1.length)

theorem aggnJobWidth_eq (hC : AggnPhaseCtxWF c n m C ϕ) {a : AggnJob}
    (ha : a ∈ aggnPhaseJobs c C) : aggnCertWidth (aggnJobLoop C a) = aggnJobWidth C := by
  have hx := (aggnJobCtx hC ha).lenStr
  simp only [aggnCertWidth, aggnCertStageWidth, hx]
  change n * (Nat.factorial a.2.length * n) = _
  rw [(aggnJob_data hC ha).2.2.1]
  exact congrArg (fun k => k * (Nat.factorial C.2.2.2.length * k)) hC.source.symm

noncomputable def aggnJobTree (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) (a : AggnJob) :=
  certRunStrong ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2)
    (fun i => aggkCanonReps (stages ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2) i)
      (aggkPoints (winSet m a.2)))
    (fun i => aggkCanonWindows (stages ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2) i))

/-- One job ends by storing its output and scanning the remaining jobs. -/
theorem aggnPhase_job (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ)
    {a : AggnJob} (ha : a ∈ aggnPhaseJobs c C) (rest : List AggnJob)
    (stores : AggnStores) (start : ℕ)
    (hwidth : start + aggnJobWidth C ≤ aggnPhaseWidth c C) :
    PhaseMatch (aggnPhaseRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnJobWidth C) start (aggnPhaseScan c C (a :: rest) stores) (aggnJobTree ϕ a)
      (fun B j v => ∃ st,
        StateFor (aggnJobCtx hC ha)
          (outStage ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2)) st ∧
        v = aggnPhaseScan c C rest (aggnStoreJob a
          (aggnCertOpen c ((aggnJobLoop C a).1, st)) stores) ∧
        B = (windowOut ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2),
          certK ϕ (decStrN n (aggnJobLoop C a).1.1) (winSet m a.2)) ∧
        j ≤ start + aggnJobWidth C) := by
  let hc := aggnJobCtx hC ha
  have h0 := aggnInitialState_for hc hC.action hgiant
  have hg : a.2.length ≤ guardBound c (aggnJobLoop C a).1.1.length := by
    rw [hc.lenStr, (aggnJob_data hC ha).2.2.1]
    simpa only [hC.source] using hC.guard
  have hp := aggnCertPhase_run c (fun _ => none) h0 hg
  rw [aggkTypedT_eq_points hc (aggnJob_data hC ha).2.2.2] at hp
  have hw : n * (Nat.factorial a.2.length * n) = aggnJobWidth C := by
    rw [(aggnJob_data hC ha).2.2.1]
    exact congrArg (fun k => k * (Nat.factorial C.2.2.2.length * k)) hC.source.symm
  rw [hw] at hp
  have hm := aggnPhase_sim_run c n C a rest stores start
    (by rwa [aggnJobWidth_eq hC ha]) hp
  apply phaseMatch_weaken hm
  rintro B j v ⟨jR, vR, ⟨st, hs, hvR, hread, hB, hjR⟩, hj, hv⟩
  have hstop : lcCond ((aggnJobLoop C a).1, st) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact not_loopCond_outStage _ _ _ ((lcCond_eq_true_iff hs).mp ht)
  refine ⟨st, hs, ?_, hB, ?_⟩
  · rw [hv, hvR, aggnPhasePack]
    exact if_neg (Bool.eq_false_iff.mp hstop)
  · rw [hw] at hjR
    omega

end Correctness
end Algo
