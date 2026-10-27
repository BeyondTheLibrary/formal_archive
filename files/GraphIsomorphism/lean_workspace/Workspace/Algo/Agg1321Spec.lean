/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: what the standalone routine of Theorem 13.2.1 computes.
-/
import Workspace.Algo.Agg1321Defs
import Workspace.Algo.AggNodeGuideSuccess

/-!
# Theorem 13.2.1 as one routine: what it computes

`Algo.a13Result ansQ C` is the whole of Procedure AggregateCertificates (§13.2) on the pair
of strings `x = C.2.1`, `y = C.2.2.1`, with the group and the giant representation given by
the raw action `C.1`, and `t = |C.2.2.2|`. The calls to String Isomorphism on windows are
answered by `ansQ`. The steps:

1. the `t`-tuples of `Γ` and the test sets (`Algo.a13Tuples`, `Algo.a13Rows`);
2. the inputs of the `2·C(m,t)` certificate runs and the `2·C(m,t)²` comparison runs
   (`Algo.a13Prep`);
3. the two phases (`Algo.a13Phases`), with calls `Algo.a13Calls`;
4. the stores, the comparison table, and `D(x)`, `D(y)` (`Algo.a13Mid`);
5. the tuple tables of case (3) and the case analysis (`Algo.a13Result`).

The hypotheses are those of the theorem (`Algo.A13Hyp`): `ϕ` is a giant representation of a
transitive `G` with `m ≥ 10 log₂ n` (`Babai.LocalCertSetting`), `max{8, 2 + log₂ n} < t`
(`Babai.LargeK`) and `t < m/10`, and the input is well formed. They give the Master chain's
guard for `c = t` (`Algo.A13Hyp.guard`), so the chain's correctness lemmas apply.

* `Algo.a13Result_eq`: the output is `Algo.a13Report` of a state whose stores are complete
  and correct and whose comparison table is correct (`Algo.a13_stores`, `Algo.a13_table`),
  and the local guide is the chain's.
* `Algo.a13_calls`: the calls number at most `Babai.aggregateRoundCost m t n` (the paper's
  `2·C(m,t)` runs of LocalCertificates and `2·C(m,t)²` runs of CompareLocalCertificates, each
  with at most `t!·n²` calls), all on windows of at most `n/t` points.
* `Algo.a13_tag_one` … `Algo.a13_tag_six`, `Algo.a13_data`, `Algo.a13_partition_majority`: what each
  exit and each output means.
-/

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000

namespace Algo
open RAM RAM.Targets Babai MulAction
open Equiv (Perm)
open scoped Pointwise

/-- A giant representation of a group of permutations of `n` points has degree at most `n`
(`|A_m| ≤ |G| ≤ n!`), once `m ≥ 3`. -/
theorem le_of_isGiantRep {n m : ℕ} {G : Subgroup (Perm (Fin n))} (ϕ : G →* Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hm : 3 ≤ m) : m ≤ n := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : Nat.card (alternatingGroup (Fin m)) ≤ Nat.card ϕ.range := Subgroup.card_le_of_le hϕ
  have h2 : Nat.card ϕ.range ≤ Nat.card G :=
    Nat.card_le_card_of_surjective _ ϕ.rangeRestrict_surjective
  have h3 : Nat.card G ≤ Nat.card (Perm (Fin n)) := Subgroup.card_le_card_group G
  have h4 := two_mul_nat_card_alternatingGroup (α := Fin m)
  rw [Nat.card_perm, Nat.card_fin] at h3 h4
  by_contra hlt
  push_neg at hlt
  have h5 : (n + 1).factorial ≤ m.factorial := Nat.factorial_le hlt
  have h6 : (3 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
  have h7 := Nat.factorial_succ n
  have h8 := Nat.factorial_pos n
  have h9 : m.factorial ≤ 2 * n.factorial := by omega
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n.factorial ≤ (1 : ℕ).factorial := Nat.factorial_le (by omega)
    simp [Nat.factorial] at this h6
    omega
  · have : 3 * n.factorial ≤ (n + 1) * n.factorial := Nat.mul_le_mul_right _ (by omega)
    omega

/-- The hypotheses of **Theorem 13.2.1** (§13.2) on the raw input `C = (A, x, y, t-list)`:

> Let `ϕ : G → S(Γ)` be a giant representation, where `G ≤ S(Ω)`, `|Ω| = n`, and `|Γ| = m`.
> Let `max{8, 2 + log₂ n} < t < m/10`.

together with the standing assumptions of §13.1 (`G` transitive, `m ≥ 10 log₂ n`,
`Babai.LocalCertSetting`) and the well-formedness of the encoding. -/
structure A13Hyp (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) :
    Prop where
  action : RawAction.WF n m C.1 ϕ
  source : C.2.1.length = n
  target : C.2.2.1.length = n
  setting : LocalCertSetting (decGroup n C.1.1.2) ϕ
  large : LargeK C.2.2.2.length n
  small : 10 * C.2.2.2.length < m

section Hyp

variable {n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

theorem A13Hyp.degree (h : A13Hyp n m C ϕ) : m ≤ n := by
  have := h.large.eight_lt
  have := h.small
  exact le_of_isGiantRep ϕ h.setting.giant (by omega)

/-- The Master chain's guard `t ≤ (log₂ n + 1)^c` holds for `c = t`. -/
theorem A13Hyp.guard (h : A13Hyp n m C ϕ) :
    C.2.2.2.length ≤ guardBound C.2.2.2.length C.2.1.length := by
  have h8 := h.large.eight_lt
  have hs := h.small
  have hd := h.degree
  rw [guardBound, h.source]
  have hl : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  calc C.2.2.2.length ≤ 2 ^ C.2.2.2.length := Nat.lt_two_pow_self.le
    _ ≤ (Nat.log 2 n + 1) ^ C.2.2.2.length := Nat.pow_le_pow_left (by omega) _

theorem A13Hyp.ctx (h : A13Hyp n m C ϕ) : AggnPhaseCtxWF C.2.2.2.length n m C ϕ where
  action := h.action
  source := h.source
  target := h.target
  degree := h.degree
  arity := by have := h.small; have := h.degree; omega
  guard := h.guard

theorem A13Hyp.largeK (h : A13Hyp n m C ϕ) : LargeK C.2.2.2.length (Nat.card (Fin n)) := by
  rw [Nat.card_fin]; exact h.large

theorem A13Hyp.small' (h : A13Hyp n m C ϕ) : 10 * C.2.2.2.length ≤ m := h.small.le

theorem A13Hyp.nonempty (h : A13Hyp n m C ϕ) : Nonempty (Fin n) :=
  ⟨⟨0, by have := h.small; have := h.degree; omega⟩⟩

end Hyp

/-! ### The routine -/

/-- Step 1: all `t`-tuples of `[m]`. -/
def a13Tuples (C : AggnPhaseCtx) : List (List ℕ) :=
  tuplesOf (List.range C.1.2.1.length) C.2.2.2.length

/-- Step 2: the jobs and the inputs of all runs. -/
def a13Prep (C : AggnPhaseCtx) : A13Ctx × (List RawLCLoop × List RawPCLoop) :=
  a13Prepare (C, a13Tuples C)

/-- Step 3: the answers of the two phases. -/
def a13Phases (ansQ : RawWinSI → RawCoset) (C : AggnPhaseCtx) :
    List RawLCOut × List RawCoset :=
  ((a13Prep C).2.1.map (lcOut (lcSolveQ ansQ)), (a13Prep C).2.2.map (pcOut (lcSolveQ ansQ)))

/-- The String Isomorphism calls of the routine (all made in the two phases). -/
def a13Calls (ansQ : RawWinSI → RawCoset) (C : AggnPhaseCtx) : List RawWinSI :=
  phaseCalls ansQ (a13Prep C).2.1 (a13Prep C).2.2

/-- Step 4: the state after the phases, the comparison table and the inputs of the tables. -/
def a13Mid (ansQ : RawWinSI → RawCoset) (C : AggnPhaseCtx) : A13Mid :=
  a13Collect ((a13Prep C).1, a13Phases ansQ C)

/-- Step 5a: the three tuple tables of case (3). -/
def a13TabsOf (M : A13Mid) : A13Tabs :=
  (tuplesOf M.2.1.1 M.2.1.2, tuplesOf M.2.2.1.1 M.2.2.1.2, tuplesOf M.2.2.2.1 M.2.2.2.2)

/-- **Theorem 13.2.1** (§13.2), the output of the whole routine. -/
def a13Result (ansQ : RawWinSI → RawCoset) (C : AggnPhaseCtx) : A13Out :=
  a13Final ((a13Mid ansQ C).1, a13TabsOf (a13Mid ansQ C))

/-- The state after the two phases. -/
def a13StateOf (ansQ : RawWinSI → RawCoset) (C : AggnPhaseCtx) : AggnAggregateState :=
  (a13Mid ansQ C).1.1.2

theorem zip_map_self {α β : Type*} (l : List α) (g : α → β) :
    l.zip (l.map g) = l.map (fun a => (a, g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ### Correctness -/

section Correct

variable {n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

theorem a13_rows (h : A13Hyp n m C ϕ) :
    a13Rows (C, a13Tuples C) = aggnPhaseRows C.2.2.2.length C :=
  (aggnPhaseRows_eq_a13Rows h.guard).symm

theorem a13_jobs (h : A13Hyp n m C ϕ) :
    (a13Prep C).1.2.1 = aggnPhaseJobs C.2.2.2.length C := by
  show a13Jobs (a13Rows (C, a13Tuples C)) = _
  rw [a13_rows h]; rfl

theorem a13_cjobs (h : A13Hyp n m C ϕ) :
    (a13Prep C).1.2.2 = aggnCompareJobs C.2.2.2.length C := by
  show a13CJobs (a13Rows (C, a13Tuples C)) = _
  rw [a13_rows h]; rfl

theorem a13_l1 (h : A13Hyp n m C ϕ) :
    (a13Prep C).2.1 = (aggnPhaseJobs C.2.2.2.length C).map (aggnJobLoop C) := by
  rw [← a13_jobs h]; rfl

theorem a13_l2 (h : A13Hyp n m C ϕ) :
    (a13Prep C).2.2 = (aggnCompareJobs C.2.2.2.length C).map (aggnCompareCtx C) := by
  rw [← a13_cjobs h]; rfl

/-- Each certificate run gets the input of Procedure LocalCertificates: a test set of `t`
points and the state `G_T` of line 01. -/
theorem a13_certRun (h : A13Hyp n m C ϕ) {a : AggnJob}
    (ha : a ∈ aggnPhaseJobs C.2.2.2.length C) :
    CertRunInput ϕ C.2.2.2.length (aggnJobLoop C a) :=
  ⟨aggnJobCtx h.ctx ha, aggnInitialState_for (aggnJobCtx h.ctx ha) h.action h.setting.giant,
    (aggnJob_data h.ctx ha).2.2.1⟩

/-- Each comparison run gets the input of CompareLocalCertificates, including the transporter
coset of line 01, and returns `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})`. -/
theorem a13_compareRun (h : A13Hyp n m C ϕ) {a : AggnCompareJob}
    (ha : a ∈ aggnCompareJobs C.2.2.2.length C) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    CompareRunInput ϕ C.2.2.2.length (aggnCompareCtx C a) ∧
      decCoset n (pcOut (lcSolveQ ansQ) (aggnCompareCtx C a)) = aggnCompareValue ϕ a := by
  obtain ⟨b, row, row'⟩ := a
  have hmem : row ∈ aggnPhaseRows C.2.2.2.length C ∧ row' ∈ aggnPhaseRows C.2.2.2.length C := by
    cases b <;> simpa [aggnCompareJobs] using ha
  have ha1 : ((false, row) : AggnJob) ∈ aggnPhaseJobs C.2.2.2.length C := aggnJob_mem.mpr hmem.1
  have ha2 : ((false, row') : AggnJob) ∈ aggnPhaseJobs C.2.2.2.length C :=
    aggnJob_mem.mpr hmem.2
  have hc := aggnJobCtx h.ctx ha1
  have d1 := aggnJob_data h.ctx ha1
  have d2 := aggnJob_data h.ctx ha2
  have h8 := h.large.eight_lt
  obtain ⟨r, hr, -, hm⟩ := aggnTransport_spec h.action h.setting.giant d1.1 d2.1 d1.2.1 d2.2.1
    (d1.2.2.1.trans d2.2.2.1.symm) (by change 2 ≤ row.length; rw [d1.2.2.1]; omega)
  obtain ⟨hσ, hmap⟩ := hm.1
  have hQ0 : decCoset n (some (topStab (C.1, row), r)) =
      decPerm n r • (bigGT ϕ (winSet m row) : Set (Perm (Fin n))) := by
    rw [decCoset_some, topStab_bigGT_of_wf (C.1, row) ϕ h.action h.setting.giant]
  have hq0 : decCoset n (some (topStab (C.1, row), r)) =
      pcTransporters ϕ (winSet m row) (winSet m row') := by
    rw [hQ0, pcTransporters, transporter_eq_smul hσ (by rw [← testImage_def]; exact hmap)]
  have hz : aggnCompareCtx C (b, row, row') =
      (((C.2.1, row), aggnInitialState (C.1, row)), cond b C.2.2.1 C.2.1,
        some (topStab (C.1, row), r)) := by
    simp only [aggnCompareCtx, aggnPairPrepare, hr, Option.map_some]
  have hy : (cond b C.2.2.1 C.2.1).length = n := by
    cases b
    · exact h.source
    · exact h.target
  have h0 := aggnInitialState_for hc h.action h.setting.giant
  have hT : (winSet m row).ncard = row.length := ncard_winSet row d1.1 d1.2.1
  have hT' : (winSet m row').ncard = row'.length := ncard_winSet row' d2.1 d2.2.1
  rw [hz]
  refine ⟨⟨hc, hy, h0, ⟨winSet m row', hq0⟩, d1.2.2.1⟩, ?_⟩
  haveI := h.nonempty
  have hlk : LargeK (winSet m row).ncard (Nat.card (Fin n)) := by
    rw [hT, d1.2.2.1]; exact h.largeK
  have htm : 10 * (winSet m row).ncard ≤ Nat.card (Fin m) := by
    rw [hT, d1.2.2.1, Nat.card_fin]; exact h.small'
  have hTT : (winSet m row').ncard = (winSet m row).ncard := by
    rw [hT, hT', d1.2.2.1, d2.2.2.1]
  have hv := (proposition_13_1_11_ram_spec hc hy h.setting hlk htm hTT h0 hq0 ansQ hQ).1
  exact hv.trans (by cases b <;> rfl)

theorem a13_certRuns (h : A13Hyp n m C ϕ) :
    ∀ p ∈ (a13Prep C).2.1, CertRunInput ϕ C.2.2.2.length p := by
  rw [a13_l1 h]
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  exact a13_certRun h ha

theorem a13_compareRuns (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    ∀ z ∈ (a13Prep C).2.2, CompareRunInput ϕ C.2.2.2.length z := by
  rw [a13_l2 h]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  exact (a13_compareRun h ha ansQ hQ).1

theorem a13Writes_map (C : AggnPhaseCtx) (jobs : List AggnJob) (g : AggnJob → RawLCOut) :
    a13Writes (C, jobs, jobs.map g) =
      jobs.map (fun a => (a, aggPack ((aggnJobLoop C a).1.1, a.2, g a))) := by
  unfold a13Writes
  rw [zip_map_self, List.map_map]
  rfl

/-- The entry of one certificate run is the paper's certificate of fullness or of
non-fullness, by Theorem 13.1.3. -/
theorem a13_entry (h : A13Hyp n m C ϕ) {a : AggnJob}
    (ha : a ∈ aggnPhaseJobs C.2.2.2.length C) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    AggnEntryFor ϕ (a, aggPack ((aggnJobLoop C a).1.1, a.2,
      lcOut (lcSolveQ ansQ) (aggnJobLoop C a))) := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  have hc := aggnJobCtx h.ctx ha
  have h0 := aggnInitialState_for hc h.action h.setting.giant
  have hs := stateFor_out hsolve h0
  have hfst := lcRun_fst (solve := lcSolveQ ansQ) (xs := (aggnJobLoop C a).1.1) (tdom := a.2)
    (st0 := aggnInitialState (C.1, a.2))
  have e : lcOut (lcSolveQ ansQ) (aggnJobLoop C a) =
      lcOutOf ((aggnJobLoop C a).1, (lcRun (lcSolveQ ansQ) (aggnJobLoop C a)).2) := by
    rw [lcwOut_eq]
    exact congrArg lcOutOf (Prod.ext hfst rfl)
  rw [e]
  exact aggnEntryFor_outStage h.ctx h.largeK h.small' ha hs

/-- **The stores of the certificate phase are complete and correct**: the proof of
Theorem 13.2.1, "Run the LocalCertificates routine for both inputs `x`, `y` and all test
sets `T`". -/
theorem a13_stores (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    AggnStoresComplete C.2.2.2.length ϕ (a13StateOf ansQ C).1.2.1 := by
  set c := C.2.2.2.length with hcdef
  set writes := a13Writes (C, (a13Prep C).1.2.1, (a13Phases ansQ C).1) with hwdef
  have hst : (a13StateOf ansQ C).1.2.1 = aggnApplyEntries writes ([], []) := by
    rw [← a13Stores_eq]; rfl
  have hwrites : writes = (aggnPhaseJobs c C).map (fun a => (a, aggPack ((aggnJobLoop C a).1.1,
      a.2, lcOut (lcSolveQ ansQ) (aggnJobLoop C a)))) := by
    rw [hwdef]
    have e1 : (a13Phases ansQ C).1 =
        (aggnPhaseJobs c C).map (fun a => lcOut (lcSolveQ ansQ) (aggnJobLoop C a)) := by
      show (a13Prep C).2.1.map _ = _
      rw [a13_l1 h, List.map_map]; rfl
    rw [e1, a13_jobs h, a13Writes_map]
  have hkeys : writes.map Prod.fst = aggnPhaseJobs c C := by
    rw [hwrites, List.map_map]; exact List.map_id _
  have hw : ∀ w ∈ writes, AggnEntryFor ϕ w := by
    intro w hwm
    rw [hwrites] at hwm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hwm
    exact a13_entry h ha ansQ hQ
  rw [hst]
  intro b
  have hname : (aggnStoreAt (aggnApplyEntries writes ([], [])) b).map Prod.fst =
      (aggnPhaseRows c C).reverse := by
    rw [aggnApplyEntries_at]
    simp only [aggnStoreAt, Bool.cond_self, List.append_nil, List.map_reverse]
    rw [aggnWritesAt_keys hkeys (fun w h => (hw w h).1), aggnPhaseJobs_at]
  have hentries : ∀ e ∈ aggnStoreAt (aggnApplyEntries writes ([], [])) b,
      AggCertFor ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length e := by
    intro e he
    rw [aggnApplyEntries_at] at he
    simp only [aggnStoreAt, Bool.cond_self, List.append_nil, List.mem_reverse] at he
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp he
    obtain ⟨hmem, hb⟩ := List.mem_filter.mp hw'
    have hc := (hw w hmem).2
    have hb' : w.1.1 = b := beq_iff_eq.mp hb
    cases b <;> simpa only [aggnJobLoop, hb', Bool.cond_false, Bool.cond_true] using hc
  have hC := h.ctx
  refine ⟨⟨?_, hentries⟩, ?_, hname⟩
  · rw [hname]
    exact List.nodup_reverse.mpr (aggNodup_testSetsOn (gdom := C.1.2.1) hC.guard)
  · intro T hT
    have hm : C.1.2.1.length ≤ C.2.1.length := by
      rw [hC.action.2.1, hC.source]; exact hC.degree
    have hr : aggName T ∈ aggnPhaseRows c C := by
      apply (aggMem_testSetsOn hC.guard hm).mpr
      exact ⟨(aggName_length T).trans hT, aggName_normal T C.1.2.1 hC.action.2.1⟩
    have hr' : aggName T ∈ (aggnStoreAt (aggnApplyEntries writes ([], [])) b).map Prod.fst := by
      rw [hname]; exact List.mem_reverse.mpr hr
    obtain ⟨e, he, hrow⟩ := List.mem_map.mp hr'
    exact ⟨e, he, hrow ▸ aggName_spec T⟩

theorem a13_tableEq (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset) :
    (a13Mid ansQ C).1.2 = aggnCompareTable C.2.2.2.length (C, (a13StateOf ansQ C).2.2.2.1) := by
  show (a13Prep C).1.2.2.zip (a13Phases ansQ C).2 =
    (aggnCompareJobs C.2.2.2.length C).zip ((a13Phases ansQ C).2.reverse.reverse)
  rw [List.reverse_reverse, a13_cjobs h]

/-- **The table of the comparison phase is correct**: the proof of Theorem 13.2.1, "Run the
CompareLocalCertificates routine for all pairs `((x, T), (x', T'))`". -/
theorem a13_table (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    AggnCompareTableFor C.2.2.2.length ϕ
      (aggnCompareTable C.2.2.2.length (C, (a13StateOf ansQ C).2.2.2.1)) := by
  rw [← a13_tableEq h]
  have e : (a13Mid ansQ C).1.2 = (aggnCompareJobs C.2.2.2.length C).map
      (fun a => (a, pcOut (lcSolveQ ansQ) (aggnCompareCtx C a))) := by
    show (a13Prep C).1.2.2.zip ((a13Prep C).2.2.map _) = _
    rw [a13_l2 h, a13_cjobs h, List.map_map, zip_map_self]
    rfl
  rw [e]
  refine ⟨by rw [List.map_map]; exact List.map_id _, ?_⟩
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact (a13_compareRun h ha ansQ hQ).2

/-- **Theorem 13.2.1, the output**: the routine's output is `Algo.a13Report` of the state
after the two phases, with the chain's local guide at `c = t`. -/
theorem a13Result_eq (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset) :
    a13Result ansQ C = a13Report ((C, a13StateOf ansQ C),
      aggnAggregateGuide C.2.2.2.length (C, a13StateOf ansQ C)) := by
  have e1 : (a13Mid ansQ C).1 = ((C, a13StateOf ansQ C),
      aggnCompareTable C.2.2.2.length (C, (a13StateOf ansQ C).2.2.2.1)) :=
    Prod.ext rfl (a13_tableEq h ansQ)
  have e2 : a13TabsOf (a13Mid ansQ C) = a13GuideTabs (C, a13StateOf ansQ C) := rfl
  rw [a13Result, a13Final, e2, e1]
  simp only
  rw [a13Guide_eq_of_table (C, a13StateOf ansQ C) h.guard]

/-- **Theorem 13.2.1, the calls**: at most `Babai.aggregateRoundCost m t n` calls (the
paper's `C(m,t)` runs of LocalCertificates for each of `x`, `y` and `2·C(m,t)²` runs of
CompareLocalCertificates, each with at most `t!·n²` calls), each on a window of at most
`n/t` points. -/
theorem a13_calls (h : A13Hyp n m C ϕ) (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    (a13Calls ansQ C).length ≤ aggregateRoundCost m C.2.2.2.length n ∧
      ∀ W ∈ a13Calls ansQ C, WinWF n W ∧ C.2.2.2.length * W.1.length ≤ n := by
  have h8 := h.large.eight_lt
  have hsp := theorem_13_2_1_phases_ram_spec (by omega) (a13_certRuns h)
    (a13_compareRuns h ansQ hQ) ansQ hQ
  have hC := h.ctx
  have hm : C.1.2.1.length ≤ C.2.1.length := by
    rw [hC.action.2.1, hC.source]; exact hC.degree
  have hrows : (aggnPhaseRows C.2.2.2.length C).length = m.choose C.2.2.2.length := by
    have := aggLength_testSetsOn hC.guard hm
    rw [hC.action.2.1] at this
    exact this
  have hl1 : (a13Prep C).2.1.length ≤ 2 * m.choose C.2.2.2.length := by
    rw [a13_l1 h, List.length_map]
    simp [aggnPhaseJobs, hrows]
    omega
  have hl2 : (a13Prep C).2.2.length ≤ 2 * (m.choose C.2.2.2.length) ^ 2 := by
    rw [a13_l2 h, List.length_map]
    simp [aggnCompareJobs, List.length_flatMap, hrows, List.map_const', List.sum_replicate]
    ring_nf
    omega
  exact ⟨hsp.2.2 hl1 hl2, hsp.2.1⟩

end Correct

/-! ### What each exit and each output means -/

section Report

variable {n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
  {s : AggnAggregateState}

/-- `F(z)`, `F(z)^Γ` and `D(z)` for `z = x` (`b = false`) and `z = y` (`b = true`). -/
theorem a13_data (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (b : Bool) :
    decGroup n (aggnAggregateData ((C, s), b)).1 =
        bigF ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
    decGroup m (aggnAggregateData ((C, s), b)).2.1 =
        bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
    winSet m (aggnAggregateData ((C, s), b)).2.2 =
        fixedGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length :=
  aggnAggregateData_spec h.ctx hs b

/-- The orbit partition of `F(z)^Γ` (the output of case (1)) and the large orbit of
`F(z)^Γ` (the orbit `C` of case (2)). -/
theorem a13_partition_majority (h : A13Hyp n m C ϕ)
    (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1) (b : Bool) :
    aggnDecodePartition m (aggnAggregatePartition ((C, s), b)) =
        orbitSplitOutcome (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
          C.2.2.2.length) ∧
      winSet m (aggnAggregateMajority ((C, s), b)) =
        colorClass (bigOrbitColoring ϕ C.2.2.2.length)
          (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) true :=
  ⟨aggnAggregatePartition_spec h.ctx hs b, aggnAggregateMajority_spec h.ctx hs b⟩

/-- **Exit `1`, case (1)**: taken exactly when `F(x)^Γ` is in case (1); the output is the
colored 4/5-partition of `Γ`. -/
theorem a13_tag_one (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (g : Option (AmbientPIn × AmbientPIn)) :
    (a13Tag ((C, s), g) = 1 ↔ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length)) ∧
      (a13Tag ((C, s), g) = 1 → IsSplitOutcome (4 / 5 : ℝ) (Set.univ : Set (Fin m))
        (aggnDecodePartition m (aggnAggregatePartition ((C, s), false)))) := by
  have e : a13Tag ((C, s), g) = 1 ↔ aggnAggregateDispatch (C, s) = 1 := by
    unfold a13Tag
    split_ifs <;> simp_all
  have hd := aggnAggregateDispatch_spec h.ctx hs
  rw [e]
  exact ⟨hd.1, aggnAggregatePartition_output h.ctx hs⟩

/-- **Exit `2`, case (2a)**: taken exactly when `F(x)^Γ` has an orbit of more than `4m/5`
points on which it acts as a giant; the output is the hypothesis of Corollary 12.0.10
(`Algo.aggnAggregateGiantBranch_spec`, `Babai.AggregateCase2a`). -/
theorem a13_tag_two (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (g : Option (AmbientPIn × AmbientPIn)) :
    a13Tag ((C, s), g) = 2 ↔ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length := by
  have e : a13Tag ((C, s), g) = 2 ↔
      aggnAggregateDispatch (C, s) = 2 ∧ aggnAggregateGiantBranch (C, s) = true := by
    unfold a13Tag
    split_ifs <;> simp_all
  have hd := aggnAggregateDispatch_spec h.ctx hs
  have hg := aggnAggregateGiantBranch_spec h.ctx hs
  rw [e, hd.2.1, hg]

/-- **Exit `0`**: in case (2) with `F(x)^Γ` not a giant on its large orbit, the case test of
(2b) fails at `y`; then `Iso_G(x, y) = ∅`. -/
theorem a13_tag_zero (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (g : Option (AmbientPIn × AmbientPIn)) (h0 : a13Tag ((C, s), g) = 0) :
    ((Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
        ¬ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ (Case2 (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) ∧
        ¬ AggregateCase2a ϕ (decStrN n C.2.2.1) C.2.2.2.length)) ∧
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ := by
  have hr : aggnRejectCase (C, s) = true := by
    unfold a13Tag at h0
    split_ifs at h0 with h1 h2 h3 h4 h5 h6 <;> first | omega | assumption
  exact ⟨(aggnRejectCase_spec h.ctx hs).mp hr, aggnRejectCase_iso h.ctx hs hr⟩

/-- **Exit `3`, case (2b)**: both `x` and `y` are in case (2) with no giant action on the
large orbit; for both, the output is the family of case (2b) (`Babai.case2bFamily`). -/
theorem a13_tag_three (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (g : Option (AmbientPIn × AmbientPIn)) (h3 : a13Tag ((C, s), g) = 3) :
    (∀ b : Bool, Case2 (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
        C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length) ∧
    ∀ b : Bool, {q | ∃ r ∈ aggnAggregateCase2b ((C, s), b), aggnDecodeConstituent m r = q} =
      case2bFamily (bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1))
        C.2.2.2.length) := by
  have hC := h.ctx
  have hside : ∀ b : Bool, aggnSideCase2b ((C, s), b) = true := by
    have hx : aggnSideCase2b ((C, s), false) = true ∧ aggnRejectCase (C, s) = false := by
      unfold a13Tag at h3
      split_ifs at h3 with h1 h2 h4 h5 <;> try omega
      refine ⟨?_, by simpa using h5⟩
      have hd2 : aggnAggregateDispatch (C, s) = 2 := by simpa using h2
      obtain ⟨t2, t2a⟩ := aggnAggregate_case2b_tests hC hd2 (by simpa using h4)
      simp only [aggnSideCase2b, aggnAggregateImage] at t2 t2a ⊢
      rw [t2, t2a]; rfl
    intro b
    cases b
    · exact hx.1
    · have := hx.2
      simp only [aggnRejectCase, hx.1, Bool.true_and, Bool.not_eq_false'] at this
      exact this
  refine ⟨fun b => (aggnSideCase2b_spec hC hs b).mp (hside b), fun b => ?_⟩
  have hb := hside b
  simp only [aggnSideCase2b, Bool.and_eq_true, Bool.not_eq_true'] at hb
  have hw : RawGens.WF m (aggnAggregateData ((C, s), b)).2.1 := wf_tidyGens hC.action.2.1 _
  have h6 : 6 ≤ (aggnLargeOrbitPoints (aggnAggregateImage ((C, s), b))).length := by
    have := h.small
    have := h.large.eight_lt
    obtain ⟨_, _, h⟩ := aggnLargeOrbitPoints_orbit hC.action.2.1 hw hb.1
    change 6 ≤ (aggnLargeOrbitPoints (C.1.2.1, (aggnAggregateData ((C, s), b)).2.1)).length
    omega
  rw [← (aggnAggregateData_spec hC hs b).2.1]
  exact aggnCase2bFamily_spec hC.action.2.1 hw hb.1 hb.2 h6

/-- **Exit `5`**: in case (3), `|D(y)| ≠ |D(x)|`; then `Iso_G(x, y) = ∅`. -/
theorem a13_tag_five (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (g : Option (AmbientPIn × AmbientPIn)) (h5 : a13Tag ((C, s), g) = 5) :
    ¬ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard ≠
        (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard ∧
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ := by
  have hd := aggnAggregateDispatch_spec h.ctx hs
  unfold a13Tag at h5
  split_ifs at h5 with h1 h2 h3 h4 h6 h7 <;> try omega
  have hr : aggnRejectDefect (C, s) = true := h6
  have h1' : aggnAggregateDispatch (C, s) ≠ 1 := by simpa using h1
  have h2' : aggnAggregateDispatch (C, s) ≠ 2 := by simpa using h2
  exact ⟨fun hc => h1' (hd.1.mpr hc), fun hc => h2' (hd.2.1.mpr hc),
    (aggnRejectDefect_spec h.ctx hs).mp hr, aggnRejectDefect_iso h.ctx hs hr⟩

section Guide

variable (htbl : AggnCompareTableFor C.2.2.2.length ϕ
  (aggnCompareTable C.2.2.2.length (C, s.2.2.2.1)))

include htbl in
/-- **Exit `6`**: in case (3) with `|D(x)| = |D(y)|`, the local guide finds no match; then
`Iso_G(x, y) = ∅` (the Local guide proposition). -/
theorem a13_tag_six (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (h6 : a13Tag ((C, s), aggnAggregateGuide C.2.2.2.length (C, s)) = 6) :
    ¬ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
    strIso (decGroup n C.1.1.2 : Set (Perm (Fin n))) (decStrN n C.2.1) (decStrN n C.2.2.1) = ∅ := by
  have hd := aggnAggregateDispatch_spec h.ctx hs
  haveI := h.nonempty
  unfold a13Tag at h6
  split_ifs at h6 with h1 h2 h3 h4 h5 h7 <;> try omega
  have h1' : aggnAggregateDispatch (C, s) ≠ 1 := by simpa using h1
  have h2' : aggnAggregateDispatch (C, s) ≠ 2 := by simpa using h2
  have hno : aggnAggregateGuide C.2.2.2.length (C, s) = none := by
    simpa using h7
  exact ⟨fun hc => h1' (hd.1.mpr hc), fun hc => h2' (hd.2.1.mpr hc),
    aggnAggregateGuide_reject h.ctx hs htbl h.setting h.largeK h.small' hno⟩

/-- **Exit `4`, case (3)**: `4m < 5|D(x)|`, and the output is the pair of canonical `t`-ary
relational structures on `D(x)` and `D(y)` built by the local guide
(`Algo.aggnGuideNumberedStruct`, the Claim in the proof of case (3)). -/
theorem a13_tag_four (h : A13Hyp n m C ϕ) (hs : AggnStoresComplete C.2.2.2.length ϕ s.1.2.1)
    (h4 : a13Tag ((C, s), aggnAggregateGuide C.2.2.2.length (C, s)) = 4) :
    ¬ Case1 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ∃ out, aggnAggregateGuide C.2.2.2.length (C, s) = some out ∧ ∀ b : Bool,
        decRel (aggnAggregateData ((C, s), b)).2.2.length C.2.2.2.length (cond b out.2 out.1).2 =
          (aggnGuideNumberedStruct (c := C.2.2.2.length) (C := C) (s := s)
            (tbl := aggnCompareTable C.2.2.2.length (C, s.2.2.2.1)) b).toKAry (fun _ => rfl) := by
  have hd := aggnAggregateDispatch_spec h.ctx hs
  unfold a13Tag at h4
  split_ifs at h4 with h1 h2 h3 h5 h6 h7 <;> try omega
  have h1' : aggnAggregateDispatch (C, s) ≠ 1 := by simpa using h1
  have h2' : aggnAggregateDispatch (C, s) ≠ 2 := by simpa using h2
  obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp h7
  exact ⟨fun hc => h1' (hd.1.mpr hc), fun hc => h2' (hd.2.1.mpr hc), out, hout,
    aggnAggregateGuide_decode hout⟩

end Guide

/-- The exits are the seven listed. -/
theorem a13Tag_le (p : (AggnPhaseCtx × AggnAggregateState) × Option (AmbientPIn × AmbientPIn)) :
    a13Tag p ≤ 6 := by
  unfold a13Tag
  split_ifs <;> omega

end Report

end Algo
