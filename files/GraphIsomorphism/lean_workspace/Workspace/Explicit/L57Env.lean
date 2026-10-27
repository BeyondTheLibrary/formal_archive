/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the size invariant of the two
phases of Procedure AggregateCertificates (Sec. 13.2) with short loops. Not part of the
faithful formalization.
-/
import Workspace.Explicit.L57Compare
import Workspace.Algo.AggNodePhaseBound
import Workspace.Algo.AggNodeCompareBound

/-!
# The size invariant of the two phases, with short loops

`Algo.AggnPhaseBound` and `Algo.AggnCompareBound` bound the states of the two phases along
any sequence of answers, through envelopes (`Algo.AggnStateEnvelope`,
`Algo.AggnCompareEnvelope`) whose cache field bounds the recomputation input of *every* loop
within the size envelope. That input is a guarded tuple table whose cost grows with the length
of the loop's string, so such a cache has no explicit exponent at the degree.

Here the same invariants are restated with one more clause: every loop of the state is short
(`Explicit.LoopOK n`, its string has at most `n` letters). The envelopes (`Explicit.PhaseEnv`,
`Explicit.CompEnv`) then only bound the recomputation input of short loops, which
`Explicit.TN.aggnrInputOf` and `Explicit.TN.aggnPairInput` bound at the degree. The proofs are
those of `Workspace/Algo/AggNodeStateBounds.lean`, `AggNodePhaseBound.lean`,
`AggNodePairBound.lean` and `AggNodeCompareBound.lean`, with the clause carried along (the
loops of the states are the job loops, the empty loop and their steps, `Explicit.loopOK_jobLoop`,
`Explicit.loopOK_empty`, `Explicit.loopOK_stepWith`).
-/

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem cons_size {α : Type*} [Enc α] (a : α) (l : List α) :
    Enc.size (a :: l) ≤ 2 * Enc.size a + Enc.size l := by
  rw [size_cons_eq, listSize_frame]
  have h := size_le_self (Enc.encode a).length
  have h' := length_lt_listSize (Enc.encode a)
  change (Enc.size a + (Nat.size (Enc.encode a).length + 1) + Enc.size l - 1) ≤ _
  change (Enc.encode a).length < Enc.size a at h'
  omega

private theorem nat_size_le {a b : ℕ} (h : a ≤ b) : Enc.size a ≤ b + 2 := by
  rw [Small.size_nat]
  have := size_le_self a
  omega

/-! ## The certificate phase -/

/-- The envelope of the certificate phase at degree `n` (`Algo.AggnStateEnvelope`, with the
cache bound asked only of short loops). -/
structure PhaseEnv (c n : ℕ) (C : AggnPhaseCtx) where
  base : ℕ
  loopState : ℕ
  cache : ℕ
  coset : ℕ
  entry : ℕ
  ctx_ok : CtxOK n C
  context_le : Enc.size C ≤ base
  jobs_le : Enc.size (aggnPhaseJobs c C) ≤ base
  open_le : ∀ a ∈ aggnPhaseJobs c C, AggnLoopBound base loopState (aggnJobLoop C a)
  empty_le : AggnLoopBound base loopState (([], []), ([], [], []))
  step_le : lcStBound base ≤ loopState
  cache_le : ∀ p, LoopOK n p → AggnLoopBound base loopState p →
    Enc.size (aggnrInputOf c p) ≤ cache
  coset_le : 4 * cache + chainBound base + 4 ≤ coset
  entry_le : ∀ a ∈ aggnPhaseJobs c C, ∀ p, AggnLoopBound base loopState p →
    Enc.size (aggnLoopEntry (a, p)) ≤ entry

variable {c n : ℕ} {C : AggnPhaseCtx}

/-- `Algo.AggnCertBound` with a short loop. -/
def CertB (B : PhaseEnv c n C) (j : ℕ) (v : AggnCertState) : Prop :=
  LoopOK n v.1 ∧ AggnLoopBound B.base B.loopState v.1 ∧ v.2.1 = aggnrInputOf c v.1 ∧
    v.2.2.1 ≤ j ∧ AggnRecomputeBound B.cache B.coset v.2.2.2

theorem CertB.open (B : PhaseEnv c n C) {p : RawLCLoop} (hl : LoopOK n p)
    (h : AggnLoopBound B.base B.loopState p) (j : ℕ) : CertB B j (aggnCertOpen c p) :=
  ⟨hl, h, rfl, Nat.zero_le _, aggnInit_bound (B.cache_le p hl h) (by have := B.coset_le; omega)⟩

theorem CertB.mono {B : PhaseEnv c n C} {j k : ℕ} {v : AggnCertState} (h : CertB B j v)
    (hjk : j ≤ k) : CertB B k v := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hjk, h.2.2.2.2⟩

theorem CertB.combine {B : PhaseEnv c n C} {j : ℕ} {v : AggnCertState} (h : CertB B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (p : AggnCertNode) (i : ℕ) :
    CertB B (j + 1) (aggnCertCombine c (p, i, v, ans)) := by
  obtain ⟨hl, h1, h2, h3, h4⟩ := h
  have hp : Enc.size v.2.1 ≤ B.cache := h2 ▸ B.cache_le v.1 hl h1
  have hx : v.2.1.1.2.2.2.1.length ≤ B.base := by
    rw [h2]
    exact (lcDeg_le v.1).trans h1.1
  have hs := aggnStep_bound hp hx (by have := B.coset_le; omega)
    (by have := B.coset_le; omega) h4.2.2.2 ha v.2.2.2.1 v.2.2.2.2.1
  change CertB B (j + 1) (aggnCertPack c v.1 (v.2.2.1 + 1)
    (aggnrStep v.2.1 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2.2 ans))
  unfold aggnCertPack
  split
  · exact ⟨hl, h1, rfl, Nat.add_le_add_right h3 1, hs⟩
  · exact CertB.open B (loopOK_stepWith hl _) (h1.step B.step_le _) _

theorem CertB.size {B : PhaseEnv c n C} {j : ℕ} {v : AggnCertState} (h : CertB B j v) :
    Enc.size v ≤ 4 * B.base + 4 * B.loopState + 52 * B.cache +
      128 * B.coset + 8 * j + 112 := by
  have hp := h.2.1.size
  have hP : Enc.size v.2.1 ≤ B.cache := h.2.2.1 ▸ B.cache_le v.1 h.1 h.2.1
  have hj := nat_size_le h.2.2.2.1
  have ht := nat_size_le h.2.2.2.2.1
  have hi := nat_size_le h.2.2.2.2.2.1
  have ha := h.2.2.2.2.2.2.1
  have hb := h.2.2.2.2.2.2.2
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 :=
    Combine.size_pair_le _ _
  have h3 : Enc.size v.2.2.2 ≤ 2 * Enc.size v.2.2.2.1 + 2 * Enc.size v.2.2.2.2 :=
    Combine.size_pair_le _ _
  have h4 : Enc.size v.2.2.2.2 ≤ 2 * Enc.size v.2.2.2.2.1 + 2 * Enc.size v.2.2.2.2.2 :=
    Combine.size_pair_le _ _
  have h5 : Enc.size v.2.2.2.2.2 ≤ 2 * Enc.size v.2.2.2.2.2.1 + 2 * Enc.size v.2.2.2.2.2.2 :=
    Combine.size_pair_le _ _
  omega

/-- `Algo.AggnPhaseBound` with short loops. -/
def PhaseB (B : PhaseEnv c n C) (j : ℕ) (v : AggnPhaseState) : Prop :=
  v.1 ⊆ aggnPhaseJobs c C ∧ Enc.size v.1 ≤ B.base ∧
    aggnStoresSize v.2.1 + 2 * B.entry * v.1.length ≤
      2 + 2 * B.entry * (aggnPhaseJobs c C).length ∧
    v.2.2.1 ≤ j ∧ CertB B j v.2.2.2

theorem PhaseB.mono {B : PhaseEnv c n C} {j k : ℕ} {v : AggnPhaseState} (h : PhaseB B j v)
    (hjk : j ≤ k) : PhaseB B k v :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hjk, h.2.2.2.2.mono hjk⟩

private theorem storeJob_size {B : PhaseEnv c n C} {a : AggnJob} (ha : a ∈ aggnPhaseJobs c C)
    {v : AggnCertState} (hv : AggnLoopBound B.base B.loopState v.1) (stores : AggnStores) :
    aggnStoresSize (aggnStoreJob a v stores) ≤ aggnStoresSize stores + 2 * B.entry := by
  have he := B.entry_le a ha v.1 hv
  have h1 := cons_size (aggnLoopEntry (a, v.1)) stores.1
  have h2 := cons_size (aggnLoopEntry (a, v.1)) stores.2
  unfold aggnStoreJob aggnStoresSize
  cases a.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    change Enc.size _ + Enc.size _ ≤ _ <;>
    dsimp only [aggnLoopEntry, aggnCertOut] at he h1 h2 ⊢ <;> omega

/-- The scan keeps the invariant (`Algo.aggnPhaseBound_scan`). -/
theorem phaseB_scan (B : PhaseEnv c n C) :
    ∀ jobs stores j, jobs ⊆ aggnPhaseJobs c C → Enc.size jobs ≤ B.base →
      aggnStoresSize stores + 2 * B.entry * jobs.length ≤
        2 + 2 * B.entry * (aggnPhaseJobs c C).length →
      PhaseB B j (aggnPhaseScan c C jobs stores) := by
  intro jobs
  induction jobs with
  | nil =>
    intro stores j hsub hsize hpot
    exact ⟨hsub, hsize, hpot, Nat.zero_le _, CertB.open B (loopOK_empty n) B.empty_le j⟩
  | cons a rest ih =>
    intro stores j hsub hsize hpot
    have ha := hsub List.mem_cons_self
    have hv := CertB.open B (loopOK_jobLoop B.ctx_ok a) (B.open_le a ha) j
    simp only [aggnPhaseScan]
    split
    · exact ⟨hsub, hsize, hpot, Nat.zero_le _, hv⟩
    · apply ih _ j (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := storeJob_size ha hv.2.1 stores
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- The start of the certificate phase (`Algo.aggnPhaseBound_init`). -/
theorem phaseB_init (B : PhaseEnv c n C) :
    PhaseB B 0 ((aggnCheckedRound c 0).init (C, none)) := by
  apply phaseB_scan B _ _ _ (List.Subset.refl _) B.jobs_le
  simp [aggnStoresSize, size_nil]

/-- One more bounded answer (`Algo.AggnPhaseBound.combine`). -/
theorem PhaseB.combine {B : PhaseEnv c n C} {j : ℕ} {v : AggnPhaseState} (h : PhaseB B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    PhaseB B (j + 1) (aggnPhaseCombine c (I, i, v, ans)) := by
  obtain ⟨jobs, stores, k, core⟩ := v
  obtain ⟨hsub, hsize, hpot, hk, hv⟩ := h
  dsimp only at hsub hsize hpot hk hv
  cases jobs with
  | nil =>
    change PhaseB B (j + 1) (aggnPhaseScan c I.1 [] stores)
    rw [hI]
    exact phaseB_scan B [] stores _ hsub hsize hpot
  | cons a rest =>
    have hcore := hv.combine ha ((aggnJobLoop C a, none)) k
    change PhaseB B (j + 1) (aggnPhasePack c I.1 a rest stores (k + 1)
      (aggnCertCombine c ((aggnJobLoop I.1 a, none), k, core, ans)))
    rw [hI]
    generalize hnew : aggnCertCombine c ((aggnJobLoop C a, none), k, core, ans) = next
      at hcore ⊢
    unfold aggnPhasePack
    split
    · exact ⟨hsub, hsize, hpot, Nat.add_le_add_right hk 1, hcore⟩
    · apply phaseB_scan B _ _ _ (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := storeJob_size (hsub List.mem_cons_self) hcore.2.1 stores
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- A normalized answer (`Algo.AggnPhaseBound.combine_norm`). -/
theorem PhaseB.combine_norm {B : PhaseEnv c n C} {j : ℕ} {v : AggnPhaseState}
    (h : PhaseB B j v) (ans : RawCoset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    PhaseB B (j + 1) (aggnPhaseCombine c (I, i, v, aggnNormAnswer C.2.1 ans)) := by
  apply h.combine (I := I) (i := i) ?_ hI
  apply (aggnNormAnswer_size ((length_le_size C.2.1).trans
    (((size_fst_le' C.2).trans (size_snd_le' C)).trans B.context_le)) ans).trans
  have := B.coset_le
  omega

/-- The size bound of `Algo.aggnEnvelopeBound`. -/
def phaseEnvBound (B : PhaseEnv c n C) (j : ℕ) : ℕ :=
  2048 * (B.base + B.loopState + B.cache + B.coset + (2 + 2 * B.entry * B.base) + j + 1)

theorem PhaseB.size {B : PhaseEnv c n C} {j : ℕ} {v : AggnPhaseState} (h : PhaseB B j v) :
    Enc.size v ≤ phaseEnvBound B j := by
  have hj := nat_size_le h.2.2.2.1
  have hc := h.2.2.2.2.size
  have hn := Nat.mul_le_mul_left (2 * B.entry)
    ((length_le_size (aggnPhaseJobs c C)).trans B.jobs_le)
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 :=
    Combine.size_pair_le _ _
  have hs : Enc.size v.2.1 ≤ 2 * Enc.size v.2.1.1 + 2 * Enc.size v.2.1.2 :=
    Combine.size_pair_le _ _
  obtain ⟨_, hsize, hpot, _, _⟩ := h
  unfold aggnStoresSize at hpot
  unfold phaseEnvBound
  omega

/-- The state of the certificate phase keeps its loop short. -/
theorem PhaseB.stOK {B : PhaseEnv c n C} {j : ℕ} {v : AggnPhaseState} (h : PhaseB B j v) :
    PhaseStOK n v := h.2.2.2.2.1

/-! ## The comparison phase -/

/-- The envelope of the comparison phase at degree `n` (`Algo.AggnCompareEnvelope`, with the
cache bound asked only of short loops). -/
structure CompEnv (c n : ℕ) (C : AggnPhaseCtx) where
  base : ℕ
  loopState : ℕ
  cache : ℕ
  coset : ℕ
  ctx_ok : CtxOK n C
  context_le : Enc.size C ≤ base
  jobs_le : Enc.size (aggnCompareJobs c C) ≤ base
  open_le : ∀ a ∈ aggnCompareJobs c C,
    AggnLoopBound base loopState (aggnCompareCtx C a).1 ∧
    Enc.size (aggnCompareCtx C a).2.1 ≤ base ∧ Enc.size (aggnCompareCtx C a).2.2 ≤ coset
  empty_le : AggnLoopBound base loopState (([], []), ([], [], []))
  empty_coset_le : Enc.size (none : RawCoset) ≤ coset
  step_le : lcStBound base ≤ loopState
  cache_le : ∀ p ys q mode, LoopOK n p → AggnLoopBound base loopState p → Enc.size ys ≤ base →
    Enc.size (aggnPairInput c p ys q mode) ≤ cache
  coset_le : 4 * cache + chainBound base + 4 ≤ coset

/-- `Algo.AggnPairBound` with a short loop. -/
def PairB (B : CompEnv c n C) (ys : RawStr) (j : ℕ) (v : AggnPairState) : Prop :=
  LoopOK n v.1 ∧ AggnLoopBound B.base B.loopState v.1 ∧ Enc.size ys ≤ B.base ∧
    Enc.size v.2.1 ≤ B.coset ∧ (∀ H, v.2.2.1 = some H → Enc.size H ≤ B.coset) ∧
    v.2.2.2.1 = aggnPairInput c v.1 ys v.2.1 v.2.2.1 ∧
    v.2.2.2.2.1 ≤ j ∧ AggnRecomputeBound B.cache B.coset v.2.2.2.2.2

theorem PairB.start (B : CompEnv c n C) {p : RawLCLoop} {ys : RawStr} {q : RawCoset}
    {mode : Option RawCoset} (hl : LoopOK n p) (hp : AggnLoopBound B.base B.loopState p)
    (hy : Enc.size ys ≤ B.base) (hq : Enc.size q ≤ B.coset)
    (hm : ∀ H, mode = some H → Enc.size H ≤ B.coset) (j : ℕ) :
    PairB B ys j (aggnPairStart c p ys q mode) :=
  ⟨hl, hp, hy, hq, hm, rfl, Nat.zero_le _, aggnInit_bound (B.cache_le p ys q mode hl hp hy)
    (by have := B.coset_le; omega)⟩

theorem PairB.mono {B : CompEnv c n C} {ys : RawStr} {j k : ℕ} {v : AggnPairState}
    (h : PairB B ys j v) (hjk : j ≤ k) : PairB B ys k v :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1.trans hjk, h.2.2.2.2.2.2.2⟩

theorem PairB.combine {B : CompEnv c n C} {ys : RawStr} {j : ℕ} {v : AggnPairState}
    (h : PairB B ys j v) {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (P : AggnPairCtx)
    (hys : P.2.1 = ys) (i : ℕ) :
    PairB B ys (j + 1) (aggnPairCombine c ((P, none), i, v, ans)) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hp : Enc.size v.2.2.2.1 ≤ B.cache :=
    h5 ▸ B.cache_le v.1 ys v.2.1 v.2.2.1 hl h1 h2
  have hx : v.2.2.2.1.1.2.2.2.1.length ≤ B.base := by
    rw [h5, aggnPairInput_source]
    exact (length_le_size v.1.1.1).trans ((size_fst_le' v.1.1).trans h1.1)
  have hs := aggnStep_bound hp hx (by have := B.coset_le; omega)
    (by have := B.coset_le; omega) h7.2.2.2 ha v.2.2.2.2.2.1 v.2.2.2.2.2.2.1
  change PairB B ys (j + 1) (aggnPairPack c v.1 P.2.1 v.2.1 v.2.2.1
    (v.2.2.2.2.1 + 1) (aggnrStep v.2.2.2.1 v.2.2.2.2.2.1
      v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2 ans))
  rw [hys]
  generalize hv : aggnrStep v.2.2.2.1 v.2.2.2.2.2.1 v.2.2.2.2.2.2.1
    v.2.2.2.2.2.2.2.2 ans = next at hs ⊢
  dsimp only [aggnPairPack]
  split
  · exact ⟨hl, h1, h2, h3, h4, rfl, Nat.add_le_add_right h6 1, hs⟩
  · cases hm : v.2.2.1 with
    | none =>
      exact PairB.start B hl h1 h2 h3
        (fun H he => by cases Option.some.inj he; exact hs.2.2.2) _
    | some H =>
      exact PairB.start B (loopOK_stepWith hl H) (h1.step B.step_le H) h2 hs.2.2.2
        (fun H he => by cases he) _

theorem PairB.size {B : CompEnv c n C} {ys : RawStr} {j : ℕ} {v : AggnPairState}
    (h : PairB B ys j v) :
    Enc.size v ≤ 4096 * (B.base + B.loopState + B.cache + B.coset + j + 1) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hp := h1.size
  have hm : Enc.size v.2.2.1 ≤ B.coset + 2 := by
    cases he : v.2.2.1 with
    | none => rw [size_none]; omega
    | some H => rw [size_some_eq]; have := h4 H he; omega
  have hP : Enc.size v.2.2.2.1 ≤ B.cache :=
    h5 ▸ B.cache_le v.1 ys v.2.1 v.2.2.1 hl h1 h2
  have hj := nat_size_le h6
  have ht := nat_size_le h7.1
  have hi := nat_size_le h7.2.1
  have ha := h7.2.2.1
  have hb := h7.2.2.2
  have h0 := Combine.size_pair_le v.1 v.2
  have h1 := Combine.size_pair_le v.2.1 v.2.2
  have h2 := Combine.size_pair_le v.2.2.1 v.2.2.2
  have h3 := Combine.size_pair_le v.2.2.2.1 v.2.2.2.2
  have h4 := Combine.size_pair_le v.2.2.2.2.1 v.2.2.2.2.2
  have h5 := Combine.size_pair_le v.2.2.2.2.2.1 v.2.2.2.2.2.2
  have h6 := Combine.size_pair_le v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2
  have h7 := Combine.size_pair_le v.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2
  simp only [Prod.eta] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

/-- `Algo.AggnCompareBound` with short loops. -/
def CompB (B : CompEnv c n C) (j : ℕ) (v : AggnCompareState) : Prop :=
  v.1 ⊆ aggnCompareJobs c C ∧ Enc.size v.1 ≤ B.base ∧
    Enc.size v.2.1 + 2 * B.coset * v.1.length ≤
      1 + 2 * B.coset * (aggnCompareJobs c C).length ∧
    v.2.2.1 ≤ j ∧ PairB B (aggnCompareTarget C v.1) j v.2.2.2

theorem CompB.mono {B : CompEnv c n C} {j k : ℕ} {v : AggnCompareState} (h : CompB B j v)
    (hjk : j ≤ k) : CompB B k v :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hjk, h.2.2.2.2.mono hjk⟩

/-- The scan keeps the invariant (`Algo.aggnCompareBound_scan`). -/
theorem compB_scan (B : CompEnv c n C) :
    ∀ jobs answers j, jobs ⊆ aggnCompareJobs c C → Enc.size jobs ≤ B.base →
      Enc.size answers + 2 * B.coset * jobs.length ≤
        1 + 2 * B.coset * (aggnCompareJobs c C).length →
      CompB B j (aggnCompareScan c C jobs answers) := by
  intro jobs
  induction jobs with
  | nil =>
    intro answers j hsub hsize hpot
    refine ⟨hsub, hsize, hpot, Nat.zero_le _, ?_⟩
    exact PairB.start B (loopOK_empty n) B.empty_le
      ((size_fst_le' (([], []) : RawStr × List ℕ)).trans B.empty_le.1)
      B.empty_coset_le (fun H he => by cases he) j
  | cons a rest ih =>
    intro answers j hsub hsize hpot
    have ha := hsub List.mem_cons_self
    have hopen := B.open_le a ha
    have hv := PairB.start B (loopOK_compareCtx B.ctx_ok a) hopen.1 hopen.2.1 hopen.2.2
      (mode := none) (fun H he => by cases he) j
    simp only [aggnCompareScan]
    split
    · exact ⟨hsub, hsize, hpot, Nat.zero_le _, hv⟩
    · apply ih _ j (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := cons_size (aggnCompareOpen c C a).2.1 answers
        have hq : Enc.size (aggnCompareOpen c C a).2.1 ≤ B.coset := hopen.2.2
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- The start of the comparison phase (`Algo.aggnCompareBound_init`). -/
theorem compB_init (B : CompEnv c n C) :
    CompB B 0 ((aggnCompareRound c 0).init (C, none)) := by
  apply compB_scan B _ _ _ (List.Subset.refl _) B.jobs_le
  simp [size_nil]

/-- One more bounded answer (`Algo.AggnCompareBound.combine`). -/
theorem CompB.combine {B : CompEnv c n C} {j : ℕ} {v : AggnCompareState} (h : CompB B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    CompB B (j + 1) (aggnCompareCombine c (I, i, v, ans)) := by
  obtain ⟨jobs, answers, k, core⟩ := v
  obtain ⟨hsub, hsize, hpot, hk, hv⟩ := h
  dsimp only at hsub hsize hpot hk hv
  cases jobs with
  | nil =>
    change CompB B (j + 1) (aggnCompareScan c I.1 [] answers)
    rw [hI]
    exact compB_scan B [] answers _ hsub hsize hpot
  | cons a rest =>
    have hcore := hv.combine ha (aggnCompareCtx C a) rfl k
    change CompB B (j + 1) (aggnComparePack c I.1 a rest answers (k + 1)
      (aggnPairCombine c ((aggnCompareCtx I.1 a, none), k, core, ans)))
    rw [hI]
    generalize hnew : aggnPairCombine c ((aggnCompareCtx C a, none), k, core, ans) = next
      at hcore ⊢
    unfold aggnComparePack
    split
    · exact ⟨hsub, hsize, hpot, Nat.add_le_add_right hk 1, hcore⟩
    · apply compB_scan B _ _ _ (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := cons_size next.2.1 answers
        have hq := hcore.2.2.2.1
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- A normalized answer (`Algo.AggnCompareBound.combine_norm`). -/
theorem CompB.combine_norm {B : CompEnv c n C} {j : ℕ} {v : AggnCompareState}
    (h : CompB B j v) (ans : RawCoset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    CompB B (j + 1) (aggnCompareCombine c (I, i, v, aggnNormAnswer C.2.1 ans)) := by
  apply h.combine (I := I) (i := i) ?_ hI
  apply (aggnNormAnswer_size ((length_le_size C.2.1).trans
    (((size_fst_le' C.2).trans (size_snd_le' C)).trans B.context_le)) ans).trans
  have := B.coset_le
  omega

/-- The size bound of `Algo.aggnCompareEnvelopeBound`. -/
def compEnvBound (B : CompEnv c n C) (j : ℕ) : ℕ :=
  65536 * (B.base + B.loopState + B.cache + B.coset + (1 + 2 * B.coset * B.base) + j + 1)

theorem CompB.size {B : CompEnv c n C} {j : ℕ} {v : AggnCompareState} (h : CompB B j v) :
    Enc.size v ≤ compEnvBound B j := by
  have hj : Enc.size v.2.2.1 ≤ j + 2 := nat_size_le h.2.2.2.1
  have hc := h.2.2.2.2.size
  have hn := Nat.mul_le_mul_left (2 * B.coset)
    ((length_le_size (aggnCompareJobs c C)).trans B.jobs_le)
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 :=
    Combine.size_pair_le _ _
  obtain ⟨_, hsize, hpot, _, _⟩ := h
  unfold compEnvBound
  omega

/-- The state of the comparison phase keeps its loop short. -/
theorem CompB.stOK {B : CompEnv c n C} {j : ℕ} {v : AggnCompareState} (h : CompB B j v) :
    CompStOK n v := h.2.2.2.2.1

end Explicit
