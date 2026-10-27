import Workspace.Algo.AggNodeStateBounds

/-! # A size invariant for every answer sequence

Each completed job pays for one stored certificate. The pending jobs stay
inside the original table, and the local cache has the uniform bounds proved
in `AggNodeStateBounds`. Only the two call counters depend on the number of
answers supplied so far.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnStoresSize (s : AggnStores) : ℕ := Enc.size s.1 + Enc.size s.2

def AggnPhaseBound {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C)
    (j : ℕ) (v : AggnPhaseState) : Prop :=
  v.1 ⊆ aggnPhaseJobs c C ∧ Enc.size v.1 ≤ B.base ∧
    aggnStoresSize v.2.1 + 2 * B.entry * v.1.length ≤
      2 + 2 * B.entry * (aggnPhaseJobs c C).length ∧
    v.2.2.1 ≤ j ∧ AggnCertBound B j v.2.2.2

private theorem aggnCons_size {α : Type*} [Enc α] (a : α) (l : List α) :
    Enc.size (a :: l) ≤ 2 * Enc.size a + Enc.size l := by
  rw [size_cons_eq, listSize_frame]
  have h := size_le_self (Enc.encode a).length
  have h' := length_lt_listSize (Enc.encode a)
  change (Enc.size a + (Nat.size (Enc.encode a).length + 1) + Enc.size l - 1) ≤ _
  change (Enc.encode a).length < Enc.size a at h'
  omega

private theorem aggnStoreJob_size {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {a : AggnJob} (ha : a ∈ aggnPhaseJobs c C) {v : AggnCertState}
    (hv : AggnLoopBound B.base B.loopState v.1) (stores : AggnStores) :
    aggnStoresSize (aggnStoreJob a v stores) ≤ aggnStoresSize stores + 2 * B.entry := by
  have he := B.entry_le a ha v.1 hv
  have h1 := aggnCons_size (aggnLoopEntry (a, v.1)) stores.1
  have h2 := aggnCons_size (aggnLoopEntry (a, v.1)) stores.2
  unfold aggnStoreJob aggnStoresSize
  cases a.1 <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    change Enc.size _ + Enc.size _ ≤ _ <;>
    dsimp only [aggnLoopEntry, aggnCertOut] at he h1 h2 ⊢ <;> omega

/-- The scan preserves the job/store budget, including on incorrect answers. -/
theorem aggnPhaseBound_scan {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C) :
    ∀ jobs stores j, jobs ⊆ aggnPhaseJobs c C → Enc.size jobs ≤ B.base →
      aggnStoresSize stores + 2 * B.entry * jobs.length ≤
        2 + 2 * B.entry * (aggnPhaseJobs c C).length →
      AggnPhaseBound B j (aggnPhaseScan c C jobs stores) := by
  intro jobs
  induction jobs with
  | nil =>
    intro stores j hsub hsize hpot
    exact ⟨hsub, hsize, hpot, Nat.zero_le _, AggnCertBound.open B B.empty_le j⟩
  | cons a rest ih =>
    intro stores j hsub hsize hpot
    have ha := hsub List.mem_cons_self
    have hv := AggnCertBound.open B (B.open_le a ha) j
    simp only [aggnPhaseScan]
    split
    · exact ⟨hsub, hsize, hpot, Nat.zero_le _, hv⟩
    · apply ih _ j (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := aggnStoreJob_size ha hv.1 stores
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- Initialization satisfies the full invariant for every context. -/
theorem aggnPhaseBound_init {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C) :
    AggnPhaseBound B 0 ((aggnCheckedRound c 0).init (C, none)) := by
  apply aggnPhaseBound_scan B _ _ _ (List.Subset.refl _) B.jobs_le
  simp [aggnStoresSize, size_nil]

/-- One more bounded answer preserves the invariant. -/
theorem AggnPhaseBound.combine {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j : ℕ} {v : AggnPhaseState} (h : AggnPhaseBound B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    AggnPhaseBound B (j + 1) (aggnPhaseCombine c (I, i, v, ans)) := by
  obtain ⟨jobs, stores, k, core⟩ := v
  obtain ⟨hsub, hsize, hpot, hk, hv⟩ := h
  dsimp only at hsub hsize hpot hk hv
  cases jobs with
  | nil =>
    change AggnPhaseBound B (j + 1) (aggnPhaseScan c I.1 [] stores)
    rw [hI]
    exact aggnPhaseBound_scan B [] stores _ hsub hsize hpot
  | cons a rest =>
    have hcore := hv.combine ha ((aggnJobLoop C a, none)) k
    change AggnPhaseBound B (j + 1) (aggnPhasePack c I.1 a rest stores (k + 1)
      (aggnCertCombine c ((aggnJobLoop I.1 a, none), k, core, ans)))
    rw [hI]
    generalize hnew : aggnCertCombine c ((aggnJobLoop C a, none), k, core, ans) = next at hcore ⊢
    unfold aggnPhasePack
    split
    · exact ⟨hsub, hsize, hpot, Nat.add_le_add_right hk 1, hcore⟩
    · apply aggnPhaseBound_scan B _ _ _ (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := aggnStoreJob_size (hsub List.mem_cons_self) hcore.1 stores
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

/-- The normalized answer is bounded regardless of its supplied representation. -/
theorem AggnPhaseBound.combine_norm {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j : ℕ} {v : AggnPhaseState} (h : AggnPhaseBound B j v)
    (ans : RawCoset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    AggnPhaseBound B (j + 1)
      (aggnPhaseCombine c (I, i, v, aggnNormAnswer C.2.1 ans)) := by
  apply h.combine (I := I) (i := i) ?_ hI
  apply (aggnNormAnswer_size ((length_le_size C.2.1).trans
    (((size_fst_le' C.2).trans (size_snd_le' C)).trans B.context_le)) ans).trans
  have := B.coset_le
  omega

/-- One scalar bound includes the stores, cache, and both local counters. -/
def aggnEnvelopeBound {c : ℕ} {C : AggnPhaseCtx} (B : AggnStateEnvelope c C) (j : ℕ) : ℕ :=
  2048 * (B.base + B.loopState + B.cache + B.coset +
    (2 + 2 * B.entry * B.base) + j + 1)

private theorem aggnNat_size_le {a b : ℕ} (h : a ≤ b) : Enc.size a ≤ b + 2 := by
  rw [Small.size_nat]
  have := size_le_self a
  omega

theorem AggnCertBound.size {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j : ℕ} {v : AggnCertState} (h : AggnCertBound B j v) :
    Enc.size v ≤ 4 * B.base + 4 * B.loopState + 52 * B.cache +
      128 * B.coset + 8 * j + 112 := by
  have hp := h.1.size
  have hP : Enc.size v.2.1 ≤ B.cache := h.2.1 ▸ B.cache_le v.1 h.1
  have hj := aggnNat_size_le h.2.2.1
  have ht := aggnNat_size_le h.2.2.2.1
  have hi := aggnNat_size_le h.2.2.2.2.1
  have ha := h.2.2.2.2.2.1
  have hb := h.2.2.2.2.2.2
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 := Combine.size_pair_le _ _
  have h3 : Enc.size v.2.2.2 ≤ 2 * Enc.size v.2.2.2.1 + 2 * Enc.size v.2.2.2.2 := Combine.size_pair_le _ _
  have h4 : Enc.size v.2.2.2.2 ≤ 2 * Enc.size v.2.2.2.2.1 + 2 * Enc.size v.2.2.2.2.2 := Combine.size_pair_le _ _
  have h5 : Enc.size v.2.2.2.2.2 ≤ 2 * Enc.size v.2.2.2.2.2.1 + 2 * Enc.size v.2.2.2.2.2.2 := Combine.size_pair_le _ _
  omega

theorem AggnPhaseBound.size {c : ℕ} {C : AggnPhaseCtx} {B : AggnStateEnvelope c C}
    {j : ℕ} {v : AggnPhaseState} (h : AggnPhaseBound B j v) :
    Enc.size v ≤ aggnEnvelopeBound B j := by
  have hj := aggnNat_size_le h.2.2.2.1
  have hc := h.2.2.2.2.size
  have hn := Nat.mul_le_mul_left (2 * B.entry)
    ((length_le_size (aggnPhaseJobs c C)).trans B.jobs_le)
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 := Combine.size_pair_le _ _
  have hs : Enc.size v.2.1 ≤ 2 * Enc.size v.2.1.1 + 2 * Enc.size v.2.1.2 := Combine.size_pair_le _ _
  obtain ⟨_, hsize, hpot, _, _⟩ := h
  unfold aggnStoresSize at hpot
  unfold aggnEnvelopeBound
  omega

end Algo
