import Workspace.Algo.AggNodePairBound

/-! # Retained state through the complete comparison phase

Each completed job pays for exactly one stored coset. The current paired
state uses the fixed cache and coset bounds from its original context.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnCompareTarget (C : AggnPhaseCtx) (jobs : List AggnCompareJob) : RawStr :=
  jobs.head?.elim [] (fun a => (aggnCompareCtx C a).2.1)

def AggnCompareBound {c : ℕ} {C : AggnPhaseCtx} (B : AggnCompareEnvelope c C)
    (j : ℕ) (v : AggnCompareState) : Prop :=
  v.1 ⊆ aggnCompareJobs c C ∧ Enc.size v.1 ≤ B.base ∧
    Enc.size v.2.1 + 2 * B.coset * v.1.length ≤
      1 + 2 * B.coset * (aggnCompareJobs c C).length ∧
    v.2.2.1 ≤ j ∧ AggnPairBound B (aggnCompareTarget C v.1) j v.2.2.2

private theorem cons_size {α : Type*} [Enc α] (a : α) (l : List α) :
    Enc.size (a :: l) ≤ 2 * Enc.size a + Enc.size l := by
  rw [size_cons_eq, listSize_frame]
  have h := size_le_self (Enc.encode a).length
  have h' := length_lt_listSize (Enc.encode a)
  change (Enc.size a + (Nat.size (Enc.encode a).length + 1) + Enc.size l - 1) ≤ _
  change (Enc.encode a).length < Enc.size a at h'
  omega

theorem aggnCompareBound_scan {c : ℕ} {C : AggnPhaseCtx} (B : AggnCompareEnvelope c C) :
    ∀ jobs answers j, jobs ⊆ aggnCompareJobs c C → Enc.size jobs ≤ B.base →
      Enc.size answers + 2 * B.coset * jobs.length ≤
        1 + 2 * B.coset * (aggnCompareJobs c C).length →
      AggnCompareBound B j (aggnCompareScan c C jobs answers) := by
  intro jobs
  induction jobs with
  | nil =>
    intro answers j hsub hsize hpot
    refine ⟨hsub, hsize, hpot, Nat.zero_le _, ?_⟩
    exact AggnPairBound.start B B.empty_le
      ((size_fst_le' (([], []) : RawStr × List ℕ)).trans B.empty_le.1)
      B.empty_coset_le (fun H he => by cases he) j
  | cons a rest ih =>
    intro answers j hsub hsize hpot
    have ha := hsub List.mem_cons_self
    have hopen := B.open_le a ha
    have hv := AggnPairBound.start B hopen.1 hopen.2.1 hopen.2.2
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

theorem aggnCompareBound_init {c : ℕ} {C : AggnPhaseCtx} (B : AggnCompareEnvelope c C) :
    AggnCompareBound B 0 ((aggnCompareRound c 0).init (C, none)) := by
  apply aggnCompareBound_scan B _ _ _ (List.Subset.refl _) B.jobs_le
  simp [size_nil]

theorem AggnCompareBound.combine {c : ℕ} {C : AggnPhaseCtx} {B : AggnCompareEnvelope c C}
    {j : ℕ} {v : AggnCompareState} (h : AggnCompareBound B j v)
    {ans : RawCoset} (ha : Enc.size ans ≤ B.coset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    AggnCompareBound B (j + 1) (aggnCompareCombine c (I, i, v, ans)) := by
  obtain ⟨jobs, answers, k, core⟩ := v
  obtain ⟨hsub, hsize, hpot, hk, hv⟩ := h
  dsimp only at hsub hsize hpot hk hv
  cases jobs with
  | nil =>
    change AggnCompareBound B (j + 1) (aggnCompareScan c I.1 [] answers)
    rw [hI]
    exact aggnCompareBound_scan B [] answers _ hsub hsize hpot
  | cons a rest =>
    have hcore := hv.combine ha (aggnCompareCtx C a) rfl k
    change AggnCompareBound B (j + 1) (aggnComparePack c I.1 a rest answers (k + 1)
      (aggnPairCombine c ((aggnCompareCtx I.1 a, none), k, core, ans)))
    rw [hI]
    generalize hnew : aggnPairCombine c ((aggnCompareCtx C a, none), k, core, ans) = next at hcore ⊢
    unfold aggnComparePack
    split
    · exact ⟨hsub, hsize, hpot, Nat.add_le_add_right hk 1, hcore⟩
    · apply aggnCompareBound_scan B _ _ _ (fun a ha => hsub (List.mem_cons_of_mem _ ha))
      · exact (size_tail_le (a :: rest)).trans hsize
      · have hs := cons_size next.2.1 answers
        have hq := hcore.2.2.1
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at hpot
        omega

theorem AggnCompareBound.combine_norm {c : ℕ} {C : AggnPhaseCtx} {B : AggnCompareEnvelope c C}
    {j : ℕ} {v : AggnCompareState} (h : AggnCompareBound B j v)
    (ans : RawCoset) (I : AggnPhaseNode) (hI : I.1 = C) (i : ℕ) :
    AggnCompareBound B (j + 1)
      (aggnCompareCombine c (I, i, v, aggnNormAnswer C.2.1 ans)) := by
  apply h.combine (I := I) (i := i) ?_ hI
  apply (aggnNormAnswer_size ((length_le_size C.2.1).trans
    (((size_fst_le' C.2).trans (size_snd_le' C)).trans B.context_le)) ans).trans
  have := B.coset_le
  omega

def aggnCompareEnvelopeBound {c : ℕ} {C : AggnPhaseCtx}
    (B : AggnCompareEnvelope c C) (j : ℕ) : ℕ :=
  65536 * (B.base + B.loopState + B.cache + B.coset + (1 + 2 * B.coset * B.base) + j + 1)

theorem AggnCompareBound.size {c : ℕ} {C : AggnPhaseCtx} {B : AggnCompareEnvelope c C}
    {j : ℕ} {v : AggnCompareState} (h : AggnCompareBound B j v) :
    Enc.size v ≤ aggnCompareEnvelopeBound B j := by
  have hj : Enc.size v.2.2.1 ≤ j + 2 := by
    rw [Small.size_nat]
    have := size_le_self v.2.2.1
    have := h.2.2.2.1
    omega
  have hc := h.2.2.2.2.size
  have hn := Nat.mul_le_mul_left (2 * B.coset)
    ((length_le_size (aggnCompareJobs c C)).trans B.jobs_le)
  have h0 : Enc.size v ≤ 2 * Enc.size v.1 + 2 * Enc.size v.2 := Combine.size_pair_le _ _
  have h1 : Enc.size v.2 ≤ 2 * Enc.size v.2.1 + 2 * Enc.size v.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size v.2.2 ≤ 2 * Enc.size v.2.2.1 + 2 * Enc.size v.2.2.2 := Combine.size_pair_le _ _
  obtain ⟨_, hsize, hpot, _, _⟩ := h
  unfold aggnCompareEnvelopeBound
  omega

end Algo
