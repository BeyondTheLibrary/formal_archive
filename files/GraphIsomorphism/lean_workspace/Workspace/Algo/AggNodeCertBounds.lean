import Workspace.Algo.AggNodeCertStores

/-! # Certificate phase bounds and read-offs

These are bounds on the fixed phase and its completed stores. They do not
constitute `Round.CostQ`: that structure also requires bounds on every
well-formed instance and every bounded, possibly malformed, fold state.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- A factorial under the arity guard has a uniform quasipolynomial bound. -/
theorem aggnFactorial_le (c : ℕ) {n t : ℕ} (htn : t ≤ n) (ht : t ≤ guardBound c n) :
    Nat.factorial t ≤ 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) := by
  calc
    Nat.factorial t ≤ t ^ t := Nat.factorial_le_pow _
    _ ≤ n ^ t := Nat.pow_le_pow_left htn _
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ t := Nat.pow_le_pow_left (le_two_pow_log n) _
    _ = 2 ^ ((Nat.log 2 n + 1) * t) := by rw [← pow_mul]
    _ ≤ 2 ^ ((Nat.log 2 n + 1) ^ (c + 1)) := by
      apply Nat.pow_le_pow_right (by decide)
      simpa only [guardBound, pow_succ, Nat.mul_comm] using
        Nat.mul_le_mul_left (Nat.log 2 n + 1) ht
    _ ≤ 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left (by omega) _)

def aggnPhaseCostBound (c n : ℕ) : ℕ :=
  2 * 2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) *
    (n * (2 ^ ((Nat.log 2 n + 2) ^ (c + 1)) * n) + 1)

theorem aggnQuasiPolyBound_phaseCost (c : ℕ) : QuasiPolyBound (aggnPhaseCostBound c) :=
  ((polyBound_const 2).quasiPoly.mul (quasiPolyBound_witness (c + 1))).mul
    ((polyBound_id.quasiPoly.mul ((quasiPolyBound_witness (c + 1)).mul polyBound_id.quasiPoly)).add
      (polyBound_const 1).quasiPoly)

section Bounds
variable {c n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

theorem aggnPhaseJobs_length (hC : AggnPhaseCtxWF c n m C ϕ) :
    (aggnPhaseJobs c C).length = 2 * m.choose C.2.2.2.length := by
  have hm : C.1.2.1.length ≤ C.2.1.length := by
    rw [hC.action.2.1, hC.source]; exact hC.degree
  have hl := (aggTestSetsOn_perm hC.guard hm).length_eq
  simp only [List.length_map, length_testSetList, Fintype.card_fin, hC.action.2.1] at hl
  simp [aggnPhaseJobs, aggnPhaseRows, hl, two_mul]

/-- The width and one scan of the test table share a uniform bound. -/
theorem aggnPhase_width_scan_le (hC : AggnPhaseCtxWF c n m C ϕ) :
    aggnPhaseWidth c C + (aggnPhaseJobs c C).length ≤ aggnPhaseCostBound c n := by
  have hg : C.2.2.2.length ≤ guardBound c n := by simpa only [hC.source] using hC.guard
  have hf := aggnFactorial_le c hC.arity hg
  have ht := aggChoose_le c hC.degree hg
  rw [aggnPhaseWidth, aggnPhaseJobs_length hC, hC.source]
  change 2 * m.choose C.2.2.2.length *
      (n * (Nat.factorial C.2.2.2.length * n)) + 2 * m.choose C.2.2.2.length ≤ _
  rw [← Nat.mul_add_one]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht)
    (Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.mul_le_mul_right n hf)) 1)

/-- The mathematical call bound applies to the exact enumeration of the raw node. -/
theorem aggnPhase_calls_le (hC : AggnPhaseCtxWF c n m C ϕ) (h5 : 5 ≤ C.2.2.2.length) :
    (certPhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        C.2.2.2 C.2.1 C.1.2.1)).calls.length ≤ aggnPhaseWidth c C := by
  let E := aggnRawCertEnum c ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
    C.2.2.2 C.2.1 C.1.2.1
  have hE : E.Spec ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) C.2.2.2.length :=
    aggnRawCertEnum_spec c _ _ _ hC.guard hC.action.2.1 (hC.source.symm ▸ hC.degree)
  have h := SIReduction.calls_length_sequence_le
    (fun S hS => (certRunsStrong_bound E hE.toBound h5 hS).1)
  have hl : (certRunsStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) E).length =
      (aggnPhaseJobs c C).length := by
    simp [certRunsStrong, E, aggnRawCertEnum, aggnCertEnum, aggnPhaseJobs, aggnPhaseRows]
  change (SIReduction.sequence _).calls.length ≤ _
  rw [hl, Nat.card_fin] at h
  simpa only [aggnPhaseWidth, hC.source, pow_two, Nat.mul_assoc, Nat.mul_left_comm n] using h

/-- The scan examines at most the number of supplied jobs. -/
def aggnPhaseScanCount (c : ℕ) (C : AggnPhaseCtx) : List AggnJob → ℕ
  | [] => 0
  | a :: rest =>
    if lcCond (aggnJobLoop C a) then 1 else 1 + aggnPhaseScanCount c C rest

theorem aggnPhaseScanCount_le (c : ℕ) (C : AggnPhaseCtx) (jobs : List AggnJob) :
    aggnPhaseScanCount c C jobs ≤ jobs.length := by
  induction jobs with
  | nil => rfl
  | cons a rest ih =>
    simp only [aggnPhaseScanCount, List.length_cons]
    split <;> omega

/-- A completed store gives the aggregate group, its image, and its fixed points. -/
theorem aggnStores_readOff (hC : AggnPhaseCtxWF c n m C ϕ) {stores : AggnStores}
    (hs : AggnStoresComplete c ϕ stores) (b : Bool) :
    decGroup n (rawF (C.1.1.1, aggnStoreAt stores b)) =
        bigF ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
      decGroup m (aggFGamma (C.1, aggnStoreAt stores b)) =
        bigFGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length ∧
      winSet m (aggFixedGamma (C.1, aggnStoreAt stores b)) =
        fixedGamma ϕ (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length := by
  obtain ⟨hd, hm, hgs, his, hI⟩ := hC.action
  have hf := aggFGamma_spec hd hm hI (hs b).1 (hs b).2.1
  have hd' := aggFixedGamma_spec hd hm hI (hs b).1 (hs b).2.1
  rw [map_encPerm_decPerm hgs, map_encPerm_decPerm his] at hf hd'
  exact ⟨aggF_spec hd (hs b).1 (hs b).2.1, hf, hd'⟩

end Bounds

/-- Complete stores have a quasipolynomial size, with the constant before the degrees. -/
theorem aggnCompleted_store_size (c : ℕ) : ∃ d : ℕ, ∀ (n m : ℕ) (C : AggnPhaseCtx)
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m))
    (hC : AggnPhaseCtxWF c n m C ϕ) (stores : AggnStores),
    AggnStoresComplete c ϕ stores → ∀ b,
    Enc.size (aggnStoreAt stores b) ≤ 2 ^ ((Nat.log 2 n + 2) ^ d) := by
  obtain ⟨d, hd⟩ := aggSize_store_quasi c
  refine ⟨d, fun n m C ϕ hC stores hs b => ?_⟩
  have hstore := (hs b).1
  have hlen : (aggnStoreAt stores b).length ≤ m.choose C.2.2.2.length := by
    have hl := congrArg List.length (hs b).2.2
    simp only [List.length_map, List.length_reverse] at hl
    have hm : C.1.2.1.length ≤ C.2.1.length := by
      rw [hC.action.2.1, hC.source]; exact hC.degree
    have ht := (aggTestSetsOn_perm hC.guard hm).length_eq
    simp only [List.length_map, length_testSetList, Fintype.card_fin, hC.action.2.1] at ht
    exact (hl.trans ht).le
  exact hd n m C.2.2.2.length _ (fun e he => (hstore.2 e he).wf) hC.degree hC.arity
    (by simpa only [hC.source] using hC.guard) hlen

end Algo
