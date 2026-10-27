import Workspace.Algo.AggNodeComparePhase

/-! # The complete comparison phase

The stored answers have the reverse of execution order. Each completed
comparison advances to the next ordered pair, including pairs whose tree
has no recursive calls.
-/
namespace Algo
open Babai Equiv
open scoped Classical

theorem aggnPairChild_active {z : AggnPairNode × ℕ × AggnPairState} {J : AggnPairNode}
    (h : aggnPairChild z = some J) :
    aggnPairActive z.2.2 = true ∧ z.2.1 < aggnPairWidth z.1.1 := by
  have ho := (aggnPairChild_some h).1
  simp only [aggnPairChild, ho, Option.elim_none] at h
  split at h
  next hg => exact ⟨by simp [aggnPairActive, hg.1, hg.2.1], hg.2.2⟩
  next => simp at h

theorem aggnCompare_sim_run (c n : ℕ) (C : AggnPhaseCtx) (a : AggnCompareJob)
    (rest : List AggnCompareJob) (answers : List RawCoset) (start : ℕ)
    (hwidth : start + aggnPairWidth (aggnCompareCtx C a) ≤ aggnCompareWidth c C)
    {fuel : ℕ} {S : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    {Q : Set (Perm (Fin n)) → ℕ → AggnPairState → Prop}
    (h : PhaseMatch (aggnPairRound c n (fun _ => none)) (aggnPairDecode n) (decCoset n)
      (aggnCompareCtx C a, none) fuel 0 (aggnCompareOpen c C a) S Q) :
    PhaseMatch (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      fuel start (aggnCompareScan c C (a :: rest) answers) S
      (fun b j v => ∃ j' v', Q b j' v' ∧ j = start + j' ∧
        v = aggnComparePack c C a rest answers j' v') := by
  let Rel := fun jR vR jM vM => jM = start + jR ∧
    vM = aggnComparePack c C a rest answers jR vR
  apply aggnPhaseMatch_sim (R := aggnPairRound c n (fun _ => none))
    (decI := aggnPairDecode n) (I := (aggnCompareCtx C a, none)) Rel ?_ h
    ⟨by omega, rfl⟩
  intro jR vR jM vM hr J hJ
  obtain ⟨hj, rfl⟩ := hr
  dsimp only [aggnPairRound] at hJ
  have ha := aggnPairChild_active (z := ((aggnCompareCtx C a, none), jR, vR)) hJ
  dsimp only at ha
  have hglobal : jM < aggnCompareWidth c C := by omega
  refine ⟨(C, J.2), ?_, ?_, ?_⟩
  · dsimp only [aggnCompareRound]
    rw [aggnComparePack, if_pos ha.1]
    simp only [aggnCompareChild, Option.elim_none, if_pos hglobal]
    rw [hJ]
    rfl
  · obtain ⟨_, W, hW⟩ := aggnPairChild_some hJ
    rw [hW]
    rfl
  · intro ans
    refine ⟨by omega, ?_⟩
    dsimp only [aggnCompareRound, aggnPairRound]
    rw [aggnComparePack, if_pos ha.1]
    rfl

section Correctness
variable {c n m : ℕ} {C : AggnPhaseCtx}
  {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}

theorem aggnCompareJob_mem {a : AggnCompareJob} :
    a ∈ aggnCompareJobs c C ↔ a.2.1 ∈ aggnPhaseRows c C ∧ a.2.2 ∈ aggnPhaseRows c C := by
  rcases a with ⟨b, row, row'⟩
  cases b <;> simp [aggnCompareJobs]

noncomputable def aggnCompareJobTree (ϕ : decGroup n C.1.1.2 →* Perm (Fin m))
    (a : AggnCompareJob) :=
  compareStrong ϕ (decStrN n C.2.1) (winSet m a.2.1)
    (decStrN n (cond a.1 C.2.2.1 C.2.1))
    (aggnCanonTransport ϕ (winSet m a.2.1) (winSet m a.2.2))
    (aggnCanonicalPair ϕ (decStrN n C.2.1) (decStrN n (cond a.1 C.2.2.1 C.2.1))
      (winSet m a.2.1) ((aggnCanonTransport ϕ (winSet m a.2.1) (winSet m a.2.2)).getD 1))

theorem aggnComparePhase_job (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ)
    (h2 : 2 ≤ C.2.2.2.length) {a : AggnCompareJob} (ha : a ∈ aggnCompareJobs c C)
    (rest : List AggnCompareJob) (answers : List RawCoset) (start : ℕ)
    (hwidth : start + aggnCompareJobWidth C ≤ aggnCompareWidth c C) :
    PhaseMatch (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnCompareJobWidth C) start (aggnCompareScan c C (a :: rest) answers)
      (aggnCompareJobTree ϕ a)
      (fun B j v => ∃ q, decCoset n q = B ∧
        v = aggnCompareScan c C rest (q :: answers) ∧ j ≤ start + aggnCompareJobWidth C) := by
  obtain ⟨hr, hr'⟩ := aggnCompareJob_mem.mp ha
  have hs : (false, a.2.1) ∈ aggnPhaseJobs c C := aggnJob_mem.mpr hr
  have ht : (false, a.2.2) ∈ aggnPhaseJobs c C := aggnJob_mem.mpr hr'
  have hd := aggnJob_data hC hs
  have hd' := aggnJob_data hC ht
  have hc : LCCtxWF n m C.2.1 a.2.1 := aggnJobCtx hC hs
  have hp := aggnPairPrepare_phase c (fun _ => none) hc hC.action hgiant
    hd'.1 hd'.2.1 (hd.2.2.1.trans hd'.2.2.1.symm) (hd.2.2.1 ▸ h2)
    (hd.2.2.1 ▸ hC.guard) hd.2.2.2 (ys := cond a.1 C.2.2.1 C.2.1)
  dsimp only at hp
  have hw : 2 * n * (Nat.factorial a.2.1.length * n) = aggnCompareJobWidth C := by
    simp only [aggnCompareJobWidth, aggnJobWidth, hC.source, hd.2.2.1]
    exact Nat.mul_assoc _ _ _
  rw [hw] at hp
  have hwp : aggnPairWidth (aggnCompareCtx C a) = aggnCompareJobWidth C := by
    simp only [aggnPairWidth, aggnCompareCtx, aggnPairPrepare, aggnCertWidth,
      aggnCertStageWidth, aggnCompareJobWidth, aggnJobWidth, hd.2.2.1]
  have hm := aggnCompare_sim_run c n C a rest answers start (by rwa [hwp]) hp
  apply phaseMatch_weaken hm
  rintro B j v ⟨jR, vR, ⟨hB, hstop, hjR⟩, hj, hv⟩
  refine ⟨vR.2.1, hB, ?_, ?_⟩
  · rw [hv, aggnComparePack, if_neg (Bool.eq_false_iff.mp hstop)]
  · omega

/-- All returned cosets are retained, in reverse execution order. -/
theorem aggnComparePhase_sequence (hC : AggnPhaseCtxWF c n m C ϕ)
    (hgiant : IsGiantRep ϕ) (h2 : 2 ≤ C.2.2.2.length) :
    ∀ (todo : List AggnCompareJob), todo ⊆ aggnCompareJobs c C → ∀ answers start,
      start + todo.length * aggnCompareJobWidth C ≤ aggnCompareWidth c C →
    PhaseMatch (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (todo.length * aggnCompareJobWidth C) start (aggnCompareScan c C todo answers)
      (SIReduction.sequence (todo.map (aggnCompareJobTree ϕ)))
      (fun B j v => ∃ qs : List RawCoset, qs.map (decCoset n) = B ∧
        v = aggnCompareScan c C [] (qs.reverse ++ answers) ∧
        j ≤ start + todo.length * aggnCompareJobWidth C) := by
  intro todo
  induction todo with
  | nil =>
    intro hsub answers start hb
    simp only [List.length_nil, Nat.zero_mul, List.map_nil, SIReduction.sequence]
    exact phaseMatch_done ⟨[], rfl, rfl, by omega⟩
  | cons a rest ih =>
    intro hsub answers start hb
    have ha := hsub List.mem_cons_self
    have hr : rest ⊆ aggnCompareJobs c C := fun b hb => hsub (List.mem_cons_of_mem a hb)
    have hwidth : start + aggnCompareJobWidth C ≤ aggnCompareWidth c C := by
      simp only [List.length_cons, Nat.succ_mul] at hb
      omega
    have hm := aggnComparePhase_job hC hgiant h2 ha rest answers start hwidth
    rw [List.map_cons, SIReduction.sequence, List.length_cons, Nat.succ_mul, Nat.add_comm]
    apply phaseMatch_bind hm
    rintro B j v ⟨q, hq, rfl, hj⟩
    have hjb : j + rest.length * aggnCompareJobWidth C ≤ aggnCompareWidth c C := by
      simp only [List.length_cons, Nat.succ_mul] at hb
      omega
    have htail := ih hr (q :: answers) j hjb
    have hend := phaseMatch_bind
      (P' := fun bs j' v' => ∃ qs : List RawCoset, qs.map (decCoset n) = bs ∧
        v' = aggnCompareScan c C [] (qs.reverse ++ answers) ∧
        j' ≤ start + (a :: rest).length * aggnCompareJobWidth C)
      (k := fun bs => .done (B :: bs)) htail (by
        rintro bs j' v' ⟨qs, hqs, hv, hj'⟩
        apply phaseMatch_done
        refine ⟨q :: qs, by simp [hq, hqs], ?_, ?_⟩
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hv
        · simp only [List.length_cons, Nat.succ_mul]
          omega)
    simpa only [Nat.add_zero, List.length_cons, Nat.succ_mul, Nat.add_comm] using hend

end Correctness

/-- The raw pair order is the order in Section 13.2. -/
theorem aggnComparePhase_tree_eq {c n m : ℕ} {C : AggnPhaseCtx}
    (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)) :
    SIReduction.sequence ((aggnCompareJobs c C).map (aggnCompareJobTree ϕ)) =
      comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))) := by
  unfold comparePhaseStrong compareRunsStrong aggnCompareJobs aggnFullEnum aggnCertEnum
  rw [List.map_flatMap]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro b hb
  rw [List.map_flatMap, List.flatMap_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row hr
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro row' hr'
  cases b <;> rfl

/-- Exact matching for every encoding of every correct recursive answer. -/
theorem aggnComparePhase_comparisons {c n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hgiant : IsGiantRep ϕ) (h2 : 2 ≤ C.2.2.2.length) :
    PhaseMatch (aggnCompareRound c n) (aggnPhaseDecode n) (decCoset n) (C, none)
      (aggnCompareWidth c C) 0 ((aggnCompareRound c n).init (C, none))
      (comparePhaseStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
        (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          ((aggnPhaseRows c C).map (winSet m))))
      (fun B _ v => v.1 = [] ∧ v.2.1.reverse.map (decCoset n) = B) := by
  have hm := aggnComparePhase_sequence hC hgiant h2 (aggnCompareJobs c C)
    (List.Subset.refl _) [] 0 (by simp [aggnCompareWidth])
  rw [aggnComparePhase_tree_eq] at hm
  apply phaseMatch_weaken hm
  rintro B j v ⟨qs, hqs, rfl, hj⟩
  exact ⟨rfl, by simpa [aggnCompareScan] using hqs⟩

end Algo
