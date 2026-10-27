import Workspace.Machine.RunsOn
import Workspace.Machine.Cases
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Per-input runs: a loop whose steps cost different amounts, and case analysis

`RAM.runsOn_iterate` (`Workspace/Machine/RunsOn.lean`) charges every step of a bounded loop the
same amount `B`. A procedure that calls a String Isomorphism routine inside its loop pays for
each call separately, and the calls have different costs. The paper's bounds of §13 ("by making
`≤ t! n²` calls … and performing `t! poly(n)` computation") add the costs of the calls, so the
loop has to be charged the *sum* of its steps.

## Main results

* `RAM.runsOn_iterate_sum`: `whileNz (K + 2) Q` iterates a step `N` times, in the sum of the
  costs of the `N` steps plus `2N + 1`; only the states the iteration passes through need a
  run of `Q`;
* `RAM.RunsOn.optionElim_none`, `RAM.RunsOn.optionElim_some`: the dispatcher on the tag of an
  `Option` (`RAM.Lists.optElimProg`), one run at a time.
-/

namespace RAM

variable {α β γ σ : Type*}

/-- **Bounded iteration, one run per step, summed costs.**  If for every `j < N` the step `Q`
runs from the `j`-th state of the iteration to the next one in `W j` steps, then
`whileNz (K + 2) Q` iterates `step` exactly `N` times within `∑_{j<N} (W j + 2) + 1` steps. -/
theorem runsOn_iterate_sum [Enc σ] {K : ℕ} {Q : Program} {step : σ → σ} (hwf : Wf Q)
    (N : ℕ) (s₀ : σ) (W : ℕ → ℕ)
    (hQ : ∀ j < N, RunsOn K Q ((N - j, step^[j] s₀) : ℕ × σ)
      ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) (W j)) :
    RunsOn K (whileNz (K + 2) Q) ((N, s₀) : ℕ × σ) ((0, step^[N] s₀) : ℕ × σ)
      ((∑ j ∈ Finset.range N, (W j + 2)) + 1) := by
  refine ⟨wf_whileNz hwf, ?_⟩
  set Wh := whileNz (K + 2) Q with hWh
  have hjz : ∀ m : Mem, Wh[(⟨0, m⟩ : Config).pc]? = some (Instr.jz (K + 2) (Q.length + 2)) :=
    fun _ => rfl
  have hjump : Wh[1 + Q.length]? = some (Instr.jump 0) := by
    simp [hWh, whileNz, Nat.add_comm]
  have key : ∀ (r j : ℕ), j + r = N →
      ∃ k ≤ (∑ i ∈ Finset.Ico j N, (W i + 2)) + 1,
        Halted Wh (run Wh ⟨0, initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ))⟩ k) ∧
        (run Wh ⟨0, initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ))⟩ k).mem
          = initMemAt K (Enc.encode ((0, step^[N] s₀) : ℕ × σ)) := by
    intro r
    induction r with
    | zero =>
        intro j hj
        have hjN : j = N := by omega
        subst hjN
        set m := initMemAt K (Enc.encode ((j - j, step^[j] s₀) : ℕ × σ)) with hm
        have h0 : m (K + 2) = 0 := by rw [hm, initMemAt_prod_counter]; omega
        have hstep : run Wh ⟨0, m⟩ 1 = ⟨Q.length + 2, m⟩ := by
          rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
          simp [exec, h0]
        refine ⟨1, by omega, ?_, ?_⟩
        · rw [hstep]; exact halted_of_pc_length (by simp [hWh])
        · rw [hstep, hm, Nat.sub_self]
    | succ r ih =>
        intro j hj
        have hjN : j < N := by omega
        set m := initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hm
        have h0 : m (K + 2) ≠ 0 := by rw [hm, initMemAt_prod_counter]; omega
        obtain ⟨k, hkT, m', hkrun, hpost, hkmin⟩ := (hQ j hjN).halt_at (m := m) rfl
        obtain ⟨k', hk'T, hk'halt, hk'mem⟩ := ih (j + 1) (by omega)
        have hstep : run Wh ⟨0, m⟩ 1 = ⟨1, m⟩ := by
          rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
          simp [exec, h0]
        have hbody : run Wh ⟨1, m⟩ k = ⟨1 + Q.length, m'⟩ := by
          rw [run_block (A := [Instr.jz (K + 2) (Q.length + 2)]) (Q := Q)
            (B := [Instr.jump 0]) (by simp [hWh, whileNz]) (by simp) k hkmin, hkrun]
        have hback : run Wh ⟨1 + Q.length, m'⟩ 1 = ⟨0, m'⟩ := by
          rw [run_succ, run_zero, step_of_get (by simpa using hjump) (by simp)]
          simp [exec]
        have hsum : ∑ i ∈ Finset.Ico j N, (W i + 2)
            = (W j + 2) + ∑ i ∈ Finset.Ico (j + 1) N, (W i + 2) :=
          Finset.sum_eq_sum_Ico_succ_bot hjN _
        have hm' : m' = initMemAt K (Enc.encode ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ)) :=
          hpost
        refine ⟨1 + k + 1 + k', by omega, ?_, ?_⟩ <;>
          rw [run_add, run_add, run_add, hstep, hbody, hback, hm']
        · exact hk'halt
        · exact hk'mem
  intro m hm
  obtain ⟨k, hk, hhalt, hmem⟩ := key N 0 (by omega)
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [Finset.range_eq_Ico]; exact hk
  · rw [hm]; simpa using hhalt
  · rw [hm]; simpa using hmem

/-! ## The dispatcher on an `Option`, one run at a time -/

section OptionElim

variable [Enc β] [Enc σ] [Enc γ]

set_option maxHeartbeats 1000000 in
/-- **The `none` branch of the dispatcher.** -/
theorem RunsOn.optionElim_none {K : ℕ} (hK : 16 ≤ K) {Pg Ph : Program} (hhwf : Wf Ph)
    {s : σ} {c : γ} {T : ℕ} (hg : RunsOn K Pg s c T) :
    RunsOn K (Lists.optElimProg K Pg Ph) (((none : Option β), s) : Option β × σ) c
      (24 * Enc.size (((none : Option β), s) : Option β × σ) + K + 80 + T + 2) := by
  have hreg := initMemAt_option_tag (K := K) (none : Option β) s
  have hsnd := Combine.cleanComputeAt_snd (α := Option β) (β := σ) hK ((none : Option β), s)
  have hnone : RunsTo (RAM.seq (Combine.sndProg K) Pg)
      (fun m => m = initMemAt K (Enc.encode (((none : Option β), s) : Option β × σ)))
      (fun m' => m' = initMemAt K (Enc.encode c))
      (24 * Enc.size (((none : Option β), s) : Option β × σ) + K + 80 + T) :=
    hsnd.seq hg
  have hwfsome : Wf (RAM.seq (Lists.stripProg K) Ph) :=
    wf_seq (Lists.runsTo_stripProg (K := K) (eb := []) (es := []) hK rfl rfl).wf hhwf
  have hbr1 : RunsTo (RAM.seq (Lists.stripProg K) Ph)
      (fun m => m = initMemAt K (Enc.encode (((none : Option β), s) : Option β × σ)) ∧
        m (K + 2) ≠ 0)
      (fun m' => m' = initMemAt K (Enc.encode c)) 0 := by
    refine runsTo_of_false hwfsome ?_
    rintro m ⟨hm1, hm2⟩
    rw [hm1, hreg] at hm2
    simp at hm2
  exact (hbr1.ifz (hnone.strengthen (fun m hm => hm.1))).mono (by omega)

set_option maxHeartbeats 1000000 in
/-- **The `some` branch of the dispatcher.** -/
theorem RunsOn.optionElim_some {K : ℕ} (hK : 16 ≤ K) {Pg Ph : Program} (hgwf : Wf Pg)
    {b : β} {s : σ} {c : γ} {T : ℕ} (hh : RunsOn K Ph ((b, s) : β × σ) c T) :
    RunsOn K (Lists.optElimProg K Pg Ph) ((some b, s) : Option β × σ) c
      (19 * Enc.size ((some b, s) : Option β × σ) + K + 104 + T + 2) := by
  have hreg := initMemAt_option_tag (K := K) (some b) s
  have henc1 : Enc.encode ((some b, s) : Option β × σ)
      = ((Enc.encode b).length + 1) :: 1 ::
        (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
    show frame (1 :: Enc.encode b) ++ frame (Enc.encode s) = _
    simp [frame]
  have henc2 : Enc.encode ((b, s) : β × σ)
      = (Enc.encode b).length :: (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
    show frame (Enc.encode b) ++ frame (Enc.encode s) = _
    simp [frame]
  have hlen : (Enc.encode ((some b, s) : Option β × σ)).length
      = (Enc.encode b).length + (Enc.encode s).length + 3 := by
    rw [henc1]; simp; all_goals omega
  have hlt : (Enc.encode b).length + (Enc.encode s).length + 3
      < Enc.size ((some b, s) : Option β × σ) := by
    have h1 := length_lt_listSize (Enc.encode ((some b, s) : Option β × σ))
    rw [hlen] at h1
    exact h1
  have hstrip : RunsTo (Lists.stripProg K)
      (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)))
      (fun m' => m' = initMemAt K (Enc.encode ((b, s) : β × σ)))
      (19 * (Enc.encode b).length + 19 * (Enc.encode s).length + K + 104) := by
    rw [henc1, henc2]
    exact Lists.runsTo_stripProg hK rfl rfl
  have hsome : RunsTo (RAM.seq (Lists.stripProg K) Ph)
      (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)))
      (fun m' => m' = initMemAt K (Enc.encode c))
      (19 * Enc.size ((some b, s) : Option β × σ) + K + 104 + T) :=
    (hstrip.seq hh).mono (by omega)
  have hbr2 : RunsTo (RAM.seq (Combine.sndProg K) Pg)
      (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)) ∧ m (K + 2) = 0)
      (fun m' => m' = initMemAt K (Enc.encode c)) 0 := by
    refine runsTo_of_false (wf_seq (Combine.cleanComputeAt_snd (α := Option β) (β := σ) hK
      ((some b, s))).wf hgwf) ?_
    rintro m ⟨hm1, hm2⟩
    rw [hm1, hreg] at hm2
    simp at hm2
  exact ((hsome.strengthen (fun m hm => hm.1)).ifz hbr2).mono (by omega)

end OptionElim

/-! ## Well-formedness of the pairing routine and the dispatcher -/

theorem wf_nil' : Wf ([] : Program) := fun _ h => absurd h (List.not_mem_nil)

theorem Layout.wf_clearRange : ∀ j, Wf (Layout.clearRange j)
  | 0 => wf_nil'
  | j + 1 => wf_seq (Layout.wf_clearRange j) (Layout.wf_assign j 0)

theorem Layout.wf_pushZeros (j : ℕ) : Wf (Layout.pushZeros j) :=
  wf_seq (Layout.wf_assign _ _) (Layout.wf_addTo _ _ _)

theorem Layout.wf_pushVal (r : ℕ) : Wf (Layout.pushVal r) :=
  wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_storeTo _ _) (Layout.wf_addTo _ _ _))

theorem Layout.wf_pushBlock : Wf Layout.pushBlock :=
  wf_seq (Layout.wf_copyTo _ _) (wf_seq Layout.wf_copyBlock (Layout.wf_addTo _ _ _))

theorem Layout.wf_callTopAt (K : ℕ) {P : Program} (hP : Wf P) : Wf (Layout.callTopAt K P) := by
  unfold Layout.callTopAt
  exact wf_seq (Reloc.wf_relocate hP) (wf_seq (Layout.wf_assign _ _) (wf_seq
    (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_assign _ _) (Layout.wf_addTo _ _ _))))))

theorem Layout.wf_finish (K : ℕ) : Wf (Layout.finish K) := by
  unfold Layout.finish
  exact wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_assign _ _) (wf_seq
    (Layout.wf_copyTo _ _) (wf_seq Layout.wf_copyBlock (wf_seq (Layout.wf_assign _ _)
      (wf_seq (Layout.wf_addTo _ _ _) (wf_seq (Layout.wf_assign _ _) (wf_seq
        (Layout.wf_subTo _ _ _) (wf_seq Layout.wf_fillZero (Layout.wf_clearRange K)))))))))

/-- The pairing routine is well formed when its two routines are. -/
theorem Pairing.wf_pairProg (K : ℕ) {Pf Pg : Program} (hf : Wf Pf) (hg : Wf Pg) :
    Wf (Pairing.pairProg K Pf Pg) := by
  have ca := Layout.wf_copyTo
  have as := Layout.wf_assign
  have ad := Layout.wf_addTo
  have lo := Layout.wf_loadTo
  have pz := Layout.wf_pushZeros
  have pv := Layout.wf_pushVal
  have pb := Layout.wf_pushBlock
  have hA : Wf (Pairing.progA K Pg) := by
    unfold Pairing.progA
    exact wf_seq (ca _ _) (wf_seq (as _ _) (wf_seq (ad _ _ _) (wf_seq (as _ _) (wf_seq
      (ad _ _ _) (wf_seq (ca _ _) (wf_seq (pz _) (wf_seq (as _ _) (wf_seq (ca _ _) (wf_seq pb
        (wf_seq (ca _ _) (wf_seq (Layout.wf_callTopAt K hg) (wf_seq (ca _ _)
          (lo _ _)))))))))))))
  have hB : Wf (Pairing.progB K Pf) := by
    unfold Pairing.progB
    exact wf_seq (ca _ _) (wf_seq (pz _) (wf_seq (as _ _) (wf_seq (ca _ _) (wf_seq pb
      (wf_seq (ca _ _) (wf_seq (Layout.wf_callTopAt K hf) (wf_seq (ca _ _) (lo _ _))))))))
  have hC1 : Wf Pairing.progC1 := by
    unfold Pairing.progC1
    exact wf_seq (ca _ _) (wf_seq (ad _ _ _) (wf_seq (as _ _) (wf_seq (ad _ _ _) (wf_seq
      (pv _) (wf_seq (pv _) (wf_seq (as _ _) (wf_seq (ad _ _ _) (wf_seq (ca _ _) (wf_seq pb
        (wf_seq (pv _) (wf_seq (as _ _) (wf_seq (ad _ _ _) (wf_seq (ca _ _) pb)))))))))))))
  have hC2 : Wf (Pairing.progC2 K) := by
    unfold Pairing.progC2
    exact wf_seq (ca _ _) (wf_seq (ad _ _ _) (wf_seq (as _ _) (wf_seq (ad _ _ _)
      (Layout.wf_finish K))))
  exact wf_seq hA (wf_seq hB (wf_seq hC1 hC2))

/-- The dispatcher on an `Option` is well formed when its two branches are. -/
theorem Lists.wf_optElimProg {K : ℕ} (hK : 16 ≤ K) {Pg Ph : Program} (hg : Wf Pg)
    (hh : Wf Ph) : Wf (Lists.optElimProg K Pg Ph) :=
  wf_ifz (wf_seq (Lists.runsTo_stripProg (K := K) (eb := []) (es := []) hK rfl rfl).wf hh)
    (wf_seq (Combine.cleanComputeAt_snd (α := ℕ) (β := ℕ) hK ((0 : ℕ), (0 : ℕ))).wf hg)

end RAM
