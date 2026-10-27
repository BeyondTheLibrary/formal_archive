/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  One round of the fast
program on the RAM: the new colors, the stop flag, and the whole round.
-/
import Workspace.Algo.WLFastRound4

/-!
# One round of the fast `k`-WL program, part 5: the new colors and the whole round

Step 6 (`r7P`) copies the rank of every row into `C[IX[r]]` and sets the flag (register `68`)
to a nonzero value exactly when some color changed.  The whole round (`roundP`) turns the
memory of the coloring `q` into the memory of the coloring `rawWLStep q`, and its flag is `0`
exactly when `rawWLStep q = q` (`Algo.WLFast.runsTo_roundP`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

section Round5

variable {n k : ℕ} {p q : RawWL} {L : Lay}

/-- One row: `C[IX[r]] := rank`, and the flag grows by `|new - old|`. -/
def r7Body : Program :=
  seq (loadTo 94 86) (seq (loadTo 95 87) (seq (addTo 87 87 1) (seq (addTo 95 56 95)
  (seq (loadTo 96 95) (seq (subTo 97 94 96) (seq (addTo 68 68 97) (seq (subTo 97 96 94)
  (seq (addTo 68 68 97) (seq (storeTo 95 94) (seq (addTo 86 86 64) (subTo 92 92 1)))))))))))

/-- **Step 6**: the new colors and the flag. -/
def r7P : Program :=
  seq (assign 68 0) (seq (addTo 86 60 67) (seq (copyTo 87 55) (seq (copyTo 92 52)
  (whileNz 92 r7Body))))

theorem wf_r7Body : Wf r7Body := by unfold r7Body; wf_tac

theorem wf_r7P : Wf r7P := by
  unfold r7P
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_whileNz wf_r7Body))))

/-- Step 6 after `r` rows; `m6` is the memory after step 5. -/
def R7I (L : Lay) (p q : RawWL) (m6 : Mem) (r : ℕ) (m : Mem) : Prop :=
  r ≤ L.N ∧ m 86 = L.SR + (r * (L.n * L.k + 2) + (L.n * L.k + 1)) ∧ m 87 = L.IX + r ∧
    m 92 = L.N - r ∧
    (m 68 = 0 ↔ ∀ r' < r, wlNewCol q (tup p r') = tblGet (q.2, tup p r')) ∧
    (∀ r' < L.N, m (L.C + idxOf L.n (tup p r')) =
      if r' < r then wlNewCol q (tup p r') else tblGet (q.2, tup p r')) ∧
    ∀ z, z ∉ rW → (z < L.C ∨ L.T ≤ z) → m z = m6 z

set_option maxHeartbeats 1000000 in
theorem runsTo_r7Body {m0 m6 m : Mem} (h0 : RoundI n k p L q m0) (h6 : R6O L p q m0 m6) {r : ℕ}
    (hr : r < L.N) (hI : R7I L p q m6 r m) :
    RunsTo r7Body (fun m' => m' = m) (R7I L p q m6 (r + 1)) 12 := by
  obtain ⟨-, e86, e87, e92, hfl, hC, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hrp : r < p.2.length := by rw [← hb.hN]; exact hr
  have hidx : idxOf L.n (tup p r) < L.N := by rw [hb.hN]; exact hb.idxL_lt hrp
  have g : ∀ z, z ∉ rW → z < L.C → m z = m0 z := fun z h1 h2 => by
    rw [hK z h1 (Or.inl h2), h6.2 z h1 (by omega)]
  have c1 : m 1 = 1 := by rw [g 1 (by rw [mem_rW]; omega) (by omega), hR.r1]
  have c56 : m 56 = L.C := by rw [g 56 (by rw [mem_rW]; omega) (by omega), hR.r56]
  have c64 : m 64 = L.n * L.k + 2 := by rw [g 64 (by rw [mem_rW]; omega) (by omega), hR.r64]
  have cIX : m (L.IX + r) = idxOf L.n (tup p r) := by
    rw [g _ (by rw [mem_rW]; omega) (by omega), h0.ix hr]
  have hs := str_lt hb hr (j := L.n * L.k + 1) (by omega)
  have crk : m (L.SR + (r * (L.n * L.k + 2) + (L.n * L.k + 1))) = wlNewCol q (tup p r) := by
    rw [hK _ (by rw [mem_rW]; omega) (Or.inr (by omega)), ← Nat.add_assoc, h6.1 r hr]
  have cC : m (L.C + idxOf L.n (tup p r)) = tblGet (q.2, tup p r) := by
    rw [hC r hr, if_neg (lt_irrefl r)]
  unfold r7Body
  rt
  unfold R7I
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e87, e92, crk, cIX, c56,
    cC, c1, c64]
  refine ⟨by omega, by ring, by wl_ar, by wl_ar, ?_, fun r' hr' => ?_, fun z hz hab => ?_⟩
  · constructor
    · intro h0'
      have hz : m 68 = 0 := by omega
      have he : wlNewCol q (tup p r) = tblGet (q.2, tup p r) := by omega
      intro r' hr'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with h | h
      · exact hfl.1 hz r' h
      · rw [h]; exact he
    · intro h
      have hz := hfl.2 (fun r' hr' => h r' (by omega))
      have he := h r (by omega)
      omega
  · by_cases hrr : r' = r
    · subst hrr
      simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      rw [if_pos (by omega)]
    · have hr'p : r' < p.2.length := by rw [← hb.hN]; exact hr'
      have hne := hb.idx_ne hrp hr'p (Ne.symm hrr)
      have hidx' : idxOf L.n (tup p r') < L.N := by rw [hb.hN]; exact hb.idxL_lt hr'p
      simp (disch := omega) only [Mem.update_of_ne]
      rw [hC r' hr']
      by_cases h : r' < r
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
  · rw [mem_rW] at hz
    have hz1 : z ≠ L.C + idxOf L.n (tup p r) := by omega
    simp (disch := omega) only [Mem.update_of_ne]
    exact hK z (by rw [mem_rW]; omega) hab

/-- The step count of step 6. -/
def tR7 (N : ℕ) : ℕ := (N * (12 + 2) + 1) + 1 + 1 + 1 + 1

theorem runsTo_r7P {m0 m6 : Mem} (h0 : RoundI n k p L q m0) (h6 : R6O L p q m0 m6) :
    RunsTo r7P (fun m' => m' = m6) (R7I L p q m6 L.N) (tR7 L.N) := by
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have g : ∀ z, z ∉ rW → z < L.Rec → m6 z = m0 z := h6.2
  unfold r7P tR7
  refine assign_seq' (add_seq' (copy_seq' (copy_seq' ?_)))
  refine runsTo_countLoop (c := 92) wf_r7Body (R7I L p q m6) L.N 12
    (fun r m h => ⟨h.2.2.2.1, h.1⟩) (fun r m hr hI => runsTo_r7Body h0 h6 hr hI) _ ?_
  unfold R7I
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  rw [g 60 (by rw [mem_rW]; omega) (by omega), g 67 (by rw [mem_rW]; omega) (by omega),
    g 55 (by rw [mem_rW]; omega) (by omega), g 52 (by rw [mem_rW]; omega) (by omega), hR.r60,
    hR.r67, hR.r55, hR.r52]
  refine ⟨by omega, by simp, by simp, by simp, by simp, fun r' hr' => ?_, fun z hz hab => ?_⟩
  · have hr'p : r' < p.2.length := by rw [← hb.hN]; exact hr'
    have hidx' : idxOf L.n (tup p r') < L.N := by rw [hb.hN]; exact hb.idxL_lt hr'p
    try simp (disch := omega) only [Mem.update_of_ne]
    rw [if_neg (by omega), g _ (by rw [mem_rW]; omega) (by omega), h0.2.2.2 r' hr']
  · rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]

/-! ## The whole round -/

theorem wf_radixP : Wf radixP := by
  unfold radixP radPre; exact wf_seq (by wf_tac) (wf_whileNz wf_radBody)

theorem wf_rankP : Wf rankP := by
  unfold rankP rkPre
  exact wf_ifz (wf_seq (by wf_tac) (wf_whileNz wf_rkBody)) Algo.ExplLinear.wf_nil

/-- **One round** of `k`-ary WL refinement (§5.4.2): records, sort, strings, sort, ranks, new
colors. -/
def roundP : Program := seq r1P (seq r2P (seq r4P (seq r5P (seq r6P r7P))))

theorem wf_roundP : Wf roundP := by
  unfold roundP
  refine wf_seq wf_r1P (wf_seq ?_ (wf_seq wf_r4P (wf_seq ?_ (wf_seq ?_ wf_r7P))))
  · unfold r2P; exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq
      (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) wf_radixP)))))
  · unfold r5P; exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq
      (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) wf_radixP)))))
  · unfold r6P; exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq
      (by wf_tac) (wf_seq (by wf_tac) wf_rankP))))

/-- The step count of one round. -/
def tRound (N n k : ℕ) : ℕ :=
  tR1 N n k + (tR2 N n k + (tR4 N n k + (tR5 N n k + (tR6 N n k + tR7 N))))

theorem QOK.step (hq : QOK n k p q) : QOK n k p (rawWLStep q) :=
  ⟨rawWLStep_wf hq.wf, by rw [rawWLStep_fst, hq.fst], by rw [rawWLStep_keys, hq.keys]⟩

/-- **One round on the RAM.**  From the memory of the coloring `q`, the round reaches the
memory of `rawWLStep q`, and the flag is `0` exactly when the round changed nothing.  The
memory below `C` changes only in the scratch registers. -/
theorem runsTo_roundP {m0 : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) (hN : 0 < L.N) :
    RunsTo roundP (fun m => m = m0)
      (fun m => RoundI n k p L (rawWLStep q) m ∧ (m 68 = 0 ↔ rawWLStep q = q) ∧
        ∀ z, z ∉ rW → z < L.C → m z = m0 z)
      (tRound L.N L.n L.k) := by
  have hb := h0.1
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hql : q.2.length = L.N := by rw [hq.length, hb.hN]
  unfold roundP tRound
  refine block_seq (runsTo_r1P h0 hq) (fun m1 h1 => ?_)
  refine block_seq (runsTo_r2P h0 hq hN h1) (fun m2 ⟨ys, hA, hp, hrecs, _, hl⟩ => ?_)
  have hy2 : YsOK L p q m0 m2 ys := ⟨hA, hp, hrecs, hl⟩
  refine block_seq (runsTo_r4P h0 hq hy2) (fun m4 h4 => ?_)
  refine block_seq (runsTo_r5P h0 hq hN (h4.out hy2)) (fun m5 h5 => ?_)
  refine block_seq (runsTo_r6P h0 hq h5) (fun m6 h6 => ?_)
  refine (runsTo_r7P h0 h6).weaken (fun m7 h7 => ?_)
  obtain ⟨-, -, -, -, hfl, hC, hK⟩ := h7
  have g : ∀ z, z ∉ rW → z < L.C → m7 z = m0 z := fun z h1 h2 => by
    rw [hK z h1 (Or.inl h2), h6.2 z h1 (by omega)]
  have hkey : ∀ r (hr : r < q.2.length), q.2[r].1 = tup p r := fun r hr => hq.key hr
  refine ⟨⟨hb.congr (fun z h1 h2 => g z h2 (by omega)), ?_, ?_, fun r hr => ?_⟩, ?_, g⟩
  · refine h0.2.1.congr (fun z h1 h2 => ?_)
    simp only [ixPre, List.length_map, List.length_range] at h2
    exact g z (by rw [mem_rW]; omega) (by omega)
  · have hl2 := length_range_flatMap (length_nbRow p L.n L.k) L.N
    refine h0.2.2.1.congr (fun z h1 h2 => ?_)
    rw [hl2] at h2
    have : L.N * (L.n * L.k) = L.NN * L.k := by rw [f12, mul_assoc]
    rw [hK z (by rw [mem_rW]; omega) (Or.inr (by omega)), h6.2 z (by rw [mem_rW]; omega)
      (by omega)]
  · have hrq : r < q.2.length := by rw [hql]; exact hr
    rw [hC r hr, if_pos hr, ← hkey r hrq, tblGet_rawWLStep (List.getElem_mem hrq)]
  · rw [hfl, step_eq_iff]
    constructor
    · intro h r hr
      rw [← tblGet_of_mem hq.wf (List.getElem_mem hr), hkey r hr]
      exact h r (by rw [← hql]; exact hr)
    · intro h r hr
      have hrq : r < q.2.length := by rw [hql]; exact hr
      have := h r hrq
      rw [← tblGet_of_mem hq.wf (List.getElem_mem hrq), hkey r hrq] at this
      exact this

end Round5

end WLFast

end Algo
