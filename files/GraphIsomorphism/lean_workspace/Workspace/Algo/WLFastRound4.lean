/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  One round of the fast
program on the RAM: sorting and ranking the strings.
-/
import Workspace.Algo.WLFastRound3

/-!
# One round of the fast `k`-WL program, part 4: sorting and ranking the strings

Step 4 (`r5P`) radix sorts the addresses of the string records by the strings (the first
`nk + 1` cells); step 5 (`r6P`) scans the sorted array and writes the dense rank of each string
into the free cell of its record.  By `Algo.WLFast.wlNewCol_eq_drank`, the rank written for row
`r` is the new color `wlNewCol q t_r` (`Algo.WLFast.runsTo_r6P`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

section Round4

variable {n k : ℕ} {p q : RawWL} {L : Lay}

/-- The string records and their addresses after step 3. -/
def R4O (L : Lay) (p q : RawWL) (m0 m : Mem) : Prop :=
  Blk m L.SR ((List.range L.N).flatMap (strRec q p L.n L.k)) ∧ Blk m L.A2 (strAddrs L L.N) ∧
    Low L m0 m

theorem R4R.out {m0 m2 m : Mem} {ys : List ℕ} (hy2 : YsOK L p q m0 m2 ys)
    (h : R4R L p q m2 L.N m) : R4O L p q m0 m :=
  ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, fun z hz hz' => keep4_low hy2.low h.2.2.2.2.2.2.2.2 hz hz'⟩

theorem mem_strAddrs {x r0 : ℕ} : x ∈ strAddrs L r0 ↔ ∃ r < r0, x = L.SR + r * (L.n * L.k + 2) := by
  simp only [strAddrs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

theorem nodup_strAddrs (L : Lay) (r0 : ℕ) : (strAddrs L r0).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have := mul_add_inj (w := L.n * L.k + 2) (a := 0) (b := 0) (by omega) (by omega)
    (by simpa using h)
  exact this.1

@[simp] theorem length_strAddrs (L : Lay) (r0 : ℕ) : (strAddrs L r0).length = r0 := by
  simp [strAddrs]

/-- A cell of a string record. -/
theorem blk_strRec {m : Mem} (h : Blk m L.SR ((List.range L.N).flatMap (strRec q p L.n L.k)))
    {r j : ℕ} (hr : r < L.N) (hj : j < L.n * L.k + 2) :
    m (L.SR + r * (L.n * L.k + 2) + j) =
      (strRec q p L.n L.k r)[j]'(by rw [length_strRec]; exact hj) := by
  rw [Nat.add_assoc]
  exact blk_range_flatMap_get (length_strRec q p L.n L.k) h hr hj

theorem strRec_eq' {M : Mem} (hb : BaseOK n k p L M) (hq : QOK n k p q) {r : ℕ} (hr : r < L.N) :
    strRec q p L.n L.k r = strOf q (tup p r) ++ [0] := by
  have hrp : r < p.2.length := by rw [← hb.hN]; exact hr
  refine strRec_eq (by rw [hb.len_tup hrp, hb.hk]) hq.fst ?_
  rw [hb.hn]; exact dom_perm hb.wf

theorem length_strOf' {M : Mem} (hb : BaseOK n k p L M) (hq : QOK n k p q) {r : ℕ}
    (hr : r < L.N) : (strOf q (tup p r)).length = L.n * L.k + 1 := by
  have := congrArg List.length (strRec_eq' hb hq hr)
  rw [length_strRec, List.length_append, List.length_singleton] at this
  omega

/-- **A string record, read with `recL`, is the string of §5.4.2.** -/
theorem recL_strRec {M m : Mem} (hb : BaseOK n k p L M) (hq : QOK n k p q)
    (h : Blk m L.SR ((List.range L.N).flatMap (strRec q p L.n L.k))) {r : ℕ} (hr : r < L.N) :
    recL m 0 (L.n * L.k + 1) (L.SR + r * (L.n * L.k + 2)) = strOf q (tup p r) := by
  have hl := length_strOf' hb hq hr
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [recL, List.getElem_map, List.getElem_range, Nat.add_zero]
  simp only [length_recL] at h1
  rw [blk_strRec h hr (by omega)]
  simp only [strRec_eq' hb hq hr]
  rw [List.getElem_append_left]

/-! ### Step 4: sorting the strings -/

/-- **Step 4**: radix sort of the string addresses. -/
def r5P : Program :=
  seq (copyTo 30 75) (seq (copyTo 31 52) (seq (assign 32 0) (seq (copyTo 33 67)
  (seq (copyTo 34 66) (seq (copyTo 35 62) radixP)))))

/-- After step 4. -/
def R5O (L : Lay) (p q : RawWL) (m0 m : Mem) : Prop :=
  ∃ zs : List ℕ, Blk m L.A2 zs ∧ zs.Perm (strAddrs L L.N) ∧
    zs.Pairwise (fun a b => recL m 0 (L.n * L.k + 1) a ≤ recL m 0 (L.n * L.k + 1) b) ∧
    Blk m L.SR ((List.range L.N).flatMap (strRec q p L.n L.k)) ∧ Low L m0 m

/-- The step count of step 4. -/
def tR5 (N n k : ℕ) : ℕ := tRadix (N + 1) N (n * k + 1) + 1 + 1 + 1 + 1 + 1 + 1

theorem str_addr_lt {M : Mem} (hb : BaseOK n k p L M) {r j : ℕ} (hr : r < L.N)
    (hj : j < L.n * L.k + 2) :
    L.SR ≤ L.SR + r * (L.n * L.k + 2) + j ∧ L.SR + r * (L.n * L.k + 2) + j < L.A2 := by
  have := str_lt hb hr hj
  constructor <;> omega

set_option maxHeartbeats 1000000 in
theorem runsTo_r5P {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) (hN : 0 < L.N)
    (hI : R4O L p q m0 m) :
    RunsTo r5P (fun m' => m' = m) (R5O L p q m0) (tR5 L.N L.n L.k) := by
  obtain ⟨hS, hA2, hl⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hql : q.2.length = L.N := by rw [hq.length, hb.hN]
  have c : ∀ z, z ∈ persist → m z = m0 z := fun z hz => by
    have := persist_ok z hz
    exact hl z (by rw [mem_rW]; omega) (by omega)
  have c1 : m 1 = 1 := by rw [c 1 (by decide), hR.r1]
  have c75 : m 75 = L.A2 := by rw [c 75 (by decide), hR.r75]
  have c52 : m 52 = L.N := by rw [c 52 (by decide), hR.r52]
  have c67 : m 67 = L.n * L.k + 1 := by rw [c 67 (by decide), hR.r67]
  have c66 : m 66 = L.N + 1 := by rw [c 66 (by decide), hR.r66]
  have c62 : m 62 = L.Cnt := by rw [c 62 (by decide), hR.r62]
  have hxl := length_strAddrs L L.N
  have hAx : ∀ x ∈ strAddrs L L.N, ∀ j < L.n * L.k + 2, L.SR ≤ x + j ∧ x + j < L.A2 := by
    intro x hx j hj
    obtain ⟨r, hr, rfl⟩ := mem_strAddrs.1 hx
    exact str_addr_lt hb hr hj
  unfold r5P tR5
  refine copy_seq' (copy_seq' (assign_seq' (copy_seq' (copy_seq' (copy_seq' ?_)))))
  simp (disch := omega) only [Mem.update_of_ne, c75, c52, c67, c66, c62]
  set m1 := (((((m.update 30 L.A2).update 31 L.N).update 32 0).update 33 (L.n * L.k + 1)).update
    34 (L.N + 1)).update 35 L.Cnt with hm1
  have d : ∀ z, 50 ≤ z → m1 z = m z := fun z hz => by
    rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]
  refine RunsTo.mono (T := tRadix (L.N + 1) (strAddrs L L.N).length (L.n * L.k + 1)) ?_
    (by rw [hxl])
  refine (runsTo_radixP (M0 := m1) (A := L.A2) (Cnt := L.Cnt) (K := L.N + 1) (f0 := 0)
    (L := L.n * L.k + 1) (xs := strAddrs L L.N) (hA2.congr (fun z h1 h2 => d z (by omega)))
    ?_ ?_ ?_ (by omega)
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact c1) ?_ ?_ ?_ ?_ ?_ ?_).weaken
    ?_
  · intro x hx j hj
    obtain ⟨r, hr, rfl⟩ := mem_strAddrs.1 hx
    have hb2 := str_addr_lt hb hr (j := j) (by omega)
    rw [Nat.add_zero, d _ (by omega), blk_strRec hS hr (by omega)]
    simp only [strRec_eq' hb hq hr]
    rw [List.getElem_append_left (by rw [length_strOf' hb hq hr]; omega)]
    rcases j with _ | j
    · simp only [strOf, List.getElem_cons_zero]
      have := tblGet_lt hq.wf (by omega) (tup p r)
      omega
    · simp only [strOf, List.getElem_cons_succ, List.getElem_map]
      omega
  · intro x hx j hj
    have := hAx x hx j (by omega)
    omega
  · rw [hxl]; omega
  all_goals (rw [hm1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, hxl])
  rintro m' ⟨⟨zs, hzs, hp, hpw⟩, hk⟩
  have e' : ∀ z, z ∉ sortW → z < L.A2 → m' z = m1 z := fun z h1 h2 => hk z h1 (Or.inl h2)
  have hS' : Blk m' L.SR ((List.range L.N).flatMap (strRec q p L.n L.k)) := by
    have hl2 := length_range_flatMap (length_strRec q p L.n L.k) L.N
    refine hS.congr (fun z h1 h2 => ?_)
    rw [hl2] at h2
    rw [e' z (by simp [sortW]; omega) (by omega), d z (by omega)]
  refine ⟨zs, hzs, hp, ?_, hS', ?_⟩
  · refine hpw.imp_of_mem (fun {a b} ha hb' hab => ?_)
    have e1 : ∀ x ∈ zs, recL m' 0 (L.n * L.k + 1) x = recL m1 0 (L.n * L.k + 1) x := by
      intro x hx
      have hx' := hp.subset hx
      simp only [recL]
      exact List.map_congr_left (fun j hj => by
        have := hAx x hx' j (by simp at hj; omega)
        exact e' _ (by simp [sortW]; omega) (by omega))
    rw [e1 a ha, e1 b hb']
    exact hab
  · intro z hz hz'
    rw [e' z (fun h => hz (mem_rW.2 (by simp [sortW] at h; omega))) (by omega), hm1]
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hl z (mem_rW.not.2 hz) hz'

/-! ### Step 5: ranking the strings -/

/-- **Step 5**: dense ranks along the sorted string addresses, into the free cells. -/
def r6P : Program :=
  seq (copyTo 30 75) (seq (copyTo 31 52) (seq (assign 32 0) (seq (copyTo 33 67)
  (seq (copyTo 34 67) rankP))))

/-- After step 5: the free cell of the string record of row `r` holds the new color. -/
def R6O (L : Lay) (p q : RawWL) (m0 m : Mem) : Prop :=
  (∀ r < L.N, m (L.SR + r * (L.n * L.k + 2) + (L.n * L.k + 1)) = wlNewCol q (tup p r)) ∧
    Low L m0 m

/-- The step count of step 5. -/
def tR6 (N n k : ℕ) : ℕ := tRank N (n * k + 1) + 1 + 1 + 1 + 1 + 1

/-- The list of the strings of all rows, as `§5.4.2` ranks them. -/
theorem drank_strs {M : Mem} (hb : BaseOK n k p L M) (hq : QOK n k p q) {r : ℕ} (hr : r < L.N) :
    drank ((List.range L.N).map (fun r => strOf q (tup p r))) (strOf q (tup p r)) =
      wlNewCol q (tup p r) := by
  have hql : q.2.length = L.N := by rw [hq.length, hb.hN]
  have hrq : r < q.2.length := by rw [hql]; exact hr
  rw [strs_eq hql (fun r hr => hq.key hr), ← hq.key hrq]
  exact (wlNewCol_eq_drank hq.wf (List.getElem_mem hrq)).symm

set_option maxHeartbeats 1000000 in
theorem runsTo_r6P {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q)
    (hI : R5O L p q m0 m) :
    RunsTo r6P (fun m' => m' = m) (R6O L p q m0) (tR6 L.N L.n L.k) := by
  obtain ⟨zs, hzs, hp, hpw, hS, hl⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have c : ∀ z, z ∈ persist → m z = m0 z := fun z hz => by
    have := persist_ok z hz
    exact hl z (by rw [mem_rW]; omega) (by omega)
  have c1 : m 1 = 1 := by rw [c 1 (by decide), hR.r1]
  have c75 : m 75 = L.A2 := by rw [c 75 (by decide), hR.r75]
  have c52 : m 52 = L.N := by rw [c 52 (by decide), hR.r52]
  have c67 : m 67 = L.n * L.k + 1 := by rw [c 67 (by decide), hR.r67]
  have hzl : zs.length = L.N := by rw [hp.length_eq, length_strAddrs]
  have hAx : ∀ x ∈ zs, ∀ j < L.n * L.k + 2, L.SR ≤ x + j ∧ x + j < L.A2 := by
    intro x hx j hj
    obtain ⟨r, hr, rfl⟩ := mem_strAddrs.1 (hp.subset hx)
    exact str_addr_lt hb hr hj
  unfold r6P tR6
  refine copy_seq' (copy_seq' (assign_seq' (copy_seq' (copy_seq' ?_))))
  simp (disch := omega) only [Mem.update_of_ne, c75, c52, c67]
  set m1 := ((((m.update 30 L.A2).update 31 L.N).update 32 0).update 33 (L.n * L.k + 1)).update
    34 (L.n * L.k + 1) with hm1
  have d : ∀ z, 50 ≤ z → m1 z = m z := fun z hz => by
    rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]
  have hrecL : ∀ x ∈ zs, recL m1 0 (L.n * L.k + 1) x = recL m 0 (L.n * L.k + 1) x := by
    intro x hx
    simp only [recL]
    exact List.map_congr_left (fun j hj => d _ (by
      have := hAx x hx j (by simp at hj; omega); omega))
  refine RunsTo.mono (T := tRank zs.length (L.n * L.k + 1)) ?_ (by rw [hzl])
  refine (runsTo_rankP m1 zs 0 (L.n * L.k + 1) (L.n * L.k + 1) (A := L.A2)
    (hzs.congr (fun z h1 h2 => d z (by omega))) ?_ (hp.nodup_iff.2 (nodup_strAddrs L L.N)) ?_ ?_ ?_
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact c1) ?_ ?_ ?_ ?_ ?_).weaken ?_
  · refine hpw.imp_of_mem (fun {a b} ha hb' hab => ?_)
    rw [hrecL a ha, hrecL b hb']
    exact hab
  · intro x hx j hj
    have := hAx x hx j (by omega)
    omega
  · intro x hx
    have := hAx x hx (L.n * L.k + 1) (by omega)
    omega
  · intro x hx x' hx' j hj he
    obtain ⟨r, hr, rfl⟩ := mem_strAddrs.1 (hp.subset hx)
    obtain ⟨r', hr', rfl⟩ := mem_strAddrs.1 (hp.subset hx')
    have := mul_add_inj (w := L.n * L.k + 2) (r := r) (r' := r') (a := L.n * L.k + 1) (b := j)
      (by omega) (by omega) (by omega)
    omega
  all_goals (try (rw [hm1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, hzl]))
  rintro m' ⟨hrk, hfr⟩
  refine ⟨fun r hr => ?_, fun z hz hz' => ?_⟩
  · have hx : L.SR + r * (L.n * L.k + 2) ∈ zs := hp.mem_iff.2 (mem_strAddrs.2 ⟨r, hr, rfl⟩)
    rw [hrk _ hx, hrecL _ hx, recL_strRec hb hq hS hr,
      drank_congr_perm (hp.map _) _, ← drank_strs hb hq hr]
    congr 1
    unfold strAddrs
    rw [List.map_map]
    exact List.map_congr_left (fun r' hr' => by
      simp only [Function.comp]
      exact recL_strRec hb hq hS (List.mem_range.1 hr') ▸ (hrecL _ (hp.mem_iff.2
        (mem_strAddrs.2 ⟨r', List.mem_range.1 hr', rfl⟩))))
  · rw [hfr z (by rw [mem_rW] at hz; simp [rkW]; omega) (fun x hx => by
      have := hAx x hx 0 (by omega); omega), hm1]
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hl z (mem_rW.not.2 hz) hz'

end Round4

end WLFast

end Algo
