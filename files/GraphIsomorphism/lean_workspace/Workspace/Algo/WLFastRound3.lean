/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  One round of the fast
program on the RAM: writing the strings.
-/
import Workspace.Algo.WLFastRound2

/-!
# One round of the fast `k`-WL program, part 3: the strings

Step 3 (`r4P`) writes, for every row `r`, the string record `strRec r` at `SR + r(nk+2)`: the
old color `C[IX[r]]`, then the `k` entries of each sorted record of row `r` (read through the
sorted address array), each complemented to `N - c`, then a free cell `0`.  It writes the
address of the string record at `A2 + r`.

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

section Round3

variable {n k : ℕ} {p q : RawWL} {L : Lay}

/-- The facts step 3 uses about the memory `m2` after step 2 and its address array `ys`. -/
structure YsOK (L : Lay) (p q : RawWL) (m0 m2 : Mem) (ys : List ℕ) : Prop where
  blk : Blk m2 L.A ys
  perm : ys.Perm (recAddrs L)
  recs : ys.map (recL m2 0 (L.k + 1)) = sortedRecs q p L.n L.k L.N
  low : Low L m0 m2

theorem YsOK.length {m0 m2 : Mem} {ys : List ℕ} (h : YsOK L p q m0 m2 ys) :
    ys.length = L.N * L.n := by rw [h.perm.length_eq, length_recAddrs]

theorem YsOK.addr {m0 m2 : Mem} {ys : List ℕ} (h : YsOK L p q m0 m2 ys)
    (hb : BaseOK n k p L m0) {j : ℕ} (hj : j < ys.length) :
    L.Rec ≤ ys.getD j 0 ∧ ys.getD j 0 + (L.k + 1) ≤ L.A := by
  rw [List.getD_eq_getElem _ _ hj]
  obtain ⟨r, hr, y, hy, e⟩ := mem_recAddrs.1 (h.perm.subset (List.getElem_mem hj))
  rw [e]
  have h1 := recAddr_lt hb hr hy (j := 0) (by omega)
  have h2 := recAddr_lt hb hr hy (j := L.k) (by omega)
  omega

/-- **The sorted records, entry by entry.** -/
theorem YsOK.val {m0 m2 : Mem} {ys : List ℕ} (h : YsOK L p q m0 m2 ys) {r y i : ℕ}
    (hr : r < L.N) (hy : y < L.n) (hi : i < L.k) :
    m2 (ys.getD (r * L.n + y) 0 + 1 + i) = ((sortV q p L.n L.k r).getD y []).getD i 0 := by
  have hj : r * L.n + y < ys.length := by rw [h.length]; exact lt_mul_of_lt' hr hy
  have hs : r * L.n + y < (sortedRecs q p L.n L.k L.N).length := by
    rw [length_sortedRecs]; exact lt_mul_of_lt' hr hy
  have e1 := congrArg (fun l => l[r * L.n + y]?) h.recs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hs,
    Option.map_some, Option.some.injEq] at e1
  rw [getElem_sortedRecs hr hy hs] at e1
  have e2 := congrArg (fun l => l[i + 1]?) e1
  have hyl : y < (sortV q p L.n L.k r).length := by simp; exact hy
  have hil : i < ((sortV q p L.n L.k r)[y]).length := by
    rw [length_of_mem_sortV (List.getElem_mem hyl)]; exact hi
  simp only [recL, List.getElem?_map, List.getElem?_range (show i + 1 < L.k + 1 by omega),
    Option.map_some, List.getElem?_cons_succ, List.getElem?_eq_getElem hil,
    Option.some.injEq] at e2
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hyl, List.getD_eq_getElem _ _ hil,
    ← e2]
  congr 1; omega

/-- The complemented entries of the sorted record `y` of row `r`. -/
def valsY (q p : RawWL) (n k r y : ℕ) : List ℕ :=
  (List.range k).map (fun i => q.2.length - (((sortV q p n k r).getD y []).getD i 0))

@[simp] theorem length_valsY (q p : RawWL) (n k r y : ℕ) : (valsY q p n k r y).length = k := by
  simp [valsY]

theorem length_strRec (q p : RawWL) (n k r : ℕ) : (strRec q p n k r).length = n * k + 2 := by
  have := length_range_flatMap (length_valsY q p n k r) n
  simp only [strRec, List.length_append, List.length_cons, List.length_singleton]
  rw [show (List.range n).flatMap (fun y => (List.range k).map
    (fun i => q.2.length - (((sortV q p n k r).getD y []).getD i 0))) =
    (List.range n).flatMap (valsY q p n k r) from rfl, this]
  simp

/-- The string records of the rows below `r`, then the color and the `y` first records of row
`r`, then `i` entries of record `y`. -/
def pre4 (q p : RawWL) (n k r y i : ℕ) : List ℕ :=
  (List.range r).flatMap (strRec q p n k) ++
    (tblGet (q.2, tup p r) :: (List.range y).flatMap (valsY q p n k r)) ++
    (valsY q p n k r y).take i

theorem length_pre4 (q p : RawWL) (n k r y : ℕ) {i : ℕ} (hi : i ≤ k) :
    (pre4 q p n k r y i).length = r * (n * k + 2) + 1 + y * k + i := by
  rw [pre4, List.length_append, List.length_append, List.length_cons,
    length_range_flatMap (length_strRec q p n k), length_range_flatMap (length_valsY q p n k r),
    List.length_take, length_valsY]
  omega

theorem pre4_succ (q p : RawWL) (n k r y : ℕ) {i : ℕ} (hi : i < k) :
    pre4 q p n k r y (i + 1) =
      pre4 q p n k r y i ++ [q.2.length - (((sortV q p n k r).getD y []).getD i 0)] := by
  rw [pre4, pre4, ← List.take_concat_get' _ _ (by simp; exact hi), List.append_assoc]
  simp [valsY]

theorem pre4_next (q p : RawWL) (n k r y : ℕ) : pre4 q p n k r y k = pre4 q p n k r (y + 1) 0 := by
  rw [pre4, pre4, List.take_of_length_le (by simp), List.take_zero, List.append_nil,
    range_flatMap_succ, List.append_assoc, ← List.cons_append]

theorem pre4_row (q p : RawWL) (n k r : ℕ) :
    pre4 q p n k r n 0 ++ [0] = (List.range (r + 1)).flatMap (strRec q p n k) := by
  rw [pre4, List.take_zero, List.append_nil, range_flatMap_succ, List.append_assoc]
  rfl

theorem pre4_zero (q p : RawWL) (n k r : ℕ) :
    pre4 q p n k r 0 0 = (List.range r).flatMap (strRec q p n k) ++ [tblGet (q.2, tup p r)] := by
  simp [pre4]

/-- The addresses of the string records. -/
def strAddrs (L : Lay) (r : ℕ) : List ℕ := (List.range r).map (fun r => L.SR + r * (L.n * L.k + 2))

/-! ### The program -/

/-- One entry: `SR[..] := N - Rec[..]`. -/
def r4I : Program :=
  seq (loadTo 94 90) (seq (subTo 94 52 94) (seq (storeTo 86 94) (seq (addTo 86 86 1)
  (seq (addTo 90 90 1) (subTo 99 99 1)))))

/-- One sorted record. -/
def r4Y : Program :=
  seq (loadTo 90 88) (seq (addTo 88 88 1) (seq (addTo 90 90 1) (seq (copyTo 99 51)
  (seq (whileNz 99 r4I) (subTo 97 97 1)))))

/-- One row: the address, the old color, the records, the free cell. -/
def r4Row : Program :=
  seq (storeTo 89 86) (seq (addTo 89 89 1) (seq (loadTo 94 87) (seq (addTo 87 87 1)
  (seq (addTo 95 56 94) (seq (loadTo 94 95) (seq (storeTo 86 94) (seq (addTo 86 86 1)
  (seq (copyTo 97 50) (seq (whileNz 97 r4Y) (seq (assign 94 0) (seq (storeTo 86 94)
  (seq (addTo 86 86 1) (subTo 92 92 1)))))))))))))

/-- **Step 3**: the string records and their addresses. -/
def r4P : Program :=
  seq (copyTo 86 60) (seq (copyTo 88 61) (seq (copyTo 89 75) (seq (copyTo 87 55)
  (seq (copyTo 92 52) (whileNz 92 r4Row)))))

theorem wf_r4I : Wf r4I := by unfold r4I; wf_tac

theorem wf_r4Y : Wf r4Y := by
  unfold r4Y
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (wf_whileNz wf_r4I) (by wf_tac)))))

theorem wf_r4Row : Wf r4Row := by
  unfold r4Row
  refine wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_r4Y) (by wf_tac))))))))))

theorem wf_r4P : Wf r4P := by
  unfold r4P
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_whileNz wf_r4Row)))))

/-! ### Invariants -/

/-- Step 3 after `r` rows. -/
def R4R (L : Lay) (p q : RawWL) (m2 : Mem) (r : ℕ) (m : Mem) : Prop :=
  r ≤ L.N ∧ m 86 = L.SR + r * (L.n * L.k + 2) ∧ m 88 = L.A + r * L.n ∧ m 89 = L.A2 + r ∧
    m 87 = L.IX + r ∧ m 92 = L.N - r ∧
    Blk m L.SR ((List.range r).flatMap (strRec q p L.n L.k)) ∧ Blk m L.A2 (strAddrs L r) ∧
    Keep rW L.SR L.Cnt m2 m

/-- Step 3 in row `r`, after `y` records. -/
def R4Y (L : Lay) (p q : RawWL) (m2 : Mem) (r y : ℕ) (m : Mem) : Prop :=
  y ≤ L.n ∧ m 97 = L.n - y ∧ m 86 = L.SR + (r * (L.n * L.k + 2) + 1 + y * L.k) ∧
    m 88 = L.A + (r * L.n + y) ∧ m 89 = L.A2 + (r + 1) ∧ m 87 = L.IX + (r + 1) ∧
    m 92 = L.N - r ∧ Blk m L.SR (pre4 q p L.n L.k r y 0) ∧ Blk m L.A2 (strAddrs L (r + 1)) ∧
    Keep rW L.SR L.Cnt m2 m

/-- Step 3 in row `r`, record `y`, after `i` entries. -/
def R4I (L : Lay) (p q : RawWL) (m2 : Mem) (ys : List ℕ) (r y i : ℕ) (m : Mem) : Prop :=
  i ≤ L.k ∧ m 99 = L.k - i ∧ m 90 = ys.getD (r * L.n + y) 0 + 1 + i ∧
    m 86 = L.SR + (r * (L.n * L.k + 2) + 1 + y * L.k + i) ∧
    m 88 = L.A + (r * L.n + y + 1) ∧ m 97 = L.n - y ∧ m 89 = L.A2 + (r + 1) ∧
    m 87 = L.IX + (r + 1) ∧ m 92 = L.N - r ∧ Blk m L.SR (pre4 q p L.n L.k r y i) ∧
    Blk m L.A2 (strAddrs L (r + 1)) ∧ Keep rW L.SR L.Cnt m2 m

theorem str_lt {M : Mem} (hb : BaseOK n k p L M) {r j : ℕ} (hr : r < L.N) (hj : j < L.n * L.k + 2) :
    L.SR + (r * (L.n * L.k + 2) + j) < L.A2 := by
  have := lt_mul_of_lt' hr hj
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  omega

/-- Registers and cells below `SR`, during step 3. -/
theorem keep4_low {m0 m2 m : Mem} (hl : Low L m0 m2) (hK : Keep rW L.SR L.Cnt m2 m) {z : ℕ}
    (hz : z ∉ rW) (hz' : z < L.Rec) : m z = m0 z := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  rw [hK z hz (Or.inl (by omega)), hl z hz hz']

set_option maxHeartbeats 1000000 in
theorem runsTo_r4I {m0 m2 m : Mem} {ys : List ℕ} (h0 : RoundI n k p L q m0) (hq : QOK n k p q)
    (hy2 : YsOK L p q m0 m2 ys) {r y i : ℕ} (hr : r < L.N) (hy : y < L.n) (hi : i < L.k)
    (hI : R4I L p q m2 ys r y i m) :
    RunsTo r4I (fun m' => m' = m) (R4I L p q m2 ys r y (i + 1)) 6 := by
  obtain ⟨-, e99, e90, e86, e88, e97, e89, e87, e92, hS, hA2, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hql : q.2.length = L.N := by rw [hq.length, hb.hN]
  have hj : r * L.n + y < ys.length := by rw [hy2.length]; exact lt_mul_of_lt' hr hy
  have hya := hy2.addr hb hj
  have c52 : m 52 = L.N := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r52]
  have c1 : m 1 = 1 := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r1]
  have cv : m (ys.getD (r * L.n + y) 0 + 1 + i) =
      ((sortV q p L.n L.k r).getD y []).getD i 0 := by
    rw [hK _ (by rw [mem_rW]; omega) (Or.inl (by omega)), hy2.val hr hy hi]
  have hlp := length_pre4 q p L.n L.k r y (le_of_lt hi)
  have hs := str_lt hb hr (j := 1 + y * L.k + i) (by
    have := lt_mul_of_lt' hy hi; omega)
  have hsl : strAddrs L (r + 1) = strAddrs L (r + 1) := rfl
  have hA2l : (strAddrs L (r + 1)).length = r + 1 := by simp [strAddrs]
  unfold r4I
  rt
  unfold R4I
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e90, e86, e99, e88, e97, e89,
    e87, e92, c52, c1, cv]
  refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar,
    ?_, ?_, ?_⟩
  · rw [pre4_succ q p L.n L.k r y hi, hql]
    refine blk_snoc_of hS ?_ (fun z h1 h2 => ?_)
    · rw [hlp]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
    · rw [hlp] at h2
      simp (disch := omega) only [Mem.update_of_ne]
  · refine hA2.congr (fun z h1 h2 => ?_)
    rw [hA2l] at h2
    simp (disch := omega) only [Mem.update_of_ne]
  · intro z hz hab
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hK z (by rw [mem_rW]; omega) hab

/-- The step count of one record of step 3. -/
def tR4Y (k : ℕ) : ℕ := (k * (6 + 2) + 1 + 1) + 1 + 1 + 1 + 1

set_option maxHeartbeats 1000000 in
theorem runsTo_r4Y {m0 m2 m : Mem} {ys : List ℕ} (h0 : RoundI n k p L q m0) (hq : QOK n k p q)
    (hy2 : YsOK L p q m0 m2 ys) {r y : ℕ} (hr : r < L.N) (hy : y < L.n)
    (hI : R4Y L p q m2 r y m) :
    RunsTo r4Y (fun m' => m' = m) (R4Y L p q m2 r (y + 1)) (tR4Y L.k) := by
  obtain ⟨-, e97, e86, e88, e89, e87, e92, hS, hA2, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hj : r * L.n + y < ys.length := by rw [hy2.length]; exact lt_mul_of_lt' hr hy
  have hya := hy2.addr hb hj
  have c51 : m 51 = L.k := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r51]
  have c1 : m 1 = 1 := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r1]
  have cA : m (L.A + (r * L.n + y)) = ys.getD (r * L.n + y) 0 := by
    have hl := hy2.length
    rw [hK _ (by rw [mem_rW]; omega) (Or.inl (by rw [hl] at hj; omega)), hy2.blk _ hj,
      List.getD_eq_getElem _ _ hj]
  have hA2l : (strAddrs L (r + 1)).length = r + 1 := by simp [strAddrs]
  have hlp := length_pre4 q p L.n L.k r y (Nat.zero_le _)
  unfold r4Y tR4Y
  refine load_seq' (add_seq' (add_seq' (copy_seq' ?_)))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e88, cA, c1, c51]
  refine block_seq (T := L.k * (6 + 2) + 1) (T' := 1)
    (runsTo_countLoop (c := 99) wf_r4I (R4I L p q m2 ys r y) L.k 6
      (fun i m h => ⟨h.2.1, h.1⟩) (fun i m hi hI => runsTo_r4I h0 hq hy2 hr hy hi hI) _ ?_)
    (fun m3 hI3 => ?_)
  · unfold R4I
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e97, e89, e87, e92]
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar,
      ?_, ?_, ?_⟩
    · refine hS.congr (fun z h1 h2 => ?_)
      simp (disch := omega) only [Mem.update_of_ne]
    · refine hA2.congr (fun z h1 h2 => ?_)
      simp (disch := omega) only [Mem.update_of_ne]
    · intro z hz hab
      rw [mem_rW] at hz
      simp (disch := omega) only [Mem.update_of_ne]
      exact hK z (by rw [mem_rW]; omega) hab
  · obtain ⟨-, f99, f90, f86, f88, f97, f89, f87, f92, fS, fA2, fK⟩ := hI3
    have c1' : m3 1 = 1 := by rw [keep4_low hy2.low fK (by rw [mem_rW]; omega) (by omega), hR.r1]
    refine sub_last' ?_
    unfold R4Y
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f86, f88, f97, f89, f87, f92,
      c1']
    refine ⟨by omega, by omega, by ring, by ring, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [← pre4_next]
      exact fS.update (Or.inl (by omega))
    · exact fA2.update (Or.inl (by omega))
    · exact fK.upd (Or.inl (by rw [mem_rW]; omega)) _

/-- The step count of one row of step 3. -/
def tR4Row (n k : ℕ) : ℕ := (n * (tR4Y k + 2) + 1 + 4) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

/-- `IX[r]` and `C[IX[r]]` during a round. -/
theorem RoundI.ix {m0 : Mem} (h0 : RoundI n k p L q m0) {r : ℕ} (hr : r < L.N) :
    m0 (L.IX + r) = idxOf L.n (tup p r) := by
  rw [h0.2.1 r (by simp [ixPre]; exact hr)]
  simp [ixPre]

set_option maxHeartbeats 1000000 in
theorem runsTo_r4Row {m0 m2 m : Mem} {ys : List ℕ} (h0 : RoundI n k p L q m0)
    (hq : QOK n k p q) (hy2 : YsOK L p q m0 m2 ys) {r : ℕ} (hr : r < L.N)
    (hI : R4R L p q m2 r m) :
    RunsTo r4Row (fun m' => m' = m) (R4R L p q m2 (r + 1)) (tR4Row L.n L.k) := by
  obtain ⟨-, e86, e88, e89, e87, e92, hS, hA2, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hrp : r < p.2.length := by rw [← hb.hN]; exact hr
  have hidx : idxOf L.n (tup p r) < L.N := by rw [hb.hN]; exact hb.idxL_lt hrp
  have c50 : m 50 = L.n := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r50]
  have c56 : m 56 = L.C := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r56]
  have c1 : m 1 = 1 := by rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), hR.r1]
  have cIX : m (L.IX + r) = idxOf L.n (tup p r) := by
    rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), h0.ix hr]
  have cC : m (L.C + idxOf L.n (tup p r)) = tblGet (q.2, tup p r) := by
    rw [keep4_low hy2.low hK (by rw [mem_rW]; omega) (by omega), h0.2.2.2 r hr]
  have hA2l : ∀ r, (strAddrs L r).length = r := fun r => by simp [strAddrs]
  have hSl := length_range_flatMap (length_strRec q p L.n L.k) r
  have hs0 := str_lt hb hr (j := 0) (by omega)
  have hsn := str_lt hb hr (j := 1 + L.n * L.k) (by omega)
  unfold r4Row tR4Row
  refine store_seq' (add_seq' (load_seq' (add_seq' (add_seq' (load_seq' (store_seq' (add_seq'
    (copy_seq' ?_))))))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e89, e87, cIX, c56, cC, c1,
    c50]
  refine block_seq (T := L.n * (tR4Y L.k + 2) + 1) (T' := 4)
    (runsTo_countLoop (c := 97) wf_r4Y (R4Y L p q m2 r) L.n (tR4Y L.k)
      (fun y m h => ⟨h.2.1, h.1⟩) (fun y m hy hI => runsTo_r4Y h0 hq hy2 hr hy hI) _ ?_)
    (fun m3 hI3 => ?_)
  · unfold R4Y
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e88, e92]
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [pre4_zero]
      refine blk_snoc_of hS ?_ (fun z h1 h2 => ?_)
      · rw [hSl]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      · rw [hSl] at h2
        simp (disch := omega) only [Mem.update_of_ne]
    · rw [strAddrs, range_map_succ, ← strAddrs]
      refine blk_snoc_of hA2 ?_ (fun z h1 h2 => ?_)
      · rw [hA2l]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      · rw [hA2l] at h2
        simp (disch := omega) only [Mem.update_of_ne]
    · intro z hz hab
      rw [mem_rW] at hz
      simp (disch := omega) only [Mem.update_of_ne]
      exact hK z (by rw [mem_rW]; omega) hab
  · obtain ⟨-, f97, f86, f88, f89, f87, f92, fS, fA2, fK⟩ := hI3
    have c1' : m3 1 = 1 := by rw [keep4_low hy2.low fK (by rw [mem_rW]; omega) (by omega), hR.r1]
    have hlp := length_pre4 q p L.n L.k r L.n (Nat.zero_le _)
    rt
    unfold R4R
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f86, f88, f89, f87, f92, c1']
    refine ⟨by omega, by ring, by ring, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [← pre4_row]
      refine blk_snoc_of fS ?_ (fun z h1 h2 => ?_)
      · rw [hlp, show L.SR + (r * (L.n * L.k + 2) + 1 + L.n * L.k + 0) =
          L.SR + (r * (L.n * L.k + 2) + 1 + L.n * L.k) by omega]
        simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      · rw [hlp] at h2
        simp (disch := omega) only [Mem.update_of_ne]
    · refine fA2.congr (fun z h1 h2 => ?_)
      rw [hA2l] at h2
      simp (disch := omega) only [Mem.update_of_ne]
    · intro z hz hab
      rw [mem_rW] at hz
      simp (disch := omega) only [Mem.update_of_ne]
      exact fK z (by rw [mem_rW]; omega) hab

/-- The step count of step 3. -/
def tR4 (N n k : ℕ) : ℕ := (N * (tR4Row n k + 2) + 1) + 1 + 1 + 1 + 1 + 1

/-- **Step 3** writes the string records and their addresses. -/
theorem runsTo_r4P {m0 m2 : Mem} {ys : List ℕ} (h0 : RoundI n k p L q m0) (hq : QOK n k p q)
    (hy2 : YsOK L p q m0 m2 ys) :
    RunsTo r4P (fun m' => m' = m2) (R4R L p q m2 L.N) (tR4 L.N L.n L.k) := by
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have g : ∀ z, z ∉ rW → z < L.Rec → m2 z = m0 z := hy2.low
  unfold r4P tR4
  refine copy_seq' (copy_seq' (copy_seq' (copy_seq' (copy_seq' ?_))))
  refine runsTo_countLoop (c := 92) wf_r4Row (R4R L p q m2) L.N (tR4Row L.n L.k)
    (fun r m h => ⟨h.2.2.2.2.2.1, h.1⟩) (fun r m hr hI => runsTo_r4Row h0 hq hy2 hr hI) _ ?_
  unfold R4R
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
  rw [g 60 (by rw [mem_rW]; omega) (by omega), g 61 (by rw [mem_rW]; omega) (by omega),
    g 75 (by rw [mem_rW]; omega) (by omega), g 55 (by rw [mem_rW]; omega) (by omega),
    g 52 (by rw [mem_rW]; omega) (by omega), hR.r60, hR.r61, hR.r75, hR.r55, hR.r52]
  refine ⟨by omega, by simp, by simp, by simp, by simp, by simp, by simp [Blk.nil],
    by simp [strAddrs, Blk.nil], ?_⟩
  intro z hz hab
  rw [mem_rW] at hz
  simp (disch := omega) only [Mem.update_of_ne]

end Round3

end WLFast

end Algo
