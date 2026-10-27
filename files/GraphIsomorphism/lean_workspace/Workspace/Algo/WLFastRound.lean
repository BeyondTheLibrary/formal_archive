/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  One round of the fast
program on the RAM: the records of the neighbours.
-/
import Workspace.Algo.WLFastRoundSem

/-!
# One round of the fast `k`-WL program, part 1: the records

Between rounds the memory holds the input copy, the registers of the layout, `IX`, `Nb`, and
the current colors in `C` (`Algo.WLFast.RoundI`).  The first step of a round (`r1P`) writes, for
every row `r` and vertex `y`, the record `r :: (C[Nb[(rn+y)k+i]])_{i<k}` at
`Rec + (rn + y)(k+1)` and its address at `A + rn + y`; each color is read with two loads
(`O(1)` tuple addressing).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

/-- The registers a round may write. -/
def rW : List ℕ := List.range' 30 20 ++ [68] ++ List.range' 80 20

theorem mem_rW {z : ℕ} : z ∈ rW ↔ (30 ≤ z ∧ z < 50) ∨ z = 68 ∨ (80 ≤ z ∧ z < 100) := by
  simp only [rW, List.mem_append, List.mem_range'_1, List.mem_singleton]; omega

theorem nmem_rW {z : ℕ} (hz : z ∉ rW) {l : List ℕ}
    (hl : ∀ x ∈ l, (30 ≤ x ∧ x < 50) ∨ x = 68 ∨ (80 ≤ x ∧ x < 100)) : z ∉ l :=
  fun h => hz (mem_rW.2 (hl z h))

/-- **The memory between rounds**, for the current coloring `q`. -/
def RoundI (n k : ℕ) (p : RawWL) (L : Lay) (q : RawWL) (m : Mem) : Prop :=
  BaseOK n k p L m ∧ Blk m L.IX (ixPre p L.n L.N) ∧
    Blk m L.Nb ((List.range L.N).flatMap (nbRow p L.n L.k)) ∧
    ∀ r < L.N, m (L.C + idxOf L.n (tup p r)) = tblGet (q.2, tup p r)

/-- The current coloring has the tuples of the input. -/
structure QOK (n k : ℕ) (p q : RawWL) : Prop where
  wf : RawWL.WF n k q
  fst : q.1 = p.1
  keys : q.2.map Prod.fst = p.2.map Prod.fst

section Round

variable {n k : ℕ} {p q : RawWL} {L : Lay}

theorem QOK.length (hq : QOK n k p q) : q.2.length = p.2.length := by
  have := congrArg List.length hq.keys; simpa using this

theorem QOK.key (hq : QOK n k p q) {r : ℕ} (hr : r < q.2.length) : q.2[r].1 = tup p r := by
  have := congrArg (fun l => l[r]?) hq.keys
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem hr, List.getElem?_eq_getElem (by rw [← hq.length]; exact hr)]
    at this
  simp only [Option.map_some, Option.some.injEq] at this
  rw [this, tup, List.getD_eq_getElem _ _ (by rw [← hq.length]; exact hr)]

theorem persist_ok : ∀ z ∈ persist, z < 80 ∧ ¬ (30 ≤ z ∧ z < 50) ∧ z ≠ 68 := by decide

theorem BaseOK.congr {M m : Mem} (hb : BaseOK n k p L M)
    (h : ∀ z, z < L.IX → z ∉ rW → m z = M z) : BaseOK n k p L m := by
  have hF := hb.hF
  have hIX : 100 ≤ L.IX := by simp only [Lay.IX]; omega
  have hregs : RegsOK L m := hb.regs.congr (fun z hz => by
    have := persist_ok z hz
    exact h z (by omega) (by rw [mem_rW]; omega))
  have hblk : Blk m L.F (Enc.encode p) := hb.blk.congr (fun z hz1 hz2 => by
    have : z < L.IX := by rw [← hb.hLin] at hz2; simp only [Lay.IX]; omega
    exact h z this (by rw [mem_rW]; omega))
  exact ⟨hb.wf, hb.hn, hb.hk, hb.hN, hb.hLin, hb.hF, hb.k1, hregs, hblk⟩

/-- A tuple over the domain is the tuple of some row. -/
theorem BaseOK.exists_row {M : Mem} (hb : BaseOK n k p L M) {t : List ℕ} (hl : t.length = k)
    (ht : ∀ d ∈ t, d < n) : ∃ r < p.2.length, tup p r = t := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ((hb.wf.keyMem t).2 ⟨hl, ht⟩)
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hq
  exact ⟨r, hr, hb.tup_eq hr⟩

/-- **Reading a color**: `C[idx t] = c(t)` for every tuple `t` over the domain. -/
theorem RoundI.col {m : Mem} (h : RoundI n k p L q m) {t : List ℕ} (hl : t.length = k)
    (ht : ∀ d ∈ t, d < n) : m (L.C + idxOf L.n t) = tblGet (q.2, t) := by
  obtain ⟨r, hr, rfl⟩ := h.1.exists_row hl ht
  exact h.2.2.2 r (by rw [h.1.hN]; exact hr)

/-- **Reading a neighbour index.** -/
theorem RoundI.nb {m : Mem} (h : RoundI n k p L q m) {r y i : ℕ} (hr : r < L.N) (hy : y < L.n)
    (hi : i < L.k) :
    m (L.Nb + (r * (L.n * L.k) + (y * L.k + i))) = idxOf L.n ((tup p r).set i y) := by
  have hw : ∀ r, (nbRow p L.n L.k r).length = L.n * L.k := length_nbRow p L.n L.k
  rw [blk_range_flatMap_get hw h.2.2.1 hr (lt_mul_of_lt' hy hi)]
  unfold nbRow
  rw [getElem_flatMap_range_of_length (length_nbCell p L.n L.k r) L.n y i hy hi]
  simp [nbCell]

theorem blk_snoc' {m : Mem} {P : ℕ} {l : List ℕ} (h : Blk m P l) {j : ℕ} (hj : l.length = j)
    (v : ℕ) : Blk (m.update (P + j) v) P (l ++ [v]) := by
  subst hj; exact blk_snoc h v

/-- Extending a block by one cell, for any memory that agrees on the block. -/
theorem blk_snoc_of {m m' : Mem} {P : ℕ} {l : List ℕ} (h : Blk m P l) {v : ℕ}
    (hv : m' (P + l.length) = v) (hk : ∀ z, P ≤ z → z < P + l.length → m' z = m z) :
    Blk m' P (l ++ [v]) := by
  rw [Blk.append]
  refine ⟨h.congr hk, ?_⟩
  simp [Blk.cons, Blk.nil, hv]

/-! ## Step 1: the records -/

/-- The records of the rows below `r`, then of the vertices below `y` in row `r`. -/
def recPre (q p : RawWL) (n k r y : ℕ) : List ℕ :=
  (List.range r).flatMap (recRow q p n k) ++ (List.range y).flatMap (fun y => r :: nvec q p k r y)

/-- Their addresses. -/
def addrPre (Rec n k r y : ℕ) : List ℕ :=
  (List.range r).flatMap (addrRow Rec n k) ++
    (List.range y).map (fun y => Rec + (r * (n * (k + 1)) + y * (k + 1)))

theorem length_recPre (q p : RawWL) (n k r y : ℕ) :
    (recPre q p n k r y).length = r * (n * (k + 1)) + y * (k + 1) := by
  rw [recPre, List.length_append, length_range_flatMap (length_recRow q p n k),
    length_range_flatMap (w := k + 1) (fun y => by simp)]

theorem length_addrPre (Rec n k r y : ℕ) : (addrPre Rec n k r y).length = r * n + y := by
  rw [addrPre, List.length_append, length_range_flatMap (length_addrRow Rec n k)]; simp

theorem addrPre_succ (Rec n k r y : ℕ) : addrPre Rec n k r (y + 1) =
    addrPre Rec n k r y ++ [Rec + (r * (n * (k + 1)) + y * (k + 1))] := by
  simp [addrPre, List.range_succ]

/-- One color: `Rec[..] := C[Nb[..]]`. -/
def r1I : Program :=
  seq (loadTo 94 89) (seq (addTo 95 56 94) (seq (loadTo 94 95) (seq (storeTo 86 94)
  (seq (addTo 86 86 1) (seq (addTo 89 89 1) (subTo 99 99 1))))))

/-- One vertex: the address, the row, the colors. -/
def r1Y : Program :=
  seq (storeTo 88 86) (seq (addTo 88 88 1) (seq (storeTo 86 90) (seq (addTo 86 86 1)
  (seq (copyTo 99 51) (seq (whileNz 99 r1I) (subTo 97 97 1))))))

/-- One row. -/
def r1Row : Program := seq (copyTo 97 50) (seq (whileNz 97 r1Y) (seq (addTo 90 90 1) (subTo 92 92 1)))

/-- **Step 1**: all records and their addresses. -/
def r1P : Program :=
  seq (copyTo 86 59) (seq (copyTo 88 61) (seq (copyTo 89 58) (seq (assign 90 0) (seq (copyTo 92 52)
  (whileNz 92 r1Row)))))

theorem wf_r1I : Wf r1I := by unfold r1I; wf_tac

theorem wf_r1Y : Wf r1Y := by
  unfold r1Y
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_r1I) (by wf_tac))))))

theorem wf_r1Row : Wf r1Row := by
  unfold r1Row
  exact wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_r1Y) (by wf_tac))

theorem wf_r1P : Wf r1P := by
  unfold r1P
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_whileNz wf_r1Row)))))

/-- Step 1 inside row `r`, vertex `y`, after `i` colors. -/
def R1I (L : Lay) (p q : RawWL) (m0 : Mem) (r y i : ℕ) (m : Mem) : Prop :=
  i ≤ L.k ∧ m 99 = L.k - i ∧
    m 86 = L.Rec + (r * (L.n * (L.k + 1)) + y * (L.k + 1) + 1 + i) ∧
    m 88 = L.A + (r * L.n + y + 1) ∧ m 89 = L.Nb + (r * (L.n * L.k) + (y * L.k + i)) ∧
    m 90 = r ∧ m 92 = L.N - r ∧ m 97 = L.n - y ∧
    Blk m L.Rec (recPre q p L.n L.k r y ++ r :: (nvec q p L.k r y).take i) ∧
    Blk m L.A (addrPre L.Rec L.n L.k r (y + 1)) ∧ Keep rW L.Rec L.SR m0 m

/-- Step 1 inside row `r`, after `y` vertices. -/
def R1Y (L : Lay) (p q : RawWL) (m0 : Mem) (r y : ℕ) (m : Mem) : Prop :=
  y ≤ L.n ∧ m 97 = L.n - y ∧ m 86 = L.Rec + (r * (L.n * (L.k + 1)) + y * (L.k + 1)) ∧
    m 88 = L.A + (r * L.n + y) ∧ m 89 = L.Nb + (r * (L.n * L.k) + y * L.k) ∧
    m 90 = r ∧ m 92 = L.N - r ∧
    Blk m L.Rec (recPre q p L.n L.k r y) ∧ Blk m L.A (addrPre L.Rec L.n L.k r y) ∧
    Keep rW L.Rec L.SR m0 m

/-- Step 1 after `r` rows. -/
def R1R (L : Lay) (p q : RawWL) (m0 : Mem) (r : ℕ) (m : Mem) : Prop :=
  r ≤ L.N ∧ m 86 = L.Rec + r * (L.n * (L.k + 1)) ∧ m 88 = L.A + r * L.n ∧
    m 89 = L.Nb + r * (L.n * L.k) ∧ m 90 = r ∧ m 92 = L.N - r ∧
    Blk m L.Rec ((List.range r).flatMap (recRow q p L.n L.k)) ∧
    Blk m L.A ((List.range r).flatMap (addrRow L.Rec L.n L.k)) ∧ Keep rW L.Rec L.SR m0 m

/-- Addresses below `Rec` and outside the scratch registers are those of `m0`. -/
theorem keep_low {m0 m : Mem} (h : Keep rW L.Rec L.SR m0 m) {z : ℕ} (hz : z ∉ rW)
    (hz' : z < L.Rec) : m z = m0 z := h z hz (Or.inl hz')

theorem rec_lt {m0 : Mem} (hb : BaseOK n k p L m0) {r y j : ℕ} (hr : r < L.N) (hy : y < L.n)
    (hj : j < L.k + 1) :
    L.Rec + (r * (L.n * (L.k + 1)) + y * (L.k + 1) + j) < L.A := by
  have h1 := lt_mul_of_lt' hy hj
  have h2 := lt_mul_of_lt' hr h1
  simp only [Lay.A, Lay.NN]
  rw [mul_assoc]; nlinarith

theorem runsTo_r1I {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) {r y i : ℕ}
    (hr : r < L.N) (hy : y < L.n) (hi : i < L.k) (hI : R1I L p q m0 r y i m) :
    RunsTo r1I (fun m' => m' = m) (R1I L p q m0 r y (i + 1)) 7 := by
  obtain ⟨-, e99, e86, e88, e89, e90, e92, e97, hRec, hA, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  have hlen := hb.len_tup (show r < p.2.length by rw [← hb.hN]; exact hr)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hnb : L.Nb + (r * (L.n * L.k) + (y * L.k + i)) < L.Rec := by
    have h1 := lt_mul_of_lt' hy hi
    have h2 := lt_mul_of_lt' hr h1
    rw [f4, f12, mul_assoc]; omega
  -- the neighbour index and its color
  have hv1 : m (L.Nb + (r * (L.n * L.k) + (y * L.k + i))) = idxOf L.n ((tup p r).set i y) := by
    rw [keep_low hK (by rw [mem_rW]; omega) hnb]; exact h0.nb hr hy hi
  have hlt : ∀ d ∈ (tup p r).set i y, d < n := fun d hd =>
    hb.set_lt (by rw [← hb.hN]; exact hr) (by rw [← hb.hn]; exact hy) hd
  have hidx : idxOf L.n ((tup p r).set i y) < L.N := by
    rw [hb.hN, hb.hn]; exact hb.idx_lt (by rw [List.length_set, hlen]) hlt
  have hv2 : m (L.C + idxOf L.n ((tup p r).set i y)) = tblGet (q.2, (tup p r).set i y) := by
    rw [keep_low hK (by rw [mem_rW]; omega) (by omega)]
    exact h0.col (by rw [List.length_set, hlen]) hlt
  have c56 : m 56 = L.C := by rw [keep_low hK (by rw [mem_rW]; omega) (by omega), hR.r56]
  have c1 : m 1 = 1 := by rw [keep_low hK (by rw [mem_rW]; omega) (by omega), hR.r1]
  have hlp := length_recPre q p L.n L.k r y
  have hlA := length_addrPre L.Rec L.n L.k r (y + 1)
  have hRA := rec_lt hb hr hy (j := 1 + i) (by omega)
  have hki : (nvec q p L.k r y)[i]'(by simp; exact hi) = tblGet (q.2, (tup p r).set i y) := by
    simp [nvec]
  unfold r1I
  rt
  unfold R1I
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e89, e99, e88, e90, e92,
    e97, hv1, c56, hv2, c1]
  refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
  · -- the new color extends the record
    refine Blk.update (Blk.update (Blk.update ?_ (Or.inl ?_)) (Or.inl ?_)) (Or.inl ?_)
    · rw [← List.take_concat_get' _ _ (by simp; exact hi), hki, ← List.cons_append,
        ← List.append_assoc]
      refine blk_snoc' (hRec.congr (fun z h1 h2 => ?_)) ?_ _
      · simp only [List.length_append, List.length_cons, List.length_take, length_nvec] at h2
        simp (disch := omega) only [Mem.update_of_ne]
      · simp only [List.length_append, List.length_cons, List.length_take, length_nvec]; omega
    all_goals omega
  · refine hA.congr (fun z h1 h2 => ?_)
    rw [hlA] at h2
    simp (disch := omega) only [Mem.update_of_ne]
  · intro z hz hab
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hK z (by rw [mem_rW]; omega) hab

theorem runsTo_r1Y {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) {r y : ℕ}
    (hr : r < L.N) (hy : y < L.n) (hI : R1Y L p q m0 r y m) :
    RunsTo r1Y (fun m' => m' = m) (R1Y L p q m0 r (y + 1)) (L.k * 9 + 7) := by
  obtain ⟨-, e97, e86, e88, e89, e90, e92, hRec, hA, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have c51 : m 51 = L.k := by rw [keep_low hK (by rw [mem_rW]; omega) (by omega), hR.r51]
  have c1 : m 1 = 1 := by rw [keep_low hK (by rw [mem_rW]; omega) (by omega), hR.r1]
  have hlp := length_recPre q p L.n L.k r y
  have hlA := length_addrPre L.Rec L.n L.k r y
  have hRA := rec_lt hb hr hy (j := 0) (by omega)
  have hAy : r * L.n + y < L.NN := by
    have := lt_mul_of_lt' hr hy; rw [f12]; exact this
  refine RunsTo.mono (T := ((((((L.k * (7 + 2) + 1) + (0 + 1)) + 1) + 1) + 1) + 1) + 1) ?_
    (by omega)
  unfold r1Y
  refine store_seq' (add_seq' (store_seq' (add_seq' (copy_seq' ?_))))
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e88, e90, c1, c51]
  refine block_seq (T := L.k * (7 + 2) + 1) (T' := 0 + 1)
    (runsTo_countLoop (c := 99) wf_r1I (R1I L p q m0 r y) L.k 7
      (fun i m h => ⟨h.2.1, h.1⟩) (fun i m hi hI => runsTo_r1I h0 hq hr hy hi hI) _ ?_)
    (fun m2 hI2 => ?_)
  · unfold R1I
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e89, e92, e97]
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [List.take_zero]
      refine blk_snoc_of hRec ?_ (fun z h1 h2 => ?_)
      · rw [hlp]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      · rw [hlp] at h2
        simp (disch := omega) only [Mem.update_of_ne]
    · rw [addrPre_succ]
      refine blk_snoc_of hA ?_ (fun z h1 h2 => ?_)
      · rw [hlA]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      · rw [hlA] at h2
        simp (disch := omega) only [Mem.update_of_ne]
    · intro z hz hab
      rw [mem_rW] at hz
      have : z ≠ L.A + (r * L.n + y) := by omega
      have : z ≠ L.Rec + (r * (L.n * (L.k + 1)) + y * (L.k + 1)) := by omega
      simp (disch := omega) only [Mem.update_of_ne]
      exact hK z (by rw [mem_rW]; omega) hab
  · obtain ⟨-, f99, f86, f88, f89, f90, f92, f97, fRec, fA, fK⟩ := hI2
    refine sub_last' ?_
    have c1' : m2 1 = 1 := by rw [keep_low fK (by rw [mem_rW]; omega) (by omega), hR.r1]
    unfold R1Y
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f86, f88, f89, f90, f92, f97,
      c1']
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by simp)] at fRec
      rw [recPre, range_flatMap_succ, ← List.append_assoc, ← recPre]
      exact Blk.update fRec (Or.inl (by omega))
    · exact Blk.update fA (Or.inl (by omega))
    · exact fK.upd (Or.inl (by rw [mem_rW]; omega)) _

/-- The step count of one row of step 1. -/
def tR1Row (n k : ℕ) : ℕ := (n * (k * 9 + 7 + 2) + 1 + ((0 + 1) + 1)) + 1

theorem runsTo_r1Row {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) {r : ℕ}
    (hr : r < L.N) (hI : R1R L p q m0 r m) :
    RunsTo r1Row (fun m' => m' = m) (R1R L p q m0 (r + 1)) (tR1Row L.n L.k) := by
  obtain ⟨-, e86, e88, e89, e90, e92, hRec, hA, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have c50 : m 50 = L.n := by rw [keep_low hK (by rw [mem_rW]; omega) (by omega), hR.r50]
  unfold r1Row tR1Row
  refine copy_seq' ?_
  refine block_seq (T := L.n * (L.k * 9 + 7 + 2) + 1) (T' := (0 + 1) + 1)
    (runsTo_countLoop (c := 97) wf_r1Y (R1Y L p q m0 r) L.n (L.k * 9 + 7)
      (fun y m h => ⟨h.2.1, h.1⟩) (fun y m hy hI => runsTo_r1Y h0 hq hr hy hI) _ ?_)
    (fun m2 hI2 => ?_)
  · unfold R1Y
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e88, e89, e90, e92, c50]
    refine ⟨by wl_ar, by wl_ar, by simp, by simp, by simp, by wl_ar, by wl_ar, ?_, ?_, ?_⟩
    · rw [recPre]; simp only [List.range_zero, List.flatMap_nil, List.append_nil]
      exact Blk.update hRec (Or.inl (by omega))
    · rw [addrPre]; simp only [List.range_zero, List.map_nil, List.append_nil]
      exact Blk.update hA (Or.inl (by omega))
    · exact hK.upd (Or.inl (by rw [mem_rW]; omega)) _
  · obtain ⟨-, f97, f86, f88, f89, f90, f92, fRec, fA, fK⟩ := hI2
    have c1 : m2 1 = 1 := by rw [keep_low fK (by rw [mem_rW]; omega) (by omega), hR.r1]
    refine add_seq' (sub_last' ?_)
    unfold R1R
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f86, f88, f89, f90, f92, c1]
    refine ⟨by omega, by ring, by ring, by ring, by wl_ar,
      by wl_ar, ?_, ?_, ?_⟩
    · rw [range_flatMap_succ]
      exact Blk.update (Blk.update fRec (Or.inl (by omega))) (Or.inl (by omega))
    · rw [range_flatMap_succ]
      exact Blk.update (Blk.update fA (Or.inl (by omega))) (Or.inl (by omega))
    · exact (fK.upd (Or.inl (by rw [mem_rW]; omega)) _).upd (Or.inl (by rw [mem_rW]; omega)) _

/-- The step count of step 1. -/
def tR1 (N n k : ℕ) : ℕ := (N * (tR1Row n k + 2) + 1) + 1 + 1 + 1 + 1 + 1

/-- **Step 1** writes all records and their addresses. -/
theorem runsTo_r1P {m0 : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) :
    RunsTo r1P (fun m' => m' = m0) (R1R L p q m0 L.N) (tR1 L.N L.n L.k) := by
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  unfold r1P tR1
  refine copy_seq' (copy_seq' (copy_seq' (assign_seq' (copy_seq' ?_))))
  refine runsTo_countLoop (c := 92) wf_r1Row (R1R L p q m0) L.N (tR1Row L.n L.k)
    (fun r m h => ⟨h.2.2.2.2.2.1, h.1⟩) (fun r m hr hI => runsTo_r1Row h0 hq hr hI) _ ?_
  unfold R1R
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hR.r52, hR.r58, hR.r59, hR.r61]
  refine ⟨by omega, by simp, by simp, by simp, by wl_ar, by wl_ar, by simp [Blk.nil],
    by simp [Blk.nil], ?_⟩
  intro z hz hab
  rw [mem_rW] at hz
  simp (disch := omega) only [Mem.update_of_ne]

end Round

end WLFast

end Algo
