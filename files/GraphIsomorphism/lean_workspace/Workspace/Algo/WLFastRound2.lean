/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  One round of the fast
program on the RAM: sorting the records, writing the strings.
-/
import Workspace.Algo.WLFastRound

/-!
# One round of the fast `k`-WL program, part 2: the sorted records and the strings

Step 2 (`r2P`) radix sorts the addresses of the records by the records (`Algo.WLFast.runsTo_r2P`);
afterwards the records listed through the address array are `sortedRecs`.  Step 3 (`r4P`) writes,
for every row, the string record `strRec` (old color, then the complemented sorted tuples, then
a free cell) and its address.

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

section Round2

variable {n k : ℕ} {p q : RawWL} {L : Lay}

/-- The memory below `Rec` is that of `m0`, except the scratch registers. -/
def Low (L : Lay) (m0 m : Mem) : Prop := ∀ z, z ∉ rW → z < L.Rec → m z = m0 z

theorem low_of_keep {m0 m : Mem} {b : ℕ} (h : Keep rW L.Rec b m0 m) : Low L m0 m :=
  fun z hz hz' => h z hz (Or.inl hz')

/-- The address of the record of row `r`, vertex `y`. -/
def recAddr (L : Lay) (r y : ℕ) : ℕ := L.Rec + (r * (L.n * (L.k + 1)) + y * (L.k + 1))

/-- The addresses of all records, in the order step 1 writes them. -/
def recAddrs (L : Lay) : List ℕ := (List.range L.N).flatMap (addrRow L.Rec L.n L.k)

theorem length_recAddrs (L : Lay) : (recAddrs L).length = L.N * L.n :=
  length_range_flatMap (length_addrRow L.Rec L.n L.k) L.N

theorem mem_recAddrs {x : ℕ} : x ∈ recAddrs L ↔ ∃ r < L.N, ∃ y < L.n, x = recAddr L r y := by
  simp only [recAddrs, addrRow, List.mem_flatMap, List.mem_range, List.mem_map, recAddr]
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩; exact ⟨r, hr, y, hy, rfl⟩
  · rintro ⟨r, hr, y, hy, rfl⟩; exact ⟨r, hr, y, hy, rfl⟩

/-- The cells of a record, after step 1. -/
theorem R1R.cell {m0 m : Mem} (h : R1R L p q m0 L.N m) {r y j : ℕ} (hr : r < L.N) (hy : y < L.n)
    (hj : j < L.k + 1) :
    m (recAddr L r y + j) = (r :: nvec q p L.k r y)[j]'(by simp; omega) := by
  obtain ⟨-, -, -, -, -, -, hRec, -, -⟩ := h
  have e : recAddr L r y + j = L.Rec + (r * (L.n * (L.k + 1)) + (y * (L.k + 1) + j)) := by
    unfold recAddr; ring
  rw [e, blk_range_flatMap_get (length_recRow q p L.n L.k) hRec hr (lt_mul_of_lt' hy hj)]
  unfold recRow
  rw [getElem_flatMap_range_of_length (f := fun y => r :: nvec q p L.k r y) (fun y => by simp)
    L.n y j hy hj]

theorem recAddr_lt {M : Mem} (hb : BaseOK n k p L M) {r y j : ℕ} (hr : r < L.N) (hy : y < L.n)
    (hj : j < L.k + 1) : L.Rec ≤ recAddr L r y + j ∧ recAddr L r y + j < L.A := by
  have := rec_lt hb hr hy hj
  unfold recAddr; constructor <;> omega

/-- The entries of a record are below `N`. -/
theorem cons_nvec_lt (hq : QOK n k p q) (hN : 0 < q.2.length) {k' r y j : ℕ}
    (hr : r < q.2.length) (hj : j < k' + 1) :
    (r :: nvec q p k' r y)[j]'(by simp; omega) < q.2.length := by
  rcases j with _ | j
  · simpa using hr
  · simp only [List.getElem_cons_succ, nvec, List.getElem_map, List.getElem_range]
    exact tblGet_lt hq.wf hN _

/-- A record, read with `recL`, after step 1. -/
theorem R1R.recL_eq {m0 m : Mem} (h : R1R L p q m0 L.N m) {r y : ℕ} (hr : r < L.N) (hy : y < L.n) :
    recL m 0 (L.k + 1) (recAddr L r y) = r :: nvec q p L.k r y := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [recL, List.getElem_map, List.getElem_range, Nat.add_zero]
  rw [h.cell hr hy (by simpa using h1)]

/-- After step 2: the addresses of the records, sorted by the records. -/
def R2O (L : Lay) (p q : RawWL) (m0 m : Mem) : Prop :=
  ∃ ys : List ℕ, Blk m L.A ys ∧ ys.Perm (recAddrs L) ∧
    ys.map (recL m 0 (L.k + 1)) = sortedRecs q p L.n L.k L.N ∧
    Blk m L.Rec ((List.range L.N).flatMap (recRow q p L.n L.k)) ∧ Low L m0 m

/-- **Step 2**: radix sort of the record addresses. -/
def r2P : Program :=
  seq (copyTo 30 61) (seq (copyTo 31 70) (seq (assign 32 0) (seq (copyTo 33 63)
  (seq (copyTo 34 52) (seq (copyTo 35 62) radixP)))))

/-- The step count of step 2. -/
def tR2 (N n k : ℕ) : ℕ := tRadix N (N * n) (k + 1) + 1 + 1 + 1 + 1 + 1 + 1

theorem runsTo_r2P {m0 m : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) (hN : 0 < L.N)
    (hI : R1R L p q m0 L.N m) :
    RunsTo r2P (fun m' => m' = m) (R2O L p q m0) (tR2 L.N L.n L.k) := by
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hK1 : Keep rW L.Rec L.SR m0 m := hI.2.2.2.2.2.2.2.2
  have hl : Low L m0 m := low_of_keep hK1
  have hql : q.2.length = L.N := by rw [hq.length, hb.hN]
  have c : ∀ z, z ∈ persist → m z = m0 z := fun z hz => by
    have := persist_ok z hz
    exact hl z (by rw [mem_rW]; omega) (by omega)
  have c1 : m 1 = 1 := by rw [c 1 (by decide), hR.r1]
  have c61 : m 61 = L.A := by rw [c 61 (by decide), hR.r61]
  have c70 : m 70 = L.N * L.n := by rw [c 70 (by decide), hR.r70, f12]
  have c63 : m 63 = L.k + 1 := by rw [c 63 (by decide), hR.r63]
  have c52 : m 52 = L.N := by rw [c 52 (by decide), hR.r52]
  have c62 : m 62 = L.Cnt := by rw [c 62 (by decide), hR.r62]
  have hxl := length_recAddrs L
  have hA : Blk m L.A (recAddrs L) := hI.2.2.2.2.2.2.2.1
  have hAx : ∀ x ∈ recAddrs L, ∀ j < L.k + 1, L.Rec ≤ x + j ∧ x + j < L.A := by
    intro x hx j hj
    obtain ⟨r, hr, y, hy, rfl⟩ := mem_recAddrs.1 hx
    exact recAddr_lt hb hr hy hj
  unfold r2P tR2
  rw [show L.N * L.n = (recAddrs L).length from hxl.symm]
  refine copy_seq' (copy_seq' (assign_seq' (copy_seq' (copy_seq' (copy_seq' ?_)))))
  simp (disch := omega) only [Mem.update_of_ne, c61, c70, c63, c52, c62]
  set m1 := (((((m.update 30 L.A).update 31 (L.N * L.n)).update 32 0).update 33 (L.k + 1)).update
    34 L.N).update 35 L.Cnt with hm1
  have d : ∀ z, 50 ≤ z → m1 z = m z := fun z hz => by
    rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]
  have hrecL : ∀ x ∈ recAddrs L, recL m1 0 (L.k + 1) x = recL m 0 (L.k + 1) x := by
    intro x hx
    simp only [recL]
    exact List.map_congr_left (fun j hj => d _ (by
      have := hAx x hx j (by simpa using hj); omega))
  refine (runsTo_radixP (M0 := m1) (A := L.A) (Cnt := L.Cnt) (K := L.N) (f0 := 0) (L := L.k + 1)
    (xs := recAddrs L) (hA.congr (fun z h1 h2 => d z (by omega))) ?_ ?_ ?_ (by omega)
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact c1) ?_ ?_ ?_ ?_ ?_ ?_).weaken ?_
  · intro x hx j hj
    obtain ⟨r, hr, y, hy, rfl⟩ := mem_recAddrs.1 hx
    have hb2 := recAddr_lt hb hr hy hj
    rw [Nat.add_zero, d _ (by omega), hI.cell hr hy hj, ← hql]
    exact cons_nvec_lt hq (by omega) (by omega) hj
  · intro x hx j hj
    have := hAx x hx j hj
    omega
  · rw [hxl]; omega
  all_goals (rw [hm1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, hxl])
  rintro m' ⟨⟨ys, hys, hp, hpw⟩, hk⟩
  have e' : ∀ z, z ∉ sortW → z < L.A → m' z = m1 z := fun z h1 h2 => hk z h1 (Or.inl h2)
  have hrecL' : ∀ x ∈ ys, recL m' 0 (L.k + 1) x = recL m1 0 (L.k + 1) x := by
    intro x hx
    have hx' := hp.subset hx
    simp only [recL]
    exact List.map_congr_left (fun j hj => by
      have := hAx x hx' j (by simpa using hj)
      exact e' _ (by simp [sortW]; omega) (by omega))
  refine ⟨ys, hys, hp, ?_, ?_, ?_⟩
  · rw [List.map_congr_left hrecL']
    refine sorted_eq (List.pairwise_map.2 hpw) ?_
    refine (hp.map _).trans (List.Perm.of_eq ?_)
    unfold recAddrs
    rw [List.map_flatMap]
    refine List.flatMap_congr (fun r hr => ?_)
    rw [List.mem_range] at hr
    unfold addrRow
    rw [List.map_map]
    refine List.map_congr_left (fun y hy => ?_)
    rw [List.mem_range] at hy
    simp only [Function.comp]
    exact (hrecL _ (mem_recAddrs.2 ⟨r, hr, y, hy, rfl⟩)).trans (hI.recL_eq hr hy)
  · have hl2 := length_range_flatMap (length_recRow q p L.n L.k) L.N
    refine hI.2.2.2.2.2.2.1.congr (fun z h1 h2 => ?_)
    rw [hl2] at h2
    have : L.N * (L.n * (L.k + 1)) = L.NN * (L.k + 1) := by rw [f12, mul_assoc]
    rw [e' z (by simp [sortW]; omega) (by omega), d z (by omega)]
  · intro z hz hz'
    rw [e' z (fun h => hz (mem_rW.2 (by simp [sortW] at h; omega))) (by omega), hm1]
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact hl z (mem_rW.not.2 hz) hz'
