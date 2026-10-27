/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The tables of the fast
program: the index of every tuple, the colors by index, and the neighbour indices.
-/
import Workspace.Algo.WLFastSetup

/-!
# Tuple addressing on the RAM

The colors of the tuples are kept in an array `C` indexed by `idxOf n t` (the base-`n` number
with digits `t`, `Algo.WLFast.idxOf`).  Before the rounds the program computes, once, for every
row `r` of the table (tuple `t_r`, color `c_r`):

* `IX[r] = idxOf n t_r`, and `C[idxOf n t_r] = c_r`;
* for every vertex `y` and position `i`, `Nb[(r n + y) k + i] = idxOf n (t_r[i ↦ y])`, the index
  of the neighbour tuple of Notation 5.2.1.

Afterwards a round reads the color of any neighbour tuple with two loads.  The indices are
computed by Horner's rule (`hornP`), with the multiplication by `n` done by `n` additions: the
build costs `O(N n k · k n)` steps, `N = n^k`, which is `O(k² n^{k+2})` and within the bound of
§5.4.2 since `k ≥ 1`.

Registers: `50 = n`, `51 = k`, `57 = T` (a scratch buffer of `k` cells), `80` the result of
`hornP`, `81`–`85` its scratch.

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

/-! ## Horner's rule -/

/-- `R83 += R80`, `R84` times. -/
def mBody : Program := seq (addTo 83 83 80) (subTo 84 84 1)

/-- One digit: `R80 := R80 * n + T[j]`. -/
def hBody : Program :=
  seq (assign 83 0) (seq (copyTo 84 50) (seq (whileNz 84 mBody) (seq (loadTo 85 81)
  (seq (addTo 80 83 85) (seq (addTo 81 81 1) (subTo 82 82 1))))))

/-- **Horner's rule**: `R80 := idxOf n T[0..k)`. -/
def hornP : Program := seq (assign 80 0) (seq (copyTo 81 57) (seq (copyTo 82 51) (whileNz 82 hBody)))

theorem wf_mBody : Wf mBody := by unfold mBody; wf_tac

theorem wf_hBody : Wf hBody := by
  unfold hBody
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_mBody) (by wf_tac)))

theorem wf_hornP : Wf hornP := by
  unfold hornP
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_whileNz wf_hBody)))

/-- The registers `hornP` writes. -/
def hornW : List ℕ := [80, 81, 82, 83, 84, 85]

/-- The multiplication loop after `t` additions. -/
def MulI (m0 : Mem) (a n : ℕ) (t : ℕ) (m : Mem) : Prop :=
  t ≤ n ∧ m 84 = n - t ∧ m 83 = a * t ∧ ∀ z, z ≠ 83 → z ≠ 84 → m z = m0 z

theorem runsTo_mLoop {m0 : Mem} {a n : ℕ} (h80 : m0 80 = a) (h1 : m0 1 = 1)
    (h83 : m0 83 = 0) (h84 : m0 84 = n) :
    RunsTo (whileNz 84 mBody) (fun m => m = m0) (MulI m0 a n n) (n * (2 + 2) + 1) := by
  refine runsTo_countLoop wf_mBody (MulI m0 a n) n 2 (fun t m h => ⟨h.2.1, h.1⟩)
    (fun t m ht ⟨_, e84, e83, hk⟩ => ?_) m0 ⟨by omega, by rw [h84]; rfl, by rw [h83]; ring,
      fun _ _ _ => rfl⟩
  have c80 : m 80 = a := by rw [hk 80 (by omega) (by omega), h80]
  have c1 : m 1 = 1 := by rw [hk 1 (by omega) (by omega), h1]
  unfold mBody
  rt
  unfold MulI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e84, e83, c80, c1]
  refine ⟨by omega, by omega, by ring, fun z a b => ?_⟩
  simp (disch := omega) only [Mem.update_of_ne]
  exact hk z a b

/-- The Horner loop after `j` digits. -/
def HornI (m0 : Mem) (n T : ℕ) (u : List ℕ) (j : ℕ) (m : Mem) : Prop :=
  j ≤ u.length ∧ m 82 = u.length - j ∧ m 81 = T + j ∧ m 80 = idxOf n (u.take j) ∧
    ∀ z, z ∉ hornW → m z = m0 z

theorem runsTo_hBody {m0 m : Mem} {n T : ℕ} {u : List ℕ} {j : ℕ} (hj : j < u.length)
    (hI : HornI m0 n T u j m) (hT : Blk m0 T u) (hT86 : 86 ≤ T) (h1 : m0 1 = 1)
    (h50 : m0 50 = n) :
    RunsTo hBody (fun m' => m' = m) (HornI m0 n T u (j + 1)) (2 + ((n * (2 + 2) + 1) + 4)) := by
  obtain ⟨_, e82, e81, e80, hk⟩ := hI
  have c1 : m 1 = 1 := by rw [hk 1 (by simp [hornW]), h1]
  have c50 : m 50 = n := by rw [hk 50 (by simp [hornW]), h50]
  have cT : m (T + j) = u[j] := by rw [hk _ (by simp [hornW]; omega)]; exact hT j hj
  unfold hBody
  refine RunsTo.mono (T := ((n * (2 + 2) + 1) + ((((0 + 1) + 1) + 1) + 1) + 1) + 1) ?_
    (by omega)
  refine assign_seq' (copy_seq' ?_)
  set m1 := (m.update 83 0).update 84 (m.update 83 0 50) with hm1
  refine block_seq (T := n * (2 + 2) + 1) (T' := (((0 + 1) + 1) + 1) + 1)
    (runsTo_mLoop (m0 := m1) (a := idxOf n (u.take j)) (n := n)
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact e80)
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact c1)
    (by rw [hm1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self])
    (by rw [hm1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, c50]))
    (fun m2 ⟨_, e84', e83', hk2⟩ => ?_)
  have g : ∀ z, z ≠ 83 → z ≠ 84 → m2 z = m z := fun z a b => by
    rw [hk2 z a b, hm1]; simp (disch := omega) only [Mem.update_of_ne]
  have d81 : m2 81 = T + j := by rw [g 81 (by omega) (by omega), e81]
  have d82 : m2 82 = u.length - j := by rw [g 82 (by omega) (by omega), e82]
  have d1 : m2 1 = 1 := by rw [g 1 (by omega) (by omega), c1]
  have dT : m2 (T + j) = u[j] := by rw [g _ (by omega) (by omega), cT]
  refine load_seq' (add_seq' (add_seq' (sub_last' ?_)))
  unfold HornI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, d81, d82, d1, dT, e83']
  refine ⟨by omega, by omega, by ring, ?_, fun z hz => ?_⟩
  · rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      idxOf_append_singleton]
  · simp only [hornW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    rw [g z (by omega) (by omega)]
    exact hk z (by simp [hornW]; omega)

/-- The step count of `hornP`. -/
def tHorn (n k : ℕ) : ℕ := k * (4 * n + 9) + 4

/-- **Horner's rule on the RAM**: with the list `u` in the buffer at `R57`, `hornP` puts
`idxOf n u` in `R80`, in `k (4n + 9) + 4` steps, `k = |u|`. -/
theorem runsTo_hornP {m0 : Mem} {n T : ℕ} {u : List ℕ} (hT : Blk m0 T u) (hT86 : 86 ≤ T)
    (h1 : m0 1 = 1) (h50 : m0 50 = n) (h51 : m0 51 = u.length) (h57 : m0 57 = T) :
    RunsTo hornP (fun m => m = m0)
      (fun m => m 80 = idxOf n u ∧ ∀ z, z ∉ hornW → m z = m0 z) (tHorn n u.length) := by
  unfold hornP tHorn
  refine RunsTo.mono (T := (u.length * ((2 + ((n * (2 + 2) + 1) + 4)) + 2) + 1) + 1 + 1 + 1) ?_
    (by ring_nf; omega)
  refine assign_seq' (copy_seq' (copy_seq' ?_))
  set m1 := ((m0.update 80 0).update 81 (m0 57)).update 82 (m0 51) with hm1
  refine (runsTo_countLoop (c := 82) wf_hBody (HornI m0 n T u) u.length
    (2 + ((n * (2 + 2) + 1) + 4)) (fun t m h => ⟨h.2.1, h.1⟩)
    (fun t m ht hI => runsTo_hBody ht hI hT hT86 h1 h50) m1 ⟨by omega, ?_, ?_, ?_, ?_⟩).weaken
    (fun m ⟨_, _, _, e80, hk⟩ => ⟨by rw [e80, List.take_length], hk⟩)
  · rw [hm1, Mem.update_self, h51]; rfl
  · rw [hm1, Mem.update_of_ne _ _ (by omega), Mem.update_self, h57]; rfl
  · rw [hm1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; rfl
  · intro z hz
    simp only [hornW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]


/-! ## Lists written through a pointer -/

theorem blk_snoc {m : Mem} {P : ℕ} {l : List ℕ} (h : Blk m P l) (v : ℕ) :
    Blk (m.update (P + l.length) v) P (l ++ [v]) := by
  rw [Blk.append]
  exact ⟨h.update (Or.inr le_rfl), by simp [Blk.cons, Blk.nil]⟩

theorem range_map_succ {β : Type*} (g : ℕ → β) (j : ℕ) :
    (List.range (j + 1)).map g = (List.range j).map g ++ [g j] := by
  rw [List.range_succ, List.map_append]; rfl

theorem range_flatMap_succ {β : Type*} (f : ℕ → List β) (j : ℕ) :
    (List.range (j + 1)).flatMap f = (List.range j).flatMap f ++ f j := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem length_range_flatMap {β : Type*} {f : ℕ → List β} {w : ℕ} (hf : ∀ j, (f j).length = w) :
    ∀ j, ((List.range j).flatMap f).length = j * w
  | 0 => by simp
  | j + 1 => by
      rw [range_flatMap_succ, List.length_append, length_range_flatMap hf j, hf]; ring

theorem blk_range_flatMap_get {m : Mem} {P : ℕ} {f : ℕ → List ℕ} {w M : ℕ}
    (hf : ∀ j, (f j).length = w) (h : Blk m P ((List.range M).flatMap f)) {r j : ℕ} (hr : r < M)
    (hj : j < w) : m (P + (r * w + j)) = (f r)[j]'(by rw [hf]; exact hj) := by
  have hl : r * w + j < ((List.range M).flatMap f).length := by
    rw [length_range_flatMap hf]; exact lt_mul_of_lt' hr hj
  rw [h _ hl, getElem_flatMap_range_of_length hf M r j hr hj]

/-! ## The data of the table -/

/-- The tuple of row `r`. -/
def tup (p : RawWL) (r : ℕ) : List ℕ := (p.2.getD r ([], 0)).1

/-- The color of row `r`. -/
def colOf (p : RawWL) (r : ℕ) : ℕ := (p.2.getD r ([], 0)).2

/-- The first `r` entries of `IX`. -/
def ixPre (p : RawWL) (n r : ℕ) : List ℕ := (List.range r).map (fun r' => idxOf n (tup p r'))

/-- The indices of the neighbours `t[i ↦ y]`, `i < k`, of the tuple of row `r`. -/
def nbCell (p : RawWL) (n k r y : ℕ) : List ℕ :=
  (List.range k).map (fun i => idxOf n ((tup p r).set i y))

/-- The entries of `Nb` for row `r`. -/
def nbRow (p : RawWL) (n k r : ℕ) : List ℕ := (List.range n).flatMap (nbCell p n k r)

@[simp] theorem length_nbCell (p : RawWL) (n k r y : ℕ) : (nbCell p n k r y).length = k := by
  simp [nbCell]

theorem length_nbRow (p : RawWL) (n k r : ℕ) : (nbRow p n k r).length = n * k :=
  length_range_flatMap (length_nbCell p n k r) n

/-- **The facts the program relies on**: the parameters, and the memory `M` after the setup. -/
structure BaseOK (n k : ℕ) (p : RawWL) (L : Lay) (M : Mem) : Prop where
  wf : RawWL.WF n k p
  hn : L.n = n
  hk : L.k = k
  hN : L.N = p.2.length
  hLin : L.Lin = (Enc.encode p).length
  hF : 100 ≤ L.F
  k1 : 1 ≤ k
  regs : RegsOK L M
  blk : Blk M L.F (Enc.encode p)

section Base

variable {n k : ℕ} {p : RawWL} {L : Lay} {M : Mem}

theorem BaseOK.keyLen (hb : BaseOK n k p L M) : ∀ q ∈ p.2, q.1.length = k := fun q hq =>
  ((hb.wf.keyMem q.1).1 (List.mem_map_of_mem hq)).1

theorem BaseOK.tup_eq (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    tup p r = p.2[r].1 := by
  rw [tup, List.getD_eq_getElem _ _ hr]

theorem BaseOK.colOf_eq (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    colOf p r = p.2[r].2 := by
  rw [colOf, List.getD_eq_getElem _ _ hr]

theorem BaseOK.len_tup (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    (tup p r).length = k := by
  rw [hb.tup_eq hr]; exact key_length hb.wf hr

theorem BaseOK.tup_lt (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) {d : ℕ}
    (hd : d ∈ tup p r) : d < n := by
  rw [hb.tup_eq hr] at hd; exact key_lt hb.wf hr hd

theorem BaseOK.set_lt (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) {i y : ℕ}
    (hy : y < n) {d : ℕ} (hd : d ∈ (tup p r).set i y) : d < n := by
  rcases List.mem_or_eq_of_mem_set hd with h | h
  · exact hb.tup_lt hr h
  · rw [h]; exact hy

theorem BaseOK.idx_lt (hb : BaseOK n k p L M) {t : List ℕ} (hl : t.length = k)
    (ht : ∀ d ∈ t, d < n) : idxOf n t < p.2.length := by
  rw [length_table hb.wf, ← hl]; exact idxOf_lt ht

theorem BaseOK.lin (hb : BaseOK n k p L M) :
    L.Lin = 2 * n + 2 + p.2.length * (2 * k + 4) := by
  rw [hb.hLin, length_encode_rawWL hb.keyLen, length_dom hb.wf]

/-- A cell of row `r` of the input copy. -/
theorem BaseOK.row (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    RowAt M (L.R0 + r * L.RW) p.2[r] := by
  have := ((blk_rawWL_iff hb.keyLen).1 hb.blk).2.2.2 r hr
  rw [length_dom hb.wf] at this
  rw [Lay.R0, Lay.RW, hb.hn, hb.hk]; exact this

theorem BaseOK.row_lt (hb : BaseOK n k p L M) {r j : ℕ} (hr : r < p.2.length) (hj : j < L.RW) :
    L.R0 + r * L.RW + j < L.IX := by
  have := lt_mul_of_lt' hr hj
  have hl := hb.lin
  simp only [Lay.R0, Lay.RW, Lay.IX, hb.hn, hb.hk] at this hl ⊢
  omega

end Base

/-! ## The build loop -/

/-- Copy one entry of the tuple into the buffer. -/
def cpBody : Program :=
  seq (loadTo 94 90) (seq (storeTo 91 94) (seq (addTo 90 90 1) (seq (addTo 90 90 1)
  (seq (addTo 91 91 1) (subTo 93 93 1)))))

/-- Copy the tuple of the current row into the buffer `T`. -/
def cpTup : Program :=
  seq (assign 90 3) (seq (addTo 90 86 90) (seq (copyTo 91 57) (seq (copyTo 93 51)
  (whileNz 93 cpBody))))

/-- Store `IX[r]` and `C[IX[r]] := c_r`; start the neighbours. -/
def rowMid : Program :=
  seq (storeTo 88 80) (seq (addTo 88 88 1) (seq (addTo 90 86 54) (seq (subTo 90 90 1)
  (seq (loadTo 94 90) (seq (addTo 95 56 80) (seq (storeTo 95 94) (seq (assign 96 0)
  (copyTo 97 50))))))))

/-- One neighbour: set `T[i] := y`, compute its index, store it, restore `T[i]`. -/
def iBody : Program :=
  seq (loadTo 94 98) (seq (storeTo 98 96) (seq hornP (seq (storeTo 89 80) (seq (addTo 89 89 1)
  (seq (storeTo 98 94) (seq (addTo 98 98 1) (subTo 99 99 1)))))))

/-- All positions `i` for one vertex `y`. -/
def yBody : Program :=
  seq (copyTo 98 57) (seq (copyTo 99 51) (seq (whileNz 99 iBody) (seq (addTo 96 96 1)
  (subTo 97 97 1))))

/-- One row. -/
def rowBody : Program :=
  seq cpTup (seq hornP (seq rowMid (seq (whileNz 97 yBody) (seq (addTo 86 86 54) (subTo 92 92 1)))))

/-- **The build**: `IX`, `C` and `Nb` for all rows. -/
def buildP : Program :=
  seq (copyTo 86 53) (seq (copyTo 88 55) (seq (copyTo 89 58) (seq (copyTo 92 52) (whileNz 92 rowBody))))

theorem wf_cpTup : Wf cpTup := by unfold cpTup cpBody; wf_tac

theorem wf_iBody : Wf iBody := by
  unfold iBody
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq wf_hornP (by wf_tac)))

theorem wf_yBody : Wf yBody := by
  unfold yBody
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (wf_whileNz wf_iBody) (by wf_tac)))

theorem wf_rowBody : Wf rowBody := by
  unfold rowBody
  exact wf_seq wf_cpTup (wf_seq wf_hornP (wf_seq (by unfold rowMid; wf_tac)
    (wf_seq (wf_whileNz wf_yBody) (by wf_tac))))

theorem wf_buildP : Wf buildP := by
  unfold buildP
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_whileNz wf_rowBody))))

/-- The registers the build writes. -/
def bW : List ℕ := List.range' 80 20

theorem mem_bW {z : ℕ} : z ∈ bW ↔ 80 ≤ z ∧ z < 100 := by
  simp only [bW, List.mem_range'_1]

theorem nmem_bW {z : ℕ} (hz : z ∉ bW) {l : List ℕ} (hl : ∀ x ∈ l, 80 ≤ x ∧ x < 100) : z ∉ l :=
  fun h => hz (mem_bW.2 (hl z h))

/-- What the build has written after `r` rows. -/
def Arr (p : RawWL) (L : Lay) (r : ℕ) (m : Mem) : Prop :=
  Blk m L.IX (ixPre p L.n r) ∧ (∀ r' < r, m (L.C + idxOf L.n (tup p r')) = colOf p r') ∧
    Blk m L.Nb ((List.range r).flatMap (nbRow p L.n L.k))

section Build

variable {n k : ℕ} {p : RawWL} {L : Lay} {M : Mem}

/-- The frame of the build: only registers `80`–`99` and `[IX, Rec)` change. -/
abbrev BFr (L : Lay) (M m : Mem) : Prop := Keep bW L.IX L.Rec M m

theorem BFr.reg (hb : BaseOK n k p L M) {m : Mem} (h : BFr L M m) {z : ℕ} (hz : z ∈ persist) :
    m z = M z := by
  refine h z (fun h' => ?_) (Or.inl ?_)
  · rw [mem_bW] at h'; simp only [persist, List.mem_cons, List.not_mem_nil, or_false] at hz; omega
  · have := hb.hF; simp only [persist, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [Lay.IX]; omega

theorem BFr.regs (hb : BaseOK n k p L M) {m : Mem} (h : BFr L M m) : RegsOK L m :=
  hb.regs.congr (fun z hz => h.reg hb hz)

theorem BFr.input (hb : BaseOK n k p L M) {m : Mem} (h : BFr L M m) {z : ℕ} (hz1 : L.F ≤ z)
    (hz2 : z < L.IX) : m z = M z :=
  h z (fun h' => by rw [mem_bW] at h'; have := hb.hF; omega) (Or.inl hz2)

theorem BFr.upd {m : Mem} (h : BFr L M m) {z : ℕ} (hz : z ∈ bW ∨ (L.IX ≤ z ∧ z < L.Rec))
    (v : ℕ) : BFr L M (m.update z v) := Keep.upd h hz v

theorem Arr.congr {r : ℕ} {m m' : Mem} (h : Arr p L r m)
    (h1 : ∀ z, L.IX ≤ z → z < L.T → m' z = m z) (h2 : ∀ z, L.Nb ≤ z → z < L.Rec → m' z = m z)
    (hr : ∀ r' < r, L.C + idxOf L.n (tup p r') < L.T)
    (hix : L.IX + r ≤ L.C) (hnb : L.Nb + r * (L.n * L.k) ≤ L.Rec) :
    Arr p L r m' := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨a.congr (fun z hz1 hz2 => h1 z hz1 ?_), fun r' hr' => ?_,
    c.congr (fun z hz1 hz2 => h2 z hz1 ?_)⟩
  · simp only [ixPre, List.length_map, List.length_range] at hz2
    simp only [Lay.C, Lay.T] at hix ⊢; omega
  · have := hr r' hr'
    rw [h1 (L.C + idxOf L.n (tup p r')) (by simp only [Lay.C]; omega) this]; exact b r' hr'
  · rw [length_range_flatMap (length_nbRow p L.n L.k)] at hz2; omega

theorem blk_take_succ {m : Mem} {P : ℕ} {l : List ℕ} {j : ℕ} (h : Blk m P (l.take j))
    (hj : j < l.length) : Blk (m.update (P + j) l[j]) P (l.take (j + 1)) := by
  have := blk_snoc h l[j]
  rw [List.length_take, min_eq_left hj.le] at this
  rw [← List.take_concat_get' l j hj]; exact this

theorem blk_set {m : Mem} {P : ℕ} {l : List ℕ} (h : Blk m P l) {i : ℕ} (v : ℕ) :
    Blk (m.update (P + i) v) P (l.set i v) := by
  intro j hj
  rw [List.length_set] at hj
  rw [List.getElem_set]
  by_cases hij : i = j
  · subst hij; rw [Mem.update_self, if_pos rfl]
  · rw [Mem.update_of_ne _ _ (by omega), if_neg hij]; exact h j hj

/-! ### Copying the tuple into the buffer -/

/-- The copy loop after `j` entries. -/
def CpI (L : Lay) (m : Mem) (b : ℕ) (t : List ℕ) (j : ℕ) (m' : Mem) : Prop :=
  j ≤ L.k ∧ m' 90 = b + 3 + 2 * j ∧ m' 91 = L.T + j ∧ m' 93 = L.k - j ∧
    Blk m' L.T (t.take j) ∧ Keep [90, 91, 93, 94] L.T (L.T + L.k) m m'

theorem runsTo_cpTup (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) {m : Mem}
    (hB : BFr L M m) (h86 : m 86 = L.R0 + r * L.RW) :
    RunsTo cpTup (fun m' => m' = m)
      (fun m' => Blk m' L.T (tup p r) ∧ Keep [90, 91, 93, 94] L.T (L.T + L.k) m m')
      (L.k * (6 + 2) + 1 + 1 + 1 + 1 + 1) := by
  have hR := hB.regs hb
  have hlen := hb.len_tup hr
  have hkL : L.k = k := hb.hk
  have hrow := hb.row hr
  obtain ⟨-, -, hent, -, -⟩ := hrow
  have hF := hb.hF
  set b := L.R0 + r * L.RW with hbdef
  have hb100 : 100 ≤ b := by simp only [hbdef, Lay.R0]; omega
  have hIX : 100 ≤ L.IX := by simp only [Lay.IX]; omega
  unfold cpTup
  refine assign_seq' (add_seq' (copy_seq' (copy_seq' ?_)))
  refine (runsTo_countLoop (c := 93) (by unfold cpBody; wf_tac) (CpI L m b (tup p r)) L.k 6
    (fun t m' h => ⟨h.2.2.2.1, h.1⟩) (fun j m' hj hI => ?_) _ ?_).weaken
    (fun m' ⟨_, _, _, _, hB', hK⟩ => ⟨by rw [hkL, ← hlen, List.take_length] at hB'; exact hB', hK⟩)
  · obtain ⟨_, e90, e91, e93, hT, hK⟩ := hI
    have hjt : j < (tup p r).length := by rw [hlen, ← hkL]; exact hj
    -- the entry `j` of the tuple, read in the input copy
    have hbj : b + 3 + 2 * j < L.IX := by
      have := hb.row_lt hr (j := 3 + 2 * j) (by simp only [Lay.RW]; omega)
      omega
    have hTge : L.IX ≤ L.T := by simp only [Lay.T, Lay.C]; omega
    have hv : m' (b + 3 + 2 * j) = (tup p r)[j] := by
      rw [hK (b + 3 + 2 * j) (by simp; omega) (Or.inl (by omega)),
        hB.input hb (by simp only [hbdef, Lay.R0]; omega) hbj]
      have := (hent j (by rw [← hb.tup_eq hr]; exact hjt)).2
      rw [show b + 2 + j * 2 + 1 = b + 3 + 2 * j by ring] at this
      rw [this]; simp only [hb.tup_eq hr]
    have c1 : m' 1 = 1 := by rw [hK 1 (by simp) (Or.inl (by omega)), hR.r1]
    unfold cpBody
    rt
    unfold CpI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e90, e91, e93, c1, hv]
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
    · refine Blk.update (Blk.update (Blk.update (Blk.update ?_ (Or.inl (by omega)))
        (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega))
      exact blk_take_succ (hT.update (Or.inl (by omega))) hjt
    · intro z hz hab
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      have hzT : z ≠ L.T + j := by omega
      simp (disch := omega) only [Mem.update_of_ne]
      exact hK z (by simp; omega) hab
  · have hTge : L.IX ≤ L.T := by simp only [Lay.T, Lay.C]; omega
    unfold CpI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h86, hR.r57, hR.r51]
    refine ⟨by omega, trivial, by omega, by omega, by simp [Blk.nil], fun z hz hab => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]

/-! ### The neighbours of one row -/

/-- The registers the neighbour loops write. -/
def nW : List ℕ := [80, 81, 82, 83, 84, 85, 89, 94, 96, 97, 98, 99]

/-- The neighbour loop of row `r`, vertex `y`, after `i` positions; `mc` is the memory before
the loop over `y`. -/
def NbI (L : Lay) (p : RawWL) (mc : Mem) (r y i : ℕ) (m' : Mem) : Prop :=
  i ≤ L.k ∧ m' 98 = L.T + i ∧ m' 99 = L.k - i ∧
    m' 89 = L.Nb + r * (L.n * L.k) + y * L.k + i ∧ m' 96 = y ∧ m' 97 = L.n - y ∧
    Blk m' (L.Nb + r * (L.n * L.k)) ((List.range y).flatMap (nbCell p L.n L.k r)) ∧
    Blk m' (L.Nb + r * (L.n * L.k) + y * L.k) ((nbCell p L.n L.k r y).take i) ∧
    Keep nW (L.Nb + r * (L.n * L.k)) (L.Nb + (r + 1) * (L.n * L.k)) mc m'

/-- The step count of `iBody`. -/
def tIB (n k : ℕ) : ℕ := tHorn n k + 6 + 1 + 1

theorem nb_row_le (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    L.Nb + (r + 1) * (L.n * L.k) ≤ L.Rec := by
  have : (r + 1) * (L.n * L.k) ≤ L.N * (L.n * L.k) :=
    Nat.mul_le_mul_right _ (by rw [hb.hN]; omega)
  simp only [Lay.Rec, Lay.NN]
  rw [mul_assoc]; omega

theorem runsTo_iBody (hb : BaseOK n k p L M) {r y i : ℕ} (hr : r < p.2.length) (hy : y < L.n)
    (hi : i < L.k) {mc m' : Mem} (hB : BFr L M mc) (hT : Blk mc L.T (tup p r))
    (hI : NbI L p mc r y i m') :
    RunsTo iBody (fun m => m = m') (NbI L p mc r y (i + 1)) (tIB L.n L.k) := by
  obtain ⟨-, e98, e99, e89, e96, e97, hP, hC, hK⟩ := hI
  have hR := hB.regs hb
  have hlen := hb.len_tup hr
  have hkL : L.k = k := hb.hk
  have hF := hb.hF
  have hrow := nb_row_le hb hr
  have hyk : y * L.k + i < L.n * L.k := lt_mul_of_lt' hy hi
  have hr1 : (r + 1) * (L.n * L.k) = r * (L.n * L.k) + L.n * L.k := by ring
  have hyk' : y * L.k + L.k ≤ L.n * L.k := by
    have := Nat.mul_le_mul_right L.k (show y + 1 ≤ L.n by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  have hTN : L.T + L.k ≤ L.Nb := by simp only [Lay.Nb]; omega
  have hT100 : 100 ≤ L.T := by simp only [Lay.T, Lay.C, Lay.IX]; omega
  -- registers and cells of `m'` read from `mc`
  have g : ∀ z, z ∉ nW → (z < L.Nb + r * (L.n * L.k) ∨ L.Nb + (r + 1) * (L.n * L.k) ≤ z) →
      m' z = mc z := fun z h1 h2 => hK z h1 h2
  have gT : ∀ j, j < L.k → m' (L.T + j) = mc (L.T + j) := fun j hj =>
    g (L.T + j) (by simp [nW]; omega) (Or.inl (by omega))
  have hti : i < (tup p r).length := by rw [hlen, ← hkL]; exact hi
  have hTi : m' (L.T + i) = (tup p r)[i] := by rw [gT i hi]; exact hT i hti
  have hTm : Blk m' L.T (tup p r) := fun j hj => by
    rw [gT j (by rw [hlen, ← hkL] at hj; exact hj)]; exact hT j hj
  have c1 : m' 1 = 1 := by rw [g 1 (by simp [nW]) (Or.inl (by omega)), hR.r1]
  have c50 : m' 50 = L.n := by rw [g 50 (by simp [nW]) (Or.inl (by omega)), hR.r50]
  have c51 : m' 51 = L.k := by rw [g 51 (by simp [nW]) (Or.inl (by omega)), hR.r51]
  have c57 : m' 57 = L.T := by rw [g 57 (by simp [nW]) (Or.inl (by omega)), hR.r57]
  unfold iBody tIB
  refine load_seq' (store_seq' ?_)
  have f98 : (m'.update 94 (m' (m' 98))) 98 = L.T + i := by
    rw [Mem.update_of_ne _ _ (by omega), e98]
  have f96 : (m'.update 94 (m' (m' 98))) 96 = y := by
    rw [Mem.update_of_ne _ _ (by omega), e96]
  rw [f98, f96, e98, hTi]
  set m1 := (m'.update 94 (tup p r)[i]).update (L.T + i) y with hm1
  have hB1 : Blk m1 L.T ((tup p r).set i y) :=
    blk_set (hTm.update (Or.inl (by omega))) y
  have d : ∀ z, z ≠ 94 → z ≠ L.T + i → m1 z = m' z := fun z a b => by
    rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]
  refine block_seq (T := tHorn L.n L.k) (T' := 6)
    ((runsTo_hornP (m0 := m1) (n := L.n) hB1 (by omega) (by rw [d 1 (by omega) (by omega), c1])
      (by rw [d 50 (by omega) (by omega), c50])
      (by rw [List.length_set, d 51 (by omega) (by omega), c51, hlen, hkL])
      (by rw [d 57 (by omega) (by omega), c57])).mono
      (by rw [List.length_set, hlen, hkL])) (fun m2 ⟨e80, hk2⟩ => ?_)
  have k2 : ∀ z, z ∉ hornW → z ≠ 94 → z ≠ L.T + i → m2 z = m' z := fun z a b c => by
    rw [hk2 z a, d z b c]
  have h89 : m2 89 = L.Nb + r * (L.n * L.k) + y * L.k + i := by
    rw [k2 89 (by simp [hornW]) (by omega) (by omega), e89]
  have h94 : m2 94 = (tup p r)[i] := by
    rw [hk2 94 (by simp [hornW]), hm1]
    simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
  have h98 : m2 98 = L.T + i := by
    rw [k2 98 (by simp [hornW]) (by omega) (by omega), e98]
  have h99 : m2 99 = L.k - i := by rw [k2 99 (by simp [hornW]) (by omega) (by omega), e99]
  have h1' : m2 1 = 1 := by rw [k2 1 (by simp [hornW]) (by omega) (by omega), c1]
  have h96 : m2 96 = y := by rw [k2 96 (by simp [hornW]) (by omega) (by omega), e96]
  have h97 : m2 97 = L.n - y := by rw [k2 97 (by simp [hornW]) (by omega) (by omega), e97]
  have hv : idxOf L.n ((tup p r).set i y) = (nbCell p L.n L.k r y)[i]'(by simp; exact hi) := by
    simp [nbCell]
  rt
  unfold NbI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h89, h94, h98, h99, h1', e80,
    h96, h97]
  refine ⟨by omega, by omega, by omega, by omega, trivial, trivial, ?_, ?_, ?_⟩
  · -- the finished cells of the row are untouched
    have hl := length_range_flatMap (length_nbCell p L.n L.k r) y
    refine Blk.update (Blk.update (Blk.update (Blk.update (Blk.update ?_ (Or.inr (by rw [hl]; omega)))
      (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega))
    refine hP.congr (fun z hz1 hz2 => ?_)
    rw [hl] at hz2
    rw [hk2 z (by simp [hornW]; omega), d z (by omega) (by omega)]
  · have hC2 : Blk m2 (L.Nb + r * (L.n * L.k) + y * L.k) ((nbCell p L.n L.k r y).take i) := by
      refine hC.congr (fun z hz1 hz2 => ?_)
      simp only [List.length_take, length_nbCell] at hz2
      rw [hk2 z (by simp [hornW]; omega), d z (by omega) (by omega)]
    have := blk_take_succ hC2 (by simp; exact hi)
    rw [← hv] at this
    refine Blk.update (Blk.update (Blk.update (Blk.update this (Or.inl (by omega)))
      (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega))
  · intro z hz hab
    simp only [nW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    by_cases hzT : z = L.T + i
    · subst hzT
      simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
      rw [← hTi, gT i hi]
    · simp (disch := omega) only [Mem.update_of_ne]
      rw [hk2 z (by simp [hornW]; omega), d z (by omega) hzT]
      exact hK z (by simp [nW]; omega) hab

/-- The loop over `y` of row `r`, after `y` vertices. -/
def YI (L : Lay) (p : RawWL) (mc : Mem) (r y : ℕ) (m' : Mem) : Prop :=
  y ≤ L.n ∧ m' 96 = y ∧ m' 97 = L.n - y ∧ m' 89 = L.Nb + r * (L.n * L.k) + y * L.k ∧
    Blk m' (L.Nb + r * (L.n * L.k)) ((List.range y).flatMap (nbCell p L.n L.k r)) ∧
    Keep nW (L.Nb + r * (L.n * L.k)) (L.Nb + (r + 1) * (L.n * L.k)) mc m'

/-- The step count of `yBody`. -/
def tYB (n k : ℕ) : ℕ := (k * (tIB n k + 2) + 1 + 2) + 1 + 1

theorem runsTo_yBody (hb : BaseOK n k p L M) {r y : ℕ} (hr : r < p.2.length) (hy : y < L.n)
    {mc m' : Mem} (hB : BFr L M mc) (hT : Blk mc L.T (tup p r)) (hI : YI L p mc r y m') :
    RunsTo yBody (fun m => m = m') (YI L p mc r (y + 1)) (tYB L.n L.k) := by
  obtain ⟨-, e96, e97, e89, hP, hK⟩ := hI
  have hR := hB.regs hb
  have hF := hb.hF
  have hrow := nb_row_le hb hr
  have hr1 : (r + 1) * (L.n * L.k) = r * (L.n * L.k) + L.n * L.k := by ring
  have hyk' : y * L.k + L.k ≤ L.n * L.k := by
    have := Nat.mul_le_mul_right L.k (show y + 1 ≤ L.n by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  have hTN : L.T + L.k ≤ L.Nb := by simp only [Lay.Nb]; omega
  have hT100 : 100 ≤ L.T := by simp only [Lay.T, Lay.C, Lay.IX]; omega
  have g : ∀ z, z ∉ nW → z < 100 → m' z = mc z := fun z h1 h2 => hK z h1 (Or.inl (by omega))
  have c51 : m' 51 = L.k := by rw [g 51 (by simp [nW]) (by omega), hR.r51]
  have c57 : m' 57 = L.T := by rw [g 57 (by simp [nW]) (by omega), hR.r57]
  have c1 : m' 1 = 1 := by rw [g 1 (by simp [nW]) (by omega), hR.r1]
  unfold yBody tYB
  refine copy_seq' (copy_seq' ?_)
  refine block_seq (T := L.k * (tIB L.n L.k + 2) + 1) (T' := 2)
    (runsTo_countLoop (c := 99) wf_iBody (NbI L p mc r y) L.k (tIB L.n L.k)
      (fun i m h => ⟨h.2.2.1, h.1⟩) (fun i m hi hI => runsTo_iBody hb hr hy hi hB hT hI) _ ?_)
    (fun m2 hI2 => ?_)
  · unfold NbI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, c51, c57, e96, e97, e89]
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, by simp [Blk.nil], ?_⟩
    · have hl := length_range_flatMap (length_nbCell p L.n L.k r) y
      exact Blk.update (Blk.update hP (Or.inl (by omega))) (Or.inl (by omega))
    · exact (hK.upd (Or.inl (by simp [nW])) _).upd (Or.inl (by simp [nW])) _
  · obtain ⟨-, -, -, f89, f96, f97, fP, fC, fK⟩ := hI2
    have c1' : m2 1 = 1 := by
      rw [fK 1 (by simp [nW]) (Or.inl (by omega)), hR.r1]
    rt
    unfold YI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f89, f96, f97, c1']
    refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, ?_, ?_⟩
    · have hl := length_range_flatMap (length_nbCell p L.n L.k r) y
      rw [range_flatMap_succ, Blk.append, hl]
      rw [List.take_of_length_le (by simp)] at fC
      exact ⟨Blk.update (Blk.update fP (Or.inl (by omega))) (Or.inl (by omega)),
        Blk.update (Blk.update fC (Or.inl (by omega))) (Or.inl (by omega))⟩
    · exact (fK.upd (Or.inl (by simp [nW])) _).upd (Or.inl (by simp [nW])) _

/-- Store `IX[r]`, `C[IX[r]] := c_r`, start the loop over `y`. -/
theorem runsTo_rowMid (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) {m : Mem}
    (hB : BFr L M m) (h86 : m 86 = L.R0 + r * L.RW) (h88 : m 88 = L.IX + r)
    (h80 : m 80 = idxOf L.n (tup p r)) :
    RunsTo rowMid (fun m' => m' = m)
      (fun m' => m' (L.IX + r) = idxOf L.n (tup p r) ∧
        m' (L.C + idxOf L.n (tup p r)) = colOf p r ∧ m' 88 = L.IX + r + 1 ∧ m' 96 = 0 ∧
        m' 97 = L.n ∧ ∀ z, z ∉ [88, 90, 94, 95, 96, 97] → z ≠ L.IX + r →
          z ≠ L.C + idxOf L.n (tup p r) → m' z = m z) 9 := by
  have hR := hB.regs hb
  have hF := hb.hF
  have hlen := hb.len_tup hr
  have hidx : idxOf L.n (tup p r) < p.2.length := by
    rw [hb.hn]; exact hb.idx_lt hlen (fun d hd => hb.tup_lt hr hd)
  have hN := hb.hN
  have hc : L.R0 + r * L.RW + (2 * k + 3) < L.IX :=
    hb.row_lt hr (by simp only [Lay.RW, hb.hk]; omega)
  have hR0 : 100 ≤ L.R0 := by simp only [Lay.R0]; omega
  have hIX : 100 ≤ L.IX := by simp only [Lay.IX]; omega
  have hcol : m (L.R0 + r * L.RW + (2 * k + 3)) = colOf p r := by
    rw [hB.input hb (by simp only [Lay.R0]; omega) hc]
    obtain ⟨-, -, -, -, h4⟩ := hb.row hr
    rw [← hb.tup_eq hr, hlen] at h4
    rw [show L.R0 + r * L.RW + (2 * k + 3) = L.R0 + r * L.RW + 3 + 2 * k by ring, h4,
      hb.colOf_eq hr]
  have hRW : L.RW = 2 * k + 4 := by simp only [Lay.RW, hb.hk]
  have hIXC : L.IX + r < L.C := by simp only [Lay.C]; omega
  unfold rowMid
  rt
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, h86, h88, h80, hR.r54, hR.r56,
    hR.r50, hR.r1]
  rw [show L.R0 + r * L.RW + L.RW - 1 = L.R0 + r * L.RW + (2 * k + 3) by rw [hRW]; omega]
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hcol]
  refine ⟨by wl_ar, by wl_ar, by wl_ar, by wl_ar, by wl_ar, fun z hz h1 h2 => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
  simp (disch := omega) only [Mem.update_of_ne]

theorem BaseOK.idx_ne (hb : BaseOK n k p L M) {r r' : ℕ} (hr : r < p.2.length)
    (hr' : r' < p.2.length) (hne : r ≠ r') : idxOf L.n (tup p r) ≠ idxOf L.n (tup p r') := by
  intro h
  have he := idxOf_inj (by rw [hb.len_tup hr, hb.len_tup hr'])
    (fun d hd => by rw [hb.hn]; exact hb.tup_lt hr hd)
    (fun d hd => by rw [hb.hn]; exact hb.tup_lt hr' hd) h
  rw [hb.tup_eq hr, hb.tup_eq hr'] at he
  have h1 : (p.2.map Prod.fst)[r]'(by simpa using hr) =
      (p.2.map Prod.fst)[r']'(by simpa using hr') := by
    simpa using he
  exact hne ((List.Nodup.getElem_inj_iff hb.wf.keyNodup).1 h1)

theorem BaseOK.idxL_lt (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) :
    idxOf L.n (tup p r) < p.2.length := by
  rw [hb.hn]; exact hb.idx_lt (hb.len_tup hr) (fun d hd => hb.tup_lt hr hd)

/-- The build after `r` rows. -/
def BuildI (L : Lay) (p : RawWL) (M : Mem) (r : ℕ) (m : Mem) : Prop :=
  r ≤ L.N ∧ m 86 = L.R0 + r * L.RW ∧ m 88 = L.IX + r ∧ m 89 = L.Nb + r * (L.n * L.k) ∧
    m 92 = L.N - r ∧ Arr p L r m ∧ BFr L M m

/-- The step count of one row. -/
def tRow (n k : ℕ) : ℕ :=
  (k * (6 + 2) + 1 + 1 + 1 + 1 + 1) + (tHorn n k + (9 + ((n * (tYB n k + 2) + 1) + 2)))

theorem runsTo_rowBody (hb : BaseOK n k p L M) {r : ℕ} (hr : r < p.2.length) {m : Mem}
    (hI : BuildI L p M r m) :
    RunsTo rowBody (fun m' => m' = m) (BuildI L p M (r + 1)) (tRow L.n L.k) := by
  obtain ⟨-, e86, e88, e89, e92, hA, hB⟩ := hI
  have hR := hB.regs hb
  have hF := hb.hF
  have hN := hb.hN
  have hlen := hb.len_tup hr
  have hkL := hb.hk
  have hidxN := hb.idxL_lt hr
  set idx := idxOf L.n (tup p r) with hidx
  have hIXC : L.IX + L.N = L.C := rfl
  have hCT : L.C + L.N = L.T := rfl
  have hTN : L.T + L.k = L.Nb := rfl
  have hrow := nb_row_le hb hr
  have hr1 : (r + 1) * (L.n * L.k) = r * (L.n * L.k) + L.n * L.k := by ring
  have hT100 : 100 ≤ L.IX := by simp only [Lay.IX]; omega
  unfold rowBody tRow
  -- copy the tuple
  refine block_seq (runsTo_cpTup hb hr hB e86) (fun ma ⟨hTa, hKa⟩ => ?_)
  have ga : ∀ z, z < 100 → z ∉ [90, 91, 93, 94] → ma z = m z := fun z h1 h2 =>
    hKa z h2 (Or.inl (by omega))
  have hBa : BFr L M ma := hB.trans hKa (fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rw [mem_bW]; omega)
    (by omega) (by omega)
  -- its index
  refine block_seq ((runsTo_hornP (m0 := ma) (n := L.n) hTa (by omega)
    (by rw [ga 1 (by omega) (by simp), hR.r1]) (by rw [ga 50 (by omega) (by simp), hR.r50])
    (by rw [ga 51 (by omega) (by simp), hR.r51, hlen, hkL])
    (by rw [ga 57 (by omega) (by simp), hR.r57])).mono (by rw [hlen, hkL]))
    (fun mb ⟨e80, hkb⟩ => ?_)
  have hBb : BFr L M mb := hBa.trans (fun z hz _ => hkb z hz) (fun z hz => by
    simp only [hornW, List.mem_cons, List.not_mem_nil, or_false] at hz; rw [mem_bW]; omega)
    le_rfl le_rfl
  have gb : ∀ z, z < 100 → z ∉ hornW → z ∉ [90, 91, 93, 94] → mb z = m z := fun z h1 h2 h3 => by
    rw [hkb z h2, ga z h1 h3]
  -- `IX[r]`, `C[IX[r]]`
  refine block_seq (runsTo_rowMid hb hr hBb
    (by rw [gb 86 (by omega) (by simp [hornW]) (by simp), e86])
    (by rw [gb 88 (by omega) (by simp [hornW]) (by simp), e88]) e80)
    (fun mc ⟨i1, i2, i3, i4, i5, hkc⟩ => ?_)
  have hCi : L.C + idx < L.T := by omega
  have hBc : BFr L M mc := by
    intro z hz hab
    rw [hkc z (nmem_bW hz (by decide)) (by omega) (by omega)]
    exact hBb z hz hab
  have hTc : Blk mc L.T (tup p r) := hTa.congr (fun z hz1 hz2 => by
    rw [hkc z (by simp; omega) (by omega) (by omega), hkb z (by simp [hornW]; omega)])
  have gc : ∀ z, z < 100 → z ∉ hornW → z ∉ [90, 91, 93, 94] → z ∉ [88, 90, 94, 95, 96, 97] →
      mc z = m z := fun z h1 h2 h3 h4 => by
    rw [hkc z h4 (by omega) (by omega), gb z h1 h2 h3]
  -- the neighbours
  have c89 : mc 89 = L.Nb + r * (L.n * L.k) + 0 * L.k := by
    rw [gc 89 (by omega) (by simp [hornW]) (by simp) (by simp), e89]; ring
  refine block_seq (runsTo_countLoop (c := 97) wf_yBody (YI L p mc r) L.n (tYB L.n L.k)
    (fun y m h => ⟨h.2.2.1, h.1⟩) (fun y m hy hI => runsTo_yBody hb hr hy hBc hTc hI) mc
    ⟨by omega, i4, (by rw [i5]; rfl), c89, (by simp [Blk.nil]), Keep.refl _ _ _ _⟩)
    (fun md ⟨_, _, _, f89, fP, fK⟩ => ?_)
  have gd : ∀ z, z < 100 → z ∉ nW → md z = mc z := fun z h1 h2 => fK z h2 (Or.inl (by omega))
  have hreg : ∀ z, z < 100 → z ∉ hornW → z ∉ [90, 91, 93, 94] → z ∉ [88, 90, 94, 95, 96, 97] →
      z ∉ nW → md z = m z := fun z h1 h2 h3 h4 h5 => by rw [gd z h1 h5, gc z h1 h2 h3 h4]
  have d86 : md 86 = L.R0 + r * L.RW := by
    rw [hreg 86 (by omega) (by simp [hornW]) (by simp) (by simp) (by simp [nW]), e86]
  have d92 : md 92 = L.N - r := by
    rw [hreg 92 (by omega) (by simp [hornW]) (by simp) (by simp) (by simp [nW]), e92]
  have d88 : md 88 = L.IX + r + 1 := by rw [gd 88 (by omega) (by simp [nW]), i3]
  have hBd : BFr L M md := by
    intro z hz hab
    rw [fK z (nmem_bW hz (by decide)) (by omega)]
    exact hBc z hz hab
  have hRd := hBd.regs hb
  -- the cells of `m` kept to the end of the row
  have fr : ∀ z, 100 ≤ z → (z < L.T ∨ L.T + L.k ≤ z) → z ≠ L.IX + r → z ≠ L.C + idx →
      (z < L.Nb + r * (L.n * L.k) ∨ L.Nb + (r + 1) * (L.n * L.k) ≤ z) → md z = m z := by
    intro z h1 h2 h3 h4 h5
    rw [fK z (by simp [nW]; omega) h5, hkc z (by simp; omega) h3 h4,
      hkb z (by simp [hornW]; omega), hKa z (by simp; omega) h2]
  have dIX : md (L.IX + r) = idx := by
    rw [fK (L.IX + r) (by simp [nW]; omega) (Or.inl (by omega)), i1]
  have dC : md (L.C + idx) = colOf p r := by
    rw [fK (L.C + idx) (by simp [nW]; omega) (Or.inl (by omega)), i2]
  obtain ⟨hA1, hA2, hA3⟩ := hA
  rt
  unfold BuildI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, d86, d92, d88, f89, hRd.r54,
    hRd.r1]
  refine ⟨by omega, by simp only [Lay.RW]; ring, by wl_ar, by ring, by omega, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- `IX`
    rw [ixPre, range_map_succ, Blk.append]
    refine ⟨Blk.update (Blk.update (hA1.congr (fun z hz1 hz2 => ?_)) (Or.inl (by omega)))
      (Or.inl (by omega)), ?_⟩
    · simp only [ixPre, List.length_map, List.length_range] at hz2
      exact fr z (by omega) (Or.inl (by omega)) (by omega) (by omega) (Or.inl (by omega))
    · simp only [List.length_map, List.length_range, Blk.cons, Blk.nil, and_true]
      simp (disch := omega) only [Mem.update_of_ne]
      exact dIX
  · -- `C`
    intro r' hr'
    simp (disch := omega) only [Mem.update_of_ne]
    rcases Nat.lt_or_ge r' r with h | h
    · have hr'N : r' < p.2.length := by omega
      have hne := hb.idx_ne hr'N hr (by omega)
      have hlt := hb.idxL_lt hr'N
      rw [fr _ (by omega) (Or.inl (by omega)) (by omega) (by omega) (Or.inl (by omega))]
      exact hA2 r' h
    · obtain rfl : r' = r := by omega
      exact dC
  · -- `Nb`
    rw [range_flatMap_succ, Blk.append, length_range_flatMap (length_nbRow p L.n L.k)]
    refine ⟨Blk.update (Blk.update (hA3.congr (fun z hz1 hz2 => ?_)) (Or.inl (by omega)))
      (Or.inl (by omega)), Blk.update (Blk.update fP (Or.inl (by omega))) (Or.inl (by omega))⟩
    rw [length_range_flatMap (length_nbRow p L.n L.k)] at hz2
    exact fr z (by omega) (Or.inr (by omega)) (by omega) (by omega) (Or.inl (by omega))
  · exact (hBd.upd (Or.inl (by rw [mem_bW]; omega)) _).upd (Or.inl (by rw [mem_bW]; omega)) _

/-- The step count of the build. -/
def tBuild (N n k : ℕ) : ℕ := N * (tRow n k + 2) + 1 + 1 + 1 + 1 + 1

/-- **The build.**  Starting from the memory `M` after the setup, `buildP` fills `IX`, `C` and
`Nb`, and writes nothing outside the registers `80`–`99` and `[IX, Rec)`. -/
theorem runsTo_buildP (hb : BaseOK n k p L M) :
    RunsTo buildP (fun m => m = M) (fun m => Arr p L L.N m ∧ BFr L M m)
      (tBuild L.N L.n L.k) := by
  have hR := hb.regs
  have hF := hb.hF
  have hN := hb.hN
  have hT100 : 100 ≤ L.IX := by simp only [Lay.IX]; omega
  unfold buildP tBuild
  refine copy_seq' (copy_seq' (copy_seq' (copy_seq' ?_)))
  refine (runsTo_countLoop (c := 92) wf_rowBody (BuildI L p M) L.N (tRow L.n L.k)
    (fun r m h => ⟨h.2.2.2.2.1, h.1⟩) (fun r m hr hI => runsTo_rowBody hb (by omega) hI) _ ?_).weaken
    (fun m h => ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
  unfold BuildI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hR.r53, hR.r55, hR.r58, hR.r52]
  refine ⟨by omega, by ring, by ring, by ring, by omega, ⟨by simp [ixPre, Blk.nil],
    fun r' h => absurd h (Nat.not_lt_zero _), by simp [Blk.nil]⟩, ?_⟩
  intro z hz hab
  rw [mem_bW] at hz
  simp (disch := omega) only [Mem.update_of_ne]

end Build

end WLFast

end Algo
