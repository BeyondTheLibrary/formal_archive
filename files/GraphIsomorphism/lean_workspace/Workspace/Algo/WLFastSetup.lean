/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The setup of the fast
program: copy the input, read `n`, `k`, `N` off it, and lay out the work arrays.
-/
import Workspace.Algo.WLFastIn

/-!
# The setup of the fast `k`-WL program

The input `encode p` sits at `17` (after `RAM.Bridge.up`).  The program copies it to
`F = |encode p| + 100`, above all registers, reads `n` (half the first cell), the cell
`N (2k + 4)` after the domain, and, when `N ≠ 0`, `k` (from the first row) and `N`.  Then it
computes the addresses of the work arrays (`Algo.WLFast.Lay`):

  `IX` (`N` cells), `C` (`N`), `T` (`k`), `Nb` (`N n k`), `Rec` (`N n (k+1)`), `A` (`N n`),
  `SR` (`N (nk+2)`), `A2` (`N`), `Cnt` (the sorting counters),

and keeps them in the registers listed in `Algo.WLFast.RegsOK`.

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

/-- Close a small arithmetic side goal (it may have been simplified to `True`). -/
macro "wl_ar" : tactic => `(tactic| first | trivial | omega | ring | (simp; done))

/-! ## Loops whose counter drops by a fixed step -/

/-- **A loop whose counter drops by `s` per round.** -/
theorem runsTo_stepLoop {c : ℕ} {P : Program} (hw : Wf P) (I : ℕ → Mem → Prop) (L T s : ℕ)
    (hs : 0 < s) (hc : ∀ t m, I t m → m c = (L - t) * s ∧ t ≤ L)
    (hP : ∀ t m, t < L → I t m → RunsTo P (fun m' => m' = m) (I (t + 1)) T)
    (M : Mem) (hM : I 0 M) :
    RunsTo (whileNz c P) (fun m => m = M) (I L) (L * (T + 2) + 1) := by
  obtain ⟨s', hs'⟩ := runsTo_whileNz_amortX (i := c) hw (fun m => ∃ t, I t m)
    (fun m => (m c / s) * (T + 2)) (fun m ⟨t, ht⟩ hne => by
      obtain ⟨h1, h2⟩ := hc t m ht
      have htL : t < L := by
        by_contra hh; apply hne; rw [h1, show L - t = 0 by omega, zero_mul]
      refine ⟨T, (hP t m htL ht).weaken (fun m' hm' => ⟨⟨t + 1, hm'⟩, ?_⟩)⟩
      obtain ⟨h1', _⟩ := hc (t + 1) m' hm'
      show m' c / s * (T + 2) + T + 2 ≤ m c / s * (T + 2)
      rw [h1', h1, Nat.mul_div_cancel _ hs, Nat.mul_div_cancel _ hs]
      have : L - t = (L - (t + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega) M ⟨0, hM⟩
  obtain ⟨M', ⟨⟨t, ht⟩, h0, hΦ⟩, hrun⟩ := hs'.exact
  obtain ⟨e1, e2⟩ := hc t M' ht
  have htL : t = L := by
    rw [h0] at e1
    rcases Nat.mul_eq_zero.1 e1.symm with h | h <;> omega
  subst htL
  obtain ⟨e3, _⟩ := hc 0 M hM
  refine (hrun.mono ?_).weaken (fun m hm => by rw [hm]; exact ht)
  rw [h0, Nat.zero_div, zero_mul, zero_add, e3, Nat.mul_div_cancel _ hs] at hΦ
  simp only [Nat.sub_zero] at hΦ
  exact hΦ

/-! ## Halving and multiplying -/

/-- One round of halving: `R c -= 2`, `R r += 1`. -/
def halfB (c r : ℕ) : Program := seq (subTo c c 1) (seq (subTo c c 1) (addTo r r 1))

theorem wf_halfB (c r : ℕ) : Wf (halfB c r) := by unfold halfB; wf_tac

/-- **Halving**: from `R c = 2a` and `R r = 0`, the loop leaves `a` in `R r`. -/
theorem runsTo_halve {c r : ℕ} (hc1 : c ≠ 1) (hr1 : r ≠ 1) (hcr : c ≠ r) {M : Mem} {a : ℕ}
    (h1 : M 1 = 1) (hc : M c = a * 2) (hr : M r = 0) :
    RunsTo (whileNz c (halfB c r)) (fun m => m = M)
      (fun m => m r = a ∧ ∀ z, z ≠ c → z ≠ r → m z = M z) (a * (3 + 2) + 1) := by
  refine (runsTo_stepLoop (wf_halfB c r)
    (fun t m => m c = (a - t) * 2 ∧ t ≤ a ∧ m r = t ∧ ∀ z, z ≠ c → z ≠ r → m z = M z) a 3 2
    (by norm_num) (fun t m h => ⟨h.1, h.2.1⟩) (fun t m ht ⟨e1, _, e2, hk⟩ => ?_) M
    ⟨by rw [hc]; simp, by omega, hr, fun _ _ _ => rfl⟩).weaken
    (fun m ⟨_, _, e, hk⟩ => ⟨e, hk⟩)
  have c1 : m 1 = 1 := by rw [hk 1 (Ne.symm hc1) (Ne.symm hr1), h1]
  unfold halfB
  rt
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, c1, e1, e2]
  refine ⟨?_, by omega, by simp, fun z h h' => ?_⟩
  · have : a - t = (a - (t + 1)) + 1 := by omega
    rw [this]; omega
  · simp (disch := omega) only [Mem.update_of_ne]; exact hk z h h'

/-- `R x := R a * R b` by `R b` additions; register `74` is the counter. -/
def mulP (x a b : ℕ) : Program :=
  seq (assign x 0) (seq (copyTo 74 b) (whileNz 74 (seq (addTo x x a) (subTo 74 74 1))))

theorem wf_mulP (x a b : ℕ) : Wf (mulP x a b) := by
  unfold mulP
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_whileNz (by wf_tac)))

theorem runsTo_mulP {x a b : ℕ} (hx74 : x ≠ 74) (ha74 : a ≠ 74) (hxa : x ≠ a) (hx1 : x ≠ 1)
    (hbx : b ≠ x) {M : Mem} (h1 : M 1 = 1) :
    RunsTo (mulP x a b) (fun m => m = M)
      (fun m => m x = M a * M b ∧ ∀ z, z ≠ x → z ≠ 74 → m z = M z) (M b * 4 + 3) := by
  unfold mulP
  refine RunsTo.mono (T := M b * (2 + 2) + 1 + 1 + 1) ?_ (by omega)
  refine assign_seq' (copy_seq' ?_)
  set M1 := (M.update x 0).update 74 ((M.update x 0) b) with hM1
  have hb : M1 74 = M b := by
    rw [hM1, Mem.update_self, Mem.update_of_ne _ _ hbx]
  refine (runsTo_countLoop (c := 74) (by wf_tac)
    (fun t m => m 74 = M b - t ∧ t ≤ M b ∧ m x = M a * t ∧ ∀ z, z ≠ x → z ≠ 74 → m z = M1 z)
    (M b) 2 (fun t m h => ⟨h.1, h.2.1⟩) (fun t m ht ⟨e1, _, e2, hk⟩ => ?_) M1
    ⟨by rw [hb]; rfl, by omega, ?_, fun _ _ _ => rfl⟩).weaken
    (fun m ⟨_, _, e, hk⟩ => ⟨e, fun z h h' => by
      rw [hk z h h', hM1]; simp (disch := omega) only [Mem.update_of_ne]⟩)
  · have c1 : m 1 = 1 := by
      rw [hk 1 (Ne.symm hx1) (by omega), hM1]
      simp (disch := omega) only [Mem.update_of_ne]; exact h1
    have ca : m a = M a := by
      rw [hk a (Ne.symm hxa) ha74, hM1]; simp (disch := omega) only [Mem.update_of_ne]
    rt
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, c1, e1, e2, ca]
    refine ⟨by omega, by omega, by ring, fun z h h' => ?_⟩
    simp (disch := omega) only [Mem.update_of_ne]; exact hk z h h'
  · rw [hM1]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, mul_zero]

/-! ## The layout -/

/-- The parameters of the layout: the address `F` of the input copy, its length `Lin`, and
`n`, `k`, `N`. -/
structure Lay where
  F : ℕ
  Lin : ℕ
  n : ℕ
  k : ℕ
  N : ℕ

namespace Lay

variable (L : Lay)

/-- Row `0` of the table. -/
def R0 : ℕ := L.F + 2 * L.n + 2
/-- The width of a row. -/
def RW : ℕ := 2 * L.k + 4
/-- `IX[r]`: the index of the tuple of row `r`. -/
def IX : ℕ := L.F + L.Lin
/-- `C[h]`: the current color of the tuple of index `h`. -/
def C : ℕ := L.IX + L.N
/-- The tuple buffer. -/
def T : ℕ := L.C + L.N
/-- `Nb[(rn+y)k+i]`: the index of the tuple of row `r` with entry `i` set to `y`. -/
def Nb : ℕ := L.T + L.k
/-- `N n`. -/
def NN : ℕ := L.N * L.n
/-- The records `(r, colors of the neighbours)`, `N n` of width `k + 1`. -/
def Rec : ℕ := L.Nb + L.NN * L.k
/-- The addresses of the records. -/
def A : ℕ := L.Rec + L.NN * (L.k + 1)
/-- The strings of the rows, `N` of width `nk + 2` (the last cell takes the rank). -/
def SR : ℕ := L.A + L.NN
/-- The addresses of the strings. -/
def A2 : ℕ := L.SR + L.N * (L.n * L.k + 2)
/-- The counters of the sorts. -/
def Cnt : ℕ := L.A2 + L.N

/-- The addresses, as equations `omega` can use. -/
theorem facts : L.C = L.IX + L.N ∧ L.T = L.C + L.N ∧ L.Nb = L.T + L.k ∧
    L.Rec = L.Nb + L.NN * L.k ∧ L.A = L.Rec + L.NN * (L.k + 1) ∧ L.SR = L.A + L.NN ∧
    L.A2 = L.SR + L.N * (L.n * L.k + 2) ∧ L.Cnt = L.A2 + L.N ∧ L.IX = L.F + L.Lin ∧
    L.R0 = L.F + 2 * L.n + 2 ∧ L.RW = 2 * L.k + 4 ∧ L.NN = L.N * L.n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Lay

/-- **The registers of the layout.** -/
structure RegsOK (L : Lay) (m : Mem) : Prop where
  r1 : m 1 = 1
  r16 : m 16 = L.Lin
  r50 : m 50 = L.n
  r51 : m 51 = L.k
  r52 : m 52 = L.N
  r53 : m 53 = L.R0
  r54 : m 54 = L.RW
  r55 : m 55 = L.IX
  r56 : m 56 = L.C
  r57 : m 57 = L.T
  r58 : m 58 = L.Nb
  r59 : m 59 = L.Rec
  r60 : m 60 = L.SR
  r61 : m 61 = L.A
  r62 : m 62 = L.Cnt
  r63 : m 63 = L.k + 1
  r64 : m 64 = L.n * L.k + 2
  r65 : m 65 = L.n * L.k
  r66 : m 66 = L.N + 1
  r67 : m 67 = L.n * L.k + 1
  r69 : m 69 = L.F
  r70 : m 70 = L.NN
  r75 : m 75 = L.A2

/-- The registers `RegsOK` reads. -/
def persist : List ℕ :=
  [1, 16, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 75]

theorem RegsOK.congr {L : Lay} {m m' : Mem} (h : RegsOK L m) (h' : ∀ z ∈ persist, m' z = m z) :
    RegsOK L m' := by
  have e : ∀ z ∈ persist, ∀ v, m z = v → m' z = v := fun z hz v hv => by rw [h' z hz, hv]
  exact ⟨e _ (by simp [persist]) _ h.r1, e _ (by simp [persist]) _ h.r16,
    e _ (by simp [persist]) _ h.r50, e _ (by simp [persist]) _ h.r51,
    e _ (by simp [persist]) _ h.r52, e _ (by simp [persist]) _ h.r53,
    e _ (by simp [persist]) _ h.r54, e _ (by simp [persist]) _ h.r55,
    e _ (by simp [persist]) _ h.r56, e _ (by simp [persist]) _ h.r57,
    e _ (by simp [persist]) _ h.r58, e _ (by simp [persist]) _ h.r59,
    e _ (by simp [persist]) _ h.r60, e _ (by simp [persist]) _ h.r61,
    e _ (by simp [persist]) _ h.r62, e _ (by simp [persist]) _ h.r63,
    e _ (by simp [persist]) _ h.r64, e _ (by simp [persist]) _ h.r65,
    e _ (by simp [persist]) _ h.r66, e _ (by simp [persist]) _ h.r67,
    e _ (by simp [persist]) _ h.r69, e _ (by simp [persist]) _ h.r70,
    e _ (by simp [persist]) _ h.r75⟩

/-! ## The input in memory -/

theorem initMemAt_cell (l : List ℕ) (j : ℕ) (hj : j < l.length) : initMemAt 16 l (17 + j) = l[j] := by
  rw [initMemAt_of_ge _ (by omega)]
  simp only [initMem, show 17 + j - 16 = j + 1 by omega, Nat.add_one_ne_zero, if_false,
    Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ hj]

theorem initMemAt_16 (l : List ℕ) : initMemAt 16 l 16 = l.length := by
  rw [initMemAt_of_ge _ le_rfl]; simp [initMem]

/-! ## Part A: copy the input to `F` -/

/-- Copy the input (at `17`) to `F = |input| + 100`; keep `F` in register `69`. -/
def setupA : Program :=
  seq (assign 1 1) (seq (assign 5 17) (seq (copyTo 6 16) (seq (assign 7 100) (seq (addTo 6 6 7)
  (seq (copyTo 7 16) (seq (Arrays.copyBlock 5 6 7 8) (copyTo 69 6)))))))

theorem wf_setupA : Wf setupA := by
  unfold setupA
  unfold Arrays.copyBlock Arrays.copyPre Arrays.copyBody
  wf_tac

theorem runsTo_setupA (l : List ℕ) :
    RunsTo setupA (fun m => m = initMemAt 16 l)
      (fun m => m 1 = 1 ∧ m 16 = l.length ∧ m 69 = l.length + 100 ∧ Blk m (l.length + 100) l)
      (7 * l.length + 12) := by
  unfold setupA
  refine RunsTo.mono (T := (7 * l.length + 5) + (0 + 1) + 1 + 1 + 1 + 1 + 1 + 1) ?_ (by omega)
  rt
  refine block_seq (T := 7 * l.length + 5) (T' := 0 + 1)
    ((Arrays.runsTo_copyBlock 5 6 7 8 (by norm_num) (by norm_num) (by norm_num) _ ?_ ?_ ?_).mono ?_)
    (fun m ⟨hc, hk⟩ => ?_)
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]; norm_num
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, initMemAt_16] <;> omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, initMemAt_16] <;> omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, initMemAt_16] <;> omega
  · simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, initMemAt_16] at hc hk
    refine copy_last' ?_
    have k6 := hk 6 (by omega) (by simp)
    have k1 := hk 1 (by omega) (by simp)
    have k16 := hk 16 (by omega) (by simp)
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, initMemAt_16] at k6 k1 k16
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne]
    refine ⟨k1, k16, by rw [k6]; try ring, fun j hj => ?_⟩
    rw [Mem.update_of_ne _ _ (by omega), hc j hj, initMemAt_cell l j hj]


/-! ## Part B: read `n` and the length of the table encoding -/

/-- After the domain: `R53 := F + 2n + 2` (row `0`), `R72 := N (2k + 4)`. -/
def tailB : Program :=
  seq (copyTo 72 69) (seq (addTo 72 72 50) (seq (addTo 72 72 50) (seq (addTo 72 72 1)
  (seq (addTo 53 72 1) (loadTo 72 72)))))

/-- Read `n` by halving the first cell, then the length cell of the table. -/
def setupB : Program :=
  seq (loadTo 71 69) (seq (assign 50 0) (seq (whileNz 71 (halfB 71 50)) tailB))

theorem wf_setupB : Wf setupB := by
  unfold setupB tailB
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (wf_whileNz (wf_halfB _ _)) (by wf_tac)))

theorem runsTo_setupB {M : Mem} {n k : ℕ} {p : RawWL} (hp : RawWL.WF n k p) {F : ℕ}
    (hF : 100 ≤ F) (h1 : M 1 = 1) (h69 : M 69 = F) (hB : Blk M F (Enc.encode p)) :
    RunsTo setupB (fun m => m = M)
      (fun m => m 50 = n ∧ m 53 = F + 2 * n + 2 ∧ m 72 = p.2.length * (2 * k + 4) ∧
        ∀ z, z ≠ 50 → z ≠ 53 → z ≠ 71 → z ≠ 72 → m z = M z)
      (n * 5 + 9) := by
  have hk : ∀ q ∈ p.2, q.1.length = k := fun q hq =>
    ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).1
  obtain ⟨e0, -, e2, -⟩ := (blk_rawWL_iff hk).1 hB
  rw [length_dom hp] at e0 e2
  unfold setupB
  refine RunsTo.mono (T := ((n * (3 + 2) + 1) + 6) + 1 + 1) ?_ (by omega)
  refine load_seq' (assign_seq' ?_)
  refine block_seq (T := n * (3 + 2) + 1) (T' := 6) (runsTo_halve (c := 71) (r := 50)
    (by omega) (by omega) (by omega) ?_ ?_ ?_) (fun m ⟨e, hkm⟩ => ?_)
  · simp (disch := omega) only [Mem.update_of_ne]; exact h1
  · simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; rw [h69, e0]; ring
  · simp (disch := omega) only [Mem.update_self]
  · have c69 : m 69 = F := by
      rw [hkm 69 (by omega) (by omega)]; simp (disch := omega) only [Mem.update_of_ne]; exact h69
    have c1 : m 1 = 1 := by
      rw [hkm 1 (by omega) (by omega)]; simp (disch := omega) only [Mem.update_of_ne]; exact h1
    have cF : m (F + 2 * n + 1) = p.2.length * (2 * k + 4) := by
      rw [hkm (F + 2 * n + 1) (by omega) (by omega)]
      simp (disch := omega) only [Mem.update_of_ne]; exact e2
    unfold tailB
    rt
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, c69, c1, e]
    refine ⟨by simp, by omega, ?_, fun z a b c d => ?_⟩
    · rw [show F + n + n + 1 = F + 2 * n + 1 by ring, cF]
    · simp (disch := omega) only [Mem.update_of_ne]
      rw [hkm z c a]; simp (disch := omega) only [Mem.update_of_ne]

/-! ## Part C: read `k` and `N` (when `N ≠ 0`) -/

/-- One round of the division by the row width. -/
def nBody : Program := seq (subTo 72 72 54) (addTo 52 52 1)

/-- Read `k` from the first row (`2k` in its second cell), the width `2k + 4`, and
`N = R72 / (2k + 4)`. -/
def parseK : Program :=
  seq (addTo 71 53 1) (seq (loadTo 71 71) (seq (assign 51 0) (seq (whileNz 71 (halfB 71 51))
  (seq (addTo 54 51 51) (seq (assign 73 4) (seq (addTo 54 54 73) (seq (assign 52 0)
  (whileNz 72 nBody))))))))

theorem wf_parseK : Wf parseK := by
  unfold parseK
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq
    (wf_whileNz (wf_halfB _ _)) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_whileNz (by unfold nBody; wf_tac)))))))))

theorem runsTo_parseK {M : Mem} {n k : ℕ} {p : RawWL} (hp : RawWL.WF n k p) {F : ℕ}
    (hF : 100 ≤ F) (hN : 0 < p.2.length) (h1 : M 1 = 1) (hB : Blk M F (Enc.encode p))
    (h53 : M 53 = F + 2 * n + 2) (h72 : M 72 = p.2.length * (2 * k + 4)) :
    RunsTo parseK (fun m => m = M)
      (fun m => m 51 = k ∧ m 54 = 2 * k + 4 ∧ m 52 = p.2.length ∧
        ∀ z, z ≠ 51 → z ≠ 52 → z ≠ 54 → z ≠ 71 → z ≠ 72 → z ≠ 73 → m z = M z)
      (k * 5 + p.2.length * 4 + 9) := by
  have hk : ∀ q ∈ p.2, q.1.length = k := fun q hq =>
    ((hp.keyMem q.1).1 (List.mem_map_of_mem hq)).1
  obtain ⟨-, -, -, e3⟩ := (blk_rawWL_iff hk).1 hB
  obtain ⟨-, r1, -⟩ := e3 0 hN
  rw [length_dom hp, hk _ (List.getElem_mem hN), zero_mul, add_zero] at r1
  unfold parseK
  refine RunsTo.mono (T := ((k * (3 + 2) + 1) + (p.2.length * (2 + 2) + 1 + 1 + 1 + 1 + 1))
    + 1 + 1 + 1) ?_ (by omega)
  refine add_seq' (load_seq' (assign_seq' ?_))
  refine block_seq (T := k * (3 + 2) + 1) (T' := p.2.length * (2 + 2) + 1 + 1 + 1 + 1 + 1)
    (runsTo_halve (c := 71) (r := 51)
    (by omega) (by omega) (by omega) ?_ ?_ ?_) (fun m ⟨e, hkm⟩ => ?_)
  · simp (disch := omega) only [Mem.update_of_ne]; exact h1
  · simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; rw [h53, h1, r1]; ring
  · simp (disch := omega) only [Mem.update_self]
  have c1 : m 1 = 1 := by
    rw [hkm 1 (by omega) (by omega)]; simp (disch := omega) only [Mem.update_of_ne]; exact h1
  have c72 : m 72 = p.2.length * (2 * k + 4) := by
    rw [hkm 72 (by omega) (by omega)]; simp (disch := omega) only [Mem.update_of_ne]; exact h72
  refine add_seq' (assign_seq' (add_seq' (assign_seq' ?_)))
  set m1 := (((((m.update 54 (m 51 + m 51)).update 73 4).update 54
    ((m.update 54 (m 51 + m 51)).update 73 4 54 + (m.update 54 (m 51 + m 51)).update 73 4 73))).update
    52 0) with hm1
  have d54 : m1 54 = 2 * k + 4 := by
    rw [hm1]; simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e]; ring
  refine (runsTo_stepLoop (c := 72) (by unfold nBody; wf_tac)
    (fun t m' => m' 72 = (p.2.length - t) * (2 * k + 4) ∧ t ≤ p.2.length ∧ m' 52 = t ∧
      ∀ z, z ≠ 52 → z ≠ 72 → m' z = m1 z) p.2.length 2 (2 * k + 4) (by omega)
    (fun t m' h => ⟨h.1, h.2.1⟩) (fun t m' ht ⟨f1, _, f2, fk⟩ => ?_) m1 ⟨?_, by omega, ?_,
      fun _ _ _ => rfl⟩).weaken (fun m' ⟨_, _, f2, fk⟩ => ⟨?_, ?_, f2, fun z a b c d e' g => ?_⟩)
  · have g54 : m' 54 = 2 * k + 4 := by rw [fk 54 (by omega) (by omega), d54]
    unfold nBody
    rt
    have g1 : m' 1 = 1 := by
      rw [fk 1 (by omega) (by omega), hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact c1
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, f1, f2, g54, g1]
    refine ⟨?_, by omega, by simp, fun z a b => ?_⟩
    · rw [show p.2.length - t = (p.2.length - (t + 1)) + 1 by omega, Nat.add_mul, one_mul,
        Nat.add_sub_cancel]
    · simp (disch := omega) only [Mem.update_of_ne]; exact fk z a b
  · rw [hm1]; simp (disch := omega) only [Mem.update_of_ne]; rw [c72]; rfl
  · rw [hm1]; simp (disch := omega) only [Mem.update_self]
  · rw [fk 51 (by omega) (by omega), hm1]; simp (disch := omega) only [Mem.update_of_ne]; exact e
  · rw [fk 54 (by omega) (by omega), d54]
  · rw [fk z b e', hm1]
    simp (disch := omega) only [Mem.update_of_ne]
    rw [hkm z d a]; simp (disch := omega) only [Mem.update_of_ne]

/-! ## Part D: the addresses of the arrays -/

/-- The additions after the products. -/
def allocTail : Program :=
  seq (addTo 55 69 16) (seq (addTo 56 55 52) (seq (addTo 57 56 52) (seq (addTo 58 57 51)
  (seq (addTo 59 58 76) (seq (addTo 61 59 77) (seq (addTo 60 61 70) (seq (addTo 75 60 78)
  (seq (addTo 62 75 52) (addTo 66 52 1)))))))))

/-- The products, then the addresses. -/
def allocP : Program :=
  seq (mulP 70 52 50) (seq (mulP 65 50 51) (seq (addTo 63 51 1) (seq (addTo 67 65 1)
  (seq (addTo 64 67 1) (seq (mulP 76 70 51) (seq (mulP 77 70 63) (seq (mulP 78 52 64)
  allocTail)))))))

theorem wf_allocP : Wf allocP := by
  unfold allocP
  exact wf_seq (wf_mulP _ _ _) (wf_seq (wf_mulP _ _ _) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_seq (by wf_tac) (wf_seq (wf_mulP _ _ _) (wf_seq (wf_mulP _ _ _) (wf_seq (wf_mulP _ _ _)
    (by unfold allocTail; wf_tac))))))))

/-- The registers `allocP` writes. -/
def allocW : List ℕ := [55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 70, 74, 75, 76, 77, 78]

/-- The step count of `allocP`. -/
def tAlloc (n k : ℕ) : ℕ := 4 * n + 12 * k + 4 * (n * k) + 40

set_option maxHeartbeats 2000000 in
theorem runsTo_allocP {M : Mem} (L : Lay) (h1 : M 1 = 1) (h16 : M 16 = L.Lin) (h50 : M 50 = L.n)
    (h51 : M 51 = L.k) (h52 : M 52 = L.N) (h53 : M 53 = L.R0) (h54 : M 54 = L.RW)
    (h69 : M 69 = L.F) :
    RunsTo allocP (fun m => m = M)
      (fun m => RegsOK L m ∧ ∀ z, z ∉ allocW → m z = M z) (tAlloc L.n L.k) := by
  unfold allocP tAlloc
  refine RunsTo.mono (T := (L.n * 4 + 3) + ((L.k * 4 + 3) + ((((L.k * 4 + 3) +
    (((L.k + 1) * 4 + 3) + (((L.n * L.k + 2) * 4 + 3) + 10))) + 1) + 1) + 1)) ?_ (by nlinarith)
  refine block_seq (T := L.n * 4 + 3) (T' := (L.k * 4 + 3) + ((((L.k * 4 + 3) +
    (((L.k + 1) * 4 + 3) + (((L.n * L.k + 2) * 4 + 3) + 10))) + 1) + 1) + 1)
    ((runsTo_mulP (x := 70) (a := 52) (b := 50) (by omega) (by omega) (by omega)
    (by omega) (by omega) h1).mono (by rw [h50])) (fun m1 ⟨e1, k1⟩ => ?_)
  have a1 : m1 1 = 1 := by rw [k1 1 (by omega) (by omega), h1]
  have a50 : m1 50 = L.n := by rw [k1 50 (by omega) (by omega), h50]
  have a51 : m1 51 = L.k := by rw [k1 51 (by omega) (by omega), h51]
  have a52 : m1 52 = L.N := by rw [k1 52 (by omega) (by omega), h52]
  refine block_seq (T := L.k * 4 + 3) (T' := ((((L.k * 4 + 3) +
    (((L.k + 1) * 4 + 3) + (((L.n * L.k + 2) * 4 + 3) + 10))) + 1) + 1) + 1)
    ((runsTo_mulP (x := 65) (a := 50) (b := 51) (by omega) (by omega) (by omega)
    (by omega) (by omega) a1).mono (by rw [a51])) (fun m2 ⟨e2, k2⟩ => ?_)
  have b1 : m2 1 = 1 := by rw [k2 1 (by omega) (by omega), a1]
  have b51 : m2 51 = L.k := by rw [k2 51 (by omega) (by omega), a51]
  have b52 : m2 52 = L.N := by rw [k2 52 (by omega) (by omega), a52]
  have b65 : m2 65 = L.n * L.k := by rw [e2, a50, a51]
  have b70 : m2 70 = L.NN := by rw [k2 70 (by omega) (by omega), e1, h52, h50]; rfl
  refine add_seq' (add_seq' (add_seq' ?_))
  set m3 := ((m2.update 63 (m2 51 + m2 1)).update 67 ((m2.update 63 (m2 51 + m2 1)) 65 +
    (m2.update 63 (m2 51 + m2 1)) 1)).update 64
    (((m2.update 63 (m2 51 + m2 1)).update 67 ((m2.update 63 (m2 51 + m2 1)) 65 +
    (m2.update 63 (m2 51 + m2 1)) 1)) 67 + ((m2.update 63 (m2 51 + m2 1)).update 67
    ((m2.update 63 (m2 51 + m2 1)) 65 + (m2.update 63 (m2 51 + m2 1)) 1)) 1) with hm3
  have c : ∀ z, z ≠ 63 → z ≠ 64 → z ≠ 67 → m3 z = m2 z := fun z a b c => by
    rw [hm3]; simp (disch := omega) only [Mem.update_of_ne]
  have c1 : m3 1 = 1 := by rw [c 1 (by omega) (by omega) (by omega), b1]
  have c63 : m3 63 = L.k + 1 := by
    rw [hm3]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, b51, b1]
  have c67 : m3 67 = L.n * L.k + 1 := by
    rw [hm3]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, b65, b1]
  have c64 : m3 64 = L.n * L.k + 2 := by
    rw [hm3]; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, b65, b1]
  have c51 : m3 51 = L.k := by rw [c 51 (by omega) (by omega) (by omega), b51]
  have c52 : m3 52 = L.N := by rw [c 52 (by omega) (by omega) (by omega), b52]
  have c70 : m3 70 = L.NN := by rw [c 70 (by omega) (by omega) (by omega), b70]
  refine block_seq (T := L.k * 4 + 3) (T' := ((L.k + 1) * 4 + 3)
    + (((L.n * L.k + 2) * 4 + 3) + 10)) ((runsTo_mulP (x := 76) (a := 70) (b := 51) (by omega) (by omega) (by omega)
    (by omega) (by omega) c1).mono (by rw [c51])) (fun m4 ⟨e4, k4⟩ => ?_)
  have d1 : m4 1 = 1 := by rw [k4 1 (by omega) (by omega), c1]
  refine block_seq (T := (L.k + 1) * 4 + 3) (T' := ((L.n * L.k + 2) * 4 + 3) + 10)
    ((runsTo_mulP (x := 77) (a := 70) (b := 63) (by omega) (by omega) (by omega)
    (by omega) (by omega) d1).mono (by rw [k4 63 (by omega) (by omega), c63]))
    (fun m5 ⟨e5, k5⟩ => ?_)
  have f1 : m5 1 = 1 := by rw [k5 1 (by omega) (by omega), d1]
  refine block_seq (T := (L.n * L.k + 2) * 4 + 3) (T' := 10) ((runsTo_mulP (x := 78) (a := 52) (b := 64) (by omega) (by omega) (by omega)
    (by omega) (by omega) f1).mono (by rw [k5 64 (by omega) (by omega),
      k4 64 (by omega) (by omega), c64])) (fun m6 ⟨e6, k6⟩ => ?_)
  -- every register the tail reads, in `m6`
  have g : ∀ z, z ≠ 76 → z ≠ 77 → z ≠ 78 → z ≠ 74 → m6 z = m3 z := fun z a b c d => by
    rw [k6 z c d, k5 z b d, k4 z a d]
  have g76 : m6 76 = L.NN * L.k := by
    rw [k6 76 (by omega) (by omega), k5 76 (by omega) (by omega), e4, c70, c51]
  have g77 : m6 77 = L.NN * (L.k + 1) := by
    rw [k6 77 (by omega) (by omega), e5, k4 70 (by omega) (by omega), c70,
      k4 63 (by omega) (by omega), c63]
  have g78 : m6 78 = L.N * (L.n * L.k + 2) := by
    rw [e6, k5 52 (by omega) (by omega), k4 52 (by omega) (by omega), c52,
      k5 64 (by omega) (by omega), k4 64 (by omega) (by omega), c64]
  have hm2 : ∀ z, z ≠ 65 → z ≠ 70 → z ≠ 74 → m2 z = M z := fun z a b d => by
    rw [k2 z a d, k1 z b d]
  have g69 : m6 69 = L.F := by
    rw [g 69 (by omega) (by omega) (by omega) (by omega), c 69 (by omega) (by omega) (by omega),
      hm2 69 (by omega) (by omega) (by omega), h69]
  have g16 : m6 16 = L.Lin := by
    rw [g 16 (by omega) (by omega) (by omega) (by omega), c 16 (by omega) (by omega) (by omega),
      hm2 16 (by omega) (by omega) (by omega), h16]
  have g1 : m6 1 = 1 := by rw [g 1 (by omega) (by omega) (by omega) (by omega), c1]
  have g50 : m6 50 = L.n := by
    rw [g 50 (by omega) (by omega) (by omega) (by omega), c 50 (by omega) (by omega) (by omega),
      hm2 50 (by omega) (by omega) (by omega), h50]
  have g51 : m6 51 = L.k := by rw [g 51 (by omega) (by omega) (by omega) (by omega), c51]
  have g52 : m6 52 = L.N := by rw [g 52 (by omega) (by omega) (by omega) (by omega), c52]
  have g53 : m6 53 = L.R0 := by
    rw [g 53 (by omega) (by omega) (by omega) (by omega), c 53 (by omega) (by omega) (by omega),
      hm2 53 (by omega) (by omega) (by omega), h53]
  have g54 : m6 54 = L.RW := by
    rw [g 54 (by omega) (by omega) (by omega) (by omega), c 54 (by omega) (by omega) (by omega),
      hm2 54 (by omega) (by omega) (by omega), h54]
  have g63 : m6 63 = L.k + 1 := by rw [g 63 (by omega) (by omega) (by omega) (by omega), c63]
  have g64 : m6 64 = L.n * L.k + 2 := by rw [g 64 (by omega) (by omega) (by omega) (by omega), c64]
  have g65 : m6 65 = L.n * L.k := by
    rw [g 65 (by omega) (by omega) (by omega) (by omega), c 65 (by omega) (by omega) (by omega), b65]
  have g67 : m6 67 = L.n * L.k + 1 := by rw [g 67 (by omega) (by omega) (by omega) (by omega), c67]
  have g70 : m6 70 = L.NN := by rw [g 70 (by omega) (by omega) (by omega) (by omega), c70]
  have gM : ∀ z, z ∉ allocW → m6 z = M z := fun z hz => by
    simp only [allocW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [g z (by omega) (by omega) (by omega) (by omega), c z (by omega) (by omega) (by omega),
      hm2 z (by omega) (by omega) (by omega)]
  unfold allocTail
  rt
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, fun z hz => ?_⟩ <;>
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, g1, g16, g50, g51, g52, g53,
      g54, g63, g64, g65, g67, g69, g70, g76, g77, g78]
  all_goals try (simp only [Lay.IX, Lay.C, Lay.T, Lay.Nb, Lay.Rec, Lay.A, Lay.SR, Lay.A2, Lay.Cnt])
  · simp only [allocW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp (disch := omega) only [Mem.update_of_ne]
    exact gM z (by simp [allocW]; omega)

end WLFast

end Algo
