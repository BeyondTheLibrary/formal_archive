/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

§5.4.2: the trivial bound `O(k²n^{2k+1})` for `k`-ary WL refinement.  The rounds with early
stopping, the output, and the whole program.
-/
import Workspace.Algo.WLFastRound5

/-!
# The fast `k`-WL program: rounds with early stopping and the output

The program repeats the round (`Algo.WLFast.roundP`) while the flag (register `68`) is nonzero,
that is, until a round changes no color.  A counter (register `79`) counts the rounds; the proof
uses it to bound their number by `N + 1` (`Algo.WLFast.exists_fix_le`).  Then it writes the
colors `C[IX[r]]` into the color cells of the input copy (`outP`), which then encodes the stable
coloring (`Algo.WLFast.blk_rawWL_recolor`).

No axiom, no `sorry`.
-/

namespace Algo

namespace WLFast

open RAM RAM.Exact

section Main

variable {n k : ℕ} {p q : RawWL} {L : Lay}

/-- A register outside the persistent ones may change between rounds. -/
theorem RoundI.update_reg {m : Mem} (h : RoundI n k p L q m) {z : ℕ} (hz : z < 100)
    (hzp : z ∉ persist) (v : ℕ) : RoundI n k p L q (m.update z v) := by
  obtain ⟨hb, hIX, hNb, hC⟩ := h
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  refine ⟨⟨hb.wf, hb.hn, hb.hk, hb.hN, hb.hLin, hb.hF, hb.k1,
    hb.regs.congr (fun z' hz' => Mem.update_of_ne _ _ (fun h => hzp (h ▸ hz'))),
    hb.blk.update (Or.inl (by omega))⟩, hIX.update (Or.inl (by omega)),
    hNb.update (Or.inl (by omega)), fun r hr => ?_⟩
  rw [Mem.update_of_ne _ _ (by omega)]; exact hC r hr

theorem qok_iter (hwf : RawWL.WF n k p) (j : ℕ) : QOK n k p (rawWLStep^[j] p) :=
  ⟨wf_rawWLIter hwf j, iter_fst p j, iter_keys p j⟩

/-- A fixed iterate is the stable coloring. -/
theorem stable_eq_of_fixed (hwf : RawWL.WF n k p) {j : ℕ}
    (hj : rawWLStep (rawWLStep^[j] p) = rawWLStep^[j] p) : rawWLStable p = rawWLStep^[j] p := by
  obtain ⟨J, hJ, hfix⟩ := exists_fix_le hwf
  rw [rawWLStable_eq_of_fix hfix (hJ.trans (Nat.le_mul_self _))]
  rcases le_total j J with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, Function.iterate_add_apply, iter_fixed hj d]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm, Function.iterate_add_apply, iter_fixed hfix d]

/-! ## The rounds -/

/-- One round, then the round counter. -/
def loopP : Program := seq roundP (addTo 79 79 1)

theorem wf_loopP : Wf loopP := wf_seq wf_roundP (by wf_tac)

theorem runsTo_loopP {m0 : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) (hN : 0 < L.N) :
    RunsTo loopP (fun m => m = m0)
      (fun m => RoundI n k p L (rawWLStep q) m ∧ (m 68 = 0 ↔ rawWLStep q = q) ∧
        m 79 = m0 79 + 1) (tRound L.N L.n L.k + 1) := by
  have hb := h0.1
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  unfold loopP
  refine block_seq (runsTo_roundP h0 hq hN) (fun m ⟨h1, h2, h3⟩ => add_last' ?_)
  have c1 : m 1 = 1 := h1.1.regs.r1
  have c79 : m 79 = m0 79 := h3 79 (by rw [mem_rW]; omega) (by omega)
  refine ⟨h1.update_reg (by omega) (by decide) _, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega)]; exact h2
  · rw [Mem.update_self, c1, c79]

/-- **The rounds with early stopping.**  From the memory of the input coloring, the loop stops
at the memory of a fixed iterate, after at most `N + 1` rounds. -/
theorem runsTo_rounds {M : Mem} (h0 : RoundI n k p L p M) (hN : 0 < L.N) (h68 : M 68 ≠ 0)
    (h79 : M 79 = 0) :
    ∃ t ≤ (L.N + 1) * (tRound L.N L.n L.k + 1 + 2) + 1,
      RunsTo (whileNz 68 loopP) (fun m => m = M) (fun m => ∃ j, RoundI n k p L (rawWLStep^[j] p) m ∧
        rawWLStep (rawWLStep^[j] p) = rawWLStep^[j] p) t := by
  have hb := h0.1
  obtain ⟨J, hJ, hfix⟩ := exists_fix_le hb.wf
  set T := tRound L.N L.n L.k + 1 with hT
  let inv : Mem → Prop := fun m => ∃ j, m 79 = j ∧ j ≤ J + 1 ∧
    RoundI n k p L (rawWLStep^[j] p) m ∧ (m 68 ≠ 0 → j ≤ J) ∧
    (m 68 = 0 → rawWLStep (rawWLStep^[j] p) = rawWLStep^[j] p)
  have hfixJ : ∀ j, J ≤ j → rawWLStep (rawWLStep^[j] p) = rawWLStep^[j] p := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm, Function.iterate_add_apply, iter_fixed hfix d]
    exact hfix
  obtain ⟨t, ht⟩ := runsTo_whileNz_amortX (i := 68) wf_loopP inv
    (fun m => (J + 1 - m 79) * (T + 2)) (fun m ⟨j, e79, hjJ, hR, hne, _⟩ hm => by
      have hjJ' := hne hm
      refine ⟨T, (runsTo_loopP hR (qok_iter hb.wf j) hN).weaken
        (fun m' ⟨hR', hfl, e79'⟩ => ⟨⟨j + 1, by rw [e79', e79], by omega, ?_, fun hne' => ?_,
          fun hz' => ?_⟩, ?_⟩)⟩
      · rw [Function.iterate_succ_apply']; exact hR'
      · by_contra hc
        exact hne' (hfl.2 (hfixJ j (by omega)))
      · rw [Function.iterate_succ_apply', hfl.1 hz']; exact hfl.1 hz'
      · show (J + 1 - m' 79) * (T + 2) + T + 2 ≤ (J + 1 - m 79) * (T + 2)
        rw [e79', e79]
        have : J + 1 - j = (J + 1 - (j + 1)) + 1 := by omega
        rw [this, Nat.add_mul, one_mul]; omega) M
    ⟨0, h79, by omega, h0, fun _ => Nat.zero_le _, fun h => absurd h h68⟩
  obtain ⟨M', ⟨⟨j, _, _, hR, _, hz⟩, h0', hΦ⟩, hrun⟩ := ht.exact
  have hJN : J ≤ L.N := by rw [hb.hN]; exact hJ
  refine ⟨t, ?_, hrun.weaken (fun m hm => by subst hm; exact ⟨j, hR, hz h0'⟩)⟩
  rw [h79] at hΦ
  have : (J + 1) * (T + 2) ≤ (L.N + 1) * (T + 2) := Nat.mul_le_mul_right _ (by omega)
  simp only [Nat.sub_zero] at hΦ
  omega

/-! ## The output -/

/-- One row: the color cell of row `r` of the input copy gets `C[IX[r]]`. -/
def outBody : Program :=
  seq (loadTo 94 87) (seq (addTo 87 87 1) (seq (addTo 95 56 94) (seq (loadTo 94 95)
  (seq (storeTo 86 94) (seq (addTo 86 86 54) (subTo 92 92 1))))))

/-- **The output**: the colors into the color cells of the input copy. -/
def outP : Program :=
  seq (addTo 86 53 54) (seq (subTo 86 86 1) (seq (copyTo 87 55) (seq (copyTo 92 52)
  (whileNz 92 outBody))))

theorem wf_outBody : Wf outBody := by unfold outBody; wf_tac

theorem wf_outP : Wf outP := by
  unfold outP
  exact wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac) (wf_seq (by wf_tac)
    (wf_whileNz wf_outBody))))

/-- The output after `r` rows. -/
def OutI (L : Lay) (p q : RawWL) (m0 : Mem) (r : ℕ) (m : Mem) : Prop :=
  r ≤ L.N ∧ m 86 = L.R0 + r * L.RW + (2 * L.k + 3) ∧ m 87 = L.IX + r ∧ m 92 = L.N - r ∧
    (∀ r' < r, m (L.R0 + r' * L.RW + (2 * L.k + 3)) = tblGet (q.2, tup p r')) ∧
    ∀ z, z ∉ rW → (∀ r' < r, z ≠ L.R0 + r' * L.RW + (2 * L.k + 3)) → m z = m0 z

theorem runsTo_outBody {m0 m : Mem} (h0 : RoundI n k p L q m0) {r : ℕ} (hr : r < L.N)
    (hI : OutI L p q m0 r m) : RunsTo outBody (fun m' => m' = m) (OutI L p q m0 (r + 1)) 7 := by
  obtain ⟨-, e86, e87, e92, hC, hK⟩ := hI
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hrp : r < p.2.length := by rw [← hb.hN]; exact hr
  have hidx : idxOf L.n (tup p r) < L.N := by rw [hb.hN]; exact hb.idxL_lt hrp
  have hRW : 0 < L.RW := by omega
  -- the color cells are below `IX`
  have hcc : ∀ r' < L.N, L.R0 + r' * L.RW + (2 * L.k + 3) < L.IX := fun r' hr' =>
    hb.row_lt (by rw [← hb.hN]; exact hr') (by omega)
  have hlow : ∀ z, L.IX ≤ z → z ∉ rW → m z = m0 z := fun z h1 h3 =>
    hK z h3 (fun r' hr' => by have := hcc r' (by omega); omega)
  have c1 : m 1 = 1 := hK 1 (by rw [mem_rW]; omega) (fun r' _ => by omega) ▸ hR.r1
  have c56 : m 56 = L.C := hK 56 (by rw [mem_rW]; omega) (fun r' _ => by omega) ▸ hR.r56
  have c54 : m 54 = L.RW := hK 54 (by rw [mem_rW]; omega) (fun r' _ => by omega) ▸ hR.r54
  have cIX : m (L.IX + r) = idxOf L.n (tup p r) := by
    rw [hlow _ (by omega) (by rw [mem_rW]; omega), h0.ix hr]
  have cC : m (L.C + idxOf L.n (tup p r)) = tblGet (q.2, tup p r) := by
    rw [hlow _ (by omega) (by rw [mem_rW]; omega), h0.2.2.2 r hr]
  have hcr := hcc r hr
  unfold outBody
  rt
  unfold OutI
  simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, e86, e87, e92, cIX, c56, cC, c1,
    c54]
  refine ⟨by omega, by ring, by wl_ar, by wl_ar, fun r' hr' => ?_, fun z hz hne => ?_⟩
  · by_cases h : r' = r
    · subst h; simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]
    · have hlt : r' < r := by omega
      have : r' * L.RW < r * L.RW := Nat.mul_lt_mul_of_pos_right hlt hRW
      have := hcc r' (by omega)
      simp (disch := omega) only [Mem.update_of_ne]
      exact hC r' hlt
  · rw [mem_rW] at hz
    have h1 := hne r (by omega)
    simp (disch := omega) only [Mem.update_of_ne]
    exact hK z (by rw [mem_rW]; omega) (fun r' hr' => hne r' (by omega))

/-- The step count of the output. -/
def tOut (N : ℕ) : ℕ := (N * (7 + 2) + 1) + 1 + 1 + 1 + 1

/-- **The output.**  Afterwards the input copy encodes the coloring `q` of the memory. -/
theorem runsTo_outP {m0 : Mem} (h0 : RoundI n k p L q m0) (hq : QOK n k p q) :
    RunsTo outP (fun m => m = m0) (fun m => Blk m L.F (Enc.encode q) ∧ RegsOK L m)
      (tOut L.N) := by
  have hb := h0.1
  have hR := hb.regs
  have hF := hb.hF
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := L.facts
  have hcc : ∀ r' < L.N, L.R0 + r' * L.RW + (2 * L.k + 3) < L.IX := fun r' hr' =>
    hb.row_lt (by rw [← hb.hN]; exact hr') (by omega)
  unfold outP tOut
  refine add_seq' (sub_seq' (copy_seq' (copy_seq' ?_)))
  refine (runsTo_countLoop (c := 92) wf_outBody (OutI L p q m0) L.N 7
    (fun r m h => ⟨h.2.2.2.1, h.1⟩) (fun r m hr hI => runsTo_outBody h0 hr hI) _ ?_).weaken ?_
  · unfold OutI
    simp (disch := omega) only [Mem.update_self, Mem.update_of_ne, hR.r53, hR.r54, hR.r1, hR.r55,
      hR.r52]
    refine ⟨by omega, by omega, by simp, by simp, fun r' hr' => absurd hr' (Nat.not_lt_zero _),
      fun z hz _ => ?_⟩
    rw [mem_rW] at hz
    simp (disch := omega) only [Mem.update_of_ne]
  · rintro m ⟨-, -, -, -, hC, hK⟩
    have hql : q.2.length = p.2.length := hq.length
    have hcol : ∀ r (hr : r < p.2.length),
        colCell L.F p.1.length k r = L.R0 + r * L.RW + (2 * L.k + 3) := fun r hr => by
      unfold colCell Lay.R0 Lay.RW
      rw [length_dom hb.wf, hb.hn, hb.hk]
    refine ⟨blk_rawWL_recolor hb.keyLen hb.blk hq.fst hql (fun r hr => ?_) (fun r hr => ?_)
      (fun z hz1 hz2 hne => ?_), hR.congr (fun z hz => ?_)⟩
    · rw [hq.key (by rw [hql]; exact hr), hb.tup_eq hr]
    · have hrq : r < q.2.length := by rw [hql]; exact hr
      rw [hcol r hr, hC r (by rw [hb.hN]; exact hr), ← hq.key hrq,
        tblGet_of_mem hq.wf (List.getElem_mem hrq)]
    · exact hK z (by rw [mem_rW]; omega) (fun r' hr' => by
        rw [← hcol r' (by rw [← hb.hN]; exact hr')]; exact hne r' (by rw [← hb.hN]; exact hr'))
    · have := persist_ok z hz
      exact hK z (by rw [mem_rW]; omega) (fun r' hr' => by have := hcc r' hr'; omega)

/-! ## The whole program -/

/-- The length of the encoding does not change along the rounds. -/
theorem length_encode_iter (hwf : RawWL.WF n k p) (j : ℕ) :
    (Enc.encode (rawWLStep^[j] p)).length = (Enc.encode p).length := by
  have hk : ∀ q ∈ p.2, q.1.length = k := fun q hq =>
    ((hwf.keyMem q.1).1 (List.mem_map_of_mem hq)).1
  have hwf' := wf_rawWLIter hwf j
  have hk' : ∀ q ∈ (rawWLStep^[j] p).2, q.1.length = k := fun q hq =>
    ((hwf'.keyMem q.1).1 (List.mem_map_of_mem hq)).1
  rw [length_encode_rawWL hk, length_encode_rawWL hk', iter_fst, iter_length]

theorem length_encode_stable (hwf : RawWL.WF n k p) :
    (Enc.encode (rawWLStable p)).length = (Enc.encode p).length := by
  rw [rawWLStable_eq_iterate]; exact length_encode_iter hwf _

/-- Copy the input copy back to `17`, where `RAM.Bridge.down` reads the output. -/
def copyBack : Program :=
  seq (copyTo 5 69) (seq (assign 6 17) (seq (copyTo 7 16) (Arrays.copyBlock 5 6 7 8)))

theorem wf_copyBack : Wf copyBack := by
  unfold copyBack Arrays.copyBlock Arrays.copyPre Arrays.copyBody; wf_tac

/-- **The end**: copy back and move the output down. -/
theorem runsTo_finish {m : Mem} {l : List ℕ} {F : ℕ} (hF : 100 ≤ F) (h16 : m 16 = l.length)
    (h69 : m 69 = F) (hB : Blk m F l) :
    RunsTo (seq copyBack Bridge.down) (fun m' => m' = m) (fun m' => OutputAt m' l)
      ((7 * l.length + 5 + 1 + 1 + 1) + (7 * l.length + 34)) := by
  refine block_seq (mid := fun m' => m' 16 = l.length ∧ ∀ j < l.length, m' (17 + j) = l[j]!)
    ?_ (fun M hM => ?_)
  · unfold copyBack
    refine copy_seq' (assign_seq' (copy_seq' ?_))
    simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, h69, h16]
    have e := Arrays.runsTo_copyBlock 5 6 7 8 (by norm_num) (by norm_num) (by norm_num)
      (((m.update 5 (m 69)).update 6 17).update 7 (((m.update 5 (m 69)).update 6 17) 16))
      (by simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; omega)
      (by simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; omega)
      (Or.inl (by simp (disch := omega) only [Mem.update_of_ne, Mem.update_self]; omega))
    simp (disch := omega) only [Mem.update_of_ne, Mem.update_self, h69, h16] at e
    refine e.weaken (fun m' ⟨hc, hk⟩ => ⟨?_, fun j hj => ?_⟩)
    · rw [hk 16 (by omega) (by simp)]
      simp (disch := omega) only [Mem.update_of_ne]; exact h16
    · rw [hc j hj, hB j hj, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  · obtain ⟨e16, hc⟩ := hM
    refine (Bridge.runsTo_down e16).weaken (fun m' ⟨h0, hi⟩ => ⟨h0, fun i hi' => ?_⟩)
    rw [hi (i + 1) (by omega) (by omega), show 16 + (i + 1) = 17 + i by ring, hc i hi',
      List.getD_eq_getElem _ _ hi', List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rfl

/-- The part of the program after reading `n` and `N (2k + 4)`, run when `N ≠ 0`. -/
def innerP : Program :=
  seq parseK (seq allocP (seq buildP (seq (assign 68 1) (seq (assign 79 0)
  (seq (whileNz 68 loopP) outP)))))

theorem wf_innerP : Wf innerP := by
  unfold innerP
  exact wf_seq wf_parseK (wf_seq wf_allocP (wf_seq wf_buildP (wf_seq (by wf_tac) (wf_seq
    (by wf_tac) (wf_seq (wf_whileNz wf_loopP) wf_outP)))))

/-- **The fast `k`-WL program** (§5.4.2). -/
def wlFastP : Program :=
  seq Bridge.up (seq setupA (seq setupB (seq (ifz 72 innerP []) (seq copyBack Bridge.down))))

/-- The step count of `innerP`. -/
def tInner (n k N : ℕ) : ℕ :=
  (k * 5 + N * 4 + 9) + (tAlloc n k + (tBuild N n k +
    (((((N + 1) * (tRound N n k + 1 + 2) + 1) + tOut N) + 1) + 1)))

/-- The step count of `wlFastP` on an input of length `Lin` with `N` rows. -/
def tWL (n k N Lin : ℕ) : ℕ :=
  (18 * Lin + 78) + ((7 * Lin + 12) + ((n * 5 + 9) + (((if N = 0 then 0 else tInner n k N) + 2) +
    ((7 * Lin + 5 + 1 + 1 + 1) + (7 * Lin + 34)))))

/-- **The fast program computes the stable coloring**, within `tWL` steps. -/
theorem runsTo_wlFastP (hk1 : 1 ≤ k) (hwf : RawWL.WF n k p) :
    RunsTo wlFastP (fun m => m = initMem (Enc.encode p))
      (fun m => OutputAt m (Enc.encode (rawWLStable p)))
      (tWL n k p.2.length (Enc.encode p).length) := by
  set l := Enc.encode p with hl
  set F := l.length + 100 with hFdef
  have hF : 100 ≤ F := by omega
  have hls := length_encode_stable hwf
  unfold wlFastP tWL
  refine block_seq (Bridge.runsTo_up _) (fun M0 hM0 => ?_)
  subst hM0
  refine block_seq (runsTo_setupA l) (fun M1 ⟨a1, a16, a69, aB⟩ => ?_)
  refine block_seq (runsTo_setupB hwf hF a1 a69 aB) (fun M2 ⟨b50, b53, b72, bK⟩ => ?_)
  have b1 : M2 1 = 1 := by rw [bK 1 (by omega) (by omega) (by omega) (by omega), a1]
  have b16 : M2 16 = l.length := by rw [bK 16 (by omega) (by omega) (by omega) (by omega), a16]
  have b69 : M2 69 = F := by rw [bK 69 (by omega) (by omega) (by omega) (by omega), a69]
  have bB : Blk M2 F l := aB.congr (fun z h1 h2 => bK z (by omega) (by omega) (by omega)
    (by omega))
  refine block_seq (mid := fun m => m 16 = (Enc.encode (rawWLStable p)).length ∧ m 69 = F ∧
    Blk m F (Enc.encode (rawWLStable p))) ?_
    (fun M3 ⟨c16, c69, cB⟩ => runsTo_finish hF c16 c69 cB |>.mono (by rw [hls]))
  rcases Nat.eq_zero_or_pos p.2.length with hN0 | hNpos
  · -- no row: the input is already stable
    have hst : rawWLStable p = p := by
      rw [rawWLStable_eq_iterate, hN0]; rfl
    rw [if_pos hN0]
    refine ifz_eq' (by rw [b72, hN0, zero_mul]) (runsTo_nil (fun m hm => ?_)) wf_innerP
    subst hm
    rw [hst]
    exact ⟨b16, b69, bB⟩
  · have hk : 2 * k + 4 ≠ 0 := by omega
    rw [if_neg (by omega)]
    refine ifz_ne' (by rw [b72]; exact Nat.mul_ne_zero (by omega) hk) ?_ Algo.ExplLinear.wf_nil
    let L : Lay := ⟨F, l.length, n, k, p.2.length⟩
    unfold innerP tInner
    refine block_seq (runsTo_parseK hwf hF hNpos b1 bB b53 b72) (fun M3 ⟨c51, c54, c52, cK⟩ => ?_)
    have g3 : ∀ z, z ≠ 51 → z ≠ 52 → z ≠ 54 → z ≠ 71 → z ≠ 72 → z ≠ 73 → M3 z = M2 z := cK
    have d1 : M3 1 = 1 := by rw [g3 1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), b1]
    have d16 : M3 16 = L.Lin := by rw [g3 16 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), b16]
    have d50 : M3 50 = L.n := by rw [g3 50 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), b50]
    have d53 : M3 53 = L.R0 := by
      rw [g3 53 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b53]
      simp only [Lay.R0, L]
    have d54 : M3 54 = L.RW := by rw [c54]; simp only [Lay.RW, L]
    have d69 : M3 69 = L.F := by rw [g3 69 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), b69]
    refine block_seq (runsTo_allocP L d1 d16 d50 c51 c52 d53 d54 d69) (fun M4 ⟨hRg, dK⟩ => ?_)
    have hb : BaseOK n k p L M4 := ⟨hwf, rfl, rfl, rfl, rfl, hF, hk1, hRg, bB.congr
      (fun z h1 h2 => by
        rw [dK z (by simp [allocW]; omega), g3 z (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)])⟩
    refine block_seq (runsTo_buildP hb) (fun M5 ⟨⟨eIX, eC, eNb⟩, hBF⟩ => ?_)
    have h5 : RoundI n k p L p M5 := by
      refine ⟨hb.congr (fun z h1 h2 => hBF z (fun h => h2 (mem_rW.2 (by
        rw [mem_bW] at h; omega))) (Or.inl h1)), eIX, eNb, fun r hr => ?_⟩
      have hrp : r < p.2.length := hr
      rw [eC r hr, hb.colOf_eq hrp, hb.tup_eq hrp, tblGet_of_mem hwf (List.getElem_mem hrp)]
    refine assign_seq' (assign_seq' ?_)
    have h6 := (h5.update_reg (z := 68) (by omega) (by decide) 1).update_reg (z := 79) (by omega)
      (by decide) 0
    obtain ⟨t, ht, hrun⟩ := runsTo_rounds h6 hNpos
      (by rw [Mem.update_of_ne _ _ (by omega), Mem.update_self]; omega) (by rw [Mem.update_self])
    refine block_seq (hrun.mono ht) (fun M7 ⟨j, hR7, hfix⟩ => ?_)
    refine (runsTo_outP hR7 (qok_iter hwf j)).weaken (fun m ⟨hB8, hR8⟩ => ?_)
    rw [stable_eq_of_fixed hwf hfix, length_encode_iter hwf j]
    exact ⟨hR8.r16, hR8.r69, hB8⟩

end Main

end WLFast

end Algo
