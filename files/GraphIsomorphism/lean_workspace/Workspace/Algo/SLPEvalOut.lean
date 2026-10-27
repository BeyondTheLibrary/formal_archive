import Workspace.Algo.SLPEvalLoop

/-!
# The straight-line-program evaluator: the answer

The last phase of `Algo.SLPRAM.slpEvalProg`: a second pass over the program pushes the marked
elements as framed blocks, then the kernel generators are copied from the input, then the
representative, and the two length fields of the answer are filled in.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Algo
namespace SLPRAM

open RAM Layout LX

theorem encList_append {α : Type*} (f : α → List ℕ) (l l' : List α) :
    encList f (l ++ l') = encList f l ++ encList f l' := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [encList, ih]

/-- The marked elements among the first `i`. -/
def Inp.marked (I : Inp) (i : ℕ) : List RawPerm :=
  ((I.prog.zip I.V).take i).filterMap (fun p => if p.1.2.2.2 = 0 then none else some p.2)

/-- Their words. -/
def Inp.encM (I : Inp) (i : ℕ) : List ℕ := encList Enc.encode (I.marked i)

theorem Inp.marked_succ (I : Inp) {i : ℕ} (hi : i < I.prog.length) :
    I.marked (i + 1) = I.marked i ++
      (if I.prog[i].2.2.2 = 0 then [] else [I.V.getD i []]) := by
  rw [Inp.marked, Inp.marked, slpMarked_take_succ _ _ _ hi, I.getD_V_of_lt hi]

theorem Inp.encM_succ_zero (I : Inp) {i : ℕ} (hi : i < I.prog.length)
    (hf : I.prog[i].2.2.2 = 0) : I.encM (i + 1) = I.encM i := by
  rw [Inp.encM, Inp.encM, I.marked_succ hi, if_pos hf, List.append_nil]

theorem Inp.encM_succ_ne (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ}
    (hi : i < I.prog.length) (hf : I.prog[i].2.2.2 ≠ 0) :
    I.encM (i + 1) = I.encM i ++ ([2 * I.n] ++ encNats (I.V.getD i [])) := by
  rw [Inp.encM, Inp.encM, I.marked_succ hi, if_neg hf, encList_append]
  simp only [encList, frame, encode_listNat, length_encNats, I.length_V hv hi, List.append_nil]
  rfl

theorem Inp.encM_zero (I : Inp) : I.encM 0 = [] := by
  simp [Inp.encM, Inp.marked]; rfl

theorem Inp.marked_all (I : Inp) : I.marked I.prog.length = slpMarked I.S I.prog := by
  rw [Inp.marked, List.take_of_length_le (by simp), slpMarked]

/-! ## The second pass -/

/-- The invariant of the second pass after `i` instructions, above the list `Lev` left by the
evaluation. -/
def FInv (I : Inp) (Lev : List ℕ) (m : Mem) : Prop :=
  ∃ i w, m = memAt 16 w (Lev ++ [0, 1, 0] ++ I.encM i) ∧ i ≤ I.prog.length ∧
    w 8 = 16 + (Lev ++ [0, 1, 0] ++ I.encM i).length ∧
    w 9 = 16 + (10 + I.LS + I.LK) + 11 * i ∧ w 11 = 16 + Lev.length ∧ w 12 = 17 + I.Ez + i ∧
    w 13 = 2 * I.n ∧ w 14 = (I.encM i).length ∧ w 15 = I.LP - 11 * i

/-- The state after the optional push of instruction `i`. -/
def FMid (I : Inp) (Lev : List ℕ) (i : ℕ) (m : Mem) : Prop :=
  ∃ w, m = memAt 16 w (Lev ++ [0, 1, 0] ++ I.encM (i + 1)) ∧
    w 8 = 16 + (Lev ++ [0, 1, 0] ++ I.encM (i + 1)).length ∧
    w 9 = 16 + (10 + I.LS + I.LK) + 11 * i ∧ w 11 = 16 + Lev.length ∧ w 12 = 17 + I.Ez + i ∧
    w 13 = 2 * I.n ∧ w 14 = (I.encM (i + 1)).length ∧ w 15 = I.LP - 11 * i

theorem pushSlot_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {tbl dat : List ℕ}
    (hg : EGood I I.prog.length tbl dat) {i : ℕ} (hi : i < I.prog.length)
    (hf : I.prog[i].2.2.2 ≠ 0) {w : Mem}
    (h8 : w 8 = 16 + (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM i).length)
    (h9 : w 9 = 16 + (10 + I.LS + I.LK) + 11 * i) (h11 : w 11 = 16 + (I.L0 ++ tbl ++ dat).length)
    (h12 : w 12 = 17 + I.Ez + i) (h13 : w 13 = 2 * I.n) (h14 : w 14 = (I.encM i).length)
    (h15 : w 15 = I.LP - 11 * i) :
    RunsTo pushSlot (St w (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM i))
      (FMid I (I.L0 ++ tbl ++ dat) i) (14 * I.n + 15) := by
  obtain ⟨p, hp, sp, -⟩ := hg.2.2.1 i hi
  have htl := hg.1
  have hLP := I.LP_eq
  have hlen := I.length_L0
  have hVn := I.length_V hv hi
  set Lev := I.L0 ++ tbl ++ dat with hLev
  set L := Lev ++ [0, 1, 0] ++ I.encM i with hL
  have hsp : p + 2 * I.n ≤ Lev.length := by have := sp.1; rw [hVn] at this; exact this
  have hLlen : L.length = Lev.length + 3 + (I.encM i).length := by rw [hL]; simp; omega
  have hLevlen : Lev.length = I.L0.length + tbl.length + dat.length := by rw [hLev]; simp; omega
  have hread : (L ++ [2 * I.n]).getD (I.L0.length + i) 0 = 16 + p := by
    rw [getD_prefix (by rw [hLlen, hLevlen]; omega), hL, List.append_assoc,
      getD_prefix (by rw [hLevlen]; omega), hLev, getD_tbl _ _ _ (by omega), hp]
  have hseg : ((L ++ [2 * I.n]).drop p).take (2 * I.n) = encNats (I.V.getD i []) := by
    have := sp.2
    rw [hVn] at this
    show seg (L ++ [2 * I.n]) p (2 * I.n) = _
    rw [seg_append_left _ _ (by rw [hLlen]; omega), hL, List.append_assoc,
      seg_append_left _ _ hsp, this]
  have hlist : L ++ [2 * I.n] ++ ((L ++ [2 * I.n]).drop p).take (2 * I.n) =
      Lev ++ [0, 1, 0] ++ I.encM (i + 1) := by
    rw [hseg, I.encM_succ_ne hv hi hf, hL]; simp
  have hlen1 : (I.encM (i + 1)).length = (I.encM i).length + 2 * I.n + 1 := by
    rw [I.encM_succ_ne hv hi hf, List.length_append, List.length_append, length_encNats, hVn]
    simp; omega
  have hcont : ∀ w' : Mem, w' 8 = 16 + L.length + 1 + 2 * I.n → w' 9 = w 9 → w' 11 = w 11 →
      w' 12 = w 12 → w' 13 = w 13 → w' 14 = w 14 → w' 15 = w 15 →
      RunsTo (seq (addTo 14 14 13) (seq (assign 3 1) (addTo 14 14 3)))
        (St w' (L ++ [2 * I.n] ++ ((L ++ [2 * I.n]).drop p).take (2 * I.n)))
        (FMid I Lev i) 3 := by
    intro w' h8' f9 f11 f12 f13 f14 f15
    have h2 := ex_addV 14 14 13 (w := w') (L := L ++ [2 * I.n] ++
        ((L ++ [2 * I.n]).drop p).take (2 * I.n)) (a := (I.encM i).length) (b := 2 * I.n)
        (by rw [f14, h14]) (by rw [f13, h13]) ⨾
      ex_assign 3 1 ⨾
      ex_addV 14 14 3 (a := (I.encM i).length + 2 * I.n) (b := 1) (by rsimp) (by rsimp)
    refine (h2.weaken (fun m hm => ⟨_, hm.to hlist, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
      (by norm_num)
    · rw [← hlist]; rsimp [h8', hLlen]
    · rsimp [f9, h9]
    · rsimp [f11, h11]
    · rsimp [f12, h12]
    · rsimp [f13, h13]
    · rsimp [hlen1]
    · rsimp [f15, h15]
  have hL1 : (L ++ [2 * I.n]).length = L.length + 1 := by simp
  have h := ex_pushV 13 (w := w) (L := L) (v := 2 * I.n) h13 h8 ⨾
    ex_loadV 0 12 (i := I.L0.length + i) (v := 16 + p) (by rsimp [h12, hlen]) hread ⨾
    ex_copyV 2 13 (a := 2 * I.n) (by rsimp [h13]) ⨾
    ex_pushBlock_then (p := p) (c := 2 * I.n) (by rsimp [hL1]) (by rsimp) (by rsimp)
      (by rw [hL1, hLlen]; omega) (by wf_tac)
      (fun w' hfr h8' => hcont w' (by rw [h8', hL1]; omega)
        (by rw [hfr 9 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 11 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 12 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 13 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 14 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 15 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp))
  exact h.mono (by omega)

theorem flagBody_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {tbl dat : List ℕ}
    (hg : EGood I I.prog.length tbl dat) (N : ℕ) :
    RunsTo flagBody (fun m => FInv I (I.L0 ++ tbl ++ dat) m ∧ m 15 ≠ 0 ∧ m 15 = N)
      (fun m => FInv I (I.L0 ++ tbl ++ dat) m ∧ m 15 < N) (14 * I.n + 32) := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨⟨i, w, hm', hile, h8, h9, h11, h12, h13, h14, h15⟩, hne, hN⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have hLP := I.LP_eq
  have hlen' := I.length_L0'
  have h15m : m 15 = w 15 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hi : i < I.prog.length := by rw [h15m, h15] at hne; omega
  have hNi : N = I.LP - 11 * i := by rw [← hN, h15m, h15]
  set Lev := I.L0 ++ tbl ++ dat with hLev
  have hLevlen : Lev.length = I.L0.length + tbl.length + dat.length := by rw [hLev]; simp; omega
  have hflag : (Lev ++ [0, 1, 0] ++ I.encM i).getD (10 + I.LS + I.LK + 11 * i + 10) 0 =
      I.prog[i].2.2.2 := by
    rw [getD_prefix (by simp; omega), getD_prefix (by omega), hLev,
      getD_ins I tbl dat hi (by norm_num)]
    rfl
  have htail : RunsTo (seq (assign 0 11) <| seq (addTo 9 9 0) <| seq (subTo 15 15 0) <|
      seq (assign 0 1) (addTo 12 12 0)) (FMid I Lev i)
      (fun m => FInv I Lev m ∧ m 15 < N) 5 := by
    refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
    obtain ⟨w', hm'', h8', h9', h11', h12', h13', h14', h15'⟩ := hm
    refine ⟨w', _, hm'', ?_⟩
    have h := ex_assign 0 11 (w := w') (L := Lev ++ [0, 1, 0] ++ I.encM (i + 1)) ⨾
      ex_addV 9 9 0 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 11) (by rsimp [h9'])
        (by rsimp) ⨾
      ex_subV 15 15 0 (a := I.LP - 11 * i) (b := 11) (by rsimp [h15']) (by rsimp) ⨾
      ex_assign 0 1 ⨾
      ex_addV 12 12 0 (a := 17 + I.Ez + i) (b := 1) (by rsimp [h12']) (by rsimp)
    refine (h.weaken (fun m hm => ⟨⟨i + 1, _, hm.to rfl, by omega, by rsimp [h8'], by rsimp,
      by rsimp [h11'], by rsimp, by rsimp [h13'], by rsimp [h14'], by rsimp⟩, ?_⟩)).mono
      (by norm_num)
    rw [hm, memAt_of_lt _ _ (by norm_num : (15:ℕ) < 16), hNi]; rsimp
  have hbr : ∀ W : Mem, W 0 = I.prog[i].2.2.2 →
      W 8 = 16 + (Lev ++ [0, 1, 0] ++ I.encM i).length →
      W 9 = 16 + (10 + I.LS + I.LK) + 11 * i → W 11 = 16 + Lev.length →
      W 12 = 17 + I.Ez + i → W 13 = 2 * I.n → W 14 = (I.encM i).length →
      W 15 = I.LP - 11 * i →
      RunsTo (ifz 0 pushSlot []) (St W (Lev ++ [0, 1, 0] ++ I.encM i)) (FMid I Lev i)
        (14 * I.n + 17) := by
    intro W g0 g8 g9 g11 g12 g13 g14 g15
    by_cases hf : I.prog[i].2.2.2 = 0
    · refine (ex_ifz_eq (by norm_num) (by rw [g0, hf])
        (runsTo_nil (fun m hm => ⟨W, hm.to (by rw [I.encM_succ_zero hi hf]),
          by rw [g8, I.encM_succ_zero hi hf], g9, g11, g12, g13,
          by rw [g14, I.encM_succ_zero hi hf], g15⟩)) (by wf_tac)).mono (by omega)
    · exact (ex_ifz_ne (by norm_num) (by rw [g0]; exact hf)
        (pushSlot_spec I hv hg hi hf g8 g9 g11 g12 g13 g14 g15) (by wf_tac)).mono (by omega)
  have h := ex_assign 0 10 (w := w) (L := Lev ++ [0, 1, 0] ++ I.encM i) ⨾
    ex_addV 0 9 0 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 10) (by rsimp [h9])
      (by rsimp) ⨾
    ex_loadV 0 0 (i := 10 + I.LS + I.LK + 11 * i + 10) (v := I.prog[i].2.2.2) (by rsimp) hflag ⨾
    hbr _ (by rsimp) (by rsimp [h8]) (by rsimp [h9]) (by rsimp [h11]) (by rsimp [h12])
      (by rsimp [h13]) (by rsimp [h14]) (by rsimp [h15]) ⨾
    htail
  exact h.mono (by omega)

/-- The state after the second pass. -/
def FDone (I : Inp) (m : Mem) : Prop :=
  ∃ tbl dat, EGood I I.prog.length tbl dat ∧ ∃ w,
    m = memAt 16 w (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM I.prog.length) ∧
    w 9 = 16 + (10 + I.LS + I.LK) + 11 * I.prog.length ∧
    w 11 = 16 + (I.L0 ++ tbl ++ dat).length ∧
    w 8 = 16 + (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM I.prog.length).length ∧
    w 13 = 2 * I.n ∧ w 14 = (I.encM I.prog.length).length

/-- **The head of the answer and the second pass.** -/
theorem outHead_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) :
    RunsTo outHead (EDone I) (FDone I) (28 + (I.LP * (14 * I.n + 34) + 1)) := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨w, tbl, dat, hm', hg, h8, h9, h11, h12, h13, h14, h15⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have hLP := I.LP_eq
  have hlen' := I.length_L0'
  have hlen := I.length_L0
  set Lev := I.L0 ++ tbl ++ dat with hLev
  have hLevlen : Lev.length = I.L0.length + tbl.length + dat.length := by rw [hLev]; simp; omega
  have hloop := runsTo_whileNz (i := 15) (inv := FInv I Lev) (μ := fun m => m 15) (N := I.LP)
    (flagBody_spec I hv hg) (fun m hm => by
      obtain ⟨i, w, hm', -, -, -, -, -, -, -, h15⟩ := hm
      show m 15 ≤ _
      rw [hm', memAt_of_lt _ _ (by norm_num), h15]; omega)
  have rd : ∀ k, k < I.L0.length → (Lev ++ [0] ++ [1] ++ [0]).getD k 0 = I.L0.getD k 0 := by
    intro k hk
    rw [getD_prefix (by simp; omega), getD_prefix (by simp; omega), getD_prefix (by omega),
      hLev, List.append_assoc, getD_prefix hk]
  have h := ex_copyV 11 8 (w := w) (L := Lev) (a := 16 + Lev.length) h8 ⨾
    ex_assign 0 0 ⨾ ex_pushV 0 (v := 0) (by rsimp) (by rsimp) ⨾
    ex_assign 0 1 ⨾ ex_pushV 0 (v := 1) (by rsimp) (by rsimp) ⨾
    ex_assign 0 0 ⨾ ex_pushV 0 (v := 0) (by rsimp) (by rsimp) ⨾
    ex_loadFixV 1 5 (v := I.LS) (by rw [rd 5 (by omega), I.getD_LS]) ⨾
    ex_assign 0 22 ⨾
    ex_addV 1 1 0 (a := I.LS) (b := 22) (by rsimp) (by rsimp) ⨾
    ex_loadV 2 1 (i := 6 + I.LS) (v := I.LK) (by rsimp) (by rw [rd _ (by omega), I.getD_LK]) ⨾
    ex_addV 5 1 2 (a := I.LS + 22) (b := I.LK) (by rsimp) (by rsimp) ⨾
    ex_assign 0 2 ⨾
    ex_addV 5 5 0 (a := I.LS + 22 + I.LK) (b := 2) (by rsimp) (by rsimp) ⨾
    ex_assign 0 2 ⨾
    ex_addV 9 5 0 (a := I.LS + 22 + I.LK + 2) (b := 2) (by rsimp) (by rsimp) ⨾
    ex_assign 0 1 ⨾
    ex_addV 6 5 0 (a := I.LS + 22 + I.LK + 2) (b := 1) (by rsimp) (by rsimp) ⨾
    ex_loadV 15 6 (i := 9 + I.LS + I.LK) (v := I.LP) (by rsimp)
      (by rw [rd _ (by omega), I.getD_LP]) ⨾
    ex_copyV 12 14 (a := 17 + I.Ez) (by rsimp [h14]) ⨾
    ex_addV 13 13 13 (a := I.n) (b := I.n) (by rsimp [h13]) (by rsimp [h13]) ⨾
    ex_assign 14 0 ⨾
    hloop.strengthen (fun m hm => ⟨0, _, hm.to (by rw [I.encM_zero]; simp), by omega,
      by rsimp [I.encM_zero], by rsimp, by rsimp, by rsimp, by rsimp,
      by rsimp [I.encM_zero], by rsimp⟩)
  refine (h.weaken (fun m hm => ?_)).mono
    (by rw [show 14 * I.n + 32 + 2 = 14 * I.n + 34 by omega]; omega)
  obtain ⟨⟨i, w', hm'', hile, h8', h9', h11', -, h13', h14', h15'⟩, h0⟩ := hm
  have : i = I.prog.length := by
    rw [hm'', memAt_of_lt _ _ (by norm_num), h15'] at h0; omega
  subst this
  exact ⟨tbl, dat, hg, w', hm'', h9', h11', h8', h13', h14'⟩

/-! ## The kernel generators, the representative and the length fields -/

/-- **The two length fields and the final move.** -/
theorem outRest2_spec {w : Mem} {Lev E Kw X : List ℕ} {c : ℕ} (hX : X.length = c)
    (h11 : w 11 = 16 + Lev.length) (h13 : w 13 = c) (h14 : w 14 = E.length)
    (h15 : w 15 = Kw.length) :
    RunsTo outRest2 (St w (Lev ++ [0, 1, 0] ++ E ++ Kw ++ [c] ++ X))
      (fun m => m = memAt 16 (fun _ => 0)
        ([E.length + Kw.length + c + 3, 1, E.length + Kw.length] ++ E ++ Kw ++ [c] ++ X))
      (7 * (E.length + Kw.length + c + 4) + 5 * Lev.length + 43) := by
  set B := [E.length + Kw.length + c + 3, 1, E.length + Kw.length] ++ E ++ Kw ++ [c] ++ X
    with hB
  have hBl : B.length = E.length + Kw.length + c + 4 := by rw [hB]; simp [hX]; omega
  have hL1 : (Lev ++ [0, 1, 0] ++ E ++ Kw ++ [c] ++ X).set (Lev.length + 2)
      (E.length + Kw.length) = Lev ++ ([0, 1, E.length + Kw.length] ++ E ++ Kw ++ [c] ++ X) := by
    simp only [List.append_assoc]
    rw [set_append2 _ _ (by simp)]; rfl
  have hL2 : (Lev ++ ([0, 1, E.length + Kw.length] ++ E ++ Kw ++ [c] ++ X)).set Lev.length
      (E.length + Kw.length + c + 3) = Lev ++ B := by
    rw [← Nat.add_zero Lev.length, set_append2 _ _ (by simp)]; rfl
  have h := ex_addV 1 14 15 (w := w) (L := Lev ++ [0, 1, 0] ++ E ++ Kw ++ [c] ++ X)
      (a := E.length) (b := Kw.length) h14 h15 ⨾
    ex_assign 0 2 ⨾
    ex_addV 0 11 0 (a := 16 + Lev.length) (b := 2) (by rsimp [h11]) (by rsimp) ⨾
    ex_storeV 0 1 (i := Lev.length + 2) (v := E.length + Kw.length) (by rsimp) (by rsimp)
      (by simp) ⨾
    ex_addV 2 1 13 (a := E.length + Kw.length) (b := c) (by rsimp) (by rsimp [h13]) ⨾
    ex_assign 0 3 ⨾
    ex_addV 2 2 0 (a := E.length + Kw.length + c) (b := 3) (by rsimp) (by rsimp) ⨾
    ex_storeV 11 2 (i := Lev.length) (v := E.length + Kw.length + c + 3) (by rsimp [h11])
      (by rsimp) (by simp) ⨾
    ex_assign 0 1 ⨾
    ex_addV 12 2 0 (a := E.length + Kw.length + c + 3) (b := 1) (by rsimp) (by rsimp) ⨾
    ex_finish (L₀ := Lev) (B := B) (by rw [hL1, hL2]) (by rsimp [h11]) (by rsimp [hBl])
  exact h.mono (by rw [hBl]; omega)

/-- **The representative**: element `σ` of the sequence, pushed as a framed block. -/
theorem outRest1_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) (hσ : I.σ < I.prog.length)
    {tbl dat : List ℕ} (hg : EGood I I.prog.length tbl dat) {w : Mem}
    (h8 : w 8 = 16 + (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM I.prog.length ++
      Enc.encode I.K).length)
    (h9 : w 9 = 16 + (10 + I.LS + I.LK) + 11 * I.prog.length)
    (h11 : w 11 = 16 + (I.L0 ++ tbl ++ dat).length) (h13 : w 13 = 2 * I.n)
    (h14 : w 14 = (I.encM I.prog.length).length) (h15 : w 15 = I.LK) :
    RunsTo outRest1 (St w (I.L0 ++ tbl ++ dat ++ [0, 1, 0] ++ I.encM I.prog.length ++
        Enc.encode I.K))
      (fun m => m = memAt 16 (fun _ => 0)
        ([(I.encM I.prog.length).length + I.LK + 2 * I.n + 3, 1,
          (I.encM I.prog.length).length + I.LK] ++ I.encM I.prog.length ++ Enc.encode I.K ++
          [2 * I.n] ++ encNats (I.V.getD I.σ [])))
      (7 * ((I.encM I.prog.length).length + I.LK + 2 * I.n + 4) +
        5 * (I.L0 ++ tbl ++ dat).length + 14 * I.n + 70) := by
  obtain ⟨p, hp, sp, -⟩ := hg.2.2.1 I.σ hσ
  have htl := hg.1
  have hLP := I.LP_eq
  have hlen := I.length_L0
  have hlen' := I.length_L0'
  have hVn := I.length_V hv hσ
  set Lev := I.L0 ++ tbl ++ dat with hLev
  set L := Lev ++ [0, 1, 0] ++ I.encM I.prog.length ++ Enc.encode I.K with hL
  have hsp : p + 2 * I.n ≤ Lev.length := by have := sp.1; rw [hVn] at this; exact this
  have hLevlen : Lev.length = I.L0.length + tbl.length + dat.length := by rw [hLev]; simp; omega
  have hLlen : L.length = Lev.length + 3 + (I.encM I.prog.length).length + I.LK := by
    rw [hL]; simp [Inp.LK]; omega
  have rd : ∀ k, k < I.L0.length → (L ++ [2 * I.n]).getD k 0 = I.L0.getD k 0 := by
    intro k hk
    rw [getD_prefix (by rw [hLlen, hLevlen]; omega), hL, List.append_assoc, List.append_assoc,
      getD_prefix (by rw [hLevlen]; omega), hLev, List.append_assoc, getD_prefix hk]
  have hσr : (L ++ [2 * I.n]).getD (11 + I.LS + I.LK + I.LP) 0 = I.σ := by
    rw [rd _ (by omega), show 11 + I.LS + I.LK + I.LP = 7 + I.LS + I.LK + (4 + I.LP) by omega,
      I.getD_tail, Inp.Tl]
    rw [List.getD_append_right _ _ _ _ (by simp [Inp.LP]; omega),
      show 4 + I.LP - ([I.LP + 4, 1, I.LP] ++ Enc.encode I.prog).length = 1 by
        simp [Inp.LP]; omega]
    rfl
  have hpr : (L ++ [2 * I.n]).getD (I.L0.length + I.σ) 0 = 16 + p := by
    rw [getD_prefix (by rw [hLlen, hLevlen]; omega), hL, List.append_assoc, List.append_assoc,
      getD_prefix (by rw [hLevlen]; omega), hLev, getD_tbl _ _ _ (by omega), hp]
  have hseg : ((L ++ [2 * I.n]).drop p).take (2 * I.n) = encNats (I.V.getD I.σ []) := by
    have := sp.2
    rw [hVn] at this
    show seg (L ++ [2 * I.n]) p (2 * I.n) = _
    rw [seg_append_left _ _ (by rw [hLlen]; omega), hL, List.append_assoc, List.append_assoc,
      seg_append_left _ _ hsp, this]
  have hX : (encNats (I.V.getD I.σ [])).length = 2 * I.n := by rw [length_encNats, hVn]
  have hL1 : (L ++ [2 * I.n]).length = L.length + 1 := by simp
  have hcont : ∀ w' : Mem, w' 11 = w 11 → w' 13 = w 13 → w' 14 = w 14 → w' 15 = w 15 →
      RunsTo outRest2 (St w' (L ++ [2 * I.n] ++ ((L ++ [2 * I.n]).drop p).take (2 * I.n)))
        (fun m => m = memAt 16 (fun _ => 0)
          ([(I.encM I.prog.length).length + I.LK + 2 * I.n + 3, 1,
            (I.encM I.prog.length).length + I.LK] ++ I.encM I.prog.length ++ Enc.encode I.K ++
            [2 * I.n] ++ encNats (I.V.getD I.σ [])))
        (7 * ((I.encM I.prog.length).length + I.LK + 2 * I.n + 4) + 5 * Lev.length + 43) := by
    intro w' f11 f13 f14 f15
    rw [hseg, hL]
    exact outRest2_spec (Lev := Lev) (E := I.encM I.prog.length) (Kw := Enc.encode I.K) hX
      (by rw [f11, h11]) (by rw [f13, h13]) (by rw [f14, h14]) (by rw [f15, h15]; rfl)
  have h := ex_pushV 13 (w := w) (L := L) (v := 2 * I.n) h13 h8 ⨾
    ex_assign 0 1 ⨾
    ex_addV 0 9 0 (a := 16 + (10 + I.LS + I.LK) + 11 * I.prog.length) (b := 1) (by rsimp [h9])
      (by rsimp) ⨾
    ex_loadV 0 0 (i := 11 + I.LS + I.LK + I.LP) (v := I.σ) (by rsimp) hσr ⨾
    ex_loadFixV 1 0 (v := I.Ez) (by rw [rd 0 (by omega), I.getD_zero]) ⨾
    ex_assign 2 17 ⨾
    ex_addV 1 1 2 (a := I.Ez) (b := 17) (by rsimp) (by rsimp) ⨾
    ex_addV 0 0 1 (a := I.σ) (b := I.Ez + 17) (by rsimp) (by rsimp) ⨾
    ex_loadV 0 0 (i := I.L0.length + I.σ) (v := 16 + p) (by rsimp) hpr ⨾
    ex_copyV 2 13 (a := 2 * I.n) (by rsimp [h13]) ⨾
    ex_pushBlock_then (p := p) (c := 2 * I.n) (by rsimp [hL1]) (by rsimp) (by rsimp)
      (by rw [hL1, hLlen]; omega) (by wf_tac)
      (fun w' hfr _ => hcont w'
        (by rw [hfr 11 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 13 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 14 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 15 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp))
  exact h.mono (by simp only [Inp.LK]; omega)

theorem Inp.length_encM_le (I : Inp) (hv : SLPValid I.n I.S I.prog) :
    ∀ i, i ≤ I.prog.length → (I.encM i).length ≤ (2 * I.n + 1) * i := by
  intro i
  induction i with
  | zero => intro _; rw [I.encM_zero]; simp
  | succ i ih =>
      intro hi
      have := ih (by omega)
      by_cases hf : I.prog[i].2.2.2 = 0
      · rw [I.encM_succ_zero (by omega) hf]; nlinarith
      · rw [I.encM_succ_ne hv (by omega) hf]
        simp only [List.length_append, List.length_singleton, length_encNats,
          I.length_V hv (by omega : i < I.prog.length)]
        nlinarith

/-- The words of the answer. -/
theorem Inp.encode_obsCore (I : Inp) (hv : SLPValid I.n I.S I.prog) (hσ : I.σ < I.prog.length) :
    Enc.encode (obsCore I.z) = [1, (I.encM I.prog.length).length + I.LK] ++
      I.encM I.prog.length ++ Enc.encode I.K ++ [2 * I.n] ++ encNats (I.V.getD I.σ []) := by
  have h : obsCore I.z = some (I.marked I.prog.length ++ I.K, I.V.getD I.σ []) := by
    rw [I.marked_all]; rfl
  rw [h]
  show 1 :: (frame (encList Enc.encode (I.marked I.prog.length ++ I.K)) ++
    frame (Enc.encode (I.V.getD I.σ []))) = _
  rw [encList_append, encode_listNat]
  simp [-List.getD_eq_getElem?_getD, frame, length_encNats, I.length_V hv hσ, Inp.encM, Inp.LK]
  exact ⟨rfl, rfl⟩

/-- **The kernel generators, the representative and the length fields.** -/
theorem outTail_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) (hσ : I.σ < I.prog.length) :
    RunsTo outTail (FDone I) (fun m => m = initMemAt 16 (Enc.encode (obsCore I.z)))
      (7 * ((2 * I.n + 1) * I.prog.length + I.LK + 2 * I.n + 4) +
        5 * (12 + 2 * I.LS + I.LK + 2 * I.LP + 2 * I.n * I.prog.length) + 14 * I.n + 84 +
        7 * I.LK) := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨tbl, dat, hg, w, hm', h9, h11, h8, h13, h14⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have hLP := I.LP_eq
  have hlen' := I.length_L0'
  have htl := hg.1
  have hdat := hg.2.2.2
  have hE := I.length_encM_le hv I.prog.length le_rfl
  set Lev := I.L0 ++ tbl ++ dat with hLev
  set L := Lev ++ [0, 1, 0] ++ I.encM I.prog.length with hL
  have hLevlen : Lev.length = I.L0.length + tbl.length + dat.length := by rw [hLev]; simp; omega
  have hLlen : L.length = Lev.length + 3 + (I.encM I.prog.length).length := by
    rw [hL]; simp; omega
  have rd : ∀ k, k < I.L0.length → L.getD k 0 = I.L0.getD k 0 := by
    intro k hk
    rw [hL, List.append_assoc, getD_prefix (by rw [hLevlen]; omega), hLev, List.append_assoc,
      getD_prefix hk]
  have hseg : (L.drop (7 + I.LS)).take I.LK = Enc.encode I.K := by
    show seg L (7 + I.LS) I.LK = _
    rw [hL, List.append_assoc, seg_append_left _ _ (by rw [hLevlen]; omega), hLev,
      List.append_assoc, seg_append_left _ _ (by omega), Inp.L0]
    exact headW_seg_K _ _ _ _ _
  have hcont : ∀ w' : Mem, w' 9 = w 9 → w' 11 = w 11 → w' 13 = w 13 → w' 14 = w 14 →
      w' 15 = I.LK → w' 8 = 16 + L.length + I.LK →
      RunsTo outRest1 (St w' (L ++ (L.drop (7 + I.LS)).take I.LK))
        (fun m => m = initMemAt 16 (Enc.encode (obsCore I.z)))
        (7 * ((I.encM I.prog.length).length + I.LK + 2 * I.n + 4) +
          5 * Lev.length + 14 * I.n + 70) := by
    intro w' f9 f11 f13 f14 f15 f8
    rw [hseg, I.encode_obsCore hv hσ, initMemAt_eq_memAt]
    have e : ([1, (I.encM I.prog.length).length + I.LK] ++ I.encM I.prog.length ++
        Enc.encode I.K ++ [2 * I.n] ++ encNats (I.V.getD I.σ [])).length =
        (I.encM I.prog.length).length + I.LK + 2 * I.n + 3 := by
      simp [-List.getD_eq_getElem?_getD, length_encNats, I.length_V hv hσ, Inp.LK]; omega
    rw [e]
    exact outRest1_spec I hv hσ hg (by rw [f8, hLlen]; simp [Inp.LK]; omega)
      (by rw [f9, h9]) (by rw [f11, h11]) (by rw [f13, h13]) (by rw [f14, h14]) f15
  have h := ex_loadFixV 0 5 (w := w) (L := L) (v := I.LS) (by rw [rd 5 (by omega), I.getD_LS]) ⨾
    ex_assign 1 23 ⨾
    ex_addV 0 0 1 (a := I.LS) (b := 23) (by rsimp) (by rsimp) ⨾
    ex_assign 1 1 ⨾
    ex_subV 1 0 1 (a := I.LS + 23) (b := 1) (by rsimp) (by rsimp) ⨾
    ex_loadV 2 1 (i := 6 + I.LS) (v := I.LK) (by rsimp) (by rw [rd _ (by omega), I.getD_LK]) ⨾
    ex_copyV 15 2 (a := I.LK) (by rsimp) ⨾
    ex_pushBlock_then (p := 7 + I.LS) (c := I.LK) (by rsimp [h8]) (by rsimp) (by rsimp)
      (by rw [hLlen]; omega) (by wf_tac)
      (fun w' hfr h8' => hcont w'
        (by rw [hfr 9 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 11 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 13 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 14 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp)
        (by rw [hfr 15 (by norm_num) (by norm_num) (by norm_num) (by omega)]; rsimp) h8')
  refine h.mono ?_
  have : 2 * I.n * I.prog.length = I.n * I.prog.length * 2 := by ring
  nlinarith

end SLPRAM
end Algo
