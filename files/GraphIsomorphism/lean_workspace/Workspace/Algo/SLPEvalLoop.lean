import Workspace.Algo.SLPEvalSetup

/-!
# The straight-line-program evaluator: the evaluation loop

The invariant of the evaluation phase of `Algo.SLPRAM.slpEvalProg` after `i` instructions: the
workspace is the input, the table and the blocks of the computed elements; table entry `j < i`
holds the address of element `j` of the sequence (`Algo.slpVals`), stored as a block
(`Algo.SLPRAM.SlotAt`) either in the input (a generator) or above the table (a product or an
inverse).
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Algo
namespace SLPRAM

open RAM Layout LX

/-- Well-formedness of a program assembled from the primitives. -/
macro "wf_tac" : tactic => `(tactic| repeat (first
  | apply wf_seq
  | apply wf_ifz
  | apply wf_whileNz
  | exact wf_assign _ _
  | exact wf_copyTo _ _
  | exact wf_addTo _ _ _
  | exact wf_subTo _ _ _
  | exact wf_loadTo _ _
  | exact wf_storeTo _ _
  | exact wf_pushVal _
  | exact wf_pushBlock
  | exact wf_finish _
  | exact wf_nil'))

/-! ## Facts about the values -/

/-- The sequence of the program of `I`. -/
abbrev Inp.V (I : Inp) : List RawPerm := slpVals I.S I.prog

theorem Inp.getD_V_of_lt (I : Inp) {j : ℕ} (hj : j < I.prog.length) :
    I.V.getD j [] = I.V[j]'(by simpa using hj) :=
  List.getD_eq_getElem _ _ _

theorem Inp.wf_V (I : Inp) (hv : SLPValid I.n I.S I.prog) {j : ℕ} (hj : j < I.prog.length) :
    RawPerm.WF I.n (I.V.getD j []) := by
  rw [I.getD_V_of_lt hj]; exact wf_slpVals hv j (by simpa using hj)

theorem Inp.length_V (I : Inp) (hv : SLPValid I.n I.S I.prog) {j : ℕ} (hj : j < I.prog.length) :
    (I.V.getD j []).length = I.n := (I.wf_V hv hj).length

theorem Inp.V_step (I : Inp) {i : ℕ} (hi : i < I.prog.length) :
    I.V.getD i [] = slpStep I.S (I.V.take i) I.prog[i] := by
  rw [I.getD_V_of_lt hi, getElem_slpVals]

theorem Inp.take_V_getD (I : Inp) {i a : ℕ} (ha : a < i) :
    (I.V.take i).getD a [] = I.V.getD a [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ha]

theorem Inp.V_op0 (I : Inp) {i : ℕ} (hi : i < I.prog.length) (h0 : I.prog[i].1 = 0) :
    I.V.getD i [] = I.S.getD I.prog[i].2.1 [] := by
  rw [I.V_step hi, slpStep, if_pos h0]

theorem Inp.V_op1 (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (h1 : I.prog[i].1 = 1) :
    I.V.getD i [] = rawMul (I.V.getD I.prog[i].2.1 [], I.V.getD I.prog[i].2.2.1 []) := by
  obtain ⟨-, ha, hb⟩ := hv.2 i hi
  rw [I.V_step hi, slpStep, if_neg (by omega), if_pos h1, I.take_V_getD (ha (by omega)),
    I.take_V_getD (hb h1)]

theorem Inp.V_op2 (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (h2 : 2 ≤ I.prog[i].1) :
    I.V.getD i [] = rawInv (I.V.getD I.prog[i].2.1 []) := by
  obtain ⟨-, ha, -⟩ := hv.2 i hi
  rw [I.V_step hi, slpStep, if_neg (by omega), if_neg (by omega), I.take_V_getD (ha (by omega))]

/-! ## The invariant -/

/-- The table and the blocks after `i` instructions. -/
def EGood (I : Inp) (i : ℕ) (tbl dat : List ℕ) : Prop :=
  tbl.length = I.LP + I.LS ∧
  (∀ j < I.S.length, tbl.getD (I.LP + j) 0 = 23 + (2 * I.n + 1) * j) ∧
  (∀ j < i, ∃ p, tbl.getD j 0 = 16 + p ∧ SlotAt (I.L0 ++ tbl ++ dat) p (I.V.getD j []) ∧
    (p + 2 * I.n ≤ I.L0.length ∨ I.L0.length + tbl.length ≤ p)) ∧
  dat.length ≤ 2 * I.n * i

/-- The loop registers before instruction `i`, with list `L`. -/
def ERegs (I : Inp) (i : ℕ) (L : List ℕ) (w : Mem) : Prop :=
  w 8 = 16 + L.length ∧ w 9 = 16 + (10 + I.LS + I.LK) + 11 * i ∧ w 11 = I.LP - 11 * i ∧
    w 12 = 17 + I.Ez + i ∧ w 13 = I.n ∧ w 14 = 17 + I.Ez ∧ w 15 = I.LP

/-- **The invariant of the evaluation loop.** -/
def EInv (I : Inp) (m : Mem) : Prop :=
  ∃ i w tbl dat, m = memAt 16 w (I.L0 ++ tbl ++ dat) ∧ i ≤ I.prog.length ∧ EGood I i tbl dat ∧
    ERegs I i (I.L0 ++ tbl ++ dat) w

/-- The state after the branch of instruction `i`: element `i` is in the table, the loop
registers not yet advanced. -/
def BPost (I : Inp) (i : ℕ) (m : Mem) : Prop :=
  ∃ w tbl dat, m = memAt 16 w (I.L0 ++ tbl ++ dat) ∧ EGood I (i + 1) tbl dat ∧
    ERegs I i (I.L0 ++ tbl ++ dat) w

/-- Registers that the branches keep. -/
def Keeps (w w' : Mem) : Prop :=
  w' 9 = w 9 ∧ w' 11 = w 11 ∧ w' 12 = w 12 ∧ w' 13 = w 13 ∧ w' 14 = w 14 ∧ w' 15 = w 15

/-! ## Reading the workspace -/

theorem Inp.LP_eq (I : Inp) : I.LP = 11 * I.prog.length := length_encode_prog I.prog

theorem getD_tbl (I : Inp) (tbl dat : List ℕ) {j : ℕ} (hj : j < tbl.length) :
    (I.L0 ++ tbl ++ dat).getD (I.L0.length + j) 0 = tbl.getD j 0 := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hj]

/-- A word of instruction `i`. -/
theorem getD_ins (I : Inp) (tbl dat : List ℕ) {i : ℕ} (hi : i < I.prog.length) {k : ℕ}
    (hk : k < 11) :
    (I.L0 ++ tbl ++ dat).getD (10 + I.LS + I.LK + 11 * i + k) 0 =
      [10, 1, I.prog[i].1, 7, 1, I.prog[i].2.1, 4, 1, I.prog[i].2.2.1, 1,
        I.prog[i].2.2.2].getD k 0 := by
  have hlen := I.length_L0'
  have hLP := I.LP_eq
  rw [List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  have h1 := I.getD_tail (3 + 11 * i + k)
  rw [show 7 + I.LS + I.LK + (3 + 11 * i + k) = 10 + I.LS + I.LK + 11 * i + k by omega] at h1
  rw [h1, Inp.Tl, List.append_assoc, show 3 + 11 * i + k = [I.LP + 4, 1, I.LP].length +
    (11 * i + k) by simp; omega, List.getD_append_right _ _ _ _ (by simp),
    Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by rw [← Inp.LP, hLP]; omega)]
  rw [← getD_of_seg (seg_encode_prog I.prog i hi) hk]

/-- A generator in place. -/
theorem slotAt_gen (I : Inp) (hS : RawGens.WF I.n I.S) {j : ℕ} (hj : j < I.S.length) :
    SlotAt I.L0 (7 + (2 * I.n + 1) * j) (I.S.getD j []) := by
  have hLSe : I.LS = (2 * I.n + 1) * I.S.length := length_encode_gens I.n hS
  have hlen := I.length_L0'
  have hwf : (I.S.getD j []).length = I.n := by
    rw [List.getD_eq_getElem _ _ hj]; exact (hS _ (List.getElem_mem hj)).length
  have hjS : (2 * I.n + 1) * j + (2 * I.n + 1) ≤ I.LS := by
    rw [hLSe, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  refine ⟨by rw [hwf]; omega, ?_⟩
  have h1 := headW_seg_S I.n I.S I.K I.Ez I.Tl
  have h2 := seg_seg (p' := (2 * I.n + 1) * j + 1) (c' := 2 * I.n) h1 (by rw [← Inp.LS]; omega)
  rw [seg_encode_gens I.n hS j hj] at h2
  rw [hwf, List.getD_eq_getElem _ _ hj, Inp.L0, show 7 + (2 * I.n + 1) * j =
    6 + ((2 * I.n + 1) * j + 1) by omega, h2]

/-! ## One more element in the table -/

/-- A block that avoids the table survives a write into the table. -/
theorem slotAt_set_tbl (I : Inp) (tbl dat : List ℕ) {i : ℕ} (hi : i < tbl.length) (x : ℕ)
    {p : ℕ} {v : List ℕ} (hp : SlotAt (I.L0 ++ tbl ++ dat) p v)
    (hd : p + 2 * v.length ≤ I.L0.length ∨ I.L0.length + tbl.length ≤ p) :
    SlotAt (I.L0 ++ tbl.set i x ++ dat) p v := by
  rw [← set_append3 _ _ _ hi]
  exact hp.set x (by omega)

theorem EGood.step {I : Inp} {i : ℕ} {tbl dat : List ℕ} (hg : EGood I i tbl dat)
    (hv : SLPValid I.n I.S I.prog) (hi : i < I.prog.length) (X : List ℕ)
    (hX : X.length ≤ 2 * I.n) {p : ℕ}
    (hp : SlotAt (I.L0 ++ tbl ++ dat ++ X) p (I.V.getD i []))
    (hd : p + 2 * I.n ≤ I.L0.length ∨ I.L0.length + tbl.length ≤ p) :
    EGood I (i + 1) (tbl.set i (16 + p)) (dat ++ X) := by
  obtain ⟨htl, hgen, hslot, hdat⟩ := hg
  have hLP := I.LP_eq
  have hitl : i < tbl.length := by rw [htl]; omega
  have hassoc : I.L0 ++ tbl ++ (dat ++ X) = I.L0 ++ tbl ++ dat ++ X := by simp
  refine ⟨by simp [htl], fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [getD_set_ne _ (by omega), hgen j hj]
  · rcases Nat.lt_or_ge j i with hji | hji
    · obtain ⟨q, hq, hqs, hqd⟩ := hslot j hji
      refine ⟨q, by rw [getD_set_ne _ (by omega), hq], ?_, by simpa using hqd⟩
      have := slotAt_set_tbl I tbl (dat ++ X) hitl (16 + p) (p := q) (v := I.V.getD j [])
        (by rw [hassoc]; exact hqs.append X) (by rw [I.length_V hv (by omega)]; exact hqd)
      exact this
    · have : j = i := by omega
      subst this
      refine ⟨p, getD_set_eq _ hitl _, ?_, by simpa using hd⟩
      exact slotAt_set_tbl I tbl (dat ++ X) hitl (16 + p) (by rw [hassoc]; exact hp)
        (by rw [I.length_V hv hi]; exact hd)
  · rw [List.length_append, Nat.mul_succ]; omega

/-! ## A generator -/

theorem genB_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (h0 : I.prog[i].1 = 0) {w : Mem} {tbl dat : List ℕ} (hg : EGood I i tbl dat)
    (hr : ERegs I i (I.L0 ++ tbl ++ dat) w) (h1 : w 1 = I.prog[i].2.1) :
    RunsTo genB (St w (I.L0 ++ tbl ++ dat)) (BPost I i) 5 := by
  obtain ⟨h8, h9, h11, h12, h13, h14, h15⟩ := hr
  have hlen := I.length_L0
  have ha : I.prog[i].2.1 < I.S.length := (hv.2 i hi).1 h0
  have htl := hg.1
  have hLP := I.LP_eq
  have hLSe : I.LS = (2 * I.n + 1) * I.S.length := length_encode_gens I.n hv.1
  have haLS : I.prog[i].2.1 < I.LS :=
    lt_of_lt_of_le ha (by rw [hLSe]; exact Nat.le_mul_of_pos_left _ (by omega))
  have hread : (I.L0 ++ tbl ++ dat).getD (I.L0.length + (I.LP + I.prog[i].2.1)) 0 =
      23 + (2 * I.n + 1) * I.prog[i].2.1 := by
    rw [getD_tbl _ _ _ (by rw [htl]; omega), hg.2.1 _ ha]
  have h := ex_copyV 3 14 (w := w) (L := I.L0 ++ tbl ++ dat) (a := 17 + I.Ez) h14 ⨾
    ex_addV 3 3 15 (a := 17 + I.Ez) (b := I.LP) (by rsimp) (by rsimp [h15]) ⨾
    ex_addV 3 3 1 (a := 17 + I.Ez + I.LP) (b := I.prog[i].2.1) (by rsimp) (by rsimp [h1]) ⨾
    ex_loadV 3 3 (i := I.L0.length + (I.LP + I.prog[i].2.1)) (by rsimp [hlen]) hread ⨾
    ex_storeV 12 3 (i := I.L0.length + i) (v := 23 + (2 * I.n + 1) * I.prog[i].2.1)
      (by rsimp [h12, hlen]) (by rsimp)
      (by simp; omega)
  refine (h.weaken (fun m hm => ⟨_, tbl.set i (16 + (7 + (2 * I.n + 1) * I.prog[i].2.1)),
    dat ++ [], hm.to ?_, ?_, ?_⟩)).mono le_rfl
  · rw [set_append3 _ _ _ (by omega), List.append_nil]; ring_nf
  · refine hg.step hv hi [] (by simp) ?_ (Or.inl ?_)
    · rw [I.V_op0 hi h0, List.append_nil, List.append_assoc]
      exact (slotAt_gen I hv.1 ha).append _
    · have hjS : (2 * I.n + 1) * I.prog[i].2.1 + (2 * I.n + 1) ≤ I.LS := by
        rw [hLSe, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ha
      have := I.length_L0'
      omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rsimp [h8, h9, h11, h12, h13, h14, h15]

/-! ## A product -/

/-- The invariant of the product loop after `u` entries. -/
def PInv (L : List ℕ) (pa pb : ℕ) (A B : List ℕ) (n : ℕ) (w : Mem) (m : Mem) : Prop :=
  ∃ u w', m = memAt 16 w' (L ++ encNats ((rawMul (A, B)).take u)) ∧ u ≤ n ∧
    w' 0 = 16 + pa + 1 ∧ w' 1 = 16 + pb + 1 + 2 * u ∧ w' 2 = n - u ∧ w' 4 = 1 ∧ w' 5 = 2 ∧
    w' 6 = 16 + L.length ∧ w' 8 = 16 + L.length + 2 * u ∧ Keeps w w'

theorem prodBody_spec {L : List ℕ} {pa pb : ℕ} {A B : List ℕ} {n : ℕ} {w : Mem}
    (hA : SlotAt L pa A) (hB : SlotAt L pb B) (hlA : A.length = n) (hlB : B.length = n)
    (hBlt : ∀ x ∈ B, x < n) (N : ℕ) :
    RunsTo prodBody (fun m => PInv L pa pb A B n w m ∧ m 2 = N + 1)
      (fun m => PInv L pa pb A B n w m ∧ m 2 = N) 12 := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨⟨u, w', hm', hun, h0, h1, h2, h4, h5, h6, h8, hk⟩, hN⟩ := hm
  refine ⟨w', _, hm', ?_⟩
  have h2' : m 2 = w' 2 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hu : u < n := by rw [h2', h2] at hN; omega
  have hlP : (rawMul (A, B)).length = n := by rw [length_rawMul, hlB]
  have hlT : (L ++ encNats ((rawMul (A, B)).take u)).length = L.length + 2 * u := by
    simp [List.length_take]; omega
  have hxn : B.getD u 0 < n := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hBlt _ (List.getElem_mem _)
  have hrB : (L ++ encNats ((rawMul (A, B)).take u) ++ [1]).getD (pb + (2 * u + 1)) 0 =
      B.getD u 0 := by
    have := hB.1
    rw [getD_prefix (by rw [hlT]; omega), getD_prefix (by omega), hB.getD' (by omega)]
  have hrA : (L ++ encNats ((rawMul (A, B)).take u) ++ [1]).getD
      (pa + (2 * B.getD u 0 + 1)) 0 = A.getD (B.getD u 0) 0 := by
    have := hA.1
    rw [getD_prefix (by rw [hlT]; omega), getD_prefix (by omega), hA.getD' (by omega)]
  have h := ex_pushV 4 (w := w') (L := L ++ encNats ((rawMul (A, B)).take u)) (v := 1) h4
      (by rw [h8, hlT]; omega) ⨾
    ex_loadV 3 1 (i := pb + (2 * u + 1)) (by rsimp [h1]) hrB ⨾
    ex_addV 3 3 3 (a := B.getD u 0) (b := B.getD u 0) (by rsimp) (by rsimp) ⨾
    ex_addV 3 3 0 (a := B.getD u 0 + B.getD u 0) (b := 16 + pa + 1) (by rsimp) (by rsimp [h0]) ⨾
    ex_loadV 3 3 (i := pa + (2 * B.getD u 0 + 1)) (by rsimp) hrA ⨾
    ex_pushV 3 (v := A.getD (B.getD u 0) 0) (by rsimp) (by rsimp [hlT]) ⨾
    ex_addV 1 1 5 (a := 16 + pb + 1 + 2 * u) (b := 2) (by rsimp [h1]) (by rsimp [h5]) ⨾
    ex_subV 2 2 4 (a := n - u) (b := 1) (by rsimp [h2]) (by rsimp [h4])
  refine (h.weaken (fun m hm => ⟨⟨u + 1, _, hm.to ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩)).mono (by norm_num)
  · rw [take_succ_getD _ (by rw [hlP]; exact hu), encNats_append, encNats_singleton,
      rawMul_getD _ _ (by rw [hlB]; exact hu) (by rw [hlA]; exact hxn)]
    simp
  · rsimp [h0]
  · rsimp
  · rsimp
  · rsimp
  · rsimp [h5]
  · rsimp [h6]
  · rsimp [hlT]
  · obtain ⟨k9, k11, k12, k13, k14, k15⟩ := hk
    exact ⟨by rsimp [k9], by rsimp [k11], by rsimp [k12], by rsimp [k13], by rsimp [k14],
      by rsimp [k15]⟩
  · rw [hm, memAt_of_lt _ _ (by norm_num : (2:ℕ) < 16)]; rw [h2', h2] at hN; rsimp

/-- Register `12` still points at table entry `i` and the other loop registers are kept. -/
theorem ERegs.keeps {I : Inp} {i : ℕ} {L L' : List ℕ} {w w' : Mem} (hr : ERegs I i L w)
    (hk : Keeps w w') (h8 : w' 8 = 16 + L'.length) : ERegs I i L' w' := by
  obtain ⟨-, h9, h11, h12, h13, h14, h15⟩ := hr
  obtain ⟨k9, k11, k12, k13, k14, k15⟩ := hk
  exact ⟨h8, k9.trans h9, k11.trans h11, k12.trans h12, k13.trans h13, k14.trans h14,
    k15.trans h15⟩

/-- Storing the address of a new block above the old list as table entry `i`. -/
theorem store_new (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    {tbl dat : List ℕ} {w : Mem} (hg : EGood I i tbl dat)
    (hr : ERegs I i (I.L0 ++ tbl ++ dat) w) (X : List ℕ) (hX : X = encNats (I.V.getD i [])) {w' : Mem} (hk : Keeps w w')
    (h6 : w' 6 = 16 + (I.L0 ++ tbl ++ dat).length)
    (h8 : w' 8 = 16 + (I.L0 ++ tbl ++ dat).length + X.length) :
    RunsTo (storeTo 12 6) (St w' (I.L0 ++ tbl ++ dat ++ X)) (BPost I i) 1 := by
  have htl := hg.1
  have hLP := I.LP_eq
  have hlen := I.length_L0
  have h12 := hr.2.2.2.1
  have k12 := hk.2.2.1
  refine (ex_storeV 12 6 (i := I.L0.length + i) (v := 16 + (I.L0 ++ tbl ++ dat).length)
    (by rw [k12, h12, hlen]; omega) h6 (by simp; omega)).weaken (fun m hm => ?_)
  refine ⟨w', tbl.set i (16 + (I.L0 ++ tbl ++ dat).length), dat ++ X, hm.to ?_, ?_, ?_⟩
  · rw [show I.L0 ++ tbl ++ dat ++ X = I.L0 ++ tbl ++ (dat ++ X) by simp,
      set_append3 _ _ _ (by omega)]
  · refine hg.step hv hi X (by rw [hX, length_encNats, I.length_V hv hi]) ?_ (Or.inr (by simp))
    rw [hX]; exact slotAt_append_self _ _
  · refine hr.keeps hk ?_
    rw [h8]; simp; omega

/-- **A product.** -/
theorem prodB_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (hop : I.prog[i].1 = 1) {w : Mem} {tbl dat : List ℕ} (hg : EGood I i tbl dat)
    (hr : ERegs I i (I.L0 ++ tbl ++ dat) w) (h1 : w 1 = I.prog[i].2.1)
    (h2 : w 2 = I.prog[i].2.2.1) (h4 : w 4 = 1) :
    RunsTo prodB (St w (I.L0 ++ tbl ++ dat)) (BPost I i) (14 * I.n + 11) := by
  obtain ⟨-, haI, hbI⟩ := hv.2 i hi
  have hai : I.prog[i].2.1 < i := haI (by omega)
  have hbi : I.prog[i].2.2.1 < i := hbI hop
  obtain ⟨pa, hpa, sA, -⟩ := hg.2.2.1 _ hai
  obtain ⟨pb, hpb, sB, -⟩ := hg.2.2.1 _ hbi
  have htl := hg.1
  have hLP := I.LP_eq
  have hlen := I.length_L0
  obtain ⟨h8, h9, h11, h12, h13, h14, h15⟩ := hr
  set L := I.L0 ++ tbl ++ dat with hL
  set A := I.V.getD I.prog[i].2.1 [] with hA
  set B := I.V.getD I.prog[i].2.2.1 [] with hB
  have wA := I.wf_V hv (j := I.prog[i].2.1) (by omega)
  have wB := I.wf_V hv (j := I.prog[i].2.2.1) (by omega)
  have hloop := runsTo_forLoop (i := 2) (inv := PInv L pa pb A B I.n w) (T := 12) (N := I.n)
    (prodBody_spec sA sB wA.length wB.length (fun x hx => wB.lt hx)) (fun m hm => by
      obtain ⟨u, w', hm', -, -, -, h2', -⟩ := hm
      rw [hm', memAt_of_lt _ _ (by norm_num), h2']; omega)
  have hstore : RunsTo (storeTo 12 6) (fun m => PInv L pa pb A B I.n w m ∧ m 2 = 0)
      (BPost I i) 1 := by
    refine runsTo_of_exists_St (wf_storeTo _ _) (fun m hm => ?_)
    obtain ⟨⟨u, w', hm', hun, -, -, h2', -, -, h6', h8', hk⟩, h0⟩ := hm
    have hu : u = I.n := by rw [hm', memAt_of_lt _ _ (by norm_num), h2'] at h0; omega
    subst hu
    have hP : (rawMul (A, B)).take I.n = I.V.getD i [] := by
      rw [List.take_of_length_le (by rw [length_rawMul, wB.length]), I.V_op1 hv hi hop]
    refine ⟨w', _, hm', ?_⟩
    rw [hP, hL]
    exact store_new I hv hi hg ⟨h8, h9, h11, h12, h13, h14, h15⟩ _ rfl hk h6'
      (by rw [h8', ← hL, length_encNats, I.length_V hv hi])
  have hread : ∀ j, j < i → L.getD (I.L0.length + j) 0 = tbl.getD j 0 := fun j hj =>
    getD_tbl I tbl dat (by rw [htl]; omega)
  have h := ex_addV 3 14 1 (w := w) (L := L) (a := 17 + I.Ez) (b := I.prog[i].2.1) h14 h1 ⨾
    ex_loadV 3 3 (i := I.L0.length + I.prog[i].2.1) (v := 16 + pa) (by rsimp [hlen])
      (by rw [hread _ hai, hpa]) ⨾
    ex_addV 0 3 4 (a := 16 + pa) (b := 1) (by rsimp) (by rsimp [h4]) ⨾
    ex_addV 3 14 2 (a := 17 + I.Ez) (b := I.prog[i].2.2.1) (by rsimp [h14]) (by rsimp [h2]) ⨾
    ex_loadV 3 3 (i := I.L0.length + I.prog[i].2.2.1) (v := 16 + pb) (by rsimp [hlen])
      (by rw [hread _ hbi, hpb]) ⨾
    ex_addV 1 3 4 (a := 16 + pb) (b := 1) (by rsimp) (by rsimp [h4]) ⨾
    ex_copyV 6 8 (a := 16 + L.length) (by rsimp [h8]) ⨾
    ex_copyV 2 13 (a := I.n) (by rsimp [h13]) ⨾
    ex_assign 5 2 ⨾
    hloop.strengthen (fun m hm => ⟨0, _, hm.to (by simp), by omega, by rsimp, by rsimp,
      by rsimp, by rsimp [h4], by rsimp, by rsimp, by rsimp [h8],
      ⟨by rsimp, by rsimp, by rsimp, by rsimp, by rsimp, by rsimp⟩⟩) ⨾
    hstore
  exact h.mono (by ring_nf; omega)

/-! ## An inverse -/

/-- The invariant of the zeroing loop after `u` blocks. -/
def ZInv (L : List ℕ) (pa n : ℕ) (w : Mem) (m : Mem) : Prop :=
  ∃ u w', m = memAt 16 w' (L ++ encNats (List.replicate u 0)) ∧ u ≤ n ∧
    w' 1 = 16 + pa + 1 ∧ w' 2 = n - u ∧ w' 4 = 1 ∧ w' 6 = 16 + L.length ∧ w' 7 = 0 ∧
    w' 8 = 16 + L.length + 2 * u ∧ Keeps w w'

theorem zeroBody_spec {L : List ℕ} {pa n : ℕ} {w : Mem} (N : ℕ) :
    RunsTo zeroBody (fun m => ZInv L pa n w m ∧ m 2 = N + 1)
      (fun m => ZInv L pa n w m ∧ m 2 = N) 7 := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨⟨u, w', hm', hun, h1, h2, h4, h6, h7, h8, hk⟩, hN⟩ := hm
  refine ⟨w', _, hm', ?_⟩
  have h2' : m 2 = w' 2 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hu : u < n := by rw [h2', h2] at hN; omega
  have hlT : (L ++ encNats (List.replicate u 0)).length = L.length + 2 * u := by simp
  have h := ex_pushV 4 (w := w') (L := L ++ encNats (List.replicate u 0)) (v := 1) h4
      (by rw [h8, hlT]; omega) ⨾
    ex_pushV 7 (v := 0) (by rsimp [h7]) (by rsimp [hlT]) ⨾
    ex_subV 2 2 4 (a := n - u) (b := 1) (by rsimp [h2]) (by rsimp [h4])
  refine (h.weaken (fun m hm => ⟨⟨u + 1, _, hm.to ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩)).mono (by norm_num)
  · rw [encNats_replicate_succ]; simp
  · rsimp [h1]
  · rsimp
  · rsimp
  · rsimp [h6]
  · rsimp [h7]
  · rsimp [hlT]
  · obtain ⟨k9, k11, k12, k13, k14, k15⟩ := hk
    exact ⟨by rsimp [k9], by rsimp [k11], by rsimp [k12], by rsimp [k13], by rsimp [k14],
      by rsimp [k15]⟩
  · rw [hm, memAt_of_lt _ _ (by norm_num : (2:ℕ) < 16)]; rw [h2', h2] at hN; rsimp

/-- The invariant of the scattering loop after `u` writes. -/
def SInv (L : List ℕ) (pa : ℕ) (A : List ℕ) (n : ℕ) (w : Mem) (m : Mem) : Prop :=
  ∃ u w', m = memAt 16 w' (L ++ encNats (scat n A u)) ∧ u ≤ n ∧
    w' 0 = 16 + L.length + 1 ∧ w' 1 = 16 + pa + 1 + 2 * u ∧ w' 2 = n - u ∧ w' 3 = u ∧
    w' 4 = 1 ∧ w' 5 = 2 ∧ w' 6 = 16 + L.length ∧ w' 8 = 16 + L.length + 2 * n ∧ Keeps w w'

theorem scatBody_spec {L : List ℕ} {pa : ℕ} {A : List ℕ} {n : ℕ} {w : Mem}
    (hA : SlotAt L pa A) (hwf : RawPerm.WF n A) (N : ℕ) :
    RunsTo scatBody (fun m => SInv L pa A n w m ∧ m 2 = N + 1)
      (fun m => SInv L pa A n w m ∧ m 2 = N) 7 := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨⟨u, w', hm', hun, h0, h1, h2, h3, h4, h5, h6, h8, hk⟩, hN⟩ := hm
  refine ⟨w', _, hm', ?_⟩
  have h2' : m 2 = w' 2 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hu : u < n := by rw [h2', h2] at hN; omega
  have hlA := hwf.length
  have hxn : A.getD u 0 < n := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hwf.lt (List.getElem_mem _)
  have hrA : (L ++ encNats (scat n A u)).getD (pa + (2 * u + 1)) 0 = A.getD u 0 := by
    have := hA.1
    rw [getD_prefix (by omega), hA.getD' (by omega)]
  have h := ex_loadV 7 1 (w := w') (L := L ++ encNats (scat n A u)) (i := pa + (2 * u + 1))
      (by rsimp [h1]) hrA ⨾
    ex_addV 7 7 7 (a := A.getD u 0) (b := A.getD u 0) (by rsimp) (by rsimp) ⨾
    ex_addV 7 7 0 (a := A.getD u 0 + A.getD u 0) (b := 16 + L.length + 1) (by rsimp)
      (by rsimp [h0]) ⨾
    ex_storeV 7 3 (i := L.length + (2 * A.getD u 0 + 1)) (v := u) (by rsimp) (by rsimp [h3])
      (by rw [List.length_append, length_encNats, length_scat]; omega) ⨾
    ex_addV 3 3 4 (a := u) (b := 1) (by rsimp [h3]) (by rsimp [h4]) ⨾
    ex_addV 1 1 5 (a := 16 + pa + 1 + 2 * u) (b := 2) (by rsimp [h1]) (by rsimp [h5]) ⨾
    ex_subV 2 2 4 (a := n - u) (b := 1) (by rsimp [h2]) (by rsimp [h4])
  refine (h.weaken (fun m hm => ⟨⟨u + 1, _, hm.to ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, ?_⟩)).mono (by norm_num)
  · rw [set_append2 _ _ (by rw [length_encNats, length_scat]; omega),
      encNats_set _ (by rw [length_scat]; exact hxn), scat_succ]
  · rsimp [h0]
  · rsimp
  · rsimp
  · rsimp
  · rsimp [h4]
  · rsimp [h5]
  · rsimp [h6]
  · rsimp [h8]
  · obtain ⟨k9, k11, k12, k13, k14, k15⟩ := hk
    exact ⟨by rsimp [k9], by rsimp [k11], by rsimp [k12], by rsimp [k13], by rsimp [k14],
      by rsimp [k15]⟩
  · rw [hm, memAt_of_lt _ _ (by norm_num : (2:ℕ) < 16)]; rw [h2', h2] at hN; rsimp

/-- **An inverse.** -/
theorem invB_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (hop : 2 ≤ I.prog[i].1) {w : Mem} {tbl dat : List ℕ} (hg : EGood I i tbl dat)
    (hr : ERegs I i (I.L0 ++ tbl ++ dat) w) (h1 : w 1 = I.prog[i].2.1) (h4 : w 4 = 1) :
    RunsTo invB (St w (I.L0 ++ tbl ++ dat)) (BPost I i) (18 * I.n + 16) := by
  obtain ⟨-, haI, -⟩ := hv.2 i hi
  have hai : I.prog[i].2.1 < i := haI (by omega)
  obtain ⟨pa, hpa, sA, -⟩ := hg.2.2.1 _ hai
  have htl := hg.1
  have hLP := I.LP_eq
  have hlen := I.length_L0
  obtain ⟨h8, h9, h11, h12, h13, h14, h15⟩ := hr
  set L := I.L0 ++ tbl ++ dat with hL
  set A := I.V.getD I.prog[i].2.1 [] with hA
  have wA := I.wf_V hv (j := I.prog[i].2.1) (by omega)
  have hzero := runsTo_forLoop (i := 2) (inv := ZInv L pa I.n w) (T := 7) (N := I.n)
    zeroBody_spec (fun m hm => by
      obtain ⟨u, w', hm', -, -, h2', -⟩ := hm
      rw [hm', memAt_of_lt _ _ (by norm_num), h2']; omega)
  have hscat := runsTo_forLoop (i := 2) (inv := SInv L pa A I.n w) (T := 7) (N := I.n)
    (scatBody_spec sA wA) (fun m hm => by
      obtain ⟨u, w', hm', -, -, -, h2', -⟩ := hm
      rw [hm', memAt_of_lt _ _ (by norm_num), h2']; omega)
  have hmid : RunsTo (seq (addTo 0 6 4) <| seq (copyTo 2 13) <| seq (assign 3 0) <|
      assign 5 2) (fun m => ZInv L pa I.n w m ∧ m 2 = 0) (SInv L pa A I.n w) 4 := by
    refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
    obtain ⟨⟨u, w', hm', hun, h1', h2', h4', h6', h7', h8', hk⟩, h0⟩ := hm
    have hu : u = I.n := by rw [hm', memAt_of_lt _ _ (by norm_num), h2'] at h0; omega
    subst hu
    refine ⟨w', _, hm', ?_⟩
    have k13 := hk.2.2.2.1
    have h := ex_addV 0 6 4 (w := w') (L := L ++ encNats (List.replicate I.n 0))
        (a := 16 + L.length) (b := 1) h6' h4' ⨾
      ex_copyV 2 13 (a := I.n) (by rsimp [k13, h13]) ⨾ ex_assign 3 0 ⨾ ex_assign 5 2
    refine h.weaken (fun m hm => ⟨0, _, hm.to (by rw [scat_zero]), by omega, by rsimp,
      by rsimp [h1'], by rsimp, by rsimp, by rsimp [h4'], by rsimp, by rsimp [h6'],
      by rsimp [h8'], ?_⟩)
    obtain ⟨k9, k11, k12, k13, k14, k15⟩ := hk
    exact ⟨by rsimp [k9], by rsimp [k11], by rsimp [k12], by rsimp [k13], by rsimp [k14],
      by rsimp [k15]⟩
  have hstore : RunsTo (storeTo 12 6) (fun m => SInv L pa A I.n w m ∧ m 2 = 0)
      (BPost I i) 1 := by
    refine runsTo_of_exists_St (wf_storeTo _ _) (fun m hm => ?_)
    obtain ⟨⟨u, w', hm', hun, -, -, h2', -, -, -, h6', h8', hk⟩, h0⟩ := hm
    have hu : u = I.n := by rw [hm', memAt_of_lt _ _ (by norm_num), h2'] at h0; omega
    subst hu
    have hP : scat I.n A I.n = I.V.getD i [] := by
      rw [scat_eq_rawInv wA, I.V_op2 hv hi hop]
    refine ⟨w', _, hm', ?_⟩
    rw [hP, hL]
    exact store_new I hv hi hg ⟨h8, h9, h11, h12, h13, h14, h15⟩ _ rfl hk h6'
      (by rw [h8', ← hL, length_encNats, I.length_V hv hi])
  have hread : L.getD (I.L0.length + I.prog[i].2.1) 0 = tbl.getD I.prog[i].2.1 0 :=
    getD_tbl I tbl dat (by rw [htl]; omega)
  have h := ex_addV 3 14 1 (w := w) (L := L) (a := 17 + I.Ez) (b := I.prog[i].2.1) h14 h1 ⨾
    ex_loadV 3 3 (i := I.L0.length + I.prog[i].2.1) (v := 16 + pa) (by rsimp [hlen])
      (by rw [hread, hpa]) ⨾
    ex_addV 1 3 4 (a := 16 + pa) (b := 1) (by rsimp) (by rsimp [h4]) ⨾
    ex_copyV 6 8 (a := 16 + L.length) (by rsimp [h8]) ⨾
    ex_copyV 2 13 (a := I.n) (by rsimp [h13]) ⨾
    ex_assign 7 0 ⨾
    hzero.strengthen (fun m hm => ⟨0, _, hm.to (by simp), by omega, by rsimp, by rsimp,
      by rsimp [h4], by rsimp, by rsimp, by rsimp [h8],
      ⟨by rsimp, by rsimp, by rsimp, by rsimp, by rsimp, by rsimp⟩⟩) ⨾
    hmid ⨾ hscat ⨾ hstore
  exact h.mono (by ring_nf; omega)

/-! ## One instruction -/

theorem ERegs.update {I : Inp} {i : ℕ} {L : List ℕ} {w : Mem} (hr : ERegs I i L w) {z : ℕ}
    (hz : z < 8 ∨ z = 10) (v : ℕ) : ERegs I i L (w.update z v) := by
  obtain ⟨h8, h9, h11, h12, h13, h14, h15⟩ := hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [Mem.update_of_ne _ _ (by omega)]; assumption)

/-- A product or an inverse. -/
theorem nonGenB_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) {i : ℕ} (hi : i < I.prog.length)
    (hop : I.prog[i].1 ≠ 0) {w : Mem} {tbl dat : List ℕ} (hg : EGood I i tbl dat)
    (hr : ERegs I i (I.L0 ++ tbl ++ dat) w) (h0 : w 0 = I.prog[i].1) (h1 : w 1 = I.prog[i].2.1)
    (h2 : w 2 = I.prog[i].2.2.1) :
    RunsTo nonGenB (St w (I.L0 ++ tbl ++ dat)) (BPost I i) (18 * I.n + 20) := by
  have hr' := (hr.update (z := 4) (by omega) 1).update (z := 3) (by omega) (I.prog[i].1 - 1)
  have hbr : RunsTo (ifz 3 invB prodB)
      (St ((w.update 4 1).update 3 (I.prog[i].1 - 1)) (I.L0 ++ tbl ++ dat)) (BPost I i)
      (18 * I.n + 18) := by
    by_cases h1op : I.prog[i].1 = 1
    · exact (ex_ifz_eq (by norm_num) (by rsimp [h1op]) (prodB_spec I hv hi h1op hg hr'
        (by rsimp [h1]) (by rsimp [h2]) (by rsimp)) (by wf_tac)).mono (by omega)
    · exact (ex_ifz_ne (by norm_num) (by rsimp) (invB_spec I hv hi (by omega) hg hr'
        (by rsimp [h1]) (by rsimp)) (by wf_tac)).mono (by omega)
  exact (ex_assign 4 1 (w := w) (L := I.L0 ++ tbl ++ dat) ⨾
    ex_subV 3 0 4 (a := I.prog[i].1) (b := 1) (by rsimp [h0]) (by rsimp) ⨾ hbr).mono
    (by omega)

/-- **One instruction of the evaluation loop.** -/
theorem evalBody_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) (N : ℕ) :
    RunsTo evalBody (fun m => EInv I m ∧ m 11 ≠ 0 ∧ m 11 = N)
      (fun m => EInv I m ∧ m 11 < N) (18 * I.n + 36) := by
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨⟨i, w, tbl, dat, hm', hile, hg, hr⟩, hne, hN⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have hLP := I.LP_eq
  have h11m : m 11 = w 11 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hi : i < I.prog.length := by
    have := hr.2.2.1; rw [h11m, this] at hne; omega
  have hNi : N = I.LP - 11 * i := by rw [← hN, h11m, hr.2.2.1]
  have h9 := hr.2.1
  have hins := fun k (hk : k < 11) => getD_ins I tbl dat hi hk
  have htail : RunsTo evalTail (BPost I i) (fun m => EInv I m ∧ m 11 < N) 5 := by
    refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
    obtain ⟨w', tbl', dat', hm'', hg', h8', h9', h11', h12', h13', h14', h15'⟩ := hm
    refine ⟨w', _, hm'', ?_⟩
    have h := ex_assign 0 11 (w := w') (L := I.L0 ++ tbl' ++ dat') ⨾
      ex_addV 9 9 0 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 11) (by rsimp [h9'])
        (by rsimp) ⨾
      ex_subV 11 11 0 (a := I.LP - 11 * i) (b := 11) (by rsimp [h11']) (by rsimp) ⨾
      ex_assign 0 1 ⨾
      ex_addV 12 12 0 (a := 17 + I.Ez + i) (b := 1) (by rsimp [h12']) (by rsimp)
    refine (h.weaken (fun m hm => ⟨⟨i + 1, _, tbl', dat', hm.to rfl, by omega, hg',
      by rsimp [h8'], by rsimp, by rsimp, by rsimp, by rsimp [h13'], by rsimp [h14'],
      by rsimp [h15']⟩, ?_⟩)).mono (by norm_num)
    rw [hm, memAt_of_lt _ _ (by norm_num : (11:ℕ) < 16), hNi]; rsimp
  have hbr : ∀ W : Mem, W 0 = I.prog[i].1 → W 1 = I.prog[i].2.1 → W 2 = I.prog[i].2.2.1 →
      ERegs I i (I.L0 ++ tbl ++ dat) W →
      RunsTo (ifz 0 nonGenB genB) (St W (I.L0 ++ tbl ++ dat)) (BPost I i) (18 * I.n + 22) := by
    intro W h0 h1 h2 hW
    by_cases hop : I.prog[i].1 = 0
    · exact (ex_ifz_eq (by norm_num) (by rw [h0, hop]) (genB_spec I hv hi hop hg hW h1)
        (by wf_tac)).mono (by omega)
    · exact (ex_ifz_ne (by norm_num) (by rw [h0]; exact hop)
        (nonGenB_spec I hv hi hop hg hW h0 h1 h2) (by wf_tac)).mono (by omega)
  have h := ex_assign 0 2 (w := w) (L := I.L0 ++ tbl ++ dat) ⨾
    ex_addV 0 9 0 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 2) (by rsimp [h9]) (by rsimp) ⨾
    ex_loadV 0 0 (i := 10 + I.LS + I.LK + 11 * i + 2) (v := I.prog[i].1) (by rsimp)
      (by rw [hins 2 (by norm_num)]; rfl) ⨾
    ex_assign 1 5 ⨾
    ex_addV 1 9 1 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 5) (by rsimp [h9]) (by rsimp) ⨾
    ex_loadV 1 1 (i := 10 + I.LS + I.LK + 11 * i + 5) (v := I.prog[i].2.1) (by rsimp)
      (by rw [hins 5 (by norm_num)]; rfl) ⨾
    ex_assign 2 8 ⨾
    ex_addV 2 9 2 (a := 16 + (10 + I.LS + I.LK) + 11 * i) (b := 8) (by rsimp [h9]) (by rsimp) ⨾
    ex_loadV 2 2 (i := 10 + I.LS + I.LK + 11 * i + 8) (v := I.prog[i].2.2.1) (by rsimp)
      (by rw [hins 8 (by norm_num)]; rfl) ⨾
    hbr _ (by rsimp) (by rsimp) (by rsimp)
      ((((((((((hr.update (z := 0) (by omega) 2).update (z := 0) (by omega) _).update
        (z := 0) (by omega) _).update (z := 1) (by omega) 5).update (z := 1) (by omega) _).update
        (z := 1) (by omega) _).update (z := 2) (by omega) 8).update (z := 2) (by omega) _).update
        (z := 2) (by omega) _)) ⨾
    htail
  exact h.mono (by omega)

/-! ## The evaluation phase -/

/-- The state after the evaluation: every element of the sequence is in the table. -/
def EDone (I : Inp) (m : Mem) : Prop :=
  ∃ w tbl dat, m = memAt 16 w (I.L0 ++ tbl ++ dat) ∧ EGood I I.prog.length tbl dat ∧
    ERegs I I.prog.length (I.L0 ++ tbl ++ dat) w

/-- **The evaluation phase.** -/
theorem evalPhase_spec (I : Inp) (hv : SLPValid I.n I.S I.prog) :
    RunsTo evalPhase
      (fun m => ∃ w tbl, m = memAt 16 w (I.L0 ++ tbl) ∧ tbl.length = I.LP + I.LS ∧
        (∀ j < I.S.length, tbl.getD (I.LP + j) 0 = 23 + (2 * I.n + 1) * j) ∧
        w 8 = 17 + I.Ez + (I.LP + I.LS) ∧ w 13 = I.n ∧ w 14 = 17 + I.Ez ∧ w 15 = I.LP ∧
        w 5 = 16 + (8 + I.LS + I.LK))
      (EDone I) (4 + (I.LP * (18 * I.n + 38) + 1)) := by
  have hLP := I.LP_eq
  have hlen := I.length_L0
  have hloop := runsTo_whileNz (i := 11) (inv := EInv I) (μ := fun m => m 11) (N := I.LP)
    (evalBody_spec I hv) (fun m hm => by
      obtain ⟨i, w, tbl, dat, hm', -, -, -, -, h11, -⟩ := hm
      show m 11 ≤ _
      rw [hm', memAt_of_lt _ _ (by norm_num), h11]; omega)
  refine runsTo_of_exists_St (by wf_tac) (fun m hm => ?_)
  obtain ⟨w, tbl, hm', htl, hgen, h8, h13, h14, h15, h5⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have h := ex_assign 0 2 (w := w) (L := I.L0 ++ tbl) ⨾
    ex_addV 9 5 0 (a := 16 + (8 + I.LS + I.LK)) (b := 2) (by rsimp [h5]) (by rsimp) ⨾
    ex_copyV 11 15 (a := I.LP) (by rsimp [h15]) ⨾
    ex_copyV 12 14 (a := 17 + I.Ez) (by rsimp [h14]) ⨾
    hloop.strengthen (fun m hm => ⟨0, _, tbl, [], hm.to (by simp), by omega,
      ⟨htl, hgen, fun j hj => absurd hj (by omega), by simp⟩,
      by rsimp [h8, htl, hlen], by rsimp, by rsimp, by rsimp, by rsimp [h13], by rsimp [h14],
      by rsimp [h15]⟩)
  refine (h.weaken (fun m hm => ?_)).mono
    (by rw [show 18 * I.n + 36 + 2 = 18 * I.n + 38 by omega]; omega)
  obtain ⟨⟨i, w', tbl', dat', hm'', hile, hg, hr⟩, h0⟩ := hm
  have : i = I.prog.length := by
    rw [hm'', memAt_of_lt _ _ (by norm_num), hr.2.2.1] at h0; omega
  subst this
  exact ⟨w', tbl', dat', hm'', hg, hr⟩

end SLPRAM
end Algo