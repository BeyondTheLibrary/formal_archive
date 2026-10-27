import Workspace.Algo.SLPEvalProg

/-!
# The straight-line-program evaluator: setup, the empty case and the generator table

Specifications of the first phases of `Algo.SLPRAM.slpEvalProg`, in the exact-state style of
`Workspace/Machine/LayoutExact.lean`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Algo
namespace SLPRAM

open RAM Layout LX

section Setup

variable (n : ℕ) (S K : RawGens)

/-- **Setup.** -/
theorem setup_spec (E : ℕ) (T : List ℕ) :
    RunsTo setup (St (fun _ => 0) (headW n S K E ++ T))
      (fun m => ∃ w, m = memAt 16 w (headW n S K E ++ T) ∧ w 13 = n ∧ w 14 = 17 + E ∧
        w 8 = 17 + E ∧ w 5 = 16 + (8 + (Enc.encode S).length + (Enc.encode K).length) ∧
        w 3 = T.getD 1 0) 13 := by
  have hLK := headW_getD_LK n S K E T
  have hTag := headW_getD_tail n S K E T 1
  have h := (ex_loadFix 13 3 (w := fun _ => 0) (L := headW n S K E ++ T)).seq
    ((ex_loadFix 14 0).seq ((ex_assign 0 17).seq ((ex_add 14 14 0).seq ((ex_copy 8 14).seq
    ((ex_loadFix 1 5).seq ((ex_assign 0 22).seq ((ex_add 1 1 0).seq
    ((ex_load 2 1 (i := 6 + (Enc.encode S).length) (by
        simp [Mem.update, -List.getD_eq_getElem?_getD, headW_getD_LS]; omega)).seq
    ((ex_add 5 1 2).seq ((ex_assign 0 2).seq ((ex_add 5 5 0).seq
    (ex_load 3 5 (i := 7 + (Enc.encode S).length + (Enc.encode K).length + 1) (by
        simp [Mem.update, -List.getD_eq_getElem?_getD, headW_getD_LS, hLK]; omega)))))))))))))
  refine (h.weaken (fun m hm => ⟨_, hm, ?_, ?_, ?_, ?_, ?_⟩)).mono (by norm_num) <;>
    simp [Mem.update, -List.getD_eq_getElem?_getD, headW_getD_LS, headW_getD_n, headW_getD_zero, hLK, hTag] <;> omega

/-- The final move from an exact state. -/
theorem ex_finish {w : Mem} {L L₀ B : List ℕ} (hL : L = L₀ ++ B) (h11 : w 11 = 16 + L₀.length)
    (h12 : w 12 = B.length) :
    RunsTo (finish 16) (St w L) (fun m' => m' = memAt 16 (fun _ => 0) B)
      (7 * B.length + 5 * L₀.length + 16 + 17) := by
  subst hL
  exact (runsTo_finish (K := 16) (Q := fun v => v = w) (le_refl _)
    (fun v hv => by subst hv; exact ⟨h11, h12⟩)).strengthen (fun m hm => ⟨w, rfl, hm⟩)

/-- **The empty case**: from the state after `setup`, with tag `0`, the answer `none`. -/
theorem noneBranch_spec {w : Mem} {L : List ℕ} (h8 : w 8 = 16 + L.length) :
    RunsTo noneBranch (St w L)
      (fun m' => m' = initMemAt 16 (Enc.encode (none : RawCoset))) (5 * L.length + 64) := by
  have h := ex_copy 11 8 (w := w) (L := L) ⨾ ex_assign 0 1 ⨾
    ex_push 0 (by simp [Mem.update, -List.getD_eq_getElem?_getD, h8]) ⨾ ex_assign 0 0 ⨾
    ex_push 0 (by simp [Mem.update, -List.getD_eq_getElem?_getD, h8] <;> omega) ⨾
    ex_assign 12 2 ⨾ ex_finish (L₀ := L) (B := [1, 0])
      (by simp [Mem.update, -List.getD_eq_getElem?_getD])
      (by simp [Mem.update, -List.getD_eq_getElem?_getD, h8])
      (by simp [Mem.update, -List.getD_eq_getElem?_getD])
  refine (h.weaken (fun m hm => ?_)).mono (by simp; omega)
  rw [hm, initMemAt_eq_memAt]
  rfl

end Setup

/-! ## The input with a program -/

/-- The data of an input with a program. -/
structure Inp where
  n : ℕ
  S : RawGens
  K : RawGens
  prog : List RawSLPInstr
  σ : ℕ

namespace Inp

variable (I : Inp)

/-- The input. -/
def z : ObsHdr × Option RawSLP := ((I.n, (I.S, I.K)), some (I.prog, I.σ))

/-- Word lengths of the generators, the kernel generators and the program. -/
def LS : ℕ := (Enc.encode I.S).length
def LK : ℕ := (Enc.encode I.K).length
def LP : ℕ := (Enc.encode I.prog).length
/-- The word length of the input. -/
def Ez : ℕ := (Enc.encode I.z).length
/-- The words after the kernel generators. -/
def Tl : List ℕ := [I.LP + 4, 1, I.LP] ++ Enc.encode I.prog ++ [1, I.σ]
/-- The input words. -/
def L0 : List ℕ := headW I.n I.S I.K I.Ez ++ I.Tl

theorem L0_eq : I.L0 = inWords I.z := by
  rw [L0, Tl, LP, Ez, z, inWords_some]

theorem length_L0 : I.L0.length = I.Ez + 1 := by
  rw [L0_eq, inWords, List.length_cons, Ez]

theorem length_L0' : I.L0.length = 12 + I.LS + I.LK + I.LP := by
  rw [L0, List.length_append, length_headW, Tl]; simp [LS, LK, LP]; omega

theorem getD_n : I.L0.getD 3 0 = I.n := headW_getD_n _ _ _ _ _

theorem getD_zero : I.L0.getD 0 0 = I.Ez := headW_getD_zero _ _

theorem getD_LS : I.L0.getD 5 0 = I.LS := headW_getD_LS _ _ _ _ _

theorem getD_LK : I.L0.getD (6 + I.LS) 0 = I.LK := headW_getD_LK _ _ _ _ _

theorem getD_tail (k : ℕ) : I.L0.getD (7 + I.LS + I.LK + k) 0 = I.Tl.getD k 0 :=
  headW_getD_tail _ _ _ _ _ k

theorem getD_tag : I.L0.getD (8 + I.LS + I.LK) 0 = 1 := by
  have := I.getD_tail 1
  rw [show 7 + I.LS + I.LK + 1 = 8 + I.LS + I.LK by omega] at this
  rw [this, Tl]; simp

theorem getD_LP : I.L0.getD (9 + I.LS + I.LK) 0 = I.LP := by
  have := I.getD_tail 2
  rw [show 7 + I.LS + I.LK + 2 = 9 + I.LS + I.LK by omega] at this
  rw [this, Tl]; simp

end Inp

/-- **Allocation of the table.** -/
theorem allocT_spec (I : Inp) {w : Mem} (h8 : w 8 = 17 + I.Ez)
    (h5 : w 5 = 16 + (8 + I.LS + I.LK)) :
    RunsTo allocT (St w I.L0)
      (fun m => ∃ w', m = memAt 16 w' (I.L0 ++ List.replicate (I.LP + I.LS) 0) ∧
        w' 8 = 17 + I.Ez + (I.LP + I.LS) ∧ w' 15 = I.LP ∧ ∀ z, z ≠ 0 → z ≠ 6 → z ≠ 8 → z ≠ 15 →
          w' z = w z) 6 := by
  have hLP := I.getD_LP
  have hLS := I.getD_LS
  have hlen := I.length_L0'
  have hLS' : (I.L0 ++ List.replicate I.LP 0).getD 5 0 = I.LS := by
    rw [List.getD_append _ _ _ _ (by omega), hLS]
  have h := ex_assign 0 1 (w := w) (L := I.L0) ⨾
    ex_addV 6 5 0 (a := 16 + (8 + I.LS + I.LK)) (b := 1) (by rsimp [h5]) (by rsimp) ⨾
    ex_loadV 15 6 (i := 9 + I.LS + I.LK) (by rsimp) hLP ⨾
    ex_advanceV 15 (t := 17 + I.Ez) (j := I.LP) (by rsimp [h8]) (by rsimp) ⨾ ex_loadFixV 0 5 hLS' ⨾
    ex_advanceV 0 (t := 17 + I.Ez + I.LP) (j := I.LS) (by rsimp) (by rsimp)
  refine (h.weaken (fun m hm => ⟨_, hm.to ?_, ?_, ?_, ?_⟩)).mono (by norm_num)
  · rw [List.append_assoc, ← List.replicate_add]
  · rsimp
  · rsimp
  · intro z h0 h6 h8 h15
    rsimp [h0, h6, h8, h15]

/-! ## The generator table -/

/-- The invariant of the generator loop after `j` generators. -/
def GInv (I : Inp) (m : Mem) : Prop :=
  ∃ j w tbl, m = memAt 16 w (I.L0 ++ tbl) ∧ tbl.length = I.LP + I.LS ∧
    (∀ j' < j, tbl.getD (I.LP + j') 0 = 23 + (2 * I.n + 1) * j') ∧
    (2 * I.n + 1) * j ≤ I.LS ∧
    w 9 = 22 + (2 * I.n + 1) * j ∧ w 11 = I.LS - (2 * I.n + 1) * j ∧
    w 12 = 17 + I.Ez + I.LP + j ∧ w 2 = 2 * I.n + 1 ∧ w 8 = 17 + I.Ez + (I.LP + I.LS) ∧
    w 13 = I.n ∧ w 14 = 17 + I.Ez ∧ w 15 = I.LP ∧ w 5 = 16 + (8 + I.LS + I.LK)

theorem genBody_spec (I : Inp) (hLS : I.LS = (2 * I.n + 1) * I.S.length) (N : ℕ) :
    RunsTo genBody (fun m => GInv I m ∧ m 11 ≠ 0 ∧ m 11 = N)
      (fun m => GInv I m ∧ m 11 < N) 6 := by
  refine runsTo_of_exists_St (wf_seq (wf_assign _ _) (wf_seq (wf_addTo _ _ _) (wf_seq
    (wf_storeTo _ _) (wf_seq (wf_addTo _ _ _) (wf_seq (wf_subTo _ _ _) (wf_addTo _ _ _))))))
    (fun m hm => ?_)
  obtain ⟨⟨j, w, tbl, hm', htl, htb, hjS, h9, h11, h12, h2, h8, h13, h14, h15, h5⟩, hne, hN⟩ :=
    hm
  refine ⟨w, _, hm', ?_⟩
  have hL := I.length_L0
  have h11' : m 11 = w 11 := by rw [hm', memAt_of_lt _ _ (by norm_num)]
  have hlt : (2 * I.n + 1) * j < I.LS := by
    rw [h11', h11] at hne; omega
  have hjlt : j < I.LS := lt_of_le_of_lt (Nat.le_mul_of_pos_left j (by omega)) hlt
  have h := ex_assign 0 1 (w := w) (L := I.L0 ++ tbl) ⨾
    ex_addV 1 9 0 (a := 22 + (2 * I.n + 1) * j) (b := 1) (by rsimp [h9]) (by rsimp) ⨾
    ex_storeV 12 1 (i := I.L0.length + (I.LP + j)) (v := 22 + (2 * I.n + 1) * j + 1)
      (by rsimp [h12, hL]) (by rsimp) (by simp; omega) ⨾
    ex_addV 9 9 2 (a := 22 + (2 * I.n + 1) * j) (b := 2 * I.n + 1) (by rsimp [h9])
      (by rsimp [h2]) ⨾
    ex_subV 11 11 2 (a := I.LS - (2 * I.n + 1) * j) (b := 2 * I.n + 1) (by rsimp [h11])
      (by rsimp [h2]) ⨾
    ex_addV 12 12 0 (a := 17 + I.Ez + I.LP + j) (b := 1) (by rsimp [h12]) (by rsimp)
  refine h.weaken (fun m hm => ⟨⟨j + 1, _, tbl.set (I.LP + j) (22 + (2 * I.n + 1) * j + 1),
    hm.to (set_append2 _ _ (by omega) _), by simp [htl], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩)
  · intro j' hj'
    rcases Nat.lt_or_ge j' j with hj'' | hj''
    · rw [getD_set_ne _ (by omega), htb j' hj'']
    · have : j' = j := by omega
      subst this
      rw [getD_set_eq _ (by omega)]; ring
  · have hj : j < I.S.length := by
      rw [hLS] at hlt; exact Nat.lt_of_mul_lt_mul_left hlt
    rw [hLS]; exact Nat.mul_le_mul_left _ hj
  · rsimp; ring
  · rsimp; rw [Nat.mul_succ]; omega
  · rsimp
  · rsimp [h2]
  · rsimp [h8]
  · rsimp [h13]
  · rsimp [h14]
  · rsimp [h15]
  · rsimp [h5]
  · rw [hm, memAt_of_lt _ _ (by norm_num : (11:ℕ) < 16), ← hN, h11', h11]; rsimp

/-- **The generator table**: entry `LP + j` holds the address of generator `j`. -/
theorem genPhase_spec (I : Inp) (hS : RawGens.WF I.n I.S) :
    RunsTo genPhase
      (fun m => ∃ w, m = memAt 16 w (I.L0 ++ List.replicate (I.LP + I.LS) 0) ∧
        w 8 = 17 + I.Ez + (I.LP + I.LS) ∧ w 15 = I.LP ∧ w 13 = I.n ∧ w 14 = 17 + I.Ez ∧
        w 5 = 16 + (8 + I.LS + I.LK))
      (fun m => ∃ w tbl, m = memAt 16 w (I.L0 ++ tbl) ∧ tbl.length = I.LP + I.LS ∧
        (∀ j < I.S.length, tbl.getD (I.LP + j) 0 = 23 + (2 * I.n + 1) * j) ∧
        w 8 = 17 + I.Ez + (I.LP + I.LS) ∧ w 13 = I.n ∧ w 14 = 17 + I.Ez ∧ w 15 = I.LP ∧
        w 5 = 16 + (8 + I.LS + I.LK))
      (7 + (I.LS * 8 + 1)) := by
  have hLS : I.LS = (2 * I.n + 1) * I.S.length := length_encode_gens I.n hS
  have hloop := runsTo_whileNz (i := 11) (inv := GInv I) (μ := fun m => m 11) (N := I.LS)
    (genBody_spec I hLS) (fun m hm => by
      obtain ⟨j, w, tbl, hm', -, -, -, -, h11, -⟩ := hm
      show m 11 ≤ _
      rw [hm', memAt_of_lt _ _ (by norm_num), h11]; omega)
  refine runsTo_of_exists_St ?wf (fun m hm => ?_)
  case wf => exact wf_seq (wf_assign _ _) (wf_seq (wf_copyTo _ _) (wf_seq (wf_addTo _ _ _)
    (wf_seq (wf_copyTo _ _) (wf_seq (wf_addTo _ _ _) (wf_seq (wf_assign _ _)
    (wf_seq (wf_addTo _ _ _) hloop.wf))))))
  obtain ⟨w, hm', h8, h15, h13, h14, h5⟩ := hm
  refine ⟨w, _, hm', ?_⟩
  have hLSr : (I.L0 ++ List.replicate (I.LP + I.LS) 0).getD 5 0 = I.LS := by
    rw [List.getD_append _ _ _ _ (by rw [I.length_L0']; omega), I.getD_LS]
  have h := ex_assign 9 (16 + 6) (w := w) (L := I.L0 ++ List.replicate (I.LP + I.LS) 0) ⨾
    ex_loadFixV 11 5 hLSr ⨾
    ex_addV 12 14 15 (a := 17 + I.Ez) (b := I.LP) (by rsimp [h14]) (by rsimp [h15]) ⨾
    ex_copyV 2 13 (a := I.n) (by rsimp [h13]) ⨾
    ex_addV 2 2 13 (a := I.n) (b := I.n) (by rsimp) (by rsimp [h13]) ⨾
    ex_assign 0 1 ⨾
    ex_addV 2 2 0 (a := I.n + I.n) (b := 1) (by rsimp) (by rsimp) ⨾
    hloop.strengthen (fun m hm => ⟨0, _, List.replicate (I.LP + I.LS) 0, hm, by simp,
      fun j' hj' => absurd hj' (by omega), by omega, by rsimp, by rsimp, by rsimp [I.length_L0],
      by rsimp, by rsimp [h8], by rsimp [h13], by rsimp [h14], by rsimp [h15], by rsimp [h5]⟩)
  refine (h.weaken (fun m hm => ?_)).mono (by omega)
  obtain ⟨⟨j, w', tbl, hm', htl, htb, hjS, -, h11, -, -, h8', h13', h14', h15', h5'⟩, h0⟩ := hm
  have : j = I.S.length := by
    rw [hm', memAt_of_lt _ _ (by norm_num), h11, hLS] at h0
    rw [hLS] at hjS
    have := Nat.le_of_mul_le_mul_left hjS (by omega : 0 < 2 * I.n + 1)
    have h2 : (2 * I.n + 1) * I.S.length ≤ (2 * I.n + 1) * j := by omega
    have := Nat.le_of_mul_le_mul_left h2 (by omega : 0 < 2 * I.n + 1)
    omega
  subst this
  exact ⟨w', tbl, hm', htl, htb, h8', h13', h14', h15', h5'⟩

end SLPRAM
end Algo