import Workspace.Machine.Cases

/-!
# The constructors: `cons` and `some`

`Workspace/Machine/Cases.lean` takes data apart.  A traversal also has to put data together
again: a fold that reverses a list, a map, a filter all build their answer one entry at a time.
This file supplies the two constructors that need machine code.

* `RAM.Lists.consProg`: `(b, l) ↦ b :: l`.  The encoding of the pair is
  `p :: eb ++ (q :: el)` and the encoding of the list is `p :: eb ++ el`, so the routine copies
  the two blocks out with the separator `q` dropped.
* `RAM.Lists.someProg`: `b ↦ some b`.  The encoding of `b` is `eb` and the encoding of `some b`
  is `1 :: eb`, so the routine copies one block out behind a fresh `1`.

Both are `Layout.lean` assemblies of the shape of `RAM.Lists.stripProg`.  The remaining
constructors, `[]` and `none`, are constants (`RAM.polyFun_nil`, `RAM.polyFun_none`).

## Main results

* `RAM.Lists.runsTo_consProg`, `RAM.cleanComputeAt_cons`, `RAM.polyFun_cons`;
* `RAM.Lists.runsTo_someProg`, `RAM.cleanComputeAt_some`, `RAM.polyFun_some`;
* `RAM.polyFun_singleton`, `RAM.polyFun_headOption`.
-/

namespace RAM

variable {α β γ σ : Type*}

namespace Lists

open Layout

/-! ## `cons`

The workspace list of `(b, l)` is `A = (p + q + 2) :: p :: (eb ++ (q :: el))` and the block to be
built is `B = (p + q + 1) :: p :: (eb ++ el)`.  The registers are those of
`RAM.Lists.stripHead`. -/

/-- Read the two lengths and set the pointers. -/
def consHead (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (copyTo 13 (K + 1)) (seq (assign 10 1) (seq (subTo 15 9 10)
    (seq (copyTo 12 9) (seq (subTo 14 9 13) (seq (assign 10 2) (seq (subTo 14 14 10)
      (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1) (seq (addTo 8 8 10)
        (copyTo 11 8))))))))))))

/-- Stack the encoding of the answer on top of the workspace. -/
def consBody (K : ℕ) : Program :=
  seq (pushVal 15) (seq (pushVal 13) (seq (assign 0 K) (seq (assign 10 2)
    (seq (addTo 0 0 10) (seq (copyTo 2 13) (seq pushBlock
      (seq (assign 0 K) (seq (assign 10 3) (seq (addTo 0 0 10) (seq (addTo 0 0 13)
        (seq (copyTo 2 14) pushBlock)))))))))))

/-- The routine `(b, l) ↦ b :: l`. -/
def consProg (K : ℕ) : Program := seq (consHead K) (seq (consBody K) (finish K))

theorem runsTo_consHead {K : ℕ} (hK : 16 ≤ K) {eb el : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : el.length = q) :
    RunsTo (consHead K)
      (At K (fun _ => True) ((p + q + 2) :: p :: (eb ++ (q :: el))))
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 1)
        ((p + q + 2) :: p :: (eb ++ (q :: el)))) 13 := by
  set A : List ℕ := (p + q + 2) :: p :: (eb ++ (q :: el)) with hA
  have hA0 : A.getD 0 0 = p + q + 2 := by rw [hA]; simp
  have hA1 : A.getD 1 0 = p := by rw [hA]; simp
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A)
      (At K (fun v => v 9 = p + q + 2) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by rw [Mem.update_self, hA0])
  have s2 : RunsTo (copyTo 13 (K + 1)) (At K (fun v => v 9 = p + q + 2) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p) A) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 13), hw],
        by rw [Mem.update_self, hA1]⟩)
  have s3 : RunsTo (assign 10 1) (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2],
        by rw [Mem.update_self]⟩)
  have s4 : RunsTo (subTo 15 9 10) (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 15), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 15), hw.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2]; omega⟩)
  have s5 : RunsTo (copyTo 12 9) (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 12), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 12), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 12), hw.2.2],
        by rw [Mem.update_self, hw.1]⟩)
  have s6 : RunsTo (subTo 14 9 13)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q + 2) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 14), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 14), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 14), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 14), hw.2.2.2],
        by rw [Mem.update_self, hw.1, hw.2.1]; omega⟩)
  have s7 : RunsTo (assign 10 2)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q + 2) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q + 2 ∧ v 10 = 2) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 10), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 10), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s8 : RunsTo (subTo 14 14 10)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q + 2 ∧ v 10 = 2) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 14), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 14), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 14), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 14), hw.2.2.2.1],
        by rw [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]; omega⟩)
  have s9 : RunsTo (assign 8 K)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q) A)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s10 : RunsTo (addTo 8 8 9)
      (At K (fun v => v 9 = p + q + 2 ∧ v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧
        v 14 = q ∧ v 8 = K) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 2)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2.2.2.2]⟩)
  have s11 : RunsTo (assign 10 1)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 2)) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 2) ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 10), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 10), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s12 : RunsTo (addTo 8 8 10)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 2) ∧ v 10 = 1) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]; omega⟩)
  have s13 : RunsTo (copyTo 11 8)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 1 ∧ v 12 = p + q + 2 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3)) A)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 1) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 11), hw.2.2.2.2],
        by rw [Mem.update_self, hw.2.2.2.2],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 11), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 11), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 11), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 11), hw.2.1]⟩)
  have c12 := s12.seq s13
  have c11 := s11.seq c12
  have c10 := s10.seq c11
  have c9 := s9.seq c10
  have c8 := s8.seq c9
  have c7 := s7.seq c8
  have c6 := s6.seq c7
  have c5 := s5.seq c6
  have c4 := s4.seq c5
  have c3 := s3.seq c4
  have c2 := s2.seq c3
  exact (s1.seq c2).mono (by omega)

set_option maxHeartbeats 1000000 in
theorem runsTo_consBody {K : ℕ} (hK : 16 ≤ K) {eb el : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : el.length = q) :
    RunsTo (consBody K)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 1)
        ((p + q + 2) :: p :: (eb ++ (q :: el))))
      (At K (fun v => v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2)
        (((p + q + 2) :: p :: (eb ++ (q :: el))) ++ ((p + q + 1) :: p :: (eb ++ el))))
      (7 * p + 7 * q + 29) := by
  set A : List ℕ := (p + q + 2) :: p :: (eb ++ (q :: el)) with hA
  have hAlen : A.length = p + q + 3 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hA2 : A.drop 2 = eb ++ (q :: el) := by rw [hA]; simp
  have hseg1 : (A.drop 2).take p = eb := by rw [hA2, ← hp, List.take_left]
  have hdropA : A.drop (3 + p) = el := by
    have h1 : A = ((p + q + 2) :: p :: (eb ++ [q])) ++ el := by rw [hA]; simp
    have h2 : ((p + q + 2) :: p :: (eb ++ [q])).length = 3 + p := by
      simp [hp]; all_goals omega
    rw [h1, ← h2, List.drop_left]
  have hseg2 : (A.drop (3 + p)).take q = el := by rw [hdropA, ← hq, List.take_length]
  set L1 : List ℕ := A ++ [p + q + 1] with hL1
  set L2 : List ℕ := L1 ++ [p] with hL2
  set L3 : List ℕ := L2 ++ eb with hL3
  set L4 : List ℕ := L3 ++ el with hL4
  have hL1len : L1.length = p + q + 4 := by rw [hL1]; simp [hAlen]
  have hL2len : L2.length = p + q + 5 := by rw [hL2]; simp [hL1len]
  have hL3len : L3.length = p + q + 5 + p := by rw [hL3]; simp [hL2len, hp]; all_goals omega
  have hfinal : L4 = A ++ ((p + q + 1) :: p :: (eb ++ el)) := by
    rw [hL4, hL3, hL2, hL1]
    simp [List.append_assoc]
  have s1 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 1) A)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q) L1) 3 := by
    refine runsTo_pushVal (L := A) (v := p + q + 1) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hAlen], hw.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2.1]
  have s2 : RunsTo (pushVal 13)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q) L1)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q) L2) 3 := by
    refine runsTo_pushVal (L := L1) (v := p) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL1len], hw.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL1len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2]
  have s3 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q) L2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s4 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s5 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L2) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s6 : RunsTo (copyTo 2 13)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2 ∧ v 2 = p) L2) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL2 : (L2.drop 2).take p = eb := by
    rw [hL2, seg_append L1 [p] 2 p (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 1] 2 p (by rw [hAlen]; omega), hseg1]
  have s7 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2 ∧ v 2 = p) L2)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q) L3) (7 * p + 7) := by
    have hlist : L3 = L2 ++ (L2.drop 2).take p := by rw [hsegL2, hL3]
    rw [hlist]
    refine runsTo_pushBlock (L := L2) hK (i := 2) (c := p) (by rw [hL2len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL2len], hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL2len]; omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.1]
  have s8 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L3) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s9 : RunsTo (assign 10 3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 3) L3) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s10 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 3) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 3) L3) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s11 : RunsTo (addTo 0 0 13)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 3) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 14 = q ∧ v 0 = K + (3 + p)) L3) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2, hw.2.2.2.1]
      omega)
  have s12 : RunsTo (copyTo 2 14)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 14 = q ∧ v 0 = K + (3 + p)) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 0 = K + (3 + p) ∧ v 2 = q) L3) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL3 : (L3.drop (3 + p)).take q = el := by
    rw [hL3, seg_append L2 eb (3 + p) q (by rw [hL2len]; omega),
      hL2, seg_append L1 [p] (3 + p) q (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 1] (3 + p) q (by rw [hAlen]; omega), hseg2]
  have s13 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 3) ∧
        v 12 = p + q + 2 ∧ v 0 = K + (3 + p) ∧ v 2 = q) L3)
      (At K (fun v => v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2) L4) (7 * q + 7) := by
    have hlist : L4 = L3 ++ (L3.drop (3 + p)).take q := by rw [hsegL3, hL4]
    rw [hlist]
    refine runsTo_pushBlock (L := L3) hK (i := 3 + p) (c := q) (by rw [hL3len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL3len], hw.2.2.2.1, hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have c12 := s12.seq s13
  have c11 := s11.seq c12
  have c10 := s10.seq c11
  have c9 := s9.seq c10
  have c8 := s8.seq c9
  have c7 := s7.seq c8
  have c6 := s6.seq c7
  have c5 := s5.seq c6
  have c4 := s4.seq c5
  have c3 := s3.seq c4
  have c2 := s2.seq c3
  have hmain := s1.seq c2
  rw [← hfinal]
  exact hmain.mono (by omega)

set_option maxHeartbeats 1000000 in
/-- **`cons`.**  From the workspace holding the encoding of `(b, l)` the routine produces the
workspace holding the encoding of `b :: l`. -/
theorem runsTo_consProg {K : ℕ} (hK : 16 ≤ K) {eb el : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : el.length = q) :
    RunsTo (consProg K)
      (fun m => m = initMemAt K (p :: (eb ++ (q :: el))))
      (fun m' => m' = initMemAt K (p :: (eb ++ el)))
      (19 * p + 19 * q + K + 88) := by
  set A : List ℕ := (p + q + 2) :: p :: (eb ++ (q :: el)) with hA
  set B : List ℕ := (p + q + 1) :: p :: (eb ++ el) with hB
  have hAlen : A.length = p + q + 3 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hBlen : B.length = p + q + 2 := by rw [hB]; simp [hp, hq]; all_goals omega
  have hin : initMemAt K (p :: (eb ++ (q :: el))) = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA]
    congr 1
    simp [hp, hq]
    all_goals omega
  have hout : initMemAt K (p :: (eb ++ el)) = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB]
    congr 1
    simp [hp, hq]
    all_goals omega
  have sfin : RunsTo (finish K)
      (At K (fun v => v 11 = K + (p + q + 3) ∧ v 12 = p + q + 2) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (p + q + 2) + 5 * (p + q + 3) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hBlen]
    · rw [hAlen, hBlen]
  have hmain := (runsTo_consHead hK hp hq).seq ((runsTo_consBody hK hp hq).seq sfin)
  refine hmain.conseq (fun m hm => ?_) (fun m hm => ?_) (by omega)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

/-! ## `some`

The workspace list of `b` is `A = p :: eb` and the block to be built is `B = (p + 1) :: 1 :: eb`.
Register `9` holds `p` throughout, `13` holds the constant `1`. -/

/-- Read the length and set the pointers. -/
def someHead (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (assign 10 1) (seq (addTo 15 9 10) (seq (copyTo 13 10)
    (seq (assign 10 2) (seq (addTo 12 9 10) (seq (assign 8 K) (seq (addTo 8 8 9)
      (seq (assign 10 1) (seq (addTo 8 8 10) (copyTo 11 8))))))))))

/-- Stack the encoding of the answer on top of the workspace. -/
def someBody (K : ℕ) : Program :=
  seq (pushVal 15) (seq (pushVal 13) (seq (assign 0 K) (seq (assign 10 1)
    (seq (addTo 0 0 10) (seq (copyTo 2 9) pushBlock)))))

/-- The routine `b ↦ some b`. -/
def someProg (K : ℕ) : Program := seq (someHead K) (seq (someBody K) (finish K))

theorem runsTo_someHead {K : ℕ} (hK : 16 ≤ K) {eb : List ℕ} {p : ℕ} (hp : eb.length = p) :
    RunsTo (someHead K)
      (At K (fun _ => True) (p :: eb))
      (At K (fun v => v 8 = K + (p + 1) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 15 = p + 1 ∧ v 9 = p) (p :: eb)) 11 := by
  set A : List ℕ := p :: eb with hA
  have hA0 : A.getD 0 0 = p := by rw [hA]; simp
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A) (At K (fun v => v 9 = p) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by rw [Mem.update_self, hA0])
  have s2 : RunsTo (assign 10 1) (At K (fun v => v 9 = p) A)
      (At K (fun v => v 9 = p ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw], by rw [Mem.update_self]⟩)
  have s3 : RunsTo (addTo 15 9 10) (At K (fun v => v 9 = p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p ∧ v 10 = 1 ∧ v 15 = p + 1) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 15), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (10:ℕ) ≠ 15), hw.2],
        by rw [Mem.update_self, hw.1, hw.2]⟩)
  have s4 : RunsTo (copyTo 13 10) (At K (fun v => v 9 = p ∧ v 10 = 1 ∧ v 15 = p + 1) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 13), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 13), hw.2.2],
        by rw [Mem.update_self, hw.2.1]⟩)
  have s5 : RunsTo (assign 10 2) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 10 = 2) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2.2],
        by rw [Mem.update_self]⟩)
  have s6 : RunsTo (addTo 12 9 10) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 10 = 2) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 12 = p + 2) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 12), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 12), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 12), hw.2.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2.2]⟩)
  have s7 : RunsTo (assign 8 K) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 12 = p + 2) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 12 = p + 2 ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2],
        by rw [Mem.update_self]⟩)
  have s8 : RunsTo (addTo 8 8 9) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 12 = p + 2 ∧ v 8 = K) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 12 = p + 2 ∧ v 8 = K + p) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2.2.2]⟩)
  have s9 : RunsTo (assign 10 1) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 12 = p + 2 ∧ v 8 = K + p) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 12 = p + 2 ∧ v 8 = K + p ∧
        v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 10), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s10 : RunsTo (addTo 8 8 10) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 12 = p + 2 ∧ v 8 = K + p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧ v 12 = p + 2 ∧
        v 8 = K + (p + 1)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]; omega⟩)
  have s11 : RunsTo (copyTo 11 8) (At K (fun v => v 9 = p ∧ v 15 = p + 1 ∧ v 13 = 1 ∧
        v 12 = p + 2 ∧ v 8 = K + (p + 1)) A)
      (At K (fun v => v 8 = K + (p + 1) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 15 = p + 1 ∧ v 9 = p) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 11), hw.2.2.2.2],
        by rw [Mem.update_self, hw.2.2.2.2],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 11), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 11), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 11), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 11), hw.1]⟩)
  have c10 := s10.seq s11
  have c9 := s9.seq c10
  have c8 := s8.seq c9
  have c7 := s7.seq c8
  have c6 := s6.seq c7
  have c5 := s5.seq c6
  have c4 := s4.seq c5
  have c3 := s3.seq c4
  have c2 := s2.seq c3
  exact (s1.seq c2).mono (by omega)

set_option maxHeartbeats 1000000 in
theorem runsTo_someBody {K : ℕ} (hK : 16 ≤ K) {eb : List ℕ} {p : ℕ} (hp : eb.length = p) :
    RunsTo (someBody K)
      (At K (fun v => v 8 = K + (p + 1) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 15 = p + 1 ∧ v 9 = p) (p :: eb))
      (At K (fun v => v 11 = K + (p + 1) ∧ v 12 = p + 2)
        ((p :: eb) ++ ((p + 1) :: 1 :: eb)))
      (7 * p + 17) := by
  set A : List ℕ := p :: eb with hA
  have hAlen : A.length = p + 1 := by rw [hA]; simp [hp]
  have hseg1 : (A.drop 1).take p = eb := by rw [hA]; simp [← hp]
  set L1 : List ℕ := A ++ [p + 1] with hL1
  set L2 : List ℕ := L1 ++ [1] with hL2
  set L3 : List ℕ := L2 ++ eb with hL3
  have hL1len : L1.length = p + 2 := by rw [hL1]; simp [hAlen]
  have hL2len : L2.length = p + 3 := by rw [hL2]; simp [hL1len]
  have hfinal : L3 = A ++ ((p + 1) :: 1 :: eb) := by
    rw [hL3, hL2, hL1]; simp [List.append_assoc]
  have s1 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + (p + 1) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 15 = p + 1 ∧ v 9 = p) A)
      (At K (fun v => v 8 = K + (p + 2) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 9 = p) L1) 3 := by
    refine runsTo_pushVal (L := A) (v := p + 1) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hAlen], hw.2.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 9 (by omega) (by omega), hw.2.2.2.2.2]
  have s2 : RunsTo (pushVal 13)
      (At K (fun v => v 8 = K + (p + 2) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 13 = 1 ∧ v 9 = p) L1)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p) L2) 3 := by
    refine runsTo_pushVal (L := L1) (v := 1) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL1len], hw.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_⟩)
    · rw [h8, hL1len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 9 (by omega) (by omega), hw.2.2.2.2]
  have s3 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p) L2)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s4 : RunsTo (assign 10 1)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K) L2)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K ∧ v 10 = 1) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s5 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K ∧ v 10 = 1) L2)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K + 1) L2) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s6 : RunsTo (copyTo 2 9)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧ v 9 = p ∧
        v 0 = K + 1) L2)
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 0 = K + 1 ∧ v 2 = p) L2) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL2 : (L2.drop 1).take p = eb := by
    rw [hL2, seg_append L1 [1] 1 p (by rw [hL1len]; omega),
      hL1, seg_append A [p + 1] 1 p (by rw [hAlen]; omega), hseg1]
  have s7 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + 3) ∧ v 11 = K + (p + 1) ∧ v 12 = p + 2 ∧
        v 0 = K + 1 ∧ v 2 = p) L2)
      (At K (fun v => v 11 = K + (p + 1) ∧ v 12 = p + 2) L3) (7 * p + 7) := by
    have hlist : L3 = L2 ++ (L2.drop 1).take p := by rw [hsegL2, hL3]
    rw [hlist]
    refine runsTo_pushBlock (L := L2) hK (i := 1) (c := p) (by rw [hL2len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL2len], hw.2.2.2.1, hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have c6 := s6.seq s7
  have c5 := s5.seq c6
  have c4 := s4.seq c5
  have c3 := s3.seq c4
  have c2 := s2.seq c3
  have hmain := s1.seq c2
  rw [← hfinal]
  exact hmain.mono (by omega)

set_option maxHeartbeats 1000000 in
/-- **`some`.**  From the workspace holding the encoding of `b` the routine produces the
workspace holding the encoding of `some b`. -/
theorem runsTo_someProg {K : ℕ} (hK : 16 ≤ K) {eb : List ℕ} {p : ℕ} (hp : eb.length = p) :
    RunsTo (someProg K)
      (fun m => m = initMemAt K eb)
      (fun m' => m' = initMemAt K (1 :: eb))
      (19 * p + K + 64) := by
  set A : List ℕ := p :: eb with hA
  set B : List ℕ := (p + 1) :: 1 :: eb with hB
  have hAlen : A.length = p + 1 := by rw [hA]; simp [hp]
  have hBlen : B.length = p + 2 := by rw [hB]; simp [hp]; all_goals omega
  have hin : initMemAt K eb = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA, hp]
  have hout : initMemAt K (1 :: eb) = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB]
    congr 1
    simp [hp]
  have sfin : RunsTo (finish K)
      (At K (fun v => v 11 = K + (p + 1) ∧ v 12 = p + 2) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (p + 2) + 5 * (p + 1) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hBlen]
    · rw [hAlen, hBlen]
  have hmain := (runsTo_someHead hK hp).seq ((runsTo_someBody hK hp).seq sfin)
  refine hmain.conseq (fun m hm => ?_) (fun m hm => ?_) (by omega)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

end Lists

/-! ## The clean classes -/

/-- The encoding of `b :: l` is no larger than the encoding of the pair `(b, l)`: the pair spends
one extra length field on the tail. -/
theorem size_cons_le [Enc β] (b : β) (l : List β) :
    Enc.size (b :: l) ≤ Enc.size ((b, l) : β × List β) := by
  have h1 : Enc.size (b :: l)
      = listSize (frame (Enc.encode b)) + listSize (Enc.encode l) - 1 := by
    show listSize (frame (Enc.encode b) ++ encList Enc.encode l) = _
    rw [listSize_append]
    rfl
  have h2 : Enc.size ((b, l) : β × List β)
      = listSize (frame (Enc.encode b)) + listSize (frame (Enc.encode l)) - 1 := by
    show listSize (frame (Enc.encode b) ++ frame (Enc.encode l)) = _
    rw [listSize_append]
  have h3 : listSize (frame (Enc.encode l))
      = listSize (Enc.encode l) + (Nat.size (Enc.encode l).length + 1) := listSize_frame _
  have h4 : 1 ≤ listSize (frame (Enc.encode b)) := by
    have := length_lt_listSize (frame (Enc.encode b)); omega
  omega

theorem cleanComputeAt_cons [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (Lists.consProg K) (fun p : β × List β => p.1 :: p.2)
      (fun n => 19 * n + K + 88) := by
  rintro ⟨b, l⟩
  have henc1 : Enc.encode ((b, l) : β × List β)
      = (Enc.encode b).length ::
        (Enc.encode b ++ ((Enc.encode l).length :: Enc.encode l)) := by
    show frame (Enc.encode b) ++ frame (Enc.encode l) = _
    simp [frame]
  have henc2 : Enc.encode (b :: l)
      = (Enc.encode b).length :: (Enc.encode b ++ Enc.encode l) := by
    show frame (Enc.encode b) ++ encList Enc.encode l = _
    simp only [frame, List.cons_append, List.nil_append]
    rfl
  have hlen : (Enc.encode ((b, l) : β × List β)).length
      = (Enc.encode b).length + (Enc.encode l).length + 2 := by
    rw [henc1]; simp; all_goals omega
  have hlt : (Enc.encode b).length + (Enc.encode l).length + 2
      < Enc.size ((b, l) : β × List β) := by
    have h1 := length_lt_listSize (Enc.encode ((b, l) : β × List β))
    rw [hlen] at h1
    exact h1
  rw [henc1, henc2]
  refine (Lists.runsTo_consProg hK (rfl : (Enc.encode b).length = _)
    (rfl : (Enc.encode l).length = _)).mono ?_
  dsimp only
  omega

theorem polyTimeCleanAt_cons [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (fun p : β × List β => p.1 :: p.2) :=
  ⟨Lists.consProg K, _, ((polyBound_const 19).mul polyBound_id).add
    (polyBound_const (K + 88)), cleanComputeAt_cons hK⟩

/-- **`cons` is a `PolyFun`.** -/
theorem polyFun_cons [Enc β] : PolyFun (fun p : β × List β => p.1 :: p.2) :=
  ⟨polyTimeCleanAt_cons (by omega),
    SizeBound.of_le (g := id) SizeBound.id' (fun p => size_cons_le p.1 p.2)⟩

theorem size_some_eq [Enc β] (b : β) : Enc.size (some b) = Enc.size b + 2 := by
  show listSize (1 :: Enc.encode b) = listSize (Enc.encode b) + 2
  rw [listSize_cons]
  simp

theorem cleanComputeAt_some [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (Lists.someProg K) (Option.some : β → Option β)
      (fun n => 19 * n + K + 64) := by
  intro b
  have henc : Enc.encode (some b) = 1 :: Enc.encode b := rfl
  rw [henc]
  refine (Lists.runsTo_someProg hK (rfl : (Enc.encode b).length = _)).mono ?_
  have h1 := length_lt_listSize (Enc.encode b)
  have h2 : Enc.size b = listSize (Enc.encode b) := rfl
  dsimp only
  omega

theorem polyTimeCleanAt_some [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (Option.some : β → Option β) :=
  ⟨Lists.someProg K, _, ((polyBound_const 19).mul polyBound_id).add
    (polyBound_const (K + 64)), cleanComputeAt_some hK⟩

/-- **`some` is a `PolyFun`.** -/
theorem polyFun_some [Enc β] : PolyFun (Option.some : β → Option β) := by
  refine ⟨polyTimeCleanAt_some (by omega), ⟨3, 1, fun b => ?_⟩⟩
  have h1 : Enc.size (some b) = Enc.size b + 2 := size_some_eq b
  have h2 : 3 * (Enc.size b + 1) ^ 1 = 3 * Enc.size b + 3 := by ring
  omega

/-! ## Two immediate consequences -/

/-- The one-entry list. -/
theorem polyFun_singleton [Enc β] : PolyFun (fun b : β => [b]) :=
  (polyFun_id.pair polyFun_nil).comp polyFun_cons

/-- The head of a list as an `Option`. -/
theorem polyFun_headOption [Enc α] : PolyFun (fun l : List α => l.head?) := by
  have hpair : PolyFun (fun l : List α => (l, (0 : ℕ))) :=
    polyFun_id.pair (polyFun_const 0)
  have hcases : PolyFun (fun p : List α × ℕ =>
      match p.1 with
      | [] => (none : Option α)
      | a :: _ => some a) :=
    PolyFun.listCases (polyFun_const (none : Option α))
      ((polyFun_fst.comp polyFun_fst).comp polyFun_some)
  refine (hpair.comp hcases).of_eq (fun l => ?_)
  cases l <;> rfl

end RAM
