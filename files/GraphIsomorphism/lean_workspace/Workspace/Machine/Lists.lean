import Workspace.Machine.PolyFun

/-!
# Taking a list apart: `uncons`

Every list routine of the paper — the length of a list of points, a lookup in an array, a fold
over a list of generators — has to take a list apart, and none of them can be obtained from
bounded iteration, because `RAM.polyTimeCleanAt_iterate` wants the number of rounds to be
*computed* by a routine, and for a traversal that number is the length.  So the destructor comes
first.  This file builds it.

## What the encodings look like

A list is encoded by concatenating the framed encodings of its entries (`RAM.encList`,
`Workspace/Machine/Encoding.lean`).  So for `l = a :: t` with `ea = encode a` and
`et = encode t`,

`encode l = ea.length :: (ea ++ et)`,

and the workspace holds `E.length :: E` for `E = encode l`.  The answer wanted is

`encode (some (a, t)) = 1 :: ea.length :: (ea ++ (et.length :: et))`.

So the routine has nothing to decode: it reads the frame length `ea.length` out of the register
just above the length field, and copies the two pieces out with one extra separator between
them.  The length of the tail is `E.length - 1 - ea.length`, which two subtractions give.

## The program

`RAM.Lists.unconsProg K` is a conditional on the length field, which sits in register `K`.

* The list is empty.  The answer is `none`, whose encoding is `[0]`, so one instruction suffices:
  `assign K 1` makes register `K` the length field `1`, and the single entry below it is already
  zero.
* The list is not empty.  The block of the answer is stacked on top of the workspace with the
  stage rules of `Workspace/Machine/Layout.lean` — three single values, the head block, the
  length of the tail, the tail block — and moved down to the base by `RAM.Layout.finish`.

## Main results

* `RAM.uncons`, the function;
* `RAM.Lists.runsTo_unconsNE`, `RAM.Lists.runsTo_unconsProg`: the program and its specification;
* `RAM.cleanComputeAt_uncons`, `RAM.polyTimeCleanAt_uncons`, `RAM.polyFun_uncons`.
-/

namespace RAM

/-- The destructor of a list: the head and the tail, or `none` for the empty list. -/
def uncons {α : Type*} : List α → Option (α × List α)
  | [] => none
  | a :: t => some (a, t)

namespace Lists

open Layout

/-! ## The nonempty branch

The workspace list is `A = (p + q + 1) :: p :: (ea ++ et)`, where `ea` is the encoding of the
head, `p` its length, `et` the encoding of the tail and `q` its length.  The block to be built
is `B = (p + q + 3) :: 1 :: p :: (ea ++ (q :: et))`.

The registers, inside the discipline of `Workspace/Machine/Layout.lean` (`0`, `1`, `2` and
`3 .. 7` belong to the copy routines, `8` is the top pointer, `10` holds constants):

| register | holds |
|---|---|
| `9` | the length `p + q + 1`, then the constant `1` to be pushed |
| `11` | the base of the block, for `RAM.Layout.finish` |
| `12` | the length of the block, for `RAM.Layout.finish` |
| `13` | `p` |
| `14` | `q` |
| `15` | `p + q + 3`, the length field of the answer |
-/

/-- Read the two lengths and set the pointers. -/
def unconsHead (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (copyTo 13 (K + 1)) (seq (assign 10 1) (seq (subTo 14 9 10)
    (seq (subTo 14 14 13) (seq (assign 10 2) (seq (addTo 15 9 10) (seq (assign 10 3)
      (seq (addTo 12 9 10) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
        (seq (addTo 8 8 10) (copyTo 11 8)))))))))))))

/-- Stack the encoding of the answer on top of the workspace. -/
def unconsBody (K : ℕ) : Program :=
  seq (pushVal 15) (seq (assign 9 1) (seq (pushVal 9) (seq (pushVal 13)
    (seq (assign 0 K) (seq (assign 10 2) (seq (addTo 0 0 10) (seq (copyTo 2 13)
      (seq pushBlock (seq (pushVal 14) (seq (assign 0 K) (seq (assign 10 2)
        (seq (addTo 0 0 10) (seq (addTo 0 0 13) (seq (copyTo 2 14) pushBlock))))))))))))))

/-- The nonempty branch of `uncons`. -/
def unconsNE (K : ℕ) : Program := seq (unconsHead K) (seq (unconsBody K) (finish K))

/-- `uncons` at the workspace convention: a conditional on the length field. -/
def unconsProg (K : ℕ) : Program := RAM.ifz K (unconsNE K) (assign K 1)

theorem runsTo_unconsHead {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (unconsHead K)
      (At K (fun _ => True) ((p + q + 1) :: p :: (ea ++ et)))
      (At K (fun v => v 8 = K + (p + q + 2) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) ((p + q + 1) :: p :: (ea ++ et))) 14 := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  have hAlen : A.length = p + q + 2 := by
    rw [hA]; simp [hp, hq]; all_goals omega
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A)
      (At K (fun v => v 9 = p + q + 1) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by simp [Mem.update, hA])
  have s2 : RunsTo (copyTo 13 (K + 1)) (At K (fun v => v 9 = p + q + 1) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p) A) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw => by simp [Mem.update, hA, hw])
  have s3 : RunsTo (assign 10 1) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (subTo 14 9 10) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = p + q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2]
      all_goals omega)
  have s5 : RunsTo (subTo 14 14 13) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = p + q) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.1, hw.2.2]
      all_goals omega)
  have s6 : RunsTo (assign 10 2) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 10 = 2) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s7 : RunsTo (addTo 15 9 10)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 10 = 2) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2.2]
      all_goals omega)
  have s8 : RunsTo (assign 10 3)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 10 = 3) A)
      1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s9 : RunsTo (addTo 12 9 10)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 10 = 3) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧
        v 12 = p + q + 4) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2.2.2]
      all_goals omega)
  have s10 : RunsTo (assign 8 K)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧
        v 12 = p + q + 4) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧
        v 12 = p + q + 4 ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s11 : RunsTo (addTo 8 8 9)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧
        v 12 = p + q + 4 ∧ v 8 = K) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 1)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.2.1], by simp [Mem.update, hw.2.2.1],
        by simp [Mem.update, hw.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2.2.2.2])
  have s12 : RunsTo (assign 10 1)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 1)) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 1) ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s13 : RunsTo (addTo 8 8 10)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 1) ∧ v 10 = 1) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 2)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]
      all_goals omega)
  have s14 : RunsTo (copyTo 11 8)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3 ∧ v 12 = p + q + 4 ∧
        v 8 = K + (p + q + 2)) A)
      (At K (fun v => v 8 = K + (p + q + 2) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.2.2.2.2], ?_, by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1]⟩
      simp only [Mem.update_self, hw.2.2.2.2])
  have c13 := s13.seq s14
  have c12 := s12.seq c13
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
theorem runsTo_unconsBody {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (unconsBody K)
      (At K (fun v => v 8 = K + (p + q + 2) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) ((p + q + 1) :: p :: (ea ++ et)))
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4)
        (((p + q + 1) :: p :: (ea ++ et)) ++
          ((p + q + 3) :: 1 :: p :: (ea ++ (q :: et)))))
      (7 * p + 7 * q + 36) := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  have hAlen : A.length = p + q + 2 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hdrop2 : A.drop 2 = ea ++ et := by rw [hA]; simp
  have hseg1 : (A.drop 2).take p = ea := by rw [hdrop2, ← hp, List.take_left]
  have hdropp : A.drop (2 + p) = et := by
    rw [hA, show 2 + p = p + 1 + 1 by omega, List.drop_succ_cons, List.drop_succ_cons,
      ← hp, List.drop_left]
  have hseg2 : (A.drop (2 + p)).take q = et := by rw [hdropp, ← hq, List.take_length]
  -- the intermediate lists
  set L1 : List ℕ := A ++ [p + q + 3] with hL1
  set L2 : List ℕ := L1 ++ [1] with hL2
  set L3 : List ℕ := L2 ++ [p] with hL3
  set L4 : List ℕ := L3 ++ ea with hL4
  set L5 : List ℕ := L4 ++ [q] with hL5
  set L6 : List ℕ := L5 ++ et with hL6
  have hL1len : L1.length = p + q + 3 := by rw [hL1]; simp [hAlen]
  have hL2len : L2.length = p + q + 4 := by rw [hL2]; simp [hL1len]
  have hL3len : L3.length = p + q + 5 := by rw [hL3]; simp [hL2len]
  have hL4len : L4.length = p + q + 5 + p := by rw [hL4]; simp [hL3len, hp]
  have hL5len : L5.length = p + q + 6 + p := by rw [hL5]; simp [hL4len]; omega
  have hfinal : L6 = A ++ ((p + q + 3) :: 1 :: p :: (ea ++ (q :: et))) := by
    rw [hL6, hL5, hL4, hL3, hL2, hL1]
    simp [List.append_assoc]
  have s1 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + (p + q + 2) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 3) A)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L1) 3 := by
    refine runsTo_pushVal (L := A) (v := p + q + 3) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hAlen], hw.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2.1]
  have s2 : RunsTo (assign 9 1)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L1)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 9 = 1) L1) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s3 : RunsTo (pushVal 9)
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 9 = 1) L1)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L2) 3 := by
    refine runsTo_pushVal (L := L1) (v := 1) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL1len], hw.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL1len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2.1]
  have s4 : RunsTo (pushVal 13)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L3) 3 := by
    refine runsTo_pushVal (L := L2) (v := p) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL2len], hw.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL2len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2]
  have s5 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q) L3)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L3) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s6 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L3)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L3) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s7 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L3)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L3) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s8 : RunsTo (copyTo 2 13)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L3)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2 ∧ v 2 = p) L3) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL3 : (L3.drop 2).take p = ea := by
    rw [hL3, seg_append L2 [p] 2 p (by rw [hL2len]; omega),
      hL2, seg_append L1 [1] 2 p (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 3] 2 p (by rw [hAlen]; omega), hseg1]
  have s9 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 2 ∧ v 2 = p) L3)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q) L4) (7 * p + 7) := by
    have hlist : L4 = L3 ++ (L3.drop 2).take p := by rw [hsegL3, hL4]
    rw [hlist]
    refine runsTo_pushBlock (L := L3) hK (i := 2) (c := p) (by rw [hL3len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL3len], hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL3len]; omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.1]
  have s10 : RunsTo (pushVal 14)
      (At K (fun v => v 8 = K + (p + q + 5 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q) L4)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q) L5) 3 := by
    refine runsTo_pushVal (L := L4) (v := q) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL4len], hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL4len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2]
  have s11 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q) L5)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L5) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s12 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L5)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L5) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s13 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 2) L5)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L5) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s14 : RunsTo (addTo 0 0 13)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 2) L5)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 14 = q ∧ v 0 = K + (2 + p)) L5) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2, hw.2.2.2.1]
      all_goals omega)
  have s15 : RunsTo (copyTo 2 14)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 14 = q ∧ v 0 = K + (2 + p)) L5)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 0 = K + (2 + p) ∧ v 2 = q) L5) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL5 : (L5.drop (2 + p)).take q = et := by
    rw [hL5, seg_append L4 [q] (2 + p) q (by rw [hL4len]; omega),
      hL4, seg_append L3 ea (2 + p) q (by rw [hL3len]; omega),
      hL3, seg_append L2 [p] (2 + p) q (by rw [hL2len]; omega),
      hL2, seg_append L1 [1] (2 + p) q (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 3] (2 + p) q (by rw [hAlen]; omega), hseg2]
  have s16 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 2) ∧
        v 12 = p + q + 4 ∧ v 0 = K + (2 + p) ∧ v 2 = q) L5)
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4) L6) (7 * q + 7) := by
    have hlist : L6 = L5 ++ (L5.drop (2 + p)).take q := by rw [hsegL5, hL6]
    rw [hlist]
    refine runsTo_pushBlock (L := L5) hK (i := 2 + p) (c := q) (by rw [hL5len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL5len], hw.2.2.2.1, hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have c15 := s15.seq s16
  have c14 := s14.seq c15
  have c13 := s13.seq c14
  have c12 := s12.seq c13
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
/-- **The nonempty branch of `uncons`.**  From the workspace holding `ea.length :: (ea ++ et)`
the routine produces the workspace holding `1 :: ea.length :: (ea ++ (et.length :: et))`. -/
theorem runsTo_unconsNE {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (unconsNE K) (fun m => m = initMemAt K (p :: (ea ++ et)))
      (fun m' => m' = initMemAt K (1 :: p :: (ea ++ (q :: et))))
      (19 * p + 19 * q + K + 105) := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  set B : List ℕ := (p + q + 3) :: 1 :: p :: (ea ++ (q :: et)) with hB
  have hAlen : A.length = p + q + 2 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hBlen : B.length = p + q + 4 := by rw [hB]; simp [hp, hq]; all_goals omega
  have hin : initMemAt K (p :: (ea ++ et)) = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA]
    congr 1
    simp [hp, hq]
    all_goals omega
  have hout : initMemAt K (1 :: p :: (ea ++ (q :: et))) = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB]
    congr 1
    simp [hp, hq]
    all_goals omega
  have sfin : RunsTo (finish K)
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = p + q + 4) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (p + q + 4) + 5 * (p + q + 2) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hBlen]
    · rw [hAlen, hBlen]
  have hmain := (runsTo_unconsHead hK hp hq).seq
    ((runsTo_unconsBody hK hp hq).seq sfin)
  refine hmain.conseq (fun m hm => ?_) (fun m hm => ?_) (by omega)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

/-- **`uncons` at the workspace convention.**  The bound is stated in the length of the input
block, which is what the two copies cost. -/
theorem runsTo_unconsProg {K : ℕ} (hK : 16 ≤ K) {E E' : List ℕ}
    (h : (E = [] ∧ E' = [0]) ∨ ∃ (ea et : List ℕ), E = ea.length :: (ea ++ et) ∧
      E' = 1 :: ea.length :: (ea ++ (et.length :: et))) :
    RunsTo (unconsProg K) (fun m => m = initMemAt K E)
      (fun m' => m' = initMemAt K E') (19 * E.length + K + 108) := by
  unfold unconsProg
  have hwfNE : Wf (unconsNE K) :=
    (runsTo_unconsNE (ea := ([] : List ℕ)) (et := ([] : List ℕ)) hK rfl rfl).wf
  have hkey : ∀ m : Mem, m = initMemAt K E → m K = E.length := by
    intro m hm
    subst hm
    simpa [initMem] using initMemAt_add K E 0
  rcases h with ⟨hE, hE'⟩ | ⟨ea, et, hE, hE'⟩
  · subst hE; subst hE'
    have hbr1 : RunsTo (unconsNE K)
        (fun m => (m = initMemAt K ([] : List ℕ)) ∧ m K ≠ 0)
        (fun m' => m' = initMemAt K [0]) 0 := by
      refine runsTo_of_false hwfNE ?_
      rintro m ⟨hm1, hm2⟩
      have hval := hkey m hm1
      simp only [List.length_nil] at hval
      exact hm2 hval
    have hbr2 : RunsTo (assign K 1)
        (fun m => (m = initMemAt K ([] : List ℕ)) ∧ m K = 0)
        (fun m' => m' = initMemAt K [0]) 1 := by
      refine runsTo_assign K 1 (fun m hm => ?_)
      rw [hm.1]
      funext z
      rcases Nat.lt_trichotomy z K with hz | hz | hz
      · rw [Mem.update_of_ne _ _ (by omega), initMemAt_of_lt ([] : List ℕ) hz,
          initMemAt_of_lt [0] hz]
      · subst hz
        rw [Mem.update_self]
        simpa [initMem] using (initMemAt_add z [0] 0).symm
      · obtain ⟨j, hj⟩ : ∃ j, z = K + (j + 1) := ⟨z - K - 1, by omega⟩
        subst hj
        rw [Mem.update_of_ne _ _ (by omega), initMemAt_add, initMemAt_add]
        all_goals simp [initMem]
    exact (hbr1.ifz hbr2).mono (by simp)
  · subst hE; subst hE'
    have hlen : (ea.length :: (ea ++ et)).length = ea.length + et.length + 1 := by
      simp
    have hbr1 : RunsTo (unconsNE K)
        (fun m => (m = initMemAt K (ea.length :: (ea ++ et))) ∧ m K ≠ 0)
        (fun m' => m' = initMemAt K (1 :: ea.length :: (ea ++ (et.length :: et))))
        (19 * ea.length + 19 * et.length + K + 105) :=
      (runsTo_unconsNE hK (rfl : ea.length = ea.length)
        (rfl : et.length = et.length)).strengthen (fun m hm => hm.1)
    have hbr2 : RunsTo (assign K 1)
        (fun m => (m = initMemAt K (ea.length :: (ea ++ et))) ∧ m K = 0)
        (fun m' => m' = initMemAt K (1 :: ea.length :: (ea ++ (et.length :: et)))) 1 := by
      refine runsTo_of_false (wf_assign _ _) ?_
      rintro m ⟨hm1, hm2⟩
      have hval := hkey m hm1
      rw [hm2, hlen] at hval
      omega
    refine (hbr1.ifz hbr2).mono ?_
    rw [hlen]
    omega

/-! ## The length of the encoding

`RAM.rawLength a` is the number of registers the encoding of `a` occupies.  It is the bound on
the number of rounds that every list traversal needs: a list is never longer than its encoding,
and, unlike the length of the list, this number sits in a register of the workspace, so one
instruction reads it. -/

/-- Read the length field and return it. -/
def rawLenProg (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
    (seq (addTo 8 8 10) (seq (copyTo 11 8) (seq (assign 12 2) (seq (assign 13 1)
      (seq (pushVal 13) (seq (pushVal 9) (finish K))))))))))

theorem runsTo_rawLenProg {K : ℕ} (hK : 16 ≤ K) (E : List ℕ) :
    RunsTo (rawLenProg K) (fun m => m = initMemAt K E)
      (fun m' => m' = initMemAt K [E.length]) (5 * E.length + K + 50) := by
  set n : ℕ := E.length with hn
  set A : List ℕ := n :: E with hA
  set B : List ℕ := [1, n] with hB
  have hAlen : A.length = n + 1 := by rw [hA]; simp [hn]
  have hin : initMemAt K E = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA, hn]
  have hout : initMemAt K [n] = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB]; simp
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A) (At K (fun v => v 9 = n) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by simp [Mem.update, hA])
  have s2 : RunsTo (assign 8 K) (At K (fun v => v 9 = n) A)
      (At K (fun v => v 9 = n ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s3 : RunsTo (addTo 8 8 9) (At K (fun v => v 9 = n ∧ v 8 = K) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + n) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (assign 10 1) (At K (fun v => v 9 = n ∧ v 8 = K + n) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + n ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s5 : RunsTo (addTo 8 8 10) (At K (fun v => v 9 = n ∧ v 8 = K + n ∧ v 10 = 1) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], ?_⟩
      simp only [Mem.update_self, hw.2.1, hw.2.2]
      omega)
  have s6 : RunsTo (copyTo 11 8) (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1)) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1)) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2], ?_⟩
      simp only [Mem.update_self, hw.2])
  have s7 : RunsTo (assign 12 2)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1)) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1) ∧ v 12 = 2) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s8 : RunsTo (assign 13 1)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1) ∧ v 12 = 2) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1) ∧ v 12 = 2 ∧
        v 13 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s9 : RunsTo (pushVal 13)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 1) ∧ v 11 = K + (n + 1) ∧ v 12 = 2 ∧
        v 13 = 1) A)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 2) ∧ v 11 = K + (n + 1) ∧ v 12 = 2)
        (A ++ [1])) 3 := by
    refine runsTo_pushVal (L := A) (v := 1) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.2.1, hAlen], hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_⟩)
    · rw [hagree 9 (by omega) (by omega), hw.1]
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.2.1]
  have s10 : RunsTo (pushVal 9)
      (At K (fun v => v 9 = n ∧ v 8 = K + (n + 2) ∧ v 11 = K + (n + 1) ∧ v 12 = 2)
        (A ++ [1]))
      (At K (fun v => v 11 = K + (n + 1) ∧ v 12 = 2) ((A ++ [1]) ++ [n])) 3 := by
    refine runsTo_pushVal (L := A ++ [1]) (v := n) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.2.1]; simp [hAlen], hw.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.2]
  have hfinal : (A ++ [1]) ++ [n] = A ++ B := by rw [hB]; simp
  have s11 : RunsTo (finish K)
      (At K (fun v => v 11 = K + (n + 1) ∧ v 12 = 2) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B) (7 * 2 + 5 * (n + 1) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hB]; simp
    · rw [hAlen, hB]; simp
  rw [hfinal] at s10
  have c10 := s10.seq s11
  have c9 := s9.seq c10
  have c8 := s8.seq c9
  have c7 := s7.seq c8
  have c6 := s6.seq c7
  have c5 := s5.seq c6
  have c4 := s4.seq c5
  have c3 := s3.seq c4
  have c2 := s2.seq c3
  refine ((s1.seq c2).conseq (fun m hm => ?_) (fun m hm => ?_) (by omega))
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

/-! ## The tail

The workspace list is `A = (p + q + 1) :: p :: (ea ++ et)`; the answer is `et`, so the block to
build is `B = q :: et`, one value and one block copy. -/

/-- Read the two lengths and set the pointers. -/
def tailHead (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (copyTo 13 (K + 1)) (seq (assign 10 1) (seq (subTo 14 9 10)
    (seq (subTo 14 14 13) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
      (seq (addTo 8 8 10) (seq (copyTo 11 8) (seq (assign 10 1) (addTo 12 14 10)))))))))))

/-- Stack the tail block on top of the workspace. -/
def tailBody (K : ℕ) : Program :=
  seq (pushVal 14) (seq (assign 0 K) (seq (assign 10 2) (seq (addTo 0 0 10)
    (seq (addTo 0 0 13) (seq (copyTo 2 14) pushBlock)))))

/-- The nonempty branch of `tail`. -/
def tailNE (K : ℕ) : Program := seq (tailHead K) (seq (tailBody K) (finish K))

/-- `tail` at the workspace convention. -/
def tailProg (K : ℕ) : Program := RAM.ifz K (tailNE K) []

theorem runsTo_tailHead {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (tailHead K) (At K (fun _ => True) ((p + q + 1) :: p :: (ea ++ et)))
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) ((p + q + 1) :: p :: (ea ++ et))) 12 := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  have hAlen : A.length = p + q + 2 := by rw [hA]; simp [hp, hq]; all_goals omega
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A)
      (At K (fun v => v 9 = p + q + 1) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by simp [Mem.update, hA])
  have s2 : RunsTo (copyTo 13 (K + 1)) (At K (fun v => v 9 = p + q + 1) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p) A) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw => by simp [Mem.update, hA, hw])
  have s3 : RunsTo (assign 10 1) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (subTo 14 9 10) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = p + q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2]
      all_goals omega)
  have s5 : RunsTo (subTo 14 14 13)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = p + q) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.1, hw.2.2]
      all_goals omega)
  have s6 : RunsTo (assign 8 K) (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q) A)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s7 : RunsTo (addTo 8 8 9)
      (At K (fun v => v 9 = p + q + 1 ∧ v 13 = p ∧ v 14 = q ∧ v 8 = K) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 1)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.2.1], by simp [Mem.update, hw.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.1, hw.2.2.2])
  have s8 : RunsTo (assign 10 1)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 1)) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 1) ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s9 : RunsTo (addTo 8 8 10)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 1) ∧ v 10 = 1) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.1, hw.2.2.2]
      all_goals omega)
  have s10 : RunsTo (copyTo 11 8)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2)) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2)) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2])
  have s11 : RunsTo (assign 10 1)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2)) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s12 : RunsTo (addTo 12 14 10)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 10 = 1) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.1, hw.2.2.2.2])
  have c11 := s11.seq s12
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
theorem runsTo_tailBody {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (tailBody K)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) ((p + q + 1) :: p :: (ea ++ et)))
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = q + 1)
        (((p + q + 1) :: p :: (ea ++ et)) ++ (q :: et))) (7 * q + 15) := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  have hAlen : A.length = p + q + 2 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hdropp : A.drop (2 + p) = et := by
    rw [hA, show 2 + p = p + 1 + 1 by omega, List.drop_succ_cons, List.drop_succ_cons,
      ← hp, List.drop_left]
  have hseg2 : (A.drop (2 + p)).take q = et := by rw [hdropp, ← hq, List.take_length]
  have s13 : RunsTo (pushVal 14)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 2) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) A)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) (A ++ [q])) 3 := by
    refine runsTo_pushVal (L := A) (v := q) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.2.2.1, hAlen], hw.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [hagree 13 (by omega) (by omega), hw.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.1]
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.2.2]
  have s14 : RunsTo (assign 0 K)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1) (A ++ [q]))
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K) (A ++ [q])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s15 : RunsTo (assign 10 2)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K) (A ++ [q]))
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K ∧ v 10 = 2) (A ++ [q])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s16 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K ∧ v 10 = 2) (A ++ [q]))
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K + 2) (A ++ [q])) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s17 : RunsTo (addTo 0 0 13)
      (At K (fun v => v 13 = p ∧ v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K + 2) (A ++ [q]))
      (At K (fun v => v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K + (2 + p)) (A ++ [q])) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.2.1], by simp [Mem.update, hw.2.2.1],
        by simp [Mem.update, hw.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2, hw.1]
      omega)
  have s18 : RunsTo (copyTo 2 14)
      (At K (fun v => v 14 = q ∧ v 8 = K + (p + q + 3) ∧
        v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧ v 0 = K + (2 + p)) (A ++ [q]))
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧
        v 0 = K + (2 + p) ∧ v 2 = q) (A ++ [q])) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.2.1], by simp [Mem.update, hw.2.2.1],
        by simp [Mem.update, hw.2.2.2.1], by simp [Mem.update, hw.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.1])
  have hlenq : (A ++ [q]).length = p + q + 3 := by simp [hAlen]
  have hsegA : ((A ++ [q]).drop (2 + p)).take q = et := by
    rw [seg_append A [q] (2 + p) q (by rw [hAlen]; omega), hseg2]
  have s19 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 3) ∧ v 11 = K + (p + q + 2) ∧ v 12 = q + 1 ∧
        v 0 = K + (2 + p) ∧ v 2 = q) (A ++ [q]))
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = q + 1) ((A ++ [q]) ++ et))
      (7 * q + 7) := by
    have hlist : (A ++ [q]) ++ et = (A ++ [q]) ++ (((A ++ [q]).drop (2 + p)).take q) := by
      rw [hsegA]
    rw [hlist]
    refine runsTo_pushBlock (L := A ++ [q]) hK (i := 2 + p) (c := q)
      (by rw [hlenq]; omega)
      (fun w hw => ⟨by rw [hw.1, hlenq], hw.2.2.2.1, hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have hfinal : (A ++ [q]) ++ et = A ++ (q :: et) := by simp
  rw [hfinal] at s19
  have c18 := s18.seq s19
  have c17 := s17.seq c18
  have c16 := s16.seq c17
  have c15 := s15.seq c16
  have c14 := s14.seq c15
  exact (s13.seq c14).mono (by omega)

/-- **The nonempty branch of `tail`.** -/
theorem runsTo_tailNE {K : ℕ} (hK : 16 ≤ K) {ea et : List ℕ} {p q : ℕ}
    (hp : ea.length = p) (hq : et.length = q) :
    RunsTo (tailNE K) (fun m => m = initMemAt K (p :: (ea ++ et)))
      (fun m' => m' = initMemAt K et) (5 * p + 19 * q + K + 61) := by
  set A : List ℕ := (p + q + 1) :: p :: (ea ++ et) with hA
  set B : List ℕ := q :: et with hB
  have hAlen : A.length = p + q + 2 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hBlen : B.length = q + 1 := by rw [hB]; simp [hq]
  have hin : initMemAt K (p :: (ea ++ et)) = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA]
    congr 1
    simp [hp, hq]
    all_goals omega
  have hout : initMemAt K et = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB, hq]
  have sfin : RunsTo (finish K)
      (At K (fun v => v 11 = K + (p + q + 2) ∧ v 12 = q + 1) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (q + 1) + 5 * (p + q + 2) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hBlen]
    · rw [hAlen, hBlen]
  have hmain := (runsTo_tailHead hK hp hq).seq ((runsTo_tailBody hK hp hq).seq sfin)
  refine hmain.conseq (fun m hm => ?_) (fun m hm => ?_) (by omega)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

/-- **`tail` at the workspace convention.** -/
theorem runsTo_tailProg {K : ℕ} (hK : 16 ≤ K) {E E' : List ℕ}
    (h : (E = [] ∧ E' = []) ∨ ∃ ea : List ℕ, E = ea.length :: (ea ++ E')) :
    RunsTo (tailProg K) (fun m => m = initMemAt K E)
      (fun m' => m' = initMemAt K E') (19 * E.length + K + 63) := by
  unfold tailProg
  have hwfNE : Wf (tailNE K) :=
    (runsTo_tailNE (ea := ([] : List ℕ)) (et := ([] : List ℕ)) hK rfl rfl).wf
  have hkey : ∀ m : Mem, m = initMemAt K E → m K = E.length := by
    intro m hm
    subst hm
    simpa [initMem] using initMemAt_add K E 0
  rcases h with ⟨hE, hE'⟩ | ⟨ea, hE⟩
  · subst hE; subst hE'
    have hbr1 : RunsTo (tailNE K)
        (fun m => (m = initMemAt K ([] : List ℕ)) ∧ m K ≠ 0)
        (fun m' => m' = initMemAt K ([] : List ℕ)) 0 := by
      refine runsTo_of_false hwfNE ?_
      rintro m ⟨hm1, hm2⟩
      have hval := hkey m hm1
      simp only [List.length_nil] at hval
      exact hm2 hval
    have hbr2 : RunsTo ([] : Program)
        (fun m => (m = initMemAt K ([] : List ℕ)) ∧ m K = 0)
        (fun m' => m' = initMemAt K ([] : List ℕ)) 0 :=
      runsTo_nil (fun m hm => hm.1)
    exact (hbr1.ifz hbr2).mono (by simp)
  · subst hE
    have hlen : (ea.length :: (ea ++ E')).length = ea.length + E'.length + 1 := by simp
    have hbr1 : RunsTo (tailNE K)
        (fun m => (m = initMemAt K (ea.length :: (ea ++ E'))) ∧ m K ≠ 0)
        (fun m' => m' = initMemAt K E')
        (5 * ea.length + 19 * E'.length + K + 61) :=
      (runsTo_tailNE hK (rfl : ea.length = ea.length)
        (rfl : E'.length = E'.length)).strengthen (fun m hm => hm.1)
    have hbr2 : RunsTo ([] : Program)
        (fun m => (m = initMemAt K (ea.length :: (ea ++ E'))) ∧ m K = 0)
        (fun m' => m' = initMemAt K E') 0 := by
      refine runsTo_of_false (fun i hi => absurd hi (by simp)) ?_
      rintro m ⟨hm1, hm2⟩
      have hval := hkey m hm1
      rw [hm2, hlen] at hval
      omega
    refine (hbr1.ifz hbr2).mono ?_
    rw [hlen]
    omega

end Lists

/-! ## The clean classes -/

variable {α : Type*}

/-- **`uncons` is a clean routine of the workspace convention.** -/
theorem cleanComputeAt_uncons [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (Lists.unconsProg K) (uncons : List α → Option (α × List α))
      (fun n => 19 * n + K + 108) := by
  intro l
  cases l with
  | nil =>
      have h1 : (Enc.encode ([] : List α)) = [] := rfl
      have h2 : (Enc.encode (uncons ([] : List α))) = [0] := rfl
      rw [h1, h2]
      refine (Lists.runsTo_unconsProg hK (Or.inl ⟨rfl, rfl⟩)).mono ?_
      show 19 * ([] : List ℕ).length + K + 108 ≤ 19 * Enc.size ([] : List α) + K + 108
      simp
  | cons a t =>
      have h1 : Enc.encode (a :: t) =
          (Enc.encode a).length :: (Enc.encode a ++ Enc.encode t) := rfl
      have h2 : Enc.encode (uncons (a :: t)) =
          1 :: (Enc.encode a).length ::
            (Enc.encode a ++ ((Enc.encode t).length :: Enc.encode t)) := rfl
      rw [h1, h2]
      refine (Lists.runsTo_unconsProg hK (Or.inr ⟨Enc.encode a, Enc.encode t, rfl, rfl⟩)).mono ?_
      show 19 * ((Enc.encode a).length :: (Enc.encode a ++ Enc.encode t)).length + K + 108 ≤
        19 * Enc.size (a :: t) + K + 108
      have hsz : Enc.size (a :: t) =
          listSize ((Enc.encode a).length :: (Enc.encode a ++ Enc.encode t)) := rfl
      rw [hsz]
      have := length_lt_listSize ((Enc.encode a).length :: (Enc.encode a ++ Enc.encode t))
      omega

/-- **`uncons` runs in polynomial time** at the workspace convention. -/
theorem polyTimeCleanAt_uncons [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (uncons : List α → Option (α × List α)) :=
  ⟨Lists.unconsProg K, _, ((polyBound_const 19).mul polyBound_id).add
    (polyBound_const (K + 108)), cleanComputeAt_uncons hK⟩

/-- The size of the answer of `uncons` is at most twice the size of the list plus two: the
answer repeats the two blocks of the list and adds one separator. -/
theorem sizeBound_uncons [Enc α] :
    ∀ l : List α, Enc.size (uncons l) ≤ 2 * (Enc.size l + 1) ^ 1 := by
  intro l
  cases l with
  | nil =>
      have h1 : Enc.size (uncons ([] : List α)) = listSize [0] := rfl
      have h2 : Enc.size ([] : List α) = listSize ([] : List ℕ) := rfl
      rw [h1, h2]
      simp [listSize]
  | cons a t =>
      set ea : List ℕ := Enc.encode a with hea
      set et : List ℕ := Enc.encode t with het
      have h1 : Enc.size (a :: t) = listSize (ea.length :: (ea ++ et)) := rfl
      have h2 : Enc.size (uncons (a :: t)) =
          listSize (1 :: ea.length :: (ea ++ (et.length :: et))) := rfl
      have e1 : listSize (ea.length :: (ea ++ et))
          = listSize ea + listSize et - 1 + (Nat.size ea.length + 1) := by
        rw [listSize_cons, listSize_append]
      have e2 : listSize (1 :: ea.length :: (ea ++ (et.length :: et)))
          = listSize ea + (listSize et + (Nat.size et.length + 1)) - 1
            + (Nat.size ea.length + 1) + (Nat.size 1 + 1) := by
        rw [listSize_cons, listSize_cons, listSize_append, listSize_cons]
      have hea1 : 1 ≤ listSize ea := by
        have := length_lt_listSize ea; omega
      have het1 : 1 ≤ listSize et := by
        have := length_lt_listSize et; omega
      have hq : Nat.size et.length ≤ et.length := size_le_self _
      have hq2 : et.length < listSize et := length_lt_listSize et
      rw [h1, h2, e1, e2, pow_one]
      have hone : Nat.size 1 = 1 := by simp
      rw [hone]
      omega

/-- **`uncons` is a `PolyFun`.** -/
theorem polyFun_uncons [Enc α] : PolyFun (uncons : List α → Option (α × List α)) :=
  ⟨polyTimeCleanAt_uncons (by omega), ⟨2, 1, sizeBound_uncons⟩⟩


/-! ## The length of the encoding, and the tail -/

/-- The number of registers the encoding of `a` occupies.  A list is never longer than its
encoding (`RAM.length_le_rawLength`), so this is the bound on the number of rounds that a list
traversal needs, and unlike the length of the list it is read off in one instruction. -/
def rawLength [Enc α] (a : α) : ℕ := (Enc.encode a).length

theorem rawLength_lt_size [Enc α] (a : α) : rawLength a < Enc.size a :=
  length_lt_listSize _

/-- A list is at most as long as its encoding: each entry occupies at least one register. -/
theorem length_le_rawLength [Enc α] (l : List α) : l.length ≤ rawLength l := by
  induction l with
  | nil => simp [rawLength, Enc.encode, encList]
  | cons a t ih =>
      have h : rawLength (a :: t) = (Enc.encode a).length + 1 + rawLength t := by
        simp [rawLength, Enc.encode, encList, frame]
        omega
      simp only [List.length_cons, h]
      omega

theorem cleanComputeAt_rawLength [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (Lists.rawLenProg K) (rawLength : α → ℕ)
      (fun n => 5 * n + K + 50) := by
  intro a
  have h2 : Enc.encode (rawLength a) = [(Enc.encode a).length] := rfl
  rw [h2]
  refine (Lists.runsTo_rawLenProg hK (Enc.encode a)).mono ?_
  have := length_lt_listSize (Enc.encode a)
  have h3 : Enc.size a = listSize (Enc.encode a) := rfl
  dsimp only
  omega

theorem polyTimeCleanAt_rawLength [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (rawLength : α → ℕ) :=
  ⟨Lists.rawLenProg K, _, ((polyBound_const 5).mul polyBound_id).add
    (polyBound_const (K + 50)), cleanComputeAt_rawLength hK⟩

/-- **The length of the encoding is a `PolyFun`.** -/
theorem polyFun_rawLength [Enc α] : PolyFun (rawLength : α → ℕ) :=
  ⟨polyTimeCleanAt_rawLength (by omega),
    SizeBound.of_nat (fun a => le_trans (size_le_self _) (le_of_lt (rawLength_lt_size a)))⟩

/-- The tail of a list is no larger than the list. -/
theorem size_tail_le [Enc α] (l : List α) : Enc.size l.tail ≤ Enc.size l := by
  cases l with
  | nil => exact le_refl _
  | cons a t =>
      show listSize (Enc.encode t) ≤
        listSize ((Enc.encode a).length :: (Enc.encode a ++ Enc.encode t))
      rw [listSize_cons, listSize_append]
      have h1 := length_lt_listSize (Enc.encode a)
      have h2 := length_lt_listSize (Enc.encode t)
      omega

theorem cleanComputeAt_tail [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (Lists.tailProg K) (List.tail : List α → List α)
      (fun n => 19 * n + K + 63) := by
  intro l
  have hdisj : ((Enc.encode l = [] ∧ Enc.encode l.tail = []) ∨
      ∃ ea : List ℕ, Enc.encode l = ea.length :: (ea ++ Enc.encode l.tail)) := by
    cases l with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons a t => exact Or.inr ⟨Enc.encode a, rfl⟩
  refine (Lists.runsTo_tailProg hK hdisj).mono ?_
  have := length_lt_listSize (Enc.encode l)
  have h3 : Enc.size l = listSize (Enc.encode l) := rfl
  dsimp only
  omega

theorem polyTimeCleanAt_tail [Enc α] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (List.tail : List α → List α) :=
  ⟨Lists.tailProg K, _, ((polyBound_const 19).mul polyBound_id).add
    (polyBound_const (K + 63)), cleanComputeAt_tail hK⟩

/-- **The tail of a list is a `PolyFun`.** -/
theorem polyFun_tail [Enc α] : PolyFun (List.tail : List α → List α) :=
  ⟨polyTimeCleanAt_tail (by omega),
    SizeBound.of_le (g := id) SizeBound.id' (fun l => size_tail_le l)⟩


/-! ## The length of a list

With the destructor and the round bound, the length is a bounded iteration: the state is a
counter together with what is left of the list, one round drops the head and counts it, and
`RAM.rawLength` is a round bound, because a list is never longer than its encoding.  The
iteration is run for exactly `rawLength` rounds; the extra rounds do nothing, since the step
leaves the state alone once the list is empty. -/

/-- One round of the traversal: drop the head and count it. -/
def lenStep [Enc α] (s : ℕ × List α) : ℕ × List α :=
  (if decide (rawLength s.2 = 0) then s.1 else s.1 + 1, s.2.tail)

theorem rawLength_eq_zero_iff [Enc α] (r : List α) : rawLength r = 0 ↔ r = [] := by
  constructor
  · intro h
    cases r with
    | nil => rfl
    | cons a t => simp [rawLength, Enc.encode, encList, frame] at h
  · rintro rfl
    rfl

/-- After `j` rounds the counter has grown by `min j r.length` and `j` entries are gone. -/
theorem lenStep_iterate [Enc α] (j : ℕ) : ∀ (n : ℕ) (r : List α),
    lenStep^[j] (n, r) = (n + min j r.length, r.drop j) := by
  induction j with
  | zero => intro n r; simp
  | succ j ih =>
      intro n r
      rw [Function.iterate_succ_apply]
      cases r with
      | nil =>
          have h1 : lenStep ((n : ℕ), ([] : List α)) = (n, ([] : List α)) := by
            simp [lenStep, rawLength_eq_zero_iff]
          rw [h1, ih]
          simp
      | cons a t =>
          have h1 : lenStep ((n : ℕ), a :: t) = (n + 1, t) := by
            have h0 : ¬ (rawLength (a :: t) = 0) := by
              rw [rawLength_eq_zero_iff]
              simp
            simp [lenStep, h0]
          rw [h1, ih, List.drop_succ_cons]
          have h2 : min (j + 1) (a :: t).length = min j t.length + 1 := by
            simp only [List.length_cons]
            omega
          rw [h2]
          congr 1
          omega

theorem rawLength_pair_zero [Enc α] (l : List α) :
    rawLength ((0 : ℕ), l) = 3 + rawLength l := by
  simp [rawLength, Enc.encode, frame]
  omega

/-- The encoding of a suffix is no larger than the encoding of the list. -/
theorem size_drop_le [Enc α] (j : ℕ) (r : List α) : Enc.size (r.drop j) ≤ Enc.size r := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [← List.tail_drop]
      exact le_trans (size_tail_le _) ih

/-- The iteration run for `rawLength` rounds returns the length. -/
theorem lenStep_result [Enc α] (l : List α) :
    (lenStep^[rawLength ((0 : ℕ), l)] ((0 : ℕ), l)).1 = l.length := by
  rw [lenStep_iterate]
  have h1 : l.length ≤ rawLength l := length_le_rawLength l
  have h2 : rawLength ((0 : ℕ), l) = 3 + rawLength l := rawLength_pair_zero l
  simp only []
  omega

/-- The states of the iteration stay polynomially small. -/
theorem lenStep_size_bound [Enc α] (a : ℕ × List α) (j : ℕ) (hj : j ≤ rawLength a) :
    Enc.size ((rawLength a - j, lenStep^[j] a) : ℕ × (ℕ × List α)) ≤ 10 * Enc.size a + 16 := by
  obtain ⟨n, r⟩ := a
  set N : ℕ := Enc.size ((n, r) : ℕ × List α) with hN
  have hn : Enc.size n ≤ N := Combine.size_fst_le n r
  have hr : Enc.size r ≤ N := Combine.size_snd_le n r
  have hraw : rawLength ((n, r) : ℕ × List α) < N := rawLength_lt_size _
  have hnsz : Nat.size n + 2 ≤ N := by
    have : Enc.size n = Nat.size n + 2 := Small.size_nat n
    omega
  have hrlen : r.length ≤ N := by
    have h1 : r.length ≤ rawLength r := length_le_rawLength r
    have h2 : rawLength r < Enc.size r := rawLength_lt_size r
    omega
  rw [lenStep_iterate]
  set X : ℕ := rawLength ((n, r) : ℕ × List α) - j with hX
  set Y : ℕ := n + min j r.length with hY
  set Z : List α := r.drop j with hZ
  have hsX : Enc.size X ≤ N + 2 := by
    have h1 : Enc.size X = Nat.size X + 2 := Small.size_nat X
    have h2 : Nat.size X ≤ X := size_le_self X
    omega
  have hsY : Enc.size Y ≤ N + 3 := by
    have h1 : Enc.size Y = Nat.size Y + 2 := Small.size_nat Y
    have hnlt : n < 2 ^ N := lt_of_lt_of_le (Nat.lt_size_self n)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hmlt : min j r.length < 2 ^ N :=
      lt_of_le_of_lt (le_trans (min_le_right _ _) hrlen) (Nat.lt_two_pow_self)
    have hsum : Y < 2 ^ (N + 1) := by rw [hY, pow_succ]; omega
    have := Nat.size_le.2 hsum
    omega
  have hsZ : Enc.size Z ≤ N := le_trans (size_drop_le j r) hr
  have hpair : Enc.size ((Y, Z) : ℕ × List α) ≤ 2 * Enc.size Y + 2 * Enc.size Z :=
    Combine.size_pair_le Y Z
  have htop : Enc.size ((X, (Y, Z)) : ℕ × (ℕ × List α)) ≤
      2 * Enc.size X + 2 * Enc.size ((Y, Z) : ℕ × List α) := Combine.size_pair_le _ _
  omega

/-- **The length of a list is a `PolyFun`.** -/
theorem polyFun_length [Enc α] : PolyFun (fun l : List α => l.length) := by
  have hp : PolyFun (fun s : ℕ × List α => decide (rawLength s.2 = 0)) :=
    PolyFun.natEq (polyFun_snd.comp polyFun_rawLength) (polyFun_const 0)
  have hcount : PolyFun (fun s : ℕ × List α =>
      if decide (rawLength s.2 = 0) then s.1 else s.1 + 1) :=
    PolyFun.ite hp polyFun_fst (PolyFun.add polyFun_fst (polyFun_const 1))
  have htail : PolyFun (fun s : ℕ × List α => s.2.tail) := polyFun_snd.comp polyFun_tail
  have hlenStep : PolyFun (lenStep : ℕ × List α → ℕ × List α) :=
    (hcount.pair htail).of_eq (fun s => rfl)
  have hstep : PolyFun (fun x : ℕ × (ℕ × List α) => (x.1 - 1, lenStep x.2)) :=
    (PolyFun.sub polyFun_fst (polyFun_const 1)).pair (polyFun_snd.comp hlenStep)
  have hk : PolyFun (fun a : ℕ × List α => (rawLength a, a)) :=
    polyFun_rawLength.pair polyFun_id
  have hiter : PolyFun (fun a : ℕ × List α => lenStep^[rawLength a] a) :=
    PolyFun.iterate hstep hk (fun a => le_of_lt (rawLength_lt_size a)) polyBound_id
      (fun a j hj => lenStep_size_bound a j hj)
      (((polyBound_const 10).mul polyBound_id).add (polyBound_const 16))
  have hzero : PolyFun (fun l : List α => ((0 : ℕ), l)) :=
    ((polyFun_const (0 : ℕ)).pair polyFun_id).of_eq (fun l => rfl)
  exact ((hzero.comp hiter).comp polyFun_fst).of_eq (fun l => lenStep_result l)

end RAM
