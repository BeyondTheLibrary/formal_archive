import Workspace.Machine.Lists

/-!
# Case analysis on an `Option`, and the list constructors

`Workspace/Machine/Lists.lean` builds the destructor `RAM.uncons`, but it leaves one gap, which
is recorded in `DESIGN.md`: the answer of `uncons` is an `Option`, and the payload of that
`Option` cannot be taken out again.  The only dispatcher available, `RAM.PolyFun.ite`, chooses
between two *total* functions, and the empty case would have to return an element of `α`, of
which an arbitrary encodable type has none.

This file closes the gap with one short routine.  For a pair `(o, s) : Option β × σ` the tag of
the `Option` sits in the *fixed* register `K + 2` of the workspace convention, exactly as the bit
of a `Bool × α` does (`RAM.Combine.initMemAt_bool_reg`), so the dispatcher is literally
`ifz (K + 2)`.  The `none` branch keeps the second component and runs a routine for `σ → γ`.  The
`some` branch first strips the tag — turning the workspace of `(some b, s)` into the workspace of
`(b, s)` — and then runs a routine for `β × σ → γ`.  Stripping the tag is a `Layout.lean`
assembly of the shape of `RAM.Lists.unconsNE`, and it is the only new machine code here.

With it, `Option.elim` with a case-dependent default is a combinator (`RAM.PolyFun.optionElim`),
and so is the case analysis on a list (`RAM.PolyFun.listCases`), which is what every traversal
needs.

## Main results

* `RAM.Lists.runsTo_stripProg`, `RAM.cleanComputeAt_optionElim`,
  `RAM.polyTimeCleanAt_optionElim`, `RAM.PolyFun.optionElim`;
* `RAM.PolyFun.listCases`;
* `RAM.polyFun_nil`, `RAM.polyFun_none`.
-/

namespace RAM

variable {α β γ σ : Type*}

/-! ## Sizes of the encodings involved -/

/-- Putting the tag `1` in front of a block does not shrink the pair it sits in: the encoding of
`(b, s)` is at most as large as the encoding of `(some b, s)`. -/
theorem size_strip_le [Enc β] [Enc σ] (b : β) (s : σ) :
    Enc.size ((b, s) : β × σ) ≤ Enc.size ((some b, s) : Option β × σ) := by
  have h1 : Enc.size ((b, s) : β × σ)
      = listSize (frame (Enc.encode b)) + listSize (frame (Enc.encode s)) - 1 := by
    show listSize (frame (Enc.encode b) ++ frame (Enc.encode s)) = _
    rw [listSize_append]
  have h2 : Enc.size ((some b, s) : Option β × σ)
      = listSize (frame (1 :: Enc.encode b)) + listSize (frame (Enc.encode s)) - 1 := by
    show listSize (frame (1 :: Enc.encode b) ++ frame (Enc.encode s)) = _
    rw [listSize_append]
  have h3 : listSize (frame (Enc.encode b))
      = listSize (Enc.encode b) + (Nat.size (Enc.encode b).length + 1) := listSize_frame _
  have h4 : listSize (frame (1 :: Enc.encode b))
      = listSize (Enc.encode b) + (Nat.size 1 + 1)
        + (Nat.size ((Enc.encode b).length + 1) + 1) := by
    rw [listSize_frame, listSize_cons]
    simp
  have h5 : Nat.size (Enc.encode b).length ≤ Nat.size ((Enc.encode b).length + 1) :=
    Nat.size_le_size (by omega)
  have h6 : 1 ≤ listSize (frame (Enc.encode s)) := by
    have := length_lt_listSize (frame (Enc.encode s)); omega
  omega

/-- The tag of an `Option` in the first component of a pair sits in register `K + 2`. -/
theorem initMemAt_option_tag [Enc β] [Enc σ] {K : ℕ} (o : Option β) (s : σ) :
    initMemAt K (Enc.encode ((o, s) : Option β × σ)) (K + 2) = (if o.isSome then 1 else 0) := by
  rw [initMemAt_add]
  show initMem (frame (Enc.encode o) ++ frame (Enc.encode s)) 2 = _
  cases o <;> simp [initMem, frame, Enc.encode]

namespace Lists

open Layout

/-! ## Stripping the tag

The workspace list of `(some b, s)` is

`A = (p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es))`,

with `eb` the encoding of `b`, `p` its length, `es` the encoding of `s` and `q` its length.  The
block to be built is the workspace list of `(b, s)`,

`B = (p + q + 2) :: p :: (eb ++ (q :: es))`.

So the routine copies the two blocks out with one entry fewer in front.  The registers follow the
discipline of `Workspace/Machine/Layout.lean`: `0`, `1`, `2` and `3 .. 7` belong to the copy
routines, `8` is the top pointer, `10` holds constants, `11` the base of the block, `12` its
length, and `13`, `14`, `15` hold `p`, `q` and the length field of the answer. -/

/-- Read the two lengths and set the pointers. -/
def stripHead (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (copyTo 13 (K + 1)) (seq (assign 10 1) (seq (subTo 13 13 10)
    (seq (subTo 15 9 10) (seq (copyTo 12 9) (seq (subTo 14 9 13) (seq (assign 10 3)
      (seq (subTo 14 14 10) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
        (seq (addTo 8 8 10) (copyTo 11 8)))))))))))))

/-- Stack the encoding of the answer on top of the workspace. -/
def stripBody (K : ℕ) : Program :=
  seq (pushVal 15) (seq (pushVal 13) (seq (assign 0 K) (seq (assign 10 3)
    (seq (addTo 0 0 10) (seq (copyTo 2 13) (seq pushBlock (seq (pushVal 14)
      (seq (assign 0 K) (seq (assign 10 4) (seq (addTo 0 0 10) (seq (addTo 0 0 13)
        (seq (copyTo 2 14) pushBlock))))))))))))

/-- The routine that strips the tag of the `Option` in the first component of a pair. -/
def stripProg (K : ℕ) : Program := seq (stripHead K) (seq (stripBody K) (finish K))

theorem runsTo_stripHead {K : ℕ} (hK : 16 ≤ K) {eb es : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : es.length = q) :
    RunsTo (stripHead K)
      (At K (fun _ => True) ((p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es))))
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 2)
        ((p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es)))) 14 := by
  set A : List ℕ := (p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es)) with hA
  have hA0 : A.getD 0 0 = p + q + 3 := by rw [hA]; simp
  have hA1 : A.getD 1 0 = p + 1 := by rw [hA]; simp
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A)
      (At K (fun v => v 9 = p + q + 3) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by rw [Mem.update_self, hA0])
  have s2 : RunsTo (copyTo 13 (K + 1)) (At K (fun v => v 9 = p + q + 3) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p + 1) A) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 13), hw],
        by rw [Mem.update_self, hA1]⟩)
  have s3 : RunsTo (assign 10 1) (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p + 1) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p + 1 ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2],
        by rw [Mem.update_self]⟩)
  have s4 : RunsTo (subTo 13 13 10) (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p + 1 ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 10 = 1) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 13), hw.1],
        by rw [Mem.update_self, hw.2.1, hw.2.2]; omega,
        by rw [Mem.update_of_ne _ _ (by omega : (10:ℕ) ≠ 13), hw.2.2]⟩)
  have s5 : RunsTo (subTo 15 9 10) (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 10 = 1) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 15), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 15), hw.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2]; omega⟩)
  have s6 : RunsTo (copyTo 12 9) (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 12), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 12), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 12), hw.2.2],
        by rw [Mem.update_self, hw.1]⟩)
  have s7 : RunsTo (subTo 14 9 13)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q + 3) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 14), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 14), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 14), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 14), hw.2.2.2],
        by rw [Mem.update_self, hw.1, hw.2.1]; omega⟩)
  have s8 : RunsTo (assign 10 3)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q + 3) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q + 3 ∧ v 10 = 3) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 10), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 10), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s9 : RunsTo (subTo 14 14 10)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q + 3 ∧ v 10 = 3) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q) A) 1 :=
    runsTo_subReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 14), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 14), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 14), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 14), hw.2.2.2.1],
        by rw [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]; omega⟩)
  have s10 : RunsTo (assign 8 K)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q) A)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s11 : RunsTo (addTo 8 8 9)
      (At K (fun v => v 9 = p + q + 3 ∧ v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧
        v 14 = q ∧ v 8 = K) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.2.1],
        by rw [Mem.update_self, hw.1, hw.2.2.2.2.2]⟩)
  have s12 : RunsTo (assign 10 1)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3)) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3) ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 10), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 10), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 10), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 10), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 10), hw.2.2.2.2],
        by rw [Mem.update_self]⟩)
  have s13 : RunsTo (addTo 8 8 10)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 3) ∧ v 10 = 1) A)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 4)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 8), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 8), hw.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 8), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 8), hw.2.2.2.1],
        by rw [Mem.update_self, hw.2.2.2.2.1, hw.2.2.2.2.2]; omega⟩)
  have s14 : RunsTo (copyTo 11 8)
      (At K (fun v => v 13 = p ∧ v 15 = p + q + 2 ∧ v 12 = p + q + 3 ∧ v 14 = q ∧
        v 8 = K + (p + q + 4)) A)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 2) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw =>
      ⟨by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 11), hw.2.2.2.2],
        by rw [Mem.update_self, hw.2.2.2.2],
        by rw [Mem.update_of_ne _ _ (by omega : (12:ℕ) ≠ 11), hw.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (13:ℕ) ≠ 11), hw.1],
        by rw [Mem.update_of_ne _ _ (by omega : (14:ℕ) ≠ 11), hw.2.2.2.1],
        by rw [Mem.update_of_ne _ _ (by omega : (15:ℕ) ≠ 11), hw.2.1]⟩)
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
theorem runsTo_stripBody {K : ℕ} (hK : 16 ≤ K) {eb es : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : es.length = q) :
    RunsTo (stripBody K)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 2)
        ((p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es))))
      (At K (fun v => v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3)
        (((p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es))) ++
          ((p + q + 2) :: p :: (eb ++ (q :: es)))))
      (7 * p + 7 * q + 32) := by
  set A : List ℕ := (p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es)) with hA
  have hAlen : A.length = p + q + 4 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hA3 : A.drop 3 = eb ++ (q :: es) := by rw [hA]; simp
  have hseg1 : (A.drop 3).take p = eb := by rw [hA3, ← hp, List.take_left]
  have hdropA : A.drop (4 + p) = es := by
    have h1 : A = ((p + q + 3) :: (p + 1) :: (1:ℕ) :: (eb ++ [q])) ++ es := by rw [hA]; simp
    have h2 : ((p + q + 3) :: (p + 1) :: (1:ℕ) :: (eb ++ [q])).length = 4 + p := by
      simp [hp]; all_goals omega
    rw [h1, ← h2, List.drop_left]
  have hseg2 : (A.drop (4 + p)).take q = es := by rw [hdropA, ← hq, List.take_length]
  set L1 : List ℕ := A ++ [p + q + 2] with hL1
  set L2 : List ℕ := L1 ++ [p] with hL2
  set L3 : List ℕ := L2 ++ eb with hL3
  set L4 : List ℕ := L3 ++ [q] with hL4
  set L5 : List ℕ := L4 ++ es with hL5
  have hL1len : L1.length = p + q + 5 := by rw [hL1]; simp [hAlen]
  have hL2len : L2.length = p + q + 6 := by rw [hL2]; simp [hL1len]
  have hL3len : L3.length = p + q + 6 + p := by rw [hL3]; simp [hL2len, hp]; all_goals omega
  have hL4len : L4.length = p + q + 7 + p := by rw [hL4]; simp [hL3len]; all_goals omega
  have hfinal : L5 = A ++ ((p + q + 2) :: p :: (eb ++ (q :: es))) := by
    rw [hL5, hL4, hL3, hL2, hL1]
    simp [List.append_assoc]
  have s1 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + (p + q + 4) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 15 = p + q + 2) A)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q) L1) 3 := by
    refine runsTo_pushVal (L := A) (v := p + q + 2) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hAlen], hw.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hAlen]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2.1]
  have s2 : RunsTo (pushVal 13)
      (At K (fun v => v 8 = K + (p + q + 5) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q) L1)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
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
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q) L2)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s4 : RunsTo (assign 10 3)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K) L2)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 3) L2) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s5 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 3) L2)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 3) L2) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s6 : RunsTo (copyTo 2 13)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 3) L2)
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 3 ∧ v 2 = p) L2) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL2 : (L2.drop 3).take p = eb := by
    rw [hL2, seg_append L1 [p] 3 p (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 2] 3 p (by rw [hAlen]; omega), hseg1]
  have s7 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 6) ∧ v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3 ∧
        v 13 = p ∧ v 14 = q ∧ v 0 = K + 3 ∧ v 2 = p) L2)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q) L3) (7 * p + 7) := by
    have hlist : L3 = L2 ++ (L2.drop 3).take p := by rw [hsegL2, hL3]
    rw [hlist]
    refine runsTo_pushBlock (L := L2) hK (i := 3) (c := p) (by rw [hL2len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL2len], hw.2.2.2.2.2.1, hw.2.2.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL2len]; omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.1]
  have s8 : RunsTo (pushVal 14)
      (At K (fun v => v 8 = K + (p + q + 6 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q) L3)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q) L4) 3 := by
    refine runsTo_pushVal (L := L3) (v := q) hK (by omega) (by omega)
      (fun w hw => ⟨by rw [hw.1, hL3len], hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [h8, hL3len]; omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.2]
  have s9 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q) L4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L4) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s10 : RunsTo (assign 10 4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K) L4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 4) L4) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s11 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K ∧ v 10 = 4) L4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 4) L4) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2.1, hw.2.2.2.2.2.2])
  have s12 : RunsTo (addTo 0 0 13)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 13 = p ∧ v 14 = q ∧ v 0 = K + 4) L4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 14 = q ∧ v 0 = K + (4 + p)) L4) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.2.2, hw.2.2.2.1]
      omega)
  have s13 : RunsTo (copyTo 2 14)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 14 = q ∧ v 0 = K + (4 + p)) L4)
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 0 = K + (4 + p) ∧ v 2 = q) L4) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2.1], by simp [Mem.update, hw.2.2.2.2], ?_⟩
      simp only [Mem.update_self, hw.2.2.2.1])
  have hsegL4 : (L4.drop (4 + p)).take q = es := by
    rw [hL4, seg_append L3 [q] (4 + p) q (by rw [hL3len]; omega),
      hL3, seg_append L2 eb (4 + p) q (by rw [hL2len]; omega),
      hL2, seg_append L1 [p] (4 + p) q (by rw [hL1len]; omega),
      hL1, seg_append A [p + q + 2] (4 + p) q (by rw [hAlen]; omega), hseg2]
  have s14 : RunsTo pushBlock
      (At K (fun v => v 8 = K + (p + q + 7 + p) ∧ v 11 = K + (p + q + 4) ∧
        v 12 = p + q + 3 ∧ v 0 = K + (4 + p) ∧ v 2 = q) L4)
      (At K (fun v => v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3) L5) (7 * q + 7) := by
    have hlist : L5 = L4 ++ (L4.drop (4 + p)).take q := by rw [hsegL4, hL5]
    rw [hlist]
    refine runsTo_pushBlock (L := L4) hK (i := 4 + p) (c := q) (by rw [hL4len]; omega)
      (fun w hw => ⟨by rw [hw.1, hL4len], hw.2.2.2.1, hw.2.2.2.2⟩)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
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
  have hmain := s1.seq c2
  rw [← hfinal]
  exact hmain.mono (by omega)

set_option maxHeartbeats 1000000 in
/-- **Stripping the tag.**  From the workspace holding the encoding of `(some b, s)` the routine
produces the workspace holding the encoding of `(b, s)`. -/
theorem runsTo_stripProg {K : ℕ} (hK : 16 ≤ K) {eb es : List ℕ} {p q : ℕ}
    (hp : eb.length = p) (hq : es.length = q) :
    RunsTo (stripProg K)
      (fun m => m = initMemAt K ((p + 1) :: 1 :: (eb ++ (q :: es))))
      (fun m' => m' = initMemAt K (p :: (eb ++ (q :: es))))
      (19 * p + 19 * q + K + 104) := by
  set A : List ℕ := (p + q + 3) :: (p + 1) :: 1 :: (eb ++ (q :: es)) with hA
  set B : List ℕ := (p + q + 2) :: p :: (eb ++ (q :: es)) with hB
  have hAlen : A.length = p + q + 4 := by rw [hA]; simp [hp, hq]; all_goals omega
  have hBlen : B.length = p + q + 3 := by rw [hB]; simp [hp, hq]; all_goals omega
  have hin : initMemAt K ((p + 1) :: 1 :: (eb ++ (q :: es))) = memAt K (fun _ => 0) A := by
    rw [initMemAt_eq_memAt, hA]
    congr 1
    simp [hp, hq]
    all_goals omega
  have hout : initMemAt K (p :: (eb ++ (q :: es))) = memAt K (fun _ => 0) B := by
    rw [initMemAt_eq_memAt, hB]
    congr 1
    simp [hp, hq]
    all_goals omega
  have sfin : RunsTo (finish K)
      (At K (fun v => v 11 = K + (p + q + 4) ∧ v 12 = p + q + 3) (A ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (p + q + 3) + 5 * (p + q + 4) + K + 17) := by
    refine (runsTo_finish (L₀ := A) (B := B) hK (fun w hw => ⟨by rw [hw.1, hAlen], ?_⟩)).mono ?_
    · rw [hw.2, hBlen]
    · rw [hAlen, hBlen]
  have hmain := (runsTo_stripHead hK hp hq).seq ((runsTo_stripBody hK hp hq).seq sfin)
  refine hmain.conseq (fun m hm => ?_) (fun m hm => ?_) (by omega)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hin]⟩
  · rw [hm, hout]

/-- The dispatcher on the tag of an `Option` in the first component of a pair. -/
def optElimProg (K : ℕ) (Pg Ph : Program) : Program :=
  ifz (K + 2) (seq (stripProg K) Ph) (seq (Combine.sndProg K) Pg)

end Lists

/-! ## `Option.elim` as a combinator -/

set_option maxHeartbeats 1000000 in
/-- **Case analysis on an `Option` carried alongside a state.**  For `(o, s) : Option β × σ` the
routine answers `g s` when `o` is `none` and `h (b, s)` when `o` is `some b`. -/
theorem cleanComputeAt_optionElim [Enc β] [Enc σ] [Enc γ] {K : ℕ} (hK : 16 ≤ K)
    (hb : Nonempty β) {Pg Ph : Program} {g : σ → γ} {h : β × σ → γ} {Tg Th : ℕ → ℕ}
    (hg : CleanComputeAt K Pg g Tg) (hh : CleanComputeAt K Ph h Th)
    (hTg : ∀ n n', n ≤ n' → Tg n ≤ Tg n') (hTh : ∀ n n', n ≤ n' → Th n ≤ Th n') :
    CleanComputeAt K (Lists.optElimProg K Pg Ph)
      (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2)))
      (fun n => 2 * (43 * n + 2 * K + 184 + (Tg n + Th n)) + 2) := by
  haveI := hb
  rintro ⟨o, s⟩
  have hreg := initMemAt_option_tag (K := K) o s
  have hsnd := Combine.cleanComputeAt_snd (α := Option β) (β := σ) hK (o, s)
  have hnone : RunsTo (seq (Combine.sndProg K) Pg)
      (fun m => m = initMemAt K (Enc.encode ((o, s) : Option β × σ)))
      (fun m' => m' = initMemAt K (Enc.encode (g s)))
      (43 * Enc.size ((o, s) : Option β × σ) + 2 * K + 184
        + (Tg (Enc.size ((o, s) : Option β × σ)) + Th (Enc.size ((o, s) : Option β × σ)))) :=
    (hsnd.seq (hg s)).mono (by
      have := hTg _ _ (Combine.size_snd_le o s)
      dsimp only
      omega)
  have hwfsome : Wf (seq (Lists.stripProg K) Ph) :=
    wf_seq (Lists.runsTo_stripProg (K := K) (eb := []) (es := []) hK rfl rfl).wf
      (hh (Classical.arbitrary β, s)).wf
  cases o with
  | none =>
      have hbr1 : RunsTo (seq (Lists.stripProg K) Ph)
          (fun m => m = initMemAt K (Enc.encode ((none, s) : Option β × σ)) ∧ m (K + 2) ≠ 0)
          (fun m' => m' = initMemAt K (Enc.encode (g s)))
          (43 * Enc.size ((none, s) : Option β × σ) + 2 * K + 184
            + (Tg (Enc.size ((none, s) : Option β × σ))
              + Th (Enc.size ((none, s) : Option β × σ)))) := by
        refine runsTo_of_false hwfsome ?_
        rintro m ⟨hm1, hm2⟩
        rw [hm1, hreg] at hm2
        simp at hm2
      exact (hbr1.ifz (hnone.strengthen (fun m hm => hm.1))).mono (by dsimp only; omega)
  | some b =>
      have henc1 : Enc.encode ((some b, s) : Option β × σ)
          = ((Enc.encode b).length + 1) :: 1 ::
            (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
        show frame (1 :: Enc.encode b) ++ frame (Enc.encode s) = _
        simp [frame]
      have henc2 : Enc.encode ((b, s) : β × σ)
          = (Enc.encode b).length :: (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
        show frame (Enc.encode b) ++ frame (Enc.encode s) = _
        simp [frame]
      have hlen : (Enc.encode ((some b, s) : Option β × σ)).length
          = (Enc.encode b).length + (Enc.encode s).length + 3 := by
        rw [henc1]; simp; all_goals omega
      have hlt : (Enc.encode b).length + (Enc.encode s).length + 3
          < Enc.size ((some b, s) : Option β × σ) := by
        have h1 := length_lt_listSize (Enc.encode ((some b, s) : Option β × σ))
        rw [hlen] at h1
        exact h1
      have hstrip : RunsTo (Lists.stripProg K)
          (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)))
          (fun m' => m' = initMemAt K (Enc.encode ((b, s) : β × σ)))
          (19 * (Enc.encode b).length + 19 * (Enc.encode s).length + K + 104) := by
        rw [henc1, henc2]
        exact Lists.runsTo_stripProg hK rfl rfl
      have hsome : RunsTo (seq (Lists.stripProg K) Ph)
          (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)))
          (fun m' => m' = initMemAt K (Enc.encode (h (b, s))))
          (43 * Enc.size ((some b, s) : Option β × σ) + 2 * K + 184
            + (Tg (Enc.size ((some b, s) : Option β × σ))
              + Th (Enc.size ((some b, s) : Option β × σ)))) :=
        (hstrip.seq (hh (b, s))).mono (by
          have := hTh _ _ (size_strip_le b s)
          omega)
      have hbr2 : RunsTo (seq (Combine.sndProg K) Pg)
          (fun m => m = initMemAt K (Enc.encode ((some b, s) : Option β × σ)) ∧ m (K + 2) = 0)
          (fun m' => m' = initMemAt K (Enc.encode (h (b, s))))
          (43 * Enc.size ((some b, s) : Option β × σ) + 2 * K + 184
            + (Tg (Enc.size ((some b, s) : Option β × σ))
              + Th (Enc.size ((some b, s) : Option β × σ)))) := by
        refine runsTo_of_false hnone.wf ?_
        rintro m ⟨hm1, hm2⟩
        rw [hm1, hreg] at hm2
        simp at hm2
      exact ((hsome.strengthen (fun m hm => hm.1)).ifz hbr2).mono (by dsimp only; omega)

/-- A size bound transported along a monotone comparison of the argument. -/
theorem sizeBound_aux {c C d D n m X : ℕ} (hc : c ≤ C) (hd : d ≤ D) (hm : m ≤ n)
    (hX : X ≤ c * (m + 1) ^ d) : X ≤ C * (n + 1) ^ D := by
  have h1 : c * (m + 1) ^ d ≤ c * (n + 1) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
  have h2 : c * (n + 1) ^ d ≤ c * (n + 1) ^ D :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)
  have h3 : c * (n + 1) ^ D ≤ C * (n + 1) ^ D := Nat.mul_le_mul_right _ hc
  omega

theorem sizeBound_optionElim [Enc β] [Enc σ] [Enc γ] {g : σ → γ} {h : β × σ → γ}
    (hg : SizeBound g) (hh : SizeBound h) :
    SizeBound (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  obtain ⟨cg, dg, hcg⟩ := hg
  obtain ⟨ch, dh, hch⟩ := hh
  refine ⟨cg + ch, max dg dh, ?_⟩
  rintro ⟨o, s⟩
  cases o with
  | none => exact sizeBound_aux (by omega) (le_max_left _ _) (Combine.size_snd_le _ s) (hcg s)
  | some b =>
      exact sizeBound_aux (by omega) (le_max_right _ _) (size_strip_le b s) (hch (b, s))

set_option maxRecDepth 4000 in
theorem polyTimeCleanAt_optionElim [Enc β] [Enc σ] [Enc γ] {K : ℕ} (hK : 16 ≤ K)
    (hb : Nonempty β) {g : σ → γ} {h : β × σ → γ} (hg : PolyTimeCleanAt K g)
    (hh : PolyTimeCleanAt K h) :
    PolyTimeCleanAt K (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  obtain ⟨Pg, Tg, ⟨cg, dg, hcg⟩, hPg⟩ := hg
  obtain ⟨Ph, Th, ⟨ch, dh, hch⟩, hPh⟩ := hh
  refine ⟨Lists.optElimProg K Pg Ph, _, ?_,
    cleanComputeAt_optionElim hK hb (hPg.mono hcg) (hPh.mono hch)
      (fun n n' hn => polyBound_witness_mono cg dg hn)
      (fun n n' hn => polyBound_witness_mono ch dh hn)⟩
  exact ((polyBound_const 2).mul ((((polyBound_const 43).mul polyBound_id).add
    (polyBound_const (2 * K + 184))).add ((polyBound_witness cg dg).add
    (polyBound_witness ch dh)))).add (polyBound_const 2)

/-- **`Option.elim` with a case-dependent default is a `PolyFun`.**  This is the combinator that
makes the payload of an `Option` usable: the `some` branch receives the payload paired with the
state, so no element of `β` has to be produced in the `none` branch. -/
theorem PolyFun.optionElim [Enc β] [Enc σ] [Enc γ] {g : σ → γ} {h : β × σ → γ}
    (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2))) := by
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine (polyFun_snd.comp hg).of_eq (fun p => ?_)
    obtain ⟨o, s⟩ := p
    cases o with
    | none => rfl
    | some b => exact (hβ.false b).elim
  · exact ⟨polyTimeCleanAt_optionElim (by omega) hβ hg.time hh.time,
      sizeBound_optionElim hg.size hh.size⟩

/-- **Case analysis on a list carried alongside a state.**  The empty case runs `g` on the state,
the nonempty case runs `h` on the head, the tail and the state.  This is the shape every list
traversal is written in. -/
theorem PolyFun.listCases [Enc α] [Enc σ] [Enc γ] {g : σ → γ} {h : (α × List α) × σ → γ}
    (hg : PolyFun g) (hh : PolyFun h) :
    PolyFun (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2)) := by
  have huncons : PolyFun (fun p : List α × σ => (uncons p.1, p.2)) :=
    (polyFun_fst.comp polyFun_uncons).pair polyFun_snd
  refine (huncons.comp (hg.optionElim hh)).of_eq (fun p => ?_)
  obtain ⟨l, s⟩ := p
  cases l with
  | nil => rfl
  | cons a t => rfl

/-! ## The trivial constructors -/

theorem polyFun_nil [Enc α] [Enc β] : PolyFun (fun _ : α => ([] : List β)) :=
  polyFun_const _

theorem polyFun_none [Enc α] [Enc β] : PolyFun (fun _ : α => (none : Option β)) :=
  polyFun_const _

end RAM
