import Workspace.Machine.Pairing

/-!
# Projections, the conditional and bounded iteration at the workspace convention

With pairing (`Workspace/Machine/Pairing.lean`) available, the remaining combinators of the
assembly language are short:

* the **projections** `Prod.fst`, `Prod.snd` need no call at all — the answer is a block of the
  input, copied to the top of the workspace and moved down to the base by
  `RAM.Layout.finish`;
* the **conditional** `a ↦ if p a then f a else g a` is `h (p a, a)` with
  `h (b, x) = if b then f x else g x`, so it is pairing with the identity, composition, and one
  test of the register holding the bit.  The bit of a pair `(b, x)` sits in the *fixed* register
  `K + 2` of the workspace convention (the encoding of the pair is `1 :: b :: ...`), so the test
  is literally `ifz (K + 2)`;
* **bounded iteration** `a ↦ step^[k a] a` is the loop `whileNz (K + 2)` of
  `Workspace/Machine/Recursion.lean`, at the workspace convention: the counter of the pair
  `(k, s)` is in register `K + 2` for the same reason.

## Main results

* `RAM.Combine.cleanComputeAt_fst`, `RAM.Combine.cleanComputeAt_snd`, and the class forms
  `RAM.polyTimeCleanAt_fst`, `RAM.polyTimeCleanAt_snd`;
* `RAM.Combine.cleanComputeAt_ite`, `RAM.polyTimeCleanAt_ite`: the conditional;
* `RAM.Combine.runsTo_iterateAt`, `RAM.Combine.cleanComputeAt_iterate`,
  `RAM.polyTimeCleanAt_iterate`: bounded iteration, with the size hypothesis on the
  intermediate states that the statement genuinely needs.
-/

namespace RAM
namespace Combine

open Layout

/-! ## The common ending: one block down to the base

`finPart r K` sets register `12` to `R r + 1` — the length of the block consisting of a length
field and `R r` entries — and runs `RAM.Layout.finish`. -/

/-- The common ending of the two projections. -/
def finPart (r K : ℕ) : Program := seq (assign 10 1) (seq (addTo 12 r 10) (finish K))

theorem runsTo_finPart {K r : ℕ} (hK : 16 ≤ K) (hr : r < K) (hr10 : r ≠ 10) (hr12 : r ≠ 12)
    {L₀ B : List ℕ} {c : ℕ} (hBlen : B.length = c + 1) {Q : Mem → Prop}
    (hQ : ∀ w, Q w → w 11 = K + L₀.length ∧ w r = c) :
    RunsTo (finPart r K) (At K Q (L₀ ++ B)) (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (c + 1) + 5 * L₀.length + K + 19) := by
  refine RunsTo.mono (T := 1 + (1 + (7 * B.length + 5 * L₀.length + K + 17))) ?_ (by omega)
  refine RunsTo.seq (mid := At K (fun v => v 11 = K + L₀.length ∧ v r = c ∧ v 10 = 1) (L₀ ++ B))
    (runsTo_assignReg (by omega) (fun w hw => ?_)) ?_
  · exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 10), (hQ w hw).1],
      by rw [Mem.update_of_ne _ _ hr10, (hQ w hw).2], by rw [Mem.update_self]⟩
  refine RunsTo.seq (mid := At K (fun v => v 11 = K + L₀.length ∧ v 12 = B.length) (L₀ ++ B))
    (runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => ?_)) ?_
  · refine ⟨by rw [Mem.update_of_ne _ _ (by omega : (11:ℕ) ≠ 12), hw.1], ?_⟩
    rw [Mem.update_self, hw.2.1, hw.2.2, hBlen]
  exact runsTo_finish hK (fun w hw => ⟨hw.1, hw.2⟩)

/-! ## The projections -/

/-- The first component: copy the first block of the pair to the top of the workspace and move
it down to the base. -/
def fstProg (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
    (seq (addTo 8 8 10) (seq (copyTo 11 8) (seq (copyTo 14 (K + 1)) (seq (pushVal 14)
      (seq (assign 0 K) (seq (assign 10 2) (seq (addTo 0 0 10) (seq (copyTo 2 14)
        (seq pushBlock (finPart 14 K)))))))))))))

set_option maxHeartbeats 1000000 in
theorem runsTo_fstProg {K : ℕ} (hK : 16 ≤ K) (X Y : List ℕ) :
    RunsTo (fstProg K)
      (fun m => m = initMemAt K ((X.length :: X) ++ (Y.length :: Y)))
      (fun m' => m' = initMemAt K X)
      (19 * X.length + 5 * Y.length + K + 70) := by
  obtain ⟨P, hP⟩ : ∃ P, P = (X.length :: X) ++ (Y.length :: Y) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = P.length :: P := ⟨_, rfl⟩
  have hPlen : P.length = X.length + Y.length + 2 := by rw [hP]; simp; omega
  have hLlen : L.length = X.length + Y.length + 3 := by rw [hL]; simp [hPlen]
  have hL0 : L.getD 0 0 = P.length := by rw [hL]; simp
  have hL1 : L.getD 1 0 = X.length := by rw [hL, hP]; simp
  have hseg : (((L ++ [X.length]).drop 2).take X.length) = X := by
    rw [seg_append L [X.length] 2 X.length (by rw [hLlen]; omega)]
    have hsplit : L = [P.length, X.length] ++ (X ++ (Y.length :: Y)) := by
      rw [hL, hP]; simp
    rw [hsplit]
    exact seg_middle [P.length, X.length] X (Y.length :: Y)
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) L)
      (At K (fun v => v 9 = P.length) L) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by rw [Mem.update_self, hL0])
  have s2 : RunsTo (assign 8 K) (At K (fun v => v 9 = P.length) L)
      (At K (fun v => v 9 = P.length ∧ v 8 = K) L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s3 : RunsTo (addTo 8 8 9) (At K (fun v => v 9 = P.length ∧ v 8 = K) L)
      (At K (fun v => v 8 = K + P.length) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (assign 10 1) (At K (fun v => v 8 = K + P.length) L)
      (At K (fun v => v 8 = K + P.length ∧ v 10 = 1) L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s5 : RunsTo (addTo 8 8 10) (At K (fun v => v 8 = K + P.length ∧ v 10 = 1) L)
      (At K (fun v => v 8 = K + L.length) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      rw [Mem.update_self, hw.1, hw.2, hLlen, hPlen]; omega)
  have s6 : RunsTo (copyTo 11 8) (At K (fun v => v 8 = K + L.length) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length) L) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by simp [Mem.update, hw])
  have s7 : RunsTo (copyTo 14 (K + 1))
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length) L) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw => ⟨by
      simp [Mem.update, hw.1], by simp [Mem.update, hw.2], by rw [Mem.update_self, hL1]⟩)
  have s8 : RunsTo (pushVal 14)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length) L)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length)
        (L ++ [X.length])) 3 := by
    refine runsTo_pushVal (L := L) (v := X.length) hK (by omega) (by omega)
      (fun w hw => ⟨hw.1, hw.2.2⟩) (fun w w' hw hagree h8 h10 => ⟨h8, ?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2]
  have s9 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length)
        (L ++ [X.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K) (L ++ [X.length])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s10 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K) (L ++ [X.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K ∧ v 10 = 2) (L ++ [X.length])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s11 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K ∧ v 10 = 2) (L ++ [X.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2) (L ++ [X.length])) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s12 : RunsTo (copyTo 2 14)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2) (L ++ [X.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2 ∧ v 2 = X.length) (L ++ [X.length])) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s13 : RunsTo pushBlock
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2 ∧ v 2 = X.length) (L ++ [X.length]))
      (At K (fun v => v 11 = K + L.length ∧ v 14 = X.length) ((L ++ [X.length]) ++ X))
      (7 * X.length + 7) := by
    have hlist : (L ++ [X.length]) ++ (((L ++ [X.length]).drop 2).take X.length)
        = (L ++ [X.length]) ++ X := by rw [hseg]
    refine RunsTo.weaken ?_ (fun m hm => by rw [← hlist]; exact hm)
    refine runsTo_pushBlock (L := L ++ [X.length]) hK (i := 2) (c := X.length)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hLlen]; omega)
      (fun w hw => ?_) (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · refine ⟨?_, hw.2.2.2.1, hw.2.2.2.2⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have s14 : RunsTo (finPart 14 K)
      (At K (fun v => v 11 = K + L.length ∧ v 14 = X.length) ((L ++ [X.length]) ++ X))
      (fun m' => m' = memAt K (fun _ => 0) (X.length :: X))
      (7 * (X.length + 1) + 5 * L.length + K + 19) := by
    have hlist : (L ++ [X.length]) ++ X = L ++ (X.length :: X) := by simp
    rw [hlist]
    exact runsTo_finPart (c := X.length) hK (by omega) (by omega) (by omega) (by simp)
      (fun w hw => ⟨hw.1, hw.2⟩)
  have hchain := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
    (s10.seq (s11.seq (s12.seq (s13.seq s14))))))))))))
  refine (hchain.conseq (fun m hm => ?_) (fun m hm => ?_) ?_)
  · exact ⟨fun _ => 0, trivial, by rw [hm, ← hP, initMemAt_eq_memAt, ← hL]⟩
  · rw [hm, initMemAt_eq_memAt]
  · rw [hLlen]; omega

/-- The second component: read the length of the second block through a pointer, copy that block
to the top of the workspace and move it down to the base. -/
def sndProg1 (K : ℕ) : Program :=
  seq (copyTo 9 K) (seq (assign 8 K) (seq (addTo 8 8 9) (seq (assign 10 1)
    (seq (addTo 8 8 10) (seq (copyTo 11 8) (seq (copyTo 14 (K + 1)) (seq (assign 0 K)
      (seq (assign 10 2) (seq (addTo 0 0 10) (seq (addTo 0 0 14) (loadTo 15 0)))))))))))

/-- The second half: copy the second block up and move it down to the base. -/
def sndProg2 (K : ℕ) : Program :=
  seq (pushVal 15) (seq (assign 10 1) (seq (addTo 0 0 10) (seq (copyTo 2 15)
    (seq pushBlock (finPart 15 K)))))

/-- The second component. -/
def sndProg (K : ℕ) : Program := seq (sndProg1 K) (sndProg2 K)

set_option maxHeartbeats 1000000 in
theorem runsTo_sndProg {K : ℕ} (hK : 16 ≤ K) (X Y : List ℕ) :
    RunsTo (sndProg K)
      (fun m => m = initMemAt K ((X.length :: X) ++ (Y.length :: Y)))
      (fun m' => m' = initMemAt K Y)
      (19 * Y.length + 5 * X.length + K + 80) := by
  obtain ⟨P, hP⟩ : ∃ P, P = (X.length :: X) ++ (Y.length :: Y) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = P.length :: P := ⟨_, rfl⟩
  have hPlen : P.length = X.length + Y.length + 2 := by rw [hP]; simp; omega
  have hLlen : L.length = X.length + Y.length + 3 := by rw [hL]; simp [hPlen]
  have hL0 : L.getD 0 0 = P.length := by rw [hL]; simp
  have hL1 : L.getD 1 0 = X.length := by rw [hL, hP]; simp
  have hsplit : L = (([P.length, X.length] ++ X) ++ [Y.length]) ++ (Y ++ []) := by
    rw [hL, hP]; simp
  have hL2 : L.getD (X.length + 2) 0 = Y.length := by
    rw [hL, hP]
    have : (X.length :: X ++ Y.length :: Y).getD (X.length + 1) 0 = Y.length := by
      rw [List.getD_append_right (X.length :: X) _ 0 _ (by simp)]
      simp
    simpa using this
  have hseg : (((L ++ [Y.length]).drop (X.length + 3)).take Y.length) = Y := by
    rw [seg_append L [Y.length] (X.length + 3) Y.length (by rw [hLlen]; omega)]
    have hlen : (([P.length, X.length] ++ X) ++ [Y.length]).length = X.length + 3 := by simp
    rw [hsplit, ← hlen, seg_middle]
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) L)
      (At K (fun v => v 9 = P.length) L) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by rw [Mem.update_self, hL0])
  have s2 : RunsTo (assign 8 K) (At K (fun v => v 9 = P.length) L)
      (At K (fun v => v 9 = P.length ∧ v 8 = K) L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s3 : RunsTo (addTo 8 8 9) (At K (fun v => v 9 = P.length ∧ v 8 = K) L)
      (At K (fun v => v 8 = K + P.length) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (assign 10 1) (At K (fun v => v 8 = K + P.length) L)
      (At K (fun v => v 8 = K + P.length ∧ v 10 = 1) L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s5 : RunsTo (addTo 8 8 10) (At K (fun v => v 8 = K + P.length ∧ v 10 = 1) L)
      (At K (fun v => v 8 = K + L.length) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      rw [Mem.update_self, hw.1, hw.2, hLlen, hPlen]; omega)
  have s6 : RunsTo (copyTo 11 8) (At K (fun v => v 8 = K + L.length) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length) L) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by simp [Mem.update, hw])
  have s7 : RunsTo (copyTo 14 (K + 1))
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length) L) 1 :=
    runsTo_copyFromList (i := 1) (by omega) (fun w hw => ⟨by
      simp [Mem.update, hw.1], by simp [Mem.update, hw.2], by rw [Mem.update_self, hL1]⟩)
  have s8 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧ v 0 = K)
        L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s9 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧ v 0 = K) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧ v 0 = K ∧
        v 10 = 2) L) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s10 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧ v 0 = K ∧
        v 10 = 2) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s11 : RunsTo (addTo 0 0 14)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧ v 14 = X.length ∧
        v 0 = K + 2) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2)) L) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_⟩
      simp only [Mem.update_self, hw.2.2.1, hw.2.2.2]
      omega)
  have s12 : RunsTo (loadTo 15 0)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2)) L)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length) L) 1 := by
    refine runsTo_loadReg (i := X.length + 2) (by omega) (by omega) (fun w hw => hw.2.2)
      (fun w hw => ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1],
        by simp [Mem.update, hw.2.2], ?_⟩)
    rw [Mem.update_self, hL2]
  have s13 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + L.length ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length) L)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length) (L ++ [Y.length])) 3 := by
    refine runsTo_pushVal (L := L) (v := Y.length) hK (by omega) (by omega)
      (fun w hw => ⟨hw.1, hw.2.2.2⟩) (fun w w' hw hagree h8 h10 => ⟨h8, ?_, ?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 0 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 15 (by omega) (by omega), hw.2.2.2]
  have s14 : RunsTo (assign 10 1)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length) (L ++ [Y.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length ∧ v 10 = 1) (L ++ [Y.length])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s15 : RunsTo (addTo 0 0 10)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 2) ∧ v 15 = Y.length ∧ v 10 = 1) (L ++ [Y.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 3) ∧ v 15 = Y.length) (L ++ [Y.length])) 1 := by
    refine runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => ?_)
    refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_,
      by simp [Mem.update, hw.2.2.2.1]⟩
    simp only [Mem.update_self, hw.2.2.1, hw.2.2.2.2]
    omega
  have s16 : RunsTo (copyTo 2 15)
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 3) ∧ v 15 = Y.length) (L ++ [Y.length]))
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 3) ∧ v 15 = Y.length ∧ v 2 = Y.length) (L ++ [Y.length])) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s17 : RunsTo pushBlock
      (At K (fun v => v 8 = K + L.length + 1 ∧ v 11 = K + L.length ∧
        v 0 = K + (X.length + 3) ∧ v 15 = Y.length ∧ v 2 = Y.length) (L ++ [Y.length]))
      (At K (fun v => v 11 = K + L.length ∧ v 15 = Y.length) ((L ++ [Y.length]) ++ Y))
      (7 * Y.length + 7) := by
    have hlist : (L ++ [Y.length]) ++ (((L ++ [Y.length]).drop (X.length + 3)).take Y.length)
        = (L ++ [Y.length]) ++ Y := by rw [hseg]
    refine RunsTo.weaken ?_ (fun m hm => by rw [← hlist]; exact hm)
    refine runsTo_pushBlock (L := L ++ [Y.length]) hK (i := X.length + 3) (c := Y.length)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [hLlen]; omega)
      (fun w hw => ?_) (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · refine ⟨?_, hw.2.2.1, hw.2.2.2.2⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 15 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
  have s18 : RunsTo (finPart 15 K)
      (At K (fun v => v 11 = K + L.length ∧ v 15 = Y.length) ((L ++ [Y.length]) ++ Y))
      (fun m' => m' = memAt K (fun _ => 0) (Y.length :: Y))
      (7 * (Y.length + 1) + 5 * L.length + K + 19) := by
    have hlist : (L ++ [Y.length]) ++ Y = L ++ (Y.length :: Y) := by simp
    rw [hlist]
    exact runsTo_finPart (c := Y.length) hK (by omega) (by omega) (by omega) (by simp)
      (fun w hw => ⟨hw.1, hw.2⟩)
  have hc1 := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12)))))))))))
  have hc2 := s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18)))))
  have hchain := hc1.seq hc2
  refine (hchain.conseq (fun m hm => ?_) (fun m hm => ?_) ?_)
  · exact ⟨fun _ => 0, trivial, by rw [hm, ← hP, initMemAt_eq_memAt, ← hL]⟩
  · rw [hm, initMemAt_eq_memAt]
  · rw [hLlen]; omega

/-! ## Sizes of pairs

The bit length of a pair is at most twice the sum of the bit lengths of its components: framing
a block adds a length field, whose bit length is at most the length of the block. -/

theorem listSize_le_two_mul (l : List ℕ) : listSize (frame l) ≤ 2 * listSize l := by
  have h := length_lt_listSize l
  have h1 : Nat.size l.length ≤ l.length := size_le_self _
  rw [listSize_frame]
  omega

theorem size_pair_le {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    Enc.size ((a, b) : α × β) ≤ 2 * Enc.size a + 2 * Enc.size b := by
  have henc : Enc.encode ((a, b) : α × β) = frame (Enc.encode a) ++ frame (Enc.encode b) := rfl
  have h1 := listSize_le_two_mul (Enc.encode a)
  have h2 := listSize_le_two_mul (Enc.encode b)
  have h3 : Enc.size ((a, b) : α × β) = listSize (frame (Enc.encode a))
      + listSize (frame (Enc.encode b)) - 1 := by
    show listSize (Enc.encode ((a, b) : α × β)) = _
    rw [henc, listSize_append]
  have h4 : 1 ≤ listSize (frame (Enc.encode b)) := by
    have := length_lt_listSize (frame (Enc.encode b)); omega
  have h5 : Enc.size a = listSize (Enc.encode a) := rfl
  have h6 : Enc.size b = listSize (Enc.encode b) := rfl
  omega

theorem size_fst_le {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    Enc.size a ≤ Enc.size ((a, b) : α × β) := by
  have henc : Enc.encode ((a, b) : α × β) = frame (Enc.encode a) ++ frame (Enc.encode b) := rfl
  have h3 : Enc.size ((a, b) : α × β) = listSize (frame (Enc.encode a))
      + listSize (frame (Enc.encode b)) - 1 := by
    show listSize (Enc.encode ((a, b) : α × β)) = _
    rw [henc, listSize_append]
  have h4 : 1 ≤ listSize (frame (Enc.encode b)) := by
    have := length_lt_listSize (frame (Enc.encode b)); omega
  have h5 : listSize (Enc.encode a) ≤ listSize (frame (Enc.encode a)) := by
    rw [listSize_frame]; omega
  have h6 : Enc.size a = listSize (Enc.encode a) := rfl
  omega

theorem size_snd_le {α β : Type*} [Enc α] [Enc β] (a : α) (b : β) :
    Enc.size b ≤ Enc.size ((a, b) : α × β) := by
  have henc : Enc.encode ((a, b) : α × β) = frame (Enc.encode a) ++ frame (Enc.encode b) := rfl
  have h3 : Enc.size ((a, b) : α × β) = listSize (frame (Enc.encode a))
      + listSize (frame (Enc.encode b)) - 1 := by
    show listSize (Enc.encode ((a, b) : α × β)) = _
    rw [henc, listSize_append]
  have h4 : 1 ≤ listSize (frame (Enc.encode a)) := by
    have := length_lt_listSize (frame (Enc.encode a)); omega
  have h5 : listSize (Enc.encode b) ≤ listSize (frame (Enc.encode b)) := by
    rw [listSize_frame]; omega
  have h6 : Enc.size b = listSize (Enc.encode b) := rfl
  omega

/-! ## The projections as clean routines -/

variable {α β γ : Type*}

/-- **The first projection** is a clean routine of the workspace convention. -/
theorem cleanComputeAt_fst [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (fstProg K) (Prod.fst : α × β → α) (fun n => 24 * n + K + 70) := by
  rintro ⟨a, b⟩
  have henc : Enc.encode ((a, b) : α × β)
      = ((Enc.encode a).length :: Enc.encode a) ++
        ((Enc.encode b).length :: Enc.encode b) := rfl
  have h := runsTo_fstProg (K := K) hK (Enc.encode a) (Enc.encode b)
  rw [← henc] at h
  refine h.mono ?_
  have h1 : (Enc.encode a).length < Enc.size a := length_lt_listSize _
  have h2 : (Enc.encode b).length < Enc.size b := length_lt_listSize _
  have h3 := size_fst_le a b
  have h4 := size_snd_le a b
  dsimp only
  omega

/-- **The second projection** is a clean routine of the workspace convention. -/
theorem cleanComputeAt_snd [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    CleanComputeAt K (sndProg K) (Prod.snd : α × β → β) (fun n => 24 * n + K + 80) := by
  rintro ⟨a, b⟩
  have henc : Enc.encode ((a, b) : α × β)
      = ((Enc.encode a).length :: Enc.encode a) ++
        ((Enc.encode b).length :: Enc.encode b) := rfl
  have h := runsTo_sndProg (K := K) hK (Enc.encode a) (Enc.encode b)
  rw [← henc] at h
  refine h.mono ?_
  have h1 : (Enc.encode a).length < Enc.size a := length_lt_listSize _
  have h2 : (Enc.encode b).length < Enc.size b := length_lt_listSize _
  have h3 := size_fst_le a b
  have h4 := size_snd_le a b
  dsimp only
  omega

end Combine

/-- **The first projection in polynomial time** at the workspace convention. -/
theorem polyTimeCleanAt_fst {α β : Type*} [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (Prod.fst : α × β → α) :=
  ⟨Combine.fstProg K, _, ((polyBound_const 24).mul polyBound_id).add
    (polyBound_const (K + 70)), Combine.cleanComputeAt_fst hK⟩

/-- **The second projection in polynomial time** at the workspace convention. -/
theorem polyTimeCleanAt_snd {α β : Type*} [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) :
    PolyTimeCleanAt K (Prod.snd : α × β → β) :=
  ⟨Combine.sndProg K, _, ((polyBound_const 24).mul polyBound_id).add
    (polyBound_const (K + 80)), Combine.cleanComputeAt_snd hK⟩

/-! ## The conditional

`a ↦ if p a then f a else g a` is `h (p a, a)` with `h (b, x) = if b then f x else g x`: pairing
with the identity, then one test of the register that holds the bit of the pair. -/

namespace Combine

/-- The bit of a pair `(b, x) : Bool × α` sits in the fixed register `K + 2` of the workspace
convention, because the encoding of the pair is `1 :: b :: ...`. -/
theorem initMemAt_bool_reg {α : Type*} [Enc α] {K : ℕ} (b : Bool) (x : α) :
    initMemAt K (Enc.encode ((b, x) : Bool × α)) (K + 2) = (if b then 1 else 0) := by
  rw [initMemAt_add]
  show initMem (frame (Enc.encode b) ++ frame (Enc.encode x)) 2 = _
  cases b <;> simp [initMem, frame, Enc.encode]

/-- A bit has size at most `3`. -/
theorem size_bool_le (b : Bool) : Enc.size b ≤ 3 := by
  show listSize (Enc.encode b) ≤ 3
  cases b <;> simp [listSize, Enc.encode, Nat.size]

/-- The routine that dispatches on the first component of a pair: it keeps the second component
and then runs `Pf` or `Pg` according to the bit. -/
def iteProg (K : ℕ) (Pf Pg : Program) : Program :=
  ifz (K + 2) (seq (sndProg K) Pf) (seq (sndProg K) Pg)

/-- **The conditional on a pair.**  `(b, x) ↦ if b then f x else g x` is clean at the workspace
convention. -/
theorem cleanComputeAt_iteOfPair {α β : Type*} [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K)
    {Pf Pg : Program} {f g : α → β} {Tf Tg : ℕ → ℕ}
    (hf : CleanComputeAt K Pf f Tf) (hg : CleanComputeAt K Pg g Tg)
    (hTf : ∀ n n', n ≤ n' → Tf n ≤ Tf n') (hTg : ∀ n n', n ≤ n' → Tg n ≤ Tg n') :
    CleanComputeAt K (iteProg K Pf Pg) (fun q : Bool × α => if q.1 then f q.2 else g q.2)
      (fun n => 2 * (24 * n + (K + 80) + (Tf n + Tg n)) + 2) := by
  rintro ⟨b, x⟩
  have hsize : Enc.size x ≤ Enc.size ((b, x) : Bool × α) := size_snd_le b x
  have hsnd := cleanComputeAt_snd (α := Bool) (β := α) hK (b, x)
  have hbF : RunsTo (seq (sndProg K) Pf)
      (fun m => m = initMemAt K (Enc.encode ((b, x) : Bool × α)))
      (fun m' => m' = initMemAt K (Enc.encode (f x)))
      (24 * Enc.size ((b, x) : Bool × α) + K + 80 + Tf (Enc.size ((b, x) : Bool × α))
        + Tg (Enc.size ((b, x) : Bool × α))) :=
    (hsnd.seq (hf x)).mono (by
      have h := hTf _ _ hsize
      dsimp only
      omega)
  have hbG : RunsTo (seq (sndProg K) Pg)
      (fun m => m = initMemAt K (Enc.encode ((b, x) : Bool × α)))
      (fun m' => m' = initMemAt K (Enc.encode (g x)))
      (24 * Enc.size ((b, x) : Bool × α) + K + 80 + Tf (Enc.size ((b, x) : Bool × α))
        + Tg (Enc.size ((b, x) : Bool × α))) :=
    (hsnd.seq (hg x)).mono (by
      have h := hTg _ _ hsize
      dsimp only
      omega)
  have hreg := initMemAt_bool_reg (K := K) b x
  cases b
  · have hbranchF : RunsTo (seq (sndProg K) Pf)
        (fun m => m = initMemAt K (Enc.encode ((false, x) : Bool × α))
          ∧ m (K + 2) ≠ 0) (fun m' => m' = initMemAt K (Enc.encode (g x)))
        (24 * Enc.size ((false, x) : Bool × α) + K + 80
          + Tf (Enc.size ((false, x) : Bool × α)) + Tg (Enc.size ((false, x) : Bool × α))) := by
      refine runsTo_of_false hbF.wf (fun m hm => ?_)
      obtain ⟨hm1, hm2⟩ := hm
      rw [hm1, hreg] at hm2
      simp at hm2
    have hbranchG : RunsTo (seq (sndProg K) Pg)
        (fun m => m = initMemAt K (Enc.encode ((false, x) : Bool × α))
          ∧ m (K + 2) = 0) (fun m' => m' = initMemAt K (Enc.encode (g x)))
        (24 * Enc.size ((false, x) : Bool × α) + K + 80
          + Tf (Enc.size ((false, x) : Bool × α)) + Tg (Enc.size ((false, x) : Bool × α))) := by
      refine hbG.strengthen (fun m hm => ?_)
      exact hm.1
    exact (RunsTo.ifz hbranchF hbranchG).mono (by dsimp only; omega)
  · have hbranchF : RunsTo (seq (sndProg K) Pf)
        (fun m => m = initMemAt K (Enc.encode ((true, x) : Bool × α))
          ∧ m (K + 2) ≠ 0) (fun m' => m' = initMemAt K (Enc.encode (f x)))
        (24 * Enc.size ((true, x) : Bool × α) + K + 80
          + Tf (Enc.size ((true, x) : Bool × α)) + Tg (Enc.size ((true, x) : Bool × α))) := by
      refine hbF.strengthen (fun m hm => ?_)
      exact hm.1
    have hbranchG : RunsTo (seq (sndProg K) Pg)
        (fun m => m = initMemAt K (Enc.encode ((true, x) : Bool × α))
          ∧ m (K + 2) = 0) (fun m' => m' = initMemAt K (Enc.encode (f x)))
        (24 * Enc.size ((true, x) : Bool × α) + K + 80
          + Tf (Enc.size ((true, x) : Bool × α)) + Tg (Enc.size ((true, x) : Bool × α))) := by
      refine runsTo_of_false hbG.wf (fun m hm => ?_)
      obtain ⟨hm1, hm2⟩ := hm
      rw [hm1, hreg] at hm2
      simp at hm2
    exact (RunsTo.ifz hbranchF hbranchG).mono (by dsimp only; omega)

end Combine

/-- **The conditional in polynomial time** at the workspace convention: for a clean predicate `p`
and clean routines `f`, `g`, the map `a ↦ if p a then f a else g a` is clean. -/
theorem polyTimeCleanAt_ite {α β : Type*} [Enc α] [Enc β] {K : ℕ} (hK : 16 ≤ K) {p : α → Bool}
    {f g : α → β} (hp : PolyTimeCleanAt K p) (hf : PolyTimeCleanAt K f)
    (hg : PolyTimeCleanAt K g) : PolyTimeCleanAt K (fun a => if p a then f a else g a) := by
  have hid : PolyTimeCleanAt K (fun a : α => a) :=
    polyTimeCleanAt_of_polyTimeClean (by omega) polyTimeClean_id
  have hpair : PolyTimeCleanAt K (fun a => (p a, a)) :=
    polyTimeCleanAt_pair (Sf := fun _ => 3) (Sg := fun n => n) hK hp hid
      (polyBound_const 3) polyBound_id (fun a => Combine.size_bool_le _) (fun a => le_refl _)
  have hh : PolyTimeCleanAt K (fun q : Bool × α => if q.1 then f q.2 else g q.2) := by
    obtain ⟨Pf, Tf, ⟨cf, df, hcf⟩, hPf⟩ := hf
    obtain ⟨Pg, Tg, ⟨cg, dg, hcg⟩, hPg⟩ := hg
    refine ⟨Combine.iteProg K Pf Pg, _, ?_,
      Combine.cleanComputeAt_iteOfPair hK (hPf.mono hcf) (hPg.mono hcg)
        (fun n n' h => polyBound_witness_mono cf df h)
        (fun n n' h => polyBound_witness_mono cg dg h)⟩
    exact ((polyBound_const 2).mul ((((polyBound_const 24).mul polyBound_id).add
      (polyBound_const (K + 80))).add ((polyBound_witness cf df).add
      (polyBound_witness cg dg)))).add (polyBound_const 2)
  exact hpair.comp hh (S := fun n => 2 * n + 6)
    (((polyBound_const 2).mul polyBound_id).add (polyBound_const 6))
    (fun a => by
      have h1 := Combine.size_pair_le (p a) a
      have h2 := Combine.size_bool_le (p a)
      dsimp only
      omega)

end RAM
