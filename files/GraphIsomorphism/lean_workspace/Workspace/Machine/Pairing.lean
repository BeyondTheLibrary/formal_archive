import Workspace.Machine.Layout

/-!
# Pairing at the workspace convention

This file builds the combinator the assembly of the paper's procedures was missing: from clean
routines for `f` and `g` at the workspace convention, a clean routine for `a ↦ (f a, g a)`.
The layout is the one of `Workspace/Machine/DESIGN.md`, carried out with the stage rules of
`Workspace/Machine/Layout.lean`:

1. copy the input block above itself (with `K` zeroed work registers below the copy) and call
   the relocated routine for `g` on the copy;
2. do the same above the result and call the relocated routine for `f`;
3. assemble, above both, the encoding of the pair — the length field, then the framed encoding
   of `f a` copied up, then the framed encoding of `g a` copied up;
4. move that block down to the base, erase everything above it and clear the work registers
   (`RAM.Layout.finish`).

The input survives the two calls because the callee is relocated above it
(`Workspace/Machine/Reloc.lean`); this is what makes the combinator possible at all.

## Main results

* `RAM.Pairing.pairProg`, `RAM.Pairing.runsTo_pairProg`: the program and its specification;
* `RAM.cleanComputeAt_pair`: the clean routine for `a ↦ (f a, g a)`;
* `RAM.polyTimeCleanAt_pair`, `RAM.quasiPolyTimeCleanAt_pair`: the class forms, with the
  polynomial bounds on the sizes of `f a` and `g a` that the running time genuinely needs.
-/

namespace RAM
namespace Pairing

open Layout

/-! ## Stage A: the input above itself, and the call to `g` -/

/-- Set up the top pointer, copy the input block above itself (with `K` zeroed work registers
below it) and call the relocated routine for `g` on the copy.  Register `9` keeps the length of
the input block, register `11` the base address of the call, then the address of the length
field of the result, register `15` the length of the result. -/
def progA (K : ℕ) (Pg : Program) : Program :=
  seq (copyTo 9 K) (seq (assign 10 1) (seq (addTo 9 9 10) (seq (assign 8 K)
    (seq (addTo 8 8 9) (seq (copyTo 11 8) (seq (pushZeros K) (seq (assign 0 K)
      (seq (copyTo 2 9) (seq pushBlock (seq (copyTo 0 11) (seq (callTopAt K Pg)
        (seq (copyTo 11 0) (loadTo 15 11)))))))))))))

theorem runsTo_progA {K : ℕ} (hK : 16 ≤ K) {Pg : Program} {E G : List ℕ} {Tg : ℕ}
    (hg : RunsTo Pg (fun m => m = initMemAt K E) (fun m' => m' = initMemAt K G) Tg) :
    RunsTo (progA K Pg) (At K (fun _ => True) (E.length :: E))
      (At K (fun v => v 8 = K + ((E.length + 1) + (K + (G.length + 1))) ∧
        v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1) + K ∧ v 15 = G.length)
        ((E.length :: E) ++ (List.replicate K 0 ++ (G.length :: G))))
      (7 * E.length + 10 * Tg + 40) := by
  set A : List ℕ := E.length :: E with hA
  set Z : List ℕ := List.replicate K 0 with hZ
  have hAlen : A.length = E.length + 1 := by rw [hA]; simp
  have hZlen : Z.length = K := by rw [hZ]; simp
  have s1 : RunsTo (copyTo 9 K) (At K (fun _ => True) A) (At K (fun v => v 9 = E.length) A) 1 :=
    runsTo_copyFromList (i := 0) (by omega) (fun w _ => by simp [Mem.update, hA])
  have s2 : RunsTo (assign 10 1) (At K (fun v => v 9 = E.length) A)
      (At K (fun v => v 9 = E.length ∧ v 10 = 1) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s3 : RunsTo (addTo 9 9 10) (At K (fun v => v 9 = E.length ∧ v 10 = 1) A)
      (At K (fun v => v 9 = E.length + 1) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2])
  have s4 : RunsTo (assign 8 K) (At K (fun v => v 9 = E.length + 1) A)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K) A) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw])
  have s5 : RunsTo (addTo 8 8 9) (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K) A)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1)) A) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2])
  have s6 : RunsTo (copyTo 11 8)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1)) A)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) ∧
        v 11 = K + (E.length + 1)) A) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s7 : RunsTo (pushZeros K)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) ∧
        v 11 = K + (E.length + 1)) A)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1)) (A ++ Z)) 2 := by
    refine runsTo_pushZeros (L := A) hK (fun w hw => by rw [hw.2.1, hAlen])
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_⟩)
    · rw [hagree 9 (by omega) (by omega), hw.1]
    · rw [h8, hAlen]
    · rw [hagree 11 (by omega) (by omega), hw.2.2]
  have s8 : RunsTo (assign 0 K)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1)) (A ++ Z))
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1) ∧ v 0 = K) (A ++ Z)) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s9 : RunsTo (copyTo 2 9)
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1) ∧ v 0 = K) (A ++ Z))
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1) ∧ v 0 = K ∧ v 2 = E.length + 1) (A ++ Z)) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s10 : RunsTo pushBlock
      (At K (fun v => v 9 = E.length + 1 ∧ v 8 = K + (E.length + 1) + K ∧
        v 11 = K + (E.length + 1) ∧ v 0 = K ∧ v 2 = E.length + 1) (A ++ Z))
      (At K (fun v => v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1)) (A ++ (Z ++ A)))
      (7 * (E.length + 1) + 7) := by
    have hlist : A ++ (Z ++ A) = (A ++ Z) ++ ((A ++ Z).drop 0).take (E.length + 1) := by
      rw [← hAlen, seg_prefix, List.append_assoc]
    rw [hlist]
    refine runsTo_pushBlock (L := A ++ Z) hK (i := 0) (c := E.length + 1)
      (by rw [List.length_append, hAlen, hZlen]; omega) (fun w hw => ?_)
      (fun w w' hw hagree h8 => ⟨?_, ?_⟩)
    · refine ⟨?_, by simp [hw.2.2.2.1], hw.2.2.2.2⟩
      rw [List.length_append, hAlen, hZlen]
      have h := hw.2.1
      omega
    · rw [hagree 9 (by omega) (by omega) (by omega) (by omega), hw.1]
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
  have s11 : RunsTo (copyTo 0 11)
      (At K (fun v => v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1)) (A ++ (Z ++ A)))
      (At K (fun v => v 9 = E.length + 1 ∧ v 0 = K + (E.length + 1)) (A ++ (Z ++ A))) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s12 : RunsTo (callTopAt K Pg)
      (At K (fun v => v 9 = E.length + 1 ∧ v 0 = K + (E.length + 1)) (A ++ (Z ++ A)))
      (At K (fun v => v 9 = E.length + 1 ∧ v 0 = K + (E.length + 1) + K ∧
        v 8 = K + ((E.length + 1) + (K + (G.length + 1)))) (A ++ (Z ++ (G.length :: G))))
      (10 * Tg + 6) := by
    refine runsTo_callTopAt (L₀ := A) (l := E) (l' := G) hK hg
      (fun w hw => by rw [hw.2, hAlen]) (fun w w' hw hagree h0 h8 => ⟨?_, ?_, ?_⟩)
    · rw [hagree 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hw.1]
    · have h := h0; rw [hAlen] at h; omega
    · have h := h8; rw [hAlen] at h; omega
  have s13 : RunsTo (copyTo 11 0)
      (At K (fun v => v 9 = E.length + 1 ∧ v 0 = K + (E.length + 1) + K ∧
        v 8 = K + ((E.length + 1) + (K + (G.length + 1)))) (A ++ (Z ++ (G.length :: G))))
      (At K (fun v => v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1) + K ∧
        v 8 = K + ((E.length + 1) + (K + (G.length + 1)))) (A ++ (Z ++ (G.length :: G)))) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s14 : RunsTo (loadTo 15 11)
      (At K (fun v => v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1) + K ∧
        v 8 = K + ((E.length + 1) + (K + (G.length + 1)))) (A ++ (Z ++ (G.length :: G))))
      (At K (fun v => v 8 = K + ((E.length + 1) + (K + (G.length + 1))) ∧
        v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1) + K ∧ v 15 = G.length)
        (A ++ (Z ++ (G.length :: G)))) 1 := by
    have hget : (A ++ (Z ++ (G.length :: G))).getD ((E.length + 1) + K) 0 = G.length := by
      rw [List.getD_append_right A _ 0 _ (by omega), hAlen]
      have h1 : E.length + 1 + K - (E.length + 1) = Z.length := by rw [hZlen]; omega
      rw [h1, List.getD_append_right Z _ 0 _ (le_refl _)]
      simp
    refine runsTo_loadReg (i := (E.length + 1) + K) (by omega) (by omega)
      (fun w hw => by rw [hw.2.1]; omega) (fun w hw => ?_)
    rw [hget]
    exact ⟨by simp [Mem.update, hw.2.2], by simp [Mem.update, hw.1],
      by simp [Mem.update, hw.2.1], by simp [Mem.update]⟩
  exact (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq (s13.seq (s14)))))))))))))).mono (by omega)

/-! ## Stage B: the input above the first result, and the call to `f` -/

/-- Copy the input block above the result of the first call (again with `K` zeroed work
registers below it) and call the relocated routine for `f` on the copy. -/
def progB (K : ℕ) (Pf : Program) : Program :=
  seq (copyTo 12 8) (seq (pushZeros K) (seq (assign 0 K) (seq (copyTo 2 9)
    (seq pushBlock (seq (copyTo 0 12) (seq (callTopAt K Pf)
      (seq (copyTo 12 0) (loadTo 14 12))))))))

theorem runsTo_progB {K : ℕ} (hK : 16 ≤ K) {Pf : Program} {E F G : List ℕ} {Tf : ℕ}
    (hf : RunsTo Pf (fun m => m = initMemAt K E) (fun m' => m' = initMemAt K F) Tf) :
    RunsTo (progB K Pf)
      (At K (fun v => v 8 = K + ((E.length + 1) + (K + (G.length + 1))) ∧
        v 9 = E.length + 1 ∧ v 11 = K + (E.length + 1) + K ∧ v 15 = G.length)
        ((E.length :: E) ++ (List.replicate K 0 ++ (G.length :: G))))
      (At K (fun v => v 8 = K + (((E.length + 1) + (K + (G.length + 1))) + (K + (F.length + 1)))
        ∧ v 11 = K + (E.length + 1) + K ∧
        v 12 = K + ((E.length + 1) + (K + (G.length + 1))) + K ∧
        v 14 = F.length ∧ v 15 = G.length)
        (((E.length :: E) ++ (List.replicate K 0 ++ (G.length :: G))) ++
          (List.replicate K 0 ++ (F.length :: F))))
      (7 * E.length + 10 * Tf + 40) := by
  set A : List ℕ := E.length :: E with hA
  set Z : List ℕ := List.replicate K 0 with hZ
  have hAlen : A.length = E.length + 1 := by rw [hA]; simp
  have hZlen : Z.length = K := by rw [hZ]; simp
  set P : List ℕ := A ++ (Z ++ (G.length :: G)) with hP
  have hPlen : P.length = (E.length + 1) + (K + (G.length + 1)) := by
    rw [hP]; simp [hAlen, hZlen]
  have s1 : RunsTo (copyTo 12 8)
      (At K (fun v => v 8 = K + P.length ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length) P)
      (At K (fun v => v 8 = K + P.length ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length) P) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s2 : RunsTo (pushZeros K)
      (At K (fun v => v 8 = K + P.length ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length) P)
      (At K (fun v => v 8 = K + P.length + K ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length) (P ++ Z)) 2 := by
    refine runsTo_pushZeros (L := P) hK (fun w hw => hw.1)
      (fun w w' hw hagree h8 => ⟨h8, ?_, ?_, ?_, ?_⟩)
    · rw [hagree 9 (by omega) (by omega), hw.2.1]
    · rw [hagree 11 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 15 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.2.2]
  have s3 : RunsTo (assign 0 K)
      (At K (fun v => v 8 = K + P.length + K ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length) (P ++ Z))
      (At K (fun v => v 8 = K + P.length + K ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length ∧ v 0 = K)
        (P ++ Z)) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s4 : RunsTo (copyTo 2 9)
      (At K (fun v => v 8 = K + P.length + K ∧ v 9 = E.length + 1 ∧
        v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧ v 12 = K + P.length ∧ v 0 = K)
        (P ++ Z))
      (At K (fun v => v 8 = K + P.length + K ∧ v 11 = K + (E.length + 1) + K ∧
        v 15 = G.length ∧ v 12 = K + P.length ∧ v 0 = K ∧ v 2 = E.length + 1) (P ++ Z)) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s5 : RunsTo pushBlock
      (At K (fun v => v 8 = K + P.length + K ∧ v 11 = K + (E.length + 1) + K ∧
        v 15 = G.length ∧ v 12 = K + P.length ∧ v 0 = K ∧ v 2 = E.length + 1) (P ++ Z))
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 12 = K + P.length) (P ++ (Z ++ A))) (7 * (E.length + 1) + 7) := by
    have hlist : P ++ (Z ++ A) = (P ++ Z) ++ ((P ++ Z).drop 0).take (E.length + 1) := by
      have h1 : ((P ++ Z).drop 0).take (E.length + 1) = A := by
        rw [List.drop_zero, hP, List.append_assoc, List.append_assoc, ← hAlen, List.take_left]
      rw [h1]
      exact (List.append_assoc P Z A).symm
    rw [hlist]
    refine runsTo_pushBlock (L := P ++ Z) hK (i := 0) (c := E.length + 1)
      (by rw [List.length_append, hZlen, hPlen]; omega) (fun w hw => ?_)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_⟩)
    · refine ⟨?_, by simp [hw.2.2.2.2.1], hw.2.2.2.2.2⟩
      rw [List.length_append, hZlen]
      have h := hw.1
      omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 15 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
    · rw [hagree 12 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
  have s6 : RunsTo (copyTo 0 12)
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 12 = K + P.length) (P ++ (Z ++ A)))
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 0 = K + P.length) (P ++ (Z ++ A))) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s7 : RunsTo (callTopAt K Pf)
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 0 = K + P.length) (P ++ (Z ++ A)))
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 0 = K + P.length + K ∧ v 8 = K + (P.length + (K + (F.length + 1))))
        (P ++ (Z ++ (F.length :: F)))) (10 * Tf + 6) := by
    refine runsTo_callTopAt (L₀ := P) (l := E) (l' := F) hK hf
      (fun w hw => hw.2.2) (fun w w' hw hagree h0 h8 => ⟨?_, ?_, h0, by omega⟩)
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hw.1]
    · rw [hagree 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hw.2.1]
  have s8 : RunsTo (copyTo 12 0)
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 0 = K + P.length + K ∧ v 8 = K + (P.length + (K + (F.length + 1))))
        (P ++ (Z ++ (F.length :: F))))
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 12 = K + P.length + K ∧ v 8 = K + (P.length + (K + (F.length + 1))))
        (P ++ (Z ++ (F.length :: F)))) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2])
  have s9 : RunsTo (loadTo 14 12)
      (At K (fun v => v 11 = K + (E.length + 1) + K ∧ v 15 = G.length ∧
        v 12 = K + P.length + K ∧ v 8 = K + (P.length + (K + (F.length + 1))))
        (P ++ (Z ++ (F.length :: F))))
      (At K (fun v => v 8 = K + (P.length + (K + (F.length + 1))) ∧
        v 11 = K + (E.length + 1) + K ∧ v 12 = K + P.length + K ∧
        v 14 = F.length ∧ v 15 = G.length) (P ++ (Z ++ (F.length :: F)))) 1 := by
    have hget : (P ++ (Z ++ (F.length :: F))).getD (P.length + K) 0 = F.length := by
      rw [List.getD_append_right P _ 0 _ (by omega)]
      have h1 : P.length + K - P.length = Z.length := by rw [hZlen]; omega
      rw [h1, List.getD_append_right Z _ 0 _ (le_refl _)]
      simp
    refine runsTo_loadReg (i := P.length + K) (by omega) (by omega)
      (fun w hw => by rw [hw.2.2.1]; omega) (fun w hw => ?_)
    rw [hget]
    exact ⟨by simp [Mem.update, hw.2.2.2], by simp [Mem.update, hw.1],
      by simp [Mem.update, hw.2.2.1], by simp [Mem.update], by simp [Mem.update, hw.2.1]⟩
  have hmain := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9))))))))
  refine (hmain.mono (by omega)).conseq (fun m hm => ?_) (fun m hm => ?_) (le_refl _)
  · obtain ⟨w, hw, hmw⟩ := hm
    exact ⟨w, ⟨by rw [hw.1, hPlen], hw.2.1, hw.2.2.1, hw.2.2.2⟩, hmw⟩
  · obtain ⟨w, hw, hmw⟩ := hm
    exact ⟨w, ⟨by rw [hw.1, hPlen], hw.2.1, by rw [hw.2.2.1, hPlen], hw.2.2.2.1,
      hw.2.2.2.2⟩, hmw⟩

/-! ## Stage C: assembling the pair and moving it down to the base

This stage is stated for an arbitrary workspace list `D` holding the two results: register `11`
points at the length field of the second component, register `12` at that of the first, and
registers `14`, `15` hold the two lengths.  Nothing else of the layout matters. -/

/-- Write the encoding of the pair above the workspace and move it down to the base. -/
def progC1 : Program :=
  seq (copyTo 13 8) (seq (addTo 2 14 15) (seq (assign 10 2) (seq (addTo 2 2 10)
    (seq (pushVal 2) (seq (pushVal 14) (seq (assign 10 1) (seq (addTo 0 12 10)
      (seq (copyTo 2 14) (seq pushBlock (seq (pushVal 15) (seq (assign 10 1)
        (seq (addTo 0 11 10) (seq (copyTo 2 15) pushBlock)))))))))))))

/-- The last four pointer settings and the final move. -/
def progC2 (K : ℕ) : Program :=
  seq (copyTo 11 13) (seq (addTo 12 14 15) (seq (assign 10 3)
    (seq (addTo 12 12 10) (finish K))))

/-- Write the encoding of the pair above the workspace and move it down to the base. -/
def progC (K : ℕ) : Program := seq progC1 (progC2 K)

set_option maxHeartbeats 1000000 in
theorem runsTo_progC {K : ℕ} (hK : 16 ≤ K) {F G D : List ℕ} {i j : ℕ}
    (hiG : i + 1 + G.length ≤ D.length) (hjF : j + 1 + F.length ≤ D.length)
    (hG : ((D.drop (i + 1)).take G.length) = G)
    (hF : ((D.drop (j + 1)).take F.length) = F) :
    RunsTo (progC K)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length) D)
      (fun m' => m' = memAt K (fun _ => 0)
        ((F.length + G.length + 2) :: ((F.length :: F) ++ (G.length :: G))))
      (14 * F.length + 14 * G.length + 5 * D.length + K + 80) := by
  obtain ⟨N, hN⟩ : ∃ N, N = F.length + G.length + 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = N :: ((F.length :: F) ++ (G.length :: G)) := ⟨_, rfl⟩
  have hBlen : B.length = F.length + G.length + 3 := by rw [hB]; simp; omega
  rw [show ((F.length + G.length + 2) :: ((F.length :: F) ++ (G.length :: G))) = B by
    rw [hB, hN]]
  have s1 : RunsTo (copyTo 13 8)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length) D)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length) D) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s2 : RunsTo (addTo 2 14 15)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length) D)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧
        v 2 = F.length + G.length) D) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s3 : RunsTo (assign 10 2)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧
        v 2 = F.length + G.length) D)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧
        v 2 = F.length + G.length ∧ v 10 = 2) D) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
        hw.2.2.2.2.2.2])
  have s4 : RunsTo (addTo 2 2 10)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧
        v 2 = F.length + G.length ∧ v 10 = 2) D)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = N) D) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
        hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2, hN])
  have s5 : RunsTo (pushVal 2)
      (At K (fun v => v 8 = K + D.length ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = N) D)
      (At K (fun v => v 8 = K + D.length + 1 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length) (D ++ [N])) 3 := by
    refine runsTo_pushVal (L := D) (v := N) hK (by omega) (by omega)
      (fun w hw => ⟨hw.1, hw.2.2.2.2.2.2⟩) (fun w w' hw hagree h8 h10 => ⟨h8, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 15 (by omega) (by omega), hw.2.2.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.2.2.1]
  have s6 : RunsTo (pushVal 14)
      (At K (fun v => v 8 = K + D.length + 1 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length) (D ++ [N]))
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((D ++ [N]) ++ [F.length])) 3 := by
    refine runsTo_pushVal (L := D ++ [N]) (v := F.length) hK (by omega) (by omega)
      (fun w hw => ⟨?_, hw.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)
    · simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil] at h8 ⊢
      omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 12 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 15 (by omega) (by omega), hw.2.2.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.2.2]
  have s7 : RunsTo (assign 10 1)
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((D ++ [N]) ++ [F.length]))
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 10 = 1)
        ((D ++ [N]) ++ [F.length])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s8 : RunsTo (addTo 0 12 10)
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 12 = K + j ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 10 = 1)
        ((D ++ [N]) ++ [F.length]))
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 0 = K + (j + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((D ++ [N]) ++ [F.length])) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], by simp [Mem.update, hw.2.1], ?_,
        by simp [Mem.update, hw.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.1],
        by simp [Mem.update, hw.2.2.2.2.2.1]⟩
      simp only [Mem.update_self, hw.2.2.1, hw.2.2.2.2.2.2]
      omega)
  have s9 : RunsTo (copyTo 2 14)
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 0 = K + (j + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((D ++ [N]) ++ [F.length]))
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 0 = K + (j + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = F.length)
        ((D ++ [N]) ++ [F.length])) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2])
  have s10 : RunsTo pushBlock
      (At K (fun v => v 8 = K + D.length + 2 ∧ v 11 = K + i ∧ v 0 = K + (j + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = F.length)
        ((D ++ [N]) ++ [F.length]))
      (At K (fun v => v 8 = K + D.length + 2 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        (((D ++ [N]) ++ [F.length]) ++ F)) (7 * F.length + 7) := by
    have hseg : ((((D ++ [N]) ++ [F.length]).drop (j + 1)).take F.length) = F := by
      rw [seg_append (D ++ [N]) [F.length] (j + 1) F.length (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        seg_append D [N] (j + 1) F.length (by omega), hF]
    have hlist : ((D ++ [N]) ++ [F.length]) ++
        ((((D ++ [N]) ++ [F.length]).drop (j + 1)).take F.length)
        = ((D ++ [N]) ++ [F.length]) ++ F := by rw [hseg]
    refine RunsTo.weaken ?_ (fun m hm => by rw [← hlist]; exact hm)
    refine runsTo_pushBlock (L := (D ++ [N]) ++ [F.length]) hK (i := j + 1) (c := F.length)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (fun w hw => ?_)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · refine ⟨?_, hw.2.2.1, hw.2.2.2.2.2.2⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil] at h8 ⊢
      omega
    · rw [hagree 11 (by omega) (by omega) (by omega) (by omega), hw.2.1]
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 15 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.1]
    · rw [hagree 13 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.2.1]
  have s11 : RunsTo (pushVal 15)
      (At K (fun v => v 8 = K + D.length + 2 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        (((D ++ [N]) ++ [F.length]) ++ F))
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length])) 3 := by
    refine runsTo_pushVal (L := ((D ++ [N]) ++ [F.length]) ++ F) (v := G.length) hK
      (by omega) (by omega) (fun w hw => ⟨?_, hw.2.2.2.1⟩)
      (fun w w' hw hagree h8 h10 => ⟨?_, ?_, ?_, ?_, ?_⟩)
    · simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil] at h8 ⊢
      omega
    · rw [hagree 11 (by omega) (by omega), hw.2.1]
    · rw [hagree 14 (by omega) (by omega), hw.2.2.1]
    · rw [hagree 15 (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 13 (by omega) (by omega), hw.2.2.2.2]
  have s12 : RunsTo (assign 10 1)
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]))
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 10 = 1)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length])) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s13 : RunsTo (addTo 0 11 10)
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 11 = K + i ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 10 = 1)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]))
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 0 = K + (i + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length])) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      refine ⟨by simp [Mem.update, hw.1], ?_, by simp [Mem.update, hw.2.2.1],
        by simp [Mem.update, hw.2.2.2.1], by simp [Mem.update, hw.2.2.2.2.1]⟩
      simp only [Mem.update_self, hw.2.1, hw.2.2.2.2.2]
      omega)
  have s14 : RunsTo (copyTo 2 15)
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 0 = K + (i + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]))
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 0 = K + (i + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = G.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length])) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2])
  have s15 : RunsTo pushBlock
      (At K (fun v => v 8 = K + D.length + 3 + F.length ∧ v 0 = K + (i + 1) ∧
        v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length ∧ v 2 = G.length)
        ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]))
      (At K (fun v => v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G)) (7 * G.length + 7) := by
    have hseg : (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]).drop (i + 1)).take G.length
        = G := by
      rw [seg_append (((D ++ [N]) ++ [F.length]) ++ F) [G.length] (i + 1) G.length
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        seg_append ((D ++ [N]) ++ [F.length]) F (i + 1) G.length (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        seg_append (D ++ [N]) [F.length] (i + 1) G.length (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        seg_append D [N] (i + 1) G.length (by omega), hG]
    have hlist : ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]).drop (i + 1)).take G.length
        = ((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G := by rw [hseg]
    refine RunsTo.weaken ?_ (fun m hm => by rw [← hlist]; exact hm)
    refine runsTo_pushBlock (L := (((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) hK
      (i := i + 1) (c := G.length) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (fun w hw => ?_)
      (fun w w' hw hagree h8 => ⟨?_, ?_, ?_⟩)
    · refine ⟨?_, hw.2.1, hw.2.2.2.2.2⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      have h1 := hw.1
      omega
    · rw [hagree 14 (by omega) (by omega) (by omega) (by omega), hw.2.2.1]
    · rw [hagree 15 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.1]
    · rw [hagree 13 (by omega) (by omega) (by omega) (by omega), hw.2.2.2.2.1]
  have s16 : RunsTo (copyTo 11 13)
      (At K (fun v => v 14 = F.length ∧ v 15 = G.length ∧ v 13 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G))
      (At K (fun v => v 14 = F.length ∧ v 15 = G.length ∧ v 11 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G)) 1 :=
    runsTo_copyReg (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s17 : RunsTo (addTo 12 14 15)
      (At K (fun v => v 14 = F.length ∧ v 15 = G.length ∧ v 11 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G))
      (At K (fun v => v 12 = F.length + G.length ∧ v 11 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G)) 1 :=
    runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s18 : RunsTo (assign 10 3)
      (At K (fun v => v 12 = F.length + G.length ∧ v 11 = K + D.length)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G))
      (At K (fun v => v 12 = F.length + G.length ∧ v 11 = K + D.length ∧ v 10 = 3)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G)) 1 :=
    runsTo_assignReg (by omega) (fun w hw => by simp [Mem.update, hw.1, hw.2])
  have s19 : RunsTo (addTo 12 12 10)
      (At K (fun v => v 12 = F.length + G.length ∧ v 11 = K + D.length ∧ v 10 = 3)
        (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G))
      (At K (fun v => v 11 = K + D.length ∧ v 12 = F.length + G.length + 3)
        (D ++ B)) 1 := by
    have hlist : (((((D ++ [N]) ++ [F.length]) ++ F) ++ [G.length]) ++ G) = D ++ B := by
      rw [hB]; simp [List.append_assoc]
    rw [hlist]
    exact runsTo_addReg (by omega) (by omega) (by omega) (fun w hw => by
      simp [Mem.update, hw.1, hw.2.1, hw.2.2])
  have s20 : RunsTo (finish K)
      (At K (fun v => v 11 = K + D.length ∧ v 12 = F.length + G.length + 3) (D ++ B))
      (fun m' => m' = memAt K (fun _ => 0) B)
      (7 * (F.length + G.length + 3) + 5 * D.length + K + 17) := by
    refine (runsTo_finish (L₀ := D) (B := B) hK (fun w hw => ⟨hw.1, by rw [hw.2, hBlen]⟩)).mono ?_
    rw [hBlen]
  have hc1 := s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq (s11.seq (s12.seq (s13.seq (s14.seq (s15))))))))))))))
  have hc2 := s16.seq (s17.seq (s18.seq (s19.seq (s20))))
  exact (hc1.seq hc2).mono (by omega)

/-! ## The pairing routine -/

/-- The pairing routine at the workspace convention: `a ↦ (f a, g a)`. -/
def pairProg (K : ℕ) (Pf Pg : Program) : Program :=
  seq (progA K Pg) (seq (progB K Pf) (progC K))

set_option maxHeartbeats 1000000 in
theorem runsTo_pairProg {K : ℕ} (hK : 16 ≤ K) {Pf Pg : Program} {E F G : List ℕ} {Tf Tg : ℕ}
    (hf : RunsTo Pf (fun m => m = initMemAt K E) (fun m' => m' = initMemAt K F) Tf)
    (hg : RunsTo Pg (fun m => m = initMemAt K E) (fun m' => m' = initMemAt K G) Tg) :
    RunsTo (pairProg K Pf Pg) (fun m => m = initMemAt K E)
      (fun m' => m' = initMemAt K ((F.length :: F) ++ (G.length :: G)))
      (19 * E.length + 19 * F.length + 19 * G.length + 10 * Tf + 10 * Tg + 11 * K + 200) := by
  set A : List ℕ := E.length :: E with hA
  set Z : List ℕ := List.replicate K 0 with hZ
  have hAlen : A.length = E.length + 1 := by rw [hA]; simp
  have hZlen : Z.length = K := by rw [hZ]; simp
  set D : List ℕ := (A ++ (Z ++ (G.length :: G))) ++ (Z ++ (F.length :: F)) with hD
  have hDlen : D.length = (E.length + 1) + (K + (G.length + 1)) + (K + (F.length + 1)) := by
    rw [hD]; simp [hAlen, hZlen]; omega
  have hsegG : ((D.drop ((E.length + 1) + K + 1)).take G.length) = G := by
    have hsplit : D = (A ++ (Z ++ [G.length])) ++ (G ++ (Z ++ (F.length :: F))) := by
      rw [hD]; simp [List.append_assoc]
    have hlen : (A ++ (Z ++ [G.length])).length = (E.length + 1) + K + 1 := by
      simp [hAlen, hZlen]; omega
    rw [hsplit, ← hlen, seg_middle]
  have hsegF : ((D.drop ((E.length + 1) + (K + (G.length + 1)) + K + 1)).take F.length) = F := by
    have hsplit : D = ((A ++ (Z ++ (G.length :: G))) ++ (Z ++ [F.length])) ++ (F ++ []) := by
      rw [hD]; simp [List.append_assoc]
    have hlen : ((A ++ (Z ++ (G.length :: G))) ++ (Z ++ [F.length])).length
        = (E.length + 1) + (K + (G.length + 1)) + K + 1 := by
      simp [hAlen, hZlen]; omega
    rw [hsplit, ← hlen, seg_middle]
  have hC := runsTo_progC (K := K) (F := F) (G := G) (D := D)
    (i := (E.length + 1) + K) (j := (E.length + 1) + (K + (G.length + 1)) + K) hK
    (by rw [hDlen]; omega) (by rw [hDlen]; omega) hsegG hsegF
  have hB := runsTo_progB (K := K) (E := E) (F := F) (G := G) hK hf
  have hA' := runsTo_progA (K := K) (E := E) (G := G) hK hg
  have hstep : RunsTo (pairProg K Pf Pg) (At K (fun _ => True) A)
      (fun m' => m' = memAt K (fun _ => 0)
        ((F.length + G.length + 2) :: ((F.length :: F) ++ (G.length :: G))))
      ((7 * E.length + 10 * Tg + 40) + ((7 * E.length + 10 * Tf + 40) +
        (14 * F.length + 14 * G.length + 5 * D.length + K + 80))) := by
    refine hA'.seq (hB.seq (hC.strengthen (fun m hm => ?_)))
    obtain ⟨w, hw, hmw⟩ := hm
    refine ⟨w, ⟨?_, ?_, ?_, hw.2.2.2.1, hw.2.2.2.2⟩, hmw⟩
    · rw [hDlen]; have h := hw.1; omega
    · rw [hw.2.1]; omega
    · rw [hw.2.2.1]; omega
  have hlen : ((F.length :: F) ++ (G.length :: G)).length = F.length + G.length + 2 := by
    simp; omega
  refine (hstep.conseq (fun m hm => ?_) (fun m hm => ?_) ?_)
  · exact ⟨fun _ => 0, trivial, by rw [hm, hA, initMemAt_eq_memAt]⟩
  · rw [hm, initMemAt_eq_memAt, hlen]
  · rw [hDlen]; omega

/-! ## The clean classes -/

variable {α β γ : Type*}

/-- **Pairing.**  If `f` and `g` are computed by clean routines of the workspace convention, so
is `a ↦ (f a, g a)`.  The cost is the two calls, plus a linear amount of copying — linear in the
input and in the two results, whose sizes are not bounded by the running time (see
`Workspace/Machine/DESIGN.md`), which is why the bound is stated in terms of them. -/
theorem cleanComputeAt_pair [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K) {Pf Pg : Program}
    {f : α → β} {g : α → γ} {Tf Tg Sf Sg : ℕ → ℕ}
    (hf : CleanComputeAt K Pf f Tf) (hg : CleanComputeAt K Pg g Tg)
    (hSf : ∀ a, Enc.size (f a) ≤ Sf (Enc.size a))
    (hSg : ∀ a, Enc.size (g a) ≤ Sg (Enc.size a)) :
    CleanComputeAt K (pairProg K Pf Pg) (fun a => (f a, g a))
      (fun n => 19 * n + 19 * Sf n + 19 * Sg n + 10 * Tf n + 10 * Tg n + 11 * K + 200) := by
  intro a
  have hpair : Enc.encode (f a, g a)
      = ((Enc.encode (f a)).length :: Enc.encode (f a)) ++
        ((Enc.encode (g a)).length :: Enc.encode (g a)) := rfl
  have h := runsTo_pairProg (K := K) (E := Enc.encode a) (F := Enc.encode (f a))
    (G := Enc.encode (g a)) hK (hf a) (hg a)
  rw [← hpair] at h
  refine h.mono ?_
  have hE : (Enc.encode a).length ≤ Enc.size a := le_of_lt (length_lt_listSize _)
  have hF : (Enc.encode (f a)).length ≤ Sf (Enc.size a) :=
    le_trans (le_of_lt (length_lt_listSize _)) (hSf a)
  have hG : (Enc.encode (g a)).length ≤ Sg (Enc.size a) :=
    le_trans (le_of_lt (length_lt_listSize _)) (hSg a)
  dsimp only
  omega

end Pairing

set_option maxRecDepth 10000 in
/-- **Pairing in polynomial time** at the workspace convention. -/
theorem polyTimeCleanAt_pair {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K)
    {f : α → β} {g : α → γ} {Sf Sg : ℕ → ℕ} (hf : PolyTimeCleanAt K f)
    (hg : PolyTimeCleanAt K g) (hSfb : PolyBound Sf) (hSgb : PolyBound Sg)
    (hSf : ∀ a, Enc.size (f a) ≤ Sf (Enc.size a))
    (hSg : ∀ a, Enc.size (g a) ≤ Sg (Enc.size a)) :
    PolyTimeCleanAt K (fun a => (f a, g a)) := by
  obtain ⟨Pf, Tf, hTf, hPf⟩ := hf
  obtain ⟨Pg, Tg, hTg, hPg⟩ := hg
  refine ⟨Pairing.pairProg K Pf Pg, _, ?_, Pairing.cleanComputeAt_pair hK hPf hPg hSf hSg⟩
  exact ((((((polyBound_const 19).mul polyBound_id).add ((polyBound_const 19).mul hSfb)).add
    ((polyBound_const 19).mul hSgb)).add ((polyBound_const 10).mul hTf)).add
    ((polyBound_const 10).mul hTg)).add (polyBound_const (11 * K + 200))

set_option maxRecDepth 10000 in
/-- **Pairing in quasipolynomial time** at the workspace convention. -/
theorem quasiPolyTimeCleanAt_pair {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {K : ℕ} (hK : 16 ≤ K)
    {f : α → β} {g : α → γ} {Sf Sg : ℕ → ℕ} (hf : QuasiPolyTimeCleanAt K f)
    (hg : QuasiPolyTimeCleanAt K g) (hSfb : PolyBound Sf) (hSgb : PolyBound Sg)
    (hSf : ∀ a, Enc.size (f a) ≤ Sf (Enc.size a))
    (hSg : ∀ a, Enc.size (g a) ≤ Sg (Enc.size a)) :
    QuasiPolyTimeCleanAt K (fun a => (f a, g a)) := by
  obtain ⟨Pf, Tf, hTf, hPf⟩ := hf
  obtain ⟨Pg, Tg, hTg, hPg⟩ := hg
  refine ⟨Pairing.pairProg K Pf Pg, _, ?_, Pairing.cleanComputeAt_pair hK hPf hPg hSf hSg⟩
  exact ((((((polyBound_const 19).mul polyBound_id).quasiPoly.add
    ((polyBound_const 19).mul hSfb).quasiPoly).add
    ((polyBound_const 19).mul hSgb).quasiPoly).add
    ((polyBound_const 10).quasiPoly.mul hTf)).add
    ((polyBound_const 10).quasiPoly.mul hTg)).add (polyBound_const (11 * K + 200)).quasiPoly

end RAM
