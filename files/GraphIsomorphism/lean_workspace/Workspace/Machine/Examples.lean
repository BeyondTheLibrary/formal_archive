import Workspace.Machine.Arrays
import Workspace.Machine.Recursion
import Workspace.Machine.Closure
import Workspace.Machine.Reloc

/-!
# Sanity checks for the machine

Three small programs, written directly in the instruction set of `RAM.lean`, with their
outputs and their exact step counts checked by kernel reduction.  They are here to make sure
the semantics is the intended one: the definitions of this directory are executable, and these
`example`s are proved by `rfl` or `decide`, not by hand.

Input and output follow the convention of `Encoding.lean`: register `0` holds the length and
registers `1, 2, ...` the entries.  Scratch registers are taken at addresses `100` and above,
above the input region, and the copy buffer of `revProg` at `200` and above.
-/

set_option maxRecDepth 100000

namespace RAM
namespace Examples

/-! ## Adding two numbers -/

/-- Input `[x, y]`, output `[x + y]`. -/
def addProg : Program := [Instr.add 1 1 2, Instr.const 0 1]

example : (run addProg (Config.init [3, 4]) 2).mem 0 = 1 := by rfl
example : (run addProg (Config.init [3, 4]) 2).mem 1 = 7 := by rfl
example : Halted addProg (run addProg (Config.init [3, 4]) 2) := by decide
example : ¬ Halted addProg (run addProg (Config.init [3, 4]) 1) := by decide

/-! ## Summing an array -/

/-- Input `[a₁, ..., aₙ]`, output `[a₁ + ... + aₙ]`.  Registers: `100` the running sum, `101`
the pointer into the input, `102` the counter, `103` a scratch cell, `104` the constant `1`. -/
def sumProg : Program :=
  [Instr.const 100 0, Instr.const 101 1, Instr.copy 102 0, Instr.const 104 1,
   Instr.jz 102 10, Instr.load 103 101, Instr.add 100 100 103, Instr.add 101 101 104,
   Instr.sub 102 102 104, Instr.jump 4, Instr.copy 1 100, Instr.const 0 1]

/-- Three entries: `6 * 3 + 7 = 25` steps. -/
example : Halted sumProg (run sumProg (Config.init [3, 4, 5]) 25) := by decide
example : ¬ Halted sumProg (run sumProg (Config.init [3, 4, 5]) 24) := by decide
example : (run sumProg (Config.init [3, 4, 5]) 25).mem 0 = 1 := by rfl
example : (run sumProg (Config.init [3, 4, 5]) 25).mem 1 = 12 := by rfl

/-! ## Reversing an array -/

/-- Input `[a₁, ..., aₙ]`, output `[aₙ, ..., a₁]`.  The array is copied to the buffer at
`200 ...` and then written back in reverse order. -/
def revProg : Program :=
  [Instr.const 100 1, Instr.copy 101 0, Instr.const 102 1, Instr.const 103 200,
   Instr.jz 101 11, Instr.load 104 100, Instr.store 103 104, Instr.add 100 100 102,
   Instr.add 103 103 102, Instr.sub 101 101 102, Instr.jump 4,
   Instr.copy 101 0, Instr.const 100 1, Instr.sub 103 103 102,
   Instr.jz 101 21, Instr.load 104 103, Instr.store 100 104, Instr.add 100 100 102,
   Instr.sub 103 103 102, Instr.sub 101 101 102, Instr.jump 14]

/-- Three entries: `14 * 3 + 9 = 51` steps. -/
example : Halted revProg (run revProg (Config.init [7, 8, 9]) 51) := by decide
example : ¬ Halted revProg (run revProg (Config.init [7, 8, 9]) 50) := by decide
example : (run revProg (Config.init [7, 8, 9]) 51).mem 0 = 3 := by rfl
example : (run revProg (Config.init [7, 8, 9]) 51).mem 1 = 9 := by rfl
example : (run revProg (Config.init [7, 8, 9]) 51).mem 2 = 8 := by rfl
example : (run revProg (Config.init [7, 8, 9]) 51).mem 3 = 7 := by rfl

/-- Five entries: `14 * 5 + 9 = 79` steps. -/
example : Halted revProg (run revProg (Config.init [1, 2, 3, 4, 5]) 79) := by decide
example : ¬ Halted revProg (run revProg (Config.init [1, 2, 3, 4, 5]) 78) := by decide

/-! ## A program assembled from the combinators

`R 5 ← 3; R 1 ← R 5 + R 5` runs in two steps and leaves `6` in register `1`, whatever the
memory it is started in. -/

example : Runs (seq (assign 5 3) (addTo 1 5 5)) (fun _ => True) 2
    (fun m => (m.update 5 3).update 1 ((m.update 5 3) 5 + (m.update 5 3) 5)) :=
  (runs_assign 5 3).seq (runs_addTo 1 5 5) (fun _ _ => trivial)

example (m : Mem) :
    ((m.update 5 3).update 1 ((m.update 5 3) 5 + (m.update 5 3) 5)) 1 = 6 := by
  simp [Mem.update]

/-! ## The routines of `Arith.lean`

Executable checks, by kernel reduction, of the routines built with the Hoare rules: the value
computed and the exact number of steps.  Arguments sit in the input registers `1, 2`, the result
is written to register `0`, and the scratch block starts at `100`. -/

open Arith

example : (run (leTo 0 1 2 100) (Config.init [3, 7]) 5).mem 0 = 1 := by rfl
example : (run (leTo 0 1 2 100) (Config.init [7, 3]) 5).mem 0 = 0 := by rfl
/-- The `≤` branch of the conditional is the shorter one: three steps, against the bound `5`. -/
example : Halted (leTo 0 1 2 100) (run (leTo 0 1 2 100) (Config.init [3, 7]) 3) := by decide
example : ¬ Halted (leTo 0 1 2 100) (run (leTo 0 1 2 100) (Config.init [3, 7]) 2) := by decide
example : Halted (leTo 0 1 2 100) (run (leTo 0 1 2 100) (Config.init [7, 3]) 4) := by decide
example : ¬ Halted (leTo 0 1 2 100) (run (leTo 0 1 2 100) (Config.init [7, 3]) 3) := by decide

example : (run (ltTo 0 1 2 100) (Config.init [3, 3]) 5).mem 0 = 0 := by rfl
example : (run (ltTo 0 1 2 100) (Config.init [3, 4]) 5).mem 0 = 1 := by rfl

example : (run (eqTo 0 1 2 100) (Config.init [7, 7]) 7).mem 0 = 1 := by rfl
example : (run (eqTo 0 1 2 100) (Config.init [7, 3]) 7).mem 0 = 0 := by rfl
example : Halted (eqTo 0 1 2 100) (run (eqTo 0 1 2 100) (Config.init [7, 3]) 6) := by decide
example : ¬ Halted (eqTo 0 1 2 100) (run (eqTo 0 1 2 100) (Config.init [7, 3]) 5) := by decide

example : (run (minTo 0 1 2 100) (Config.init [7, 3]) 5).mem 0 = 3 := by rfl
example : (run (maxTo 0 1 2 100) (Config.init [7, 3]) 5).mem 0 = 7 := by rfl

/-- `Nat.size 5 = 3`; the loop runs three times, so the run takes `5 + 3 * 6 + 1 = 24` steps,
which is exactly the bound `6 * Nat.size 5 + 6` proved in `runsTo_sizeTo`. -/
example : (run (sizeTo 0 1 100) (Config.init [5]) 24).mem 0 = 3 := by rfl
example : Halted (sizeTo 0 1 100) (run (sizeTo 0 1 100) (Config.init [5]) 24) := by decide
example : ¬ Halted (sizeTo 0 1 100) (run (sizeTo 0 1 100) (Config.init [5]) 23) := by decide

/-- `Nat.size 0 = 0`: the loop is not entered, `5 + 1 = 6` steps. -/
example : (run (sizeTo 0 1 100) (Config.init [0]) 6).mem 0 = 0 := by rfl
example : Halted (sizeTo 0 1 100) (run (sizeTo 0 1 100) (Config.init [0]) 6) := by decide
example : ¬ Halted (sizeTo 0 1 100) (run (sizeTo 0 1 100) (Config.init [0]) 5) := by decide

/-! ## Array routines

A memory with a source block of two entries at address `200` and a destination block at `300`;
register `1` holds the source base, register `2` the destination base, register `3` the length.
The scratch block starts at `100`, below both blocks, as the routines require. -/

/-- A test memory: `R 1 = 200`, `R 2 = 300`, `R 3 = 2`, and the source block `R 200 = 7`,
`R 201 = 9`. -/
def testMem : Mem := fun a =>
  if a = 1 then 200 else if a = 2 then 300 else if a = 3 then 2 else
  if a = 200 then 7 else if a = 201 then 9 else 0

open Arrays

/-- Copying two entries takes `7 * 2 + 5 = 19` steps. -/
example : (run (copyBlock 1 2 3 100) ⟨0, testMem⟩ 19).mem 300 = 7 := by rfl
example : (run (copyBlock 1 2 3 100) ⟨0, testMem⟩ 19).mem 301 = 9 := by rfl
example : (run (copyBlock 1 2 3 100) ⟨0, testMem⟩ 19).mem 200 = 7 := by rfl
example : Halted (copyBlock 1 2 3 100) (run (copyBlock 1 2 3 100) ⟨0, testMem⟩ 19) := by decide
example : ¬ Halted (copyBlock 1 2 3 100) (run (copyBlock 1 2 3 100) ⟨0, testMem⟩ 18) := by
  decide

/-- Zeroing two entries takes `5 * 2 + 5 = 15` steps. -/
example : (run (fillZero 1 3 100) ⟨0, testMem⟩ 15).mem 200 = 0 := by rfl
example : (run (fillZero 1 3 100) ⟨0, testMem⟩ 15).mem 201 = 0 := by rfl
example : Halted (fillZero 1 3 100) (run (fillZero 1 3 100) ⟨0, testMem⟩ 15) := by decide
example : ¬ Halted (fillZero 1 3 100) (run (fillZero 1 3 100) ⟨0, testMem⟩ 14) := by decide

/-! ## Clean composition

The empty program is clean, and clean programs compose; the composite of the identity with
itself is the identity, in zero steps. -/

example : CleanCompute (seq [] []) (fun a : ℕ => id (id a)) (fun n => 0 + 0) :=
  cleanCompute_id.comp (S := fun n => n) cleanCompute_id (fun _ _ _ => le_refl _)
    (fun a => le_refl (Enc.size a))

/-! ## Erasing the input and the constant functions (`Const.lean`)

`eraseProg` wipes the whole memory of the input convention; `constProg l` wipes it and writes
`l`.  The step counts below are the ones the proofs give. -/

/-- Three entries: the set-up costs `4` steps, the loop is not entered (`R4 = 3 - 3 = 0`, one
test), the five clearing assignments cost `5`: ten steps in all. -/
example : Halted eraseProg (run eraseProg (Config.init [7, 8, 9]) 10) := by decide
example : ¬ Halted eraseProg (run eraseProg (Config.init [7, 8, 9]) 9) := by decide
example : (run eraseProg (Config.init [7, 8, 9]) 10).mem 0 = 0 := by rfl
example : (run eraseProg (Config.init [7, 8, 9]) 10).mem 1 = 0 := by rfl
example : (run eraseProg (Config.init [7, 8, 9]) 10).mem 3 = 0 := by rfl

/-- Six entries: the loop runs three times (the pointer walks `6, 5, 4`), at `5` steps each,
so `4 + (3 * 5 + 1) + 5 = 25` steps, within the bound `5 * 6 + 10`. -/
example : Halted eraseProg (run eraseProg (Config.init [1, 2, 3, 4, 5, 6]) 25) := by decide
example : ¬ Halted eraseProg (run eraseProg (Config.init [1, 2, 3, 4, 5, 6]) 24) := by decide
example : (run eraseProg (Config.init [1, 2, 3, 4, 5, 6]) 25).mem 5 = 0 := by rfl
example : (run eraseProg (Config.init [1, 2, 3, 4, 5, 6]) 25).mem 6 = 0 := by rfl

/-- `constProg [5, 6]`: ten steps of erasing, two entries written, one length: `13`. -/
example : Halted (constProg [5, 6]) (run (constProg [5, 6]) (Config.init [7, 8, 9]) 13) := by
  decide
example : (run (constProg [5, 6]) (Config.init [7, 8, 9]) 13).mem 0 = 2 := by rfl
example : (run (constProg [5, 6]) (Config.init [7, 8, 9]) 13).mem 1 = 5 := by rfl
example : (run (constProg [5, 6]) (Config.init [7, 8, 9]) 13).mem 2 = 6 := by rfl
example : (run (constProg [5, 6]) (Config.init [7, 8, 9]) 13).mem 3 = 0 := by rfl

/-- A function of one bit: `true ↦ [7]`, `false ↦ [9]`.  On input `true` the test falls through
to the first branch (`1 + 12 + 1 = 14` steps), on input `false` it jumps to the second
(`1 + 12 = 13` steps). -/
example : (run (boolProg [7] [9]) (Config.init [1]) 14).mem 1 = 7 := by rfl
example : Halted (boolProg [7] [9]) (run (boolProg [7] [9]) (Config.init [1]) 14) := by decide
example : (run (boolProg [7] [9]) (Config.init [0]) 13).mem 1 = 9 := by rfl
example : Halted (boolProg [7] [9]) (run (boolProg [7] [9]) (Config.init [0]) 13) := by decide

/-! ## Locality (`Locality.lean`)

The summing program above, run in a memory that carries a caller's datum at address `1000`:
the answer is the same, and the datum is untouched.  This is the executable form of
`RAM.run_agree`. -/

/-- The input `[3, 4, 5]` with the value `999` parked at address `1000`. -/
def junkMem : Mem := fun a => if a = 1000 then 999 else initMem [3, 4, 5] a

example : (run sumProg ⟨0, junkMem⟩ 25).mem 1 = 12 := by rfl
example : (run sumProg ⟨0, junkMem⟩ 25).mem 1000 = 999 := by rfl
example : Halted sumProg (run sumProg ⟨0, junkMem⟩ 25) := by decide

/-! ## Routines on inputs of fixed shape (`Small.lean`)

`sizeProg` on the input `[5]`: `Nat.size 5 = 3`, so the inner routine costs `6 * 3 + 6 = 24`
steps, and the packaging (copy, length, eight clearing assignments) ten more. -/

example : (run Small.sizeProg (Config.init [5]) 34).mem 0 = 1 := by rfl
example : (run Small.sizeProg (Config.init [5]) 34).mem 1 = 3 := by rfl
example : (run Small.sizeProg (Config.init [5]) 34).mem 2 = 0 := by rfl
example : Halted Small.sizeProg (run Small.sizeProg (Config.init [5]) 34) := by decide

/-- `Nat.log 2 5 = 2`; two steps more than the bit length. -/
example : (run Small.log2Prog (Config.init [5]) 36).mem 1 = 2 := by rfl
example : Halted Small.log2Prog (run Small.log2Prog (Config.init [5]) 36) := by decide

/-- A pair `(3, 4)` is encoded as `[1, 3, 1, 4]`.  Addition costs one step and the packaging
ten. -/
example : (run (seq (addTo 5 2 4) (seq (copyTo 1 5) (seq (assign 0 1)
    (Small.clearRegs Small.scratch)))) (Config.init [1, 3, 1, 4]) 11).mem 1 = 7 := by rfl
example : (run (seq (addTo 5 2 4) (seq (copyTo 1 5) (seq (assign 0 1)
    (Small.clearRegs Small.scratch)))) (Config.init [1, 3, 1, 4]) 11).mem 0 = 1 := by rfl

/-- The comparison `3 ≤ 4` returns the bit `1`, in `5 + 10` steps. -/
example : (run (seq (Arith.leTo 5 2 4 6) (seq (copyTo 1 5) (seq (assign 0 1)
    (Small.clearRegs Small.scratch)))) (Config.init [1, 3, 1, 4]) 15).mem 1 = 1 := by rfl
example : (run (seq (Arith.leTo 5 2 4 6) (seq (copyTo 1 5) (seq (assign 0 1)
    (Small.clearRegs Small.scratch)))) (Config.init [1, 4, 1, 3]) 15).mem 1 = 0 := by rfl

/-! ## Relocation (`Reloc.lean`)

`relocate 0 1 2 P` runs `P` with every address shifted by the value of register `0`, using
registers `1` and `2` as scratch.  Each instruction becomes a block of ten, so the two
instructions of `addProg` become twenty.  The caller's datum at address `5` is untouched, and so
is the base register. -/

/-- The relocated adder. -/
def addProgReloc : Program := Reloc.relocate 0 1 2 addProg

/-- The caller's memory: the base `10` in register `0`, the caller's own datum `999` at address
`5`, and the callee's input `[3, 4]` from address `10` on. -/
def relocMem : Mem := fun a =>
  if a = 0 then 10 else if a = 5 then 999 else
    if 10 ≤ a then initMem [3, 4] (a - 10) else 0

/-- Two instructions, so twenty steps, and the answer appears at the callee's register `1`,
that is, at address `11`. -/
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 11 = 7 := by rfl
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 10 = 1 := by rfl
example : Halted addProgReloc (run addProgReloc ⟨0, relocMem⟩ 20) := by decide
example : ¬ Halted addProgReloc (run addProgReloc ⟨0, relocMem⟩ 19) := by decide

/-- The caller's datum and the base register survive the call. -/
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 5 = 999 := by rfl
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 0 = 10 := by rfl

/-- Nothing below the base is written except the two scratch registers `1` and `2`. -/
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 3 = 0 := by rfl
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 4 = 0 := by rfl
example : (run addProgReloc ⟨0, relocMem⟩ 20).mem 6 = 0 := by rfl

/-! ## The bridge to the workspace convention (`Offset.lean`, `Reloc.lean`)

`relocAt K P` sets the base register, runs `P` relocated to the base `K`, and clears the three
reserved registers, so that `P` runs at the workspace convention `initMemAt K`.  With the adder
and four work registers: one step to set the base, twenty for the two blocks, three to clear, so
twenty-four steps, the length in register `4` and the answer in register `5`, and the four work
registers zero again. -/

example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 5 = 7 := by rfl
example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 4 = 1 := by rfl
example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 0 = 0 := by rfl
example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 1 = 0 := by rfl
example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 2 = 0 := by rfl
example : (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24).mem 3 = 0 := by rfl
example : Halted (relocAt 4 addProg) (run (relocAt 4 addProg) ⟨0, initMemAt 4 [3, 4]⟩ 24) := by
  decide

/-! ## The projections (`Combine.lean`)

`Combine.fstProg K` and `Combine.sndProg K` are routines of the workspace convention: started in
`initMemAt K (Enc.encode (x, y))` they halt in `initMemAt K (Enc.encode x)` resp.
`initMemAt K (Enc.encode y)`.  The encoding of `((3 : ℕ), (4 : ℕ))` is `[1, 3, 1, 4]`, so with
`K = 16` the input occupies registers `16 .. 20` and the answer must be the length `1` in
register `16`, the value in register `17`, and zeros everywhere else. -/

example : (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110).mem 16 = 1 := by rfl
example : (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110).mem 17 = 3 := by rfl
example : (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110).mem 18 = 0 := by rfl
example : (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110).mem 0 = 0 := by rfl
example : (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110).mem 8 = 0 := by rfl
example : Halted (Combine.fstProg 16)
    (run (Combine.fstProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 110) := by decide

example : (run (Combine.sndProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 120).mem 16 = 1 := by rfl
example : (run (Combine.sndProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 120).mem 17 = 4 := by rfl
example : (run (Combine.sndProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 120).mem 18 = 0 := by rfl
example : (run (Combine.sndProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 120).mem 0 = 0 := by rfl
example : Halted (Combine.sndProg 16)
    (run (Combine.sndProg 16) ⟨0, initMemAt 16 [1, 3, 1, 4]⟩ 120) := by decide

end Examples
end RAM
