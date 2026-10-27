import Workspace.Algo.SLPEvalLayout
import Workspace.Machine.RunsOnLoop

/-!
# The straight-line-program evaluator: the program text (Observation 11.1.11)

The RAM program that evaluates a straight-line program on full permutations of the domain,
keeping the sequence in **random-access arrays** in the workspace.  Its specification is proved
in `Workspace/Algo/SLPEvalRAM.lean`; this file only lists the code.

**The input** is `((n, (S, Ker)), prog?)` at the workspace convention (offset `16`); its word
layout is in `Workspace/Algo/SLPEvalLayout.lean`.  Absolute addresses below are `16 + index`
of the list `|E| :: E`.

**The layout of the work.**  Above the input the evaluator allocates a table of `LP + LS`
words (`LP`, `LS` the word lengths of the program and of the generator list):

* entry `LP + j` of the table holds the address of generator `j` (read in place in the input);
* entry `i` holds the address of element `i` of the sequence.

A product or an inverse is written above the table as a fresh block `[1, v[0], 1, v[1], ...]`
(the encoding of the permutation), so every element of the sequence, generator or computed, is
read in constant time per entry.  The product `A B` (`Algo.rawMul`) is the block of the entries
`A[B[u]]`; the inverse is written by scattering, `c[A[u]] := u` (`Algo.scat_eq_rawInv`).

**Registers.**  `8` is the top of the workspace and `10` is scratch (both used by
`RAM.Layout.pushVal`); `0, ..., 7` are scratch; during the evaluation `9` points at the current
instruction, `11` counts the program words left, `12` points at the current table entry,
`13 = n`, `14` is the table base and `15 = LP`.
-/

namespace Algo
namespace SLPRAM

open RAM Layout

/-! ## Setup -/

/-- Registers `13 = n`, `14 = 8 = ` the address above the input, `5 = ` the address of the
option tag of the program, `3 = ` the tag. -/
def setup : Program :=
  seq (copyTo 13 (16 + 3)) <| seq (copyTo 14 (16 + 0)) <| seq (assign 0 17) <|
  seq (addTo 14 14 0) <| seq (copyTo 8 14) <| seq (copyTo 1 (16 + 5)) <| seq (assign 0 22) <|
  seq (addTo 1 1 0) <| seq (loadTo 2 1) <| seq (addTo 5 1 2) <| seq (assign 0 2) <|
  seq (addTo 5 5 0) (loadTo 3 5)

/-- No program: the answer is `none`, the block `[1, 0]`. -/
def noneBranch : Program :=
  seq (copyTo 11 8) <| seq (assign 0 1) <| seq (pushVal 0) <| seq (assign 0 0) <|
  seq (pushVal 0) <| seq (assign 12 2) (finish 16)

/-- Register `15 = LP`, and the table of `LP + LS` zeros allocated above the input. -/
def allocT : Program :=
  seq (assign 0 1) <| seq (addTo 6 5 0) <| seq (loadTo 15 6) <| seq (addTo 8 8 15) <|
  seq (copyTo 0 (16 + 5)) (addTo 8 8 0)

/-! ## The generators -/

/-- One generator: table entry `LP + j` gets the address of its entries. -/
def genBody : Program :=
  seq (assign 0 1) <| seq (addTo 1 9 0) <| seq (storeTo 12 1) <| seq (addTo 9 9 2) <|
  seq (subTo 11 11 2) (addTo 12 12 0)

/-- The generator phase: `9` walks over the generator blocks (`2n + 1` words each), `11`
counts the words left, `12` points at table entry `LP + j`. -/
def genPhase : Program :=
  seq (assign 9 (16 + 6)) <| seq (copyTo 11 (16 + 5)) <| seq (addTo 12 14 15) <|
  seq (copyTo 2 13) <| seq (addTo 2 2 13) <| seq (assign 0 1) <| seq (addTo 2 2 0) <|
  whileNz 11 genBody

/-! ## The evaluation -/

/-- Registers `0 = op`, `1 = a`, `2 = b` of the current instruction. -/
def readIns : Program :=
  seq (assign 0 2) <| seq (addTo 0 9 0) <| seq (loadTo 0 0) <| seq (assign 1 5) <|
  seq (addTo 1 9 1) <| seq (loadTo 1 1) <| seq (assign 2 8) <| seq (addTo 2 9 2) (loadTo 2 2)

/-- A generator: copy its table entry. -/
def genB : Program :=
  seq (copyTo 3 14) <| seq (addTo 3 3 15) <| seq (addTo 3 3 1) <| seq (loadTo 3 3) (storeTo 12 3)

/-- One entry of a product: push `1` and `A[B[u]]`. -/
def prodBody : Program :=
  seq (pushVal 4) <| seq (loadTo 3 1) <| seq (addTo 3 3 3) <| seq (addTo 3 3 0) <|
  seq (loadTo 3 3) <| seq (pushVal 3) <| seq (addTo 1 1 5) (subTo 2 2 4)

/-- A product of elements `a` and `b`. -/
def prodB : Program :=
  seq (addTo 3 14 1) <| seq (loadTo 3 3) <| seq (addTo 0 3 4) <| seq (addTo 3 14 2) <|
  seq (loadTo 3 3) <| seq (addTo 1 3 4) <| seq (copyTo 6 8) <| seq (copyTo 2 13) <|
  seq (assign 5 2) <| seq (whileNz 2 prodBody) (storeTo 12 6)

/-- One block `[1, 0]` of the zeroed array. -/
def zeroBody : Program := seq (pushVal 4) <| seq (pushVal 7) (subTo 2 2 4)

/-- One write of the scattering: `c[A[u]] := u`. -/
def scatBody : Program :=
  seq (loadTo 7 1) <| seq (addTo 7 7 7) <| seq (addTo 7 7 0) <| seq (storeTo 7 3) <|
  seq (addTo 3 3 4) <| seq (addTo 1 1 5) (subTo 2 2 4)

/-- The inverse of element `a`. -/
def invB : Program :=
  seq (addTo 3 14 1) <| seq (loadTo 3 3) <| seq (addTo 1 3 4) <| seq (copyTo 6 8) <|
  seq (copyTo 2 13) <| seq (assign 7 0) <| seq (whileNz 2 zeroBody) <|
  seq (addTo 0 6 4) <| seq (copyTo 2 13) <| seq (assign 3 0) <| seq (assign 5 2) <|
  seq (whileNz 2 scatBody) (storeTo 12 6)

/-- A product (`op = 1`) or an inverse (`op ≥ 2`). -/
def nonGenB : Program := seq (assign 4 1) <| seq (subTo 3 0 4) (ifz 3 invB prodB)

/-- Advance to the next instruction. -/
def evalTail : Program :=
  seq (assign 0 11) <| seq (addTo 9 9 0) <| seq (subTo 11 11 0) <| seq (assign 0 1)
    (addTo 12 12 0)

/-- One instruction. -/
def evalBody : Program := seq readIns <| seq (ifz 0 nonGenB genB) evalTail

/-- The evaluation phase. -/
def evalPhase : Program :=
  seq (assign 0 2) <| seq (addTo 9 5 0) <| seq (copyTo 11 15) <| seq (copyTo 12 14) <|
  whileNz 11 evalBody

/-! ## The answer -/

/-- Register `5 = ` the address of the option tag, recomputed. -/
def tagPtr : Program :=
  seq (copyTo 1 (16 + 5)) <| seq (assign 0 22) <| seq (addTo 1 1 0) <| seq (loadTo 2 1) <|
  seq (addTo 5 1 2) <| seq (assign 0 2) (addTo 5 5 0)

/-- Push a marked element as a framed block: `2n`, then its words. -/
def pushSlot : Program :=
  seq (pushVal 13) <| seq (loadTo 0 12) <| seq (copyTo 2 13) <| seq pushBlock <|
  seq (addTo 14 14 13) <| seq (assign 3 1) (addTo 14 14 3)

/-- One instruction of the second pass: push the element if it is marked. -/
def flagBody : Program :=
  seq (assign 0 10) <| seq (addTo 0 9 0) <| seq (loadTo 0 0) <| seq (ifz 0 pushSlot []) <|
  seq (assign 0 11) <| seq (addTo 9 9 0) <| seq (subTo 15 15 0) <| seq (assign 0 1)
    (addTo 12 12 0)

/-- The head of the answer block and the second pass over the program. -/
def outHead : Program :=
  seq (copyTo 11 8) <| seq (assign 0 0) <| seq (pushVal 0) <| seq (assign 0 1) <|
  seq (pushVal 0) <| seq (assign 0 0) <| seq (pushVal 0) <| seq tagPtr <| seq (assign 0 2) <|
  seq (addTo 9 5 0) <| seq (assign 0 1) <| seq (addTo 6 5 0) <| seq (loadTo 15 6) <|
  seq (copyTo 12 14) <| seq (addTo 13 13 13) <| seq (assign 14 0) (whileNz 15 flagBody)

/-- The two length fields of the answer, and the final move. -/
def outRest2 : Program :=
  seq (addTo 1 14 15) <| seq (assign 0 2) <| seq (addTo 0 11 0) <| seq (storeTo 0 1) <|
  seq (addTo 2 1 13) <| seq (assign 0 3) <| seq (addTo 2 2 0) <| seq (storeTo 11 2) <|
  seq (assign 0 1) <| seq (addTo 12 2 0) (finish 16)

/-- The representative. -/
def outRest1 : Program :=
  seq (pushVal 13) <| seq (assign 0 1) <| seq (addTo 0 9 0) <| seq (loadTo 0 0) <|
  seq (copyTo 1 (16 + 0)) <| seq (assign 2 17) <| seq (addTo 1 1 2) <| seq (addTo 0 0 1) <|
  seq (loadTo 0 0) <| seq (copyTo 2 13) <| seq pushBlock outRest2

/-- The kernel generators, the representative, the two length fields, and the final move. -/
def outTail : Program :=
  seq (copyTo 0 (16 + 5)) <| seq (assign 1 23) <| seq (addTo 0 0 1) <| seq (assign 1 1) <|
  seq (subTo 1 0 1) <| seq (loadTo 2 1) <| seq (copyTo 15 2) <| seq pushBlock outRest1

/-- With a program. -/
def someBranch : Program := seq allocT <| seq genPhase <| seq evalPhase <| seq outHead outTail

/-- **The evaluator.** -/
def slpEvalProg : Program := seq setup (ifz 3 someBranch noneBranch)

end SLPRAM
end Algo
