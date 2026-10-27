/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the outcome the routine of §8.2 returns is the object the reduction of
§6 finds.
-/
import Workspace.Algo.DesignRelabel
import Workspace.DesignLemma.Reduction

/-!
# §8.1–8.2 — the interface between the routine and the reduction

`Babai.designLemma_finds` states Theorem 8.1.2 in the categorical language of §6: the reduction
*finds* one of a family of outcomes, `Babai.designOut X`, at the multiplicative cost `n^k`.  The
routine of `Workspace/Algo/DesignOut.lean` returns a string `x⃗` at which the test of lines 04–08
fires, together with the three objects lines 05 and 08 read off at it.

This file connects the two *statements of the test*.  §8.2 spells the test in two ways:

* `Babai.KAryPartStruct.Returns α X hl x⃗` — used by `Babai.KAryPartStruct.procedure` and by the
  routine's specification (`Algo.designOutcome_spec`);
* `Babai.KAryPartStruct.ReturnsAtStruct α (X_x⃗)` — used by `Babai.DesignReturns` and hence by
  `Babai.designOut`, the family `Babai.designLemma_finds` finds.

They are the same test: `Algo.returns_iff_returnsAtStruct`.  With it, the outcome attached to the
string the routine returns is a member of `Babai.designOut`
(`Algo.designOutcomeOf_mem_designOut`), which is what package A10 has to feed to §9.

What is *not* here is the encoding: the categorical side works over an abstract vertex set
`↥X.car`, the routine over `Fin n` with the vertices named `0, …, n − 1`.  Transporting the
input along a naming of the vertices is the job of the encoding layer; see the note "A9,
session 3" in `Workspace/Algo/DESIGN.md` for the exact statement that remains.

No axiom and no `sorry`.
-/

namespace Algo

open Babai

section Spelling

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω} [Fintype ↥s] [DecidableEq ↥s]
  {C : Type*} {k l : ℕ}

/-- **The two spellings of lines 04–08 agree.**  `Babai.KAryPartStruct.Returns` (used by the
mathematical procedure and by the routine's specification) is `Str.Distinct` together with
`Babai.KAryPartStruct.ReturnsAtStruct` at the restriction `X_x⃗` (used by `Babai.designOut`).
The two existential clauses `ℓ + 2 ≤ k` and `2 ≤ k − ℓ` are the same condition, since
`ℓ ≤ k`. -/
theorem returns_iff_returnsAtStruct (α : ℝ) (X : KAryPartStruct ↥s C k) (hl : l ≤ k)
    (x : Str ↥s l) :
    KAryPartStruct.Returns α X hl x
      ↔ Str.Distinct x ∧ KAryPartStruct.ReturnsAtStruct α (X.restrTo hl x) := by
  rw [KAryPartStruct.Returns, KAryPartStruct.ReturnsAtStruct]
  refine and_congr Iff.rfl (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨h2, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨hm, h⟩; exact ⟨by omega, h⟩

end Spelling

/-- Line 01 of the routine's specification *is* `Babai.KAryRelStruct.kWL`: the specifications of
`Workspace/Algo/DesignScan.lean` and `Workspace/Algo/DesignOut.lean` are stated for
`F3 ∘ F2 ∘ F1` of the decoded input structure, which is what the categorical side calls
`kWL`. -/
theorem decRel_kWL (n k : ℕ) (rels : RawRelStruct) :
    (decRel n k rels).kWL = (decRel n k rels).F1.F2.F3 := rfl

section Family

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {k : ℕ} {α : ℝ}

/-- **The outcome at a returning string is one of the outcomes the reduction finds.**  If the
test of lines 04–08 fires at the string `x⃗` in the `k`-ary coherent configuration `kWL(X)` that
line 01 produces, then the outcome read off at `x⃗` belongs to the family `Babai.designOut X`
whose members `Babai.designLemma_finds` finds.  This is the interface package A10 calls:
`Algo.designOutcome_spec` produces such an `x⃗`. -/
theorem designOutcomeOf_mem_designOut (X : Pt (DesignInputs Ω k α)) {l : ℕ} (hl : l < k)
    (x : Str ↥X.car l)
    (hx : letI : Fintype ↥X.car := Fintype.ofFinite _
          letI : DecidableEq ↥X.car := Classical.decEq _
          KAryPartStruct.Returns α (karyOf X).kWL hl.le x) :
    Babai.designOutcome X hl.le x ∈ designOut X := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨hd, hr⟩ := (returns_iff_returnsAtStruct α (karyOf X).kWL hl.le x).1 hx
  exact ⟨l, hl, x, hd, hr, rfl⟩

end Family

end Algo
