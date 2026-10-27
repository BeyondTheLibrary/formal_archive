/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the testable part of the well-formedness predicate of each round.
-/
import Workspace.Algo.WFTestsSI
import Workspace.Algo.Descent
import Workspace.Algo.Imprimitive
import Workspace.Algo.LocalCertRound
import Workspace.Algo.TopRound
import Workspace.Algo.TopWindowRound
import Workspace.Algo.TopThreeRound

/-!
# The testable part of each round's well-formedness

`Workspace/Algo/WFTestsSI.lean` tests `Algo.WinWF` and `Algo.NormSIWF` in full.  The rounds
built on top of a window instance add clauses, and only some of them are tests.  This file
gives a routine for the part that is, one round at a time, and says in each docstring what is
left over.  Nothing is faked: a clause with no polynomial test gets no routine.

## Main definitions

* `Algo.wftBlocksWF` — the test for `Algo.BlocksWF` (this one is complete);
* `Algo.wftDescPart`, `Algo.wftImpPart`, `Algo.wftLCPart` — the testable part of
  `Algo.DescWF`, `Algo.ImpWF`, `Algo.LCWF`;
* `Algo.wftTop1Part`, `Algo.wftTop2Part`, `Algo.wftTop3Part` — the testable part of
  `Algo.Top1WF`, `Algo.Top2WF`, `Algo.Top3WF`.

## Main results

Each routine comes with `… = true ↔ <the testable conjunct>` and a `RAM.PolyFun` statement on
all inputs.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM

/-! ## Block systems

`Algo.BlocksWF n bl` (`Workspace/Algo/Blocks.lean`) has three clauses: the blocks are
nonempty, their points are points of the domain, and no point is repeated across the whole
system.  All three are tests, so this predicate is decided in full. -/

/-- **The test for `Algo.BlocksWF`.** -/
def wftBlocksWF (p : ℕ × RawBlocks) : Bool :=
  wftAll (fun z : ℕ × List ℕ => !z.2.isEmpty) p &&
    wftAllLt (p.1, p.2.flatten) && wftNodup p.2.flatten

/-- **The specification of `Algo.wftBlocksWF`.** -/
theorem wftBlocksWF_eq_true_iff (n : ℕ) (bl : RawBlocks) :
    wftBlocksWF (n, bl) = true ↔ BlocksWF n bl := by
  rw [wftBlocksWF]
  simp only [Bool.and_eq_true, wftAll_eq_true_iff, wftAllLt_eq_true_iff,
    wftNodup_eq_true_iff, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem wftPolyFun_blocksWF : PolyFun wftBlocksWF := by
  have hn : PolyFun (fun p : ℕ × RawBlocks => p.1) := polyFun_fst
  have hfl : PolyFun (fun p : ℕ × RawBlocks => p.2.flatten) :=
    polyFun_snd.comp polyFun_flatten
  exact wftPolyFun_and (wftPolyFun_and
    (wftPolyFun_all (wftPolyFun_not (polyFun_snd.comp polyFun_isEmpty)))
    ((hn.pair hfl).comp wftPolyFun_allLt))
    (hfl.comp wftPolyFun_nodup)

/-! ## The descent round

`Algo.DescWF n I` is `Algo.WinWF n I.1` and, when the node stores `(d, idx)`, the two
clauses `d.Nodup` and `∀ x ∈ d, x < n` — both tests — and `idx = Algo.winCosetIndex n … d …`.
The last one is **not** a test: `winCosetIndex` is the index `|G : G_(Δ_H)|` of a pointwise
stabilizer, which can be as large as `n^{|d|}`, so no routine compares it in polynomial time.
It is a fact about the data, placed in the node by the parent that built it. -/

/-- **The testable part of `Algo.DescWF`.** -/
def wftDescPart (p : ℕ × RawDescSI) : Bool :=
  wftWinWF (p.1, p.2.1) &&
    p.2.2.elim true (fun q => wftNodup q.1 && wftAllLt (p.1, q.1))

/-- **The specification of `Algo.wftDescPart`.** -/
theorem wftDescPart_eq_true_iff (n : ℕ) (I : RawDescSI) :
    wftDescPart (n, I) = true ↔
      WinWF n I.1 ∧ ∀ d idx, I.2 = some (d, idx) → d.Nodup ∧ ∀ x ∈ d, x < n := by
  rw [wftDescPart]
  cases hs : I.2 with
  | none => simp [hs, wftWinWF_eq_true_iff]
  | some q =>
    obtain ⟨d, idx⟩ := q
    simp only [hs, Option.elim_some, Bool.and_eq_true, wftWinWF_eq_true_iff,
      wftNodup_eq_true_iff, wftAllLt_eq_true_iff]
    constructor
    · rintro ⟨hw, hnd, hlt⟩
      exact ⟨hw, fun d' idx' h => by cases h; exact ⟨hnd, hlt⟩⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, (h d idx rfl).1, (h d idx rfl).2⟩

theorem wftPolyFun_descPart : PolyFun wftDescPart := by
  have hn : PolyFun (fun p : ℕ × RawDescSI => p.1) := polyFun_fst
  have hw : PolyFun (fun p : ℕ × RawDescSI => ((p.1, p.2.1) : ℕ × RawWinSI)) :=
    hn.pair ((polyFun_snd.comp polyFun_fst))
  have hopt : PolyFun (fun p : ℕ × RawDescSI =>
      ((p.2.2, p.1) : Option (List ℕ × ℕ) × ℕ)) :=
    (polyFun_snd.comp polyFun_snd).pair hn
  have hinner : PolyFun (fun z : (List ℕ × ℕ) × ℕ =>
      wftNodup z.1.1 && wftAllLt (z.2, z.1.1)) :=
    wftPolyFun_and ((polyFun_fst.comp polyFun_fst).comp wftPolyFun_nodup)
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp wftPolyFun_allLt)
  exact wftPolyFun_and (hw.comp wftPolyFun_winWF)
    (hopt.comp (PolyFun.optionElim (polyFun_const true) hinner))

/-! ## The imprimitive round

`Algo.ImpWF n I` is `Algo.WinWF n I.1` and, when the node stores `(bl, idx)`,
`Algo.BlocksWF n bl` — a test — together with `Algo.BlockData n bl (descGens n I.1)` and
`idx = Algo.blockCosetIndex …`.  `BlockData` says that "generator ↦ its action on the blocks"
extends to a homomorphism; see the note on `Algo.ImgsOf` at the end of
`Workspace/Algo/WFTestsSI.lean` for why that is not a polynomial test with the tools of
`Workspace/Algo/`.  `blockCosetIndex` is a subgroup index, so it is not one either. -/

/-- **The testable part of `Algo.ImpWF`.** -/
def wftImpPart (p : ℕ × RawImpSI) : Bool :=
  wftWinWF (p.1, p.2.1) && p.2.2.elim true (fun q => wftBlocksWF (p.1, q.1))

/-- **The specification of `Algo.wftImpPart`.** -/
theorem wftImpPart_eq_true_iff (n : ℕ) (I : RawImpSI) :
    wftImpPart (n, I) = true ↔
      WinWF n I.1 ∧ ∀ bl idx, I.2 = some (bl, idx) → BlocksWF n bl := by
  rw [wftImpPart]
  cases hs : I.2 with
  | none => simp [hs, wftWinWF_eq_true_iff]
  | some q =>
    obtain ⟨bl, idx⟩ := q
    simp only [hs, Option.elim_some, Bool.and_eq_true, wftWinWF_eq_true_iff,
      wftBlocksWF_eq_true_iff]
    constructor
    · rintro ⟨hw, hb⟩
      exact ⟨hw, fun bl' idx' h => by cases h; exact hb⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, h bl idx rfl⟩

theorem wftPolyFun_impPart : PolyFun wftImpPart := by
  have hn : PolyFun (fun p : ℕ × RawImpSI => p.1) := polyFun_fst
  have hw : PolyFun (fun p : ℕ × RawImpSI => ((p.1, p.2.1) : ℕ × RawWinSI)) :=
    hn.pair (polyFun_snd.comp polyFun_fst)
  have hopt : PolyFun (fun p : ℕ × RawImpSI =>
      ((p.2.2, p.1) : Option (RawBlocks × ℕ) × ℕ)) :=
    (polyFun_snd.comp polyFun_snd).pair hn
  have hinner : PolyFun (fun z : (RawBlocks × ℕ) × ℕ => wftBlocksWF (z.2, z.1.1)) :=
    (polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp wftPolyFun_blocksWF
  exact wftPolyFun_and (hw.comp wftPolyFun_winWF)
    (hopt.comp (PolyFun.optionElim (polyFun_const true) hinner))

/-! ## The local certificates round

`Algo.LCWF n I` is `Algo.WinWF n I.1` and, when the node stores `(td, idx)`: the test set is
a domain witness of at most `n` points — two tests — its images are well-formed permutations
of the test set — a test — and then `∃ ψ, Algo.ImgsOf (descGens n I.1) (lcImgs td) ψ` and
`idx = Algo.actCosetIndex …`, neither of which is a test. -/

/-- **The testable part of `Algo.LCWF`.** -/
def wftLCPart (p : ℕ × RawLCSI) : Bool :=
  wftWinWF (p.1, p.2.1) &&
    p.2.2.elim true (fun q =>
      decide (q.1.1.length ≤ p.1) && wftAllLt (p.1, q.1.1) &&
        wftIsGensOf (q.1.1.length, q.1.2))

/-- **The specification of `Algo.wftLCPart`.** -/
theorem wftLCPart_eq_true_iff (n : ℕ) (I : RawLCSI) :
    wftLCPart (n, I) = true ↔
      WinWF n I.1 ∧ ∀ td idx, I.2 = some (td, idx) →
        (td.1.length ≤ n ∧ ∀ u ∈ td.1, u < n) ∧ RawGens.WF td.1.length td.2 := by
  rw [wftLCPart]
  cases hs : I.2 with
  | none => simp [hs, wftWinWF_eq_true_iff]
  | some q =>
    obtain ⟨td, idx⟩ := q
    simp only [hs, Option.elim_some, Bool.and_eq_true, wftWinWF_eq_true_iff,
      decide_eq_true_iff, wftAllLt_eq_true_iff, wftIsGensOf_eq_true_iff]
    constructor
    · rintro ⟨hw, ⟨hl, hlt⟩, hg⟩
      exact ⟨hw, fun td' idx' h => by cases h; exact ⟨⟨hl, hlt⟩, hg⟩⟩
    · rintro ⟨hw, h⟩
      exact ⟨hw, ⟨(h td idx rfl).1.1, (h td idx rfl).1.2⟩, (h td idx rfl).2⟩

theorem wftPolyFun_lcPart : PolyFun wftLCPart := by
  have hn : PolyFun (fun p : ℕ × RawLCSI => p.1) := polyFun_fst
  have hw : PolyFun (fun p : ℕ × RawLCSI => ((p.1, p.2.1) : ℕ × RawWinSI)) :=
    hn.pair (polyFun_snd.comp polyFun_fst)
  have hopt : PolyFun (fun p : ℕ × RawLCSI =>
      ((p.2.2, p.1) : Option (RawTAct × ℕ) × ℕ)) :=
    (polyFun_snd.comp polyFun_snd).pair hn
  have htd : PolyFun (fun z : (RawTAct × ℕ) × ℕ => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have himgs : PolyFun (fun z : (RawTAct × ℕ) × ℕ => z.1.1.2) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_snd
  have hinner : PolyFun (fun z : (RawTAct × ℕ) × ℕ =>
      decide (z.1.1.1.length ≤ z.2) && wftAllLt (z.2, z.1.1.1) &&
        wftIsGensOf (z.1.1.1.length, z.1.1.2)) :=
    wftPolyFun_and (wftPolyFun_and ((htd.comp polyFun_length).le polyFun_snd)
      ((polyFun_snd.pair htd).comp wftPolyFun_allLt))
      (((htd.comp polyFun_length).pair himgs).comp wftPolyFun_isGensOf)
  exact wftPolyFun_and (hw.comp wftPolyFun_winWF)
    (hopt.comp (PolyFun.optionElim (polyFun_const true) hinner))

/-! ## The top-action rounds

For all three, the testable part is the domain length, and for the last two also `0 < n`.
What is left over is, in every case, "the stored child is one of the children the top node
builds".  For `Algo.Top1WF` this is a **bounded** existential over the child index, so it is
decidable by scanning the children; but the number of children is bounded only by the round's
quasipolynomial `widthBound`, so the scan is a `RAM.QuasiFun` and not a `RAM.PolyFun`.  For
`Algo.Top2WF` and `Algo.Top3WF` the existential also ranges over a coset
`c : RawGens × RawPerm`, which is the answer of a sibling call and is not carried by the
node, so there is nothing to scan at all. -/

/-- The domain of the action data has the right length. -/
def wftActDomLen (p : ℕ × RawAction) : Bool := decide (p.2.1.1.length = p.1)

theorem wftPolyFun_actDomLen : PolyFun wftActDomLen :=
  (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).comp polyFun_length).natEq polyFun_fst

/-- **The testable part of `Algo.Top1WF`.** -/
def wftTop1Part (p : ℕ × RawTop1Node) : Bool := wftActDomLen (p.1, p.2.1.1)

/-- **The specification of `Algo.wftTop1Part`.** -/
theorem wftTop1Part_eq_true_iff (n : ℕ) (I : RawTop1Node) :
    wftTop1Part (n, I) = true ↔ I.1.1.1.1.length = n := by
  simp [wftTop1Part, wftActDomLen]

theorem wftPolyFun_top1Part : PolyFun wftTop1Part :=
  (polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).comp
    wftPolyFun_actDomLen

/-- **The testable part of `Algo.Top2WF`.** -/
def wftTop2Part (p : ℕ × RawTop2Node) : Bool :=
  decide (0 < p.1) && wftActDomLen (p.1, p.2.1.1)

/-- **The specification of `Algo.wftTop2Part`.** -/
theorem wftTop2Part_eq_true_iff (n : ℕ) (I : RawTop2Node) :
    wftTop2Part (n, I) = true ↔ 0 < n ∧ I.1.1.1.1.length = n := by
  simp [wftTop2Part, wftActDomLen]

theorem wftPolyFun_top2Part : PolyFun wftTop2Part :=
  wftPolyFun_and ((polyFun_const 1).le polyFun_fst)
    ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).comp
      wftPolyFun_actDomLen)

/-- **The testable part of `Algo.Top3WF`.** -/
def wftTop3Part (p : ℕ × RawTop3Node) : Bool :=
  decide (0 < p.1) && wftActDomLen (p.1, p.2.1.1)

/-- **The specification of `Algo.wftTop3Part`.** -/
theorem wftTop3Part_eq_true_iff (n : ℕ) (I : RawTop3Node) :
    wftTop3Part (n, I) = true ↔ 0 < n ∧ I.1.1.1.1.length = n := by
  simp [wftTop3Part, wftActDomLen]

theorem wftPolyFun_top3Part : PolyFun wftTop3Part :=
  wftPolyFun_and ((polyFun_const 1).le polyFun_fst)
    ((polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).comp
      wftPolyFun_actDomLen)

/-! ## The Chain Rule round, in full

`Algo.chainRound`'s `WF` is `Algo.WinWF n`, and `Algo.wftWinWF` tests it completely.  So the
Chain Rule is the one round in the tree whose `Algo.Round.RunCost.wfCheck` can be supplied
today, with `wfCheck_eq_true` and not only soundness. -/

/-- **The Chain Rule round's well-formedness is decided.** -/
theorem wftWinWF_chainRound (n : ℕ) (solve : RawWinSI → RawCoset) (I : RawWinSI) :
    wftWinWF (n, I) = true ↔ (chainRound n solve).WF I :=
  wftWinWF_eq_true_iff n I

end Algo
