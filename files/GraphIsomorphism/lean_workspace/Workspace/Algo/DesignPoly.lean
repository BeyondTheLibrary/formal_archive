/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the running time of the tests of Procedure "Design Lemma" (§8.2).
-/
import Workspace.Algo.DesignRaw

/-!
# §8.2 Procedure "Design Lemma" — the tests at one string are `RAM.PolyFun`

Theorem 8.1.2 and Theorem 8.1.5 claim the whole procedure runs *"in time `n^{O(k)}`"*.  The
`k`-ary refinement of line 01 is A8 (`Algo.polyFun_wlPipeline`, `Algo.quasiFun_guardedPipeline`).
This file is the other half at one string: every test of lines 03–08 is polynomial **in the
size of the table**, uniformly in `k` — the arity enters only through the length of the tuples
that are looked up, never through a loop over `k^k` many objects as `Algo.rawF2` does.  Feeding
the guarded table of `Workspace/Algo/WLGuarded.lean` into these routines therefore gives the
paper's `n^{O(k)}` with `k = O(log n)` in the input, exactly as
`Algo.quasiPolyFun_guardedVertexColoring` does for the vertex coloring.

Everything here is a `RAM.PolyFun` for the unit-cost RAM of `Workspace/Machine`; nothing is an
abstract cost count.  No axiom and no `sorry`.
-/

namespace Algo

open Babai RAM

/-! ## The individualized tuple -/

theorem polyFun_indivTuple : PolyFun indivTuple := by
  classical
  -- the letter written at one position of the tuple
  have hxs : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => w.1.1.2) :=
    polyFun_fst.comp (polyFun_fst.comp polyFun_snd)
  have hidx : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => w.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hu : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => w.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have hv : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) => w.1.2.2) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_snd)
  have hdef : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) =>
      if w.2.2 = w.1.1.2.length then w.1.2.1 else w.1.2.2) := by
    refine (PolyFun.ite ((hidx.pair (hxs.comp polyFun_length)).comp polyFun_natEq)
      hu hv).of_eq (fun w => ?_)
    by_cases h : w.2.2 = w.1.1.2.length <;> simp [h]
  have hf : PolyFun (fun w : ((List ℕ × List ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) =>
      w.1.1.2.getD w.2.2 (if w.2.2 = w.1.1.2.length then w.1.2.1 else w.1.2.2)) :=
    ((hxs.pair hidx).pair hdef).comp polyFun_getD
  have hzip : PolyFun (fun z : (List ℕ × List ℕ) × (ℕ × ℕ) => z.1.1.zipIdx) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_zipIdx
  exact ((polyFun_id.pair hzip).comp (PolyFun.mapParam hf)).of_eq (fun z => rfl)

/-! ## Reading the restriction -/

theorem polyFun_restrPairColorAt : PolyFun restrPairColorAt := by
  have htbl : PolyFun (fun w : DIn × (ℕ × ℕ) => w.1.1.2.2) :=
    polyFun_fst.comp (polyFun_fst.comp (polyFun_snd.comp polyFun_snd))
  have harg : PolyFun (fun w : DIn × (ℕ × ℕ) => ((w.1.1.1, w.2) : (List ℕ × List ℕ) × (ℕ × ℕ))) :=
    (polyFun_fst.comp (polyFun_fst.comp polyFun_fst)).pair polyFun_snd
  exact (htbl.pair (harg.comp polyFun_indivTuple)).comp polyFun_tblGet

theorem polyFun_restrVColorAt : PolyFun restrVColorAt :=
  (polyFun_fst.pair (polyFun_snd.pair polyFun_snd)).comp polyFun_restrPairColorAt

theorem polyFun_restrVColors : PolyFun restrVColors := by
  have hdom : PolyFun (fun z : DIn => z.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  exact ((polyFun_id.pair hdom).comp (PolyFun.mapParam polyFun_restrVColorAt)).of_eq
    (fun z => rfl)

/-! ## Lines 04–06 -/

theorem polyFun_classSize : PolyFun classSize := by
  classical
  have hdom : PolyFun (fun w : DIn × ℕ => w.1.1.2.1) :=
    polyFun_fst.comp (polyFun_fst.comp (polyFun_snd.comp polyFun_fst))
  have hq : PolyFun (fun s : (DIn × ℕ) × ℕ =>
      decide (restrVColorAt (s.1.1, s.2) = s.1.2)) :=
    (((polyFun_fst.comp polyFun_fst).pair polyFun_snd).comp polyFun_restrVColorAt).pair
      (polyFun_fst.comp polyFun_snd) |>.comp polyFun_natEq
  exact ((polyFun_id.pair hdom).comp (PolyFun.filterParam hq)).comp polyFun_length

theorem polyFun_noDominantB : PolyFun noDominantB := by
  classical
  have hb : PolyFun (fun s : DIn × ℕ => s.1.2.2) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_snd)
  have ha : PolyFun (fun s : DIn × ℕ => s.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have hn : PolyFun (fun s : DIn × ℕ => s.1.1.2.1.length) :=
    (polyFun_fst.comp (polyFun_fst.comp (polyFun_snd.comp polyFun_fst))).comp polyFun_length
  have hq : PolyFun (fun s : DIn × ℕ =>
      !decide (s.1.2.2 * classSize (s.1, s.2) ≤ s.1.2.1 * s.1.1.2.1.length)) := by
    have htest : PolyFun (fun s : DIn × ℕ =>
        decide (s.1.2.2 * classSize (s.1, s.2) ≤ s.1.2.1 * s.1.1.2.1.length)) :=
      ((hb.pair polyFun_classSize).comp polyFun_mul).pair ((ha.pair hn).comp polyFun_mul)
        |>.comp polyFun_le
    refine (PolyFun.ite htest (polyFun_const false) (polyFun_const true)).of_eq (fun s => ?_)
    by_cases h : s.1.2.2 * classSize (s.1, s.2) ≤ s.1.2.1 * s.1.1.2.1.length <;> simp [h]
  exact ((polyFun_id.pair polyFun_restrVColors).comp (PolyFun.filterParam hq)).comp
    polyFun_isEmpty

theorem polyFun_dominantList : PolyFun dominantList := by
  classical
  have hdom : PolyFun (fun z : DIn => z.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have ha : PolyFun (fun s : DIn × ℕ => s.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have hb : PolyFun (fun s : DIn × ℕ => s.1.2.2) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_snd)
  have hn : PolyFun (fun s : DIn × ℕ => s.1.1.2.1.length) :=
    (polyFun_fst.comp (polyFun_fst.comp (polyFun_snd.comp polyFun_fst))).comp polyFun_length
  have hsz : PolyFun (fun s : DIn × ℕ => classSize (s.1, restrVColorAt (s.1, s.2))) :=
    (polyFun_fst.pair polyFun_restrVColorAt).comp polyFun_classSize
  have hq : PolyFun (fun s : DIn × ℕ =>
      decide (s.1.2.1 * s.1.1.2.1.length + 1 ≤ s.1.2.2 * classSize (s.1,
        restrVColorAt (s.1, s.2)))) :=
    ((((ha.pair hn).comp polyFun_mul).pair (polyFun_const 1)).comp polyFun_add).pair
      ((hb.pair hsz).comp polyFun_mul) |>.comp polyFun_le
  exact ((polyFun_id.pair hdom).comp (PolyFun.filterParam hq)).of_eq (fun z => rfl)

/-! ## Line 07 -/

theorem polyFun_pairColors : PolyFun pairColors := by
  have hinner : PolyFun (fun w : DIn × ℕ =>
      (dominantList w.1).map fun v => restrPairColorAt (w.1, (w.2, v))) := by
    have hf : PolyFun (fun s : (DIn × ℕ) × ℕ =>
        restrPairColorAt (s.1.1, (s.1.2, s.2))) :=
      ((polyFun_fst.comp polyFun_fst).pair
        ((polyFun_fst.comp polyFun_snd).pair polyFun_snd)).comp polyFun_restrPairColorAt
    exact ((polyFun_id.pair ((polyFun_fst).comp polyFun_dominantList)).comp
      (PolyFun.mapParam hf)).of_eq (fun w => rfl)
  exact ((polyFun_id.pair polyFun_dominantList).comp
    (PolyFun.flatMapParam hinner)).of_eq (fun z => rfl)

theorem polyFun_cliqueRank : PolyFun cliqueRank :=
  (((polyFun_const ([] : List ℕ)).pair polyFun_pairColors).comp
    (polyFun_dedupG polyFun_natEq)).comp polyFun_length

/-! ## Line 03 and the whole test -/

theorem polyFun_nodupB : PolyFun nodupB :=
  (((polyFun_const ([] : List ℕ)).pair polyFun_id).comp
    (polyFun_dedupG polyFun_natEq) |>.comp polyFun_length).pair polyFun_length
    |>.comp polyFun_natEq

theorem polyFun_returnsB : PolyFun returnsB := by
  classical
  have hnd : PolyFun (fun z : DIn => nodupB z.1.1.2) :=
    (polyFun_fst.comp (polyFun_fst.comp polyFun_snd)).comp polyFun_nodupB
  have hroom : PolyFun (fun z : DIn => decide (z.1.1.2.length + 2 ≤ z.1.1.1.length)) :=
    ((((polyFun_fst.comp (polyFun_fst.comp polyFun_snd)).comp polyFun_length).pair
      (polyFun_const 2)).comp polyFun_add).pair
      ((polyFun_fst.comp (polyFun_fst.comp polyFun_fst)).comp polyFun_length)
      |>.comp polyFun_le
  have hnotclique : PolyFun (fun z : DIn => !decide (cliqueRank z = 2)) := by
    have htest : PolyFun (fun z : DIn => decide (cliqueRank z = 2)) :=
      (polyFun_cliqueRank.pair (polyFun_const 2)).comp polyFun_natEq
    refine (PolyFun.ite htest (polyFun_const false) (polyFun_const true)).of_eq (fun z => ?_)
    by_cases h : cliqueRank z = 2 <;> simp [h]
  exact PolyFun.ite hnd
    (PolyFun.ite polyFun_noDominantB (polyFun_const true)
      (PolyFun.ite hroom hnotclique (polyFun_const false)))
    (polyFun_const false)



/-! ## Line 03: the loop over the strings of one length -/

theorem polyFun_withStr : PolyFun withStr :=
  (((polyFun_fst.comp (polyFun_fst.comp (polyFun_fst.comp polyFun_fst))).pair
    polyFun_snd).pair (polyFun_fst.comp (polyFun_fst.comp polyFun_snd))).pair
    (polyFun_fst.comp polyFun_snd)

/-- **Line 03 is a `RAM.PolyFun` at each length**, in the size of the table: it enumerates the
`n^ℓ` strings and runs the polynomial test of lines 04–08 at each.  The length `ℓ` is a
parameter of the theorem, as the arity is in `Algo.polyFun_rawF2`; the paper's loop of line 02
over all `ℓ ≤ k − 1` puts `ℓ` into the input and belongs to the guarded layer. -/
theorem polyFun_scanLen (l : ℕ) : PolyFun (scanLen l) := by
  have hdom : PolyFun (fun z : DIn => z.1.2.1) :=
    polyFun_fst.comp (polyFun_snd.comp polyFun_fst)
  have htuples : PolyFun (fun z : DIn => tuplesOf z.1.2.1 l) :=
    hdom.comp ((polyFun_tuplesOf l).comp polyFun_snd)
  have hq : PolyFun (fun s : DIn × List ℕ => returnsB (withStr s)) :=
    polyFun_withStr.comp polyFun_returnsB
  exact ((polyFun_id.pair htuples).comp (PolyFun.filterParam hq)).comp polyFun_headOption

end Algo
