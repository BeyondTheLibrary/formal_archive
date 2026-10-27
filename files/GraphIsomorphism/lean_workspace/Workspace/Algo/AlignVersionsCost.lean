/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the step functions of Eq. (71) run in polynomial time.
-/
import Workspace.Algo.AlignVersions

/-! # The step functions of Procedure Align over the versions are polynomial

Each step of the loop of `Workspace/Algo/AlignVersions.lean` is a `RAM.PolyFun`: the skip to
the next version (`Algo.avNext`) scans the versions once with a filter, and every other step
is a fixed composition of routines already on the RAM (`Algo.alignPairCoset`,
`Algo.rawIsInvariant`, `Algo.tidyGens`, `Algo.normPerm`, `Algo.rawCosetJoin`). No fold with a
growing accumulator is needed.
-/

namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem pIsSome {β : Type*} [Enc β] : PolyFun (fun o : Option β => o.isSome) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const false) (polyFun_const true))).of_eq
      (fun o => by cases o <;> rfl)

private theorem pand {α : Type*} [Enc α] {f g : α → Bool} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a && g a) :=
  (PolyFun.ite hf hg (polyFun_const false)).of_eq (fun a => by
    cases hfa : f a <;> simp [hfa])

theorem polyFun_rawCosetNorm : PolyFun rawCosetNorm := by
  have hs : PolyFun (fun r : (RawGens × RawPerm) × (RawStr × RawCoset) =>
      (some (tidyGens (r.2.1, r.1.1), normPerm (r.2.1, r.1.2)) : RawCoset)) := by
    have j : PolyFun (fun r : (RawGens × RawPerm) × (RawStr × RawCoset) => r) := polyFun_id
    exact ((((pfst (psnd j)).pair (pfst (pfst j))).comp polyFun_tidyGens).pair
      (((pfst (psnd j)).pair (psnd (pfst j))).comp polyFun_normPerm)).comp polyFun_some
  have i : PolyFun (fun p : RawStr × RawCoset => p) := polyFun_id
  refine (((psnd i).pair i).comp (PolyFun.optionElim (polyFun_const none) hs)).of_eq
    (fun p => ?_)
  obtain ⟨x, a⟩ := p
  cases a <;> rfl

theorem polyFun_avTr : PolyFun avTr := by
  have i : PolyFun (fun p : AVHdr × ℕ => p) := polyFun_id
  exact (pfst (psnd (psnd (psnd (psnd (pfst i)))))).pair
    (((pfst (pfst i)).pair ((pfst (psnd (pfst i))).pair
    (((pfst (psnd (psnd (pfst i)))).pair (psnd i)).pair
      (polyFun_const ((none, none) : RawAlignOutcome)) |>.comp polyFun_getD))).comp
    polyFun_alignPairCoset) |>.comp polyFun_rawCosetNorm

theorem polyFun_avNext : PolyFun avNext := by
  have i : PolyFun (fun p : AVHdr × ℕ => p) := polyFun_id
  have hL := pfst (psnd (psnd (pfst i)))
  have hq : PolyFun (fun r : (AVHdr × ℕ) × ℕ => decide (r.1.2 ≤ r.2) && (avTr (r.1.1, r.2)).isSome) := by
    have j : PolyFun (fun r : (AVHdr × ℕ) × ℕ => r) := polyFun_id
    exact pand ((psnd (pfst j)).le (psnd j))
      ((((pfst (pfst j)).pair (psnd j)).comp polyFun_avTr).comp pIsSome)
  have hfilt : PolyFun (fun p : AVHdr × ℕ =>
      (List.range p.1.2.2.1.length).filter (fun i => decide (p.2 ≤ i) && (avTr (p.1, i)).isSome)) :=
    (i.pair (hL.comp polyFun_rangeLength)).comp (PolyFun.filterParam hq)
  refine ((hfilt.comp polyFun_headOption).pair (hL.comp polyFun_length) |>.comp
    polyFun_optionGetD).of_eq (fun p => ?_)
  unfold avNext
  cases (List.range p.1.2.2.1.length).filter
    (fun i => decide (p.2 ≤ i) && (avTr (p.1, i)).isSome) <;> rfl

theorem polyFun_avPos : PolyFun avPos := by
  have i : PolyFun (fun p : AVHdr × ℕ × RawCoset => p) := polyFun_id
  have hn : PolyFun (fun p : AVHdr × ℕ × RawCoset => avNext (p.1, p.2.1)) :=
    ((pfst i).pair (pfst (psnd i))).comp polyFun_avNext
  exact hn.pair ((polyFun_const 0).pair
    ((((pfst i).pair hn).comp polyFun_avTr).pair
      (((pfst (psnd (psnd (psnd (psnd (pfst i)))))).pair (psnd (psnd i))).comp
        polyFun_rawCosetNorm)))

theorem polyFun_avInit : PolyFun avInit :=
  (polyFun_id.pair ((polyFun_const 0).pair (polyFun_const none))).comp polyFun_avPos

set_option maxHeartbeats 2000000 in
theorem polyFun_avChild : PolyFun avChild := by
  let Z := (RawGens × RawPerm) × (AVHdr × AVState)
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hh := pfst (psnd z)
  have hw := pfst (psnd (psnd (psnd z)))
  have hwins := pfst (psnd (psnd (psnd hh)))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hy := psnd (psnd (psnd (psnd (psnd hh))))
  have hwin : PolyFun (fun q : Z => q.2.1.2.2.2.1.getD q.2.2.2.1 []) :=
    ((hwins.pair hw).pair (polyFun_const [])).comp polyFun_getD
  have htidy : PolyFun (fun q : Z => tidyGens (q.2.1.2.2.2.2.1, q.1.1)) :=
    (hx.pair (pfst (pfst z))).comp polyFun_tidyGens
  have hnorm : PolyFun (fun q : Z => normPerm (q.2.1.2.2.2.2.1, q.1.2)) :=
    (hx.pair (psnd (pfst z))).comp polyFun_normPerm
  have ht1 : PolyFun (fun q : Z => decide (q.2.2.2.1 < q.2.1.2.2.2.1.length)) :=
    (hw.add (polyFun_const 1)).le (hwins.comp polyFun_length)
  have ht2 : PolyFun (fun q : Z => rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
      q.2.1.2.2.2.1.getD q.2.2.2.1 [])) := (htidy.pair hwin).comp polyFun_rawIsInvariant
  have hsome : PolyFun (fun q : Z => (some (q.2.1.2.2.2.1.getD q.2.2.2.1 [],
      tidyGens (q.2.1.2.2.2.2.1, q.1.1), normPerm (q.2.1.2.2.2.2.1, q.1.2),
      q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)) :=
    (hwin.pair (htidy.pair (hnorm.pair (hx.pair hy)))).comp polyFun_some
  have hbody : PolyFun (fun q : Z =>
      if q.2.2.2.1 < q.2.1.2.2.2.1.length ∧
          rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1), q.2.1.2.2.2.1.getD q.2.2.2.1 []) = true
      then (some (q.2.1.2.2.2.1.getD q.2.2.2.1 [], tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        normPerm (q.2.1.2.2.2.2.1, q.1.2), q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)
      else none) := by
    refine (PolyFun.ite (pand ht1 ht2) hsome (polyFun_const none)).of_eq (fun q => ?_)
    by_cases h1 : q.2.2.2.1 < q.2.1.2.2.2.1.length
    · by_cases h2 : rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        q.2.1.2.2.2.1.getD q.2.2.2.1 []) = true <;> simp [h1, h2]
    · simp [h1]
  have i : PolyFun (fun p : AVHdr × AVState => p) := polyFun_id
  refine (((pfst (psnd (psnd (psnd i)))).pair i).comp
    (PolyFun.optionElim (polyFun_const none) hbody)).of_eq (fun p => ?_)
  unfold avChild
  cases p.2.2.2.1 <;> rfl

theorem polyFun_avCombine : PolyFun avCombine := by
  let Z := AVHdr × AVState × RawCoset
  have i : PolyFun (fun p : Z => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (pfst (psnd i))
  have hw := pfst (psnd (pfst (psnd i)))
  have hacc := psnd (psnd (psnd (pfst (psnd i))))
  have ha := psnd (psnd i)
  have hwins := pfst (psnd (psnd (psnd hh)))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hskip : PolyFun (fun p : Z => avPos (p.1, p.2.1.1 + 1, p.2.1.2.2.2)) :=
    (hh.pair ((hv.add (polyFun_const 1)).pair hacc)).comp polyFun_avPos
  have hjoin : PolyFun (fun p : Z =>
      avPos (p.1, p.2.1.1 + 1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2.2, p.2.2))) :=
    (hh.pair ((hv.add (polyFun_const 1)).pair
      ((hx.pair (hacc.pair ha)).comp polyFun_rawCosetJoin))).comp polyFun_avPos
  have hnext : PolyFun (fun p : Z =>
      ((min p.2.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2.2)) : AVState)) := by
    have hL := (pfst (psnd (psnd hh))).comp polyFun_length
    have hmin : PolyFun (fun p : Z => min p.2.1.1 p.1.2.2.1.length) :=
      (PolyFun.ite (hv.le hL) hv hL).of_eq (fun p => by
        by_cases hc : p.2.1.1 ≤ p.1.2.2.1.length
        · simp [hc]
        · simp [hc, Nat.min_eq_right (Nat.le_of_not_le hc)])
    exact hmin.pair ((hw.add (polyFun_const 1)).pair
      (((hx.pair ha).comp polyFun_rawCosetNorm).pair ((hx.pair hacc).comp polyFun_rawCosetNorm)))
  have hlt : PolyFun (fun p : Z => decide (p.2.1.2.1 + 1 < p.1.2.2.2.1.length)) :=
    ((hw.add (polyFun_const 1)).add (polyFun_const 1)).le (hwins.comp polyFun_length)
  have hsome : PolyFun (fun r : (RawGens × RawPerm) × Z =>
      if r.2.2.1.2.1 + 1 < r.2.1.2.2.2.1.length then
        ((min r.2.2.1.1 r.2.1.2.2.1.length, r.2.2.1.2.1 + 1, rawCosetNorm (r.2.1.2.2.2.2.1, r.2.2.2),
          rawCosetNorm (r.2.1.2.2.2.2.1, r.2.2.1.2.2.2)) : AVState)
      else avPos (r.2.1, r.2.2.1.1 + 1, rawCosetJoin (r.2.1.2.2.2.2.1, r.2.2.1.2.2.2, r.2.2.2))) :=
    ((psnd polyFun_id).comp (PolyFun.ite hlt hnext hjoin)).of_eq (fun _ => by simp)
  refine ((ha.pair i).comp (PolyFun.optionElim hskip hsome)).of_eq (fun p => ?_)
  obtain ⟨h, st, a⟩ := p
  unfold avCombine
  cases a <;> rfl

end Algo
