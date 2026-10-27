/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): lines 7–11 of Procedure
Align (Sec. 14.1, repaired in the corrected paper), bounded at an external degree. Not part of the
faithful formalization.
-/
import Workspace.Explicit.S9Line4c
import Workspace.Explicit.NodeMap
import Workspace.Algo.AlignDescentCost
import Workspace.Algo.AlignDomReps
import Workspace.Algo.AggNodeLine57RAM

/-!
# Lines 7–11 of Procedure Align, bounded at the degree

The steps of stretch 3 (`Algo.l57Calls`, `Algo.l57Init`, `Algo.l57Child`, `Algo.l57Step`)
are polynomial except for the list of cosets of `ker ϕ*` (`Algo.adRightReps`). That list walks
a fuel of `m*^{m*}` entries, built by the guarded tuple table (`Algo.aggTable 2`), whose guard
keeps `m* ≤ (log₂ n + 1)^2`. So every step is bounded at exponent `3`, at any degree `n` that
bounds the number of points of the header's action (`Explicit.AVHdrOK`). The state of the
loop is only read by polynomial routines, so it needs no precondition.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp
    polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

namespace TN

variable {α β : Type*} [Enc α] [Enc β]

/-- **The conditional with a bounded test.** -/
theorem iteT {p : α → Bool} {f g : α → β} {Pre : ℕ → α → Prop} {k : ℕ}
    (hp : TN p Pre k) (hf : TN f Pre k) (hg : TN g Pre k) :
    TN (fun a => if p a then f a else g a) Pre k :=
  ((hp.pair (id' Pre k)).comp (ite (Pre := fun n (q : Bool × α) => Pre n q.2) polyFun_fst
    (poly_comp polyFun_snd hf) (poly_comp polyFun_snd hg) (fun _ _ h _ => h)
    (fun _ _ h _ => h)) (fun _ _ h => h)).of_eq (fun _ => rfl)

end TN

/-- The header of lines 7–11 at degree `n`: its action has at most `n` points. -/
def AVHdrOK (n : ℕ) (h : AVHdr) : Prop := h.1.1.1.length ≤ n

theorem log_two_le_self (m : ℕ) : Nat.log 2 m ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact (Nat.log_lt_self 2 hm.ne').le

theorem guardBound_two_le {m n : ℕ} (h : m ≤ n) : guardBound 2 m ≤ 2 ^ 0 * (n + 1) ^ 2 := by
  unfold guardBound
  rw [pow_zero, one_mul]
  exact Nat.pow_le_pow_left (by have := log_two_le_self m; omega) 2

namespace TN

/-- **The fuel of the search for the cosets of `ker ϕ*`** (Sec. 14.1, lines 9–11): the guarded
tuple table of the `m*` letters, at exponent `3`. -/
theorem adFuel : TN Algo.adFuel (fun n p => p.1.1.1.length ≤ n) 3 := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have hin : PolyFun (fun p : RawAction × RawAlignOutcome =>
      (adFuelDom p, p.1.1.1, adFuelDom p)) :=
    polyFun_adFuelDom.pair ((pfst (pfst (pfst i))).pair polyFun_adFuelDom)
  have hmap : PolyFun (fun l : List (List ℕ × ℕ) => l.map (fun _ => (0 : ℕ))) :=
    PolyFun.map (polyFun_const 0)
  have ht : TN (Algo.aggTable 2)
      (fun n (a : RawAggTestInput) => a.2.1.length ≤ n ∧ a.1 = a.2.2) 3 :=
    (TN.aggTable 2).scale 0 2 (fun n a ha => ⟨(n + 1) ^ 2, by rw [pow_zero, one_mul],
      (ha.1.trans (by nlinarith)), fun hg => by
        rw [← ha.2]; exact hg.trans (by simpa using guardBound_two_le ha.1)⟩)
  exact ((poly_comp hin ht).comp_poly (polyFun_snd.comp hmap)).restrict
    (fun n p hp => ⟨hp, rfl⟩) |>.of_eq (fun _ => rfl)

theorem adRightReps : TN Algo.adRightReps (fun n p => p.1.1.1.length ≤ n) 3 := by
  have i : PolyFun (fun p : RawAction × RawAlignOutcome => p) := polyFun_id
  have h1 : PolyFun (fun p : RawAction × RawAlignOutcome => (p.1.1.1, alignPairG1 p)) :=
    (pfst (pfst (pfst i))).pair polyFun_alignPairG1
  exact (((ofPoly h1 _ _).pair ((ofPoly polyFun_alignKerGens _ _).pair adFuel)).comp_poly
    polyFun_rawCosetReps).of_eq (fun _ => rfl)

theorem adReps : TN Algo.adReps (fun n z => z.1.1.1.1.length ≤ n) 3 := by
  have hf : PolyFun (fun z : RawPerm × RawPerm => rawMul (z.1, rawInv z.2)) :=
    (polyFun_fst.pair (polyFun_snd.comp polyFun_rawInv)).comp polyFun_rawMul
  exact (((ofPoly polyFun_snd _ _).pair (poly_comp polyFun_fst adRightReps)).comp_poly
    (PolyFun.mapParam (α := RawPerm) (β := RawPerm) (γ := RawPerm)
      (f := fun z : RawPerm × RawPerm => rawMul (z.1, rawInv z.2)) hf)).of_eq (fun _ => rfl)

theorem adRN : TN Algo.adRN AVHdrOK 3 :=
  ((poly_comp ((pfst polyFun_id).pair (pfst (psnd polyFun_id))) adRightReps).comp_poly
    polyFun_length).of_eq (fun _ => rfl)

section Steps

attribute [local irreducible] Algo.adRN Algo.adReps adCanon

private theorem ite' {α β : Type*} [Enc α] [Enc β] {p : α → Bool} {f g : α → β}
    {Pre : ℕ → α → Prop} {k : ℕ} (hp : PolyFun p) (hf : TN f Pre k) (hg : TN g Pre k) :
    TN (fun a => if p a then f a else g a) Pre k :=
  TN.ite hp hf hg (fun _ _ h _ => h) (fun _ _ h _ => h)

theorem adBegin : TN Algo.adBegin (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ => p) := polyFun_id
  have hh := pfst i
  have hreps : TN (fun p : AVHdr × ℕ × ℕ =>
      Algo.adReps ((p.1.1, p.1.2.1), adCanon (p.1, p.2.1))) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (((pfst hh).pair (pfst (psnd hh))).pair
      ((hh.pair (pfst (psnd i))).comp polyFun_adCanon)) adReps
  have hget := ((hreps.pair (ofPoly (psnd (psnd i)) _ _)).pair
    (const' ([] : RawPerm) _ _)).comp_poly polyFun_getD
  exact (((ofPoly (hh.comp polyFun_adKG) _ _).pair hget).comp_poly polyFun_some).of_eq
    (fun _ => rfl)

theorem adPos : TN Algo.adPos (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ × RawCoset => p) := polyFun_id
  have hh := pfst i
  have hn : PolyFun (fun p : AVHdr × ℕ × RawCoset => avNext (p.1, p.2.1)) :=
    (hh.pair (pfst (psnd i))).comp polyFun_avNext
  have hL := (pfst (psnd (psnd hh))).comp polyFun_length
  have hnorm : PolyFun (fun p : AVHdr × ℕ × RawCoset => rawCosetNorm (p.1.2.2.2.2.1, p.2.2)) :=
    ((pfst (psnd (psnd (psnd (psnd hh))))).pair (psnd (psnd i))).comp polyFun_rawCosetNorm
  have hc1 : PolyFun (fun p : AVHdr × ℕ × RawCoset => decide (avNext (p.1, p.2.1) <
      p.1.2.2.1.length)) := (hn.pair hL).comp plt
  have hc2 : PolyFun (fun p : AVHdr × ℕ × RawCoset => (adKO p.1).isEmpty) :=
    (hh.comp polyFun_adKO).comp polyFun_isEmpty
  have hRN : TN (fun p : AVHdr × ℕ × RawCoset => Algo.adRN p.1)
      (fun n p => AVHdrOK n p.1) 3 := poly_comp hh adRN
  have hA : TN (fun p : AVHdr × ℕ × RawCoset =>
      (((avNext (p.1, p.2.1), 0, avTr (p.1, avNext (p.1, p.2.1)),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (Algo.adRN p.1, none)) : ADState))
      (fun n p => AVHdrOK n p.1) 3 :=
    (ofPoly (hn.pair ((polyFun_const 0).pair (((hh.pair hn).comp polyFun_avTr).pair hnorm)))
      _ _).pair (hRN.pair (const' none _ _))
  have hB : TN (fun p : AVHdr × ℕ × RawCoset =>
      (((avNext (p.1, p.2.1), 0, Algo.adBegin (p.1, avNext (p.1, p.2.1), 0),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none)) : ADState))
      (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly hn _ _).pair ((const' 0 _ _).pair
      ((poly_comp (hh.pair (hn.pair (polyFun_const 0))) adBegin).pair
        (ofPoly hnorm _ _)))).pair (const' (0, none) _ _)
  have hC : TN (fun p : AVHdr × ℕ × RawCoset =>
      (((p.1.2.2.1.length, 0, none, rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none)) : ADState))
      (fun n p => AVHdrOK n p.1) 3 :=
    ofPoly ((hL.pair ((polyFun_const 0).pair ((polyFun_const none).pair hnorm))).pair
      (polyFun_const (0, none))) _ _
  refine (ite' hc1 (ite' hc2 hA hB) hC).of_eq (fun p => ?_)
  unfold Algo.adPos
  by_cases h1 : avNext (p.1, p.2.1) < p.1.2.2.1.length
  · by_cases h2 : (adKO p.1).isEmpty = true
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem adInit : TN Algo.adInit AVHdrOK 3 :=
  (poly_comp (polyFun_id.pair ((polyFun_const 0).pair (polyFun_const none))) adPos).of_eq
    (fun _ => rfl)

theorem adAfter : TN Algo.adAfter (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ × RawCoset × RawCoset => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (psnd i)
  have hr := pfst (psnd (psnd i))
  have ha := psnd (psnd (psnd i))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hjoin : TN (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      Algo.adPos (p.1, p.2.1 + 1, rawCosetJoin (p.1.2.2.2.2.1, p.2.2.2, p.2.2.1)))
      (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair ((hv.add (polyFun_const 1)).pair
      ((hx.pair (ha.pair hr)).comp polyFun_rawCosetJoin))) adPos
  have hnone : TN (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      Algo.adPos (p.1, p.2.1 + 1, p.2.2.2)) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair ((hv.add (polyFun_const 1)).pair ha)) adPos
  have hsome : TN (fun r : (RawGens × RawPerm) × (AVHdr × ℕ × RawCoset × RawCoset) =>
      (((r.2.2.1, 0, rawCosetNorm (r.2.1.2.2.2.2.1, r.2.2.2.1), r.2.2.2.2),
        (Algo.adRN r.2.1, none)) : ADState)) (fun n r => AVHdrOK n r.2.1) 3 := by
    have j : PolyFun (fun r : (RawGens × RawPerm) × (AVHdr × ℕ × RawCoset × RawCoset) => r) :=
      polyFun_id
    have hh' := pfst (psnd j)
    exact (ofPoly ((pfst (psnd (psnd j))).pair ((polyFun_const 0).pair
      ((((pfst (psnd (psnd (psnd (psnd hh'))))).pair (pfst (psnd (psnd (psnd j))))).comp
        polyFun_rawCosetNorm).pair (psnd (psnd (psnd (psnd j))))))) _ _).pair
      ((poly_comp hh' adRN).pair (const' none _ _))
  have helim : TN (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      p.2.2.1.elim (Algo.adPos (p.1, p.2.1 + 1, p.2.2.2))
        (fun _ => ((p.2.1, 0, rawCosetNorm (p.1.2.2.2.2.1, p.2.2.1), p.2.2.2),
          (Algo.adRN p.1, none)))) (fun n p => AVHdrOK n p.1) 3 := by
    refine ((ofPoly (hr.pair i) _ _).comp (optionElim
      (Pre := fun n (q : Option (RawGens × RawPerm) × (AVHdr × ℕ × RawCoset × RawCoset)) =>
        AVHdrOK n q.2.1) hnone hsome (fun _ _ h => h) (fun _ _ _ h => h))
      (fun _ _ h => h)).of_eq (fun p => ?_)
    obtain ⟨h, v, r, a⟩ := p
    cases r <;> rfl
  refine (ite' ((hh.comp polyFun_adTW).comp polyFun_isEmpty) hjoin helim).of_eq
    (fun p => ?_)
  unfold Algo.adAfter
  by_cases h1 : (adTW p.1).isEmpty = true <;> simp [h1]

theorem adOpen : TN Algo.adOpen (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (psnd i)
  have hr := pfst (psnd (psnd i))
  have hra := pfst (psnd (psnd (psnd i)))
  have ha := psnd (psnd (psnd (psnd i)))
  have hc : TN (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      decide (p.2.2.1 < Algo.adRN p.1)) (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly hr _ _).pair (poly_comp hh adRN)).comp_poly plt
  have hA : TN (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      (((p.2.1, 0, Algo.adBegin (p.1, p.2.1, p.2.2.1), p.2.2.2.2), (p.2.2.1, p.2.2.2.1)) :
        ADState)) (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly hv _ _).pair ((const' 0 _ _).pair
      ((poly_comp (hh.pair (hv.pair hr)) adBegin).pair (ofPoly ha _ _)))).pair
      (ofPoly (hr.pair hra) _ _)
  have hB : TN (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      Algo.adAfter (p.1, p.2.1, p.2.2.2.1, p.2.2.2.2)) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair (hv.pair (hra.pair ha))) adAfter
  refine (iteT hc hA hB).of_eq (fun p => ?_)
  unfold Algo.adOpen
  by_cases h1 : p.2.2.1 < Algo.adRN p.1 <;> simp [h1]

theorem adSegLen : TN Algo.adSegLen (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ => p) := polyFun_id
  have hc : TN (fun p : AVHdr × ℕ => decide (p.2 < Algo.adRN p.1))
      (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly (psnd i) _ _).pair (poly_comp (pfst i) adRN)).comp_poly plt
  refine (iteT hc (ofPoly (((pfst i).comp polyFun_adKO).comp polyFun_length) _ _)
    (ofPoly (((pfst i).comp polyFun_adTW).comp polyFun_length) _ _)).of_eq (fun p => ?_)
  unfold Algo.adSegLen
  by_cases h1 : p.2 < Algo.adRN p.1 <;> simp [h1]

theorem adSegWin : TN Algo.adSegWin (fun n p => AVHdrOK n p.1) 3 := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ => p) := polyFun_id
  have hc : TN (fun p : AVHdr × ℕ × ℕ => decide (p.2.1 < Algo.adRN p.1))
      (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly (pfst (psnd i)) _ _).pair (poly_comp (pfst i) adRN)).comp_poly plt
  have hA : PolyFun (fun p : AVHdr × ℕ × ℕ => (adKO p.1).getD p.2.2 []) :=
    ((((pfst i).comp polyFun_adKO).pair (psnd (psnd i))).pair (polyFun_const [])).comp
      polyFun_getD
  have hB : PolyFun (fun p : AVHdr × ℕ × ℕ => (adTW p.1).getD p.2.2 []) :=
    ((((pfst i).comp polyFun_adTW).pair (psnd (psnd i))).pair (polyFun_const [])).comp
      polyFun_getD
  refine (iteT hc (ofPoly hA _ _) (ofPoly hB _ _)).of_eq (fun p => ?_)
  unfold Algo.adSegWin
  by_cases h1 : p.2.1 < Algo.adRN p.1 <;> simp [h1]

attribute [local irreducible] Algo.adSegLen Algo.adSegWin Algo.adBegin adKO adTW adKG Algo.adOpen
  Algo.adPos Algo.adAfter

theorem adChild : TN Algo.adChild (fun n p => AVHdrOK n p.1) 3 := by
  let Z := (RawGens × RawPerm) × (AVHdr × ADState)
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hh := pfst (psnd z)
  have hw := pfst (psnd (pfst (psnd (psnd z))))
  have hr := pfst (psnd (psnd (psnd z)))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hy := psnd (psnd (psnd (psnd (psnd hh))))
  have hwin : TN (fun q : Z => Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1))
      (fun n q => AVHdrOK n q.2.1) 3 :=
    poly_comp (hh.pair (hr.pair hw)) adSegWin
  have hlen : TN (fun q : Z => Algo.adSegLen (q.2.1, q.2.2.2.1))
      (fun n q => AVHdrOK n q.2.1) 3 :=
    poly_comp (hh.pair hr) adSegLen
  have htidy : PolyFun (fun q : Z => tidyGens (q.2.1.2.2.2.2.1, q.1.1)) :=
    (hx.pair (pfst (pfst z))).comp polyFun_tidyGens
  have hnorm : PolyFun (fun q : Z => normPerm (q.2.1.2.2.2.2.1, q.1.2)) :=
    (hx.pair (psnd (pfst z))).comp polyFun_normPerm
  have ht1 : TN (fun q : Z => decide (q.2.2.1.2.1 < Algo.adSegLen (q.2.1, q.2.2.2.1)))
      (fun n q => AVHdrOK n q.2.1) 3 :=
    ((ofPoly hw _ _).pair hlen).comp_poly plt
  have ht2 : TN (fun q : Z => rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
      Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1))) (fun n q => AVHdrOK n q.2.1) 3 :=
    ((ofPoly htidy _ _).pair hwin).comp_poly polyFun_rawIsInvariant
  have hand : TN (fun q : Z => decide (q.2.2.1.2.1 < Algo.adSegLen (q.2.1, q.2.2.2.1)) &&
      rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1))) (fun n q => AVHdrOK n q.2.1) 3 := by
    refine (iteT ht1 ht2 (const' false _ _)).of_eq (fun q => ?_)
    by_cases h1 : q.2.2.1.2.1 < Algo.adSegLen (q.2.1, q.2.2.2.1) <;> simp [h1]
  have hsome : TN (fun q : Z => (some (Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1),
      tidyGens (q.2.1.2.2.2.2.1, q.1.1), normPerm (q.2.1.2.2.2.2.1, q.1.2),
      q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)) (fun n q => AVHdrOK n q.2.1) 3 :=
    (hwin.pair ((ofPoly htidy _ _).pair ((ofPoly hnorm _ _).pair
      (ofPoly (hx.pair hy) _ _)))).comp_poly polyFun_some
  have hbody : TN (fun q : Z =>
      if q.2.2.1.2.1 < Algo.adSegLen (q.2.1, q.2.2.2.1) ∧
          rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
            Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1)) = true
      then (some (Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1),
        tidyGens (q.2.1.2.2.2.2.1, q.1.1), normPerm (q.2.1.2.2.2.2.1, q.1.2),
        q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)
      else none) (fun n q => AVHdrOK n q.2.1) 3 := by
    refine (iteT hand hsome (const' none _ _)).of_eq (fun q => ?_)
    by_cases h1 : q.2.2.1.2.1 < Algo.adSegLen (q.2.1, q.2.2.2.1)
    · by_cases h2 : rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        Algo.adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1)) = true <;> simp [h1, h2]
    · simp [h1]
  have i : PolyFun (fun p : AVHdr × ADState => p) := polyFun_id
  refine ((ofPoly ((pfst (psnd (psnd (pfst (psnd i))))).pair i) _ _).comp
    (optionElim (Pre := fun n (q : Option (RawGens × RawPerm) × (AVHdr × ADState)) =>
      AVHdrOK n q.2.1) (const' none _ _) hbody (fun _ _ _ => trivial) (fun _ _ _ h => h))
    (fun _ _ h => h)).of_eq (fun p => ?_)
  unfold Algo.adChild
  cases p.2.1.2.2.1 <;> rfl

set_option maxHeartbeats 8000000 in
theorem adCombine : TN Algo.adCombine (fun n p => AVHdrOK n p.1) 3 := by
  let Z := AVHdr × ADState × RawCoset
  have i : PolyFun (fun p : Z => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (pfst (pfst (psnd i)))
  have hw := pfst (psnd (pfst (pfst (psnd i))))
  have hacc := psnd (psnd (psnd (pfst (pfst (psnd i)))))
  have hr := pfst (psnd (pfst (psnd i)))
  have hra := psnd (psnd (pfst (psnd i)))
  have ha := psnd (psnd i)
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hL := (pfst (psnd (psnd hh))).comp polyFun_length
  have hmin : PolyFun (fun p : Z => min p.2.1.1.1 p.1.2.2.1.length) :=
    (hv.pair hL).comp polyFun_min
  have hRN : TN (fun p : Z => Algo.adRN p.1) (fun n p => AVHdrOK n p.1) 3 := poly_comp hh adRN
  have hrlt : TN (fun p : Z => decide (p.2.1.2.1 < Algo.adRN p.1))
      (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly hr _ _).pair hRN).comp_poly plt
  have hnormA : PolyFun (fun p : Z => rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)) :=
    (hx.pair hacc).comp polyFun_rawCosetNorm
  have hnormR : PolyFun (fun p : Z => rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2)) :=
    (hx.pair hra).comp polyFun_rawCosetNorm
  have hopen0 : TN (fun p : Z => Algo.adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length,
      p.2.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2),
      rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair (hmin.pair ((hr.add (polyFun_const 1)).pair (hnormR.pair hnormA))))
      adOpen
  have hpos0 : TN (fun p : Z => Algo.adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
      p.2.1.1.2.2.2)) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair ((hmin.add (polyFun_const 1)).pair hacc)) adPos
  have hnone : TN (fun p : Z =>
      if p.2.1.2.1 < Algo.adRN p.1 then
        Algo.adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
      else Algo.adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1, p.2.1.1.2.2.2))
      (fun n p => AVHdrOK n p.1) 3 := by
    refine (iteT hrlt hopen0 hpos0).of_eq (fun p => ?_)
    by_cases h1 : p.2.1.2.1 < Algo.adRN p.1 <;> simp [h1]
  have hseg : TN (fun p : Z => decide (p.2.1.1.2.1 + 1 < Algo.adSegLen (p.1, p.2.1.2.1)))
      (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly (hw.add (polyFun_const 1)) _ _).pair (poly_comp (hh.pair hr) adSegLen)).comp_poly
      plt
  have hminr : TN (fun p : Z => min p.2.1.2.1 (Algo.adRN p.1)) (fun n p => AVHdrOK n p.1) 3 :=
    ((ofPoly hr _ _).pair hRN).comp_poly polyFun_min
  have hcont : TN (fun p : Z =>
      (((min p.2.1.1.1 p.1.2.2.1.length, p.2.1.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)),
        (min p.2.1.2.1 (Algo.adRN p.1), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2))) : ADState))
      (fun n p => AVHdrOK n p.1) 3 :=
    (ofPoly (hmin.pair ((hw.add (polyFun_const 1)).pair
      (((hx.pair ha).comp polyFun_rawCosetNorm).pair hnormA))) _ _).pair
      (hminr.pair (ofPoly hnormR _ _))
  have hopen1 : TN (fun p : Z => Algo.adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length,
      p.2.1.2.1 + 1,
      rawCosetNorm (p.1.2.2.2.2.1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2, p.2.2)),
      rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair (hmin.pair ((hr.add (polyFun_const 1)).pair
      (((hx.pair ((hx.pair (hra.pair ha)).comp polyFun_rawCosetJoin)).comp
        polyFun_rawCosetNorm).pair hnormA)))) adOpen
  have hpos1 : TN (fun p : Z => Algo.adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
      rawCosetJoin (p.1.2.2.2.2.1, p.2.1.1.2.2.2, p.2.2))) (fun n p => AVHdrOK n p.1) 3 :=
    poly_comp (hh.pair ((hmin.add (polyFun_const 1)).pair
      ((hx.pair (hacc.pair ha)).comp polyFun_rawCosetJoin))) adPos
  have hsomeZ : TN (fun p : Z =>
      if p.2.1.1.2.1 + 1 < Algo.adSegLen (p.1, p.2.1.2.1) then
        (((min p.2.1.1.1 p.1.2.2.1.length, p.2.1.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)),
          (min p.2.1.2.1 (Algo.adRN p.1), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2))) : ADState)
      else if p.2.1.2.1 < Algo.adRN p.1 then
        Algo.adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
          rawCosetNorm (p.1.2.2.2.2.1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2, p.2.2)),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
      else Algo.adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
        rawCosetJoin (p.1.2.2.2.2.1, p.2.1.1.2.2.2, p.2.2))) (fun n p => AVHdrOK n p.1) 3 := by
    have hin := iteT hrlt hopen1 hpos1
    refine (iteT hseg hcont hin).of_eq (fun p => ?_)
    by_cases h1 : p.2.1.1.2.1 + 1 < Algo.adSegLen (p.1, p.2.1.2.1)
    · simp [h1]
    · by_cases h2 : p.2.1.2.1 < Algo.adRN p.1 <;> simp [h1, h2]
  refine ((ofPoly (ha.pair i) (fun n (p : Z) => AVHdrOK n p.1) 3).comp (optionElim
    (Pre := fun n (q : RawCoset × Z) => AVHdrOK n q.2.1) hnone
    (poly_comp polyFun_snd hsomeZ) (fun _ _ h => h) (fun _ _ _ h => h))
    (fun _ _ h => h)).of_eq (fun p => ?_)
  obtain ⟨h, st, a⟩ := p
  unfold Algo.adCombine
  cases a <;> rfl

end Steps

/-! ## Stretch 3 -/

theorem adCalls : TN Algo.adCalls AVHdrOK 3 := by
  have i : PolyFun (fun h : AVHdr => h) := polyFun_id
  exact (((ofPoly ((pfst (psnd (psnd i))).comp polyFun_length) _ _).pair
    (((adRN.pair (ofPoly ((i.comp polyFun_adKO).comp polyFun_length) _ _)).comp_poly
      polyFun_mul |>.pair (ofPoly ((i.comp polyFun_adTW).comp polyFun_length) _ _)).comp_poly
        polyFun_add)).comp_poly polyFun_mul).of_eq (fun h => rfl)

theorem l57Calls : TN Algo.l57Calls AVHdrOK 3 :=
  (TN.ite polyFun_l57Small adCalls (ofPoly polyFun_avCalls _ _) (fun _ _ h _ => h)
    (fun _ _ h _ => h)).of_eq (fun h => by unfold Algo.l57Calls; cases l57Small h <;> rfl)

theorem l57Init : TN Algo.l57Init AVHdrOK 3 :=
  (TN.ite polyFun_l57Small adInit
    (ofPoly (polyFun_avInit.pair (polyFun_const ((0, none) : ℕ × RawCoset))) _ _)
    (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq
    (fun h => by unfold Algo.l57Init; cases l57Small h <;> rfl)

theorem l57Child : TN Algo.l57Child (fun n p => AVHdrOK n p.1) 3 :=
  (TN.ite ((pfst polyFun_id).comp polyFun_l57Small) adChild
    (ofPoly (((pfst polyFun_id).pair (pfst (psnd polyFun_id))).comp polyFun_avChild) _ _)
    (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq (fun p => by unfold Algo.l57Child; rfl)

theorem l57Step : TN Algo.l57Step (fun n p => AVHdrOK n p.1) 3 :=
  (TN.ite ((pfst polyFun_id).comp polyFun_l57Small) adCombine
    (ofPoly ((((pfst polyFun_id).pair ((pfst (pfst (psnd polyFun_id))).pair
      (psnd (psnd polyFun_id)))).comp polyFun_avCombine).pair
        (polyFun_const ((0, none) : ℕ × RawCoset))) _ _)
    (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq (fun p => by unfold Algo.l57Step; rfl)

end TN

end Explicit
