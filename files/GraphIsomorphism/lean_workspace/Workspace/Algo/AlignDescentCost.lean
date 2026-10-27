/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the step functions of the loop of case 1 of the repair of §14.1,
lines 7–11, run in quasipolynomial time, keep the state small, and make at
most `Algo.adCalls` calls.
-/
import Workspace.Algo.AlignDescentMatch
import Workspace.Algo.AlignVersionsCost
import Workspace.Algo.AggNodeCheckedLocal

/-!
# The cost of the loop of case 1

* the step functions `Algo.adChild`, `Algo.adCombine` and `Algo.adInit` are `RAM.QuasiFun`;
  only the list of cosets of `ker ϕ*` (`Algo.adReps`, which walks the `m*^{m*}` letters of its
  fuel) is not polynomial;
* `Algo.adRem` bounds the calls the loop still makes: it is at most `Algo.adCalls` at the
  start and drops at every call;
* every state the steps produce has its counters bounded by the header and its cosets either
  normalized (`Algo.rawCosetNorm`) or a start `Algo.adBegin` of a coset of `ker ϕ*`, whose
  size is bounded by a quasipolynomial function of the header (`Algo.adStep_size`).
-/

set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp
    polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

/-! ## The routines -/

theorem polyFun_adKO : PolyFun adKO :=
  ((pfst polyFun_id).pair (pfst (psnd polyFun_id))).comp polyFun_alignKerOrbits

theorem polyFun_adTW : PolyFun adTW :=
  (pfst (psnd (psnd (psnd (polyFun_id : PolyFun (fun h : AVHdr => h)))))).comp polyFun_tail

theorem polyFun_adKG : PolyFun adKG :=
  ((pfst polyFun_id).pair (pfst (psnd polyFun_id))).comp polyFun_alignKerGens

theorem quasiFun_adRN : QuasiFun adRN :=
  (((pfst polyFun_id).pair (pfst (psnd polyFun_id))).comp_quasiFun quasiFun_adRightReps).comp_poly
    polyFun_length

theorem polyFun_adCanon : PolyFun adCanon := by
  have i : PolyFun (fun p : AVHdr × ℕ => p) := polyFun_id
  have hc : PolyFun (fun r : (RawGens × RawPerm) × (AVHdr × ℕ) =>
      aggnCanonCoset ((r.2.1.2.2.2.2.1, r.1.1), r.1.2)) :=
    (((pfst (psnd (psnd (psnd (psnd (pfst (psnd polyFun_id))))))).pair
      (pfst (pfst polyFun_id))).pair (psnd (pfst polyFun_id))).comp aggnPolyFun_canonCoset
  refine ((polyFun_avTr.pair i).comp (PolyFun.optionElim (polyFun_const []) hc)).of_eq
    (fun p => ?_)
  unfold adCanon
  cases avTr p <;> rfl

theorem quasiFun_adBegin : QuasiFun adBegin := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ => p) := polyFun_id
  have hh := pfst i
  have hreps : QuasiFun (fun p : AVHdr × ℕ × ℕ =>
      adReps ((p.1.1, p.1.2.1), adCanon (p.1, p.2.1))) :=
    (((pfst hh).pair (pfst (psnd hh))).pair ((hh.pair (pfst (psnd i))).comp polyFun_adCanon)).comp_quasiFun
      quasiFun_adReps
  have hget : QuasiFun (fun p : AVHdr × ℕ × ℕ =>
      (adReps ((p.1.1, p.1.2.1), adCanon (p.1, p.2.1))).getD p.2.2 []) :=
    ((hreps.pair (psnd (psnd i)).quasiFun).pair (quasiFun_const [])).comp_poly polyFun_getD
  exact ((hh.comp polyFun_adKG).quasiFun.pair hget).comp_poly polyFun_some

theorem quasiFun_adPos : QuasiFun adPos := by
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
  have hA : QuasiFun (fun p : AVHdr × ℕ × RawCoset =>
      (((avNext (p.1, p.2.1), 0, avTr (p.1, avNext (p.1, p.2.1)),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (adRN p.1, none)) : ADState)) :=
    (hn.pair ((polyFun_const 0).pair (((hh.pair hn).comp polyFun_avTr).pair hnorm))).quasiFun.pair
      ((hh.comp_quasiFun quasiFun_adRN).pair (quasiFun_const none))
  have hB : QuasiFun (fun p : AVHdr × ℕ × RawCoset =>
      (((avNext (p.1, p.2.1), 0, adBegin (p.1, avNext (p.1, p.2.1), 0),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none)) : ADState)) :=
    (hn.quasiFun.pair ((quasiFun_const 0).pair
      (((hh.pair (hn.pair (polyFun_const 0))).comp_quasiFun quasiFun_adBegin).pair
        hnorm.quasiFun))).pair (quasiFun_const (0, none))
  have hC : QuasiFun (fun p : AVHdr × ℕ × RawCoset =>
      (((p.1.2.2.1.length, 0, none, rawCosetNorm (p.1.2.2.2.2.1, p.2.2)), (0, none)) : ADState)) :=
    (hL.pair ((polyFun_const 0).pair ((polyFun_const none).pair hnorm))).quasiFun.pair
      (quasiFun_const (0, none))
  refine (QuasiFun.ite hc1 (QuasiFun.ite hc2 hA hB) hC).of_eq (fun p => ?_)
  unfold adPos
  by_cases h1 : avNext (p.1, p.2.1) < p.1.2.2.1.length
  · by_cases h2 : (adKO p.1).isEmpty = true
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem quasiFun_adInit : QuasiFun adInit :=
  (polyFun_id.pair ((polyFun_const 0).pair (polyFun_const none))).comp_quasiFun quasiFun_adPos

theorem quasiFun_adAfter : QuasiFun adAfter := by
  have i : PolyFun (fun p : AVHdr × ℕ × RawCoset × RawCoset => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (psnd i)
  have hr := pfst (psnd (psnd i))
  have ha := psnd (psnd (psnd i))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hjoin : QuasiFun (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      adPos (p.1, p.2.1 + 1, rawCosetJoin (p.1.2.2.2.2.1, p.2.2.2, p.2.2.1))) :=
    (hh.pair ((hv.add (polyFun_const 1)).pair
      ((hx.pair (ha.pair hr)).comp polyFun_rawCosetJoin))).comp_quasiFun quasiFun_adPos
  have hnone : QuasiFun (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      adPos (p.1, p.2.1 + 1, p.2.2.2)) :=
    (hh.pair ((hv.add (polyFun_const 1)).pair ha)).comp_quasiFun quasiFun_adPos
  have hsome : QuasiFun (fun r : (RawGens × RawPerm) × (AVHdr × ℕ × RawCoset × RawCoset) =>
      (((r.2.2.1, 0, rawCosetNorm (r.2.1.2.2.2.2.1, r.2.2.2.1), r.2.2.2.2),
        (adRN r.2.1, none)) : ADState)) := by
    have j : PolyFun (fun r : (RawGens × RawPerm) × (AVHdr × ℕ × RawCoset × RawCoset) => r) :=
      polyFun_id
    have hh' := pfst (psnd j)
    exact ((pfst (psnd (psnd j))).pair ((polyFun_const 0).pair
      ((((pfst (psnd (psnd (psnd (psnd hh'))))).pair (pfst (psnd (psnd (psnd j))))).comp
        polyFun_rawCosetNorm).pair (psnd (psnd (psnd (psnd j))))))).quasiFun.pair
      ((hh'.comp_quasiFun quasiFun_adRN).pair (quasiFun_const none))
  have helim : QuasiFun (fun p : AVHdr × ℕ × RawCoset × RawCoset =>
      p.2.2.1.elim (adPos (p.1, p.2.1 + 1, p.2.2.2))
        (fun _ => ((p.2.1, 0, rawCosetNorm (p.1.2.2.2.2.1, p.2.2.1), p.2.2.2),
          (adRN p.1, none)))) := by
    refine ((hr.pair i).quasiFun.comp (QuasiFun.optionElim hnone hsome)).of_eq (fun p => ?_)
    obtain ⟨h, v, r, a⟩ := p
    cases r <;> rfl
  refine (QuasiFun.ite ((hh.comp polyFun_adTW).comp polyFun_isEmpty) hjoin helim).of_eq
    (fun p => ?_)
  unfold adAfter
  by_cases h1 : (adTW p.1).isEmpty = true <;> simp [h1]

theorem quasiFun_adOpen : QuasiFun adOpen := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset => p) := polyFun_id
  have hh := pfst i
  have hv := pfst (psnd i)
  have hr := pfst (psnd (psnd i))
  have hra := pfst (psnd (psnd (psnd i)))
  have ha := psnd (psnd (psnd (psnd i)))
  have hc : QuasiFun (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      decide (p.2.2.1 < adRN p.1)) :=
    (hr.quasiFun.pair (hh.comp_quasiFun quasiFun_adRN)).comp_poly plt
  have hA : QuasiFun (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      (((p.2.1, 0, adBegin (p.1, p.2.1, p.2.2.1), p.2.2.2.2), (p.2.2.1, p.2.2.2.1)) : ADState)) :=
    (hv.quasiFun.pair ((quasiFun_const 0).pair
      (((hh.pair (hv.pair hr)).comp_quasiFun quasiFun_adBegin).pair ha.quasiFun))).pair
      (hr.pair hra).quasiFun
  have hB : QuasiFun (fun p : AVHdr × ℕ × ℕ × RawCoset × RawCoset =>
      adAfter (p.1, p.2.1, p.2.2.2.1, p.2.2.2.2)) :=
    (hh.pair (hv.pair (hra.pair ha))).comp_quasiFun quasiFun_adAfter
  refine (aggnQuasiFun_ite hc hA hB).of_eq (fun p => ?_)
  unfold adOpen
  by_cases h1 : p.2.2.1 < adRN p.1 <;> simp [h1]

theorem quasiFun_adSegLen : QuasiFun adSegLen := by
  have i : PolyFun (fun p : AVHdr × ℕ => p) := polyFun_id
  have hc : QuasiFun (fun p : AVHdr × ℕ => decide (p.2 < adRN p.1)) :=
    ((psnd i).quasiFun.pair ((pfst i).comp_quasiFun quasiFun_adRN)).comp_poly plt
  refine (aggnQuasiFun_ite hc (((pfst i).comp polyFun_adKO).comp polyFun_length).quasiFun
    (((pfst i).comp polyFun_adTW).comp polyFun_length).quasiFun).of_eq (fun p => ?_)
  unfold adSegLen
  by_cases h1 : p.2 < adRN p.1 <;> simp [h1]

theorem quasiFun_adSegWin : QuasiFun adSegWin := by
  have i : PolyFun (fun p : AVHdr × ℕ × ℕ => p) := polyFun_id
  have hc : QuasiFun (fun p : AVHdr × ℕ × ℕ => decide (p.2.1 < adRN p.1)) :=
    ((pfst (psnd i)).quasiFun.pair ((pfst i).comp_quasiFun quasiFun_adRN)).comp_poly plt
  have hA : PolyFun (fun p : AVHdr × ℕ × ℕ => (adKO p.1).getD p.2.2 []) :=
    ((((pfst i).comp polyFun_adKO).pair (psnd (psnd i))).pair (polyFun_const [])).comp
      polyFun_getD
  have hB : PolyFun (fun p : AVHdr × ℕ × ℕ => (adTW p.1).getD p.2.2 []) :=
    ((((pfst i).comp polyFun_adTW).pair (psnd (psnd i))).pair (polyFun_const [])).comp
      polyFun_getD
  refine (aggnQuasiFun_ite hc hA.quasiFun hB.quasiFun).of_eq (fun p => ?_)
  unfold adSegWin
  by_cases h1 : p.2.1 < adRN p.1 <;> simp [h1]


/-! ## The calls the loop still makes -/

/-- The calls of one version: one chain over the orbits of `N` per coset of `N`, and one
chain over the other classes. -/
def adPer (h : AVHdr) : ℕ := adRN h * (adKO h).length + (adTW h).length

/-- An upper bound on the calls the loop still makes from a state: the windows left in the
current chain, the chains of the cosets of `N` left in the current version, the chain over
the other classes, and all calls of every later version. -/
def adRem (p : AVHdr × ADState) : ℕ :=
  p.2.1.2.2.1.elim 0 fun _ =>
    if p.2.2.1 < adRN p.1 then
      ((adKO p.1).length - p.2.1.2.1) + (adRN p.1 - (p.2.2.1 + 1)) * (adKO p.1).length +
        (adTW p.1).length + (p.1.2.2.1.length - (p.2.1.1 + 1)) * adPer p.1
    else ((adTW p.1).length - p.2.1.2.1) + (p.1.2.2.1.length - (p.2.1.1 + 1)) * adPer p.1

section Rem

variable {h : AVHdr}

theorem adRem_none {v w r : ℕ} {acc racc : RawCoset} :
    adRem (h, ((v, w, none, acc), (r, racc))) = 0 := rfl

theorem adRem_some_lt {v w r : ℕ} {g : RawGens × RawPerm} {acc racc : RawCoset}
    (hr : r < adRN h) :
    adRem (h, ((v, w, some g, acc), (r, racc))) =
      ((adKO h).length - w) + (adRN h - (r + 1)) * (adKO h).length +
        (adTW h).length + (h.2.2.1.length - (v + 1)) * adPer h := by
  simp only [adRem, Option.elim, if_pos hr]

theorem adRem_some_ge {v w r : ℕ} {g : RawGens × RawPerm} {acc racc : RawCoset}
    (hr : ¬ r < adRN h) :
    adRem (h, ((v, w, some g, acc), (r, racc))) =
      ((adTW h).length - w) + (h.2.2.1.length - (v + 1)) * adPer h := by
  simp only [adRem, Option.elim, if_neg hr]

theorem adRem_adPos (k : ℕ) (acc : RawCoset) :
    adRem (h, adPos (h, k, acc)) ≤ (h.2.2.1.length - k) * adPer h := by
  have hge : avNext (h, k) < h.2.2.1.length → k ≤ avNext (h, k) := by
    intro hlt
    rcases avNext_spec h k with ⟨he, _⟩ | ⟨hle, _⟩
    · omega
    · exact hle
  have hpos := adRN_pos h
  have hTP : (adTW h).length ≤ adPer h := by unfold adPer; omega
  have hPer : adPer h = (adRN h - 1) * (adKO h).length + (adKO h).length + (adTW h).length := by
    unfold adPer
    obtain ⟨R, hR⟩ : ∃ R, adRN h = R + 1 := ⟨adRN h - 1, by omega⟩
    rw [hR, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  unfold adPos
  dsimp only
  split_ifs with h1 h2
  · have hk := hge h1
    rcases avTr (h, avNext (h, k)) with _ | g
    · exact Nat.zero_le _
    · rw [adRem_some_ge (lt_irrefl _)]
      generalize avNext (h, k) = k' at h1 hk
      have : h.2.2.1.length - k = (h.2.2.1.length - (k' + 1)) + 1 + (k' - k) := by omega
      rw [this, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.sub_zero]
      omega
  · have hk := hge h1
    rw [adBegin, adRem_some_lt hpos]
    generalize avNext (h, k) = k' at h1 hk
    have : h.2.2.1.length - k = (h.2.2.1.length - (k' + 1)) + 1 + (k' - k) := by omega
    rw [this, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.sub_zero, Nat.zero_add]
    omega
  · exact Nat.zero_le _

theorem adRem_init : adRem (h, adInit h) ≤ adCalls h := by
  have := adRem_adPos (h := h) 0 none
  rw [Nat.sub_zero] at this
  exact this

theorem adRem_adAfter (v : ℕ) (racc acc : RawCoset) :
    adRem (h, adAfter (h, v, racc, acc)) ≤
      (adTW h).length + (h.2.2.1.length - (v + 1)) * adPer h := by
  unfold adAfter
  dsimp only
  split_ifs
  · exact (adRem_adPos _ _).trans (Nat.le_add_left _ _)
  · rcases racc with _ | g
    · exact (adRem_adPos _ _).trans (Nat.le_add_left _ _)
    · show adRem (h, ((v, 0, some _, acc), (adRN h, none))) ≤ _
      rw [adRem_some_ge (lt_irrefl _), Nat.sub_zero]

theorem adRem_adOpen (v r : ℕ) (racc acc : RawCoset) :
    adRem (h, adOpen (h, v, r, racc, acc)) ≤
      (adRN h - r) * (adKO h).length + (adTW h).length +
        (h.2.2.1.length - (v + 1)) * adPer h := by
  unfold adOpen
  dsimp only
  split_ifs with hr
  · rw [adBegin, adRem_some_lt hr, Nat.sub_zero]
    have : adRN h - r = (adRN h - (r + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega
  · exact (adRem_adAfter v racc acc).trans (by omega)

theorem adChild_some_cur {st : ADState} {J : RawWinSI} (hJ : adChild (h, st) = some J) :
    ∃ g, st.1.2.2.1 = some g ∧ st.1.2.1 < adSegLen (h, st.2.1) := by
  obtain ⟨⟨v, w, cur, acc⟩, r, racc⟩ := st
  cases cur with
  | none => simp [adChild] at hJ
  | some g =>
    refine ⟨g, rfl, ?_⟩
    simp only [adChild, Option.bind_some] at hJ
    split_ifs at hJ with hc
    exact hc.1

theorem adRem_pos {st : ADState} {J : RawWinSI} (hJ : adChild (h, st) = some J) :
    1 ≤ adRem (h, st) := by
  obtain ⟨g, hcur, hw⟩ := adChild_some_cur hJ
  obtain ⟨⟨v, w, cur, acc⟩, r, racc⟩ := st
  dsimp only at hcur hw
  subst hcur
  by_cases hr : r < adRN h
  · rw [adRem_some_lt hr]
    rw [adSegLen_lt hr] at hw
    omega
  · rw [adRem_some_ge hr]
    rw [adSegLen_ge (Nat.not_lt.1 hr)] at hw
    omega

/-- **Every call makes the count drop.** -/
theorem adRem_combine {st : ADState} {J : RawWinSI} (hJ : adChild (h, st) = some J)
    (a : RawCoset) : adRem (h, adCombine (h, st, a)) + 1 ≤ adRem (h, st) := by
  obtain ⟨g, hcur, hw⟩ := adChild_some_cur hJ
  obtain ⟨⟨v, w, cur, acc⟩, r, racc⟩ := st
  dsimp only at hcur hw
  subst hcur
  have hmin : h.2.2.1.length - (min v h.2.2.1.length + 1) = h.2.2.1.length - (v + 1) := by
    omega
  by_cases hr : r < adRN h
  · rw [adSegLen_lt hr] at hw
    rw [adRem_some_lt hr]
    rcases a with _ | a
    · show adRem (h, adCombine (h, ((v, w, some g, acc), (r, racc)), none)) + 1 ≤ _
      simp only [adCombine, Option.elim, if_pos hr]
      have := adRem_adOpen (h := h) (min v h.2.2.1.length) (r + 1)
        (rawCosetNorm (h.2.2.2.2.1, racc)) (rawCosetNorm (h.2.2.2.2.1, acc))
      rw [hmin] at this
      omega
    · show adRem (h, adCombine (h, ((v, w, some g, acc), (r, racc)), some a)) + 1 ≤ _
      simp only [adCombine, Option.elim, adSegLen_lt hr]
      split_ifs with hw'
      · show adRem (h, ((min v h.2.2.1.length, w + 1, some _, _), (min r (adRN h), _))) + 1 ≤ _
        rw [Nat.min_eq_left (Nat.le_of_lt hr), adRem_some_lt hr, hmin]
        omega
      · have := adRem_adOpen (h := h) (min v h.2.2.1.length) (r + 1)
          (rawCosetNorm (h.2.2.2.2.1, rawCosetJoin (h.2.2.2.2.1, racc, some a)))
          (rawCosetNorm (h.2.2.2.2.1, acc))
        rw [hmin] at this
        omega
  · rw [adSegLen_ge (Nat.not_lt.1 hr)] at hw
    rw [adRem_some_ge hr]
    rcases a with _ | a
    · show adRem (h, adCombine (h, ((v, w, some g, acc), (r, racc)), none)) + 1 ≤ _
      simp only [adCombine, Option.elim, if_neg hr]
      have := adRem_adPos (h := h) (min v h.2.2.1.length + 1) acc
      have h2 : h.2.2.1.length - (min v h.2.2.1.length + 1) = h.2.2.1.length - (v + 1) := hmin
      rw [h2] at this
      omega
    · show adRem (h, adCombine (h, ((v, w, some g, acc), (r, racc)), some a)) + 1 ≤ _
      simp only [adCombine, Option.elim, adSegLen_ge (Nat.not_lt.1 hr)]
      split_ifs with hw'
      · show adRem (h, ((min v h.2.2.1.length, w + 1, some _, _), (min r (adRN h), _))) + 1 ≤ _
        have hge : min r (adRN h) = adRN h := Nat.min_eq_right (by omega)
        rw [hge, adRem_some_ge (lt_irrefl _), hmin]
        omega
      · have := adRem_adPos (h := h) (min v h.2.2.1.length + 1)
          (rawCosetJoin (h.2.2.2.2.1, acc, some a))
        rw [hmin] at this
        omega

end Rem

attribute [local irreducible] adRN adSegLen adSegWin adBegin adKO adTW adKG adCanon adOpen
  adPos adAfter

theorem quasiFun_adChild : QuasiFun adChild := by
  let Z := (RawGens × RawPerm) × (AVHdr × ADState)
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hh := pfst (psnd z)
  have hw := pfst (psnd (pfst (psnd (psnd z))))
  have hr := pfst (psnd (psnd (psnd z)))
  have hx := pfst (psnd (psnd (psnd (psnd hh))))
  have hy := psnd (psnd (psnd (psnd (psnd hh))))
  have hwin : QuasiFun (fun q : Z => adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1)) :=
    (hh.pair (hr.pair hw)).comp_quasiFun quasiFun_adSegWin
  have hlen : QuasiFun (fun q : Z => adSegLen (q.2.1, q.2.2.2.1)) :=
    (hh.pair hr).comp_quasiFun quasiFun_adSegLen
  have htidy : PolyFun (fun q : Z => tidyGens (q.2.1.2.2.2.2.1, q.1.1)) :=
    (hx.pair (pfst (pfst z))).comp polyFun_tidyGens
  have hnorm : PolyFun (fun q : Z => normPerm (q.2.1.2.2.2.2.1, q.1.2)) :=
    (hx.pair (psnd (pfst z))).comp polyFun_normPerm
  have ht1 : QuasiFun (fun q : Z => decide (q.2.2.1.2.1 < adSegLen (q.2.1, q.2.2.2.1))) :=
    (hw.quasiFun.pair hlen).comp_poly plt
  have ht2 : QuasiFun (fun q : Z => rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
      adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1))) :=
    (htidy.quasiFun.pair hwin).comp_poly polyFun_rawIsInvariant
  have hand : QuasiFun (fun q : Z => decide (q.2.2.1.2.1 < adSegLen (q.2.1, q.2.2.2.1)) &&
      rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1))) := by
    refine (aggnQuasiFun_ite ht1 ht2 (quasiFun_const false)).of_eq (fun q => ?_)
    by_cases h1 : q.2.2.1.2.1 < adSegLen (q.2.1, q.2.2.2.1) <;> simp [h1]
  have hsome : QuasiFun (fun q : Z => (some (adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1),
      tidyGens (q.2.1.2.2.2.2.1, q.1.1), normPerm (q.2.1.2.2.2.2.1, q.1.2),
      q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)) :=
    (hwin.pair (htidy.quasiFun.pair (hnorm.quasiFun.pair (hx.pair hy).quasiFun))).comp_poly
      polyFun_some
  have hbody : QuasiFun (fun q : Z =>
      if q.2.2.1.2.1 < adSegLen (q.2.1, q.2.2.2.1) ∧
          rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
            adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1)) = true
      then (some (adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1),
        tidyGens (q.2.1.2.2.2.2.1, q.1.1), normPerm (q.2.1.2.2.2.2.1, q.1.2),
        q.2.1.2.2.2.2.1, q.2.1.2.2.2.2.2) : Option RawWinSI)
      else none) := by
    refine (aggnQuasiFun_ite hand hsome (quasiFun_const none)).of_eq (fun q => ?_)
    by_cases h1 : q.2.2.1.2.1 < adSegLen (q.2.1, q.2.2.2.1)
    · by_cases h2 : rawIsInvariant (tidyGens (q.2.1.2.2.2.2.1, q.1.1),
        adSegWin (q.2.1, q.2.2.2.1, q.2.2.1.2.1)) = true <;> simp [h1, h2]
    · simp [h1]
  have i : PolyFun (fun p : AVHdr × ADState => p) := polyFun_id
  refine (((pfst (psnd (psnd (pfst (psnd i))))).pair i).quasiFun.comp
    (QuasiFun.optionElim (quasiFun_const none) hbody)).of_eq (fun p => ?_)
  unfold adChild
  cases p.2.1.2.2.1 <;> rfl

set_option maxHeartbeats 8000000 in
theorem quasiFun_adCombine : QuasiFun adCombine := by
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
  have hRN : QuasiFun (fun p : Z => adRN p.1) := hh.comp_quasiFun quasiFun_adRN
  have hrlt : QuasiFun (fun p : Z => decide (p.2.1.2.1 < adRN p.1)) :=
    (hr.quasiFun.pair hRN).comp_poly plt
  have hnormA : PolyFun (fun p : Z => rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)) :=
    (hx.pair hacc).comp polyFun_rawCosetNorm
  have hnormR : PolyFun (fun p : Z => rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2)) :=
    (hx.pair hra).comp polyFun_rawCosetNorm
  have hopen0 : QuasiFun (fun p : Z => adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length,
      p.2.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2),
      rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))) :=
    (hh.pair (hmin.pair ((hr.add (polyFun_const 1)).pair (hnormR.pair hnormA)))).comp_quasiFun
      quasiFun_adOpen
  have hpos0 : QuasiFun (fun p : Z => adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
      p.2.1.1.2.2.2)) :=
    (hh.pair ((hmin.add (polyFun_const 1)).pair hacc)).comp_quasiFun quasiFun_adPos
  have hnone : QuasiFun (fun p : Z =>
      if p.2.1.2.1 < adRN p.1 then
        adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
      else adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1, p.2.1.1.2.2.2)) := by
    refine (aggnQuasiFun_ite hrlt hopen0 hpos0).of_eq (fun p => ?_)
    by_cases h1 : p.2.1.2.1 < adRN p.1 <;> simp [h1]
  have hseg : QuasiFun (fun p : Z => decide (p.2.1.1.2.1 + 1 < adSegLen (p.1, p.2.1.2.1))) :=
    ((hw.add (polyFun_const 1)).quasiFun.pair ((hh.pair hr).comp_quasiFun quasiFun_adSegLen)).comp_poly
      plt
  have hminr : QuasiFun (fun p : Z => min p.2.1.2.1 (adRN p.1)) :=
    (hr.quasiFun.pair hRN).comp_poly polyFun_min
  have hcont : QuasiFun (fun p : Z =>
      (((min p.2.1.1.1 p.1.2.2.1.length, p.2.1.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
        rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)),
        (min p.2.1.2.1 (adRN p.1), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2))) : ADState)) :=
    (hmin.pair ((hw.add (polyFun_const 1)).pair (((hx.pair ha).comp polyFun_rawCosetNorm).pair
      hnormA))).quasiFun.pair (hminr.pair hnormR.quasiFun)
  have hopen1 : QuasiFun (fun p : Z => adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length,
      p.2.1.2.1 + 1,
      rawCosetNorm (p.1.2.2.2.2.1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2, p.2.2)),
      rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))) :=
    (hh.pair (hmin.pair ((hr.add (polyFun_const 1)).pair
      (((hx.pair ((hx.pair (hra.pair ha)).comp polyFun_rawCosetJoin)).comp
        polyFun_rawCosetNorm).pair hnormA)))).comp_quasiFun quasiFun_adOpen
  have hpos1 : QuasiFun (fun p : Z => adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
      rawCosetJoin (p.1.2.2.2.2.1, p.2.1.1.2.2.2, p.2.2))) :=
    (hh.pair ((hmin.add (polyFun_const 1)).pair
      ((hx.pair (hacc.pair ha)).comp polyFun_rawCosetJoin))).comp_quasiFun quasiFun_adPos
  have hsomeZ : QuasiFun (fun p : Z =>
      if p.2.1.1.2.1 + 1 < adSegLen (p.1, p.2.1.2.1) then
        (((min p.2.1.1.1 p.1.2.2.1.length, p.2.1.1.2.1 + 1, rawCosetNorm (p.1.2.2.2.2.1, p.2.2),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2)),
          (min p.2.1.2.1 (adRN p.1), rawCosetNorm (p.1.2.2.2.2.1, p.2.1.2.2))) : ADState)
      else if p.2.1.2.1 < adRN p.1 then
        adOpen (p.1, min p.2.1.1.1 p.1.2.2.1.length, p.2.1.2.1 + 1,
          rawCosetNorm (p.1.2.2.2.2.1, rawCosetJoin (p.1.2.2.2.2.1, p.2.1.2.2, p.2.2)),
          rawCosetNorm (p.1.2.2.2.2.1, p.2.1.1.2.2.2))
      else adPos (p.1, min p.2.1.1.1 p.1.2.2.1.length + 1,
        rawCosetJoin (p.1.2.2.2.2.1, p.2.1.1.2.2.2, p.2.2))) := by
    have hin := aggnQuasiFun_ite hrlt hopen1 hpos1
    refine (aggnQuasiFun_ite hseg hcont hin).of_eq (fun p => ?_)
    by_cases h1 : p.2.1.1.2.1 + 1 < adSegLen (p.1, p.2.1.2.1)
    · simp [h1]
    · by_cases h2 : p.2.1.2.1 < adRN p.1 <;> simp [h1, h2]
  refine ((ha.pair i).quasiFun.comp (QuasiFun.optionElim hnone
    (polyFun_snd.comp_quasiFun hsomeZ))).of_eq (fun p => ?_)
  obtain ⟨h, st, a⟩ := p
  unfold adCombine
  cases a <;> rfl

end Algo
