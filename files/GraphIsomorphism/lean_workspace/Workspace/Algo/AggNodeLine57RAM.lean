/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the round of Sec. 15, lines 5–7 (`Algo.aggnL57Round`) has the cost
data the machine packaging needs.
-/
import Workspace.Algo.AggNodeLine57Round

/-!
# The round of lines 5–7 runs on the machine

`Algo.aggnL57Round_hasRunCostQ` gives `Algo.aggnL57Round` the cost data
`Algo.Round.RunCostQ`: its four routines are `RAM.QuasiFun`, its states are quasipolynomially
small, its answers are polynomially small and its width is quasipolynomial, all in the degree
`n` of the node.

The state has two parts. The stores of AggregateCertificates are kept through the caps of the
aggregate carrier (`Algo.aggnAggregatePack`) at every step, so they are bounded as in
`Algo.aggnAggregate_hasRunCostQ`. The state of the loop over the versions is bounded by the
header of Eq. (71), whose size is a quasipolynomial function of the node and the capped stores
(`Algo.quasiFun_aggnL57Hdr`): its two counters are at most the number of versions and the
number of windows, and its two cosets are stored with shortened generators
(`Algo.rawCosetNorm`). In case 1 of the repair of lines 7–11 the loop also carries the index of
a coset of `ker ϕ*` and the hull of the answers of the cosets done so far, and its current
coset may be a coset of `ker ϕ*` as `Algo.adReps` lists it; all of these are bounded by a
quasipolynomial function of the header (`Algo.adStep_size_bdd`).
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

/-! ## The state of the loop over the versions is small -/

theorem size_rawCosetNorm {x : RawStr} {n : ℕ} (hx : x.length ≤ n) (a : RawCoset) :
    Enc.size (rawCosetNorm (x, a)) ≤ chainBound n :=
  aggnNormAnswer_size hx a

theorem avNext_le (h : AVHdr) (k : ℕ) : avNext (h, k) ≤ h.2.2.1.length := by
  rcases avNext_spec h k with ⟨he, _⟩ | ⟨_, hlt, _, _⟩ <;> omega

private theorem size_nat_le {k M : ℕ} (hk : k ≤ M) : Enc.size k ≤ M + 2 := by
  rw [Small.size_nat]
  have := size_le_self k
  omega

theorem avState_size_le {st : AVState} {M B : ℕ} (hk : st.1 ≤ M) (hw : st.2.1 ≤ M)
    (hc : Enc.size st.2.2.1 ≤ B) (ha : Enc.size st.2.2.2 ≤ B) :
    Enc.size st ≤ 16 * (M + B + 2) := by
  have h0 : Enc.size st ≤ 2 * Enc.size st.1 + 2 * Enc.size st.2 := Combine.size_pair_le _ _
  have h1 : Enc.size st.2 ≤ 2 * Enc.size st.2.1 + 2 * Enc.size st.2.2 := Combine.size_pair_le _ _
  have h2 : Enc.size st.2.2 ≤ 2 * Enc.size st.2.2.1 + 2 * Enc.size st.2.2.2 :=
    Combine.size_pair_le _ _
  have := size_nat_le hk
  have := size_nat_le hw
  omega

theorem avHdr_vers_le (h : AVHdr) : h.2.2.1.length ≤ Enc.size h :=
  (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans (size_snd_le' _)))

theorem avHdr_wins_le (h : AVHdr) : h.2.2.2.1.length ≤ Enc.size h :=
  (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans
    ((size_snd_le' _).trans (size_snd_le' _))))

theorem avPos_size {n : ℕ} (p : AVHdr × ℕ × RawCoset) (hx : p.1.2.2.2.2.1.length ≤ n) :
    Enc.size (avPos p) ≤ 16 * (Enc.size p.1 + chainBound n + 2) := by
  obtain ⟨h, k, acc⟩ := p
  exact avState_size_le (st := avPos (h, k, acc)) ((avNext_le h k).trans (avHdr_vers_le h))
    (Nat.zero_le _) (size_rawCosetNorm hx _) (size_rawCosetNorm hx _)

theorem avInit_size {n : ℕ} (h : AVHdr) (hx : h.2.2.2.2.1.length ≤ n) :
    Enc.size (avInit h) ≤ 16 * (Enc.size h + chainBound n + 2) :=
  avPos_size (h, 0, none) hx

theorem avCombine_cont {h : AVHdr} {k w : ℕ} {cur acc : RawCoset} {a : RawGens × RawPerm}
    (hw : w + 1 < h.2.2.2.1.length) :
    avCombine (h, (k, w, cur, acc), some a) = (min k h.2.2.1.length, w + 1,
      rawCosetNorm (h.2.2.2.2.1, some a), rawCosetNorm (h.2.2.2.2.1, acc)) := by
  simp only [avCombine, Option.elim, if_pos hw]

theorem avCombine_last {h : AVHdr} {k w : ℕ} {cur acc : RawCoset} {a : RawGens × RawPerm}
    (hw : ¬ w + 1 < h.2.2.2.1.length) :
    avCombine (h, (k, w, cur, acc), some a) =
      avPos (h, k + 1, rawCosetJoin (h.2.2.2.2.1, acc, some a)) := by
  simp only [avCombine, Option.elim, if_neg hw]

theorem avCombine_size {n : ℕ} (p : AVHdr × AVState × RawCoset)
    (hx : p.1.2.2.2.2.1.length ≤ n) :
    Enc.size (avCombine p) ≤ 16 * (Enc.size p.1 + chainBound n + 2) := by
  obtain ⟨h, ⟨k, w, cur, acc⟩, a⟩ := p
  replace hx : h.2.2.2.2.1.length ≤ n := hx
  show Enc.size (avCombine (h, (k, w, cur, acc), a)) ≤ 16 * (Enc.size h + chainBound n + 2)
  cases a with
  | none => exact avPos_size (h, k + 1, acc) hx
  | some a =>
    by_cases hw : w + 1 < h.2.2.2.1.length
    · rw [avCombine_cont hw]
      have h1 : min k h.2.2.1.length ≤ Enc.size h :=
        (Nat.min_le_right k h.2.2.1.length).trans (avHdr_vers_le h)
      have h2 : w + 1 ≤ Enc.size h := (Nat.le_of_lt hw).trans (avHdr_wins_le h)
      have h3 : Enc.size (rawCosetNorm (h.2.2.2.2.1, some a)) ≤ chainBound n :=
        size_rawCosetNorm hx _
      have h4 : Enc.size (rawCosetNorm (h.2.2.2.2.1, acc)) ≤ chainBound n :=
        size_rawCosetNorm hx _
      exact avState_size_le (st := (min k h.2.2.1.length, w + 1,
        rawCosetNorm (h.2.2.2.2.1, some a), rawCosetNorm (h.2.2.2.2.1, acc))) h1 h2 h3 h4
    · rw [avCombine_last hw]
      exact avPos_size (h, k + 1, rawCosetJoin (h.2.2.2.2.1, acc, some a)) hx


/-! ## The states stay small -/

private theorem size_nat_le' {k M : ℕ} (hk : k ≤ M) : Enc.size k ≤ M + 2 := by
  rw [Small.size_nat]
  have := size_le_self k
  omega

theorem adState_size_le {st : ADState} {M B : ℕ} (hv : st.1.1 ≤ M) (hw : st.1.2.1 ≤ M)
    (hc : Enc.size st.1.2.2.1 ≤ B) (ha : Enc.size st.1.2.2.2 ≤ B) (hr : st.2.1 ≤ M)
    (hra : Enc.size st.2.2 ≤ B) : Enc.size st ≤ 64 * (M + B + 2) := by
  have h0 : Enc.size st ≤ 2 * Enc.size st.1 + 2 * Enc.size st.2 := Combine.size_pair_le _ _
  have h1 : Enc.size st.2 ≤ 2 * Enc.size st.2.1 + 2 * Enc.size st.2.2 :=
    Combine.size_pair_le _ _
  have h2 := avState_size_le (st := st.1) hv hw hc ha
  have := size_nat_le' hr
  omega

private abbrev Wq (c n : ℕ) : ℕ := 2 ^ ((Nat.log 2 n + 2) ^ c)

private theorem Wq_mono (c : ℕ) {a b : ℕ} (h : a ≤ b) : Wq c a ≤ Wq c b :=
  quasiPolyBound_witness_mono c h

set_option maxHeartbeats 8000000 in
/-- **The steps keep the state small**: every state `Algo.adPos` or `Algo.adCombine` produces
has size at most a quasipolynomial function of the size of the header and `chainBound n`,
whatever the state it starts from. -/
theorem adStep_size_bdd : ∃ F : ℕ → ℕ, QuasiPolyBound F ∧ Monotone F ∧
    ∀ (n : ℕ) (h : AVHdr), h.2.2.2.2.1.length ≤ n →
      (∀ k acc, Enc.size (adPos (h, k, acc)) ≤ F (Enc.size h + chainBound n)) ∧
      (∀ st a, Enc.size (adCombine (h, st, a)) ≤ F (Enc.size h + chainBound n)) := by
  obtain ⟨cK, hK⟩ := polyFun_adKO.quasiFun.size
  obtain ⟨cR, hR⟩ := (((pfst polyFun_id).pair (pfst (psnd polyFun_id))).comp_quasiFun
    quasiFun_adRightReps : QuasiFun (fun h : AVHdr => adRightReps (h.1, h.2.1))).size
  obtain ⟨cB, hB⟩ := quasiFun_adBegin.size
  let G := fun N => 2 * N + 4 * (N + 2) + 4 * (Wq cR N + 2)
  let M := fun N => N + Wq cK N + Wq cR N
  let B := fun N => N + Wq cB (G N) + 2
  let F := fun N => 64 * (M N + B N + 2)
  have hG : QuasiPolyBound G :=
    (((polyBound_const 2).mul polyBound_id).quasiPoly.add
      ((polyBound_const 4).mul (polyBound_id.add (polyBound_const 2))).quasiPoly).add
      ((polyBound_const 4).quasiPoly.mul ((quasiPolyBound_witness cR).add
        (polyBound_const 2).quasiPoly))
  have hGm : Monotone G := by
    intro a b hab
    have := Wq_mono cR hab
    dsimp only [G]
    omega
  refine ⟨F, ?_, ?_, ?_⟩
  · exact (polyBound_const 64).quasiPoly.mul
      (((polyBound_id.quasiPoly.add (quasiPolyBound_witness cK)).add
        (quasiPolyBound_witness cR)).add
      ((polyBound_id.quasiPoly.add ((quasiPolyBound_witness cB).comp hG)).add
        (polyBound_const 2).quasiPoly) |>.add (polyBound_const 2).quasiPoly)
  · intro a b hab
    have := Wq_mono cK hab
    have := Wq_mono cR hab
    have := Wq_mono cB (hGm hab)
    dsimp only [F, M, B]
    omega
  intro n h hx
  set N := Enc.size h + chainBound n with hN
  have hhN : Enc.size h ≤ N := Nat.le_add_right _ _
  have hL : h.2.2.1.length ≤ N := (avHdr_vers_le h).trans hhN
  have hTW : (adTW h).length ≤ N := by
    have : (adTW h).length ≤ h.2.2.2.1.length := by
      unfold adTW; rw [List.length_tail]; omega
    exact this.trans ((avHdr_wins_le h).trans hhN)
  have hKO : (adKO h).length ≤ Wq cK N :=
    (length_le_size _).trans ((hK h).trans (Wq_mono cK hhN))
  have hRN : adRN h ≤ Wq cR N :=
    (length_le_size _).trans ((hR h).trans (Wq_mono cR hhN))
  have hnorm : ∀ a : RawCoset, Enc.size (rawCosetNorm (h.2.2.2.2.1, a)) ≤ B N := by
    intro a
    have := size_rawCosetNorm hx a
    dsimp only [B]
    omega
  have hnone : Enc.size (none : RawCoset) ≤ B N := by
    rw [size_none]; dsimp only [B]; omega
  have hbegin : ∀ v r, v ≤ N → r ≤ Wq cR N → Enc.size (adBegin (h, v, r)) ≤ B N := by
    intro v r hv hr
    have h1 := hB (h, v, r)
    have h2 := Combine.size_pair_le h (v, r)
    have h3 := Combine.size_pair_le v r
    have h4 := size_nat_le' hv
    have h5 := size_nat_le' hr
    have h6 : Enc.size (h, v, r) ≤ G N := by dsimp only [G]; omega
    have h7 : Enc.size (adBegin (h, v, r)) ≤ Wq cB (Enc.size (h, v, r)) := h1
    have := Wq_mono cB h6
    dsimp only [B]
    omega
  have hMN : N ≤ M N := by dsimp only [M]; omega
  have hMK : Wq cK N ≤ M N := by dsimp only [M]; omega
  have hMR : Wq cR N ≤ M N := by dsimp only [M]; omega
  have hpos : ∀ k acc, Enc.size (adPos (h, k, acc)) ≤ F N := by
    intro k acc
    have hnext : avNext (h, k) ≤ N := (avNext_le h k).trans hL
    unfold adPos
    dsimp only
    split_ifs
    · exact adState_size_le (M := M N) (B := B N) (hnext.trans hMN) (Nat.zero_le _)
        (hnorm _) (hnorm _) (hRN.trans hMR) hnone
    · exact adState_size_le (M := M N) (B := B N) (hnext.trans hMN) (Nat.zero_le _)
        (hbegin _ _ hnext (Nat.zero_le _)) (hnorm _) (Nat.zero_le _) hnone
    · exact adState_size_le (M := M N) (B := B N) (hL.trans hMN) (Nat.zero_le _)
        hnone (hnorm _) (Nat.zero_le _) hnone
  have hafter : ∀ v racc acc, v ≤ N → Enc.size acc ≤ B N →
      Enc.size (adAfter (h, v, racc, acc)) ≤ F N := by
    intro v racc acc hv hacc
    unfold adAfter
    dsimp only
    split_ifs
    · exact hpos _ _
    · rcases racc with _ | g
      · exact hpos _ _
      · show Enc.size (((v, 0, rawCosetNorm (h.2.2.2.2.1, some g), acc), (adRN h, none)) :
          ADState) ≤ F N
        exact adState_size_le (M := M N) (B := B N)
          (st := ((v, 0, rawCosetNorm (h.2.2.2.2.1, some g), acc), (adRN h, none)))
          (hv.trans hMN) (Nat.zero_le _) (hnorm (some g)) hacc (hRN.trans hMR) hnone
  have hopen : ∀ v r racc acc, v ≤ N → Enc.size racc ≤ B N → Enc.size acc ≤ B N →
      Enc.size (adOpen (h, v, r, racc, acc)) ≤ F N := by
    intro v r racc acc hv hracc hacc
    by_cases hr : r < adRN h
    · rw [adOpen_lt racc acc hr]
      exact adState_size_le (M := M N) (B := B N) (hv.trans hMN) (Nat.zero_le _)
        (hbegin _ _ hv (hr.le.trans hRN)) hacc ((hr.le.trans hRN).trans hMR) hracc
    · rw [adOpen_ge racc acc (Nat.not_lt.1 hr)]
      exact hafter v racc acc hv hacc
  refine ⟨hpos, ?_⟩
  rintro ⟨⟨v, w, cur, acc⟩, r, racc⟩ a
  have hmin : min v h.2.2.1.length ≤ N := (Nat.min_le_right _ _).trans hL
  rcases a with _ | a
  · show Enc.size (adCombine (h, ((v, w, cur, acc), (r, racc)), none)) ≤ F N
    simp only [adCombine, Option.elim]
    split_ifs
    · exact hopen _ _ _ _ hmin (hnorm _) (hnorm _)
    · exact hpos _ _
  · show Enc.size (adCombine (h, ((v, w, cur, acc), (r, racc)), some a)) ≤ F N
    simp only [adCombine, Option.elim]
    split_ifs with hw hr
    · have hseg : adSegLen (h, r) ≤ (adKO h).length + (adTW h).length := by
        unfold adSegLen; dsimp only; split_ifs <;> omega
      have hw' : w + 1 ≤ M N := by dsimp only [M]; omega
      exact adState_size_le (M := M N) (B := B N)
        (st := ((min v h.2.2.1.length, w + 1, rawCosetNorm (h.2.2.2.2.1, some a),
          rawCosetNorm (h.2.2.2.2.1, acc)),
          (min r (adRN h), rawCosetNorm (h.2.2.2.2.1, racc))))
        (hmin.trans hMN) hw' (hnorm (some a)) (hnorm acc)
        ((Nat.min_le_right _ _).trans (hRN.trans hMR)) (hnorm racc)
    · exact hopen _ _ _ _ hmin (hnorm _) (hnorm _)
    · exact hpos _ _

/-- The size of one step of stretch 3, in either loop. -/
theorem l57Step_size {F : ℕ → ℕ}
    (hF : ∀ (n : ℕ) (h : AVHdr), h.2.2.2.2.1.length ≤ n →
      (∀ k acc, Enc.size (adPos (h, k, acc)) ≤ F (Enc.size h + chainBound n)) ∧
      (∀ st a, Enc.size (adCombine (h, st, a)) ≤ F (Enc.size h + chainBound n)))
    {n : ℕ} (h : AVHdr) (hx : h.2.2.2.2.1.length ≤ n) (st : ADState) (a : RawCoset) :
    Enc.size (l57Step (h, st, a)) ≤
      F (Enc.size h + chainBound n) + 32 * (Enc.size h + chainBound n + 2) + 20 := by
  unfold l57Step
  split_ifs
  · have := (hF n h hx).2 st a
    omega
  · have h1 := avCombine_size (h, st.1, a) hx
    have h2 := Combine.size_pair_le (avCombine (h, st.1, a)) ((0, none) : ℕ × RawCoset)
    have h3 := Combine.size_pair_le (0 : ℕ) (none : RawCoset)
    have h4 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl
    have h5 : Enc.size (none : RawCoset) = 2 := size_none
    dsimp only at h1 ⊢
    omega

/-! ## The four routines -/

section Routines

variable (c b t d dc dp : ℕ)

theorem polyFun_avCalls : PolyFun avCalls := by
  have i : PolyFun (fun h : AVHdr => h) := polyFun_id
  exact ((pfst (psnd (psnd i))).comp polyFun_length).mul
    ((pfst (psnd (psnd (psnd i)))).comp polyFun_length)

theorem polyFun_l57Small : PolyFun l57Small := by
  have hp : PolyFun (fun h : AVHdr => (h.1, h.2.1)) := polyFun_fst.pair (polyFun_snd.comp polyFun_fst)
  exact polyFun_and (hp.comp polyFun_alignRSmall) ((polyFun_const 2).le (hp.comp polyFun_alignRMs))

theorem quasiFun_l57Calls : QuasiFun l57Calls := by
  have hadCalls : QuasiFun adCalls := by
    have i : PolyFun (fun h : AVHdr => h) := polyFun_id
    exact ((((pfst (psnd (psnd i))).comp polyFun_length).quasiFun.pair
      (((i.comp_quasiFun quasiFun_adRN).pair ((i.comp polyFun_adKO).comp polyFun_length).quasiFun).comp_poly
        polyFun_mul |>.pair ((i.comp polyFun_adTW).comp polyFun_length).quasiFun |>.comp_poly
        polyFun_add)).comp_poly polyFun_mul).of_eq (fun h => rfl)
  exact (QuasiFun.ite polyFun_l57Small hadCalls polyFun_avCalls.quasiFun).of_eq
    (fun h => by unfold l57Calls; cases l57Small h <;> rfl)

theorem quasiFun_l57Init : QuasiFun l57Init :=
  (QuasiFun.ite polyFun_l57Small quasiFun_adInit
    (polyFun_avInit.pair (polyFun_const ((0, none) : ℕ × RawCoset))).quasiFun).of_eq
    (fun h => by unfold l57Init; cases l57Small h <;> rfl)

theorem quasiFun_l57Child : QuasiFun l57Child :=
  (QuasiFun.ite ((pfst polyFun_id).comp polyFun_l57Small) quasiFun_adChild
    ((pfst polyFun_id).pair (pfst (psnd polyFun_id)) |>.comp polyFun_avChild).quasiFun).of_eq
    (fun p => by unfold l57Child; rfl)

theorem quasiFun_l57Step : QuasiFun l57Step :=
  (QuasiFun.ite ((pfst polyFun_id).comp polyFun_l57Small) quasiFun_adCombine
    ((((pfst polyFun_id).pair ((pfst (pfst (psnd polyFun_id))).pair (psnd (psnd polyFun_id)))).comp
      polyFun_avCombine).pair (polyFun_const ((0, none) : ℕ × RawCoset))).quasiFun).of_eq
    (fun p => by unfold l57Step; rfl)

theorem quasiFun_aggnL57AlignChild : QuasiFun (aggnL57AlignChild c b t d dc dp) := by
  let Z := AggnPhaseNode × ℕ × AggnL57State
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hdr : QuasiFun (fun q : Z => aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1)) :=
    ((pfst (pfst z)).pair (pfst (psnd (psnd z)))).comp_quasiFun (quasiFun_aggnL57Hdr c b t d dc dp)
  have hgate : QuasiFun (fun q : Z =>
      decide (q.2.1 < aggnAggregateWidth c q.1.1 + l57Calls (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1)))) :=
    ((pfst (psnd z)).quasiFun.pair
      ((((pfst (pfst z)).comp_quasiFun (aggnQuasiFun_aggregateWidth c)).pair
        (hdr.comp quasiFun_l57Calls)).comp_poly polyFun_add)).comp_poly plt
  have hst : QuasiFun (fun q : Z => q.2.2.2.getD (l57Init (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1)))) :=
    ((psnd (psnd (psnd z))).quasiFun.pair (hdr.comp quasiFun_l57Init)).comp_poly
      polyFun_optionGetD
  have hav := (hdr.pair hst).comp quasiFun_l57Child
  have hemb : PolyFun (fun r : RawWinSI × Z => (some (avEmb (r.2.1.1, r.1)) : Option AggnPhaseNode)) := by
    have j : PolyFun (fun r : RawWinSI × Z => r) := polyFun_id
    exact ((pfst (pfst (psnd j))).pair
      ((((pfst (psnd (pfst (pfst (psnd j))))).pair (pfst j)).comp aggnPolyFun_checkedWindow).comp
        polyFun_some)).comp polyFun_some
  have hmap : QuasiFun (fun q : Z =>
      (l57Child (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1),
        q.2.2.2.getD (l57Init (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1))))).map
        (fun J => avEmb (q.1.1, J))) := by
    refine ((hav.pair quasiFun_id).comp
      (QuasiFun.optionElim (quasiFun_const none) hemb.quasiFun)).of_eq (fun q => ?_)
    dsimp only
    cases l57Child (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1),
      q.2.2.2.getD (l57Init (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1)))) <;> rfl
  have hrun := aggnQuasiFun_ite hgate hmap (quasiFun_const none)
  refine (((psnd (pfst z)).quasiFun.pair quasiFun_id).comp
    (QuasiFun.optionElim hrun (quasiFun_const none))).of_eq (fun q => ?_)
  obtain ⟨⟨C, o⟩, j, s⟩ := q
  cases o with
  | some W => rfl
  | none =>
    simp only [aggnL57AlignChild, Option.elim_none, decide_eq_true_eq, id]

theorem quasiFun_aggnL57Child : QuasiFun (aggnL57Child c b t d dc dp) := by
  let Z := AggnPhaseNode × ℕ × AggnL57State
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hagg : QuasiFun (fun q : Z => aggnAggregateChild c (q.1, q.2.1, q.2.2.1)) :=
    ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z))))).comp_quasiFun
      (aggnQuasiFun_aggregateChild c)
  refine ((hagg.pair quasiFun_id).comp (QuasiFun.optionElim
    (quasiFun_aggnL57AlignChild c b t d dc dp)
    (polyFun_fst.comp polyFun_some).quasiFun)).of_eq (fun q => ?_)
  unfold aggnL57Child
  cases aggnAggregateChild c (q.1, q.2.1, q.2.2.1) <;> rfl

theorem quasiFun_aggnL57Combine : QuasiFun (aggnL57Combine c b t d dc dp) := by
  let Z := AggnPhaseNode × ℕ × AggnL57State × RawCoset
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hdr : QuasiFun (fun q : Z => aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1.1)) :=
    ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z))))).comp_quasiFun
      (quasiFun_aggnL57Hdr c b t d dc dp)
  have hst : QuasiFun (fun q : Z =>
      q.2.2.1.2.getD (l57Init (aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1.1)))) :=
    ((psnd (pfst (psnd (psnd z)))).quasiFun.pair (hdr.comp quasiFun_l57Init)).comp_poly
      polyFun_optionGetD
  have hav := (hdr.pair (hst.pair (psnd (psnd (psnd z))).quasiFun)).comp quasiFun_l57Step
  have hpk : QuasiFun (fun q : Z => aggnAggregatePack c dc dp q.1.1 q.2.2.1.1) :=
    ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z))))).comp_quasiFun
      (aggnQuasiFun_aggregatePack c dc dp)
  have hA := hpk.pair (hav.comp_poly polyFun_some)
  have hB : QuasiFun (fun r : AggnPhaseNode × Z =>
      ((aggnAggregateCombine c dc dp (r.2.1, r.2.2.1, r.2.2.2.1.1, r.2.2.2.2), none) :
        AggnL57State)) := by
    have j : PolyFun (fun r : AggnPhaseNode × Z => r) := polyFun_id
    exact (((pfst (psnd j)).pair ((pfst (psnd (psnd j))).pair
      ((pfst (pfst (psnd (psnd (psnd j))))).pair (psnd (psnd (psnd (psnd j))))))).comp_quasiFun
        (aggnQuasiFun_aggregateCombine c dc dp)).pair (quasiFun_const none)
  have hagg : QuasiFun (fun q : Z => aggnAggregateChild c (q.1, q.2.1, q.2.2.1.1)) :=
    ((pfst z).pair ((pfst (psnd z)).pair (pfst (pfst (psnd (psnd z)))))).comp_quasiFun
      (aggnQuasiFun_aggregateChild c)
  refine ((hagg.pair quasiFun_id).comp (QuasiFun.optionElim hA hB)).of_eq (fun q => ?_)
  unfold aggnL57Combine
  cases aggnAggregateChild c (q.1, q.2.1, q.2.2.1.1) <;> rfl

theorem polyFun_aggnL57Finish : PolyFun aggnL57Finish := by
  let Z := AggnPhaseNode × AggnL57State
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hsel : PolyFun (fun r : ADState × Z => r.1.1.2.2.2) :=
    psnd (psnd (psnd (pfst (pfst polyFun_id))))
  have hacc : PolyFun (fun q : Z => q.2.2.elim none (fun st => st.1.2.2.2)) :=
    (((psnd (psnd z)).pair z).comp (PolyFun.optionElim (polyFun_const none) hsel)).of_eq
      (fun q => by cases q.2.2 <;> rfl)
  exact ((pfst (psnd (pfst (pfst z)))).pair hacc).comp polyFun_rawCosetNorm

end Routines

/-! ## The cost data -/

/-- The bound on the input of the header routine, in the degree alone. -/
def aggnL57InBound (dc dp : ℕ) (Wp : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * aggnCheckedBound n + 2 * (16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2))

attribute [local irreducible] Enc.size aggnBoundedInit aggnCompareBoundedInit
  aggnBoundedCombine aggnCompareBoundedCombine

/-- The cost data of the round of lines 5–7, with two bounds that hold on every state: the
combine keeps the state below the state bound, and the answer is below the answer bound,
whatever the state it reads. -/
theorem aggnL57_hasRunCostQ_strong (c b t d dc dp : ℕ) :
    ∃ RC : Round.RunCostQ (aggnL57Round c b t d dc dp),
      (∀ I j s a, (aggnL57Round c b t d dc dp).WF I →
        Enc.size (aggnL57Combine c b t d dc dp (I, j, s, a)) ≤ RC.stateBound I.1.2.1.length) ∧
      (∀ I s, (aggnL57Round c b t d dc dp).WF I →
        Enc.size (aggnL57Finish (I, s)) ≤ RC.bound I.1.2.1.length) := by
  obtain ⟨Wc, hWc, hWcm, hcw⟩ := aggnChecked_width_bound c
  obtain ⟨Wp, hWp, hWpm, hpw⟩ := aggnCompareChecked_width_bound c
  obtain ⟨e1, he1⟩ := (quasiFun_aggnL57HdrCore c b t d).size
  obtain ⟨Kc, hKc, hKcm, he2⟩ := aggnL57Cap_le c b t d dc dp
  obtain ⟨F, hF, hFm, hFs⟩ := adStep_size_bdd
  let B := fun n => 16 * (aggnStateCap dc n + aggnCompareStateCap dp n + Wp n + 2)
  have hB : QuasiPolyBound B := (polyBound_const 16).quasiPoly.mul
    ((((aggnQuasiPolyBound_stateCap dc).add (aggnQuasiPolyBound_compareStateCap dp)).add hWp).add
      (polyBound_const 2).quasiPoly)
  have hBm : Monotone B := by
    intro a b hab
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (aggnMono_stateCap dc hab)
        (aggnMono_compareStateCap dp hab)) (hWpm hab)) 2)
  let Q := aggnL57InBound dc dp Wp
  have hQ : QuasiPolyBound Q :=
    ((polyBound_const 2).quasiPoly.mul aggnPolyBound_checked.quasiPoly).add
      ((polyBound_const 2).quasiPoly.mul hB)
  have hQm : Monotone Q := by
    intro a b hab
    have := aggnMono_checkedBound hab
    have := hBm hab
    dsimp only [Q, aggnL57InBound]
    dsimp only [B] at this
    omega
  let H := fun n => 2 ^ ((Nat.log 2 (Q n) + 2) ^ e1)
  have hH : QuasiPolyBound H := (quasiPolyBound_witness e1).comp hQ
  have hHm : Monotone H := fun a b hab => quasiPolyBound_witness_mono e1 (hQm hab)
  let K := fun n => Kc (Q n)
  have hK : QuasiPolyBound K := hKc.comp hQ
  let V := fun n => F (H n + chainBound n) + 32 * (H n + chainBound n + 2) + 22
  have hV : QuasiPolyBound V := ((hF.comp (hH.add polyBound_chainBound.quasiPoly)).add
    ((polyBound_const 32).quasiPoly.mul
      ((hH.add polyBound_chainBound.quasiPoly).add (polyBound_const 2).quasiPoly))).add
      (polyBound_const 22).quasiPoly
  have hVm : Monotone V := by
    intro a b hab
    have h1 := hHm hab
    have h2 := mono_chainBound hab
    have h3 := hFm (Nat.add_le_add h1 h2)
    dsimp only [V]
    omega
  -- the facts about a well-formed node
  have hwidth : ∀ I, (aggnL57Round c b t d dc dp).WF I →
      aggnCompareWidth c I.1 ≤ Wp I.1.2.1.length := by
    intro I hI
    exact hpw (I.1, none) ⟨rfl, hI.2.1, by simp⟩
  have hsizeC : ∀ I, (aggnL57Round c b t d dc dp).WF I →
      Enc.size I.1 ≤ aggnCheckedBound I.1.2.1.length := fun I hI =>
    (size_fst_le' I).trans (aggnCheckedRound_size c I.1.2.1.length I hI)
  have hpack : ∀ I, (aggnL57Round c b t d dc dp).WF I → ∀ s,
      Enc.size (aggnAggregatePack c dc dp I.1 s) ≤ B I.1.2.1.length := by
    intro I hI s
    dsimp only [aggnAggregatePack]
    exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
      (w := Wp I.1.2.1.length) (aggnCapState_size dc _ _)
      ((Nat.min_le_right _ _).trans (hwidth I hI)) (aggnCompareCapState_size dp _ _)
  have hin : ∀ I, (aggnL57Round c b t d dc dp).WF I →
      2 * Enc.size I.1 + 2 * (16 * (aggnStateCap dc I.1.2.1.length +
        aggnCompareStateCap dp I.1.2.1.length + aggnCompareWidth c I.1 + 2)) ≤
        Q I.1.2.1.length := by
    intro I hI
    have := hsizeC I hI
    have := hwidth I hI
    dsimp only [Q, aggnL57InBound]
    omega
  have hhdr : ∀ I, (aggnL57Round c b t d dc dp).WF I → ∀ s,
      Enc.size (aggnL57Hdr c b t d dc dp (I.1, s)) ≤ H I.1.2.1.length := by
    intro I hI s
    have h1 : Enc.size (I.1, aggnAggregatePack c dc dp I.1 s) ≤ Q I.1.2.1.length := by
      have := Combine.size_pair_le I.1 (aggnAggregatePack c dc dp I.1 s)
      have := aggnAggregatePack_size c dc dp I.1 s
      have := hin I hI
      omega
    exact (he1 _).trans (quasiPolyBound_witness_mono e1 h1)
  have hcomb : ∀ I j s a, (aggnL57Round c b t d dc dp).WF I →
      Enc.size (aggnL57Combine c b t d dc dp (I, j, s, a)) ≤
        2 * B I.1.2.1.length + 2 * V I.1.2.1.length := by
    intro I j s a hI
    unfold aggnL57Combine
    cases aggnAggregateChild c (I, j, s.1) with
    | some J =>
      simp only [Option.elim_some]
      have h1 : Enc.size (aggnAggregateCombine c dc dp (I, j, s.1, a)) ≤ B I.1.2.1.length := by
        unfold aggnAggregateCombine
        exact hpack I hI _
      have h2 := Combine.size_pair_le (aggnAggregateCombine c dc dp (I, j, s.1, a))
        (none : Option ADState)
      have h3 : Enc.size (none : Option ADState) = 2 := size_none
      have h4 : 2 ≤ V I.1.2.1.length := by dsimp only [V]; omega
      omega
    | none =>
      simp only [Option.elim_none]
      set h := aggnL57Hdr c b t d dc dp (I.1, s.1)
      have hx : h.2.2.2.2.1.length ≤ I.1.2.1.length := le_rfl
      have h1 := hpack I hI s.1
      set st := l57Step (h, s.2.getD (l57Init h), a)
      have h2 : Enc.size st ≤ F (Enc.size h + chainBound I.1.2.1.length) +
          32 * (Enc.size h + chainBound I.1.2.1.length + 2) + 20 :=
        l57Step_size hFs h hx _ a
      have h3 : Enc.size h ≤ H I.1.2.1.length := hhdr I hI s.1
      have h3' := hFm (Nat.add_le_add_right h3 (chainBound I.1.2.1.length))
      have h4 : Enc.size (some st) = Enc.size st + 2 := size_some_eq _
      have h5 := Combine.size_pair_le (aggnAggregatePack c dc dp I.1 s.1) (some st)
      show Enc.size ((aggnAggregatePack c dc dp I.1 s.1, some st) : AggnL57State) ≤ _
      dsimp only [V]
      omega
  have hfin : ∀ I s, (aggnL57Round c b t d dc dp).WF I →
      Enc.size (aggnL57Finish (I, s)) ≤
        aggnCheckedBound I.1.2.1.length + chainBound I.1.2.1.length + 2 := by
    intro I s hI
    exact (size_rawCosetNorm (x := I.1.2.1) (n := I.1.2.1.length) le_rfl
      (s.2.elim none (fun st => st.1.2.2.2))).trans (by omega)
  refine ⟨{
    bound := fun k => aggnCheckedBound k + chainBound k + 2
    polyBound_bound := (aggnPolyBound_checked.add polyBound_chainBound).add (polyBound_const 2)
    mono_bound := fun _ _ h => Nat.add_le_add_right
      (Nat.add_le_add (aggnMono_checkedBound h) (mono_chainBound h)) 2
    stateBound := fun n => 2 * B n + 2 * V n
    quasiPolyBound_stateBound := ((polyBound_const 2).quasiPoly.mul hB).add
      ((polyBound_const 2).quasiPoly.mul hV)
    mono_stateBound := fun _ _ h => Nat.add_le_add (Nat.mul_le_mul_left 2 (hBm h))
      (Nat.mul_le_mul_left 2 (hVm h))
    widthBound := fun n => Wc n + Wp n + K n
    quasiPolyBound_widthBound := (hWc.add hWp).add hK
    quasiFun_child := quasiFun_aggnL57Child c b t d dc dp
    quasiFun_init := (aggnQuasiFun_aggregateInit c dc dp).pair (quasiFun_const none)
    quasiFun_combine := quasiFun_aggnL57Combine c b t d dc dp
    quasiFun_finish := polyFun_aggnL57Finish.quasiFun
    ground_le := fun I => (length_le_size I.1.2.1).trans
      ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans (size_fst_le' I)))
    size_le := fun I hI => (aggnCheckedRound_size c I.1.2.1.length I hI).trans
      (show aggnCheckedBound I.1.2.1.length ≤
        aggnCheckedBound I.1.2.1.length + chainBound I.1.2.1.length + 2 by omega)
    init_le := ?_
    combine_le := ?_
    finish_le := ?_
    bot_le := fun m => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound m + chainBound m + 2
      rw [size_none]
      omega
    width_le := ?_
    polyFun_ground := aggnPolyFun_ground c dc 0
    wfCheck := aggnUniformWfCheck
    polyFun_wfCheck := aggnPolyFun_uniformWfCheck
    wfCheck_eq_true := aggnUniformWfCheck_spec c dc
    measureBound := fun _ => 1
    polyBound_measureBound := polyBound_const 1
    mono_measureBound := fun _ _ _ => le_rfl
    measure_le := ?_ }, hcomb, hfin⟩
  · -- the initial state
    intro I hI
    show Enc.size ((aggnAggregateInit c dc dp I, none) : AggnL57State) ≤
      2 * B I.1.2.1.length + 2 * V I.1.2.1.length
    have hc : Enc.size ((aggnUniformRound c dc).init I) ≤ aggnStateCap dc I.1.2.1.length := by
      dsimp only [aggnUniformRound]
      unfold aggnBoundedInit
      exact aggnCapState_size dc I.1.2.1.length _
    have hp : Enc.size ((aggnCompareBoundedRound c dp).init I) ≤
        aggnCompareStateCap dp I.1.2.1.length := by
      dsimp only [aggnCompareBoundedRound]
      unfold aggnCompareBoundedInit
      exact aggnCompareCapState_size dp I.1.2.1.length _
    have h1 : Enc.size (aggnAggregateInit c dc dp I) ≤ B I.1.2.1.length := by
      dsimp only [aggnAggregateInit]
      exact aggnAggregateState_size (dc := dc) (dp := dp) (n := I.1.2.1.length)
          (w := Wp I.1.2.1.length)
          (s := ((aggnUniformRound c dc).init I, 0, (aggnCompareBoundedRound c dp).init I))
          hc (Nat.zero_le _) hp
    have h2 := Combine.size_pair_le (aggnAggregateInit c dc dp I) (none : Option ADState)
    have h3 : Enc.size (none : Option ADState) = 2 := size_none
    have h4 : 2 ≤ V I.1.2.1.length := by dsimp only [V]; omega
    omega
  · -- the combine keeps the state small
    intro I j s a hI _ _
    exact hcomb I j s a hI
  · -- the answer is small
    intro I s hI _
    exact hfin I s hI
  · -- the width
    intro I hI
    have hc := hcw I.1.2.1.length I hI
    have hp := hpw I hI
    have hcap : aggnL57Cap c b t d dc dp I.1 ≤ K I.1.2.1.length :=
      (he2 I.1).trans (hKcm (hin I hI))
    change I.2.elim (aggnAggregateWidth c I.1 + aggnL57Cap c b t d dc dp I.1) (fun _ => 0) ≤ _
    change I.2.elim (aggnPhaseWidth c I.1) (fun _ => 0) ≤ _ at hc
    change I.2.elim (aggnCompareWidth c I.1) (fun _ => 0) ≤ _ at hp
    cases ho : I.2 <;> simp only [ho, Option.elim_none, Option.elim_some] at hc hp ⊢
    · exact Nat.add_le_add (Nat.add_le_add hc hp) hcap
    · exact Nat.zero_le _
  · intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

theorem aggnL57_hasRunCostQ (c b t d dc dp : ℕ) :
    Nonempty (Round.RunCostQ (aggnL57Round c b t d dc dp)) :=
  ⟨(aggnL57_hasRunCostQ_strong c b t d dc dp).choose⟩

/-- The cost data of the round of lines 5–7. -/
noncomputable def aggnL57RunCostQ (c b t d dc dp : ℕ) :
    Round.RunCostQ (aggnL57Round c b t d dc dp) :=
  Classical.choice (aggnL57_hasRunCostQ c b t d dc dp)

end Algo
