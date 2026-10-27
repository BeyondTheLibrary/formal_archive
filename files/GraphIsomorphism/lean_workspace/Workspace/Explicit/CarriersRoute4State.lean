/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the fold states of lines
4c–4d of the Master (Sec. 15; Procedure Align, Sec. 14.1), with an explicit exponent. Not part
of the faithful formalization.
-/
import Workspace.Explicit.S9AlignDom
import Workspace.Explicit.Top.Q5
import Workspace.Algo.PrimitiveLine4dCarrier

/-!
# The fold states of lines 4c–4d, with an explicit exponent

`Algo.adStep_size_bdd` bounds the states of stretch 3 (lines 7–11 of Procedure Align) by a
quasipolynomial of the header's size, with an exponent that is not given. Here the same
argument is run on one header with the bounds as parameters (`Explicit.adStep_size_of`), and
the parameters are filled with the explicit bounds of `Workspace/Explicit/S9AlignDom.lean`
(the cosets of `ker ϕ*` are listed within `2^{A (log₂ n + 2)^3}` steps). The result
(`Explicit.l57_state_q5`): if the header has at most `n` points and size at most
`2^{c (log₂ n + 2)^5}`, then every state of the loop has size at most `2^{K (log₂ n + 2)^5}`,
whatever the state it starts from.
-/

namespace Explicit

open RAM Algo

private theorem size_nat_le2 {k M : ℕ} (hk : k ≤ M) : Enc.size k ≤ M + 2 := by
  rw [Small.size_nat]
  have := size_le_self k
  omega

/-- **The steps of stretch 3 keep the state small, for one header** (the argument of
`Algo.adStep_size_bdd` with the bounds as parameters). -/
theorem adStep_size_of (h : AVHdr) {N MK MR MB : ℕ} (hhN : Enc.size h ≤ N)
    (hnorm0 : ∀ a : RawCoset, Enc.size (rawCosetNorm (h.2.2.2.2.1, a)) ≤ N)
    (hKO : (adKO h).length ≤ MK) (hRN : adRN h ≤ MR)
    (hbeg : ∀ v r, v ≤ N → r ≤ MR → Enc.size (adBegin (h, v, r)) ≤ MB) :
    (∀ k acc, Enc.size (adPos (h, k, acc)) ≤ 64 * ((N + MK + MR) + (N + MB + 2) + 2)) ∧
    (∀ st a, Enc.size (adCombine (h, st, a)) ≤ 64 * ((N + MK + MR) + (N + MB + 2) + 2)) := by
  have hL : h.2.2.1.length ≤ N := (avHdr_vers_le h).trans hhN
  have hTW : (adTW h).length ≤ N := by
    have : (adTW h).length ≤ h.2.2.2.1.length := by
      unfold adTW; rw [List.length_tail]; omega
    exact this.trans ((avHdr_wins_le h).trans hhN)
  have hnorm : ∀ a : RawCoset, Enc.size (rawCosetNorm (h.2.2.2.2.1, a)) ≤ N + MB + 2 :=
    fun a => by have := hnorm0 a; omega
  have hnone : Enc.size (none : RawCoset) ≤ N + MB + 2 := by rw [size_none]; omega
  have hbegin : ∀ v r, v ≤ N → r ≤ MR → Enc.size (adBegin (h, v, r)) ≤ N + MB + 2 :=
    fun v r hv hr => by have := hbeg v r hv hr; omega
  have hMN : N ≤ N + MK + MR := by omega
  have hMR : MR ≤ N + MK + MR := by omega
  have hpos : ∀ k acc, Enc.size (adPos (h, k, acc)) ≤
      64 * ((N + MK + MR) + (N + MB + 2) + 2) := by
    intro k acc
    have hnext : avNext (h, k) ≤ N := (avNext_le h k).trans hL
    unfold adPos
    dsimp only
    split_ifs
    · exact adState_size_le (M := N + MK + MR) (B := N + MB + 2) (hnext.trans hMN)
        (Nat.zero_le _) (hnorm _) (hnorm _) (hRN.trans hMR) hnone
    · exact adState_size_le (M := N + MK + MR) (B := N + MB + 2) (hnext.trans hMN)
        (Nat.zero_le _) (hbegin _ _ hnext (Nat.zero_le _)) (hnorm _) (Nat.zero_le _) hnone
    · exact adState_size_le (M := N + MK + MR) (B := N + MB + 2) (hL.trans hMN)
        (Nat.zero_le _) hnone (hnorm _) (Nat.zero_le _) hnone
  have hafter : ∀ v racc acc, v ≤ N → Enc.size acc ≤ N + MB + 2 →
      Enc.size (adAfter (h, v, racc, acc)) ≤ 64 * ((N + MK + MR) + (N + MB + 2) + 2) := by
    intro v racc acc hv hacc
    unfold adAfter
    dsimp only
    split_ifs
    · exact hpos _ _
    · rcases racc with _ | g
      · exact hpos _ _
      · show Enc.size (((v, 0, rawCosetNorm (h.2.2.2.2.1, some g), acc), (adRN h, none)) :
          ADState) ≤ _
        exact adState_size_le (M := N + MK + MR) (B := N + MB + 2)
          (st := ((v, 0, rawCosetNorm (h.2.2.2.2.1, some g), acc), (adRN h, none)))
          (hv.trans hMN) (Nat.zero_le _) (hnorm (some g)) hacc (hRN.trans hMR) hnone
  have hopen : ∀ v r racc acc, v ≤ N → Enc.size racc ≤ N + MB + 2 →
      Enc.size acc ≤ N + MB + 2 →
      Enc.size (adOpen (h, v, r, racc, acc)) ≤ 64 * ((N + MK + MR) + (N + MB + 2) + 2) := by
    intro v r racc acc hv hracc hacc
    by_cases hr : r < adRN h
    · rw [adOpen_lt racc acc hr]
      exact adState_size_le (M := N + MK + MR) (B := N + MB + 2) (hv.trans hMN)
        (Nat.zero_le _) (hbegin _ _ hv (hr.le.trans hRN)) hacc ((hr.le.trans hRN).trans hMR)
        hracc
    · rw [adOpen_ge racc acc (Nat.not_lt.1 hr)]
      exact hafter v racc acc hv hacc
  refine ⟨hpos, ?_⟩
  rintro ⟨⟨v, w, cur, acc⟩, r, racc⟩ a
  have hmin : min v h.2.2.1.length ≤ N := (Nat.min_le_right _ _).trans hL
  rcases a with _ | a
  · show Enc.size (adCombine (h, ((v, w, cur, acc), (r, racc)), none)) ≤ _
    simp only [adCombine, Option.elim]
    split_ifs
    · exact hopen _ _ _ _ hmin (hnorm _) (hnorm _)
    · exact hpos _ _
  · show Enc.size (adCombine (h, ((v, w, cur, acc), (r, racc)), some a)) ≤ _
    simp only [adCombine, Option.elim]
    split_ifs with hw hr
    · have hseg : adSegLen (h, r) ≤ (adKO h).length + (adTW h).length := by
        unfold adSegLen; dsimp only; split_ifs <;> omega
      have hw' : w + 1 ≤ N + MK + MR := by omega
      exact adState_size_le (M := N + MK + MR) (B := N + MB + 2)
        (st := ((min v h.2.2.1.length, w + 1, rawCosetNorm (h.2.2.2.2.1, some a),
          rawCosetNorm (h.2.2.2.2.1, acc)),
          (min r (adRN h), rawCosetNorm (h.2.2.2.2.1, racc))))
        (hmin.trans hMN) hw' (hnorm (some a)) (hnorm acc)
        ((Nat.min_le_right _ _).trans (hRN.trans hMR)) (hnorm racc)
    · exact hopen _ _ _ _ hmin (hnorm _) (hnorm _)
    · exact hpos _ _

theorem tsB_mono_right (A k b n : ℕ) {x y : ℕ} (h : x ≤ y) : tsB A k b n x ≤ tsB A k b n y :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b)

theorem q5_tsB3 {T : ℕ → ℕ} (hT : Q5 T) (A b : ℕ) : Q5 (fun n => tsB A 3 b n (T n)) :=
  ((q5_two_pow_lg A 3 (by norm_num)).mul ((hT.add (q5_const 1)).pow b)).mono
    (fun _ => le_rfl)

theorem q5_polyOf {T : ℕ → ℕ} (hT : Q5 T) (c d : ℕ) : Q5 (fun n => c * (T n + 1) ^ d) :=
  (q5_const c).mul ((hT.add (q5_const 1)).pow d)

/-- **The states of lines 7–11 of Procedure Align, with an explicit exponent.** If the
header has at most `n` points and size at most `2^{c (log₂ n + 2)^5}`, every state of the loop
of lines 5–11 (`Algo.l57Init`, `Algo.l57Step`) and of the loop of Eq. (71) (`Algo.avInit`,
`Algo.avCombine`) has size at most `2^{K (log₂ n + 2)^5}`, whatever the state it starts from. -/
theorem l57_state_q5 (c : ℕ) : ∃ K, ∀ (n : ℕ) (h : AVHdr), AVHdrOK n h →
    Enc.size h ≤ 2 ^ (c * lg n ^ 5) →
    (∀ st a, Enc.size (l57Step (h, st, a)) ≤ 2 ^ (K * lg n ^ 5)) ∧
    Enc.size (l57Init h) ≤ 2 ^ (K * lg n ^ 5) ∧
    Enc.size (avInit h) ≤ 2 ^ (K * lg n ^ 5) ∧
    (∀ st a, Enc.size (avCombine (h, st, a)) ≤ 2 ^ (K * lg n ^ 5)) := by
  obtain ⟨cC, dC, hC⟩ := polyBound_chainBound
  obtain ⟨cK, dK, hK⟩ := polyFun_adKO.size
  obtain ⟨AR, bR, hR⟩ := TN.adRightReps
  obtain ⟨AB, bB, hB⟩ := TN.adBegin
  let X : ℕ → ℕ := fun n => 2 ^ (c * lg n ^ 5)
  let NB : ℕ → ℕ := fun n => X n + cC * (X n + 1) ^ dC
  let MK : ℕ → ℕ := fun n => cK * (X n + 1) ^ dK
  let MR : ℕ → ℕ := fun n => tsB AR 3 bR n (4 * X n)
  let MB : ℕ → ℕ := fun n => tsB AB 3 bB n (2 * X n + 4 * (NB n + 2) + 4 * (MR n + 2))
  let Φ : ℕ → ℕ := fun n => 64 * ((NB n + MK n + MR n) + (NB n + MB n + 2) + 2) +
    32 * (NB n + 2) + 20
  have qX : Q5 X := q5_two_pow_lg c 5 le_rfl
  have qNB : Q5 NB := qX.add (q5_polyOf qX cC dC)
  have qMR : Q5 MR := q5_tsB3 ((q5_const 4).mul qX) AR bR
  have qMB : Q5 MB := q5_tsB3 ((((q5_const 2).mul qX).add ((q5_const 4).mul
    (qNB.add (q5_const 2)))).add ((q5_const 4).mul (qMR.add (q5_const 2)))) AB bB
  have qΦ : Q5 Φ := ((((q5_const 64).mul ((((qNB.add (q5_polyOf qX cK dK)).add qMR).add
    ((qNB.add qMB).add (q5_const 2))).add (q5_const 2))).add
    ((q5_const 32).mul (qNB.add (q5_const 2)))).add (q5_const 20))
  obtain ⟨K, hΦ⟩ := qΦ
  refine ⟨K, fun n h hok hX => ?_⟩
  have hx : h.2.2.2.2.1.length ≤ Enc.size h := length_hdrX_le_size h
  have hX' : Enc.size h ≤ X n := hX
  have hcb : chainBound (Enc.size h) ≤ cC * (X n + 1) ^ dC :=
    (hC _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hN : Enc.size h + chainBound (Enc.size h) ≤ NB n := by
    show _ ≤ X n + _; have : Enc.size h ≤ X n := hX; omega
  have hnorm0 : ∀ a : RawCoset, Enc.size (rawCosetNorm (h.2.2.2.2.1, a)) ≤ NB n :=
    fun a => (size_rawCosetNorm hx a).trans (by omega)
  have hKO : (adKO h).length ≤ MK n :=
    (length_le_size _).trans ((hK h).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
  have hpair : Enc.size ((h.1, h.2.1) : RawAction × RawAlignOutcome) ≤ 4 * X n := by
    have h1 := Combine.size_pair_le h.1 h.2.1
    have h2 := size_fst_le' h
    have h3 := size_snd_le' h
    have h4 := size_fst_le' h.2
    have : Enc.size h ≤ X n := hX
    omega
  have hRN : adRN h ≤ MR n :=
    (length_le_size _).trans ((hR.size n (h.1, h.2.1) hok).trans
      (tsB_mono_right _ _ _ _ hpair))
  have hbeg : ∀ v r, v ≤ NB n → r ≤ MR n → Enc.size (adBegin (h, v, r)) ≤ MB n := by
    intro v r hv hr
    refine (hB.size n (h, v, r) hok).trans (tsB_mono_right _ _ _ _ ?_)
    have h1 := Combine.size_pair_le h (v, r)
    have h2 := Combine.size_pair_le v r
    have h3 := size_nat_le2 hv
    have h4 := size_nat_le2 hr
    have : Enc.size h ≤ X n := hX
    omega
  obtain ⟨hpos, hcomb⟩ := adStep_size_of h (N := NB n) (by omega) hnorm0 hKO hRN hbeg
  have hΦn := hΦ n
  have h0 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl
  have h5 : Enc.size (none : RawCoset) = 2 := size_none
  have hp3 := Combine.size_pair_le (0 : ℕ) (none : RawCoset)
  refine ⟨fun st a => ?_, ?_, ?_, fun st a => ?_⟩
  · unfold l57Step
    split_ifs
    · have := hcomb st a
      show _ ≤ _
      dsimp only [Φ] at hΦn
      omega
    · have h1 := avCombine_size (h, st.1, a) hx
      have h2 := Combine.size_pair_le (avCombine (h, st.1, a)) ((0, none) : ℕ × RawCoset)
      dsimp only at h1 ⊢
      dsimp only [Φ] at hΦn
      omega
  · unfold l57Init
    split_ifs
    · have := hpos 0 none
      unfold adInit
      dsimp only [Φ] at hΦn
      omega
    · have h1 := avInit_size h hx
      have h2 := Combine.size_pair_le (avInit h) ((0, none) : ℕ × RawCoset)
      dsimp only [Φ] at hΦn
      omega
  · have h1 := avInit_size h hx
    dsimp only [Φ] at hΦn
    omega
  · have h1 := avCombine_size (h, st, a) hx
    dsimp only at h1
    dsimp only [Φ] at hΦn
    omega

end Explicit
