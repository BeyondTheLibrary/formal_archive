/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the calls of one
node of the variant Master round at route 4 (lines 4c–4d). Not part of the faithful
formalization.
-/
import Workspace.Explicit.NodeCalls
import Workspace.Explicit.Sec9Family
import Workspace.Algo.PrimitiveLine4dDomData
import Workspace.Luks.JohnsonBarrier

/-!
# The calls of a node at route 4 (lines 4c–4d)

The width at route 4 is the number of versions of `X(y)` times a count of windows and
cosets that is read off the data. The versions are the outcomes of Theorem 9.2.3 on the
structure `H(y)` (Sec. 14.2), a represented input of Theorem 9.2.3 on the `m` points of `Γ`
of arity `t` (`Algo.extendedInputRep_line4c`), so there are at most
`(m+1)^t · (m (B m+1) + 1)` of them (`Explicit.extendedSplitFamily_length_le`), and
`2^t ≤ C(m,t) = |Ω|` gives `t ≤ log₂ |Ω|`. The other factors are at most
`2^{2(log₂ n+2)^3}·n + 2n + 1`: the kernel orbits and the color classes are at most `n`, and
the coset representatives of the dominant case at most `(g+1)^g + 1` with
`g = (log₂ n + 1)^2` the guard of the table of `m*`-tuples.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open Algo RAM Babai Equiv

/-! ## The versions of `X(y)` -/

theorem ys_arith {n m t : ℕ} (hm : m ≤ n) (ht : 2 ^ t ≤ n) :
    (m + 1) ^ t * (m * (outBound m + 1) + 1) ≤ 2 ^ (48 * lg n ^ 3) := by
  set L := lg n with hL
  have hL2 : 2 ≤ L := two_le_lg n
  have hn1 : n + 1 ≤ 2 ^ L := succ_le_two_pow_lg n
  have htL : t ≤ L := by
    have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := t); omega
    have := Nat.le_log_of_pow_le (by norm_num) ht
    show t ≤ Nat.log 2 n + 2
    omega
  have h1 : (m + 1) ^ t ≤ 2 ^ (L * L) :=
    (Nat.pow_le_pow_left (by omega : m + 1 ≤ 2 ^ L) t).trans
      (by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ htL))
  have hB : outBound m + 1 ≤ 2 ^ (45 * L ^ 3 + 1) := by
    have := outBound_mono hm
    have e : outBound n = 2 ^ (45 * L ^ 3) := rfl
    rw [pow_succ]
    have : 1 ≤ 2 ^ (45 * L ^ 3) := Nat.one_le_two_pow
    omega
  have h2 : m * (outBound m + 1) + 1 ≤ 2 ^ (L + 45 * L ^ 3 + 1) := by
    have hm1 : m + 1 ≤ 2 ^ L := by omega
    calc m * (outBound m + 1) + 1 ≤ (m + 1) * (outBound m + 1) := by nlinarith
      _ ≤ 2 ^ L * 2 ^ (45 * L ^ 3 + 1) := Nat.mul_le_mul hm1 hB
      _ = 2 ^ (L + 45 * L ^ 3 + 1) := by rw [← pow_add]; ring_nf
  have hLL : L * L ≤ L ^ 3 := by
    calc L * L = L ^ 2 := (sq L).symm
      _ ≤ L ^ 3 := lg_pow_le_lg_pow (by norm_num) n
  have hL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := lg_pow_le_lg_pow (by norm_num) n
  have h13 : 1 ≤ L ^ 3 := one_le_lg_pow n 3
  calc (m + 1) ^ t * (m * (outBound m + 1) + 1) ≤ 2 ^ (L * L) * 2 ^ (L + 45 * L ^ 3 + 1) :=
        Nat.mul_le_mul h1 h2
    _ = 2 ^ (L * L + (L + 45 * L ^ 3 + 1)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (48 * L ^ 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The versions of `X(y)` at a good node of route 4**: at most `2^{48 (log₂ |Ω|+2)^3}`. -/
theorem line4dYs_length_le {tt dd : ℕ} (he : SbipExact tt dd) {q : MasterHintInput}
    (hg : MasterHintGood q) (hr : masterHintRoute q = 4) :
    (line4dYs 0 tt dd q).length ≤ 2 ^ (48 * lg q.1.1.length ^ 3) := by
  obtain ⟨m, ϕ, B, hB, hp, hG, hϕ, -, -, -, -, -, hn⟩ := hg
  obtain ⟨hvl, id, ht2, -, hmn, -⟩ := masterLine4c_facts q hp hG hϕ hn hr
  unfold line4dYs
  split_ifs with hsd
  · exact Nat.zero_le _
  · refine (length_rawVersDedup_le _).trans ?_
    set A := (masterHintTop q).1 with hA
    set x := (masterHintTop q).2.1
    set y := (masterHintTop q).2.2
    have hdef := fun hlt => hsd ((primitiveSmallDefect_iff hp hϕ hvl id y).2 hlt)
    have hrep : ExtendedInputRep 1 m (line4cAmbient (((A, x, y), q.2.2), y)) :=
      extendedInputRep_line4c hp hϕ hvl id x y y (Or.inr rfl) ht2 hdef
    have hlen := line4cArity_length hp id x y
    have hc := extendedSplitFamily_length_le he hrep
    change (extendedSplitFamily 1 0 tt dd (line4cAmbient (((A, x, y), q.2.2), y))).length ≤ _
    refine hc.trans ?_
    change (m + 1) ^ (line4cArity ((A, x, y), q.2.2)).length * _ ≤ _
    rw [hlen]
    have hcard : q.1.1.length = m.choose q.2.2 := by
      have he := Nat.card_congr id.label
      rw [card_binom (Fin m) q.2.2] at he
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using he
    have hfour : 4 * q.2.2 < m := by simpa only [Fintype.card_fin] using id.four_t
    have ht : 2 ^ q.2.2 ≤ q.1.1.length := by
      rw [hcard]; exact two_pow_le_choose (by omega)
    exact ys_arith hmn ht


/-! ## The windows and the cosets -/

theorem length_alignRWindows_le (q : RawAction × RawLab) :
    (alignRWindows q).length ≤ q.1.1.1.length + 1 := by
  have h := length_alignRClasses_le q
  unfold alignRWindows
  split_ifs
  · simp only [List.length_cons]
    exact Nat.add_le_add_right ((List.length_filter_le _ _).trans h) 1
  · omega

theorem length_alignRDomWindow_le (z : (RawAction × RawLab) × ℕ) :
    (alignRDomWindow z).length ≤ z.1.1.1.1.length := by
  unfold alignRDomWindow
  exact (List.length_filter_le _ _).trans (by simp)

theorem length_alignDomOrbits_le (x : (RawGens × List ℕ) × ℕ) :
    (alignDomOrbits x).length ≤ x.1.2.length := by
  unfold alignDomOrbits
  rw [(perm_alignDomFirst _).length_eq]
  exact length_winOrbits_le _ _

theorem length_alignL57Windows_le (p : RawAction × RawAlignOutcome) :
    (alignL57Windows p).length ≤ 2 * p.1.1.1.length + 1 := by
  have hw := length_alignRWindows_le (alignRColorOf p)
  change _ ≤ p.1.1.1.length + 1 at hw
  unfold alignL57Windows
  split_ifs
  · rw [List.length_append, List.length_tail]
    have h1 := length_alignDomOrbits_le ((alignPairG1 p,
        alignRDomWindow (alignRColorOf p, alignRDomColor (alignRColorOf p))), p.1.1.1.length)
    have h2 := length_alignRDomWindow_le (alignRColorOf p, alignRDomColor (alignRColorOf p))
    change _ ≤ p.1.1.1.length at h2
    dsimp only at h1
    omega
  · omega

theorem length_aggTable_le_guard (c : ℕ) (a : RawAggTestInput) :
    (aggTable c a).2.length ≤
      if a.1.length ≤ guardBound c a.2.1.length then (a.2.2.length + 1) ^ a.1.length else 0 := by
  split_ifs with hg
  · exact length_aggTable_le c a
  · unfold aggTable aggTabSetUp
    rw [if_neg hg]
    simp [length_tabRead]

theorem length_cosetAdd_le {c : CosetParam} {reps : RawGens} (x : RawPerm)
    (h : reps.length ≤ c.2.2.length + 1) :
    (cosetAdd (c, (reps, x))).length ≤ c.2.2.length + 1 := by
  unfold cosetAdd cosetNew
  split_ifs with hn
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    simp only [List.length_append, List.length_singleton]
    omega
  · exact h

theorem length_cosetRound_le {c : CosetParam} {reps : RawGens}
    (h : reps.length ≤ c.2.2.length + 1) :
    (cosetRound (c, reps)).length ≤ c.2.2.length + 1 := by
  unfold cosetRound
  generalize cosetCands (reps, c.1.2) = l
  induction l generalizing reps with
  | nil => exact h
  | cons x l ih =>
    rw [List.foldl_cons]
    exact ih (length_cosetAdd_le x h)

/-- The coset search lists at most one representative more than its fuel. -/
theorem length_rawCosetReps_le (c : CosetParam) :
    (rawCosetReps c).length ≤ c.2.2.length + 1 := by
  unfold rawCosetReps
  have h0 : [rawOne c.1.1].length ≤ c.2.2.length + 1 := by simp
  generalize [rawOne c.1.1] = reps at h0
  generalize hjs : c.2.2 = js
  rw [hjs] at h0
  have key : ∀ (l : List ℕ) (reps : RawGens), reps.length ≤ js.length + 1 →
      (List.foldl (fun reps _ => cosetRound (c, reps)) reps l).length ≤ js.length + 1 := by
    intro l
    induction l with
    | nil => intro reps h; exact h
    | cons x l ih =>
      intro reps h
      rw [List.foldl_cons]
      exact ih _ (by rw [← hjs]; exact length_cosetRound_le (by rw [hjs]; exact h))
  exact key js reps h0

theorem length_adFuel_le (p : RawAction × RawAlignOutcome) :
    (adFuel p).length ≤ (guardBound 2 p.1.1.1.length + 1) ^ guardBound 2 p.1.1.1.length := by
  unfold adFuel
  rw [List.length_map]
  refine (length_aggTable_le_guard 2 _).trans ?_
  dsimp only
  split_ifs with hg
  · exact (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hg)
  · exact Nat.zero_le _

theorem adRN_le (h : AVHdr) :
    adRN h ≤ (guardBound 2 h.1.1.1.length + 1) ^ guardBound 2 h.1.1.1.length + 1 := by
  unfold adRN adRightReps
  exact (length_rawCosetReps_le _).trans (Nat.add_le_add_right (length_adFuel_le _) 1)

theorem length_adKO_le (h : AVHdr) : (adKO h).length ≤ h.1.1.1.length := by
  unfold adKO alignKerOrbits
  exact (length_winOrbits_le _ _).trans (length_alignRDomWindow_le _)


/-! ## The width at route 4 -/

/-- The factor of the width besides the versions: `((g+1)^g + 1)·w + 2w + 1` with `w` the
size of the window and `g = (log₂ w + 1)^2`. -/
def l4Factor (w : ℕ) : ℕ :=
  ((guardBound 2 w + 1) ^ guardBound 2 w + 1) * w + 2 * w + 1

theorem avCalls_le_of (h : AVHdr) (hw : h.2.2.2.1.length ≤ 2 * h.1.1.1.length + 1) :
    avCalls h ≤ h.2.2.1.length * l4Factor h.1.1.1.length := by
  unfold avCalls l4Factor
  refine Nat.mul_le_mul_left _ (hw.trans ?_)
  have : 0 ≤ ((guardBound 2 h.1.1.1.length + 1) ^ guardBound 2 h.1.1.1.length + 1) *
    h.1.1.1.length := Nat.zero_le _
  omega

theorem adCalls_le_of (h : AVHdr) (hw : h.2.2.2.1.length ≤ 2 * h.1.1.1.length + 1) :
    adCalls h ≤ h.2.2.1.length * l4Factor h.1.1.1.length := by
  unfold adCalls l4Factor
  refine Nat.mul_le_mul_left _ ?_
  have h1 := Nat.mul_le_mul (adRN_le h) (length_adKO_le h)
  have h2 : (adTW h).length ≤ 2 * h.1.1.1.length + 1 := by
    unfold adTW; rw [List.length_tail]; omega
  omega

theorem l4Factor_le (w : ℕ) : l4Factor w ≤ 2 ^ (5 * lg w ^ 3) := by
  set L := lg w with hL
  have hL2 : 2 ≤ L := two_le_lg w
  have hw1 : w + 1 ≤ 2 ^ L := succ_le_two_pow_lg w
  set g := guardBound 2 w with hg
  have hgL : g ≤ L ^ 2 := by
    show (Nat.log 2 w + 1) ^ 2 ≤ L ^ 2
    exact Nat.pow_le_pow_left (by show Nat.log 2 w + 1 ≤ Nat.log 2 w + 2; omega) 2
  have hL1 : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
  have hsq : L ^ 2 + 1 ≤ 2 ^ (L * 2) := by
    have : (L + 1) ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left hL1 2
    rw [← pow_mul] at this
    nlinarith
  have hA : (g + 1) ^ g ≤ 2 ^ (2 * L ^ 3) := by
    refine (Nat.pow_le_pow_left (by omega : g + 1 ≤ 2 ^ (L * 2)) g).trans ?_
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    calc L * 2 * g ≤ L * 2 * L ^ 2 := Nat.mul_le_mul_left _ hgL
      _ = 2 * L ^ 3 := by ring
  have h1 : 1 ≤ 2 ^ (2 * L ^ 3) := Nat.one_le_two_pow
  have hX : l4Factor w ≤ 2 ^ (2 * L ^ 3 + 2) * 2 ^ L := by
    unfold l4Factor
    rw [← hg]
    have e : 2 ^ (2 * L ^ 3 + 2) = 4 * 2 ^ (2 * L ^ 3) := by rw [pow_add]; ring
    rw [e]
    have h3 : ((g + 1) ^ g + 1) * w ≤ (2 ^ (2 * L ^ 3) + 1) * w := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  refine hX.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have hL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := lg_pow_le_lg_pow (by norm_num) w
  have h13 : 1 ≤ L ^ 3 := one_le_lg_pow w 3
  omega

/-- **The width at route 4** (lines 4c–4d) at a good, well-formed node:
`2^{53 (log₂ n+2)^3}`. -/
theorem widthE_route4_le {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (he : SbipExact p.tt p.dd) {n : ℕ} {P : RawMasterSI} (hG : MasterNodeGood n P)
    (hW : MasterInputWF p.a p.b P) (hr : masterRoute P = 4) :
    (masterRoundE p cam).width P ≤ 2 ^ (53 * lg (masterDegree P) ^ 3) := by
  rw [widthE_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hr]
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact absurd hr (by simp [masterRoute])
  | some h =>
    have hg : MasterHintGood (W, h) := hG.2 h rfl
    have hr' : masterHintRoute (W, h) = 4 := hr
    have hY := line4dYs_length_le he hg hr'
    have hwn : W.1.length ≤ masterDegree ((W, some h) : RawMasterSI) := hW.2.1
    set w := W.1.length with hw
    have hF := l4Factor_le w
    have hmono : lg w ≤ lg (masterDegree ((W, some h) : RawMasterSI)) := lg_mono hwn
    have hbound : (line4dYs 0 p.tt p.dd (W, h)).length * l4Factor w ≤
        2 ^ (53 * lg (masterDegree ((W, some h) : RawMasterSI)) ^ 3) := by
      refine (Nat.mul_le_mul hY hF).trans ?_
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      have := Nat.pow_le_pow_left hmono 3
      change 48 * lg w ^ 3 + 5 * lg w ^ 3 ≤ _
      omega
    change (if masterHasDom 0 p.tt p.dd (W, some h) then
      l57Calls (line4dDomHdr 0 p.tt p.dd (W, h)) else avCalls (line4dHdr 0 p.tt p.dd (W, h))) ≤ _
    split_ifs
    · unfold l57Calls
      split_ifs
      · exact (adCalls_le_of _ (length_alignL57Windows_le _)).trans hbound
      · exact (avCalls_le_of _ (length_alignL57Windows_le _)).trans hbound
    · refine (avCalls_le_of _ ?_).trans hbound
      have := length_alignRWindows_le ((masterHintTop (W, h)).1, line4dLab 0 p.tt p.dd (W, h))
      change _ ≤ W.1.length + 1 at this
      change (alignRWindows ((masterHintTop (W, h)).1, line4dLab 0 p.tt p.dd (W, h))).length ≤
        2 * W.1.length + 1
      omega

end Explicit
