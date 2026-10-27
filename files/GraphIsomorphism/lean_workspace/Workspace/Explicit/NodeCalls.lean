/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: the calls of one
node of the variant Master round, routes 0–3. Not part of the faithful formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Explicit.Top.Count
import Workspace.Explicit.Sec9Width
import Workspace.Explicit.NodeBound

/-!
# The calls of a node, routes 0–3

The calls of the run at a node are at most the width of the node
(`Explicit.length_roundCalls_le_width`). At routes 0–3 the width itself is small at a good
node, so the width bound is enough:

* route 0 (line 1, Sec. 11.3): the two leaves ask nothing; the Chain Rule asks one call per
  orbit of the window (`≤ n`); the block route runs the descent fold on the block action
  with at most `min(#keys, |image|)` representatives per window orbit, and the route is taken
  only when the block system has fewer than `B` blocks or the image is smaller than
  `|blocks|^{1+⌈log |blocks|⌉}`; Cameron's route asks at most `n` calls per window orbit;
* route 1 (line 2): the descent fold on the hint's Johnson action of degree
  `m ≤ ℓ = (log₂ n)^3`, so at most `((m+1)^m + (n+1)^{log₂ n+2}) · n` calls, which is
  `2^{O((log₂ n+2)^4)}`;
* route 2: a leaf;
* route 3 (line 4b): the width of the line-4b context, polynomial in `n`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open Algo RAM Babai

variable {p : Params} {cam : RawGens × List ℕ → Option RawCameron}

/-! ## The width, route by route -/

theorem widthE_eq (P : RawMasterSI) : (masterRoundE p cam).width P =
    if masterRoute P = 0 then (masterLine1Ops p.B p.C₀ cam).width P
    else if masterRoute P = 1 then masterDescOpenWidth 3 (masterDescPreparedSelect P)
    else if masterRoute P = 2 then 0
    else if masterRoute P = 3 then (master4bOps p.e p.f p.u p.v).width P
    else if masterRoute P = 4 then
      (masterLine4cdOps 0 p.tt p.dd (line4dDomOps 0 p.tt p.dd) default).width P
    else (masterL57Ops 2 0 p.t p.d p.dc p.dp p.e p.f p.E).width P := by
  simp only [masterRoundE, masterAdmittedRound, masterOpsE, masterNodeHOps, masterTopOps,
    masterHintOps, masterLine4cdOps, MasterOps.pairIte, MasterOps.withHint_width,
    masterIsLine1, masterRouteAt, decide_eq_true_eq]
  split_ifs <;> rfl


/-! ## Arithmetic -/

theorem succ_le_two_pow_lg (n : ℕ) : n + 1 ≤ 2 ^ lg n := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have h2 : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ lg n := Nat.pow_le_pow_right (by norm_num) (by unfold lg; omega)
  omega

theorem pow_le_two_pow_mul {a x : ℕ} (h : a ≤ 2 ^ x) (y : ℕ) : a ^ y ≤ 2 ^ (x * y) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left h y

theorem two_pow_add_two_pow_le (a b : ℕ) : 2 ^ a + 2 ^ b ≤ 2 ^ (a + b + 1) := by
  have ha : 2 ^ a ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : 2 ^ b ≤ 2 ^ (a + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem poly_le_two_pow_lg (c d n : ℕ) : c * (n + 1) ^ d ≤ 2 ^ ((c + d) * lg n) := by
  have hc : c ≤ 2 ^ (c * lg n) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right _ (by have := two_le_lg n; omega)))
  have hn : (n + 1) ^ d ≤ 2 ^ (lg n * d) := pow_le_two_pow_mul (succ_le_two_pow_lg n) d
  calc c * (n + 1) ^ d ≤ 2 ^ (c * lg n) * 2 ^ (lg n * d) := Nat.mul_le_mul hc hn
    _ = 2 ^ ((c + d) * lg n) := by rw [← pow_add]; congr 1; ring

theorem lg_pow_le_lg_pow {k k' : ℕ} (h : k ≤ k') (n : ℕ) : lg n ^ k ≤ lg n ^ k' :=
  Nat.pow_le_pow_right (by have := two_le_lg n; omega) h

/-! ## The descent fold -/

theorem length_masterDescKeys_le (c : ℕ) (q : MasterDescInput) :
    (masterDescKeys c q).length ≤ (q.2.1.length + 1) ^ q.2.1.length +
      (q.1.2.2.2.1.length + 1) ^ (Nat.log 2 q.1.2.2.2.1.length + 2) := by
  unfold masterDescKeys
  rw [List.length_append]
  refine Nat.add_le_add (length_aggTable_le c _) ((length_aggTable_le 2 _).trans ?_)
  simp only [rawOne, List.length_range, masterDescArity, List.length_take]
  exact Nat.pow_le_pow_right (Nat.succ_pos _) (min_le_left _ _)

/-- The width of the descent fold: at most `min(#keys, |image|)` representatives, each
followed by one call per orbit of the kernel on the window. -/
theorem masterDescOpenWidth_le (c : ℕ) (q : MasterDescInput) :
    masterDescOpenWidth c q ≤ min (masterDescKeys c q).length (rawOrder q.2) * q.1.1.length := by
  unfold masterDescOpenWidth masterDescFoldWidth aggnrCount aggnrWindows masterDescLists
    masterDescReps masterDescFuel masterDescWidth
  simp only [List.length_map, List.length_take, List.length_range]
  exact Nat.mul_le_mul (by omega) (length_winOrbits_le _ _)


/-! ## Route 1 (line 2) -/

theorem masterHintRoute_eq_one {q : MasterHintInput} (h : masterHintRoute q = 1) :
    q.2.1.1.length ≤ ellOf q.1.1.length := by
  unfold masterHintRoute at h
  split_ifs at h with h1 <;> first | exact h1 | omega

/-- The arithmetic of line 2: `((m+1)^m + (n+1)^{log n+2}) · w ≤ 2^{6 (log n+2)^4}` for
`m ≤ (log n)^3` and `w ≤ n`. -/
theorem line2_arith {n m w K : ℕ} (hw : w ≤ n) (hm : m ≤ Nat.log 2 n ^ 3)
    (hK : K ≤ (m + 1) ^ m + (n + 1) ^ (Nat.log 2 n + 2)) :
    K * w ≤ 2 ^ (6 * lg n ^ 4) := by
  set L := lg n with hL
  have hL2 : 2 ≤ L := two_le_lg n
  have hlog : Nat.log 2 n + 2 = L := rfl
  have h3 : Nat.log 2 n ^ 3 < L ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hm1 : m + 1 ≤ 2 ^ (L * 3) :=
    (show m + 1 ≤ L ^ 3 by omega).trans (pow_le_two_pow_mul (Nat.lt_two_pow_self).le 3)
  have hA : (m + 1) ^ m ≤ 2 ^ (3 * L ^ 4) := by
    refine (pow_le_two_pow_mul hm1 m).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    have : L * 3 * m ≤ L * 3 * L ^ 3 := Nat.mul_le_mul_left _ (by omega)
    calc L * 3 * m ≤ L * 3 * L ^ 3 := this
      _ = 3 * L ^ 4 := by ring
  have hB : (n + 1) ^ (Nat.log 2 n + 2) ≤ 2 ^ (L * L) := by
    rw [hlog]; exact pow_le_two_pow_mul (succ_le_two_pow_lg n) L
  have hW : w ≤ 2 ^ L := (Nat.le_succ_of_le hw).trans (succ_le_two_pow_lg n)
  have hsum : K ≤ 2 ^ (3 * L ^ 4 + L * L + 1) :=
    hK.trans ((Nat.add_le_add hA hB).trans (two_pow_add_two_pow_le _ _))
  have h4 : L ≤ L ^ 4 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 4 := lg_pow_le_lg_pow (by norm_num) n
  have h2 : L * L ≤ L ^ 4 := by
    calc L * L = L ^ 2 := (sq L).symm
      _ ≤ L ^ 4 := lg_pow_le_lg_pow (by norm_num) n
  have h1 : 1 ≤ L ^ 4 := one_le_lg_pow n 4
  calc K * w ≤ 2 ^ (3 * L ^ 4 + L * L + 1) * 2 ^ L := Nat.mul_le_mul hsum hW
    _ = 2 ^ (3 * L ^ 4 + L * L + 1 + L) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (6 * L ^ 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The width at route 1 (line 2).** -/
theorem widthE_route1_le {P : RawMasterSI} (hW : MasterInputWF p.a p.b P)
    (hr : masterRoute P = 1) :
    (masterRoundE p cam).width P ≤ 2 ^ (6 * lg (masterDegree P) ^ 4) := by
  rw [widthE_eq, if_neg (by omega), if_pos hr]
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact absurd hr (by simp [masterRoute])
  | some h =>
    have hm : h.1.1.length ≤ ellOf W.1.length := masterHintRoute_eq_one (q := (W, h)) hr
    have hwn : W.1.length ≤ W.2.2.2.1.length := hW.2.1
    have hm' : h.1.1.length ≤ Nat.log 2 W.2.2.2.1.length ^ 3 :=
      hm.trans (Nat.pow_le_pow_left (Nat.log_mono_right hwn) 3)
    refine (masterDescOpenWidth_le 3 _).trans ?_
    exact line2_arith hwn hm' ((min_le_left _ _).trans (length_masterDescKeys_le 3 _))


/-! ## Polynomial bounds in the form `2^{Y (log₂ n + 2)}` -/

theorem polyBound_le_two_pow_lg {T : ℕ → ℕ} (h : PolyBound T) :
    ∃ Y, ∀ n, T n ≤ 2 ^ (Y * lg n) := by
  obtain ⟨c, d, hcd⟩ := h
  exact ⟨c + d, fun n => (hcd n).trans (poly_le_two_pow_lg c d n)⟩

theorem poly_comp_two_pow_lg {n x Y : ℕ} (hx : x ≤ 2 ^ (Y * lg n)) (c d : ℕ) :
    c * (x + 1) ^ d ≤ 2 ^ ((c + d * (Y + 1)) * lg n) := by
  have hL := two_le_lg n
  have hc : c ≤ 2 ^ (c * lg n) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right _ (by omega)))
  have hx1 : x + 1 ≤ 2 ^ ((Y + 1) * lg n) := by
    have h1 : 1 ≤ 2 ^ (Y * lg n) := Nat.one_le_two_pow
    have h2 : 2 ^ (Y * lg n) * 2 ≤ 2 ^ ((Y + 1) * lg n) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  calc c * (x + 1) ^ d ≤ 2 ^ (c * lg n) * 2 ^ ((Y + 1) * lg n * d) :=
        Nat.mul_le_mul hc (pow_le_two_pow_mul hx1 d)
    _ = 2 ^ ((c + d * (Y + 1)) * lg n) := by rw [← pow_add]; congr 1; ring

theorem exists_size_le_of_wf (a b : ℕ) :
    ∃ Y, ∀ P, MasterInputWF a b P → Enc.size P ≤ 2 ^ (Y * lg (masterDegree P)) := by
  obtain ⟨Y, hY⟩ := polyBound_le_two_pow_lg (polyBound_masterInputCap a b)
  exact ⟨Y, fun P hP => hP.1.trans (hY _)⟩

/-! ## Route 0 (line 1) -/

/-- The block route: fewer than `B` blocks, or an image smaller than
`|blocks|^{1+⌈log₂ |blocks|⌉}`. -/
theorem exists_blockWidth_le (a b B : ℕ) :
    ∃ A, ∀ P : RawMasterSI, MasterInputWF a b P →
      ((masterBlockGroup P.1).2.length < B ∨ masterSmallOrder (masterBlockGroup P.1) = true) →
      masterBlockOps.width P ≤ 2 ^ (A * lg (masterDegree P) ^ 2) := by
  obtain ⟨Y, hY⟩ := exists_size_le_of_wf a b
  obtain ⟨c, d, hcd⟩ := polyFun_masterWindowBlockAction.size
  set Z := c + d * (Y + 1) with hZ
  refine ⟨B * B + Z * (Z + 2) + 3, fun P hP hroute => ?_⟩
  set n := masterDegree P with hn
  set L := lg n with hL
  have hL2 : 2 ≤ L := two_le_lg n
  have hwn : P.1.1.length ≤ n := hP.2.1
  have hW : P.1.1.length ≤ 2 ^ L := (Nat.le_succ_of_le hwn).trans (succ_le_two_pow_lg n)
  have hq := masterDescOpenWidth_le 3 (masterBlockSelect P)
  change masterDescOpenWidth 3 (masterBlockSelect P) ≤ _
  set k := (masterWindowBlockAction P.1).2.1.length with hk
  have hLL : L ≤ L ^ 2 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 2 := lg_pow_le_lg_pow (by norm_num) n
  rcases hroute with hB | hsmall
  · -- fewer than `B` blocks: the image-domain table has at most `B^B` rows
    have hkB : k < B := hB
    have hK := length_masterDescKeys_le 3 (masterBlockSelect P)
    change _ ≤ (k + 1) ^ k + (n + 1) ^ (Nat.log 2 n + 2) at hK
    have hA : (k + 1) ^ k ≤ 2 ^ (B * B) := by
      calc (k + 1) ^ k ≤ B ^ B := (Nat.pow_le_pow_left (by omega) k).trans
            (Nat.pow_le_pow_right (by omega) hkB.le)
        _ ≤ (2 ^ B) ^ B := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le B
        _ = 2 ^ (B * B) := (pow_mul 2 B B).symm
    have hBn : (n + 1) ^ (Nat.log 2 n + 2) ≤ 2 ^ (L * L) :=
      pow_le_two_pow_mul (succ_le_two_pow_lg n) L
    have hsum := (Nat.add_le_add hA hBn).trans (two_pow_add_two_pow_le _ _)
    refine hq.trans ((Nat.mul_le_mul ((min_le_left _ _).trans (hK.trans hsum)) hW).trans ?_)
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : 1 ≤ L ^ 2 := one_le_lg_pow n 2
    have h2 : L * L = L ^ 2 := (sq L).symm
    have h3 : B * B ≤ B * B * L ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    have e : (B * B + Z * (Z + 2) + 3) * L ^ 2 = B * B * L ^ 2 + Z * (Z + 2) * L ^ 2 + 3 * L ^ 2 := by
      ring
    omega
  · -- a small image
    have hsize : Enc.size (masterWindowBlockAction P.1) ≤ 2 ^ (Z * L) := by
      have h1 := hcd P.1
      have h2 : Enc.size P.1 ≤ 2 ^ (Y * L) := (size_fst_le' P).trans (hY P hP)
      exact h1.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)).trans
        (poly_comp_two_pow_lg h2 c d))
    have hkZ : k ≤ 2 ^ (Z * L) := by
      refine le_trans ?_ hsize
      refine (length_le_size _).trans ?_
      exact (size_fst_le' _).trans ((size_snd_le' _).trans le_rfl)
    have hord : rawOrder (masterBlockSelect P).2 < masterOrderCap (masterWindowBlockAction P.1).2.1 := by
      simpa [masterSmallOrder, masterBlockGroup] using hsmall
    have hlogk : Nat.log 2 k ≤ Z * L := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0]; simp
      · calc Nat.log 2 k ≤ Nat.log 2 (2 ^ (Z * L)) := Nat.log_mono_right hkZ
          _ = Z * L := Nat.log_pow (by norm_num) _
    have hcap : masterOrderCap (masterWindowBlockAction P.1).2.1 ≤ 2 ^ (Z * L * (Z * L + 2)) := by
      unfold masterOrderCap
      rw [← hk]
      refine (pow_le_two_pow_mul hkZ _).trans (Nat.pow_le_pow_right (by norm_num) ?_)
      have := masterClog_le k
      exact Nat.mul_le_mul_left _ (by omega)
    refine hq.trans ((Nat.mul_le_mul ((min_le_right _ _).trans (hord.le.trans hcap)) hW).trans ?_)
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have e : Z * L * (Z * L + 2) = Z * Z * L ^ 2 + 2 * Z * L := by ring
    have h2 : 2 * Z * L ≤ 2 * Z * L ^ 2 := Nat.mul_le_mul_left _ hLL
    nlinarith


/-- Cameron's route: at most `n` calls per window orbit. -/
theorem camWidth_le (cam : RawGens × List ℕ → Option RawCameron) (P : RawMasterSI) :
    (masterCamPreparedOps (masterCamRouteInput cam)).width P ≤
      masterDegree P * P.1.1.length + masterDegree P := by
  set q := masterCamPrepared (masterCamRouteInput cam P) with hq
  have hx : masterCamOpenWidth q ≤ masterDegree P := min_le_right _ _
  change (if masterCamHasHint q then masterCamOpenWidth q
    else masterDescFoldWidth (masterCamLists q)) ≤ _
  split_ifs
  · omega
  · unfold masterDescFoldWidth aggnrCount aggnrWindows masterCamLists masterCamReps masterCamFuel
    simp only [List.length_map, List.length_take]
    have h1 := length_winOrbits_le (camLiftGens (q.1, masterDescAction q.2)) q.2.1.1
    have h2 : min (masterCamOpenWidth q) (rawOne q.2.1.2.2.2.1).length ≤ masterDegree P :=
      (min_le_left _ _).trans hx
    have h3 := Nat.mul_le_mul h2 h1
    change _ ≤ masterDegree P * P.1.1.length at h3
    omega

/-- **The width at route 0 (line 1).** -/
theorem exists_line1Width_le (a b B C₀ : ℕ) (cam : RawGens × List ℕ → Option RawCameron) :
    ∃ A, ∀ P : RawMasterSI, MasterInputWF a b P →
      (masterLine1Ops B C₀ cam).width P ≤ 2 ^ (A * lg (masterDegree P) ^ 2) := by
  obtain ⟨A, hA⟩ := exists_blockWidth_le a b B
  refine ⟨A + 2, fun P hP => ?_⟩
  set n := masterDegree P with hn
  set L := lg n with hL
  have hL2 : 2 ≤ L := two_le_lg n
  have hwn : P.1.1.length ≤ n := hP.2.1
  have hn2 : n + 1 ≤ 2 ^ L := succ_le_two_pow_lg n
  have hmono : ∀ x, x ≤ 2 ^ (A * L ^ 2) → x ≤ 2 ^ ((A + 2) * L ^ 2) := fun x h =>
    h.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega)))
  have hsq : n * P.1.1.length + n ≤ 2 ^ ((A + 2) * L ^ 2) := by
    have h1 : n * P.1.1.length + n ≤ (n + 1) * (n + 1) := by nlinarith
    have h2 : (n + 1) * (n + 1) ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hn2 hn2
    have h3 : 2 ^ L * 2 ^ L = 2 ^ (2 * L) := by rw [← pow_add]; ring_nf
    have h4 : 2 * L ≤ (A + 2) * L ^ 2 := by nlinarith
    have h5 : 2 ^ (2 * L) ≤ 2 ^ ((A + 2) * L ^ 2) := Nat.pow_le_pow_right (by norm_num) h4
    omega
  simp only [masterLine1Ops, MasterOps.ite, masterRouteIs, decide_eq_true_eq]
  split_ifs with h0 h1 h2 h3
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact (length_winOrbits_le _ _).trans (hwn.trans (by omega))
  · refine hmono _ (hA P hP ?_)
    unfold masterReduceRoute at h3
    split_ifs at h3 with g1 g2 g3 g4 g5 <;> first | omega | exact Or.inl g4 | exact Or.inr g5
  · exact (camWidth_le cam P).trans hsq

/-! ## Route 3 (line 4b) -/

theorem exists_line4bWidth_le (a b e f u v : ℕ) :
    ∃ A, ∀ P : RawMasterSI, MasterInputWF a b P →
      (master4bOps e f u v).width P ≤ 2 ^ (A * lg (masterDegree P)) := by
  obtain ⟨c, d, hb⟩ := master4Open_uniform_bounds a b
  obtain ⟨A, hA⟩ := polyBound_le_two_pow_lg (polyBound_master4OpenWidthBound c d)
  refine ⟨A, fun P hP => ?_⟩
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact Nat.zero_le _
  | some h =>
    change master4OpenWidth (W, h) ≤ _
    exact ((hb (W, h) hP).2.2).trans (hA _)

/-! ## Routes 0, 2, 3 together -/

/-- **The width at routes 0, 2 and 3**: `2^{A (log₂ n+2)^2}` at a well-formed node. -/
theorem exists_widthE_low_le (p : Params) (cam : RawGens × List ℕ → Option RawCameron) :
    ∃ A, ∀ P : RawMasterSI, MasterInputWF p.a p.b P →
      (masterRoute P = 0 ∨ masterRoute P = 2 ∨ masterRoute P = 3) →
      (masterRoundE p cam).width P ≤ 2 ^ (A * lg (masterDegree P) ^ 2) := by
  obtain ⟨A₁, h₁⟩ := exists_line1Width_le p.a p.b p.B p.C₀ cam
  obtain ⟨A₃, h₃⟩ := exists_line4bWidth_le p.a p.b p.e p.f p.u p.v
  refine ⟨A₁ + A₃, fun P hP hr => ?_⟩
  have hL : lg (masterDegree P) ≤ lg (masterDegree P) ^ 2 := by
    calc lg (masterDegree P) = lg (masterDegree P) ^ 1 := (pow_one _).symm
      _ ≤ _ := lg_pow_le_lg_pow (by norm_num) _
  rw [widthE_eq]
  rcases hr with hr | hr | hr
  · rw [if_pos hr]
    exact (h₁ P hP).trans (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (by omega)))
  · rw [if_neg (by omega), if_neg (by omega), if_pos hr]; exact Nat.zero_le _
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hr]
    refine (h₃ P hP).trans (Nat.pow_le_pow_right (by norm_num) ?_)
    calc A₃ * lg (masterDegree P) ≤ A₃ * lg (masterDegree P) ^ 2 := Nat.mul_le_mul_left _ hL
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end Explicit
