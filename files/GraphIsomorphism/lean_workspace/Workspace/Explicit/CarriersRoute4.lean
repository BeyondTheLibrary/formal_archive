/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the node carrier of route 4
(lines 4c–4d of the Master, Sec. 15; Procedure Align, Sec. 14.1) bounded at the degree. Not part
of the faithful formalization.
-/
import Workspace.Explicit.CarriersRoute4State
import Workspace.Explicit.CarriersLowBase
import Workspace.Algo.TopMasterLine4cd
import Workspace.Algo.TopMasterRoute4Hint

/-!
# Route 4 bounded at the degree

The carrier of route 4 in `Explicit.masterOpsE` is
`masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint (line4dDomHint 0 tt dd)) dD`: line 6
of Procedure Align tests for a dominant color class (`Algo.masterHasDom`); with one, lines 7–11
run (`Algo.line4dDomOps`, with the hint routine of line 11); without, the loop of Eq. (71)
(`Algo.line4dOps`). Every routine reads the header of line 4d, built on line 4c, which is
bounded at the degree at a node of route 4 (`Explicit.TN.line4dHdr`, Pre `Explicit.TN.R4Good`).

* `Explicit.R4`: the node is on route 4 and its hint is good (the route-4 part of the
  Master's good nodes). `Explicit.r4Good_of` turns it into `Explicit.TN.R4Good n` of the hinted
  input, at an admitted node of degree at most `n`.
* `Explicit.carrierTN_route4`: the four routines are bounded at the degree with exponent 5.
* `Explicit.stateBoundsXR_route4`: the fold states have size at most `2^{K (log₂ n + 2)^5}`
  **at the nodes of route 4 with a good hint** (`Explicit.StateBoundsXR`, the variant of
  `Explicit.StateBoundsX` restricted to a node predicate). The restriction is needed: the
  header of line 4d runs the Extended Design Lemma on relational structures whose size is
  bounded at the degree only when the hint is good (Theorem 9.2.3 needs `m ≤ n` points).

Generic tools: `Explicit.CarrierTN.pairIte` (a branch test bounded at the degree),
`Explicit.CarrierTN.withHint`, and the same for `Explicit.StateBoundsXR`.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ## Generic tools -/

namespace CarrierTN

variable {a b : ℕ} {R : RawMasterSI → Prop}

/-- **Two carriers side by side, with a branch test bounded at the degree.** -/
theorem pairIte {S T : Type} [Enc S] [Enc T] {sel : RawMasterSI → Bool}
    (hsel : TN sel (CarrierPre a b R) 5) {F : MasterOps S} {G : MasterOps T} {dS : S} {dT : T}
    (hF : CarrierTN a b F R) (hG : CarrierTN a b G R) :
    CarrierTN a b (MasterOps.pairIte sel F G dS dT) R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : TN (fun z : RawMasterSI × ℕ × S × T => sel z.1)
        (fun n z => CarrierPre a b R n z.1) 5 := TN.poly_comp polyFun_fst hsel
    have h1 : TN (fun z : RawMasterSI × ℕ × S × T => F.child (z.1, z.2.1, z.2.2.1))
        (fun n z => CarrierPre a b R n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (pfst (psnd polyFun_snd))))
        hF.child).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × S × T => G.child (z.1, z.2.1, z.2.2.2))
        (fun n z => CarrierPre a b R n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair (psnd (psnd polyFun_snd))))
        hG.child).restrict (fun _ _ h => h)
    exact (TN.iteT hs h1 h2).of_eq (fun _ => rfl)
  · exact (TN.iteT hsel (hF.init.pair (TN.const' dT _ 5))
      ((TN.const' dS _ 5).pair hG.init)).of_eq (fun _ => rfl)
  · have hs : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset => sel z.1)
        (fun n z => CarrierPre a b R n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp polyFun_fst hsel).restrict (fun _ _ h => h.1)
    have h1 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        F.combine (z.1, z.2.1, z.2.2.1.1, z.2.2.2))
        (fun n z => CarrierPre a b R n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((pfst (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hF.combine).restrict
        (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × ℕ × (S × T) × RawCoset =>
        G.combine (z.1, z.2.1, z.2.2.1.2, z.2.2.2))
        (fun n z => CarrierPre a b R n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp (polyFun_fst.pair ((pfst polyFun_snd).pair
        ((psnd (pfst (psnd polyFun_snd))).pair (psnd (psnd polyFun_snd))))) hG.combine).restrict
        (fun _ _ h => h)
    exact (TN.iteT hs (h1.pair (TN.const' dT _ 5)) ((TN.const' dS _ 5).pair h2)).of_eq
      (fun _ => rfl)
  · have hs : TN (fun z : RawMasterSI × S × T => sel z.1)
        (fun n z => CarrierPre a b R n z.1) 5 := TN.poly_comp polyFun_fst hsel
    have h1 : TN (fun z : RawMasterSI × S × T => F.finish (z.1, z.2.1))
        (fun n z => CarrierPre a b R n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair (pfst polyFun_snd)) hF.finish).restrict (fun _ _ h => h)
    have h2 : TN (fun z : RawMasterSI × S × T => G.finish (z.1, z.2.2))
        (fun n z => CarrierPre a b R n z.1) 5 :=
      (TN.poly_comp (polyFun_fst.pair (psnd polyFun_snd)) hG.finish).restrict (fun _ _ h => h)
    exact (TN.iteT hs h1 h2).of_eq (fun _ => rfl)

/-- **A carrier with a hint routine bounded at the degree.** -/
theorem withHint {S : Type} [Enc S] {F : MasterOps S}
    {H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint}
    (hF : CarrierTN a b F R) (hH : TN H (fun n w => CarrierPre a b R n w.1.1) 5) :
    CarrierTN a b (F.withHint H) R := by
  refine ⟨?_, hF.init, hF.combine, hF.finish⟩
  have hH' : TN (fun w : RawMasterSI × (RawMasterSI × ℕ × S) => H (w.2, w.1))
      (fun n w => CarrierPre a b R n w.2.1) 5 :=
    (TN.poly_comp (polyFun_snd.pair polyFun_fst) hH).restrict (fun _ _ h => h)
  have hh : TN (fun w : RawMasterSI × (RawMasterSI × ℕ × S) =>
      some (masterAttachHint (w.1, H (w.2, w.1))))
      (fun n w => CarrierPre a b R n w.2.1) 5 :=
    ((TN.ofPoly polyFun_fst _ 5).pair hH').comp_poly
      (polyFun_masterAttachHint.comp polyFun_some)
  have ho := TN.optionElim
    (Pre := fun n (p : Option RawMasterSI × (RawMasterSI × ℕ × S)) => CarrierPre a b R n p.2.1)
    (TN.const' (none : Option RawMasterSI) (fun _ (_ : RawMasterSI × ℕ × S) => True) 5) hh
    (fun _ _ _ => trivial) (fun _ _ _ h => h)
  refine ((hF.child.pair (TN.id' _ 5)).comp ho (fun _ _ h => h)).of_eq (fun z => ?_)
  change Option.elim (F.child z) none
      (fun C => some (masterAttachHint (C, H (z, C)))) =
    Option.map (fun C => masterAttachHint (C, H (z, C))) (F.child z)
  cases F.child z <;> rfl

end CarrierTN

/-- **The fields of `Explicit.StateBoundsX`, at the nodes with `R` only.** -/
def StateBoundsXR {S : Type} [Enc S] (a b K : ℕ) (F : MasterOps S) (R : RawMasterSI → Prop) :
    Prop :=
  (∀ P, MasterInputWF a b P → R P →
    Enc.size (F.init P) ≤ 2 ^ (K * lg (masterDegree P) ^ 5)) ∧
  (∀ P j s A, MasterInputWF a b P → R P → Enc.size A ≤ masterInputCap a b (masterDegree P) →
    Enc.size (F.combine (P, j, s, A)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5)) ∧
  (∀ P s, MasterInputWF a b P → R P →
    Enc.size (F.finish (P, s)) ≤ masterInputCap a b (masterDegree P)) ∧
  (∀ P s, MasterInputWF a b P → R P →
    Enc.size (F.finish (P, s)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))

theorem StateBoundsX.toR {S : Type} [Enc S] {a b K : ℕ} {F : MasterOps S}
    (h : StateBoundsX a b K F) (R : RawMasterSI → Prop) : StateBoundsXR a b K F R :=
  ⟨fun P hP _ => h.1 P hP, fun P j s A hP _ hA => h.2.1 P j s A hP hA,
    fun P s hP _ => h.2.2.1 P s hP, fun P s hP _ => h.2.2.2 P s hP⟩

/-- `2 x + 2 e ≤ 2^{(K + d + 1) L}` when `x ≤ 2^{K L}`, `e ≤ d` and `L ≥ 1`. -/
theorem pair_le_two_pow {x e d K L : ℕ} (hx : x ≤ 2 ^ (K * L)) (he : e ≤ d) (hL : 1 ≤ L) :
    2 * x + 2 * e ≤ 2 ^ ((K + d + 1) * L) := by
  have h1 : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  have h2 : 2 ^ (d + 1) ≤ 2 ^ ((d + 1) * L) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hL)
  have h3 : 1 ≤ 2 ^ (K * L) := Nat.one_le_two_pow
  have h4 : 2 ^ ((K + d + 1) * L) = 2 ^ (K * L) * 2 ^ ((d + 1) * L) := by
    rw [← pow_add]; ring_nf
  have h5 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
  rw [h4]
  calc 2 * x + 2 * e ≤ 2 ^ (K * L) * 2 + 2 ^ (K * L) * (2 * d) := by nlinarith
    _ = 2 ^ (K * L) * (2 * (d + 1)) := by ring
    _ ≤ 2 ^ (K * L) * 2 ^ (d + 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2 ^ (K * L) * 2 ^ ((d + 1) * L) := Nat.mul_le_mul_left _ h2

namespace StateBoundsXR

variable {a b : ℕ} {R : RawMasterSI → Prop}

theorem mono {S : Type} [Enc S] {F : MasterOps S} {K K' : ℕ} (h : StateBoundsXR a b K F R)
    (hK : K ≤ K') : StateBoundsXR a b K' F R :=
  ⟨fun P hP hR => (h.1 P hP hR).trans (StateBoundsX.two_pow_mono hK _),
    fun P j s A hP hR hA => (h.2.1 P j s A hP hR hA).trans (StateBoundsX.two_pow_mono hK _),
    h.2.2.1, fun P s hP hR => (h.2.2.2 P s hP hR).trans (StateBoundsX.two_pow_mono hK _)⟩

/-- From the three `MasterOpsCost`-style bounds, at the nodes with `R`. -/
theorem of_three {S : Type} [Enc S] {F : MasterOps S} (K : ℕ)
    (hi : ∀ P, MasterInputWF a b P → R P →
      Enc.size (F.init P) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))
    (hu : ∀ P j s A, MasterInputWF a b P → R P →
      Enc.size A ≤ masterInputCap a b (masterDegree P) →
      Enc.size (F.combine (P, j, s, A)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))
    (hf : ∀ P s, MasterInputWF a b P → R P →
      Enc.size (F.finish (P, s)) ≤ masterInputCap a b (masterDegree P)) :
    ∃ K', StateBoundsXR a b K' F R := by
  obtain ⟨c, hc⟩ := q5_masterInputCap a b
  exact ⟨K + c,
    fun P hP hR => (hi P hP hR).trans (StateBoundsX.two_pow_mono (Nat.le_add_right _ _) _),
    fun P j s A hP hR hA => (hu P j s A hP hR hA).trans
      (StateBoundsX.two_pow_mono (Nat.le_add_right _ _) _),
    hf, fun P s hP hR => ((hf P s hP hR).trans (hc _)).trans
      (StateBoundsX.two_pow_mono (Nat.le_add_left _ _) _)⟩

theorem withHint {S : Type} [Enc S] {F : MasterOps S} {K : ℕ}
    (H : (RawMasterSI × ℕ × S) × RawMasterSI → Option RawMasterHint)
    (h : StateBoundsXR a b K F R) : StateBoundsXR a b K (F.withHint H) R := h

/-- **Two carriers side by side**: the default states add a constant to the exponent. -/
theorem pairIte {S T : Type} [Enc S] [Enc T] (sel : RawMasterSI → Bool) {F : MasterOps S}
    {G : MasterOps T} (dS : S) (dT : T) {K : ℕ} (hF : StateBoundsXR a b K F R)
    (hG : StateBoundsXR a b K G R) :
    StateBoundsXR a b (K + (Enc.size dS + Enc.size dT) + 1)
      (MasterOps.pairIte sel F G dS dT) R := by
  have hL : ∀ P : RawMasterSI, 1 ≤ lg (masterDegree P) ^ 5 := fun P => one_le_lg5 _
  refine ⟨fun P hP hR => ?_, fun P j s A hP hR hA => ?_, fun P s hP hR => ?_,
    fun P s hP hR => ?_⟩
  · show Enc.size (if sel P then (F.init P, dT) else (dS, G.init P)) ≤ _
    split
    · have := Combine.size_pair_le (F.init P) dT
      exact this.trans (pair_le_two_pow (hF.1 P hP hR) (by omega) (hL P))
    · have := Combine.size_pair_le dS (G.init P)
      have h2 := pair_le_two_pow (e := Enc.size dS) (d := Enc.size dS + Enc.size dT)
        (hG.1 P hP hR) (by omega) (hL P)
      omega
  · show Enc.size (if sel P then (F.combine (P, j, s.1, A), dT)
      else (dS, G.combine (P, j, s.2, A))) ≤ _
    split
    · have := Combine.size_pair_le (F.combine (P, j, s.1, A)) dT
      exact this.trans (pair_le_two_pow (hF.2.1 P j s.1 A hP hR hA) (by omega) (hL P))
    · have := Combine.size_pair_le dS (G.combine (P, j, s.2, A))
      have h2 := pair_le_two_pow (e := Enc.size dS) (d := Enc.size dS + Enc.size dT)
        (hG.2.1 P j s.2 A hP hR hA) (by omega) (hL P)
      omega
  · show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    split
    · exact hF.2.2.1 P s.1 hP hR
    · exact hG.2.2.1 P s.2 hP hR
  · have hK : K ≤ K + (Enc.size dS + Enc.size dT) + 1 := by omega
    show Enc.size (if sel P then F.finish (P, s.1) else G.finish (P, s.2)) ≤ _
    split
    · exact (hF.2.2.2 P s.1 hP hR).trans (StateBoundsX.two_pow_mono hK _)
    · exact (hG.2.2.2 P s.2 hP hR).trans (StateBoundsX.two_pow_mono hK _)

end StateBoundsXR

/-! ## Nodes of route 4 -/

/-- **A node of route 4 with a good hint** (the route-4 part of the Master's good nodes). -/
def R4 (P : RawMasterSI) : Prop :=
  masterRoute P = 4 ∧ ∀ h, P.2 = some h → MasterHintGood (P.1, h)

/-- At an admitted node of route 4 with a good hint and degree at most `n`, the hinted input
is a node of route 4 at degree `n` (`Explicit.TN.R4Good`): its window has at most
`masterDegree P ≤ n` points (`Algo.MasterInputWF`). -/
theorem r4Good_of {a b n : ℕ} {P : RawMasterSI} (hP : CarrierPre a b R4 n P) :
    TN.R4Good n (line4dHint P) := by
  obtain ⟨hwf, hdeg, hr, hg⟩ := hP
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact absurd hr (by simp [masterRoute])
  | some h =>
    refine ⟨hg h rfl, hr, ?_⟩
    show W.1.length ≤ n
    exact le_trans hwf.2.1 hdeg

/-- The hint routine of line 4d once its header is computed. -/
def line4dDomHintPost (x : AVHdr × ((RawMasterSI × ℕ × ADState) × RawMasterSI)) :
    Option RawMasterHint :=
  if (!l57Small x.1 && decide (2 * x.2.1.1.1.1.length < 3 * x.2.2.1.1.length)) then
    some (alignDomHintAt (((x.1.1, x.1.2.1), x.2.1.1.1.1), x.2.2.1))
  else none

theorem polyFun_line4dDomHintPost : PolyFun line4dDomHintPost := by
  let Z := AVHdr × ((RawMasterSI × ℕ × ADState) × RawMasterSI)
  have i : PolyFun (fun x : Z => x) := polyFun_id
  have hH := pfst i
  have hnot : PolyFun (fun x : Z => !l57Small x.1) :=
    (hH.comp polyFun_l57Small).comp ((PolyFun.ite polyFun_id (polyFun_const false)
      (polyFun_const true)).of_eq (fun x => by cases x <;> rfl))
  have hlt : PolyFun (fun x : Z => decide (2 * x.2.1.1.1.1.length < 3 * x.2.2.1.1.length)) :=
    ((((pfst (pfst (pfst (pfst (psnd i))))).comp polyFun_length).comp
      ((polyFun_const 2).mul polyFun_id)).pair
      (((pfst (pfst (psnd (psnd i)))).comp polyFun_length).comp
        ((polyFun_const 3).mul polyFun_id))).comp polyFun_natLt
  have harg : PolyFun (fun x : Z => (((x.1.1, x.1.2.1), x.2.1.1.1.1), x.2.2.1)) :=
    (((pfst hH).pair (pfst (psnd hH))).pair (pfst (pfst (pfst (pfst (psnd i)))))).pair
      (pfst (psnd (psnd i)))
  exact (PolyFun.ite (polyFun_and hnot hlt) (harg.comp (polyFun_alignDomHintAt.comp
    polyFun_some)) (polyFun_const none)).of_eq (fun _ => rfl)

/-- The answer of line 4d fits the Master's input cap (as in `Algo.line4dOps_cost`). -/
theorem size_line4dFinish_le (a b : ℕ) (P : RawMasterSI) (s : AVState) :
    Enc.size (line4dFinish (line4dHint P, s)) ≤ masterInputCap a b (masterDegree P) := by
  have hs := size_top3Shift_le (n := P.1.2.2.2.1.length) rfl le_rfl
    (normPerm (P.1.2.2.2.1, P.1.2.2.1))
    (top2NormC P.1.2.2.2.1 (topwCosetPreimage ((P.1.2.2.2.1, P.1.2.1), P.1.1, s.2.2.2)))
  change Enc.size (top3Shift _) ≤ _
  refine hs.trans ?_
  unfold masterInputCap
  change chainBound (masterDegree P) ≤ _
  omega

/-- The header of line 4d, at a node of route 4 with a good hint, has size at most
`2^{c (log₂ n + 2)^5}` in the degree `n`. -/
theorem hdr_size_q5 (a b : ℕ) {H : RawMasterSI → AVHdr}
    (hH : TN H (CarrierPre a b R4) 5) : ∃ c, ∀ P, MasterInputWF a b P → R4 P →
      Enc.size (H P) ≤ 2 ^ (c * lg (masterDegree P) ^ 5) := by
  obtain ⟨A, e, hT⟩ := hH
  obtain ⟨c, hc⟩ := (q5_two_pow_lg A 5 le_rfl).mul
    (((q5_masterInputCap a b).add (q5_const 1)).pow e)
  refine ⟨c, fun P hP hR => ?_⟩
  refine ((hT.size _ P ⟨hP, le_rfl, hR⟩).trans ?_).trans (hc (masterDegree P))
  exact tsB_mono_right _ _ _ _ hP.1

private theorem h25 : 2 ≤ 5 := by norm_num
private theorem hk5 : max (0 + 2) 4 ≤ 5 := by norm_num

section Route4

variable (tt dd : ℕ) (ht : tt + 2 ≤ 5)
include ht


/-- The header of lines 7–11 at line 4d (`Algo.line4dDomHdr`), bounded at the degree at a node
of route 4 (the port of `Algo.quasiFun_line4dDomHdr`). -/
theorem tn_line4dDomHdr : TN (line4dDomHdr 0 tt dd) TN.R4Good 5 := by
  have hT := polyFun_masterHintTop
  have hA : PolyFun (fun p : MasterHintInput => (masterHintTop p).1) := hT.comp polyFun_fst
  have hF := TN.line4dFixed 0 tt dd 5 h25 hk5 ht
  have hW : TN (fun p : MasterHintInput =>
      alignL57Windows ((masterHintTop p).1, line4dFixed 0 tt dd p)) TN.R4Good 5 :=
    ((TN.ofPoly hA _ _).pair hF).comp_poly polyFun_alignL57Windows
  exact ((TN.ofPoly hA _ _).pair (hF.pair ((TN.line4dYs 0 tt dd 5 h25 hk5 ht).pair (hW.pair
    ((TN.ofPoly (hT.comp (polyFun_snd.comp polyFun_fst)) _ _).pair
      (TN.ofPoly (hT.comp (polyFun_snd.comp polyFun_snd)) _ _)))))).of_eq (fun _ => rfl)

variable (a b : ℕ)

theorem tn_domHdrAt :
    TN (fun P => line4dDomHdr 0 tt dd (line4dHint P)) (CarrierPre a b R4) 5 :=
  (TN.poly_comp polyFun_line4dHint (tn_line4dDomHdr tt dd ht)).restrict (fun _ _ h => r4Good_of h)

theorem tn_hdrAt : TN (fun P => line4dHdr 0 tt dd (line4dHint P)) (CarrierPre a b R4) 5 :=
  (TN.poly_comp polyFun_line4dHint (TN.line4dHdr 0 tt dd 5 h25 hk5 ht)).restrict
    (fun _ _ h => r4Good_of h)

theorem tn_masterHasDom : TN (masterHasDom 0 tt dd) (CarrierPre a b R4) 5 :=
  (TN.poly_comp polyFun_line4dHint (TN.line4dHasDom 0 tt dd 5 h25 hk5 ht)).restrict
    (fun _ _ h => r4Good_of h)

/-- **The hint routine of line 4d, bounded at the degree** (the port of
`Algo.quasiFun_line4dDomHint`). -/
theorem tn_line4dDomHint :
    TN (line4dDomHint 0 tt dd) (fun n w => CarrierPre a b R4 n w.1.1) 5 :=
  (((TN.poly_comp (pfst polyFun_fst) (tn_domHdrAt tt dd ht a b)).pair (TN.id' _ 5)).comp_poly
    polyFun_line4dDomHintPost).of_eq (fun _ => rfl)

/-- **Lines 7–11 of Procedure Align at line 4d** (`Algo.line4dDomOps`), bounded at the degree
(the port of the `QuasiFun` fields of `Algo.line4dDomOps_cost`). -/
theorem carrierTN_line4dDom : CarrierTN a b (line4dDomOps 0 tt dd) R4 := by
  have hH : TN (fun z : RawMasterSI × ℕ × ADState => line4dDomHdr 0 tt dd (line4dHint z.1))
      (fun n z => CarrierPre a b R4 n z.1) 5 :=
    TN.poly_comp polyFun_fst (tn_domHdrAt tt dd ht a b)
  have hok : ∀ n (P : RawMasterSI), CarrierPre a b R4 n P →
      AVHdrOK n (line4dDomHdr 0 tt dd (line4dHint P)) := fun _ _ h => (r4Good_of h).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hK := hH.comp (TN.l57Calls.mono_k (by norm_num)) (fun n z h => hok n z.1 h)
    have hC := (hH.pair (TN.ofPoly (psnd (psnd polyFun_id)) _ 5)).comp
      (TN.l57Child.mono_k (by norm_num)) (fun n z h => hok n z.1 h)
    exact (((hH.pair (TN.id' _ 5)).pair (hK.pair hC)).comp_poly polyFun_line4dDomPost).of_eq
      (fun z => (line4dDomOps_child_eq 0 tt dd z).symm)
  · exact ((tn_domHdrAt tt dd ht a b).comp (TN.l57Init.mono_k (by norm_num)) hok).of_eq
      (fun _ => rfl)
  · have i : PolyFun (fun z : RawMasterSI × ℕ × ADState × RawCoset => z) := polyFun_id
    have hq := pfst i
    have himg : PolyFun (fun z : RawMasterSI × ℕ × ADState × RawCoset =>
        topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
      ((pfst (psnd (psnd (psnd (pfst hq))))).pair ((pfst (pfst hq)).pair
        (psnd (psnd (psnd i))))).comp polyFun_topwCosetImage
    have hH' : TN (fun z : RawMasterSI × ℕ × ADState × RawCoset =>
        line4dDomHdr 0 tt dd (line4dHint z.1))
        (fun n z => CarrierPre a b R4 n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp polyFun_fst (tn_domHdrAt tt dd ht a b)).restrict (fun _ _ h => h.1)
    exact ((hH'.pair (TN.ofPoly ((pfst (psnd (psnd i))).pair himg) _ 5)).comp
      (TN.l57Step.mono_k (by norm_num)) (fun n z h => hok n z.1 h.1)).of_eq (fun _ => rfl)
  · exact (TN.ofPoly (((polyFun_fst.comp polyFun_line4dHint).pair (pfst polyFun_snd)).comp
      polyFun_line4dFinish) _ 5).of_eq (fun _ => rfl)

/-- **The loop of Eq. (71) at line 4d** (`Algo.line4dOps`), bounded at the degree (the port of
the `QuasiFun` fields of `Algo.line4dOps_cost`). -/
theorem carrierTN_line4d : CarrierTN a b (line4dOps 0 tt dd) R4 := by
  have hH : TN (fun z : RawMasterSI × ℕ × AVState => line4dHdr 0 tt dd (line4dHint z.1))
      (fun n z => CarrierPre a b R4 n z.1) 5 :=
    TN.poly_comp polyFun_fst (tn_hdrAt tt dd ht a b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hH.pair (TN.id' _ 5)).comp_poly polyFun_line4dChildBody).of_eq
      (fun z => (line4dOps_child_eq 0 tt dd z).symm)
  · exact ((tn_hdrAt tt dd ht a b).comp_poly polyFun_avInit).of_eq (fun _ => rfl)
  · have i : PolyFun (fun z : RawMasterSI × ℕ × AVState × RawCoset => z) := polyFun_id
    have hq := pfst i
    have himg : PolyFun (fun z : RawMasterSI × ℕ × AVState × RawCoset =>
        topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
      ((pfst (psnd (psnd (psnd (pfst hq))))).pair ((pfst (pfst hq)).pair
        (psnd (psnd (psnd i))))).comp polyFun_topwCosetImage
    have hH' : TN (fun z : RawMasterSI × ℕ × AVState × RawCoset =>
        line4dHdr 0 tt dd (line4dHint z.1))
        (fun n z => CarrierPre a b R4 n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5 :=
      (TN.poly_comp polyFun_fst (tn_hdrAt tt dd ht a b)).restrict (fun _ _ h => h.1)
    exact ((hH'.pair (TN.ofPoly ((pfst (psnd (psnd i))).pair himg) _ 5)).comp_poly
      polyFun_avCombine).of_eq (fun _ => rfl)
  · exact (TN.ofPoly (((polyFun_fst.comp polyFun_line4dHint).pair polyFun_snd).comp
      polyFun_line4dFinish) _ 5).of_eq (fun _ => rfl)

/-- **Route 4 (lines 4c–4d of the Master), bounded at the degree with exponent 5**, at the
parameters of `Explicit.masterOpsE` (`c = 0`, any `tt ≤ 3`). -/
theorem carrierTN_route4 (dD : ADState) :
    CarrierTN a b (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint
      (line4dDomHint 0 tt dd)) dD) R4 :=
  CarrierTN.pairIte (tn_masterHasDom tt dd ht a b)
    ((carrierTN_line4dDom tt dd ht a b).withHint (tn_line4dDomHint tt dd ht a b))
    (carrierTN_line4d tt dd ht a b)

/-! ## The fold states of route 4 -/

theorem stateBoundsXR_line4dDom : ∃ K, StateBoundsXR a b K (line4dDomOps 0 tt dd) R4 := by
  obtain ⟨c, hc⟩ := hdr_size_q5 a b (tn_domHdrAt tt dd ht a b)
  obtain ⟨K, hK⟩ := l57_state_q5 c
  refine StateBoundsXR.of_three K (fun P hP hR => ?_) (fun P j s A hP hR _ => ?_)
    (fun P s _ _ => size_line4dFinish_le a b P s.1)
  · have hok := (r4Good_of (a := a) (b := b) (n := masterDegree P) ⟨hP, le_rfl, hR⟩).2.2
    exact (hK _ (line4dDomHdr 0 tt dd (line4dHint P)) hok (hc P hP hR)).2.1
  · have hok := (r4Good_of (a := a) (b := b) (n := masterDegree P) ⟨hP, le_rfl, hR⟩).2.2
    exact (hK _ (line4dDomHdr 0 tt dd (line4dHint P)) hok (hc P hP hR)).1 _ _

theorem stateBoundsXR_line4d : ∃ K, StateBoundsXR a b K (line4dOps 0 tt dd) R4 := by
  obtain ⟨c, hc⟩ := hdr_size_q5 a b (tn_hdrAt tt dd ht a b)
  obtain ⟨K, hK⟩ := l57_state_q5 c
  refine StateBoundsXR.of_three K (fun P hP hR => ?_) (fun P j s A hP hR _ => ?_)
    (fun P s _ _ => size_line4dFinish_le a b P s)
  · have hok := (r4Good_of (a := a) (b := b) (n := masterDegree P) ⟨hP, le_rfl, hR⟩).2.2
    exact (hK _ (line4dHdr 0 tt dd (line4dHint P)) hok (hc P hP hR)).2.2.1
  · have hok := (r4Good_of (a := a) (b := b) (n := masterDegree P) ⟨hP, le_rfl, hR⟩).2.2
    exact (hK _ (line4dHdr 0 tt dd (line4dHint P)) hok (hc P hP hR)).2.2.2 _ _

/-- **The fold states of route 4, with an explicit exponent**, at the nodes of route 4 with a
good hint. -/
theorem stateBoundsXR_route4 (dD : ADState) :
    ∃ K, StateBoundsXR a b K (masterLine4cdOps 0 tt dd ((line4dDomOps 0 tt dd).withHint
      (line4dDomHint 0 tt dd)) dD) R4 := by
  obtain ⟨K₁, h₁⟩ := stateBoundsXR_line4dDom tt dd ht a b
  obtain ⟨K₂, h₂⟩ := stateBoundsXR_line4d tt dd ht a b
  exact ⟨_, StateBoundsXR.pairIte (masterHasDom 0 tt dd) dD default
    ((h₁.withHint (line4dDomHint 0 tt dd)).mono (Nat.le_add_right K₁ K₂))
    (h₂.mono (Nat.le_add_left K₂ K₁))⟩

end Route4

end Explicit
