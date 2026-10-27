/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the carrier of lines 5–7 of
the Master (Sec. 15) and its hint routine, bounded at an external degree. Not part of the
faithful formalization.
-/
import Workspace.Explicit.L57Giant
import Workspace.Algo.AlignDomHintL57

/-!
# The carrier of lines 5–7, bounded at the degree

`Algo.masterL57Ops` runs the round of lines 5–7 (`Algo.masterL57Round`) on the context
`Algo.masterL57Ctx P` of a hinted node `P`, lifting its calls and its answer between the window
and the node. At a node of route 5 with a good hint (`Explicit.R5`) the context satisfies the
conditions under which the round is bounded at the degree (`Explicit.l57CtxOK_of`): the window
has `|Δ| ≥ 64` points, the image domain has `m ≤ |Δ|` points, and the list of the context has
`min(10 + log₂|Δ|, |Δ|)` entries, within the guard `(log₂|Δ| + 1)^3`.
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem polyFun_isNone' {α : Type*} [Enc α] : PolyFun (fun o : Option α => o.isNone) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) (polyFun_const false))).of_eq
    (fun o => by cases o <;> rfl)

/-- **A node of route 5 with a good hint** (the route-5 part of the Master's good nodes). -/
def R5 (P : RawMasterSI) : Prop :=
  masterRoute P = 5 ∧ ∀ h, P.2 = some h → MasterHintGood (P.1, h)

/-- The list of the context is within the guard: `min(10 + log₂ N, N) ≤ (log₂ N + 1)^{c+1}`
once `N ≥ 64` and `c ≥ 2`. -/
theorem l57_list_guard {c N : ℕ} (hc : 2 ≤ c) (hN : 64 ≤ N) :
    min (10 + Nat.log 2 N) N ≤ guardBound (c + 1) N := by
  unfold guardBound
  have hL : 6 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2
    (by norm_num; omega)
  set L := Nat.log 2 N
  have h3 : (L + 1) ^ 3 ≤ (L + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 10 + L ≤ (L + 1) ^ 3 := by
    have : 7 ≤ L + 1 := by omega
    calc 10 + L ≤ (L + 1) * 49 := by omega
      _ ≤ (L + 1) * ((L + 1) * (L + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = (L + 1) ^ 3 := by ring
  exact (Nat.min_le_left _ _).trans (h1.trans h3)

/-- **The context of lines 5–7 at a good node of route 5 is bounded at the degree.** -/
theorem l57CtxOK_of {a b c n : ℕ} (hc : 2 ≤ c) {P : RawMasterSI}
    (hP : CarrierPre a b R5 n P) : L57CtxOK c n (masterL57Ctx P) := by
  obtain ⟨hwf, hdeg, hr, hg⟩ := hP
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact absurd hr (by simp [masterRoute])
  | some h =>
    obtain ⟨m, ϕ, B, hB, hp, -, -, -, -, -, -, hmΔ, h64⟩ := hg h rfl
    have hΔ : W.1.length ≤ n := le_trans hwf.2.1 hdeg
    have hx := masterL57Ctx_length (W, some h)
    have hy := masterL57Ctx_length_y (W, some h)
    have hm : (masterHintTop (W, h)).1.2.1.length = m := hp.2.1
    change m ≤ W.1.length at hmΔ
    change 64 ≤ W.1.length at h64
    change _ = W.1.length at hx hy
    refine ⟨⟨⟨by omega, by omega, ?_⟩, by omega, ?_⟩, ?_⟩
    · change (List.range (masterHintTop (W, h)).1.2.1.length).length ≤ n
      rw [List.length_range, hm]; omega
    · rw [hx]
      change (List.range (min (10 + Nat.log 2 W.1.length) W.1.length)).length ≤ _
      rw [List.length_range]
      exact l57_list_guard hc h64
    · change (List.range W.1.length).length ≤ n
      rw [List.length_range]; exact hΔ

namespace TN

variable {c b t d : ℕ} (dc dp e f E : ℕ)

theorem masterL57Ops_child (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5)
    (ht : t + 2 ≤ 5) :
    TN (masterL57Ops c b t d dc dp e f E).child (fun n z => CarrierPre a b' R5 n z.1) 5 := by
  let Z := RawMasterSI × ℕ × AggnL57GState
  have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
  have hRc : TN (fun z : Z => (masterL57Round c b t d dc dp e f).child (masterL57Enter z.1, z.2.1, z.2.2))
      (fun n z => CarrierPre a b' R5 n z.1) 5 :=
    (poly_comp ((hP.comp polyFun_masterL57Enter).pair (psnd polyFun_id))
      (aggnL57GChild (d := d) dc dp (l57UV e f).1 (l57UV e f).2 e f hc hb ht)).restrict
      (fun _ _ h => l57CtxOK_of hc2 h)
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hlift : PolyFun (fun q : AggnPhaseNode × Z =>
      (topwRawInstance (masterWinCtx q.2.1, masterL57Read q.2.1 q.1)).map
        (fun V => masterCheckedCall (q.2.1.1.2.2.2.1, V))) := by
    have h1 : PolyFun (fun q : AggnPhaseNode × Z =>
        topwRawInstance (masterWinCtx q.2.1, masterL57Read q.2.1 q.1)) :=
      (((psnd polyFun_id).comp (hP.comp polyFun_masterWinCtx)).pair
        ((((psnd polyFun_id).comp hP).pair polyFun_fst).comp polyFun_masterL57Read)).comp
          polyFun_topwRawInstance
    have hh : PolyFun (fun r : RawWinSI × (AggnPhaseNode × Z) =>
        (some (masterCheckedCall (r.2.2.1.1.2.2.2.1, r.1)) : Option RawMasterSI)) :=
      ((((psnd (psnd polyFun_id)).comp (hP.comp hx)).pair polyFun_fst).comp
        polyFun_masterCheckedCall).comp polyFun_some
    have h3 := PolyFun.optionElim (β := RawWinSI) (σ := AggnPhaseNode × Z) (polyFun_const none) hh
    exact ((h1.pair polyFun_id).comp h3).of_eq (fun q => by
      cases topwRawInstance (masterWinCtx q.2.1, masterL57Read q.2.1 q.1) <;> rfl)
  have hbind : TN (fun z : Z => ((masterL57Round c b t d dc dp e f).child
      (masterL57Enter z.1, z.2.1, z.2.2)).bind (fun J =>
        (topwRawInstance (masterWinCtx z.1, masterL57Read z.1 J)).map
          (fun V => masterCheckedCall (z.1.1.2.2.2.1, V))))
      (fun n z => CarrierPre a b' R5 n z.1) 5 :=
    ((hRc.pair (id' _ _)).comp_poly
      (PolyFun.optionElim (polyFun_const none) hlift)).of_eq (fun z => by
        cases (masterL57Round c b t d dc dp e f).child (masterL57Enter z.1, z.2.1, z.2.2) <;> rfl)
  exact (TN.ite (hP.comp polyFun_masterL57Guard) hbind (const' none _ _) (fun _ _ h _ => h)
    (fun _ _ _ _ => trivial)).of_eq (fun _ => rfl)

theorem masterL57Ops_init (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) :
    TN (masterL57Ops c b t d dc dp e f E).init (CarrierPre a b' R5) 5 := by
  have hi0 : TN (fun P : RawMasterSI =>
      ((Algo.aggnAggregateInit c dc dp (masterL57Enter P), (none : Option ADState)),
        (none : Option (ℕ × Top4State)))) (CarrierPre a b' R5) 5 :=
    ((poly_comp polyFun_masterL57Enter ((aggnAggregateInit c dc dp).mono_k (by omega))).restrict
      (fun _ _ h => (l57CtxOK_of hc2 h).1.1)).pair (const' none _ _) |>.pair (const' none _ _)
  have hi : TN (fun P : RawMasterSI => (masterL57Round c b t d dc dp e f).init (masterL57Enter P))
      (CarrierPre a b' R5) 5 :=
    hi0.of_eq (fun P => by simp only [masterL57Round, aggnL57GRound])
  exact (TN.ite polyFun_masterL57Guard hi (const' default _ _) (fun _ _ h _ => h)
    (fun _ _ _ _ => trivial)).of_eq (fun _ => rfl)

/-- The state condition of the combine: the stored loops of the phases are short. -/
def L57StOK (n : ℕ) (s : AggnL57GState) : Prop := AggStOK n s.1.1

theorem masterL57Ops_combine (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5)
    (ht : t + 2 ≤ 5) :
    TN (masterL57Ops c b t d dc dp e f E).combine
      (fun n z => CarrierPre a b' R5 n z.1 ∧ L57StOK n z.2.2.1) 5 := by
  let Z := RawMasterSI × ℕ × AggnL57GState × RawCoset
  have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hΔ : PolyFun (fun P : RawMasterSI => P.1.1) := polyFun_fst.comp polyFun_fst
  have himg : PolyFun (fun z : Z => topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2)) :=
    ((hP.comp hx).pair ((hP.comp hΔ).pair (psnd (psnd (psnd polyFun_id))))).comp
      polyFun_topwCosetImage
  have hin : PolyFun (fun z : Z => (masterL57Enter z.1, z.2.1, z.2.2.1,
      topwCosetImage (z.1.1.2.2.2.1, z.1.1.1, z.2.2.2))) :=
    (hP.comp polyFun_masterL57Enter).pair ((psnd polyFun_id).comp polyFun_fst |>.pair
      ((psnd (psnd polyFun_id)).comp polyFun_fst |>.pair himg))
  have hu := (poly_comp hin (aggnL57GCombine (d := d) dc dp (l57UV e f).1 (l57UV e f).2 e f hc hb ht)).restrict
    (Pre' := fun n (z : Z) => CarrierPre a b' R5 n z.1 ∧ L57StOK n z.2.2.1)
    (fun _ _ h => ⟨l57CtxOK_of hc2 h.1, h.2⟩)
  exact (TN.ite (hP.comp polyFun_masterL57Guard) hu (const' default _ _) (fun _ _ h _ => h)
    (fun _ _ _ _ => trivial)).of_eq (fun _ => rfl)

theorem masterL57Ops_finish (a b' : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5)
    (ht : t + 2 ≤ 5) :
    TN (masterL57Ops c b t d dc dp e f E).finish (fun n z => CarrierPre a b' R5 n z.1) 5 := by
  let Z := RawMasterSI × AggnL57GState
  have hP : PolyFun (fun z : Z => z.1) := polyFun_fst
  have hx : PolyFun (fun P : RawMasterSI => P.1.2.2.2.1) :=
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun P : RawMasterSI => P.1.2.2.1) :=
    ((polyFun_fst.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  have hΔ : PolyFun (fun P : RawMasterSI => P.1.1) := polyFun_fst.comp polyFun_fst
  have hgens : PolyFun (fun P : RawMasterSI => P.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hRf : TN (fun z : Z => (masterL57Round c b t d dc dp e f).finish (masterL57Enter z.1, z.2))
      (fun n z => CarrierPre a b' R5 n z.1) 5 :=
    (poly_comp ((hP.comp polyFun_masterL57Enter).pair polyFun_snd)
      (aggnL57GFinish (d := d) dc dp (l57UV e f).1 (l57UV e f).2 e f hc hb ht)).restrict
      (fun _ _ h => (l57CtxOK_of hc2 h).1)
  have hpre := ((ofPoly ((hP.comp hx).pair (hP.comp hgens)) _ _).pair
    ((ofPoly (hP.comp hΔ) _ _).pair hRf)).comp_poly polyFun_topwCosetPreimage
  have hF := ((ofPoly (hP.comp hx) _ _).pair hpre).comp_poly polyFun_top2NormC
  exact (((ofPoly (hP.comp hx) _ _).pair ((ofPoly (hP.comp hr) _ _).pair hF)).comp_poly
    polyFun_top3Shift).of_eq (fun _ => rfl)

/-! ## The hint routine `H5` -/

theorem masterL57HintHdr (a b' dc dp : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5)
    (ht : t + 2 ≤ 5) :
    TN (Algo.masterL57HintHdr c b t d dc dp) (fun n z => CarrierPre a b' R5 n z.1) 5 := by
  let Z := RawMasterSI × ℕ × AggnL57GState
  have i : PolyFun (fun z : Z => z) := polyFun_id
  exact ((poly_comp (((pfst i).comp polyFun_masterL57Ctx).pair (pfst (pfst (psnd (psnd i)))))
    (aggnL57Hdr (d := d) dc dp hc hb ht)).restrict
    (fun _ _ h => (l57CtxOK_of hc2 h).1)).of_eq (fun _ => rfl)

theorem masterL57Hint (a b' dc dp u v e f : ℕ) (hc2 : 2 ≤ c) (hc : c + 2 ≤ 5)
    (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.masterL57Hint c b t d dc dp u v e f)
      (fun n w => CarrierPre a b' R5 n w.1.1) 5 := by
  let Z := (RawMasterSI × ℕ × AggnL57GState) × RawMasterSI
  let Pre := fun n (w : Z) => CarrierPre a b' R5 n w.1.1
  have i : PolyFun (fun z : Z => z) := polyFun_id
  have hhdr : TN (fun z : Z => Algo.masterL57HintHdr c b t d dc dp z.1) Pre 5 :=
    poly_comp (pfst i) (masterL57HintHdr (d := d) a b' dc dp hc2 hc hb ht)
  have h1 : TN (fun z : Z =>
      !Algo.aggnL57GActive c b t d dc dp u v e f (masterL57Enter z.1.1, z.1.2.1, z.1.2.2)) Pre 5 :=
    ((poly_comp ((((pfst (pfst i)).comp polyFun_masterL57Enter).pair ((pfst (psnd (pfst i))).pair
      (psnd (psnd (pfst i)))))) (aggnL57GActive (d := d) dc dp u v e f hc hb ht)).restrict
      (fun _ _ h => (l57CtxOK_of hc2 h).1)).comp_poly
      ((PolyFun.ite polyFun_id (polyFun_const false) (polyFun_const true)).of_eq
        (fun x => by cases x <;> rfl))
  have h2 : TN (fun z : Z =>
      (Algo.aggnAggregateChild c (masterL57Enter z.1.1, z.1.2.1, z.1.2.2.1.1)).isNone) Pre 5 :=
    ((poly_comp ((((pfst (pfst i)).comp polyFun_masterL57Enter).pair ((pfst (psnd (pfst i))).pair
      (pfst (pfst (psnd (psnd (pfst i))))))))
      ((aggnAggregateChild c).mono_k (by omega))).restrict
      (fun _ _ h => (l57CtxOK_of hc2 h).1.1)).comp_poly polyFun_isNone'
  have h3 := hhdr.comp_poly ((polyFun_fst.pair (pfst polyFun_snd)).comp polyFun_alignRLarge)
  have h4 : PolyFun (fun z : Z => decide (2 * z.1.1.1.1.length < 3 * z.2.1.1.length)) :=
    ((((pfst (pfst (pfst (pfst i)))).comp polyFun_length).comp
      ((polyFun_const 2).mul polyFun_id)).pair
      (((pfst (pfst (psnd i))).comp polyFun_length).comp
        ((polyFun_const 3).mul polyFun_id))).comp polyFun_natLt
  have htest : TN (Algo.masterL57HintTest c b t d dc dp u v e f) Pre 5 :=
    ((((h1.pair h2).comp_poly (polyFun_and polyFun_fst polyFun_snd)).pair h3).comp_poly
      (polyFun_and polyFun_fst polyFun_snd) |>.pair (ofPoly h4 _ _)).comp_poly
      (polyFun_and polyFun_fst polyFun_snd) |>.of_eq (fun _ => rfl)
  have harg := (hhdr.comp_poly (polyFun_fst.pair (pfst polyFun_snd))).pair
    (ofPoly (pfst (pfst (pfst (pfst i)))) Pre 5)
  have hall := htest.pair (harg.pair (ofPoly (pfst (psnd i)) _ _))
  exact (hall.comp_poly (PolyFun.ite polyFun_fst
    ((psnd polyFun_id).comp (polyFun_alignDomHintAt.comp polyFun_some))
    (polyFun_const none))).of_eq (fun z => by
      unfold Algo.masterL57Hint
      cases Algo.masterL57HintTest c b t d dc dp u v e f z <;> rfl)

end TN

end Explicit
