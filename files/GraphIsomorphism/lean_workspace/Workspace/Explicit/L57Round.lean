/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the round of lines 5–7 of
the Master (Sec. 15) on its window, bounded at an external degree. Not part of the faithful
formalization.
-/
import Workspace.Explicit.L57Cont

/-!
# The round of lines 5–7, bounded at the degree

The round runs the two phases of AggregateCertificates, reads the dispatch of Theorem 13.2.1,
and runs Procedure Align over the versions (stretch 3). Its header (`Algo.aggnL57Hdr`) is
recomputed at every step from the stores through the continuation, and the loop of stretch 3
is bounded at the degree by `Workspace/Explicit/S9AlignDom.lean` once the action of the
header has at most `n` points (`Explicit.L57CtxOK`).
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

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
private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

/-- The context of the round of lines 5–7 at degree `n`: the context of the continuation, and
an action on at most `n` points. -/
def L57CtxOK (c n : ℕ) (C : AggnPhaseCtx) : Prop := ContCtxOK c n C ∧ C.1.1.1.length ≤ n

theorem avHdrOK_aggnL57Hdr {c b t d dc dp n : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    (h : L57CtxOK c n C) : AVHdrOK n (aggnL57Hdr c b t d dc dp (C, s)) := h.2

namespace TN

variable {c b t d : ℕ}

/-! ## The header -/

theorem aggnL57HdrCore (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57HdrCore c b t d) (fun n z => ContCtxOK c n z.1) 5 := by
  have i : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z) := polyFun_id
  have hA := pfst (pfst i)
  have hx := pfst (psnd (pfst i))
  have hy := pfst (psnd (psnd (pfst i)))
  have ho : TN (aggnL57Cont c b t d) (fun n z => ContCtxOK c n z.1) 5 :=
    aggnContinuation (d := d) hc hb ht
  have hfix : PolyFun aggnL57Fixed :=
    ((((polyFun_snd.comp polyFun_fst).comp polyFun_headOption).pair
      (polyFun_const ((none, none) : RawAlignOutcome))).comp polyFun_optionGetD).of_eq
      (fun o => by unfold aggnL57Fixed; cases o.2.1 <;> rfl)
  have hX := ho.comp_poly hfix
  have hvers := ho.comp_poly (polyFun_snd.comp polyFun_snd)
  have hwin := ((ofPoly hA _ _).pair hX).comp_poly polyFun_alignL57Windows
  exact ((ofPoly hA _ _).pair (hX.pair (hvers.pair (hwin.pair
    ((ofPoly hx _ _).pair (ofPoly hy _ _)))))).of_eq (fun _ => rfl)

theorem aggnL57Hdr (dc dp : ℕ) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57Hdr c b t d dc dp) (fun n z => ContCtxOK c n z.1) 5 := by
  have hp : TN (fun z : AggnPhaseCtx × AggnAggregateState =>
      (z.1, Algo.aggnAggregatePack c dc dp z.1 z.2)) (fun n z => ContCtxOK c n z.1) 5 :=
    (ofPoly polyFun_fst _ _).pair
      (((aggnAggregatePack c dc dp).mono_k (by omega)).restrict (fun _ _ h => h.1))
  exact (hp.comp (aggnL57HdrCore (d := d) hc hb ht) (fun _ _ h => h)).of_eq (fun _ => rfl)

/-! ## Stretch 3 -/

theorem aggnL57AlignChild (dc dp : ℕ) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57AlignChild c b t d dc dp) (fun n z => L57CtxOK c n z.1.1) 5 := by
  let X := AggnPhaseNode × ℕ × AggnL57State
  have z : PolyFun (fun q : X => q) := polyFun_id
  have hC := pfst (pfst z)
  have hj := pfst (psnd z)
  have hs := pfst (psnd (psnd z))
  have hst := psnd (psnd (psnd z))
  have hh : TN (fun q : X => Algo.aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1))
      (fun n q => L57CtxOK c n q.1.1) 5 :=
    (poly_comp (hC.pair hs) (aggnL57Hdr (d := d) dc dp hc hb ht)).restrict
      (fun _ _ h => h.1)
  have hok : ∀ n (q : X), L57CtxOK c n q.1.1 →
      AVHdrOK n (Algo.aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1)) :=
    fun _ _ h => avHdrOK_aggnL57Hdr h
  have hcalls := hh.comp (l57Calls.mono_k (by omega)) hok
  have hwidth : TN (fun q : X => Algo.aggnAggregateWidth c q.1.1)
      (fun n q => L57CtxOK c n q.1.1) 5 :=
    (poly_comp hC ((aggnAggregateWidth c).mono_k (by omega))).restrict (fun _ _ h => h.1.1)
  have hgate := ((ofPoly hj _ _).pair ((hwidth.pair hcalls).comp_poly polyFun_add)).comp_poly plt
  have hinit := hh.comp (l57Init.mono_k (by omega)) hok
  have hget := ((ofPoly hst _ _).pair hinit).comp_poly polyFun_optionGetD
  have hch := (hh.pair hget).comp (l57Child.mono_k (by omega)) (fun n q h => hok n q h)
  have hemb : PolyFun (fun p : RawWinSI × AggnPhaseCtx => avEmb (p.2, p.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_avEmb
  have hmap := (hch.pair (ofPoly hC _ _)).comp_poly (pmap hemb)
  have hrun := iteT hgate hmap (const' none _ _)
  exact ((ofPoly ((psnd (pfst z)).pair z) (fun n (q : X) => L57CtxOK c n q.1.1) 5).comp
    (optionElim (Pre := fun n (q : Option RawWinSI × X) => L57CtxOK c n q.2.1.1) hrun
      (const' none (fun n (q : RawWinSI × X) => L57CtxOK c n q.2.1.1) _) (fun _ _ h => h)
      (fun _ _ _ h => h)) (fun _ _ h => h)).of_eq
    (fun q => by simp only [Algo.aggnL57AlignChild, decide_eq_true_eq])

/-! ## The round -/

theorem aggnL57Child (dc dp : ℕ) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57Child c b t d dc dp) (fun n z => L57CtxOK c n z.1.1) 5 := by
  let X := AggnPhaseNode × ℕ × AggnL57State
  have z : PolyFun (fun q : X => q) := polyFun_id
  have hagg : TN (fun q : X => Algo.aggnAggregateChild c (q.1, q.2.1, q.2.2.1))
      (fun n q => L57CtxOK c n q.1.1) 5 :=
    (poly_comp ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z)))))
      ((aggnAggregateChild c).mono_k (by omega))).restrict (fun _ _ h => h.1.1)
  exact ((hagg.pair (id' _ _)).comp
    (optionElim (Pre := fun n (q : Option AggnPhaseNode × X) => L57CtxOK c n q.2.1.1)
      (aggnL57AlignChild (d := d) dc dp hc hb ht)
      (ofPoly (polyFun_fst.comp polyFun_some) (fun _ (_ : AggnPhaseNode × X) => True) _)
      (fun _ _ h => h) (fun _ _ _ _ => trivial))
    (fun _ _ h => h)).of_eq (fun q => by unfold Algo.aggnL57Child; rfl)

theorem aggnL57Combine (dc dp : ℕ) (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57Combine c b t d dc dp)
      (fun n z => L57CtxOK c n z.1.1 ∧ AggStOK n z.2.2.1.1) 5 := by
  let X := AggnPhaseNode × ℕ × AggnL57State × RawCoset
  let Pre := fun n (q : X) => L57CtxOK c n q.1.1 ∧ AggStOK n q.2.2.1.1
  have z : PolyFun (fun q : X => q) := polyFun_id
  have hI := pfst z
  have hC := pfst hI
  have hj := pfst (psnd z)
  have hs := pfst (pfst (psnd (psnd z)))
  have hst := psnd (pfst (psnd (psnd z)))
  have ha := psnd (psnd (psnd z))
  have hagg : TN (fun q : X => Algo.aggnAggregateChild c (q.1, q.2.1, q.2.2.1.1)) Pre 5 :=
    (poly_comp (hI.pair (hj.pair hs)) ((aggnAggregateChild c).mono_k (by omega))).restrict
      (fun _ _ h => h.1.1.1)
  have hh : TN (fun q : X => Algo.aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1.1)) Pre 5 :=
    (poly_comp (hC.pair hs) (aggnL57Hdr (d := d) dc dp hc hb ht)).restrict
      (fun _ _ h => h.1.1)
  have hok : ∀ n (q : X), Pre n q →
      AVHdrOK n (Algo.aggnL57Hdr c b t d dc dp (q.1.1, q.2.2.1.1)) :=
    fun _ _ h => avHdrOK_aggnL57Hdr h.1
  have hinit := hh.comp (l57Init.mono_k (by omega)) hok
  have hget := ((ofPoly hst _ _).pair hinit).comp_poly polyFun_optionGetD
  have hstep := (hh.pair (hget.pair (ofPoly ha _ _))).comp (l57Step.mono_k (by omega))
    (fun n q h => hok n q h)
  have hpack : TN (fun q : X => Algo.aggnAggregatePack c dc dp q.1.1 q.2.2.1.1) Pre 5 :=
    (poly_comp (hC.pair hs) ((aggnAggregatePack c dc dp).mono_k (by omega))).restrict
      (fun _ _ h => h.1.1.1)
  have hnone := hpack.pair (hstep.comp_poly polyFun_some)
  have hcomb : TN (fun q : X => Algo.aggnAggregateCombine c dc dp (q.1, q.2.1, q.2.2.1.1, q.2.2.2))
      Pre 5 :=
    (poly_comp (hI.pair (hj.pair (hs.pair ha))) ((aggnAggregateCombine c dc dp).mono_k
      (by omega))).restrict (fun _ _ h => ⟨h.1.1.1, h.2⟩)
  have hsome := hcomb.pair (const' (none : Option ADState) _ _)
  exact ((hagg.pair (id' _ _)).comp
    (optionElim (Pre := fun n (q : Option AggnPhaseNode × X) => Pre n q.2)
      hnone (poly_comp polyFun_snd hsome) (fun _ _ h => h) (fun _ _ _ h => h))
    (fun _ _ h => h)).of_eq (fun q => by unfold Algo.aggnL57Combine; rfl)

theorem aggnL57Finish : TN Algo.aggnL57Finish (fun _ _ => True) 5 :=
  ofPoly polyFun_aggnL57Finish _ _

end TN

end Explicit
