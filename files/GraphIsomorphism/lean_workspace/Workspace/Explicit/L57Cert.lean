/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the certificate phase of
Procedure AggregateCertificates (Sec. 13.2) at lines 5–7 of the Master (Sec. 15), bounded at an
external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.S9AlignDom

/-!
# The certificate phase, bounded at the degree

The only quasipolynomial work of the certificate phase is the guarded tuple table
(`Algo.aggTable c`): the test sets `T ∈ Γ^t` (`Algo.aggTestSetsOn`) and the fuel of the
canonical coset representatives (`Algo.aggkRepFuel`, `|T|^{|T|}` entries). Both are bounded
at exponent `c + 1` once the guard witness (the string of the context, of length `|Δ|`) and the
domain `Γ` have at most `n` elements:

* `Explicit.CtxOK n C`: the context of the phase has short strings and a short domain `Γ`;
* `Explicit.LoopOK n p`: the loop of a certificate works on a short string.

The loops that the phase opens always take their string from the context
(`Algo.aggnJobLoop`), and a step of a loop keeps it (`Algo.lcStepWith`); so the only condition
on the state is that its current loop has a short string (`Explicit.PhaseStOK`).
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

private theorem pif {α β : Type*} [Enc α] [Enc β] {p : α → Prop}
    [∀ a, Decidable (p a)] {f g : α → β}
    (hp : PolyFun (fun a => decide (p a))) (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => if p a then f a else g a) :=
  (PolyFun.ite hp hf hg).of_eq (fun a => by simp)

private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

/-- A copy of the private `Algo.aggnPolyFun_phaseChildAtWidth`: the child of the certificate
phase once the width is given. -/
theorem polyFun_phaseChildAtWidth :
    PolyFun (fun p : ℕ × (AggnPhaseNode × ℕ × AggnPhaseState) =>
      p.2.1.2.elim
        (if p.2.2.1 < p.1 then
          match p.2.2.2.1 with
          | [] => none
          | a :: _ =>
            (aggnCertChild ((aggnJobLoop p.2.1.1 a, none),
              p.2.2.2.2.2.1, p.2.2.2.2.2.2)).map (fun J => (p.2.1.1, J.2))
        else none) (fun _ => none)) := by
  let X := ℕ × (AggnPhaseNode × ℕ × AggnPhaseState)
  have hC : PolyFun (fun z : X => z.2.1.1) := pfst (pfst polyFun_snd)
  have hs : PolyFun (fun z : X => z.2.2.2) := psnd (psnd polyFun_snd)
  have hj : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have hj' := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have hbody : PolyFun (fun z : (AggnJob × List AggnJob) × X =>
      (aggnCertChild ((aggnJobLoop z.2.2.1.1 z.1.1, none),
        z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2)).map (fun J => (z.2.2.1.1, J.2))) := by
    have hp : PolyFun (fun z : (AggnJob × List AggnJob) × X =>
        aggnJobLoop z.2.2.1.1 z.1.1) :=
      ((polyFun_snd.comp hC).pair (pfst polyFun_fst)).comp aggnPolyFun_jobLoop
    have hi := (hp.pair (polyFun_const (none : Option RawWinSI))).pair
      ((polyFun_snd.comp hj').pair (polyFun_snd.comp hv))
    have hf : PolyFun (fun z : AggnCertNode × ((AggnJob × List AggnJob) × X) =>
        (z.2.2.2.1.1, z.1.2)) :=
      ((psnd polyFun_snd).comp hC).pair (psnd polyFun_fst)
    exact ((hi.comp aggnPolyFun_certChild).pair polyFun_id).comp (pmap hf)
  have hlist := ((pfst hs).pair polyFun_id).comp
    (PolyFun.listCases (polyFun_const none) hbody)
  have htest := (hj.pair polyFun_fst).comp plt
  have hrun := pif htest hlist (polyFun_const none)
  have ho : PolyFun (fun z : X => z.2.1.2) := psnd (pfst polyFun_snd)
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun p => by
      simp only [id_eq]
      cases p.2.2.2.1 <;> rfl)

/-- The guard of the tuple table is polynomial in the length of its witness. -/
theorem guardBound_le_pow {c m n : ℕ} (h : m ≤ n) : guardBound c m ≤ (n + 1) ^ (c + 1) := by
  unfold guardBound
  calc (Nat.log 2 m + 1) ^ c ≤ (n + 1) ^ c :=
        Nat.pow_le_pow_left (by have := log_two_le_self m; omega) c
    _ ≤ (n + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The context of the phase at degree `n`. -/
def CtxOK (n : ℕ) (C : AggnPhaseCtx) : Prop :=
  C.2.1.length ≤ n ∧ C.2.2.1.length ≤ n ∧ C.1.2.1.length ≤ n

/-- The loop of a certificate at degree `n`: its string is short. -/
def LoopOK (n : ℕ) (p : RawLCLoop) : Prop := p.1.1.length ≤ n

/-- The state of the certificate phase at degree `n`: its current loop is short. -/
def PhaseStOK (n : ℕ) (v : AggnPhaseState) : Prop := LoopOK n v.2.2.2.1

theorem loopOK_jobLoop {n : ℕ} {C : AggnPhaseCtx} (h : CtxOK n C) (a : AggnJob) :
    LoopOK n (aggnJobLoop C a) := by
  unfold LoopOK aggnJobLoop
  cases a.1
  · exact h.1
  · exact h.2.1

theorem loopOK_stepWith {n : ℕ} {p : RawLCLoop} (h : LoopOK n p) (a : RawCoset) :
    LoopOK n (lcStepWith a p) := by
  unfold LoopOK lcStepWith
  split_ifs
  · exact h
  · exact h

theorem loopOK_empty (n : ℕ) : LoopOK n ((([], []), ([], [], [])) : RawLCLoop) := by
  unfold LoopOK; simp

namespace TN

/-- **The guarded tuple table whose tuples are over the arity list itself**, at a guard witness
of at most `n` elements. -/
theorem aggTableSame (c : ℕ) :
    TN (Algo.aggTable c) (fun n (a : RawAggTestInput) => a.2.1.length ≤ n ∧ a.1 = a.2.2)
      (c + 1) :=
  (TN.aggTable c).scale 0 (c + 1) (fun n a ha => ⟨(n + 1) ^ (c + 1),
    by rw [pow_zero, one_mul],
    (ha.1.trans ((Nat.le_succ n).trans (Nat.le_self_pow (by omega) _))), fun hg => by
      rw [← ha.2]; exact hg.trans (guardBound_le_pow ha.1)⟩)

/-- **The test sets on `Γ`**, at a guard witness and a domain of at most `n` elements. -/
theorem aggTestSetsOn (c : ℕ) :
    TN (Algo.aggTestSetsOn c)
      (fun n (p : RawAggTestInput) => p.2.1.length ≤ n ∧ p.2.2.length ≤ n) (c + 1) := by
  have ht : TN (fun p : RawAggTestInput =>
      (Algo.aggTable c (p.1, p.2.1, List.range p.2.2.length)).2.map Prod.fst)
      (fun n (p : RawAggTestInput) => p.2.1.length ≤ n ∧ p.2.2.length ≤ n) (c + 1) :=
    ((poly_comp (polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_rangeLength))) (TN.aggTable c)).restrict
        (fun n p hp => ⟨hp.1, fun _ => by simpa using hp.2⟩)).comp_poly
      (polyFun_snd.comp (PolyFun.map polyFun_fst))
  have hf : PolyFun (fun z : List ℕ × List ℕ => decide (z.2 = aggNormalizeRow z)) :=
    (polyFun_snd.pair aggPolyFun_normalizeRow).comp polyFun_listNatEq
  exact (((ofPoly (polyFun_snd.comp polyFun_snd) _ _).pair ht).comp_poly
    (PolyFun.filterParam hf)).of_eq (fun _ => rfl)

theorem aggnPhaseRows (c : ℕ) : TN (Algo.aggnPhaseRows c) CtxOK (c + 1) :=
  (poly_comp ((psnd (psnd (psnd polyFun_id))).pair ((pfst (psnd polyFun_id)).pair
    (pfst (psnd (pfst polyFun_id))))) (aggTestSetsOn c)).restrict
    (fun n C h => ⟨h.1, h.2.2⟩) |>.of_eq (fun _ => rfl)

theorem aggnPhaseJobs (c : ℕ) : TN (Algo.aggnPhaseJobs c) CtxOK (c + 1) := by
  have hf := (aggnPhaseRows c).comp_poly (PolyFun.map ((polyFun_const false).pair polyFun_id))
  have ht := (aggnPhaseRows c).comp_poly (PolyFun.map ((polyFun_const true).pair polyFun_id))
  exact ((hf.pair ht).comp_poly polyFun_append).of_eq (fun C => by
    simp only [Algo.aggnPhaseJobs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl)

theorem aggnPhaseWidth (c : ℕ) : TN (Algo.aggnPhaseWidth c) CtxOK (c + 1) := by
  have hC : PolyFun (fun C : AggnPhaseCtx => C) := polyFun_id
  have hx := pfst (psnd hC)
  have ht := psnd (psnd (psnd hC))
  have hn := hx.comp polyFun_length
  have hfact := ht.comp (polyFun_length.factorial length_le_size polyBound_id)
  have hwidth := (hn.pair ((hfact.pair hn).comp polyFun_mul)).comp polyFun_mul
  have hlen := ((const' 2 _ _).pair ((aggnPhaseRows c).comp_poly polyFun_length)).comp_poly
    polyFun_mul
  exact ((hlen.pair (ofPoly hwidth _ _)).comp_poly polyFun_mul).of_eq (fun C => by
    simp [Algo.aggnPhaseWidth, Algo.aggnPhaseJobs, Algo.aggnPhaseRows, two_mul])

/-! ## One certificate -/

theorem aggkRepFuel (c : ℕ) : TN (Algo.aggkRepFuel c) LoopOK (c + 1) := by
  have hinput : PolyFun (fun p : RawLCLoop => (p.1.2, p.1.1, p.1.2)) :=
    polyFun_lcTdom.pair (polyFun_lcStr.pair polyFun_lcTdom)
  have hrows := ((poly_comp hinput (aggTableSame c)).restrict
    (fun n p (hp : LoopOK n p) => ⟨hp, rfl⟩)).comp_poly (polyFun_snd.comp polyFun_rangeLength)
  exact ((hrows.pair (ofPoly polyFun_lcIdx _ _)).comp_poly polyFun_take).of_eq (fun _ => rfl)

theorem aggkRawReps (c : ℕ) : TN (Algo.aggkRawReps c) LoopOK (c + 1) :=
  ((((id' _ _).pair (aggkRepFuel c)).comp_poly (PolyFun.mapParam aggkPolyFun_repRow)).comp_poly
    aggkPolyFun_sortRows).comp_poly (PolyFun.map polyFun_snd) |>.of_eq (fun _ => rfl)

theorem aggnrInputOf (c : ℕ) : TN (Algo.aggnrInputOf c) LoopOK (c + 1) := by
  have hi := polyFun_lcInst.comp polyFun_fst
  have hk := ((polyFun_lcTdom.pair polyFun_lcImgsOf).pair hi).comp polyFun_lcKer
  have hw := (hk.pair (pfst hi)).comp polyFun_winOrbits
  exact (ofPoly hi _ _).pair ((ofPoly hk _ _).pair ((aggkRawReps c).pair (ofPoly hw _ _)))

theorem aggnCertOpen (c : ℕ) : TN (Algo.aggnCertOpen c) LoopOK (c + 1) := by
  have hp := aggnrInputOf c
  have hi := (hp.pair (const' (none : Option RawWinSI) _ _)).comp_poly
    aggnPolyFun_recomputeInit
  exact (id' _ _).pair (hp.pair ((const' 0 _ _).pair hi))

theorem aggnCertPack (c : ℕ) :
    TN (fun z : RawLCLoop × ℕ × AggnRecomputeState => Algo.aggnCertPack c z.1 z.2.1 z.2.2)
      (fun n z => LoopOK n z.1) (c + 1) := by
  have hp : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.1) := polyFun_fst
  have hj : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.2.1) := pfst polyFun_snd
  have hv : PolyFun (fun z : RawLCLoop × ℕ × AggnRecomputeState => z.2.2) := psnd polyFun_snd
  have hcache : TN (fun z : RawLCLoop × ℕ × AggnRecomputeState => Algo.aggnrInputOf c z.1)
      (fun n z => LoopOK n z.1) (c + 1) := poly_comp hp (aggnrInputOf c)
  have hcount := hcache.comp_poly ((pfst (psnd polyFun_snd)).comp polyFun_length)
  have htest := ((ofPoly (((pfst hv).pair (polyFun_const 1)).comp polyFun_add) _ _).pair
    hcount).comp_poly polyFun_le
  have hthen := (ofPoly hp _ _).pair (hcache.pair (ofPoly (hj.pair hv) _ _))
  have helse : TN (fun z : RawLCLoop × ℕ × AggnRecomputeState =>
      Algo.aggnCertOpen c (lcStepWith z.2.2.2.2.2 z.1)) (fun n z => LoopOK n z.1) (c + 1) :=
    (poly_comp (((psnd (psnd (psnd hv))).pair hp).comp lcwPolyFun_step) (aggnCertOpen c)).restrict
      (fun n z h => loopOK_stepWith h _)
  exact (iteT htest hthen helse).of_eq (fun z => by
    simp only [Algo.aggnCertPack, aggnrCount, Nat.add_one_le_iff, decide_eq_true_eq]
    rfl)

theorem aggnCertCombine (c : ℕ) :
    TN (Algo.aggnCertCombine c) (fun n z => LoopOK n z.2.2.1.1) (c + 1) := by
  have hz : PolyFun (fun z : AggnCertNode × ℕ × AggnCertState × RawCoset => z) := polyFun_id
  have hs := pfst (psnd (psnd hz))
  have hP := pfst (psnd hs)
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hr := (((hP.pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair (hv.pair ha))).comp aggnPolyFun_recomputeCombine)
  exact (poly_comp ((pfst hs).pair (((hj.pair (polyFun_const 1)).comp polyFun_add).pair hr))
    (aggnCertPack c)).of_eq (fun _ => rfl)

/-! ## The phase -/

theorem aggnReadyJob (c : ℕ) :
    TN (Algo.aggnReadyJob c) (fun n p => CtxOK n p.1) (c + 1) := by
  have hpack : PolyFun (fun p : AggnJob × AggnCertState =>
      (p.1, p.2, aggPack (p.2.1.1.1, p.1.2, aggnCertOut p.2))) := by
    have hp : PolyFun (fun p : AggnJob × AggnCertState => p) := polyFun_id
    have ha := pfst hp
    have hv := psnd hp
    have he := ((pfst (pfst (pfst hv))).pair ((psnd ha).pair
      ((pfst hv).comp lcwPolyFun_out))).comp aggPolyFun_pack
    exact ha.pair (hv.pair he)
  have hv : TN (fun p : AggnPhaseCtx × AggnJob => Algo.aggnCertOpen c (aggnJobLoop p.1 p.2))
      (fun n p => CtxOK n p.1) (c + 1) :=
    (poly_comp aggnPolyFun_jobLoop (aggnCertOpen c)).restrict
      (fun n p h => loopOK_jobLoop h p.2)
  exact ((ofPoly polyFun_snd _ _).pair hv).comp_poly hpack

theorem aggnPhaseScan (c : ℕ) :
    TN (fun z : AggnPhaseCtx × List AggnJob × AggnStores => Algo.aggnPhaseScan c z.1 z.2.1 z.2.2)
      (fun n z => CtxOK n z.1) (c + 1) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × List AggnJob × AggnStores => z) := polyFun_id
  have hprep := (poly_comp ((pfst hz).pair (pfst (psnd hz))) (mapParam (aggnReadyJob c))).restrict
    (fun n z (h : CtxOK n z.1) a _ => h)
  have hm := (hprep.pair (ofPoly (psnd (psnd hz)) _ _)).comp_poly
    (aggnPolyFun_readyScan (Algo.aggnCertOpen c (([], []), ([], [], []))))
  exact hm.of_eq (fun z => aggnReadyJob_scan c z.1 z.2.1 z.2.2)

theorem aggnPhasePack (c : ℕ) :
    TN (fun z : AggnPhaseCtx × AggnJob × List AggnJob × AggnStores × ℕ × AggnCertState =>
      Algo.aggnPhasePack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2)
      (fun n z => CtxOK n z.1) (c + 1) := by
  let X := AggnPhaseCtx × AggnJob × List AggnJob × AggnStores × ℕ × AggnCertState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst hz
  have ha := pfst (psnd hz)
  have hr := pfst (psnd (psnd hz))
  have hs := pfst (psnd (psnd (psnd hz)))
  have hj := pfst (psnd (psnd (psnd (psnd hz))))
  have hv := psnd (psnd (psnd (psnd (psnd hz))))
  have ht := (pfst hv).comp polyFun_lcCond
  have hthen := ((ha.pair hr).comp polyFun_cons).pair (hs.pair (hj.pair hv))
  have hstore := (ha.pair (hv.pair hs)).comp aggnPolyFun_storeJob
  have helse : TN (fun z : X => Algo.aggnPhaseScan c z.1 z.2.2.1
      (aggnStoreJob z.2.1 z.2.2.2.2.2 z.2.2.2.1)) (fun n z => CtxOK n z.1) (c + 1) :=
    poly_comp (hC.pair (hr.pair hstore)) (aggnPhaseScan c)
  exact (TN.ite ht (ofPoly hthen _ _) helse (fun _ _ _ _ => trivial)
    (fun _ _ h _ => h)).of_eq (fun _ => rfl)

/-- **One combine of the certificate phase**, on a state whose current loop is short. -/
theorem aggnPhaseCombine (c : ℕ) :
    TN (Algo.aggnPhaseCombine c) (fun n z => CtxOK n z.1.1 ∧ PhaseStOK n z.2.2.1) (c + 1) := by
  let X := AggnPhaseNode × ℕ × AggnPhaseState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst (pfst hz)
  have hs := pfst (psnd (psnd hz))
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hstores := pfst (psnd hs)
  have hnil : TN (fun z : X => Algo.aggnPhaseScan c z.1.1 [] z.2.2.1.2.1)
      (fun n z => CtxOK n z.1.1 ∧ PhaseStOK n z.2.2.1) (c + 1) :=
    (poly_comp (hC.pair ((polyFun_const ([] : List AggnJob)).pair hstores))
      (aggnPhaseScan c)).restrict (fun _ _ h => h.1)
  have hcons : TN (fun z : (AggnJob × List AggnJob) × X =>
      Algo.aggnPhasePack c z.2.1.1 z.1.1 z.1.2 z.2.2.2.1.2.1 (z.2.2.2.1.2.2.1 + 1)
        (Algo.aggnCertCombine c ((aggnJobLoop z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2)))
      (fun n z => CtxOK n z.2.1.1 ∧ PhaseStOK n z.2.2.2.1) (c + 1) := by
    have hctx : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.1.1) := polyFun_snd.comp hC
    have hjob : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.1.1) := pfst polyFun_fst
    have hrest : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.1.2) := psnd polyFun_fst
    have hstore : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.2.2.1.2.1) :=
      polyFun_snd.comp hstores
    have hidx : PolyFun (fun z : (AggnJob × List AggnJob) × X => z.2.2.2.1.2.2.1) :=
      polyFun_snd.comp hj
    have hloop := (hctx.pair hjob).comp aggnPolyFun_jobLoop
    have hinput := (hloop.pair (polyFun_const (none : Option RawWinSI))).pair
      (hidx.pair ((polyFun_snd.comp hv).pair (polyFun_snd.comp ha)))
    have hnext : TN (fun z : (AggnJob × List AggnJob) × X =>
        Algo.aggnCertCombine c ((aggnJobLoop z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2))
        (fun n z => CtxOK n z.2.1.1 ∧ PhaseStOK n z.2.2.2.1) (c + 1) :=
      (poly_comp hinput (aggnCertCombine c)).restrict (fun _ _ h => h.2)
    have hidx' := (hidx.pair (polyFun_const 1)).comp polyFun_add
    have hpack := (ofPoly hctx _ _).pair ((ofPoly hjob _ _).pair ((ofPoly hrest _ _).pair
      ((ofPoly hstore _ _).pair ((ofPoly hidx' _ _).pair hnext))))
    exact (hpack.comp (aggnPhasePack c) (fun _ _ h => h.1)).of_eq (fun z => by dsimp only)
  have hm := (ofPoly ((pfst hs).pair hz)
    (fun n (z : X) => CtxOK n z.1.1 ∧ PhaseStOK n z.2.2.1) (c + 1)).comp
    (listCases (Pre := fun n (q : List AggnJob × X) => CtxOK n q.2.1.1 ∧ PhaseStOK n q.2.2.2.1)
      hnil hcons (fun _ _ h => h) (fun _ _ _ _ h => h)) (fun _ _ h => h)
  exact hm.of_eq (fun z => by unfold Algo.aggnPhaseCombine; cases z.2.2.1.1 <;> rfl)

theorem aggnPhaseInit (c n : ℕ) :
    TN (aggnCheckedRound c n).init (fun n I => CtxOK n I.1) (c + 1) := by
  have hC : PolyFun (fun I : AggnPhaseNode => I.1) := polyFun_fst
  have hj := poly_comp hC (aggnPhaseJobs c)
  have hi := (ofPoly hC _ _).pair (hj.pair (const' (([], []) : AggnStores) _ _))
  exact (hi.comp (aggnPhaseScan c) (fun _ _ h => h)).of_eq (fun _ => rfl)

/-- **The child of the certificate phase**: only the width reads the context; the rest is
polynomial. -/
theorem aggnCheckedChild (c : ℕ) :
    TN (Algo.aggnCheckedChild c) (fun n z => CtxOK n z.1.1) (c + 1) := by
  have hC : PolyFun (fun z : AggnPhaseNode × ℕ × AggnPhaseState => z.1.1) := pfst polyFun_fst
  have hf : PolyFun (fun z : AggnPhaseNode × Option AggnPhaseNode => aggnCheckedNode z.1) :=
    polyFun_fst.comp aggnPolyFun_checkedNode
  have hm : PolyFun (fun o : Option AggnPhaseNode => o.map aggnCheckedNode) :=
    ((polyFun_id.pair polyFun_id).comp (pmap hf)).of_eq (fun _ => rfl)
  exact ((((poly_comp hC (aggnPhaseWidth c)).pair (id' _ _)).comp_poly
    polyFun_phaseChildAtWidth).comp_poly hm).of_eq (fun _ => rfl)

end TN

end Explicit
