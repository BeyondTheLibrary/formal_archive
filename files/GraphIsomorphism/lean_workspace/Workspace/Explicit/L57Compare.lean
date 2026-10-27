/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the comparison phase of
Procedure AggregateCertificates (Sec. 13.2) and the two phases together, bounded at an external
degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.L57Cert

/-!
# The comparison phase and the aggregate carrier, bounded at the degree

As for the certificate phase (`Workspace/Explicit/L57Cert.lean`), the only quasipolynomial
work is the guarded tuple table, read on the context and on the loop of the current
comparison. A comparison opens its loop on the source string of the context
(`Algo.aggnPairPrepare`), and a step keeps it, so the only condition on the states is that
the current loops are short (`Explicit.AggStOK`).
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
private theorem comparePolyFun_product {α β : Type*} [Enc α] [Enc β] :
    PolyFun (fun p : List α × List β => p.1.product p.2) := by
  have h : PolyFun (fun p : List β × α => p.1.map (fun b => (p.2, b))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam (polyFun_fst.pair polyFun_snd))
  exact ((polyFun_snd.pair polyFun_fst).comp h.flatMapParam).of_eq (fun _ => rfl)

/-- A copy of the private `Algo.aggnPolyFun_compareChildAtWidth`. -/
theorem polyFun_compareChildAtWidth :
    PolyFun (fun p : ℕ × (AggnPhaseNode × ℕ × AggnCompareState) =>
      p.2.1.2.elim
        (if p.2.2.1 < p.1 then
          match p.2.2.2.1 with
          | [] => none
          | a :: _ =>
            (aggnPairChild ((aggnCompareCtx p.2.1.1 a, none),
              p.2.2.2.2.2.1, p.2.2.2.2.2.2)).map (fun J => (p.2.1.1, J.2))
        else none) (fun _ => none)) := by
  let X := ℕ × (AggnPhaseNode × ℕ × AggnCompareState)
  have hC : PolyFun (fun z : X => z.2.1.1) := pfst (pfst polyFun_snd)
  have hs : PolyFun (fun z : X => z.2.2.2) := psnd (psnd polyFun_snd)
  have hj : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have hj' := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have hbody : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
      (aggnPairChild ((aggnCompareCtx z.2.2.1.1 z.1.1, none),
        z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2)).map (fun J => (z.2.2.1.1, J.2))) := by
    have hp : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
        aggnCompareCtx z.2.2.1.1 z.1.1) :=
      ((polyFun_snd.comp hC).pair (pfst polyFun_fst)).comp aggnPolyFun_compareCtx
    have hi := (hp.pair (polyFun_const (none : Option RawWinSI))).pair
      ((polyFun_snd.comp hj').pair (polyFun_snd.comp hv))
    have hf : PolyFun (fun z : AggnPairNode × ((AggnCompareJob × List AggnCompareJob) × X) =>
        (z.2.2.2.1.1, z.1.2)) :=
      ((psnd polyFun_snd).comp hC).pair (psnd polyFun_fst)
    exact ((hi.comp aggnPolyFun_pairChild).pair polyFun_id).comp (pmap hf)
  have hlist := ((pfst hs).pair polyFun_id).comp
    (PolyFun.listCases (polyFun_const none) hbody)
  have htest := (hj.pair polyFun_fst).comp plt
  have hrun := pif htest hlist (polyFun_const none)
  have ho : PolyFun (fun z : X => z.2.1.2) := psnd (pfst polyFun_snd)
  exact ((ho.pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun p => by
      simp only [id_eq]
      cases p.2.2.2.1 <;> rfl)

/-- The state of the comparison phase at degree `n`: its current loop is short. -/
def CompStOK (n : ℕ) (v : AggnCompareState) : Prop := LoopOK n v.2.2.2.1

/-- The state of both phases at degree `n`: both current loops are short. -/
def AggStOK (n : ℕ) (s : AggnAggregateState) : Prop := PhaseStOK n s.1 ∧ CompStOK n s.2.2

theorem loopOK_compareCtx {n : ℕ} {C : AggnPhaseCtx} (h : CtxOK n C) (a : AggnCompareJob) :
    LoopOK n (aggnCompareCtx C a).1 := h.1

namespace TN

/-! ## One comparison -/

theorem aggnCompareInputOf (c : ℕ) :
    TN (Algo.aggnCompareInputOf c) (fun n z => LoopOK n z.1) (c + 1) := by
  have hp : TN (fun z : AggnCompareInput => Algo.aggnrInputOf c z.1) (fun n z => LoopOK n z.1)
      (c + 1) := poly_comp polyFun_fst (aggnrInputOf c)
  have hx : PolyFun (fun z : AggnCompareInput => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hq : PolyFun (fun z : AggnCompareInput => z.2.2) := polyFun_snd.comp polyFun_snd
  have hrs := hp.comp_poly ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have ht := ((ofPoly hx _ _).pair ((ofPoly hq _ _).pair hrs)).comp_poly
    aggnPolyFun_translateReps
  exact (ofPoly aggnPolyFun_compareWindow _ _).pair
    ((hp.comp_poly (polyFun_snd.comp polyFun_fst)).pair
      (ht.pair (hp.comp_poly ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))))

theorem aggnPairInput (c : ℕ) :
    TN (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      Algo.aggnPairInput c z.1 z.2.1 z.2.2.1 z.2.2.2) (fun n z => LoopOK n z.1) (c + 1) := by
  have hp : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z.1) :=
    polyFun_fst
  have hy : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z.2.1) :=
    pfst polyFun_snd
  have hq := pfst (psnd (psnd (polyFun_id : PolyFun
    (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z))))
  have hm := psnd (psnd (psnd (polyFun_id : PolyFun
    (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z))))
  have hs : TN (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      Algo.aggnrInputOf c z.1) (fun n z => LoopOK n z.1) (c + 1) := poly_comp hp (aggnrInputOf c)
  have ht : TN (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      Algo.aggnCompareInputOf c (z.1, z.2.1, z.2.2.1)) (fun n z => LoopOK n z.1) (c + 1) :=
    poly_comp (hp.pair (hy.pair hq)) (aggnCompareInputOf c)
  exact ((ofPoly (hm.pair polyFun_id) (fun n z => LoopOK n z.1) (c + 1)).comp
    (optionElim (Pre := fun n (q : Option RawCoset ×
      (RawLCLoop × RawStr × RawCoset × Option RawCoset)) => LoopOK n q.2.1)
      hs (poly_comp polyFun_snd ht) (fun _ _ h => h) (fun _ _ _ h => h))
    (fun _ _ h => h)).of_eq (fun _ => rfl)

theorem aggnPairStart (c : ℕ) :
    TN (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset =>
      Algo.aggnPairStart c z.1 z.2.1 z.2.2.1 z.2.2.2) (fun n z => LoopOK n z.1) (c + 1) := by
  have hp := aggnPairInput c
  have hi := (hp.pair (const' (none : Option RawWinSI) _ _)).comp_poly
    aggnPolyFun_recomputeInit
  have hz : PolyFun (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset => z) := polyFun_id
  exact (ofPoly (pfst hz) _ _).pair ((ofPoly (pfst (psnd (psnd hz))) _ _).pair
    ((ofPoly (psnd (psnd (psnd hz))) _ _).pair (hp.pair ((const' 0 _ _).pair hi))))

theorem aggnPairPack (c : ℕ) :
    TN (fun z : RawLCLoop × RawStr × RawCoset × Option RawCoset × ℕ × AggnRecomputeState =>
      Algo.aggnPairPack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2)
      (fun n z => LoopOK n z.1) (c + 1) := by
  let X := RawLCLoop × RawStr × RawCoset × Option RawCoset × ℕ × AggnRecomputeState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hp := pfst hz
  have hy := pfst (psnd hz)
  have hq := pfst (psnd (psnd hz))
  have hm := pfst (psnd (psnd (psnd hz)))
  have hj := pfst (psnd (psnd (psnd (psnd hz))))
  have hv := psnd (psnd (psnd (psnd (psnd hz))))
  have hcache : TN (fun z : X => Algo.aggnPairInput c z.1 z.2.1 z.2.2.1 z.2.2.2.1)
      (fun n z => LoopOK n z.1) (c + 1) :=
    poly_comp (hp.pair (hy.pair (hq.pair hm))) (aggnPairInput c)
  have hcount := hcache.comp_poly ((pfst (psnd polyFun_snd)).comp polyFun_length)
  have htest := ((ofPoly (pfst hv) _ _).pair hcount).comp_poly plt
  have hthen := (ofPoly hp _ _).pair ((ofPoly hq _ _).pair ((ofPoly hm _ _).pair
    (hcache.pair (ofPoly (hj.pair hv) _ _))))
  have hans := psnd (psnd (psnd hv))
  have hsource : TN (fun z : X => Algo.aggnPairStart c z.1 z.2.1 z.2.2.1 (some z.2.2.2.2.2.2.2.2))
      (fun n z => LoopOK n z.1) (c + 1) :=
    poly_comp (hp.pair (hy.pair (hq.pair (hans.comp polyFun_some)))) (aggnPairStart c)
  have htarget : TN (fun z : RawCoset × X =>
      Algo.aggnPairStart c (lcStepWith z.1 z.2.1) z.2.2.1 z.2.2.2.2.2.2.2.2.2 none)
      (fun n z => LoopOK n z.2.1) (c + 1) := by
    have hnext := (polyFun_fst.pair (polyFun_snd.comp hp)).comp lcwPolyFun_step
    exact (poly_comp (hnext.pair ((polyFun_snd.comp hy).pair
      ((polyFun_snd.comp hans).pair (polyFun_const (none : Option RawCoset)))))
        (aggnPairStart c)).restrict (fun n z h => loopOK_stepWith h _)
  have helse : TN (fun z : X => z.2.2.2.1.elim
      (Algo.aggnPairStart c z.1 z.2.1 z.2.2.1 (some z.2.2.2.2.2.2.2.2))
      (fun H => Algo.aggnPairStart c (lcStepWith H z.1) z.2.1 z.2.2.2.2.2.2.2.2 none))
      (fun n z => LoopOK n z.1) (c + 1) :=
    ((ofPoly (hm.pair hz) (fun n (z : X) => LoopOK n z.1) (c + 1)).comp
      (optionElim (Pre := fun n (q : Option RawCoset × X) => LoopOK n q.2.1)
        hsource htarget (fun _ _ h => h) (fun _ _ _ h => h)) (fun _ _ h => h)).of_eq
      (fun _ => rfl)
  exact (iteT htest hthen helse).of_eq (fun z => by
    simp only [Algo.aggnPairPack, aggnrCount, decide_eq_true_eq]
    rfl)

theorem aggnPairCombine (c : ℕ) :
    TN (Algo.aggnPairCombine c) (fun n z => LoopOK n z.2.2.1.1) (c + 1) := by
  have hz : PolyFun (fun z : AggnPairNode × ℕ × AggnPairState × RawCoset => z) := polyFun_id
  have hs := pfst (psnd (psnd hz))
  have hy := pfst (psnd (pfst (pfst hz)))
  have hcache := pfst (psnd (psnd (psnd hs)))
  have hj := pfst (psnd (psnd (psnd (psnd hs))))
  have hv := psnd (psnd (psnd (psnd (psnd hs))))
  have ha := psnd (psnd (psnd hz))
  have hr := ((hcache.pair (polyFun_const (none : Option RawWinSI))).pair
    (hj.pair (hv.pair ha))).comp aggnPolyFun_recomputeCombine
  exact (poly_comp ((pfst hs).pair (hy.pair ((pfst (psnd hs)).pair
    ((pfst (psnd (psnd hs))).pair (((hj.pair (polyFun_const 1)).comp polyFun_add).pair hr)))))
      (aggnPairPack c)).of_eq (fun _ => rfl)

/-! ## The comparison phase -/

theorem aggnCompareJobs (c : ℕ) : TN (Algo.aggnCompareJobs c) CtxOK (c + 1) := by
  have hrows := aggnPhaseRows c
  have hp := (hrows.pair hrows).comp_poly comparePolyFun_product
  have hf := hp.comp_poly (PolyFun.map ((polyFun_const false).pair polyFun_id))
  have ht := hp.comp_poly (PolyFun.map ((polyFun_const true).pair polyFun_id))
  exact ((hf.pair ht).comp_poly polyFun_append).of_eq (fun C => by
    simp only [Algo.aggnCompareJobs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.product, List.map_flatMap, List.map_map]
    rfl)

theorem aggnCompareWidth (c : ℕ) : TN (Algo.aggnCompareWidth c) CtxOK (c + 1) :=
  (((aggnCompareJobs c).comp_poly polyFun_length).pair
    (ofPoly aggnPolyFun_compareJobWidth _ _)).comp_poly polyFun_mul

theorem aggnCompareOpen (c : ℕ) :
    TN (fun p : AggnPhaseCtx × AggnCompareJob => Algo.aggnCompareOpen c p.1 p.2)
      (fun n p => CtxOK n p.1) (c + 1) := by
  have h := aggnPolyFun_compareCtx
  exact (poly_comp ((pfst h).pair ((pfst (psnd h)).pair ((psnd (psnd h)).pair
    (polyFun_const (none : Option RawCoset))))) (aggnPairStart c)).restrict
    (fun n p hp => loopOK_compareCtx hp p.2)

theorem aggnCompareScan (c : ℕ) :
    TN (fun z : AggnPhaseCtx × List AggnCompareJob × List RawCoset =>
      Algo.aggnCompareScan c z.1 z.2.1 z.2.2) (fun n z => CtxOK n z.1) (c + 1) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × List AggnCompareJob × List RawCoset => z) :=
    polyFun_id
  have hready : TN (aggnCompareReadyJob c) (fun n p => CtxOK n p.1) (c + 1) :=
    (ofPoly polyFun_snd _ _).pair (aggnCompareOpen c)
  have hprep := (poly_comp ((pfst hz).pair (pfst (psnd hz))) (mapParam hready)).restrict
    (fun n z (h : CtxOK n z.1) a _ => h)
  have hm := (hprep.pair (ofPoly (psnd (psnd hz)) _ _)).comp_poly
    (aggnPolyFun_compareReadyScan (Algo.aggnPairStart c (([], []), ([], [], [])) [] none none))
  exact hm.of_eq (fun z => aggnCompareReadyJob_scan c z.1 z.2.1 z.2.2)

theorem aggnComparePack (c : ℕ) :
    TN (fun z : AggnPhaseCtx × AggnCompareJob × List AggnCompareJob × List RawCoset × ℕ ×
        AggnPairState =>
      Algo.aggnComparePack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2)
      (fun n z => CtxOK n z.1) (c + 1) := by
  let X := AggnPhaseCtx × AggnCompareJob × List AggnCompareJob × List RawCoset × ℕ ×
    AggnPairState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst hz
  have ha := pfst (psnd hz)
  have hr := pfst (psnd (psnd hz))
  have hs := pfst (psnd (psnd (psnd hz)))
  have hj := pfst (psnd (psnd (psnd (psnd hz))))
  have hv := psnd (psnd (psnd (psnd (psnd hz))))
  have ht := hv.comp aggnPolyFun_pairActive
  have hthen := ((ha.pair hr).comp polyFun_cons).pair (hs.pair (hj.pair hv))
  have hstore := ((pfst (psnd hv)).pair hs).comp polyFun_cons
  have helse : TN (fun z : X => Algo.aggnCompareScan c z.1 z.2.2.1
      (z.2.2.2.2.2.2.1 :: z.2.2.2.1)) (fun n z => CtxOK n z.1) (c + 1) :=
    poly_comp (hC.pair (hr.pair hstore)) (aggnCompareScan c)
  exact (TN.ite ht (ofPoly hthen _ _) helse (fun _ _ _ _ => trivial)
    (fun _ _ h _ => h)).of_eq (fun _ => rfl)

theorem aggnCompareCombine (c : ℕ) :
    TN (Algo.aggnCompareCombine c) (fun n z => CtxOK n z.1.1 ∧ CompStOK n z.2.2.1) (c + 1) := by
  let X := AggnPhaseNode × ℕ × AggnCompareState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst (pfst hz)
  have hs := pfst (psnd (psnd hz))
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hstores := pfst (psnd hs)
  have hnil : TN (fun z : X => Algo.aggnCompareScan c z.1.1 [] z.2.2.1.2.1)
      (fun n z => CtxOK n z.1.1 ∧ CompStOK n z.2.2.1) (c + 1) :=
    (poly_comp (hC.pair ((polyFun_const ([] : List AggnCompareJob)).pair hstores))
      (aggnCompareScan c)).restrict (fun _ _ h => h.1)
  have hcons : TN (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
      Algo.aggnComparePack c z.2.1.1 z.1.1 z.1.2 z.2.2.2.1.2.1 (z.2.2.2.1.2.2.1 + 1)
        (Algo.aggnPairCombine c ((aggnCompareCtx z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2)))
      (fun n z => CtxOK n z.2.1.1 ∧ CompStOK n z.2.2.2.1) (c + 1) := by
    have hctx : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.2.1.1) :=
      polyFun_snd.comp hC
    have hjob : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.1.1) :=
      pfst polyFun_fst
    have hrest : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.1.2) :=
      psnd polyFun_fst
    have hstore : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
        z.2.2.2.1.2.1) := polyFun_snd.comp hstores
    have hidx : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
        z.2.2.2.1.2.2.1) := polyFun_snd.comp hj
    have hloop := (hctx.pair hjob).comp aggnPolyFun_compareCtx
    have hinput := (hloop.pair (polyFun_const (none : Option RawWinSI))).pair
      (hidx.pair ((polyFun_snd.comp hv).pair (polyFun_snd.comp ha)))
    have hnext : TN (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
        Algo.aggnPairCombine c ((aggnCompareCtx z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2))
        (fun n z => CtxOK n z.2.1.1 ∧ CompStOK n z.2.2.2.1) (c + 1) :=
      (poly_comp hinput (aggnPairCombine c)).restrict (fun _ _ h => h.2)
    have hidx' := (hidx.pair (polyFun_const 1)).comp polyFun_add
    have hpack := (ofPoly hctx _ _).pair ((ofPoly hjob _ _).pair ((ofPoly hrest _ _).pair
      ((ofPoly hstore _ _).pair ((ofPoly hidx' _ _).pair hnext))))
    exact (hpack.comp (aggnComparePack c) (fun _ _ h => h.1)).of_eq (fun z => by dsimp only)
  have hm := (ofPoly ((pfst hs).pair hz)
    (fun n (z : X) => CtxOK n z.1.1 ∧ CompStOK n z.2.2.1) (c + 1)).comp
    (listCases (Pre := fun n (q : List AggnCompareJob × X) =>
      CtxOK n q.2.1.1 ∧ CompStOK n q.2.2.2.1)
      hnil hcons (fun _ _ h => h) (fun _ _ _ _ h => h)) (fun _ _ h => h)
  exact hm.of_eq (fun z => by unfold Algo.aggnCompareCombine; cases z.2.2.1.1 <;> rfl)

theorem aggnCompareInit (c n : ℕ) :
    TN (aggnCompareRound c n).init (fun n I => CtxOK n I.1) (c + 1) := by
  have hC : PolyFun (fun I : AggnPhaseNode => I.1) := polyFun_fst
  have hj := poly_comp hC (aggnCompareJobs c)
  have hi := (ofPoly hC _ _).pair (hj.pair (const' ([] : List RawCoset) _ _))
  exact (hi.comp (aggnCompareScan c) (fun _ _ h => h)).of_eq (fun _ => rfl)

theorem aggnCompareCheckedChild (c : ℕ) :
    TN (Algo.aggnCompareCheckedChild c) (fun n z => CtxOK n z.1.1) (c + 1) := by
  have hC : PolyFun (fun z : AggnPhaseNode × ℕ × AggnCompareState => z.1.1) := pfst polyFun_fst
  have hf : PolyFun (fun z : AggnPhaseNode × Option AggnPhaseNode => some (aggnCheckedNode z.1)) :=
    (polyFun_fst.comp aggnPolyFun_checkedNode).comp polyFun_some
  have hm : PolyFun (fun o : Option AggnPhaseNode => o.map aggnCheckedNode) :=
    ((polyFun_id.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hf)).of_eq
      (fun o => by cases o <;> rfl)
  exact ((((poly_comp hC (aggnCompareWidth c)).pair (id' _ _)).comp_poly
    polyFun_compareChildAtWidth).comp_poly hm).of_eq (fun _ => rfl)

/-! ## The capped phases -/

theorem aggnBoundedInit (c d : ℕ) :
    TN (Algo.aggnBoundedInit c d) (fun n I => CtxOK n I.1) (c + 1) :=
  (((ofPoly (aggnPolyFun_ground c d 0) _ _).pair (aggnPhaseInit c 0)).comp_poly
    (aggnPolyFun_capState d)).of_eq (fun _ => rfl)

theorem aggnBoundedCombine (c d : ℕ) :
    TN (Algo.aggnBoundedCombine c d) (fun n z => CtxOK n z.1.1 ∧ PhaseStOK n z.2.2.1)
      (c + 1) := by
  have hz : PolyFun (fun z : AggnPhaseNode × ℕ × AggnPhaseState × RawCoset => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hx := pfst (psnd (pfst hI))
  have hn := hx.comp polyFun_length
  have hans := (hx.pair ha).comp aggnPolyFun_normAnswer
  have hnext := poly_comp (hI.pair (hj.pair (hs.pair hans))) (aggnPhaseCombine c)
  exact (((ofPoly hn _ _).pair hnext).comp_poly (aggnPolyFun_capState d)).of_eq (fun _ => rfl)

theorem aggnCompareBoundedInit (c d : ℕ) :
    TN (Algo.aggnCompareBoundedInit c d) (fun n I => CtxOK n I.1) (c + 1) :=
  (((ofPoly (aggnPolyFun_ground c d 0) _ _).pair (aggnCompareInit c 0)).comp_poly
    (aggnPolyFun_compareCapState d)).of_eq (fun _ => rfl)

theorem aggnCompareBoundedCombine (c d : ℕ) :
    TN (Algo.aggnCompareBoundedCombine c d) (fun n z => CtxOK n z.1.1 ∧ CompStOK n z.2.2.1)
      (c + 1) := by
  have hz : PolyFun (fun z : AggnPhaseNode × ℕ × AggnCompareState × RawCoset => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hx := pfst (psnd (pfst hI))
  have hn := hx.comp polyFun_length
  have hans := (hx.pair ha).comp aggnPolyFun_normAnswer
  have hnext := poly_comp (hI.pair (hj.pair (hs.pair hans))) (aggnCompareCombine c)
  exact (((ofPoly hn _ _).pair hnext).comp_poly (aggnPolyFun_compareCapState d)).of_eq
    (fun _ => rfl)

/-! ## Both phases -/

theorem aggnAggregateWidth (c : ℕ) : TN (Algo.aggnAggregateWidth c) CtxOK (c + 1) :=
  ((aggnPhaseWidth c).pair (aggnCompareWidth c)).comp_poly polyFun_add

theorem aggnAggregatePack (c dc dp : ℕ) :
    TN (fun z : AggnPhaseCtx × AggnAggregateState => Algo.aggnAggregatePack c dc dp z.1 z.2)
      (fun n z => CtxOK n z.1) (c + 1) := by
  have hz : PolyFun (fun z : AggnPhaseCtx × AggnAggregateState => z) := polyFun_id
  have hC := pfst hz
  have hs := psnd hz
  have hn := (pfst (psnd hC)).comp polyFun_length
  have hc := (hn.pair (pfst hs)).comp (aggnPolyFun_capState dc)
  have hp := (hn.pair (psnd (psnd hs))).comp (aggnPolyFun_compareCapState dp)
  have hj := ((ofPoly (pfst (psnd hs)) _ _).pair (poly_comp hC (aggnCompareWidth c))).comp_poly
    polyFun_min
  have h := (ofPoly hc (fun n (z : AggnPhaseCtx × AggnAggregateState) => CtxOK n z.1) (c + 1)).pair
    (hj.pair (ofPoly hp (fun n (z : AggnPhaseCtx × AggnAggregateState) => CtxOK n z.1) (c + 1)))
  exact h.of_eq (fun _ => rfl)

theorem aggnAggregateInit (c dc dp : ℕ) :
    TN (Algo.aggnAggregateInit c dc dp) (fun n I => CtxOK n I.1) (c + 1) := by
  have h1 := aggnBoundedInit c dc
  have h2 := aggnCompareBoundedInit c dp
  have h0 : TN (fun _ : AggnPhaseNode => 0) (fun n (I : AggnPhaseNode) => CtxOK n I.1) (c + 1) :=
    const' 0 _ _
  have h := h1.pair (h0.pair h2)
  exact h.of_eq (fun I => by
    simp only [Algo.aggnAggregateInit, aggnUniformRound, aggnCompareBoundedRound])

theorem aggnAggregateChild (c : ℕ) :
    TN (Algo.aggnAggregateChild c) (fun n z => CtxOK n z.1.1) (c + 1) := by
  let X := AggnPhaseNode × ℕ × AggnAggregateState
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := psnd (psnd hz)
  have htest := (pfst (pfst hs)).comp polyFun_isEmpty
  have hc : TN (fun z : X => Algo.aggnCheckedChild c (z.1, z.2.1, z.2.2.1))
      (fun n z => CtxOK n z.1.1) (c + 1) := poly_comp (hI.pair (hj.pair (pfst hs)))
    (aggnCheckedChild c)
  have hp : TN (fun z : X => Algo.aggnCompareCheckedChild c (z.1, z.2.2.2.1, z.2.2.2.2))
      (fun n z => CtxOK n z.1.1) (c + 1) :=
    poly_comp (hI.pair ((pfst (psnd hs)).pair (psnd (psnd hs)))) (aggnCompareCheckedChild c)
  have hbranch := TN.ite htest hp hc (fun _ _ h _ => h) (fun _ _ h _ => h)
  have hwidth : TN (fun z : X => Algo.aggnAggregateWidth c z.1.1) (fun n z => CtxOK n z.1.1)
      (c + 1) := poly_comp (pfst hI) (aggnAggregateWidth c)
  have hgate := ((ofPoly hj _ _).pair hwidth).comp_poly plt
  have hrun := iteT hgate hbranch (const' none _ _)
  exact ((ofPoly ((psnd hI).pair hz) (fun n (z : X) => CtxOK n z.1.1) (c + 1)).comp
    (optionElim (Pre := fun n (q : Option RawWinSI × X) => CtxOK n q.2.1.1) hrun
      (const' none (fun n (q : RawWinSI × X) => CtxOK n q.2.1.1) _) (fun _ _ h => h)
      (fun _ _ _ h => h)) (fun _ _ h => h)).of_eq
    (fun z => by simp only [Algo.aggnAggregateChild, decide_eq_true_eq])

theorem aggnAggregateCombine (c dc dp : ℕ) :
    TN (Algo.aggnAggregateCombine c dc dp) (fun n z => CtxOK n z.1.1 ∧ AggStOK n z.2.2.1)
      (c + 1) := by
  let X := AggnPhaseNode × ℕ × AggnAggregateState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hc := pfst hs
  have hk := pfst (psnd hs)
  have hp := psnd (psnd hs)
  have htest := (pfst hc).comp polyFun_isEmpty
  have hnextc : TN (fun z : X => Algo.aggnBoundedCombine c dc (z.1, z.2.1, z.2.2.1.1, z.2.2.2))
      (fun n z => CtxOK n z.1.1 ∧ AggStOK n z.2.2.1) (c + 1) :=
    (poly_comp (hI.pair (hj.pair (hc.pair ha))) (aggnBoundedCombine c dc)).restrict
      (fun _ _ h => ⟨h.1, h.2.1⟩)
  have hnextp : TN (fun z : X =>
      Algo.aggnCompareBoundedCombine c dp (z.1, z.2.2.1.2.1, z.2.2.1.2.2, z.2.2.2))
      (fun n z => CtxOK n z.1.1 ∧ AggStOK n z.2.2.1) (c + 1) :=
    (poly_comp (hI.pair (hk.pair (hp.pair ha))) (aggnCompareBoundedCombine c dp)).restrict
      (fun _ _ h => ⟨h.1, h.2.2⟩)
  have hcomp := (ofPoly hc _ _).pair ((ofPoly ((hk.pair (polyFun_const 1)).comp polyFun_add)
    _ _).pair hnextp)
  have hcert := hnextc.pair (ofPoly (hk.pair hp) _ _)
  have hnext := TN.ite htest hcomp hcert (fun _ _ h _ => h) (fun _ _ h _ => h)
  exact ((ofPoly (pfst hI) _ _).pair hnext).comp (aggnAggregatePack c dc dp)
    (fun _ _ h => h.1) |>.of_eq (fun _ => by
      dsimp only [Algo.aggnAggregateCombine, aggnUniformRound, aggnBoundedRound]; rfl)

end TN

end Explicit
