import Workspace.Algo.AggNodeCompareScan

/-! # All-input RAM bounds for the comparison carrier

The scan proof supplies the only variable-length traversal used by init
and combine. Computing the fixed ordered-pair table remains quasipolynomial.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

private theorem comparePolyFun_product {α β : Type*} [Enc α] [Enc β] :
    PolyFun (fun p : List α × List β => p.1.product p.2) := by
  have h : PolyFun (fun p : List β × α => p.1.map (fun b => (p.2, b))) :=
    (polyFun_snd.pair polyFun_fst).comp (PolyFun.mapParam (polyFun_fst.pair polyFun_snd))
  exact ((polyFun_snd.pair polyFun_fst).comp h.flatMapParam).of_eq (fun _ => rfl)

theorem aggnQuasiFun_compareRows (c : ℕ) : QuasiFun (aggnPhaseRows c) := by
  have hC : PolyFun (fun C : AggnPhaseCtx => C) := polyFun_id
  exact ((psnd (psnd (psnd hC))).pair
    ((pfst (psnd hC)).pair (pfst (psnd (pfst hC))))).comp_quasiFun (aggQuasiFun_testSetsOn c)

theorem aggnQuasiFun_compareJobs (c : ℕ) : QuasiFun (aggnCompareJobs c) := by
  have hrows := aggnQuasiFun_compareRows c
  have hp := (hrows.pair hrows).comp_poly comparePolyFun_product
  have hf := hp.comp_poly (PolyFun.map ((polyFun_const false).pair polyFun_id))
  have ht := hp.comp_poly (PolyFun.map ((polyFun_const true).pair polyFun_id))
  exact ((hf.pair ht).comp_poly polyFun_append).of_eq (fun C => by
    simp only [aggnCompareJobs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.product, List.map_flatMap, List.map_map]
    rfl)

theorem aggnPolyFun_compareJobWidth : PolyFun aggnCompareJobWidth := by
  have hx : PolyFun (fun C : AggnPhaseCtx => C.2.1.length) :=
    (pfst polyFun_snd).comp polyFun_length
  have ht : PolyFun (fun C : AggnPhaseCtx => C.2.2.2) := psnd (psnd polyFun_snd)
  have hfact := ht.comp (polyFun_length.factorial length_le_size polyBound_id)
  have hjob := (hx.pair ((hfact.pair hx).comp polyFun_mul)).comp polyFun_mul
  exact ((polyFun_const 2).pair hjob).comp polyFun_mul

theorem aggnQuasiFun_compareWidth (c : ℕ) : QuasiFun (aggnCompareWidth c) :=
  (((aggnQuasiFun_compareJobs c).comp_poly polyFun_length).pair
    aggnPolyFun_compareJobWidth.quasiFun).comp_poly polyFun_mul

theorem aggnQuasiFun_compareInit (c n : ℕ) : QuasiFun (aggnCompareRound c n).init := by
  have hC : PolyFun (fun I : AggnPhaseNode => I.1) := polyFun_fst
  have hj := hC.comp_quasiFun (aggnQuasiFun_compareJobs c)
  have hi := hC.quasiFun.pair (hj.pair (quasiFun_const ([] : List RawCoset)))
  have hr := hi.comp (aggnQuasiFun_compareScan c)
  exact hr.of_eq (fun _ => rfl)

theorem aggnQuasiFun_comparePack (c : ℕ) :
    QuasiFun (fun z : AggnPhaseCtx × AggnCompareJob × List AggnCompareJob × List RawCoset × ℕ × AggnPairState =>
      aggnComparePack c z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  let X := AggnPhaseCtx × AggnCompareJob × List AggnCompareJob × List RawCoset × ℕ × AggnPairState
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
  have helse := (hC.pair (hr.pair hstore)).comp_quasiFun (aggnQuasiFun_compareScan c)
  exact (QuasiFun.ite ht hthen.quasiFun helse).of_eq (fun _ => rfl)

/-- Combining an answer has a quasipolynomial machine bound, including on malformed states. -/
theorem aggnQuasiFun_compareCombine (c : ℕ) : QuasiFun (aggnCompareCombine c) := by
  let X := AggnPhaseNode × ℕ × AggnCompareState × RawCoset
  have hz : PolyFun (fun z : X => z) := polyFun_id
  have hC := pfst (pfst hz)
  have hs := pfst (psnd (psnd hz))
  have hj := pfst (psnd (psnd hs))
  have hv := psnd (psnd (psnd hs))
  have ha := psnd (psnd (psnd hz))
  have hstores := pfst (psnd hs)
  have hnil := (hC.pair ((polyFun_const ([] : List AggnCompareJob)).pair hstores)).comp_quasiFun
    (aggnQuasiFun_compareScan c)
  have hcons : QuasiFun (fun z : (AggnCompareJob × List AggnCompareJob) × X =>
      aggnComparePack c z.2.1.1 z.1.1 z.1.2 z.2.2.2.1.2.1 (z.2.2.2.1.2.2.1 + 1)
        (aggnPairCombine c ((aggnCompareCtx z.2.1.1 z.1.1, none), z.2.2.2.1.2.2.1,
          z.2.2.2.1.2.2.2, z.2.2.2.2))) := by
    have hctx : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.2.1.1) := polyFun_snd.comp hC
    have hjob : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.1.1) := pfst polyFun_fst
    have hrest : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.1.2) := psnd polyFun_fst
    have hstore : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.2.2.2.1.2.1) :=
      polyFun_snd.comp hstores
    have hidx : PolyFun (fun z : (AggnCompareJob × List AggnCompareJob) × X => z.2.2.2.1.2.2.1) :=
      polyFun_snd.comp hj
    have hloop := (hctx.pair hjob).comp aggnPolyFun_compareCtx
    have hinput := (hloop.pair (polyFun_const (none : Option RawWinSI))).pair
      (hidx.pair ((polyFun_snd.comp hv).pair (polyFun_snd.comp ha)))
    have hnext := hinput.comp_quasiFun (aggnQuasiFun_pairCombine c)
    have hidx' := (hidx.pair (polyFun_const 1)).comp polyFun_add
    have hpack := hctx.quasiFun.pair (hjob.quasiFun.pair (hrest.quasiFun.pair
      (hstore.quasiFun.pair (hidx'.quasiFun.pair hnext))))
    have hm := hpack.comp (aggnQuasiFun_comparePack c)
    exact hm.of_eq (fun z => by dsimp only)
  have hm := (((pfst hs).pair hz).comp_quasiFun (QuasiFun.listCases hnil hcons))
  exact hm.of_eq (fun z => by unfold aggnCompareCombine; cases z.2.2.1.1 <;> rfl)


private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])

private theorem pif {α β : Type*} [Enc α] [Enc β] {p : α → Prop}
    [∀ a, Decidable (p a)] {f g : α → β}
    (hp : PolyFun (fun a => decide (p a))) (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => if p a then f a else g a) :=
  (PolyFun.ite hp hf hg).of_eq (fun a => by simp)

private theorem pand {α : Type*} [Enc α] {p q : α → Prop}
    [∀ a, Decidable (p a)] [∀ a, Decidable (q a)]
    (hp : PolyFun (fun a => decide (p a))) (hq : PolyFun (fun a => decide (q a))) :
    PolyFun (fun a => decide (p a ∧ q a)) :=
  (pif hp hq (polyFun_const false)).of_eq (fun a => by by_cases h : p a <;> simp [h])

private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

/-- All local tests and cache reads, after the global width has been supplied. -/
private theorem aggnPolyFun_compareChildAtWidth :
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

/-- The raw selector is quasipolynomial even for arbitrary cached states. -/
theorem aggnQuasiFun_compareChild (c : ℕ) : QuasiFun (aggnCompareChild c) := by
  have hC : PolyFun (fun z : AggnPhaseNode × ℕ × AggnCompareState => z.1.1) :=
    pfst polyFun_fst
  exact (((hC.comp_quasiFun (aggnQuasiFun_compareWidth c)).pair polyFun_id.quasiFun).comp_poly
    aggnPolyFun_compareChildAtWidth).of_eq (fun _ => rfl)


end Algo
