import Workspace.Algo.TopSuppliedMatch
import Workspace.Algo.RoundQ

/-! # RAM routines for the complete supplied top-action-3 phase

Preparation, child creation and every fold update are polynomial on all raw
inputs. The final routines expose both the giant-test flag and the answer
coset. Recursive calls are separate from these local machine operations.
-/

set_option synthInstance.maxSize 512

namespace Algo

open RAM RAM.Targets

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem plt : PolyFun (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
  have h := (((polyFun_fst.pair (polyFun_const 1)).comp polyFun_add).pair polyFun_snd).comp polyFun_le
  exact h.of_eq (fun _ => by simp only [Nat.add_one_le_iff])
private theorem pif {α β : Type*} [Enc α] [Enc β] {p : α → Prop}
    [∀ a, Decidable (p a)] {f g : α → β}
    (hp : PolyFun (fun a => decide (p a))) (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => if p a then f a else g a) :=
  (PolyFun.ite hp hf hg).of_eq (fun _ => by simp)
private theorem pand {α : Type*} [Enc α] {p q : α → Prop}
    [∀ a, Decidable (p a)] [∀ a, Decidable (q a)]
    (hp : PolyFun (fun a => decide (p a))) (hq : PolyFun (fun a => decide (q a))) :
    PolyFun (fun a => decide (p a ∧ q a)) :=
  (pif hp hq (polyFun_const false)).of_eq (fun a => by by_cases h : p a <;> simp [h])
private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)
private theorem pisSome {α : Type*} [Enc α] : PolyFun (fun o : Option α => o.isSome) :=
  ((polyFun_id.pair (polyFun_const (0 : ℕ))).comp
    (PolyFun.optionElim (polyFun_const false) (polyFun_const true))).of_eq
      (fun o => by cases o <;> rfl)

theorem polyFun_topcsX : PolyFun topcsX := polyFun_fst
theorem polyFun_topcsY : PolyFun topcsY := pfst polyFun_snd
theorem polyFun_topcsWins : PolyFun topcsWins := pfst (psnd polyFun_snd)
theorem polyFun_topcsTests : PolyFun topcsTests := pfst (psnd (psnd polyFun_snd))
theorem polyFun_topcsKernel : PolyFun topcsKernel := pfst (psnd (psnd (psnd polyFun_snd)))
theorem polyFun_topcsOdd : PolyFun topcsOdd := pfst (psnd (psnd (psnd (psnd polyFun_snd))))
theorem polyFun_topcsEven : PolyFun topcsEven := pfst (psnd (psnd (psnd (psnd (psnd polyFun_snd)))))
theorem polyFun_topcsCount : PolyFun topcsCount := polyFun_topcsTests.comp polyFun_length
theorem polyFun_topcsJobs : PolyFun topcsJobs :=
  (polyFun_topcsCount.pair (polyFun_const 2)).comp polyFun_add

theorem polyFun_topcsPrepare : PolyFun topcsPrepare := by
  have hp : PolyFun (fun p : TopcsRawInput => p.1.1) := pfst polyFun_fst
  have hd := pfst (pfst hp)
  have hgdom := pfst (psnd hp)
  have hs : PolyFun (fun p : TopcsRawInput => p.2.1) := pfst polyFun_snd
  have ho : PolyFun (fun p : TopcsRawInput => p.2.2) := psnd polyFun_snd
  have hx : PolyFun (fun p : TopcsRawInput => p.1.2.1) := pfst (psnd polyFun_fst)
  have hy : PolyFun (fun p : TopcsRawInput => p.1.2.2) := psnd (psnd polyFun_fst)
  have hlist := ((hgdom.comp polyFun_rawOne).pair hs).comp polyFun_cons
  have htests := (hp.pair hlist).comp (PolyFun.mapParam polyFun_topCosetStart)
  have hk := hp.comp polyFun_topKernel
  exact ((hd.pair hx).comp polyFun_fixStr).pair (((hd.pair hy).comp polyFun_fixStr).pair
    ((hp.comp polyFun_topKernelWindows).pair (htests.pair
      (((hk.pair (hd.comp polyFun_rawOne)).comp polyFun_some).pair
        (((hk.pair ((hd.pair ho).comp polyFun_normPerm)).comp polyFun_some).pair
          ((hp.comp polyFun_topAllEven).pair ((hd.pair (psnd (pfst hp))).comp polyFun_tidyGens)))))))

theorem polyFun_topcsTgt : PolyFun (fun z : TopcsInput × ℕ => topcsTgt z.1 z.2) :=
  pif ((polyFun_snd.pair (polyFun_fst.comp polyFun_topcsCount)).comp plt)
    (polyFun_fst.comp polyFun_topcsX) (polyFun_fst.comp polyFun_topcsY)

theorem polyFun_topcsBegin : PolyFun (fun z : TopcsInput × ℕ => topcsBegin z.1 z.2) := by
  have hp : PolyFun (fun z : TopcsInput × ℕ => z.1) := polyFun_fst
  have hc := hp.comp polyFun_topcsCount
  have hget := ((((hp.comp polyFun_topcsTests).pair polyFun_snd).pair
    (polyFun_const (none : RawCoset))).comp polyFun_getD)
  have hcase := pif (polyFun_snd.natEq hc)
    (hp.comp polyFun_topcsKernel) (hp.comp polyFun_topcsOdd)
  exact ((hp.comp polyFun_topcsX).pair
    (pif ((polyFun_snd.pair hc).comp plt) hget hcase)).comp polyFun_top2NormC

theorem polyFun_topcsLeaf :
    PolyFun (fun z : TopcsInput × ℕ × ℕ × (RawGens × RawPerm) => topcsLeaf z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : PolyFun (fun z : TopcsInput × ℕ × ℕ × (RawGens × RawPerm) => z.1) := polyFun_fst
  have ht : PolyFun (fun z : TopcsInput × ℕ × ℕ × (RawGens × RawPerm) => z.2.1) := pfst polyFun_snd
  have hi : PolyFun (fun z : TopcsInput × ℕ × ℕ × (RawGens × RawPerm) => z.2.2.1) := pfst (psnd polyFun_snd)
  have hq : PolyFun (fun z : TopcsInput × ℕ × ℕ × (RawGens × RawPerm) => z.2.2.2) := psnd (psnd polyFun_snd)
  have hx := hp.comp polyFun_topcsX
  have hw := ((((hp.comp polyFun_topcsWins).pair hi).pair
    (polyFun_const ([] : List ℕ))).comp polyFun_getD)
  exact hw.pair (((hx.pair (pfst hq)).comp polyFun_tidyGens).pair
    (((hx.pair (psnd hq)).comp polyFun_normPerm).pair
      (hx.pair ((hp.pair ht).comp polyFun_topcsTgt))))

theorem polyFun_topcsChild : PolyFun topcsChild := by
  let X := TopcsNode × ℕ × TopcsState
  have hp : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hs : PolyFun (fun z : X => z.2.2) := psnd polyFun_snd
  have hj : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have ht := pfst hs
  have hi := pfst (psnd hs)
  have hc := pfst (psnd (psnd hs))
  have hn := hp.comp polyFun_topcsJobs
  have hw := (hp.comp polyFun_topcsWins).comp polyFun_length
  have hgate := pand ((ht.pair hn).comp plt)
    (pand ((hi.pair hw).comp plt) ((hj.pair ((hn.pair hw).comp polyFun_mul)).comp plt))
  have hbody : PolyFun (fun z : (RawGens × RawPerm) × X =>
      (z.2.1.1, some (topcsLeaf z.2.1.1 z.2.2.2.1 z.2.2.2.2.1 z.1))) := by
    have hp' : PolyFun (fun z : (RawGens × RawPerm) × X => z.2.1.1) := polyFun_snd.comp hp
    exact hp'.pair (((hp'.pair ((polyFun_snd.comp ht).pair
      ((polyFun_snd.comp hi).pair polyFun_fst))).comp polyFun_topcsLeaf).comp polyFun_some)
  have hrun := pif hgate ((hc.pair polyFun_id).comp (pmap hbody)) (polyFun_const none)
  exact (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim hrun (polyFun_const none))).of_eq (fun _ => rfl)

theorem polyFun_topcsClose :
    PolyFun (fun z : TopcsInput × ℕ × Top1State × RawCoset × RawCoset × RawCoset =>
      topcsClose z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  let X := TopcsInput × ℕ × Top1State × RawCoset × RawCoset × RawCoset
  have hp : PolyFun (fun z : X => z.1) := polyFun_fst
  have ht : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have ha : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have h1 : PolyFun (fun z : X => z.2.2.2.1) := pfst (psnd (psnd polyFun_snd))
  have h2 : PolyFun (fun z : X => z.2.2.2.2.1) := pfst (psnd (psnd (psnd polyFun_snd)))
  have hc : PolyFun (fun z : X => z.2.2.2.2.2) := psnd (psnd (psnd (psnd polyFun_snd)))
  have hx := hp.comp polyFun_topcsX
  have hn := hp.comp polyFun_topcsCount
  have hjobs := hp.comp polyFun_topcsJobs
  have hnext := ht.add (polyFun_const 1)
  have hn' := hn.add (polyFun_const 1)
  have hacc := (hx.pair ((hx.pair (ha.pair hc)).comp polyFun_top1Join)).comp polyFun_top2NormS
  have hacc0 := (hx.pair ha).comp polyFun_top2NormS
  have hnorm1 := (hx.pair h1).comp polyFun_top2NormC
  have hnorm2 := (hx.pair h2).comp polyFun_top2NormC
  have hnormc := (hx.pair hc).comp polyFun_top2NormC
  have hfirst := hnext.pair ((polyFun_const 0).pair
    (((hp.pair hnext).comp polyFun_topcsBegin).pair (hacc.pair (hnorm1.pair hnorm2))))
  have hlast := (PolyFun.ite (hacc.comp pisSome) hn hjobs).pair ((polyFun_const 0).pair
    (((hp.pair hn).comp polyFun_topcsBegin).pair (hacc.pair (hnorm1.pair hnorm2))))
  have hkernel := (PolyFun.ite (hp.comp polyFun_topcsEven) hjobs hn').pair ((polyFun_const 0).pair
    (((hp.pair hn').comp polyFun_topcsBegin).pair (hacc0.pair (hnormc.pair hnorm2))))
  have hodd := hjobs.pair ((polyFun_const 0).pair
    (((hp.pair hjobs).comp polyFun_topcsBegin).pair (hacc0.pair (hnorm1.pair hnormc))))
  exact pif ((hnext.pair hn).comp plt) hfirst
    (pif (hnext.natEq hn) hlast (pif (ht.natEq hn) hkernel hodd))

theorem polyFun_topcsStep :
    PolyFun (fun z : TopcsInput × ℕ × ℕ × Top1State × RawCoset × RawCoset × RawCoset =>
      topcsStep z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2) := by
  let X := TopcsInput × ℕ × ℕ × Top1State × RawCoset × RawCoset × RawCoset
  have hp : PolyFun (fun z : X => z.1) := polyFun_fst
  have ht : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hi : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have ha : PolyFun (fun z : X => z.2.2.2.1) := pfst (psnd (psnd polyFun_snd))
  have h1 : PolyFun (fun z : X => z.2.2.2.2.1) := pfst (psnd (psnd (psnd polyFun_snd)))
  have h2 : PolyFun (fun z : X => z.2.2.2.2.2.1) := pfst (psnd (psnd (psnd (psnd polyFun_snd))))
  have hc : PolyFun (fun z : X => z.2.2.2.2.2.2) := psnd (psnd (psnd (psnd (psnd polyFun_snd))))
  have hx := hp.comp polyFun_topcsX
  have hn := hp.comp polyFun_topcsJobs
  have hw := (hp.comp polyFun_topcsWins).comp polyFun_length
  have hi' := hi.add (polyFun_const 1)
  have hsome : PolyFun (fun z : X => decide (z.2.2.2.2.2.2.isSome = true)) :=
    (hc.comp pisSome).of_eq (fun z => by cases z.2.2.2.2.2.2.isSome <;> rfl)
  have hgate := pand hsome ((hi'.pair hw).comp plt)
  have hthen := ((ht.pair hn).comp polyFun_min).pair (((hi'.pair hw).comp polyFun_min).pair
    (((hx.pair hc).comp polyFun_top2NormC).pair (((hx.pair ha).comp polyFun_top2NormS).pair
      (((hx.pair h1).comp polyFun_top2NormC).pair ((hx.pair h2).comp polyFun_top2NormC)))))
  have helse := (hp.pair (ht.pair (ha.pair (h1.pair (h2.pair hc))))).comp polyFun_topcsClose
  exact pif hgate hthen helse

theorem polyFun_topcsInit : PolyFun topcsInit :=
  (polyFun_const 0).pair ((polyFun_const 0).pair
    (((polyFun_fst.pair (polyFun_const 0)).comp polyFun_topcsBegin).pair
      ((polyFun_const (some (none : RawCoset))).pair
        ((polyFun_const (none : RawCoset)).pair (polyFun_const (none : RawCoset))))))

theorem polyFun_topcsCombine : PolyFun topcsCombine := by
  have hz : PolyFun (fun z : TopcsNode × ℕ × TopcsState × RawCoset => z) := polyFun_id
  have hs := pfst (psnd (psnd hz))
  exact ((pfst (pfst hz)).pair ((pfst hs).pair ((pfst (psnd hs)).pair
    ((pfst (psnd (psnd (psnd hs)))).pair ((pfst (psnd (psnd (psnd (psnd hs))))).pair
      ((psnd (psnd (psnd (psnd (psnd hs))))).pair (psnd (psnd (psnd hz))))))))).comp polyFun_topcsStep

theorem polyFun_topcsAnswer : PolyFun (fun z : TopcsInput × TopcsState => topcsAnswer z.1 z.2) := by
  let X := TopcsInput × TopcsState
  have hp : PolyFun (fun z : X => z.1) := polyFun_fst
  have hs : PolyFun (fun z : X => z.2) := polyFun_snd
  have ha := pfst (psnd (psnd (psnd hs)))
  have hbody : PolyFun (fun z : RawCoset × X =>
      if topcsEven z.2.1 then top3Prod (topcsX z.2.1, z.2.2.2.2.2.2.1, z.1)
      else rawCosetJoin (topcsX z.2.1, top3Prod (topcsX z.2.1, z.2.2.2.2.2.2.1, z.1),
        top3Prod (topcsX z.2.1, z.2.2.2.2.2.2.2, z.1))) := by
    have hp' : PolyFun (fun z : RawCoset × X => z.2.1) := polyFun_snd.comp hp
    have hs' : PolyFun (fun z : RawCoset × X => z.2.2) := polyFun_snd.comp hs
    have hx := hp'.comp polyFun_topcsX
    have h1 := (hx.pair ((pfst (psnd (psnd (psnd (psnd hs'))))).pair polyFun_fst)).comp polyFun_top3Prod
    have h2 := (hx.pair ((psnd (psnd (psnd (psnd (psnd hs'))))).pair polyFun_fst)).comp polyFun_top3Prod
    exact PolyFun.ite (hp'.comp polyFun_topcsEven) h1 ((hx.pair (h1.pair h2)).comp polyFun_rawCosetJoin)
  exact ((ha.pair polyFun_id).comp (pmap hbody)).of_eq (fun _ => rfl)

theorem quasiFun_topcsFinish {solve : RawWinSI → RawCoset} (hs : QuasiFun solve) :
    QuasiFun (topcsFinish solve) := by
  have hparent : PolyFun (fun z : TopcsNode × TopcsState => (topcsAnswer z.1.1 z.2).getD none) :=
    ((((pfst polyFun_fst).pair polyFun_snd).comp polyFun_topcsAnswer).pair
      (polyFun_const (none : RawCoset))).comp polyFun_optionGetD
  exact (((psnd polyFun_fst).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hparent.quasiFun (polyFun_fst.comp_quasiFun hs))).of_eq (fun _ => rfl)

end Algo
