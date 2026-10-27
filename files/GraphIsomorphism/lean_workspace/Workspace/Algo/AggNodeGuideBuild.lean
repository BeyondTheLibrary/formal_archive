import Workspace.Algo.AggNodeGuideRelations
import Workspace.Algo.AggNodeConstituentInput

/-! # Computing both Case 3 structures from the completed aggregate

The stores determine the two fixed-point sets. The comparison table
determines the tuple classes. Representatives are chosen from the source
and used as the common relation labels of both numbered structures.
A failed target coverage or cardinality check returns rejection.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev AggnGuideSide := List ℕ × List (List ℕ)
abbrev AggnGuidePrepared := (RawAction × RawAggCompareTable) ×
  (List (List ℕ) × (AggnGuideSide × AggnGuideSide))
abbrev AggnGuidePrepareInput := (AggnPhaseCtx × AggnAggregateState) × RawAggCompareTable

def aggnGuideSideRows (c : ℕ) (p : (List ℕ × List ℕ) × List ℕ) : AggnGuideSide :=
  (p.2,aggnGuideRows c (p.1.1,p.1.2,List.range p.2.length))

def aggnGuidePrepare (c : ℕ) (p : AggnGuidePrepareInput) : AggnGuidePrepared :=
  let Dx := (aggnAggregateData (p.1,false)).2.2
  let Dy := (aggnAggregateData (p.1,true)).2.2
  let ctx := (p.1.1.1,p.2)
  let rows := aggnGuideRows c (p.1.1.2.2.2,p.1.1.2.1,Dx)
  (ctx,aggnGuideReps (ctx,rows),
    aggnGuideSideRows c ((p.1.1.2.2.2,p.1.1.2.1),Dx),
    aggnGuideSideRows c ((p.1.1.2.2.2,p.1.1.2.1),Dy))

def aggnGuideAt (p : AggnGuidePrepared × Bool) : AggnGuideRelCtx × List (List ℕ) :=
  ((p.1.1,p.2,cond p.2 p.1.2.2.2 p.1.2.2.1),p.1.2.1)

def aggnGuideEnter (p : (List ℕ × List ℕ) × (AggnGuidePrepared × Bool)) : AmbientPIn :=
  let q := aggnGuideAt p.2
  ((p.1.1,p.1.2,List.range q.1.2.2.1.length),aggnGuideRelations q)

def aggnGuideBuild (p : (List ℕ × List ℕ) × AggnGuidePrepared) : Option (AmbientPIn × AmbientPIn) :=
  if decide (p.2.2.2.1.1.length = p.2.2.2.2.1.length) && aggnGuideCovered (aggnGuideAt (p.2,true)) then
    some (aggnGuideEnter (p.1,p.2,false),aggnGuideEnter (p.1,p.2,true))
  else none

/-- The complete raw constructor consumes the actual stored comparison answers. -/
def aggnAggregateGuide (c : ℕ) (p : AggnPhaseCtx × AggnAggregateState) :
    Option (AmbientPIn × AmbientPIn) :=
  aggnGuideBuild ((p.1.2.2.2,p.1.2.1),
    aggnGuidePrepare c (p,aggnCompareTable c (p.1,p.2.2.2.2.1)))

private theorem fstP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem sndP {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem fstQ {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : QuasiFun f) : QuasiFun (fun a => (f a).1) := h.comp_poly polyFun_fst
private theorem sndQ {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : QuasiFun f) : QuasiFun (fun a => (f a).2) := h.comp_poly polyFun_snd

theorem aggnQuasiFun_guideSideRows (c : ℕ) : QuasiFun (aggnGuideSideRows c) :=
  polyFun_snd.quasiFun.pair
    (((polyFun_fst.comp polyFun_fst).pair ((polyFun_fst.comp polyFun_snd).pair
      (polyFun_snd.comp polyFun_rangeLength))).comp_quasiFun (aggnQuasiFun_guideRows c))

theorem aggnQuasiFun_guidePrepare (c : ℕ) : QuasiFun (aggnGuidePrepare c) := by
  have hi : PolyFun (fun p : AggnGuidePrepareInput => p) := polyFun_id
  have hC := fstP (fstP hi)
  have hks := sndP (sndP (sndP hC))
  have hdom := fstP (sndP hC)
  have hctx := (fstP hC).pair (sndP hi)
  have hx := sndP (sndP (((fstP hi).pair (polyFun_const false)).comp aggnPolyFun_aggregateData))
  have hy := sndP (sndP (((fstP hi).pair (polyFun_const true)).comp aggnPolyFun_aggregateData))
  have hrows := (hks.pair (hdom.pair hx)).comp_quasiFun (aggnQuasiFun_guideRows c)
  exact hctx.quasiFun.pair (((hctx.quasiFun.pair hrows).comp_poly aggnPolyFun_guideReps).pair
    ((((hks.pair hdom).pair hx).comp_quasiFun (aggnQuasiFun_guideSideRows c)).pair
      (((hks.pair hdom).pair hy).comp_quasiFun (aggnQuasiFun_guideSideRows c))))

theorem aggnPolyFun_guideAt : PolyFun aggnGuideAt := by
  have hi : PolyFun (fun p : AggnGuidePrepared × Bool => p) := polyFun_id
  have hs := sndP (sndP (fstP hi))
  have h := (((fstP (fstP hi)).pair ((sndP hi).pair
    (PolyFun.ite (sndP hi) (sndP hs) (fstP hs)))).pair (fstP (sndP (fstP hi))))
  exact h.of_eq (fun p => by rcases p with ⟨p,b⟩; cases b <;> rfl)

theorem aggnPolyFun_guideEnter : PolyFun aggnGuideEnter := by
  have hi : PolyFun (fun p : (List ℕ × List ℕ) × (AggnGuidePrepared × Bool) => p) := polyFun_id
  have hq := (sndP hi).comp aggnPolyFun_guideAt
  exact (((fstP (fstP hi)).pair ((sndP (fstP hi)).pair
    ((fstP (sndP (sndP (fstP hq)))).comp polyFun_rangeLength))).pair
      (hq.comp aggnPolyFun_guideRelations))

theorem aggnPolyFun_guideBuild : PolyFun aggnGuideBuild := by
  have hi : PolyFun (fun p : (List ℕ × List ℕ) × AggnGuidePrepared => p) := polyFun_id
  have hs := sndP (sndP (sndP hi))
  have hlen := (((fstP (fstP hs)).comp polyFun_length).pair
    ((fstP (sndP hs)).comp polyFun_length)).comp polyFun_natEq
  have hat := ((sndP hi).pair (polyFun_const true)).comp aggnPolyFun_guideAt
  have hx := ((fstP hi).pair ((sndP hi).pair (polyFun_const false))).comp aggnPolyFun_guideEnter
  have hy := ((fstP hi).pair ((sndP hi).pair (polyFun_const true))).comp aggnPolyFun_guideEnter
  exact PolyFun.ite (wftPolyFun_and hlen (hat.comp aggnPolyFun_guideCovered))
    ((hx.pair hy).comp polyFun_some) (polyFun_const none)

theorem aggnQuasiFun_aggregateGuide (c : ℕ) : QuasiFun (aggnAggregateGuide c) := by
  have hi : PolyFun (fun p : AggnPhaseCtx × AggnAggregateState => p) := polyFun_id
  have hC := fstP hi
  have hs := sndP hi
  have htable := (hC.pair (fstP (sndP (sndP (sndP hs))))).comp_quasiFun (aggnQuasiFun_compareTable c)
  have hp := (hi.quasiFun.pair htable).comp (aggnQuasiFun_guidePrepare c)
  exact (((sndP (sndP (sndP hC))).pair (fstP (sndP hC))).quasiFun.pair hp).comp_poly aggnPolyFun_guideBuild

theorem aggnGuideBuild_some {p : (List ℕ × List ℕ) × AggnGuidePrepared} {out : AmbientPIn × AmbientPIn}
    (h : aggnGuideBuild p = some out) :
    p.2.2.2.1.1.length = p.2.2.2.2.1.length ∧
    aggnGuideCovered (aggnGuideAt (p.2,true)) = true ∧
    out = (aggnGuideEnter (p.1,p.2,false),aggnGuideEnter (p.1,p.2,true)) := by
  unfold aggnGuideBuild at h
  split at h
  · rename_i ht
    simp only [Bool.and_eq_true,decide_eq_true_eq] at ht
    exact ⟨ht.1,ht.2,(Option.some.inj h).symm⟩
  · contradiction

end Algo
