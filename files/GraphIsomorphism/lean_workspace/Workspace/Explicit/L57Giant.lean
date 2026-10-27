/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the round of lines 5–7 of
the Master (Sec. 15) with the giant branch of outcome (2a), bounded at an external degree.
Not part of the faithful formalization.
-/
import Workspace.Explicit.L57Round
import Workspace.Explicit.L57Giant4a

/-!
# The round of lines 5–7 with the giant branch, bounded at the degree

`Algo.aggnL57GRound` adds to the round of lines 5–7 the branch of outcome (2a), which runs the
round of Cor. 12.0.10 (`Algo.top4aRound`) on a node read off the stores. That round is
polynomial here (its answer routine is constant); the only quasipolynomial work of the branch
is the test of outcome (2a), which reads the continuation.
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
private theorem polyFun_isNone' {α : Type*} [Enc α] : PolyFun (fun o : Option α => o.isNone) :=
  ((polyFun_id.pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const true) (polyFun_const false))).of_eq
    (fun o => by cases o <;> rfl)

namespace TN

variable {c b t d : ℕ} (dc dp u v e f : ℕ)

theorem aggnL57GNode (hc : c + 2 ≤ 5) :
    TN (Algo.aggnL57GNode c dc dp) (fun n z => CtxOK n z.1) 5 :=
  (((ofPoly polyFun_fst _ _).pair ((aggnAggregatePack c dc dp).mono_k (by omega))).comp_poly
    polyFun_top4AggregateEnter).of_eq (fun _ => rfl)

theorem aggnL57GOn (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57GOn c b t d dc dp u v e f) (fun n z => ContCtxOK c n z.1) 5 := by
  have hp : TN (fun z : AggnPhaseCtx × AggnAggregateState =>
      (z.1, Algo.aggnAggregatePack c dc dp z.1 z.2)) (fun n z => ContCtxOK c n z.1) 5 :=
    (ofPoly polyFun_fst _ _).pair
      (((aggnAggregatePack c dc dp).mono_k (by omega)).restrict (fun _ _ h => h.1))
  have hcont := hp.comp (aggnContinuation (d := d) hc hb ht) (fun _ _ h => h)
  have htag := hcont.comp_poly (polyFun_fst.natEq (polyFun_const 2))
  have hchk := ((aggnL57GNode (c := c) dc dp hc).restrict
    (fun _ (_ : AggnPhaseCtx × AggnAggregateState) (h : ContCtxOK c _ _) => h.1)).comp_poly
    (polyFun_top4aCheck u v e f)
  exact ((htag.pair hchk).comp_poly (polyFun_and polyFun_fst polyFun_snd)).of_eq (fun _ => rfl)

theorem aggnL57GActive (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57GActive c b t d dc dp u v e f) (fun n z => ContCtxOK c n z.1.1) 5 := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have h1 := ofPoly ((psnd (pfst z)).comp polyFun_isNone')
    (fun n (q : Z) => ContCtxOK c n q.1.1) 5
  have h2 : TN (fun q : Z => (Algo.aggnAggregateChild c (q.1, q.2.1, q.2.2.1.1)).isNone)
      (fun n q => ContCtxOK c n q.1.1) 5 :=
    ((poly_comp ((pfst z).pair ((pfst (psnd z)).pair (pfst (pfst (psnd (psnd z))))))
      ((aggnAggregateChild c).mono_k (by omega))).restrict (fun _ _ h => h.1)).comp_poly
      polyFun_isNone'
  have h3 := poly_comp ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z)))))
    (aggnL57GOn (d := d) dc dp u v e f hc hb ht)
  exact ((((h1.pair h2).comp_poly (polyFun_and polyFun_fst polyFun_snd)).pair h3).comp_poly
    (polyFun_and polyFun_fst polyFun_snd)).of_eq (fun _ => rfl)

theorem aggnL57GPos (hc : c + 2 ≤ 5) :
    TN (Algo.aggnL57GPos c dc dp) (fun n z => CtxOK n z.1) 5 := by
  let P := AggnPhaseCtx × AggnL57GState
  have z : PolyFun (fun q : P => q) := polyFun_id
  have hnode : TN (fun q : P => Algo.aggnL57GNode c dc dp (q.1, q.2.1.1))
      (fun n q => CtxOK n q.1) 5 :=
    poly_comp ((pfst z).pair (pfst (pfst (psnd z)))) (aggnL57GNode dc dp hc)
  exact ((ofPoly (psnd (psnd z)) _ _).pair ((const' 0 _ _).pair
    (hnode.comp_poly polyFun_top4aInit))).comp_poly polyFun_optionGetD

theorem aggnL57GTopChild (hc : c + 2 ≤ 5) :
    TN (Algo.aggnL57GTopChild c dc dp e f) (fun n z => CtxOK n z.1.1) 5 := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hnode : TN (fun q : Z => Algo.aggnL57GNode c dc dp (q.1.1, q.2.2.1.1))
      (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp ((pfst (pfst z)).pair (pfst (pfst (psnd (psnd z))))) (aggnL57GNode dc dp hc)
  have hpos : TN (fun q : Z => Algo.aggnL57GPos c dc dp (q.1.1, q.2.2))
      (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp ((pfst (pfst z)).pair (psnd (psnd z))) (aggnL57GPos dc dp hc)
  have hwidth : TN (fun q : Z => Algo.aggnAggregateWidth c q.1.1) (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp (pfst (pfst z)) ((aggnAggregateWidth c).mono_k (by omega))
  have hgate := ((ofPoly (pfst (psnd z)) _ _).pair ((hwidth.pair
    (hnode.comp_poly polyFun_l57gW4)).comp_poly polyFun_add)).comp_poly plt
  have hch := (hnode.pair ((hpos.comp_poly polyFun_fst).pair
    (hpos.comp_poly polyFun_snd))).comp_poly (polyFun_top4aChild e f)
  have hmap : PolyFun (fun r : Option Top4aNode × AggnPhaseCtx =>
      r.1.bind (fun J => J.1.2.map (fun W => avEmb (r.2, W)))) := by
    have hin : PolyFun (fun r : Top4aNode × AggnPhaseCtx =>
        r.1.1.2.map (fun W => avEmb (r.2, W))) :=
      (((psnd (pfst (pfst polyFun_id))).pair (psnd polyFun_id)).comp (PolyFun.optionElim
        (polyFun_const none) (((psnd polyFun_id).pair (pfst polyFun_id)).comp polyFun_avEmb
          |>.comp polyFun_some))).of_eq (fun r => by
            obtain ⟨⟨⟨ctx, o⟩, α⟩, C⟩ := r
            cases o <;> rfl)
    exact (PolyFun.optionElim (polyFun_const none) hin).of_eq (fun r => by
      obtain ⟨o, C⟩ := r
      cases o <;> rfl)
  have hbind := (hch.pair (ofPoly (pfst (pfst z)) _ _)).comp_poly hmap
  exact (iteT hgate hbind (const' none _ _)).of_eq (fun q => by
    unfold Algo.aggnL57GTopChild; simp only [decide_eq_true_eq])

theorem aggnL57GTopCombine (hc : c + 2 ≤ 5) :
    TN (Algo.aggnL57GTopCombine c dc dp) (fun n z => CtxOK n z.1.1) 5 := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState × RawCoset
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hnode : TN (fun q : Z => Algo.aggnL57GNode c dc dp (q.1.1, q.2.2.1.1.1))
      (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp ((pfst (pfst z)).pair (pfst (pfst (pfst (psnd (psnd z))))))
      (aggnL57GNode dc dp hc)
  have hpos : TN (fun q : Z => Algo.aggnL57GPos c dc dp (q.1.1, q.2.2.1))
      (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp ((pfst (pfst z)).pair (pfst (psnd (psnd z)))) (aggnL57GPos dc dp hc)
  have hpk : TN (fun q : Z => Algo.aggnAggregatePack c dc dp q.1.1 q.2.2.1.1.1)
      (fun n q => CtxOK n q.1.1) 5 :=
    poly_comp ((pfst (pfst z)).pair (pfst (pfst (pfst (psnd (psnd z))))))
      ((aggnAggregatePack c dc dp).mono_k (by omega))
  have hk := ((((hpos.comp_poly polyFun_fst).pair (const' 1 _ _)).comp_poly polyFun_add).pair
    (hnode.comp_poly polyFun_l57gW4)).comp_poly polyFun_min
  have hst := (hnode.pair ((hpos.comp_poly polyFun_fst).pair ((hpos.comp_poly polyFun_snd).pair
    (ofPoly (psnd (psnd (psnd z))) _ _)))).comp_poly polyFun_top4aCombine
  exact ((hpk.pair (const' (none : Option ADState) _ _)).pair
    ((hk.pair hst).comp_poly polyFun_some)).of_eq (fun q => by unfold Algo.aggnL57GTopCombine; rfl)

theorem aggnL57GChild (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57GChild c b t d dc dp u v e f) (fun n z => L57CtxOK c n z.1.1) 5 := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hold : TN (fun q : Z => Algo.aggnL57Child c b t d dc dp (q.1, q.2.1, q.2.2.1))
      (fun n q => L57CtxOK c n q.1.1) 5 :=
    poly_comp ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z)))))
      (aggnL57Child (d := d) dc dp hc hb ht)
  exact (TN.iteT ((aggnL57GActive (d := d) dc dp u v e f hc hb ht).restrict
      (fun _ _ h => h.1))
    ((aggnL57GTopChild (c := c) dc dp e f hc).restrict (fun _ _ h => h.1.1)) hold).of_eq
    (fun q => by unfold Algo.aggnL57GChild; rfl)

theorem aggnL57GCombine (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57GCombine c b t d dc dp u v e f)
      (fun n z => L57CtxOK c n z.1.1 ∧ AggStOK n z.2.2.1.1.1) 5 := by
  let Z := AggnPhaseNode × ℕ × AggnL57GState × RawCoset
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have hact : TN (fun q : Z => Algo.aggnL57GActive c b t d dc dp u v e f (q.1, q.2.1, q.2.2.1))
      (fun n q => L57CtxOK c n q.1.1 ∧ AggStOK n q.2.2.1.1.1) 5 :=
    (poly_comp ((pfst z).pair ((pfst (psnd z)).pair (pfst (psnd (psnd z)))))
      (aggnL57GActive (d := d) dc dp u v e f hc hb ht)).restrict (fun _ _ h => h.1.1)
  have hold : TN (fun q : Z =>
      ((Algo.aggnL57Combine c b t d dc dp (q.1, q.2.1, q.2.2.1.1, q.2.2.2), none) : AggnL57GState))
      (fun n q => L57CtxOK c n q.1.1 ∧ AggStOK n q.2.2.1.1.1) 5 :=
    (poly_comp ((pfst z).pair ((pfst (psnd z)).pair ((pfst (pfst (psnd (psnd z)))).pair
      (psnd (psnd (psnd z)))))) (aggnL57Combine (d := d) dc dp hc hb ht)).pair
      (const' none _ _)
  exact (TN.iteT hact ((aggnL57GTopCombine (c := c) dc dp hc).restrict (fun _ _ h => h.1.1.1))
    hold).of_eq (fun q => by unfold Algo.aggnL57GCombine; rfl)

theorem aggnL57GFinish (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) :
    TN (Algo.aggnL57GFinish c b t d dc dp u v e f) (fun n z => ContCtxOK c n z.1.1) 5 := by
  let Z := AggnPhaseNode × AggnL57GState
  have z : PolyFun (fun q : Z => q) := polyFun_id
  have htest : TN (fun q : Z =>
      q.1.2.isNone && Algo.aggnL57GOn c b t d dc dp u v e f (q.1.1, q.2.1.1))
      (fun n q => ContCtxOK c n q.1.1) 5 :=
    ((ofPoly ((psnd (pfst z)).comp polyFun_isNone') _ _).pair
      (poly_comp ((pfst (pfst z)).pair (pfst (pfst (psnd z))))
        (aggnL57GOn (d := d) dc dp u v e f hc hb ht))).comp_poly
      (polyFun_and polyFun_fst polyFun_snd)
  have hnode : TN (fun q : Z => Algo.aggnL57GNode c dc dp (q.1.1, q.2.1.1))
      (fun n q => ContCtxOK c n q.1.1) 5 :=
    (poly_comp ((pfst (pfst z)).pair (pfst (pfst (psnd z)))) (aggnL57GNode dc dp hc)).restrict
      (fun _ _ h => h.1)
  have hpos : TN (fun q : Z => Algo.aggnL57GPos c dc dp (q.1.1, q.2))
      (fun n q => ContCtxOK c n q.1.1) 5 :=
    (poly_comp ((pfst (pfst z)).pair (psnd z)) (aggnL57GPos dc dp hc)).restrict
      (fun _ _ h => h.1)
  have htop := (hnode.pair (hpos.comp_poly polyFun_snd)).comp_poly
    (polyFun_top4aFinishP (solve := l57gSolve) (polyFun_const none))
  have hold := ofPoly (((pfst z).pair (pfst (psnd z))).comp polyFun_aggnL57Finish)
    (fun n (q : Z) => ContCtxOK c n q.1.1) 5
  exact (TN.iteT htest htop hold).of_eq (fun q => by unfold Algo.aggnL57GFinish; rfl)

end TN

end Explicit
