import Workspace.Algo.AggNodeGuideDefect

/-! # Actual Case 3 outputs are admitted by the recursive Design Lemma

The source dispatch gives the large fixed set. Successful construction
checks equal sizes, so the target inherits the same bound. Thus the actual
outputs carry all arity and defect premises, in their computed numbering.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- Both computed domains satisfy the strict Case 3 size bound. -/
theorem aggnAggregateGuide_large {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)} (hC : AggnPhaseCtxWF c n m C ϕ)
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out)
    (hcase : aggnAggregateDispatch (C,s) = 3) (b : Bool) :
    4*m < 5*(aggnAggregateData ((C,s),b)).2.2.length := by
  have hsrc := aggnAggregateCase_three_fixed hC.action.2.1
    (wf_tidyGens hC.action.2.1 _) hcase
  change 4*m < 5*(aggnAggregateData ((C,s),false)).2.2.length at hsrc
  cases b with
  | false => exact hsrc
  | true => rwa [aggnAggregateGuide_equal_sizes hout] at hsrc

/-- No defect or arity premise is left to the caller of the successful Case 3 constructor. -/
theorem aggnAggregateGuide_admissible {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (hcase : aggnAggregateDispatch (C,s) = 3)
    (b : Bool) :
    2 ≤ C.2.2.2.length ∧ 4*C.2.2.2.length ≤ (aggnAggregateData ((C,s),b)).2.2.length ∧
      (1/2 : ℚ) < defect (decRel (aggnAggregateData ((C,s),b)).2.2.length
        C.2.2.2.length (cond b out.2 out.1).2).Aut := by
  rw [aggnAggregateGuide_decode hout b,RelStructure.toKAry_aut]
  exact aggnGuideNumbered_admissible hC hs htbl hset ht htm b
    (aggnAggregateGuide_covered hout) (aggnAggregateGuide_large hC hout hcase b)

/-- Every input-group string isomorphism transports the actual pair of raw outputs. -/
theorem aggnAggregateGuide_canonical {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C,s.2.2.2.1)))
    (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
    (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10*C.2.2.2.length ≤ m)
    [Nonempty (Fin n)] {out : AmbientPIn × AmbientPIn}
    (hout : aggnAggregateGuide c (C,s) = some out) (σ : decGroup n C.1.1.2)
    (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1) :
    ∃ f : Fin (aggnAggregateData ((C,s),false)).2.2.length ≃
        Fin (aggnAggregateData ((C,s),true)).2.2.length,
      (∀ a, (aggnAggregateGuideEquiv hC hs true (f a)).val =
        ϕ σ (aggnAggregateGuideEquiv hC hs false a).val) ∧
      f ∈ KAryRelStruct.Iso
        (decRel (aggnAggregateData ((C,s),false)).2.2.length C.2.2.2.length out.1.2)
        (decRel (aggnAggregateData ((C,s),true)).2.2.length C.2.2.2.length out.2.2) := by
  obtain ⟨f,hf,hval⟩ := exists_mem_guideMorC ϕ C.2.2.2.length
    (fun b : Bool => cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) false true σ hσ
  let e := ((aggnAggregateGuideEquiv hC hs false).trans f).trans
    (aggnAggregateGuideEquiv hC hs true).symm
  refine ⟨e,?_,?_⟩
  · intro a
    simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply] using hval (aggnAggregateGuideEquiv hC hs false a)
  · have hm := aggnGuideNumberedStruct_map_mor hC hs htbl hset ht htm false true f hf
    have hi := RelStructure.toKAry_iso (fun _ => rfl) (fun _ => rfl) hm
    have hx := aggnAggregateGuide_decode hout false
    have hy := aggnAggregateGuide_decode hout true
    simp only [Bool.cond_false] at hx
    simp only [Bool.cond_true] at hy
    rw [hx,hy]
    exact hi

end Algo
