import Workspace.Algo.AggNodeGuideBuild

/-! # Shape of the computed guide structures

The local coordinate tuples come from the guarded enumeration on consecutive
vertex labels. Filtering them by the local-guide test preserves their arity,
range and lack of repetitions. This supplies the raw relational input
obligations of the Section 9 pipeline.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem aggnGuideRelations_rows {c : ℕ} {ks dom D : List ℕ}
    (hg : ks.length ≤ guardBound c dom.length) (ctx : RawAction × RawAggCompareTable)
    (b : Bool) (reps : List (List ℕ))
    {R : RawRel} (hR : R ∈ aggnGuideRelations ((ctx,b,aggnGuideSideRows c ((ks,dom),D)),reps))
    {row : List ℕ} (hr : row ∈ R) :
    row.length = ks.length ∧ (∀ a ∈ row,a < D.length) ∧ row.Nodup := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hR
  obtain ⟨hrow,_⟩ := aggnGuideRel_mem.mp hr
  obtain ⟨hlen,hsub,hnd⟩ := (aggnGuideRows_mem hg).mp hrow
  exact ⟨hlen,fun a ha => List.mem_range.mp (hsub a ha),hnd⟩

theorem aggnGuideEnter_prepare_fields (c : ℕ) (p : AggnGuidePrepareInput) (b : Bool) :
    (aggnGuideEnter ((p.1.1.2.2.2,p.1.1.2.1),aggnGuidePrepare c p,b)).1 =
      (p.1.1.2.2.2,p.1.1.2.1,List.range (aggnAggregateData (p.1,b)).2.2.length) := by
  cases b <;> rfl

theorem aggnGuideEnter_prepare_rows {c : ℕ} {p : AggnGuidePrepareInput}
    (hg : p.1.1.2.2.2.length ≤ guardBound c p.1.1.2.1.length) (b : Bool)
    {R : RawRel} (hR : R ∈ (aggnGuideEnter
      ((p.1.1.2.2.2,p.1.1.2.1),aggnGuidePrepare c p,b)).2)
    {row : List ℕ} (hr : row ∈ R) :
    row.length = p.1.1.2.2.2.length ∧
      (∀ a ∈ row,a < (aggnAggregateData (p.1,b)).2.2.length) ∧ row.Nodup := by
  cases b <;> exact aggnGuideRelations_rows hg (p.1.1.1,p.2) _ _ hR hr

/-- Both actual outputs have the original arity witness and valid local tuple labels. -/
theorem aggnAggregateGuide_rows {c : ℕ} {p : AggnPhaseCtx × AggnAggregateState}
    (hg : p.1.2.2.2.length ≤ guardBound c p.1.2.1.length)
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c p = some out) (b : Bool) :
    let a := cond b out.2 out.1
    a.1 = (p.1.2.2.2,p.1.2.1,List.range (aggnAggregateData (p,b)).2.2.length) ∧
    ∀ R ∈ a.2,∀ row ∈ R,
      row.length = p.1.2.2.2.length ∧
        (∀ u ∈ row,u < (aggnAggregateData (p,b)).2.2.length) ∧ row.Nodup := by
  obtain ⟨_,_,he⟩ := aggnGuideBuild_some hout
  subst out
  let q : AggnGuidePrepareInput := (p,aggnCompareTable c (p.1,p.2.2.2.2.1))
  cases b with
  | false => exact ⟨aggnGuideEnter_prepare_fields c q false,fun R hR row hr =>
      aggnGuideEnter_prepare_rows (p := q) hg false hR hr⟩
  | true => exact ⟨aggnGuideEnter_prepare_fields c q true,fun R hR row hr =>
      aggnGuideEnter_prepare_rows (p := q) hg true hR hr⟩

end Algo
