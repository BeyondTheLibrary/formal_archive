import Workspace.Algo.AggNodeGuideCanonical

/-! # The successful raw outputs are the proved guide structures

The decoder accounts for every natural relation index, including empty
relations after the last stored label. The result consumes the actual
aggregate constructor and comparison cache.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The complete numbered decoder, including indices beyond the stored table. -/
theorem aggnGuideEnter_numbered (c : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState)
    (tbl : RawAggCompareTable) (b : Bool) :
    decRel (aggnAggregateData ((C,s),b)).2.2.length C.2.2.2.length
      (aggnGuideEnter ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl),b)).2 =
      (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).toKAry (fun _ => rfl) := by
  let reps := aggnGuideReps ((C.1,tbl),
    aggnGuideRows c (C.2.2.2,C.2.1,(aggnAggregateData ((C,s),false)).2.2))
  let ctx : AggnGuideRelCtx := ((C.1,tbl),b,
    aggnGuideSideRows c ((C.2.2.2,C.2.1),(aggnAggregateData ((C,s),b)).2.2))
  have hrel : (aggnGuideEnter ((C.2.2.2,C.2.1),aggnGuidePrepare c ((C,s),tbl),b)).2 =
      aggnGuideRelations (ctx,reps) := by cases b <;> rfl
  rw [hrel]
  apply congrArg KAryRelStruct.mk
  funext i
  apply Set.ext
  intro v
  by_cases hi : i < reps.length
  · rw [dif_pos (show i < (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).numRel from hi)]
    rfl
  · rw [dif_neg (show ¬ i < (aggnGuideNumberedStruct (c := c) (C := C) (s := s) (tbl := tbl) b).numRel from hi)]
    change (tupleOf v ∈ (aggnGuideRelations (ctx,reps)).getD i []) ↔ False
    rw [getD_of_length_le (by rw [aggnGuideRelations_length]; exact Nat.le_of_not_gt hi)]
    simp

/-- Successful construction establishes its actual coverage check. -/
theorem aggnAggregateGuide_covered {c : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out) :
    aggnGuideCovered (aggnGuideAt
      (aggnGuidePrepare c ((C,s),aggnCompareTable c (C,s.2.2.2.1)),true)) = true :=
  (aggnGuideBuild_some hout).2.1

/-- Both successful structures use equal-size fixed sets. -/
theorem aggnAggregateGuide_equal_sizes {c : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out) :
    (aggnAggregateData ((C,s),false)).2.2.length = (aggnAggregateData ((C,s),true)).2.2.length :=
  (aggnGuideBuild_some hout).1

/-- The actual two raw outputs decode to the fully specified numbered guides. -/
theorem aggnAggregateGuide_decode {c : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {out : AmbientPIn × AmbientPIn} (hout : aggnAggregateGuide c (C,s) = some out) (b : Bool) :
    decRel (aggnAggregateData ((C,s),b)).2.2.length C.2.2.2.length (cond b out.2 out.1).2 =
      (aggnGuideNumberedStruct (c := c) (C := C) (s := s)
        (tbl := aggnCompareTable c (C,s.2.2.2.1)) b).toKAry (fun _ => rfl) := by
  obtain ⟨_,_,he⟩ := aggnGuideBuild_some hout
  subst out
  cases b <;> exact aggnGuideEnter_numbered c C s _ _

end Algo
