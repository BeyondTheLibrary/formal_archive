/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: what the round of Sec. 15, lines 5–7 computes after the two phases of
Procedure AggregateCertificates is the same at every state the phases may end in.
-/
import Workspace.Algo.AggNodeGensSame

/-!
# The continuation after AggregateCertificates depends only on the answers

The two phases of Procedure AggregateCertificates (Sec. 13.2) end in a state whose stores
hold the certificates and whose comparison table holds the comparisons; both are the answers
of calls, and each answer may come in any encoding.  The states the phases may end in are
those of `Algo.AggnL57Post`: complete stores and a complete comparison table, whose decoded
contents are fixed by the paper.

`Algo.aggnContinuation_congr` shows that the continuation (the exit taken and the two lists
of versions, Sec. 13.2 and Sec. 15 lines 6–7a) is the same raw value at all these states,
and `Algo.aggnAggregateMajority_congr` does the same for the input of Cor. 12.0.10 at
outcome (2a).  So the round of lines 5–7 makes the same calls after the phases, whatever
encoding the answers of the phases came in, as the Master's round `Babai.Line57Shape.red`
(one tree) requires.

* The stores enter through the group `F(z)^Γ` (`Algo.aggnFGamma_same`): its generators differ,
  its group does not (`Algo.aggnAggregateData_spec`), and everything computed from it depends
  on the group only (`Workspace/Algo/AggNodeGensSame.lean`).
* The comparison table enters the local guide of outcome (3) only through the tuple test
  `Algo.aggnGuideTuple`, whose value is fixed by the decoded comparisons
  (`Algo.aggnGuideTuple_spec`) on the tuples the guide asks about.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction

/-- The class representatives depend only on the relation on the listed elements. -/
theorem aggnClassReps_congr {α : Type*} [DecidableEq α] {r r' : α → α → Bool} {L : List α}
    (h : ∀ a ∈ L, ∀ b ∈ L, r a b = r' a b) : aggnClassReps r L = aggnClassReps r' L := by
  unfold aggnClassReps aggnFirstBy
  refine List.filter_congr fun a ha => ?_
  rw [List.filter_congr (fun b hb => h b hb a ha)]

section Unique

variable {c n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
  (hC : AggnPhaseCtxWF c n m C ϕ)

include hC

/-- The generators of `F(z)^Γ` read off two complete stores generate the same group. -/
theorem aggnFGamma_same {s s' : AggnAggregateState} (hs : AggnStoresComplete c ϕ s.1.2.1)
    (hs' : AggnStoresComplete c ϕ s'.1.2.1) (b : Bool) :
    RawGensSame m (aggnAggregateData ((C, s), b)).2.1 (aggnAggregateData ((C, s'), b)).2.1 :=
  ⟨wf_tidyGens hC.action.2.1 _, wf_tidyGens hC.action.2.1 _, by
    rw [(aggnAggregateData_spec hC hs b).2.1, (aggnAggregateData_spec hC hs' b).2.1]⟩

variable {s s' : AggnAggregateState} (hs : AggnStoresComplete c ϕ s.1.2.1)
  (hs' : AggnStoresComplete c ϕ s'.1.2.1)
include hs hs'

theorem aggnAggregateFixed_congr (b : Bool) :
    (aggnAggregateData ((C, s), b)).2.2 = (aggnAggregateData ((C, s'), b)).2.2 :=
  (aggnFGamma_same hC hs hs' b).aggFixed hC.action.2.1

theorem aggnAggregateImage_same (b : Bool) :
    (aggnAggregateImage ((C, s), b)).1 = (aggnAggregateImage ((C, s'), b)).1 ∧
      RawGensSame m (aggnAggregateImage ((C, s), b)).2 (aggnAggregateImage ((C, s'), b)).2 :=
  ⟨rfl, aggnFGamma_same hC hs hs' b⟩

theorem aggnAggregateDispatch_congr : aggnAggregateDispatch (C, s) = aggnAggregateDispatch (C, s') := by
  have h := aggnFGamma_same hC hs hs' false
  unfold aggnAggregateDispatch aggnAggregateCase
  rw [h.aggnCase1 hC.action.2.1, h.aggnCase2 hC.action.2.1]

theorem aggnAggregateGiantBranch_congr :
    aggnAggregateGiantBranch (C, s) = aggnAggregateGiantBranch (C, s') := by
  have h := aggnFGamma_same hC hs hs' false
  unfold aggnAggregateGiantBranch
  dsimp only
  rw [h.aggnCase2 hC.action.2.1, h.aggnCase2a hC.action.2.1]

theorem aggnSideCase2b_congr (b : Bool) :
    aggnSideCase2b ((C, s), b) = aggnSideCase2b ((C, s'), b) := by
  have h := aggnFGamma_same hC hs hs' b
  unfold aggnSideCase2b aggnAggregateImage
  rw [h.aggnCase2 hC.action.2.1, h.aggnCase2a hC.action.2.1]

theorem aggnRejectCase_congr : aggnRejectCase (C, s) = aggnRejectCase (C, s') := by
  unfold aggnRejectCase
  rw [aggnSideCase2b_congr hC hs hs', aggnSideCase2b_congr hC hs hs']

theorem aggnRejectDefect_congr : aggnRejectDefect (C, s) = aggnRejectDefect (C, s') := by
  unfold aggnRejectDefect
  rw [aggnAggregateFixed_congr hC hs hs', aggnAggregateFixed_congr hC hs hs']

theorem aggnCaseOneOutcome_congr (b : Bool) :
    aggnCaseOneOutcome ((C, s), b) = aggnCaseOneOutcome ((C, s'), b) := by
  unfold aggnCaseOneOutcome aggnAggregatePartition
  rw [(aggnFGamma_same hC hs hs' b).aggnOrbitPartition hC.action.2.1]

theorem aggnAggregateCase2b_congr (b : Bool) :
    aggnAggregateCase2b ((C, s), b) = aggnAggregateCase2b ((C, s'), b) := by
  unfold aggnAggregateCase2b aggnAggregateImage
  rw [(aggnFGamma_same hC hs hs' b).aggnCase2bFamily hC.action.2.1]

theorem aggnCase2bSplitFamily_congr (b' t d : ℕ) (b : Bool) :
    aggnCase2bSplitFamily c b' t d ((C, s), b) = aggnCase2bSplitFamily c b' t d ((C, s'), b) := by
  unfold aggnCase2bSplitFamily aggnCase2bEntries
  rw [aggnAggregateCase2b_congr hC hs hs']

theorem aggnAggregateMajority_congr (b : Bool) :
    aggnAggregateMajority ((C, s), b) = aggnAggregateMajority ((C, s'), b) :=
  (aggnFGamma_same hC hs hs' b).aggnLargeOrbitPoints hC.action.2.1

theorem top4AggregateEnter_congr : top4AggregateEnter (C, s) = top4AggregateEnter (C, s') := by
  unfold top4AggregateEnter top4AggregateInput
  rw [aggnAggregateMajority_congr hC hs hs', aggnAggregateMajority_congr hC hs hs']

theorem aggnGuidePrepare_congr (tbl : RawAggCompareTable) :
    aggnGuidePrepare c ((C, s), tbl) = aggnGuidePrepare c ((C, s'), tbl) := by
  unfold aggnGuidePrepare
  dsimp only
  rw [aggnAggregateFixed_congr hC hs hs', aggnAggregateFixed_congr hC hs hs']

end Unique

/-! ### The local guide depends only on the decoded comparisons -/

section Guide

variable {c n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
  (hC : AggnPhaseCtxWF c n m C ϕ) {tbl tbl' : RawAggCompareTable}
  (htbl : AggnCompareTableFor c ϕ tbl) (htbl' : AggnCompareTableFor c ϕ tbl')
  (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
  (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
  [Nonempty (Fin n)]
include hC htbl htbl' hset ht htm

/-- The tuple test of the local guide has the same value on two complete comparison tables,
on tuples of `t` distinct points of `Γ`. -/
theorem aggnGuideTuple_congr (b : Bool) {u v : List ℕ} (hu : u.Nodup) (hv : v.Nodup)
    (hult : ∀ a ∈ u, a < m) (hvlt : ∀ a ∈ v, a < m) (hul : u.length = C.2.2.2.length)
    (hvl : v.length = C.2.2.2.length) :
    aggnGuideTuple ((C.1, tbl), (b, u, v)) = aggnGuideTuple ((C.1, tbl'), (b, u, v)) :=
  Bool.eq_iff_iff.2 ((aggnGuideTuple_spec hC htbl hset ht htm b hu hv hult hvlt hul hvl).trans
    (aggnGuideTuple_spec hC htbl' hset ht htm b hu hv hult hvlt hul hvl).symm)

/-- A tuple of the guide rows: `t` distinct points of the list `D`. -/
theorem aggnGuideRows_wf {D row : List ℕ} (hD : ∀ a ∈ D, a < m)
    (hrow : row ∈ aggnGuideRows c (C.2.2.2, C.2.1, D)) :
    row.Nodup ∧ (∀ a ∈ row, a < m) ∧ row.length = C.2.2.2.length := by
  have hg : C.2.2.2.length ≤ guardBound c C.2.1.length := hC.guard
  obtain ⟨hl, hmem, hnd⟩ := (aggnGuideRows_mem hg).1 hrow
  exact ⟨hnd, fun a ha => hD a (hmem a ha), hl⟩

/-- The tuple of points of `D` a side row names. -/
theorem aggnGuideSide_wf {D row : List ℕ} (hDn : D.Nodup) (hD : ∀ a ∈ D, a < m)
    (hrow : row ∈ aggnGuideRows c (C.2.2.2, C.2.1, List.range D.length)) :
    (rawRestrictStr (D, row)).Nodup ∧ (∀ a ∈ rawRestrictStr (D, row), a < m) ∧
      (rawRestrictStr (D, row)).length = C.2.2.2.length := by
  have hg : C.2.2.2.length ≤ guardBound c C.2.1.length := hC.guard
  obtain ⟨hl, hmem, hnd⟩ := (aggnGuideRows_mem hg).1 hrow
  have hlt : ∀ i ∈ row, i < D.length := fun i hi => List.mem_range.1 (hmem i hi)
  have hget : ∀ (i : ℕ) (hi : i ∈ row), rawGet (D, i) = D[i]'(hlt i hi) := fun i hi => by
    simp [rawGet, List.getElem?_eq_getElem (hlt i hi)]
  refine ⟨?_, ?_, by simp [hl]⟩
  · unfold rawRestrictStr
    refine List.Nodup.map_on (fun i hi j hj he => ?_) hnd
    rw [hget i hi, hget j hj] at he
    exact (List.Nodup.getElem_inj_iff hDn).1 he
  · intro a ha
    unfold rawRestrictStr at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    rw [hget i hi]
    exact hD _ (List.getElem_mem _)

/-- §13.2, case (3), **the local guide on two complete comparison tables**: the constructor
returns the same structures, or rejects on both. -/
theorem aggnGuideBuild_tbl_congr {Dx Dy : List ℕ} (hDxn : Dx.Nodup) (hDx : ∀ a ∈ Dx, a < m)
    (hDyn : Dy.Nodup) (hDy : ∀ a ∈ Dy, a < m) :
    aggnGuideBuild ((C.2.2.2, C.2.1), ((C.1, tbl),
        aggnGuideReps ((C.1, tbl), aggnGuideRows c (C.2.2.2, C.2.1, Dx)),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx), aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy))) =
      aggnGuideBuild ((C.2.2.2, C.2.1), ((C.1, tbl'),
        aggnGuideReps ((C.1, tbl'), aggnGuideRows c (C.2.2.2, C.2.1, Dx)),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy))) := by
  set rows := aggnGuideRows c (C.2.2.2, C.2.1, Dx) with hrows
  have hreps : aggnGuideReps ((C.1, tbl), rows) = aggnGuideReps ((C.1, tbl'), rows) := by
    unfold aggnGuideReps
    refine aggnClassReps_congr fun a ha b hb => ?_
    obtain ⟨han, hal, hall⟩ := aggnGuideRows_wf hC htbl htbl' hset ht htm hDx ha
    obtain ⟨hbn, hbl, hbll⟩ := aggnGuideRows_wf hC htbl htbl' hset ht htm hDx hb
    exact aggnGuideTuple_congr hC htbl htbl' hset ht htm false han hbn hal hbl hall hbll
  have hrepsSub : ∀ u ∈ aggnGuideReps ((C.1, tbl), rows), u ∈ rows := fun u hu =>
    List.mem_of_mem_filter hu
  -- the test of a relation, on the tuples the guide asks about
  have htest : ∀ (b : Bool), ∀ u ∈ rows, ∀ row ∈ (cond b (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy))
      (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx))).2,
      aggnGuideRelTest (((((C.1, tbl), b, cond b (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy))
        (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx)))), u), row) =
      aggnGuideRelTest (((((C.1, tbl'), b, cond b (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy))
        (aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx)))), u), row) := by
    intro b u hu row hrow
    obtain ⟨hun, hul, hull⟩ := aggnGuideRows_wf hC htbl htbl' hset ht htm hDx hu
    unfold aggnGuideRelTest
    dsimp only
    cases b
    · obtain ⟨hvn, hvl, hvll⟩ := aggnGuideSide_wf hC htbl htbl' hset ht htm hDxn hDx hrow
      exact aggnGuideTuple_congr hC htbl htbl' hset ht htm false hun hvn hul hvl hull hvll
    · obtain ⟨hvn, hvl, hvll⟩ := aggnGuideSide_wf hC htbl htbl' hset ht htm hDyn hDy hrow
      exact aggnGuideTuple_congr hC htbl htbl' hset ht htm true hun hvn hul hvl hull hvll
  have hrel : ∀ b : Bool,
      aggnGuideRelations (aggnGuideAt (((C.1, tbl), aggnGuideReps ((C.1, tbl), rows),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx), aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy)), b)) =
      aggnGuideRelations (aggnGuideAt (((C.1, tbl'), aggnGuideReps ((C.1, tbl'), rows),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx), aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy)), b)) := by
    intro b
    unfold aggnGuideRelations aggnGuideAt
    dsimp only
    rw [← hreps]
    refine List.map_congr_left fun u hu => ?_
    unfold aggnGuideRel
    exact List.filter_congr fun row hrow => htest b u (hrepsSub u hu) row hrow
  have hcov : aggnGuideCovered (aggnGuideAt (((C.1, tbl), aggnGuideReps ((C.1, tbl), rows),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx), aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy)), true)) =
      aggnGuideCovered (aggnGuideAt (((C.1, tbl'), aggnGuideReps ((C.1, tbl'), rows),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dx),
        aggnGuideSideRows c ((C.2.2.2, C.2.1), Dy)), true)) := by
    unfold aggnGuideCovered aggnGuideAt
    dsimp only
    rw [← hreps]
    refine Bool.eq_iff_iff.2 ?_
    simp only [List.all_eq_true, List.any_eq_true]
    refine forall₂_congr fun row hrow => exists_congr fun u => and_congr_right fun hu => ?_
    rw [htest true u (hrepsSub u hu) row hrow]
  unfold aggnGuideBuild
  rw [hcov]
  unfold aggnGuideEnter
  simp only [hrel]
  rfl

end Guide

/-! ### The continuation -/

section Continuation

variable {c n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
  (hC : AggnPhaseCtxWF c n m C ϕ) {s s' : AggnAggregateState}
  (hs : AggnStoresComplete c ϕ s.1.2.1) (hs' : AggnStoresComplete c ϕ s'.1.2.1)
  (htbl : AggnCompareTableFor c ϕ (aggnCompareTable c (C, s.2.2.2.1)))
  (htbl' : AggnCompareTableFor c ϕ (aggnCompareTable c (C, s'.2.2.2.1)))
  (hset : LocalCertSetting (decGroup n C.1.1.2) ϕ)
  (ht : LargeK C.2.2.2.length (Nat.card (Fin n))) (htm : 10 * C.2.2.2.length ≤ m)
  [Nonempty (Fin n)]
include hC hs hs' htbl htbl' hset ht htm

theorem aggnFixed_wf (b : Bool) :
    (aggnAggregateData ((C, s), b)).2.2.Nodup ∧ ∀ a ∈ (aggnAggregateData ((C, s), b)).2.2, a < m := by
  refine ⟨List.nodup_range.filter _, fun a ha => ?_⟩
  have := List.mem_range.1 (List.mem_of_mem_filter ha)
  change a < C.1.2.1.length at this
  rw [hC.action.2.1] at this
  exact this

/-- §13.2, case (3), **the local guide at two end states of the phases**. -/
theorem aggnAggregateGuide_congr : aggnAggregateGuide c (C, s) = aggnAggregateGuide c (C, s') := by
  unfold aggnAggregateGuide
  rw [aggnGuidePrepare_congr hC hs hs']
  obtain ⟨hxn, hx⟩ := aggnFixed_wf hC hs hs' htbl htbl' hset ht htm false
  obtain ⟨hyn, hy⟩ := aggnFixed_wf hC hs hs' htbl htbl' hset ht htm true
  rw [aggnAggregateFixed_congr hC hs hs'] at hxn hx hyn hy
  exact aggnGuideBuild_tbl_congr hC htbl htbl' hset ht htm hxn hx hyn hy

theorem aggnGuideSplitFamilies_congr (b t d : ℕ) :
    aggnGuideSplitFamilies c b t d (C, s) = aggnGuideSplitFamilies c b t d (C, s') := by
  unfold aggnGuideSplitFamilies aggnGuideEntries
  rw [aggnAggregateGuide_congr hC hs hs' htbl htbl' hset ht htm]
  cases aggnAggregateGuide c (C, s') with
  | none => rfl
  | some out =>
    simp only [Option.map_some]
    unfold aggnGuideSplitPair aggnGuideEntryPair
    rw [aggnAggregateFixed_congr hC hs hs', aggnAggregateFixed_congr hC hs hs']

/-- §13.2 and §15, lines 5–7a, **the continuation depends only on the answers of the
phases**: at two states the phases of AggregateCertificates may end in (complete stores and
complete comparison tables), the continuation takes the same exit and lists the same
versions. -/
theorem aggnContinuation_congr (b t d : ℕ) :
    aggnContinuation c b t d (C, s) = aggnContinuation c b t d (C, s') := by
  unfold aggnContinuation
  rw [aggnAggregateDispatch_congr hC hs hs', aggnAggregateGiantBranch_congr hC hs hs',
    aggnRejectCase_congr hC hs hs', aggnRejectDefect_congr hC hs hs']
  unfold aggnContCaseOne aggnContCase2b aggnContCase3
  rw [aggnCaseOneOutcome_congr hC hs hs', aggnCaseOneOutcome_congr hC hs hs',
    aggnCase2bSplitFamily_congr hC hs hs', aggnCase2bSplitFamily_congr hC hs hs',
    aggnGuideSplitFamilies_congr hC hs hs' htbl htbl' hset ht htm]

end Continuation

/-! ### The tree of Cor. 12.0.10 at outcome (2a) -/

section Giant

variable {c n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
  (hC : AggnPhaseCtxWF c n m C ϕ) {s s' : AggnAggregateState}
  (hs : AggnStoresComplete c ϕ s.1.2.1) (hs' : AggnStoresComplete c ϕ s'.1.2.1)
  (hG : LocalCertSetting (decGroup n C.1.1.2) ϕ) (hm : HugeM m (Nat.card (Fin n)))

/-- §15, line 5, outcome (2a): **the tree of Cor. 12.0.10 the machine computes is the same at
two end states of the phases** (it depends on the state only through the two large orbits,
`Algo.aggnAggregateMajority_congr`). -/
theorem top4AggregateTree_congr (h2a : aggnAggregateGiantBranch (C, s) = true)
    (h2a' : aggnAggregateGiantBranch (C, s') = true) :
    top4AggregateTree hC hs hG hm h2a = top4AggregateTree hC hs' hG hm h2a' := by
  have e0 := aggnAggregateMajority_congr hC hs hs' false
  have e1 := aggnAggregateMajority_congr hC hs hs' true
  unfold top4AggregateTree top4AggregateSource
  congr!

end Giant

end Algo
