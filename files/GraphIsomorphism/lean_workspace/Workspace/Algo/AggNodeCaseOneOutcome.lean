import Workspace.Algo.AggNodeAggregatePartition
import Workspace.Algo.AggNodeRestoreValidity

/-! Case 1 returns the single full-domain partition in the raw answer type
shared by the recursive Split-or-Johnson routine and Procedure Align.
Its decoder is exactly the paper's orbit outcome, including its canonicity.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets Babai Equiv

def aggnCaseOneOutcome (z : (AggnPhaseCtx × AggnAggregateState) × Bool) : RawAlignOutcome :=
  rawAlignPartition (aggnAggregatePartition z)

theorem aggnPolyFun_caseOneOutcome : PolyFun aggnCaseOneOutcome :=
  aggnPolyFun_aggregatePartition.comp polyFun_rawAlignPartition

theorem aggnCaseOneOutcome_decode {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1) (b : Bool) :
    decAlignOutcome m (aggnCaseOneOutcome ((C,s),b)) =
      some (orbitSplitOutcome (bigFGamma ϕ
        (cond b (decStrN n C.2.2.1) (decStrN n C.2.1)) C.2.2.2.length)) := by
  change some (aggnDecodePartition m (aggnAggregatePartition ((C,s),b))) = _
  rw [aggnAggregatePartition_spec hC hs b]

theorem aggnCaseOneOutcome_valid {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (hcase : aggnAggregateDispatch (C,s) = 1) :
    ∃ Z, decAlignOutcome m (aggnCaseOneOutcome ((C,s),false)) = some Z ∧
      IsSplitOutcome (4/5 : ℝ) Set.univ Z :=
  ⟨_,rfl,aggnAggregatePartition_output hC hs hcase⟩

/-- Every input string isomorphism carries the decoded source output to the
actual decoded target output, even though raw block labels use least points. -/
theorem aggnCaseOneOutcome_canonical {c n m : ℕ} {C : AggnPhaseCtx} {s : AggnAggregateState}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    [MulAction (Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    (hC : AggnPhaseCtxWF c n m C ϕ) (hs : AggnStoresComplete c ϕ s.1.2.1)
    (σ : decGroup n C.1.1.2) (hσ : strAct (decStrN n C.2.1) σ.val = decStrN n C.2.2.1) :
    decAlignOutcome m (aggnCaseOneOutcome ((C,s),true)) =
      (decAlignOutcome m (aggnCaseOneOutcome ((C,s),false))).map (fun Z => ϕ σ • Z) := by
  rw [aggnCaseOneOutcome_decode hC hs true,aggnCaseOneOutcome_decode hC hs false]
  simp only [Bool.cond_true,Bool.cond_false,Option.map_some]
  apply congrArg some
  rw [← hσ]
  exact isCanonicalStructure_orbitSplitOutcome hK ϕ C.2.2.2.length (decStrN n C.2.1) σ

end Algo
