import Workspace.Algo.SplitBipNodeRAM
import Workspace.Algo.SplitBipRecursionCost

/-! The executable Section 9 family evaluator uses fixed exponents for
its time and storage limits. Its RAM bound holds on every raw input.
`SplitBipRunExact` proves that these limits preserve the uncapped value
on every represented paper input. -/
namespace Algo
open RAM Babai

def sbipRun (c t d : ℕ) : RawSbipNode → Option RawSbipAnswers :=
  (sbipRound c).runFamily
    (fun I => Round.roundCount t (Enc.size I))
    (fun I => 2 ^ ((Nat.log 2 (Enc.size I) + 2)^d))

theorem quasiFun_sbipRun (c t d : ℕ) : QuasiFun (sbipRun c t d) := by
  have hsize : PolyFun (Enc.size : RawSbipNode → ℕ) := AggnSizeRoutine.polyFun_size
  apply Round.quasiFun_runFamily
  · exact hsize.comp (Round.polyFun_roundCount t)
  · exact hsize.comp (aggnPolyFun_sizeCap d)
  · exact AggnSizeRoutine.polyFun_size
  · exact (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)).comp_quasiFun
      (quasiFun_sbipNodeChild c)
  · exact quasiFun_sbipNodeInit c
  · exact quasiFun_sbipNodeCombine c
  · exact polyFun_snd.quasiFun
  · exact Round.quasiPolyBound_roundCount t
  · exact quasiPolyBound_witness d
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl

theorem sbipRun_eq_value (c t d f : ℕ) (I : RawSbipNode)
    (hf : sbipNodeMeasure I < f)
    (hc : (sbipRound c).subSteps f I ≤ Round.roundCount t (Enc.size I))
    (hb : ∀ k, 0 < k → k ≤ Round.roundCount t (Enc.size I) →
      Enc.size ((sbipRound c).stepDFS^[k] ((sbipRound c).startState I)) ≤
        2 ^ ((Nat.log 2 (Enc.size I) + 2)^d)) :
    sbipRun c t d I = some ((sbipRound c).value f I) :=
  Round.runFamily_eq_value _ _ _ f I trivial hf hc hb

def sbipFamilyRun (c t d : ℕ) (I : RawSbipTurnInput) : Option RawSbipAnswers :=
  sbipRun c t d (I,1)

theorem quasiFun_sbipFamilyRun (c t d : ℕ) : QuasiFun (sbipFamilyRun c t d) :=
  (polyFun_id.pair (polyFun_const 1)).comp_quasiFun (quasiFun_sbipRun c t d)

end Algo
