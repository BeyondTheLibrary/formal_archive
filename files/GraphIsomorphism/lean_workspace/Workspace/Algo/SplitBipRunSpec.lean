import Workspace.Algo.SplitBipRunExact
import Workspace.Algo.SplitBipTurnValue

/-! The concrete RAM family is nonempty and all its entries decode to
valid Split-or-Johnson outcomes. The separate family transport proof is
still needed to establish its canonical behavior under isomorphisms. -/
namespace Algo
open RAM Babai

theorem exists_sbipRun_valid (c : ℕ) :
    ∃ t d,QuasiFun (sbipRun c t d) ∧
      ∀ m I,SbipNodeValid m I → ∃ A,sbipRun c t d I = some A ∧
        (∃ o,o ∈ A) ∧ SbipAnswersGood m I A := by
  obtain ⟨t,d,hr,he⟩ := exists_sbipRun_exact c
  refine ⟨t,d,hr,?_⟩
  intro m I hI
  let f := sbipNodeMeasure I+1
  have hf : sbipNodeMeasure I < f := Nat.lt_succ_self _
  exact ⟨(sbipRound c).value f I,he m I hI f hf,sbipValue_valid_nonempty hI hf⟩

theorem exists_sbipFamilyRun_valid (c : ℕ) :
    ∃ t d,QuasiFun (sbipFamilyRun c t d) ∧
      ∀ m I,SbipNodeValid m (I,1) → ∃ A,sbipFamilyRun c t d I = some A ∧
        (∃ o,o ∈ A) ∧ SbipAnswersGood m (I,1) A := by
  obtain ⟨t,d,hr,he⟩ := exists_sbipRun_valid c
  exact ⟨t,d,quasiFun_sbipFamilyRun c t d,fun m I hI => he m (I,1) hI⟩

end Algo
