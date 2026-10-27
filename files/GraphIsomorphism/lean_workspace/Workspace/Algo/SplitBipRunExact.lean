import Workspace.Algo.SplitBipCallBound
import Workspace.Algo.SplitBipRun

/-! The time and storage limits are chosen once, before the input degree.
The actual call budget and uncapped-state bounds show that neither limit
alters a represented Split-or-Johnson computation. -/
namespace Algo
open RAM Babai

theorem exists_sbipRun_exact (c : ℕ) :
    ∃ t d,QuasiFun (sbipRun c t d) ∧
      ∀ m I,SbipNodeValid m I → ∀ f,sbipNodeMeasure I < f →
        sbipRun c t d I = some ((sbipRound c).value f I) := by
  obtain ⟨t,ht⟩ := exists_sbipRun_count c
  obtain ⟨B,hB,hb⟩ := exists_sbipOrbit_envelope c (Round.roundCount t)
    (Round.quasiPolyBound_roundCount t)
  obtain ⟨d,hd⟩ := hB
  refine ⟨t,d,quasiFun_sbipRun c t d,?_⟩
  intro m I hI f hf
  apply sbipRun_eq_value c t d f I hf (ht m I hI f)
  intro k hk hcount
  exact (hb m I hI k hcount).trans (hd _)

theorem exists_sbipFamilyRun_exact (c : ℕ) :
    ∃ t d,QuasiFun (sbipFamilyRun c t d) ∧
      ∀ m I,SbipNodeValid m (I,1) →
        sbipFamilyRun c t d I =
          some ((sbipRound c).value (sbipNodeMeasure (I,1)+1) (I,1)) := by
  obtain ⟨t,d,hr,he⟩ := exists_sbipRun_exact c
  exact ⟨t,d,quasiFun_sbipFamilyRun c t d,fun m I hI => he m (I,1) hI _ (by omega)⟩

end Algo
