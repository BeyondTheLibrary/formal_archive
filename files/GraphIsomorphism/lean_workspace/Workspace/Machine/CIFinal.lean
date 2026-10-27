import Workspace.Machine.CIRaw
import Workspace.Machine.SIDecisionReduction

/-! # Corollary 1.1.2 for Coset Intersection -/

namespace RAM.CIReduction

open Targets Algo

/-- **Corollary 1.1.2, Sec. 1.1, CI part from the SI workspace routine.**
One polynomial constructor and one clean SI call serve all permutation degrees. -/
theorem corollary_1_1_2_CI_of_workspaceRoutine (h : SIWorkspaceRoutine) :
    Corollary_1_1_2_CI_statement := by
  obtain ⟨P, T, hT, hP⟩ := siDecision_of_polyReduction (A := CIInput)
    (fun _ => rawOfCI) (fun _ => encode_rawOfCI) build polyFun_build
    (fun n => n * n) (fun _ => 2) (fun _ => instanceSI)
    (fun _ a => by rw [build_spec]; exact encode_si_eq _) h
  refine ⟨P, T, hT, fun n => ?_⟩
  obtain ⟨f, hf, hcomp⟩ := hP n
  exact ⟨f, fun a => (hf a).trans (instanceSI_correct a), hcomp⟩

end RAM.CIReduction

#print axioms RAM.CIReduction.corollary_1_1_2_CI_of_workspaceRoutine
