import Workspace.Machine.GISpec
import Workspace.Machine.SIDecisionReduction

/-!
# Corollary 1.1.2 for Graph Isomorphism

The program builds the pair instance, calls the clean SI routine, and reads
whether its answer is present. The final bridge changes the workspace convention
to the bare RAM convention. All programs and bounds are independent of `n`.
-/

namespace RAM.GIReduction

open Algo Targets Babai.GraphToString

/-- **Corollary 1.1.2, Sec. 1.1, GI part from the SI workspace routine.**
The hypothesis is the same remaining obligation used to prove Theorem 1.1.1.
The bare theorem alone has no clean-composition bridge in the current machine library. -/
theorem corollary_1_1_2_GI_of_workspaceRoutine (h : SIWorkspaceRoutine) :
    Corollary_1_1_2_GI_statement := by
  obtain ⟨P, T, hT, hP⟩ := siDecision_of_polyReduction (A := GIInput)
    (fun _ => GIInput.raw) (fun _ _ => rfl) build polyFun_build
    (fun n => (pairList n).length) (fun _ => 2) (fun _ a => siInput a.X a.Y)
    (fun _ a => by rw [build_spec]; exact encode_si_eq _) h
  refine ⟨P, T, hT, fun n => ?_⟩
  obtain ⟨f, hf, hcomp⟩ := hP n
  exact ⟨f, fun a => (hf a).trans (siInput_correct a.X a.Y), hcomp⟩

end RAM.GIReduction

#print axioms RAM.GIReduction.corollary_1_1_2_GI_of_workspaceRoutine
