import Workspace.Machine.GIFinal
import Workspace.Machine.CIFinal

/-! # Corollary 1.1.2 from the SI workspace routine -/

namespace RAM

/-- **Corollary 1.1.2, Sec. 1.1.** A clean workspace routine for String
Isomorphism gives quasipolynomial algorithms for Graph Isomorphism and Coset
Intersection. The same hypothesis gives Theorem 1.1.1 via
`theorem_1_1_1_of_workspaceRoutine`. -/
theorem corollary_1_1_2_of_workspaceRoutine (h : SIWorkspaceRoutine) :
    Targets.Corollary_1_1_2_GI_statement ∧ Targets.Corollary_1_1_2_CI_statement :=
  ⟨GIReduction.corollary_1_1_2_GI_of_workspaceRoutine h,
    CIReduction.corollary_1_1_2_CI_of_workspaceRoutine h⟩

end RAM

#print axioms RAM.corollary_1_1_2_of_workspaceRoutine
