/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 1.1.1 on the RAM, with no open hypothesis.
-/
import Workspace.Algo.TopMasterL57Final
import Workspace.Algo.TopMasterRoute4Dom
import Workspace.Machine.Final
import Workspace.Machine.Corollary112

/-!
# Theorem 1.1.1 on the RAM

Route 4 with a dominant class is `Algo.siWorkspaceRoutine_of_route5`; route 5 is
`Algo.exists_masterL57SupplyH` at constants of the round of lines 5–7 that meet their
specifications (`Algo.exists_l57Constants`). Together they give `RAM.SIWorkspaceRoutine`, and
the machine layer turns it into `RAM.Targets.Theorem_1_1_1_statement`
(`RAM.theorem_1_1_1_of_workspaceRoutine`).

The same routine closes the decision form of Theorem 1.1.1, which is how Sec. 1.1 words the
String Isomorphism problem ("does there exist an element of `G` that transforms `x` into
`y`"), and Corollary 1.1.2 (Graph Isomorphism and Coset Intersection).

The other two corollaries of §1.1 use `Algo.siWorkspaceRoutine` from this file, so they sit in
the files that import it: Corollary 1.1.3 is `Algo.corollary_1_1_3` (`Algo/Corollary113.lean`)
and Corollary 1.1.4 is `Algo.corollary_1_1_4` (`Algo/Corollary114.lean`).
-/

set_option synthInstance.maxSize 4096

namespace Algo
open RAM RAM.Targets Babai

/-- **Theorem 1.1.1 on the RAM, in the workspace convention**: the Master Algorithm (Section
15) solves String Isomorphism in quasipolynomial time. -/
theorem siWorkspaceRoutine : SIWorkspaceRoutine := by
  obtain ⟨c', b', t, d, dc, dp, hc2, hok, hsolver, hbip⟩ := exists_l57Constants
  obtain ⟨q5, hq5m, hq5, h5⟩ := exists_masterL57SupplyH (E := masterL57E c' b' t d dc dp) hok
    masterTopEF_spec hsolver hbip hc2 (masterL57E_spec c' b' t d dc dp)
  exact siWorkspaceRoutine_of_route5 (c := 0)
    (quasiFun_masterL57Hint _ _ _ _ _ _ _ _ _ _) hq5m hq5 h5

/-- **Theorem 1.1.1** (§1.1): String Isomorphism, hence Graph Isomorphism, is solvable in
quasipolynomial time, on the RAM model of `Workspace/Machine/`. -/
theorem theorem_1_1_1 : Theorem_1_1_1_statement :=
  theorem_1_1_1_of_workspaceRoutine siWorkspaceRoutine

/-- **Theorem 1.1.1** (§1.1), in the words of Sec. 1.1: *"The String Isomorphism (SI)
problem asks, given `G`, `x`, and `y`, does there exist an element of `G` that transforms `x`
into `y`"* and *"The String Isomorphism problem can be solved in quasipolynomial time."*
This is the decision form; `Algo.theorem_1_1_1` is the stronger search form of Def. 11.1.2.
The program runs the SI routine and reads whether its answer is present
(`RAM.siDecision_of_polyReduction` with the identity as the constructor). -/
theorem theorem_1_1_1_decision : Theorem_1_1_1_decision_statement := by
  obtain ⟨P, T, hT, hP⟩ := siDecision_of_polyReduction (ι := ℕ × ℕ)
    (A := fun p => SIInput p.1 p.2) (α := RawSI) (fun _ a => rawOfSI a)
    (fun _ a => (encode_si_eq a).symm) id polyFun_id (fun p => p.1) (fun p => p.2)
    (fun _ a => a) (fun _ a => encode_si_eq a) siWorkspaceRoutine
  exact ⟨P, T, hT, fun n s => hP (n, s)⟩

/-- **Corollary 1.1.2** (§1.1): *"The Graph Isomorphism problem and the Coset Intersection
problem can be solved in quasipolynomial time."* -/
theorem corollary_1_1_2 :
    Corollary_1_1_2_GI_statement ∧ Corollary_1_1_2_CI_statement :=
  corollary_1_1_2_of_workspaceRoutine siWorkspaceRoutine

end Algo
