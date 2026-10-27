import Workspace.Algo.Chain
import Workspace.Algo.ChainRaw
import Workspace.Algo.ChainBuild
import Workspace.Algo.ChainBuildRaw
import Workspace.Algo.ChainBuildPoly
import Workspace.Algo.Order
import Workspace.Algo.Transversal
import Workspace.Algo.Encodings
import Workspace.Algo.Orbits
import Workspace.Algo.Perm
import Workspace.Algo.Round
import Workspace.Algo.Evaluator
import Workspace.Algo.EvaluatorRAM

/-!
# The algorithmic layer

The plan is in `Workspace/Algo/DESIGN.md`.  What exists so far is the raw encodings
(`Workspace/Algo/Encodings.lean`), the permutation routines on raw data
(`Workspace/Algo/Perm.lean`), the orbit routines (`Workspace/Algo/Orbits.lean`), the point
stabilizer chain with its sifting table (`Workspace/Algo/Chain.lean`) and the raw sifting loop
(`Workspace/Algo/ChainRaw.lean`), and the computable round (`Workspace/Algo/Round.lean`) with
its depth-first evaluator (`Workspace/Algo/Evaluator.lean`), and the evaluator as a machine
routine with the bridge to `RAM.SIWorkspaceRoutine` (`Workspace/Algo/EvaluatorRAM.lean`).
-/
