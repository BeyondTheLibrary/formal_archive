/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

All results that the paper cites from the literature without proof, as `axiom`s.
One file per paper section; see `PLAN.md` (decision 1) and `CITED.md`.
`CameronRecognition.lean` holds the one algorithmic axiom, the structure of a Cameron group
in polynomial time [BaLS], stated on the RAM.  Proposition 10.5.4 was
an axiom until it was proved (`Workspace/Algo/StdBlocksProved.lean`).
-/
import Workspace.Cited.Prelim
import Workspace.Cited.AltQuotients
import Workspace.Cited.Luks
import Workspace.Cited.CameronRecognition
