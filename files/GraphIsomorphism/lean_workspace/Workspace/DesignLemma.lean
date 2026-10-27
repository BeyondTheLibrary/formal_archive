/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8: The Design Lemma.
-/
import Workspace.DesignLemma.Defs
import Workspace.DesignLemma.NonClique
import Workspace.DesignLemma.Correctness
import Workspace.DesignLemma.Main
import Workspace.DesignLemma.Bridge
import Workspace.DesignLemma.NatRank

/-!
# §8 The Design Lemma

Version 2.5, Section 8 (lines 3680–3925 of `babai-gi-source/quasi25.txt`).

| Paper | Lean file |
|---|---|
| §8.1 Definition 8.1.1 | `Workspace/DesignLemma/Defs.lean` |
| §8.1 Theorems 8.1.2, 8.1.5, Obs. 8.1.3, Remark 8.1.4 | `Workspace/DesignLemma/Main.lean` |
| §8.2 Procedure "Design Lemma", Thm 8.2.1, Remark 8.2.2 | `Workspace/DesignLemma/Defs.lean`, `Workspace/DesignLemma/Correctness.lean` |
| §8.3 Lemma 8.3.1, Remark 8.3.2, Claim 8.3.3 | `Workspace/DesignLemma/NonClique.lean` |
| §8.4 Claims 8.4.1, 8.4.2 | `Workspace/DesignLemma/Correctness.lean` |
-/
