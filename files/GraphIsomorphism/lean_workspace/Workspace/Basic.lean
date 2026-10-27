/-
Shared imports for the formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018), `babai-gi-source/quasi25.pdf`.

The paper reduces Graph Isomorphism to String Isomorphism under a group action,
so the two things every module needs are permutation groups and their actions.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
