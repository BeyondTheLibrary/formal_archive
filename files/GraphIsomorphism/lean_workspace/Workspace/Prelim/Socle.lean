/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The socle (Definition 10.2.1), shared by Section 10 and Section 11.
-/
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The socle

Definition 10.2.1 defines the socle; §11.2 repeats the definition verbatim ("The socle
`Soc(G)` of the group `G` is defined as the product of its minimal normal subgroups").
Both sections use the same notion, so it is defined once here.
-/

namespace Babai

/-- A minimal normal subgroup: a nontrivial normal subgroup containing no smaller
nontrivial normal subgroup of the whole group. -/
def IsMinimalNormal {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N

/-- **Definition 10.2.1**, §10.2 (repeated in §11.2).

> The *socle* `Soc(G)` of a group `G` is the product of its minimal normal subgroups.

The product of a family of normal subgroups is the subgroup they generate, i.e. their
supremum; for a group with no minimal normal subgroup (only possible for infinite groups)
this is the empty product `⊥`. -/
def socle (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | IsMinimalNormal N}

end Babai
