/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.1: The definition (configurations, coherent configurations, orbital
configurations).
-/
import Workspace.Prelim.BinaryRelations

/-!
# §3.1 Configurations and coherent configurations

A *partition structure* (Def. 3.1.1) is `X = (Ω; R₁,…,R_r)` where the nonempty `Rᵢ`
partition `Ω × Ω`.  The paper immediately identifies this with an edge coloring
`c : Ω × Ω → [r]`, and uses both notations interchangeably.  We take the coloring as
primitive: a `PartitionStructure Ω` carries its rank `r`, the coloring
`c : Ω → Ω → Fin r`, and the requirement that every color is used (this is exactly
"the sets `Rᵢ` are not empty").  The relations are recovered as `X.rel i = c⁻¹(i)`.

The right-action convention of `Workspace.Prelim.PermGroups` is used throughout: the
paper's `x^σ` is Lean's `σ x`.

## Numbering map

| Paper | Lean |
|---|---|
| Definition 3.1.1 | `Babai.PartitionStructure`, `.rank`, `.color`, `.rel`, `.nbr`, `.extConstituent`, `.effVertex`, `.constituent`, `.outDegC`, `.inDegC` |
| Definition 3.1.2 | `Babai.PartitionStructure.IsConfiguration` |
| Terminology 3.1.3 | `.IsDiagonalColor`, `.IsOffDiagonalColor`, `.diagonal_or_offDiagonal`, `.conv`, `.rel_conv`, `.IsUndirectedColor`, `.IsOrientedColor` |
| Definition 3.1.4 | `.vcolor`, `.vertexClass` |
| Definition 3.1.5 | `.IsStable` |
| Definition 3.1.6 | `.IsHomogeneous` |
| Example 3.1.7 | `.ofDigraph`, `.rank_ofDigraph` |
| Definition 3.1.8 | `.cliqueConfig`, `.cliqueConfig_unique` |
| Definition 3.1.9 | `.IsEquitablePartition`, `.IsEquitableColoring` |
| Observation 3.1.10 | `.isEquitableColoring_refines` |
| Definition 3.1.11 | `.IsCoherent`, `.interNum`, `.interNum_eq` |
| Observation 3.1.12 | `.orbitalConfig`, `.orbitalConfig_isCoherent` |
| Observation 3.1.13 | `.le_aut_orbitalConfig` |
| Remark 3.1.14 | not formalized (cited examples, used in no proof) |
| Observation 3.1.15 | `.vertexClass_orbitalConfig`, `.orbitalConfig_exists_rel_eq_diag_iff`, `.orbitalConfig_isHomogeneous_iff` |
-/

namespace Babai

variable {Ω : Type*}

/-! ### §3.1.1 Configurations -/

/-- Definition 3.1.1 (Partition structure).  "By a (binary) *partition structure* we mean
a binary relational structure `X = (Ω; R₁,…,R_r)` where the sets `Rᵢ ⊆ Ω × Ω` are not
empty and they partition `Ω × Ω`.  This is equivalent to coloring the edges of the
complete reflexive digraph, i.e., a function `c : Ω × Ω → [r]`; here `c(x,y) = i` exactly
if `(x,y) ∈ Rᵢ`. … We shall interchangeably use the notation `X = (Ω, c)` and
`X = (Ω; R₁,…,R_r)` for partition structures, each notation implying the other."

We take the coloring as the primitive datum.  The field `color_surjective` is the
paper's "the sets `Rᵢ` are not empty". -/
structure PartitionStructure (Ω : Type*) where
  /-- Definition 3.1.1.  "We call `r` the *rank* of `X`." -/
  rank : ℕ
  /-- Definition 3.1.1.  "`c : Ω × Ω → [r]`; … We refer to `c(x,y)` as the *color* of the
  'edge' `(x,y)`." -/
  color : Ω → Ω → Fin rank
  /-- Definition 3.1.1.  "the sets `Rᵢ ⊆ Ω × Ω` are not empty". -/
  color_surjective : ∀ i : Fin rank, ∃ x y : Ω, color x y = i

namespace PartitionStructure

variable (X : PartitionStructure Ω)

/-- Definition 3.1.1.  "`Rᵢ = c⁻¹(i)`."  "We shall refer to `Rᵢ` as a *constituent
relation* of `X`." -/
def rel (i : Fin X.rank) : Set (Ω × Ω) := {p | X.color p.1 p.2 = i}

@[simp] theorem mem_rel {i : Fin X.rank} {p : Ω × Ω} :
    p ∈ X.rel i ↔ X.color p.1 p.2 = i := Iff.rfl

theorem rel_nonempty (i : Fin X.rank) : (X.rel i).Nonempty := by
  obtain ⟨x, y, h⟩ := X.color_surjective i
  exact ⟨(x, y), h⟩

/-- Definition 3.1.1, Eq. (16): the constituent relations are pairwise disjoint. -/
theorem rel_disjoint {i j : Fin X.rank} (h : i ≠ j) : Disjoint (X.rel i) (X.rel j) := by
  rw [Set.disjoint_left]
  rintro p hp hq
  exact h (hp ▸ hq ▸ rfl)

/-- Definition 3.1.1, Eq. (16): `Ω × Ω = R₁ ∪ … ∪ R_r`. -/
theorem iUnion_rel : (⋃ i : Fin X.rank, X.rel i) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, mem_rel, Set.mem_univ, iff_true]
  exact ⟨X.color p.1 p.2, rfl⟩

/-- Notation 2.4.1 applied to a constituent relation: `Rᵢ(x)`, the set of out-neighbours
of `x` in color `i`. -/
def nbr (i : Fin X.rank) (x : Ω) : Set Ω := {y | X.color x y = i}

@[simp] theorem mem_nbr {i : Fin X.rank} {x y : Ω} :
    y ∈ X.nbr i x ↔ X.color x y = i := Iff.rfl

theorem nbr_eq_outNbr (i : Fin X.rank) (x : Ω) : X.nbr i x = outNbr (X.rel i) x := rfl

/-- Definition 3.1.1.  "The *extended color-`i` constituent* is `(Ω, Rᵢ)` (we do not
ignore the isolated vertices)." -/
def extConstituent (i : Fin X.rank) : Digraph Ω := ⟨X.rel i⟩

@[simp] theorem extConstituent_E (i : Fin X.rank) : (X.extConstituent i).E = X.rel i := rfl

/-- Definition 3.1.1.  "`Ω(i)` denotes the set of non-isolated vertices of the digraph
`(Ω, Rᵢ)`." -/
def effVertex (i : Fin X.rank) : Set Ω := {x | ¬ (X.extConstituent i).IsIsolated x}

/-- Definition 3.1.1.  "We call the digraph `Xᵢ = (Ω(i), Rᵢ)` the *color-`i` constituent
digraph* of `X`." -/
def constituent (i : Fin X.rank) : Digraph (X.effVertex i) :=
  (X.extConstituent i).induced (X.effVertex i)

/-- Definition 3.1.1.  "For `x ∈ Ω` we write `deg⁺ᵢ(x)` to denote the out-degree of `x` in
the extended constituent `(Ω, Rᵢ)`." -/
noncomputable def outDegC (i : Fin X.rank) (x : Ω) : ℕ := (X.extConstituent i).outDeg x

/-- Definition 3.1.1.  "We define `deg⁻(x)` analogously." -/
noncomputable def inDegC (i : Fin X.rank) (x : Ω) : ℕ := (X.extConstituent i).inDeg x

theorem outDegC_eq_ncard (i : Fin X.rank) (x : Ω) : X.outDegC i x = (X.nbr i x).ncard :=
  rfl

theorem inDegC_eq_ncard (i : Fin X.rank) (y : Ω) :
    X.inDegC i y = {x : Ω | X.color x y = i}.ncard := rfl

/-- Definition 3.1.1.  The corresponding binary relational structure (Def. 2.3.1):
`X = (Ω; R₁,…,R_r)`. -/
def toRelStructure : RelStructure Ω where
  numRel := X.rank
  arity _ := 2
  rel i := {x : Fin 2 → Ω | X.color (x 0) (x 1) = i}

/-- Definition 2.3.4 for a partition structure: the automorphism group consists of the
permutations preserving every constituent relation, i.e. preserving the coloring. -/
def Aut : Subgroup (Equiv.Perm Ω) where
  carrier := {σ | ∀ x y : Ω, X.color (σ x) (σ y) = X.color x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro a b ha hb x y
    simpa [Equiv.Perm.mul_apply] using (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have := ha (a⁻¹ x) (a⁻¹ y)
    simpa using this.symm

@[simp] theorem mem_aut {X : PartitionStructure Ω} {σ : Equiv.Perm Ω} :
    σ ∈ X.Aut ↔ ∀ x y : Ω, X.color (σ x) (σ y) = X.color x y := Iff.rfl

end PartitionStructure

instance : IsStructure (PartitionStructure Ω) Ω := ⟨PartitionStructure.Aut⟩

namespace PartitionStructure

variable (X : PartitionStructure Ω)

/-- Definition 3.1.2 (Configuration).  "We say that the partition structure
`X = (Ω, c) = (Ω; R₁,…,R_r)` is a (binary) *configuration* if
(i) `(∀x,y,z ∈ Ω)(c(x,y) = c(z,z) ⟹ x = y)`;
(ii) `(∀u,v,x,y ∈ Ω)(c(u,v) = c(x,y) ⟹ c(v,u) = c(y,x))`. -/
structure IsConfiguration : Prop where
  /-- Axiom (i). -/
  diag : ∀ x y z : Ω, X.color x y = X.color z z → x = y
  /-- Axiom (ii). -/
  converse : ∀ u v x y : Ω, X.color u v = X.color x y → X.color v u = X.color y x

/-- The rank is at most `|Ω|²`: the coloring of `Ω × Ω` is onto `[r]` (Def. 3.1.1). -/
theorem rank_le_card_sq [Fintype Ω] : X.rank ≤ Fintype.card Ω * Fintype.card Ω := by
  have hsurj : Function.Surjective (fun p : Ω × Ω => X.color p.1 p.2) := by
    intro i
    obtain ⟨x, y, h⟩ := X.color_surjective i
    exact ⟨(x, y), h⟩
  have h := Fintype.card_le_of_surjective _ hsurj
  simpa [Fintype.card_prod] using h

/-- Definition 3.1.1.  "if `|Ω| ≥ 2` then `r ≥ 2`."  (This uses axiom (i) of Def. 3.1.2:
in a partition structure that is not a configuration the coloring may be constant.) -/
theorem two_le_rank [Nontrivial Ω] (h : X.IsConfiguration) : 2 ≤ X.rank := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  have hne : X.color x y ≠ X.color x x := fun hc => hxy (h.diag x y x hc)
  have : Nontrivial (Fin X.rank) := ⟨⟨X.color x y, X.color x x, hne⟩⟩
  have h1 := Fintype.one_lt_card (α := Fin X.rank)
  simpa using h1

/-- Terminology 3.1.3.  "Axiom (i) says that `(∀i)(either Rᵢ ⊆ diag(Ω) or
Rᵢ ∩ diag(Ω) = ∅)`.  In the former case we say that `i` is a *diagonal color* and `Xᵢ` is
a *diagonal constituent*." -/
def IsDiagonalColor (i : Fin X.rank) : Prop := X.rel i ⊆ diag Ω

/-- Terminology 3.1.3.  "…in the latter case we speak of an *off-diagonal* color and
constituent." -/
def IsOffDiagonalColor (i : Fin X.rank) : Prop := X.rel i ∩ diag Ω = ∅

/-- Terminology 3.1.3.  "Axiom (i) says that `(∀i)(either Rᵢ ⊆ diag(Ω) or
Rᵢ ∩ diag(Ω) = ∅)`." -/
theorem diagonal_or_offDiagonal (h : X.IsConfiguration) (i : Fin X.rank) :
    X.IsDiagonalColor i ∨ X.IsOffDiagonalColor i := by
  by_cases hd : ∃ z : Ω, X.color z z = i
  · obtain ⟨z, hz⟩ := hd
    left
    rintro ⟨x, y⟩ hxy
    exact h.diag x y z (by rw [show X.color x y = i from hxy, hz])
  · right
    push_neg at hd
    ext p
    simp only [Set.mem_inter_iff, mem_rel, mem_diag, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro hp hdg
    exact hd p.1 (by rw [← hp]; exact congrArg (X.color p.1) hdg)

theorem isDiagonalColor_vcolor_aux (x : Ω) (h : X.IsConfiguration) :
    X.IsDiagonalColor (X.color x x) := by
  rcases X.diagonal_or_offDiagonal h (X.color x x) with hd | ho
  · exact hd
  · exact absurd (Set.eq_empty_iff_forall_notMem.1 ho (x, x) ⟨rfl, rfl⟩) not_false

open Classical in
/-- Terminology 3.1.3.  "Axiom (ii) says that `c(x,y)` determines `c(y,x)`, i.e.
`(∀i)(∃j)(R_j = Rᵢ⁻)`.  We write `j = i⁻` if `R_j = Rᵢ⁻`."

Outside configurations there need be no such `j`; we then return `i` itself, so that
`conv` is a total function and `rel_conv` is its defining property. -/
noncomputable def conv (i : Fin X.rank) : Fin X.rank :=
  if h : ∃ j, X.rel j = invRel (X.rel i) then h.choose else i

/-- Terminology 3.1.3.  `R_{i⁻} = Rᵢ⁻`. -/
theorem rel_conv (h : X.IsConfiguration) (i : Fin X.rank) :
    X.rel (X.conv i) = invRel (X.rel i) := by
  classical
  have hex : ∃ j, X.rel j = invRel (X.rel i) := by
    obtain ⟨x, y, hxy⟩ := X.color_surjective i
    refine ⟨X.color y x, ?_⟩
    ext p
    simp only [mem_rel, mem_invRel]
    constructor
    · intro hp
      have := h.converse p.1 p.2 y x (by rw [show X.color p.1 p.2 = X.color y x from hp])
      rw [this, hxy]
    · intro hp
      have := h.converse p.2 p.1 x y (by rw [show X.color p.2 p.1 = i from hp, hxy])
      rw [this]
  rw [conv, dif_pos hex]
  exact hex.choose_spec

/-- Terminology 3.1.3.  `c(y,x) = c(x,y)⁻`. -/
theorem color_comm (h : X.IsConfiguration) (x y : Ω) :
    X.color y x = X.conv (X.color x y) := by
  have hr := X.rel_conv h (X.color x y)
  have hmem : (y, x) ∈ invRel (X.rel (X.color x y)) := by
    simp only [mem_invRel, mem_rel]
  rw [← hr] at hmem
  exact hmem

/-- Terminology 3.1.3.  "If `i` is an off-diagonal color and `i⁻ = i` (i.e.
`R_{i⁻} = Rᵢ`) then we say that the color `i` and the constituent `Xᵢ` are
*undirected*." -/
def IsUndirectedColor (i : Fin X.rank) : Prop :=
  X.IsOffDiagonalColor i ∧ X.conv i = i

/-- Terminology 3.1.3.  "…otherwise (in this case `Rᵢ ∩ R_{i⁻} = ∅`), we say that `i` and
`Xᵢ` are *oriented*." -/
def IsOrientedColor (i : Fin X.rank) : Prop :=
  X.IsOffDiagonalColor i ∧ X.conv i ≠ i

/-- Definition 3.1.4 (Vertex colors).  "We view the diagonal colors as a coloring of the
vertices, setting `c(x) := c(x,x)`." -/
def vcolor (x : Ω) : Fin X.rank := X.color x x

/-- Definition 3.1.4.  "We write `Ωᵢ = {x ∈ Ω | c(x) = i}`." -/
def vertexClass (i : Fin X.rank) : Set Ω := {x | X.vcolor x = i}

@[simp] theorem mem_vertexClass {X : PartitionStructure Ω} {i : Fin X.rank} {x : Ω} :
    x ∈ X.vertexClass i ↔ X.color x x = i := Iff.rfl

instance decidablePredVertexClass (i : Fin X.rank) :
    DecidablePred (· ∈ X.vertexClass i) := fun x => decidable_of_iff (X.vcolor x = i) Iff.rfl

/-- Definition 3.1.4.  "we have the partition `Ω = ⋃ᵢ Ωᵢ` into the vertex-color
classes `Ωᵢ`." -/
theorem iUnion_vertexClass : (⋃ i : Fin X.rank, X.vertexClass i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, mem_vertexClass, Set.mem_univ, iff_true]
  exact ⟨X.color x x, rfl⟩

/-- Definition 3.1.5 (Stable set).  "A subset `Δ ⊆ Ω` is *stable* if it is the union of
some vertex-color classes." -/
def IsStable (Δ : Set Ω) : Prop := ∃ S : Set (Fin X.rank), Δ = {x | X.vcolor x ∈ S}

/-- Definition 3.1.5, restated: a set is stable exactly if it is closed under replacing a
vertex by another of the same color. -/
theorem isStable_iff (Δ : Set Ω) :
    X.IsStable Δ ↔ ∀ x ∈ Δ, ∀ y, X.vcolor y = X.vcolor x → y ∈ Δ := by
  constructor
  · rintro ⟨S, rfl⟩ x hx y hy
    simpa [hy] using hx
  · intro h
    refine ⟨X.vcolor '' Δ, ?_⟩
    ext x
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact h y hy x hxy.symm

/-- Every vertex-color class is stable. -/
theorem isStable_vertexClass (i : Fin X.rank) : X.IsStable (X.vertexClass i) :=
  ⟨{i}, rfl⟩

/-- Definition 3.1.6 (Homogeneous configuration).  "The configuration `X = (Ω, c)` is
*homogeneous* if all vertices have the same color, i.e. `R₁ = diag(Ω)`." -/
def IsHomogeneous : Prop := ∀ x y : Ω, X.vcolor x = X.vcolor y

/-- Definition 3.1.9 (Equitable partition).  "Let `X = (Ω; R₁,…,R_r)` be a configuration
and `Π = {Δ₁,…,Δ_k}` a partition of `Ω`.  We say that `Π` is an *equitable partition*
of `X` if `Π` is equitable for each of the extended constituents `(Ω, Rᵢ)`." -/
def IsEquitablePartition (P : Set (Set Ω)) : Prop :=
  ∀ i : Fin X.rank, (X.extConstituent i).IsEquitablePartition P

/-- Definition 3.1.9 (Equitable coloring).  "We say that the coloring `d : Ω → C` is
*equitable* if the partition `ker(d)` is equitable." -/
def IsEquitableColoring {C : Type*} (d : Ω → C) : Prop :=
  ∀ i : Fin X.rank, (X.extConstituent i).IsEquitableColoring d

/-- Observation 3.1.10.  "An equitable coloring `d` of the configuration `X = (Ω, c)` is a
refinement of the coloring of `X`, i.e. `(∀x,y ∈ Ω)(d(x) = d(y) ⟹ c(x) = c(y))`."

Paper's proof: "Let `c(x) = i` and `d(x) = d(y) = h`.  Let `D = d⁻¹(h)`; so `x, y ∈ D`.
Consider the induced subgraph `Y = Rᵢ[D]`.  We have `deg⁺_Y(x) = 1` so by equitability
`deg⁺_Y(y) = 1`, meaning that `c(y) = i`." -/
theorem isEquitableColoring_refines {C : Type*} {d : Ω → C}
    (hcfg : X.IsConfiguration) (hd : X.IsEquitableColoring d) (x y : Ω)
    (hxy : d x = d y) : X.vcolor x = X.vcolor y := by
  classical
  have hxD : x ∈ d ⁻¹' {d x} := rfl
  have hyD : y ∈ d ⁻¹' {d x} := hxy.symm
  -- the induced subgraph of the extended constituent `(Ω, Rᵢ)` on `D = d⁻¹(d x)`
  obtain ⟨e, he⟩ := ((hd (X.vcolor x)).1 (d x)).1
  -- `deg⁺(x) = 1` in `Rᵢ[D]`, because the only out-neighbour of `x` is `x` itself
  have hx1 : ((X.extConstituent (X.vcolor x)).induced (d ⁻¹' {d x})).outDeg
      ⟨x, hxD⟩ = 1 := by
    have hset : outNbr ((X.extConstituent (X.vcolor x)).induced
        (d ⁻¹' {d x})).E ⟨x, hxD⟩ = {⟨x, hxD⟩} := by
      ext ⟨z, hz⟩
      simp only [mem_outNbr, Digraph.induced, Set.mem_setOf_eq, extConstituent_E, mem_rel,
        Set.mem_singleton_iff, Subtype.mk.injEq]
      exact ⟨fun h => (hcfg.diag x z x h).symm, fun h => by rw [← h]; rfl⟩
    rw [Digraph.outDeg, hset, Set.ncard_singleton]
  have hy1 : ((X.extConstituent (X.vcolor x)).induced (d ⁻¹' {d x})).outDeg
      ⟨y, hyD⟩ = 1 := by
    rw [he ⟨y, hyD⟩, ← he ⟨x, hxD⟩, hx1]
  -- hence `y` has an out-neighbour in color `i` inside `D`, forcing `c(y) = i`
  have hne : outNbr ((X.extConstituent (X.vcolor x)).induced
      (d ⁻¹' {d x})).E ⟨y, hyD⟩ ≠ ∅ := by
    intro hempty
    rw [Digraph.outDeg, hempty, Set.ncard_empty] at hy1
    exact one_ne_zero hy1.symm
  obtain ⟨⟨z, hz⟩, hzmem⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hcz : X.color y z = X.vcolor x := hzmem
  have hyz : y = z := hcfg.diag y z x hcz
  calc X.vcolor x = X.color y z := hcz.symm
    _ = X.color y y := by rw [← hyz]
    _ = X.vcolor y := rfl

/-! ### §3.1.2 Coherent configurations, intersection numbers -/

/-- Definition 3.1.11.  "A (classical) *coherent configuration of rank `r`* is a binary
configuration `X = (Ω, c)` of rank `r` satisfying the following additional axiom.
(iii) There exists a family of `r³` nonnegative integers `p^k_{ij}` (`1 ≤ i,j,k ≤ r`)
such that `(∀i,j,k ≤ r)(∀x,y ∈ Ω)(c(x,y) = k ⟹ |{z | c(x,z) = i and c(z,y) = j}| =
p^k_{ij})`.  The `p^k_{ij}` are called the *intersection numbers* of `X`." -/
structure IsCoherent : Prop extends X.IsConfiguration where
  /-- Axiom (iii), Eq. (17). -/
  intersection : ∃ p : Fin X.rank → Fin X.rank → Fin X.rank → ℕ,
    ∀ (i j k : Fin X.rank) (x y : Ω), X.color x y = k →
      {z : Ω | X.color x z = i ∧ X.color z y = j}.ncard = p i j k

/-- A pair of vertices realizing the color `k`; it exists by Def. 3.1.1. -/
noncomputable def colorWitness (k : Fin X.rank) : Ω × Ω :=
  ((X.color_surjective k).choose, (X.color_surjective k).choose_spec.choose)

theorem color_colorWitness (k : Fin X.rank) :
    X.color (X.colorWitness k).1 (X.colorWitness k).2 = k :=
  (X.color_surjective k).choose_spec.choose_spec

/-- Definition 3.1.11.  The intersection number `p^k_{ij}` of a coherent configuration. -/
noncomputable def interNum (i j k : Fin X.rank) : ℕ :=
  {z : Ω | X.color (X.colorWitness k).1 z = i ∧
      X.color z (X.colorWitness k).2 = j}.ncard

/-- Definition 3.1.11, Eq. (17): the defining property of the intersection numbers. -/
theorem interNum_eq (h : X.IsCoherent) (i j k : Fin X.rank) {x y : Ω}
    (hxy : X.color x y = k) :
    {z : Ω | X.color x z = i ∧ X.color z y = j}.ncard = X.interNum i j k := by
  obtain ⟨p, hp⟩ := h.intersection
  rw [hp i j k x y hxy, interNum, hp i j k _ _ (X.color_colorWitness k)]

/-- Def. 3.1.2 and Def. 3.1.11 depend on the coloring only through its kernel: two
colorings of `Ω × Ω` with the same color classes define the same configuration and the
same coherent configuration.  (This is the paper's silent convention that the names of the
colors do not matter; Def. 3.1.1 numbers them by `[r]`.  It is the classical counterpart
of `Babai.KAryPartStruct.isCoherent_congr`.) -/
theorem isConfiguration_congr {X X' : PartitionStructure Ω}
    (hker : ∀ x y u v : Ω, X.color x y = X.color u v ↔ X'.color x y = X'.color u v)
    (h : X.IsConfiguration) : X'.IsConfiguration where
  diag x y z hxyz := h.diag x y z ((hker x y z z).2 hxyz)
  converse u v x y huv := (hker v u y x).1 (h.converse u v x y ((hker u v x y).2 huv))

theorem isCoherent_congr [Fintype Ω] {X X' : PartitionStructure Ω}
    (hker : ∀ x y u v : Ω, X.color x y = X.color u v ↔ X'.color x y = X'.color u v)
    (h : X.IsCoherent) : X'.IsCoherent := by
  classical
  refine ⟨isConfiguration_congr hker h.toIsConfiguration, ?_⟩
  obtain ⟨p, hp⟩ := h.intersection
  -- read each color of `X'` off a pair realizing it, and count in `X`
  refine ⟨fun i j k =>
    p (X.color (X'.colorWitness i).1 (X'.colorWitness i).2)
      (X.color (X'.colorWitness j).1 (X'.colorWitness j).2)
      (X.color (X'.colorWitness k).1 (X'.colorWitness k).2), ?_⟩
  intro i j k x y hxy
  have hset : {z : Ω | X'.color x z = i ∧ X'.color z y = j}
      = {z : Ω | X.color x z = X.color (X'.colorWitness i).1 (X'.colorWitness i).2 ∧
          X.color z y = X.color (X'.colorWitness j).1 (X'.colorWitness j).2} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hker _ _ _ _).2 (by rw [h1, X'.color_colorWitness i]),
        (hker _ _ _ _).2 (by rw [h2, X'.color_colorWitness j])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← X'.color_colorWitness i]; exact (hker _ _ _ _).1 h1,
        by rw [← X'.color_colorWitness j]; exact (hker _ _ _ _).1 h2⟩
  have hxy' : X.color x y
      = X.color (X'.colorWitness k).1 (X'.colorWitness k).2 :=
    (hker _ _ _ _).2 (by rw [hxy, X'.color_colorWitness k])
  rw [hset, hp _ _ _ x y hxy']

/-! ### Re-coloring: dropping the unused colors

Definition 3.1.1 demands that every constituent relation be nonempty.  Constructions
that start from a coloring by an arbitrary label set therefore have to drop the labels
that are not used; the paper does this silently ("empty relations are omitted",
Example 3.1.7).  `ofColoring` performs this renumbering, and
`ofColoring_color_eq_iff` says that it changes nothing but the names of the colors. -/

section OfColoring

variable {C : Type*} [Fintype Ω] [DecidableEq C]

/-- The partition structure whose colors are the *realized* values of an arbitrary edge
coloring `d : Ω → Ω → C`, renumbered by `[r]` where `r` is the number of realized
values. -/
noncomputable def ofColoring (d : Ω → Ω → C) : PartitionStructure Ω where
  rank := (Finset.univ.image fun p : Ω × Ω => d p.1 p.2).card
  color x y := (Finset.univ.image fun p : Ω × Ω => d p.1 p.2).equivFin
    ⟨d x y, Finset.mem_image.2 ⟨(x, y), Finset.mem_univ _, rfl⟩⟩
  color_surjective i := by
    obtain ⟨⟨c, hc⟩, h⟩ :=
      (Finset.univ.image fun p : Ω × Ω => d p.1 p.2).equivFin.surjective i
    obtain ⟨⟨x, y⟩, -, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨x, y, h⟩

/-- `ofColoring d` has exactly the color classes of `d`. -/
theorem ofColoring_color_eq_iff (d : Ω → Ω → C) (x y u v : Ω) :
    (ofColoring d).color x y = (ofColoring d).color u v ↔ d x y = d u v := by
  constructor
  · intro h
    exact congrArg Subtype.val
      ((Finset.univ.image fun p : Ω × Ω => d p.1 p.2).equivFin.injective h)
  · intro h
    exact congrArg _ (Subtype.ext h)

/-- Definition 2.3.7 (Induced substructure) for configurations: `X[Δ]`.  The colors of
`X[Δ]` are the colors of `X` that occur on `Δ × Δ`. -/
noncomputable def induced (Δ : Set Ω) [Fintype Δ] : PartitionStructure Δ :=
  ofColoring (fun x y : Δ => X.color x y)

theorem induced_color_eq_iff (Δ : Set Ω) [Fintype Δ] (x y u v : Δ) :
    (X.induced Δ).color x y = (X.induced Δ).color u v ↔
      X.color (x : Ω) (y : Ω) = X.color (u : Ω) (v : Ω) :=
  ofColoring_color_eq_iff _ x y u v

/-- An induced substructure of a configuration is a configuration. -/
theorem induced_isConfiguration (Δ : Set Ω) [Fintype Δ] (h : X.IsConfiguration) :
    (X.induced Δ).IsConfiguration where
  diag x y z hxyz := by
    rw [X.induced_color_eq_iff] at hxyz
    exact Subtype.ext (h.diag (x : Ω) (y : Ω) (z : Ω) hxyz)
  converse u v x y huv := by
    rw [X.induced_color_eq_iff] at huv ⊢
    exact h.converse (u : Ω) (v : Ω) (x : Ω) (y : Ω) huv

end OfColoring

/-! ### Example 3.1.7 and Definition 3.1.8 -/

section Examples

variable [Fintype Ω] [DecidableEq Ω]

open Classical in
/-- Example 3.1.7. The partition structure with diagonal, edge and nonedge colors.
For an undirected graph this is a homogeneous configuration, as proved in
`ofDigraph_isConfiguration` and `ofDigraph_isHomogeneous`. The printed claim for
all irreflexive digraphs fails: see `oneArc_not_configuration` and the entry for
Example 3.1.7 in the corrected paper. -/
noncomputable def ofDigraph (Y : Digraph Ω) : PartitionStructure Ω :=
  ofColoring (C := Fin 3) fun x y =>
    if x = y then 0 else if (x, y) ∈ Y.E then 1 else 2

/-- Example 3.1.7, the configuration claim for undirected graphs. -/
theorem ofDigraph_isConfiguration (Y : Digraph Ω) (hY : Y.IsGraph) :
    (ofDigraph Y).IsConfiguration := by
  classical
  have hsymm : ∀ x y : Ω, (x, y) ∈ Y.E ↔ (y, x) ∈ Y.E := by
    intro x y
    change (x, y) ∈ Y.E ↔ (x, y) ∈ invRel Y.E
    rw [← hY.symm]
  have hcomm : ∀ x y : Ω, (ofDigraph Y).color x y = (ofDigraph Y).color y x := by
    intro x y
    apply (ofColoring_color_eq_iff _ _ _ _ _).2
    simp only [eq_comm (a := x) (b := y), hsymm x y]
  constructor
  · intro x y z h
    have h' := (ofColoring_color_eq_iff _ _ _ _ _).1 h
    by_contra hne
    by_cases he : (x, y) ∈ Y.E <;> simp [hne, he] at h'
  · intro u v x y h
    exact (hcomm v u).trans (h.trans (hcomm x y))

/-- Example 3.1.7. All vertices have the diagonal color. -/
theorem ofDigraph_isHomogeneous (Y : Digraph Ω) : (ofDigraph Y).IsHomogeneous := by
  classical
  intro x y
  apply (ofColoring_color_eq_iff _ _ _ _ _).2
  simp

/-- The one-arc digraph that refutes the general claim in Example 3.1.7. -/
def oneArc : Digraph (Fin 3) := ⟨{(0, 1)}⟩

/-- The counterexample in Example 3.1.7 has no loops. -/
theorem oneArc_irreflexive : oneArc.IsIrreflexive := by
  ext p
  simp only [oneArc, Set.mem_inter_iff, Set.mem_singleton_iff,
    mem_diag, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  decide

/-- Example 3.1.7 fails for digraphs: `(1,0)` and `(1,2)` have the same color,
but their reverses have different colors. -/
theorem oneArc_not_configuration : ¬ (ofDigraph oneArc).IsConfiguration := by
  intro h
  have hcol : (ofDigraph oneArc).color 1 0 = (ofDigraph oneArc).color 1 2 := by
    apply (ofColoring_color_eq_iff _ _ _ _ _).2
    simp [oneArc]
  have hrev := h.converse 1 0 1 2 hcol
  have bad := (ofColoring_color_eq_iff _ _ _ _ _).1 hrev
  simp [oneArc, show (2 : Fin 3) ≠ 1 by decide,
    show (2 : Fin 3) ≠ 0 by decide] at bad

/-- Example 3.1.7.  "The configuration `X(X)` has rank 3 unless `X` is trivial (empty or
complete) (empty relations are omitted), in which case it has rank 2."
This rank statement needs at least two vertices. The rank is one on a singleton
and zero on an empty domain. -/
theorem rank_ofDigraph (Y : Digraph Ω) (hirr : Y.IsIrreflexive) [Nontrivial Ω] :
    (ofDigraph Y).rank = if Y.E = ∅ ∨ Y.E = Set.univ \ diag Ω then 2 else 3 := by
  classical
  obtain ⟨x₀, y₀, hx₀y₀⟩ := exists_pair_ne Ω
  have hrank : (ofDigraph Y).rank
      = (Finset.univ.image fun p : Ω × Ω =>
          if p.1 = p.2 then (0 : Fin 3) else if (p.1, p.2) ∈ Y.E then 1 else 2).card := rfl
  set D := Finset.univ.image fun p : Ω × Ω =>
    if p.1 = p.2 then (0 : Fin 3) else if (p.1, p.2) ∈ Y.E then 1 else 2 with hD
  have hsub : Y.E ⊆ Set.univ \ diag Ω := by
    rintro ⟨u, v⟩ hp
    refine ⟨trivial, fun hdiag => ?_⟩
    exact absurd (Set.eq_empty_iff_forall_notMem.1 hirr (u, v) ⟨hp, hdiag⟩) not_false
  have hcases : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  have h0 : (0 : Fin 3) ∈ D :=
    Finset.mem_image.2 ⟨(x₀, x₀), Finset.mem_univ _, by simp⟩
  have h1 : (1 : Fin 3) ∈ D ↔ Y.E.Nonempty := by
    constructor
    · intro hc
      obtain ⟨⟨u, v⟩, -, huv⟩ := Finset.mem_image.1 hc
      by_cases he : u = v
      · simp [he] at huv
      · by_cases hE : (u, v) ∈ Y.E
        · exact ⟨(u, v), hE⟩
        · simp [he, hE] at huv
    · rintro ⟨⟨u, v⟩, huv⟩
      have hne : u ≠ v := by
        intro he
        exact absurd (Set.eq_empty_iff_forall_notMem.1 hirr (u, v) ⟨huv, he⟩) not_false
      exact Finset.mem_image.2 ⟨(u, v), Finset.mem_univ _, by simp [hne, huv]⟩
  have h2 : (2 : Fin 3) ∈ D ↔ Y.E ≠ Set.univ \ diag Ω := by
    constructor
    · intro hc heq
      obtain ⟨⟨u, v⟩, -, huv⟩ := Finset.mem_image.1 hc
      by_cases he : u = v
      · simp [he] at huv
      · by_cases hE : (u, v) ∈ Y.E
        · simp [he, hE] at huv
        · exact hE (heq ▸ ⟨trivial, he⟩)
    · intro hne
      have : ∃ p ∈ Set.univ \ diag Ω, p ∉ Y.E := by
        by_contra hcon
        push_neg at hcon
        exact hne (Set.Subset.antisymm hsub hcon)
      obtain ⟨⟨u, v⟩, ⟨-, hd⟩, hE⟩ := this
      have hne' : u ≠ v := hd
      exact Finset.mem_image.2 ⟨(u, v), Finset.mem_univ _, by simp [hne', hE]⟩
  by_cases hE : Y.E = ∅ ∨ Y.E = Set.univ \ diag Ω
  · rw [if_pos hE, hrank]
    rcases hE with hE | hE
    · -- the empty digraph: the colors are the diagonal and the non-diagonal
      have h1not : (1 : Fin 3) ∉ D := fun hc => by
        obtain ⟨p, hp⟩ := h1.1 hc
        rw [hE] at hp
        exact hp
      have h2mem : (2 : Fin 3) ∈ D := h2.2 (by
        rw [hE]
        intro hcon
        exact absurd (Set.eq_empty_iff_forall_notMem.1 hcon.symm (x₀, y₀) ⟨trivial, hx₀y₀⟩)
          not_false)
      have hDeq : D = {0, 2} := by
        ext c
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hc
          rcases hcases c with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact absurd hc h1not
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact h0
          · exact h2mem
      rw [hDeq]; decide
    · -- the complete irreflexive digraph
      have h2not : (2 : Fin 3) ∉ D := fun hc => (h2.1 hc) hE
      have h1mem : (1 : Fin 3) ∈ D := h1.2 ⟨(x₀, y₀), by rw [hE]; exact ⟨trivial, hx₀y₀⟩⟩
      have hDeq : D = {0, 1} := by
        ext c
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hc
          rcases hcases c with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exact absurd hc h2not
        · rintro (rfl | rfl)
          · exact h0
          · exact h1mem
      rw [hDeq]; decide
  · rw [if_neg hE, hrank]
    push_neg at hE
    have h1mem : (1 : Fin 3) ∈ D := h1.2 hE.1
    have h2mem : (2 : Fin 3) ∈ D := h2.2 hE.2
    have hDeq : D = {0, 1, 2} := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hc
        exact hcases c
      · rintro (rfl | rfl | rfl)
        · exact h0
        · exact h1mem
        · exact h2mem
    rw [hDeq]; decide

/-- In a configuration of rank 2 the color of a pair depends only on whether the two
vertices are equal: all diagonal pairs have one color, all off-diagonal pairs the other.
(This is the content of Def. 3.1.8, "the unique rank-2 configuration".) -/
theorem color_diag_eq_of_rank_two (h : X.IsConfiguration) (hr : X.rank = 2) (x u : Ω) :
    X.color x x = X.color u u := by
  by_contra hne
  -- `c(x,x) ≠ c(u,u)` would exhaust the two colors, leaving none for an off-diagonal pair
  by_cases hxu : x = u
  · exact hne (by rw [hxu])
  have h1 : (X.color x x : ℕ) < 2 := by rw [← hr]; exact (X.color x x).isLt
  have h2 : (X.color u u : ℕ) < 2 := by rw [← hr]; exact (X.color u u).isLt
  have h3 : (X.color x u : ℕ) < 2 := by rw [← hr]; exact (X.color x u).isLt
  have h4 : X.color x u ≠ X.color x x := fun hc => hxu (h.diag x u x hc)
  have h5 : X.color x u ≠ X.color u u := fun hc => hxu (h.diag x u u hc)
  have e1 : (X.color x x : ℕ) ≠ (X.color u u : ℕ) := fun hc => hne (Fin.ext hc)
  have e4 : (X.color x u : ℕ) ≠ (X.color x x : ℕ) := fun hc => h4 (Fin.ext hc)
  have e5 : (X.color x u : ℕ) ≠ (X.color u u : ℕ) := fun hc => h5 (Fin.ext hc)
  omega

/-- In a configuration of rank 2, any two off-diagonal pairs have the same color. -/
theorem color_eq_of_rank_two (h : X.IsConfiguration) (hr : X.rank = 2) {x y u v : Ω}
    (hxy : x ≠ y) (huv : u ≠ v) : X.color x y = X.color u v := by
  have hdiag : X.color x x = X.color u u := X.color_diag_eq_of_rank_two h hr x u
  have h1 : (X.color x y : ℕ) < 2 := by rw [← hr]; exact (X.color x y).isLt
  have h2 : (X.color u v : ℕ) < 2 := by rw [← hr]; exact (X.color u v).isLt
  have h3 : (X.color x x : ℕ) < 2 := by rw [← hr]; exact (X.color x x).isLt
  have e1 : (X.color x y : ℕ) ≠ (X.color x x : ℕ) := fun hc =>
    hxy (h.diag x y x (Fin.ext hc))
  have e2 : (X.color u v : ℕ) ≠ (X.color x x : ℕ) := fun hc =>
    huv (h.diag u v u ((Fin.ext hc).trans hdiag))
  exact Fin.ext (by omega)

/-- Definition 3.1.8 (Clique configuration).  "The *clique configuration* on `Ω`
(`|Ω| ≥ 2`) is the unique rank-2 configuration on `Ω` (corresponding to the clique
graph)." -/
def cliqueConfig (Ω : Type*) [DecidableEq Ω] [Nontrivial Ω] : PartitionStructure Ω where
  rank := 2
  color x y := if x = y then 0 else 1
  color_surjective i := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
    fin_cases i
    · exact ⟨x, x, by simp⟩
    · exact ⟨x, y, by simp [hxy]⟩

theorem cliqueConfig_isConfiguration [Nontrivial Ω] :
    (cliqueConfig Ω).IsConfiguration where
  diag x y z h := by
    by_cases hxy : x = y
    · exact hxy
    · simp [cliqueConfig, hxy] at h
  converse u v x y h := by
    by_cases huv : u = v <;> by_cases hxy : x = y <;>
      simp_all [cliqueConfig, Ne.symm, eq_comm]

/-- Definition 3.1.8.  Uniqueness: every rank-2 configuration on `Ω` is the clique
configuration, up to renaming the two colors. -/
theorem cliqueConfig_unique [Nontrivial Ω] (h : X.IsConfiguration) (hr : X.rank = 2) :
    ∃ e : Fin 2 ≃ Fin X.rank,
      ∀ x y : Ω, X.color x y = e ((cliqueConfig Ω).color x y) := by
  classical
  obtain ⟨x₀, y₀, hx₀y₀⟩ := exists_pair_ne Ω
  -- the two colors: `a` on the diagonal, `b` off it
  set a := X.color x₀ x₀ with ha
  set b := X.color x₀ y₀ with hb
  have hab : a ≠ b := fun hc => hx₀y₀ (h.diag x₀ y₀ x₀ hc.symm)
  have hinj : Function.Injective (![a, b]) := by
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp_all
  have hbij : Function.Bijective (![a, b]) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [hr]⟩
  refine ⟨Equiv.ofBijective _ hbij, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    show X.color x x = ![a, b] ((cliqueConfig Ω).color x x)
    have h0 : (cliqueConfig Ω).color x x = (0 : Fin 2) := by simp [cliqueConfig]
    rw [h0, Matrix.cons_val_zero]
    exact X.color_diag_eq_of_rank_two h hr x x₀
  · show X.color x y = ![a, b] ((cliqueConfig Ω).color x y)
    have h1 : ![a, b] ((cliqueConfig Ω).color x y) = b := by simp [cliqueConfig, hxy]
    rw [h1]
    exact X.color_eq_of_rank_two h hr hxy hx₀y₀

end Examples

/-! ### §3.1.3 Orbitals, Schurian coherent configurations -/

section Orbital

variable [Fintype Ω] [DecidableEq Ω]

/-- §3.1.3.  "Let `G ≤ S(Ω)` be a permutation group.  An *orbital* of `G` is an orbit of
the `G`-action on `Ω × Ω`." -/
def IsOrbital (G : Subgroup (Equiv.Perm Ω)) (R : Set (Ω × Ω)) : Prop :=
  ∃ p : Ω × Ω, R = MulAction.orbit G p

open Classical in
/-- Observation 3.1.12 (Orbital configuration).  "Let `R₁,…,R_r` denote the orbitals
of `G`.  Then `X(G) := (Ω; R₁,…,R_r)` is a coherent configuration."  This is the
structure `X(G)`; coherence is `orbitalConfig_isCoherent`. -/
noncomputable def orbitalConfig (G : Subgroup (Equiv.Perm Ω)) : PartitionStructure Ω :=
  ofColoring (C := Quotient (MulAction.orbitRel G (Ω × Ω)))
    fun x y => Quotient.mk _ (x, y)

theorem orbitalConfig_color_eq_iff (G : Subgroup (Equiv.Perm Ω)) (x y u v : Ω) :
    (orbitalConfig G).color x y = (orbitalConfig G).color u v ↔
      ∃ σ ∈ G, ((σ : Equiv.Perm Ω) u, (σ : Equiv.Perm Ω) v) = (x, y) := by
  classical
  rw [orbitalConfig, ofColoring_color_eq_iff, Quotient.eq]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨(σ : Equiv.Perm Ω), σ.2, by simpa using hσ⟩
  · rintro ⟨σ, hσ, hσ'⟩
    exact ⟨⟨σ, hσ⟩, by simpa using hσ'⟩

/-- The constituent relations of `X(G)` are exactly the orbitals of `G`. -/
theorem isOrbital_rel_orbitalConfig (G : Subgroup (Equiv.Perm Ω))
    (i : Fin (orbitalConfig G).rank) : IsOrbital G ((orbitalConfig G).rel i) := by
  obtain ⟨x, y, hxy⟩ := (orbitalConfig G).color_surjective i
  refine ⟨(x, y), ?_⟩
  ext p
  simp only [mem_rel, MulAction.mem_orbit_iff]
  constructor
  · intro hp
    obtain ⟨σ, hσ, hσ'⟩ := (orbitalConfig_color_eq_iff G p.1 p.2 x y).1
      (by rw [show (orbitalConfig G).color p.1 p.2 = i from hp, hxy])
    refine ⟨⟨σ, hσ⟩, Prod.ext ?_ ?_⟩
    · exact congrArg Prod.fst hσ'
    · exact congrArg Prod.snd hσ'
  · rintro ⟨σ, hσ⟩
    show (orbitalConfig G).color p.1 p.2 = i
    rw [← hxy]
    refine (orbitalConfig_color_eq_iff G p.1 p.2 x y).2 ⟨(σ : Equiv.Perm Ω), σ.2, ?_⟩
    refine Prod.ext ?_ ?_
    · exact congrArg Prod.fst hσ
    · exact congrArg Prod.snd hσ

/-- Observation 3.1.12.  "`X(G) := (Ω; R₁,…,R_r)` is a coherent configuration." -/
theorem orbitalConfig_isCoherent (G : Subgroup (Equiv.Perm Ω)) :
    (orbitalConfig G).IsCoherent := by
  classical
  have hcfg : (orbitalConfig G).IsConfiguration := by
    constructor
    · -- axiom (i): an orbital meeting the diagonal is contained in it
      intro x y z hxyz
      obtain ⟨σ, -, hσ⟩ := (orbitalConfig_color_eq_iff G x y z z).1 hxyz
      have h1 : σ z = x := congrArg Prod.fst hσ
      have h2 : σ z = y := congrArg Prod.snd hσ
      rw [← h1, ← h2]
    · -- axiom (ii): the converse of an orbital is an orbital
      intro u v x y huv
      obtain ⟨σ, hσG, hσ⟩ := (orbitalConfig_color_eq_iff G u v x y).1 huv
      refine (orbitalConfig_color_eq_iff G v u y x).2 ⟨σ, hσG, ?_⟩
      have h1 : σ x = u := congrArg Prod.fst hσ
      have h2 : σ y = v := congrArg Prod.snd hσ
      rw [h1, h2]
  refine ⟨hcfg, ?_⟩
  refine ⟨fun i j k => {z : Ω | (orbitalConfig G).color ((orbitalConfig G).colorWitness k).1 z = i ∧
    (orbitalConfig G).color z ((orbitalConfig G).colorWitness k).2 = j}.ncard, ?_⟩
  intro i j k x y hxy
  -- `(x,y)` and the canonical pair of color `k` lie in the same orbital, so some `σ ∈ G`
  -- maps one to the other; `z ↦ σ z` is the required bijection
  obtain ⟨σ, hσG, hσ⟩ := (orbitalConfig_color_eq_iff G x y
    ((orbitalConfig G).colorWitness k).1 ((orbitalConfig G).colorWitness k).2).1
    (by rw [hxy, (orbitalConfig G).color_colorWitness k])
  have hx : σ ((orbitalConfig G).colorWitness k).1 = x := congrArg Prod.fst hσ
  have hy : σ ((orbitalConfig G).colorWitness k).2 = y := congrArg Prod.snd hσ
  have hinv : ∀ a b : Ω, (orbitalConfig G).color (σ a) (σ b) = (orbitalConfig G).color a b :=
    fun a b => (orbitalConfig_color_eq_iff G (σ a) (σ b) a b).2 ⟨σ, hσG, rfl⟩
  have himg : (σ : Equiv.Perm Ω) ''
      {z : Ω | (orbitalConfig G).color ((orbitalConfig G).colorWitness k).1 z = i ∧
        (orbitalConfig G).color z ((orbitalConfig G).colorWitness k).2 = j}
      = {z : Ω | (orbitalConfig G).color x z = i ∧ (orbitalConfig G).color z y = j} := by
    ext z
    constructor
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hx, hinv]; exact h1
      · rw [← hy, hinv]; exact h2
    · rintro ⟨h1, h2⟩
      have h3 : σ (σ⁻¹ z) = z := by simp
      refine ⟨σ⁻¹ z, ⟨?_, ?_⟩, h3⟩
      · have hc := hinv ((orbitalConfig G).colorWitness k).1 (σ⁻¹ z)
        rw [hx, h3] at hc
        rw [← hc]; exact h1
      · have hc := hinv (σ⁻¹ z) ((orbitalConfig G).colorWitness k).2
        rw [hy, h3] at hc
        rw [← hc]; exact h2
  rw [← himg, Set.ncard_image_of_injective _ (Equiv.injective _)]

/-- §3.1.3.  "We say that a coherent configuration is *Schurian* if it is the orbital
configuration of some permutation group." -/
def IsSchurian : Prop :=
  ∃ (G : Subgroup (Equiv.Perm Ω)) (e : Fin (orbitalConfig G).rank ≃ Fin X.rank),
    ∀ x y : Ω, X.color x y = e ((orbitalConfig G).color x y)

/-- Observation 3.1.13.  "`G ≤ Aut(X(G))`." -/
theorem le_aut_orbitalConfig (G : Subgroup (Equiv.Perm Ω)) :
    G ≤ (orbitalConfig G).Aut := by
  intro σ hσ x y
  rw [orbitalConfig_color_eq_iff]
  exact ⟨σ, hσ, rfl⟩

/-- Observation 3.1.15.  "The orbits of `G ≤ S(Ω)` are the vertex-color classes
of `X(G)`." -/
theorem vertexClass_orbitalConfig (G : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    (orbitalConfig G).vertexClass ((orbitalConfig G).vcolor x) =
      MulAction.orbit G x := by
  ext y
  rw [mem_vertexClass]
  constructor
  · intro h
    obtain ⟨σ, hσ, hσ'⟩ := (orbitalConfig_color_eq_iff G y y x x).1 h
    exact ⟨⟨σ, hσ⟩, congrArg Prod.fst hσ'⟩
  · rintro ⟨σ, rfl⟩
    exact (orbitalConfig_color_eq_iff G _ _ x x).2 ⟨(σ : Equiv.Perm Ω), σ.2, rfl⟩

/-- Observation 3.1.15.  "In particular, `X(G)` is homogeneous if and only if `G` is
transitive."

Degenerate carrier: for `Ω = ∅` the left-hand side is vacuously true (Def. 3.1.6, "all
vertices have the same color") while the right-hand side is false (the paper's
"transitive" means *one* orbit, and there is no orbit).  The hypothesis `[Nonempty Ω]`
excludes exactly that case; it is not an extra assumption anywhere in the development,
since a configuration on the empty set has rank `0`. -/
theorem orbitalConfig_isHomogeneous_iff [Nonempty Ω] (G : Subgroup (Equiv.Perm Ω)) :
    (orbitalConfig G).IsHomogeneous ↔ IsTransitive G := by
  constructor
  · intro hhom
    obtain ⟨x⟩ := ‹Nonempty Ω›
    refine ⟨x, ?_⟩
    rw [← vertexClass_orbitalConfig G x]
    ext y
    simp only [mem_vertexClass, Set.mem_univ, iff_true]
    exact hhom y x
  · rintro ⟨x, hx⟩ u v
    have hmem : ∀ w : Ω, w ∈ (orbitalConfig G).vertexClass ((orbitalConfig G).vcolor x) := by
      intro w
      rw [vertexClass_orbitalConfig G x, hx]
      trivial
    exact (hmem u).trans (hmem v).symm

/-- The degenerate case of Observation 3.1.15, spelled out: on `Ω = ∅` the orbital
configuration is homogeneous (Def. 3.1.6 is vacuous) while the group is not transitive
(§2.2.1: "transitive" means there is a point whose orbit is everything, and there is no
point).  This is a degenerate case of the definitions, not an error of the paper; it is
what the hypothesis `[Nonempty Ω]` of `orbitalConfig_isHomogeneous_iff` excludes.  See
the corrected paper. -/
example :
    (orbitalConfig (⊥ : Subgroup (Equiv.Perm (Fin 0)))).IsHomogeneous ∧
      ¬ IsTransitive (⊥ : Subgroup (Equiv.Perm (Fin 0))) := by
  refine ⟨fun x _ => absurd x.2 (by omega), ?_⟩
  rintro ⟨x, -⟩
  exact absurd x.2 (by omega)

/-- Observation 3.1.15, in the form of Def. 3.1.6 after "i.e.": *"`X(G)` is homogeneous
if and only if `G` is transitive"*, with "homogeneous" read as "`R₁ = diag(Ω)`" (some color
class of `X(G)` is the diagonal).  This form needs no hypothesis on `Ω`: for `Ω = ∅` the
configuration has no color at all, so both sides are false.  With `Ω` nonempty it is
`orbitalConfig_isHomogeneous_iff`. -/
theorem orbitalConfig_exists_rel_eq_diag_iff (G : Subgroup (Equiv.Perm Ω)) :
    (∃ i, (orbitalConfig G).rel i = diag Ω) ↔ IsTransitive G := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨x, -, -⟩ := (orbitalConfig G).color_surjective i
    haveI : Nonempty Ω := ⟨x⟩
    refine (orbitalConfig_isHomogeneous_iff G).1 fun u v => ?_
    have hu : (u, u) ∈ (orbitalConfig G).rel i := by rw [hi]; rfl
    have hv : (v, v) ∈ (orbitalConfig G).rel i := by rw [hi]; rfl
    exact hu.trans hv.symm
  · intro hG
    obtain ⟨x, -⟩ := id hG
    haveI : Nonempty Ω := ⟨x⟩
    have hhom := (orbitalConfig_isHomogeneous_iff G).2 hG
    refine ⟨(orbitalConfig G).vcolor x, Set.ext fun p => ?_⟩
    constructor
    · intro hp
      exact (orbitalConfig_isCoherent G).toIsConfiguration.diag p.1 p.2 x hp
    · intro hp
      have hp' : p.1 = p.2 := hp
      show (orbitalConfig G).color p.1 p.2 = (orbitalConfig G).color x x
      rw [← hp']
      exact hhom p.1 x

end Orbital

/- Remark 3.1.14.  "Not every coherent configuration is Schurian; in fact, there are
large families of strongly regular graphs with no non-identity automorphisms (line graphs
of Steiner triple systems, point graphs of Latin squares [Ba80, Cam80])."  This remark cites
examples from the literature and is used nowhere in the paper's proofs (§3.2 refers to it
only to illustrate that the converse of Obs. 3.2.3 fails), so it has no Lean statement. -/

end PartitionStructure

end Babai
