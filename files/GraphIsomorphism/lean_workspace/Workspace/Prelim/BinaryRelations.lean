/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.4: Binary relations (digraphs; bipartite graphs, semiregularity, equitable
partitions).
-/
import Workspace.Prelim.Structures
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# §2.4 Binary relations

The right-action convention of `Workspace.Prelim.PermGroups` is used throughout.

A digraph is a pair `X = (Ω, E)` with `E ⊆ Ω × Ω` (Definition 2.4.3); we keep the vertex
set as the type parameter, so a `Digraph Ω` carries only its edge relation.  Induced
subgraphs live on subtypes.

A bipartite graph is a triple `X = (A, B; E)` with `E ⊆ A × B` (§2.4.2).  We keep `A` and
`B` as two type parameters; for automorphisms and twins we use, as the paper does, the
digraph on `A ⊕ B` whose edges all point from `A` to `B`.

## Composition order

See the "Composition order" note of `Workspace.Prelim.Structures`: `RelStructure.map` is a
left action, so the paper's `X^{στ}` is Lean's `X.map (τ * σ)`.

## Finiteness

`outDeg`, `inDeg`, `IsBiregular`, `degA`, `degB`, `IsSemiregular` and `density` are stated
for bare types and count with `Set.ncard`/`Fintype.card`, which return `0` on infinite
sets; on an infinite vertex type "biregular" and "semiregular" become junk-true.  The
paper's vertex sets are finite throughout, and every theorem below that uses these notions
carries a `[Fintype _]` assumption.

## Degenerate carriers

`density`, `relSymmetricity₁/₂` and `defect₁/₂` use Lean's total division (`0/0 = 0`), so
an empty part gives density `0` and defect `1`, outside the paper's ranges.  The paper
assigns no value there.  See the corresponding docstrings and the "Degenerate carriers"
note of `Workspace.Prelim.Structures`.

## Numbering map

| Paper | Lean |
|---|---|
| Notation 2.4.1 | `Babai.invRel`, `Babai.outNbr`, `Babai.inNbr` |
| Definition 2.4.2 | `Babai.diag`, `Babai.IsIrreflexiveRel` |
| Definition 2.4.3 | `Babai.Digraph`, `Babai.Digraph.Adj`, `Babai.Digraph.inv`, `Babai.Digraph.induced` |
| Definition 2.4.4 | `Babai.Digraph.outNbhd`, `Babai.Digraph.inNbhd` |
| Observation 2.4.5 | `Babai.Digraph.handshake` |
| Definition 2.4.6 | `Babai.Digraph.IsBiregular` |
| Definition 2.4.7 | `Babai.Digraph.IsIrreflexive`, `Babai.Digraph.compl` |
| Definition 2.4.8 | `Babai.Digraph.completeReflexive`, `Babai.Digraph.completeIrreflexive` |
| Definition 2.4.9 | `Babai.Digraph.IsTrivial`, `Babai.Digraph.isTrivial_iff` |
| Definition 2.4.10 | `Babai.Digraph.IsIndependent` |
| Proposition 2.4.11 | `Babai.Digraph.ncard_independent_le` |
| Corollary 2.4.12 | `Babai.Digraph.defect_biregular_ge_half` |
| Definition 2.4.13 | `Babai.Digraph.IsGraph`, `Babai.Digraph.IsRegularOfDegree` |
| Definition 2.4.14 | `Babai.Digraph.IsStronglyRegular` |
| Examples 2.4.15 | `Babai.pentagon_sr`, `Babai.petersen_sr`, `Babai.clique_sr` |
| Definition 2.4.16 | `Babai.Digraph.symmetrization` |
| Definition 2.4.17 | `Babai.Digraph.IsWalk`, `Babai.Digraph.Accessible`, `Babai.Digraph.MutuallyAccessible`, `Babai.Digraph.strongComponent`, `Babai.Digraph.IsStronglyConnected` |
| Notation 2.4.18 | `Babai.Digraph.edgesBetween` |
| Definition 2.4.19 | `Babai.Digraph.IsCut` |
| Proposition 2.4.20 | `Babai.Digraph.isStronglyConnected_iff_cut` |
| Definition 2.4.21 | `Babai.Digraph.IsWeakWalk`, `Babai.Digraph.WeaklyAccessible`, `Babai.Digraph.weakComponent`, `Babai.Digraph.IsWeaklyConnected` |
| Definition 2.4.22 | `Babai.Digraph.IsEulerian` |
| Proposition 2.4.23 | `Babai.Digraph.weakComponent_eq_strongComponent` |
| Lemma 2.4.24 | `Babai.Digraph.card_edgesBetween_eq` |
| §2.4.2 bipartite graphs | `Babai.BipGraph` and its API |
| Definition 2.4.25 | `Babai.Digraph.inducedBip` |
| Definition 2.4.26 | `Babai.Digraph.IsEquitablePartition`, `Babai.Digraph.IsEquitableColoring` |
| Remark 2.4.27 | pointer to `Babai.PartitionStructure.IsEquitablePartition` and Obs. 4.1.1 `Babai.ColoredDigraph.isStable_iff_isEquitableColoring` |
| Observation 2.4.28 | `Babai.BipGraph.isTwin_iff`, `Babai.BipGraph.isTwin_inr_iff`, `Babai.BipGraph.not_isTwin_inl_inr`, `Babai.BipGraph.not_isTwin_inr_inl` |
| Definition 2.4.29 | `Babai.BipGraph.symmetricity₁`, `Babai.BipGraph.defect₁` (and `₂`) |
| Proposition 2.4.30 | `Babai.BipGraph.defect_ge_half` |
| Proposition 2.4.31 | `Babai.BipGraph.independent_sum_le_one` |
| Corollary 2.4.32 | `Babai.BipGraph.trivial_subgraph_sum_le_one` |
-/

namespace Babai

open Equiv Equiv.Perm

variable {Ω : Type*}

/-! ### §2.4.1 Digraphs -/

/-- Notation 2.4.1.  "The *inverse relation* `R⁻` is defined as
`R⁻ = {(y,x) | (x,y) ∈ R}`." -/
def invRel (R : Set (Ω × Ω)) : Set (Ω × Ω) := {p | (p.2, p.1) ∈ R}

@[simp] theorem mem_invRel {R : Set (Ω × Ω)} {p : Ω × Ω} :
    p ∈ invRel R ↔ (p.2, p.1) ∈ R := Iff.rfl

@[simp] theorem invRel_invRel (R : Set (Ω × Ω)) : invRel (invRel R) = R := rfl

/-- Notation 2.4.1.  "For `x ∈ Ω` we write `R(x) = {y ∈ Ω | (x,y) ∈ R}` for the set of
*out-neighbors* of `x`.  If `(x,y) ∈ R`, we say that `y` is an out-neighbor of `x` and `x`
is an in-neighbor of `y`." -/
def outNbr (R : Set (Ω × Ω)) (x : Ω) : Set Ω := {y | (x, y) ∈ R}

/-- Notation 2.4.1.  "`R⁻(x)` is the set of *in-neighbors* of `x`." -/
def inNbr (R : Set (Ω × Ω)) (x : Ω) : Set Ω := outNbr (invRel R) x

@[simp] theorem mem_outNbr {R : Set (Ω × Ω)} {x y : Ω} : y ∈ outNbr R x ↔ (x, y) ∈ R :=
  Iff.rfl

@[simp] theorem mem_inNbr {R : Set (Ω × Ω)} {x y : Ω} : y ∈ inNbr R x ↔ (y, x) ∈ R :=
  Iff.rfl

/-- Definition 2.4.2.  "The *diagonal* of the set `Ω` is the set
`diag(Ω) = {(x,x) | x ∈ Ω}`." -/
def diag (Ω : Type*) : Set (Ω × Ω) := {p | p.1 = p.2}

@[simp] theorem mem_diag {p : Ω × Ω} : p ∈ diag Ω ↔ p.1 = p.2 := Iff.rfl

/-- Definition 2.4.2.  "The relation `R ⊆ Ω × Ω` is *irreflexive* if
`R ∩ diag(Ω) = ∅`." -/
def IsIrreflexiveRel (R : Set (Ω × Ω)) : Prop := R ∩ diag Ω = ∅

/-- Definition 2.4.3.  "A *digraph* (directed graph) is a pair `X = (Ω, E)` where
`E ⊆ Ω × Ω` is a binary relation on `Ω`.  We say that `Ω` is the set of vertices and `E`
is the set of edges of `X`." -/
structure Digraph (Ω : Type*) where
  /-- The edge set: `E ⊆ Ω × Ω`.  "Vertex `u` is the *tail* and vertex `v` the *head* of
  the edge `(u,v)`." -/
  E : Set (Ω × Ω)

namespace Digraph

/-- Definition 2.4.3.  "We call `E` the *adjacency relation*.  If `(u,v) ∈ E`, we say that
`u` is *adjacent* to `v`." -/
def Adj (X : Digraph Ω) (u v : Ω) : Prop := (u, v) ∈ X.E

@[simp] theorem adj_def {X : Digraph Ω} {u v : Ω} : X.Adj u v ↔ (u, v) ∈ X.E := Iff.rfl

/-- Definition 2.4.3.  "If we reverse every edge, we obtain the digraph
`X⁻ = (Ω, E⁻)`." -/
def inv (X : Digraph Ω) : Digraph Ω := ⟨invRel X.E⟩

/-- Definition 2.4.3.  "For `Δ ⊆ Ω`, the *induced subgraph* `X[Δ]` of the digraph
`X = (Ω, E)` is defined as `X[Δ] = (Δ, E ∩ (Δ × Δ))`." -/
def induced (X : Digraph Ω) (Δ : Set Ω) : Digraph Δ :=
  ⟨{p | ((p.1 : Ω), (p.2 : Ω)) ∈ X.E}⟩

/-- Definition 2.4.3.  "We say that `X` is *empty* if it has no edges (`E = ∅`)." -/
def IsEmpty (X : Digraph Ω) : Prop := X.E = ∅

/-- Definition 2.4.4 (Neighborhood).  "The *out-neighborhood* of `Δ` is the set
`E(Δ) = ⋃_{x ∈ Δ} E(x) = {y ∈ Ω | (∃ x ∈ Δ)((x,y) ∈ E)}`." -/
def outNbhd (X : Digraph Ω) (Δ : Set Ω) : Set Ω := {y | ∃ x ∈ Δ, (x, y) ∈ X.E}

/-- Definition 2.4.4.  "The *in-neighborhood* is `E⁻(Δ)`." -/
def inNbhd (X : Digraph Ω) (Δ : Set Ω) : Set Ω := X.inv.outNbhd Δ

/-- Definition 2.4.3.  "The *out-degree* of vertex `u ∈ Ω` is `deg⁺(u) = |E(u)|`, the
number of out-neighbors of `u`." -/
noncomputable def outDeg (X : Digraph Ω) (u : Ω) : ℕ := (outNbr X.E u).ncard

/-- Definition 2.4.3.  "Analogously, the *in-degree* `deg⁻(u) = |E⁻(u)|` is the number of
in-neighbors of `u`." -/
noncomputable def inDeg (X : Digraph Ω) (u : Ω) : ℕ := (inNbr X.E u).ncard

/-- Definition 2.4.3.  "An *isolated vertex* is a vertex `u` with
`deg⁺(u) = deg⁻(u) = 0`." -/
def IsIsolated (X : Digraph Ω) (u : Ω) : Prop := outNbr X.E u = ∅ ∧ inNbr X.E u = ∅

/-- Definition 2.4.3.  "An edge of the form `(u,u)` is referred to as a *self-loop*
attached to vertex `u`." -/
def HasSelfLoop (X : Digraph Ω) (u : Ω) : Prop := (u, u) ∈ X.E

/-- Definition 2.4.3.  "The digraph is *oriented* if `E` is antisymmetric, i.e.
`E ∩ E⁻ = ∅`." -/
def IsOriented (X : Digraph Ω) : Prop := X.E ∩ invRel X.E = ∅

/-- Observation 2.4.5 (Directed "handshake theorem").
`∑_{u ∈ Ω} deg⁺(u) = ∑_{u ∈ Ω} deg⁻(u) = |E|`. -/
theorem handshake [Fintype Ω] (X : Digraph Ω) :
    (∑ u : Ω, X.outDeg u) = X.E.ncard ∧ (∑ u : Ω, X.inDeg u) = X.E.ncard := by
  classical
  have key : ∀ R : Set (Ω × Ω), (∑ u : Ω, (outNbr R u).ncard) = R.ncard := by
    intro R
    rw [Set.ncard_eq_toFinset_card',
      Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
        (fun x _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Set.ncard_eq_toFinset_card']
    have himg : (R.toFinset.filter fun p => p.1 = u)
        = (outNbr R u).toFinset.image (fun y => (u, y)) := by
      ext p
      simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_image, mem_outNbr]
      constructor
      · rintro ⟨hp, hu⟩
        exact ⟨p.2, by rw [← hu]; exact hp, by rw [← hu]⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, rfl⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hinv : (invRel X.E).ncard = X.E.ncard := by
    have himg : invRel X.E = Prod.swap '' X.E := by
      ext p
      simp only [mem_invRel, Set.mem_image]
      constructor
      · intro hp; exact ⟨p.swap, hp, by simp⟩
      · rintro ⟨q, hq, rfl⟩; simpa using hq
    rw [himg, Set.ncard_image_of_injective _ Prod.swap_injective]
  exact ⟨key X.E, (key (invRel X.E)).trans hinv⟩

/-- Definition 2.4.6 (Biregular digraph).  "`X` is *biregular* if all vertices have the
same in-degree and all vertices have the same out-degree (so these two numbers are
necessarily equal)." -/
def IsBiregular (X : Digraph Ω) : Prop :=
  (∃ d, ∀ u, X.outDeg u = d) ∧ (∃ d, ∀ u, X.inDeg u = d)

/-- Definition 2.4.7 (Complement).  "We say that the digraph `X` is *irreflexive* if the
relation `E` is irreflexive." -/
def IsIrreflexive (X : Digraph Ω) : Prop := IsIrreflexiveRel X.E

/-- Definition 2.4.7.  "The *irreflexive complement* of an irreflexive digraph
`X = (Ω, E)` is `X̄ = (Ω, Ē)` where `Ē = (Ω × Ω) \ (diag(Ω) ∪ E)`." -/
def compl (X : Digraph Ω) : Digraph Ω := ⟨Set.univ \ (diag Ω ∪ X.E)⟩

/-- Definition 2.4.8 (Complete digraph).  "If `E = Ω × Ω`, we call `X` the *complete
reflexive digraph* on `Ω`." -/
def completeReflexive (Ω : Type*) : Digraph Ω := ⟨Set.univ⟩

/-- Definition 2.4.8.  "If `E = (Ω × Ω) \ diag(Ω)`, we call `X` the *complete irreflexive
digraph* or *clique* on `Ω`." -/
def completeIrreflexive (Ω : Type*) : Digraph Ω := ⟨Set.univ \ diag Ω⟩

/-- The *diagonal* digraph `(Ω, diag(Ω))`, one of the trivial digraphs of
Definition 2.4.9. -/
def diagonal (Ω : Type*) : Digraph Ω := ⟨diag Ω⟩

/-- Definition 2.4.4.  `Aut(X) ≤ S(Ω)` for a digraph `X`: the permutations of the vertex
set preserving the edge relation. -/
def Aut (X : Digraph Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {σ | ∀ u v, ((σ u, σ v) ∈ X.E ↔ (u, v) ∈ X.E)}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro a b ha hb u v
    simpa [Equiv.Perm.mul_apply] using (ha (b u) (b v)).trans (hb u v)
  inv_mem' := by
    intro a ha u v
    have := ha (a⁻¹ u) (a⁻¹ v)
    simpa using this.symm

@[simp] theorem mem_aut {X : Digraph Ω} {σ : Equiv.Perm Ω} :
    σ ∈ Aut X ↔ ∀ u v, ((σ u, σ v) ∈ X.E ↔ (u, v) ∈ X.E) := Iff.rfl

end Digraph

instance : IsStructure (Digraph Ω) Ω := ⟨Digraph.Aut⟩

namespace Digraph

/-- Definition 2.4.9 (Trivial digraphs).  "We say that `X = (Ω, E)` is *trivial* if
`Aut(X) = S(Ω)`." -/
def IsTrivial (X : Digraph Ω) : Prop := Aut X = ⊤

/-- Definition 2.4.9.  "…i.e. if `X` is empty, the diagonal, or the reflexive or
irreflexive complete digraph."  (The four listed digraphs are exactly the unions of
orbits of `S(Ω)` on `Ω × Ω`.) -/
theorem isTrivial_iff (X : Digraph Ω) :
    IsTrivial X ↔ X = ⟨∅⟩ ∨ X = diagonal Ω ∨ X = completeReflexive Ω ∨
      X = completeIrreflexive Ω := by
  classical
  have hext : ∀ {Y Z : Digraph Ω}, Y.E = Z.E → Y = Z := by
    rintro ⟨E⟩ ⟨F⟩ h
    simp only [Digraph.mk.injEq]
    exact h
  constructor
  · intro htriv
    have haut : ∀ (σ : Equiv.Perm Ω) (u v : Ω), ((σ u, σ v) ∈ X.E ↔ (u, v) ∈ X.E) := by
      intro σ
      exact Digraph.mem_aut.1 (by rw [htriv]; trivial)
    -- the loops form a union of `S(Ω)`-orbits, and so do the proper edges
    have hloop : (∃ x : Ω, (x, x) ∈ X.E) → ∀ x : Ω, (x, x) ∈ X.E := by
      rintro ⟨a, ha⟩ x
      by_cases hxa : x = a
      · exact hxa ▸ ha
      · have h := haut (Equiv.swap a x) a a
        rw [Equiv.swap_apply_left] at h
        exact h.2 ha
    have hoffall : (∃ a b : Ω, a ≠ b ∧ (a, b) ∈ X.E) →
        ∀ u v : Ω, u ≠ v → (u, v) ∈ X.E := by
      rintro ⟨a, b, hab, hE⟩ u v huv
      obtain ⟨σ, -, hσa, hσb⟩ :=
        exists_symOn_map_pair (Ψ := (Set.univ : Set Ω)) (Set.mem_univ a) (Set.mem_univ b)
          (Set.mem_univ u) (Set.mem_univ v) hab huv
      rw [← hσa, ← hσb]
      exact (haut σ a b).2 hE
    by_cases hdiag : ∃ x : Ω, (x, x) ∈ X.E
    · by_cases hoff : ∃ a b : Ω, a ≠ b ∧ (a, b) ∈ X.E
      · -- loops and proper edges: the complete reflexive digraph
        refine Or.inr (Or.inr (Or.inl (hext ?_)))
        ext ⟨u, v⟩
        simp only [completeReflexive, Set.mem_univ, iff_true]
        by_cases huv : u = v
        · exact huv ▸ hloop hdiag u
        · exact hoffall hoff u v huv
      · -- loops only: the diagonal
        push_neg at hoff
        refine Or.inr (Or.inl (hext ?_))
        ext ⟨u, v⟩
        simp only [diagonal, mem_diag]
        constructor
        · intro hE
          by_contra huv
          exact hoff u v huv hE
        · intro huv
          exact huv ▸ hloop hdiag u
    · push_neg at hdiag
      by_cases hoff : ∃ a b : Ω, a ≠ b ∧ (a, b) ∈ X.E
      · -- proper edges only: the complete irreflexive digraph
        refine Or.inr (Or.inr (Or.inr (hext ?_)))
        ext ⟨u, v⟩
        simp only [completeIrreflexive, Set.mem_diff, Set.mem_univ, true_and, mem_diag]
        constructor
        · intro hE huv
          exact hdiag u (huv ▸ hE)
        · intro huv
          exact hoffall hoff u v huv
      · -- neither: the empty digraph
        push_neg at hoff
        refine Or.inl (hext ?_)
        ext ⟨u, v⟩
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hE
        by_cases huv : u = v
        · exact hdiag u (huv ▸ hE)
        · exact hoff u v huv hE
  · rintro (rfl | rfl | rfl | rfl)
    · refine (Subgroup.eq_top_iff' _).2 fun σ u v => ?_
      simp
    · refine (Subgroup.eq_top_iff' _).2 fun σ u v => ?_
      simp only [diagonal, mem_diag]
      exact ⟨fun h => σ.injective h, fun h => by rw [h]⟩
    · refine (Subgroup.eq_top_iff' _).2 fun σ u v => ?_
      simp [completeReflexive]
    · refine (Subgroup.eq_top_iff' _).2 fun σ u v => ?_
      simp only [completeIrreflexive, Set.mem_diff, Set.mem_univ, true_and, mem_diag]
      exact not_congr ⟨fun h => σ.injective h, fun h => by rw [h]⟩

/-- Definition 2.4.9.  An empty digraph is trivial. -/
theorem isTrivial_of_isEmpty {X : Digraph Ω} (h : X.IsEmpty) : X.IsTrivial :=
  (Subgroup.eq_top_iff' _).2 fun σ u v => by rw [IsEmpty] at h; simp [h]

/-- Definition 2.4.9.  An irreflexive digraph whose irreflexive complement is empty is the
complete irreflexive digraph, hence trivial. -/
theorem isTrivial_of_compl_isEmpty {X : Digraph Ω} (hirr : X.IsIrreflexive)
    (h : X.compl.IsEmpty) : X.IsTrivial := by
  have hE : X.E = Set.univ \ diag Ω := by
    ext p
    constructor
    · refine fun hp => ⟨Set.mem_univ _, fun hd => ?_⟩
      have hmem : p ∈ X.E ∩ diag Ω := ⟨hp, hd⟩
      rw [show X.E ∩ diag Ω = ∅ from hirr] at hmem
      exact hmem
    · intro hp
      by_contra hc
      have hmem : p ∈ X.compl.E := ⟨Set.mem_univ _, by
        rintro (hd | he)
        · exact hp.2 hd
        · exact hc he⟩
      rw [IsEmpty] at h
      rw [h] at hmem
      exact hmem
  refine (Subgroup.eq_top_iff' _).2 fun σ u v => ?_
  rw [hE]
  simp [diag]

/-- The out-degree in the irreflexive complement: `deg⁺_{X̄}(u) = n - 1 - deg⁺_X(u)`. -/
theorem outDeg_compl [Fintype Ω] {X : Digraph Ω} (hirr : X.IsIrreflexive) (u : Ω) :
    X.compl.outDeg u = Fintype.card Ω - 1 - X.outDeg u := by
  classical
  have hset : outNbr X.compl.E u = (insert u (outNbr X.E u))ᶜ := by
    ext v
    simp only [mem_outNbr, compl, Set.mem_diff, Set.mem_univ, true_and, Set.mem_union,
      mem_diag, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
    tauto
  have hnot : u ∉ outNbr X.E u := fun hu => by
    have hmem : ((u, u) : Ω × Ω) ∈ X.E ∩ diag Ω := ⟨hu, rfl⟩
    rw [show X.E ∩ diag Ω = ∅ from hirr] at hmem
    exact hmem
  have hins : (insert u (outNbr X.E u)).ncard = X.outDeg u + 1 :=
    Set.ncard_insert_of_notMem hnot (Set.toFinite _)
  have hsum := Set.ncard_add_ncard_compl (insert u (outNbr X.E u))
  rw [Nat.card_eq_fintype_card] at hsum
  rw [outDeg, hset]
  omega

/-- The in-degree in the irreflexive complement: `deg⁻_{X̄}(u) = n - 1 - deg⁻_X(u)`. -/
theorem inDeg_compl [Fintype Ω] {X : Digraph Ω} (hirr : X.IsIrreflexive) (u : Ω) :
    X.compl.inDeg u = Fintype.card Ω - 1 - X.inDeg u := by
  classical
  have hset : inNbr X.compl.E u = (insert u (inNbr X.E u))ᶜ := by
    ext v
    simp only [mem_inNbr, compl, Set.mem_diff, Set.mem_univ, true_and, Set.mem_union,
      mem_diag, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
  have hnot : u ∉ inNbr X.E u := fun hu => by
    have hmem : ((u, u) : Ω × Ω) ∈ X.E ∩ diag Ω := ⟨hu, rfl⟩
    rw [show X.E ∩ diag Ω = ∅ from hirr] at hmem
    exact hmem
  have hins : (insert u (inNbr X.E u)).ncard = X.inDeg u + 1 :=
    Set.ncard_insert_of_notMem hnot (Set.toFinite _)
  have hsum := Set.ncard_add_ncard_compl (insert u (inNbr X.E u))
  rw [Nat.card_eq_fintype_card] at hsum
  rw [inDeg, hset]
  omega

/-- Definition 2.4.6 and 2.4.7.  The irreflexive complement of a biregular irreflexive
digraph is biregular. -/
theorem IsBiregular.compl [Fintype Ω] {X : Digraph Ω} (hirr : X.IsIrreflexive)
    (h : X.IsBiregular) : X.compl.IsBiregular := by
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩⟩ := h
  exact ⟨⟨Fintype.card Ω - 1 - d, fun u => by rw [outDeg_compl hirr u, hd u]⟩,
    ⟨Fintype.card Ω - 1 - d', fun u => by rw [inDeg_compl hirr u, hd' u]⟩⟩

/-- Definition 2.4.10 (Independent set).  "A subset `A ⊆ Ω` is an *independent set* in the
digraph `X = (Ω, E)` if `A` contains no edges, i.e. `E ∩ (A × A) = ∅`." -/
def IsIndependent (X : Digraph Ω) (A : Set Ω) : Prop := X.E ∩ (A ×ˢ A) = ∅

/-- Definition 2.4.10.  "Note that an independent set cannot contain a self-adjacent
vertex (a vertex with a self-loop)." -/
theorem not_hasSelfLoop_of_mem_independent {X : Digraph Ω} {A : Set Ω}
    (h : IsIndependent X A) {u : Ω} (hu : u ∈ A) : ¬ X.HasSelfLoop u := by
  intro hloop
  have : (u, u) ∈ X.E ∩ (A ×ˢ A) := ⟨hloop, ⟨hu, hu⟩⟩
  rw [h] at this
  exact this

open scoped Classical in
/-- Counting the edges emanating from a set of vertices: `|E ∩ (S × Ω)| = ∑_{u ∈ S} deg⁺(u)`.
This is the restriction of Observation 2.4.5 to a set of tails; it is stated for a
relation between two sets, so that it also serves the bipartite case (Prop. 2.4.31). -/
private theorem ncard_edges_from {α β : Type*} [Fintype α] [Fintype β]
    (R : Set (α × β)) (S : Set α) :
    (R ∩ (S ×ˢ (Set.univ : Set β))).ncard = ∑ u ∈ S.toFinset, {y : β | (u, y) ∈ R}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card',
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S.toFinset)
      (fun p hp => by
        simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_inter_iff, Set.mem_prod] at hp ⊢
        exact hp.2.1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Set.ncard_eq_toFinset_card']
  have himg : ((R ∩ (S ×ˢ (Set.univ : Set β))).toFinset.filter fun p => p.1 = u)
      = {y : β | (u, y) ∈ R}.toFinset.image (fun y => (u, y)) := by
    ext p
    simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨⟨hp, _⟩, hu'⟩
      exact ⟨p.2, by rw [← hu']; exact hp, by rw [← hu']⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨hy, Set.mem_toFinset.1 hu⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

open scoped Classical in
/-- Counting the edges absorbed by a set of vertices: `|E ∩ (Ω × S)| = ∑_{u ∈ S} deg⁻(u)`. -/
private theorem ncard_edges_into {α β : Type*} [Fintype α] [Fintype β]
    (R : Set (α × β)) (S : Set β) :
    (R ∩ ((Set.univ : Set α) ×ˢ S)).ncard = ∑ v ∈ S.toFinset, {y : α | (y, v) ∈ R}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card',
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := S.toFinset)
      (fun p hp => by
        simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_inter_iff, Set.mem_prod] at hp ⊢
        exact hp.2.2)]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Set.ncard_eq_toFinset_card']
  have himg : ((R ∩ ((Set.univ : Set α) ×ˢ S)).toFinset.filter fun p => p.2 = v)
      = {y : α | (y, v) ∈ R}.toFinset.image (fun y => (y, v)) := by
    ext p
    simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hp, _⟩, hv'⟩
      exact ⟨p.1, by rw [← hv']; exact hp, by rw [← hv']⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨hy, Set.mem_toFinset.1 hv⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]

/-- Proposition 2.4.11 (Independent sets in biregular digraphs).  "Let `X = (Ω, E)` be a
non-empty biregular digraph.  Then `X` has no independent set of size greater than `n/2`
where `n = |Ω|`."

Paper's proof: with `d > 0` the common degree and `A` independent, `Ω \ A` has to absorb
all edges emanating from `A`, so `d(n - |A|) ≥ d|A|`. -/
theorem ncard_independent_le [Fintype Ω] {X : Digraph Ω} (hne : ¬ X.IsEmpty)
    (hreg : X.IsBiregular) {A : Set Ω} (hA : X.IsIndependent A) :
    2 * A.ncard ≤ Fintype.card Ω := by
  classical
  obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩⟩ := hreg
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.2 hne
  -- `d > 0` since `X` is non-empty
  have hdpos : 0 < d := by
    have h1 : (outNbr X.E p.1).Nonempty := ⟨p.2, by simpa using hp⟩
    have h2 : 0 < (outNbr X.E p.1).ncard := (Set.ncard_pos (Set.toFinite _)).2 h1
    rwa [show (outNbr X.E p.1).ncard = d from hd p.1] at h2
  -- the common in- and out-degree agree, by the handshake theorem (Obs. 2.4.5)
  haveI : Nonempty Ω := ⟨p.1⟩
  have hdd : d = d' := by
    have hs := X.handshake
    have e₁ : (∑ u : Ω, X.outDeg u) = Fintype.card Ω * d := by
      rw [Finset.sum_congr rfl (fun u _ => hd u), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    have e₂ : (∑ u : Ω, X.inDeg u) = Fintype.card Ω * d' := by
      rw [Finset.sum_congr rfl (fun u _ => hd' u), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    have hmul : Fintype.card Ω * d = Fintype.card Ω * d' := by
      rw [← e₁, ← e₂, hs.1, hs.2]
    exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos hmul
  -- `Ω \ A` absorbs all edges emanating from `A`
  have hsub : X.E ∩ (A ×ˢ (Set.univ : Set Ω)) ⊆ X.E ∩ ((Set.univ : Set Ω) ×ˢ Aᶜ) := by
    rintro ⟨u, v⟩ ⟨he, hu, -⟩
    refine ⟨he, Set.mem_univ _, fun hv => ?_⟩
    have hmem : ((u, v) : Ω × Ω) ∈ X.E ∩ (A ×ˢ A) := ⟨he, hu, hv⟩
    rw [hA] at hmem
    exact hmem
  have h1 : (X.E ∩ (A ×ˢ (Set.univ : Set Ω))).ncard = A.ncard * d := by
    have hval : ∀ u : Ω, {y : Ω | (u, y) ∈ X.E}.ncard = d := fun u => hd u
    rw [ncard_edges_from, Finset.sum_congr rfl (fun u _ => hval u), Finset.sum_const,
      smul_eq_mul, ← Set.ncard_eq_toFinset_card']
  have h2 : (X.E ∩ ((Set.univ : Set Ω) ×ˢ Aᶜ)).ncard = (Aᶜ : Set Ω).ncard * d' := by
    have hval : ∀ v : Ω, {y : Ω | (y, v) ∈ X.E}.ncard = d' := fun v => hd' v
    rw [ncard_edges_into, Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_const,
      smul_eq_mul, ← Set.ncard_eq_toFinset_card']
  have hle : A.ncard * d ≤ (Aᶜ : Set Ω).ncard * d' := by
    rw [← h1, ← h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← hdd] at hle
  have hAle : A.ncard ≤ (Aᶜ : Set Ω).ncard := Nat.le_of_mul_le_mul_right hle hdpos
  have hsum : A.ncard + (Aᶜ : Set Ω).ncard = Fintype.card Ω := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  omega

end Digraph

/-! ### Definition 2.4.13: graphs -/

namespace Digraph

/-- Definition 2.4.13 (Graph).  "By a *graph* `X = (Ω, E)` we mean an irreflexive digraph
where the relation `E` is symmetric (`E = E⁻`)." -/
structure IsGraph (X : Digraph Ω) : Prop where
  irrefl : X.IsIrreflexive
  symm : X.E = invRel X.E

/-- Definition 2.4.13.  "The *degree* of a vertex is its common in- and out-degree.  `X`
is *regular of degree `k`* if each vertex has degree `k`." -/
def IsRegularOfDegree (X : Digraph Ω) (k : ℕ) : Prop := ∀ u, X.outDeg u = k

/-- Definition 2.4.14 (Strongly regular graphs).  "A graph `X = (Ω, E)` is *strongly
regular* (SR) with parameters `(n, k, λ, μ)` if it has `n` vertices, it is regular of
degree `k`, every pair of adjacent vertices has `λ` common neighbors and every pair of
distinct, non-adjacent vertices has `μ` common neighbors." -/
structure IsStronglyRegular [Fintype Ω] (X : Digraph Ω) (n k lam mu : ℕ) : Prop where
  isGraph : X.IsGraph
  card_eq : Fintype.card Ω = n
  regular : X.IsRegularOfDegree k
  common_adj : ∀ u v, X.Adj u v → (outNbr X.E u ∩ outNbr X.E v).ncard = lam
  common_nonadj : ∀ u v, u ≠ v → ¬ X.Adj u v → (outNbr X.E u ∩ outNbr X.E v).ncard = mu

/-- Definition 2.4.16 (Symmetrization).  "Let `X = (Ω, E)` be a digraph.  The
*symmetrization* of `X` is the digraph `X̃ = (Ω, E ∪ E⁻)`." -/
def symmetrization (X : Digraph Ω) : Digraph Ω := ⟨X.E ∪ invRel X.E⟩

/-- Definition 2.4.16.  "Note that the symmetrization of an irreflexive digraph is a
graph." -/
theorem isGraph_symmetrization {X : Digraph Ω} (h : X.IsIrreflexive) :
    X.symmetrization.IsGraph where
  irrefl := by
    rw [IsIrreflexive, IsIrreflexiveRel] at *
    ext p
    simp only [symmetrization, Set.mem_inter_iff, Set.mem_union, mem_invRel, mem_diag,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (hp | hp) hdiag
    · exact absurd (Set.eq_empty_iff_forall_notMem.1 h p ⟨hp, hdiag⟩) not_false
    · refine absurd (Set.eq_empty_iff_forall_notMem.1 h (p.2, p.1) ⟨hp, ?_⟩) not_false
      simpa using hdiag.symm
  symm := by
    ext p
    simp only [symmetrization, Set.mem_union, mem_invRel]
    tauto

/-! ### Definition 2.4.17: walks and strong components -/

/-- Definition 2.4.17.  "A *walk of length `t ≥ 0`* in the digraph `X = (Ω, E)` is a
sequence `(u₀,…,u_t)` of vertices such that `(∀ i ≥ 1)((u_{i-1}, u_i) ∈ E)`." -/
def IsWalk (X : Digraph Ω) {t : ℕ} (u : Fin (t + 1) → Ω) : Prop :=
  ∀ i : Fin t, X.Adj (u i.castSucc) (u i.succ)

/-- Definition 2.4.17.  "We say that vertex `v` is *accessible* from vertex `u` if there
exists a walk that starts at `u` and ends at `v`." -/
def Accessible (X : Digraph Ω) (u v : Ω) : Prop :=
  ∃ (t : ℕ) (w : Fin (t + 1) → Ω), X.IsWalk w ∧ w 0 = u ∧ w (Fin.last t) = v

/-- Induction along a walk: a reflexive, transitive relation containing the adjacency
relation contains the "accessible" relation. -/
theorem walk_rel (Y : Digraph Ω) {r : Ω → Ω → Prop} (hrefl : ∀ x, r x x)
    (htrans : ∀ {a b c}, r a b → r b c → r a c) (hadj : ∀ a b, Y.Adj a b → r a b) :
    ∀ (t : ℕ) (w : Fin (t + 1) → Ω), Y.IsWalk w → r (w 0) (w (Fin.last t)) := by
  intro t
  induction t with
  | zero => intro w _; simpa using hrefl (w 0)
  | succ n ih =>
    intro w hw
    have hw' : Y.IsWalk (fun i : Fin (n + 1) => w i.castSucc) := by
      intro j
      have h := hw j.castSucc
      rwa [Fin.succ_castSucc] at h
    have h1 := ih (fun i : Fin (n + 1) => w i.castSucc) hw'
    have h2 : Y.Adj (w (Fin.last n).castSucc) (w (Fin.last (n + 1))) := by
      have h := hw (Fin.last n)
      rwa [show (Fin.last n).succ = Fin.last (n + 1) from rfl] at h
    exact htrans (by simpa using h1) (hadj _ _ h2)

/-- Accessibility (Def. 2.4.17) is contained in every reflexive, transitive relation
that contains the adjacency relation. -/
theorem accessible_rel (Y : Digraph Ω) {r : Ω → Ω → Prop} (hrefl : ∀ x, r x x)
    (htrans : ∀ {a b c}, r a b → r b c → r a c) (hadj : ∀ a b, Y.Adj a b → r a b)
    {u v : Ω} (h : Y.Accessible u v) : r u v := by
  obtain ⟨t, w, hw, h0, hl⟩ := h
  have := Y.walk_rel hrefl htrans hadj t w hw
  rwa [h0, hl] at this

/-- Accessibility is the reflexive-transitive closure of the adjacency relation. -/
theorem accessible_iff_reflTransGen (X : Digraph Ω) (u v : Ω) :
    X.Accessible u v ↔ Relation.ReflTransGen X.Adj u v := by
  constructor
  · exact X.accessible_rel (fun _ => Relation.ReflTransGen.refl)
      (fun h h' => h.trans h') (fun _ _ h => Relation.ReflTransGen.single h)
  · intro h
    induction h with
    | refl => exact ⟨0, fun _ => u, fun i => i.elim0, rfl, rfl⟩
    | @tail b c _ hadj ih =>
      obtain ⟨t, w, hw, h0, hl⟩ := ih
      refine ⟨t + 1, Fin.snoc w c, ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last,
            Fin.snoc_castSucc, hl]
          exact hadj
        · intro i
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hw i
      · rw [show (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc from rfl, Fin.snoc_castSucc]
        exact h0
      · rw [Fin.snoc_last]

/-- Definition 2.4.17.  "We say that `u` and `v` are *mutually accessible* if each is
accessible from the other." -/
def MutuallyAccessible (X : Digraph Ω) (u v : Ω) : Prop :=
  X.Accessible u v ∧ X.Accessible v u

/-- Definition 2.4.17.  "Mutual accessibility is an equivalence relation on `Ω`." -/
theorem mutuallyAccessible_equivalence (X : Digraph Ω) :
    Equivalence X.MutuallyAccessible where
  refl u := by
    constructor <;>
      exact (X.accessible_iff_reflTransGen u u).2 Relation.ReflTransGen.refl
  symm h := ⟨h.2, h.1⟩
  trans := by
    rintro a b c ⟨hab, hba⟩ ⟨hbc, hcb⟩
    rw [accessible_iff_reflTransGen] at hab hba hbc hcb
    exact ⟨(accessible_iff_reflTransGen X _ _).2 (hab.trans hbc),
      (accessible_iff_reflTransGen X _ _).2 (hcb.trans hba)⟩

/-- Definition 2.4.17.  "Its equivalence classes are called the *strong components*
of `X`." -/
def strongComponent (X : Digraph Ω) (u : Ω) : Set Ω := {v | X.MutuallyAccessible u v}

/-- Definition 2.4.17.  "We say that `X` is *strongly connected* if every vertex is
accessible from every vertex, i.e. there is just one strong component."

We use the paper's first phrasing.  It differs from the second one only for `Ω = ∅`,
where there is no strong component at all but every vertex is accessible from every
vertex; the first phrasing is the one under which Prop. 2.4.20 holds with no extra
hypothesis. -/
def IsStronglyConnected (X : Digraph Ω) : Prop := ∀ u v, X.Accessible u v

/-- Notation 2.4.18.  "Let `X = (Ω, E)` be a digraph and `A, B ⊆ Ω`.  Set
`E(A,B) = E ∩ (A × B)`." -/
def edgesBetween (X : Digraph Ω) (A B : Set Ω) : Set (Ω × Ω) := X.E ∩ (A ×ˢ B)

/-- Definition 2.4.19 (Cut).  "A *cut* `(A,B)` of a digraph `X = (Ω, E)` is an ordered
pair of nonempty sets `A, B ⊆ Ω` where `B = Ω \ A`." -/
def IsCut (_X : Digraph Ω) (A B : Set Ω) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ B = Set.univ \ A

/-- Proposition 2.4.20 (Cut characterization).  "The digraph `X = (Ω, E)` is strongly
connected if and only if for every cut `(A,B)` we have `E(A,B) ≠ ∅`."

The paper calls this "well-known" and gives no proof and no citation. -/
theorem isStronglyConnected_iff_cut (X : Digraph Ω) :
    X.IsStronglyConnected ↔ ∀ A B : Set Ω, X.IsCut A B → X.edgesBetween A B ≠ ∅ := by
  constructor
  · -- a walk from a point of `A` to a point of `B` has to cross the cut
    rintro hconn A B ⟨⟨a, ha⟩, ⟨b, hb⟩, hB⟩ hEmpty
    have hacc := (X.accessible_iff_reflTransGen a b).1 (hconn a b)
    have hstay : ∀ z, Relation.ReflTransGen X.Adj a z → z ∈ A := by
      intro z hz
      induction hz with
      | refl => exact ha
      | @tail c z _ hadj ih =>
        by_contra hzA
        have hmem : ((c, z) : Ω × Ω) ∈ X.edgesBetween A B :=
          ⟨hadj, ih, by rw [hB]; exact ⟨trivial, hzA⟩⟩
        rw [hEmpty] at hmem
        exact hmem
    rw [hB] at hb
    exact hb.2 (hstay b hacc)
  · -- the set of vertices accessible from `u` absorbs all edges leaving it
    intro h u v
    by_contra hnacc
    have huA : u ∈ {x | X.Accessible u x} := ⟨0, fun _ => u, fun i => i.elim0, rfl, rfl⟩
    have hcut : X.IsCut {x | X.Accessible u x} (Set.univ \ {x | X.Accessible u x}) :=
      ⟨⟨u, huA⟩, ⟨v, trivial, hnacc⟩, rfl⟩
    refine h _ _ hcut ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, y⟩ ⟨hxy, hxA, hyB⟩
    exact hyB.2 ((X.accessible_iff_reflTransGen u y).2
      (((X.accessible_iff_reflTransGen u x).1 hxA).tail hxy))

/-- Definition 2.4.21 (Weak components).  "A *weak walk* of length `t` in the digraph
`X = (Ω, E)` is a walk of length `t` in its symmetrization `X̃`." -/
def IsWeakWalk (X : Digraph Ω) {t : ℕ} (u : Fin (t + 1) → Ω) : Prop :=
  X.symmetrization.IsWalk u

/-- Definition 2.4.21.  "We say that vertex `v` is *weakly accessible* from vertex `u` if
`v` is accessible from `u` in `X̃`." -/
def WeaklyAccessible (X : Digraph Ω) (u v : Ω) : Prop := X.symmetrization.Accessible u v

/-- Induction along a weak walk: a reflexive, symmetric and transitive relation containing
the adjacency relation contains the "weakly accessible" relation. -/
theorem weaklyAccessible_rel (Y : Digraph Ω) {r : Ω → Ω → Prop} (hrefl : ∀ x, r x x)
    (hsymm : ∀ {a b}, r a b → r b a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (hadj : ∀ a b, Y.Adj a b → r a b) {u v : Ω} (h : Y.WeaklyAccessible u v) : r u v := by
  refine Y.symmetrization.accessible_rel hrefl htrans ?_ h
  intro a b hab
  rcases hab with hab | hab
  · exact hadj a b hab
  · exact hsymm (hadj b a hab)

/-- Definition 2.4.21.  "The *weak components* of `X` are the (strong) components
of `X̃`." -/
def weakComponent (X : Digraph Ω) (u : Ω) : Set Ω := X.symmetrization.strongComponent u

/-- Definition 2.4.21.  "We say that `X` is *weakly connected* if `X̃` is (strongly)
connected." -/
def IsWeaklyConnected (X : Digraph Ω) : Prop := X.symmetrization.IsStronglyConnected

/-! ### Def. 2.4.17 and 2.4.21: components form a partition

Mutual accessibility is an equivalence relation (Def. 2.4.17), so the strong components
are its classes; the weak components are the strong components of the symmetrization
(Def. 2.4.21), hence they too form a partition of the vertex set. -/

/-- Every vertex lies in its own strong component. -/
theorem mem_strongComponent_self (X : Digraph Ω) (u : Ω) : u ∈ X.strongComponent u :=
  X.mutuallyAccessible_equivalence.refl u

/-- Strong components are the classes of an equivalence relation: if `v` lies in the
strong component of `u`, the two strong components coincide. -/
theorem strongComponent_eq_of_mem (X : Digraph Ω) {u v : Ω}
    (h : v ∈ X.strongComponent u) : X.strongComponent v = X.strongComponent u := by
  ext w
  exact ⟨fun hw => X.mutuallyAccessible_equivalence.trans h hw,
    fun hw => X.mutuallyAccessible_equivalence.trans
      (X.mutuallyAccessible_equivalence.symm h) hw⟩

/-- Two strong components are equal or disjoint. -/
theorem strongComponent_eq_or_disjoint (X : Digraph Ω) (u v : Ω) :
    X.strongComponent u = X.strongComponent v ∨
      Disjoint (X.strongComponent u) (X.strongComponent v) := by
  by_cases h : (X.strongComponent u ∩ X.strongComponent v).Nonempty
  · obtain ⟨w, hwu, hwv⟩ := h
    left
    rw [← X.strongComponent_eq_of_mem hwu, ← X.strongComponent_eq_of_mem hwv]
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 h))

/-- `u` lies in its own weak component. -/
theorem mem_weakComponent_self (X : Digraph Ω) (u : Ω) : u ∈ X.weakComponent u :=
  X.symmetrization.mem_strongComponent_self u

/-- Weak components are the classes of an equivalence relation: if `v` lies in the weak
component of `u`, the two weak components coincide. -/
theorem weakComponent_eq_of_mem (X : Digraph Ω) {u v : Ω} (h : v ∈ X.weakComponent u) :
    X.weakComponent v = X.weakComponent u :=
  X.symmetrization.strongComponent_eq_of_mem h

/-- Two weak components are equal or disjoint. -/
theorem weakComponent_eq_or_disjoint (X : Digraph Ω) (u v : Ω) :
    X.weakComponent u = X.weakComponent v ∨
      Disjoint (X.weakComponent u) (X.weakComponent v) :=
  X.symmetrization.strongComponent_eq_or_disjoint u v

/-- The set of weak components of `X`. -/
def weakComponents (X : Digraph Ω) : Set (Set Ω) := Set.range X.weakComponent

@[simp] theorem mem_weakComponents {X : Digraph Ω} {A : Set Ω} :
    A ∈ X.weakComponents ↔ ∃ u, X.weakComponent u = A := Iff.rfl

/-- Def. 2.4.21: the weak components of a digraph partition its vertex set — each
component is nonempty, distinct components are disjoint, and every vertex lies in one. -/
theorem weakComponents_nonempty (X : Digraph Ω) {A : Set Ω} (hA : A ∈ X.weakComponents) :
    A.Nonempty := by
  obtain ⟨u, rfl⟩ := hA
  exact ⟨u, X.mem_weakComponent_self u⟩

theorem weakComponents_pairwiseDisjoint (X : Digraph Ω) {A B : Set Ω}
    (hA : A ∈ X.weakComponents) (hB : B ∈ X.weakComponents) (hAB : A ≠ B) :
    Disjoint A B := by
  obtain ⟨u, rfl⟩ := hA
  obtain ⟨v, rfl⟩ := hB
  rcases X.weakComponent_eq_or_disjoint u v with h | h
  · exact absurd h hAB
  · exact h

theorem sUnion_weakComponents (X : Digraph Ω) : ⋃₀ X.weakComponents = Set.univ := by
  ext u
  exact ⟨fun _ => trivial,
    fun _ => ⟨X.weakComponent u, ⟨u, rfl⟩, X.mem_weakComponent_self u⟩⟩

/-- A digraph that is not weakly connected has at least two weak components. -/
theorem exists_ne_weakComponents (X : Digraph Ω) (h : ¬ X.IsWeaklyConnected) :
    ∃ A ∈ X.weakComponents, ∃ B ∈ X.weakComponents, A ≠ B := by
  rw [IsWeaklyConnected, IsStronglyConnected] at h
  push_neg at h
  obtain ⟨u, v, huv⟩ := h
  refine ⟨X.weakComponent u, ⟨u, rfl⟩, X.weakComponent v, ⟨v, rfl⟩, fun hc => huv ?_⟩
  have hv : v ∈ X.weakComponent u := by
    rw [hc]; exact X.mem_weakComponent_self v
  exact hv.1

/-- An edge of a digraph has both ends in one weak component. -/
theorem mem_weakComponent_of_adj (X : Digraph Ω) {u v : Ω} (h : X.Adj u v) :
    v ∈ X.weakComponent u := by
  have hacc : X.symmetrization.Accessible u v :=
    (X.symmetrization.accessible_iff_reflTransGen u v).2
      (Relation.ReflTransGen.single (Or.inl h))
  have hacc' : X.symmetrization.Accessible v u :=
    (X.symmetrization.accessible_iff_reflTransGen v u).2
      (Relation.ReflTransGen.single (Or.inr h))
  exact ⟨hacc, hacc'⟩

/-- Definition 2.4.22 (Eulerian digraph).  "A digraph `X = (Ω, E)` is *eulerian* if
`(∀ u ∈ Ω)(deg⁺(u) = deg⁻(u))`." -/
def IsEulerian (X : Digraph Ω) : Prop := ∀ u, X.outDeg u = X.inDeg u

/-- Definition 2.4.22.  "Note that a biregular digraph is necessarily eulerian; the
converse is not true." -/
theorem IsBiregular.isEulerian [Fintype Ω] {X : Digraph Ω}
    (h : X.IsBiregular) : X.IsEulerian := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact fun u => (hΩ.false u).elim
  obtain ⟨⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩ := h
  have hs := X.handshake
  have e₁ : (∑ _u : Ω, d₁) = Fintype.card Ω * d₁ := by
    simp [Finset.card_univ, mul_comm]
  have e₂ : (∑ _u : Ω, d₂) = Fintype.card Ω * d₂ := by
    simp [Finset.card_univ, mul_comm]
  have key : Fintype.card Ω * d₁ = Fintype.card Ω * d₂ := by
    rw [← e₁, ← e₂, ← Finset.sum_congr rfl (fun u _ => h₁ u),
      ← Finset.sum_congr rfl (fun u _ => h₂ u), hs.1, hs.2]
  have hd : d₁ = d₂ := Nat.eq_of_mul_eq_mul_left Fintype.card_pos key
  intro u
  rw [h₁ u, h₂ u, hd]

/-- Lemma 2.4.24 (Cuts in Eulerian digraphs).  "Let `X = (Ω, E)` be an eulerian digraph.
Then for every cut `(A,B)` we have `|E(A,B)| = |E(B,A)|`."

Paper's proof:
`|E(A,B)| - |E(B,A)| = ∑_{u ∈ A} (deg⁺(u) - deg⁻(u)) = 0`. -/
theorem card_edgesBetween_eq [Fintype Ω] {X : Digraph Ω} (h : X.IsEulerian)
    {A B : Set Ω} (hcut : X.IsCut A B) :
    (X.edgesBetween A B).ncard = (X.edgesBetween B A).ncard := by
  classical
  obtain ⟨-, -, hB⟩ := hcut
  subst hB
  -- the edges emanating from `A` split into those inside `A` and those crossing to `B`
  have hsplit1 : X.E ∩ (A ×ˢ (Set.univ : Set Ω))
      = (X.E ∩ (A ×ˢ A)) ∪ X.edgesBetween A (Set.univ \ A) := by
    ext ⟨u, v⟩
    simp only [edgesBetween, Set.mem_inter_iff, Set.mem_prod, Set.mem_union, Set.mem_univ,
      Set.mem_diff, true_and, and_true]
    tauto
  have hdisj1 : Disjoint (X.E ∩ (A ×ˢ A)) (X.edgesBetween A (Set.univ \ A)) := by
    rw [Set.disjoint_left]
    rintro ⟨u, v⟩ ⟨-, -, hv⟩ ⟨-, -, -, hv'⟩
    exact hv' hv
  have hsplit2 : X.E ∩ ((Set.univ : Set Ω) ×ˢ A)
      = (X.E ∩ (A ×ˢ A)) ∪ X.edgesBetween (Set.univ \ A) A := by
    ext ⟨u, v⟩
    simp only [edgesBetween, Set.mem_inter_iff, Set.mem_prod, Set.mem_union, Set.mem_univ,
      Set.mem_diff, true_and, and_true]
    tauto
  have hdisj2 : Disjoint (X.E ∩ (A ×ˢ A)) (X.edgesBetween (Set.univ \ A) A) := by
    rw [Set.disjoint_left]
    rintro ⟨u, v⟩ ⟨-, hu, -⟩ ⟨-, ⟨-, hu'⟩, -⟩
    exact hu' hu
  -- `∑_{u ∈ A} deg⁺(u) = ∑_{u ∈ A} deg⁻(u)` since `X` is eulerian
  have hsum : (X.E ∩ (A ×ˢ (Set.univ : Set Ω))).ncard
      = (X.E ∩ ((Set.univ : Set Ω) ×ˢ A)).ncard := by
    rw [ncard_edges_from, ncard_edges_into]
    refine Finset.sum_congr rfl fun u _ => ?_
    exact h u
  rw [hsplit1, Set.ncard_union_eq hdisj1 (Set.toFinite _) (Set.toFinite _),
    hsplit2, Set.ncard_union_eq hdisj2 (Set.toFinite _) (Set.toFinite _)] at hsum
  omega

/-- Proposition 2.4.23 (Weak is strong).  "The weak components of an eulerian digraph are
its strong components."

Paper's proof: a weakly connected eulerian digraph is strongly connected; if a weak
component `C` were not strongly connected, Prop. 2.4.20 would give a cut `(A,B)` of `C`
with `E(A,B) = ∅`, hence by Lemma 2.4.24 also `E(B,A) = ∅`, so `X̃[C]` would be
disconnected. -/
theorem weakComponent_eq_strongComponent [Fintype Ω] {X : Digraph Ω} (h : X.IsEulerian)
    (u : Ω) : X.weakComponent u = X.strongComponent u := by
  classical
  -- accessibility in `X` implies accessibility in `X̃`
  have hmono : ∀ a b : Ω, X.Accessible a b → X.symmetrization.Accessible a b := by
    intro a b hab
    rw [accessible_iff_reflTransGen] at hab ⊢
    exact hab.mono fun x y hxy => Or.inl hxy
  -- Prop. 2.4.20's construction plus Lemma 2.4.24: a set absorbing all edges that leave it
  -- also absorbs all edges that enter it, and conversely
  have closedOut : ∀ A : Set Ω, (∀ x y, x ∈ A → X.Adj x y → y ∈ A) →
      ∀ x y, y ∈ A → X.Adj x y → x ∈ A := by
    intro A hout x y hyA hxy
    by_contra hxA
    have hcut : X.IsCut A (Set.univ \ A) := ⟨⟨y, hyA⟩, ⟨x, trivial, hxA⟩, rfl⟩
    have h1 : X.edgesBetween A (Set.univ \ A) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨a, b⟩ ⟨hab, haA, hbB⟩
      exact hbB.2 (hout a b haA hab)
    have h2 := card_edgesBetween_eq h hcut
    rw [h1, Set.ncard_empty] at h2
    have h3 : X.edgesBetween (Set.univ \ A) A = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).1 h2.symm
    have hmem : ((x, y) : Ω × Ω) ∈ X.edgesBetween (Set.univ \ A) A :=
      ⟨hxy, ⟨trivial, hxA⟩, hyA⟩
    rw [h3] at hmem
    exact hmem
  have closedIn : ∀ A : Set Ω, (∀ x y, y ∈ A → X.Adj x y → x ∈ A) →
      ∀ x y, x ∈ A → X.Adj x y → y ∈ A := by
    intro A hin x y hxA hxy
    by_contra hyA
    have hcut : X.IsCut A (Set.univ \ A) := ⟨⟨x, hxA⟩, ⟨y, trivial, hyA⟩, rfl⟩
    have h1 : X.edgesBetween (Set.univ \ A) A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨a, b⟩ ⟨hab, haB, hbA⟩
      exact haB.2 (hin a b hbA hab)
    have h2 := card_edgesBetween_eq h hcut
    rw [h1, Set.ncard_empty] at h2
    have h3 : X.edgesBetween A (Set.univ \ A) = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).1 h2
    have hmem : ((x, y) : Ω × Ω) ∈ X.edgesBetween A (Set.univ \ A) :=
      ⟨hxy, hxA, ⟨trivial, hyA⟩⟩
    rw [h3] at hmem
    exact hmem
  -- a set closed under edges in both directions contains the whole weak component
  have hweak : ∀ (A : Set Ω), (∀ x y, x ∈ A → X.Adj x y → y ∈ A) →
      (∀ x y, y ∈ A → X.Adj x y → x ∈ A) →
      ∀ a b : Ω, X.WeaklyAccessible a b → a ∈ A → b ∈ A := by
    intro A hout hin a b hab haA
    have hr := X.weaklyAccessible_rel (r := fun x y => (x ∈ A ↔ y ∈ A))
      (fun _ => Iff.rfl) (fun hxy => hxy.symm) (fun hxy hyz => hxy.trans hyz)
      (fun x y hxy => ⟨fun hx => hout x y hx hxy, fun hy => hin x y hy hxy⟩) hab
    exact hr.1 haA
  have hrefl : ∀ a : Ω, X.Accessible a a := fun a => ⟨0, fun _ => a, fun i => i.elim0, rfl, rfl⟩
  ext v
  constructor
  · rintro ⟨huv, hvu⟩
    constructor
    · -- the forward-accessible set from `u` is closed in both directions
      have hout : ∀ x y, x ∈ {z | X.Accessible u z} → X.Adj x y → y ∈ {z | X.Accessible u z} :=
        fun x y hx hxy => (X.accessible_iff_reflTransGen u y).2
          (((X.accessible_iff_reflTransGen u x).1 hx).tail hxy)
      exact hweak _ hout (closedOut _ hout) u v huv (hrefl u)
    · -- and likewise the backward-accessible set
      have hin : ∀ x y, y ∈ {z | X.Accessible z u} → X.Adj x y → x ∈ {z | X.Accessible z u} :=
        fun x y hy hxy => (X.accessible_iff_reflTransGen x u).2
          (((X.accessible_iff_reflTransGen y u).1 hy).head hxy)
      exact hweak _ (closedIn _ hin) hin u v huv (hrefl u)
  · rintro ⟨huv, hvu⟩
    exact ⟨hmono u v huv, hmono v u hvu⟩

end Digraph

/-! ### §2.4.2 Bipartite graphs, semiregularity, equitable partitions -/

/-- §2.4.2.  "We use the term *bipartite graph* to denote a triple of the form
`X = (A, B; E)` where `E ⊆ A × B`.  So, in our terminology, a bipartite graph is a digraph
with the vertex set split into two parts, `A` and `B`, with all edges pointing from `A`
to `B`." -/
structure BipGraph (A B : Type*) where
  /-- The edge set `E ⊆ A × B`. -/
  E : Set (A × B)

namespace BipGraph

variable {A B : Type*}

/-- §2.4.2.  The bipartite graph `(A, B; E)` read as the digraph on `A ⊕ B` all of whose
edges point from `A` to `B`.  This is what the automorphisms and twins of `X` refer to. -/
def toDigraph (X : BipGraph A B) : Digraph (A ⊕ B) :=
  ⟨{p | ∃ a b, p.1 = Sum.inl a ∧ p.2 = Sum.inr b ∧ (a, b) ∈ X.E}⟩

/-- The automorphism group of a bipartite graph: the automorphism group of the associated
digraph on `A ⊕ B`. -/
def Aut (X : BipGraph A B) : Subgroup (Equiv.Perm (A ⊕ B)) := Digraph.Aut X.toDigraph

/-- §2.4.2 and Observation 2.5.4. Automorphisms of the bipartite triple
`(A,B;E)` preserve both parts. The full digraph group `Aut` is retained for twins. -/
def PartAut (X : BipGraph A B) : Subgroup (Equiv.Perm (A ⊕ B)) :=
  X.Aut ⊓ (Equiv.Perm.sumCongrHom A B).range

/-- The permutations induced on the two parts. -/
noncomputable def partAutParts (X : BipGraph A B) :
    X.PartAut →* Equiv.Perm A × Equiv.Perm B :=
  (MonoidHom.ofInjective Equiv.Perm.sumCongrHom_injective).symm.toMonoidHom.comp
    (Subgroup.inclusion inf_le_right)

/-- Recombining the two restrictions gives the original automorphism. -/
theorem partAutParts_spec (X : BipGraph A B) (g : X.PartAut) :
    Equiv.sumCongr (X.partAutParts g).1 (X.partAutParts g).2 = g.val :=
  MonoidHom.apply_ofInjective_symm Equiv.Perm.sumCongrHom_injective ⟨g.val, g.property.2⟩

/-- Observation 2.5.4 uses the restriction to the second part. -/
noncomputable def restrictPartB (X : BipGraph A B) : X.PartAut →* Equiv.Perm B :=
  (MonoidHom.snd _ _).comp X.partAutParts

/-- A pair of permutations preserving incidence gives a part-preserving automorphism. -/
def partAutOfPerms (X : BipGraph A B) (π : Equiv.Perm A) (σ : Equiv.Perm B)
    (h : Equiv.sumCongr π σ ∈ X.Aut) : X.PartAut :=
  ⟨Equiv.sumCongr π σ, h, ⟨(π, σ), rfl⟩⟩

@[simp] theorem partAutParts_ofPerms (X : BipGraph A B) (π : Equiv.Perm A)
    (σ : Equiv.Perm B) (h : Equiv.sumCongr π σ ∈ X.Aut) :
    X.partAutParts (X.partAutOfPerms π σ h) = (π, σ) :=
  Equiv.Perm.sumCongrHom_injective (X.partAutParts_spec _)

@[simp] theorem restrictPartB_ofPerms (X : BipGraph A B) (π : Equiv.Perm A)
    (σ : Equiv.Perm B) (h : Equiv.sumCongr π σ ∈ X.Aut) :
    X.restrictPartB (X.partAutOfPerms π σ h) = σ := by
  change (X.partAutParts (X.partAutOfPerms π σ h)).2 = σ
  rw [partAutParts_ofPerms]

/-- The restriction acts on a vertex exactly as the original permutation does. -/
theorem restrictPartB_apply (X : BipGraph A B) (g : X.PartAut) (b : B) :
    Sum.inr (X.restrictPartB g b) = g.val (Sum.inr b) :=
  Equiv.congr_fun (X.partAutParts_spec g) (Sum.inr b)

/-- §2.4.2.  "By the *degree* of vertices in `A` we mean their out-degree." -/
noncomputable def degA (X : BipGraph A B) (a : A) : ℕ := {b : B | (a, b) ∈ X.E}.ncard

/-- §2.4.2.  "…and for vertices in `B` their in-degree." -/
noncomputable def degB (X : BipGraph A B) (b : B) : ℕ := {a : A | (a, b) ∈ X.E}.ncard

/-- §2.4.2.  "We say that `X` is *semiregular* if every vertex in `A` has the same degree
and every vertex in `B` has the same degree." -/
def IsSemiregular (X : BipGraph A B) : Prop :=
  (∃ d, ∀ a, X.degA a = d) ∧ (∃ d, ∀ b, X.degB b = d)

/-- §2.4.2.  "The *trivial* bipartite graphs are the empty (`E = ∅`) and complete
(`E = A × B`) bipartite graphs." -/
def IsTrivial (X : BipGraph A B) : Prop := X.E = ∅ ∨ X.E = Set.univ

/-- §2.4.2.  "The *bipartite complement* of `X = (A,B;E)` is
`X^c = (A, B; (A × B) \ E)`." -/
def compl (X : BipGraph A B) : BipGraph A B := ⟨Set.univ \ X.E⟩

/-- §2.4.2.  "The *density* of `X` is defined as `d(X) = |E|/(|A|·|B|)`; this quantity is
between `0` and `1`."

Degenerate part: if `A` or `B` is empty this is Lean's `0 / 0 = 0`; the paper's quantity
is undefined there.  The paper's bounds are `density_nonneg_le_one`, and
`density_add_density_compl` carries `[Nonempty A] [Nonempty B]`. -/
noncomputable def density [Fintype A] [Fintype B] (X : BipGraph A B) : ℚ :=
  (X.E.ncard : ℚ) / ((Fintype.card A : ℚ) * (Fintype.card B : ℚ))

/-- §2.4.2.  "…this quantity is between `0` and `1`."  (With the convention `0/0 = 0` the
bounds also hold when a part is empty, so no nonemptiness hypothesis is needed.) -/
theorem density_nonneg_le_one [Fintype A] [Fintype B] (X : BipGraph A B) :
    0 ≤ X.density ∧ X.density ≤ 1 := by
  classical
  have hcard : (X.E.ncard : ℚ) ≤ (Fintype.card A : ℚ) * (Fintype.card B : ℚ) := by
    have h : X.E.ncard ≤ Fintype.card (A × B) := by
      rw [Set.ncard_eq_toFinset_card']
      exact Finset.card_le_univ _
    rw [Fintype.card_prod] at h
    exact_mod_cast h
  have hnn : (0 : ℚ) ≤ (Fintype.card A : ℚ) * (Fintype.card B : ℚ) := by positivity
  refine ⟨by unfold density; positivity, ?_⟩
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · unfold density
    rw [← h0, div_zero]
    norm_num
  · unfold density
    rw [div_le_one hpos]
    exact hcard

/-- §2.4.2.  "We have `d(X) + d(X^c) = 1`." -/
theorem density_add_density_compl [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (X : BipGraph A B) : X.density + X.compl.density = 1 := by
  classical
  have hcompl : X.compl.E = X.Eᶜ := by
    ext p
    simp [compl]
  have hsum : X.E.ncard + X.compl.E.ncard = Fintype.card A * Fintype.card B := by
    have h := Set.ncard_add_ncard_compl X.E
    rw [Nat.card_eq_fintype_card, Fintype.card_prod] at h
    rw [hcompl]
    exact h
  have hA : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℚ) < (Fintype.card B : ℚ) := by exact_mod_cast Fintype.card_pos
  rw [density, density, ← add_div, div_eq_one_iff_eq (by positivity)]
  exact_mod_cast hsum

/-- §2.4.2.  The degree of a vertex of `Ω₁` in the bipartite complement is
`|Ω₂| - deg(x)`. -/
theorem degA_compl [Fintype B] (X : BipGraph A B) (a : A) :
    X.compl.degA a = Fintype.card B - X.degA a := by
  classical
  have hset : {b : B | (a, b) ∈ X.compl.E} = {b : B | (a, b) ∈ X.E}ᶜ := by
    ext b
    simp [compl]
  have hsum := Set.ncard_add_ncard_compl {b : B | (a, b) ∈ X.E}
  rw [Nat.card_eq_fintype_card] at hsum
  have hdeg : X.degA a = {b : B | (a, b) ∈ X.E}.ncard := rfl
  rw [degA, hset]
  omega

/-- §2.4.2.  The degree of a vertex of `Ω₂` in the bipartite complement is
`|Ω₁| - deg(y)`. -/
theorem degB_compl [Fintype A] (X : BipGraph A B) (b : B) :
    X.compl.degB b = Fintype.card A - X.degB b := by
  classical
  have hset : {a : A | (a, b) ∈ X.compl.E} = {a : A | (a, b) ∈ X.E}ᶜ := by
    ext a
    simp [compl]
  have hsum := Set.ncard_add_ncard_compl {a : A | (a, b) ∈ X.E}
  rw [Nat.card_eq_fintype_card] at hsum
  have hdeg : X.degB b = {a : A | (a, b) ∈ X.E}.ncard := rfl
  rw [degB, hset]
  omega

/-- §2.4.2.  The bipartite complement of a semiregular bipartite graph is semiregular.
(Used in Cor. 2.4.32 and Prop. 2.4.30, where the paper passes "to the bipartite complement
if necessary".) -/
theorem IsSemiregular.compl [Fintype A] [Fintype B] {X : BipGraph A B}
    (h : X.IsSemiregular) : X.compl.IsSemiregular := by
  obtain ⟨⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩ := h
  exact ⟨⟨Fintype.card B - d₁, fun a => by rw [degA_compl, h₁ a]⟩,
    ⟨Fintype.card A - d₂, fun b => by rw [degB_compl, h₂ b]⟩⟩

/-- Definition 2.4.10 for bipartite graphs: `A₁ ∪ A₂` is independent in `X` if it
contains no edge. -/
def IsIndependentPair (X : BipGraph A B) (A₁ : Set A) (A₂ : Set B) : Prop :=
  X.E ∩ (A₁ ×ˢ A₂) = ∅

/-- Definition 2.4.25 (Induced bipartite subgraph).  "Let `X = (Ω, E)` be a digraph and
`A, B` disjoint subsets of `Ω`.  We define the *induced bipartite subgraph* `X[A,B]` as
`X[A,B] = (A, B; E(A,B))`." -/
def _root_.Babai.Digraph.inducedBip (X : Digraph Ω) (A B : Set Ω) : BipGraph A B :=
  ⟨{p | ((p.1 : Ω), (p.2 : Ω)) ∈ X.E}⟩

/-- The induced bipartite subgraph of a bipartite graph on subsets of its two parts. -/
def induced (X : BipGraph A B) (A₁ : Set A) (A₂ : Set B) : BipGraph A₁ A₂ :=
  ⟨{p | ((p.1 : A), (p.2 : B)) ∈ X.E}⟩

end BipGraph

namespace Digraph

/-- Definition 2.4.26 (Equitable partition).  "Let `X = (Ω, E)` be a digraph and
`Ω = Ω₁ ∪ … ∪ Ω_k` (disjointly) be a partition of the vertex set.  We say that this
partition is *equitable* if (a) each induced subgraph `X[Ωᵢ]` is biregular; (b) each
induced bipartite subgraph `X[Ωᵢ, Ωⱼ]` (`i ≠ j`) is semiregular." -/
structure IsEquitablePartition (X : Digraph Ω) (P : Set (Set Ω)) : Prop where
  nonempty : ∀ Δ ∈ P, Δ.Nonempty
  pairwiseDisjoint : ∀ Δ ∈ P, ∀ Δ' ∈ P, Δ ≠ Δ' → Disjoint Δ Δ'
  covers : ⋃₀ P = Set.univ
  biregular : ∀ Δ ∈ P, (X.induced Δ).IsBiregular
  semiregular : ∀ Δ ∈ P, ∀ Δ' ∈ P, Δ ≠ Δ' → (X.inducedBip Δ Δ').IsSemiregular

/-- Definition 2.4.26 (coloring).  "We say that the coloring `d : Ω → C` is *equitable* if
the partition `ker(d) = {d⁻¹(i) | i ∈ C}` is equitable." -/
def IsEquitableColoring (X : Digraph Ω) {C : Type*} (d : Ω → C) : Prop :=
  (∀ c : C, (X.induced (d ⁻¹' {c})).IsBiregular) ∧
    (∀ c c' : C, c ≠ c' → (X.inducedBip (d ⁻¹' {c}) (d ⁻¹' {c'})).IsSemiregular)

/- Remark 2.4.27.  "We shall generalize this concept to configurations in Def. 3.1.9.
Equitable partitions are the stable partitions under the naive refinement process (see
Sec. 4.1).  They play a central role in the analysis of coherent configurations (see
Sec. 3.4.3)."  The generalization is `Babai.PartitionStructure.IsEquitablePartition`
(`Coherent/Configurations.lean`); the claim about naive refinement is Obs. 4.1.1,
`Babai.ColoredDigraph.isStable_iff_isEquitableColoring` (`Refinement/Naive.lean`), which
cannot be stated here because that file imports this one. -/

end Digraph

namespace BipGraph

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- Observation 2.4.28 (b) for `Ω₁`, without the paper's non-isolatedness hypothesis.  The
hypothesis is not needed: two isolated vertices of `Ω₁` are twins and both have empty
neighborhood.  This form is what Prop. 2.4.30 uses. -/
theorem isTwin_inl_iff_aux (X : BipGraph A B) (x y : A) (hxy : x ≠ y) :
    IsTwin X.Aut (.inl x) (.inl y) ↔ {b | (x, b) ∈ X.E} = {b | (y, b) ∈ X.E} := by
  classical
  set σ : Equiv.Perm (A ⊕ B) := Equiv.swap (Sum.inl x) (Sum.inl y) with hσ
  have hinl : ∀ a : A, σ (Sum.inl a) = Sum.inl (Equiv.swap x y a) := by
    intro a
    by_cases h1 : a = x
    · subst h1; rw [hσ, Equiv.swap_apply_left, Equiv.swap_apply_left]
    by_cases h2 : a = y
    · subst h2; rw [hσ, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne (by simp [h1]) (by simp [h2]),
        Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hinr : ∀ b : B, σ (Sum.inr b) = Sum.inr b :=
    fun b => Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
  constructor
  · rintro ⟨-, hmem⟩
    have haut := Digraph.mem_aut.1 hmem
    ext b
    simp only [Set.mem_setOf_eq]
    have h := haut (Sum.inl x) (Sum.inr b)
    rw [hinl, hinr, Equiv.swap_apply_left] at h
    constructor
    · intro hb
      obtain ⟨a', b', ha', hb', hE⟩ := h.2 ⟨x, b, rfl, rfl, hb⟩
      rw [Sum.inl.injEq] at ha'
      rw [Sum.inr.injEq] at hb'
      subst ha'; subst hb'; exact hE
    · intro hb
      obtain ⟨a', b', ha', hb', hE⟩ := h.1 ⟨y, b, rfl, rfl, hb⟩
      rw [Sum.inl.injEq] at ha'
      rw [Sum.inr.injEq] at hb'
      subst ha'; subst hb'; exact hE
  · intro hnbhd
    refine ⟨by simp [hxy], Digraph.mem_aut.2 fun u v => ?_⟩
    rcases u with a | b₁ <;> rcases v with a₂ | b₂
    · rw [hinl, hinl]
      constructor
      · rintro ⟨a', b', ha', hb', -⟩; exact absurd hb' (by simp)
      · rintro ⟨a', b', ha', hb', -⟩; exact absurd hb' (by simp)
    · rw [hinl, hinr]
      constructor
      · rintro ⟨a', b', ha', hb', hE⟩
        cases ha'; cases hb'
        refine ⟨a, b₂, rfl, rfl, ?_⟩
        by_cases h1 : a = x
        · subst h1
          rw [Equiv.swap_apply_left] at hE
          have := Set.ext_iff.1 hnbhd b₂
          exact this.2 hE
        by_cases h2 : a = y
        · subst h2
          rw [Equiv.swap_apply_right] at hE
          have := Set.ext_iff.1 hnbhd b₂
          exact this.1 hE
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hE
      · rintro ⟨a', b', ha', hb', hE⟩
        cases ha'; cases hb'
        refine ⟨Equiv.swap x y a, b₂, rfl, rfl, ?_⟩
        by_cases h1 : a = x
        · subst h1
          rw [Equiv.swap_apply_left]
          exact (Set.ext_iff.1 hnbhd b₂).1 hE
        by_cases h2 : a = y
        · subst h2
          rw [Equiv.swap_apply_right]
          exact (Set.ext_iff.1 hnbhd b₂).2 hE
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hinr, hinl]
      constructor
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)
    · rw [hinr, hinr]

/-- Observation 2.4.28 (b) for `Ω₂`, without the paper's non-isolatedness hypothesis
(see `isTwin_inl_iff_aux`). -/
theorem isTwin_inr_iff_aux (X : BipGraph A B) (x y : B) (hxy : x ≠ y) :
    IsTwin X.Aut (.inr x) (.inr y) ↔ {a | (a, x) ∈ X.E} = {a | (a, y) ∈ X.E} := by
  classical
  set σ : Equiv.Perm (A ⊕ B) := Equiv.swap (Sum.inr x) (Sum.inr y) with hσ
  have hinr : ∀ b : B, σ (Sum.inr b) = Sum.inr (Equiv.swap x y b) := by
    intro b
    by_cases h1 : b = x
    · subst h1; rw [hσ, Equiv.swap_apply_left, Equiv.swap_apply_left]
    by_cases h2 : b = y
    · subst h2; rw [hσ, Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [hσ, Equiv.swap_apply_of_ne_of_ne (by simp [h1]) (by simp [h2]),
        Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hinl : ∀ a : A, σ (Sum.inl a) = Sum.inl a :=
    fun a => Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
  constructor
  · rintro ⟨-, hmem⟩
    have haut := Digraph.mem_aut.1 hmem
    ext a
    simp only [Set.mem_setOf_eq]
    have h := haut (Sum.inl a) (Sum.inr x)
    rw [hinl, hinr, Equiv.swap_apply_left] at h
    constructor
    · intro ha
      obtain ⟨a', b', ha', hb', hE⟩ := h.2 ⟨a, x, rfl, rfl, ha⟩
      rw [Sum.inl.injEq] at ha'
      rw [Sum.inr.injEq] at hb'
      subst ha'; subst hb'; exact hE
    · intro ha
      obtain ⟨a', b', ha', hb', hE⟩ := h.1 ⟨a, y, rfl, rfl, ha⟩
      rw [Sum.inl.injEq] at ha'
      rw [Sum.inr.injEq] at hb'
      subst ha'; subst hb'; exact hE
  · intro hnbhd
    refine ⟨by simp [hxy], Digraph.mem_aut.2 fun u v => ?_⟩
    rcases u with a | b₁ <;> rcases v with a₂ | b₂
    · rw [hinl, hinl]
    · rw [hinl, hinr]
      constructor
      · rintro ⟨a', b', ha', hb', hE⟩
        cases ha'; cases hb'
        refine ⟨a, b₂, rfl, rfl, ?_⟩
        by_cases h1 : b₂ = x
        · subst h1
          rw [Equiv.swap_apply_left] at hE
          exact (Set.ext_iff.1 hnbhd a).2 hE
        by_cases h2 : b₂ = y
        · subst h2
          rw [Equiv.swap_apply_right] at hE
          exact (Set.ext_iff.1 hnbhd a).1 hE
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at hE
      · rintro ⟨a', b', ha', hb', hE⟩
        cases ha'; cases hb'
        refine ⟨a, Equiv.swap x y b₂, rfl, rfl, ?_⟩
        by_cases h1 : b₂ = x
        · subst h1
          rw [Equiv.swap_apply_left]
          exact (Set.ext_iff.1 hnbhd a).1 hE
        by_cases h2 : b₂ = y
        · subst h2
          rw [Equiv.swap_apply_right]
          exact (Set.ext_iff.1 hnbhd a).2 hE
        · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hinr, hinl]
      constructor
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)
    · rw [hinr, hinr]
      constructor
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)
      · rintro ⟨a', b', ha', -, -⟩; exact absurd ha' (by simp)

/-- Observation 2.4.28 (a).  Two non-isolated vertices in different parts are never
twins. -/
theorem not_isTwin_inl_inr (X : BipGraph A B) (x : A) (y : B)
    (hx : ¬ X.toDigraph.IsIsolated (.inl x)) (hy : ¬ X.toDigraph.IsIsolated (.inr y)) :
    ¬ IsTwin X.Aut (.inl x) (.inr y) := by
  classical
  rintro ⟨-, hmem⟩
  have haut := Digraph.mem_aut.1 hmem
  -- `x` is non-isolated and no edge ends in `Ω₁`, so `x` has an out-neighbor
  obtain ⟨b, hb⟩ : ∃ b : B, (x, b) ∈ X.E := by
    by_contra hc
    push_neg at hc
    refine hx ⟨?_, ?_⟩
    · ext v
      simp only [mem_outNbr, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a', b', ha', hb', hE⟩
      rw [Sum.inl.injEq] at ha'
      subst ha'
      exact hc b' hE
    · ext v
      simp only [mem_inNbr, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a', b', -, hb', -⟩
      exact absurd hb' (by simp)
  have h := haut (Sum.inl x) (Sum.inr b)
  rw [Equiv.swap_apply_left] at h
  by_cases hby : b = y
  · subst hby
    rw [Equiv.swap_apply_right] at h
    obtain ⟨a', b', ha', -, -⟩ := h.2 ⟨x, b, rfl, rfl, hb⟩
    exact absurd ha' (by simp)
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp [hby])] at h
    obtain ⟨a', b', ha', -, -⟩ := h.2 ⟨x, b, rfl, rfl, hb⟩
    exact absurd ha' (by simp)

/-- Observation 2.4.28 (a), the other order. -/
theorem not_isTwin_inr_inl (X : BipGraph A B) (x : B) (y : A)
    (hx : ¬ X.toDigraph.IsIsolated (.inr x)) (hy : ¬ X.toDigraph.IsIsolated (.inl y)) :
    ¬ IsTwin X.Aut (.inr x) (.inl y) := by
  intro h
  exact X.not_isTwin_inl_inr y x hy hx
    ⟨h.1.symm, by rw [Equiv.swap_comm]; exact h.2⟩

/-- Observation 2.4.28 (Twins in bipartite graphs).  "Let `X = (Ω₁, Ω₂; E)` be a bipartite
graph and `x ≠ y` two non-isolated vertices.  Then `x` and `y` are twins if and only if
(a) `x, y` belong to the same part `Ωᵢ`, and (b) they have the same neighborhood in the
other part: `X̃(x) = X̃(y)` (where `X̃` denotes the symmetrization of `X`, see
Def. 2.4.16)."

The observation splits into four Lean statements.  Part (a) says that two non-isolated
vertices in different parts are never twins, in either order: `not_isTwin_inl_inr` and
`not_isTwin_inr_inl`.  Part (b) is stated once for each part: `isTwin_iff` for two
vertices of `Ω₁` and `isTwin_inr_iff` for two vertices of `Ω₂`.  Since all edges of `X`
point from `Ω₁` to `Ω₂`, the symmetrization neighborhood `X̃(x)` of a vertex `x ∈ Ω₁` is
its set of out-neighbors and that of a vertex `x ∈ Ω₂` is its set of in-neighbors. -/
theorem isTwin_iff (X : BipGraph A B) (x y : A) (hx : ¬ X.toDigraph.IsIsolated (.inl x))
    (hy : ¬ X.toDigraph.IsIsolated (.inl y)) (hxy : x ≠ y) :
    IsTwin X.Aut (.inl x) (.inl y) ↔ {b | (x, b) ∈ X.E} = {b | (y, b) ∈ X.E} :=
  isTwin_inl_iff_aux X x y hxy

/-- Observation 2.4.28 (b) for the second part `Ω₂`.  Two distinct non-isolated vertices
of `Ω₂` are twins if and only if they have the same neighborhood in `Ω₁`. -/
theorem isTwin_inr_iff (X : BipGraph A B) (x y : B) (hx : ¬ X.toDigraph.IsIsolated (.inr x))
    (hy : ¬ X.toDigraph.IsIsolated (.inr y)) (hxy : x ≠ y) :
    IsTwin X.Aut (.inr x) (.inr y) ↔ {a | (a, x) ∈ X.E} = {a | (a, y) ∈ X.E} :=
  isTwin_inr_iff_aux X x y hxy

section Defect

variable [Fintype A] [Fintype B]

open scoped Classical in
/-- Definition 2.4.29 (Symmetricity and symmetry defect in bipartite graphs).  "Let
`X = (Ω₁, Ω₂; E)` be a bipartite graph.  Let `Tᵢ` be a largest set of twins in `Ωᵢ`.  We
say that `|Tᵢ|` is the *absolute symmetricity* … of `Ωᵢ` in `X`."  This is the case
`i = 1`. -/
noncomputable def symmetricity₁ (X : BipGraph A B) : ℕ :=
  (Finset.univ.filter fun T : Finset A =>
    IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A))).sup Finset.card

open scoped Classical in
/-- Definition 2.4.29, the case `i = 2`. -/
noncomputable def symmetricity₂ (X : BipGraph A B) : ℕ :=
  (Finset.univ.filter fun T : Finset B =>
    IsTwinSet X.Aut ((fun b => Sum.inr b) '' (↑T : Set B))).sup Finset.card

/-- Definition 2.4.29.  "`|Ωᵢ \ Tᵢ|` is the *absolute symmetry defect* of `Ωᵢ` in `X`." -/
noncomputable def symDefect₁ (X : BipGraph A B) : ℕ := Fintype.card A - X.symmetricity₁

/-- Definition 2.4.29, the case `i = 2`. -/
noncomputable def symDefect₂ (X : BipGraph A B) : ℕ := Fintype.card B - X.symmetricity₂

/-- Definition 2.4.29.  "`|Tᵢ|/|Ωᵢ|` is the *relative symmetricity* … of `Ωᵢ` in `X`."

Degenerate part: if `Ωᵢ` is empty this is Lean's `0 / 0 = 0`, so `defectᵢ = 1`, outside
the paper's range; the paper assigns no value there (there is no largest set of twins in
an empty part).  Prop. 2.4.30, the only §2 result about `defectᵢ`, has hypotheses forcing
both parts nonempty. -/
noncomputable def relSymmetricity₁ (X : BipGraph A B) : ℚ :=
  (X.symmetricity₁ : ℚ) / (Fintype.card A : ℚ)

/-- Definition 2.4.29, the case `i = 2`. -/
noncomputable def relSymmetricity₂ (X : BipGraph A B) : ℚ :=
  (X.symmetricity₂ : ℚ) / (Fintype.card B : ℚ)

/-- Definition 2.4.29.  "`1 - |Tᵢ|/|Ωᵢ|` is the *relative symmetry defect* of `Ωᵢ`
in `X`."

Degenerate part: for an empty `Ωᵢ` this evaluates to `1 - 0/0 = 1`, outside the paper's
range `0 ≤ defect < 1`; see `relSymmetricity₁`. -/
noncomputable def defect₁ (X : BipGraph A B) : ℚ := 1 - X.relSymmetricity₁

/-- Definition 2.4.29, the case `i = 2`. -/
noncomputable def defect₂ (X : BipGraph A B) : ℚ := 1 - X.relSymmetricity₂

open scoped Classical in
/-- Definition 2.4.29.  A bound on every set of twins of `Ω₁` bounds `symmetricity₁`. -/
theorem two_mul_symmetricity₁_le {X : BipGraph A B}
    (h : ∀ T : Finset A, IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A)) →
      2 * T.card ≤ Fintype.card A) :
    2 * X.symmetricity₁ ≤ Fintype.card A := by
  have hs : X.symmetricity₁ ≤ Fintype.card A / 2 := by
    refine Finset.sup_le fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have := h T hT
    omega
  omega

open scoped Classical in
/-- Definition 2.4.29.  A bound on every set of twins of `Ω₂` bounds `symmetricity₂`. -/
theorem two_mul_symmetricity₂_le {X : BipGraph A B}
    (h : ∀ T : Finset B, IsTwinSet X.Aut ((fun b => Sum.inr b) '' (↑T : Set B)) →
      2 * T.card ≤ Fintype.card B) :
    2 * X.symmetricity₂ ≤ Fintype.card B := by
  have hs : X.symmetricity₂ ≤ Fintype.card B / 2 := by
    refine Finset.sup_le fun T hT => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have := h T hT
    omega
  omega

/-- `2 s₁ ≤ |Ω₁|` is the integer form of "the symmetry defect of `Ω₁` is `≥ 1/2`". -/
theorem half_le_defect₁ {X : BipGraph A B} (h : 2 * X.symmetricity₁ ≤ Fintype.card A) :
    1 / 2 ≤ X.defect₁ := by
  rcases Nat.eq_zero_or_pos (Fintype.card A) with h0 | hpos
  · have hs : X.symmetricity₁ = 0 := by omega
    rw [defect₁, relSymmetricity₁, hs, h0]
    norm_num
  · have hn : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hpos
    have hle : (X.symmetricity₁ : ℚ) / (Fintype.card A : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      have : (2 : ℚ) * (X.symmetricity₁ : ℚ) ≤ (Fintype.card A : ℚ) := by exact_mod_cast h
      linarith
    rw [defect₁, relSymmetricity₁]
    linarith

/-- `2 s₂ ≤ |Ω₂|` is the integer form of "the symmetry defect of `Ω₂` is `≥ 1/2`". -/
theorem half_le_defect₂ {X : BipGraph A B} (h : 2 * X.symmetricity₂ ≤ Fintype.card B) :
    1 / 2 ≤ X.defect₂ := by
  rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | hpos
  · have hs : X.symmetricity₂ = 0 := by omega
    rw [defect₂, relSymmetricity₂, hs, h0]
    norm_num
  · have hn : (0 : ℚ) < (Fintype.card B : ℚ) := by exact_mod_cast hpos
    have hle : (X.symmetricity₂ : ℚ) / (Fintype.card B : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      have : (2 : ℚ) * (X.symmetricity₂ : ℚ) ≤ (Fintype.card B : ℚ) := by exact_mod_cast h
      linarith
    rw [defect₂, relSymmetricity₂]
    linarith

/-- A set of twins in `Ω₁` is contained in the neighborhood of any neighbor of any of its
points, so it has at most `d₂` elements (the paper's `|T| ≤ deg(y)`). -/
theorem twinSet₁_card_le {X : BipGraph A B} {T : Finset A}
    (hT : IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A))) {d₁ d₂ : ℕ}
    (h₁ : ∀ a, X.degA a = d₁) (hd₁ : 0 < d₁) (h₂ : ∀ b, X.degB b = d₂) : T.card ≤ d₂ := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have hNx : 0 < {b : B | (x, b) ∈ X.E}.ncard := by
      rw [show {b : B | (x, b) ∈ X.E}.ncard = d₁ from h₁ x]; exact hd₁
    obtain ⟨y, hy⟩ := (Set.ncard_pos (Set.toFinite _)).1 hNx
    have hsub : (↑T : Set A) ⊆ {a : A | (a, y) ∈ X.E} := by
      intro a ha
      by_cases hax : a = x
      · subst hax; exact hy
      · have htwin : IsTwin X.Aut (Sum.inl x) (Sum.inl a) :=
          hT _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩ (by simp [Ne.symm hax])
        have heq := (isTwin_inl_iff_aux X x a (Ne.symm hax)).1 htwin
        exact (Set.ext_iff.1 heq y).1 hy
    calc T.card = (↑T : Set A).ncard := (Set.ncard_coe_finset T).symm
      _ ≤ {a : A | (a, y) ∈ X.E}.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = d₂ := h₂ y

/-- The mirror of `twinSet₁_card_le` for `Ω₂`. -/
theorem twinSet₂_card_le {X : BipGraph A B} {T : Finset B}
    (hT : IsTwinSet X.Aut ((fun b => Sum.inr b) '' (↑T : Set B))) {d₁ d₂ : ℕ}
    (h₂ : ∀ b, X.degB b = d₂) (hd₂ : 0 < d₂) (h₁ : ∀ a, X.degA a = d₁) : T.card ≤ d₁ := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp
  · have hNy : 0 < {a : A | (a, y) ∈ X.E}.ncard := by
      rw [show {a : A | (a, y) ∈ X.E}.ncard = d₂ from h₂ y]; exact hd₂
    obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).1 hNy
    have hsub : (↑T : Set B) ⊆ {b : B | (x, b) ∈ X.E} := by
      intro b hb
      by_cases hby : b = y
      · subst hby; exact hx
      · have htwin : IsTwin X.Aut (Sum.inr y) (Sum.inr b) :=
          hT _ ⟨y, hy, rfl⟩ _ ⟨b, hb, rfl⟩ (by simp [Ne.symm hby])
        have heq := (isTwin_inr_iff_aux X y b (Ne.symm hby)).1 htwin
        exact (Set.ext_iff.1 heq x).1 hx
    calc T.card = (↑T : Set B).ncard := (Set.ncard_coe_finset T).symm
      _ ≤ {b : B | (x, b) ∈ X.E}.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = d₁ := h₁ x

/-- A set of twins of `Ω₁` in `X` is a set of twins of `Ω₁` in the bipartite complement
(their neighborhoods are complementary).  This is what makes the paper's "by taking the
bipartite complement if necessary" legitimate: it changes neither `symmetricity₁` nor
`symmetricity₂`. -/
theorem isTwinSet_compl₁ {X : BipGraph A B} {T : Finset A}
    (hT : IsTwinSet X.Aut ((fun a => Sum.inl a) '' (↑T : Set A))) :
    IsTwinSet X.compl.Aut ((fun a => Sum.inl a) '' (↑T : Set A)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  have hxy : x ≠ y := fun h => hne (by rw [h])
  refine (isTwin_inl_iff_aux X.compl x y hxy).2 ?_
  have heq := (isTwin_inl_iff_aux X x y hxy).1 (hT _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne)
  ext b
  simp only [Set.mem_setOf_eq, compl, Set.mem_diff, Set.mem_univ, true_and]
  exact not_congr (Set.ext_iff.1 heq b)

/-- The mirror of `isTwinSet_compl₁` for `Ω₂`. -/
theorem isTwinSet_compl₂ {X : BipGraph A B} {T : Finset B}
    (hT : IsTwinSet X.Aut ((fun b => Sum.inr b) '' (↑T : Set B))) :
    IsTwinSet X.compl.Aut ((fun b => Sum.inr b) '' (↑T : Set B)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
  have hxy : x ≠ y := fun h => hne (by rw [h])
  refine (isTwin_inr_iff_aux X.compl x y hxy).2 ?_
  have heq := (isTwin_inr_iff_aux X x y hxy).1 (hT _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne)
  ext a
  simp only [Set.mem_setOf_eq, compl, Set.mem_diff, Set.mem_univ, true_and]
  exact not_congr (Set.ext_iff.1 heq a)

/-- Proposition 2.4.30 (Symmetry defect of semiregular bipartite graphs).  "The symmetry
defect of each part of a nontrivial semiregular bipartite graph is `≥ 1/2`."

Paper's proof: by taking the bipartite complement if necessary we may assume the density
is `≤ 1/2`; a vertex `x` of a set `T` of twins in `Ωᵢ` has a neighbor `y` in the other
part, and then `X(y) ⊇ T`, so `|T| ≤ deg(y) ≤ |Ωᵢ|/2`.

The passage to the bipartite complement is `isTwinSet_compl₁`/`isTwinSet_compl₂` (a set of
twins of `X` is a set of twins of `X^c`), and "density `≤ 1/2`" is the integer condition
`2 d₂ ≤ |Ω₁|` (resp. `2 d₁ ≤ |Ω₂|`), on which the proof splits. -/
theorem defect_ge_half {X : BipGraph A B} (hnt : ¬ X.IsTrivial) (hsr : X.IsSemiregular) :
    1 / 2 ≤ X.defect₁ ∧ 1 / 2 ≤ X.defect₂ := by
  classical
  obtain ⟨⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩ := hsr
  have h₁c : ∀ a, X.compl.degA a = Fintype.card B - d₁ := fun a => by
    rw [degA_compl, h₁ a]
  have h₂c : ∀ b, X.compl.degB b = Fintype.card A - d₂ := fun b => by
    rw [degB_compl, h₂ b]
  -- `X` is non-empty, so every vertex of `Ω₁` has a neighbor
  have hd₁ : 0 < d₁ := by
    rcases Nat.eq_zero_or_pos d₁ with h0 | h
    · refine absurd (Or.inl ?_ : X.IsTrivial) hnt
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ⟨a, b⟩ he
      have hpos : 0 < {b : B | (a, b) ∈ X.E}.ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨b, he⟩
      rw [show {b : B | (a, b) ∈ X.E}.ncard = d₁ from h₁ a, h0] at hpos
      omega
    · exact h
  -- `X` is not complete, so every vertex of `Ω₁` has a non-neighbor
  have hd₁c : 0 < Fintype.card B - d₁ := by
    rcases Nat.eq_zero_or_pos (Fintype.card B - d₁) with h0 | h
    · refine absurd (Or.inr ?_ : X.IsTrivial) hnt
      rw [Set.eq_univ_iff_forall]
      rintro ⟨a, b⟩
      by_contra hc
      have hpos : 0 < {b : B | (a, b) ∈ X.compl.E}.ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨b, ⟨Set.mem_univ _, hc⟩⟩
      rw [show {b : B | (a, b) ∈ X.compl.E}.ncard = Fintype.card B - d₁ from h₁c a,
        h0] at hpos
      omega
    · exact h
  -- both parts are non-empty
  have hA : Nonempty A := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    refine hnt (Or.inl ?_)
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ -
    exact hc.false a
  obtain ⟨a₀⟩ := hA
  have hB : Nonempty B := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have hz : {b : B | (a₀, b) ∈ X.E}.ncard = 0 := by
      rw [show {b : B | (a₀, b) ∈ X.E} = ∅ from
        Set.eq_empty_iff_forall_notMem.2 fun b _ => hc.false b]
      simp
    rw [show {b : B | (a₀, b) ∈ X.E}.ncard = d₁ from h₁ a₀] at hz
    omega
  obtain ⟨b₀⟩ := hB
  have hd₁le : d₁ ≤ Fintype.card B := by
    rw [← h₁ a₀]
    calc {b : B | (a₀, b) ∈ X.E}.ncard ≤ (Set.univ : Set B).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = Fintype.card B := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hd₂le : d₂ ≤ Fintype.card A := by
    rw [← h₂ b₀]
    calc {a : A | (a, b₀) ∈ X.E}.ncard ≤ (Set.univ : Set A).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = Fintype.card A := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  -- every vertex of `Ω₂` has a neighbor and a non-neighbor
  have hd₂ : 0 < d₂ := by
    have hpos : 0 < {b : B | (a₀, b) ∈ X.E}.ncard := by
      rw [show {b : B | (a₀, b) ∈ X.E}.ncard = d₁ from h₁ a₀]; exact hd₁
    obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    have h0 : 0 < {a : A | (a, b) ∈ X.E}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨a₀, hb⟩
    rwa [show {a : A | (a, b) ∈ X.E}.ncard = d₂ from h₂ b] at h0
  have hd₂c : 0 < Fintype.card A - d₂ := by
    have hpos : 0 < {b : B | (a₀, b) ∈ X.compl.E}.ncard := by
      rw [show {b : B | (a₀, b) ∈ X.compl.E}.ncard = Fintype.card B - d₁ from h₁c a₀]
      exact hd₁c
    obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    have h0 : 0 < {a : A | (a, b) ∈ X.compl.E}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨a₀, hb⟩
    rwa [show {a : A | (a, b) ∈ X.compl.E}.ncard = Fintype.card A - d₂ from h₂c b] at h0
  constructor
  · -- `Ω₁`: use `X` when the density is `≤ 1/2`, the bipartite complement otherwise
    refine half_le_defect₁ (two_mul_symmetricity₁_le fun T hT => ?_)
    by_cases hdens : 2 * d₂ ≤ Fintype.card A
    · have := twinSet₁_card_le hT h₁ hd₁ h₂
      omega
    · have := twinSet₁_card_le (isTwinSet_compl₁ hT) h₁c hd₁c h₂c
      omega
  · -- `Ω₂`, symmetrically
    refine half_le_defect₂ (two_mul_symmetricity₂_le fun T hT => ?_)
    by_cases hdens : 2 * d₁ ≤ Fintype.card B
    · have := twinSet₂_card_le hT h₂ hd₂ h₁
      omega
    · have := twinSet₂_card_le (isTwinSet_compl₂ hT) h₂c hd₂c h₁c
      omega

/-- Proposition 2.4.31 (Independent sets in semiregular bipartite graphs).  "Let
`X = (Ω₁, Ω₂; E)` be a non-empty semiregular bipartite graph.  Let `Aᵢ ⊆ Ωᵢ` (`i = 1,2`).
If `A₁ ∪ A₂` is an independent set in `X` then the relative sizes of the `Aᵢ` add up to
`≤ 1`, i.e. `|A₁|/|Ω₁| + |A₂|/|Ω₂| ≤ 1`"   (Eq. (13)).

Paper's proof: all edges emanating from `A₁` are absorbed by `Ω₂ \ A₂`, so
`d₁|A₁| ≤ d₂(|Ω₂| - |A₂|)`; divide by `|E| = d₁|Ω₁| = d₂|Ω₂|`. -/
theorem independent_sum_le_one {X : BipGraph A B} (hne : X.E ≠ ∅) (hsr : X.IsSemiregular)
    {A₁ : Set A} {A₂ : Set B} (hind : X.IsIndependentPair A₁ A₂) :
    (A₁.ncard : ℚ) / (Fintype.card A : ℚ) + (A₂.ncard : ℚ) / (Fintype.card B : ℚ) ≤ 1 := by
  classical
  obtain ⟨⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩ := hsr
  -- `|E| = d₁|Ω₁| = d₂|Ω₂|`
  have hEA : X.E.ncard = Fintype.card A * d₁ := by
    have hsum := Digraph.ncard_edges_from X.E (Set.univ : Set A)
    rw [Set.univ_prod_univ, Set.inter_univ] at hsum
    rw [hsum]
    have hval : ∀ a : A, {y : B | (a, y) ∈ X.E}.ncard = d₁ := fun a => h₁ a
    rw [Finset.sum_congr rfl (fun a _ => hval a), Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card', Set.ncard_univ, Nat.card_eq_fintype_card]
  have hEB : X.E.ncard = Fintype.card B * d₂ := by
    have hsum := Digraph.ncard_edges_into X.E (Set.univ : Set B)
    rw [Set.univ_prod_univ, Set.inter_univ] at hsum
    rw [hsum]
    have hval : ∀ b : B, {y : A | (y, b) ∈ X.E}.ncard = d₂ := fun b => h₂ b
    rw [Finset.sum_congr rfl (fun b _ => hval b), Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card', Set.ncard_univ, Nat.card_eq_fintype_card]
  -- "all edges emanating from `A₁` are absorbed by `Ω₂ \ A₂`"
  have hsub : X.E ∩ (A₁ ×ˢ (Set.univ : Set B)) ⊆ X.E ∩ ((Set.univ : Set A) ×ˢ A₂ᶜ) := by
    rintro ⟨a, b⟩ ⟨he, ha, -⟩
    refine ⟨he, Set.mem_univ _, fun hb => ?_⟩
    have hmem : ((a, b) : A × B) ∈ X.E ∩ (A₁ ×ˢ A₂) := ⟨he, ha, hb⟩
    rw [IsIndependentPair] at hind
    rw [hind] at hmem
    exact hmem
  have hlhs : (X.E ∩ (A₁ ×ˢ (Set.univ : Set B))).ncard = A₁.ncard * d₁ := by
    rw [Digraph.ncard_edges_from]
    have hval : ∀ a : A, {y : B | (a, y) ∈ X.E}.ncard = d₁ := fun a => h₁ a
    rw [Finset.sum_congr rfl (fun a _ => hval a), Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card']
  have hrhs : (X.E ∩ ((Set.univ : Set A) ×ˢ A₂ᶜ)).ncard = (A₂ᶜ : Set B).ncard * d₂ := by
    rw [Digraph.ncard_edges_into]
    have hval : ∀ b : B, {y : A | (y, b) ∈ X.E}.ncard = d₂ := fun b => h₂ b
    rw [Finset.sum_congr rfl (fun b _ => hval b), Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card']
  -- Eq. (14): `d₁|A₁| ≤ d₂(|Ω₂| - |A₂|)`
  have hcount : A₁.ncard * d₁ ≤ (A₂ᶜ : Set B).ncard * d₂ := by
    rw [← hlhs, ← hrhs]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hsplit : (A₂ᶜ : Set B).ncard * d₂ + A₂.ncard * d₂ = Fintype.card B * d₂ := by
    rw [← add_mul]
    congr 1
    have := Set.ncard_add_ncard_compl A₂
    rw [Nat.card_eq_fintype_card] at this
    omega
  have hEq : Fintype.card B * d₂ = Fintype.card A * d₁ := by rw [← hEB, hEA]
  have hnat : A₁.ncard * d₁ + A₂.ncard * d₂ ≤ Fintype.card A * d₁ := by
    rw [← hEq, ← hsplit]
    exact Nat.add_le_add_right hcount _
  -- positivity of the parameters
  have hEpos : 0 < X.E.ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 (Set.nonempty_iff_ne_empty.2 hne)
  have hnA : 0 < Fintype.card A := by
    rcases Nat.eq_zero_or_pos (Fintype.card A) with h0 | h
    · rw [h0, zero_mul] at hEA; omega
    · exact h
  have hnB : 0 < Fintype.card B := by
    rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | h
    · rw [h0, zero_mul] at hEB; omega
    · exact h
  have hd₁ : 0 < d₁ := by
    rcases Nat.eq_zero_or_pos d₁ with h0 | h
    · rw [h0, mul_zero] at hEA; omega
    · exact h
  -- divide Eq. (14) by `|E|`
  have key : (A₁.ncard : ℚ) * d₁ + (A₂.ncard : ℚ) * d₂ ≤ (Fintype.card A : ℚ) * d₁ := by
    exact_mod_cast hnat
  have hEqq : (Fintype.card B : ℚ) * d₂ = (Fintype.card A : ℚ) * d₁ := by exact_mod_cast hEq
  have hnAq : (0 : ℚ) < (Fintype.card A : ℚ) := by exact_mod_cast hnA
  have hnBq : (0 : ℚ) < (Fintype.card B : ℚ) := by exact_mod_cast hnB
  have hd₁q : (0 : ℚ) < (d₁ : ℚ) := by exact_mod_cast hd₁
  rw [div_add_div _ _ (ne_of_gt hnAq) (ne_of_gt hnBq), div_le_one (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right key (le_of_lt hnBq), hEqq, hnAq, hnBq, hd₁q]

/-- Corollary 2.4.32 (Trivial subgraphs in semiregular bipartite graphs).  "Let
`X = (Ω₁, Ω₂; E)` be a nontrivial semiregular bipartite graph.  Let `Aᵢ ⊆ Ωᵢ`
(`i = 1,2`).  If the induced bipartite subgraph `X[A₁, A₂]` is trivial (empty or complete)
then inequality (13) holds."

Paper's proof: apply Prop. 2.4.31 to `X` and to its bipartite complement. -/
theorem trivial_subgraph_sum_le_one {X : BipGraph A B} (hnt : ¬ X.IsTrivial)
    (hsr : X.IsSemiregular) {A₁ : Set A} {A₂ : Set B}
    (htriv : (X.induced A₁ A₂).IsTrivial) :
    (A₁.ncard : ℚ) / (Fintype.card A : ℚ) + (A₂.ncard : ℚ) / (Fintype.card B : ℚ) ≤ 1 := by
  rcases htriv with hempty | hfull
  · -- `X[A₁,A₂]` is empty: `A₁ ∪ A₂` is independent in `X`, apply Prop. 2.4.31 to `X`
    refine independent_sum_le_one (fun h => hnt (Or.inl h)) hsr ?_
    rw [IsIndependentPair, Set.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ ⟨he, ha, hb⟩
    have hmem : ((⟨a, ha⟩, ⟨b, hb⟩) : A₁ × A₂) ∈ (X.induced A₁ A₂).E := he
    rw [hempty] at hmem
    exact hmem
  · -- `X[A₁,A₂]` is complete: `A₁ ∪ A₂` is independent in the bipartite complement
    have hcompl : X.compl.E ≠ ∅ := by
      intro h
      refine hnt (Or.inr ?_)
      ext p
      simp only [Set.mem_univ, iff_true]
      by_contra hc
      have hmem : p ∈ X.compl.E := ⟨Set.mem_univ _, hc⟩
      rw [h] at hmem
      exact hmem
    refine independent_sum_le_one hcompl (hsr.compl) ?_
    rw [IsIndependentPair, Set.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ ⟨he, ha, hb⟩
    have hmem : ((⟨a, ha⟩, ⟨b, hb⟩) : A₁ × A₂) ∈ (X.induced A₁ A₂).E := by
      rw [hfull]; exact Set.mem_univ _
    exact he.2 hmem

end Defect

end BipGraph

/-! ### Corollary 2.4.12 and Examples 2.4.15 -/

namespace Digraph

variable [Fintype Ω] [DecidableEq Ω]

/-- Corollary 2.4.12 (Symmetry defect of biregular digraphs).  "The symmetry defect of any
nontrivial irreflexive biregular digraph is `≥ 1/2`."

Paper's proof: a set `A` of twins satisfies `Aut(X) ≥ S(A)`, hence `A` is either
independent in `X` or independent in the irreflexive complement of `X`; in each case
Prop. 2.4.11 gives `|A| ≤ n/2`. -/
theorem defect_biregular_ge_half {X : Digraph Ω} (hnt : ¬ X.IsTrivial)
    (hirr : X.IsIrreflexive) (hreg : X.IsBiregular) : 1 / 2 ≤ defect (Aut X) := by
  classical
  have hXne : ¬ X.IsEmpty := fun h => hnt (isTrivial_of_isEmpty h)
  have hCne : ¬ X.compl.IsEmpty := fun h => hnt (isTrivial_of_compl_isEmpty hirr h)
  have hCreg : X.compl.IsBiregular := hreg.compl hirr
  have hcard2 : 2 ≤ Fintype.card Ω := by
    by_contra hc
    push_neg at hc
    refine hnt ((Subgroup.eq_top_iff' _).2 fun σ => ?_)
    have : Subsingleton Ω := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    have hσ : σ = 1 := Equiv.ext fun x => Subsingleton.elim _ _
    rw [hσ]
    exact one_mem _
  refine half_le_defect (two_mul_symmetricity_le fun Ψ hΨ => ?_)
  by_cases hsmall : Ψ.card ≤ 1
  · omega
  push_neg at hsmall
  by_cases hedge : ∃ a ∈ Ψ, ∃ b ∈ Ψ, (a, b) ∈ X.E
  · -- some pair of twins is an edge, so every pair is: `Ψ` is independent in `X̄`
    obtain ⟨a, ha, b, hb, hab⟩ := hedge
    have hne : a ≠ b := by
      rintro rfl
      have hmem : ((a, a) : Ω × Ω) ∈ X.E ∩ diag Ω := ⟨hab, rfl⟩
      rw [show X.E ∩ diag Ω = ∅ from hirr] at hmem
      exact hmem
    have hind : X.compl.IsIndependent (↑Ψ : Set Ω) := by
      rw [IsIndependent, Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨hp, hu, hv⟩
      have hu' : u ∈ (↑Ψ : Set Ω) := hu
      have hv' : v ∈ (↑Ψ : Set Ω) := hv
      have huv : u ≠ v := by
        rintro rfl
        exact hp.2 (Or.inl rfl)
      obtain ⟨σ, hσ, hσa, hσb⟩ :=
        exists_symOn_map_pair (Ψ := (↑Ψ : Set Ω)) ha hb hu' hv' hne huv
      have hσAut : σ ∈ Aut X := (isTwinSet_iff_symOn_le (Aut X) (↑Ψ : Set Ω)).1 hΨ hσ
      have : (u, v) ∈ X.E := by
        rw [← hσa, ← hσb]
        exact (hσAut a b).2 hab
      exact hp.2 (Or.inr this)
    have h := ncard_independent_le hCne hCreg hind
    rwa [Set.ncard_coe_finset] at h
  · -- no pair of twins is an edge: `Ψ` is independent in `X`
    push_neg at hedge
    have hind : X.IsIndependent (↑Ψ : Set Ω) := by
      rw [IsIndependent, Set.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ ⟨hp, hu, hv⟩
      exact hedge u hu v hv hp
    have h := ncard_independent_le hXne hreg hind
    rwa [Set.ncard_coe_finset] at h

end Digraph

/-- Examples 2.4.15.  "The pentagon is SR with parameters `(5, 2, 0, 1)`."  The pentagon
is the cycle `C₅`: vertices `Fin 5`, with `i` adjacent to `i ± 1`. -/
def pentagon : Digraph (Fin 5) := ⟨{p | p.2 = p.1 + 1 ∨ p.1 = p.2 + 1}⟩

/-- Auxiliary for Examples 2.4.15: the size of a set of a finite type, computed from an
explicit `Finset` with the same elements. -/
private theorem ncard_eq_of_iff {α : Type*} (s : Set α) (f : Finset α)
    (h : ∀ x, x ∈ s ↔ x ∈ f) : s.ncard = f.card := by
  rw [show s = (↑f : Set α) from Set.ext fun x => (h x).trans (by simp)]
  exact Set.ncard_coe_finset f

/-- Examples 2.4.15, first example. -/
theorem pentagon_sr : pentagon.IsStronglyRegular 5 2 0 1 := by
  have hmem : ∀ u z : Fin 5, z ∈ outNbr pentagon.E u ↔ (z = u + 1 ∨ u = z + 1) :=
    fun _ _ => Iff.rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext ⟨a, b⟩
    simp only [pentagon, Set.mem_inter_iff, Set.mem_setOf_eq, mem_diag,
      Set.mem_empty_iff_false, iff_false, not_and]
    revert a b
    decide
  · ext ⟨a, b⟩
    simp only [pentagon, mem_invRel, Set.mem_setOf_eq]
    revert a b
    decide
  · decide
  · intro u
    show (outNbr pentagon.E u).ncard = 2
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : Fin 5 => z = u + 1 ∨ u = z + 1)
        (fun z => by rw [hmem]; simp)]
    revert u
    decide
  · intro u v huv
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : Fin 5 =>
        (z = u + 1 ∨ u = z + 1) ∧ (z = v + 1 ∨ v = z + 1))
      (fun z => by simp only [Set.mem_inter_iff, hmem, Finset.mem_filter, Finset.mem_univ,
        true_and])]
    revert huv
    show (v = u + 1 ∨ u = v + 1) → _
    revert u v
    decide
  · intro u v huv hadj
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : Fin 5 =>
        (z = u + 1 ∨ u = z + 1) ∧ (z = v + 1 ∨ v = z + 1))
      (fun z => by simp only [Set.mem_inter_iff, hmem, Finset.mem_filter, Finset.mem_univ,
        true_and])]
    revert hadj
    revert huv
    show u ≠ v → ¬ (v = u + 1 ∨ u = v + 1) → _
    revert u v
    decide

/-- Examples 2.4.15.  "Petersen's graph is SR with parameters `(10, 3, 0, 1)`."  Petersen's
graph is the Kneser graph on the `2`-subsets of a `5`-set: two `2`-subsets are adjacent
exactly if they are disjoint. -/
def petersen : Digraph (binom (Fin 5) 2) :=
  ⟨{p | Disjoint (p.1 : Finset (Fin 5)) (p.2 : Finset (Fin 5))}⟩

/-- Examples 2.4.15, second example. -/
theorem petersen_sr : petersen.IsStronglyRegular 10 3 0 1 := by
  have hmem : ∀ u z : binom (Fin 5) 2,
      z ∈ outNbr petersen.E u ↔ Disjoint (u : Finset (Fin 5)) (z : Finset (Fin 5)) :=
    fun _ _ => Iff.rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext ⟨a, b⟩
    simp only [petersen, Set.mem_inter_iff, Set.mem_setOf_eq, mem_diag,
      Set.mem_empty_iff_false, iff_false, not_and]
    revert a b
    decide
  · ext ⟨a, b⟩
    simp only [petersen, mem_invRel, Set.mem_setOf_eq]
    revert a b
    decide
  · decide
  · intro u
    show (outNbr petersen.E u).ncard = 3
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : binom (Fin 5) 2 =>
        Disjoint (u : Finset (Fin 5)) (z : Finset (Fin 5)))
      (fun z => by rw [hmem]; simp)]
    revert u
    decide
  · intro u v huv
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : binom (Fin 5) 2 =>
        Disjoint (u : Finset (Fin 5)) (z : Finset (Fin 5)) ∧
          Disjoint (v : Finset (Fin 5)) (z : Finset (Fin 5)))
      (fun z => by simp only [Set.mem_inter_iff, hmem, Finset.mem_filter, Finset.mem_univ,
        true_and])]
    revert huv
    show Disjoint (u : Finset (Fin 5)) (v : Finset (Fin 5)) → _
    revert u v
    decide
  · intro u v huv hadj
    rw [ncard_eq_of_iff _ (Finset.univ.filter fun z : binom (Fin 5) 2 =>
        Disjoint (u : Finset (Fin 5)) (z : Finset (Fin 5)) ∧
          Disjoint (v : Finset (Fin 5)) (z : Finset (Fin 5)))
      (fun z => by simp only [Set.mem_inter_iff, hmem, Finset.mem_filter, Finset.mem_univ,
        true_and])]
    revert hadj
    revert huv
    show u ≠ v → ¬ Disjoint (u : Finset (Fin 5)) (v : Finset (Fin 5)) → _
    revert u v
    decide

/-- Examples 2.4.15.  "An `n`-clique is SR with parameters `(n, n-1, n-2, *)`, where `*`
can be any number."  (There are no distinct non-adjacent vertices in a clique, so the
last parameter is unconstrained.) -/
theorem clique_sr [Fintype Ω] [DecidableEq Ω] (mu : ℕ) :
    (Digraph.completeIrreflexive Ω).IsStronglyRegular
      (Fintype.card Ω) (Fintype.card Ω - 1) (Fintype.card Ω - 2) mu := by
  classical
  have hmem : ∀ u z : Ω, z ∈ outNbr (Digraph.completeIrreflexive Ω).E u ↔ u ≠ z := by
    intro u z
    simp only [mem_outNbr, Digraph.completeIrreflexive, Set.mem_diff, Set.mem_univ, true_and,
      mem_diag]
  refine ⟨⟨?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · ext ⟨a, b⟩
    simp only [Digraph.completeIrreflexive, Set.mem_inter_iff, Set.mem_diff, Set.mem_univ,
      true_and, mem_diag, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun h => h
  · ext ⟨a, b⟩
    simp only [Digraph.completeIrreflexive, mem_invRel, Set.mem_diff, Set.mem_univ, true_and,
      mem_diag]
    exact not_congr eq_comm
  · intro u
    show (outNbr (Digraph.completeIrreflexive Ω).E u).ncard = Fintype.card Ω - 1
    have hset : outNbr (Digraph.completeIrreflexive Ω).E u = ({u} : Set Ω)ᶜ := by
      ext z
      rw [hmem]
      simp [eq_comm, Set.mem_compl_iff]
    have hsum := Set.ncard_add_ncard_compl ({u} : Set Ω)
    rw [Nat.card_eq_fintype_card, Set.ncard_singleton] at hsum
    rw [hset]
    omega
  · intro u v hadj
    have huv : u ≠ v := by
      intro h
      have : ((u, v) : Ω × Ω) ∈ (Digraph.completeIrreflexive Ω).E := hadj
      exact this.2 h
    have hset : outNbr (Digraph.completeIrreflexive Ω).E u ∩
        outNbr (Digraph.completeIrreflexive Ω).E v = ({u, v} : Set Ω)ᶜ := by
      ext z
      simp only [Set.mem_inter_iff, hmem, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ⟨fun hz => h.1 hz.symm, fun hz => h.2 hz.symm⟩,
        fun h => ⟨fun hz => h.1 hz.symm, fun hz => h.2 hz.symm⟩⟩
    have hsum := Set.ncard_add_ncard_compl ({u, v} : Set Ω)
    rw [Nat.card_eq_fintype_card, Set.ncard_pair huv] at hsum
    rw [hset]
    omega
  · intro u v huv hadj
    exact absurd (show ((u, v) : Ω × Ω) ∈ (Digraph.completeIrreflexive Ω).E from
      ⟨Set.mem_univ _, huv⟩) hadj

end Babai
