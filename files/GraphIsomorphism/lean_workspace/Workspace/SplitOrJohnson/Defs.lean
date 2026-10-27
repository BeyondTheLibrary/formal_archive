/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9: Breaking symmetry: Split-or-Johnson.  Definitions and the categories in which
the canonicity of Section 9 is stated.
-/
import Workspace.Functors.Compose
import Workspace.ColoredPartitions.Basic
import Workspace.Coherent.Classes
import Workspace.Machine.TimeClasses

/-!
# §9 Split-or-Johnson: the objects and the categories

Version 2.5, lines 3900–4355 of `babai-gi-source/quasi25.txt`.

§9.2: *"In each result in this section, canonicity involves a combination of the following
categories (cf. Section 6): binary relational structures (Theorem 9.2.1), vertex-colored
bipartite graphs (Theorem 9.2.2), k-ary relational structures (Theorem 9.2.3), and the
category of colored partitions in each result."*

This file sets up those categories as objects of `Babai.Cat` (§6), together with the
common shape of the conclusions of Theorems 9.2.1–9.2.3:

> *"at (quasipolynomial) multiplicative cost we can find either (a) a canonical colored
> `α`-partition of `V`, or (b) a canonically embedded nontrivial Johnson scheme on a
> subset of `V` of size `≥ α|V|`."*

## Numbering map

| Paper | Lean |
|---|---|
| full subcategory of admissible inputs | `Babai.Cat.full` (`Workspace/Functors/Compose.lean`) |
| the category of the two possible outputs | `Babai.Cat.sum` (`Workspace/Functors/Compose.lean`), `Babai.SplitOutcomes` |
| binary structures with colored edges | `Babai.ColoredEdges` |
| UPCC (Def. 3.2.1) as an object | `Babai.IsUPCCColoring`, `Babai.UPCCs` |
| Johnson scheme (Def. 3.2.13) as an object | `Babai.IsJohnsonColoring`, `Babai.JohnsonSchemes` |
| vertex-colored bipartite graph (§2.4.2) | `Babai.VColBip`, `Babai.VColBipGraphs` |
| symmetry defect of `V₁` in `X` (Def. 2.4.29) | `Babai.VColBip.defect₁` |
| "(a) or (b)" of Thms 9.2.1, 9.2.2 | `Babai.IsSplitOutcome` |
| "at multiplicative cost `s` we can find …" (Defs. 6.0.3, 6.0.5, 6.0.7) | `Babai.FindsAtMultCost` (`Workspace/Functors/Cost.lean`) |
| chaining reductions, case distinction, individualization | `Babai.FindsAtMultCost.comp`, `.cases`, `.individualize` (`Workspace/Functors/Compose.lean`) |

## Modelling notes

* **Colors as labels.**  A binary relational structure `X = (V; R₁,…,R_r)` in which the
  `Rᵢ` partition `V × V` is the same thing as an edge-coloring `c : V × V → [r]`
  (Def. 3.1.1), and an isomorphism of two such structures is a bijection preserving the
  color *labels* (Def. 2.3.4).  So the category of the binary structures occurring in §9
  is `ColoredEdges Ω ℕ`: objects are edge-colorings by `ℕ`, morphisms are the
  color-preserving bijections.  A UPCC and a Johnson scheme are objects of this category
  cut out by a predicate (`Cat.full`).

* **The input category is the category of admissible inputs.**  A functor has to be
  defined on all objects of its source category, while the algorithms of §9 take a UPCC
  (Thm. 9.2.1), a vertex-colored bipartite graph with the stated properties (Thm. 9.2.2),
  or a `k`-ary relational structure (Thm. 9.2.3).  We therefore take the source category
  to be the full subcategory of the admissible inputs; canonicity is then exactly the
  paper's "the construction commutes with the isomorphisms of the input".

* **Multiplicative cost.**  *"At a multiplicative cost of `s` we can find a canonical …"*
  is `Babai.FindsAtMultCost` (Defs. 6.0.3, 6.0.5, 6.0.7), which lives in
  `Workspace/Functors/Cost.lean` because §8 and §9 share it.

* **Running time is pending.**  Theorems 9.2.1–9.2.3 also assert a running time.  Those
  clauses are not stated here; see the entry of kind "pending" in the corrected paper.  Only
  the multiplicative cost, canonicity and the mathematical content of the output are
  formalized.
-/

namespace Babai

universe u v v'

/-! ### Binary structures with colored edges -/

/-- §2.3, §3.1.1.  The category of binary structures whose edges are colored by `κ`:
objects are the colorings `c : □X × □X → κ`, morphisms are the color-preserving bijections
(Def. 2.3.4: `σ` is an isomorphism `X → X'` if it carries `Rᵢ` onto `Rᵢ'` for each `i`).

A partition structure `X = (Ω; R₁,…,R_r) = (Ω, c)` (Def. 3.1.1) is such an object; this is
the category in which the canonicity of Theorem 9.2.1 is stated ("binary relational
structures"). -/
def ColoredEdges (Ω : Type u) (κ : Type v) : Cat.{u, max u v} Ω where
  Obj s := ↥s → ↥s → κ
  Iso c d := {f | ∀ x y, d (f x) (f y) = c x y}
  refl_mem _ _ _ := rfl
  symm_mem {_ _ _ _ f} hf x y := by
    simpa using (hf (f.symm x) (f.symm y)).symm
  trans_mem hf hg x y := by simpa using (hg _ _).trans (hf x y)
  faithful hid := funext fun x => funext fun y => (hid x y).symm

/-- The `ℕ`-valued edge-coloring of a partition structure: the color labels of
Def. 3.1.1 read as natural numbers. -/
def PartitionStructure.natColor {Ω : Type u} (X : PartitionStructure Ω) (x y : Ω) : ℕ :=
  (X.color x y : ℕ)

/-- Definition 3.2.1.  *"A uniprimitive coherent configuration (UPCC) is a homogeneous
coherent configuration that is primitive and not the clique configuration."*  Read as a
predicate on edge-colorings: the coloring is the coloring of a coherent configuration that
is uniprimitive (`IsUniprimitive` = primitive of rank `≥ 3`, Def. 3.2.1). -/
def IsUPCCColoring {Ω : Type u} {s : Set Ω} (c : ↥s → ↥s → ℕ) : Prop :=
  ∃ X : PartitionStructure ↥s, X.IsCoherent ∧ X.IsUniprimitive ∧ X.natColor = c

/-- §9.2.  The category in which Theorem 9.2.1 lives: the full subcategory of binary
structures on the UPCCs. -/
def UPCCs (Ω : Type u) : Cat.{u, u} Ω :=
  (ColoredEdges Ω ℕ).full fun _ c => IsUPCCColoring c

/-- Definitions 3.2.9 and 3.2.13.  *"Let `t ≥ 2` and let `Γ` be a set of size
`|Γ| = k ≥ 2t + 1`.  The Johnson scheme `J(Γ,t) = (Ω; c)` is an association scheme with
`k choose t` vertices corresponding to the `t`-subsets of a `k`-set `Γ`.  For
`S, T ∈ (Γ choose t)`, the color of the edge `(v_S, v_T)` is `c(v_S, v_T) = |S \ T|."*

Read as a predicate on edge-colorings of a set: the set is identified with the `t`-subsets
of a `k`-set and the coloring is `|S \ T|`.  The label set `Γ` is taken to be `Fin k`,
which is no loss: `Γ` enters only through its size.

*Nontriviality.*  §9 asks for a **nontrivial** Johnson scheme; by Remark 3.2.15 the
degenerate Johnson schemes `J(k,1)` (the clique configurations) are exactly those excluded
by the constraint `t ≥ 2` of Def. 3.2.9, which is part of this predicate.  So an object of
`JohnsonSchemes` is a nontrivial Johnson scheme. -/
def IsJohnsonColoring {Ω : Type u} {s : Set Ω} (c : ↥s → ↥s → ℕ) : Prop :=
  ∃ (k t : ℕ) (φ : ↥s ≃ binom (Fin k) t), 2 ≤ t ∧ 2 * t + 1 ≤ k ∧
    ∀ x y, c x y = ((φ x : Finset (Fin k)) \ (φ y : Finset (Fin k))).card

/-- §9.2.  The category of (nontrivial) Johnson schemes: the full subcategory of binary
structures on the Johnson colorings.  Objective (b) of Theorems 9.2.1–9.2.3 is a canonical
embedding of an object of this category into the input. -/
def JohnsonSchemes (Ω : Type u) : Cat.{u, u} Ω :=
  (ColoredEdges Ω ℕ).full fun _ c => IsJohnsonColoring c

/-- Non-vacuity of `IsJohnsonColoring`: the Johnson scheme `J(5,2)` is a coloring of this
kind, on the set of all `2`-subsets of a `5`-set. -/
example : IsJohnsonColoring (Ω := binom (Fin 5) 2) (s := Set.univ)
    (fun x y => ((x : binom (Fin 5) 2).1 \ (y : binom (Fin 5) 2).1).card) :=
  ⟨5, 2, (Equiv.Set.univ _), le_refl 2, by norm_num, fun _ _ => rfl⟩

/-! ### Vertex-colored bipartite graphs -/

/-- §2.4.2, §9.2.  A vertex-colored bipartite graph `X = (V₁, V₂; E, f)` on the vertex set
`s`: a splitting of `s` into two parts, a set of edges from the first to the second part,
and a coloring of the vertices.  (§9.4: *"We view `X` as a vertex-colored graph where the
vertex-colors discriminate between `V₁` and `V₂`."*) -/
structure VColBip (s : Type u) (κ : Type v) where
  /-- The membership predicate of the first part `V₁`. -/
  part₁ : s → Prop
  /-- `E ⊆ V₁ × V₂`. -/
  E : Set (s × s)
  /-- The vertex-coloring `f`. -/
  f : s → κ
  /-- Every edge goes from the first part to the second. -/
  E_sub : ∀ p ∈ E, part₁ p.1 ∧ ¬ part₁ p.2

namespace VColBip

variable {s : Type u} {κ : Type v} (X : VColBip s κ)

/-- The first part `V₁`. -/
def V₁ : Set s := {x | X.part₁ x}

/-- The second part `V₂`. -/
def V₂ : Set s := {x | ¬ X.part₁ x}

/-- Definition 2.3.4 for a vertex-colored bipartite graph: the automorphisms are the
permutations of the vertex set preserving the two parts, the edges and the vertex
colors. -/
def Aut : Subgroup (Equiv.Perm s) where
  carrier := {σ | (∀ x, X.part₁ (σ x) ↔ X.part₁ x) ∧ (∀ x y, (σ x, σ y) ∈ X.E ↔ (x, y) ∈ X.E)
    ∧ ∀ x, X.f (σ x) = X.f x}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩
  mul_mem' {a b} ha hb :=
    ⟨fun x => (ha.1 (b x)).trans (hb.1 x),
     fun x y => (ha.2.1 (b x) (b y)).trans (hb.2.1 x y),
     fun x => (ha.2.2 (b x)).trans (hb.2.2 x)⟩
  inv_mem' {a} ha :=
    ⟨fun x => by simpa using (ha.1 (a.symm x)).symm,
     fun x y => by simpa using (ha.2.1 (a.symm x) (a.symm y)).symm,
     fun x => by simpa using (ha.2.2 (a.symm x)).symm⟩

open scoped Classical in
/-- Definition 2.4.29, for a vertex-colored bipartite graph.  *"Let `Tᵢ` be a largest set
of twins in `Ωᵢ`.  We say that `|Tᵢ|` is the absolute symmetricity of `Ωᵢ` in `X`."*
Twins are twins with respect to `Aut(X)` (Def. 2.3.9, Def. 2.3.16). -/
noncomputable def symmetricity₁ [Fintype s] [DecidableEq s] : ℕ :=
  (Finset.univ.filter fun T : Finset s =>
    (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s)).sup Finset.card

/-- Definition 2.4.29.  *"`1 - |Tᵢ|/|Ωᵢ|` is the relative symmetry defect of `Ωᵢ`
in `X`."*  The case `i = 1`. -/
noncomputable def defect₁ [Fintype s] [DecidableEq s] : ℚ :=
  1 - (X.symmetricity₁ : ℚ) / (X.V₁.ncard : ℚ)

/-- The degree of a vertex of the first part (§2.4.2: *"By the degree of vertices in `A`
we mean their out-degree"*). -/
noncomputable def degA (x : s) : ℕ := {y | (x, y) ∈ X.E}.ncard

/-- The degree of a vertex of the second part (§2.4.2: *"…and for vertices in `B` their
in-degree"*). -/
noncomputable def degB (y : s) : ℕ := {x | (x, y) ∈ X.E}.ncard

/-- §2.4.2.  *"We say that `X` is semiregular if every vertex in `A` has the same degree
and every vertex in `B` has the same degree."* -/
def IsSemiregular : Prop :=
  (∃ d, ∀ x ∈ X.V₁, X.degA x = d) ∧ (∃ d, ∀ y ∈ X.V₂, X.degB y = d)

/-- §2.4.2.  *"The trivial bipartite graphs are the empty (`E = ∅`) and complete
(`E = A × B`) bipartite graphs."* -/
def IsTrivial : Prop := X.E = ∅ ∨ X.E = {p | X.part₁ p.1 ∧ ¬ X.part₁ p.2}

/-- The hypotheses that Theorem 9.2.2 puts on its input `X` for the threshold parameter
`α`: *"`|V₁| ≥ 2`"*, *"`|V₂| < α|V₁|`"* and *"the symmetry defect of `X` on `V₁` is at
least `1 - α`"*. -/
def IsThm922Input [Fintype s] [DecidableEq s] (α : ℝ) : Prop :=
  2 ≤ X.V₁.ncard ∧ (X.V₂.ncard : ℝ) < α * X.V₁.ncard ∧ 1 - α ≤ (X.defect₁ : ℝ)

/-- §9.3, §9.4.  *"We say that `x, y ∈ V₁` are twins if the transposition `τ = (x,y)` is an
automorphism of `X`, i.e., if `x` and `y` have the same neighborhood."*  This is
Def. 2.3.9 for `Aut(X)`. -/
def IsTwinIn [DecidableEq s] (x y : s) : Prop := IsTwin X.Aut x y

end VColBip

/-- §9.2.  The category of vertex-colored bipartite graphs, in which the canonicity of
Theorem 9.2.2 is stated: morphisms are the bijections preserving the two parts, the edges
and the vertex colors. -/
def VColBipGraphs (Ω : Type u) (κ : Type v) : Cat.{u, max u v} Ω where
  Obj s := VColBip ↥s κ
  Iso X Y := {g | (∀ x, Y.part₁ (g x) ↔ X.part₁ x)
    ∧ (∀ x y, (g x, g y) ∈ Y.E ↔ (x, y) ∈ X.E) ∧ ∀ x, Y.f (g x) = X.f x}
  refl_mem _ := ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩
  symm_mem {_ _ _ _ g} hg :=
    ⟨fun x => by simpa using (hg.1 (g.symm x)).symm,
     fun x y => by simpa using (hg.2.1 (g.symm x) (g.symm y)).symm,
     fun x => by simpa using (hg.2.2 (g.symm x)).symm⟩
  trans_mem {_ _ _ _ _ _ g h} hg hh :=
    ⟨fun x => (hh.1 (g x)).trans (hg.1 x),
     fun x y => (hh.2.1 (g x) (g y)).trans (hg.2.1 x y),
     fun x => (hh.2.2 (g x)).trans (hg.2.2 x)⟩
  faithful {s X Y} hid := by
    obtain ⟨p, E, f, hE⟩ := X
    obtain ⟨p', E', f', hE'⟩ := Y
    obtain ⟨h1, h2, h3⟩ := hid
    have hp : p' = p := funext fun x => propext (h1 x)
    have hE2 : E' = E := Set.ext fun q => by simpa using h2 q.1 q.2
    have hf : f' = f := funext fun x => h3 x
    subst hp; subst hE2; subst hf; rfl

/-- §9.2, Theorem 9.2.2.  Vertex-colored bipartite graphs **carrying their threshold
parameter**: an object on `s` is a pair `(X, α)` of a vertex-colored bipartite graph and a
real number, and a morphism `(X, α) → (Y, β)` is an isomorphism `X → Y` of vertex-colored
bipartite graphs together with `α = β`.

Why the parameter is data of the object.  The conclusion of Theorem 9.2.2 depends on `α`,
and Lemma 9.3.1 feeds Theorem 9.2.2 an `α = βn/d₂` that depends on the *input object*.
The composition rule for canonical reductions (`Babai.FindsAtMultCost.comp`) takes one
source category for the second step, so that step cannot be stated on a category indexed
by `α` from outside.  Carrying `α` in the object solves this, and loses nothing: the
objects with a fixed value of `α` form a full subcategory with exactly the morphisms of
the printed statement, and `Babai.FindsAtMultCost.full` restricts to it (see
`Babai.theorem_9_2_2_at`). -/
def VColBipThr (Ω : Type) : Cat.{0, 0} Ω where
  Obj s := VColBip ↥s ℕ × ℝ
  Iso X Y := {g | X.2 = Y.2 ∧ g ∈ (VColBipGraphs Ω ℕ).Iso X.1 Y.1}
  refl_mem X := ⟨rfl, (VColBipGraphs Ω ℕ).refl_mem X.1⟩
  symm_mem hf := ⟨hf.1.symm, (VColBipGraphs Ω ℕ).symm_mem hf.2⟩
  trans_mem hf hg := ⟨hf.1.trans hg.1, (VColBipGraphs Ω ℕ).trans_mem hf.2 hg.2⟩
  faithful hid := Prod.ext ((VColBipGraphs Ω ℕ).faithful hid.2) hid.1

/-! ### `k`-ary relational structures -/

/-- §2.3, §9.2.  The category of `k`-ary relational structures (Def. 2.3.1), in which the
canonicity of Theorem 9.2.3 is stated.  Morphisms are the isomorphisms of Def. 2.3.4:
`σ` is an isomorphism `X → X'` if `X' = X^σ`. -/
def KAryStructures (Ω : Type u) (k : ℕ) : Cat.{u, u} Ω where
  Obj s := {X : RelStructure ↥s // X.IsKAry k}
  Iso {s t} X Y := {f : ↥s ≃ ↥t | X.1.map (f : ↥s → ↥t) = Y.1}
  refl_mem {s} X := by
    show X.1.map ((Equiv.refl ↥s : ↥s ≃ ↥s) : ↥s → ↥s) = X.1
    rw [Equiv.coe_refl, RelStructure.map_id]
  symm_mem {s t X Y f} hf := by
    show Y.1.map ((f.symm : ↥t ≃ ↥s) : ↥t → ↥s) = X.1
    have hY : Y.1 = X.1.map (f : ↥s → ↥t) := hf.symm
    rw [hY, RelStructure.map_map,
      show ((f.symm : ↥t → ↥s) ∘ (f : ↥s → ↥t)) = id from funext fun x => by simp,
      RelStructure.map_id]
  trans_mem {s t r X Y Z f g} hf hg := by
    show X.1.map ((f.trans g : ↥s ≃ ↥r) : ↥s → ↥r) = Z.1
    rw [show ((f.trans g : ↥s ≃ ↥r) : ↥s → ↥r) = (g : ↥t → ↥r) ∘ (f : ↥s → ↥t) from rfl,
      ← RelStructure.map_map, show X.1.map (f : ↥s → ↥t) = Y.1 from hf, hg]
  faithful {s X Y} hid := by
    refine Subtype.ext ?_
    have h : X.1.map ((Equiv.refl ↥s : ↥s ≃ ↥s) : ↥s → ↥s) = Y.1 := hid
    rwa [Equiv.coe_refl, RelStructure.map_id] at h

/-! ### The outcome of Split-or-Johnson -/

/-- §9.2.  The category of the possible outputs of the algorithms of §9: either a colored
partition (Def. 7.1.1, the category `ColoredPartitions` of §7.1) or a Johnson scheme
(Def. 3.2.13).  See `Cat.sum`. -/
def SplitOutcomes (Ω : Type u) : Cat.{u, u} Ω :=
  Cat.sum (ColoredPartitions Ω ℕ) (JohnsonSchemes Ω)

/-- §9.2.  The disjunction in the conclusion of Theorems 9.2.1–9.2.3, for the vertex set
`W` that is to be split:

> *"(a) a canonical colored `α`-partition of `W`, or (b) a canonically embedded nontrivial
> Johnson scheme on a subset of `W` of size `≥ α|W|`."*

Case (a) is the first summand, and then the underlying set of the output is all of `W`
(Def. 7.1.2: a canonical colored partition is a canonical embedding *onto*) and the
partition is a colored `α`-partition (Def. 7.1.1).  Case (b) is the second summand, and
then the underlying set is a subset of `W` of size `≥ α|W|`; it is a nontrivial Johnson
scheme by the definition of `JohnsonSchemes`. -/
def IsSplitOutcome {Ω : Type u} [Finite Ω] (α : ℝ) (W : Set Ω) (Z : Pt (SplitOutcomes Ω)) :
    Prop :=
  match Z.obj with
  | Sum.inl P => Z.car = W ∧ letI : Fintype ↥Z.car := Fintype.ofFinite _;
      P.IsAlphaPartition α
  | Sum.inr _ => Z.car ⊆ W ∧ α * (W.ncard : ℝ) ≤ (Z.car.ncard : ℝ)

end Babai
