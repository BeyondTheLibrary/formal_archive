/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.3: Relational structures, twins, symmetricity and symmetry defect.
-/
import Workspace.Prelim.PermGroups
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Lattice.Fold

/-!
# §2.3 Relational structures, twins, symmetricity and symmetry defect

The right-action convention of `Workspace.Prelim.PermGroups` is used throughout: the
paper's `x^σ` is Lean's `σ x`.

## Composition order

On points the paper's exponential notation and Lean's application notation agree
(`x^σ = σ x`), but on *composites* they do not.  The paper's action on structures is a
right action, `X^{στ} = (X^σ)^τ`, while `RelStructure.map` is a **left** action:
`map_map` gives `(X.map σ).map τ = X.map (τ ∘ σ)`, and `map_mul` gives
`X.map ((σ * τ : Perm Ω)) = (X.map τ).map σ`.  Consequently

  the paper's `X^{στ}` is Lean's `X.map (τ * σ)`.

This is invisible for `Aut X` (a subgroup either way) and for `Iso X X'` as a set, but it
matters as soon as a later section writes a coset identity such as
`Iso(X,Y) = Aut(X)σ = σ Aut(Y)`.

## Finiteness

The paper's vertex set `Ω` is finite throughout §2.  Cardinalities here are `Set.ncard`
and `Fintype.card`, both of which return `0` on infinite sets, so notions defined by
counting (degree, density, biregularity, semiregularity in `Prelim/BinaryRelations.lean`)
are junk on infinite types.  Every theorem about them carries a `[Fintype _]`
assumption; definitions are left unconstrained only for convenience.

## Degenerate carriers

Lean's division is total (`0/0 = 0`) and `ℕ`-subtraction truncates.  For `Ω = ∅` we get
`symmetricity G = 0`, `relSymmetricity G = 0` and hence `defect G = 1`, which is outside
the paper's range `0 ≤ defect(G) < 1`.  The paper never assigns a value there (an empty
`Ω` has no twin equivalence class at all), so this is a convention, not a correction;
`defect_nonneg_lt_one` carries `[Nonempty Ω]`, and every §2 result that mentions `defect`
has hypotheses forcing `Ω ≠ ∅`.

## Numbering map

| Paper | Lean |
|---|---|
| Definition 2.3.1 | `Babai.RelStructure`, `Babai.RelStructure.IsKAry` |
| Notation 2.3.2 | `Babai.tupleMap` |
| Notation 2.3.3 | `Babai.mapRel`, `Babai.RelStructure.map` |
| Definition 2.3.4 | `Babai.RelStructure.IsIsoOf`, `Babai.RelStructure.Iso`, `Babai.RelStructure.Isomorphic`, `Babai.RelStructure.Aut` |
| Observation 2.3.5 | `Babai.RelStructure.numRel_eq_of_iso`, `Babai.RelStructure.arity_heq_of_iso` |
| Proposition 2.3.6 | `Babai.RelStructure.map_eq_iff`, `Babai.RelStructure.mem_aut_iff`, `Babai.RelStructure.decidableMemAut`; RAM: `Algo.rawExplIsoTest_spec`, `Algo.polyFun_rawExplIsoTest`; linear time: `Algo.Proposition_2_3_6_linear_statement`, proved as `Algo.ExplLinear.proposition_2_3_6_linear` |
| Definition 2.3.7 | `Babai.RelStructure.induced` |
| Convention 2.3.8 | `Babai.symOn` |
| Definition 2.3.9 | `Babai.IsTwin` |
| Observation 2.3.10 | `Babai.twinOrEq_equivalence` |
| Definition 2.3.11 | `Babai.twinClass`, `Babai.IsTwinSet` |
| Observation 2.3.12 | `Babai.isTwinSet_iff_symOn_le`, `Babai.twinClass_isTwinSet`, `Babai.twinClass_maximal` |
| Definition 2.3.13 | `Babai.symmetricity`, `Babai.relSymmetricity`, `Babai.symDefect`, `Babai.defect` |
| Examples 2.3.14 | `Babai.symDefect_top`, `Babai.symDefect_alternating`, `Babai.symDefect_prod` |
| Observation 2.3.15 | `Babai.defect_antitone` |
| Definition 2.3.16 | `Babai.IsStructure`, `Babai.structDefect` |
| Observation 2.3.17 | `Babai.instDecidableIsTwin`, `Babai.symmetricity_eq_sup_twinClass`; RAM: `Algo.explTwinClasses_spec`, `Algo.explSymmetricity_spec`, `Algo.explSymDefect_spec`, `Algo.polyFun_explTwinClasses`, `Algo.polyFun_explSymmetricity`, `Algo.polyFun_explSymDefect` |
-/

namespace Babai

open Equiv Equiv.Perm

variable {Ω Ω' Ω'' : Type*}

/-! ### §2.3.1 Relational structures, isomorphism -/

/-- Definition 2.3.1.  "A *`k`-ary relation* on the set `Ω` is a subset `R ⊆ Ω^k`.  We say
that the *arity* of `R` is `k`.  A *relational structure* `X = (Ω; R)` consists of `Ω`,
the set of vertices, and `R = (R₁,…,R_r)`, a list of relations on `Ω`."

We represent `Ω^k` by `Fin k → Ω` and the list `R` by its length `numRel = r`, the list of
arities, and the relations themselves. -/
structure RelStructure (Ω : Type*) where
  /-- The number `r` of relations in the list `R = (R₁,…,R_r)`. -/
  numRel : ℕ
  /-- The arity of each relation in the list. -/
  arity : Fin numRel → ℕ
  /-- The relations themselves: `Rᵢ ⊆ Ω^(arity i)`. -/
  rel : ∀ i, Set (Fin (arity i) → Ω)

namespace RelStructure

/-- Definition 2.3.1.  "We say that `X` is a *`k`-ary relational structure* if each `Rᵢ`
is `k`-ary." -/
def IsKAry (X : RelStructure Ω) (k : ℕ) : Prop := ∀ i, X.arity i = k

/-- Definition 2.3.1.  "We write `Ω = V(X)`" for the vertex set of `X`.  In this
development the vertex set is the type parameter, so `V X` is `Ω` itself. -/
abbrev V (_X : RelStructure Ω) : Type _ := Ω

end RelStructure

/-- Notation 2.3.2.  "Let `x = (x₁,…,x_k) ∈ Ω^k` and let `f : Ω → Ω'` be a function.
Then we write `x^f = (x₁^f,…,x_k^f) ∈ Ω'^k`." -/
def tupleMap {k : ℕ} (f : Ω → Ω') (x : Fin k → Ω) : Fin k → Ω' := fun i => f (x i)

@[simp] theorem tupleMap_apply {k : ℕ} (f : Ω → Ω') (x : Fin k → Ω) (i : Fin k) :
    tupleMap f x i = f (x i) := rfl

@[simp] theorem tupleMap_id {k : ℕ} (x : Fin k → Ω) : tupleMap id x = x := rfl

@[simp] theorem tupleMap_comp {k : ℕ} (f : Ω' → Ω'') (g : Ω → Ω') (x : Fin k → Ω) :
    tupleMap f (tupleMap g x) = tupleMap (f ∘ g) x := rfl

/-- Notation 2.3.3.  "Let `σ : Ω → Ω'` be a bijection and `R ⊆ Ω^k` a `k`-ary relation.
Then we define `R^σ ⊆ Ω'^k` by setting `R^σ = {x^σ | x ∈ R}`." -/
def mapRel {k : ℕ} (σ : Ω → Ω') (R : Set (Fin k → Ω)) : Set (Fin k → Ω') :=
  tupleMap σ '' R

namespace RelStructure

/-- Notation 2.3.3.  "For a relational structure `X = (Ω; R)` and a bijection
`σ : Ω → Ω'` we set `X^σ = (Ω'; R^σ)`, where `R^σ = (R₁^σ,…,R_r^σ)`." -/
def map (X : RelStructure Ω) (σ : Ω → Ω') : RelStructure Ω' where
  numRel := X.numRel
  arity := X.arity
  rel i := mapRel σ (X.rel i)

@[simp] theorem map_numRel (X : RelStructure Ω) (σ : Ω → Ω') :
    (X.map σ).numRel = X.numRel := rfl

@[simp] theorem map_arity (X : RelStructure Ω) (σ : Ω → Ω') :
    (X.map σ).arity = X.arity := rfl

@[simp] theorem map_id (X : RelStructure Ω) : X.map id = X := by
  cases X with
  | mk n a R =>
    simp only [map, mk.injEq, heq_eq_eq, true_and]
    funext i
    simp [mapRel, tupleMap, Set.image_id']

theorem map_map (X : RelStructure Ω) (σ : Ω → Ω') (τ : Ω' → Ω'') :
    (X.map σ).map τ = X.map (τ ∘ σ) := by
  cases X with
  | mk n a R =>
    simp only [map, mk.injEq, heq_eq_eq, true_and]
    funext i
    simp [mapRel, Set.image_image, tupleMap, Function.comp_def]

/-- `map` is a left action of `S(Ω)` (see the "Composition order" note in the module
docstring): the identity acts trivially. -/
@[simp] theorem map_one (X : RelStructure Ω) : X.map ((1 : Equiv.Perm Ω) : Ω → Ω) = X :=
  X.map_id

/-- `map` is a **left** action of `S(Ω)`, whereas the paper's `X ↦ X^σ` is a right
action.  Hence the paper's `X^{στ} = (X^σ)^τ` is Lean's `X.map (τ * σ)`. -/
theorem map_mul (X : RelStructure Ω) (σ τ : Equiv.Perm Ω) :
    X.map ((σ * τ : Equiv.Perm Ω) : Ω → Ω) = (X.map (τ : Ω → Ω)).map (σ : Ω → Ω) := by
  rw [X.map_map]
  rfl

/-- Definition 2.3.4 (Isomorphisms).  "A bijection `σ : Ω → Ω'` is an `X → X'`
isomorphism if `X' = X^σ`." -/
def IsIsoOf (σ : Ω → Ω') (X : RelStructure Ω) (X' : RelStructure Ω') : Prop :=
  Function.Bijective σ ∧ X.map σ = X'

/-- Definition 2.3.4.  `Iso(X, X')`, the set of isomorphisms `X → X'`, viewed as a set of
bijections `Ω ≃ Ω'`. -/
def Iso (X : RelStructure Ω) (X' : RelStructure Ω') : Set (Ω ≃ Ω') :=
  {σ | X.map σ = X'}

/-- Definition 2.3.4.  "We say that `X ≅ X'` (`X` and `X'` are *isomorphic*) if such `σ`
exists." -/
def Isomorphic (X : RelStructure Ω) (X' : RelStructure Ω') : Prop :=
  ∃ σ : Ω ≃ Ω', σ ∈ Iso X X'

/-- Definition 2.3.4.  `Aut(X) ≤ S(Ω)`, the automorphism group of a relational
structure. -/
def Aut (X : RelStructure Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {σ | X.map σ = X}
  one_mem' := by simpa using X.map_id
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [show ((a * b : Equiv.Perm Ω) : Ω → Ω) = (a : Ω → Ω) ∘ (b : Ω → Ω) from rfl,
      ← X.map_map (b : Ω → Ω) (a : Ω → Ω), hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [X.map_map]
    have : ((a⁻¹ : Equiv.Perm Ω) : Ω → Ω) ∘ ((a : Equiv.Perm Ω) : Ω → Ω) = id := by
      funext x; simp
    rw [this, X.map_id]

@[simp] theorem mem_Aut {X : RelStructure Ω} {σ : Equiv.Perm Ω} :
    σ ∈ Aut X ↔ X.map σ = X := Iff.rfl

/-- Observation 2.3.5.  "Using the notation of Def. 2.3.4, if `X ≅ X'` then `r = r'`."

In our representation `r = numRel`. -/
theorem numRel_eq_of_iso {X : RelStructure Ω} {X' : RelStructure Ω'} (σ : Ω ≃ Ω')
    (h : σ ∈ Iso X X') : X.numRel = X'.numRel := by
  rw [Iso, Set.mem_setOf_eq] at h; rw [← h]; rfl

/-- Observation 2.3.5.  "…and for each `i`, the relations `Rᵢ` and `Rᵢ'` have the same
arity." -/
theorem arity_heq_of_iso {X : RelStructure Ω} {X' : RelStructure Ω'} (σ : Ω ≃ Ω')
    (h : σ ∈ Iso X X') : HEq X.arity X'.arity := by
  rw [Iso, Set.mem_setOf_eq] at h; rw [← h]; rfl

/-- Proposition 2.3.6 (Testing candidate isomorphism).  "Given two explicit relational
structures `X = (Ω, R)` and `X' = (Ω', R')` and a bijection `σ : Ω → Ω'`, one can decide
in linear time whether `σ ∈ Iso(X, X')`."

On the RAM of `Workspace/Machine/`, the test is `Algo.rawExplIsoTest`
(`Workspace/Algo/ExplicitStructures.lean`): `Algo.rawExplIsoTest_spec` says it decides
`σ ∈ Iso(X, X')` for explicit structures, and `Algo.polyFun_rawExplIsoTest` that it runs in
polynomial time.  The linear bound is the statement `Algo.Proposition_2_3_6_linear_statement`,
proved as `Algo.ExplLinear.proposition_2_3_6_linear` (`Workspace/Algo/ExplLinear.lean`).  What we record here is the
mathematical content of the test: `σ` is an isomorphism exactly if, relation by relation and tuple by
tuple, membership is preserved.  By Observation 2.3.5 every `X'` isomorphic to `X` has
the same list of arities as `X`, which is why the statement is phrased for such an
`X'`. -/
theorem map_eq_iff (X : RelStructure Ω) (σ : Ω ≃ Ω')
    (R' : ∀ i, Set (Fin (X.arity i) → Ω')) :
    X.map σ = ⟨X.numRel, X.arity, R'⟩ ↔
      ∀ i, ∀ x : Fin (X.arity i) → Ω, (tupleMap σ x ∈ R' i ↔ x ∈ X.rel i) := by
  obtain ⟨n, a, R⟩ := X
  simp only [map, mk.injEq, heq_eq_eq, true_and]
  constructor
  · intro h i x
    have hrel : mapRel (σ : Ω → Ω') (R i) = R' i := congrFun h i
    rw [← hrel]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := by
        funext j
        exact σ.injective (congrFun hxy j)
      exact this ▸ hy
    · intro hx; exact ⟨x, hx, rfl⟩
  · intro h
    funext i
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h i x).2 hx
    · intro hy
      refine ⟨tupleMap (σ.symm : Ω' → Ω) y, ?_, ?_⟩
      · refine (h i _).1 ?_
        simpa [tupleMap] using hy
      · funext j; simp [tupleMap]

/-- Proposition 2.3.6, second part.  "In particular, given an explicit relational
structure `X = (Ω, R)` and a permutation `σ ∈ S(Ω)`, one can decide in linear time
whether `σ ∈ Aut(X)`."  On the RAM: `Algo.rawExplAutTest_spec`, `Algo.polyFun_rawExplAutTest`. -/
theorem mem_aut_iff (X : RelStructure Ω) (σ : Equiv.Perm Ω) :
    σ ∈ Aut X ↔ ∀ i, ∀ x : Fin (X.arity i) → Ω, (tupleMap σ x ∈ X.rel i ↔ x ∈ X.rel i) := by
  rw [mem_Aut]
  have := X.map_eq_iff σ X.rel
  rwa [show (⟨X.numRel, X.arity, X.rel⟩ : RelStructure Ω) = X from rfl] at this

/-- Proposition 2.3.6.  The membership test of `Aut(X)` is decidable (the paper's
"explicitness" assumption becomes decidability of the relations). -/
instance decidableMemAut [Fintype Ω] (X : RelStructure Ω)
    [∀ i, DecidablePred (· ∈ X.rel i)] (σ : Equiv.Perm Ω) : Decidable (σ ∈ Aut X) :=
  decidable_of_iff _ (X.mem_aut_iff σ).symm

/-- Definition 2.3.7 (Induced substructure).  "Let `Δ ⊆ Ω` and let
`X = (Ω; R₁,…,R_r)` be a `k`-ary relational structure.  Let `Rᵢ^Δ = Rᵢ ∩ Δ^k`.  We define
the *induced substructure* `X[Δ]` of `X` on `Δ` as `X[Δ] = (Δ; R₁^Δ,…,R_r^Δ)`."

The relations of `X[Δ]` are the tuples of `Δ` that lie in the corresponding relation
of `X`; this is `Rᵢ ∩ Δ^k` read as a relation on `Δ`. -/
def induced (X : RelStructure Ω) (Δ : Set Ω) : RelStructure Δ where
  numRel := X.numRel
  arity := X.arity
  rel i := {x : Fin (X.arity i) → Δ | tupleMap (Subtype.val) x ∈ X.rel i}

end RelStructure

/-! ### §2.3.2 Twins, symmetricity, symmetry defect -/

/-- Convention 2.3.8.  "Let `Ψ ⊆ Ω`.  We view `S(Ψ)` as a subgroup of `S(Ω)` under the
natural embedding, extending each element of `S(Ψ)` to act trivially on `Ω \ Ψ`."

Concretely, `symOn Ψ` is the group of permutations of `Ω` that fix every point outside
`Ψ`; these are exactly the extensions of permutations of `Ψ`. -/
def symOn (Ψ : Set Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {σ | ∀ x ∉ Ψ, σ x = x}
  one_mem' := by intro x _; rfl
  mul_mem' := by
    intro a b ha hb x hx
    simp [Equiv.Perm.mul_apply, hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    conv_lhs => rw [← ha x hx]
    simp

@[simp] theorem mem_symOn {Ψ : Set Ω} {σ : Equiv.Perm Ω} :
    σ ∈ symOn Ψ ↔ ∀ x ∉ Ψ, σ x = x := Iff.rfl

theorem symOn_mono {Ψ Ψ' : Set Ω} (h : Ψ ⊆ Ψ') : symOn Ψ ≤ symOn Ψ' :=
  fun _ hσ x hx => hσ x (fun hxΨ => hx (h hxΨ))

/-- `S(Ψ)` is `2`-transitive on `Ψ`: any ordered pair of distinct points of `Ψ` can be
carried to any other by a permutation fixing `Ω \ Ψ` pointwise.  This is what makes a set
of twins either independent or complete in an invariant irreflexive digraph
(Cor. 2.4.12). -/
theorem exists_symOn_map_pair [DecidableEq Ω] {Ψ : Set Ω} {x y x' y' : Ω}
    (hx : x ∈ Ψ) (hy : y ∈ Ψ) (hx' : x' ∈ Ψ) (hy' : y' ∈ Ψ)
    (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ σ ∈ symOn Ψ, σ x = x' ∧ σ y = y' := by
  classical
  set σ₁ : Equiv.Perm Ω := Equiv.swap x x' with hσ₁
  have hσ₁mem : σ₁ ∈ symOn Ψ := fun w hw =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hw (h ▸ hx)) (fun h => hw (h ▸ hx'))
  have hσ₁x : σ₁ x = x' := Equiv.swap_apply_left x x'
  set z : Ω := σ₁ y with hz
  have hzΨ : z ∈ Ψ := by
    rw [hz, hσ₁]
    by_cases h1 : y = x
    · rw [h1, Equiv.swap_apply_left]; exact hx'
    by_cases h2 : y = x'
    · rw [h2, Equiv.swap_apply_right]; exact hx
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hy
  have hzx' : z ≠ x' := fun h => hxy (σ₁.injective (h.trans hσ₁x.symm)).symm
  by_cases hzy : z = y'
  · exact ⟨σ₁, hσ₁mem, hσ₁x, by rw [← hz, hzy]⟩
  · refine ⟨Equiv.swap z y' * σ₁, Subgroup.mul_mem _ (fun w hw =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hw (h ▸ hzΨ)) (fun h => hw (h ▸ hy'))) hσ₁mem,
      ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hσ₁x,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hzx') hxy']
    · rw [Equiv.Perm.mul_apply, ← hz, Equiv.swap_apply_left]

section Twins

variable [DecidableEq Ω]

/-- Definition 2.3.9 (Twins).  "Let `G ≤ S(Ω)` and `x, y ∈ Ω`.  We say that the points
`x ≠ y` are *twins* with respect to `G` if the transposition `τ = (x, y)` belongs to `G`."

(Version 2.5 removed the notions of "strong" and "weak" twins of versions 1 and 2; this
is the former "strong twin" relation, see footnote 5 of version 2.5.) -/
def IsTwin (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Prop :=
  x ≠ y ∧ Equiv.swap x y ∈ G

/-- The "twin or equal" relation of Observation 2.3.10. -/
def TwinOrEq (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Prop :=
  x = y ∨ IsTwin G x y

/-- Observation 2.3.10.  "The 'twin or equal' relation is an equivalence relation
on `Ω`." -/
theorem twinOrEq_equivalence (G : Subgroup (Equiv.Perm Ω)) :
    Equivalence (TwinOrEq G) where
  refl _ := Or.inl rfl
  symm := by
    rintro x y (rfl | ⟨hne, hmem⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hne.symm, by rwa [Equiv.swap_comm]⟩
  trans := by
    rintro x y z (rfl | ⟨hxy, hxyG⟩) h
    · exact h
    rcases h with (rfl | ⟨hyz, hyzG⟩)
    · exact Or.inr ⟨hxy, hxyG⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    refine Or.inr ⟨hxz, ?_⟩
    -- `(x,z) = (y,z)(x,y)(y,z)`, since `(y,z)` maps `x ↦ x` and `y ↦ z`
    have key : Equiv.swap x z =
        Equiv.swap y z * Equiv.swap x y * (Equiv.swap y z)⁻¹ := by
      rw [← Equiv.swap_apply_apply (Equiv.swap y z) x y]
      rw [Equiv.swap_apply_of_ne_of_ne hxy hxz, Equiv.swap_apply_left]
    rw [key]
    exact G.mul_mem (G.mul_mem hyzG hxyG) (G.inv_mem hyzG)

/-- Observation 2.3.17.  "One can find the twin equivalence classes in polynomial time
(test each transposition)."  The content recorded here is that the twin relation is a
single membership test in `G`.  On the RAM (`Workspace/Algo/ExplicitStructures.lean`), for
any polynomial-time automorphism test: `Algo.rawTwinClasses` (`Algo.mem_rawTwinClasses`),
`Algo.rawSymmetricity` (`Algo.rawSymmetricity_eq`) and `Algo.rawSymDefect`
(`Algo.rawSymDefect_eq`); for explicit relational structures `Algo.explTwinClasses_spec`,
`Algo.explSymmetricity_spec`, `Algo.explSymDefect_spec`, with their `polyFun_` lemmas. -/
instance instDecidableIsTwin (G : Subgroup (Equiv.Perm Ω)) [DecidablePred (· ∈ G)]
    (x y : Ω) : Decidable (IsTwin G x y) := by
  unfold IsTwin; infer_instance

/-- Definition 2.3.11.  "We call the equivalence classes of the twin-or-equal relation the
*twin equivalence classes* of `G`." -/
def twinClass (G : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | TwinOrEq G x y}

/-- Definition 2.3.11.  "We shall say that a set `Ψ ⊆ Ω` is a *set of twins* if `Ψ` is a
subset of a twin equivalence class, i.e. if all pairs in `Ψ` are twins." -/
def IsTwinSet (G : Subgroup (Equiv.Perm Ω)) (Ψ : Set Ω) : Prop :=
  ∀ x ∈ Ψ, ∀ y ∈ Ψ, x ≠ y → IsTwin G x y

/-- Auxiliary induction for Observation 2.3.12: a permutation fixing everything outside a
set of twins `Ψ` is a product of transpositions of pairs of points of `Ψ`, hence lies
in `G`.  The induction is on the size of the support. -/
private theorem mem_of_symOn_aux [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (Ψ : Set Ω)
    (h : IsTwinSet G Ψ) :
    ∀ (n : ℕ) (σ : Equiv.Perm Ω), σ.support.card ≤ n → (∀ x ∉ Ψ, σ x = x) → σ ∈ G := by
  intro n
  induction n with
  | zero =>
    intro σ hcard _
    have : σ = 1 := by
      rw [← Equiv.Perm.support_eq_empty_iff]
      exact Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    simp [this]
  | succ n ih =>
    intro σ hcard hfix
    by_cases hone : σ = 1
    · simp [hone]
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hc
      push_neg at hc
      exact hone (Equiv.ext hc)
    have hxΨ : x ∈ Ψ := by by_contra hc; exact hx (hfix x hc)
    have hyΨ : σ x ∈ Ψ := by
      by_contra hc
      exact hx (σ.injective (hfix (σ x) hc))
    set y := σ x with hy
    have hxy : x ≠ y := fun hh => hx hh.symm
    have hswap : Equiv.swap x y ∈ G := (h x hxΨ y hyΨ hxy).2
    set τ := Equiv.swap x y * σ with hτ
    have hτfix : ∀ z ∉ Ψ, τ z = z := by
      intro z hz
      have h1 : σ z = z := hfix z hz
      have hzx : z ≠ x := fun hh => hz (hh ▸ hxΨ)
      have hzy : z ≠ y := fun hh => hz (hh ▸ hyΨ)
      simp [hτ, Equiv.Perm.mul_apply, h1, Equiv.swap_apply_of_ne_of_ne hzx hzy]
    have hsubset : τ.support ⊆ σ.support := by
      intro z hz
      rw [Equiv.Perm.mem_support] at hz ⊢
      by_contra hc
      apply hz
      have hzx : z ≠ x := by rintro rfl; exact hx hc
      have hzy : z ≠ y := by rintro rfl; exact hx (σ.injective hc)
      simp [hτ, Equiv.Perm.mul_apply, hc, Equiv.swap_apply_of_ne_of_ne hzx hzy]
    have hssub : τ.support ⊂ σ.support := by
      refine (Finset.ssubset_iff_of_subset hsubset).2 ⟨x, ?_, ?_⟩
      · rwa [Equiv.Perm.mem_support]
      · have hfix' : τ x = x := by
          rw [hτ]
          simp [Equiv.Perm.mul_apply, ← hy]
        simp [Equiv.Perm.mem_support, hfix']
    have hcardτ : τ.support.card ≤ n := by
      have := Finset.card_lt_card hssub
      omega
    have hmem : τ ∈ G := ih τ hcardτ hτfix
    have hfact : σ = Equiv.swap x y * τ := by
      rw [hτ, ← mul_assoc, Equiv.swap_mul_self, one_mul]
    rw [hfact]
    exact G.mul_mem hswap hmem

/-- Observation 2.3.12.  "A subset `Ψ ⊆ Ω` is a set of twins if and only if
`S(Ψ) ≤ G`."

The forward implication uses that `S(Ψ)` is generated by the transpositions of pairs of
points of `Ψ`. -/
theorem isTwinSet_iff_symOn_le [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (Ψ : Set Ω) :
    IsTwinSet G Ψ ↔ symOn Ψ ≤ G := by
  constructor
  · intro h σ hσ
    rw [mem_symOn] at hσ
    exact mem_of_symOn_aux G Ψ h σ.support.card σ le_rfl hσ
  · intro h x hx y hy hxy
    refine ⟨hxy, h ?_⟩
    rw [mem_symOn]
    intro z hz
    exact Equiv.swap_apply_of_ne_of_ne (fun hzx => hz (hzx ▸ hx)) (fun hzy => hz (hzy ▸ hy))

/-- Observation 2.3.12.  Each twin equivalence class is a set of twins. -/
theorem twinClass_isTwinSet (G : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    IsTwinSet G (twinClass G x) := by
  intro y hy z hz hyz
  have h := twinOrEq_equivalence G
  have : TwinOrEq G y z := h.trans (h.symm hy) hz
  rcases this with (rfl | ht)
  · exact absurd rfl hyz
  · exact ht

/-- Observation 2.3.12.  "The twin equivalence classes are the maximal sets of twins."
Every set of twins is contained in a twin equivalence class. -/
theorem IsTwinSet.subset_twinClass {G : Subgroup (Equiv.Perm Ω)} {Ψ : Set Ω}
    (h : IsTwinSet G Ψ) {x : Ω} (hx : x ∈ Ψ) : Ψ ⊆ twinClass G x := by
  intro y hy
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr (h x hx y hy hxy)

/-- Observation 2.3.12.  The twin equivalence classes are maximal among sets of twins. -/
theorem twinClass_maximal (G : Subgroup (Equiv.Perm Ω)) (x : Ω) {Ψ : Set Ω}
    (hΨ : IsTwinSet G Ψ) (h : twinClass G x ⊆ Ψ) : Ψ = twinClass G x := by
  refine le_antisymm ?_ h
  exact hΨ.subset_twinClass (h (Or.inl rfl))

end Twins

/-! ### Definition 2.3.13: symmetricity and symmetry defect -/

section Symmetricity

variable [Fintype Ω] [DecidableEq Ω]

open scoped Classical in
/-- Definition 2.3.13.  "The (absolute) *symmetricity* `s(G)` of `G ≤ S(Ω)` is the size of
its largest twin equivalence class."

Equivalently (Observation 2.3.12) it is the size of a largest set of twins, which is the
form we use.

Degenerate carrier: for `Ω = ∅` the paper's definition is empty (there is no twin
equivalence class), while the supremum below is over the single set `∅`, so Lean gives
`symmetricity G = 0`. -/
noncomputable def symmetricity (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  (Finset.univ.filter fun Ψ : Finset Ω => IsTwinSet G (↑Ψ : Set Ω)).sup Finset.card

open scoped Classical in
theorem le_symmetricity {G : Subgroup (Equiv.Perm Ω)} {Ψ : Finset Ω}
    (h : IsTwinSet G (↑Ψ : Set Ω)) : Ψ.card ≤ symmetricity G :=
  Finset.le_sup (f := Finset.card) (by simp [h])

open scoped Classical in
/-- Definition 2.3.13 in the paper's own words: "the size of its largest twin equivalence
class".  (The Lean definition takes the largest set of twins; by Observation 2.3.12 the two
agree.)  For `Ω = ∅` both sides are `0`. -/
theorem symmetricity_eq_sup_twinClass (G : Subgroup (Equiv.Perm Ω)) :
    symmetricity G = Finset.univ.sup (fun x => (Finset.univ.filter (fun y => TwinOrEq G x y)).card) := by
  apply le_antisymm
  · refine Finset.sup_le fun Ψ hΨ => ?_
    have hΨ' : IsTwinSet G (↑Ψ : Set Ω) := (Finset.mem_filter.1 hΨ).2
    rcases Ψ.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact Nat.zero_le _
    · refine le_trans (Finset.card_le_card fun y hy => ?_)
        (Finset.le_sup (f := fun x => (Finset.univ.filter (fun y => TwinOrEq G x y)).card)
          (Finset.mem_univ x))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hΨ'.subset_twinClass (x := x) hx hy
  · refine Finset.sup_le fun x _ => le_symmetricity ?_
    have h := twinClass_isTwinSet G x
    intro y hy z hz hyz
    exact h y (by simpa using hy) z (by simpa using hz) hyz

theorem symmetricity_le_card (G : Subgroup (Equiv.Perm Ω)) :
    symmetricity G ≤ Fintype.card Ω := by
  classical
  refine Finset.sup_le fun Ψ _ => ?_
  simpa using Finset.card_le_univ Ψ

/-- Definition 2.3.13.  "The *relative symmetricity* of `G` is `s(G)/|Ω|`."

Degenerate carrier: for `Ω = ∅` this is Lean's `0 / 0 = 0`, and hence `defect G = 1`,
outside the paper's range `0 ≤ defect(G) < 1`.  The paper assigns no value there; see
`defect_nonneg_lt_one`, which assumes `[Nonempty Ω]`. -/
noncomputable def relSymmetricity (G : Subgroup (Equiv.Perm Ω)) : ℚ :=
  (symmetricity G : ℚ) / (Fintype.card Ω : ℚ)

/-- Definition 2.3.13.  "The *symmetry defect* of `G` is the complementary quantity
`|Ω| - s(G)`." -/
noncomputable def symDefect (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  Fintype.card Ω - symmetricity G

/-- Definition 2.3.13.  "The *relative symmetry defect* of `G` is
`defect(G) = 1 - s(G)/|Ω|`."

Degenerate carrier: for `Ω = ∅` we get `defect G = 1 - 0/0 = 1`, outside the paper's
range.  The bounds `0 ≤ defect(G) < 1` are proved in `defect_nonneg_lt_one` under
`[Nonempty Ω]`, which is the only case the paper's definition covers. -/
noncomputable def defect (G : Subgroup (Equiv.Perm Ω)) : ℚ :=
  1 - relSymmetricity G

/-- Definition 2.3.13.  "Note that `0 ≤ defect(G) < 1`."  (For `Ω ≠ ∅`; the lower bound
needs `s(G) ≤ |Ω|` and the strict upper bound needs `s(G) ≥ 1`.) -/
theorem defect_nonneg_lt_one [Nonempty Ω] (G : Subgroup (Equiv.Perm Ω)) :
    0 ≤ defect G ∧ defect G < 1 := by
  have hn : (0 : ℚ) < (Fintype.card Ω : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : 1 ≤ symmetricity G := by
    obtain ⟨x⟩ := ‹Nonempty Ω›
    have : IsTwinSet G (↑({x} : Finset Ω) : Set Ω) := by
      intro a ha b hb hab
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
    simpa using le_symmetricity this
  have h2 : symmetricity G ≤ Fintype.card Ω := symmetricity_le_card G
  have hs : (0 : ℚ) < (symmetricity G : ℚ) := by exact_mod_cast h1
  constructor
  · rw [defect, relSymmetricity, sub_nonneg, div_le_one hn]
    exact_mod_cast h2
  · rw [defect, relSymmetricity, sub_lt_self_iff]
    exact div_pos hs hn

open scoped Classical in
/-- A bound on the size of every set of twins bounds the symmetricity.  (Used to prove the
"symmetry defect `> 1/4`" statement 2.5.12.) -/
theorem symmetricity_le {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (h : ∀ Ψ : Finset Ω, IsTwinSet G (↑Ψ : Set Ω) → Ψ.card ≤ k) : symmetricity G ≤ k := by
  refine Finset.sup_le fun Ψ hΨ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
  exact h Ψ hΨ

open scoped Classical in
/-- A bound on the size of every set of twins bounds the symmetricity.  (Used to prove the
"symmetry defect `≥ 1/2`" statements 2.4.12 and 2.4.30.) -/
theorem two_mul_symmetricity_le {G : Subgroup (Equiv.Perm Ω)}
    (h : ∀ Ψ : Finset Ω, IsTwinSet G (↑Ψ : Set Ω) → 2 * Ψ.card ≤ Fintype.card Ω) :
    2 * symmetricity G ≤ Fintype.card Ω := by
  have hs : symmetricity G ≤ Fintype.card Ω / 2 := by
    refine Finset.sup_le fun Ψ hΨ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    have := h Ψ hΨ
    omega
  omega

/-- `2 s(G) ≤ |Ω|` is the integer form of the paper's "symmetry defect `≥ 1/2`". -/
theorem half_le_defect {G : Subgroup (Equiv.Perm Ω)}
    (h : 2 * symmetricity G ≤ Fintype.card Ω) : 1 / 2 ≤ defect G := by
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · have hs : symmetricity G = 0 := by
      have := symmetricity_le_card G; omega
    rw [defect, relSymmetricity, hs, h0]
    norm_num
  · have hn : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast hpos
    have hle : (symmetricity G : ℚ) / (Fintype.card Ω : ℚ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn]
      have : (2 : ℚ) * (symmetricity G : ℚ) ≤ (Fintype.card Ω : ℚ) := by exact_mod_cast h
      linarith
    rw [defect, relSymmetricity]
    linarith

/-- Examples 2.3.14.  "The symmetry defect of `S_n` is `0`."  (All of `Ω` is one twin
class.) -/
theorem symDefect_top : symDefect (⊤ : Subgroup (Equiv.Perm Ω)) = 0 := by
  classical
  have : IsTwinSet (⊤ : Subgroup (Equiv.Perm Ω)) (↑(Finset.univ : Finset Ω) : Set Ω) :=
    fun x _ y _ hxy => ⟨hxy, Subgroup.mem_top _⟩
  have hle := le_symmetricity this
  simp only [Finset.card_univ] at hle
  have := symmetricity_le_card (⊤ : Subgroup (Equiv.Perm Ω))
  unfold symDefect
  omega

/-- Examples 2.3.14.  "…and the symmetry defect of `A_n` is `n - 1`."  (The alternating
group contains no transposition, so all twin classes are singletons.  With truncated
subtraction on `ℕ` the statement also holds for `n ≤ 1`, so no hypothesis is needed.) -/
theorem symDefect_alternating :
    symDefect (alternatingGroup Ω) = Fintype.card Ω - 1 := by
  classical
  -- a transposition is odd, so no two points are twins
  have hle : symmetricity (alternatingGroup Ω) ≤ 1 := by
    refine symmetricity_le fun Ψ hΨ => ?_
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hc
    have hmem := (hΨ x (by simpa using hx) y (by simpa using hy) hxy).2
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hxy] at hmem
    exact absurd hmem (by decide)
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · have hz : symmetricity (alternatingGroup Ω) = 0 := by
      have := symmetricity_le_card (alternatingGroup Ω)
      omega
    rw [symDefect, hz, h0]
  · have hge : 1 ≤ symmetricity (alternatingGroup Ω) := by
      obtain ⟨x⟩ := Fintype.card_pos_iff.1 hpos
      have hts : IsTwinSet (alternatingGroup Ω) (↑({x} : Finset Ω) : Set Ω) := by
        intro a ha b hb hab
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
        exact absurd (ha.trans hb.symm) hab
      simpa using le_symmetricity hts
    rw [symDefect]
    omega

/-- Examples 2.3.14.  "If `Ω = Ω₁ ∪ Ω₂` (disjointly) and `G = S(Ω₁) × S(Ω₂)` then the
symmetry defect of `G` is `min(|Ω₁|, |Ω₂|)`."

Here `G = S(Ω₁) × S(Ω₂)` is realized inside `S(Ω)` as the join `symOn Ω₁ ⊔ symOn Ω₂`
(Convention 2.3.8). -/
theorem symDefect_prod (Ω₁ Ω₂ : Set Ω) (hdisj : Disjoint Ω₁ Ω₂)
    (hcov : Ω₁ ∪ Ω₂ = Set.univ) :
    symDefect (symOn Ω₁ ⊔ symOn Ω₂) = min Ω₁.ncard Ω₂.ncard := by
  classical
  have hmemcov : ∀ x : Ω, x ∈ Ω₁ ∨ x ∈ Ω₂ := by
    intro x
    have : x ∈ Ω₁ ∪ Ω₂ := by rw [hcov]; trivial
    exact this
  have hdisj' : ∀ x : Ω, x ∈ Ω₁ → x ∈ Ω₂ → False := fun x h1 h2 =>
    (Set.disjoint_left.1 hdisj h1) h2
  -- both factors preserve `Ω₁` setwise, hence so does the group they generate
  let K : Subgroup (Equiv.Perm Ω) :=
    { carrier := {σ | ∀ x : Ω, x ∈ Ω₁ ↔ σ x ∈ Ω₁}
      one_mem' := fun _ => Iff.rfl
      mul_mem' := fun {a b} ha hb x => (hb x).trans (ha (b x))
      inv_mem' := fun {a} ha x => by
        have h := ha (a⁻¹ x)
        simpa using h.symm }
  have hK₁ : symOn Ω₁ ≤ K := by
    intro σ hσ x
    constructor
    · intro hx
      by_contra hσx
      have heq : σ x = x := σ.injective (hσ (σ x) hσx)
      exact hσx (by rw [heq]; exact hx)
    · intro hσx
      by_contra hx
      exact hx (hσ x hx ▸ hσx)
  have hK₂ : symOn Ω₂ ≤ K := by
    intro σ hσ x
    have hfix : ∀ z : Ω, z ∈ Ω₁ → σ z = z := fun z hz => hσ z (fun hz₂ => hdisj' z hz hz₂)
    constructor
    · intro hx; rw [hfix x hx]; exact hx
    · intro hσx
      by_contra hx
      rcases hmemcov x with h | h
      · exact hx h
      · -- `σ` maps `Ω₂` into `Ω₂`, which is disjoint from `Ω₁`
        have hσx₂ : σ x ∈ Ω₂ := by
          by_contra hc
          have heq : σ x = x := σ.injective (hσ (σ x) hc)
          exact hc (by rw [heq]; exact h)
        exact hdisj' (σ x) hσx hσx₂
  have hle : symOn Ω₁ ⊔ symOn Ω₂ ≤ K := sup_le hK₁ hK₂
  -- a set of twins lies entirely in `Ω₁` or entirely in `Ω₂`
  have hsymle : symmetricity (symOn Ω₁ ⊔ symOn Ω₂) ≤ max Ω₁.ncard Ω₂.ncard := by
    refine symmetricity_le fun Ψ hΨ => ?_
    by_cases h1 : ∀ x ∈ Ψ, x ∈ Ω₁
    · have hc : Ψ.card ≤ Ω₁.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        exact Finset.card_le_card fun x hx => Set.mem_toFinset.2 (h1 x hx)
      omega
    · push_neg at h1
      obtain ⟨y, hyΨ, hyΩ₁⟩ := h1
      have hyΩ₂ : y ∈ Ω₂ := (hmemcov y).resolve_left hyΩ₁
      have h2 : ∀ x ∈ Ψ, x ∈ Ω₂ := by
        intro x hx
        by_cases hxy : x = y
        · exact hxy ▸ hyΩ₂
        by_contra hxΩ₂
        have hxΩ₁ : x ∈ Ω₁ := (hmemcov x).resolve_right hxΩ₂
        have htwin := hΨ x (by simpa using hx) y (by simpa using hyΨ) hxy
        have hswap := hle htwin.2 x
        rw [Equiv.swap_apply_left] at hswap
        exact hyΩ₁ (hswap.1 hxΩ₁)
      have hc : Ψ.card ≤ Ω₂.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        exact Finset.card_le_card fun x hx => Set.mem_toFinset.2 (h2 x hx)
      omega
  -- both parts are sets of twins
  have hsymge : max Ω₁.ncard Ω₂.ncard ≤ symmetricity (symOn Ω₁ ⊔ symOn Ω₂) := by
    have hpart : ∀ Δ : Set Ω, symOn Δ ≤ symOn Ω₁ ⊔ symOn Ω₂ → Δ.ncard ≤
        symmetricity (symOn Ω₁ ⊔ symOn Ω₂) := by
      intro Δ hΔ
      have hts : IsTwinSet (symOn Ω₁ ⊔ symOn Ω₂) (↑Δ.toFinset : Set Ω) := by
        rw [isTwinSet_iff_symOn_le, Set.coe_toFinset]
        exact hΔ
      have := le_symmetricity hts
      rwa [← Set.ncard_eq_toFinset_card'] at this
    exact max_le (hpart Ω₁ le_sup_left) (hpart Ω₂ le_sup_right)
  have hsym : symmetricity (symOn Ω₁ ⊔ symOn Ω₂) = max Ω₁.ncard Ω₂.ncard :=
    le_antisymm hsymle hsymge
  have hcard : Ω₁.ncard + Ω₂.ncard = Fintype.card Ω := by
    have h := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    rw [hcov, Set.ncard_univ, Nat.card_eq_fintype_card] at h
    omega
  rw [symDefect, hsym]
  omega

/-- Observation 2.3.15.  "The symmetry defect is monotone decreasing: if `H ≤ G` then
`defect(H) ≥ defect(G)`." -/
theorem defect_antitone {H G : Subgroup (Equiv.Perm Ω)} (h : H ≤ G) :
    defect G ≤ defect H := by
  classical
  have hs : symmetricity H ≤ symmetricity G := by
    refine Finset.sup_le fun Ψ hΨ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    exact le_symmetricity (fun x hx y hy hxy => ⟨(hΨ x hx y hy hxy).1, h (hΨ x hx y hy hxy).2⟩)
  unfold defect relSymmetricity
  have hn : (0 : ℚ) ≤ (Fintype.card Ω : ℚ) := by positivity
  have : (symmetricity H : ℚ) ≤ (symmetricity G : ℚ) := by exact_mod_cast hs
  gcongr

end Symmetricity

/-! ### Definition 2.3.16: symmetricity and symmetry defect of structures -/

/-- Definition 2.3.16, preamble.  "By 'structure' in the next statement we mean any
member of a concrete category; the only thing that matters is that a structure `X` has an
underlying set `Ω` and the automorphisms of `X` are permutations of `Ω`.  Examples we
shall use are relational structures and hypergraphs."

We record this as a class: a type `X` of structures with underlying vertex set `Ω` and an
automorphism group inside `S(Ω)`. -/
class IsStructure (X : Type*) (Ω : outParam (Type*)) where
  /-- The automorphism group of a structure, a subgroup of `S(Ω)`. -/
  autGroup : X → Subgroup (Equiv.Perm Ω)

instance : IsStructure (RelStructure Ω) Ω := ⟨RelStructure.Aut⟩

section StructDefect

variable {X : Type*} [IsStructure X Ω] [Fintype Ω] [DecidableEq Ω]

/-- Definition 2.3.16.  "We say that `x, y ∈ Ω` are *twins with respect to `X`* if they
are twins with respect to `Aut(X)`." -/
def structIsTwin (x : X) (a b : Ω) : Prop := IsTwin (IsStructure.autGroup x) a b

/-- Definition 2.3.16.  The (absolute) symmetricity of a structure. -/
noncomputable def structSymmetricity (x : X) : ℕ := symmetricity (IsStructure.autGroup x)

/-- Definition 2.3.16.  The absolute symmetry defect of a structure. -/
noncomputable def structSymDefect (x : X) : ℕ := symDefect (IsStructure.autGroup x)

/-- Definition 2.3.16.  "We use the notation `defect(X)` to denote `defect(Aut(X))`." -/
noncomputable def structDefect (x : X) : ℚ := defect (IsStructure.autGroup x)

end StructDefect

end Babai
