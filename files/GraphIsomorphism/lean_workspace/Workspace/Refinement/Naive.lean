/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4 (introduction), 4.1 (Naive vertex-refinement) and 4.1.1 (tagged structures).
-/
import Workspace.Refinement.Iterate
import Workspace.Prelim.BinaryRelations
import Mathlib.Data.Finset.Sort

/-!
# §4 Individualization and canonical refinement; §4.1 naive vertex-refinement

§4 is headed "ADD DETAILS" in version 2.5 and §4.1.1 ends with "TO BE WRITTEN"; §4.2
("Weisfeiler–Leman canonical refinement") is a heading with no body.  What §4 *does* say
is formalized here and in `Refinement/Bipartite.lean` and `Refinement/WL.lean`; where the
text stops, the constructions are completed in the paper's style and the completion is
recorded in the corrected paper "hole in 2.5".

## Objects

§4.1: *"Let `X = (V, E, c)` be a vertex-colored digraph without loops, i.e.
`E ⊆ (V × V) \ diag(V)` and `c : V → C` is a vertex coloring."*  `ColoredDigraph` carries
`E` and `c`; looplessness is the predicate `IsLoopless`, imposed where the paper uses it.
The untagged refinement uses structured colors. Tagged standardization uses the
paper's order to give the realized colors consecutive ranks and to record their sorted list.

## The number of rounds

The refinement process stops "when `X_k` is stable".  To keep the process canonical we run
it for a fixed number of rounds, `|V × V|`, which is at least the number of rounds any
input needs (`Refinement/Iterate.lean`); the result is stable
(`stableRefine_isStable`), which is the paper's `X*`.

## Numbering map

| Paper | Lean |
|---|---|
| §4, "a refinement of the coloring `c`" | `Babai.IsRefinement` |
| §4, Eq. (22) (canonicity of a refinement) | `Babai.ColoredDigraph.IsCanonicalRefinement` |
| §4, individualization, Eq. (23) | `Babai.ColoredDigraph.individualize`, `.iso_eq_iUnion_individualize` |
| §4.1, `d⁺ᵢ(x)`, `d⁻ᵢ(x)`, `c'` | `.outDegCol`, `.inDegCol`, `.naiveStep`, `.naiveRefine` |
| §4.1, `Π(c)`, stability | `Babai.kernelSet`, `.IsStable` |
| Observation 4.1.1 | `.isStable_iff_isEquitableColoring` |
| §4.1, the process `X_j`, `X*` | `.naiveIter`, `.stableRefine`, `.stableRefine_isStable` |
| §4.1.1, "terminates in `k ≤ n-1` rounds" | `.exists_isStable_le`, `.naiveIter_isStable_of_le` |
| Observation 4.1.2, Eq. (24) | `.iso_naiveRefine`, `.iso_naiveIter`, `.iso_stableRefine` |
| §4.1.1, tagged colored digraphs, Eq. (25) | `Babai.TaggedDigraph`, `.Iso` |
| §4.1.1, standard form, `st(c)`, `st(X)` | `.IsStandard`, `.standardize` |
| §4.1.1, complexity of naive refinement | polynomial time on the RAM: `Algo.rawStableRefine_spec` (`Algo/RefineRaw.lean`), `Algo.polyFun_rawStableRefine` (`Algo/RefinePoly.lean`) |
| §4.1.1, the tagged process `X_j`, `X*`, `t*`, tag lengths | `Babai.TaggedDigraph.tagIter`, `.stableTagged`, `.finalTag`, `.iso_stableTagged`, `.tagLen_finalTag_le` (`Refinement/TaggedProcess.lean`) |
| §4.1.1, costs `O(nm) + \|t₁\|` and `O(m log n)` | false on the RAM: `Algo.not_Section_4_1_1_cost_statement`, `Algo.not_Section_4_1_1_HopcroftTarjan_statement`; corrected `Algo.Section_4_1_1_cost_corrected_statement` (`Algo/TaggedCost.lean`), proved as `Algo.section_4_1_1_cost_corrected` (`Algo/TagLinCost.lean`) |
-/

namespace Babai

universe u

variable {Ω Ω' : Type*} {C C' C'' : Type*}

/-- §4.  "A *refinement* of the coloring `c` is a new coloring `c'` of the same elements
such that if `c'(x) = c'(y)` for elements `x, y` then `c(x) = c(y)`." -/
def IsRefinement (c' : Ω → C') (c : Ω → C) : Prop := ∀ x y : Ω, c' x = c' y → c x = c y

theorem IsRefinement.refl (c : Ω → C) : IsRefinement c c := fun _ _ h => h

theorem IsRefinement.trans {c'' : Ω → C''} {c' : Ω → C'} {c : Ω → C}
    (h₁ : IsRefinement c'' c') (h₂ : IsRefinement c' c) : IsRefinement c'' c :=
  fun x y h => h₂ x y (h₁ x y h)

/-- §4.1.  "Let `X = (V, E, c)` be a vertex-colored digraph … and `c : V → C` is a vertex
coloring." -/
structure ColoredDigraph (Ω : Type*) (C : Type*) where
  /-- The edge set `E ⊆ V × V`. -/
  E : Set (Ω × Ω)
  /-- The vertex coloring `c : V → C`. -/
  c : Ω → C

namespace ColoredDigraph

variable (X : ColoredDigraph Ω C)

/-- The underlying digraph `(V, E)`. -/
def toDigraph : Digraph Ω := ⟨X.E⟩

/-- §4.1.  "a vertex-colored digraph *without loops*, i.e. `E ⊆ (V × V) \ diag(V)`." -/
def IsLoopless : Prop := X.E ∩ diag Ω = ∅

/-- The same digraph with a new coloring: the paper's `X'` for a refined coloring `c'`. -/
def recolor (d : Ω → C') : ColoredDigraph Ω C' := ⟨X.E, d⟩

@[simp] theorem recolor_E (d : Ω → C') : (X.recolor d).E = X.E := rfl
@[simp] theorem recolor_c (d : Ω → C') : (X.recolor d).c = d := rfl

/-- Isomorphisms of vertex-colored digraphs: edge- and color-preserving bijections. -/
def Iso (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C) : Set (Ω ≃ Ω') :=
  {f | (∀ x y : Ω, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x : Ω, Y.c (f x) = X.c x}

theorem mem_iso_iff {X : ColoredDigraph Ω C} {Y : ColoredDigraph Ω' C} {f : Ω ≃ Ω'} :
    f ∈ Iso X Y ↔ (∀ x y : Ω, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧ ∀ x, Y.c (f x) = X.c x :=
  Iff.rfl

/-- §4, Eq. (22).  "We say that the refinement is *canonical* with respect to a set
`{Xᵢ | i ∈ I}` of objects of the same type if it is executed simultaneously on each `Xᵢ`
and for all `i, j ∈ I` we have `Iso(X'ᵢ, X'ⱼ) = Iso(Xᵢ, Xⱼ)`."

A refinement procedure is an assignment `R` of a new coloring to each colored digraph;
"executed simultaneously" is the fact that the new colors of all the objects live in one
and the same set, which here is the type `C'`.  (This is consistent with the functorial
notion of canonicity of §6, `Workspace/Functors/Basic.lean`.) -/
def IsCanonicalRefinement (R : ∀ {Ω : Type u}, ColoredDigraph Ω C → (Ω → C')) : Prop :=
  ∀ {Ω Ω' : Type u} (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C),
    Iso (X.recolor (R X)) (Y.recolor (R Y)) = Iso X Y

/-- §4.  "Another classical heuristic is *individualization*: the assignment of a unique
color to an element.  Let `X_x` denote `X` with the element `x` individualized." -/
def individualize (x : Ω) : ColoredDigraph Ω (C × Prop) :=
  ⟨X.E, fun v => (X.c v, v = x)⟩

@[simp] theorem individualize_c (x v : Ω) :
    (X.individualize x).c v = (X.c v, v = x) := rfl

/-- §4, Eq. (23).  "if we individualize `x ∈ X`, we need compare `X_x` with all `Y_y` for
`y ∈ Y`: for any `x ∈ X` we have `Iso(X, Y) = ⋃_{y ∈ Y} Iso(X_x, Y_y)`." -/
theorem iso_eq_iUnion_individualize (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C)
    (x : Ω) : Iso X Y = ⋃ y : Ω', Iso (X.individualize x) (Y.individualize y) := by
  ext f
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨f x, hE, fun v => ?_⟩
    refine Prod.ext (hc v) ?_
    show (f v = f x) = (v = x)
    exact propext ⟨fun h => f.injective h, fun h => congrArg f h⟩
  · rintro ⟨y, hE, hc⟩
    exact ⟨hE, fun v => congrArg Prod.fst (hc v)⟩

/-! ### §4.1 The naive refinement step -/

/-- §4.1.  "For vertex `x ∈ V` and each color `i ∈ C`, let `d⁺ᵢ(x)` be the number of
out-neighbors of `x` of color `i`." -/
noncomputable def outDegCol (i : C) (x : Ω) : ℕ := {y : Ω | (x, y) ∈ X.E ∧ X.c y = i}.ncard

/-- §4.1.  "…and `d⁻ᵢ(x)` be the number of in-neighbors of `x` of color `i`." -/
noncomputable def inDegCol (i : C) (x : Ω) : ℕ := {y : Ω | (y, x) ∈ X.E ∧ X.c y = i}.ncard

/-- §4.1.  "Let `c'(x) = (c(x), d⁺ᵢ(x), d⁻ᵢ(x) | i ∈ C)`, where the terms in the string
`c'(x)` are arranged in the order defined by the ordering of `C`.  We regard the set
`C' = {c'(x) | x ∈ V}` of strings as a new set of colors, ordered lexicographically."

The ordering of `C` serves only to lay the numbers `d±ᵢ(x)` out as a string; we keep them
as the functions `i ↦ d±ᵢ(x)`. -/
noncomputable def naiveStep (x : Ω) : C × (C → ℕ) × (C → ℕ) :=
  (X.c x, fun i => X.outDegCol i x, fun i => X.inDegCol i x)

/-- §4.1.  "Let `X' = (V, E, c')`." -/
noncomputable def naiveRefine : ColoredDigraph Ω (C × (C → ℕ) × (C → ℕ)) :=
  X.recolor X.naiveStep

/-- §4.1.  "Clearly, the coloring `c'` is a refinement of `c`." -/
theorem naiveStep_isRefinement : IsRefinement X.naiveStep X.c :=
  fun _ _ h => congrArg Prod.fst h

theorem naiveStep_eq_iff (x y : Ω) :
    X.naiveStep x = X.naiveStep y ↔
      X.c x = X.c y ∧ (∀ i, X.outDegCol i x = X.outDegCol i y) ∧
        ∀ i, X.inDegCol i x = X.inDegCol i y := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, fun i => congrFun (congrArg (fun p => p.2.1) h) i,
      fun i => congrFun (congrArg (fun p => p.2.2) h) i⟩
  · rintro ⟨h1, h2, h3⟩
    exact Prod.ext h1 (Prod.ext (funext h2) (funext h3))

/-- §4.1.  "We say that `X` is *stable with respect to naive vertex-refinement* if
`Π(c') = Π(c)` (no proper refinement is obtained)." -/
def IsStable : Prop := ∀ x y : Ω, X.c x = X.c y → X.naiveStep x = X.naiveStep y

theorem isStable_iff_kernelSet :
    X.IsStable ↔ kernelSet X.naiveStep = kernelSet X.c := by
  constructor
  · intro h
    ext ⟨x, y⟩
    exact ⟨fun hxy => X.naiveStep_isRefinement x y hxy, fun hxy => h x y hxy⟩
  · intro h x y hxy
    have : (x, y) ∈ kernelSet X.naiveStep := by rw [h]; exact hxy
    exact this

/-! #### Observation 4.1.1 -/

section Equitable

variable {X}

theorem outDeg_induced (A : Set Ω) (u : A) :
    (X.toDigraph.induced A).outDeg u = {y : Ω | ((u : Ω), y) ∈ X.E ∧ y ∈ A}.ncard := by
  have himg : Subtype.val '' (outNbr (X.toDigraph.induced A).E u)
      = {y : Ω | ((u : Ω), y) ∈ X.E ∧ y ∈ A} := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
    · rintro ⟨hw, hwA⟩; exact ⟨⟨w, hwA⟩, hw, rfl⟩
  rw [Digraph.outDeg, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem inDeg_induced (A : Set Ω) (u : A) :
    (X.toDigraph.induced A).inDeg u = {y : Ω | (y, (u : Ω)) ∈ X.E ∧ y ∈ A}.ncard := by
  have himg : Subtype.val '' (inNbr (X.toDigraph.induced A).E u)
      = {y : Ω | (y, (u : Ω)) ∈ X.E ∧ y ∈ A} := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
    · rintro ⟨hw, hwA⟩; exact ⟨⟨w, hwA⟩, hw, rfl⟩
  rw [Digraph.inDeg, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem degA_inducedBip (A B : Set Ω) (u : A) :
    (X.toDigraph.inducedBip A B).degA u = {y : Ω | ((u : Ω), y) ∈ X.E ∧ y ∈ B}.ncard := by
  have himg : Subtype.val '' {b : B | (u, b) ∈ (X.toDigraph.inducedBip A B).E}
      = {y : Ω | ((u : Ω), y) ∈ X.E ∧ y ∈ B} := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
    · rintro ⟨hw, hwB⟩; exact ⟨⟨w, hwB⟩, hw, rfl⟩
  rw [BipGraph.degA, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem degB_inducedBip (A B : Set Ω) (w : B) :
    (X.toDigraph.inducedBip A B).degB w = {y : Ω | (y, (w : Ω)) ∈ X.E ∧ y ∈ A}.ncard := by
  have himg : Subtype.val '' {a : A | (a, w) ∈ (X.toDigraph.inducedBip A B).E}
      = {y : Ω | (y, (w : Ω)) ∈ X.E ∧ y ∈ A} := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, hmem, rfl⟩; exact ⟨hmem, ha⟩
    · rintro ⟨hz, hzA⟩; exact ⟨⟨z, hzA⟩, hz, rfl⟩
  rw [BipGraph.degB, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem outDegCol_eq (i : C) (x : Ω) :
    X.outDegCol i x = {y : Ω | (x, y) ∈ X.E ∧ y ∈ X.c ⁻¹' {i}}.ncard := rfl

theorem inDegCol_eq (i : C) (x : Ω) :
    X.inDegCol i x = {y : Ω | (y, x) ∈ X.E ∧ y ∈ X.c ⁻¹' {i}}.ncard := rfl

/-- Observation 4.1.1.  "The vertex-colored digraph `X = (V, E, c)` is stable with respect
to naive vertex-refinement if and only if the partition `Π(c)` is equitable (see
Def. 2.4.26)."

Def. 2.4.26: the partition is equitable if each induced subgraph `X[Ωᵢ]` is biregular and
each induced bipartite subgraph `X[Ωᵢ, Ωⱼ]` (`i ≠ j`) is semiregular.  Both sides say that
for all colors `i, j`, the number of out-neighbors of color `j` and the number of
in-neighbors of color `j` are the same for all vertices of color `i`. -/
theorem isStable_iff_isEquitableColoring :
    X.IsStable ↔ X.toDigraph.IsEquitableColoring X.c := by
  constructor
  · intro h
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ⟨?_, ?_⟩⟩
    · rcases isEmpty_or_nonempty (X.c ⁻¹' {i}) with hA | ⟨⟨u₀⟩⟩
      · exact ⟨0, fun u => (hA.false u).elim⟩
      · refine ⟨X.outDegCol i (u₀ : Ω), fun u => ?_⟩
        rw [outDeg_induced]
        exact ((X.naiveStep_eq_iff _ _).1 (h _ _ ((u.2 : _ = i).trans (u₀.2 : _ = i).symm))).2.1 i
    · rcases isEmpty_or_nonempty (X.c ⁻¹' {i}) with hA | ⟨⟨u₀⟩⟩
      · exact ⟨0, fun u => (hA.false u).elim⟩
      · refine ⟨X.inDegCol i (u₀ : Ω), fun u => ?_⟩
        rw [inDeg_induced]
        exact ((X.naiveStep_eq_iff _ _).1 (h _ _ ((u.2 : _ = i).trans (u₀.2 : _ = i).symm))).2.2 i
    · rcases isEmpty_or_nonempty (X.c ⁻¹' {i}) with hA | ⟨⟨u₀⟩⟩
      · exact ⟨0, fun u => (hA.false u).elim⟩
      · refine ⟨X.outDegCol j (u₀ : Ω), fun u => ?_⟩
        rw [degA_inducedBip]
        exact ((X.naiveStep_eq_iff _ _).1 (h _ _ ((u.2 : _ = i).trans (u₀.2 : _ = i).symm))).2.1 j
    · rcases isEmpty_or_nonempty (X.c ⁻¹' {j}) with hB | ⟨⟨w₀⟩⟩
      · exact ⟨0, fun w => (hB.false w).elim⟩
      · refine ⟨X.inDegCol i (w₀ : Ω), fun w => ?_⟩
        rw [degB_inducedBip]
        exact ((X.naiveStep_eq_iff _ _).1 (h _ _ ((w.2 : _ = j).trans (w₀.2 : _ = j).symm))).2.2 i
  · rintro ⟨hbi, hsemi⟩ x y hxy
    have hx : x ∈ X.c ⁻¹' {X.c x} := rfl
    have hy : y ∈ X.c ⁻¹' {X.c x} := hxy.symm
    refine (X.naiveStep_eq_iff x y).2 ⟨hxy, fun j => ?_, fun j => ?_⟩
    · rcases eq_or_ne (X.c x) j with rfl | hj
      · obtain ⟨⟨d, hd⟩, -⟩ := hbi (X.c x)
        have h1 := hd ⟨x, hx⟩
        have h2 := hd ⟨y, hy⟩
        rw [outDeg_induced] at h1 h2
        exact h1.trans h2.symm
      · obtain ⟨⟨d, hd⟩, -⟩ := hsemi (X.c x) j hj
        have h1 := hd ⟨x, hx⟩
        have h2 := hd ⟨y, hy⟩
        rw [degA_inducedBip] at h1 h2
        exact h1.trans h2.symm
    · rcases eq_or_ne (X.c x) j with rfl | hj
      · obtain ⟨-, ⟨d, hd⟩⟩ := hbi (X.c x)
        have h1 := hd ⟨x, hx⟩
        have h2 := hd ⟨y, hy⟩
        rw [inDeg_induced] at h1 h2
        exact h1.trans h2.symm
      · obtain ⟨-, ⟨d, hd⟩⟩ := hsemi j (X.c x) (Ne.symm hj)
        have h1 := hd ⟨x, hx⟩
        have h2 := hd ⟨y, hy⟩
        rw [degB_inducedBip] at h1 h2
        exact h1.trans h2.symm

end Equitable

/-! ### §4.1 The naive refinement process -/

/-- §4.1.  The color set after `n` rounds of naive refinement: the paper's set of strings
of length `O(n·|V|)` over the alphabet of the previous round. -/
def naiveColorType (C : Type u) : ℕ → Type u
  | 0 => C
  | n + 1 => naiveColorType C n × (naiveColorType C n → ℕ) × (naiveColorType C n → ℕ)

/-- §4.1.  "We now describe the naive vertex-refinement process.  Let `X₀ = X` and
`X_{j+1} = X'_j`.  We write `X_j = (V, E, c_j)`, so `c_{j+1} = c'_j`." -/
noncomputable def naiveIter {C : Type u} (X : ColoredDigraph Ω C) :
    ∀ n : ℕ, Ω → naiveColorType C n
  | 0 => X.c
  | n + 1 => (X.recolor (X.naiveIter n)).naiveStep

@[simp] theorem naiveIter_zero {C : Type u} (X : ColoredDigraph Ω C) :
    X.naiveIter 0 = X.c := rfl

@[simp] theorem naiveIter_succ {C : Type u} (X : ColoredDigraph Ω C) (n : ℕ) :
    X.naiveIter (n + 1) = (X.recolor (X.naiveIter n)).naiveStep := rfl

theorem naiveIter_isRefinement {C : Type u} (X : ColoredDigraph Ω C) (n : ℕ) :
    IsRefinement (X.naiveIter (n + 1)) (X.naiveIter n) :=
  (X.recolor (X.naiveIter n)).naiveStep_isRefinement

theorem naiveIter_isRefinement_c {C : Type u} (X : ColoredDigraph Ω C) :
    ∀ n : ℕ, IsRefinement (X.naiveIter n) X.c
  | 0 => IsRefinement.refl _
  | n + 1 => (X.naiveIter_isRefinement n).trans (X.naiveIter_isRefinement_c n)

theorem naiveIter_isRefinement_le {C : Type u} (X : ColoredDigraph Ω C) {m n : ℕ}
    (h : m ≤ n) : IsRefinement (X.naiveIter n) (X.naiveIter m) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.1 h
    exact IsRefinement.refl _
  | succ p ih =>
    rcases Nat.lt_or_ge m (p + 1) with hlt | hge
    · exact (X.naiveIter_isRefinement p).trans (ih (by omega))
    · obtain rfl : m = p + 1 := le_antisymm h hge
      exact IsRefinement.refl _

/-! ### Observation 4.1.2 and the stable refinement -/

/-- Observation 4.1.2, one round, Eq. (24): "`Iso(X, Y) = Iso(X', Y')`." -/
theorem iso_naiveRefine (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C) :
    Iso X.naiveRefine Y.naiveRefine = Iso X Y := by
  ext f
  constructor
  · rintro ⟨hE, hc⟩
    exact ⟨hE, fun x => congrArg Prod.fst (hc x)⟩
  · rintro ⟨hE, hc⟩
    refine ⟨hE, fun x => ?_⟩
    have hout : ∀ i : C, Y.outDegCol i (f x) = X.outDegCol i x := by
      intro i
      have himg : (f : Ω → Ω') '' {y : Ω | (x, y) ∈ X.E ∧ X.c y = i}
          = {y' : Ω' | (f x, y') ∈ Y.E ∧ Y.c y' = i} := by
        ext w
        constructor
        · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
          exact ⟨(hE x y).1 hy1, (hc y).trans hy2⟩
        · rintro ⟨hw1, hw2⟩
          refine ⟨f.symm w, ⟨(hE x (f.symm w)).2 (by simpa using hw1), ?_⟩, by simp⟩
          rw [← hc (f.symm w)]
          simpa using hw2
      rw [outDegCol, outDegCol, ← himg, Set.ncard_image_of_injective _ f.injective]
    have hin : ∀ i : C, Y.inDegCol i (f x) = X.inDegCol i x := by
      intro i
      have himg : (f : Ω → Ω') '' {y : Ω | (y, x) ∈ X.E ∧ X.c y = i}
          = {y' : Ω' | (y', f x) ∈ Y.E ∧ Y.c y' = i} := by
        ext w
        constructor
        · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
          exact ⟨(hE y x).1 hy1, (hc y).trans hy2⟩
        · rintro ⟨hw1, hw2⟩
          refine ⟨f.symm w, ⟨(hE (f.symm w) x).2 (by simpa using hw1), ?_⟩, by simp⟩
          rw [← hc (f.symm w)]
          simpa using hw2
      rw [inDegCol, inDegCol, ← himg, Set.ncard_image_of_injective _ f.injective]
    exact Prod.ext (hc x) (Prod.ext (funext hout) (funext hin))

/-- Observation 4.1.2, Eq. (24), for every round of the process. -/
theorem iso_naiveIter {C : Type u} (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C) :
    ∀ n : ℕ, Iso (X.recolor (X.naiveIter n)) (Y.recolor (Y.naiveIter n)) = Iso X Y
  | 0 => rfl
  | n + 1 => by
    have h1 : Iso ((X.recolor (X.naiveIter n)).naiveRefine)
        ((Y.recolor (Y.naiveIter n)).naiveRefine)
        = Iso (X.recolor (X.naiveIter n)) (Y.recolor (Y.naiveIter n)) :=
      iso_naiveRefine _ _
    exact h1.trans (iso_naiveIter X Y n)

/-- One direction of `colorCount_congr`. -/
theorem colorCount_congr_mp {E E' : Type*} {e : Ω → E} {e' : Ω → E'}
    (hk : ∀ u v : Ω, e u = e v ↔ e' u = e' v) (P Q : Ω → Prop)
    (h : ∀ i : E, {y : Ω | P y ∧ e y = i}.ncard = {y : Ω | Q y ∧ e y = i}.ncard) :
    ∀ i : E', {y : Ω | P y ∧ e' y = i}.ncard = {y : Ω | Q y ∧ e' y = i}.ncard := by
  classical
  intro i
  by_cases hex : ∃ w : Ω, e' w = i
  · obtain ⟨w, rfl⟩ := hex
    have hP : {y : Ω | P y ∧ e' y = e' w} = {y : Ω | P y ∧ e y = e w} := by
      ext y; exact and_congr_right fun _ => (hk y w).symm
    have hQ : {y : Ω | Q y ∧ e' y = e' w} = {y : Ω | Q y ∧ e y = e w} := by
      ext y; exact and_congr_right fun _ => (hk y w).symm
    rw [hP, hQ]
    exact h (e w)
  · push_neg at hex
    have hP : {y : Ω | P y ∧ e' y = i} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨-, hy⟩
      exact hex y hy
    have hQ : {y : Ω | Q y ∧ e' y = i} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨-, hy⟩
      exact hex y hy
    rw [hP, hQ]

/-- Counting by colors depends on the coloring only through its partition: two colorings
with the same color classes give the same numbers, indexed differently.  (Used for the
termination of the refinement process: one round depends on the previous coloring only
through its partition.) -/
theorem colorCount_congr {D D' : Type*} {d : Ω → D} {d' : Ω → D'}
    (hker : ∀ u v : Ω, d u = d v ↔ d' u = d' v) (P Q : Ω → Prop) :
    ((∀ i : D, {y : Ω | P y ∧ d y = i}.ncard = {y : Ω | Q y ∧ d y = i}.ncard) ↔
      ∀ i : D', {y : Ω | P y ∧ d' y = i}.ncard = {y : Ω | Q y ∧ d' y = i}.ncard) :=
  ⟨colorCount_congr_mp hker P Q, colorCount_congr_mp (fun u v => (hker u v).symm) P Q⟩

/-- One round of naive refinement depends on the current coloring only through its
partition. -/
theorem kernelSet_naiveStep_congr {D D' : Type*} (X : ColoredDigraph Ω C) {d : Ω → D}
    {d' : Ω → D'} (hker : kernelSet d = kernelSet d') :
    kernelSet (X.recolor d).naiveStep = kernelSet (X.recolor d').naiveStep := by
  have hk : ∀ u v : Ω, d u = d v ↔ d' u = d' v := by
    intro u v
    constructor
    · intro huv
      have : (u, v) ∈ kernelSet d' := by rw [← hker]; exact huv
      exact this
    · intro huv
      have : (u, v) ∈ kernelSet d := by rw [hker]; exact huv
      exact this
  ext ⟨x, y⟩
  simp only [mem_kernelSet]
  rw [naiveStep_eq_iff, naiveStep_eq_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(hk x y).1 h1, (colorCount_congr hk (fun z => (x, z) ∈ X.E) fun z => (y, z) ∈ X.E).1 h2,
      (colorCount_congr hk (fun z => (z, x) ∈ X.E) fun z => (z, y) ∈ X.E).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(hk x y).2 h1, (colorCount_congr hk (fun z => (x, z) ∈ X.E) fun z => (y, z) ∈ X.E).2 h2,
      (colorCount_congr hk (fun z => (z, x) ∈ X.E) fun z => (z, y) ∈ X.E).2 h3⟩

/-- §4.1.  "We stop when `X_k` is stable, i.e. when `N(c_{k+1}) = N(c_k)`.  We call the
colored digraph `X* = X_k` the *stable refinement* of `X`."

The process is run for `|V × V|` rounds, a bound valid for every input on the vertex set
`V` (the paper: "The naive refinement process clearly terminates in `k ≤ n-1` rounds"),
which makes the number of rounds independent of the input and hence keeps the process
canonical.  `stableRefine_isStable` shows that the result is stable, so this is the
paper's `X*`. -/
noncomputable def stableRefine {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) :
    ColoredDigraph Ω (naiveColorType C (Fintype.card (Ω × Ω))) :=
  X.recolor (X.naiveIter (Fintype.card (Ω × Ω)))

/-- §4.1.  The stable refinement is stable: the process has terminated. -/
theorem stableRefine_isStable {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) :
    X.stableRefine.IsStable := by
  have hmono : ∀ n, kernelSet (X.naiveIter (n + 1)) ⊆ kernelSet (X.naiveIter n) := by
    intro n p hp
    exact X.naiveIter_isRefinement n p.1 p.2 hp
  have hstep : ∀ n, kernelSet (X.naiveIter (n + 1)) = kernelSet (X.naiveIter n) →
      kernelSet (X.naiveIter (n + 2)) = kernelSet (X.naiveIter (n + 1)) := by
    intro n hn
    exact kernelSet_naiveStep_congr X hn
  have hfix := eq_of_antitone_sets (fun n => kernelSet (X.naiveIter n)) hmono hstep
  have := ((X.recolor (X.naiveIter (Fintype.card (Ω × Ω)))).isStable_iff_kernelSet).2 hfix
  exact this

/-- §4.1.1.  *"The naive refinement process clearly terminates in `k ≤ n-1` rounds."*  After
any number `m ≥ n - 1` of rounds, where `n = |V|`, the coloring is stable.  (The process
`stableRefine` runs `|V × V|` rounds, a bound fixed in advance so that the process is
canonical; by this theorem the coloring is already stable after `n - 1` of them.) -/
theorem naiveIter_isStable_of_le {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) {m : ℕ}
    (hm : Fintype.card Ω - 1 ≤ m) : (X.recolor (X.naiveIter m)).IsStable := by
  have hmono : ∀ n, kernelSet (X.naiveIter (n + 1)) ⊆ kernelSet (X.naiveIter n) := by
    intro n p hp
    exact X.naiveIter_isRefinement n p.1 p.2 hp
  have hstep : ∀ n, kernelSet (X.naiveIter (n + 1)) = kernelSet (X.naiveIter n) →
      kernelSet (X.naiveIter (n + 2)) = kernelSet (X.naiveIter (n + 1)) := by
    intro n hn
    exact kernelSet_naiveStep_congr X hn
  exact ((X.recolor (X.naiveIter m)).isStable_iff_kernelSet).2
    (kernelSet_eq_of_card_sub_one_le (fun n => X.naiveIter n) hmono hstep hm)

/-- §4.1.1, the form of the paper: some `k ≤ n - 1` has `X_k` stable. -/
theorem exists_isStable_le {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) :
    ∃ k ≤ Fintype.card Ω - 1, (X.recolor (X.naiveIter k)).IsStable :=
  ⟨Fintype.card Ω - 1, le_rfl, X.naiveIter_isStable_of_le le_rfl⟩

/-- Observation 4.1.2, Eq. (24), for the stable refinement: "`Iso(X, Y) = Iso(X*, Y*)`." -/
theorem iso_stableRefine {C : Type u} {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (X : ColoredDigraph Ω C) (Y : ColoredDigraph Ω' C)
    (hcard : Fintype.card (Ω × Ω) = Fintype.card (Ω' × Ω')) :
    Iso X.stableRefine (Y.recolor (Y.naiveIter (Fintype.card (Ω × Ω)))) = Iso X Y :=
  iso_naiveIter X Y _

/-- §4.1.  The stable refinement refines the original coloring. -/
theorem stableRefine_isRefinement {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) :
    IsRefinement X.stableRefine.c X.c :=
  X.naiveIter_isRefinement_c _

/-- Observation 4.1.1 for the stable refinement: the partition of `X*` is equitable.  This
is the form used in §4.1.2 (Prop. 4.1.4). -/
theorem stableRefine_isEquitable {C : Type u} [Fintype Ω] (X : ColoredDigraph Ω C) :
    X.toDigraph.IsEquitableColoring X.stableRefine.c :=
  X.stableRefine.isStable_iff_isEquitableColoring.1 X.stableRefine_isStable

end ColoredDigraph

/-! ### §4.1.1 Tagged structures -/

/-- §4.1.1.  "Our objects are *tagged colored digraphs* (without loops), i.e. quadruples
`X = (V, E, c, t)` where `E ⊆ (V × V) \ diag(V)`, `c : V → C` is a coloring, and `t` is
the 'tag' (a string)."  The alphabet `Σ` of §4.1.1 is a type parameter. -/
structure TaggedDigraph (Ω : Type*) (C : Type*) (Alph : Type*) extends ColoredDigraph Ω C where
  /-- The tag: a string over the alphabet `Σ`. -/
  tag : List Alph

namespace TaggedDigraph

variable {Alph : Type*}

open scoped Classical in
/-- §4.1.1, Eq. (25).  "For two tagged colored digraphs `X` and `Y = (W, F, d, u)` we set
`Iso(X, Y) = Iso((V,E,c),(W,F,d))` if `u = t`, and `Iso(X, Y) = ∅` if `u ≠ t`." -/
def Iso (X : TaggedDigraph Ω C Alph) (Y : TaggedDigraph Ω' C Alph) : Set (Ω ≃ Ω') :=
  if Y.tag = X.tag then ColoredDigraph.Iso X.toColoredDigraph Y.toColoredDigraph else ∅

theorem iso_of_tag_eq {X : TaggedDigraph Ω C Alph} {Y : TaggedDigraph Ω' C Alph}
    (h : Y.tag = X.tag) :
    Iso X Y = ColoredDigraph.Iso X.toColoredDigraph Y.toColoredDigraph := by
  simp [Iso, h]

theorem iso_of_tag_ne {X : TaggedDigraph Ω C Alph} {Y : TaggedDigraph Ω' C Alph}
    (h : Y.tag ≠ X.tag) : Iso X Y = ∅ := by simp [Iso, h]

/-- §4.1.1.  "We say that the coloring `c` is in *standard form* if `C = [N(c)]` where
`N(c)` is the size of the range of `c`."  (With `C` a type, standard form means that the
coloring is onto its color type, which is what the renumbering achieves.) -/
def IsStandard (X : TaggedDigraph Ω C Alph) : Prop := Function.Surjective X.c

/-- Membership in Eq. (25) records tag equality and the untagged isomorphism. -/
theorem mem_iso_iff {X : TaggedDigraph Ω C Alph} {Y : TaggedDigraph Ω' C Alph}
    {f : Ω ≃ Ω'} : f ∈ Iso X Y ↔
      Y.tag = X.tag ∧ f ∈ ColoredDigraph.Iso X.toColoredDigraph Y.toColoredDigraph := by
  by_cases ht : Y.tag = X.tag <;> simp [Iso, ht]

/-- Change only the vertex colors, retaining the graph and tag. -/
def recolor (X : TaggedDigraph Ω C Alph) (d : Ω → C') : TaggedDigraph Ω C' Alph where
  E := X.E
  c := d
  tag := X.tag

/-- Compare finite color numbers in their common ambient type `ℕ`. This embedding
fixes every color number and does not permit color renaming. -/
def natColors {n : ℕ} (X : TaggedDigraph Ω (Fin n) Alph) : TaggedDigraph Ω ℕ Alph :=
  X.recolor (fun v => (X.c v).val)

section Standardize

variable [Fintype Ω] [Fintype Ω'] [LinearOrder C]

/-- §4.1.1. The colors that occur in the input. -/
def realizedColors (X : TaggedDigraph Ω C Alph) : Finset C := Finset.univ.image X.c

/-- §4.1.1. The ordered list of old colors, each listed exactly once. -/
def oldColors (X : TaggedDigraph Ω C Alph) : List C := X.realizedColors.sort (· ≤ ·)

theorem oldColors_nodup (X : TaggedDigraph Ω C Alph) : X.oldColors.Nodup :=
  X.realizedColors.sort_nodup _

theorem oldColors_sorted (X : TaggedDigraph Ω C Alph) : X.oldColors.Pairwise (· ≤ ·) :=
  X.realizedColors.pairwise_sort _

@[simp] theorem mem_oldColors (X : TaggedDigraph Ω C Alph) (c : C) :
    c ∈ X.oldColors ↔ ∃ v, X.c v = c := by
  simp [oldColors, realizedColors]

/-- A constant coloring on a nonempty domain has exactly one history entry.
In particular, the one-vertex example cannot choose an empty or repeated history. -/
theorem oldColors_of_constant [Nonempty Ω] (X : TaggedDigraph Ω C Alph) (c : C)
    (hc : ∀ v, X.c v = c) : X.oldColors = [c] := by
  have hp : X.realizedColors = {c} := by
    ext d
    simp [realizedColors, hc, eq_comm]
  simp [oldColors, hp]

/-- §4.1.1. Replace each realized color by its rank in the sorted palette `Fin N`
and append the sorted old palette to the tag. The disjoint sum separates old tag
letters from color history, so both lists can be recovered. -/
noncomputable def standardize (X : TaggedDigraph Ω C Alph) :
    TaggedDigraph Ω (Fin X.realizedColors.card) (Alph ⊕ C) where
  E := X.E
  c := fun v => (X.realizedColors.orderIsoOfFin rfl).symm
    ⟨X.c v, Finset.mem_image.2 ⟨v, Finset.mem_univ _, rfl⟩⟩
  tag := X.tag.map Sum.inl ++ X.oldColors.map Sum.inr

/-- §4.1.1. Every rank in the standard palette is realized. -/
theorem standardize_isStandard (X : TaggedDigraph Ω C Alph) :
    X.standardize.IsStandard := by
  intro i
  obtain ⟨v, _, hv⟩ := Finset.mem_image.1 (X.realizedColors.orderIsoOfFin rfl i).property
  refine ⟨v, ?_⟩
  change (X.realizedColors.orderIsoOfFin rfl).symm _ = i
  apply (X.realizedColors.orderIsoOfFin rfl).injective
  simp only [OrderIso.apply_symm_apply]
  exact Subtype.ext hv

/-- The rank of a color is its index in the saved sorted list. -/
theorem standardize_color_val (X : TaggedDigraph Ω C Alph) (v : Ω) :
    (X.standardize.c v).val = X.oldColors.idxOf (X.c v) := rfl

/-- Both the old tag and the old colors are recoverable from the new tag. -/
theorem standardize_tag_eq_iff (X : TaggedDigraph Ω C Alph) (Y : TaggedDigraph Ω' C Alph) :
    Y.standardize.tag = X.standardize.tag ↔
      Y.tag = X.tag ∧ Y.oldColors = X.oldColors := by
  constructor
  · intro h
    constructor
    · have hl := congrArg (List.filterMap Sum.getLeft?) h
      simpa [standardize, List.filterMap_map, Function.comp_def] using hl
    · have hr := congrArg (List.filterMap Sum.getRight?) h
      simpa [standardize, List.filterMap_map, Function.comp_def] using hr
  · rintro ⟨ht, hc⟩
    simp only [standardize, ht, hc]

/-- A color-preserving bijection preserves the sorted list of realized colors. -/
theorem oldColors_eq_of_preserves {X : TaggedDigraph Ω C Alph}
    {Y : TaggedDigraph Ω' C Alph} (f : Ω ≃ Ω') (hc : ∀ v, Y.c (f v) = X.c v) :
    Y.oldColors = X.oldColors := by
  have hp : Y.realizedColors = X.realizedColors := by
    ext c
    simp only [realizedColors, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨f.symm v, by simpa using (hc (f.symm v)).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨f v, hc v⟩
  exact congrArg (fun s : Finset C => s.sort (· ≤ ·)) hp

/-- §4.1.1, lines 2901–2904. The new tag is an isomorphism invariant. -/
theorem standardize_tag_eq_of_iso {X : TaggedDigraph Ω C Alph}
    {Y : TaggedDigraph Ω' C Alph} {f : Ω ≃ Ω'} (hf : f ∈ Iso X Y) :
    Y.standardize.tag = X.standardize.tag := by
  obtain ⟨ht, _, hc⟩ := mem_iso_iff.1 hf
  exact (standardize_tag_eq_iff X Y).2 ⟨ht, oldColors_eq_of_preserves f hc⟩

/-- §4.1.1 and Eq. (24). Standardization keeps exactly the input isomorphisms.
The two palettes are `Fin N(X)` and `Fin N(Y)`. Embedding their ranks in `ℕ`
compares the same color numbers even before their sizes are known to agree. -/
theorem iso_standardize (X : TaggedDigraph Ω C Alph) (Y : TaggedDigraph Ω' C Alph) :
    Iso X.standardize.natColors Y.standardize.natColors = Iso X Y := by
  ext f
  rw [mem_iso_iff, mem_iso_iff]
  change (Y.standardize.tag = X.standardize.tag ∧
    (∀ x y, (x, y) ∈ X.E ↔ (f x, f y) ∈ Y.E) ∧
    ∀ x, (Y.standardize.c (f x)).val = (X.standardize.c x).val) ↔ _
  rw [standardize_tag_eq_iff]
  constructor
  · rintro ⟨⟨ht, hp⟩, hE, hc⟩
    refine ⟨ht, hE, fun x => ?_⟩
    have hr := hc x
    rw [standardize_color_val, standardize_color_val, hp] at hr
    exact ((List.idxOf_inj ((X.mem_oldColors (X.c x)).2 ⟨x, rfl⟩)).1 hr.symm).symm
  · rintro ⟨ht, hE, hc⟩
    have hp := oldColors_eq_of_preserves f hc
    refine ⟨⟨ht, hp⟩, hE, fun x => ?_⟩
    rw [standardize_color_val, standardize_color_val, hp, hc x]

/-- Eq. (24) with an explicit cast between equal finite palettes. This is the
same comparison as `iso_standardize`, expressed in the palette of the first input. -/
theorem iso_standardize_cast (X : TaggedDigraph Ω C Alph) (Y : TaggedDigraph Ω' C Alph)
    (h : Y.realizedColors.card = X.realizedColors.card) :
    Iso X.standardize (Y.standardize.recolor (fun v => Fin.cast h (Y.standardize.c v))) =
      Iso X Y := by
  rw [← iso_standardize X Y]
  ext f
  simp only [mem_iso_iff, ColoredDigraph.mem_iso_iff, recolor, natColors, Fin.ext_iff,
    Fin.val_cast]

/-- Eq. (24) for automorphisms, using the actual finite palette. -/
theorem iso_standardize_self (X : TaggedDigraph Ω C Alph) :
    Iso X.standardize X.standardize = Iso X X := by
  simpa [recolor] using iso_standardize_cast X X rfl

/-- §4.1.1. Unequal new tags reject the original inputs too. -/
theorem iso_eq_empty_of_standardize_tag_ne {X : TaggedDigraph Ω C Alph}
    {Y : TaggedDigraph Ω' C Alph} (h : Y.standardize.tag ≠ X.standardize.tag) :
    Iso X Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro f hf
  exact h (standardize_tag_eq_of_iso hf)

/-- Identical inputs retain their identity isomorphism after standardization.
There is no free history list with which to reject a second copy of the input. -/
theorem standardize_identity (X : TaggedDigraph Ω C Alph) :
    Equiv.refl Ω ∈ Iso X.standardize X.standardize := by
  simp [Iso, ColoredDigraph.Iso]

end Standardize

/-- §4.1.1.  "Each tag `t_j` is an isomorphism invariant, justifying the second line on the
right-hand side of Eq. (25) (isomorphism rejection if the tags are not equal)." -/
theorem iso_eq_empty_of_tag_ne {X : TaggedDigraph Ω C Alph} {Y : TaggedDigraph Ω' C Alph}
    (h : Y.tag ≠ X.tag) : Iso X Y = ∅ := iso_of_tag_ne h

end TaggedDigraph

end Babai
