/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 4.1.2: Splitting a semiregular bipartite graph – minor savings.
-/
import Workspace.Refinement.Naive

/-!
# §4.1.2 Splitting a semiregular bipartite graph

§4.1.2: *"Let `X = (Ω₁, Ω₂; E)` be a bipartite graph, so `E ⊆ Ω₁ × Ω₂`.  Let `nᵢ = |Ωᵢ|`."*
*"Let `X = (Ω₁, Ω₂; E)` be a bipartite graph and `f : Ω₂ → C` be a `k`-coloring of `Ω₂`.
In this section we shall view such a coloring `f` as a `(k+1)`-coloring of the vertices of
`X` by assigning `Ω₁` a separate color."*

## Naive refinement of `(Ω₁, Ω₂; E, f)`, and how it is recorded here

One round of naive refinement (§4.1) assigns to `a ∈ Ω₁` the numbers `d⁺ᵢ(a)`, `i ∈ C`,
the number of neighbours of `a` of color `i` (its in-degrees are `0` and its own color is
the separate color of `Ω₁`).  This is `refineA` below, and `naiveStep_inl_eq_iff` is the
bridge: two vertices of `Ω₁` get the same color in one round of naive refinement of the
colored digraph exactly if `refineA` gives them the same vector.  Since the stable
refinement refines one round, the upper bounds proved here for one round hold a fortiori
for the stable refinement, which is what the paper's statements are about.

"`f` yields a `(p/q)`-coloring of `Ω₁`" — each color-subclass of `Ω₁` has size at most
`(p/q)·n₁` — is `ClassesLe X f p q`, written without division.

## Numbering map

| Paper | Lean |
|---|---|
| §4.1.2, the coloring induced on `Ω₁` | `Babai.BipGraph.refineA`, `.naiveStep_inl_eq_iff` |
| §4.1.2, "`f` yields an `α`-coloring of `Ω₁`" | `Babai.BipGraph.ClassesLe`, `.RoundClassesLe` |
| §4.1.2, prefixes `P_k` | `Babai.BipGraph.pref` |
| Observation 4.1.3 | `Babai.BipGraph.refineA_injective_of_no_twins` |
| Claim 4.1.6 | `Babai.BipGraph.exists_prefix_nbhd` |
| Lemma 4.1.5 | `Babai.BipGraph.exists_two_coloring` |
| Prop. 4.1.4, "`Y` is not complete" | `Babai.BipGraph.exists_nbr_not_complete` |
| Prop. 4.1.4, "`Y` is semiregular since `h` is equitable" | `.ncard_nbrB_eq_of_stable`, `.ncard_nbrA_eq_of_stable` |
| Prop. 4.1.4, "`h*` is a refinement of `h` because `f` is a refinement of `g`" | `Babai.ColoredDigraph.stableRefine_mono` |
| Proposition 4.1.4 | `Babai.BipGraph.exists_three_coloring` |
| §4.1.2, "the multiplicative cost … is `3^{n₂}`" | `Babai.BipGraph.card_three_colorings` |
-/

namespace Babai

universe u

variable {A B C : Type*}

/-! ### Auxiliary: naive refinement is monotone for refinement of the input coloring

The proof of Prop. 4.1.4 uses twice that a finer input coloring gives a finer output
("`h*` is a refinement of `h` because `f` is a refinement of `g`").  Nothing here is in
the paper beyond that sentence. -/

open scoped Classical in
/-- `Set.ncard` of a set-builder set over a finite type, as a `Finset.card`. -/
theorem ncard_setOf_of_fintype {α : Type*} [Fintype α] (p : α → Prop) :
    {x | p x}.ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

open scoped Classical in
/-- Counting a finite set by the fibers of a map, over any finset containing the relevant
values. -/
theorem ncard_fiberwise' {α : Type*} [Fintype α] {D : Type*} (p : α → Prop) (d : α → D)
    (T : Finset D) (hp : ∀ x, p x → d x ∈ T) :
    {x | p x}.ncard = ∑ j ∈ T, {x | p x ∧ d x = j}.ncard := by
  have H : ∀ x ∈ Finset.univ.filter p, d x ∈ T := fun x hx => hp x (by simpa using hx)
  rw [ncard_setOf_of_fintype, Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ncard_setOf_of_fintype]
  congr 1
  ext x
  simp

open scoped Classical in
/-- Counting by a coarser coloring: if two conditions `P`, `Q` select equally many elements
of each color of `d`, then they select equally many of each color of any coarsening
`G ∘ d` of `d`.  (The color types are not assumed finite, so the fibers are collected over
the image of `d`, which is finite because `α` is.) -/
theorem ncard_comp_congr {α : Type*} [Finite α] {D D' : Type*} (d : α → D) (G : D → D')
    (P Q : α → Prop)
    (h : ∀ j : D, {x | P x ∧ d x = j}.ncard = {x | Q x ∧ d x = j}.ncard) (i : D') :
    {x | P x ∧ G (d x) = i}.ncard = {x | Q x ∧ G (d x) = i}.ncard := by
  cases nonempty_fintype α
  set T : Finset D := (Finset.univ.image d).filter (fun j => G j = i) with hT
  have key : ∀ R : α → Prop,
      {x | R x ∧ G (d x) = i}.ncard = ∑ j ∈ T, {x | R x ∧ d x = j}.ncard := by
    intro R
    rw [ncard_fiberwise' (fun x => R x ∧ G (d x) = i) d T
      (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ x), hx.2⟩)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : G j = i := (Finset.mem_filter.1 hj).2
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, by rw [hx.2]; exact hj'⟩, hx.2⟩⟩
  rw [key P, key Q]
  exact Finset.sum_congr rfl fun j _ => h j

namespace ColoredDigraph

variable {Ω : Type*}

/-- A finer input coloring gives a finer output after one round of naive refinement. -/
theorem naiveStep_mono [Finite Ω] {D D' : Type*} (X : ColoredDigraph Ω C) {d : Ω → D}
    {d' : Ω → D'} (hr : IsRefinement d d') :
    IsRefinement (X.recolor d).naiveStep (X.recolor d').naiveStep := by
  classical
  rcases isEmpty_or_nonempty Ω with hE | hNE
  · intro x; exact (hE.false x).elim
  obtain ⟨y₀⟩ := hNE
  -- the coarser coloring is a function `G` of the finer one
  obtain ⟨G, hG⟩ : ∃ G : D → D', ∀ z : Ω, G (d z) = d' z := by
    refine ⟨fun j => if hj : ∃ z : Ω, d z = j then d' hj.choose else d' y₀, fun z => ?_⟩
    have hj : ∃ z' : Ω, d z' = d z := ⟨z, rfl⟩
    show (if hj' : ∃ z' : Ω, d z' = d z then d' hj'.choose else d' y₀) = d' z
    rw [dif_pos hj]
    exact hr _ _ hj.choose_spec
  intro x y hxy
  obtain ⟨h1, h2, h3⟩ := ((X.recolor d).naiveStep_eq_iff x y).1 hxy
  refine ((X.recolor d').naiveStep_eq_iff x y).2 ⟨hr _ _ h1, fun i => ?_, fun i => ?_⟩
  · have e : ∀ w : Ω, {z : Ω | (w, z) ∈ X.E ∧ d' z = i}
        = {z : Ω | (w, z) ∈ X.E ∧ G (d z) = i} := by
      intro w; ext z; simp only [Set.mem_setOf_eq, hG]
    show {z : Ω | (x, z) ∈ X.E ∧ d' z = i}.ncard = {z : Ω | (y, z) ∈ X.E ∧ d' z = i}.ncard
    rw [e x, e y]
    exact ncard_comp_congr d G _ _ (fun j => h2 j) i
  · have e : ∀ w : Ω, {z : Ω | (z, w) ∈ X.E ∧ d' z = i}
        = {z : Ω | (z, w) ∈ X.E ∧ G (d z) = i} := by
      intro w; ext z; simp only [Set.mem_setOf_eq, hG]
    show {z : Ω | (z, x) ∈ X.E ∧ d' z = i}.ncard = {z : Ω | (z, y) ∈ X.E ∧ d' z = i}.ncard
    rw [e x, e y]
    exact ncard_comp_congr d G _ _ (fun j => h3 j) i

/-- A finer input coloring gives a finer output after `n` rounds of naive refinement. -/
theorem naiveIter_mono [Finite Ω] {D D' : Type u} (X : ColoredDigraph Ω C) {d : Ω → D}
    {d' : Ω → D'} (hr : IsRefinement d d') :
    ∀ n : ℕ, IsRefinement ((X.recolor d).naiveIter n) ((X.recolor d').naiveIter n)
  | 0 => hr
  | n + 1 => naiveStep_mono X (X.naiveIter_mono hr n)

/-- A finer input coloring gives a finer stable refinement. -/
theorem stableRefine_mono [Fintype Ω] {D D' : Type u} (X : ColoredDigraph Ω C) {d : Ω → D}
    {d' : Ω → D'} (hr : IsRefinement d d') :
    IsRefinement (X.recolor d).stableRefine.c (X.recolor d').stableRefine.c :=
  X.naiveIter_mono hr _

end ColoredDigraph

namespace BipGraph

/-- §4.1.2.  `X(S)`, the neighborhood in `Ω₁` of a set `S ⊆ Ω₂`. -/
def nbhdA (X : BipGraph A B) (S : Set B) : Set A := {a : A | ∃ b ∈ S, (a, b) ∈ X.E}

/-- §4.1.2.  The coloring of `Ω₁` produced by one round of naive refinement of the
colored bipartite graph `(Ω₁, Ω₂; E, f)`: the vertex `a ∈ Ω₁` receives the vector of the
numbers of its neighbours of each color. -/
noncomputable def refineA (X : BipGraph A B) (f : B → C) (a : A) : C → ℕ :=
  fun i => {b : B | (a, b) ∈ X.E ∧ f b = i}.ncard

/-- §4.1.2.  The bound of Prop. 4.1.4 and Lemma 4.1.5 after *one round* of naive
refinement: every class of the coloring `refineA` of `Ω₁` has size `≤ (p/q)·|Ω₁|`,
written without division. -/
def RoundClassesLe [Fintype A] (X : BipGraph A B) (f : B → C) (p q : ℕ) : Prop :=
  ∀ a : A, q * {a' : A | X.refineA f a' = X.refineA f a}.ncard ≤ p * Fintype.card A

/-- §4.1.2.  The colored digraph of §4.1 attached to `(Ω₁, Ω₂; E, f)`: the vertices of
`Ω₁` all receive one separate color (`none`). -/
def toColoredDigraph (X : BipGraph A B) (f : B → C) : ColoredDigraph (A ⊕ B) (Option C) where
  E := X.toDigraph.E
  c := Sum.elim (fun _ => none) (fun b => some (f b))

/-- The bridge between `refineA` and §4.1's naive refinement step: one round of naive
refinement separates two vertices of `Ω₁` exactly if `refineA` does. -/
theorem naiveStep_inl_eq_iff (X : BipGraph A B) (f : B → C) (a a' : A) :
    (X.toColoredDigraph f).naiveStep (Sum.inl a) = (X.toColoredDigraph f).naiveStep (Sum.inl a')
      ↔ X.refineA f a = X.refineA f a' := by
  have hout : ∀ (u : A) (j : C),
      (X.toColoredDigraph f).outDegCol (some j) (Sum.inl u) = X.refineA f u j := by
    intro u j
    have hset : {v : A ⊕ B | (Sum.inl u, v) ∈ (X.toColoredDigraph f).E ∧
        (X.toColoredDigraph f).c v = some j}
        = Sum.inr '' {b : B | (u, b) ∈ X.E ∧ f b = j} := by
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩
        obtain ⟨p, q, hp, hq, hpq⟩ := hv1
        have hpu : Sum.inl u = (Sum.inl p : A ⊕ B) := hp
        have hqv : v = Sum.inr q := hq
        have hup : u = p := by simpa using hpu
        refine ⟨q, ⟨?_, ?_⟩, hqv.symm⟩
        · rw [hup]; exact hpq
        · rw [hqv] at hv2
          simpa [toColoredDigraph] using hv2
      · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
        exact ⟨⟨u, b, rfl, rfl, hb1⟩, by simpa [toColoredDigraph] using hb2⟩
    rw [ColoredDigraph.outDegCol, hset, Set.ncard_image_of_injective _ Sum.inr_injective]
    rfl
  have houtn : ∀ u : A, (X.toColoredDigraph f).outDegCol none (Sum.inl u) = 0 := by
    intro u
    have hset : {v : A ⊕ B | (Sum.inl u, v) ∈ (X.toColoredDigraph f).E ∧
        (X.toColoredDigraph f).c v = none} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hv1, hv2⟩
      obtain ⟨p, q, -, hq, -⟩ := hv1
      have hqv : v = Sum.inr q := hq
      rw [hqv] at hv2
      exact absurd hv2 (by simp [toColoredDigraph])
    rw [ColoredDigraph.outDegCol, hset, Set.ncard_empty]
  have hin : ∀ (u : A) (i : Option C), (X.toColoredDigraph f).inDegCol i (Sum.inl u) = 0 := by
    intro u i
    have hset : {v : A ⊕ B | (v, Sum.inl u) ∈ (X.toColoredDigraph f).E ∧
        (X.toColoredDigraph f).c v = i} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro v ⟨hv1, -⟩
      obtain ⟨p, q, -, hq, -⟩ := hv1
      have : (Sum.inl u : A ⊕ B) = Sum.inr q := hq
      exact absurd this (by simp)
    rw [ColoredDigraph.inDegCol, hset, Set.ncard_empty]
  constructor
  · intro h
    funext j
    have hd := (((X.toColoredDigraph f).naiveStep_eq_iff _ _).1 h).2.1 (some j)
    rw [hout a j, hout a' j] at hd
    exact hd
  · intro h
    refine ((X.toColoredDigraph f).naiveStep_eq_iff _ _).2 ⟨rfl, fun i => ?_, fun i => ?_⟩
    · cases i with
      | none => rw [houtn a, houtn a']
      | some j => rw [hout a j, hout a' j]; exact congrFun h j
    · rw [hin a i, hin a' i]

/-- §4.1.2.  "`f` yields a `(p/q)`-coloring of `Ω₁`: each color-subclass of `Ω₁` has size
`≤ (p/q)·|Ω₁|`", written without division.  Here "the coloring of `Ω₁` yielded by `f`" is
the coloring of `Ω₁` produced by the naive refinement process of §4.1 run to stability on
the colored bipartite graph `(Ω₁, Ω₂; E, f)`, which is what §4.1 calls "naive refinement".
-/
def ClassesLe [Fintype A] [Fintype B] (X : BipGraph A B) (f : B → C) (p q : ℕ) : Prop :=
  ∀ a : A, q * {a' : A | (X.toColoredDigraph f).stableRefine.c (Sum.inl a')
      = (X.toColoredDigraph f).stableRefine.c (Sum.inl a)}.ncard ≤ p * Fintype.card A

/-- A bound after one round of naive refinement holds a fortiori after refining to
stability, since the stable refinement refines every round. -/
theorem classesLe_of_roundClassesLe [Fintype A] [Fintype B] [Nonempty A] (X : BipGraph A B)
    (f : B → C) {p q : ℕ} (h : X.RoundClassesLe f p q) : X.ClassesLe f p q := by
  classical
  intro a
  have hsub : {a' : A | (X.toColoredDigraph f).stableRefine.c (Sum.inl a')
      = (X.toColoredDigraph f).stableRefine.c (Sum.inl a)}
      ⊆ {a' : A | X.refineA f a' = X.refineA f a} := by
    intro a' ha'
    have hN : 1 ≤ Fintype.card ((A ⊕ B) × (A ⊕ B)) := Fintype.card_pos
    have h1 := (X.toColoredDigraph f).naiveIter_isRefinement_le hN (Sum.inl a') (Sum.inl a) ha'
    have h2 : (X.toColoredDigraph f).naiveStep (Sum.inl a')
        = (X.toColoredDigraph f).naiveStep (Sum.inl a) := h1
    exact (X.naiveStep_inl_eq_iff f a' a).1 h2
  exact le_trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub (Set.toFinite _))) (h a)

/-! ### Observation 4.1.3 -/

/-- Observation 4.1.3.  "Let `X = (Ω₁, Ω₂; E)` be a bipartite graph.  If there are no twins
in `Ω₁` then individualizing each element of `Ω₂` completely splits `Ω₁`."

Individualizing every element of `Ω₂` is the coloring `f = id : Ω₂ → Ω₂`; "completely
splits `Ω₁`" is that the resulting coloring of `Ω₁` is injective.  (Observation 2.4.28(b),
`Babai.BipGraph.isTwin_inl_iff_aux`, identifies twins in `Ω₁` with equality of
neighborhoods.) -/
theorem refineA_injective_of_no_twins [DecidableEq A] [DecidableEq B] (X : BipGraph A B)
    (h : ∀ x y : A, x ≠ y → ¬ IsTwin X.Aut (Sum.inl x) (Sum.inl y)) :
    Function.Injective (X.refineA (id : B → B)) := by
  classical
  intro x y hxy
  by_contra hne
  refine h x y hne ((X.isTwin_inl_iff_aux x y hne).2 ?_)
  ext b
  have hb : ∀ a : A, X.refineA (id : B → B) a b = if (a, b) ∈ X.E then 1 else 0 := by
    intro a
    by_cases hab : (a, b) ∈ X.E
    · have hset : {b' : B | (a, b') ∈ X.E ∧ id b' = b} = {b} := by
        ext b'
        constructor
        · rintro ⟨-, rfl⟩; rfl
        · rintro rfl; exact ⟨hab, rfl⟩
      rw [refineA, hset, Set.ncard_singleton, if_pos hab]
    · have hset : {b' : B | (a, b') ∈ X.E ∧ id b' = b} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro b' ⟨hb', rfl⟩
        exact hab hb'
      rw [refineA, hset, Set.ncard_empty, if_neg hab]
  have := congrFun hxy b
  rw [hb x, hb y] at this
  by_cases hx : (x, b) ∈ X.E <;> by_cases hy : (y, b) ∈ X.E <;>
    simp_all

/-! ### Claim 4.1.6 and Lemma 4.1.5 -/

/-- §4.1.2, proof of Lemma 4.1.5: *"Let us fix an ordering of `Ω₂ = {v₁, …, v_{n₂}}`.  The
prefix `P_k` in this ordering is the subset `P_k = {v₁, …, v_k}`."* -/
def pref {n : ℕ} (v : Fin n → B) (k : ℕ) : Set B := {b | ∃ i : Fin n, (i : ℕ) < k ∧ v i = b}

/-- Claim 4.1.6.  "There is a prefix `P_k` of which the neighborhood `X(P_k)` has size
`n₁/3 < |X(P_k)| ≤ 2n₁/3`."

The hypotheses are those in force where the claim is stated (inside the proof of
Lemma 4.1.5): `X` is semiregular of degree `d₂` on `Ω₂` with `d₂ ≤ n₁/2` (the paper's
`deg₂ ≤ n₁/2`, obtained there from the density assumption), and every vertex of `Ω₁` has a
neighbor (`X` is nontrivial and semiregular).  Both inequalities are written without
division.

The paper's proof reads *"`|X(P_k)| ≤ |X(P_{k-1})| + deg₂ < n₂/3 + deg₂`, so we are done if
`deg₂ ≤ n₂/3`.  If `deg₂ > n₂/3` then we necessarily have `k = 1`"*; the three occurrences
of `n₂` there are typos for `n₁` (the bound concerns a subset of `Ω₁`, and `deg₂ ≤ n₁/2` is
a bound in terms of `n₁`).  See the corrected paper 4.1.6. -/
theorem exists_prefix_nbhd [Fintype A] [Fintype B] (X : BipGraph A B)
    (hA1 : 0 < Fintype.card A) (hA : ∀ a : A, ∃ b, (a, b) ∈ X.E)
    (d₂ : ℕ) (hd₂ : ∀ b, X.degB b = d₂) (hhalf : 2 * d₂ ≤ Fintype.card A)
    (v : Fin (Fintype.card B) ≃ B) :
    ∃ k, Fintype.card A < 3 * (X.nbhdA (pref v k)).ncard ∧
      3 * (X.nbhdA (pref v k)).ncard ≤ 2 * Fintype.card A := by
  classical
  have hfull : X.nbhdA (pref v (Fintype.card B)) = Set.univ := by
    ext a
    simp only [Set.mem_univ, iff_true]
    obtain ⟨b, hb⟩ := hA a
    exact ⟨b, ⟨v.symm b, (v.symm b).isLt, v.apply_symm_apply b⟩, hb⟩
  have hP : ∃ k, Fintype.card A < 3 * (X.nbhdA (pref v k)).ncard := by
    refine ⟨Fintype.card B, ?_⟩
    rw [hfull, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  have hk := Nat.find_spec hP
  have hmin : ∀ m, m < Nat.find hP → ¬ (Fintype.card A < 3 * (X.nbhdA (pref v m)).ncard) :=
    fun m hm => Nat.find_min hP hm
  have hk0 : Nat.find hP ≠ 0 := by
    intro h0
    have hempty : X.nbhdA (pref v 0) = ∅ := by
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨b, ⟨i, hi, rfl⟩, -⟩
      omega
    rw [h0, hempty, Set.ncard_empty] at hk
    omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hP = m + 1 := ⟨Nat.find hP - 1, by omega⟩
  rw [hm] at hk hmin ⊢
  have hmn : m < Fintype.card B := by
    by_contra hcon
    push_neg at hcon
    have heq : pref v m = pref v (m + 1) := by
      ext b
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨i, lt_of_lt_of_le i.isLt hcon, rfl⟩
    exact hmin m (by omega) (by rw [heq]; exact hk)
  have hdeg : ∀ (j : Fin (Fintype.card B)), {a : A | (a, v j) ∈ X.E}.ncard = d₂ := fun j => hd₂ _
  have hstep : X.nbhdA (pref v (m + 1))
      ⊆ X.nbhdA (pref v m) ∪ {a : A | (a, v ⟨m, hmn⟩) ∈ X.E} := by
    rintro a ⟨b, ⟨i, hi, rfl⟩, hab⟩
    rcases Nat.lt_or_ge (i : ℕ) m with h | h
    · exact Or.inl ⟨v i, ⟨i, h, rfl⟩, hab⟩
    · have hieq : i = ⟨m, hmn⟩ := by
        apply Fin.ext
        simp only []
        omega
      exact Or.inr (by rw [← hieq]; exact hab)
  have hcard : (X.nbhdA (pref v (m + 1))).ncard ≤ (X.nbhdA (pref v m)).ncard + d₂ := by
    have h1 := Set.ncard_le_ncard hstep (Set.toFinite _)
    have h2 := Set.ncard_union_le (X.nbhdA (pref v m)) {a : A | (a, v ⟨m, hmn⟩) ∈ X.E}
    have h3 := hdeg ⟨m, hmn⟩
    omega
  rcases Nat.lt_or_ge (Fintype.card A) (3 * d₂) with hbig | hsmall
  · -- `deg₂ > n₁/3`: then `k = 1`, and `|X(P₁)| = deg₂ ≤ n₁/2 ≤ 2n₁/3`
    have h0 : (0 : ℕ) < Fintype.card B := by omega
    have hpref1 : X.nbhdA (pref v 1) = {a : A | (a, v ⟨0, h0⟩) ∈ X.E} := by
      ext a
      constructor
      · rintro ⟨b, ⟨i, hi, rfl⟩, hab⟩
        have hieq : i = ⟨0, h0⟩ := by
          apply Fin.ext
          simp only []
          omega
        rw [← hieq]; exact hab
      · intro ha
        exact ⟨v ⟨0, h0⟩, ⟨⟨0, h0⟩, by norm_num, rfl⟩, ha⟩
    have h1 : Fintype.card A < 3 * (X.nbhdA (pref v 1)).ncard := by
      rw [hpref1, hdeg ⟨0, h0⟩]; omega
    have hm0 : m = 0 := by
      by_contra hne
      exact hmin 1 (by omega) h1
    subst hm0
    rw [hpref1, hdeg ⟨0, h0⟩]
    omega
  · -- `deg₂ ≤ n₁/3`: minimality of `k` bounds `|X(P_{k-1})|` by `n₁/3`
    have hprev := hmin m (by omega)
    push_neg at hprev
    omega

/-- §4.1.2.  The coloring of `Ω₁` after one round of naive refinement is unchanged, as a
partition, when one passes to the bipartite complement: the number of neighbors of `a` of
color `i` in `X^c` is `|f⁻¹(i)|` minus the number in `X`.  This makes the paper's opening
move in the proof of Lemma 4.1.5 ("by complementing if necessary") legitimate. -/
theorem refineA_compl [Fintype B] (X : BipGraph A B) (f : B → C) (a : A) (i : C) :
    X.compl.refineA f a i = {b : B | f b = i}.ncard - X.refineA f a i := by
  classical
  have hsub : {b : B | (a, b) ∈ X.E ∧ f b = i} ⊆ {b : B | f b = i} := fun b hb => hb.2
  have hdiff : {b : B | (a, b) ∈ X.compl.E ∧ f b = i}
      = {b : B | f b = i} \ {b : B | (a, b) ∈ X.E ∧ f b = i} := by
    ext b
    constructor
    · rintro ⟨hb1, hb2⟩
      have hnot : (a, b) ∉ X.E := hb1.2
      exact ⟨hb2, fun hc => hnot hc.1⟩
    · rintro ⟨hb1, hb2⟩
      exact ⟨⟨Set.mem_univ _, fun hc => hb2 ⟨hc, hb1⟩⟩, hb1⟩
  rw [refineA, hdiff, Set.ncard_diff hsub (Set.toFinite _)]
  rfl

/-- The one-round coloring of `Ω₁` in `X` and in the bipartite complement of `X` have the
same classes. -/
theorem refineA_compl_class [Fintype B] (X : BipGraph A B) (f : B → C) (a : A) :
    {a' : A | X.compl.refineA f a' = X.compl.refineA f a}
      = {a' : A | X.refineA f a' = X.refineA f a} := by
  classical
  have hle : ∀ (u : A) (i : C), X.refineA f u i ≤ {b : B | f b = i}.ncard := by
    intro u i
    exact Set.ncard_le_ncard (fun b hb => hb.2) (Set.toFinite _)
  ext a'
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    funext i
    have h1 := congrFun h i
    rw [refineA_compl, refineA_compl] at h1
    have := hle a' i
    have := hle a i
    omega
  · intro h
    funext i
    rw [refineA_compl, refineA_compl, congrFun h i]

/-- Lemma 4.1.5, main case.  This is the situation reached in the paper's proof after the
opening reduction: `X` is semiregular with `deg₂ = d₂ ≤ n₁/2`, and every vertex of `Ω₁`
has a neighbor.  The conclusion is the bound after one round of naive refinement, which
implies the bound for the naive refinement process (`classesLe_of_roundClassesLe`). -/
theorem exists_two_coloring_aux [Fintype A] [Fintype B] (X : BipGraph A B)
    (hA1 : 0 < Fintype.card A) (hA : ∀ a : A, ∃ b, (a, b) ∈ X.E)
    (d₂ : ℕ) (hd₂ : ∀ b, X.degB b = d₂) (hhalf : 2 * d₂ ≤ Fintype.card A) :
    ∃ g : B → Fin 2, X.RoundClassesLe g 2 3 := by
  classical
  obtain ⟨k, hk1, hk2⟩ := X.exists_prefix_nbhd hA1 hA d₂ hd₂ hhalf (Fintype.equivFin B).symm
  set P : Set B := pref (Fintype.equivFin B).symm k with hPdef
  refine ⟨fun b => if b ∈ P then 0 else 1, ?_⟩
  intro a
  -- membership in `X(P)` is determined by the refined color
  have hmem : ∀ u : A, u ∈ X.nbhdA P ↔ X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) u 0 ≠ 0 := by
    intro u
    have hset : {b : B | (u, b) ∈ X.E ∧ (if b ∈ P then (0 : Fin 2) else 1) = 0}
        = {b : B | (u, b) ∈ X.E ∧ b ∈ P} := by
      ext b
      by_cases hb : b ∈ P <;> simp [hb]
    have hval : X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) u 0
        = {b : B | (u, b) ∈ X.E ∧ b ∈ P}.ncard := by
      show {b : B | (u, b) ∈ X.E ∧ (if b ∈ P then (0 : Fin 2) else 1) = 0}.ncard = _
      rw [hset]
    have hiff : X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) u 0 ≠ 0
        ↔ {b : B | (u, b) ∈ X.E ∧ b ∈ P}.Nonempty := by
      rw [hval]
      exact (not_congr (Set.ncard_eq_zero (Set.toFinite _))).trans
        Set.nonempty_iff_ne_empty.symm
    rw [hiff]
    constructor
    · rintro ⟨b, hbP, hub⟩; exact ⟨b, hub, hbP⟩
    · rintro ⟨b, hub, hbP⟩; exact ⟨b, hbP, hub⟩
  have hNle : (X.nbhdA P).ncard ≤ Fintype.card A := by
    have := Set.ncard_le_ncard (Set.subset_univ (X.nbhdA P)) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  by_cases ha : a ∈ X.nbhdA P
  · have hsub : {a' : A | X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) a'
        = X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) a} ⊆ X.nbhdA P := by
      intro a' ha'
      refine (hmem a').2 ?_
      rw [Set.mem_setOf_eq] at ha'
      rw [congrFun ha' 0]
      exact (hmem a).1 ha
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · have hsub : {a' : A | X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) a'
        = X.refineA (fun b => if b ∈ P then (0 : Fin 2) else 1) a} ⊆ (X.nbhdA P)ᶜ := by
      intro a' ha'
      rw [Set.mem_setOf_eq] at ha'
      intro hc
      exact ha ((hmem a).2 (by rw [← congrFun ha' 0]; exact (hmem a').1 hc))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_add_ncard_compl (X.nbhdA P)
    rw [Nat.card_eq_fintype_card] at h2
    omega

/-- Lemma 4.1.5.  "Let `X = (Ω₁, Ω₂; E)` be a nontrivial semiregular bipartite graph.  Then
there is a 2-coloring `g : Ω₂ → [2]` such that the naive refinement of the colored
bipartite graph `(Ω₁, Ω₂; E, g)` yields a `(2/3)`-coloring of `Ω₁`: each color-class in
`Ω₁` will have size `≤ 2|Ω₁|/3`."

The paper's opening reduction *"by complementing if necessary, we may assume that the
density of `X` is `|E|/(n₁n₂) ≤ 1/2`"* is used here only through its consequence
`deg₂ ≤ n₁/2`, so the case distinction below is made directly on `2·deg₂ ≤ n₁`; in the
other case the bipartite complement has `deg₂^c = n₁ - deg₂ ≤ n₁/2`, and
`refineA_compl_class` carries the conclusion back to `X`. -/
theorem exists_two_coloring [Fintype A] [Fintype B] (X : BipGraph A B)
    (hnt : ¬ X.IsTrivial) (hsr : X.IsSemiregular) :
    ∃ g : B → Fin 2, X.RoundClassesLe g 2 3 := by
  classical
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := hsr
  have hne : X.E ≠ ∅ := fun h => hnt (Or.inl h)
  have hnu : X.E ≠ Set.univ := fun h => hnt (Or.inr h)
  obtain ⟨⟨a₀, b₀⟩, hab₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hA1 : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a₀⟩
  have hB1 : 0 < Fintype.card B := Fintype.card_pos_iff.2 ⟨b₀⟩
  -- every vertex of `Ω₁` has a neighbor, and misses some vertex of `Ω₂`
  have hd₁pos : 0 < d₁ := by
    have : 0 < X.degA a₀ := by
      rw [degA, Set.ncard_pos (Set.toFinite _)]
      exact ⟨b₀, hab₀⟩
    rw [hd₁ a₀] at this; exact this
  have hA : ∀ a : A, ∃ b, (a, b) ∈ X.E := by
    intro a
    have : 0 < {b : B | (a, b) ∈ X.E}.ncard := by rw [← degA, hd₁ a]; exact hd₁pos
    obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite _)).1 this
    exact ⟨b, hb⟩
  obtain ⟨⟨a₁, b₁⟩, hab₁⟩ : ∃ p : A × B, p ∉ X.E := by
    by_contra hcon
    push_neg at hcon
    exact hnu (Set.eq_univ_of_forall hcon)
  have hd₁lt : d₁ < Fintype.card B := by
    have hss : {b : B | (a₁, b) ∈ X.E} ⊂ Set.univ :=
      ⟨Set.subset_univ _, fun hc => hab₁ (hc (Set.mem_univ b₁))⟩
    have := Set.ncard_lt_ncard hss (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, ← degA, hd₁ a₁] at this
    exact this
  have hd₂le : d₂ ≤ Fintype.card A := by
    have : X.degB b₀ ≤ Fintype.card A := by
      have := Set.ncard_le_ncard (Set.subset_univ {a : A | (a, b₀) ∈ X.E}) (Set.toFinite _)
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
    rw [hd₂ b₀] at this; exact this
  rcases Nat.lt_or_ge (Fintype.card A) (2 * d₂) with hhalf | hhalf
  swap
  · exact X.exists_two_coloring_aux hA1 hA d₂ hd₂ hhalf
  · -- pass to the bipartite complement
    have hAc : ∀ a : A, ∃ b, (a, b) ∈ X.compl.E := by
      intro a
      have hpos : 0 < X.compl.degA a := by
        rw [degA_compl, hd₁ a]; omega
      rw [degA, Set.ncard_pos (Set.toFinite _)] at hpos
      obtain ⟨b, hb⟩ := hpos
      exact ⟨b, hb⟩
    have hd₂c : ∀ b, X.compl.degB b = Fintype.card A - d₂ := by
      intro b; rw [degB_compl, hd₂ b]
    obtain ⟨g, hg⟩ := X.compl.exists_two_coloring_aux hA1 hAc (Fintype.card A - d₂) hd₂c
      (by omega)
    refine ⟨g, ?_⟩
    intro a
    have := hg a
    rwa [refineA_compl_class] at this

/-! ### Proposition 4.1.4 -/

/-- In a nontrivial semiregular bipartite graph every vertex of `Ω₁` has a neighbor.  (Used
in the proofs of Lemma 4.1.5 and Prop. 4.1.4.) -/
theorem exists_nbr [Fintype A] [Fintype B] (X : BipGraph A B) (hnt : ¬ X.IsTrivial)
    (hsr : X.IsSemiregular) (a : A) : ∃ b, (a, b) ∈ X.E := by
  classical
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := hsr
  have hne : X.E ≠ ∅ := fun h => hnt (Or.inl h)
  obtain ⟨⟨a₀, b₀⟩, hab₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hd₁pos : 0 < d₁ := by
    have h0 : 0 < X.degA a₀ := by
      rw [degA, Set.ncard_pos (Set.toFinite _)]
      exact ⟨b₀, hab₀⟩
    rw [hd₁ a₀] at h0; exact h0
  have : 0 < {b : B | (a, b) ∈ X.E}.ncard := by rw [← degA, hd₁ a]; exact hd₁pos
  obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite _)).1 this
  exact ⟨b, hb⟩

/-- Stability of a coloring of `(Ω₁ ⊔ Ω₂)` (Obs. 4.1.1), on the `Ω₁` side: two vertices of
`Ω₁` of the same color have equally many neighbors of each color. -/
theorem ncard_nbrB_eq_of_stable {D : Type*} (X : BipGraph A B) (Y : ColoredDigraph (A ⊕ B) D)
    (hE : Y.E = X.toDigraph.E) (hst : Y.IsStable) {u u' : A}
    (h : Y.c (Sum.inl u) = Y.c (Sum.inl u')) (col : D) :
    {b : B | (u, b) ∈ X.E ∧ Y.c (Sum.inr b) = col}.ncard
      = {b : B | (u', b) ∈ X.E ∧ Y.c (Sum.inr b) = col}.ncard := by
  classical
  have hset : ∀ w : A, {v : A ⊕ B | (Sum.inl w, v) ∈ Y.E ∧ Y.c v = col}
      = Sum.inr '' {b : B | (w, b) ∈ X.E ∧ Y.c (Sum.inr b) = col} := by
    intro w
    ext v
    constructor
    · rintro ⟨hv1, hv2⟩
      rw [hE] at hv1
      obtain ⟨p, q, hp, hq, hpq⟩ := hv1
      have hwp : w = p := by simpa using (hp : (Sum.inl w : A ⊕ B) = Sum.inl p)
      refine ⟨q, ⟨by rw [hwp]; exact hpq, ?_⟩, hq.symm⟩
      rw [← hq]; exact hv2
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      exact ⟨by rw [hE]; exact ⟨w, b, rfl, rfl, hb1⟩, hb2⟩
  have hd := ((Y.naiveStep_eq_iff (Sum.inl u) (Sum.inl u')).1 (hst _ _ h)).2.1 col
  rw [ColoredDigraph.outDegCol, ColoredDigraph.outDegCol, hset u, hset u',
    Set.ncard_image_of_injective _ Sum.inr_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective] at hd
  exact hd

/-- Stability of a coloring of `(Ω₁ ⊔ Ω₂)` (Obs. 4.1.1), on the `Ω₂` side. -/
theorem ncard_nbrA_eq_of_stable {D : Type*} (X : BipGraph A B) (Y : ColoredDigraph (A ⊕ B) D)
    (hE : Y.E = X.toDigraph.E) (hst : Y.IsStable) {w w' : B}
    (h : Y.c (Sum.inr w) = Y.c (Sum.inr w')) (col : D) :
    {a : A | (a, w) ∈ X.E ∧ Y.c (Sum.inl a) = col}.ncard
      = {a : A | (a, w') ∈ X.E ∧ Y.c (Sum.inl a) = col}.ncard := by
  classical
  have hset : ∀ z : B, {v : A ⊕ B | (v, Sum.inr z) ∈ Y.E ∧ Y.c v = col}
      = Sum.inl '' {a : A | (a, z) ∈ X.E ∧ Y.c (Sum.inl a) = col} := by
    intro z
    ext v
    constructor
    · rintro ⟨hv1, hv2⟩
      rw [hE] at hv1
      obtain ⟨p, q, hp, hq, hpq⟩ := hv1
      have hzq : z = q := by simpa using (hq : (Sum.inr z : A ⊕ B) = Sum.inr q)
      refine ⟨p, ⟨by rw [hzq]; exact hpq, ?_⟩, hp.symm⟩
      rw [← hp]; exact hv2
    · rintro ⟨aa, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨by rw [hE]; exact ⟨aa, z, rfl, rfl, ha1⟩, ha2⟩
  have hd := ((Y.naiveStep_eq_iff (Sum.inr w) (Sum.inr w')).1 (hst _ _ h)).2.2 col
  rw [ColoredDigraph.inDegCol, ColoredDigraph.inDegCol, hset w, hset w',
    Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inl_injective] at hd
  exact hd

/-- The step *"`Y` is not complete"* of the proof of Prop. 4.1.4, in the form in which it
is true.

The paper justifies it by *"`deg(y) ≤ n₁/2 < |Γ|`"*, but `deg₂ ≤ n₁/2` is an assumption
made inside the proof of Lemma 4.1.5 (*"by complementing if necessary"*) and is not
available in the proof of Prop. 4.1.4, where `X` is an arbitrary nontrivial semiregular
bipartite graph.  What is true, and is all the proof uses, is that the neighbor `y` of
`x` can be *chosen* so that `X[Γ, Δ_y]` is not complete: if for every neighbor `y` of `x`
every vertex of `Γ` were joined to all of `Δ_y`, then every `u ∈ Γ` would have
`N(x) ⊆ N(u)`, hence `N(u) = N(x) =: S` because `X` is semiregular; then every vertex of
`S` would have at least `|Γ| > n₁/2` neighbors and every vertex outside `S` at most
`n₁ - |Γ| < n₁/2`, so, `X` being semiregular, `S = Ω₂` or `S = ∅`, and in both cases `X`
would be trivial.  See the corrected paper. 4.1.4.

The classes `Γ` and `Δ_y` enter only through `a ∈ Γ`, `|Γ| > n₁/2` and `y ∈ Δ_y`. -/
theorem exists_nbr_not_complete [Fintype A] [Fintype B] (X : BipGraph A B)
    (hnt : ¬ X.IsTrivial) (hsr : X.IsSemiregular) (Γ : Set A) (a : A) (haΓ : a ∈ Γ)
    (P : B → Set B) (hP : ∀ b : B, b ∈ P b)
    (hdom : Fintype.card A < 2 * Γ.ncard) :
    ∃ y : B, (a, y) ∈ X.E ∧ ∃ u ∈ Γ, ∃ b ∈ P y, (u, b) ∉ X.E := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every `u ∈ Γ` is joined to every neighbor of `a`
  have hsub : ∀ u ∈ Γ, {b : B | (a, b) ∈ X.E} ⊆ {b : B | (u, b) ∈ X.E} := by
    intro u hu b hb
    exact hcon b hb u hu b (hP b)
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := hsr
  have heq : ∀ u ∈ Γ, {b : B | (u, b) ∈ X.E} = {b : B | (a, b) ∈ X.E} := by
    intro u hu
    refine (Set.eq_of_subset_of_ncard_le (hsub u hu) (le_of_eq ?_) (Set.toFinite _)).symm
    show {b : B | (u, b) ∈ X.E}.ncard = {b : B | (a, b) ∈ X.E}.ncard
    rw [← degA, ← degA, hd₁ u, hd₁ a]
  -- `S = N(a)` is either all of `Ω₂` or empty
  by_cases hall : ∀ b : B, (a, b) ∈ X.E
  · -- `N(a) = Ω₂`, so every vertex of `Ω₁` is joined to everything: `X` is complete
    have hd₁B : d₁ = Fintype.card B := by
      have h1 : {b : B | (a, b) ∈ X.E} = Set.univ := Set.eq_univ_of_forall hall
      have := hd₁ a
      rw [degA, h1, Set.ncard_univ, Nat.card_eq_fintype_card] at this
      exact this.symm
    refine hnt (Or.inr (Set.eq_univ_of_forall ?_))
    rintro ⟨u, b⟩
    have h2 : {b : B | (u, b) ∈ X.E} = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (le_of_eq ?_) (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, ← hd₁B, ← hd₁ u, degA]
    have : b ∈ {b : B | (u, b) ∈ X.E} := by rw [h2]; trivial
    exact this
  · push_neg at hall
    obtain ⟨b₁, hb₁⟩ := hall
    -- a vertex outside `N(a)` has no neighbor in `Γ`
    have hout : {u : A | (u, b₁) ∈ X.E} ⊆ Γᶜ := by
      intro u hu hcΓ
      have : b₁ ∈ {b : B | (u, b) ∈ X.E} := hu
      rw [heq u hcΓ] at this
      exact hb₁ this
    have hd₂le : d₂ ≤ Fintype.card A - Γ.ncard := by
      have h1 : {u : A | (u, b₁) ∈ X.E}.ncard ≤ (Γᶜ : Set A).ncard :=
        Set.ncard_le_ncard hout (Set.toFinite _)
      have h2 := Set.ncard_add_ncard_compl Γ
      rw [Nat.card_eq_fintype_card] at h2
      rw [← degB, hd₂ b₁] at h1
      omega
    -- a neighbor of `a` has all of `Γ` among its neighbors
    obtain ⟨y, hy⟩ := X.exists_nbr hnt ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ a
    have hin : Γ ⊆ {u : A | (u, y) ∈ X.E} := by
      intro u hu
      have : y ∈ {b : B | (u, b) ∈ X.E} := by rw [heq u hu]; exact hy
      exact this
    have hd₂ge : Γ.ncard ≤ d₂ := by
      have := Set.ncard_le_ncard hin (Set.toFinite _)
      rw [← degB, hd₂ y] at this
      exact this
    omega

/-- Proposition 4.1.4.  "Let `X = (Ω₁, Ω₂; E)` be a nontrivial semiregular bipartite graph.
Then there is a 3-coloring `f : Ω₂ → [3]` such that naive refinement of the colored
bipartite graph `(Ω₁, Ω₂; E, f)` yields a `(1/2)`-coloring of `Ω₁`: each color-subclass of
`Ω₁` has size `≤ |Ω₁|/2`."

The paper's proof: take `g` from Lemma 4.1.5 and let `h` be the coloring after naive
refinement of `(Ω₁, Ω₂; E, g)`.  If every `h`-color class in `Ω₁` has size `≤ n₁/2`, take
`f := g`.  Otherwise there is a dominant class `Γ ⊆ Ω₁` with `n₁/2 < |Γ| ≤ 2n₁/3`; pick an
edge `(x,y)` with `x ∈ Γ`, let `Δ` be the `h`-class of `y`, and let `Y = X[Γ, Δ]`.  Then
`Y` is nontrivial (it has the edge `(x,y)`, and is not complete since
`deg(y) ≤ n₁/2 < |Γ|`) and semiregular (because `h` is equitable, Obs. 4.1.1), so
Lemma 4.1.5 applied to `Y` gives `g' : Δ → {i, 3}` whose refinement `h'` has classes of
size `≤ 2|Γ|/3 ≤ 4n₁/9` inside `Γ`.  Gluing `f := g` off `Δ` and `f := g'` on `Δ` gives a
3-coloring whose refinement `h*` refines both `h` and (on `Γ`) `h'`, so its classes have
size `≤ max(n₁ - |Γ|, 4n₁/9) < n₁/2`.

Two places need more than the printed text.  *"`Y` is not complete"* is
`exists_nbr_not_complete` (the paper's reason is not available here; see its docstring).
*"On `Γ`, the coloring `h*` is a refinement of `h'`"* is proved without transferring the
whole refinement process to `Y`: already after *one* round, the color of `u ∈ Γ` under `f`
determines the pair of numbers that one round of refinement of `(Γ, Δ; g')` gives `u`,
because the number of neighbors of `u` in `Δ` of `g'`-color `3` is the number of its
neighbors of `f`-color `3`, and the number of its neighbors in `Δ` is the same for all
`u ∈ Γ` by stability of `h` (Obs. 4.1.1). -/
theorem exists_three_coloring [Fintype A] [Fintype B] (X : BipGraph A B)
    (hnt : ¬ X.IsTrivial) (hsr : X.IsSemiregular) :
    ∃ f : B → Fin 3, X.ClassesLe f 1 2 := by
  classical
  obtain ⟨g, hg⟩ := X.exists_two_coloring hnt hsr
  have hne : X.E ≠ ∅ := fun h => hnt (Or.inl h)
  obtain ⟨⟨a₀, b₀⟩, hab₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  haveI : Nonempty A := ⟨a₀⟩
  have hgc : X.ClassesLe g 2 3 := X.classesLe_of_roundClassesLe g hg
  set H : A ⊕ B → _ := (X.toColoredDigraph g).stableRefine.c with hH
  have hHg : ∀ b b' : B, H (Sum.inr b) = H (Sum.inr b') → g b = g b' := by
    intro b b' hb
    have h1 := (X.toColoredDigraph g).stableRefine_isRefinement (Sum.inr b) (Sum.inr b') hb
    simpa [toColoredDigraph] using h1
  by_cases hdom : ∀ a : A, 2 * {a' : A | H (Sum.inl a') = H (Sum.inl a)}.ncard ≤ Fintype.card A
  · -- no dominant class: the 2-coloring `g` already works, read as a 3-coloring
    refine ⟨fun b => (g b).castSucc, fun a => ?_⟩
    have hrf : IsRefinement (X.toColoredDigraph (fun b => (g b).castSucc)).c
        (X.toColoredDigraph g).c := by
      rintro (u | b) (u' | b') hxy
      · rfl
      · exact absurd hxy (by simp [toColoredDigraph])
      · exact absurd hxy (by simp [toColoredDigraph])
      · have h1 : (g b).castSucc = (g b').castSucc := by simpa [toColoredDigraph] using hxy
        have h2 : g b = g b' := Fin.castSucc_injective 2 h1
        simp [toColoredDigraph, h2]
    have hmono : IsRefinement
        (X.toColoredDigraph (fun b => (g b).castSucc)).stableRefine.c H :=
      ColoredDigraph.stableRefine_mono (X.toColoredDigraph g) hrf
    have hsub : {a' : A | (X.toColoredDigraph (fun b => (g b).castSucc)).stableRefine.c
          (Sum.inl a') = (X.toColoredDigraph (fun b => (g b).castSucc)).stableRefine.c (Sum.inl a)}
        ⊆ {a' : A | H (Sum.inl a') = H (Sum.inl a)} := fun a' h' => hmono _ _ h'
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := hdom a
    show 2 * _ ≤ 1 * _
    omega
  · push_neg at hdom
    obtain ⟨a, ha⟩ := hdom
    set Γ : Set A := {a' : A | H (Sum.inl a') = H (Sum.inl a)} with hΓ
    have haΓ : a ∈ Γ := rfl
    have hΓ2 : Fintype.card A < 2 * Γ.ncard := ha
    have hΓ3 : 3 * Γ.ncard ≤ 2 * Fintype.card A := hgc a
    obtain ⟨y, hay, u₀, hu₀Γ, b₀', hb₀Δ, hb₀E⟩ :=
      X.exists_nbr_not_complete hnt hsr Γ a haΓ
        (fun b => {b' : B | H (Sum.inr b') = H (Sum.inr b)}) (fun b => rfl) hΓ2
    set Δ : Set B := {b' : B | H (Sum.inr b') = H (Sum.inr y)} with hΔ
    have hyΔ : y ∈ Δ := rfl
    haveI : Fintype Γ := Fintype.ofFinite _
    haveI : Fintype Δ := Fintype.ofFinite _
    set Y : BipGraph Γ Δ := ⟨{p : Γ × Δ | ((p.1 : A), (p.2 : B)) ∈ X.E}⟩ with hY
    have hstable := (X.toColoredDigraph g).stableRefine_isStable
    have hEeq : (X.toColoredDigraph g).stableRefine.E = X.toDigraph.E := rfl
    -- Obs. 4.1.1: the numbers of neighbors across the classes `Γ` and `Δ` are constant
    have hdegA : ∀ u ∈ Γ, ∀ u' ∈ Γ,
        {b : B | (u, b) ∈ X.E ∧ b ∈ Δ}.ncard = {b : B | (u', b) ∈ X.E ∧ b ∈ Δ}.ncard :=
      fun u hu u' hu' =>
        X.ncard_nbrB_eq_of_stable _ hEeq hstable (hu.trans hu'.symm) (H (Sum.inr y))
    have hdegB : ∀ b ∈ Δ, ∀ b' ∈ Δ,
        {u : A | (u, b) ∈ X.E ∧ u ∈ Γ}.ncard = {u : A | (u, b') ∈ X.E ∧ u ∈ Γ}.ncard :=
      fun b hb b' hb' =>
        X.ncard_nbrA_eq_of_stable _ hEeq hstable (hb.trans hb'.symm) (H (Sum.inl a))
    have hvalA : ∀ (u : A) (hu : u ∈ Γ),
        Y.degA ⟨u, hu⟩ = {b : B | (u, b) ∈ X.E ∧ b ∈ Δ}.ncard := by
      intro u hu
      have himg : Subtype.val '' {b : Δ | ((⟨u, hu⟩ : Γ), b) ∈ Y.E}
          = {b : B | (u, b) ∈ X.E ∧ b ∈ Δ} := by
        ext b
        constructor
        · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨b, h2⟩, h1, rfl⟩
      rw [degA, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hvalB : ∀ (b : B) (hb : b ∈ Δ),
        Y.degB ⟨b, hb⟩ = {u : A | (u, b) ∈ X.E ∧ u ∈ Γ}.ncard := by
      intro b hb
      have himg : Subtype.val '' {u : Γ | (u, (⟨b, hb⟩ : Δ)) ∈ Y.E}
          = {u : A | (u, b) ∈ X.E ∧ u ∈ Γ} := by
        ext u
        constructor
        · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨u, h2⟩, h1, rfl⟩
      rw [degB, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hYsr : Y.IsSemiregular := by
      constructor
      · refine ⟨{b : B | (a, b) ∈ X.E ∧ b ∈ Δ}.ncard, fun u => ?_⟩
        exact (hvalA (u : A) u.2).trans (hdegA (u : A) u.2 a haΓ)
      · refine ⟨{u : A | (u, y) ∈ X.E ∧ u ∈ Γ}.ncard, fun b => ?_⟩
        exact (hvalB (b : B) b.2).trans (hdegB (b : B) b.2 y hyΔ)
    have hYnt : ¬ Y.IsTrivial := by
      rintro (hemp | huniv)
      · have h1 : ((⟨a, haΓ⟩, ⟨y, hyΔ⟩) : Γ × Δ) ∈ Y.E := hay
        rw [hemp] at h1; exact h1
      · have h1 : ((⟨u₀, hu₀Γ⟩, ⟨b₀', hb₀Δ⟩) : Γ × Δ) ∉ Y.E := hb₀E
        exact h1 (by rw [huniv]; trivial)
    obtain ⟨g', hg'⟩ := Y.exists_two_coloring hYnt hYsr
    -- the 3-coloring `f`: `g` off `Δ`, and the new color `3` on the `g'`-color `1` of `Δ`
    set G2 : B → Fin 2 := fun b => if hb : b ∈ Δ then g' ⟨b, hb⟩ else 0 with hG2
    have hG2val : ∀ (b : B) (hb : b ∈ Δ), G2 b = g' ⟨b, hb⟩ := by
      intro b hb
      show (if hb' : b ∈ Δ then g' ⟨b, hb'⟩ else 0) = _
      rw [dif_pos hb]
    set f : B → Fin 3 := fun b => if b ∈ Δ ∧ G2 b = 1 then (2 : Fin 3) else (g b).castSucc
      with hf
    have hcastne : ∀ i : Fin 2, i.castSucc ≠ (2 : Fin 3) := by decide
    have hfval : ∀ b : B, f b = 2 ↔ (b ∈ Δ ∧ G2 b = 1) := by
      intro b
      by_cases hb : b ∈ Δ ∧ G2 b = 1
      · simp [hf, hb]
      · show (if b ∈ Δ ∧ G2 b = 1 then (2 : Fin 3) else (g b).castSucc) = 2 ↔ _
        rw [if_neg hb]
        exact ⟨fun hc => absurd hc (hcastne (g b)), fun hc => absurd hc hb⟩
    have hfelse : ∀ b : B, f b ≠ 2 → f b = (g b).castSucc := by
      intro b hb
      show (if b ∈ Δ ∧ G2 b = 1 then (2 : Fin 3) else (g b).castSucc) = _
      rw [if_neg (fun hc => hb ((hfval b).2 hc))]
    have hgΔ : ∀ b ∈ Δ, ∀ b' ∈ Δ, g b = g b' :=
      fun b hb b' hb' => hHg b b' (hb.trans hb'.symm)
    have hrf : IsRefinement (X.toColoredDigraph f).c (X.toColoredDigraph g).c := by
      rintro (u | b) (u' | b') hxy
      · rfl
      · exact absurd hxy (by simp [toColoredDigraph])
      · exact absurd hxy (by simp [toColoredDigraph])
      · have hfb : f b = f b' := by simpa [toColoredDigraph] using hxy
        have hgb : g b = g b' := by
          by_cases h1 : f b = 2
          · have h2 : f b' = 2 := hfb ▸ h1
            exact hgΔ b ((hfval b).1 h1).1 b' ((hfval b').1 h2).1
          · have h2 : f b' ≠ 2 := fun hc => h1 (hfb.trans hc)
            exact Fin.castSucc_injective 2 (by rw [← hfelse b h1, ← hfelse b' h2]; exact hfb)
        simp [toColoredDigraph, hgb]
    have hmono : IsRefinement (X.toColoredDigraph f).stableRefine.c H :=
      ColoredDigraph.stableRefine_mono (X.toColoredDigraph g) hrf
    have hround : ∀ u u' : A, (X.toColoredDigraph f).stableRefine.c (Sum.inl u)
        = (X.toColoredDigraph f).stableRefine.c (Sum.inl u') → X.refineA f u = X.refineA f u' := by
      intro u u' huu
      have hN : 1 ≤ Fintype.card ((A ⊕ B) × (A ⊕ B)) := Fintype.card_pos
      have h1 := (X.toColoredDigraph f).naiveIter_isRefinement_le hN (Sum.inl u) (Sum.inl u') huu
      have h2 : (X.toColoredDigraph f).naiveStep (Sum.inl u)
          = (X.toColoredDigraph f).naiveStep (Sum.inl u') := h1
      exact (X.naiveStep_inl_eq_iff f u u').1 h2
    -- one round of refinement by `f` determines one round of refinement of `Y` by `g'`
    have hvalR : ∀ (u : A) (hu : u ∈ Γ) (i : Fin 2),
        Y.refineA g' ⟨u, hu⟩ i = {b : B | (u, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = i}.ncard := by
      intro u hu i
      have himg : Subtype.val '' {b : Δ | ((⟨u, hu⟩ : Γ), b) ∈ Y.E ∧ g' b = i}
          = {b : B | (u, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = i} := by
        ext b
        constructor
        · rintro ⟨⟨z, hz⟩, ⟨hmem, hcol⟩, rfl⟩
          exact ⟨hmem, hz, (hG2val z hz).trans hcol⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨b, h2⟩, ⟨h1, ((hG2val b h2).symm.trans h3)⟩, rfl⟩
      rw [refineA, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hone : ∀ w : A, {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1}.ncard = X.refineA f w 2 := by
      intro w
      rw [refineA]
      congr 1
      ext b
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, (hfval b).2 ⟨h2, h3⟩⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ((hfval b).1 h2).1, ((hfval b).1 h2).2⟩
    have hsplit : ∀ w : A, {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 0}.ncard
        + {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1}.ncard
        = {b : B | (w, b) ∈ X.E ∧ b ∈ Δ}.ncard := by
      intro w
      have hdisj : Disjoint {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 0}
          {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1} := by
        rw [Set.disjoint_left]
        rintro b ⟨-, -, h1⟩ ⟨-, -, h2⟩
        rw [h1] at h2
        exact absurd h2 (by decide)
      have hun : {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 0}
          ∪ {b : B | (w, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1}
          = {b : B | (w, b) ∈ X.E ∧ b ∈ Δ} := by
        ext b
        constructor
        · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (G2 b) with h3 | h3
          · exact Or.inl ⟨h1, h2, h3⟩
          · exact Or.inr ⟨h1, h2, h3⟩
      rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hun]
    have htrans : ∀ (u : A) (hu : u ∈ Γ) (u' : A) (hu' : u' ∈ Γ),
        X.refineA f u = X.refineA f u' → Y.refineA g' ⟨u, hu⟩ = Y.refineA g' ⟨u', hu'⟩ := by
      intro u hu u' hu' hff
      have e1 : {b : B | (u, b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1}.ncard
          = {b : B | (u', b) ∈ X.E ∧ b ∈ Δ ∧ G2 b = 1}.ncard := by
        rw [hone u, hone u', hff]
      funext i
      rw [hvalR u hu i, hvalR u' hu' i]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) i with rfl | rfl
      · have e2 := hsplit u
        have e3 := hsplit u'
        have e4 := hdegA u hu u' hu'
        omega
      · exact e1
    -- the conclusion
    refine ⟨f, fun a' => ?_⟩
    by_cases ha'Γ : a' ∈ Γ
    · have hsubΓ : {a'' : A | (X.toColoredDigraph f).stableRefine.c (Sum.inl a'')
          = (X.toColoredDigraph f).stableRefine.c (Sum.inl a')} ⊆ Γ := by
        intro a'' ha''
        have h1 : H (Sum.inl a'') = H (Sum.inl a') := hmono _ _ ha''
        exact h1.trans ha'Γ
      have hK : {a'' : A | (X.toColoredDigraph f).stableRefine.c (Sum.inl a'')
            = (X.toColoredDigraph f).stableRefine.c (Sum.inl a')}
          ⊆ Subtype.val '' {u : Γ | Y.refineA g' u = Y.refineA g' ⟨a', ha'Γ⟩} := by
        intro a'' ha''
        exact ⟨⟨a'', hsubΓ ha''⟩, htrans a'' (hsubΓ ha'') a' ha'Γ (hround a'' a' ha''), rfl⟩
      have h1 := Set.ncard_le_ncard hK (Set.toFinite _)
      rw [Set.ncard_image_of_injective _ Subtype.val_injective] at h1
      have h2 := hg' ⟨a', ha'Γ⟩
      have h3 : Fintype.card Γ = Γ.ncard := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      show 2 * _ ≤ 1 * _
      omega
    · have hsubc : {a'' : A | (X.toColoredDigraph f).stableRefine.c (Sum.inl a'')
          = (X.toColoredDigraph f).stableRefine.c (Sum.inl a')} ⊆ Γᶜ := by
        intro a'' ha'' hc
        have h1 : H (Sum.inl a'') = H (Sum.inl a') := hmono _ _ ha''
        exact ha'Γ (h1.symm.trans hc)
      have h1 := Set.ncard_le_ncard hsubc (Set.toFinite _)
      have h2 := Set.ncard_add_ncard_compl Γ
      rw [Nat.card_eq_fintype_card] at h2
      show 2 * _ ≤ 1 * _
      omega

/-- §4.1.2, after Prop. 4.1.4: "the multiplicative cost incurred by selecting a 3-coloring of
`Ω₂` is `3^{n₂}`": there are exactly `3^{n₂}` colorings `f : Ω₂ → [3]` to try. -/
theorem card_three_colorings [Fintype B] [DecidableEq B] :
    Fintype.card (B → Fin 3) = 3 ^ Fintype.card B := by
  simp [Fintype.card_fun]

end BipGraph

end Babai
