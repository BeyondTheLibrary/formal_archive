/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: the block design case.
-/
import Workspace.SplitOrJohnson.Procedure
import Workspace.Prelim.Hypergraphs

/-!
# §9.7 Block design case

Version 2.5, lines 4233–4301 of `babai-gi-source/quasi25.txt`.

> *Assumptions: no twins in `V₁`, `X₂` is the clique configuration (rank-2).*
> *"Let `H = (V₂, E)` be the hypergraph of neighborhoods of vertices in `V₁`.  This
> hypergraph has no multiple edges because there are no twins in `V₁`."*

| Paper | Lean |
|---|---|
| the neighborhood hypergraph `H` | `Babai.nbhdHypergraph` |
| `H` has no multiple edges | `Babai.nbhdHypergraph_isSimple` |
| Case 1 (`V₂` is a set of twins in `H`) | `Babai.case_9_7_1`, `Babai.case_9_7_1_two_le_d₁` |
| Case 2, non-triviality of `X*` | `Babai.case_9_7_2` |
| Case 2, the `c'`-coloring of `V₁` | `Babai.localSizeColoring` |
| Case 3a (`d₁ ≤ (7/3)log₂ n₁`), the cost exponent | `Babai.case_9_7_3a_cost` |
| Case 3a1, filling the reference `Cor. ??` | `Babai.case_9_7_3a1` |
| Case 3a2, the rank-2 alternative | `Babai.case_9_7_3a2` |
| Case 3b, `t ≤ ⌈(3/4)d₁⌉` | `Babai.case_9_7_3b_t_le` |
| Case 3b, filling the `*****` gap | the section comment "Case 3b" below |

## Two holes of version 2.5 in this subsection

Version 2.5 has a dangling reference `Cor. ??` in Case 3a1 and a `*****` placeholder in
Case 3b.  In Case 3a1 the missing step is spelled out by the original (`babai-gi.tex`,
lines 3981–3992).  In Case 3b the two versions differ: the original *exits* on the
`3/4`-partition, while version 2.5 says that a Reduce-Part2-by-Color step and, if
necessary, an ImprimitiveCase step follow.  Version 2.5 governs (Decision 3 of `PLAN.md`),
and its own words after the `*****` name those two steps, which are the steps of Case 3a1.
See the two entries of kind "hole in 2.5" in the corrected paper.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The neighborhood hypergraph -/

open scoped Classical in
/-- §9.7.  *"Let `H = (V₂, E)` be the hypergraph of neighborhoods of vertices in `V₁`."*
The hyperedges are indexed by the vertices of `V₁`, the hyperedge of `v ∈ V₁` being its
neighborhood `X(v) ⊆ V₂`.  (Def. 2.5.1: a hypergraph is a *multiset* of edges, here the
indexed family `v ↦ X(v)`.) -/
noncomputable def nbhdHypergraph {s : Type} [Fintype s] (X : VColBip s Unit)
    (e : Fin (X.V₁.ncard) ≃ ↥X.V₁) : Hypergraph s where
  numEdges := X.V₁.ncard
  edge i := Finset.univ.filter fun y => ((e i : s), y) ∈ X.E

/-- §9.7.  *"This hypergraph has no multiple edges because there are no twins in `V₁`."*

Two vertices of `V₁` with the same neighborhood are twins (Obs. 2.4.28; the vertex colors
agree because in §9.7 the coloring of `V₁` is constant — `X₁` is homogeneous — which is why
the coloring type is `Unit` here), so the map `v ↦ X(v)` is injective.

Proof: equal hyperedges mean equal neighborhoods, and two vertices of `V₁` with equal
neighborhoods and equal vertex colors are twins (`VColBip.isTwinIn_of_nbhd_eq`). -/
theorem nbhdHypergraph_isSimple {s : Type} [Fintype s] [DecidableEq s] (X : VColBip s Unit)
    (e : Fin (X.V₁.ncard) ≃ ↥X.V₁)
    (hno : ∀ x ∈ X.V₁, ∀ y ∈ X.V₁, ¬ X.IsTwinIn x y) :
    (nbhdHypergraph X e).IsSimple := by
  classical
  intro i j hij
  -- equal hyperedges mean equal neighborhoods
  have hnb : ∀ y : s, ((e i : s), y) ∈ X.E ↔ ((e j : s), y) ∈ X.E := by
    intro y
    have h := congrArg (fun F : Finset s => y ∈ F) hij
    simpa [nbhdHypergraph] using h
  by_contra hne
  have hune : (e i : s) ≠ (e j : s) := fun h => hne (e.injective (Subtype.ext h))
  exact hno _ (e i).2 _ (e j).2
    (VColBip.isTwinIn_of_nbhd_eq (e i).2 (e j).2 hune hnb rfl)

/-! ### Case 1 -/

open scoped Classical in
/-- Case 1 of §9.7.  *"`V₂` is a set of twins in `H`.  This means `Aut(H)` acts on `V₂` as
`S(V₂)`.  Since `H` has no multiple edges and is uniform of rank `d₁`, it follows that `H`
is the complete `d₁`-uniform hypergraph.  Let us label `v ∈ V₁` by the set `X(v)`.  This
establishes a bijection between `V₁` and the set `(V₂ choose d₁)`.  Since isomorphisms
preserve the number of common neighbors, this correspondence gives a canonical embedding of
the Johnson scheme `J(n₂, d₁)` on `V₁`, achieving goal (b) of Theorem 9.2.2."*
(Version 2.5, lines 4240–4251.)

Goal (b) asks for a **nontrivial** Johnson scheme, i.e. an object of `JohnsonSchemes`
(Defs. 3.2.9/3.2.13, with `2 ≤ t` and `2t + 1 ≤ k`), so the conclusion is stated in the
shape of `IsJohnsonColoring`: a bijection `φ : V₁ ≃ (V₂ choose d₁)` under which the edge
coloring `d₁ - |X(u) ∩ X(v)|` of `V₁` (the paper's *"isomorphisms preserve the number of
common neighbors"*) is the Johnson coloring `|φ(u) \ φ(v)|` of `J(n₂, d₁)`, together with
`2 ≤ d₁` and `2d₁ + 1 ≤ n₂`.

§9.7 checks neither of the last two, and both are needed for goal (b); see the entry
"§9.7 Case 1" in the corrected paper.  `2 ≤ d₁` follows from the standing hypothesis
`|V₂| < α|V₁|` of Theorem 9.2.2 (`case_9_7_1_two_le_d₁`).  `2d₁ + 1 ≤ n₂` comes from
outside Case 1 — from the primitivity of `X₁`, established in step 6 of Procedure Bipartite
Split-or-Johnson: for `n₂ = 2d₁` the Johnson coloring of `J(2d₁, d₁)` has the disconnected
constituent `|S \ T| = d₁` (a perfect matching), and `X₁`, which refines that coloring,
would then have a disconnected non-diagonal constituent — so it is carried as a hypothesis
here, and both are repeated in the conclusion, where goal (b) needs them. -/
theorem case_9_7_1 {s : Type} [Fintype s] [DecidableEq s] (X : VColBip s Unit)
    (e : Fin (X.V₁.ncard) ≃ ↥X.V₁) (d₁ : ℕ)
    (hsimple : (nbhdHypergraph X e).IsSimple)
    (huniform : (nbhdHypergraph X e).IsUniform d₁)
    (hcomplete : (nbhdHypergraph X e).edgeSet =
      {A : Finset s | A.card = d₁ ∧ ∀ y ∈ A, y ∈ X.V₂})
    (hd₁ : 2 ≤ d₁) (hn₂ : 2 * d₁ + 1 ≤ X.V₂.ncard) :
    ∃ φ : ↥X.V₁ ≃ binom ↥X.V₂ d₁,
      (2 ≤ d₁ ∧ 2 * d₁ + 1 ≤ X.V₂.ncard) ∧
      ∀ u v : ↥X.V₁,
        ((φ u : Finset ↥X.V₂) \ (φ v : Finset ↥X.V₂)).card
          = d₁ - {y : ↥X.V₂ | ((u : s), (y : s)) ∈ X.E ∧ ((v : s), (y : s)) ∈ X.E}.ncard := by
  classical
  -- `N v` is the neighbourhood `X(v) ⊆ V₂` of `v ∈ V₁`, as a subset of `V₂`
  set N : ↥X.V₁ → Finset ↥X.V₂ :=
    fun v => Finset.univ.filter (fun y : ↥X.V₂ => ((v : s), (y : s)) ∈ X.E) with hN
  -- `N v` is the hyperedge of `H` indexed by `v`, read inside `V₂`
  have himg : ∀ v : ↥X.V₁, (N v).image (Subtype.val : ↥X.V₂ → s)
      = (nbhdHypergraph X e).edge (e.symm v) := by
    intro v
    ext y
    simp only [hN, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      nbhdHypergraph, Equiv.apply_symm_apply]
    constructor
    · rintro ⟨y', hy', rfl⟩; exact hy'
    · intro hy
      exact ⟨⟨y, (X.E_sub _ hy).2⟩, hy, rfl⟩
  have hvalinj : Function.Injective (Subtype.val : ↥X.V₂ → s) := Subtype.val_injective
  have hcardN : ∀ v : ↥X.V₁, (N v).card = d₁ := by
    intro v
    rw [← Finset.card_image_of_injective _ hvalinj, himg v]
    exact huniform (e.symm v)
  -- the map `v ↦ X(v)` is a bijection onto the `d₁`-subsets of `V₂`
  have hinj : Function.Injective (fun v : ↥X.V₁ => (⟨N v, hcardN v⟩ : binom ↥X.V₂ d₁)) := by
    intro u v huv
    have h1 : N u = N v := congrArg Subtype.val huv
    have h2 : (nbhdHypergraph X e).edge (e.symm u) = (nbhdHypergraph X e).edge (e.symm v) := by
      rw [← himg u, ← himg v, h1]
    have h3 : e.symm u = e.symm v := hsimple h2
    exact e.symm.injective h3
  have hsurj : Function.Surjective
      (fun v : ↥X.V₁ => (⟨N v, hcardN v⟩ : binom ↥X.V₂ d₁)) := by
    rintro ⟨A, hA⟩
    -- the image of `A` in `s` is a `d₁`-subset of `V₂`, hence a hyperedge of `H`
    have hmem : A.image (Subtype.val : ↥X.V₂ → s) ∈ (nbhdHypergraph X e).edgeSet := by
      rw [hcomplete]
      refine ⟨by rw [Finset.card_image_of_injective _ hvalinj, hA], ?_⟩
      rintro y hy
      obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hy
      exact y'.2
    obtain ⟨i, hi⟩ := hmem
    refine ⟨e i, Subtype.ext ?_⟩
    have h1 : (N (e i)).image (Subtype.val : ↥X.V₂ → s)
        = A.image (Subtype.val : ↥X.V₂ → s) := by
      rw [himg (e i), Equiv.symm_apply_apply, hi]
    exact Finset.image_injective hvalinj h1
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, ⟨hd₁, hn₂⟩, ?_⟩
  intro u v
  have hφ : ∀ w : ↥X.V₁,
      ((Equiv.ofBijective _ ⟨hinj, hsurj⟩ : ↥X.V₁ ≃ binom ↥X.V₂ d₁) w
        : Finset ↥X.V₂) = N w := fun _ => rfl
  rw [hφ, hφ]
  -- `|X(u) \ X(v)| = |X(u)| - |X(u) ∩ X(v)|`, and `|X(u)| = d₁`
  have hset : {y : ↥X.V₂ | ((u : s), (y : s)) ∈ X.E ∧ ((v : s), (y : s)) ∈ X.E}
      = (↑(N u ∩ N v) : Set ↥X.V₂) := by
    ext y
    simp [hN]
  rw [hset, Set.ncard_coe_finset, ← hcardN u]
  have := Finset.card_sdiff_add_card_inter (N u) (N v)
  omega

/-- Case 1 of §9.7, a step the paper does not check: `d₁ ≥ 2`, which goal (b) needs
(Def. 3.2.9 excludes `t = 1`, and by Remark 3.2.15 the Johnson schemes `J(k,1)` are the
clique configurations, i.e. trivial).

In Case 1 the map `v ↦ X(v)` is a bijection of `V₁` onto the `d₁`-subsets of `V₂`, so
`n₁ = C(n₂, d₁)`.  The standing hypothesis of Theorem 9.2.2 is `n₂ < αn₁` with `α < 1`,
hence `n₂ < n₁`.  But `d₁ = 0` gives `n₁ = 1 ≤ n₂`, and `d₁ = 1` gives `n₁ = n₂` (the
paper's *"perfect matching"*); both contradict `n₂ < n₁`. -/
theorem case_9_7_1_two_le_d₁ {n₁ n₂ d₁ : ℕ} (hcard : n₁ = n₂.choose d₁)
    (hn₂ : 1 ≤ n₂) (hlt : n₂ < n₁) : 2 ≤ d₁ := by
  by_contra hd
  push_neg at hd
  interval_cases d₁
  · rw [Nat.choose_zero_right] at hcard; omega
  · rw [Nat.choose_one_right] at hcard; omega

/-! ### Case 2 -/

open scoped Classical in
/-- Case 2 of §9.7.  *"Color each vertex of `V₁` by the size of the corresponding hyperedge
in `H'`: for `v ∈ V₁` let `c'(v) = |X(v) ∩ C|."* -/
noncomputable def localSizeColoring {s : Type} [Fintype s] (X : VColBip s Unit) (C : Set s)
    (v : s) : ℕ :=
  (Finset.univ.filter fun y => (v, y) ∈ X.E ∧ y ∈ C).card

/-- Case 2 of §9.7.  *"There is an `H`-twin equivalence class `C ⊆ V₂` of size
`|C| ≥ n₂/2`.  So `S(C) ≤ Aut(H)`. … Apply procedure Reduce-Part2-by-Color to the coloring
`(C, V₂ \ C)`.  If `V₂ \ C` is selected, we have made significant progress (reduced `|V₂|`
by half).  If `C` is selected, let `X' = X[V₁, C]` … Color each vertex of `V₁` by the size
of the corresponding hyperedge in `H'` … If all `c'`-color classes have size less than
`αn₁`, return this coloring, exit.  Otherwise, let `A ⊆ V₁` be the dominant `c'`-color
class, so `|A| ≥ αn₁ > n₁/2` … `X*` is semiregular.  It cannot be trivial because the
relative sizes of `A` (in `V₁`) and `C` (in `V₂`) add up to more than 1, contradicting
Cor. 2.4.32. … Since `Aut(H*)` acts on `C` as the symmetric group, all edges of `H*` have
the same multiplicity.  In other words, `A` is equipartitioned by the twin equivalence
classes in `X*`.  If this is a nontrivial partition, return this partition, exit. … the
only remaining option is that there are no twins in `A`, i.e. `E*` has no multiple edges.
Since `C` is a set of twins in `H*`, we are back to Case 1."*
(Version 2.5, lines 4252–4274.)

The step of Case 2 that is not bookkeeping is the non-triviality of `X*`, and the paper's
reason for it is the hypothesis stated here: *"the relative sizes of `A` (in `V₁`) and `C`
(in `V₂`) add up to more than 1"*.  At the call site `|A| ≥ αn₁ > n₁/2` and `|C| ≥ n₂/2`;
the second of these is not strict, so the hypothesis has to be the sum of the two relative
sizes, not the two halves separately. -/
theorem case_9_7_2 {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (Y : BipGraph A B)
    (hsr : Y.IsSemiregular) (hnt : ¬ Y.IsTrivial) (A₁ : Set A) (C : Set B)
    (hsizes : 1 < (A₁.ncard : ℚ) / (Fintype.card A : ℚ)
      + (C.ncard : ℚ) / (Fintype.card B : ℚ)) :
    ¬ (Y.induced A₁ C).IsTrivial := fun htriv =>
  absurd (BipGraph.trivial_subgraph_sum_le_one hnt hsr htriv) (not_le.2 hsizes)

/-! ### Case 3 -/

/-- Case 3a of §9.7.  *"`d₁ ≤ (7/3) log₂ n₁`.  Apply the Design lemma to `H`, viewed as a
`d₁`-ary relational structure.  (Multiplicative cost `n₂^{d₁} < n₂^{(7/3)log₂ n₁}`.)"*
(Version 2.5, lines 4276–4280.)

The content of the parenthesis is the monotonicity of the exponent, which is what makes the
cost of the Design Lemma call quasipolynomial in `n₁`.  The cost itself is a running-time
claim; see the entry of kind "pending" in the corrected paper. -/
theorem case_9_7_3a_cost (n₂ d₁ : ℕ) (r : ℝ) (hd : (d₁ : ℝ) ≤ r) (hn₂ : 1 ≤ (n₂ : ℝ)) :
    ((n₂ : ℝ)) ^ (d₁ : ℝ) ≤ ((n₂ : ℝ)) ^ r :=
  Real.rpow_le_rpow_of_exponent_le hn₂ hd

/-! ### Cases 3a1, 3a2 and 3b -/

/-- Case 3a1 of §9.7, with the missing reference `Cor. ??` filled from the original
version (`babai-gi.tex`, lines 3981–3992).

Version 2.5 (lines 4281–4284): *"The Design lemma returns a canonical colored
`3/4`-partition of `V₂`.  Apply Cor. ??.  Significant progress is made in time, polynomial
in `n₁`, namely, `n₂` is reduced to `≤ 3n₂/4`.  If a multiplicative cost of `m` is
incurred, the progress is more significant: `n₂` is reduced to `≤ n₂/m` (`2 ≤ m ≤ n₂/2`)."*

Original: *"Recompute `X` and thereby `X₂`.  Colored `(3/4)`-partition on `V₂` persists
(colors can only get refined).  Apply Reduce-Part2-by-Color to the coloring.  If color
class selected is greater than `3n₂/4`, this color class is equipartitioned; apply
Procedure ImprimitiveCase (Sec. 9.6).  In either case, significant progress: `n₂` reduced
to `≤ 3n₂/4`."*

Here `C₁`, `C₂` are the two unions of color classes to which Reduce-Part2-by-Color is
applied, and `hsmall` is the property of a colored `3/4`-partition `Π` of `V₂` that the
paper uses: each of the two parts either has size `≤ (3/4)n₂` already, or is one color
class of `Π`, and then the blocks of `Π` inside it are a partition into at least two
blocks, each of size `≥ 2` (admissibility, Def. 7.1.1) and `≤ (3/4)n₂` (`ρ(Π) ≤ (3/4)n₂`),
which is exactly the input of Procedure ImprimitiveCase (§9.6).  The conclusion is that the
*selected* part `U` keeps the symmetry defect of `V₁` at `≥ (n₁ - 1)/2` (Lemma 9.3.2) and
has that same property, which is the *"significant progress: `n₂` reduced to `≤ 3n₂/4`"*.

The three conditions on the blocks are what makes the second alternative say something:
without `2 ≤ |Q|` and `1 < |P|` it is satisfied by the partition of `D` into singletons,
for any `D`, and the alternative would be vacuous.  Both come from the colored
`3/4`-partition: `2 ≤ |Q|` is `ColoredPartition.IsAdmissible` for a color class of size
`≥ 2`, and `1 < |P|` holds because a single block would have size `|D| > (3/4)n₂ ≥ ρ(Π)`. -/
theorem case_9_7_3a1 {s : Type} [Fintype s] [DecidableEq s] {κ : Type} (X : VColBip s κ)
    (hno : ∀ x ∈ X.V₁, ∀ y ∈ X.V₁, ¬ X.IsTwinIn x y) {C₁ C₂ : Set s}
    (hcov : X.V₂ ⊆ C₁ ∪ C₂)
    (hsmall : ∀ D : Set s, D = C₁ ∨ D = C₂ →
      4 * D.ncard ≤ 3 * X.V₂.ncard ∨
        ∃ P : Set (Set s), (⋃₀ P = D) ∧ P.PairwiseDisjoint id ∧ 1 < P.ncard ∧
          ∀ Q ∈ P, 2 ≤ Q.ncard ∧ 4 * Q.ncard ≤ 3 * X.V₂.ncard) :
    ((X.V₁.ncard : ℚ) - 1) / 2 ≤
        (X.restrict₂ (reducePart2ByColor X C₁ C₂)).symDefect₁ ∧
      (4 * (reducePart2ByColor X C₁ C₂).ncard ≤ 3 * X.V₂.ncard ∨
        ∃ P : Set (Set s), (⋃₀ P = reducePart2ByColor X C₁ C₂) ∧
          P.PairwiseDisjoint id ∧ 1 < P.ncard ∧
          ∀ Q ∈ P, 2 ≤ Q.ncard ∧ 4 * Q.ncard ≤ 3 * X.V₂.ncard) :=
  ⟨reducePart2ByColor_spec X hno hcov, hsmall _ (reducePart2ByColor_mem X C₁ C₂)⟩

/-- Case 3a2 of §9.7.  *"The Design lemma returns a UPCC `Y` canonically embedded on a
subset `W ⊆ V₂` with `|W| ≥ (3/4)n₂`.  Apply Reduce-Part2-by-Color to the partition
`(W, V₂ \ W)`.  If the procedure selects `V₂ \ W`, significant progress (`n₂` reduced to
`≤ n₂/4`).  If it selects `W`, go to Sec. 9.8.  Let `U ⊆ V₂` be the part selected, and
`(X₂)_new` the homogeneous coherent configuration obtained on `U`.  If `(X₂)_new` is a
UPCC, exit, significant progress.  If `(X₂)_new` is not a UPCC, i.e. it has rank 2, then
`U` was a clique in `Y` and therefore `|U| ≤ |W|/2 ≤ n₂/2` by Prop. 2.4.11, a significant
reduction of `|V₂|`."*  (Version 2.5, lines 4285–4294.)

The step with mathematical content is the last one, and it is Prop. 2.4.11: a rank-2
`(X₂)_new` means that `U` carries no edge of the non-diagonal constituent of `Y` that it
would otherwise carry, i.e. `U` is an independent set of that constituent, which is a
non-empty biregular digraph on `W`; hence `2|U| ≤ |W|`. -/
theorem case_9_7_3a2 {W : Type} [Fintype W] [DecidableEq W] {Y : Digraph W}
    (hne : ¬ Y.IsEmpty) (hreg : Y.IsBiregular) {U : Set W} (hU : Y.IsIndependent U) :
    2 * U.ncard ≤ Fintype.card W :=
  Digraph.ncard_independent_le hne hreg hU

/-- Case 3b of §9.7.  *"`d₁ > 7/3 log₂ n₁`.  Let `t = ⌈(7/4) log₂ n₁⌉`.  So
`t ≤ (3/4)d₁`."*  (Version 2.5, lines 4295–4301.)

**The paper's `t` does not satisfy `t ≤ (3/4)d₁`.**  Writing `L = log₂ n₁`, Case 3b only
gives `d₁ > (7/3)L`, so `(3/4)d₁ > (7/4)L`, and rounding `(7/4)L` *up* can overshoot that
margin.  Counterexample: `n₁ = 11`, `L = 3.4594…`, `(7/3)L = 8.072…`, so `d₁ = 9` is a
legal Case 3b value (and `d₁ ≤ n₂ < n₁` allows it, e.g. `n₂ = 10`); then
`t = ⌈(7/4)L⌉ = ⌈6.054…⌉ = 7`, while `(3/4)d₁ = 6.75 < 7`.  The same happens for a positive
fraction of all `n₁`.  See the entry "§9.7 Case 3b, `t ≤ (3/4)d₁`" in the corrected paper.

Rounding `(7/4)L` up is exactly what breaks the printed inequality, so `t` is kept as the
paper defines it and the **upper bound is relaxed to the ceiling**: from `(7/3)L < d₁` one
gets `(7/4)L < (3/4)d₁`, hence `t = ⌈(7/4)L⌉ ≤ ⌈(3/4)d₁⌉` by monotonicity of the ceiling.
That is enough for Lemma 2.5.12, which is proved here in the form
`Babai.Hypergraph.skeleton_defect` with the hypothesis `t ≤ ⌈(3/4)d⌉`: its proof uses the
upper bound only to pick a `t`-subset of `S ∩ E` with `|S ∩ E| ≥ (3/4)d`, and `|S ∩ E|` is
an integer, so `|S ∩ E| ≥ ⌈(3/4)d⌉ ≥ t`.

The second conclusion, `t < (7/4)L + 1`, is the upper bound on `t` that keeps the
multiplicative cost `n₂^t` of the Design Lemma call quasipolynomial in `n₁`. -/
theorem case_9_7_3b_t_le (L : ℝ) (hL : 0 ≤ L) (d₁ : ℕ) (hd₁ : 7 / 3 * L < (d₁ : ℝ)) :
    ⌈7 / 4 * L⌉₊ ≤ ⌈3 / 4 * (d₁ : ℝ)⌉₊ ∧
      ((⌈7 / 4 * L⌉₊ : ℕ) : ℝ) < 7 / 4 * L + 1 := by
  refine ⟨Nat.ceil_le_ceil (by linarith), Nat.ceil_lt_add_one (by positivity)⟩

/-! ### Case 3b, the `*****` gap

Version 2.5: *"`d₁ > 7/3 log₂ n₁`.  Let `t = ⌈(7/4) log₂ n₁⌉`.  So `t ≤ (3/4)d₁`.  By
Lemma 2.5.12, the symmetry defect of the `t`-skeleton `H^(t)` of `H` is greater than `1/4`.
Let us apply the Design lemma to `H^(t)`.  If the result is a `3/4`-partition of `V₂`,
********* an application of Reduce-Part2-by-Color and if necessary, an application of the
imprimitive case.  Else (the result is a UPCC on a subset of `V₂` of size `≥ (3/4)n₂`
(significant progress, exit)."*

The `*****` hides the verb of the sentence: what follows the stars names the two steps that
are applied, and they are exactly the steps of Case 3a1 — Reduce-Part2-by-Color, and
Procedure ImprimitiveCase if the selected color class is too large.  So the filled step is
`case_9_7_3a1`, applied to the colored `3/4`-partition of `V₂` that the Design Lemma
returns for the `t`-skeleton `H^(t)`; no separate statement is introduced.

The original reads differently here (*"The result is either a `3/4`-partition of `V₂` (done,
exit), or a UPCC on a subset of `V₂` of size `≥ (3/4)n₂` (significant progress, exit)"*,
`babai-gi.tex`, lines 4026–4032): it **exits** on the partition and applies neither
procedure.  Version 2.5 governs (Decision 3 of `PLAN.md`), and the fill follows 2.5's own
words.  See the entry of kind "hole in 2.5" for Case 3b in the corrected paper. -/

end Babai
