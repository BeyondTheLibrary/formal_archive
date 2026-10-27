/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 3: the coherent configuration `X` of the WL refinement, read as a
`Babai.PartitionStructure` on the vertex set "points of `V₁` plus blocks".
-/
import Workspace.SplitOrJohnson.WLColor
import Workspace.Refinement.NamedConfig
import Workspace.SplitOrJohnson.NatColor
import Workspace.DesignLemma.Reduction

/-!
# §9.4, step 3.  From the WL coloring to a coherent configuration

Step 3 of §9.4 produces a coloring of the pairs of vertices of the bipartite graph, read on
the vertex set *"points of `V₁` plus blocks"* (`Babai.VColBipBlk.wlColor`,
`Workspace/SplitOrJohnson/WLColor.lean`).  What §9.6, §9.7 and §9.8 ask for, in the field
`Babai.IsBipartiteCase.coherent`, is a `Babai.PartitionStructure` on that vertex set whose
`natColor` **is** that coloring, which is coherent, and whose vertex-color classes are the
two parts.  This file builds it.

## The two halves

**A general half**, about colorings only, which is where the mathematics is:

* `Babai.WL.diag_fst_eq_of_eq`, `Babai.WL.diag_snd_eq_of_eq` — Observation 3.3.4
  (vertex-color awareness) stated for a coherent *coloring*: the color of an edge
  determines the colors of its tail and of its head.
* `Babai.WL.isCoherentColoring_restrict` — **Observation 3.3.2** (*"if `Δ ⊆ Ω` is a stable
  subset then the induced substructure `X[Δ]` is a coherent configuration"*) for colorings:
  the restriction of a coherent coloring to a union of vertex-color classes is coherent.
  This is what the restrictions `X ← X[W₁ ∪ V₂]` of step 5 and `X ← X[V₁ ∪ D_j]` of step 7
  need, and it is also how the coloring on the vertex set is cut out of the coloring on all
  subsets of the point set.
* `Babai.PartitionStructure.isCoherent_ofNatColoring` — a coherent coloring names a
  coherent configuration, with the **canonical** `Babai.natRank` naming of the colors
  (`Babai.PartitionStructure.ofNatColoring`), the naming that makes the labels an
  isomorphism invariant.

**A half about step 3 itself**: the vertex set `Babai.VColBipBlk.vtx` is stable
(`Babai.VColBipBlk.isStableSet_vtx`), so the configuration is
`Babai.VColBipBlk.wlConfig`, its `natColor` is `Babai.VColBipBlk.wlCaseColor`
(`Babai.VColBipBlk.natColor_wlConfig`), and, once `X₁` and `X₂` are homogeneous, the two
parts are vertex-color classes (`Babai.VColBipBlk.exists_wlConfig`), which is exactly the
field `Babai.IsBipartiteCase.coherent`.

## Why `wlCaseColor` and not `wlColor`

`Babai.VColBipBlk.wlColor` uses the named WL color plus one, the shift keeping the
padding color `0` (used off the vertex set) apart from the colors of genuine pairs of
vertices.  A `Babai.PartitionStructure.natColor` **cannot** have that shift: its values are
the elements of `Fin rank` and every color is used (Def. 3.1.1), so the color `0` is
attained.  The coloring the case categories carry is therefore the unshifted
`Babai.VColBipBlk.wlCaseColor`, which agrees with `wlColor` up to the shift on the vertices
(`Babai.VColBipBlk.wlColor_eq_wlCaseColor_succ`) and so has the same color classes there;
`0` is then both the padding color and a genuine color, which no construction reads,
because every construction of §9.6-§9.8 reads the coloring on the vertex set only (see
`Babai.BlkImprimitiveObj.isIso_of_vertexColor`).

## Numbering map

| Paper | Lean |
|---|---|
| Observation 3.3.4, for a coloring | `Babai.WL.diag_fst_eq_of_eq`, `Babai.WL.diag_snd_eq_of_eq` |
| Definition 3.1.5 (stable subset), for a coloring | `Babai.WL.IsStableSet` |
| Observation 3.3.2, for a coloring | `Babai.WL.isCoherentColoring_restrict` |
| Definition 3.1.11 from a coherent coloring | `Babai.PartitionStructure.isCoherent_ofNatColoring` |
| §9.4, step 3, the configuration on the vertex set | `Babai.VColBipBlk.wlConfig`, `.wlCaseColor` |
| §9.4, step 3, the `coherent` field of the three cases | `Babai.VColBipBlk.exists_wlConfig` |
-/

namespace Babai

/-! ### Observation 3.3.4 for a coloring -/

namespace WL

variable {V K : Type*} [Finite V] {d : V → V → K}

/-- Observation 3.3.4 (Vertex-color awareness), for a coherent **coloring**: *"the color of
an edge determines the color of its tail."*

The proof is the paper's: `x` is the only `z` with `c(x,z) = c(x,x)` and `c(z,y) = c(x,y)`,
so that intersection number is `1`; applying it to `(x',y')` produces a `z'` with
`c(x',z') = c(x,x)`, and `c(x,x)` is a diagonal color, so `z' = x'`. -/
theorem diag_fst_eq_of_eq (h : IsCoherentColoring d) {x y x' y' : V}
    (hxy : d x y = d x' y') : d x x = d x' x' := by
  classical
  obtain ⟨⟨hdiag, -⟩, p, hp⟩ := h
  have hS : {z : V | d x z = d x x ∧ d z y = d x y} = {x} := by
    ext z
    constructor
    · rintro ⟨h1, -⟩
      exact (hdiag x z x h1).symm
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have h1 : {z : V | d x z = d x x ∧ d z y = d x y}.ncard = p (d x x) (d x y) (d x y) :=
    hp _ _ _ x y rfl
  have h2 : {z : V | d x' z = d x x ∧ d z y' = d x y}.ncard = p (d x x) (d x y) (d x y) :=
    hp _ _ _ x' y' hxy.symm
  rw [hS, Set.ncard_singleton] at h1
  have hne : {z : V | d x' z = d x x ∧ d z y' = d x y}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [h2, ← h1]; exact one_ne_zero)
  obtain ⟨z', hz'⟩ := hne
  have : x' = z' := hdiag x' z' x hz'.1
  rw [← this] at hz'
  exact hz'.1.symm

/-- Observation 3.3.4, for a coherent coloring: the color of an edge determines the color
of its head.  Apply `Babai.WL.diag_fst_eq_of_eq` to the converse edge. -/
theorem diag_snd_eq_of_eq (h : IsCoherentColoring d) {x y x' y' : V}
    (hxy : d x y = d x' y') : d y y = d y' y' :=
  diag_fst_eq_of_eq h (h.1.2 x y x' y' hxy)

/-! ### Observation 3.3.2 for a coloring -/

/-- Definition 3.1.5 (Stable subset) for a coloring: `T` is a union of vertex-color
classes. -/
def IsStableSet (d : V → V → K) (T : Set V) : Prop :=
  ∀ x ∈ T, ∀ y : V, d y y = d x x → y ∈ T

/-- Membership of `T` in a stable set is decided by the color of an edge into it: if
`d u z = d u' z'` with `z ∈ T`, then `z' ∈ T`. -/
theorem IsStableSet.mem_of_color_eq (h : IsCoherentColoring d) {T : Set V}
    (hT : IsStableSet d T) {u z u' z' : V} (hz : z ∈ T) (huz : d u z = d u' z') : z' ∈ T :=
  hT z hz z' (diag_snd_eq_of_eq h huz).symm

/-- Observation 3.3.2 (Stable is coherent), for a coloring: *"if `Δ ⊆ Ω` is a stable subset
then the induced substructure `X[Δ]` is a coherent configuration."*

The point is the paper's: for `u ∈ T` the color `c(u,z)` determines the vertex color of
`z` (Obs. 3.3.4), hence whether `z ∈ T`; so the set counted by an intersection number of
the restriction either lies inside `T`, and the count is the ambient one, or misses `T`
altogether, and the count is `0`.  Which of the two happens depends on the color `i`
alone. -/
theorem isCoherentColoring_restrict (h : IsCoherentColoring d) {T : Set V}
    (hT : IsStableSet d T) : IsCoherentColoring (fun u v : ↥T => d u v) := by
  classical
  obtain ⟨⟨hdiag, hconv⟩, p, hp⟩ := h
  have hcoh : IsCoherentColoring d := ⟨⟨hdiag, hconv⟩, p, hp⟩
  refine ⟨⟨fun u v w huv => Subtype.ext (hdiag u v w huv),
      fun u v x y huv => hconv u v x y huv⟩, ?_⟩
  set q : K → K → K → ℕ :=
    fun i j k => if ∃ u' z' : V, z' ∈ T ∧ d u' z' = i then p i j k else 0 with hq
  refine ⟨q, ?_⟩
  intro i j k u v huv
  have hqval : q i j k = if ∃ u' z' : V, z' ∈ T ∧ d u' z' = i then p i j k else 0 := rfl
  rw [hqval]
  -- the ambient set of midpoints
  set A : Set V := {z : V | d u z = i ∧ d z v = j} with hA
  have hAcard : A.ncard = p i j k := hp i j k u v huv
  -- the set of midpoints inside `T`, as a subset of `V`
  have himg : (Subtype.val '' {z : ↥T | d u z = i ∧ d z v = j} : Set V) = A ∩ T := by
    ext z
    constructor
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      exact ⟨⟨hw1, hw2⟩, w.2⟩
    · rintro ⟨⟨h1, h2⟩, hzT⟩
      exact ⟨⟨z, hzT⟩, ⟨h1, h2⟩, rfl⟩
  have hcard : {z : ↥T | (fun a b : ↥T => d a b) u z = i ∧ (fun a b : ↥T => d a b) z v = j}.ncard
      = (A ∩ T).ncard := by
    rw [← himg]
    exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm
  rw [hcard]
  by_cases hex : ∃ u' z' : V, z' ∈ T ∧ d u' z' = i
  · rw [if_pos hex]
    obtain ⟨u', z', hz'T, hz'i⟩ := hex
    -- every midpoint lies in `T`, because its vertex color is determined by `i`
    have hsub : A ⊆ T := by
      rintro z ⟨hz1, -⟩
      exact hT.mem_of_color_eq hcoh hz'T (hz'i.trans hz1.symm)
    rw [Set.inter_eq_self_of_subset_left hsub, hAcard]
  · rw [if_neg hex]
    have hempty : A ∩ T = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨⟨hz1, -⟩, hzT⟩
      exact hex ⟨u, z, hzT, hz1⟩
    rw [hempty, Set.ncard_empty]

end WL

/-! ### A coherent coloring names a coherent configuration -/

namespace PartitionStructure

variable {V K : Type*} [Finite V]

/-- Definition 3.1.11 for the canonical `ℕ`-naming of a coherent coloring: the partition
structure `Babai.PartitionStructure.ofNatColoring d` of a coherent coloring `d` is a
coherent configuration.

`ofNatColoring` names the colors by `Babai.natRank`, so the naming is a function of the
coloring alone; this is the naming under which the labels of the coloring are an
isomorphism invariant. -/
theorem isCoherent_ofNatColoring {d : V → V → K} (h : WL.IsCoherentColoring d) :
    (ofNatColoring d).IsCoherent := by
  classical
  obtain ⟨⟨hdiag, hconv⟩, p, hp⟩ := h
  set X := ofNatColoring d with hX
  -- reading a color of `X` off a pair realizing it
  have hread : ∀ (i : Fin X.rank) (a b : V), X.color a b = i ↔
      d a b = d (X.colorWitness i).1 (X.colorWitness i).2 := by
    intro i a b
    constructor
    · intro hab
      exact (ofNatColoring_color_eq_iff d a b _ _).1
        (by rw [hab, X.color_colorWitness i])
    · intro hab
      rw [← X.color_colorWitness i]
      exact (ofNatColoring_color_eq_iff d a b _ _).2 hab
  refine ⟨⟨fun a b c hab => hdiag a b c ((ofNatColoring_color_eq_iff d a b c c).1 hab),
      fun a b x y hab => (ofNatColoring_color_eq_iff d _ _ _ _).2
        (hconv a b x y ((ofNatColoring_color_eq_iff d a b x y).1 hab))⟩, ?_⟩
  refine ⟨fun i j k => p (d (X.colorWitness i).1 (X.colorWitness i).2)
    (d (X.colorWitness j).1 (X.colorWitness j).2)
    (d (X.colorWitness k).1 (X.colorWitness k).2), ?_⟩
  intro i j k x y hxy
  have hset : {z : V | X.color x z = i ∧ X.color z y = j}
      = {z : V | d x z = d (X.colorWitness i).1 (X.colorWitness i).2 ∧
          d z y = d (X.colorWitness j).1 (X.colorWitness j).2} := by
    ext z
    exact and_congr (hread i x z) (hread j z y)
  rw [hset]
  exact hp _ _ _ x y ((hread k x y).1 hxy)

end PartitionStructure

/-! ### The vertex set of step 3 and its stability -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace VColBipBlk

variable {s t : Set Ω}

/-- §9.4, step 3.  The **vertex set** of the coherent configuration `X`: the singletons of
the points of `V₁` together with the blocks.  This is the set that
`Babai.IsImprimitiveCaseOn` and its analogues in §9.7 and §9.8 read the configuration
on. -/
def vtx (G : VColBipBlk ↥s ℕ) : Set (Set ↥s) := {A | ∃ x, G.part₁ x ∧ A = {x}} ∪ G.blocks

theorem mem_vtx_iff (G : VColBipBlk ↥s ℕ) (A : Set ↥s) :
    A ∈ G.vtx ↔ IsVertexOn G.part₁ G.blocks A := Iff.rfl

theorem singleton_mem_vtx (G : VColBipBlk ↥s ℕ) {x : ↥s} (hx : G.part₁ x) :
    ({x} : Set ↥s) ∈ G.vtx := Or.inl ⟨x, hx, rfl⟩

theorem block_mem_vtx (G : VColBipBlk ↥s ℕ) {B : Set ↥s} (hB : B ∈ G.blocks) :
    B ∈ G.vtx := Or.inr hB

private theorem pair_ne_zero {a b : ℕ} (ha : a ≠ 0) : Nat.pair a b ≠ 0 := by
  intro h
  have h0 : Nat.pair a b = Nat.pair 0 0 := by rw [h]; simp [Nat.pair]
  exact ha (Nat.pair_eq_pair.1 h0).1

/-- The initial vertex color of a vertex is not the color `0` of a non-vertex. -/
theorem initVtxColor_ne_zero (G : VColBipBlk ↥s ℕ) {A : Set ↥s}
    (hA : IsVertexOn G.part₁ G.blocks A) : initVtxColor G A ≠ 0 := by
  classical
  rcases hA with hA | hA
  · rw [initVtxColor, if_pos hA]
    exact pair_ne_zero one_ne_zero
  · have hns : ¬ ∃ x, G.part₁ x ∧ A = {x} := by
      rintro ⟨x, hx, rfl⟩
      exact G.blocks_off₁ _ hA x rfl hx
    rw [initVtxColor, if_neg hns, if_pos hA]
    exact pair_ne_zero (by norm_num)

/-- A subset whose initial vertex color is that of a vertex is a vertex: the initial
coloring gives a non-vertex the color `0` and a vertex a color of the form
`Nat.pair 1 _` or `Nat.pair 2 _`. -/
theorem isVertexOn_of_initVtxColor_eq (G : VColBipBlk ↥s ℕ) {A B : Set ↥s}
    (hA : IsVertexOn G.part₁ G.blocks A) (h : initVtxColor G B = initVtxColor G A) :
    IsVertexOn G.part₁ G.blocks B := by
  classical
  by_cases hB1 : ∃ x, G.part₁ x ∧ B = {x}
  · exact Or.inl hB1
  · by_cases hB2 : B ∈ G.blocks
    · exact Or.inr hB2
    · have hzero : initVtxColor G B = 0 := by rw [initVtxColor, if_neg hB1, if_neg hB2]
      exact absurd (h.symm.trans hzero) (G.initVtxColor_ne_zero hA)

/-- §9.4, step 3.  **The vertex set is stable** (Def. 3.1.5): it is a union of
vertex-color classes of the refined coloring.  This is what makes the restriction of the
coloring to the vertices coherent (Obs. 3.3.2): the refinement refines the initial
coloring, and the initial coloring already tells a vertex from a non-vertex. -/
theorem isStableSet_vtx (G : VColBipBlk ↥s ℕ) : WL.IsStableSet (wlRaw G) G.vtx := by
  intro A hA B h
  have hinit : initColor G B B = initColor G A A := initColor_eq_of_wlRaw_eq G h
  rw [initColor, initColor, if_pos rfl, if_pos rfl] at hinit
  exact G.isVertexOn_of_initVtxColor_eq hA (Nat.pair_eq_pair.1 hinit).2

/-- §9.4, step 3.  The refined coloring, read on the vertices only, is coherent. -/
theorem isCoherentColoring_wlRaw_vtx (G : VColBipBlk ↥s ℕ) :
    WL.IsCoherentColoring (fun u v : ↥G.vtx => wlRaw G (u : Set ↥s) (v : Set ↥s)) :=
  WL.isCoherentColoring_restrict (isCoherentColoring_wlRaw G) (isStableSet_vtx G)

/-- §9.4, steps 5 and 7.  *"`X ← X[W₁ ∪ V₂]`"*, *"Set `X ← X[V₁ ∪ D_j]`"*: **the induced
subconfiguration of the configuration of step 3 on a union of vertex-color classes is a
coherent configuration** (Obs. 3.3.2), with its colors again named canonically.

The set `T` the paper restricts to is a union of vertex-color classes: in step 5 it is the
dominant vertex-color class of `V₁` together with all of `V₂`, in step 7 it is `V₁`
together with one vertex-color class `D_j` of `V₂`. -/
theorem isCoherent_ofNatColoring_wlRaw {G : VColBipBlk ↥s ℕ} {T : Set (Set ↥s)}
    (hT : WL.IsStableSet (wlRaw G) T) :
    (PartitionStructure.ofNatColoring
      (fun u v : ↥T => wlRaw G (u : Set ↥s) (v : Set ↥s))).IsCoherent :=
  PartitionStructure.isCoherent_ofNatColoring
    (WL.isCoherentColoring_restrict (isCoherentColoring_wlRaw G) hT)

/-- A subset of the vertex set that is closed under the diagonal colors of the refinement
is stable, so `Babai.VColBipBlk.isCoherent_ofNatColoring_wlRaw` applies to it. -/
theorem isStableSet_of_subset_vtx {G : VColBipBlk ↥s ℕ} {T : Set (Set ↥s)}
    (hsub : T ⊆ G.vtx)
    (hclosed : ∀ A ∈ T, ∀ B ∈ G.vtx, wlRaw G B B = wlRaw G A A → B ∈ T) :
    WL.IsStableSet (wlRaw G) T := by
  intro A hA B h
  exact hclosed A hA B (isStableSet_vtx G A (hsub hA) B h) h

/-! ### The coherent configuration of step 3 and its `ℕ`-named coloring -/

open scoped Classical in
/-- §9.4, step 3.  **The coloring of the coherent configuration `X` that steps 5-9 carry.**
It is `Babai.VColBipBlk.wlColor` without the shift by one: on a pair of vertices the name
of the WL color is its rank among the colors that occur, and off the vertex set the color
is `0`, the normalization that `Babai.BlkImprimitiveObj.c_off` and `Babai.BlkCaseObj.c_off`
demand.

The shift has to go because a `Babai.PartitionStructure.natColor` attains the color `0`;
see the module docstring. -/
noncomputable def wlCaseColor (G : VColBipBlk ↥s ℕ) (A B : Set ↥s) : ℕ :=
  if hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B then
    wlNamed G ⟨A, hv.1⟩ ⟨B, hv.2⟩ else 0

theorem wlCaseColor_off (G : VColBipBlk ↥s ℕ) {A B : Set ↥s}
    (h : ¬ (IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)) :
    wlCaseColor G A B = 0 := by
  classical
  rw [wlCaseColor, dif_neg h]

/-- On the vertices the two namings differ by the shift of
`Babai.VColBipBlk.wlColor`, so they have the same color classes there. -/
theorem wlColor_eq_wlCaseColor_succ (G : VColBipBlk ↥s ℕ) {A B : Set ↥s}
    (h : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B) :
    wlColor G A B = wlCaseColor G A B + 1 := by
  classical
  rw [wlColor, wlCaseColor, dif_pos h, dif_pos h]

/-- §9.4, step 3.  **The coloring of steps 5-9 is canonical.**  The proof of
`Babai.VColBipBlk.wlColor_map`, without the shift. -/
theorem wlCaseColor_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (A B : Set ↥s) :
    wlCaseColor H (φ '' A) (φ '' B) = wlCaseColor G A B := by
  classical
  have hvA := isVertexOn_image_iff h.part₁ h.blocks A
  have hvB := isVertexOn_image_iff h.part₁ h.blocks B
  by_cases hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B
  · have hm := wlColor_map h A B
    rw [wlColor_eq_wlCaseColor_succ H ⟨hvA.2 hv.1, hvB.2 hv.2⟩,
      wlColor_eq_wlCaseColor_succ G hv] at hm
    exact Nat.add_right_cancel hm
  · rw [wlCaseColor_off G hv, wlCaseColor_off H (fun hh => hv ⟨hvA.1 hh.1, hvB.1 hh.2⟩)]

/-- The unshifted names have the classes of the raw refinement on vertices. -/
theorem wlCaseColor_eq_iff_raw (G : VColBipBlk ↥s ℕ) {A B C D : Set ↥s}
    (hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)
    (hv' : IsVertexOn G.part₁ G.blocks C ∧ IsVertexOn G.part₁ G.blocks D) :
    wlCaseColor G A B = wlCaseColor G C D ↔ wlRaw G A B = wlRaw G C D := by
  classical
  rw [wlCaseColor, wlCaseColor, dif_pos hv, dif_pos hv']
  exact wlNamed_eq_iff G ⟨A, hv.1⟩ ⟨B, hv.2⟩ ⟨C, hv'.1⟩ ⟨D, hv'.2⟩

/-- The unshifted coloring restricted to the vertices is coherent. -/
theorem wlCaseColor_vtx_coherent (G : VColBipBlk ↥s ℕ) :
    WL.IsCoherentColoring (fun u v : ↥G.vtx => wlCaseColor G u.val v.val) :=
  WL.named_coherent_congr
    (fun a b x y => (wlCaseColor_eq_iff_raw G ⟨a.property, b.property⟩ ⟨x.property, y.property⟩).symm)
    (isCoherentColoring_wlRaw_vtx G)

/-- A stable restriction keeps the classes and the integer order of the full refinement. -/
noncomputable def wlRestrictedConfig (G : VColBipBlk ↥s ℕ) (T : Set (Set ↥s)) :
    PartitionStructure ↥T :=
  PartitionStructure.ofNamedColoring (fun u v : ↥T => wlCaseColor G u.val v.val)

theorem wlRestrictedConfig_eq_iff (G : VColBipBlk ↥s ℕ) {T : Set (Set ↥s)}
    (hsub : T ⊆ G.vtx) (a b x y : ↥T) :
    (wlRestrictedConfig G T).color a b = (wlRestrictedConfig G T).color x y ↔
      wlRaw G a.val b.val = wlRaw G x.val y.val :=
  (PartitionStructure.ofNamedColoring_color_eq_iff _ a b x y).trans
    (wlCaseColor_eq_iff_raw G ⟨hsub a.property, hsub b.property⟩ ⟨hsub x.property, hsub y.property⟩)

theorem wlRestrictedConfig_coherent (G : VColBipBlk ↥s ℕ) {T : Set (Set ↥s)}
    (hsub : T ⊆ G.vtx) (hT : WL.IsStableSet (wlRaw G) T) :
    (wlRestrictedConfig G T).IsCoherent :=
  PartitionStructure.named_isCoherent_of_kernel _
    (WL.isCoherentColoring_restrict (isCoherentColoring_wlRaw G) hT)
    (fun a b x y => (wlRestrictedConfig_eq_iff G hsub a b x y).symm)

/-- §9.4, step 3.  **The coherent configuration `X`** of step 3, on the vertex set
*"points of `V₁` plus blocks"*.  Its colors use the integer names of `Babai.WL.namedIter`, so its
`natColor` is the canonical coloring `Babai.VColBipBlk.wlCaseColor`. -/
noncomputable def wlConfig (G : VColBipBlk ↥s ℕ) : PartitionStructure ↥G.vtx := by
  classical
  exact PartitionStructure.ofNamedColoring (fun u v : ↥G.vtx => wlCaseColor G u.val v.val)

/-- Section 9.4, step 3: the named configuration is coherent. -/
theorem wlConfig_isCoherent (G : VColBipBlk ↥s ℕ) : (wlConfig G).IsCoherent := by
  classical
  exact PartitionStructure.isCoherent_ofNamedColoring (wlCaseColor_vtx_coherent G)

/-- The colors that occur on the vertices are exactly `Babai.VColBipBlk.wlColorSet`. -/
theorem natCodes_wlRaw_vtx (G : VColBipBlk ↥s ℕ) :
    PartitionStructure.natCodes (fun u v : ↥G.vtx => wlRaw G (u : Set ↥s) (v : Set ↥s))
      = wlColorSet G := by
  ext k
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨u, v, u.2, v.2, rfl⟩
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), rfl⟩

/-- §9.4, step 3.  The `natColor` of the configuration of step 3 **is** the coloring
`Babai.VColBipBlk.wlCaseColor`; this is the equation that the field
`Babai.IsBipartiteCase.coherent` asks for. -/
theorem natColor_wlConfig (G : VColBipBlk ↥s ℕ) (u v : ↥G.vtx) :
    (wlConfig G).natColor u v = wlCaseColor G (u : Set ↥s) (v : Set ↥s) := by
  classical
  letI : Fintype ↥G.vtx := Fintype.ofFinite _
  let c := fun u v : ↥G.vtx => wlCaseColor G u.val v.val
  have hcoh := wlCaseColor_vtx_coherent G
  have he : c = @WL.namedIter (Vtx G) (Fintype.ofFinite _) (vtxInitColor G) (wlRounds Ω) := by
    funext u v
    exact (show wlCaseColor G u.val v.val = wlNamed G u v by
      rw [wlCaseColor, dif_pos ⟨u.property, v.property⟩]; rfl).trans (wlNamed_eq G u v)
  have hr : 1 ≤ wlRounds Ω := Nat.card_pos
  have hn : Finset.univ.image (fun p : ↥G.vtx × ↥G.vtx => c p.1 p.2) =
      Finset.range (Finset.univ.image (fun p : ↥G.vtx × ↥G.vtx => c p.1 p.2)).card := by
    rw [he]
    have hi : Fintype.ofFinite (Vtx G) = (inferInstance : Fintype ↥G.vtx) := Subsingleton.elim _ _
    rw [hi]
    exact WL.namedIter_image _ hr
  change WL.namedRecode c u v = c u v
  rw [WL.namedRecode_eq_step ((WL.isStable_iff_isCoherentColoring hcoh.1).2 hcoh)]
  exact congrFun (congrFun (WL.namedStep_eq_of_stable
    ((WL.isStable_iff_isCoherentColoring hcoh.1).2 hcoh) hn) u) v

/-- The named configuration and the raw refinement have exactly the same classes. -/
theorem wlConfig_color_eq_iff (G : VColBipBlk ↥s ℕ) (a b x y : ↥G.vtx) :
    (wlConfig G).color a b = (wlConfig G).color x y ↔
      wlRaw G a.val b.val = wlRaw G x.val y.val := by
  rw [← (wlConfig G).natColor_eq_iff, natColor_wlConfig, natColor_wlConfig]
  exact wlCaseColor_eq_iff_raw G ⟨a.property, b.property⟩ ⟨x.property, y.property⟩

/-- Two vertices have the same vertex color in the configuration of step 3 exactly if the
refinement gives them the same diagonal color. -/
theorem wlConfig_vcolor_eq_iff (G : VColBipBlk ↥s ℕ) (u v : ↥G.vtx) :
    (wlConfig G).vcolor u = (wlConfig G).vcolor v ↔
      wlRaw G (u : Set ↥s) (u : Set ↥s) = wlRaw G (v : Set ↥s) (v : Set ↥s) := by
  change (wlConfig G).color u u = (wlConfig G).color v v ↔ _
  rw [← (wlConfig G).natColor_eq_iff, natColor_wlConfig, natColor_wlConfig]
  exact wlCaseColor_eq_iff_raw G ⟨u.property, u.property⟩ ⟨v.property, v.property⟩

/-- §9.4, step 3.  *"the vertex-colors discriminate between `V₁` and `V₂`"*, read in the
configuration of step 3: a point of `V₁` and a block have different vertex colors. -/
theorem wlConfig_vcolor_ne (G : VColBipBlk ↥s ℕ) {x : ↥s} (hx : G.part₁ x)
    {B : Set ↥s} (hB : B ∈ G.blocks) :
    (wlConfig G).vcolor ⟨{x}, G.singleton_mem_vtx hx⟩
      ≠ (wlConfig G).vcolor ⟨B, G.block_mem_vtx hB⟩ := by
  intro hc
  have hraw := (wlConfig_vcolor_eq_iff G _ _).1 hc
  refine G.wlColor_ne_of_part₁_blocks hx hB ?_
  have hvx : IsVertexOn G.part₁ G.blocks ({x} : Set ↥s) := Or.inl ⟨x, hx, rfl⟩
  have hvB : IsVertexOn G.part₁ G.blocks B := Or.inr hB
  exact wlColor_eq_of_raw G ⟨hvx, hvx⟩ ⟨hvB, hvB⟩ hraw

/-! ### Counting the vertices of the two parts -/

theorem ncard_setOf_mem_blocks (G : VColBipBlk ↥s ℕ) :
    {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks}.ncard = G.blocks.ncard := by
  have himg : (Subtype.val '' {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks} : Set (Set ↥s))
      = G.blocks := by
    ext B
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hB
      exact ⟨⟨B, G.block_mem_vtx hB⟩, hB, rfl⟩
  rw [← Set.ncard_image_of_injective {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks}
    Subtype.val_injective, himg]

theorem ncard_setOf_mem_pts (G : VColBipBlk ↥s ℕ) :
    {u : ↥G.vtx | (u : Set ↥s) ∈ {A : Set ↥s | ∃ x, G.part₁ x ∧ A = {x}}}.ncard
      = {x : ↥s | G.part₁ x}.ncard := by
  have himg : (Subtype.val ''
      {u : ↥G.vtx | (u : Set ↥s) ∈ {A : Set ↥s | ∃ x, G.part₁ x ∧ A = {x}}} : Set (Set ↥s))
      = (fun x : ↥s => ({x} : Set ↥s)) '' {x : ↥s | G.part₁ x} := by
    ext A
    constructor
    · rintro ⟨u, ⟨x, hx, hux⟩, rfl⟩
      exact ⟨x, hx, hux.symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨{x}, G.singleton_mem_vtx hx⟩, ⟨x, hx, rfl⟩, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Set.ncard_image_of_injective _ (Set.singleton_injective)]

/-- §9.4, step 6, the hypothesis of the Large clique lemma (Lemma 3.4.25): *"`V₁` is larger
than any other color-class in `X`."*

After step 5 the first part is a single vertex-color class, so every *other* vertex-color
class consists of blocks; there are `n₂` of those, and `n₂ < α n₁ < |V₁|` at this point of
the procedure, which is the hypothesis `hlt`. -/
theorem vertexClass_ncard_lt_of_dominant (G : VColBipBlk ↥s ℕ)
    {i₀ : Fin (wlConfig G).rank}
    (hV₁ : {u : ↥G.vtx | (u : Set ↥s) ∈ {A : Set ↥s | ∃ x, G.part₁ x ∧ A = {x}}}
      = (wlConfig G).vertexClass i₀)
    (hlt : G.blocks.ncard < {x : ↥s | G.part₁ x}.ncard)
    (i : Fin (wlConfig G).rank) (hi : i ≠ i₀) :
    ((wlConfig G).vertexClass i).ncard < ((wlConfig G).vertexClass i₀).ncard := by
  have hsub : (wlConfig G).vertexClass i ⊆ {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks} := by
    intro u hu
    rcases u.2 with h | h
    · exact absurd ((hV₁ ▸ h : u ∈ (wlConfig G).vertexClass i₀).symm.trans hu) (Ne.symm hi)
    · exact h
  calc ((wlConfig G).vertexClass i).ncard
      ≤ {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = G.blocks.ncard := G.ncard_setOf_mem_blocks
    _ < {x : ↥s | G.part₁ x}.ncard := hlt
    _ = ((wlConfig G).vertexClass i₀).ncard := by
        rw [← G.ncard_setOf_mem_pts, hV₁]

/-- §9.4, step 3, **the `coherent` field of the `Case` of §9.6, §9.7 and §9.8**: once `X₁`
and `X₂` are homogeneous — which is what steps 5 and 7 arrange — the coherent configuration
of step 3 has the two parts as its two vertex-color classes.

The hypotheses are read on the refined coloring: `hom₁` is *"`X₁` is homogeneous"*, `hom₂`
is *"`X₂` is homogeneous"*, and `hne₁`, `hne₂` say that the two parts are nonempty, which
is Def. 3.1.1 for the two vertex colors (`Babai.PartitionStructure.vertexClass` of a color
that does not occur is empty, and the paper's parts are not). -/
theorem exists_wlConfig (G : VColBipBlk ↥s ℕ)
    (hom₁ : ∀ x y : ↥s, G.part₁ x → G.part₁ y →
      wlRaw G ({x} : Set ↥s) {x} = wlRaw G ({y} : Set ↥s) {y})
    (hom₂ : ∀ B ∈ G.blocks, ∀ B' ∈ G.blocks, wlRaw G B B = wlRaw G B' B')
    (hne₁ : ∃ x, G.part₁ x) (hne₂ : G.blocks.Nonempty) :
    ∃ X : PartitionStructure ↥G.vtx, X.IsCoherent ∧
      X.natColor = (fun u v : ↥G.vtx => wlCaseColor G (u : Set ↥s) (v : Set ↥s)) ∧
      ∃ i j : Fin X.rank, i ≠ j ∧
        {u : ↥G.vtx | (u : Set ↥s) ∈ {A : Set ↥s | ∃ x, G.part₁ x ∧ A = {x}}}
          = X.vertexClass i ∧
        {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks} = X.vertexClass j ∧
        (∀ u : ↥G.vtx, u ∈ {u : ↥G.vtx | (u : Set ↥s) ∈ {A : Set ↥s | ∃ x, G.part₁ x ∧ A = {x}}}
          ∨ u ∈ {u : ↥G.vtx | (u : Set ↥s) ∈ G.blocks}) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne₁
  obtain ⟨B₀, hB₀⟩ := hne₂
  set u₀ : ↥G.vtx := ⟨{x₀}, G.singleton_mem_vtx hx₀⟩ with hu₀
  set v₀ : ↥G.vtx := ⟨B₀, G.block_mem_vtx hB₀⟩ with hv₀
  refine ⟨wlConfig G, wlConfig_isCoherent G,
    funext fun u => funext fun v => natColor_wlConfig G u v,
    (wlConfig G).vcolor u₀, (wlConfig G).vcolor v₀, G.wlConfig_vcolor_ne hx₀ hB₀, ?_, ?_, ?_⟩
  · ext u
    simp only [Set.mem_setOf_eq, PartitionStructure.vertexClass]
    constructor
    · rintro ⟨x, hx, hux⟩
      refine (wlConfig_vcolor_eq_iff G u u₀).2 ?_
      rw [hux]
      exact hom₁ x x₀ hx hx₀
    · intro hvc
      rcases u.2 with h | h
      · exact h
      · exact absurd (hvc.symm.trans
          ((wlConfig_vcolor_eq_iff G u v₀).2 (hom₂ _ h _ hB₀)))
          (G.wlConfig_vcolor_ne hx₀ hB₀)
  · ext u
    simp only [Set.mem_setOf_eq, PartitionStructure.vertexClass]
    constructor
    · intro hu
      exact (wlConfig_vcolor_eq_iff G u v₀).2 (hom₂ _ hu _ hB₀)
    · intro hvc
      rcases u.2 with h | h
      · obtain ⟨x, hx, hux⟩ := h
        have hraw : wlRaw G ({x₀} : Set ↥s) {x₀} = wlRaw G (u : Set ↥s) (u : Set ↥s) := by
          rw [hux]; exact hom₁ x₀ x hx₀ hx
        exact absurd (((wlConfig_vcolor_eq_iff G u₀ u).2 hraw).trans hvc)
          (G.wlConfig_vcolor_ne hx₀ hB₀)
      · exact h
  · intro u
    exact u.2

end VColBipBlk

end Babai
