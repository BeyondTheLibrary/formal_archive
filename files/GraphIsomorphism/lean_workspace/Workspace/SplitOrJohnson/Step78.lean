/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 7: the restriction `X ← X[V₁ ∪ D_j]` to one vertex-color class of `V₂`.
-/
import Workspace.SplitOrJohnson.Step6Claim

/-!
# §9.4, step 7

Version 2.5, lines 4152-4156 of `babai-gi-source/quasi25.txt`.

> *"7. If `X₂` is not homogeneous, let `(D₁, …, D_k)` be the partition of `V₂` into
> vertex-color classes.  Pick the smallest `j` such that the induced bipartite substructure
> `X[V₁, D_j]` is nontrivial.  (Such a `j` exists because otherwise `V₁` would be a twin
> equivalence class in `X₁₂`.)  Set `X ← X[V₁ ∪ D_j]`.  This automatically updates
> `V₂ ← D_j` (: `X` bihomogeneous :)"*

As in step 5 (`Workspace/SplitOrJohnson/Step6.lean`), the step is taken **literally**: it
restricts the coherent configuration of step 3 to a union of vertex-color classes and does
not re-run WL refinement, so everything stays on the ambient point set `↥□X` and the
coloring is still `Babai.VColBipBlk.wlRaw` of the input.

## The step is taken unconditionally

The paper guards step 7 by *"if `X₂` is not homogeneous"*.  Here the same construction is
performed for every object, because **when `X₂` is homogeneous it is the identity**: the
blocks then form a single vertex-color class `D₁`, the link `X[V₁, D₁] = X₁₂` is nontrivial
(the parenthetical of step 3), so the chosen class is `D₁` and `X[V₁ ∪ D₁] = X`
(`Babai.step7Blocks_eq_of_homogeneous`, `Babai.step7Vtx_eq_of_homogeneous`,
`Babai.step7Set_eq_of_homogeneous`).  Not branching keeps the chain of §9.4 shorter by one
`Babai.FindsAtMultCost.cases`; it changes nothing that the paper says.

| Paper | Lean |
|---|---|
| §9.4, step 7, the vertex color of a block | `Babai.step7BlkColor` |
| §9.4, step 7, *"`X[V₁, D_j]` is nontrivial"* | `Babai.LinkTrivialOn` |
| §9.4, step 7, *"the smallest `j`"* | `Babai.step7Color` |
| §9.4, step 7, *"such a `j` exists"* | `Babai.step7Colors_nonempty` |
| §9.4, step 7, *"`X ← X[V₁ ∪ D_j]`"* | `Babai.step7Vtx`, `Babai.step7Config` |
| §9.4, step 7, *"(: `X` bihomogeneous :)"* | `Babai.step7Config_hom₁`, `Babai.step7Config_hom₂` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open VColBipBlk

/-! ### `W₁` is not a set of twins of the graph

The contradiction that both the Claim of step 6 and the parenthetical of step 7 rest on:
the restricted instance of step 5 is an admissible input of Theorem 9.2.2 for the threshold
`α_new < 1`, so its symmetry defect on `W₁` is at least `1 - α_new > 0` and `W₁` is not a
set of twins. -/

section NoTwins

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, steps 6 and 7, *"a contradiction with the positive symmetry defect assumption"*,
*"otherwise `V₁` would be a twin equivalence class in `X₁₂`"*: **the points of `W₁` are not
all pairwise twins of `X[W₁ ∪ V₂]`.** -/
theorem not_isTwinSet_step5Obj_V₁ (h : ¬ AllClassesSmall X)
    [Fintype ↥(step5Set X)] : ¬ IsTwinSet (step5Obj X).Aut (step5Obj X).V₁ := by
  classical
  intro hall
  have hle : (step5Obj X).V₁.ncard ≤ (step5Obj X).symmetricity₁ :=
    ncard_le_symmetricity₁ _ (fun _ hx => hx) hall
  obtain ⟨-, -, hdef⟩ := step5Obj_isThm922Input (X := X) h
  have hpos : 0 < (step5Obj X).V₁.ncard := by
    rw [step5Obj_V₁_ncard]
    have := two_le_dominantClass_ncard h
    omega
  have hq : ((step5Obj X).defect₁ : ℚ) ≤ 0 := by
    have hn : (0 : ℚ) < ((step5Obj X).V₁.ncard : ℚ) := by exact_mod_cast hpos
    have hle' : ((step5Obj X).V₁.ncard : ℚ) ≤ ((step5Obj X).symmetricity₁ : ℚ) := by
      exact_mod_cast hle
    have : (1 : ℚ) ≤ ((step5Obj X).symmetricity₁ : ℚ) / ((step5Obj X).V₁.ncard : ℚ) := by
      rw [le_div_iff₀ hn]; linarith
    rw [VColBipBlk.defect₁]; linarith
  have hqR : ((step5Obj X).defect₁ : ℝ) ≤ 0 := by exact_mod_cast hq
  have hlt := alphaNew_lt_one (X := X) h
  linarith

/-- The points of `W₁` all have the same color `f`: `X₁` is homogeneous (step 5), and the
refined coloring refines the vertex coloring of the input. -/
theorem f_eq_of_mem_dominantClass {x y : ↥X.car} (hx : x ∈ dominantClass X)
    (hy : y ∈ dominantClass X) : X.obj.1.1.f x = X.obj.1.1.f y := by
  have hraw : wlRaw X.obj.1.1 ({x} : Set ↥X.car) {x}
      = wlRaw X.obj.1.1 ({y} : Set ↥X.car) {y} :=
    wlRaw_eq_of_wlColor_eq X.obj.1.1
      ⟨Or.inl ⟨x, hx.1, rfl⟩, Or.inl ⟨x, hx.1, rfl⟩⟩
      ⟨Or.inl ⟨y, hy.1, rfl⟩, Or.inl ⟨y, hy.1, rfl⟩⟩ (hx.2.trans hy.2.symm)
  exact X.obj.1.1.f_eq_of_wlColor_eq hx.1 hy.1
    (X.obj.1.1.wlColor_eq_of_wlRaw_eq
      ⟨Or.inl ⟨x, hx.1, rfl⟩, Or.inl ⟨x, hx.1, rfl⟩⟩
      ⟨Or.inl ⟨y, hy.1, rfl⟩, Or.inl ⟨y, hy.1, rfl⟩⟩ hraw)

/-- **Two points of `W₁` joined to the same blocks are twins** of `X[W₁ ∪ V₂]`: they have
the same color `f` because `X₁` is homogeneous. -/
theorem isTwin_step5Obj_of_edges [Fintype ↥(step5Set X)] {x y : ↥(dominantClass X)}
    (hxy : x ≠ y)
    (hE : ∀ B ∈ X.obj.1.1.blocks,
      (((x : ↥X.car), B) ∈ X.obj.1.1.E ↔ ((y : ↥X.car), B) ∈ X.obj.1.1.E)) :
    IsTwin (step5Obj X).Aut (step5Point X x) (step5Point X y) := by
  classical
  refine ((step5Obj X).isTwin_iff (step5Point_part₁ X x) (step5Point_part₁ X y)
    (fun hc => hxy (step5Point_injective X hc))).2
    ⟨f_eq_of_mem_dominantClass X x.2 y.2, ?_⟩
  intro B hB
  exact hE _ hB

/-- §9.4, step 5.  **There is at least one block.**  If there were none, all the points of
`W₁` would be twins of `X[W₁ ∪ V₂]` — they have the same color `f` because `X₁` is
homogeneous, and there is no block to tell them apart — contradicting the positive symmetry
defect.  (This is the paper's *"`E` is not empty because of the positive symmetry defect
assumption"*, line 4101, read after step 5.) -/
theorem blocks_nonempty_of_dominant (h : ¬ AllClassesSmall X) :
    X.obj.1.1.blocks.Nonempty := by
  classical
  letI : Fintype ↥(step5Set X) := Fintype.ofFinite _
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  refine not_isTwinSet_step5Obj_V₁ X h ?_
  intro p hp q hq hpq
  obtain ⟨x, rfl⟩ := exists_step5Point X hp
  obtain ⟨y, rfl⟩ := exists_step5Point X hq
  refine isTwin_step5Obj_of_edges X (fun hc => hpq (congrArg (step5Point X) hc)) ?_
  intro B hB
  rw [hemp] at hB
  exact absurd hB (Set.notMem_empty B)

end NoTwins

/-! ### §9.4, step 7: the vertex-color classes of `V₂` and the choice of `D_j` -/

section Step7

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 7.  **The vertex color of a block** in the configuration of step 3, named
by the named WL process.  The classes `D₁, …, D_k` of the paper are the classes of
this coloring, and *"the smallest `j`"* is the smallest value it takes. -/
noncomputable def step7BlkColor (B : Set ↥X.car) : ℕ :=
  VColBipBlk.wlCaseColor X.obj.1.1 B B

/-- Two blocks of the same vertex color have the same refined diagonal color: the naming is
injective on the colors that occur. -/
theorem wlRaw_eq_of_step7BlkColor_eq {B B' : Set ↥X.car} (hB : B ∈ X.obj.1.1.blocks)
    (hB' : B' ∈ X.obj.1.1.blocks) (h : step7BlkColor X B = step7BlkColor X B') :
    wlRaw X.obj.1.1 B B = wlRaw X.obj.1.1 B' B' := by
  exact (VColBipBlk.wlCaseColor_eq_iff_raw X.obj.1.1
    ⟨Or.inr hB, Or.inr hB⟩ ⟨Or.inr hB', Or.inr hB'⟩).1 h

/-- §9.4, step 7.  *"the induced bipartite substructure `X[V₁, D_j]`"* is **trivial**: all
the pairs (point of `W₁`, block of the color class `k`) carry the same color of the
configuration of step 3. -/
def LinkTrivialOn (X : Pt (BipBlockInputs Ω)) (k : ℕ) : Prop :=
  ∀ x ∈ dominantClass X, ∀ y ∈ dominantClass X,
    ∀ B ∈ X.obj.1.1.blocks, ∀ B' ∈ X.obj.1.1.blocks,
      step7BlkColor X B = k → step7BlkColor X B' = k →
        wlRaw X.obj.1.1 ({x} : Set ↥X.car) B = wlRaw X.obj.1.1 ({y} : Set ↥X.car) B'

/-- §9.4, step 7.  The colors `j` that the step may choose: those of a nonempty class `D_j`
whose link with `V₁` is nontrivial. -/
def step7Colors (X : Pt (BipBlockInputs Ω)) : Set ℕ :=
  {k | (∃ B ∈ X.obj.1.1.blocks, step7BlkColor X B = k) ∧ ¬ LinkTrivialOn X k}

/-- §9.4, step 7.  *"Pick the smallest `j` such that the induced bipartite substructure
`X[V₁, D_j]` is nontrivial."*  The smallest such color; it is a function of the object,
hence canonical. -/
noncomputable def step7Color (X : Pt (BipBlockInputs Ω)) : ℕ := sInf (step7Colors X)

/-- §9.4, step 7, the parenthetical: *"Such a `j` exists because otherwise `V₁` would be a
twin equivalence class in `X₁₂`."*

If every class `D_j` had a trivial link with `W₁`, then for any two points `x ≠ y` of `W₁`
and any block `B` the pairs `({x}, B)` and `({y}, B)` would carry the same color of the
configuration, hence — the refinement refining the edge relation — `x` and `y` would be
joined to the same blocks; with the equality of colors `f` that the homogeneity of `X₁`
gives, `x` and `y` would be twins of `X[W₁ ∪ V₂]`.  So `W₁` would be a set of twins, which
`Babai.not_isTwinSet_step5Obj_V₁` forbids. -/
theorem step7Colors_nonempty (h : ¬ AllClassesSmall X) : (step7Colors X).Nonempty := by
  classical
  letI : Fintype ↥(step5Set X) := Fintype.ofFinite _
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have htriv : ∀ k, (∃ B ∈ X.obj.1.1.blocks, step7BlkColor X B = k) → LinkTrivialOn X k := by
    intro k hk
    by_contra hnt
    exact absurd (Set.eq_empty_iff_forall_notMem.1 hemp k) (by simp [step7Colors, hk, hnt])
  refine not_isTwinSet_step5Obj_V₁ X h ?_
  intro p hp q hq hpq
  obtain ⟨x, rfl⟩ := exists_step5Point X hp
  obtain ⟨y, rfl⟩ := exists_step5Point X hq
  refine isTwin_step5Obj_of_edges X (fun hc => hpq (congrArg (step5Point X) hc)) ?_
  intro B hB
  refine X.obj.1.1.edge_iff_of_wlRaw_eq x.2.1 y.2.1 hB ?_
  exact htriv (step7BlkColor X B) ⟨B, hB, rfl⟩ _ x.2 _ y.2 B hB B hB rfl rfl

theorem step7Color_mem (h : ¬ AllClassesSmall X) : step7Color X ∈ step7Colors X :=
  Nat.sInf_mem (step7Colors_nonempty X h)

/-- §9.4, step 7.  The class `D_j`. -/
def step7Blocks (X : Pt (BipBlockInputs Ω)) : Set (Set ↥X.car) :=
  {B | B ∈ X.obj.1.1.blocks ∧ step7BlkColor X B = step7Color X}

theorem step7Blocks_subset : step7Blocks X ⊆ X.obj.1.1.blocks := fun _ hB => hB.1

theorem step7Blocks_nonempty (h : ¬ AllClassesSmall X) : (step7Blocks X).Nonempty := by
  obtain ⟨⟨B, hB, hBc⟩, -⟩ := step7Color_mem X h
  exact ⟨B, hB, hBc⟩

/-- §9.4, step 7.  **The link `X[V₁, D_j]` is nontrivial**, which is the parenthetical
*"`X₁₂` is nontrivial"* of step 8 for the restricted instance. -/
theorem step7_link_nontrivial (h : ¬ AllClassesSmall X) :
    ∃ x ∈ dominantClass X, ∃ y ∈ dominantClass X, ∃ B ∈ step7Blocks X, ∃ B' ∈ step7Blocks X,
      wlRaw X.obj.1.1 ({x} : Set ↥X.car) B ≠ wlRaw X.obj.1.1 ({y} : Set ↥X.car) B' := by
  have hnt := (step7Color_mem X h).2
  rw [LinkTrivialOn] at hnt
  push_neg at hnt
  obtain ⟨x, hx, y, hy, B, hB, B', hB', hBc, hB'c, hne⟩ := hnt
  exact ⟨x, hx, y, hy, B, ⟨hB, hBc⟩, B', ⟨hB', hB'c⟩, hne⟩

/-! ### The restriction `X ← X[V₁ ∪ D_j]` -/

/-- §9.4, step 7.  **The vertex set of `X[V₁ ∪ D_j]`**: the singletons of the points of
`W₁` together with the blocks of the chosen vertex-color class. -/
noncomputable def step7Vtx (X : Pt (BipBlockInputs Ω)) : Set (Set ↥X.car) :=
  step5Pts X ∪ step7Blocks X

theorem step7Vtx_subset_step5Vtx : step7Vtx X ⊆ step5Vtx X := by
  rintro A (hA | hA)
  · exact Or.inl hA
  · exact Or.inr hA.1

theorem step7Vtx_subset_vtx : step7Vtx X ⊆ (X.obj.1.1).vtx :=
  fun _ hA => step5Vtx_subset_vtx X (step7Vtx_subset_step5Vtx X hA)

/-- §9.4, step 7.  **The vertex set of `X[V₁ ∪ D_j]` is stable** (Def. 3.1.5): it is the
union of the vertex-color class `W₁` with the vertex-color class `D_j`.  This is the
hypothesis of Observation 3.3.2 that makes the restriction a coherent configuration. -/
theorem step7Vtx_isStableSet :
    WL.IsStableSet (wlRaw X.obj.1.1) (step7Vtx X) := by
  classical
  refine VColBipBlk.isStableSet_of_subset_vtx (step7Vtx_subset_vtx X) ?_
  rintro A hA B hB hcol
  rcases hA with hA | hA
  · exact Or.inl (step5Pts_isStableSet X A hA B hcol)
  · -- `B` has the diagonal color of a block of `D_j`, so it is a block of `D_j`
    have hvA : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks A := Or.inr hA.1
    have hBblk : B ∈ X.obj.1.1.blocks := by
      rcases hB with ⟨x, hx, rfl⟩ | hB
      · exact absurd (X.obj.1.1.wlColor_eq_of_wlRaw_eq ⟨hvA, hvA⟩
          ⟨Or.inl ⟨x, hx, rfl⟩, Or.inl ⟨x, hx, rfl⟩⟩ hcol.symm)
          (X.obj.1.1.wlColor_ne_of_part₁_blocks hx hA.1).symm
      · exact hB
    refine Or.inr ⟨hBblk, ?_⟩
    have : step7BlkColor X B = step7BlkColor X A := by
      exact (VColBipBlk.wlCaseColor_eq_iff_raw X.obj.1.1
        ⟨Or.inr hBblk, Or.inr hBblk⟩ ⟨hvA, hvA⟩).2 hcol
    rw [this, hA.2]

/-- §9.4, step 7.  *"Set `X ← X[V₁ ∪ D_j]`"*: **the restricted configuration**, the
coloring of step 3 read on the new vertex set, named in the order of the integer WL colors. -/
noncomputable def step7Config (X : Pt (BipBlockInputs Ω)) :
    PartitionStructure ↥(step7Vtx X) :=
  VColBipBlk.wlRestrictedConfig X.obj.1.1 (step7Vtx X)

/-- §9.4, step 7.  The restriction leaves a coherent configuration: Observation 3.3.2. -/
theorem step7Config_isCoherent : (step7Config X).IsCoherent :=
  VColBipBlk.wlRestrictedConfig_coherent X.obj.1.1 (step7Vtx_subset_vtx X) (step7Vtx_isStableSet X)

theorem step7Config_color_eq_iff (u v u' v' : ↥(step7Vtx X)) :
    (step7Config X).natColor u v = (step7Config X).natColor u' v'
      ↔ wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)
        = wlRaw X.obj.1.1 (u' : Set ↥X.car) (v' : Set ↥X.car) :=
  ((step7Config X).natColor_eq_iff u v u' v').trans
    (VColBipBlk.wlRestrictedConfig_eq_iff X.obj.1.1 (step7Vtx_subset_vtx X) u v u' v')

/-- §9.4, step 7, the parenthetical *"(: `X` bihomogeneous :)"*, first half: all the
vertices of `W₁` carry one vertex color (this is the parenthetical of step 5, unchanged by
the restriction). -/
theorem step7Config_hom₁ {x y : ↥X.car} (hx : x ∈ dominantClass X)
    (hy : y ∈ dominantClass X) :
    wlRaw X.obj.1.1 ({x} : Set ↥X.car) {x} = wlRaw X.obj.1.1 ({y} : Set ↥X.car) {y} :=
  wlRaw_eq_of_wlColor_eq X.obj.1.1
    ⟨Or.inl ⟨x, hx.1, rfl⟩, Or.inl ⟨x, hx.1, rfl⟩⟩
    ⟨Or.inl ⟨y, hy.1, rfl⟩, Or.inl ⟨y, hy.1, rfl⟩⟩ (hx.2.trans hy.2.symm)

/-- §9.4, step 7, the parenthetical *"(: `X` bihomogeneous :)"*, second half: **`X₂` is now
homogeneous**, because `D_j` is a single vertex-color class of the configuration of
step 3. -/
theorem step7Config_hom₂ {B B' : Set ↥X.car} (hB : B ∈ step7Blocks X)
    (hB' : B' ∈ step7Blocks X) :
    wlRaw X.obj.1.1 B B = wlRaw X.obj.1.1 B' B' :=
  wlRaw_eq_of_step7BlkColor_eq X hB.1 hB'.1 (hB.2.trans hB'.2.symm)

/-- §9.4, step 7.  **When `X₂` is already homogeneous the step is the identity**: all the
blocks then carry one vertex color, so the chosen class `D_j` is all of `V₂`.  This is why
the step may be taken unconditionally; see the module docstring. -/
theorem step7Blocks_eq_of_homogeneous (h : ¬ AllClassesSmall X)
    (hhom : ∀ B ∈ X.obj.1.1.blocks, ∀ B' ∈ X.obj.1.1.blocks,
      wlRaw X.obj.1.1 B B = wlRaw X.obj.1.1 B' B') :
    step7Blocks X = X.obj.1.1.blocks := by
  classical
  obtain ⟨B₀, hB₀, hB₀c⟩ := step7Blocks_nonempty X h
  refine Set.Subset.antisymm (step7Blocks_subset X) ?_
  intro A hA
  refine ⟨hA, ?_⟩
  have hv : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks A := Or.inr hA
  have hv₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B₀ := Or.inr hB₀
  have hAB : step7BlkColor X A = step7BlkColor X B₀ := by
    exact (VColBipBlk.wlCaseColor_eq_iff_raw X.obj.1.1
      ⟨hv, hv⟩ ⟨hv₀, hv₀⟩).2 (hhom A hA B₀ hB₀)
  rw [hAB, hB₀c]

/-- §9.4, step 7.  The vertex set is unchanged when `X₂` is already homogeneous. -/
theorem step7Vtx_eq_of_homogeneous (h : ¬ AllClassesSmall X)
    (hhom : ∀ B ∈ X.obj.1.1.blocks, ∀ B' ∈ X.obj.1.1.blocks,
      wlRaw X.obj.1.1 B B = wlRaw X.obj.1.1 B' B') :
    step7Vtx X = step5Vtx X := by
  rw [step7Vtx, step5Vtx, step7Blocks_eq_of_homogeneous X h hhom]


/-! ### The object `X[V₁ ∪ D_j]` and the invariants of §9.5 -/

/-- §9.4, step 7.  The points that lie in a block of `D_j`. -/
def step7Support (X : Pt (BipBlockInputs Ω)) : Set ↥X.car := ⋃₀ step7Blocks X

/-- §9.4, step 7.  **The new point set `W₁ ∪ D_j`.** -/
noncomputable def step7Set (X : Pt (BipBlockInputs Ω)) : Set Ω :=
  Subtype.val '' (dominantClass X ∪ step7Support X)

theorem step7Set_subset : step7Set X ⊆ X.car := by
  rintro z ⟨w, -, rfl⟩; exact w.2

/-- §9.4, step 7.  *"Set `X ← X[V₁ ∪ D_j]`"*, as an object of the category: the induced
substructure on `W₁ ∪ D_j`. -/
noncomputable def step7Obj (X : Pt (BipBlockInputs Ω)) : VColBipBlk ↥(step7Set X) ℕ :=
  X.obj.1.1.restrictTo (step7Set_subset X)

/-- §9.4, step 7.  *"`V₂ ← D_j`"* and `V₁` unchanged: a point of `W₁ ∪ D_j` that lies in
the old first part cannot lie in a block, so it lies in `W₁`. -/
theorem step7Obj_part₁_iff (x : ↥(step7Set X)) :
    (step7Obj X).part₁ x ↔ VColBipBlk.incl (step7Set_subset X) x ∈ dominantClass X := by
  constructor
  · intro hx
    obtain ⟨w, hw, hwx⟩ := x.2
    have hwu : w = VColBipBlk.incl (step7Set_subset X) x := Subtype.ext hwx
    subst hwu
    rcases hw with hw | ⟨B, hB, hmem⟩
    · exact hw
    · exact absurd hx (X.obj.1.1.blocks_off₁ B hB.1 _ hmem)
  · intro hx; exact hx.1

theorem step7Obj_V₁_image :
    VColBipBlk.incl (step7Set_subset X) '' (step7Obj X).V₁ = dominantClass X := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (step7Obj_part₁_iff X x).1 hx
  · intro hu
    refine ⟨⟨(u : Ω), ⟨u, Or.inl hu, rfl⟩⟩, ?_, rfl⟩
    exact (step7Obj_part₁_iff X _).2 hu

/-- §9.4, step 7.  **`n₁` does not change**: the first part is still `W₁`. -/
theorem step7Obj_V₁_ncard : (step7Obj X).V₁.ncard = (dominantClass X).ncard := by
  rw [← step7Obj_V₁_image X,
    Set.ncard_image_of_injective _ (VColBipBlk.incl_injective (step7Set_subset X))]

/-- §9.4, step 7.  **The blocks that survive are exactly those of `D_j`.**  A block of the
restriction is a block of `X` all of whose points lie in `W₁ ∪ D_j`; its points lie in no
block of `D_j` other than itself (the blocks are pairwise disjoint) and in no point of `W₁`
(a block is disjoint from the first part), so it is a block of `D_j`. -/
theorem step7Obj_blocks_image :
    (fun B : Set ↥(step7Set X) => VColBipBlk.incl (step7Set_subset X) '' B) ''
        (step7Obj X).blocks = step7Blocks X := by
  ext B
  constructor
  · rintro ⟨B', hB', rfl⟩
    set ι := VColBipBlk.incl (step7Set_subset X) with hι
    have hmem : ι '' B' ∈ X.obj.1.1.blocks := hB'
    obtain ⟨y, hy⟩ := X.obj.1.1.blocks_nonempty _ hmem
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨w, hw, hwy⟩ := y₀.2
    have hwu : w = ι y₀ := Subtype.ext hwy
    subst hwu
    rcases hw with hw | ⟨C, hC, hmemC⟩
    · exact absurd hw.1 (X.obj.1.1.blocks_off₁ _ hmem _ (Set.mem_image_of_mem _ hy₀))
    · have hne : ¬ Disjoint (ι '' B') C :=
        fun hd => (Set.disjoint_left.1 hd) (Set.mem_image_of_mem _ hy₀) hmemC
      have : ι '' B' = C := by
        by_contra hc
        exact hne (X.obj.1.1.blocks_disjoint _ hmem _ hC.1 hc)
      show ι '' B' ∈ step7Blocks X
      rw [this]; exact hC
  · intro hB
    set ι := VColBipBlk.incl (step7Set_subset X) with hι
    have hsub : B ⊆ ι '' (ι ⁻¹' B) := by
      intro y hy
      exact ⟨⟨(y : Ω), ⟨y, Or.inr ⟨B, hB, hy⟩, rfl⟩⟩, hy, rfl⟩
    have himg : ι '' (ι ⁻¹' B) = B :=
      le_antisymm (Set.image_preimage_subset _ _) hsub
    exact ⟨ι ⁻¹' B, by
      show ι '' (ι ⁻¹' B) ∈ X.obj.1.1.blocks
      rw [himg]; exact hB.1, himg⟩

/-- §9.4, step 7.  `n₂` becomes `|D_j|`. -/
theorem step7Obj_numBlocks : (step7Obj X).numBlocks = (step7Blocks X).ncard := by
  rw [VColBipBlk.numBlocks, ← step7Obj_blocks_image X,
    Set.ncard_image_of_injective _ (VColBipBlk.incl_image_injective (step7Set_subset X))]

/-- §9.5.  **`n₂` does not increase.** -/
theorem step7Obj_numBlocks_le : (step7Obj X).numBlocks ≤ X.obj.1.1.numBlocks := by
  rw [step7Obj_numBlocks]
  exact Set.ncard_le_ncard (step7Blocks_subset X) (Set.toFinite _)

/-- §9.4, step 7.  **The hypothesis `|V₂| < α|V₁|` of Theorem 9.2.2 survives the step**, for
the threshold `α_new` of step 5: `n₂` does not increase and `V₁` does not change, and
`α_new |W₁| = α n₁ > n₂` (`Babai.alphaNew_mul_dominantClass`). -/
theorem step7Obj_numBlocks_lt (h : ¬ AllClassesSmall X) :
    ((step7Obj X).numBlocks : ℝ) < alphaNew X * ((step7Obj X).V₁.ncard : ℝ) := by
  have h1 : ((step7Obj X).numBlocks : ℝ) ≤ (X.obj.1.1.numBlocks : ℝ) := by
    exact_mod_cast step7Obj_numBlocks_le X
  have h2 : (X.obj.1.1.numBlocks : ℝ)
      < BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := X.obj.2.2.2.2.1
  rw [step7Obj_V₁_ncard, alphaNew_mul_dominantClass h]
  linarith

/-- §9.4, step 7.  The point set is unchanged when `X₂` is already homogeneous, so the
object `X[V₁ ∪ D_j]` is the object `X[W₁ ∪ V₂]` of step 5. -/
theorem step7Set_eq_of_homogeneous (h : ¬ AllClassesSmall X)
    (hhom : ∀ B ∈ X.obj.1.1.blocks, ∀ B' ∈ X.obj.1.1.blocks,
      wlRaw X.obj.1.1 B B = wlRaw X.obj.1.1 B' B') :
    step7Set X = step5Set X := by
  rw [step7Set, step5Set, step7Support, step7Blocks_eq_of_homogeneous X h hhom]
  rfl


end Step7

/-! ### §9.4, step 7: everything is a function of the object -/

section Canonical

open VColBipBlk

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 7.  **The vertex color of a block is canonical** (`wlCaseColor` is, by the
canonicity of step 3). -/
theorem step7BlkColor_map (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (B : Set ↥X.car) :
    step7BlkColor Y (φ '' B) = step7BlkColor X B :=
  VColBipBlk.wlCaseColor_map hφ.2 B B

/-- A morphism of the inputs carries the blocks onto the blocks. -/
theorem blocks_image_iso (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    (Y.obj.1.1).blocks = (fun A : Set ↥X.car => φ '' A) '' (X.obj.1.1).blocks := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  ext B
  constructor
  · intro hB
    refine ⟨φ.symm '' B, ?_, Equiv.image_symm_image φ B⟩
    rw [← hg.blocks (φ.symm '' B), Equiv.image_symm_image]
    exact hB
  · rintro ⟨B', hB', rfl⟩
    exact (hg.blocks B').2 hB'

/-- §9.4, step 7.  **The triviality of the link `X[V₁, D_k]` is an isomorphism
invariant.** -/
theorem linkTrivialOn_map (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) {k : ℕ}
    (hX : LinkTrivialOn X k) : LinkTrivialOn Y k := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  intro x hx y hy B hB B' hB' hBc hB'c
  obtain ⟨x₀, hx₀, rfl⟩ : x ∈ φ '' dominantClass X := by
    rw [← dominantClass_image hφ]; exact hx
  obtain ⟨y₀, hy₀, rfl⟩ : y ∈ φ '' dominantClass X := by
    rw [← dominantClass_image hφ]; exact hy
  obtain ⟨B₀, hB₀, rfl⟩ : B ∈ (fun A : Set ↥X.car => φ '' A) '' (X.obj.1.1).blocks := by
    rw [← blocks_image_iso hφ]; exact hB
  obtain ⟨B₀', hB₀', rfl⟩ : B' ∈ (fun A : Set ↥X.car => φ '' A) '' (X.obj.1.1).blocks := by
    rw [← blocks_image_iso hφ]; exact hB'
  have e₁ : wlRaw Y.obj.1.1 ({φ x₀} : Set ↥Y.car) (φ '' B₀)
      = wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀ := by
    rw [← Set.image_singleton (f := φ), wlRaw_map hg]
  have e₂ : wlRaw Y.obj.1.1 ({φ y₀} : Set ↥Y.car) (φ '' B₀')
      = wlRaw X.obj.1.1 ({y₀} : Set ↥X.car) B₀' := by
    rw [← Set.image_singleton (f := φ), wlRaw_map hg]
  rw [e₁, e₂]
  exact hX x₀ hx₀ y₀ hy₀ B₀ hB₀ B₀' hB₀'
    ((step7BlkColor_map hφ B₀).symm.trans hBc) ((step7BlkColor_map hφ B₀').symm.trans hB'c)

/-- §9.4, step 7.  **The set of colors the step may choose is an isomorphism
invariant.** -/
theorem step7Colors_eq (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step7Colors X = step7Colors Y := by
  have hsymm : φ.symm ∈ (BipBlockInputs Ω).IsoP Y X := (BipBlockInputs Ω).symm_mem hφ
  have hclass : ∀ k : ℕ, (∃ B ∈ (X.obj.1.1).blocks, step7BlkColor X B = k)
      ↔ (∃ B ∈ (Y.obj.1.1).blocks, step7BlkColor Y B = k) := by
    intro k
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨φ '' B, (blocks_image_iso hφ) ▸ ⟨B, hB, rfl⟩, step7BlkColor_map hφ B⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨φ.symm '' B, (blocks_image_iso hsymm) ▸ ⟨B, hB, rfl⟩, step7BlkColor_map hsymm B⟩
  ext k
  simp only [step7Colors, Set.mem_setOf_eq, hclass k]
  exact and_congr Iff.rfl (not_congr ⟨linkTrivialOn_map hφ, linkTrivialOn_map hsymm⟩)

/-- §9.4, step 7.  **The chosen color `j` is an isomorphism invariant**, which is what makes
the restriction of step 7 a functor. -/
theorem step7Color_congr (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) :
    step7Color X = step7Color Y := by
  obtain ⟨φ, hφ⟩ := h
  rw [step7Color, step7Color, step7Colors_eq hφ]

/-- §9.4, step 7.  **The class `D_j` is canonical**: a morphism of the inputs carries it
onto the class `D_j` of the other input. -/
theorem step7Blocks_image (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step7Blocks Y = (fun A : Set ↥X.car => φ '' A) '' step7Blocks X := by
  have hcol : step7Color X = step7Color Y := step7Color_congr ⟨φ, hφ⟩
  ext B
  constructor
  · rintro ⟨hB, hBc⟩
    obtain ⟨B₀, hB₀, rfl⟩ : B ∈ (fun A : Set ↥X.car => φ '' A) '' (X.obj.1.1).blocks := by
      rw [← blocks_image_iso hφ]; exact hB
    exact ⟨B₀, ⟨hB₀, by rw [hcol, ← step7BlkColor_map hφ B₀]; exact hBc⟩, rfl⟩
  · rintro ⟨B₀, ⟨hB₀, hB₀c⟩, rfl⟩
    refine ⟨(blocks_image_iso hφ) ▸ ⟨B₀, hB₀, rfl⟩, ?_⟩
    rw [step7BlkColor_map hφ B₀, hB₀c, hcol]

/-- §9.4, step 7.  **The vertex set of `X[V₁ ∪ D_j]` is canonical.** -/
theorem step7Vtx_image (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step7Vtx Y = (fun A : Set ↥X.car => φ '' A) '' step7Vtx X := by
  have hpts : step5Pts Y = (fun A : Set ↥X.car => φ '' A) '' step5Pts X := by
    ext A
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [dominantClass_image hφ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨{x}, ⟨x, hx, rfl⟩, Set.image_singleton⟩
    · rintro ⟨A', ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨φ x, ?_, Set.image_singleton⟩
      rw [dominantClass_image hφ]
      exact ⟨x, hx, rfl⟩
  rw [step7Vtx, step7Vtx, hpts, step7Blocks_image hφ, Set.image_union]

end Canonical

end Babai
