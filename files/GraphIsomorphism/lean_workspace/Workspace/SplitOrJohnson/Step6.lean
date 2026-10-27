/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, steps 5 and 6: the coherent configuration `X[W₁ ∪ V₂]` that step 5 leaves,
the branch of step 6 on the imprimitivity of `X₁`, and the Claim of step 6.
-/
import Workspace.SplitOrJohnson.WLConfig
import Workspace.SplitOrJohnson.BipSplit
import Workspace.SplitOrJohnson.BlockSystem
import Workspace.SplitOrJohnson.Procedure

/-!
# §9.4, steps 5 and 6

Version 2.5, lines 4136-4146 of `babai-gi-source/quasi25.txt`.

*"5. Let `W₁ ⊆ V₁` be the dominant color class … `X ← X[W₁ ∪ V₂]`; this automatically
updates `X₁`, `X₂`, `X₁₂` (: `X₁` is homogeneous :).  6. If `X₁` is imprimitive, return the
connected components of the first disconnected off-diagonal color, exit (objective (a)
achieved) (: `X₁` is primitive :).  Claim.  `X₁` is uniprimitive."*

## The configuration of step 5 is a **restriction**, not a new refinement

Step 5 writes `X ← X[W₁ ∪ V₂]`: it restricts the coherent configuration `X` produced by
step 3 to the union of vertex-color classes `W₁ ∪ V₂`.  It does **not** re-run WL
refinement on the restricted bipartite graph.  The difference matters: the parenthetical
*"(: `X₁` is homogeneous :)"* of step 5 holds because `W₁` is a **single vertex-color class
of the configuration of step 3**, which survives restriction by Observation 3.3.2, while a
refinement started afresh from the restricted graph could in principle split `W₁`.

So everything in this file stays on the **old ambient point set** `↥□X`: the vertices of
the restricted configuration are the singletons of the points of `W₁` together with the
blocks, all of them subsets of `↥□X`, and the coloring is `Babai.VColBipBlk.wlRaw` of the
input read on those vertices, named in the order of the integer WL colors.  Nothing has to be
transported along the inclusion `↥(W₁ ∪ V₂) → ↥□X`; the point set only shrinks when the
object is handed to one of the three cases of step 9.

| Paper | Lean |
|---|---|
| §9.4, step 5, the vertex set of `X[W₁ ∪ V₂]` | `Babai.step5Vtx` |
| §9.4, step 5, *"`X ← X[W₁ ∪ V₂]`"* | `Babai.step5Config` |
| §9.4, step 5, *"(: `X₁` is homogeneous :)"* | `Babai.step6Config_isHomogeneous` |
| §9.4, step 6, *"`X₁` is imprimitive"* | `Babai.Step6Imprimitive` |
| §9.4, step 6, the branch condition is canonical | `Babai.step6Imprimitive_congr` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### Transport of a coherent coloring along a bijection of vertex sets -/

namespace WL

variable {V V' K : Type*} [Finite V] [Finite V']

/-- A coherent coloring stays coherent when the vertex set is renamed by a bijection. -/
theorem isCoherentColoring_congr {d : V → V → K} {d' : V' → V' → K} (e : V ≃ V')
    (he : ∀ u v : V, d' (e u) (e v) = d u v) (h : IsCoherentColoring d) :
    IsCoherentColoring d' := by
  obtain ⟨⟨hdiag, hconv⟩, p, hp⟩ := h
  have he' : ∀ u v : V', d' u v = d (e.symm u) (e.symm v) := by
    intro u v; simpa using he (e.symm u) (e.symm v)
  refine ⟨⟨fun x y z hxy => ?_, fun x y u v hxy => ?_⟩, p, ?_⟩
  · rw [he' x y, he' z z] at hxy
    have := hdiag (e.symm x) (e.symm y) (e.symm z) hxy
    exact e.symm.injective this
  · rw [he' x y, he' u v] at hxy
    rw [he' y x, he' v u]
    exact hconv _ _ _ _ hxy
  · intro i j k x y hxy
    rw [he' x y] at hxy
    have key : ∀ w : V, (d' x (e w) = i ∧ d' (e w) y = j)
        ↔ (d (e.symm x) w = i ∧ d w (e.symm y) = j) := by
      intro w
      have h1 : d' x (e w) = d (e.symm x) w := by
        conv_lhs => rw [← e.apply_symm_apply x]
        exact he _ _
      have h2 : d' (e w) y = d w (e.symm y) := by
        conv_lhs => rw [← e.apply_symm_apply y]
        exact he _ _
      rw [h1, h2]
    have himg : {z : V' | d' x z = i ∧ d' z y = j}
        = e '' {z : V | d (e.symm x) z = i ∧ d z (e.symm y) = j} := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, (key (e.symm z)).1 (by simpa using hz), by simp⟩
      · rintro ⟨w, hw, rfl⟩
        exact (key w).2 hw
    rw [himg, Set.ncard_image_of_injective _ e.injective]
    exact hp i j k (e.symm x) (e.symm y) hxy

end WL


/-! ### §9.4, step 5: the restricted configuration `X[W₁ ∪ V₂]` -/

section Step5

open VColBipBlk

variable (X : Pt (BipBlockInputs Ω))

/-- Two vertices with the same diagonal color in the refinement have the same `ℕ`-named
diagonal color.  (The `ℕ`-naming is a function of the color.) -/
private theorem wlColor_diag_eq_of_wlRaw_diag_eq {s : Set Ω} (G : VColBipBlk ↥s ℕ)
    {A B : Set ↥s} (hA : IsVertexOn G.part₁ G.blocks A)
    (hB : IsVertexOn G.part₁ G.blocks B) (h : wlRaw G B B = wlRaw G A A) :
    wlColor G B B = wlColor G A A := by
  exact wlColor_eq_of_raw G ⟨hB, hB⟩ ⟨hA, hA⟩ h

/-- §9.4, step 5.  The **vertices of `W₁`**: the singletons of the points of the dominant
color class, read as subsets of `□X`.  This is the first part of `X[W₁ ∪ V₂]`. -/
noncomputable def step5Pts : Set (Set ↥X.car) :=
  {A | ∃ x, x ∈ dominantClass X ∧ A = {x}}

/-- §9.4, step 5.  The **vertex set of `X[W₁ ∪ V₂]`**: the singletons of the points of
`W₁` together with the blocks, which are the vertices of `V₂`. -/
noncomputable def step5Vtx : Set (Set ↥X.car) := step5Pts X ∪ X.obj.1.1.blocks

theorem step5Pts_subset_vtx : step5Pts X ⊆ (X.obj.1.1).vtx := by
  rintro A ⟨x, hx, rfl⟩
  exact (X.obj.1.1).singleton_mem_vtx hx.1

theorem step5Vtx_subset_vtx : step5Vtx X ⊆ (X.obj.1.1).vtx := by
  rintro A (hA | hA)
  · exact step5Pts_subset_vtx X hA
  · exact (X.obj.1.1).block_mem_vtx hA

/-- The vertices of `W₁` are closed under equality of the diagonal color: a vertex with the
diagonal color of a point of `W₁` is a point of `V₁` (the vertex colors discriminate
between `V₁` and `V₂`) whose vertex color is the dominant one, that is a point of `W₁`. -/
theorem step5Pts_isStableSet :
    WL.IsStableSet (wlRaw X.obj.1.1) (step5Pts X) := by
  refine isStableSet_of_subset_vtx (step5Pts_subset_vtx X) ?_
  rintro A ⟨x, hx, rfl⟩ B hB hcol
  have hvx : IsVertexOn (X.obj.1.1).part₁ (X.obj.1.1).blocks ({x} : Set ↥X.car) :=
    Or.inl ⟨x, hx.1, rfl⟩
  have hc := wlColor_diag_eq_of_wlRaw_diag_eq X.obj.1.1 hvx hB hcol
  rcases hB with ⟨y, hy, rfl⟩ | hB
  · refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    show wlDiag X.obj.1.1 y = dominantColor X
    rw [wlDiag, hc]
    exact hx.2
  · exact absurd hc ((X.obj.1.1).wlColor_ne_of_part₁_blocks hx.1 hB).symm

/-- §9.4, step 5.  **The vertex set of `X[W₁ ∪ V₂]` is stable** (Def. 3.1.5): it is the
union of the vertex-color class `W₁` with the vertex-color classes of the blocks.  This is
the hypothesis of Observation 3.3.2 that makes the restriction of step 5 a coherent
configuration. -/
theorem step5Vtx_isStableSet :
    WL.IsStableSet (wlRaw X.obj.1.1) (step5Vtx X) := by
  refine isStableSet_of_subset_vtx (step5Vtx_subset_vtx X) ?_
  rintro A hA B hB hcol
  rcases hA with hA | hA
  · exact Or.inl (step5Pts_isStableSet X A hA B hcol)
  · -- `A` is a block, so `B` has the diagonal color of a block, so `B` is a block
    rcases hB with ⟨y, hy, rfl⟩ | hB
    · exact absurd (wlColor_diag_eq_of_wlRaw_diag_eq X.obj.1.1 (Or.inr hA)
        (Or.inl ⟨y, hy, rfl⟩) hcol) ((X.obj.1.1).wlColor_ne_of_part₁_blocks hy hA)
    · exact Or.inr hB

/-- §9.4, step 5.  **The coherent configuration `X[W₁ ∪ V₂]`.**  Its vertices are the
points of `W₁`, read as singletons, and the blocks; its coloring is the coloring of step 3
restricted to those vertices, named in the order of the integer WL colors. -/
noncomputable def step5Config : PartitionStructure ↥(step5Vtx X) :=
  VColBipBlk.wlRestrictedConfig X.obj.1.1 (step5Vtx X)

/-- §9.4, step 5.  *"`X ← X[W₁ ∪ V₂]`"* leaves a coherent configuration: Observation
3.3.2. -/
theorem step5Config_isCoherent : (step5Config X).IsCoherent :=
  VColBipBlk.wlRestrictedConfig_coherent X.obj.1.1 (step5Vtx_subset_vtx X) (step5Vtx_isStableSet X)

theorem step5Config_color_eq_iff (u v u' v' : ↥(step5Vtx X)) :
    (step5Config X).natColor u v = (step5Config X).natColor u' v'
      ↔ wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)
        = wlRaw X.obj.1.1 (u' : Set ↥X.car) (v' : Set ↥X.car) :=
  ((step5Config X).natColor_eq_iff u v u' v').trans
    (VColBipBlk.wlRestrictedConfig_eq_iff X.obj.1.1 (step5Vtx_subset_vtx X) u v u' v')

/-! ### §9.4, step 6: the configuration `X₁` -/

/-- §9.4, step 6.  A point of `W₁`, read as a vertex of `X[W₁ ∪ V₂]`. -/
noncomputable def step5Pt (x : ↥(dominantClass X)) : ↥(step5Vtx X) :=
  ⟨{(x : ↥X.car)}, Or.inl ⟨x, x.2, rfl⟩⟩

/-- §9.4, step 6.  The **uncoded** coloring of `X₁`: the refined coloring of step 3 read on
the singletons of the points of `W₁`. -/
noncomputable def step6Raw (u v : ↥(dominantClass X)) : WL.colorType ℕ (wlRounds Ω) :=
  wlRaw X.obj.1.1 {(u : ↥X.car)} {(v : ↥X.car)}

/-- §9.4, step 6.  **The coloring of `X₁`**: the coloring of `X[W₁ ∪ V₂]` read on the
points of `W₁`.  The color labels are the labels `R₁, …, R_r` of `X`, which is what the
paper's *"the first disconnected off-diagonal color"* of step 6 refers to. -/
noncomputable def step6Color (u v : ↥(dominantClass X)) : ℕ :=
  (step5Config X).natColor (step5Pt X u) (step5Pt X v)

theorem step6Color_eq_iff (u v u' v' : ↥(dominantClass X)) :
    step6Color X u v = step6Color X u' v' ↔ step6Raw X u v = step6Raw X u' v' :=
  step5Config_color_eq_iff X _ _ _ _

/-- §9.4, step 6.  `X₁` as a configuration on the points of `W₁`.  It has the same color
classes as `Babai.step6Color`, but names them by its own rank; the naming that steps 6 to 8
read is `Babai.step6Color`. -/
noncomputable def step6Config : PartitionStructure ↥(dominantClass X) :=
  PartitionStructure.ofNamedColoring (step6Color X)

theorem step6Config_natColor_eq_iff (u v u' v' : ↥(dominantClass X)) :
    (step6Config X).natColor u v = (step6Config X).natColor u' v'
      ↔ step6Raw X u v = step6Raw X u' v' :=
  ((step6Config X).natColor_eq_iff u v u' v').trans
    ((PartitionStructure.ofNamedColoring_color_eq_iff _ u v u' v').trans
      (step6Color_eq_iff X u v u' v'))

theorem step6Config_color_eq_iff (u v u' v' : ↥(dominantClass X)) :
    (step6Config X).color u v = (step6Config X).color u' v' ↔
      step6Raw X u v = step6Raw X u' v' :=
  ((step6Config X).natColor_eq_iff u v u' v').symm.trans
    (step6Config_natColor_eq_iff X u v u' v')

/-- The coloring of `X₁` and the configuration `X₁` have the same color classes. -/
theorem sameKernel_step6Color : SameKernel (step6Color X) (step6Config X).natColor :=
  fun a b a' b' =>
    (step6Color_eq_iff X a b a' b').trans (step6Config_natColor_eq_iff X a b a' b').symm

/-- The vertices of `W₁`, in bijection with the points of `W₁`. -/
noncomputable def step6Equiv : ↥(dominantClass X) ≃ ↥(step5Pts X) :=
  Equiv.ofBijective (fun x => ⟨{(x : ↥X.car)}, ⟨x, x.2, rfl⟩⟩) (by
    constructor
    · intro x y hxy
      have h : ({(x : ↥X.car)} : Set ↥X.car) = {(y : ↥X.car)} := congrArg Subtype.val hxy
      exact Subtype.ext (Set.singleton_eq_singleton_iff.1 h)
    · rintro ⟨A, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)

@[simp] theorem step6Equiv_val (x : ↥(dominantClass X)) :
    ((step6Equiv X x : ↥(step5Pts X)) : Set ↥X.car) = {(x : ↥X.car)} := rfl

/-- §9.4, step 6.  **`X₁` is a coherent configuration**: it is the restriction of the
configuration of step 3 to the vertex-color class `W₁` (Obs. 3.3.2). -/
theorem step6Config_isCoherent : (step6Config X).IsCoherent := by
  apply PartitionStructure.named_isCoherent_of_kernel (c := step6Raw X)
  swap
  · intro a b x y
    exact ((step6Config X).natColor_eq_iff a b x y).symm.trans
      (step6Config_natColor_eq_iff X a b x y) |>.symm
  refine WL.isCoherentColoring_congr (step6Equiv X).symm (fun u v => ?_)
    (WL.isCoherentColoring_restrict (isCoherentColoring_wlRaw X.obj.1.1)
      (step5Pts_isStableSet X))
  show wlRaw X.obj.1.1 {((step6Equiv X).symm u : ↥X.car)} {((step6Equiv X).symm v : ↥X.car)}
    = wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)
  rw [show ({((step6Equiv X).symm u : ↥X.car)} : Set ↥X.car) = (u : Set ↥X.car) from
      congrArg Subtype.val ((step6Equiv X).apply_symm_apply u),
    show ({((step6Equiv X).symm v : ↥X.car)} : Set ↥X.car) = (v : Set ↥X.car) from
      congrArg Subtype.val ((step6Equiv X).apply_symm_apply v)]

/-- §9.4, step 5, the parenthetical *"(: `X₁` is homogeneous :)"*.  `W₁` is a **single
vertex-color class** of the configuration of step 3, and restriction to a union of
vertex-color classes does not change the colors, so all the points of `W₁` still carry one
and the same vertex color. -/
theorem step6Config_isHomogeneous : (step6Config X).IsHomogeneous := by
  intro x y
  apply ((step6Config X).natColor_eq_iff x x y y).1
  apply (step6Config_natColor_eq_iff X x x y y).2
  have hx : wlDiag X.obj.1.1 (x : ↥X.car) = dominantColor X := x.2.2
  have hy : wlDiag X.obj.1.1 (y : ↥X.car) = dominantColor X := y.2.2
  exact wlRaw_eq_of_wlColor_eq X.obj.1.1
    ⟨Or.inl ⟨_, x.2.1, rfl⟩, Or.inl ⟨_, x.2.1, rfl⟩⟩
    ⟨Or.inl ⟨_, y.2.1, rfl⟩, Or.inl ⟨_, y.2.1, rfl⟩⟩ (hx.trans hy.symm)

/-- §9.4, step 5, the parenthetical *"(: `X₁` is homogeneous :)"* read in `X[W₁ ∪ V₂]`:
**`W₁` is one vertex-color class of the restricted configuration.**  This is the hypothesis
`hV₁` that the Large clique lemma needs in the Claim of step 6, and it is what makes `X₁`
the induced subconfiguration on a vertex-color class (Obs. 3.3.2).

The two halves are: every point of `W₁` carries the vertex color of a fixed one, which is
`Babai.step6Config_isHomogeneous`; and a block never carries the vertex color of a point,
which is *"the vertex-colors discriminate between `V₁` and `V₂`"*
(`Babai.VColBipBlk.wlColor_ne_of_part₁_blocks`). -/
theorem step5Pts_eq_vertexClass {x₀ : ↥X.car} (hx₀ : x₀ ∈ dominantClass X) :
    {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass
        ((step5Config X).vcolor ⟨{x₀}, Or.inl ⟨x₀, hx₀, rfl⟩⟩) := by
  classical
  set u₀ : ↥(step5Vtx X) := ⟨{x₀}, Or.inl ⟨x₀, hx₀, rfl⟩⟩ with hu₀
  have hiff : ∀ u : ↥(step5Vtx X),
      (step5Config X).vcolor u = (step5Config X).vcolor u₀
        ↔ wlRaw X.obj.1.1 (u : Set ↥X.car) (u : Set ↥X.car)
          = wlRaw X.obj.1.1 (u₀ : Set ↥X.car) (u₀ : Set ↥X.car) := by
    intro u
    exact (Fin.val_eq_val _ _).symm.trans (step5Config_color_eq_iff X u u u₀ u₀)
  ext u
  simp only [Set.mem_setOf_eq, PartitionStructure.vertexClass]
  constructor
  · rintro ⟨y, hy, huy⟩
    refine (hiff u).2 ?_
    rw [huy]
    exact wlRaw_eq_of_wlColor_eq X.obj.1.1
      ⟨Or.inl ⟨y, hy.1, rfl⟩, Or.inl ⟨y, hy.1, rfl⟩⟩
      ⟨Or.inl ⟨x₀, hx₀.1, rfl⟩, Or.inl ⟨x₀, hx₀.1, rfl⟩⟩ (hy.2.trans hx₀.2.symm)
  · intro hvc
    rcases u.2 with h | h
    · exact h
    · -- a block cannot carry the vertex color of a point of `W₁`
      exact absurd (wlColor_diag_eq_of_wlRaw_diag_eq X.obj.1.1
          (Or.inl ⟨x₀, hx₀.1, rfl⟩) (Or.inr h) ((hiff u).1 hvc))
        ((X.obj.1.1).wlColor_ne_of_part₁_blocks hx₀.1 h).symm

end Step5

/-! ### §9.4, step 6: the branch condition *"`X₁` is imprimitive"* -/

section Step6

variable {V : Type*} [Finite V]

/-- A configuration with a disconnected off-diagonal color is not primitive
(Def. 3.2.1). -/
theorem not_isPrimitive_of_isDisconnectedColor {P : PartitionStructure V}
    (h : ∃ k, IsDisconnectedColor P.natColor k) : ¬ P.IsPrimitive := by
  rintro ⟨-, hconn⟩
  obtain ⟨hdiag, ⟨u, v, huv⟩, hdisc⟩ := blockColor_spec h
  have hk : blockColor P.natColor < P.rank := blockColor_lt_rank h
  refine hdisc ?_
  rw [colorDigraph_natColor P hk]
  exact hconn ⟨blockColor P.natColor, hk⟩ (blockColor_isOffDiagonalColor h)

/-- Definition 3.2.1, for a homogeneous configuration: *"imprimitive"* is the same as
*"some off-diagonal color is disconnected"*. -/
theorem exists_isDisconnectedColor_iff_not_isPrimitive {P : PartitionStructure V}
    (hhom : P.IsHomogeneous) :
    (∃ k, IsDisconnectedColor P.natColor k) ↔ ¬ P.IsPrimitive :=
  ⟨not_isPrimitive_of_isDisconnectedColor, exists_isDisconnectedColor hhom⟩

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- §9.4, step 6.  **The branch condition**: *"`X₁` is imprimitive"*, read off the coloring
of `X₁` as *"some off-diagonal color of `X₁` is disconnected"*
(`Babai.step6Imprimitive_iff` is Def. 3.2.1 for the configuration `X₁`, which is
homogeneous).

Reading the condition off the coloring rather than off a configuration chosen from an
existential is what makes it a **function of the object**, hence an isomorphism invariant
(`Babai.step6Imprimitive_congr`), which is what `Babai.FindsAtMultCost.cases` asks of a
branch condition. -/
noncomputable def Step6Imprimitive (X : Pt (BipBlockInputs Ω)) : Prop :=
  ∃ k, IsDisconnectedColor (step6Color X) k

/-- §9.4, step 6.  The branch condition is Definition 3.2.1 for `X₁`: *"`X₁` is
imprimitive"*, that is `X₁` is homogeneous but not primitive. -/
theorem step6Imprimitive_iff (X : Pt (BipBlockInputs Ω)) :
    Step6Imprimitive X ↔ ¬ (step6Config X).IsPrimitive :=
  (exists_isDisconnectedColor_congr (sameKernel_step6Color X)).trans
    (exists_isDisconnectedColor_iff_not_isPrimitive (step6Config_isHomogeneous X))

/-! ### §9.4, steps 5 and 6: everything is a function of the object -/

section Canonical

open VColBipBlk

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 5.  A morphism of the inputs carries `W₁` onto `W₁`
(`Babai.dominantClass_image`), so the points of the two dominant classes correspond. -/
noncomputable def domEquiv (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    ↥(dominantClass X) ≃ ↥(dominantClass Y) :=
  Equiv.ofBijective
    (fun x => ⟨φ (x : ↥X.car), by rw [dominantClass_image hφ]; exact ⟨x, x.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (φ.injective (congrArg Subtype.val h)), by
      rintro ⟨y, hy⟩
      rw [dominantClass_image hφ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩⟩

@[simp] theorem domEquiv_val (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y)
    (x : ↥(dominantClass X)) :
    ((domEquiv hφ x : ↥(dominantClass Y)) : ↥Y.car) = φ (x : ↥X.car) := rfl

/-- §9.4, step 5.  **The vertex set of `X[W₁ ∪ V₂]` is canonical**: a morphism of the
inputs carries it onto the vertex set of the restriction of the other input. -/
theorem step5Vtx_image (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step5Vtx Y = (fun A : Set ↥X.car => φ '' A) '' step5Vtx X := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
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
  have hblk : (Y.obj.1.1).blocks = (fun A : Set ↥X.car => φ '' A) '' (X.obj.1.1).blocks := by
    ext B
    constructor
    · intro hB
      refine ⟨φ.symm '' B, ?_, Equiv.image_symm_image φ B⟩
      rw [← hg.blocks (φ.symm '' B), Equiv.image_symm_image]
      exact hB
    · rintro ⟨B', hB', rfl⟩
      exact (hg.blocks B').2 hB'
  rw [step5Vtx, step5Vtx, hpts, hblk, Set.image_union]

/-- §9.4, step 5.  The colors that occur on the restricted vertex set are the same for two
isomorphic inputs, so the ordered integer naming of them agrees. -/
theorem natCodes_step5_congr (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    PartitionStructure.natCodes
        (fun u v : ↥(step5Vtx Y) => wlRaw Y.obj.1.1 (u : Set ↥Y.car) (v : Set ↥Y.car))
      = PartitionStructure.natCodes
        (fun u v : ↥(step5Vtx X) => wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)) := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  have himg := step5Vtx_image hφ
  ext k
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    obtain ⟨A, hA, hAu⟩ : (u : Set ↥Y.car) ∈ (fun A : Set ↥X.car => φ '' A) '' step5Vtx X :=
      himg ▸ u.2
    obtain ⟨B, hB, hBv⟩ : (v : Set ↥Y.car) ∈ (fun A : Set ↥X.car => φ '' A) '' step5Vtx X :=
      himg ▸ v.2
    have hAu' : φ '' A = (u : Set ↥Y.car) := hAu
    have hBv' : φ '' B = (v : Set ↥Y.car) := hBv
    refine ⟨(⟨A, hA⟩, ⟨B, hB⟩), ?_⟩
    show wlRaw X.obj.1.1 A B = wlRaw Y.obj.1.1 (u : Set ↥Y.car) (v : Set ↥Y.car)
    rw [← hAu', ← hBv', wlRaw_map hg]
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(⟨φ '' (u : Set ↥X.car), himg ▸ ⟨_, u.2, rfl⟩⟩,
      ⟨φ '' (v : Set ↥X.car), himg ▸ ⟨_, v.2, rfl⟩⟩), ?_⟩
    show wlRaw Y.obj.1.1 (φ '' (u : Set ↥X.car)) (φ '' (v : Set ↥X.car))
      = wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)
    rw [wlRaw_map hg]

/-- §9.4, step 6.  **The coloring of `X₁` is canonical**: a morphism of the inputs carries
the color of a pair of points of `W₁` to the **same** color label.  This is the canonicity
of step 3 (`Babai.VColBipBlk.wlRaw_map`, Eq. (26)) together with the canonicity of the
ordered integer naming. -/
theorem step6Color_map (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) (u v : ↥(dominantClass X)) :
    step6Color Y (domEquiv hφ u) (domEquiv hφ v) = step6Color X u v := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  let e : ↥(step5Vtx X) ≃ ↥(step5Vtx Y) := (imgEquiv φ).subtypeEquiv (fun A => by
    change A ∈ step5Vtx X ↔ φ '' A ∈ step5Vtx Y
    rw [step5Vtx_image hφ]
    constructor
    · intro ha; exact ⟨A, ha, rfl⟩
    · rintro ⟨B, hB, he⟩
      exact (imgEquiv φ).injective he ▸ hB)
  have he := PartitionStructure.natColor_ofNamedColoring_map e
    (c := fun a b : ↥(step5Vtx X) => wlCaseColor X.obj.1.1 a.val b.val)
    (d := fun a b : ↥(step5Vtx Y) => wlCaseColor Y.obj.1.1 a.val b.val)
    (fun a b => wlCaseColor_map hg a.val b.val) (step5Pt X u) (step5Pt X v)
  have hu : e (step5Pt X u) = step5Pt Y (domEquiv hφ u) :=
    Subtype.ext (by exact Set.image_singleton)
  have hv : e (step5Pt X v) = step5Pt Y (domEquiv hφ v) :=
    Subtype.ext (by exact Set.image_singleton)
  rw [hu, hv] at he
  exact he

/-- §9.4, step 6.  **The branch condition is an isomorphism invariant**, which is what
`Babai.FindsAtMultCost.cases` asks of it. -/
theorem step6Imprimitive_congr (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty)
    (hX : Step6Imprimitive X) : Step6Imprimitive Y := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨k, hk⟩ := hX
  exact ⟨k, (isDisconnectedColor_map (domEquiv hφ) (step6Color_map hφ) k).2 hk⟩

end Canonical

/-! ### §9.4, step 6: the colored partition into the components `B₁, …, B_m`

*"return the connected components of the first disconnected off-diagonal color, exit
(objective (a) achieved)"*.

The blocks of the returned partition are the components; they are of equal size and there
are at least two of them, so each holds at most half of `W₁` (Prop. 3.4.4), which is
objective (a) for the threshold `α_new ≥ 2/3 ≥ 1/2` that step 5 left.  All the blocks get
the same color: the partition is an *equipartition* of a single color class, and it is
admissible because every component has at least two points (Prop. 3.4.4 again). -/

section CompPartition

variable {s : Set Ω}

/-- The point of `W` underlying a point of the image of `W` inside `Ω`. -/
def wPt {W : Set ↥s} (z : ↥(Subtype.val '' W)) : ↥W := ⟨liftPt z, liftPt_mem z⟩

theorem wPt_injective {W : Set ↥s} : Function.Injective (wPt (W := W)) :=
  fun _ _ h => liftPt_injective (congrArg Subtype.val h)

theorem wPt_mkPt {W : Set ↥s} (u : ↥W) : wPt (mkPt u.2) = u := Subtype.ext rfl

/-- §9.4, step 6.  **The colored partition of `W₁` into the components of the first
disconnected off-diagonal color.**  All the points get the color `0`; the blocks are the
components `Babai.blockOf` of the coloring. -/
def compPartition (W : Set ↥s) (c : ↥W → ↥W → ℕ) :
    ColoredPartition ↥(Subtype.val '' W) ℕ where
  color _ := 0
  part := Setoid.ker fun z => blockOf c (wPt z)
  part_le_color _ := rfl

theorem compPartition_block (W : Set ↥s) (c : ↥W → ↥W → ℕ)
    (z : ↥(Subtype.val '' W)) :
    (compPartition W c).block z = {y | blockOf c (wPt y) = blockOf c (wPt z)} := rfl

/-- A block of the partition is a component, so it has as many points. -/
theorem ncard_block_compPartition (W : Set ↥s) (c : ↥W → ↥W → ℕ)
    (z : ↥(Subtype.val '' W)) :
    ((compPartition W c).block z).ncard = (blockOf c (wPt z)).ncard := by
  have himg : wPt '' ((compPartition W c).block z) = blockOf c (wPt z) := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hself := mem_blockOf_self c (wPt y)
      have hy' : blockOf c (wPt y) = blockOf c (wPt z) := hy
      rwa [hy'] at hself
    · intro hu
      refine ⟨mkPt u.2, ?_, wPt_mkPt u⟩
      show blockOf c (wPt (mkPt u.2)) = blockOf c (wPt z)
      rw [wPt_mkPt u]
      exact (colorDigraph c (blockColor c)).weakComponent_eq_of_mem hu
  rw [← himg, Set.ncard_image_of_injective _ wPt_injective]

/-- §9.4, step 6.  **The components are a colored `α`-partition of `W₁`** for every
`α ≥ 1/2`: they are of equal size and there are at least two of them, so each has at most
half of the points, and each has at least two points, so the partition is admissible
(Def. 7.1.1).  Both facts are Proposition 3.4.4. -/
theorem compPartition_isAlphaPartition (W : Set ↥s) (c : ↥W → ↥W → ℕ)
    (iF : Fintype ↥(Subtype.val '' W)) (hnt : ∀ u : ↥W, (blockOf c u).Nontrivial)
    (heq : IsEquipartition (blocks c))
    (hne : ∃ A ∈ blocks c, ∃ B ∈ blocks c, A ≠ B) {α : ℝ} (hα : 1 / 2 ≤ α) :
    @ColoredPartition.IsAlphaPartition _ _ (compPartition W c) iF α := by
  classical
  obtain ⟨A, hA, B, hB, hAB⟩ := hne
  -- every block has at most half of the points
  have hhalf : ∀ z : ↥(Subtype.val '' W),
      2 * ((compPartition W c).block z).ncard ≤ W.ncard := by
    intro z
    have hmem : blockOf c (wPt z) ∈ blocks c := blockOf_mem_blocks c (wPt z)
    have hsize : (blockOf c (wPt z)).ncard = A.ncard := heq.equal_size _ hmem _ hA
    have h2 : 2 * A.ncard ≤ Nat.card ↥W :=
      two_mul_ncard_le_of_isEquipartition heq hA hB hAB
    rw [ncard_block_compPartition, hsize, Nat.card_coe_set_eq] at *
    exact h2
  refine ⟨?_, ?_⟩
  · -- admissible: every block has at least two points
    intro z _
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt (wPt z)
    rw [ncard_block_compPartition]
    have hsub : ({x, y} : Set ↥W) ⊆ blockOf c (wPt z) := by
      rintro w (rfl | rfl)
      · exact hx
      · exact hy
    calc 2 = ({x, y} : Set ↥W).ncard := (Set.ncard_pair hxy).symm
      _ ≤ (blockOf c (wPt z)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  · have hrho : (compPartition W c).rho ≤ W.ncard / 2 :=
      ColoredPartition.rho_le _ fun z => by have := hhalf z; omega
    have hcard : (@Fintype.card ↥(Subtype.val '' W) iF : ℕ) = W.ncard := card_image_val W iF
    have hrhoR : ((compPartition W c).rho : ℝ) ≤ ((W.ncard / 2 : ℕ) : ℝ) := by
      exact_mod_cast hrho
    have hdiv : 2 * (W.ncard / 2) ≤ W.ncard := by omega
    have hdivR : (2 : ℝ) * ((W.ncard / 2 : ℕ) : ℝ) ≤ (W.ncard : ℝ) := by exact_mod_cast hdiv
    have hW0 : (0 : ℝ) ≤ (W.ncard : ℝ) := by positivity
    rw [hcard]
    nlinarith

/-- The restriction of a bijection of the point sets to `W`, when it carries `W` onto
`W'`. -/
def wEquiv {t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) : ↥W ≃ ↥W' where
  toFun u := ⟨φ (u : ↥s), (h _).2 u.2⟩
  invFun v := ⟨φ.symm (v : ↥t), by
    rw [← h (φ.symm (v : ↥t)), Equiv.apply_symm_apply]; exact v.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)

@[simp] theorem wEquiv_val {t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (u : ↥W) :
    ((wEquiv φ h u : ↥W') : ↥t) = φ (u : ↥s) := rfl

/-- §6.  **Canonicity of the partition into components**: a bijection that carries `W` onto
`W'` and the coloring `c'` back to `c` is a morphism of the two partitions, because it
carries the components onto the components (`Babai.blockOf_map`). -/
theorem compPartition_mem_iso {t : Set Ω} (φ : ↥s ≃ ↥t) {W : Set ↥s} {W' : Set ↥t}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) {c : ↥W → ↥W → ℕ} {c' : ↥W' → ↥W' → ℕ}
    (hc : ∀ u v : ↥W, c' (wEquiv φ h u) (wEquiv φ h v) = c u v) :
    subEquiv φ h ∈
      (ColoredPartitions Ω ℕ).Iso (compPartition W c) (compPartition W' c') := by
  have hwPt : ∀ z : ↥(Subtype.val '' W),
      wPt (subEquiv φ h z) = wEquiv φ h (wPt z) := fun z => Subtype.ext (by simp [wPt])
  refine ⟨fun _ => rfl, fun z w => ?_⟩
  show blockOf c (wPt z) = blockOf c (wPt w)
    ↔ blockOf c' (wPt (subEquiv φ h z)) = blockOf c' (wPt (subEquiv φ h w))
  rw [hwPt z, hwPt w, blockOf_map (wEquiv φ h) hc, blockOf_map (wEquiv φ h) hc]
  exact ⟨fun hzw => by rw [hzw],
    fun hzw => (Set.image_eq_image (wEquiv φ h).injective).1 hzw⟩

end CompPartition

/-! ### §9.4, step 6: the exit -/

section Step6Exit

/-- There are at least two components, for an arbitrary coloring.  This is
`Babai.exists_blockOf_ne` without the hypothesis that the coloring is a `natColor`; the
proof is the same, since only `Babai.blockColor_spec` is used. -/
theorem exists_blockOf_ne' {T : Type*} {c : T → T → ℕ} (h : ∃ k, IsDisconnectedColor c k) :
    ∃ A ∈ blocks c, ∃ B ∈ blocks c, A ≠ B := by
  obtain ⟨-, -, hdisc⟩ := blockColor_spec h
  exact (colorDigraph c (blockColor c)).exists_ne_weakComponents hdisc

variable (X : Pt (BipBlockInputs Ω))

theorem dominantClass_image_subset_V₁ :
    Subtype.val '' dominantClass X ⊆ BipBlockInputs.V₁ X :=
  Set.image_mono (dominantClass_subset X)

/-- §9.4, step 6.  **The components of the first disconnected off-diagonal color of `X₁`,
extended to `V₁` by the block `V₁ \ W₁`, are a colored `α`-partition of `V₁`** — objective
(a) of Theorem 9.2.2 for the threshold `α` the procedure started the turn with.

Three things go into it: Proposition 3.4.4, which makes the components an equipartition of
`W₁` into at least two blocks of at least two points each, so a colored `1/2`-partition of
`W₁` and hence a colored `α_new`-partition since `α_new ≥ 2/3`; and the bookkeeping of
step 5, `α_new|W₁| = α n₁` (`Babai.alphaNew_mul_dominantClass`), which is what turns a
colored `α_new`-partition of `W₁` into a colored `α`-partition of `V₁`
(`Babai.extendPartition.isAlphaPartition`). -/
theorem step6_isAlphaPartition (h : ¬ AllClassesSmall X) (himp : Step6Imprimitive X)
    (iV : Fintype ↥(BipBlockInputs.V₁ X)) :
    @ColoredPartition.IsAlphaPartition _ _
      (extendPartition (BipBlockInputs.V₁ X) (Subtype.val '' dominantClass X)
        (compPartition (dominantClass X) (step6Color X))) iV (BipBlockInputs.alpha X) := by
  classical
  letI iW : Fintype ↥(Subtype.val '' dominantClass X) := Fintype.ofFinite _
  have hα23 : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
  have hnew23 : (2 : ℝ) / 3 ≤ alphaNew X := le_trans hα23 (alpha_le_alphaNew h)
  -- Proposition 3.4.4 for the coloring of `X₁`
  have hnt : ∀ u : ↥(dominantClass X), (blockOf (step6Color X) u).Nontrivial := fun u =>
    blockOf_nontrivial_of_sameKernel (step6Config_isCoherent X)
      (step6Config_isHomogeneous X) (sameKernel_step6Color X) himp u
  have heq : IsEquipartition (blocks (step6Color X)) :=
    isEquipartition_blocks_of_sameKernel (step6Config_isCoherent X)
      (step6Config_isHomogeneous X) (sameKernel_step6Color X) himp
  have hP := compPartition_isAlphaPartition (dominantClass X) (step6Color X) iW hnt heq
    (exists_blockOf_ne' himp) (α := alphaNew X) (by linarith)
  -- the bookkeeping of step 5
  have hncardW : (Subtype.val '' dominantClass X).ncard = (dominantClass X).ncard :=
    ncard_image_val _
  have hncardV : (BipBlockInputs.V₁ X).ncard = BipBlockInputs.n₁ X := ncard_image_val _
  have hαβ : alphaNew X * ((Subtype.val '' dominantClass X).ncard : ℝ)
      = BipBlockInputs.alpha X * ((BipBlockInputs.V₁ X).ncard : ℝ) := by
    rw [hncardW, hncardV]
    exact alphaNew_mul_dominantClass h
  exact extendPartition.isAlphaPartition (dominantClass_image_subset_V₁ X) iW iV _
    (le_of_lt (alphaNew_lt_one h)) (by linarith) hαβ hP

/-- §9.4, step 6.  **The outcome of the exit**: the colored partition of `V₁` whose blocks
are the components `B₁, …, B_m` of the first disconnected off-diagonal color of `X₁`,
together with the one block `V₁ \ W₁` that the bookkeeping of step 5 adds. -/
noncomputable def step6Outcome : (Cat.sub (SplitOutcomes Ω)).Obj X.car :=
  ⟨⟨Subtype.val '' X.obj.1.1.V₁, by rintro z ⟨w, -, rfl⟩; exact w.2⟩,
    Sum.inl (extendPartition (Subtype.val '' X.obj.1.1.V₁)
      (Subtype.val '' dominantClass X) (compPartition (dominantClass X) (step6Color X)))⟩

variable {X}

/-- §6.  Condition (ii) of Definition 6.0.1 for the outcome of step 6: a morphism of the
inputs carries the components onto the components (`Babai.step6Color_map`) and `W₁` onto
`W₁` (`Babai.dominantClass_image`), hence the colored partition onto the colored
partition. -/
theorem step6Outcome_mem_subIso {Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    φ ∈ (Cat.sub (SplitOutcomes Ω)).Iso (step6Outcome X) (step6Outcome Y) := by
  have hg : (X.obj.1.1).IsIsoTo Y.obj.1.1 φ := hφ.2
  have hV : ∀ x, φ x ∈ Y.obj.1.1.V₁ ↔ x ∈ X.obj.1.1.V₁ := fun x => hg.part₁ x
  have hW : ∀ x, φ x ∈ dominantClass Y ↔ x ∈ dominantClass X := by
    intro x
    rw [dominantClass_image hφ]
    exact ⟨fun ⟨y, hy, hyx⟩ => (φ.injective hyx) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨subEquiv φ hV, fun _ => rfl, ?_⟩
  exact extendPartition.mem_iso (dominantClass_image_subset_V₁ X)
    (dominantClass_image_subset_V₁ Y) (subEquiv φ hV) (subEquiv φ hW) (fun _ => rfl)
    (compPartition_mem_iso φ hW (fun u v => step6Color_map hφ u v))

variable (Ω)

/-- §9.4, step 6.  *"If `X₁` is imprimitive, return the connected components of the first
disconnected off-diagonal color, exit (objective (a) achieved)."*
(Version 2.5, lines 4140-4141.)

There is one outcome, so the multiplicative cost is `1`; it is canonical by
`Babai.step6Outcome_mem_subIso`, and it achieves objective (a) for the threshold `α` and
the set `V₁` the turn started with, by `Babai.step6_isAlphaPartition`. -/
theorem step_9_4_6 (C₀ N : ℕ) :
    FindsAtMultCost
      (((((BipBlockInputsAt Ω N).full fun s Y => ¬ IsSmallPart₁ C₀ ⟨s, Y.1⟩).full
        fun s Y => ¬ IsSmallPart₂ C₀ ⟨s, Y.1.1⟩).full
        fun s Y => ¬ AllClassesSmall ⟨s, Y.1.1.1⟩).full
        fun s Y => Step6Imprimitive ⟨s, Y.1.1.1.1⟩)
      (SplitOutcomes Ω)
      (fun X => cost_9_4 C₀ ⟨X.car, X.obj.1.1.1.1.1⟩)
      (fun X Z => Good_9_2_2 ⟨X.car, X.obj.1.1.1.1.1⟩ Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub
    (fun X => {step6Outcome (⟨X.car, X.obj.1.1.1.1.1⟩ : Pt (BipBlockInputs Ω))})
    (fun X => Set.singleton_nonempty _) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.mul_pos (one_le_constFactor C₀) (Nat.one_le_pow _ _ (one_le_turnCost _))
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hφ : f ∈ (BipBlockInputs Ω).IsoP (⟨X.car, X.obj.1.1.1.1.1⟩ : Pt (BipBlockInputs Ω))
      ⟨Y.car, Y.obj.1.1.1.1.1⟩ := hf
    exact ⟨_, rfl, step6Outcome_mem_subIso hφ⟩
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    exact ⟨rfl, step6_isAlphaPartition _ X.obj.1.2 X.obj.2 _⟩

end Step6Exit

end Step6

end Babai
