/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, the Claim of step 6: on the branch where `X₁` is primitive, `X₁` is a UPCC.
-/
import Workspace.SplitOrJohnson.Step6

/-!
# §9.4, the Claim of step 6: *"`X₁` is uniprimitive"*

Version 2.5, lines 4142-4146 of `babai-gi-source/quasi25.txt`.

> *"Claim.  `X₁` is uniprimitive.  Proof.  Given that `X₁` is primitive, we only need to
> rule out that `X₁` is the clique configuration.  `V₁` is larger than any other
> color-class in `X`.  Therefore, if `X₁` were the clique configuration, it would follow by
> the Large clique lemma (Lemma 3.4.25) that `V₁` is a twin equivalence class in `X`, a
> contradiction with the positive symmetry defect assumption."*

The Claim is `Babai.claim_9_4_step6` (`Workspace/SplitOrJohnson/Procedure.lean`); this file
supplies its three inputs at the configuration `X[W₁ ∪ V₂]` that step 5 leaves
(`Babai.step5Config`), and concludes for `Babai.step6Config`, the configuration `X₁`.

## The three inputs

* *"`V₁` is larger than any other color-class in `X`"* — `Babai.step5_vertexClass_ncard_lt`.
  After step 5 the first part is one vertex-color class (`Babai.step5Pts_eq_vertexClass`),
  so every other vertex-color class consists of blocks; there are `n₂` of those, and
  `n₂ < α n₁ < |W₁|` (`Babai.numBlocks_lt_dominantClass_ncard`).

* *"a contradiction with the positive symmetry defect assumption"* —
  `Babai.not_twinClass_eq_step5Pts`.  Only the **easy half** of the parenthetical of step 3,
  *"`Aut(X) = Aut(X₁₂)`"*, is needed: a permutation of the vertices preserving all colors of
  the WL configuration preserves the graph, because the refined coloring refines the initial
  coloring (`Babai.VColBipBlk.initColor_eq_of_wlRaw_eq`), and the initial coloring records
  the edges, the vertex coloring `f` and the two parts.  So twins of the configuration
  inside `W₁` are twins of the graph `Babai.step5Obj`, and if `W₁` were one twin class the
  symmetry defect of `W₁` in `Babai.step5Obj` would be `0`, contradicting
  `Babai.step5Obj_isThm922Input`, which gives defect `≥ 1 - α_new > 0`.

* the passage from the induced subconfiguration on the vertex-color class of `W₁` to the
  configuration `X₁` on the points of `W₁` — `Babai.PartitionStructure.rank_congr_equiv`,
  the rank being a function of the color classes alone.

| Paper | Lean |
|---|---|
| §9.4, step 6, *"`V₁` is larger than any other color-class"* | `Babai.step5_vertexClass_ncard_lt` |
| §9.4, step 3, *"`Aut(X₁₂) ≤ Aut(X)`"*, on the edges | `Babai.VColBipBlk.edge_iff_of_wlRaw_eq` |
| §9.4, step 6, *"a contradiction with the positive symmetry defect"* | `Babai.not_twinClass_eq_step5Pts` |
| §9.4, step 6, Claim, *"`X₁` is uniprimitive"* | `Babai.step6Config_isUniprimitive` |
| §9.4, step 6, the Claim in the shape `IsBipartiteCase.upcc₁` needs | `Babai.step6_upcc₁` |
-/

namespace Babai

/-! ### The rank is a function of the color classes, across a renaming of the points -/

namespace PartitionStructure

/-- Definition 3.1.1 depends on the coloring only through its kernel, also when the point
sets are renamed by a bijection: `Babai.PartitionStructure.rank_congr` across `e`. -/
theorem rank_congr_equiv {V V' : Type*} {Y : PartitionStructure V} {Y' : PartitionStructure V'}
    (e : V ≃ V')
    (hker : ∀ x y u v : V,
      Y.color x y = Y.color u v ↔ Y'.color (e x) (e y) = Y'.color (e u) (e v)) :
    Y.rank = Y'.rank := by
  classical
  have hbij : Function.Bijective
      (fun i : Fin Y.rank => Y'.color (e (Y.colorWitness i).1) (e (Y.colorWitness i).2)) := by
    constructor
    · intro i j hij
      have h := (hker (Y.colorWitness i).1 (Y.colorWitness i).2
        (Y.colorWitness j).1 (Y.colorWitness j).2).2 hij
      rwa [Y.color_colorWitness, Y.color_colorWitness] at h
    · intro i'
      refine ⟨Y.color (e.symm (Y'.colorWitness i').1) (e.symm (Y'.colorWitness i').2), ?_⟩
      have h : Y.color
            (Y.colorWitness (Y.color (e.symm (Y'.colorWitness i').1)
              (e.symm (Y'.colorWitness i').2))).1
            (Y.colorWitness (Y.color (e.symm (Y'.colorWitness i').1)
              (e.symm (Y'.colorWitness i').2))).2
          = Y.color (e.symm (Y'.colorWitness i').1) (e.symm (Y'.colorWitness i').2) :=
        Y.color_colorWitness _
      have h' := (hker _ _ _ _).1 h
      show Y'.color (e (Y.colorWitness (Y.color (e.symm (Y'.colorWitness i').1)
          (e.symm (Y'.colorWitness i').2))).1)
        (e (Y.colorWitness (Y.color (e.symm (Y'.colorWitness i').1)
          (e.symm (Y'.colorWitness i').2))).2) = i'
      rw [h', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Y'.color_colorWitness]
  have h := Fintype.card_of_bijective hbij
  simpa using h

end PartitionStructure

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The easy half of *"`Aut(X) = Aut(X₁₂)`"* (step 3)

The refined coloring refines the initial coloring, and the initial coloring records the
edges and the vertex coloring `f`.  So two points of `V₁` whose pairs with a block carry
the same refined color are joined to that block simultaneously, and two points with the
same refined diagonal color have the same color `f`.  This is all that the Claim of step 6
needs from the parenthetical *"`Aut(X₁₂) ≤ Aut(X)` because `X₁₂` is a refinement
of `E`"*. -/

namespace VColBipBlk

variable {s : Set Ω}

omit [Fintype Ω] [DecidableEq Ω] in
/-- The refined color of a pair of vertices determines its `ℕ`-name. -/
theorem wlColor_eq_of_wlRaw_eq (G : VColBipBlk ↥s ℕ) {A B A' B' : Set ↥s}
    (hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)
    (hv' : IsVertexOn G.part₁ G.blocks A' ∧ IsVertexOn G.part₁ G.blocks B')
    (h : wlRaw G A B = wlRaw G A' B') : wlColor G A B = wlColor G A' B' := by
  exact wlColor_eq_of_raw G hv hv' h

omit [DecidableEq Ω] in
/-- The edge indicator of the initial coloring reads off the edge relation. -/
theorem initEdge_eq_one_iff (G : VColBipBlk ↥s ℕ) {x : ↥s} (hx : G.part₁ x) (B : Set ↥s) :
    initEdge G {x} B = 1 ↔ (x, B) ∈ G.E := by
  classical
  rw [initEdge]
  constructor
  · intro h
    by_cases hc : ∃ z, G.part₁ z ∧ ({x} : Set ↥s) = {z} ∧ (z, B) ∈ G.E
    · obtain ⟨z, -, hz, hzB⟩ := hc
      obtain rfl : x = z := Set.singleton_eq_singleton_iff.1 hz
      exact hzB
    · rw [if_neg hc] at h; exact absurd h (by norm_num)
  · intro h
    rw [if_pos ⟨x, hx, rfl, h⟩]

/-- §9.4, step 3, the easy half of *"`Aut(X) = Aut(X₁₂)`"*: **the refined coloring refines
the edge relation.**  If the pairs `({x}, B)` and `({y}, B)` carry the same refined color,
with `x, y ∈ V₁` and `B` a block, then `x` and `y` are joined to `B` simultaneously. -/
theorem edge_iff_of_wlRaw_eq (G : VColBipBlk ↥s ℕ) {x y : ↥s} (hx : G.part₁ x)
    (hy : G.part₁ y) {B : Set ↥s} (hB : B ∈ G.blocks)
    (h : wlRaw G {x} B = wlRaw G {y} B) : ((x, B) ∈ G.E ↔ (y, B) ∈ G.E) := by
  classical
  have hxB : ({x} : Set ↥s) ≠ B := fun hc => G.blocks_off₁ B hB x (by rw [← hc]; rfl) hx
  have hyB : ({y} : Set ↥s) ≠ B := fun hc => G.blocks_off₁ B hB y (by rw [← hc]; rfl) hy
  have hinit := initColor_eq_of_wlRaw_eq G h
  rw [initColor, initColor, if_neg hxB, if_neg hyB] at hinit
  have h2 := (Nat.pair_eq_pair.1 hinit).2
  have h3 := (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 h2).1).1
  rw [← G.initEdge_eq_one_iff hx B, ← G.initEdge_eq_one_iff hy B, h3]

end VColBipBlk

/-! ### Counting the vertices of `X[W₁ ∪ V₂]` -/

section Counting

open VColBipBlk

variable (X : Pt (BipBlockInputs Ω))

theorem ncard_setOf_mem_blocks_step5 :
    {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ X.obj.1.1.blocks}.ncard
      = X.obj.1.1.blocks.ncard := by
  have himg : (Subtype.val '' {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ X.obj.1.1.blocks}
      : Set (Set ↥X.car)) = X.obj.1.1.blocks := by
    ext B
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hB; exact ⟨⟨B, Or.inr hB⟩, hB, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]

theorem step5Pts_eq_image :
    step5Pts X = (fun x : ↥X.car => ({x} : Set ↥X.car)) '' dominantClass X := by
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem ncard_setOf_mem_step5Pts :
    {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}.ncard
      = (dominantClass X).ncard := by
  have himg : (Subtype.val '' {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      : Set (Set ↥X.car)) = step5Pts X := by
    ext A
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hA; exact ⟨⟨A, Or.inl hA⟩, hA, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg, step5Pts_eq_image,
    Set.ncard_image_of_injective _ Set.singleton_injective]

/-- §9.4, step 5.  `n₂ < α n₁ < |W₁|`: **the dominant class has more points than there are
blocks**, which is the hypothesis *"`V₁` is larger than any other color-class in `X`"* of
the Large clique lemma, once the other classes are known to consist of blocks. -/
theorem numBlocks_lt_dominantClass_ncard (h : ¬ AllClassesSmall X) :
    X.obj.1.1.blocks.ncard < (dominantClass X).ncard := by
  have h1 : (X.obj.1.1.numBlocks : ℝ)
      < BipBlockInputs.alpha X * (BipBlockInputs.n₁ X : ℝ) := X.obj.2.2.2.2.1
  have h2 := alpha_mul_n₁_lt_dominantClass h
  have : (X.obj.1.1.blocks.ncard : ℝ) < ((dominantClass X).ncard : ℝ) := by
    have : (X.obj.1.1.numBlocks : ℝ) = (X.obj.1.1.blocks.ncard : ℝ) := rfl
    linarith [this ▸ h1]
  exact_mod_cast this

/-- §9.4, step 6, the hypothesis of the Large clique lemma (Lemma 3.4.25): *"`V₁` is larger
than any other color-class in `X`."*  This is
`Babai.VColBipBlk.vertexClass_ncard_lt_of_dominant` for the restricted configuration
`X[W₁ ∪ V₂]` of step 5: the first part `W₁` is one vertex-color class, so every other
vertex-color class consists of blocks, of which there are fewer than `|W₁|`. -/
theorem step5_vertexClass_ncard_lt (h : ¬ AllClassesSmall X)
    {i₀ : Fin (step5Config X).rank}
    (hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀)
    (i : Fin (step5Config X).rank) (hi : i ≠ i₀) :
    ((step5Config X).vertexClass i).ncard < ((step5Config X).vertexClass i₀).ncard := by
  have hsub : (step5Config X).vertexClass i
      ⊆ {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ X.obj.1.1.blocks} := by
    intro u hu
    rcases u.2 with hup | hub
    · exact absurd ((hV₁ ▸ hup : u ∈ (step5Config X).vertexClass i₀).symm.trans hu)
        (Ne.symm hi)
    · exact hub
  calc ((step5Config X).vertexClass i).ncard
      ≤ {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ X.obj.1.1.blocks}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = X.obj.1.1.blocks.ncard := ncard_setOf_mem_blocks_step5 X
    _ < (dominantClass X).ncard := numBlocks_lt_dominantClass_ncard X h
    _ = ((step5Config X).vertexClass i₀).ncard := by
        rw [← ncard_setOf_mem_step5Pts X, hV₁]

end Counting

/-! ### The positive symmetry defect: `W₁` is not a twin equivalence class -/

section Defect

open VColBipBlk

variable (X : Pt (BipBlockInputs Ω))

/-- A point of `W₁`, read as a point of the restricted point set `W₁ ∪ V₂`. -/
noncomputable def step5Point (x : ↥(dominantClass X)) : ↥(step5Set X) :=
  ⟨((x : ↥X.car) : Ω), ⟨(x : ↥X.car), Or.inl x.2, rfl⟩⟩

theorem incl_step5Point (x : ↥(dominantClass X)) :
    VColBipBlk.incl (step5Set_subset X) (step5Point X x) = (x : ↥X.car) := rfl

theorem step5Point_part₁ (x : ↥(dominantClass X)) :
    (step5Obj X).part₁ (step5Point X x) :=
  (step5Obj_part₁_iff X _).2 (by rw [incl_step5Point]; exact x.2)

theorem step5Point_injective : Function.Injective (step5Point X) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

/-- Every point of the new first part comes from a point of `W₁`. -/
theorem exists_step5Point {p : ↥(step5Set X)} (hp : (step5Obj X).part₁ p) :
    ∃ x : ↥(dominantClass X), step5Point X x = p := by
  refine ⟨⟨VColBipBlk.incl (step5Set_subset X) p, (step5Obj_part₁_iff X p).1 hp⟩, ?_⟩
  exact Subtype.ext rfl

/-- §9.4, step 6.  **Twins of the configuration `X[W₁ ∪ V₂]` inside `W₁` are twins of the
graph.**  This is the easy half of the parenthetical of step 3, *"`Aut(X₁₂) ≤ Aut(X)`
because `X₁₂` is a refinement of `E`"*: the transposition of two vertices of `W₁` that
preserves all colors of the configuration preserves the color `f` and the edges, hence is
an automorphism of the restricted graph `X[W₁ ∪ V₂]`. -/
theorem isTwin_step5Obj_of_isTwin_step5Config {u v : ↥(dominantClass X)} (huv : u ≠ v)
    (h : IsTwin (step5Config X).Aut (step5Pt X u) (step5Pt X v)) :
    IsTwin (step5Obj X).Aut (step5Point X u) (step5Point X v) := by
  classical
  set G := X.obj.1.1 with hG
  obtain ⟨-, hmem⟩ := h
  have hcol : ∀ a b : ↥(step5Vtx X),
      (step5Config X).color (Equiv.swap (step5Pt X u) (step5Pt X v) a)
        (Equiv.swap (step5Pt X u) (step5Pt X v) b) = (step5Config X).color a b := hmem
  -- the transposition of two vertices of `W₁` fixes every block
  have hfixBlk : ∀ B : ↥(step5Vtx X), (B : Set ↥X.car) ∈ G.blocks →
      Equiv.swap (step5Pt X u) (step5Pt X v) B = B := by
    intro B hB
    have key : ∀ w : ↥(dominantClass X), B ≠ step5Pt X w := by
      intro w hc
      have hBw : (B : Set ↥X.car) = {((w : ↥X.car))} := congrArg Subtype.val hc
      refine G.blocks_off₁ (B : Set ↥X.car) hB ((w : ↥X.car)) ?_ w.2.1
      rw [hBw]
      exact rfl
    exact Equiv.swap_apply_of_ne_of_ne (key u) (key v)
  -- the same vertex color, hence the same color `f`
  have hdiag : wlRaw G ({((u : ↥X.car))} : Set ↥X.car) {((u : ↥X.car))}
      = wlRaw G ({((v : ↥X.car))} : Set ↥X.car) {((v : ↥X.car))} := by
    have h1 := hcol (step5Pt X u) (step5Pt X u)
    rw [Equiv.swap_apply_left] at h1
    exact (step5Config_color_eq_iff X _ _ _ _).1 (congrArg Fin.val h1.symm)
  have hvu : IsVertexOn G.part₁ G.blocks ({((u : ↥X.car))} : Set ↥X.car) :=
    Or.inl ⟨_, u.2.1, rfl⟩
  have hvv : IsVertexOn G.part₁ G.blocks ({((v : ↥X.car))} : Set ↥X.car) :=
    Or.inl ⟨_, v.2.1, rfl⟩
  have hf : G.f (u : ↥X.car) = G.f (v : ↥X.car) :=
    G.f_eq_of_wlColor_eq u.2.1 v.2.1
      (G.wlColor_eq_of_wlRaw_eq ⟨hvu, hvu⟩ ⟨hvv, hvv⟩ hdiag)
  -- the same neighbouring blocks
  have hedge : ∀ B ∈ G.blocks,
      (((u : ↥X.car), B) ∈ G.E ↔ ((v : ↥X.car), B) ∈ G.E) := by
    intro B hB
    refine G.edge_iff_of_wlRaw_eq u.2.1 v.2.1 hB ?_
    have h1 := hcol (step5Pt X u) ⟨B, Or.inr hB⟩
    rw [Equiv.swap_apply_left, hfixBlk ⟨B, Or.inr hB⟩ hB] at h1
    exact ((step5Config_color_eq_iff X _ _ _ _).1 (congrArg Fin.val h1)).symm
  refine ((step5Obj X).isTwin_iff (step5Point_part₁ X u) (step5Point_part₁ X v)
    (fun hc => huv (step5Point_injective X hc))).2 ⟨hf, ?_⟩
  intro B hB
  have hBmem : VColBipBlk.incl (step5Set_subset X) '' B ∈ G.blocks := hB
  have := hedge _ hBmem
  exact this

/-- §9.4, step 6, *"a contradiction with the positive symmetry defect assumption"*.
**`W₁` is not a single twin equivalence class of `X[W₁ ∪ V₂]`.**

If it were, all the points of `W₁` would be pairwise twins of the graph `X[W₁ ∪ V₂]`
(`Babai.isTwin_step5Obj_of_isTwin_step5Config`), so the absolute symmetricity of the new
first part would be all of it and its symmetry defect would be `0`; but the restricted
instance is an admissible input of Theorem 9.2.2 for the threshold `α_new < 1`
(`Babai.step5Obj_isThm922Input`), whose symmetry defect is therefore at least
`1 - α_new > 0`. -/
theorem not_twinClass_eq_step5Pts (h : ¬ AllClassesSmall X)
    {i₀ : Fin (step5Config X).rank}
    (hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀)
    (x₀ : ↥(dominantClass X)) :
    twinClass (step5Config X).Aut (step5Pt X x₀) ≠ (step5Config X).vertexClass i₀ := by
  classical
  letI : Fintype ↥(step5Set X) := Fintype.ofFinite _
  intro hcl
  -- every vertex of `W₁` is a twin of `x₀`, hence any two of them are twins
  have hmem : ∀ x : ↥(dominantClass X),
      TwinOrEq (step5Config X).Aut (step5Pt X x₀) (step5Pt X x) := by
    intro x
    have : step5Pt X x ∈ (step5Config X).vertexClass i₀ := by
      rw [← hV₁]; exact ⟨(x : ↥X.car), x.2, rfl⟩
    rw [← hcl] at this
    exact this
  have htwin : ∀ x y : ↥(dominantClass X), x ≠ y →
      IsTwin (step5Obj X).Aut (step5Point X x) (step5Point X y) := by
    intro x y hxy
    refine isTwin_step5Obj_of_isTwin_step5Config X hxy ?_
    have heq := twinOrEq_equivalence (step5Config X).Aut
    have h1 : TwinOrEq (step5Config X).Aut (step5Pt X x) (step5Pt X y) :=
      heq.trans (heq.symm (hmem x)) (hmem y)
    rcases h1 with hc | hc
    · exact absurd (Subtype.ext (Set.singleton_eq_singleton_iff.1
        (congrArg Subtype.val hc))) hxy
    · exact hc
  -- so the whole new first part is a set of twins
  have hall : IsTwinSet (step5Obj X).Aut (step5Obj X).V₁ := by
    intro p hp q hq hpq
    obtain ⟨x, rfl⟩ := exists_step5Point X hp
    obtain ⟨y, rfl⟩ := exists_step5Point X hq
    exact htwin x y (fun hc => hpq (congrArg (step5Point X) hc))
  have hle : (step5Obj X).V₁.ncard ≤ (step5Obj X).symmetricity₁ :=
    ncard_le_symmetricity₁ _ (fun _ hx => hx) hall
  -- but the symmetry defect of the restricted instance is at least `1 - α_new > 0`
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

end Defect

/-! ### The Claim of step 6 -/

/-- §9.4, the Claim of step 6, **as step 8 re-runs it**: *"`X₁` is uniprimitive."*

The Claim is made of three inputs, which step 6 and step 8 supply from their own data:
`V₁` is one vertex-color class of a coherent configuration `P` and is larger than every
other class (`hmax`), `V₁` is not a single twin equivalence class of `P` (`hdef`, the
positive symmetry defect assumption), and `X₁ = P[V₁]` is primitive (`hprim`, the branch
condition of step 6 for step 6, and the survival of primitivity under the coarsening of
step 8 for step 8).  `h2` is the trivial remark that a configuration on at least two points
has at least two colors.

The content is the Large clique lemma (Lemma 3.4.25), through
`Babai.claim_9_4_step6`: were `X₁` the clique configuration, `V₁` would be a twin
equivalence class of `P`.

Step 8 has to re-run this Claim rather than inherit uniprimitivity from step 6, because a
coarsening of the coloring can lower the rank of `X₁` to `2`; what it cannot do is
disconnect a constituent (`Babai.PartitionStructure.isPrimitive_of_coarser`). -/
theorem claim_9_4_step6_general {V : Type} [Fintype V] [DecidableEq V]
    (P : PartitionStructure V)
    (hP : P.IsCoherent) (i₀ : Fin P.rank)
    (hmax : ∀ i : Fin P.rank, i ≠ i₀ →
      (P.vertexClass i).ncard < (P.vertexClass i₀).ncard)
    {x : V} (hx : x ∈ P.vertexClass i₀) (hdef : twinClass P.Aut x ≠ P.vertexClass i₀)
    (hprim : (P.induced (P.vertexClass i₀)).IsPrimitive)
    (h2 : 2 ≤ (P.induced (P.vertexClass i₀)).rank) :
    (P.induced (P.vertexClass i₀)).IsUniprimitive := by
  refine ⟨hprim, ?_⟩
  have hne := claim_9_4_step6 P hP i₀ hmax hx hdef
  omega

section Claim

open VColBipBlk

variable (X : Pt (BipBlockInputs Ω))

/-- The points of `W₁`, in bijection with the vertex-color class of `W₁` in
`X[W₁ ∪ V₂]`. -/
noncomputable def step6ClassEquiv {i₀ : Fin (step5Config X).rank}
    (hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀) :
    ↥(dominantClass X) ≃ ↥((step5Config X).vertexClass i₀) :=
  Equiv.ofBijective
    (fun x => ⟨step5Pt X x, hV₁ ▸ (⟨(x : ↥X.car), x.2, rfl⟩ :
      (step5Pt X x : Set ↥X.car) ∈ step5Pts X)⟩)
    (by
      constructor
      · intro a b hab
        have h : ({((a : ↥X.car))} : Set ↥X.car) = {((b : ↥X.car))} :=
          congrArg (fun z : ↥((step5Config X).vertexClass i₀) => ((z : ↥(step5Vtx X)) :
            Set ↥X.car)) hab
        exact Subtype.ext (Set.singleton_eq_singleton_iff.1 h)
      · rintro ⟨u, hu⟩
        have hup : (u : Set ↥X.car) ∈ step5Pts X := by
          have : u ∈ {w : ↥(step5Vtx X) | (w : Set ↥X.car) ∈ step5Pts X} := by
            rw [hV₁]; exact hu
          exact this
        obtain ⟨x, hx, hux⟩ := hup
        exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hux.symm)⟩)

@[simp] theorem step6ClassEquiv_val {i₀ : Fin (step5Config X).rank}
    (hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀) (x : ↥(dominantClass X)) :
    (((step6ClassEquiv X hV₁ x : ↥((step5Config X).vertexClass i₀)) : ↥(step5Vtx X)) :
      Set ↥X.car) = {((x : ↥X.car))} := rfl

/-- §9.4, step 6.  **The rank of `X₁` is the rank of the subconfiguration induced on the
vertex-color class of `W₁`.**  The two configurations have the same color classes — both
are the refined coloring read on the pairs of points of `W₁` — and the rank depends on the
coloring only through its color classes. -/
theorem rank_step6Config_eq {i₀ : Fin (step5Config X).rank}
    (hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀)
    [Fintype ↥(step5Vtx X)] :
    (step6Config X).rank
      = ((step5Config X).induced ((step5Config X).vertexClass i₀)).rank := by
  refine PartitionStructure.rank_congr_equiv (step6ClassEquiv X hV₁) ?_
  intro a b c d
  rw [PartitionStructure.induced_color_eq_iff, ← PartitionStructure.natColor_eq_iff,
    ← PartitionStructure.natColor_eq_iff, step5Config_color_eq_iff,
    step6Config_natColor_eq_iff]
  exact Iff.rfl

/-- `X₁` has at least two colors: its first part has at least two points, and a
configuration whose points are not all equal has an off-diagonal color. -/
theorem two_le_rank_step6Config (h : ¬ AllClassesSmall X) : 2 ≤ (step6Config X).rank := by
  classical
  have hcard : 2 ≤ (dominantClass X).ncard := two_le_dominantClass_ncard h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard (Set.toFinite (dominantClass X))).1 (by omega)
  set u : ↥(dominantClass X) := ⟨a, ha⟩ with hu
  set v : ↥(dominantClass X) := ⟨b, hb⟩ with hv
  have huv : u ≠ v := fun hc => hab (congrArg Subtype.val hc)
  by_contra hlt
  rw [Nat.not_le] at hlt
  have h1 := ((step6Config X).color u v).isLt
  have h2 := ((step6Config X).color v v).isLt
  have hsub : (step6Config X).color u v = (step6Config X).color v v := Fin.ext (by omega)
  exact huv ((step6Config_isCoherent X).toIsConfiguration.diag u v v hsub)

/-- §9.4, step 6, **the Claim**: *"`X₁` is uniprimitive."*  (Version 2.5, lines 4142-4146.)

On the branch of step 6 where `X₁` is primitive, `X₁` is a UPCC (Def. 3.2.1): it is
primitive by the branch condition (`Babai.step6Imprimitive_iff`), and it is not the clique
configuration, because it has at least two points and, were its rank `2`, the Large clique
lemma (Lemma 3.4.25) would make `W₁` a twin equivalence class of `X[W₁ ∪ V₂]`
(`Babai.claim_9_4_step6`), which the positive symmetry defect of the restricted instance
forbids (`Babai.not_twinClass_eq_step5Pts`).

The hypothesis `h` is the branch condition of step 4, *"the dominant vertex-color class has
size `> α n₁`"*, which is what step 5 runs on. -/
theorem step6Config_isUniprimitive (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X) :
    (step6Config X).IsUniprimitive := by
  classical
  letI : Fintype ↥(step5Vtx X) := Fintype.ofFinite _
  refine ⟨not_not.1 (fun hp => himp ((step6Imprimitive_iff X).2 hp)), ?_⟩
  -- a point of `W₁`
  have hne : (dominantClass X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    have := two_le_dominantClass_ncard h
    rw [hc, Set.ncard_empty] at this
    omega
  obtain ⟨x₀, hx₀⟩ := hne
  set u₀ : ↥(step5Vtx X) := ⟨{x₀}, Or.inl ⟨x₀, hx₀, rfl⟩⟩ with hu₀
  set i₀ : Fin (step5Config X).rank := (step5Config X).vcolor u₀ with hi₀
  have hV₁ : {u : ↥(step5Vtx X) | (u : Set ↥X.car) ∈ step5Pts X}
      = (step5Config X).vertexClass i₀ := step5Pts_eq_vertexClass X hx₀
  have hx : u₀ ∈ (step5Config X).vertexClass i₀ := rfl
  have hne2 : (step6Config X).rank ≠ 2 := by
    rw [rank_step6Config_eq X hV₁]
    exact claim_9_4_step6 (step5Config X) (step5Config_isCoherent X) i₀
      (step5_vertexClass_ncard_lt X h hV₁) hx
      (not_twinClass_eq_step5Pts X h hV₁ ⟨x₀, hx₀⟩)
  have h2 := two_le_rank_step6Config X h
  omega

/-- §9.4, step 6, the Claim in the shape the field `Babai.IsBipartiteCase.upcc₁` asks for:
**there is a coherent uniprimitive configuration on the points of `W₁` whose color classes
are those of the coloring `Babai.step6Color` that steps 6-8 read.**

This is exactly what the field `Babai.IsBipartiteCase.upcc₁` asks for. -/
theorem step6_upcc₁ (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X) :
    ∃ P : PartitionStructure ↥(dominantClass X), P.IsCoherent ∧ P.IsUniprimitive ∧
      ∀ u v u' v' : ↥(dominantClass X),
        P.natColor u v = P.natColor u' v' ↔ step6Color X u v = step6Color X u' v' :=
  ⟨step6Config X, step6Config_isCoherent X, step6Config_isUniprimitive X h himp,
    fun u v u' v' => (sameKernel_step6Color X u v u' v').symm⟩

end Claim

/-! ### Why the fields `upcc₁` and `imprimitive₂` speak of color classes

The fields of a `Case` of §9.6-§9.8 that describe the configuration on one part
(`Babai.IsBipartiteCase.upcc₁`, `Babai.IsImprimitiveCase.imprimitive₂`,
`Babai.IsBlockDesignCase.clique₂`, `Babai.IsUPCCCase.upcc₂`) ask for a configuration whose
**color classes** on the part are the color classes of `c`.  They do not ask for the
equation `natColor = c`, and they cannot: the lemma below shows that naming the colors of
`V₁` and of `V₂` by the ambient `c` is contradictory once both parts are nonempty, which
`Babai.IsBipartiteCase.link_nontrivial` forces.

The reason is that a `Babai.PartitionStructure.natColor` is onto `{0, …, rank-1}` (the
field `color_surjective`, Def. 3.1.1: no constituent is empty), so the two equations force
the color `0` of `c` to occur both inside `V₁` and inside `V₂`; but one color of a coherent
configuration determines the vertex color of its tail (Obs. 3.3.4), and the tails of those
two pairs lie in different vertex-color classes.  What step 6 of §9.4 supplies is the
color-class form (`Babai.step6_upcc₁`), and that is the form the fields take.  See the
entry for §9.6-§9.8 in the corrected paper. -/

section CaseFields

/-- Naming the colors of a **part** by the ambient coloring `c`, on `V₁` and on `V₂` at the
same time, is contradictory when both parts are nonempty.  This is why the part fields of
the `Case` structures of §9.6-§9.8 ask for the color classes of `c` on the part and not for
the equation `natColor = c`. -/
theorem partNaming_false {V : Type} {c : V → V → ℕ} {V₁ V₂ : Set V}
    (hcoh : ∃ X : PartitionStructure V, X.IsCoherent ∧ X.natColor = c ∧
      ∃ i j : Fin X.rank, i ≠ j ∧ V₁ = X.vertexClass i ∧ V₂ = X.vertexClass j ∧
        (∀ x : V, x ∈ V₁ ∨ x ∈ V₂))
    (hP₁ : ∃ P : PartitionStructure ↥V₁, ∀ x y : ↥V₁, P.natColor x y = c (x : V) (y : V))
    (hP₂ : ∃ P : PartitionStructure ↥V₂, ∀ x y : ↥V₂, P.natColor x y = c (x : V) (y : V))
    (h₁ : V₁.Nonempty) (h₂ : V₂.Nonempty) : False := by
  obtain ⟨X, hX, hXc, i, j, hij, hV₁, hV₂, -⟩ := hcoh
  obtain ⟨P₁, hc₁⟩ := hP₁
  obtain ⟨P₂, hc₂⟩ := hP₂
  obtain ⟨x₁, hx₁⟩ := h₁
  obtain ⟨x₂, hx₂⟩ := h₂
  have hr₁ : 0 < P₁.rank := lt_of_le_of_lt (Nat.zero_le _) (P₁.color ⟨x₁, hx₁⟩ ⟨x₁, hx₁⟩).isLt
  have hr₂ : 0 < P₂.rank := lt_of_le_of_lt (Nat.zero_le _) (P₂.color ⟨x₂, hx₂⟩ ⟨x₂, hx₂⟩).isLt
  obtain ⟨u, v, huv⟩ := P₁.color_surjective ⟨0, hr₁⟩
  obtain ⟨u', v', huv'⟩ := P₂.color_surjective ⟨0, hr₂⟩
  have h0₁ : c (u : V) (v : V) = 0 := by
    rw [← hc₁ u v, PartitionStructure.natColor, huv]
  have h0₂ : c (u' : V) (v' : V) = 0 := by
    rw [← hc₂ u' v', PartitionStructure.natColor, huv']
  have hnat : X.natColor (u : V) (v : V) = X.natColor (u' : V) (v' : V) := by
    rw [hXc, h0₁, h0₂]
  have hcol : X.color (u : V) (v : V) = X.color (u' : V) (v' : V) :=
    (X.natColor_eq_iff _ _ _ _).1 hnat
  have e1 : X.vcolor (u : V) = X.tailColor (X.color (u' : V) (v' : V)) :=
    X.vcolor_fst_eq hX hcol
  have e2 : X.vcolor (u' : V) = X.tailColor (X.color (u' : V) (v' : V)) :=
    X.vcolor_fst_eq hX rfl
  have hu : X.vcolor (u : V) = i := hV₁ ▸ u.2
  have hu' : X.vcolor (u' : V) = j := hV₂ ▸ u'.2
  exact hij (by rw [← hu, ← hu', e1, e2])

end CaseFields

end Babai
