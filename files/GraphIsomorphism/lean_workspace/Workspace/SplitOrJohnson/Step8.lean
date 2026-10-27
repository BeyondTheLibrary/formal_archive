/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 8: `X ← (V₁, V₂; R_i)` and the WL refinement of the resulting graph.
-/
import Workspace.SplitOrJohnson.Step78
import Workspace.SplitOrJohnson.Minor

/-!
# §9.4, step 8

Version 2.5, lines 4157-4165 of `babai-gi-source/quasi25.txt`.

> *"8. (: `X₁` is a UPCC, `X₂` is homogeneous, and `X₁₂` is nonotrivial :)  Let `i` be the
> smallest index such that `R_i` is involved in `X₁₂`.  Replace `X ← (V₁, V₂; R_i)`
> (: `X` is semiregular, nontrivial; therefore its symmetry defect is `≥ 1/2` in each part
> by Prop. 2.4.30 :)  Update `X ← WL refinement of X`.  The only effect of this is that it
> may merge some of the edge-color classes in `X`; but `X₁₂` remains nontrival (because
> `R_i` remains one of its constituents).  `X₁` remains a UPCC by Claim above."*

## What is formalized here

This file is written on top of `Workspace/SplitOrJohnson/Step78.lean`, which leaves the
bihomogeneous instance `X[V₁ ∪ D_j]` of step 7: the point set is `Babai.step7Set`, the
graph is `Babai.step7Obj`, and the coherent configuration is `Babai.step7Config`, the
coloring of step 3 read on the vertex set `Babai.step7Vtx`.

* *"the smallest index `i` such that `R_i` is involved in `X₁₂`"* — `Babai.step8Color`,
  the smallest color of `Babai.VColBipBlk.wlCaseColor` that occurs on a pair (point of
  `V₁`, block of `D_j`).  As in step 7, "smallest" is read in the canonical naming of the
  colors, so the choice is a function of the object.
* *"Replace `X ← (V₁, V₂; R_i)`"* — `Babai.step8Obj`: the graph of step 7 with its edge
  set replaced by `R_i`.  The first part, the blocks and the two colorings are unchanged,
  so `n₁` and `n₂` are unchanged and the hypothesis `n₂ < α n₁` survives.
* *"`X` is semiregular, nontrivial; therefore its symmetry defect is `≥ 1/2` in each part
  by Prop. 2.4.30"* — `Babai.step8Obj_isSemiregular`, `Babai.step8Obj_not_isTrivial`,
  `Babai.half_le_step8Obj_defect₁`.
* *"Update `X ← WL refinement of `X`"* — `Babai.step8Raw`, the WL refinement of the new
  graph, run **on the vertex set** `V₁ ∪ V₂` (this is where the paper runs it).
* *"The only effect of this is that it may merge some of the edge-color classes"* —
  `Babai.step8Raw_eq_of_step8Old_eq`: the configuration of step 7 refines the new one.  The
  reason is the one the paper gives implicitly: the configuration of step 7 is a coherent,
  that is a *stable*, coloring (Obs. 4.3.1) which refines the input coloring of the new
  refinement, and WL refinement produces the **coarsest** stable refinement of its input
  (`Babai.WL.stable_refines_iter`).

## The general lemma about WL refinement

`Babai.WL.step_refines_of_refines` is the monotonicity of a round of WL refinement: if a
coloring `d` refines a coloring `c`, then the refined coloring of `d` refines the refined
coloring of `c`.  The proof is the counting argument of §4.3: a color class of `c` is a
union of color classes of `d`, so a count made in the colors of `c` is a sum of counts made
in the colors of `d`, and each summand is the same for the two pairs.  Together with
Obs. 4.3.1 this gives `Babai.WL.stable_refines_iter`, which is what step 8 uses.

| Paper | Lean |
|---|---|
| §4.3, WL refinement is monotone | `Babai.WL.step_refines_of_refines`, `.iter_refines_of_refines` |
| §4.3, WL refinement is the coarsest stable refinement | `Babai.WL.stable_refines_iter` |
| §9.4, step 8, *"the smallest index `i`"* | `Babai.step8Color` |
| §9.4, step 8, *"`X ← (V₁, V₂; R_i)`"* | `Babai.step8Obj` |
| §9.4, step 8, *"`X` is semiregular"* | `Babai.step8Obj_isSemiregular` |
| §9.4, step 8, *"nontrivial"* | `Babai.step8Obj_not_isTrivial` |
| §9.4, step 8, *"symmetry defect `≥ 1/2` … by Prop. 2.4.30"* | `Babai.half_le_step8Obj_defect₁` |
| §9.4, step 8, *"`X ← WL refinement of X`"* | `Babai.step8Raw`, `Babai.step8Config` |
| §9.4, step 8, *"it may merge some of the edge-color classes"* | `Babai.step8Raw_eq_of_step8Old_eq` |
| §9.4, step 8, *"(: `X` bihomogeneous :)"* after the step | `Babai.step8Config_parts` |
| §9.4, step 8, *"`X₁₂` remains nontrivial"* | `Babai.step8_link_nontrivial` |
| §9.4, step 8, *"`R_i` remains one of its constituents"* | `Babai.step8_edge_iff_of_step8Raw_eq` |
| §9.4, step 8, *"`X₁` remains a UPCC by Claim above"* | `Babai.step8_induced_isUniprimitive` |
| §9.4, the Claim of step 6, as step 8 re-runs it | `Babai.claim_9_4_step6_general` |
| §9.4, step 9, the three cases | `Babai.step8_induced₂_trichotomy` |

## Where the rest of step 8 is

The choice of `R_i` is canonical (`Babai.step8Color_congr`).  The canonicity of the object
`Babai.step8Obj` and of the coloring `Babai.step8Raw` under an isomorphism of the inputs is
proved in `Workspace/SplitOrJohnson/Step8Canon.lean` (`Babai.step8Obj_isIsoTo`,
`Babai.step8Raw_map`), and the Claim of step 8 (*"There are no `X`-twins in `V₁`"*) at
this instance is `Babai.claim_9_4_step8_at` in `Workspace/SplitOrJohnson/Step8Claim.lean`.
-/

namespace Babai

/-! ### WL refinement is monotone, and is the coarsest stable refinement

The two facts about §4.3 that step 8 needs.  Both are about colorings only. -/

namespace WL

variable {Ω : Type*} {C D : Type*}

/-- §4.3.  **One round of WL refinement is monotone**: if `d` refines `c` then the round
run on `d` refines the round run on `c`.

The proof is the counting argument of §4.3.  Write `μ` for the map that sends a color of
`d` to the color of `c` that contains it; then a set counted by the round of `c`,
`{z | c(x,z) = j and c(z,y) = k}`, is the disjoint union of the sets
`{z | d(x,z) = a and d(z,y) = b}` over the pairs `(a,b)` with `μ(a) = j` and `μ(b) = k`,
and the round run on `d` gives each of those sets the same size at `(x,y)` and at
`(x',y')`. -/
theorem step_refines_of_refines [Finite Ω] {c : Ω → Ω → C} {d : Ω → Ω → D}
    (h : ∀ u v u' v' : Ω, d u v = d u' v' → c u v = c u' v')
    {x y x' y' : Ω} (hxy : step d x y = step d x' y') : step c x y = step c x' y' := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  obtain ⟨hd, hcount⟩ := (step_eq_iff d x y x' y').1 hxy
  refine (step_eq_iff c x y x' y').2 ⟨h _ _ _ _ hd, ?_⟩
  intro j k
  -- the map from the colors of `d` to the colors of `c`
  set μ : D → C := fun a =>
    if ha : ∃ p : Ω × Ω, d p.1 p.2 = a then c ha.choose.1 ha.choose.2 else c x y with hμdef
  have hμ : ∀ u v : Ω, μ (d u v) = c u v := by
    intro u v
    have ha : ∃ p : Ω × Ω, d p.1 p.2 = d u v := ⟨(u, v), rfl⟩
    have : μ (d u v) = c ha.choose.1 ha.choose.2 := by
      rw [hμdef]; exact dif_pos ha
    rw [this]
    exact h _ _ _ _ ha.choose_spec
  -- the pairs of colors of `d` that occur along the two pairs
  set T : Finset (D × D) :=
    (Finset.univ.image fun z : Ω => (d x z, d z y))
      ∪ (Finset.univ.image fun z : Ω => (d x' z, d z y')) with hT
  set T' : Finset (D × D) := T.filter fun p => μ p.1 = j ∧ μ p.2 = k with hT'
  have key : ∀ u v : Ω, (∀ z : Ω, ((d u z, d z v) : D × D) ∈ T) →
      ({z : Ω | c u z = j ∧ c z v = k}).ncard
        = ∑ p ∈ T', ({z : Ω | d u z = p.1 ∧ d z v = p.2}).ncard := by
    intro u v hmem
    have hfib : (Finset.univ.filter fun z : Ω => c u z = j ∧ c z v = k).card
        = ∑ p ∈ T', ((Finset.univ.filter fun z : Ω => c u z = j ∧ c z v = k).filter
            fun z : Ω => ((d u z, d z v) : D × D) = p).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro z hz
      have hz' := (Finset.mem_filter.1 hz).2
      refine Finset.mem_filter.2 ⟨hmem z, ?_, ?_⟩
      · rw [hμ]; exact hz'.1
      · rw [hμ]; exact hz'.2
    have hset : ({z : Ω | c u z = j ∧ c z v = k}).ncard
        = (Finset.univ.filter fun z : Ω => c u z = j ∧ c z v = k).card := by
      have : {z : Ω | c u z = j ∧ c z v = k}
          = ↑(Finset.univ.filter fun z : Ω => c u z = j ∧ c z v = k) := by
        ext z; simp
      rw [this, Set.ncard_coe_finset]
    rw [hset, hfib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp only [hT', Finset.mem_filter] at hp
    have hEq : ((Finset.univ.filter fun z : Ω => c u z = j ∧ c z v = k).filter
        fun z : Ω => ((d u z, d z v) : D × D) = p)
        = Finset.univ.filter fun z : Ω => d u z = p.1 ∧ d z v = p.2 := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      constructor
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, ?_⟩, h1, h2⟩
        · rw [← hμ u z, h1]; exact hp.2.1
        · rw [← hμ z v, h2]; exact hp.2.2
    have hcoe : {z : Ω | d u z = p.1 ∧ d z v = p.2}
        = ↑(Finset.univ.filter fun z : Ω => d u z = p.1 ∧ d z v = p.2) := by
      ext z; simp
    rw [hEq, hcoe, Set.ncard_coe_finset]
  rw [key x y (fun z => Finset.mem_union_left _ (Finset.mem_image.2 ⟨z, Finset.mem_univ z, rfl⟩)),
    key x' y' (fun z => Finset.mem_union_right _ (Finset.mem_image.2 ⟨z, Finset.mem_univ z, rfl⟩))]
  exact Finset.sum_congr rfl fun p _ => hcount p.1 p.2

/-- §4.3.  **WL refinement is monotone**: if `d` refines `c` then `n` rounds run on `d`
refine `n` rounds run on `c`. -/
theorem iter_refines_of_refines [Finite Ω] {c : Ω → Ω → C} {d : Ω → Ω → D}
    (h : ∀ u v u' v' : Ω, d u v = d u' v' → c u v = c u' v') :
    ∀ (n : ℕ) (x y x' y' : Ω), iter d n x y = iter d n x' y' → iter c n x y = iter c n x' y'
  | 0, _, _, _, _, hxy => h _ _ _ _ hxy
  | _ + 1, _, _, _, _, hxy =>
      step_refines_of_refines (iter_refines_of_refines h _) hxy

/-- §4.3, Observation 4.3.1.  **WL refinement produces the coarsest stable refinement of
its input**: a stable coloring `d` that refines `c` refines every round of the refinement
of `c`.

This is what step 8 of §9.4 means by *"The only effect of this is that it may merge some of
the edge-color classes"*: the configuration that step 7 leaves is stable and refines the
input coloring of the new refinement, so the new refinement is coarser. -/
theorem stable_refines_iter [Finite Ω] {c : Ω → Ω → C} {d : Ω → Ω → D} (hst : IsStable d)
    (h : ∀ u v u' v' : Ω, d u v = d u' v' → c u v = c u' v') :
    ∀ (n : ℕ) (x y x' y' : Ω), d x y = d x' y' → iter c n x y = iter c n x' y'
  | 0, _, _, _, _, hxy => h _ _ _ _ hxy
  | _ + 1, x, y, x', y', hxy =>
      step_refines_of_refines (stable_refines_iter hst h _) (hst x y x' y' hxy)

/-! ### Observation 3.3.5 for a coherent coloring

Step 8 needs the semiregularity of the constituent `R_i`, which is degree awareness
(Obs. 3.3.5) for the configuration of step 7.  Stated for a coloring, degree awareness is
the observation that `{z | d(u,z) = γ}` is `{z | d(u,z) = γ and d(z,u) = γ⁻}`, an
intersection number of the pair `(u,u)`. -/

/-- The converse color: in a configuration the color of a pair determines the color of the
reversed pair (Def. 3.1.2(ii)), so a color `γ` has a well-defined converse, and a color
that is not used may be given any converse. -/
theorem exists_conv {d : Ω → Ω → C} (h : IsConfigColoring d) (γ : C) :
    ∃ cv : C, ∀ a b : Ω, d a b = γ → d b a = cv := by
  classical
  by_cases hγ : ∃ q : Ω × Ω, d q.1 q.2 = γ
  · obtain ⟨q, hq⟩ := hγ
    exact ⟨d q.2 q.1, fun a b hab => h.2 a b q.1 q.2 (hab.trans hq.symm)⟩
  · exact ⟨γ, fun a b hab => absurd ⟨(a, b), hab⟩ hγ⟩

/-- Observation 3.3.5 (Degree awareness) for a coherent coloring: *"The color of a vertex
determines its out-degree in any given color."* -/
theorem outDeg_eq_of_diag_eq [Finite Ω] {d : Ω → Ω → C} (h : IsCoherentColoring d)
    {u u' : Ω} (huu : d u u = d u' u') (γ : C) :
    {z : Ω | d u z = γ}.ncard = {z : Ω | d u' z = γ}.ncard := by
  obtain ⟨hcfg, p, hp⟩ := h
  obtain ⟨cv, hcv⟩ := exists_conv hcfg γ
  have hset : ∀ w : Ω, {z : Ω | d w z = γ} = {z : Ω | d w z = γ ∧ d z w = cv} := fun w => by
    ext z; exact ⟨fun hz => ⟨hz, hcv w z hz⟩, fun hz => hz.1⟩
  rw [hset u, hset u', hp γ cv (d u u) u u rfl, hp γ cv (d u' u') u' u' rfl, huu]

/-- Observation 3.3.5 (Degree awareness) for a coherent coloring: *"The color of a vertex
determines its … in-degree in any given color."* -/
theorem inDeg_eq_of_diag_eq [Finite Ω] {d : Ω → Ω → C} (h : IsCoherentColoring d)
    {u u' : Ω} (huu : d u u = d u' u') (γ : C) :
    {z : Ω | d z u = γ}.ncard = {z : Ω | d z u' = γ}.ncard := by
  obtain ⟨hcfg, p, hp⟩ := h
  obtain ⟨cv, hcv⟩ := exists_conv hcfg γ
  have hset : ∀ w : Ω, {z : Ω | d z w = γ} = {z : Ω | d w z = cv ∧ d z w = γ} := fun w => by
    ext z; exact ⟨fun hz => ⟨hcv z w hz, hz⟩, fun hz => hz.2⟩
  rw [hset u, hset u', hp cv γ (d u u) u u rfl, hp cv γ (d u' u') u' u' rfl, huu]


/-- A coherent coloring stays coherent when the points are renamed by a bijection. -/
theorem isCoherentColoring_comp_equiv {Ω Ω' C : Type*} [Finite Ω'] {d : Ω → Ω → C}
    (e : Ω' ≃ Ω) (h : IsCoherentColoring d) :
    IsCoherentColoring (fun u v : Ω' => d (e u) (e v)) := by
  obtain ⟨⟨hdiag, hconv⟩, p, hp⟩ := h
  refine ⟨⟨fun x y z hxy => e.injective (hdiag (e x) (e y) (e z) hxy),
    fun u v x y huv => hconv (e u) (e v) (e x) (e y) huv⟩, p, ?_⟩
  intro i j k u v huv
  have himg : (fun z : Ω' => e z) ''
      {z : Ω' | d (e u) (e z) = i ∧ d (e z) (e v) = j} = {z : Ω | d (e u) z = i ∧ d z (e v) = j} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hz
      exact ⟨e.symm z, by simpa using hz, by simp⟩
  have := hp i j k (e u) (e v) huv
  rw [← this, ← himg, Set.ncard_image_of_injective _ e.injective]

end WL

/-! ### §9.4, step 8: the constituent `R_i` -/

section CaseColor

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}

namespace VColBipBlk

/-- On the pairs of vertices the canonical `ℕ`-naming of the colors is injective, so two
pairs carry the same name exactly when they carry the same color. -/
theorem wlCaseColor_eq_iff (G : VColBipBlk ↥s ℕ) {A B A' B' : Set ↥s}
    (hv : IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B)
    (hv' : IsVertexOn G.part₁ G.blocks A' ∧ IsVertexOn G.part₁ G.blocks B') :
    wlCaseColor G A B = wlCaseColor G A' B' ↔ wlRaw G A B = wlRaw G A' B' := by
  exact wlCaseColor_eq_iff_raw G hv hv'

end VColBipBlk

end CaseColor

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open VColBipBlk

section Step8

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 8.  **The colors involved in the link `X₁₂`**: the colors of the
configuration of step 7 that occur on a pair (point of `V₁`, block of `D_j`). -/
noncomputable def step8Colors (X : Pt (BipBlockInputs Ω)) : Set ℕ :=
  {k | ∃ x ∈ dominantClass X, ∃ B ∈ step7Blocks X,
    VColBipBlk.wlCaseColor X.obj.1.1 ({x} : Set ↥X.car) B = k}

/-- §9.4, step 8.  *"Let `i` be the smallest index such that `R_i` is involved in
`X₁₂`."*  The colors are named canonically by the named WL process, as in step 3, so the choice
is a function of the object. -/
noncomputable def step8Color (X : Pt (BipBlockInputs Ω)) : ℕ := sInf (step8Colors X)

/-- §9.4, step 8.  There is a color involved in the link: both parts are non-empty. -/
theorem step8Colors_nonempty (h : ¬ AllClassesSmall X) : (step8Colors X).Nonempty := by
  obtain ⟨B, hB⟩ := step7Blocks_nonempty X h
  obtain ⟨x, hx⟩ : (dominantClass X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    have := two_le_dominantClass_ncard h
    rw [hc, Set.ncard_empty] at this
    omega
  exact ⟨_, x, hx, B, hB, rfl⟩

theorem step8Color_mem (h : ¬ AllClassesSmall X) : step8Color X ∈ step8Colors X :=
  Nat.sInf_mem (step8Colors_nonempty X h)

/-- §9.4, step 8.  The pairs joined by the constituent `R_i`, read on the point set of
step 7: a point of `V₁` and a block of `D_j` whose pair carries the color `i`. -/
noncomputable def step8Edge (X : Pt (BipBlockInputs Ω)) :
    Set (↥(step7Set X) × Set ↥(step7Set X)) :=
  {p | (step7Obj X).part₁ p.1 ∧ p.2 ∈ (step7Obj X).blocks ∧
    VColBipBlk.wlCaseColor X.obj.1.1
      ({VColBipBlk.incl (step7Set_subset X) p.1} : Set ↥X.car)
      (VColBipBlk.incl (step7Set_subset X) '' p.2) = step8Color X}

/-- §9.4, step 8.  *"Replace `X ← (V₁, V₂; R_i)`."*  The graph of step 7 with its edge set
replaced by the constituent `R_i`: the first part, the blocks and the two colorings are
unchanged, so `n₁` and `n₂` do not change. -/
noncomputable def step8Obj (X : Pt (BipBlockInputs Ω)) : VColBipBlk ↥(step7Set X) ℕ :=
  { step7Obj X with
    E := step8Edge X
    E_sub := fun _ hp => ⟨hp.1, hp.2.1⟩ }

@[simp] theorem step8Obj_part₁ (p : ↥(step7Set X)) :
    (step8Obj X).part₁ p ↔ (step7Obj X).part₁ p := Iff.rfl

@[simp] theorem step8Obj_blocks (B : Set ↥(step7Set X)) :
    B ∈ (step8Obj X).blocks ↔ B ∈ (step7Obj X).blocks := Iff.rfl

@[simp] theorem step8Obj_E (p : ↥(step7Set X)) (B : Set ↥(step7Set X)) :
    (p, B) ∈ (step8Obj X).E ↔ (p, B) ∈ step8Edge X := Iff.rfl

theorem step8Obj_V₁ : (step8Obj X).V₁ = (step7Obj X).V₁ := rfl

theorem step8Obj_numBlocks : (step8Obj X).numBlocks = (step7Obj X).numBlocks := rfl

/-- §9.4, step 8.  **`n₁` does not change.** -/
theorem step8Obj_V₁_ncard : (step8Obj X).V₁.ncard = (dominantClass X).ncard :=
  step7Obj_V₁_ncard X

/-- §9.4, step 8.  **The hypothesis `n₂ < α n₁` of Theorem 9.2.2 survives the step**: the
step changes neither part. -/
theorem step8Obj_numBlocks_lt (h : ¬ AllClassesSmall X) :
    ((step8Obj X).numBlocks : ℝ) < alphaNew X * ((step8Obj X).V₁.ncard : ℝ) :=
  step7Obj_numBlocks_lt X h

end Step8

/-! ### §9.4, step 8: *"`X` is semiregular, nontrivial"* -/

section Semiregular

variable (X : Pt (BipBlockInputs Ω))

/-- Observation 3.3.2 for the configuration of step 7: the coloring of step 3, read on the
vertex set `V₁ ∪ D_j`, is coherent. -/
theorem step7Vtx_isCoherentColoring :
    WL.IsCoherentColoring
      (fun u v : ↥(step7Vtx X) => wlRaw X.obj.1.1 (u : Set ↥X.car) (v : Set ↥X.car)) :=
  WL.isCoherentColoring_restrict (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1)
    (step7Vtx_isStableSet X)

/-- A vertex of `X[V₁ ∪ D_j]` whose pair with a point of `W₁` carries the color of a pair
(point of `W₁`, block of `D_j`) is itself a block of `D_j`: the color of a pair determines
the vertex color of its head (Obs. 3.3.4), and a point and a block never carry the same
vertex color. -/
theorem mem_step7Blocks_of_wlRaw_eq {x y : ↥X.car} (hx : x ∈ dominantClass X)
    {A B₀ : Set ↥X.car} (hA : A ∈ step7Vtx X) (hB₀ : B₀ ∈ step7Blocks X)
    (hcol : wlRaw X.obj.1.1 ({y} : Set ↥X.car) A
      = wlRaw X.obj.1.1 ({x} : Set ↥X.car) B₀) : A ∈ step7Blocks X := by
  rcases hA with ⟨z, hz, rfl⟩ | hA
  · exfalso
    have hdiag := WL.diag_snd_eq_of_eq (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1) hcol
    have hvz : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({z} : Set ↥X.car) :=
      Or.inl ⟨z, hz.1, rfl⟩
    have hvB : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B₀ := Or.inr hB₀.1
    exact X.obj.1.1.wlColor_ne_of_part₁_blocks hz.1 hB₀.1
      (X.obj.1.1.wlColor_eq_of_wlRaw_eq ⟨hvz, hvz⟩ ⟨hvB, hvB⟩ hdiag)
  · exact hA

/-- A vertex of `X[V₁ ∪ D_j]` whose pair with a block of `D_j` carries the color of a pair
(point of `W₁`, block of `D_j`) is a point of `W₁`: the color of a pair determines the
vertex color of its tail (Obs. 3.3.4). -/
theorem mem_step5Pts_of_wlRaw_eq {x : ↥X.car} (hx : x ∈ dominantClass X)
    {A B B₀ : Set ↥X.car} (hA : A ∈ step7Vtx X) (hB₀ : B₀ ∈ step7Blocks X)
    (hcol : wlRaw X.obj.1.1 A B = wlRaw X.obj.1.1 ({x} : Set ↥X.car) B₀) :
    ∃ y ∈ dominantClass X, A = {y} := by
  rcases hA with hA | hA
  · exact hA
  · exfalso
    have hdiag := WL.diag_fst_eq_of_eq (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1) hcol
    have hvx : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x} : Set ↥X.car) :=
      Or.inl ⟨x, hx.1, rfl⟩
    have hvA : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks A := Or.inr hA.1
    exact X.obj.1.1.wlColor_ne_of_part₁_blocks hx.1 hA.1
      (X.obj.1.1.wlColor_eq_of_wlRaw_eq ⟨hvx, hvx⟩ ⟨hvA, hvA⟩ hdiag.symm)

/-- The blocks of `D_j` joined to a point `x` of `W₁` by `R_i`, read in the ambient
configuration: they are the blocks `A` with `wlRaw {x} A` the color `i`. -/
theorem step8_outNbhd_ncard {x : ↥X.car} (hx : x ∈ dominantClass X)
    {x₀ : ↥X.car} (hx₀ : x₀ ∈ dominantClass X) {B₀ : Set ↥X.car} (hB₀ : B₀ ∈ step7Blocks X)
    (hwit : VColBipBlk.wlCaseColor X.obj.1.1 ({x₀} : Set ↥X.car) B₀ = step8Color X)
    {p : ↥(step7Set X)} (hp : VColBipBlk.incl (step7Set_subset X) p = x) :
    {B : Set ↥(step7Set X) | (p, B) ∈ (step8Obj X).E}.ncard
      = {z : ↥(step7Vtx X) | wlRaw X.obj.1.1 ({x} : Set ↥X.car) (z : Set ↥X.car)
          = wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀}.ncard := by
  classical
  set ι := VColBipBlk.incl (step7Set_subset X) with hι
  set γ := wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀ with hγ
  have hvx₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x₀} : Set ↥X.car) :=
    Or.inl ⟨x₀, hx₀.1, rfl⟩
  have hvx : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x} : Set ↥X.car) :=
    Or.inl ⟨x, hx.1, rfl⟩
  have hvB₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B₀ := Or.inr hB₀.1
  -- the middle set: the blocks of `D_j` of the right color
  have hpx : VColBipBlk.incl (step7Set_subset X) p ∈ dominantClass X := by
    rw [show VColBipBlk.incl (step7Set_subset X) p = x from hp]; exact hx
  set L : Set (Set ↥X.car) :=
    {A | A ∈ step7Blocks X ∧ wlRaw X.obj.1.1 ({x} : Set ↥X.car) A = γ} with hL
  have h1 : (fun B : Set ↥(step7Set X) => ι '' B) ''
      {B : Set ↥(step7Set X) | (p, B) ∈ (step8Obj X).E} = L := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨-, hBblk, hBcol⟩ := hB
      have hAblk : ι '' B ∈ step7Blocks X := by
        rw [← step7Obj_blocks_image X]
        exact ⟨B, hBblk, rfl⟩
      refine ⟨hAblk, ?_⟩
      have hBcol' : VColBipBlk.wlCaseColor X.obj.1.1 ({x} : Set ↥X.car) (ι '' B)
          = step8Color X := by rw [← hp]; exact hBcol
      exact (VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨hvx, Or.inr hAblk.1⟩ ⟨hvx₀, hvB₀⟩).1
        (by rw [hBcol', hwit])
    · rintro ⟨hAblk, hAcol⟩
      obtain ⟨B, hBblk, rfl⟩ : ∃ B ∈ (step7Obj X).blocks, ι '' B = A := by
        have : A ∈ (fun B : Set ↥(step7Set X) => ι '' B) '' (step7Obj X).blocks := by
          rw [step7Obj_blocks_image X]; exact hAblk
        exact this
      refine ⟨B, ⟨?_, hBblk, ?_⟩, rfl⟩
      · exact (step7Obj_part₁_iff X p).2 hpx
      · show VColBipBlk.wlCaseColor X.obj.1.1 ({ι p} : Set ↥X.car) (ι '' B) = step8Color X
        rw [hp]
        exact ((VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨hvx, Or.inr hAblk.1⟩
          ⟨hvx₀, hvB₀⟩).2 hAcol).trans hwit
  have h2 : (Subtype.val : ↥(step7Vtx X) → Set ↥X.car) ''
      {z : ↥(step7Vtx X) | wlRaw X.obj.1.1 ({x} : Set ↥X.car) (z : Set ↥X.car) = γ} = L := by
    ext A
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mem_step7Blocks_of_wlRaw_eq X hx₀ z.2 hB₀ hz, hz⟩
    · rintro ⟨hAblk, hAcol⟩
      exact ⟨⟨A, Or.inr hAblk⟩, hAcol, rfl⟩
  rw [← Set.ncard_image_of_injective _ (VColBipBlk.incl_image_injective (step7Set_subset X)),
    h1, ← h2, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The points of `W₁` joined to a block `B` of `D_j` by `R_i`. -/
theorem step8_inNbhd_ncard {x₀ : ↥X.car} (hx₀ : x₀ ∈ dominantClass X)
    {B₀ : Set ↥X.car} (hB₀ : B₀ ∈ step7Blocks X)
    (hwit : VColBipBlk.wlCaseColor X.obj.1.1 ({x₀} : Set ↥X.car) B₀ = step8Color X)
    {B : Set ↥(step7Set X)} (hB : B ∈ (step7Obj X).blocks) :
    {p : ↥(step7Set X) | (p, B) ∈ (step8Obj X).E}.ncard
      = {z : ↥(step7Vtx X) | wlRaw X.obj.1.1 (z : Set ↥X.car)
          (VColBipBlk.incl (step7Set_subset X) '' B)
          = wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀}.ncard := by
  classical
  set ι := VColBipBlk.incl (step7Set_subset X) with hι
  set γ := wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀ with hγ
  have hvx₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x₀} : Set ↥X.car) :=
    Or.inl ⟨x₀, hx₀.1, rfl⟩
  have hvB₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B₀ := Or.inr hB₀.1
  have hBblk : ι '' B ∈ step7Blocks X := by
    rw [← step7Obj_blocks_image X]; exact ⟨B, hB, rfl⟩
  have hvB : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks (ι '' B) := Or.inr hBblk.1
  set L : Set ↥X.car :=
    {y | y ∈ dominantClass X ∧ wlRaw X.obj.1.1 ({y} : Set ↥X.car) (ι '' B) = γ} with hL
  have h1 : ι '' {p : ↥(step7Set X) | (p, B) ∈ (step8Obj X).E} = L := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hq₁, -, hqcol⟩ := hq
      have hy : ι q ∈ dominantClass X := (step7Obj_part₁_iff X q).1 hq₁
      refine ⟨hy, ?_⟩
      exact (VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨Or.inl ⟨ι q, hy.1, rfl⟩, hvB⟩
        ⟨hvx₀, hvB₀⟩).1 (hqcol.trans hwit.symm)
    · rintro ⟨hy, hycol⟩
      refine ⟨⟨(y : Ω), ⟨y, Or.inl hy, rfl⟩⟩, ⟨?_, hB, ?_⟩, rfl⟩
      · exact (step7Obj_part₁_iff X _).2 hy
      · exact ((VColBipBlk.wlCaseColor_eq_iff X.obj.1.1
          ⟨Or.inl ⟨y, hy.1, rfl⟩, hvB⟩ ⟨hvx₀, hvB₀⟩).2 hycol).trans hwit
  have h2 : (fun y : ↥X.car => ({y} : Set ↥X.car)) '' L
      = (Subtype.val : ↥(step7Vtx X) → Set ↥X.car) ''
        {z : ↥(step7Vtx X) | wlRaw X.obj.1.1 (z : Set ↥X.car) (ι '' B) = γ} := by
    ext A
    constructor
    · rintro ⟨y, ⟨hy, hycol⟩, rfl⟩
      exact ⟨⟨{y}, Or.inl ⟨y, hy, rfl⟩⟩, hycol, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hzy⟩ := mem_step5Pts_of_wlRaw_eq X hx₀ z.2 hB₀ hz
      exact ⟨y, ⟨hy, by rw [← hzy]; exact hz⟩, hzy.symm⟩
  rw [← Set.ncard_image_of_injective _ (VColBipBlk.incl_injective (step7Set_subset X)), h1,
    ← Set.ncard_image_of_injective L Set.singleton_injective, h2,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-- §9.4, step 8.  *"(: `X` is semiregular … :)"*  The new graph `(V₁, V₂; R_i)` is
semiregular: `R_i` is one constituent of a coherent configuration in which `V₁` and `D_j`
are single vertex-color classes, so degree awareness (Obs. 3.3.5) makes all the degrees
inside `V₁` equal and all the degrees inside `D_j` equal. -/
theorem step8Obj_isSemiregular (h : ¬ AllClassesSmall X) : (step8Obj X).IsSemiregular := by
  classical
  obtain ⟨x₀, hx₀, B₀, hB₀, hwit⟩ := step8Color_mem X h
  have hcoh := step7Vtx_isCoherentColoring X
  constructor
  · refine ⟨{z : ↥(step7Vtx X) | wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) (z : Set ↥X.car)
        = wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀}.ncard, ?_⟩
    intro p hp
    have hx : VColBipBlk.incl (step7Set_subset X) p ∈ dominantClass X :=
      (step7Obj_part₁_iff X p).1 hp
    rw [step8_outNbhd_ncard X hx hx₀ hB₀ hwit rfl]
    exact WL.outDeg_eq_of_diag_eq hcoh
      (u := ⟨{VColBipBlk.incl (step7Set_subset X) p}, Or.inl ⟨_, hx, rfl⟩⟩)
      (u' := ⟨{x₀}, Or.inl ⟨x₀, hx₀, rfl⟩⟩) (step7Config_hom₁ X hx hx₀) _
  · refine ⟨{z : ↥(step7Vtx X) | wlRaw X.obj.1.1 (z : Set ↥X.car) B₀
        = wlRaw X.obj.1.1 ({x₀} : Set ↥X.car) B₀}.ncard, ?_⟩
    intro B hB
    have hBblk : VColBipBlk.incl (step7Set_subset X) '' B ∈ step7Blocks X := by
      rw [← step7Obj_blocks_image X]; exact ⟨B, hB, rfl⟩
    rw [step8_inNbhd_ncard X hx₀ hB₀ hwit hB]
    exact WL.inDeg_eq_of_diag_eq hcoh
      (u := ⟨VColBipBlk.incl (step7Set_subset X) '' B, Or.inr hBblk⟩)
      (u' := ⟨B₀, Or.inr hB₀⟩) (step7Config_hom₂ X hBblk hB₀) _

end Semiregular

/-! ### §9.4, step 8: *"its symmetry defect is `≥ 1/2` in each part by Prop. 2.4.30"* -/

section Defect

variable (X : Pt (BipBlockInputs Ω))

/-- A pair (point of `W₁`, block of `D_j`) of the configuration of step 7, read on the
point set `V₁ ∪ D_j` of step 7. -/
theorem exists_step8Pair {x : ↥X.car} (hx : x ∈ dominantClass X) {B : Set ↥X.car}
    (hB : B ∈ step7Blocks X) :
    ∃ p : ↥(step7Set X), ∃ Bs : Set ↥(step7Set X),
      (step7Obj X).part₁ p ∧ Bs ∈ (step7Obj X).blocks ∧
        VColBipBlk.incl (step7Set_subset X) p = x ∧
        VColBipBlk.incl (step7Set_subset X) '' Bs = B := by
  obtain ⟨Bs, hBs, hBsimg⟩ : ∃ Bs ∈ (step7Obj X).blocks,
      VColBipBlk.incl (step7Set_subset X) '' Bs = B := by
    have : B ∈ (fun A : Set ↥(step7Set X) => VColBipBlk.incl (step7Set_subset X) '' A) ''
        (step7Obj X).blocks := by rw [step7Obj_blocks_image X]; exact hB
    exact this
  refine ⟨⟨(x : Ω), ⟨x, Or.inl hx, rfl⟩⟩, Bs, ?_, hBs, rfl, hBsimg⟩
  exact (step7Obj_part₁_iff X _).2 hx

/-- §9.4, step 8.  *"(: `X` is semiregular, **nontrivial** … :)"*  The new graph is neither
empty nor complete: the color `i` occurs on the link, and the link has a second color
because `X₁₂` is nontrivial (step 7). -/
theorem step8Obj_not_isTrivial (h : ¬ AllClassesSmall X) : ¬ (step8Obj X).IsTrivial := by
  classical
  obtain ⟨x₀, hx₀, B₀, hB₀, hwit⟩ := step8Color_mem X h
  have hvx₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x₀} : Set ↥X.car) :=
    Or.inl ⟨x₀, hx₀.1, rfl⟩
  have hvB₀ : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B₀ := Or.inr hB₀.1
  rintro (hempty | hfull)
  · -- the chosen color occurs, so `R_i` is not empty
    obtain ⟨p, Bs, hp, hBs, hpx, hBsimg⟩ := exists_step8Pair X hx₀ hB₀
    have hmem : ((p, Bs) : ↥(step7Set X) × Set ↥(step7Set X)) ∈ (step8Obj X).E := by
      refine ⟨hp, hBs, ?_⟩
      rw [show VColBipBlk.incl (step7Set_subset X) (p, Bs).1 = x₀ from hpx,
        show VColBipBlk.incl (step7Set_subset X) '' (p, Bs).2 = B₀ from hBsimg]
      exact hwit
    rw [hempty] at hmem
    exact hmem
  · -- the link has a second color, so `R_i` is not the complete bipartite graph
    obtain ⟨x, hx, y, hy, B, hB, B', hB', hne⟩ := step7_link_nontrivial X h
    have hvx : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x} : Set ↥X.car) :=
      Or.inl ⟨x, hx.1, rfl⟩
    have hvy : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({y} : Set ↥X.car) :=
      Or.inl ⟨y, hy.1, rfl⟩
    have hvB : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B := Or.inr hB.1
    have hvB' : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks B' := Or.inr hB'.1
    -- one of the two pairs does not carry the color `i`
    obtain ⟨z, hz, C, hC, hzC⟩ : ∃ z ∈ dominantClass X, ∃ C ∈ step7Blocks X,
        VColBipBlk.wlCaseColor X.obj.1.1 ({z} : Set ↥X.car) C ≠ step8Color X := by
      by_contra hcon
      push_neg at hcon
      exact hne ((VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨hvx, hvB⟩ ⟨hvy, hvB'⟩).1
        ((hcon x hx B hB).trans (hcon y hy B' hB').symm))
    obtain ⟨p, Bs, hp, hBs, hpz, hBsimg⟩ := exists_step8Pair X hz hC
    have hmem : ((p, Bs) : ↥(step7Set X) × Set ↥(step7Set X))
        ∈ {q : ↥(step7Set X) × Set ↥(step7Set X) |
          (step8Obj X).part₁ q.1 ∧ q.2 ∈ (step8Obj X).blocks} := ⟨hp, hBs⟩
    rw [← hfull] at hmem
    refine hzC ?_
    have := hmem.2.2
    rw [show VColBipBlk.incl (step7Set_subset X) (p, Bs).1 = z from hpz,
      show VColBipBlk.incl (step7Set_subset X) '' (p, Bs).2 = C from hBsimg] at this
    exact this

/-- §9.4, step 8.  *"therefore its symmetry defect is `≥ 1/2` in each part by
Prop. 2.4.30"* (`Babai.VColBipBlk.half_le_defect₁`). -/
theorem half_le_step8Obj_defect₁ (h : ¬ AllClassesSmall X) [Fintype ↥(step7Set X)] :
    1 / 2 ≤ (step8Obj X).defect₁ :=
  VColBipBlk.half_le_defect₁ (step8Obj_isSemiregular X h) (step8Obj_not_isTrivial X h)

/-- §9.4, step 8.  **The graph `(V₁, V₂; R_i)` is again an admissible input of
Theorem 9.2.2** for the threshold `α_new` of step 5: the two parts are unchanged, so
`n₁ ≥ 2` and `n₂ < α_new n₁` are inherited from step 7, and the symmetry defect is at
least `1/2 ≥ 1 - α_new` because `α_new ≥ α ≥ 2/3`. -/
theorem step8Obj_isThm922Input (h : ¬ AllClassesSmall X) [Fintype ↥(step7Set X)] :
    (step8Obj X).IsThm922Input (alphaNew X) := by
  refine ⟨?_, step8Obj_numBlocks_lt X h, ?_⟩
  · rw [step8Obj_V₁_ncard]
    exact two_le_dominantClass_ncard h
  · have hdef : (1 : ℚ) / 2 ≤ (step8Obj X).defect₁ := half_le_step8Obj_defect₁ X h
    have hdefR : (1 : ℝ) / 2 ≤ ((step8Obj X).defect₁ : ℝ) := by
      have : ((1 / 2 : ℚ) : ℝ) ≤ ((step8Obj X).defect₁ : ℝ) := by exact_mod_cast hdef
      norm_num at this; linarith
    have hα : (2 : ℝ) / 3 ≤ BipBlockInputs.alpha X := X.obj.2.1
    have hnew : (2 : ℝ) / 3 ≤ alphaNew X := le_trans hα (alpha_le_alphaNew h)
    linarith

end Defect

/-! ### §9.4, step 8: *"Update `X ← WL refinement of `X`"* -/

section Refine

variable (X : Pt (BipBlockInputs Ω))

/-- The vertices of the new graph are the vertices of step 7, read on the point set
`V₁ ∪ D_j`. -/
theorem step8Vtx_image_mem {A : Set ↥(step7Set X)} (hA : A ∈ (step8Obj X).vtx) :
    VColBipBlk.incl (step7Set_subset X) '' A ∈ step7Vtx X := by
  rcases hA with ⟨p, hp, rfl⟩ | hA
  · exact Or.inl ⟨VColBipBlk.incl (step7Set_subset X) p, (step7Obj_part₁_iff X p).1 hp,
      Set.image_singleton⟩
  · exact Or.inr (by rw [← step7Obj_blocks_image X]; exact ⟨A, hA, rfl⟩)

theorem step8Vtx_image_surj {A : Set ↥X.car} (hA : A ∈ step7Vtx X) :
    ∃ B, ∃ hB : B ∈ (step8Obj X).vtx, VColBipBlk.incl (step7Set_subset X) '' B = A := by
  rcases hA with ⟨x, hx, rfl⟩ | hA
  · refine ⟨{⟨(x : Ω), ⟨x, Or.inl hx, rfl⟩⟩}, Or.inl ⟨_, ?_, rfl⟩, Set.image_singleton⟩
    exact (step7Obj_part₁_iff X _).2 hx
  · obtain ⟨B, hB, hBimg⟩ : ∃ B ∈ (step7Obj X).blocks,
        VColBipBlk.incl (step7Set_subset X) '' B = A := by
      have : A ∈ (fun C : Set ↥(step7Set X) => VColBipBlk.incl (step7Set_subset X) '' C) ''
          (step7Obj X).blocks := by rw [step7Obj_blocks_image X]; exact hA
      exact this
    exact ⟨B, Or.inr hB, hBimg⟩

/-- The vertices of the new graph and the vertices of step 7 are in bijection. -/
noncomputable def step8VtxEquiv : ↥((step8Obj X).vtx) ≃ ↥(step7Vtx X) :=
  Equiv.ofBijective
    (fun A => ⟨VColBipBlk.incl (step7Set_subset X) '' (A : Set ↥(step7Set X)),
      step8Vtx_image_mem X A.2⟩)
    ⟨fun A B hAB => Subtype.ext (VColBipBlk.incl_image_injective (step7Set_subset X)
        (congrArg Subtype.val hAB)),
     fun A => by
       obtain ⟨B, hB, hBimg⟩ := step8Vtx_image_surj X A.2
       exact ⟨⟨B, hB⟩, Subtype.ext hBimg⟩⟩

@[simp] theorem step8VtxEquiv_val (A : ↥((step8Obj X).vtx)) :
    ((step8VtxEquiv X A : ↥(step7Vtx X)) : Set ↥X.car)
      = VColBipBlk.incl (step7Set_subset X) '' (A : Set ↥(step7Set X)) := rfl

/-- §9.4, step 8.  **The configuration of step 7, read on the vertices of the new
graph.**  This is the coloring that the new refinement is compared with. -/
noncomputable def step8Old (X : Pt (BipBlockInputs Ω)) (u v : ↥((step8Obj X).vtx)) :
    WL.colorType ℕ (wlRounds Ω) :=
  wlRaw X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' (u : Set ↥(step7Set X)))
    (VColBipBlk.incl (step7Set_subset X) '' (v : Set ↥(step7Set X)))

theorem step8Old_isCoherentColoring : WL.IsCoherentColoring (step8Old X) :=
  WL.isCoherentColoring_comp_equiv (step8VtxEquiv X) (step7Vtx_isCoherentColoring X)

/-- Observation 4.3.1: the configuration of step 7 is stable. -/
theorem step8Old_isStable : WL.IsStable (step8Old X) :=
  (WL.isStable_iff_isCoherentColoring (step8Old_isCoherentColoring X).1).2
    (step8Old_isCoherentColoring X)

/-- The vertex color of the new graph at a vertex is the vertex color of the old
configuration at the corresponding vertex: the first part, the blocks and the two colorings
are unchanged by step 8. -/
theorem initVtxColor_step8Obj {A : Set ↥(step7Set X)} (hA : A ∈ (step8Obj X).vtx) :
    VColBipBlk.initVtxColor (step8Obj X) A
      = VColBipBlk.initVtxColor X.obj.1.1
        (VColBipBlk.incl (step7Set_subset X) '' A) := by
  classical
  rcases hA with ⟨p, hp, rfl⟩ | hA
  · have hp' : X.obj.1.1.part₁ (VColBipBlk.incl (step7Set_subset X) p) := hp
    rw [VColBipBlk.initVtxColor, VColBipBlk.initVtxColor, if_pos ⟨p, hp, rfl⟩,
      if_pos ⟨VColBipBlk.incl (step7Set_subset X) p, hp', Set.image_singleton⟩,
      Set.image_singleton, Set.image_singleton, Set.image_singleton]
    rfl
  · have hAbig : VColBipBlk.incl (step7Set_subset X) '' A ∈ X.obj.1.1.blocks := hA
    have hns : ¬ ∃ p, (step8Obj X).part₁ p ∧ A = {p} := by
      rintro ⟨p, hp, rfl⟩
      exact X.obj.1.1.blocks_off₁ _ hAbig (VColBipBlk.incl (step7Set_subset X) p)
        (by rw [Set.image_singleton]; rfl) hp
    have hnsbig : ¬ ∃ x, X.obj.1.1.part₁ x
        ∧ VColBipBlk.incl (step7Set_subset X) '' A = {x} := by
      rintro ⟨x, hx, hAx⟩
      exact X.obj.1.1.blocks_off₁ _ hAbig x (by rw [hAx]; rfl) hx
    rw [VColBipBlk.initVtxColor, VColBipBlk.initVtxColor, if_neg hns, if_neg hnsbig,
      if_pos hA, if_pos hAbig]
    show Nat.pair 2 (if VColBipBlk.incl (step7Set_subset X) '' A ∈ X.obj.1.1.blocks then
      X.obj.1.1.g (VColBipBlk.incl (step7Set_subset X) '' A) else 0) = _
    rw [if_pos hAbig]

/-- A vertex of the new graph that carries the old vertex color of a point of `V₁` is a
point of `V₁` (Obs. 3.3.4 for the old configuration). -/
theorem step8_isPt_of_diag_eq {A A' : Set ↥(step7Set X)} (hA' : A' ∈ (step8Obj X).vtx)
    {p : ↥(step7Set X)} (hp : (step8Obj X).part₁ p) (hAp : A = {p})
    (hdiag : wlRaw X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' A)
        (VColBipBlk.incl (step7Set_subset X) '' A)
      = wlRaw X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' A')
        (VColBipBlk.incl (step7Set_subset X) '' A')) :
    ∃ p', (step8Obj X).part₁ p' ∧ A' = {p'} := by
  rcases hA' with hA' | hA'
  · exact hA'
  · exfalso
    set ι := VColBipBlk.incl (step7Set_subset X) with hι
    have hpbig : X.obj.1.1.part₁ (ι p) := hp
    have hA'big : ι '' A' ∈ X.obj.1.1.blocks := hA'
    have hvp : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({ι p} : Set ↥X.car) :=
      Or.inl ⟨ι p, hpbig, rfl⟩
    have hvA' : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks (ι '' A') := Or.inr hA'big
    rw [hAp, Set.image_singleton] at hdiag
    exact X.obj.1.1.wlColor_ne_of_part₁_blocks hpbig hA'big
      (X.obj.1.1.wlColor_eq_of_wlRaw_eq ⟨hvp, hvp⟩ ⟨hvA', hvA'⟩ hdiag)

/-- The edge indicator of the new graph is determined by the old color of the pair: an
edge of `R_i` is a pair (point of `V₁`, block of `D_j`) carrying the color `i`, and all
three conditions are read off the old color (Obs. 3.3.4 for the first two). -/
theorem initEdge_step8Obj_eq {A B A' B' : Set ↥(step7Set X)} (hA : A ∈ (step8Obj X).vtx)
    (hB : B ∈ (step8Obj X).vtx) (hA' : A' ∈ (step8Obj X).vtx) (hB' : B' ∈ (step8Obj X).vtx)
    (h : step8Old X ⟨A, hA⟩ ⟨B, hB⟩ = step8Old X ⟨A', hA'⟩ ⟨B', hB'⟩) :
    VColBipBlk.initEdge (step8Obj X) A B = VColBipBlk.initEdge (step8Obj X) A' B' := by
  classical
  set ι := VColBipBlk.incl (step7Set_subset X) with hι
  -- the statement is symmetric in the two pairs, so one implication suffices
  have key : ∀ (C D C' D' : Set ↥(step7Set X)), C ∈ (step8Obj X).vtx → D ∈ (step8Obj X).vtx →
      C' ∈ (step8Obj X).vtx → D' ∈ (step8Obj X).vtx →
      wlRaw X.obj.1.1 (ι '' C) (ι '' D) = wlRaw X.obj.1.1 (ι '' C') (ι '' D') →
      VColBipBlk.initEdge (step8Obj X) C D = 1 →
      VColBipBlk.initEdge (step8Obj X) C' D' = 1 := by
    intro C D C' D' hC hD hC' hD' hcol hone
    obtain ⟨p, hp, hCp, hpD⟩ : ∃ p, (step8Obj X).part₁ p ∧ C = {p} ∧ (p, D) ∈ (step8Obj X).E := by
      by_contra hcon
      rw [VColBipBlk.initEdge, if_neg hcon] at hone
      exact absurd hone (by norm_num)
    obtain ⟨-, hDblk, hcolD⟩ := hpD
    -- the tail of the image pair is again a point of `V₁`
    have hdiagC := WL.diag_fst_eq_of_eq (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1) hcol
    obtain ⟨p', hp', hC'p⟩ := step8_isPt_of_diag_eq X hC' hp hCp hdiagC
    -- the head of the image pair is again a block of `D_j`
    have hdiagD := WL.diag_snd_eq_of_eq (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1) hcol
    have hD'blk : D' ∈ (step8Obj X).blocks := by
      rcases hD' with ⟨q, hq, hDq⟩ | hD'
      · exfalso
        have hqbig : X.obj.1.1.part₁ (ι q) := hq
        have hDbig : ι '' D ∈ X.obj.1.1.blocks := hDblk
        have hvq : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({ι q} : Set ↥X.car) :=
          Or.inl ⟨ι q, hqbig, rfl⟩
        have hvD : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks (ι '' D) := Or.inr hDbig
        rw [hDq, Set.image_singleton] at hdiagD
        exact X.obj.1.1.wlColor_ne_of_part₁_blocks hqbig hDbig
          (X.obj.1.1.wlColor_eq_of_wlRaw_eq ⟨hvq, hvq⟩ ⟨hvD, hvD⟩ hdiagD.symm)
      · exact hD'
    -- and the pair carries the color `i`
    have hpbig : X.obj.1.1.part₁ (ι p) := hp
    have hp'big : X.obj.1.1.part₁ (ι p') := hp'
    have hDbig : ι '' D ∈ X.obj.1.1.blocks := hDblk
    have hD'big : ι '' D' ∈ X.obj.1.1.blocks := hD'blk
    have hvp : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({ι p} : Set ↥X.car) :=
      Or.inl ⟨ι p, hpbig, rfl⟩
    have hvp' : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({ι p'} : Set ↥X.car) :=
      Or.inl ⟨ι p', hp'big, rfl⟩
    have hcol' : wlRaw X.obj.1.1 ({ι p} : Set ↥X.car) (ι '' D)
        = wlRaw X.obj.1.1 ({ι p'} : Set ↥X.car) (ι '' D') := by
      rw [← Set.image_singleton (f := ι), ← Set.image_singleton (f := ι), ← hCp, ← hC'p]
      exact hcol
    have hcase := (VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨hvp, Or.inr hDbig⟩
      ⟨hvp', Or.inr hD'big⟩).2 hcol'
    have hE' : ((p', D') : ↥(step7Set X) × Set ↥(step7Set X)) ∈ (step8Obj X).E := by
      refine ⟨hp', hD'blk, ?_⟩
      show VColBipBlk.wlCaseColor X.obj.1.1 ({ι p'} : Set ↥X.car) (ι '' D') = step8Color X
      rw [← hcase]
      exact hcolD
    rw [VColBipBlk.initEdge, if_pos ⟨p', hp', hC'p, hE'⟩]
  have hdic : ∀ C D : Set ↥(step7Set X),
      VColBipBlk.initEdge (step8Obj X) C D = 1 ∨ VColBipBlk.initEdge (step8Obj X) C D = 0 := by
    intro C D
    rw [VColBipBlk.initEdge]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hdic A B with h1 | h0
  · rw [h1, key A B A' B' hA hB hA' hB' h h1]
  · rcases hdic A' B' with h1' | h0'
    · rw [key A' B' A B hA' hB' hA hB h.symm h1'] at h0
      exact absurd h0 (by norm_num)
    · rw [h0, h0']


/-- §9.4, step 8.  **The configuration of step 7 refines the input coloring of the new
refinement**: the new graph is `(V₁, V₂; R_i)`, whose parts, vertex colors and edges are
all read off the colors of the configuration of step 7. -/
theorem initColor_step8Obj_eq (u v u' v' : ↥((step8Obj X).vtx))
    (h : step8Old X u v = step8Old X u' v') :
    VColBipBlk.initColor (step8Obj X) (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X))
      = VColBipBlk.initColor (step8Obj X) (u' : Set ↥(step7Set X))
        (v' : Set ↥(step7Set X)) := by
  classical
  set ι := VColBipBlk.incl (step7Set_subset X) with hι
  have hcfg := (VColBipBlk.isCoherentColoring_wlRaw X.obj.1.1).1
  -- the diagonal is determined
  have hdiag : ∀ a b a' b' : ↥((step8Obj X).vtx), step8Old X a b = step8Old X a' b' →
      a' = b' → a = b := by
    intro a b a' b' hab hab'
    subst hab'
    exact Subtype.ext (VColBipBlk.incl_image_injective (step7Set_subset X)
      (hcfg.1 (ι '' (a : Set ↥(step7Set X))) (ι '' (b : Set ↥(step7Set X)))
        (ι '' (a' : Set ↥(step7Set X))) hab))
  by_cases huv : u = v
  · have huv' : u' = v' := hdiag u' v' u v h.symm huv
    subst huv; subst huv'
    have hinit := VColBipBlk.initColor_eq_of_wlRaw_eq X.obj.1.1 h
    rw [VColBipBlk.initColor, VColBipBlk.initColor, if_pos rfl, if_pos rfl] at hinit ⊢
    rw [initVtxColor_step8Obj X u.2, initVtxColor_step8Obj X u'.2,
      (Nat.pair_eq_pair.1 hinit).2]
  · have huv' : u' ≠ v' := fun hc => huv (hdiag u v u' v' h hc)
    have hne : (u : Set ↥(step7Set X)) ≠ (v : Set ↥(step7Set X)) :=
      fun hc => huv (Subtype.ext hc)
    have hne' : (u' : Set ↥(step7Set X)) ≠ (v' : Set ↥(step7Set X)) :=
      fun hc => huv' (Subtype.ext hc)
    have hconv : step8Old X v u = step8Old X v' u' :=
      hcfg.2 (ι '' (u : Set ↥(step7Set X))) (ι '' (v : Set ↥(step7Set X)))
        (ι '' (u' : Set ↥(step7Set X))) (ι '' (v' : Set ↥(step7Set X))) h
    -- the hint is read off the configuration of step 7 as well: the initial coloring of
    -- step 3 records `h` on the off-diagonal pairs, and `step8Old` refines it.
    have hιne : ι '' (u : Set ↥(step7Set X)) ≠ ι '' (v : Set ↥(step7Set X)) := fun hc =>
      hne (VColBipBlk.incl_image_injective (step7Set_subset X) hc)
    have hιne' : ι '' (u' : Set ↥(step7Set X)) ≠ ι '' (v' : Set ↥(step7Set X)) := fun hc =>
      hne' (VColBipBlk.incl_image_injective (step7Set_subset X) hc)
    have hhint := VColBipBlk.h_eq_of_initColor_eq hιne hιne'
      (VColBipBlk.initColor_eq_of_wlRaw_eq X.obj.1.1 h)
    have hh1 : (step8Obj X).h (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X))
        = (step8Obj X).h (u' : Set ↥(step7Set X)) (v' : Set ↥(step7Set X)) := hhint.1
    have hh2 : (step8Obj X).h (v : Set ↥(step7Set X)) (u : Set ↥(step7Set X))
        = (step8Obj X).h (v' : Set ↥(step7Set X)) (u' : Set ↥(step7Set X)) := hhint.2
    rw [VColBipBlk.initColor, VColBipBlk.initColor, if_neg hne, if_neg hne',
      initEdge_step8Obj_eq X u.2 v.2 u'.2 v'.2 h,
      initEdge_step8Obj_eq X v.2 u.2 v'.2 u'.2 hconv, hh1, hh2]

/-- §9.4, step 8.  *"Update `X ← WL refinement of `X`."*  The WL refinement of the graph
`(V₁, V₂; R_i)`, run on its vertex set `V₁ ∪ V₂`, for the number of rounds fixed in
step 3. -/
noncomputable def step8Raw (X : Pt (BipBlockInputs Ω)) :
    ↥((step8Obj X).vtx) → ↥((step8Obj X).vtx) → WL.colorType ℕ (wlRounds Ω) :=
  WL.iter (fun u v : ↥((step8Obj X).vtx) =>
    VColBipBlk.initColor (step8Obj X) (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X)))
    (wlRounds Ω)

theorem step8Init_isConfigColoring :
    WL.IsConfigColoring (fun u v : ↥((step8Obj X).vtx) =>
      VColBipBlk.initColor (step8Obj X) (u : Set ↥(step7Set X))
        (v : Set ↥(step7Set X))) := by
  obtain ⟨h1, h2⟩ := VColBipBlk.isConfigColoring_initColor (step8Obj X)
  exact ⟨fun x y z hxy => Subtype.ext (h1 _ _ _ hxy), fun u v x y huv => h2 _ _ _ _ huv⟩

/-- The fixed number of rounds of step 3 is enough for the vertex set of the new graph. -/
theorem card_step8Vtx_le :
    Nat.card ((↥((step8Obj X).vtx) × ↥((step8Obj X).vtx))
      × (↥((step8Obj X).vtx) × ↥((step8Obj X).vtx))) ≤ wlRounds Ω := by
  have hinj : Function.Injective (fun A : ↥((step8Obj X).vtx) =>
      (Subtype.val '' (A : Set ↥(step7Set X)) : Set Ω)) := by
    intro A B hAB
    exact Subtype.ext (Set.image_injective.2 Subtype.val_injective hAB)
  have h : Nat.card ↥((step8Obj X).vtx) ≤ Nat.card (Set Ω) :=
    Nat.card_le_card_of_injective _ hinj
  simp only [wlRounds, Nat.card_prod]
  exact Nat.mul_le_mul (Nat.mul_le_mul h h) (Nat.mul_le_mul h h)

/-- §9.4, step 8.  *"Let `X = (V; R₁, …, R_r)` denote the resulting CC"*, for the new
graph: the refinement is coherent. -/
theorem step8Raw_isCoherentColoring : WL.IsCoherentColoring (step8Raw X) :=
  WL.isCoherentColoring_iter_of_card_le (step8Init_isConfigColoring X) (card_step8Vtx_le X)

/-- §9.4, step 8.  **"The only effect of this is that it may merge some of the edge-color
classes in `X`":** the configuration of step 7 refines the new refinement.

The configuration of step 7 is stable (Obs. 4.3.1) and refines the input coloring of the
new refinement (`Babai.initColor_step8Obj_eq`), and WL refinement gives the coarsest stable
refinement of its input (`Babai.WL.stable_refines_iter`). -/
theorem step8Raw_eq_of_step8Old_eq (u v u' v' : ↥((step8Obj X).vtx))
    (h : step8Old X u v = step8Old X u' v') : step8Raw X u v = step8Raw X u' v' :=
  WL.stable_refines_iter (step8Old_isStable X) (fun a b a' b' hab =>
    initColor_step8Obj_eq X a b a' b' hab) (wlRounds Ω) u v u' v' h

/-- The new refinement refines the input coloring of the new graph. -/
theorem initColor_eq_of_step8Raw_eq {u v u' v' : ↥((step8Obj X).vtx)}
    (h : step8Raw X u v = step8Raw X u' v') :
    VColBipBlk.initColor (step8Obj X) (u : Set ↥(step7Set X)) (v : Set ↥(step7Set X))
      = VColBipBlk.initColor (step8Obj X) (u' : Set ↥(step7Set X))
        (v' : Set ↥(step7Set X)) :=
  WL.iter_isRefinement_le _ (Nat.zero_le _) u v u' v' h

end Refine

/-! ### §9.4, step 8: the two parts of the new configuration

*"`X` bihomogeneous"* survives step 8: the new refinement is coarser than the
configuration of step 7, in which `V₁` and `D_j` are single vertex-color classes, and the
input coloring of the new refinement still tells a point of `V₁` from a block. -/

section Parts

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 8.  **The coherent configuration after step 8**: the colors of the new
refinement, named in the order of the integer WL colors. -/
noncomputable def step8Config (X : Pt (BipBlockInputs Ω)) :
    PartitionStructure ↥((step8Obj X).vtx) :=
  VColBipBlk.wlConfig (step8Obj X)

theorem step8Config_isCoherent : (step8Config X).IsCoherent :=
  VColBipBlk.wlConfig_isCoherent (step8Obj X)

theorem step8Config_color_eq_iff (u v u' v' : ↥((step8Obj X).vtx)) :
    (step8Config X).natColor u v = (step8Config X).natColor u' v'
      ↔ step8Raw X u v = step8Raw X u' v' :=
  ((step8Config X).natColor_eq_iff u v u' v').trans
    ((VColBipBlk.wlConfig_color_eq_iff (step8Obj X) u v u' v').trans
      (VColBipBlk.carrier_wlRaw (step8Obj X) u v u' v'))

theorem step8Config_raw_eq_iff (u v u' v' : ↥((step8Obj X).vtx)) :
    (step8Config X).color u v = (step8Config X).color u' v' ↔
      step8Raw X u v = step8Raw X u' v' :=
  ((step8Config X).natColor_eq_iff u v u' v').symm.trans
    (step8Config_color_eq_iff X u v u' v')

theorem step8Config_vcolor_eq_iff (u v : ↥((step8Obj X).vtx)) :
    (step8Config X).vcolor u = (step8Config X).vcolor v
      ↔ step8Raw X u u = step8Raw X v v :=
  ((step8Config X).natColor_eq_iff u u v v).symm.trans
    (step8Config_color_eq_iff X u u v v)

/-- §9.4, step 8.  The first part `V₁` of the new configuration. -/
def step8Pts (X : Pt (BipBlockInputs Ω)) : Set ↥((step8Obj X).vtx) :=
  {u | ∃ p, (step8Obj X).part₁ p ∧ (u : Set ↥(step7Set X)) = {p}}

/-- §9.4, step 8.  The second part `V₂` of the new configuration. -/
def step8Blks (X : Pt (BipBlockInputs Ω)) : Set ↥((step8Obj X).vtx) :=
  {u | (u : Set ↥(step7Set X)) ∈ (step8Obj X).blocks}

theorem step8Pts_union_step8Blks (u : ↥((step8Obj X).vtx)) :
    u ∈ step8Pts X ∨ u ∈ step8Blks X := u.2

/-- §9.4, step 8, *"`X₁` remains homogeneous"*: the new refinement is coarser than the
configuration of step 7, in which all the points of `V₁` carry one vertex color. -/
theorem step8Raw_hom₁ {u v : ↥((step8Obj X).vtx)} (hu : u ∈ step8Pts X)
    (hv : v ∈ step8Pts X) : step8Raw X u u = step8Raw X v v := by
  obtain ⟨p, hp, hup⟩ := hu
  obtain ⟨q, hq, hvq⟩ := hv
  refine step8Raw_eq_of_step8Old_eq X u u v v ?_
  show wlRaw X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' (u : Set ↥(step7Set X)))
      (VColBipBlk.incl (step7Set_subset X) '' (u : Set ↥(step7Set X)))
    = wlRaw X.obj.1.1 (VColBipBlk.incl (step7Set_subset X) '' (v : Set ↥(step7Set X)))
      (VColBipBlk.incl (step7Set_subset X) '' (v : Set ↥(step7Set X)))
  rw [hup, hvq, Set.image_singleton, Set.image_singleton]
  exact step7Config_hom₁ X ((step7Obj_part₁_iff X p).1 hp) ((step7Obj_part₁_iff X q).1 hq)

/-- §9.4, step 8, *"`X₂` remains homogeneous"*: same argument, with the blocks of `D_j`,
which form one vertex-color class of the configuration of step 7. -/
theorem step8Raw_hom₂ {u v : ↥((step8Obj X).vtx)} (hu : u ∈ step8Blks X)
    (hv : v ∈ step8Blks X) : step8Raw X u u = step8Raw X v v := by
  have hu' : VColBipBlk.incl (step7Set_subset X) '' (u : Set ↥(step7Set X)) ∈ step7Blocks X := by
    rw [← step7Obj_blocks_image X]; exact ⟨(u : Set ↥(step7Set X)), hu, rfl⟩
  have hv' : VColBipBlk.incl (step7Set_subset X) '' (v : Set ↥(step7Set X)) ∈ step7Blocks X := by
    rw [← step7Obj_blocks_image X]; exact ⟨(v : Set ↥(step7Set X)), hv, rfl⟩
  exact step8Raw_eq_of_step8Old_eq X u u v v (step7Config_hom₂ X hu' hv')

/-- §9.4, step 8.  **A point of `V₁` and a block never carry the same vertex color** in the
new configuration: the input coloring of the new refinement already tells them apart, and
the refinement refines it. -/
theorem step8Raw_vcolor_ne {u v : ↥((step8Obj X).vtx)} (hu : u ∈ step8Pts X)
    (hv : v ∈ step8Blks X) : step8Raw X u u ≠ step8Raw X v v := by
  classical
  intro hc
  obtain ⟨p, hp, hup⟩ := hu
  have hinit := initColor_eq_of_step8Raw_eq X hc
  rw [VColBipBlk.initColor, VColBipBlk.initColor, if_pos rfl, if_pos rfl] at hinit
  have hvtx := (Nat.pair_eq_pair.1 hinit).2
  have hns : ¬ ∃ q, (step8Obj X).part₁ q ∧ (v : Set ↥(step7Set X)) = {q} := by
    rintro ⟨q, hq, hvq⟩
    exact (step8Obj X).blocks_off₁ _ hv q (by rw [hvq]; rfl) hq
  rw [VColBipBlk.initVtxColor, VColBipBlk.initVtxColor, if_pos ⟨p, hp, hup⟩, if_neg hns,
    if_pos (show (v : Set ↥(step7Set X)) ∈ (step8Obj X).blocks from hv)] at hvtx
  exact absurd (Nat.pair_eq_pair.1 hvtx).1 (by norm_num)

/-- §9.4, step 8, *"(: `X` is bihomogeneous :)"*: **the two parts are exactly the two
vertex-color classes of the new configuration.** -/
theorem step8Config_parts (h : ¬ AllClassesSmall X) :
    ∃ i j : Fin (step8Config X).rank, i ≠ j ∧
      step8Pts X = (step8Config X).vertexClass i ∧
      step8Blks X = (step8Config X).vertexClass j ∧
      ∀ u : ↥((step8Obj X).vtx),
        u ∈ (step8Config X).vertexClass i ∨ u ∈ (step8Config X).vertexClass j := by
  classical
  -- a point of `V₁` and a block of `D_j`
  obtain ⟨x₀, hx₀⟩ : (dominantClass X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    have := two_le_dominantClass_ncard h
    rw [hc, Set.ncard_empty] at this
    omega
  obtain ⟨B₀, hB₀⟩ := step7Blocks_nonempty X h
  obtain ⟨p₀, Bs₀, hp₀, hBs₀, -, -⟩ := exists_step8Pair X hx₀ hB₀
  set u₀ : ↥((step8Obj X).vtx) := ⟨{p₀}, Or.inl ⟨p₀, hp₀, rfl⟩⟩ with hu₀
  set v₀ : ↥((step8Obj X).vtx) := ⟨Bs₀, Or.inr hBs₀⟩ with hv₀
  have hu₀mem : u₀ ∈ step8Pts X := ⟨p₀, hp₀, rfl⟩
  have hv₀mem : v₀ ∈ step8Blks X := hBs₀
  refine ⟨(step8Config X).vcolor u₀, (step8Config X).vcolor v₀, ?_, ?_, ?_, ?_⟩
  · intro hc
    exact step8Raw_vcolor_ne X hu₀mem hv₀mem ((step8Config_vcolor_eq_iff X u₀ v₀).1 hc)
  · ext u
    simp only [PartitionStructure.vertexClass, Set.mem_setOf_eq]
    constructor
    · intro hu
      exact (step8Config_vcolor_eq_iff X u u₀).2 (step8Raw_hom₁ X hu hu₀mem)
    · intro hu
      rcases step8Pts_union_step8Blks X u with hp | hb
      · exact hp
      · exact absurd ((step8Config_vcolor_eq_iff X u u₀).1 hu)
          (fun hcc => step8Raw_vcolor_ne X hu₀mem hb hcc.symm)
  · ext u
    simp only [PartitionStructure.vertexClass, Set.mem_setOf_eq]
    constructor
    · intro hu
      exact (step8Config_vcolor_eq_iff X u v₀).2 (step8Raw_hom₂ X hu hv₀mem)
    · intro hu
      rcases step8Pts_union_step8Blks X u with hp | hb
      · exact absurd ((step8Config_vcolor_eq_iff X u v₀).1 hu)
          (step8Raw_vcolor_ne X hp hv₀mem)
      · exact hb
  · intro u
    rcases step8Pts_union_step8Blks X u with hp | hb
    · exact Or.inl ((step8Config_vcolor_eq_iff X u u₀).2 (step8Raw_hom₁ X hp hu₀mem))
    · exact Or.inr ((step8Config_vcolor_eq_iff X u v₀).2 (step8Raw_hom₂ X hb hv₀mem))

/-- §9.4, step 8, *"`X₁₂` remains nontrivial (because `R_i` remains one of its
constituents)"*: the new refinement refines the edge relation `R_i`, and `R_i` is neither
empty nor all of `V₁ × V₂` (`Babai.step8Obj_not_isTrivial`), so the link carries at least
two colors. -/
theorem step8_link_nontrivial (h : ¬ AllClassesSmall X) :
    ∃ u₁ ∈ step8Pts X, ∃ v₁ ∈ step8Blks X, ∃ u₂ ∈ step8Pts X, ∃ v₂ ∈ step8Blks X,
      step8Raw X u₁ v₁ ≠ step8Raw X u₂ v₂ := by
  classical
  -- an edge of `R_i`
  obtain ⟨x₀, hx₀, B₀, hB₀, hwit⟩ := step8Color_mem X h
  obtain ⟨p₀, Bs₀, hp₀, hBs₀, hp₀x, hBs₀img⟩ := exists_step8Pair X hx₀ hB₀
  have hE₀ : ((p₀, Bs₀) : ↥(step7Set X) × Set ↥(step7Set X)) ∈ (step8Obj X).E := by
    refine ⟨hp₀, hBs₀, ?_⟩
    rw [show VColBipBlk.incl (step7Set_subset X) (p₀, Bs₀).1 = x₀ from hp₀x,
      show VColBipBlk.incl (step7Set_subset X) '' (p₀, Bs₀).2 = B₀ from hBs₀img]
    exact hwit
  -- a non-edge
  obtain ⟨z, hz, C, hC, hzC⟩ : ∃ z ∈ dominantClass X, ∃ C ∈ step7Blocks X,
      VColBipBlk.wlCaseColor X.obj.1.1 ({z} : Set ↥X.car) C ≠ step8Color X := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx, y, hy, B, hB, B', hB', hne⟩ := step7_link_nontrivial X h
    have hvx : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({x} : Set ↥X.car) :=
      Or.inl ⟨x, hx.1, rfl⟩
    have hvy : IsVertexOn X.obj.1.1.part₁ X.obj.1.1.blocks ({y} : Set ↥X.car) :=
      Or.inl ⟨y, hy.1, rfl⟩
    exact hne ((VColBipBlk.wlCaseColor_eq_iff X.obj.1.1 ⟨hvx, Or.inr hB.1⟩
      ⟨hvy, Or.inr hB'.1⟩).1 ((hcon x hx B hB).trans (hcon y hy B' hB').symm))
  obtain ⟨p₁, Bs₁, hp₁, hBs₁, hp₁z, hBs₁img⟩ := exists_step8Pair X hz hC
  have hE₁ : ((p₁, Bs₁) : ↥(step7Set X) × Set ↥(step7Set X)) ∉ (step8Obj X).E := by
    rintro ⟨-, -, hcol⟩
    refine hzC ?_
    rw [show VColBipBlk.incl (step7Set_subset X) (p₁, Bs₁).1 = z from hp₁z,
      show VColBipBlk.incl (step7Set_subset X) '' (p₁, Bs₁).2 = C from hBs₁img] at hcol
    exact hcol
  refine ⟨⟨{p₀}, Or.inl ⟨p₀, hp₀, rfl⟩⟩, ⟨p₀, hp₀, rfl⟩, ⟨Bs₀, Or.inr hBs₀⟩, hBs₀,
    ⟨{p₁}, Or.inl ⟨p₁, hp₁, rfl⟩⟩, ⟨p₁, hp₁, rfl⟩, ⟨Bs₁, Or.inr hBs₁⟩, hBs₁, ?_⟩
  intro hcc
  have hinit := initColor_eq_of_step8Raw_eq X hcc
  have hne₀ : ({p₀} : Set ↥(step7Set X)) ≠ Bs₀ := fun hcp =>
    (step8Obj X).blocks_off₁ _ hBs₀ p₀ (by rw [← hcp]; rfl) hp₀
  have hne₁ : ({p₁} : Set ↥(step7Set X)) ≠ Bs₁ := fun hcp =>
    (step8Obj X).blocks_off₁ _ hBs₁ p₁ (by rw [← hcp]; rfl) hp₁
  rw [VColBipBlk.initColor, VColBipBlk.initColor, if_neg hne₀, if_neg hne₁] at hinit
  have hedge := (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 hinit).2).1).1
  rw [VColBipBlk.initEdge, VColBipBlk.initEdge, if_pos ⟨p₀, hp₀, rfl, hE₀⟩,
    if_neg ?_] at hedge
  · exact absurd hedge (by norm_num)
  · rintro ⟨q, hq, hqe, hqE⟩
    exact hE₁ (by rw [show p₁ = q from Set.singleton_eq_singleton_iff.1 hqe]; exact hqE)

end Parts

/-! ### §9.4, step 8: *"`X₁` remains a UPCC by Claim above"*, the primitivity

Coarsening the coloring cannot disconnect an off-diagonal constituent: each off-diagonal
color class of the coarser configuration is a union of off-diagonal color classes of the
finer one, and one of those spanning subgraphs is already weakly connected. -/

namespace Digraph

/-- Weak connectivity is inherited by a digraph with more edges, across a renaming of the
vertices: a weak walk of `Y` is carried to a weak walk of `Z`. -/
theorem isWeaklyConnected_of_equiv {V V' : Type*} (e : V ≃ V') {Y : Digraph V}
    {Z : Digraph V'} (hmap : ∀ x y : V, Y.Adj x y → Z.Adj (e x) (e y))
    (hY : Y.IsWeaklyConnected) : Z.IsWeaklyConnected := by
  intro u v
  have h1 := hY (e.symm u) (e.symm v)
  rw [Digraph.accessible_iff_reflTransGen] at h1 ⊢
  have hlift : ∀ a b : V, Y.symmetrization.Adj a b → Z.symmetrization.Adj (e a) (e b) := by
    intro a b hab
    rcases hab with hab | hab
    · exact Or.inl (hmap a b hab)
    · exact Or.inr (hmap b a hab)
  have h2 := Relation.ReflTransGen.lift (fun x : V => e x) hlift h1
  simpa using h2

end Digraph

namespace PartitionStructure

/-- **Primitivity survives a coarsening of the coloring.**  If the color classes of `Y'`
are unions of color classes of a primitive `Y` — across a renaming `e` of the points — and
`Y'` is homogeneous, then `Y'` is primitive.

This is the argument behind *"`X₁` remains a UPCC by Claim above"* in step 8 of §9.4, for
the primitivity half: an off-diagonal color of `Y'` contains an off-diagonal color of `Y`,
whose constituent is a connected spanning subgraph, so the constituent of `Y'` is connected
too.  (Uniprimitivity itself does **not** survive coarsening: the rank can drop to `2`.
That is why the paper re-runs the Claim of step 6.) -/
theorem isPrimitive_of_coarser {V V' : Type*} {Y : PartitionStructure V}
    {Y' : PartitionStructure V'} (e : V ≃ V') (hYcfg : Y.IsConfiguration)
    (hcoarse : ∀ x y u v : V, Y.color x y = Y.color u v →
      Y'.color (e x) (e y) = Y'.color (e u) (e v))
    (hY : Y.IsPrimitive) (hhom : Y'.IsHomogeneous) : Y'.IsPrimitive := by
  refine ⟨hhom, fun k' hoff' => ?_⟩
  obtain ⟨a', b', hab'⟩ := Y'.color_surjective k'
  set a : V := e.symm a' with ha
  set b : V := e.symm b' with hb
  have hne : a ≠ b := by
    intro hc
    have : ((a', b') : V' × V') ∈ Y'.rel k' ∩ diag V' := by
      refine ⟨hab', ?_⟩
      show a' = b'
      rw [← e.apply_symm_apply a', ← e.apply_symm_apply b', ← ha, ← hb, hc]
    rw [hoff'] at this
    exact this
  have hoffk : Y.IsOffDiagonalColor (Y.color a b) := by
    rw [IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro ⟨z, w⟩ ⟨hzw, hd⟩
    have hzw' : Y.color z w = Y.color a b := hzw
    have : z = w := hd
    subst this
    exact hne (hYcfg.diag a b z hzw'.symm)
  have hconn := hY.2 (Y.color a b) hoffk
  refine Digraph.isWeaklyConnected_of_equiv e (Y := Y.extConstituent (Y.color a b))
    (Z := Y'.extConstituent k') ?_ hconn
  intro x y hxy
  have hxy' : Y.color x y = Y.color a b := hxy
  show Y'.color (e x) (e y) = k'
  rw [hcoarse x y a b hxy', ha, hb, e.apply_symm_apply, e.apply_symm_apply]
  exact hab'

end PartitionStructure

section Primitive

variable (X : Pt (BipBlockInputs Ω))

/-- A point of `W₁`, read as a point of the point set of step 7. -/
noncomputable def step8Point (x : ↥(dominantClass X)) : ↥(step7Set X) :=
  ⟨((x : ↥X.car) : Ω), ⟨(x : ↥X.car), Or.inl x.2, rfl⟩⟩

theorem incl_step8Point (x : ↥(dominantClass X)) :
    VColBipBlk.incl (step7Set_subset X) (step8Point X x) = (x : ↥X.car) := rfl

theorem step8Point_part₁ (x : ↥(dominantClass X)) :
    (step8Obj X).part₁ (step8Point X x) :=
  (step7Obj_part₁_iff X _).2 (by rw [incl_step8Point]; exact x.2)

/-- §9.4, step 8.  **The points of `W₁` are the first part of the new configuration.** -/
noncomputable def step8PtEquiv : ↥(dominantClass X) ≃ ↥(step8Pts X) :=
  Equiv.ofBijective
    (fun x => ⟨⟨{step8Point X x}, Or.inl ⟨step8Point X x, step8Point_part₁ X x, rfl⟩⟩,
      ⟨step8Point X x, step8Point_part₁ X x, rfl⟩⟩)
    ⟨by
      intro x y hxy
      have h : ({step8Point X x} : Set ↥(step7Set X)) = {step8Point X y} :=
        congrArg (fun u : ↥(step8Pts X) => ((u : ↥((step8Obj X).vtx)) : Set ↥(step7Set X))) hxy
      have h2 : step8Point X x = step8Point X y := Set.singleton_eq_singleton_iff.1 h
      have h3 : ((x : ↥X.car) : Ω) = ((y : ↥X.car) : Ω) :=
        congrArg (Subtype.val : ↥(step7Set X) → Ω) h2
      exact Subtype.ext (Subtype.ext h3),
     by
      rintro ⟨⟨u, hu⟩, p, hp, hup⟩
      refine ⟨⟨VColBipBlk.incl (step7Set_subset X) p, (step7Obj_part₁_iff X p).1 hp⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (by rw [hup]; rfl))⟩

theorem step8PtEquiv_image (x : ↥(dominantClass X)) :
    VColBipBlk.incl (step7Set_subset X) ''
        ((((step8PtEquiv X x : ↥(step8Pts X)) : ↥((step8Obj X).vtx)) : Set ↥(step7Set X)))
      = {((x : ↥X.car))} := by
  show VColBipBlk.incl (step7Set_subset X) '' ({step8Point X x} : Set ↥(step7Set X))
    = {((x : ↥X.car))}
  rw [Set.image_singleton, incl_step8Point]

/-- §9.4, step 8.  **The coloring of `X₁` after step 8 is coarser than the coloring of `X₁`
before it.**  This is *"The only effect of this is that it may merge some of the edge-color
classes"*, read on the first part. -/
theorem step8Raw_eq_of_step6Raw_eq (x y u v : ↥(dominantClass X))
    (h : step6Raw X x y = step6Raw X u v) :
    step8Raw X ((step8PtEquiv X x : ↥(step8Pts X)) : ↥((step8Obj X).vtx))
        ((step8PtEquiv X y : ↥(step8Pts X)) : ↥((step8Obj X).vtx))
      = step8Raw X ((step8PtEquiv X u : ↥(step8Pts X)) : ↥((step8Obj X).vtx))
        ((step8PtEquiv X v : ↥(step8Pts X)) : ↥((step8Obj X).vtx)) := by
  refine step8Raw_eq_of_step8Old_eq X _ _ _ _ ?_
  show wlRaw X.obj.1.1 _ _ = wlRaw X.obj.1.1 _ _
  rw [step8PtEquiv_image X x, step8PtEquiv_image X y, step8PtEquiv_image X u,
    step8PtEquiv_image X v]
  exact h

/-- §9.4, step 8, *"`X₁` remains …"*: **`X₁` is still primitive after step 8.**

`X₁` is homogeneous after the step (`Babai.step8Raw_hom₁`), and each of its off-diagonal
constituents is a union of off-diagonal constituents of `X₁` before the step, one of which
is already a connected spanning subgraph because `X₁` was primitive
(`Babai.PartitionStructure.isPrimitive_of_coarser`). -/
theorem step8_induced_isPrimitive (himp : ¬ Step6Imprimitive X)
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥(step8Pts X)] :
    ((step8Config X).induced (step8Pts X)).IsPrimitive := by
  have hY : (step6Config X).IsPrimitive :=
    not_not.1 (fun hp => himp ((step6Imprimitive_iff X).2 hp))
  refine PartitionStructure.isPrimitive_of_coarser (step8PtEquiv X)
    (step6Config_isCoherent X).toIsConfiguration ?_ hY ?_
  · intro x y u v hxy
    refine ((step8Config X).induced_color_eq_iff (step8Pts X) _ _ _ _).2 ?_
    refine (step8Config_raw_eq_iff X _ _ _ _).2 ?_
    exact step8Raw_eq_of_step6Raw_eq X x y u v
      ((step6Config_color_eq_iff X x y u v).1 hxy)
  · intro a b
    refine ((step8Config X).induced_color_eq_iff (step8Pts X) _ _ _ _).2 ?_
    refine (step8Config_raw_eq_iff X _ _ _ _).2 ?_
    exact step8Raw_hom₁ X a.2 b.2

end Primitive

/-! ### §9.4, step 8: *"`X₁` remains a UPCC by Claim above"*, the Claim -/

section Twins

variable (X : Pt (BipBlockInputs Ω))

/-- The vertex of the new configuration given by a point of `W₁`. -/
noncomputable def step8Vertex (x : ↥(dominantClass X)) : ↥((step8Obj X).vtx) :=
  ((step8PtEquiv X x : ↥(step8Pts X)) : ↥((step8Obj X).vtx))

theorem step8Vertex_val (x : ↥(dominantClass X)) :
    ((step8Vertex X x : ↥((step8Obj X).vtx)) : Set ↥(step7Set X)) = {step8Point X x} := rfl

theorem step8Vertex_mem (x : ↥(dominantClass X)) : step8Vertex X x ∈ step8Pts X :=
  (step8PtEquiv X x).2

theorem step8Vertex_injective : Function.Injective (step8Vertex X) := by
  intro x y hxy
  exact (step8PtEquiv X).injective (Subtype.ext hxy)

/-- Every point of the first part of the new graph comes from a point of `W₁`. -/
theorem exists_step8Point {p : ↥(step7Set X)} (hp : (step8Obj X).part₁ p) :
    ∃ x : ↥(dominantClass X), step8Point X x = p :=
  ⟨⟨VColBipBlk.incl (step7Set_subset X) p, (step7Obj_part₁_iff X p).1 hp⟩, Subtype.ext rfl⟩

/-- §9.4, step 8.  **Twins of the new configuration inside `V₁` are twins of the new
graph.**  This is the easy half of *"`Aut(X) = Aut(X₁₂)`"* (step 3) for the new instance:
the new refinement refines the input coloring of the new graph, which records the vertex
colors and the edges. -/
theorem isTwin_step8Obj_of_isTwin_step8Config {u v : ↥(dominantClass X)} (huv : u ≠ v)
    (h : IsTwin (step8Config X).Aut (step8Vertex X u) (step8Vertex X v)) :
    IsTwin (step8Obj X).Aut (step8Point X u) (step8Point X v) := by
  classical
  obtain ⟨-, hmem⟩ := h
  have hcol : ∀ a b : ↥((step8Obj X).vtx),
      (step8Config X).color (Equiv.swap (step8Vertex X u) (step8Vertex X v) a)
        (Equiv.swap (step8Vertex X u) (step8Vertex X v) b)
      = (step8Config X).color a b := hmem
  have hpu : (step8Obj X).part₁ (step8Point X u) := step8Point_part₁ X u
  have hpv : (step8Obj X).part₁ (step8Point X v) := step8Point_part₁ X v
  -- the transposition of two points of `V₁` fixes every block
  have hfixBlk : ∀ B : ↥((step8Obj X).vtx),
      ((B : Set ↥(step7Set X)) ∈ (step8Obj X).blocks) →
      Equiv.swap (step8Vertex X u) (step8Vertex X v) B = B := by
    intro B hB
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro hc
      have hBval : (B : Set ↥(step7Set X)) = {step8Point X u} := by
        rw [hc]; exact step8Vertex_val X u
      exact (step8Obj X).blocks_off₁ _ hB (step8Point X u) (by rw [hBval]; rfl) hpu
    · intro hc
      have hBval : (B : Set ↥(step7Set X)) = {step8Point X v} := by
        rw [hc]; exact step8Vertex_val X v
      exact (step8Obj X).blocks_off₁ _ hB (step8Point X v) (by rw [hBval]; rfl) hpv
  -- the same vertex color, hence the same color `f`
  have hdiag : step8Raw X (step8Vertex X v) (step8Vertex X v)
      = step8Raw X (step8Vertex X u) (step8Vertex X u) := by
    have h1 := hcol (step8Vertex X u) (step8Vertex X u)
    rw [Equiv.swap_apply_left] at h1
    exact (step8Config_raw_eq_iff X _ _ _ _).1 h1
  have hf : (step8Obj X).f (step8Point X u) = (step8Obj X).f (step8Point X v) := by
    have hinit := initColor_eq_of_step8Raw_eq X hdiag
    rw [VColBipBlk.initColor, VColBipBlk.initColor, if_pos rfl, if_pos rfl] at hinit
    have hvtx := (Nat.pair_eq_pair.1 hinit).2
    rw [VColBipBlk.initVtxColor, VColBipBlk.initVtxColor,
      if_pos ⟨step8Point X v, hpv, step8Vertex_val X v⟩,
      if_pos ⟨step8Point X u, hpu, step8Vertex_val X u⟩, step8Vertex_val X u,
      step8Vertex_val X v, Set.image_singleton, Set.image_singleton, csSup_singleton,
      csSup_singleton] at hvtx
    exact ((Nat.pair_eq_pair.1 hvtx).2).symm
  -- the same neighbouring blocks
  have hedge : ∀ B ∈ (step8Obj X).blocks,
      (((step8Point X u, B) ∈ (step8Obj X).E) ↔ ((step8Point X v, B) ∈ (step8Obj X).E)) := by
    intro B hB
    set Bv : ↥((step8Obj X).vtx) := ⟨B, Or.inr hB⟩ with hBv
    have h1 := hcol (step8Vertex X u) Bv
    rw [Equiv.swap_apply_left, hfixBlk Bv hB] at h1
    have hraw : step8Raw X (step8Vertex X v) Bv = step8Raw X (step8Vertex X u) Bv :=
      (step8Config_raw_eq_iff X _ _ _ _).1 h1
    have hinit := initColor_eq_of_step8Raw_eq X hraw
    have hneu : ({step8Point X u} : Set ↥(step7Set X)) ≠ B := fun hc =>
      (step8Obj X).blocks_off₁ _ hB (step8Point X u) (by rw [← hc]; rfl) hpu
    have hnev : ({step8Point X v} : Set ↥(step7Set X)) ≠ B := fun hc =>
      (step8Obj X).blocks_off₁ _ hB (step8Point X v) (by rw [← hc]; rfl) hpv
    rw [step8Vertex_val X u, step8Vertex_val X v] at hinit
    rw [VColBipBlk.initColor, VColBipBlk.initColor, if_neg hnev, if_neg hneu] at hinit
    have hE := (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 hinit).2).1).1
    rw [← (step8Obj X).initEdge_eq_one_iff hpu B, ← (step8Obj X).initEdge_eq_one_iff hpv B,
      hE]
  exact ((step8Obj X).isTwin_iff hpu hpv
    (fun hc => huv (by
      have : step8Vertex X u = step8Vertex X v := by
        apply Subtype.ext; rw [step8Vertex_val X u, step8Vertex_val X v, hc]
      exact step8Vertex_injective X this))).2 ⟨hf, hedge⟩

/-- §9.4, step 8, the positive symmetry defect of the new instance: **`V₁` is not a single
twin equivalence class of the new configuration.**

If it were, all the points of `V₁` would be pairwise twins of the graph `(V₁, V₂; R_i)`,
so its symmetry defect on `V₁` would be `0`; but that defect is at least `1/2`
(`Babai.half_le_step8Obj_defect₁`). -/
theorem not_twinClass_eq_step8Pts (h : ¬ AllClassesSmall X) [Fintype ↥(step7Set X)]
    {i₀ : Fin (step8Config X).rank} (hV₁ : step8Pts X = (step8Config X).vertexClass i₀)
    (x₀ : ↥(dominantClass X)) :
    twinClass (step8Config X).Aut (step8Vertex X x₀)
      ≠ (step8Config X).vertexClass i₀ := by
  classical
  intro hcl
  have hmem : ∀ x : ↥(dominantClass X),
      TwinOrEq (step8Config X).Aut (step8Vertex X x₀) (step8Vertex X x) := by
    intro x
    have : step8Vertex X x ∈ (step8Config X).vertexClass i₀ := by
      rw [← hV₁]; exact step8Vertex_mem X x
    rw [← hcl] at this
    exact this
  have htwin : ∀ x y : ↥(dominantClass X), x ≠ y →
      IsTwin (step8Obj X).Aut (step8Point X x) (step8Point X y) := by
    intro x y hxy
    refine isTwin_step8Obj_of_isTwin_step8Config X hxy ?_
    have heq := twinOrEq_equivalence (step8Config X).Aut
    rcases heq.trans (heq.symm (hmem x)) (hmem y) with hc | hc
    · exact absurd (step8Vertex_injective X hc) hxy
    · exact hc
  have hall : IsTwinSet (step8Obj X).Aut (step8Obj X).V₁ := by
    intro p hp q hq hpq
    obtain ⟨x, rfl⟩ := exists_step8Point X hp
    obtain ⟨y, rfl⟩ := exists_step8Point X hq
    exact htwin x y (fun hc => hpq (congrArg (step8Point X) hc))
  have hle : (step8Obj X).V₁.ncard ≤ (step8Obj X).symmetricity₁ :=
    ncard_le_symmetricity₁ _ (fun _ hx => hx) hall
  have hpos : 0 < (step8Obj X).V₁.ncard := by
    rw [step8Obj_V₁_ncard]
    have := two_le_dominantClass_ncard h
    omega
  have hq : ((step8Obj X).defect₁ : ℚ) ≤ 0 := by
    have hn : (0 : ℚ) < ((step8Obj X).V₁.ncard : ℚ) := by exact_mod_cast hpos
    have hle' : ((step8Obj X).V₁.ncard : ℚ) ≤ ((step8Obj X).symmetricity₁ : ℚ) := by
      exact_mod_cast hle
    have : (1 : ℚ) ≤ ((step8Obj X).symmetricity₁ : ℚ) / ((step8Obj X).V₁.ncard : ℚ) := by
      rw [le_div_iff₀ hn]; linarith
    rw [VColBipBlk.defect₁]; linarith
  have := half_le_step8Obj_defect₁ X h
  linarith

end Twins

/-! ### §9.4, step 8: *"`X₁` remains a UPCC by Claim above"* -/

section Uniprimitive

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 8.  `n₁` is unchanged: the first part of the new configuration is `W₁`. -/
theorem ncard_step8Pts : (step8Pts X).ncard = (dominantClass X).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (step8PtEquiv X).symm

/-- §9.4, step 8.  `n₂` is unchanged: the second part of the new configuration is `D_j`. -/
theorem ncard_step8Blks : (step8Blks X).ncard = (step8Obj X).numBlocks :=
  VColBipBlk.ncard_setOf_mem_blocks (step8Obj X)

/-- §9.4, step 8.  *"`V₁` is larger than any other color-class in `X`"*, the counting:
`n₂ ≤` the old `n₂` `< α n₁ < |W₁|`. -/
theorem step8_numBlocks_lt (h : ¬ AllClassesSmall X) :
    (step8Obj X).numBlocks < (dominantClass X).ncard := by
  have h1 : (step8Obj X).numBlocks ≤ X.obj.1.1.numBlocks := step7Obj_numBlocks_le X
  have h2 : X.obj.1.1.numBlocks < (dominantClass X).ncard :=
    numBlocks_lt_dominantClass_ncard X h
  omega

/-- §9.4, step 8, the hypothesis of the Large clique lemma: *"`V₁` is larger than any other
color-class in `X`."*  The new configuration has two vertex-color classes, `V₁` and `D_j`,
and every other class is empty. -/
theorem step8_vertexClass_ncard_lt (h : ¬ AllClassesSmall X)
    {i₀ j₀ : Fin (step8Config X).rank} (hV₁ : step8Pts X = (step8Config X).vertexClass i₀)
    (hV₂ : step8Blks X = (step8Config X).vertexClass j₀)
    (hcover : ∀ u : ↥((step8Obj X).vtx), u ∈ (step8Config X).vertexClass i₀
      ∨ u ∈ (step8Config X).vertexClass j₀)
    (i : Fin (step8Config X).rank) (hi : i ≠ i₀) :
    ((step8Config X).vertexClass i).ncard < ((step8Config X).vertexClass i₀).ncard := by
  have hsub : (step8Config X).vertexClass i ⊆ (step8Config X).vertexClass j₀ := by
    intro u hu
    rcases hcover u with hc | hc
    · exact absurd (hc.symm.trans hu) (Ne.symm hi)
    · exact hc
  calc ((step8Config X).vertexClass i).ncard
      ≤ ((step8Config X).vertexClass j₀).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (step8Obj X).numBlocks := by rw [← hV₂, ncard_step8Blks]
    _ < (dominantClass X).ncard := step8_numBlocks_lt X h
    _ = ((step8Config X).vertexClass i₀).ncard := by rw [← hV₁, ncard_step8Pts]

/-- `X₁` has at least two colors after step 8: its first part has at least two points. -/
theorem two_le_rank_step8 (h : ¬ AllClassesSmall X) {S : Set ↥((step8Obj X).vtx)}
    (hS : S = step8Pts X) [Fintype ↥((step8Obj X).vtx)] [Fintype ↥S] :
    2 ≤ ((step8Config X).induced S).rank := by
  classical
  subst hS
  have hcard : 2 ≤ (step8Pts X).ncard := by
    rw [ncard_step8Pts]; exact two_le_dominantClass_ncard h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard (Set.toFinite (step8Pts X))).1 (by omega)
  set u : ↥(step8Pts X) := ⟨a, ha⟩ with hu
  set v : ↥(step8Pts X) := ⟨b, hb⟩ with hv
  have huv : u ≠ v := fun hc => hab (congrArg Subtype.val hc)
  by_contra hlt
  rw [Nat.not_le] at hlt
  have h1 := (((step8Config X).induced (step8Pts X)).color u v).isLt
  have h2 := (((step8Config X).induced (step8Pts X)).color v v).isLt
  have hsub : ((step8Config X).induced (step8Pts X)).color u v
      = ((step8Config X).induced (step8Pts X)).color v v := Fin.ext (by omega)
  exact huv (Subtype.ext ((step8Config_isCoherent X).toIsConfiguration.diag _ _ _
    (((step8Config X).induced_color_eq_iff (step8Pts X) u v v v).1 hsub)))

/-- §9.4, step 8, *"`X₁` remains …"*: **`X₁` is still primitive after step 8**, for a set
presented as the first part. -/
theorem step8_isPrimitive_of_eq (himp : ¬ Step6Imprimitive X)
    {S : Set ↥((step8Obj X).vtx)} (hS : S = step8Pts X)
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥S] :
    ((step8Config X).induced S).IsPrimitive := by
  subst hS
  exact step8_induced_isPrimitive X himp

/-- §9.4, step 8, **the last sentence of the step**: *"`X₁` remains a UPCC by Claim
above."*

All three inputs of the Claim are again available at the new instance: `V₁` is one
vertex-color class of the new configuration and is larger than every other class
(`Babai.step8_vertexClass_ncard_lt`), `V₁` is not a twin equivalence class because the new
graph is semiregular and nontrivial, so its symmetry defect on `V₁` is at least `1/2`
(`Babai.not_twinClass_eq_step8Pts`), and `X₁` is still primitive
(`Babai.step8_induced_isPrimitive`).  The rank is what the Claim has to re-establish: a
coarsening of the coloring can lower it to `2`. -/
theorem step8_induced_isUniprimitive (h : ¬ AllClassesSmall X) (himp : ¬ Step6Imprimitive X)
    [Fintype ↥(step7Set X)] [Fintype ↥((step8Obj X).vtx)]
    {i₀ j₀ : Fin (step8Config X).rank}
    (hV₁ : step8Pts X = (step8Config X).vertexClass i₀)
    (hV₂ : step8Blks X = (step8Config X).vertexClass j₀)
    (hcover : ∀ u : ↥((step8Obj X).vtx), u ∈ (step8Config X).vertexClass i₀
      ∨ u ∈ (step8Config X).vertexClass j₀) :
    ((step8Config X).induced ((step8Config X).vertexClass i₀)).IsUniprimitive := by
  obtain ⟨x₀, hx₀⟩ : (dominantClass X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    have := two_le_dominantClass_ncard h
    rw [hc, Set.ncard_empty] at this
    omega
  have hx : step8Vertex X ⟨x₀, hx₀⟩ ∈ (step8Config X).vertexClass i₀ := by
    rw [← hV₁]; exact step8Vertex_mem X ⟨x₀, hx₀⟩
  exact claim_9_4_step6_general (step8Config X) (step8Config_isCoherent X) i₀
    (step8_vertexClass_ncard_lt X h hV₁ hV₂ hcover) hx
    (not_twinClass_eq_step8Pts X h hV₁ ⟨x₀, hx₀⟩)
    (step8_isPrimitive_of_eq X himp hV₁.symm)
    (two_le_rank_step8 X h hV₁.symm)

end Uniprimitive

/-! ### §9.4, step 8: `X₂` and the three cases of step 9 -/

section Part₂

variable (X : Pt (BipBlockInputs Ω))

/-- §9.4, step 8, *"`X₂` is homogeneous"*: the blocks of `D_j` form one vertex-color class
of the new configuration as well (`Babai.step8Raw_hom₂`). -/
theorem step8_induced₂_isHomogeneous {S : Set ↥((step8Obj X).vtx)} (hS : S = step8Blks X)
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥S] :
    ((step8Config X).induced S).IsHomogeneous := by
  subst hS
  intro a b
  refine ((step8Config X).induced_color_eq_iff (step8Blks X) _ _ _ _).2 ?_
  exact (step8Config_raw_eq_iff X _ _ _ _).2
    (step8Raw_hom₂ X a.2 b.2)

/-- §9.4, step 9.  *"We need to consider the following cases: (i) `X₂` is imprimitive;
(ii) `X₂` is the clique configuration; (iii) `X₂` is uniprimitive."*  (Version 2.5, lines
4166-4171.)

The three cases are exhaustive for a homogeneous configuration: either it is imprimitive,
or it is primitive, and then it is the clique configuration (rank `≤ 2`) or uniprimitive
(rank `≥ 3`, Def. 3.2.1). -/
theorem homogeneous_trichotomy {V : Type*} (P : PartitionStructure V)
    (hhom : P.IsHomogeneous) :
    (P.IsHomogeneous ∧ ¬ P.IsPrimitive) ∨ P.rank ≤ 2 ∨ P.IsUniprimitive := by
  by_cases hp : P.IsPrimitive
  · by_cases hr : 3 ≤ P.rank
    · exact Or.inr (Or.inr ⟨hp, hr⟩)
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl ⟨hhom, hp⟩

/-- §9.4, step 9, the case distinction, read at the instance that step 8 leaves. -/
theorem step8_induced₂_trichotomy {S : Set ↥((step8Obj X).vtx)} (hS : S = step8Blks X)
    [Fintype ↥((step8Obj X).vtx)] [Fintype ↥S] :
    (((step8Config X).induced S).IsHomogeneous ∧ ¬ ((step8Config X).induced S).IsPrimitive)
      ∨ ((step8Config X).induced S).rank ≤ 2
      ∨ ((step8Config X).induced S).IsUniprimitive :=
  homogeneous_trichotomy _ (step8_induced₂_isHomogeneous X hS)

/-- §9.4, step 8, *"`X₁₂` remains nontrivial (because `R_i` remains one of its
constituents)"*: **`R_i` is a union of color classes of the new configuration.**  Together
with `Babai.step8Raw_eq_of_step8Old_eq` — which makes `R_i`, one class of the old
configuration, lie inside one new class — this says that `R_i` is exactly one constituent
of the new `X₁₂`. -/
theorem step8_edge_iff_of_step8Raw_eq {p q : ↥(step7Set X)} (hp : (step8Obj X).part₁ p)
    (hq : (step8Obj X).part₁ q) {B C : Set ↥(step7Set X)} (hB : B ∈ (step8Obj X).blocks)
    (hC : C ∈ (step8Obj X).blocks)
    (h : step8Raw X ⟨{p}, Or.inl ⟨p, hp, rfl⟩⟩ ⟨B, Or.inr hB⟩
      = step8Raw X ⟨{q}, Or.inl ⟨q, hq, rfl⟩⟩ ⟨C, Or.inr hC⟩) :
    (((p, B) ∈ (step8Obj X).E) ↔ ((q, C) ∈ (step8Obj X).E)) := by
  classical
  have hinit := initColor_eq_of_step8Raw_eq X h
  have hnep : ({p} : Set ↥(step7Set X)) ≠ B := fun hc =>
    (step8Obj X).blocks_off₁ _ hB p (by rw [← hc]; rfl) hp
  have hneq : ({q} : Set ↥(step7Set X)) ≠ C := fun hc =>
    (step8Obj X).blocks_off₁ _ hC q (by rw [← hc]; rfl) hq
  rw [VColBipBlk.initColor, VColBipBlk.initColor, if_neg hnep, if_neg hneq] at hinit
  have hE := (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 hinit).2).1).1
  rw [← (step8Obj X).initEdge_eq_one_iff hp B, ← (step8Obj X).initEdge_eq_one_iff hq C, hE]

end Part₂

/-! ### §9.4, step 8: the choice of `R_i` is canonical -/

section Canonical

variable {X Y : Pt (BipBlockInputs Ω)} {φ : ↥X.car ≃ ↥Y.car}

/-- §9.4, step 8.  **The set of colors involved in the link is an isomorphism
invariant.** -/
theorem step8Colors_eq (hφ : φ ∈ (BipBlockInputs Ω).IsoP X Y) :
    step8Colors X = step8Colors Y := by
  have hsymm : φ.symm ∈ (BipBlockInputs Ω).IsoP Y X := (BipBlockInputs Ω).symm_mem hφ
  have key : ∀ {X' Y' : Pt (BipBlockInputs Ω)} {ψ : ↥X'.car ≃ ↥Y'.car},
      ψ ∈ (BipBlockInputs Ω).IsoP X' Y' → step8Colors X' ⊆ step8Colors Y' := by
    rintro X' Y' ψ hψ k ⟨x, hx, B, hB, rfl⟩
    refine ⟨ψ x, ?_, ψ '' B, ?_, ?_⟩
    · rw [dominantClass_image hψ]; exact ⟨x, hx, rfl⟩
    · rw [step7Blocks_image hψ]; exact ⟨B, hB, rfl⟩
    · rw [← Set.image_singleton (f := ψ), VColBipBlk.wlCaseColor_map hψ.2]
  exact Set.Subset.antisymm (key hφ) (key hsymm)

/-- §9.4, step 8.  **The chosen color `i` is an isomorphism invariant**, which is what
makes the replacement `X ← (V₁, V₂; R_i)` of step 8 canonical. -/
theorem step8Color_congr (h : ((BipBlockInputs Ω).IsoP X Y).Nonempty) :
    step8Color X = step8Color Y := by
  obtain ⟨φ, hφ⟩ := h
  rw [step8Color, step8Color, step8Colors_eq hφ]

end Canonical

end Babai









