/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.4, step 3: WL refinement of the input of Theorem 9.2.2, with its colors named by
natural numbers canonically.
-/
import Workspace.SplitOrJohnson.BipBlocks
import Workspace.Refinement.WL

/-!
# Section 9.4, step 3: the initial coloring and the padded abstract refinement

Actual vertices are singletons from the first part and blocks from the second part.
The original abstract refinement runs on all subsets. Its definitions remain here
for the existing class-level proofs. `WLCarrier` proves that restricting each round
to actual vertices gives the same classes as refinement on those vertices alone.
`WLColor` assigns the integer names by running the named process on actual vertices.
-/

namespace Babai

/-! ### The bijection of the subsets induced by a bijection of the points -/

/-- The bijection of the power sets induced by a bijection of the points.  This is the map
on the **vertices** of the configuration of step 3: a vertex is a subset of the point
set. -/
def imgEquiv {α β : Type*} (φ : α ≃ β) : Set α ≃ Set β where
  toFun A := φ '' A
  invFun B := φ.symm '' B
  left_inv A := Equiv.symm_image_image φ A
  right_inv B := Equiv.image_symm_image φ B

@[simp] theorem imgEquiv_apply {α β : Type*} (φ : α ≃ β) (A : Set α) :
    imgEquiv φ A = φ '' A := rfl

/-- §9.6.  The vertices of the coherent configuration of step 3 of §9.4, indexed by
subsets of the point set: a point `x` of `V₁` is the singleton `{x}`, and a vertex of `V₂`
is a block. -/
def IsVertexOn {V : Type*} (part₁ : V → Prop) (blocks : Set (Set V)) (A : Set V) : Prop :=
  (∃ x, part₁ x ∧ A = {x}) ∨ A ∈ blocks

/-- A bijection that carries the first part to the first part and blocks to blocks carries
the vertex set onto the vertex set. -/
theorem isVertexOn_image_iff {V W : Type*} {p : V → Prop} {q : W → Prop}
    {blocks : Set (Set V)} {blocks' : Set (Set W)} {φ : V ≃ W}
    (hp : ∀ x, q (φ x) ↔ p x) (hb : ∀ B, φ '' B ∈ blocks' ↔ B ∈ blocks) (A : Set V) :
    IsVertexOn q blocks' (φ '' A) ↔ IsVertexOn p blocks A := by
  unfold IsVertexOn
  refine or_congr ?_ (hb A)
  constructor
  · rintro ⟨y, hy, hA⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · rw [← hp (φ.symm y), Equiv.apply_symm_apply]; exact hy
    · have h : φ.symm '' (φ '' A) = φ.symm '' ({y} : Set W) := by rw [hA]
      rwa [Equiv.symm_image_image, Set.image_singleton] at h
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, (hp x).2 hx, by rw [Set.image_singleton]⟩

/-! ### The number of rounds -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- §9.4, step 3.  The number of rounds of WL refinement run on **every** input on a subset
of the ambient set `Ω`.  It is the bound of `Babai.WL.stable` for the largest possible
vertex set, the power set of `Ω`; running this many rounds on a smaller vertex set changes
nothing (`Babai.WL.isStable_iter_of_card_le`) and makes the color type independent of the
input, which is what canonicity needs.  See the module docstring. -/
noncomputable def wlRounds (Ω : Type) : ℕ := Nat.card ((Set Ω × Set Ω) × (Set Ω × Set Ω))

/-- The fixed number of rounds is enough for every vertex set of the form `Set ↥s` with
`s ⊆ Ω`. -/
theorem card_le_wlRounds (s : Set Ω) :
    Nat.card ((Set ↥s × Set ↥s) × (Set ↥s × Set ↥s)) ≤ wlRounds Ω := by
  have hinj : Function.Injective (fun A : Set ↥s => (Subtype.val '' A : Set Ω)) :=
    Set.image_injective.2 Subtype.val_injective
  have h : Nat.card (Set ↥s) ≤ Nat.card (Set Ω) := Nat.card_le_card_of_injective _ hinj
  simp only [wlRounds, Nat.card_prod]
  exact Nat.mul_le_mul (Nat.mul_le_mul h h) (Nat.mul_le_mul h h)

namespace VColBipBlk

/-! ### The configuration that is refined -/

variable {s t : Type}

open scoped Classical in
/-- §9.4, step 3.  The color of a **vertex** of the input configuration: the paper's
*"vertex-colored graph where the vertex-colors discriminate between `V₁` and `V₂`"*
(version 2.5, line 4098).  A point `x` of `V₁` is the singleton `{x}` and keeps its color
`f x`, a block keeps its color `g B`, and the two parts are told apart by the tag `1`
versus `2`.  A subset that is not a vertex gets the color `0`.

The color of a singleton is written `sSup (f '' A)` rather than `f x`: on `A = {x}` the two
agree, and this form needs no choice of the point `x`, which is what makes the equivariance
proof (`Babai.VColBipBlk.initVtxColor_map`) a rewriting. -/
noncomputable def initVtxColor (G : VColBipBlk s ℕ) (A : Set s) : ℕ :=
  if ∃ x, G.part₁ x ∧ A = {x} then Nat.pair 1 (sSup (G.f '' A))
  else if A ∈ G.blocks then Nat.pair 2 (G.g A) else 0

open scoped Classical in
/-- §9.4, step 3.  The edge indicator of the input configuration: `1` when `A` is the
singleton of a point of `V₁` joined to `B`, and `0` otherwise. -/
noncomputable def initEdge (G : VColBipBlk s ℕ) (A B : Set s) : ℕ :=
  if ∃ x, G.part₁ x ∧ A = {x} ∧ (x, B) ∈ G.E then 1 else 0

open scoped Classical in
/-- §9.4, step 3.  The coloring of the pairs of vertices that WL refinement is applied to:
on the diagonal the vertex color, off the diagonal the pair of edge indicators of the two
directions.  The diagonal colors are tagged `0` and the off-diagonal ones `1`, which is
axiom (i) of Definition 3.1.2; recording both directions is axiom (ii). -/
noncomputable def initColor (G : VColBipBlk s ℕ) (A B : Set s) : ℕ :=
  if A = B then Nat.pair 0 (initVtxColor G A)
  else Nat.pair 1 (Nat.pair (Nat.pair (initEdge G A B) (initEdge G B A))
    (Nat.pair (G.h A B) (G.h B A)))

/-- §9.4, step 3, **without the hint**: the initial coloring as it was before the field
`Babai.VColBipBlk.h` was added.  It is kept only to state
`Babai.VColBipBlk.initColor_eq_iff_of_hint_zero`, which says that for `h = 0` the two
colorings have the same color classes. -/
noncomputable def initColorNoHint (G : VColBipBlk s ℕ) (A B : Set s) : ℕ :=
  if A = B then Nat.pair 0 (initVtxColor G A)
  else Nat.pair 1 (Nat.pair (initEdge G A B) (initEdge G B A))

/-- §9.4, step 3.  **For `h = 0` the hint changes nothing.**  When the hint is the constant
`0` — which is the case for an honest vertex-colored bipartite graph
(`Babai.VColBip.toBlk`), hence for the printed Theorem 9.2.2 — the initial coloring of
step 3 has exactly the color classes of the coloring without the hint.  So the whole
refinement, and with it everything §9.4-§9.8 reads off it, is the one from before the
repair. -/
theorem initColor_eq_iff_of_hint_zero (G : VColBipBlk s ℕ) (hz : ∀ A B, G.h A B = 0)
    (A B C D : Set s) :
    initColor G A B = initColor G C D ↔ initColorNoHint G A B = initColorNoHint G C D := by
  classical
  have hcol : ∀ P Q : Set s, initColor G P Q
      = if P = Q then Nat.pair 0 (initVtxColor G P)
        else Nat.pair 1 (Nat.pair (Nat.pair (initEdge G P Q) (initEdge G Q P))
          (Nat.pair 0 0)) := by
    intro P Q
    rw [initColor, hz, hz]
  rw [hcol, hcol, initColorNoHint, initColorNoHint]
  by_cases hAB : A = B <;> by_cases hCD : C = D <;>
    simp only [hAB, hCD, if_pos, if_neg, if_true, if_false, Nat.pair_eq_pair] <;>
    simp_all [Nat.pair_eq_pair]

/-- §9.4, step 3.  *"Apply WL refinement to `X`"* presupposes that `X` is a configuration
(Def. 3.1.2); this is it. -/
theorem isConfigColoring_initColor (G : VColBipBlk s ℕ) :
    WL.IsConfigColoring (initColor G) := by
  classical
  constructor
  · intro A B D h
    by_contra hne
    rw [initColor, initColor, if_neg hne, if_pos rfl] at h
    exact absurd (Nat.pair_eq_pair.1 h).1 (by norm_num)
  · intro A B X Y h
    by_cases hAB : A = B
    · subst hAB
      by_cases hXY : X = Y
      · subst hXY; exact h
      · rw [initColor, initColor, if_pos rfl, if_neg hXY] at h
        exact absurd (Nat.pair_eq_pair.1 h).1 (by norm_num)
    · by_cases hXY : X = Y
      · subst hXY
        rw [initColor, initColor, if_neg hAB, if_pos rfl] at h
        exact absurd (Nat.pair_eq_pair.1 h).1 (by norm_num)
      · rw [initColor, initColor, if_neg hAB, if_neg hXY] at h
        obtain ⟨-, h2⟩ := Nat.pair_eq_pair.1 h
        obtain ⟨he, hh⟩ := Nat.pair_eq_pair.1 h2
        obtain ⟨h3, h4⟩ := Nat.pair_eq_pair.1 he
        obtain ⟨h5, h6⟩ := Nat.pair_eq_pair.1 hh
        rw [initColor, initColor, if_neg (Ne.symm hAB), if_neg (Ne.symm hXY),
          h3, h4, h5, h6]

/-- §9.4, step 3.  Reading the **edge** components off an equality of two off-diagonal
colors of the initial coloring. -/
theorem initEdge_eq_of_initColor_eq {G : VColBipBlk s ℕ} {H : VColBipBlk t ℕ}
    {A B : Set s} {C D : Set t} (hAB : A ≠ B) (hCD : C ≠ D)
    (hc : initColor G A B = initColor H C D) :
    initEdge G A B = initEdge H C D ∧ initEdge G B A = initEdge H D C := by
  classical
  rw [initColor, initColor, if_neg hAB, if_neg hCD] at hc
  exact Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 hc).2).1

/-- §9.4, step 3.  Reading the **hint** off an equality of two off-diagonal colors of the
initial coloring.  This is what makes the hint survive the second WL refinement of step 8:
the stable coloring of step 3 refines the initial coloring, which records `h`. -/
theorem h_eq_of_initColor_eq {G : VColBipBlk s ℕ} {H : VColBipBlk t ℕ}
    {A B : Set s} {C D : Set t} (hAB : A ≠ B) (hCD : C ≠ D)
    (hc : initColor G A B = initColor H C D) :
    G.h A B = H.h C D ∧ G.h B A = H.h D C := by
  classical
  rw [initColor, initColor, if_neg hAB, if_neg hCD] at hc
  exact Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 hc).2).2

/-! ### Equivariance of the input configuration -/

variable {G : VColBipBlk s ℕ} {H : VColBipBlk t ℕ} {φ : s ≃ t}

/-- A bijection of the point sets that is an isomorphism carries the singletons of `V₁`
onto the singletons of `V₁`. -/
theorem isSingleton₁_image_iff (h : G.IsIsoTo H φ) (A : Set s) :
    (∃ y, H.part₁ y ∧ φ '' A = {y}) ↔ ∃ x, G.part₁ x ∧ A = {x} := by
  constructor
  · rintro ⟨y, hy, hA⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · rw [← h.part₁ (φ.symm y), Equiv.apply_symm_apply]; exact hy
    · have h2 : φ.symm '' (φ '' A) = φ.symm '' ({y} : Set t) := by rw [hA]
      rwa [Equiv.symm_image_image, Set.image_singleton] at h2
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, (h.part₁ x).2 hx, by rw [Set.image_singleton]⟩

theorem initVtxColor_map (h : G.IsIsoTo H φ) (A : Set s) :
    initVtxColor H (φ '' A) = initVtxColor G A := by
  classical
  have himg : H.f '' (φ '' A) = G.f '' A := by
    rw [← Set.image_comp]
    exact Set.image_congr (fun x _ => h.color₁ x)
  rw [initVtxColor, initVtxColor]
  by_cases hA : ∃ x, G.part₁ x ∧ A = {x}
  · rw [if_pos ((isSingleton₁_image_iff h A).2 hA), if_pos hA, himg]
  · rw [if_neg (fun hc => hA ((isSingleton₁_image_iff h A).1 hc)), if_neg hA]
    by_cases hB : A ∈ G.blocks
    · rw [if_pos ((h.blocks A).2 hB), if_pos hB, h.color₂ A]
    · rw [if_neg (fun hc => hB ((h.blocks A).1 hc)), if_neg hB]

theorem initEdge_map (h : G.IsIsoTo H φ) (A B : Set s) :
    initEdge H (φ '' A) (φ '' B) = initEdge G A B := by
  classical
  have hiff : (∃ y, H.part₁ y ∧ φ '' A = {y} ∧ (y, φ '' B) ∈ H.E)
      ↔ ∃ x, G.part₁ x ∧ A = {x} ∧ (x, B) ∈ G.E := by
    constructor
    · rintro ⟨y, hy, hA, hE⟩
      refine ⟨φ.symm y, ?_, ?_, ?_⟩
      · rw [← h.part₁ (φ.symm y), Equiv.apply_symm_apply]; exact hy
      · have h2 : φ.symm '' (φ '' A) = φ.symm '' ({y} : Set t) := by rw [hA]
        rwa [Equiv.symm_image_image, Set.image_singleton] at h2
      · rw [← h.edges (φ.symm y) B, Equiv.apply_symm_apply]; exact hE
    · rintro ⟨x, hx, rfl, hE⟩
      exact ⟨φ x, (h.part₁ x).2 hx, by rw [Set.image_singleton], (h.edges x B).2 hE⟩
  rw [initEdge, initEdge]
  by_cases hc : ∃ x, G.part₁ x ∧ A = {x} ∧ (x, B) ∈ G.E
  · rw [if_pos (hiff.2 hc), if_pos hc]
  · rw [if_neg (fun hd => hc (hiff.1 hd)), if_neg hc]

/-- §9.4, step 3.  The configuration that is refined is canonical: an isomorphism of the
inputs carries it to the configuration of the image. -/
theorem initColor_map (h : G.IsIsoTo H φ) (A B : Set s) :
    initColor H (φ '' A) (φ '' B) = initColor G A B := by
  have hinj : φ '' A = φ '' B ↔ A = B := Set.image_eq_image φ.injective
  rw [initColor, initColor]
  by_cases hAB : A = B
  · rw [if_pos (hinj.2 hAB), if_pos hAB, initVtxColor_map h]
  · rw [if_neg (fun hc => hAB (hinj.1 hc)), if_neg hAB, initEdge_map h, initEdge_map h,
      h.hint A B, h.hint B A]

end VColBipBlk

/-! ### The refined coloring and its canonical `ℕ`-names -/

namespace VColBipBlk

variable {s t : Set Ω}

/-- §9.4, step 3.  *"Apply WL refinement to `X`.  Let `X = (V; R₁, …, R_r)` denote the
resulting CC."*  The refinement is run for `Babai.wlRounds Ω` rounds, one and the same
number for every input on every subset of `Ω`, so the color type does not depend on the
input.  The colors are abstract; `Babai.VColBipBlk.wlColor` names them by natural
numbers. -/
noncomputable def wlRaw (G : VColBipBlk ↥s ℕ) :
    Set ↥s → Set ↥s → WL.colorType ℕ (wlRounds Ω) :=
  WL.iter (initColor G) (wlRounds Ω)

/-- §9.4, step 3.  *"the resulting CC"*: the refined coloring is coherent. -/
theorem isCoherentColoring_wlRaw (G : VColBipBlk ↥s ℕ) :
    WL.IsCoherentColoring (wlRaw G) :=
  WL.isCoherentColoring_iter_of_card_le (isConfigColoring_initColor G) (card_le_wlRounds s)

/-- §4.3, Eq. (26).  The refined coloring is canonical: an isomorphism of the inputs
preserves it.  This is where the fixed number of rounds pays: both sides have the same
color type, so there is no `cast`. -/
theorem wlRaw_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) (A B : Set ↥s) : wlRaw H (φ '' A) (φ '' B) = wlRaw G A B := by
  have hiso : imgEquiv φ ∈ WL.Iso (initColor G) (initColor H) := fun A B => initColor_map h A B
  have hstep : imgEquiv φ ∈ WL.Iso (WL.iter (initColor G) (wlRounds Ω))
      (WL.iter (initColor H) (wlRounds Ω)) := by
    rw [WL.iso_iter (initColor G) (initColor H) (wlRounds Ω)]
    exact hiso
  exact hstep A B

/-- §9.4, step 3.  The set of colors that occur on the pairs of vertices.  The `ℕ`-name of
raw colors remain available for proofs that compare color classes. Integer names
are assigned separately, round by round, in `WLColor`. -/
noncomputable def wlColorSet (G : VColBipBlk ↥s ℕ) : Set (WL.colorType ℕ (wlRounds Ω)) :=
  {k | ∃ A B, IsVertexOn G.part₁ G.blocks A ∧ IsVertexOn G.part₁ G.blocks B ∧
    wlRaw G A B = k}

theorem wlColorSet_finite (G : VColBipBlk ↥s ℕ) : (wlColorSet G).Finite := by
  refine Set.Finite.subset (Set.finite_range fun p : Set ↥s × Set ↥s => wlRaw G p.1 p.2) ?_
  rintro k ⟨A, B, -, -, rfl⟩
  exact ⟨(A, B), rfl⟩

/-- The set of colors that occur is an isomorphism invariant: the vertices correspond, and
so do the colors of corresponding pairs. -/
theorem wlColorSet_map {G : VColBipBlk ↥s ℕ} {H : VColBipBlk ↥t ℕ} {φ : ↥s ≃ ↥t}
    (h : G.IsIsoTo H φ) : wlColorSet H = wlColorSet G := by
  ext k
  constructor
  · rintro ⟨A', B', hA', hB', rfl⟩
    refine ⟨φ.symm '' A', φ.symm '' B', ?_, ?_, ?_⟩
    · rw [← isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) (φ.symm '' A'),
        Equiv.image_symm_image]
      exact hA'
    · rw [← isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) (φ.symm '' B'),
        Equiv.image_symm_image]
      exact hB'
    · rw [← wlRaw_map h (φ.symm '' A') (φ.symm '' B'), Equiv.image_symm_image,
        Equiv.image_symm_image]
  · rintro ⟨A, B, hA, hB, rfl⟩
    exact ⟨φ '' A, φ '' B,
      (isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) A).2 hA,
      (isVertexOn_image_iff (fun x => h.part₁ x) (fun B => h.blocks B) B).2 hB,
      wlRaw_map h A B⟩

end VColBipBlk

end Babai
