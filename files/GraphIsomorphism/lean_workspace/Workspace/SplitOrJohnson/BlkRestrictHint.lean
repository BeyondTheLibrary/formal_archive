/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7: restricting an input of the block design case to a sub-family of its blocks
**and attaching the hint** of §9.5 to the pairs of the kept blocks.
-/
import Workspace.SplitOrJohnson.BlkRestrict
import Workspace.SplitOrJohnson.HintBuild

/-!
# §9.7  The restricted input with the hint

Version 2.5, lines 4176-4181 (§9.5) and 4281-4301 (§9.7, Cases 3a1, 3a2 and 3b).

§9.5 counts three kinds of major progress.  `Workspace/SplitOrJohnson/BlkRestrict.lean`
builds the outcome of the second one, *"`n₂` is significantly reduced"*: the input of §9.7
restricted to a canonical sub-family `U` of its blocks, with `10|U| ≤ 9n₂`.  This file
builds the outcome of the **third** one,

> *"`X₂` moves from clique to UPCC while `n₂` does not increase"*,

which is the same restricted input with the hint set: the coloring `h` of the ordered pairs
of blocks records the homogeneous coherent configuration of rank `≥ 3` that the Design
Lemma found on `U` — the UPCC `Y` of Case 3a2, or the equipartition of Cases 3a1 and 3b.
See entries 88 and 94 of the corrected paper.

| Paper | Lean |
|---|---|
| `X[V₁, U]` with the structure found on `U` attached | `Babai.VColBipBlk.restrictBlkHint` |
| it is an admissible input of Thm. 9.2.2 | `Babai.restrictObjHint`, `Babai.restrictObjHint_pred` |
| it carries the hint | `Babai.VColBipBlk.hasHint_restrictBlkHint` |
| *"`X₂` moves from clique to UPCC while `n₂` does not increase"* | `Babai.good97_restrict_hint` |

## Why the symmetry defect does not see the hint

The input of Theorem 9.2.2 asks for a symmetry defect of `V₁`, and the hint is new data
that enters the automorphism group.  It changes nothing: by
`Babai.VColBipBlk.isTwin_iff` two points of `V₁` are twins exactly when they have the same
color and the same neighboring blocks, because the transposition of two points of `V₁`
fixes *every block setwise* (`Babai.VColBipBlk.swap_image_block`), hence preserves any
coloring of the pairs of blocks.  `Babai.VColBipBlk.symmetricity₁_congr` is that statement:
two objects with the same first part, the same blocks, the same edges and the same point
coloring have the same symmetricity of `V₁`, whatever their block coloring and hint.  So
`Babai.restrictObjHint_pred` has exactly the hypotheses of `Babai.restrictObj_pred`.
-/

namespace Babai

namespace VColBipBlk

variable {s : Type} [Fintype s] [DecidableEq s] {κ : Type} [Zero κ]

/-! ### The symmetry defect of `V₁` does not see the block coloring or the hint -/

/-- Two objects with the same first part, the same blocks, the same edges and the same
point coloring have the same twins inside `V₁`.  (`Babai.VColBipBlk.isTwin_iff`: neither
the block coloring `g` nor the hint `h` enters the twin relation of `V₁`.) -/
theorem isTwin_congr {X Y : VColBipBlk s κ} (hp : X.part₁ = Y.part₁)
    (hb : X.blocks = Y.blocks) (hE : X.E = Y.E) (hf : X.f = Y.f) {x y : s}
    (hx : X.part₁ x) (hy : X.part₁ y) (hne : x ≠ y) :
    IsTwin X.Aut x y ↔ IsTwin Y.Aut x y := by
  rw [X.isTwin_iff hx hy hne, Y.isTwin_iff (hp ▸ hx) (hp ▸ hy) hne, hb, hE, hf]

open scoped Classical in
/-- Definition 2.4.29.  The symmetricity of `V₁` does not see the block coloring or the
hint. -/
theorem symmetricity₁_congr {X Y : VColBipBlk s κ} (hp : X.part₁ = Y.part₁)
    (hb : X.blocks = Y.blocks) (hE : X.E = Y.E) (hf : X.f = Y.f) :
    X.symmetricity₁ = Y.symmetricity₁ := by
  classical
  have hset : (Finset.univ.filter fun T : Finset s =>
        (∀ x ∈ T, X.part₁ x) ∧ IsTwinSet X.Aut (↑T : Set s))
      = (Finset.univ.filter fun T : Finset s =>
        (∀ x ∈ T, Y.part₁ x) ∧ IsTwinSet Y.Aut (↑T : Set s)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => hp ▸ h1 x hx, fun x hx y hy hne => ?_⟩
      exact (isTwin_congr hp hb hE hf (h1 x hx) (h1 y hy) hne).1 (h2 x hx y hy hne)
    · rintro ⟨h1, h2⟩
      have h1' : ∀ x ∈ T, X.part₁ x := fun x hx => hp ▸ h1 x hx
      refine ⟨h1', fun x hx y hy hne => ?_⟩
      exact (isTwin_congr hp hb hE hf (h1' x hx) (h1' y hy) hne).2 (h2 x hx y hy hne)
  unfold symmetricity₁
  rw [hset]

/-- The relative symmetry defect of `V₁` does not see the block coloring or the hint. -/
theorem defect₁_congr {X Y : VColBipBlk s κ} (hp : X.part₁ = Y.part₁)
    (hb : X.blocks = Y.blocks) (hE : X.E = Y.E) (hf : X.f = Y.f) :
    X.defect₁ = Y.defect₁ := by
  have hV : X.V₁ = Y.V₁ := by
    show {x | X.part₁ x} = {x | Y.part₁ x}
    rw [hp]
  rw [defect₁, defect₁, symmetricity₁_congr hp hb hE hf, hV]

/-- The absolute symmetry defect of `V₁` does not see the block coloring or the hint. -/
theorem symDefect₁_congr {X Y : VColBipBlk s κ} (hp : X.part₁ = Y.part₁)
    (hb : X.blocks = Y.blocks) (hE : X.E = Y.E) (hf : X.f = Y.f) :
    X.symDefect₁ = Y.symDefect₁ := by
  have hV : X.V₁ = Y.V₁ := by
    show {x | X.part₁ x} = {x | Y.part₁ x}
    rw [hp]
  rw [symDefect₁, symDefect₁, symmetricity₁_congr hp hb hE hf, hV]

end VColBipBlk

namespace VColBipBlk

variable {s : Type} {κ : Type} [Zero κ] (X : VColBipBlk s κ)

open scoped Classical in
/-- §9.7, Cases 3a1, 3a2 and 3b.  **The induced subgraph `X[V₁, U]` with the hint `c`
attached.**  It is `Babai.VColBipBlk.restrictBlk` except for the field `h`, which is the
given coloring `c` of the ordered pairs of the kept blocks, padded by `0` elsewhere.

`c` is the coloring of the structure that the Design Lemma found on `U`; the padding is
the normalization that `Babai.VColBipBlk.h_off` asks for. -/
noncomputable def restrictBlkHint (U : Set (Set s)) (c : Set s → Set s → κ) :
    VColBipBlk s κ :=
  { X.restrictBlk U with
    h := fun A B => if A ∈ X.blocks ∩ U ∧ B ∈ X.blocks ∩ U then c A B else 0
    h_off := by
      intro A B hAB
      refine if_neg (fun hc => ?_)
      rcases hAB with h | h
      · exact h hc.1
      · exact h hc.2 }

variable {X}

@[simp] theorem restrictBlkHint_part₁ (U : Set (Set s)) (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).part₁ = X.part₁ := rfl

@[simp] theorem restrictBlkHint_blocks (U : Set (Set s)) (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).blocks = X.blocks ∩ U := rfl

@[simp] theorem restrictBlkHint_E (U : Set (Set s)) (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).E = (X.restrictBlk U).E := rfl

@[simp] theorem restrictBlkHint_f (U : Set (Set s)) (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).f = X.f := rfl

@[simp] theorem restrictBlkHint_V₁ (U : Set (Set s)) (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).V₁ = X.V₁ := rfl

open scoped Classical in
theorem restrictBlkHint_h {U : Set (Set s)} {c : Set s → Set s → κ} {A B : Set s}
    (hA : A ∈ X.blocks ∩ U) (hB : B ∈ X.blocks ∩ U) :
    (X.restrictBlkHint U c).h A B = c A B := by
  show (if A ∈ X.blocks ∩ U ∧ B ∈ X.blocks ∩ U then c A B else 0) = c A B
  rw [if_pos ⟨hA, hB⟩]

/-- The number of blocks of the hinted restriction is `|U|`, as soon as `U` is a
sub-family of the blocks. -/
theorem restrictBlkHint_numBlocks {U : Set (Set s)} {c : Set s → Set s → κ}
    (hU : U ⊆ X.blocks) : (X.restrictBlkHint U c).numBlocks = U.ncard := by
  rw [numBlocks, restrictBlkHint_blocks, Set.inter_eq_self_of_subset_right hU]

end VColBipBlk

namespace VColBipBlk

variable {s : Type} [Fintype s] [DecidableEq s] {κ : Type} [Zero κ]

/-- The hinted restriction has the symmetry defect of the plain restriction: the hint is
not seen by the twins of `V₁`.  See the module docstring. -/
theorem restrictBlkHint_symDefect₁ (X : VColBipBlk s κ) (U : Set (Set s))
    (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).symDefect₁ = (X.restrictBlk U).symDefect₁ :=
  symDefect₁_congr rfl rfl rfl rfl

theorem restrictBlkHint_defect₁ (X : VColBipBlk s κ) (U : Set (Set s))
    (c : Set s → Set s → κ) :
    (X.restrictBlkHint U c).defect₁ = (X.restrictBlk U).defect₁ :=
  defect₁_congr rfl rfl rfl rfl

end VColBipBlk

namespace VColBipBlk

variable {s t : Type} {κ : Type} [Zero κ] {X : VColBipBlk s κ} {Y : VColBipBlk t κ}
  {φ : s ≃ t}

open scoped Classical in
/-- §9.7.  **The hinted restriction is canonical.**  An isomorphism of graphs that carries
the sub-family `U` of the blocks onto `U'` and the hint `c` onto the hint `c'` is an
isomorphism of the hinted restrictions.

This is what makes the exits of Cases 3a1, 3a2 and 3b canonical: both the sub-family they
select and the structure they find on it are defined canonically. -/
theorem restrictBlkHint_isIsoTo (h : X.IsIsoTo Y φ) {U : Set (Set s)} {U' : Set (Set t)}
    {c : Set s → Set s → κ} {c' : Set t → Set t → κ}
    (hU : ∀ B : Set s, φ '' B ∈ U' ↔ B ∈ U)
    (hc : ∀ A B : Set s, A ∈ X.blocks ∩ U → B ∈ X.blocks ∩ U →
      c' (φ '' A) (φ '' B) = c A B) :
    (X.restrictBlkHint U c).IsIsoTo (Y.restrictBlkHint U' c') φ := by
  obtain ⟨hp, hb, he, h1, h2, -⟩ := restrictBlk_isIsoTo h hU (U' := U')
  refine ⟨hp, hb, he, h1, h2, fun A B => ?_⟩
  have hmem : ∀ C : Set s, φ '' C ∈ Y.blocks ∩ U' ↔ C ∈ X.blocks ∩ U := by
    intro C
    exact and_congr (h.blocks C) (hU C)
  show (if φ '' A ∈ Y.blocks ∩ U' ∧ φ '' B ∈ Y.blocks ∩ U' then c' (φ '' A) (φ '' B)
      else 0)
    = (if A ∈ X.blocks ∩ U ∧ B ∈ X.blocks ∩ U then c A B else 0)
  by_cases hAB : A ∈ X.blocks ∩ U ∧ B ∈ X.blocks ∩ U
  · rw [if_pos ⟨(hmem A).2 hAB.1, (hmem B).2 hAB.2⟩, if_pos hAB, hc A B hAB.1 hAB.2]
  · rw [if_neg (fun hcon => hAB ⟨(hmem A).1 hcon.1, (hmem B).1 hcon.2⟩), if_neg hAB]

end VColBipBlk

/-! ### The hint of the restricted object -/

namespace VColBipBlk

variable {s : Type} [Fintype s] [DecidableEq s]

/-- §9.5, §9.7.  **The hinted restriction carries the hint.**  If `P` is a homogeneous
coherent configuration of rank at least `3` on the sub-family `U` of the blocks, then the
restriction to `U` with the hint `Babai.hintColoring U P` has
`Babai.VColBipBlk.HasHint`.

This is the third kind of major progress of §9.5, *"`X₂` moves from clique to UPCC"*: `P`
is the UPCC `Y` of Case 3a2 or the equipartition configuration `Babai.eqvConfig` of
Cases 3a1 and 3b. -/
theorem hasHint_restrictBlkHint {X : VColBipBlk s ℕ} {U : Set (Set s)}
    (hU : U ⊆ X.blocks) (P : PartitionStructure ↥U) (hco : P.IsCoherent)
    (hhom : P.IsHomogeneous) (hrank : 3 ≤ P.rank) :
    (X.restrictBlkHint U (hintColoring U P)).HasHint := by
  classical
  set Z := X.restrictBlkHint U (hintColoring U P) with hZ
  have hbl : Z.blocks = X.blocks ∩ U := rfl
  have hUeq : X.blocks ∩ U = U := Set.inter_eq_self_of_subset_right hU
  -- carry `P` from `↥U` to `↥Z.blocks`
  let e : ↥Z.blocks ≃ ↥U := Equiv.setCongr (hbl.trans hUeq)
  refine VColBipBlk.hasHint_of_structure (P.transport e.symm)
    (PartitionStructure.transport_isCoherent _ hco)
    (PartitionStructure.transport_isHomogeneous _ hhom) hrank (fun A B => ?_)
  have hA : (A : Set s) ∈ X.blocks ∩ U := hbl ▸ A.2
  have hB : (B : Set s) ∈ X.blocks ∩ U := hbl ▸ B.2
  rw [restrictBlkHint_h hA hB]
  have hA' : (A : Set s) ∈ U := hUeq ▸ hA
  have hB' : (B : Set s) ∈ U := hUeq ▸ hB
  have : hintColoring U P (A : Set s) (B : Set s)
      = (P.color ⟨(A : Set s), hA'⟩ ⟨(B : Set s), hB'⟩ : ℕ) :=
    hintColoring_apply U P ⟨(A : Set s), hA'⟩ ⟨(B : Set s), hB'⟩
  rw [this]
  rfl

end VColBipBlk

/-! ### The hinted restriction as an outcome of §9.7 -/

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open BlkBlockDesignInputs in
/-- §9.7.  The input of §9.7 restricted to a sub-family `U` of its blocks, with the
structure found on `U` attached as the hint. -/
noncomputable def restrictObjHint (X : Pt (BlkBlockDesignInputs Ω))
    (U : Set (Set ↥X.car)) (c : Set ↥X.car → Set ↥X.car → ℕ) :
    VColBipBlk ↥X.car ℕ × ℝ :=
  ((obj₀ X).linkGraph.restrictBlkHint U c, alpha X)

open BlkBlockDesignInputs in
/-- §9.7.  **The hinted restricted input is an admissible input of Theorem 9.2.2** for the
same threshold `α`.  The hypotheses are those of `Babai.restrictObj_pred`: the hint does
not enter the symmetry defect of `V₁` (`Babai.VColBipBlk.symDefect₁_congr`). -/
theorem restrictObjHint_pred (X : Pt (BlkBlockDesignInputs Ω)) {U : Set (Set ↥X.car)}
    (c : Set ↥X.car → Set ↥X.car → ℕ)
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁) :
    letI : Fintype ↥X.car := Fintype.ofFinite _
    letI : DecidableEq ↥X.car := Classical.decEq _
    2 / 3 ≤ (restrictObjHint X U c).2 ∧ (restrictObjHint X U c).2 < 1 ∧
      (restrictObjHint X U c).1.IsThm922Input (restrictObjHint X U c).2 := by
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  obtain ⟨hα, hα1, hpred⟩ := restrictObj_pred X hU h3 hdef
  refine ⟨hα, hα1, ?_, ?_, ?_⟩
  · exact hpred.1
  · have hnb : (restrictObjHint X U c).1.numBlocks = U.ncard :=
      VColBipBlk.restrictBlkHint_numBlocks hU
    have hnb' : (restrictObj X U).1.numBlocks = U.ncard :=
      VColBipBlk.restrictBlk_numBlocks hU
    have := hpred.2.1
    rw [hnb', ] at this
    rw [hnb]
    exact this
  · have hd : (restrictObjHint X U c).1.defect₁ = (restrictObj X U).1.defect₁ :=
      VColBipBlk.restrictBlkHint_defect₁ _ _ _
    have := hpred.2.2
    show 1 - (restrictObjHint X U c).2 ≤ (((restrictObjHint X U c).1.defect₁ : ℚ) : ℝ)
    rw [hd]
    exact this

open BlkBlockDesignInputs in
/-- §9.7.  The outcome that the exits *"apply Procedure ImprimitiveCase"* (Cases 3a1, 3b)
and *"go to Sec. 9.8"* (Case 3a2) return: the restricted input with the hint. -/
noncomputable def restrictOutcomeHint (X : Pt (BlkBlockDesignInputs Ω))
    {U : Set (Set ↥X.car)} (c : Set ↥X.car → Set ↥X.car → ℕ)
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁) :
    Pt (Out97 Ω) :=
  ⟨X.car, Sum.inr ⟨restrictObjHint X U c, restrictObjHint_pred X c hU h3 hdef⟩⟩


open BlkBlockDesignInputs in
/-- §9.7.  The outcome lemma of the **second** kind of major progress of §9.5, for the
hinted restriction: with `10|U| ≤ 9n₂` the restricted input is an outcome whatever the
hint is.  This is `Babai.good97_restrict` with the hint attached, so that the four
sub-branches of Case 3a can all return an object of the same shape. -/
theorem good97_restrict_hint_small (X : Pt (BlkBlockDesignInputs Ω))
    {U : Set (Set ↥X.car)} (c : Set ↥X.car → Set ↥X.car → ℕ)
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁)
    (hprog : 10 * U.ncard ≤ 9 * numBlocks X) :
    Good97 X (restrictOutcomeHint X c hU h3 hdef) := by
  refine ⟨subset_rfl, rfl, Or.inl ?_⟩
  show 10 * ((obj₀ X).linkGraph.restrictBlkHint U c).numBlocks ≤ 9 * numBlocks X
  rw [VColBipBlk.restrictBlkHint_numBlocks (X := (obj₀ X).linkGraph) hU]
  exact hprog

open BlkBlockDesignInputs in
/-- §9.7, §9.5.  **The outcome lemma of the third kind of major progress.**  *"`X₂` moves
from clique to UPCC while `n₂` does not increase."*  With `|U| ≤ n₂` and the hint on `U`,
the hinted restricted input is an outcome of §9.7 in the sense of
`Babai.IsBlkDesignOutcome`, through its second alternative.

Its first part is the first part of the input, so it is contained in it and
`α_new |V₁_new| = α |V₁|` holds with `α_new = α`, exactly as in
`Babai.good97_restrict`. -/
theorem good97_restrict_hint (X : Pt (BlkBlockDesignInputs Ω)) {U : Set (Set ↥X.car)}
    (c : Set ↥X.car → Set ↥X.car → ℕ)
    (hU : U ⊆ (obj₀ X).blocks) (h3 : 3 ≤ (obj₀ X).n₁)
    (hdef : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      (((obj₀ X).n₁ : ℚ) - 1) / 2 ≤ ((obj₀ X).linkGraph.restrictBlk U).symDefect₁)
    (hle : U.ncard ≤ numBlocks X)
    (hhint : letI : Fintype ↥X.car := Fintype.ofFinite _
      letI : DecidableEq ↥X.car := Classical.decEq _
      ((obj₀ X).linkGraph.restrictBlkHint U c).HasHint) :
    Good97 X (restrictOutcomeHint X c hU h3 hdef) := by
  refine ⟨subset_rfl, rfl, Or.inr ⟨?_, hhint⟩⟩
  show ((obj₀ X).linkGraph.restrictBlkHint U c).numBlocks ≤ numBlocks X
  rw [VColBipBlk.restrictBlkHint_numBlocks (X := (obj₀ X).linkGraph) hU]
  exact hle

end Babai
