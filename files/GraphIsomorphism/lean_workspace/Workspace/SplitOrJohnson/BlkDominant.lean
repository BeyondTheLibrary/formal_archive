/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 2: the dominant `c'`-color class `A`, and the three exits at it.
-/
import Workspace.SplitOrJohnson.BlkOrbit
import Workspace.SplitOrJohnson.BlkRegular
import Workspace.SplitOrJohnson.KerPart

/-!
# §9.7, Case 2  The dominant `c'`-color class

Version 2.5, lines 4264-4274:

> *"Otherwise, let `A ⊆ V₁` be the dominant `c'`-color class, so `|A| ≥ αn₁ > n₁/2`. …
> Since `Aut(H*)` acts on `C` as the symmetric group, all edges of `H*` have the same
> multiplicity.  In other words, `A` is equipartitioned by the twin equivalence classes in
> `X*`.  If this is a nontrivial partition, return this partition, exit. …  Since `C` is a
> set of twins in `H*`, we are back to Case 1.  Proceed as in Case 1, exit."*

This file does the mathematics of the two exits, on one object of §9.7 and for one
threshold `α`; `Workspace/SplitOrJohnson/BlockDesignCase2.lean` turns it into the two
branches of the reduction.

* `Babai.BlkCaseObj.domClass` is `A`, **as a function of the object**: the union of the
  `c'`-color classes of at least `αn₁` points.  Since `α > 1/2` there is at most one such
  class, so this is the dominant class when there is one
  (`Babai.BlkCaseObj.domClass_eq_localSizeClass`), and it is canonical.
* `Babai.BlkCaseObj.DomHyp` collects the hypotheses in force at that point of §9.7.
* `Babai.BlkCaseObj.one_le_dstar` and `.dstar_lt` are *"`X*` … cannot be trivial"*
  (`Babai.case_9_7_2` through `Workspace/SplitOrJohnson/BlkRegular.lean`): the common trace
  `d* = |X(v) ∩ C|`, `v ∈ A`, satisfies `1 ≤ d* < |C|`.
* `Babai.labPartition` is the colored partition of `V₁` returned at the first exit: its
  color is `c'` and its blocks are the classes of `c'` refined by a label.  The two exits
  use the labels `Babai.BlkCaseObj.domLab` (the trace `X(v) ∩ C`, on `A` only) and
  `Babai.BlkCaseObj.domPairLab` (the unordered pair `{X(v) ∩ C, C ∖ X(v)}`, entry 83 of
  the corrected paper).
* `Babai.BlkCaseObj.domIsJohnsonColoring` is the last exit, *"we are back to Case 1"*.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- A family inside `C` has as many members read inside `C` as read in the ambient type. -/
theorem ncard_coe_of_subset {γ : Type*} {C T : Set γ} (hT : T ⊆ C) :
    {B : ↥C | (B : γ) ∈ T}.ncard = T.ncard := by
  have himg : Subtype.val '' {B : ↥C | (B : γ) ∈ T} = T := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩; exact hB
    · intro hA; exact ⟨⟨A, hT hA⟩, hA, rfl⟩
  have hc := Set.ncard_image_of_injective {B : ↥C | (B : γ) ∈ T} Subtype.val_injective
  rw [himg] at hc
  exact hc.symm

/-! ### A colored partition whose blocks are the classes of a coloring refined by a label

`Babai.kerPartition` is the case of a constant label. -/

/-- §7.1.  The colored partition of `W` whose color is `col` and whose blocks are the
classes of the pair `(col, lab)`: the `col`-classes, each refined by `lab`. -/
def labPartition {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ) (lab : ↥s → β) :
    ColoredPartition ↥(Subtype.val '' W) ℕ where
  color z := col (liftPt z)
  part := Setoid.ker fun z => (col (liftPt z), lab (liftPt z))
  part_le_color h := congrArg Prod.fst h

@[simp] theorem labPartition_color {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ)
    (lab : ↥s → β) (z : ↥(Subtype.val '' W)) :
    (labPartition W col lab).color z = col (liftPt z) := rfl

/-- The block of `Babai.labPartition` at `z`, read inside `↥s`. -/
def labClass {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ) (lab : ↥s → β) (x : ↥s) :
    Set ↥s :=
  {y : ↥s | y ∈ W ∧ col y = col x ∧ lab y = lab x}

theorem liftPt_image_block {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ)
    (lab : ↥s → β) (z : ↥(Subtype.val '' W)) :
    liftPt '' ((labPartition W col lab).block z) = labClass W col lab (liftPt z) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (col (liftPt w), lab (liftPt w)) = (col (liftPt z), lab (liftPt z)) := hw
    exact ⟨liftPt_mem w, congrArg Prod.fst hw', congrArg Prod.snd hw'⟩
  · rintro ⟨hyW, h1, h2⟩
    refine ⟨mkPt hyW, ?_, rfl⟩
    show (col (liftPt (mkPt hyW)), lab (liftPt (mkPt hyW)))
      = (col (liftPt z), lab (liftPt z))
    rw [liftPt_mkPt, h1, h2]

theorem ncard_block_labPartition {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ)
    (lab : ↥s → β) (z : ↥(Subtype.val '' W)) :
    ((labPartition W col lab).block z).ncard = (labClass W col lab (liftPt z)).ncard := by
  rw [← liftPt_image_block W col lab z,
    Set.ncard_image_of_injective _ (liftPt_injective (W := W))]

/-- Definition 7.1.1.  `Babai.labPartition` is admissible as soon as each of its blocks,
read inside `↥s`, has at least two points whenever its color class has. -/
theorem labPartition_isAdmissible {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ)
    (lab : ↥s → β)
    (h : ∀ x ∈ W, 2 ≤ {y : ↥s | y ∈ W ∧ col y = col x}.ncard →
      2 ≤ (labClass W col lab x).ncard) :
    (labPartition W col lab).IsAdmissible := by
  intro z hz
  rw [ncard_block_labPartition]
  refine h (liftPt z) (liftPt_mem z) ?_
  have himg : liftPt '' ((labPartition W col lab).colorClass
      ((labPartition W col lab).color z)) ⊆ {y : ↥s | y ∈ W ∧ col y = col (liftPt z)} := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨liftPt_mem w, hw⟩
  have h1 : ((labPartition W col lab).colorClass ((labPartition W col lab).color z)).ncard
      ≤ {y : ↥s | y ∈ W ∧ col y = col (liftPt z)}.ncard := by
    rw [← Set.ncard_image_of_injective _ (liftPt_injective (W := W))]
    exact Set.ncard_le_ncard himg (Set.toFinite _)
  omega

/-- Definition 7.1.1.  `Babai.labPartition` is a colored `α`-partition as soon as it is
admissible and every block, read inside `↥s`, has at most `α|W|` points. -/
theorem labPartition_isAlphaPartition {s : Set Ω} {β : Type} (W : Set ↥s) (col : ↥s → ℕ)
    (lab : ↥s → β) (iF : Fintype ↥(Subtype.val '' W)) {α : ℝ} (hne : W.Nonempty)
    (hadm : (labPartition W col lab).IsAdmissible)
    (h : ∀ x ∈ W, ((labClass W col lab x).ncard : ℝ) ≤ α * (W.ncard : ℝ)) :
    @ColoredPartition.IsAlphaPartition _ _ (labPartition W col lab) iF α := by
  refine ⟨hadm, ?_⟩
  rw [card_image_val W iF]
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ↥(Subtype.val '' W))
    ⟨mkPt hx₀, Finset.mem_univ _⟩ (fun z => ((labPartition W col lab).block z).ncard)
  have h1 : @ColoredPartition.rho _ _ (labPartition W col lab) iF
      = ((labPartition W col lab).block z).ncard := hz
  rw [h1, ncard_block_labPartition]
  exact h (liftPt z) (liftPt_mem z)

/-- §7.1.  **Canonicity of `Babai.labPartition`**: a bijection that carries `W` onto `W'`,
the coloring `col'` back to `col` and the label `lab'` back to `lab` (as an equivalence
relation, the two labels being allowed to have different types) is a morphism of the two
colored partitions. -/
theorem labPartition_mem_iso {s t : Set Ω} {β γ : Type} (φ : ↥s ≃ ↥t) {W : Set ↥s}
    {W' : Set ↥t} (h : ∀ x, φ x ∈ W' ↔ x ∈ W) {col : ↥s → ℕ} {col' : ↥t → ℕ}
    {lab : ↥s → β} {lab' : ↥t → γ} (hc : ∀ x, col' (φ x) = col x)
    (hl : ∀ x y, lab' (φ x) = lab' (φ y) ↔ lab x = lab y) :
    subEquiv φ h ∈
      (ColoredPartitions Ω ℕ).Iso (labPartition W col lab) (labPartition W' col' lab') := by
  refine ⟨fun z => ?_, fun z w => ?_⟩
  · show col' (liftPt (subEquiv φ h z)) = col (liftPt z)
    rw [liftPt_subEquiv]; exact hc _
  · show ((col (liftPt z), lab (liftPt z)) = (col (liftPt w), lab (liftPt w)))
      ↔ ((col' (liftPt (subEquiv φ h z)), lab' (liftPt (subEquiv φ h z)))
        = (col' (liftPt (subEquiv φ h w)), lab' (liftPt (subEquiv φ h w))))
    rw [liftPt_subEquiv, liftPt_subEquiv, hc, hc, Prod.mk.injEq, Prod.mk.injEq, hl]

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-! ### The dominant `c'`-color class -/

/-- §9.7, Case 2.  A `c'`-color class, `c'` being `Babai.BlkCaseObj.localSize`. -/
def localSizeClass (X : BlkCaseObj s Case) (x : ↥s) : Set ↥s :=
  {y | X.part₁ y ∧ X.localSize y = X.localSize x}

/-- §9.7, Case 2.  ***"the dominant `c'`-color class `A`"***, as a function of the object:
the union of the `c'`-color classes of at least `αn₁` points.  For `α > 1/2` there is at
most one such class, so this is the paper's `A`
(`Babai.BlkCaseObj.domClass_eq_localSizeClass`). -/
def domClass (X : BlkCaseObj s Case) (α : ℝ) : Set ↥s :=
  {x | X.part₁ x ∧ α * (X.n₁ : ℝ) ≤ ((X.localSizeClass x).ncard : ℝ)}

theorem domClass_subset (X : BlkCaseObj s Case) (α : ℝ) :
    X.domClass α ⊆ {x | X.part₁ x} := fun _ hx => hx.1

theorem localSizeClass_subset (X : BlkCaseObj s Case) (x : ↥s) :
    X.localSizeClass x ⊆ {y | X.part₁ y} := fun _ hy => hy.1

theorem localSizeClass_eq (X : BlkCaseObj s Case) {x y : ↥s}
    (h : X.localSize y = X.localSize x) : X.localSizeClass y = X.localSizeClass x := by
  ext z; simp only [localSizeClass, Set.mem_setOf_eq, h]

theorem mem_localSizeClass_self (X : BlkCaseObj s Case) {x : ↥s} (hx : X.part₁ x) :
    x ∈ X.localSizeClass x := ⟨hx, rfl⟩

/-- Two different `c'`-color classes are disjoint. -/
theorem localSizeClass_disjoint (X : BlkCaseObj s Case) {x y : ↥s}
    (h : X.localSize x ≠ X.localSize y) :
    Disjoint (X.localSizeClass x) (X.localSizeClass y) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hz⟩ ⟨-, hz'⟩
  exact h (hz.symm.trans hz')

/-- §9.7, Case 2.  **The dominant class is a `c'`-color class**: since `α > 1/2`, two
classes of at least `αn₁` points would exhaust more than `n₁` points. -/
theorem domClass_eq_localSizeClass (X : BlkCaseObj s Case) {α : ℝ} (hα : 1 / 2 < α)
    (hn₁ : 0 < X.n₁) {x : ↥s} (hx : x ∈ X.domClass α) :
    X.domClass α = X.localSizeClass x := by
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · by_contra hcon
    have hne : X.localSize z ≠ X.localSize x := by
      intro hc; exact hcon ⟨hz.1, hc⟩
    have hd := X.localSizeClass_disjoint hne
    have hsum : (X.localSizeClass z).ncard + (X.localSizeClass x).ncard ≤ X.n₁ := by
      have hun : ((X.localSizeClass z) ∪ (X.localSizeClass x)).ncard
          = (X.localSizeClass z).ncard + (X.localSizeClass x).ncard :=
        Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
      rw [← hun]
      exact Set.ncard_le_ncard
        (Set.union_subset (X.localSizeClass_subset z) (X.localSizeClass_subset x))
        (Set.toFinite _)
    have hsum' : ((X.localSizeClass z).ncard : ℝ) + ((X.localSizeClass x).ncard : ℝ)
        ≤ (X.n₁ : ℝ) := by exact_mod_cast hsum
    have hpos : (0 : ℝ) < (X.n₁ : ℝ) := by exact_mod_cast hn₁
    have h1 := hz.2
    have h2 := hx.2
    nlinarith
  · refine ⟨hz.1, ?_⟩
    rw [X.localSizeClass_eq hz.2]
    exact hx.2

/-! ### The hypotheses in force at the dominant class -/

/-- §9.7, Case 2, at the dominant `c'`-color class: the hypotheses in force.  The first
three are the standing hypotheses of Theorem 9.2.2 carried by an admissible input of §9.7,
the next two are the branch conditions of Case 2 and of the canonical choice of `C`
(entry 100 of the corrected paper), and the last is the branch condition of this exit,
*"some `c'`-color class has at least `αn₁` points"*. -/
structure DomHyp (X : BlkDesignObj s) (α : ℝ) : Prop where
  /-- *"`2/3 ≤ α`"*. -/
  alpha_ge : 2 / 3 ≤ α
  /-- *"`α < 1`"*. -/
  alpha_lt : α < 1
  /-- *"`|V₂| < α|V₁|`"*. -/
  numBlocks_lt : (X.n₂ : ℝ) < α * (X.n₁ : ℝ)
  /-- The branch condition of Case 2. -/
  case2 : X.IsCase2
  /-- The class `C` is unique (`Babai.BlkCaseObj.bigTwin` is not all of `V₂`). -/
  notTie : X.bigTwin ≠ X.blocks
  /-- The branch condition of this exit. -/
  dom : (X.domClass α).Nonempty

namespace DomHyp

variable {X : BlkDesignObj s} {α : ℝ} (h : DomHyp X α)
include h

theorem one_le_n₁ : 1 ≤ X.n₁ := by
  obtain ⟨x, hx⟩ := X.part₁_nonempty
  have : 0 < X.n₁ := (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hx⟩
  omega

theorem one_le_n₂ : 1 ≤ X.n₂ :=
  (Set.ncard_pos (Set.toFinite _)).2 (BlkBlockDesignInputs.blocks_nonempty_of_case X.case)

theorem alpha_gt_half : 1 / 2 < α := by have := h.alpha_ge; linarith

/-- The four clauses of `Babai.BlkCaseObj.bigTwin_spec` under these hypotheses. -/
theorem twin_pairwise : ∀ B ∈ X.bigTwin, ∀ B' ∈ X.bigTwin, X.IsHTwin B B' :=
  (X.bigTwin_spec h.case2 h.notTie).2.2.1

theorem two_mul_bigTwin : X.n₂ ≤ 2 * X.bigTwin.ncard :=
  (X.bigTwin_spec h.case2 h.notTie).2.1

/-- `A` is the `c'`-color class of each of its points. -/
theorem domClass_eq {x : ↥s} (hx : x ∈ X.domClass α) :
    X.domClass α = X.localSizeClass x :=
  X.domClass_eq_localSizeClass h.alpha_gt_half h.one_le_n₁ hx

/-- *"`|A| ≥ αn₁`"*. -/
theorem alpha_le_ncard_domClass : α * (X.n₁ : ℝ) ≤ ((X.domClass α).ncard : ℝ) := by
  obtain ⟨x, hx⟩ := h.dom
  rw [h.domClass_eq hx]
  exact hx.2

/-- *"`|A| ≥ αn₁ > n₁/2`"*, read in `ℕ`: `2|A| > n₁`, and even `3|A| ≥ 2n₁`. -/
theorem two_mul_n₁_le : 2 * X.n₁ ≤ 3 * (X.domClass α).ncard := by
  have h1 := h.alpha_le_ncard_domClass
  have h2 : (2 : ℝ) / 3 * (X.n₁ : ℝ) ≤ ((X.domClass α).ncard : ℝ) := by
    have hn : (0 : ℝ) ≤ (X.n₁ : ℝ) := Nat.cast_nonneg _
    nlinarith [h.alpha_ge]
  have : (2 * X.n₁ : ℝ) ≤ (3 * (X.domClass α).ncard : ℝ) := by push_cast; linarith
  exact_mod_cast this

theorem n₁_lt_two_mul : X.n₁ < 2 * (X.domClass α).ncard := by
  have h1 := h.alpha_le_ncard_domClass
  have hn : (0 : ℝ) < (X.n₁ : ℝ) := by exact_mod_cast h.one_le_n₁
  have h2 : (X.n₁ : ℝ) < 2 * ((X.domClass α).ncard : ℝ) := by
    nlinarith [h.alpha_gt_half]
  exact_mod_cast h2

/-- `|C| < |A|`: `|C| ≤ n₂ < αn₁ ≤ |A|`.  This is what replaces the standing hypothesis
`n₂ < n₁` of Case 1 when Case 1 is re-entered on `X*`. -/
theorem bigTwin_ncard_lt : X.bigTwin.ncard < (X.domClass α).ncard := by
  have h1 : X.bigTwin.ncard ≤ X.n₂ :=
    Set.ncard_le_ncard X.bigTwin_subset_blocks (Set.toFinite _)
  have h2 := h.alpha_le_ncard_domClass
  have h3 := h.numBlocks_lt
  have h1' : (X.bigTwin.ncard : ℝ) ≤ (X.n₂ : ℝ) := by exact_mod_cast h1
  have : (X.bigTwin.ncard : ℝ) < ((X.domClass α).ncard : ℝ) := by linarith
  exact_mod_cast this

/-! ### *"`X*` … cannot be trivial"* -/

/-- §9.7, Case 2.  *"the relative sizes of `A` (in `V₁`) and `C` (in `V₂`) add up to more
than 1"*: `|A|/n₁ ≥ 2/3` and `|C|/n₂ ≥ 1/2`. -/
theorem sizes_gt_one :
    1 < (((X.domClass α).ncard : ℚ)) / ((X.n₁ : ℚ)) + ((X.bigTwin.ncard : ℚ)) / ((X.n₂ : ℚ)) := by
  have hn₁ : (0 : ℚ) < (X.n₁ : ℚ) := by exact_mod_cast h.one_le_n₁
  have hn₂ : (0 : ℚ) < (X.n₂ : ℚ) := by exact_mod_cast h.one_le_n₂
  have e1 : (2 : ℚ) / 3 ≤ (((X.domClass α).ncard : ℚ)) / ((X.n₁ : ℚ)) := by
    rw [le_div_iff₀ hn₁]
    have := h.two_mul_n₁_le
    have : (2 * X.n₁ : ℚ) ≤ (3 * (X.domClass α).ncard : ℚ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  have e2 : (1 : ℚ) / 2 ≤ ((X.bigTwin.ncard : ℚ)) / ((X.n₂ : ℚ)) := by
    rw [le_div_iff₀ hn₂]
    have := h.two_mul_bigTwin
    have : (X.n₂ : ℚ) ≤ (2 * X.bigTwin.ncard : ℚ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith
  linarith

/-- §9.7, Case 2.  ***"`X*` … cannot be trivial"***, the edge half: `d* ≥ 1`. -/
theorem one_le_localSize {x : ↥s} (hx : x ∈ X.domClass α) : 1 ≤ X.localSize x := by
  obtain ⟨y, hy, B, hB, hBy⟩ := X.exists_mem_nbhd_of_sizes (X.domClass_subset α)
    X.bigTwin_subset_blocks h.sizes_gt_one
  have hxy : X.localSize y = X.localSize x := by
    have : y ∈ X.localSizeClass x := (h.domClass_eq hx) ▸ hy
    exact this.2
  rw [← hxy]
  have : (X.nbhd y ∩ X.bigTwin).Nonempty := ⟨B, hBy, hB⟩
  exact (Set.ncard_pos (Set.toFinite _)).2 this

/-- §9.7, Case 2.  ***"`X*` … cannot be trivial"***, the non-edge half: `d* < |C|`. -/
theorem localSize_lt {x : ↥s} (hx : x ∈ X.domClass α) :
    X.localSize x < X.bigTwin.ncard := by
  obtain ⟨y, hy, B, hB, hBy⟩ := X.exists_notMem_nbhd_of_sizes (X.domClass_subset α)
    X.bigTwin_subset_blocks h.sizes_gt_one
  have hxy : X.localSize y = X.localSize x := by
    have : y ∈ X.localSizeClass x := (h.domClass_eq hx) ▸ hy
    exact this.2
  rw [← hxy]
  refine Set.ncard_lt_ncard ⟨Set.inter_subset_right, fun hc => hBy (hc hB).1⟩ (Set.toFinite _)

/-! ### The trace classes inside `A` -/

theorem traceClass_subset_domClass {x : ↥s} (hx : x ∈ X.domClass α) {T : Set (Set ↥s)}
    (hcard : T.ncard = X.localSize x) : X.traceClass T ⊆ X.domClass α := by
  rintro y ⟨hy, hTy⟩
  rw [h.domClass_eq hx]
  refine ⟨hy, ?_⟩
  show (X.nbhd y ∩ X.bigTwin).ncard = X.localSize x
  rw [hTy, hcard]

theorem mem_traceClass_self {y : ↥s} (hy : X.part₁ y) :
    y ∈ X.traceClass (X.nbhd y ∩ X.bigTwin) := ⟨hy, rfl⟩

/-- §9.7, Case 2.  ***"`A` is equipartitioned by the twin equivalence classes in `X*`"***:
the trace classes of the points of `A` all have the same number of points. -/
theorem ncard_traceClass_eq_of_mem {x y : ↥s} (hx : x ∈ X.domClass α)
    (hy : y ∈ X.domClass α) :
    (X.traceClass (X.nbhd x ∩ X.bigTwin)).ncard
      = (X.traceClass (X.nbhd y ∩ X.bigTwin)).ncard := by
  refine X.ncard_traceClass_eq h.twin_pairwise Set.inter_subset_right Set.inter_subset_right ?_
  have hxy : X.localSize y = X.localSize x := by
    have : y ∈ X.localSizeClass x := (h.domClass_eq hx) ▸ hy
    exact this.2
  exact hxy.symm

/-- §9.7, Case 2.  A second trace of the same size inside `C`: `d*` is neither `0` nor
`|C|`, so one member of the trace may be exchanged for one outside it. -/
theorem exists_other_trace {x : ↥s} (hx : x ∈ X.domClass α) :
    ∃ T ⊆ X.bigTwin, T.ncard = X.localSize x ∧ T ≠ X.nbhd x ∩ X.bigTwin := by
  have h1 : (X.nbhd x ∩ X.bigTwin).Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    have := h.one_le_localSize hx
    have hls : (X.nbhd x ∩ X.bigTwin).ncard = X.localSize x := rfl
    show (X.nbhd x ∩ X.bigTwin).ncard ≠ 0
    omega
  obtain ⟨B, hB⟩ := h1
  have h2 : (X.bigTwin \ (X.nbhd x ∩ X.bigTwin)).Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    have hlt := h.localSize_lt hx
    have hsub : X.nbhd x ∩ X.bigTwin ⊆ X.bigTwin := Set.inter_subset_right
    have := Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
    have hls : (X.nbhd x ∩ X.bigTwin).ncard = X.localSize x := rfl
    omega
  obtain ⟨B', hB'C, hB'⟩ := h2
  refine ⟨swapIn B B' (X.nbhd x ∩ X.bigTwin), ?_, ?_, ?_⟩
  · exact swapIn_subset_of_subset hB.2 hB'C Set.inter_subset_right
  · rw [swapIn_eq_insert hB hB',
      Set.ncard_insert_of_notMem (fun hc => hB' hc.1) (Set.toFinite _),
      Set.ncard_diff_singleton_of_mem hB]
    have := h.one_le_localSize hx
    have hls : (X.nbhd x ∩ X.bigTwin).ncard = X.localSize x := rfl
    omega
  · intro hc
    have hBmem : B ∈ swapIn B B' (X.nbhd x ∩ X.bigTwin) := by rw [hc]; exact hB
    rw [swapIn_eq_insert hB hB'] at hBmem
    rcases hBmem with h' | h'
    · exact hB' (h' ▸ hB)
    · exact h'.2 rfl

/-- §9.7, Case 2.  A trace class inside `A` has at most half of `A`: there is a second
trace class of the same size (`Babai.BlkCaseObj.DomHyp.exists_other_trace`), disjoint from
it and inside `A`. -/
theorem two_mul_ncard_traceClass_le {x : ↥s} (hx : x ∈ X.domClass α) :
    2 * (X.traceClass (X.nbhd x ∩ X.bigTwin)).ncard ≤ (X.domClass α).ncard := by
  obtain ⟨T, hTC, hTcard, hTne⟩ := h.exists_other_trace hx
  have heq : (X.traceClass T).ncard = (X.traceClass (X.nbhd x ∩ X.bigTwin)).ncard :=
    X.ncard_traceClass_eq h.twin_pairwise hTC Set.inter_subset_right (by rw [hTcard]; rfl)
  have hd : Disjoint (X.traceClass (X.nbhd x ∩ X.bigTwin)) (X.traceClass T) := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hz⟩ ⟨-, hz'⟩
    exact hTne (hz' ▸ hz)
  have hsub : X.traceClass (X.nbhd x ∩ X.bigTwin) ∪ X.traceClass T ⊆ X.domClass α :=
    Set.union_subset (h.traceClass_subset_domClass hx rfl) (h.traceClass_subset_domClass hx hTcard)
  have hun : (X.traceClass (X.nbhd x ∩ X.bigTwin) ∪ X.traceClass T).ncard
      = (X.traceClass (X.nbhd x ∩ X.bigTwin)).ncard + (X.traceClass T).ncard :=
    Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end DomHyp

/-! ### The label of the first exit: the trace `X(v) ∩ C`, on `A` only

The partition returned at the first exit is the `c'`-partition of `V₁` with the class `A`
replaced by the twin classes of `X*` inside it (entry 80 of the corrected paper).  Outside `A`
the label is constant, so the blocks there are the `c'`-color classes themselves. -/

open scoped Classical in
/-- §9.7, Case 2, the first exit.  The label refining the `c'`-coloring: the trace
`X(v) ∩ C` for `v ∈ A`, and nothing outside `A`. -/
noncomputable def domLab (X : BlkCaseObj s Case) (α : ℝ) (x : ↥s) : Set (Set (Set ↥s)) :=
  if x ∈ X.domClass α then {X.nbhd x ∩ X.bigTwin} else ∅

open scoped Classical in
/-- §9.7, Case 2, the boundary exit `|C| = 2d*` (entry 83 of the corrected paper).  The label
refining the `c'`-coloring: the **unordered pair** `{X(v) ∩ C, C ∖ X(v)}` for `v ∈ A`, and
nothing outside `A`. -/
noncomputable def domPairLab (X : BlkCaseObj s Case) (α : ℝ) (x : ↥s) :
    Set (Set (Set ↥s)) :=
  if x ∈ X.domClass α then {X.nbhd x ∩ X.bigTwin, X.bigTwin \ (X.nbhd x ∩ X.bigTwin)}
  else ∅

end BlkCaseObj

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- §9.7, Case 2.  **The dominant class `A` is canonical**: it is read off the canonical
coloring `c'` (`Babai.BlkCaseObj.IsMorphOn.localSize_eq`) and `n₁`. -/
theorem IsMorphOn.mem_domClass_iff (h : X.IsMorphOn Y φ) (α : ℝ) (x : ↥s) :
    φ x ∈ Y.domClass α ↔ x ∈ X.domClass α := by
  show (Y.part₁ (φ x) ∧ α * (Y.n₁ : ℝ) ≤ ((Y.localSizeClass (φ x)).ncard : ℝ))
    ↔ (X.part₁ x ∧ α * (X.n₁ : ℝ) ≤ ((X.localSizeClass x).ncard : ℝ))
  rw [h.part₁ x, h.n₁_eq]
  have : (Y.localSizeClass (φ x)).ncard = (X.localSizeClass x).ncard :=
    h.ncard_localSizeClass x
  rw [this]

/-- §9.7, Case 2.  `|C|` is an isomorphism invariant. -/
theorem IsMorphOn.ncard_bigTwin_eq (h : X.IsMorphOn Y φ) :
    Y.bigTwin.ncard = X.bigTwin.ncard := by
  rw [h.bigTwin_image_eq, Set.ncard_image_of_injective _ (imgEquiv φ).injective]

/-- §9.7, Case 2.  The trace `X(v) ∩ C` is carried to the trace of the image. -/
theorem IsMorphOn.trace_eq (h : X.IsMorphOn Y φ) (x : ↥s) :
    Y.nbhd (φ x) ∩ Y.bigTwin = imgEquiv φ '' (X.nbhd x ∩ X.bigTwin) := by
  rw [h.nbhd_eq x, h.bigTwin_image_eq, ← Set.image_inter (imgEquiv φ).injective]

theorem image_image_imgEquiv_injective (φ : ↥s ≃ ↥t) :
    Function.Injective
      (fun F : Set (Set (Set ↥s)) => (fun T => imgEquiv φ '' T) '' F) :=
  Set.image_injective.2 (image_imgEquiv_injective φ)

/-- §9.7, Case 2.  The label of the first exit is canonical. -/
theorem IsMorphOn.domLab_eq (h : X.IsMorphOn Y φ) (α : ℝ) (x : ↥s) :
    Y.domLab α (φ x) = (fun T => imgEquiv φ '' T) '' (X.domLab α x) := by
  classical
  show (if φ x ∈ Y.domClass α then {Y.nbhd (φ x) ∩ Y.bigTwin} else ∅)
    = (fun T => imgEquiv φ '' T) '' (if x ∈ X.domClass α then {X.nbhd x ∩ X.bigTwin} else ∅)
  by_cases hx : x ∈ X.domClass α
  · rw [if_pos hx, if_pos ((h.mem_domClass_iff α x).2 hx), Set.image_singleton, h.trace_eq x]
  · rw [if_neg hx, if_neg (fun hc => hx ((h.mem_domClass_iff α x).1 hc)), Set.image_empty]

/-- §9.7, Case 2.  The label of the boundary exit is canonical. -/
theorem IsMorphOn.domPairLab_eq (h : X.IsMorphOn Y φ) (α : ℝ) (x : ↥s) :
    Y.domPairLab α (φ x) = (fun T => imgEquiv φ '' T) '' (X.domPairLab α x) := by
  classical
  show (if φ x ∈ Y.domClass α then
      {Y.nbhd (φ x) ∩ Y.bigTwin, Y.bigTwin \ (Y.nbhd (φ x) ∩ Y.bigTwin)} else ∅)
    = (fun T => imgEquiv φ '' T) '' (if x ∈ X.domClass α then
      {X.nbhd x ∩ X.bigTwin, X.bigTwin \ (X.nbhd x ∩ X.bigTwin)} else ∅)
  by_cases hx : x ∈ X.domClass α
  · rw [if_pos hx, if_pos ((h.mem_domClass_iff α x).2 hx), Set.image_pair, h.trace_eq x,
      h.bigTwin_image_eq, ← Set.image_diff (imgEquiv φ).injective]
  · rw [if_neg hx, if_neg (fun hc => hx ((h.mem_domClass_iff α x).1 hc)), Set.image_empty]

theorem IsMorphOn.domLab_iff (h : X.IsMorphOn Y φ) (α : ℝ) (x y : ↥s) :
    Y.domLab α (φ x) = Y.domLab α (φ y) ↔ X.domLab α x = X.domLab α y := by
  rw [h.domLab_eq α x, h.domLab_eq α y]
  exact ⟨fun hc => image_image_imgEquiv_injective φ hc, fun hc => by rw [hc]⟩

theorem IsMorphOn.domPairLab_iff (h : X.IsMorphOn Y φ) (α : ℝ) (x y : ↥s) :
    Y.domPairLab α (φ x) = Y.domPairLab α (φ y) ↔ X.domPairLab α x = X.domPairLab α y := by
  rw [h.domPairLab_eq α x, h.domPairLab_eq α y]
  exact ⟨fun hc => image_image_imgEquiv_injective φ hc, fun hc => by rw [hc]⟩

end BlkCaseObj

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

namespace DomHyp

variable {X : BlkDesignObj s} {α : ℝ} (h : DomHyp X α)
include h

/-! ### The blocks of the partition returned at the first exit -/

theorem notMem_domClass_of_localSize {x y : ↥s} (hx : X.part₁ x) (hx' : x ∉ X.domClass α)
    (hy : X.part₁ y) (hxy : X.localSize y = X.localSize x) : y ∉ X.domClass α := by
  intro hc
  refine hx' ?_
  rw [h.domClass_eq hc]
  exact ⟨hx, hxy.symm⟩

theorem labClass_domLab_of_mem {x : ↥s} (hx : x ∈ X.domClass α) :
    labClass {x | X.part₁ x} X.localSize (X.domLab α) x
      = X.traceClass (X.nbhd x ∩ X.bigTwin) := by
  classical
  have hlabx : X.domLab α x = {X.nbhd x ∩ X.bigTwin} := if_pos hx
  ext y
  constructor
  · rintro ⟨hy, -, hlab⟩
    have hyA : y ∈ X.domClass α := by
      by_contra hc
      rw [hlabx, show X.domLab α y = ∅ from if_neg hc] at hlab
      exact absurd hlab.symm (Set.singleton_ne_empty _)
    have hlaby : X.domLab α y = {X.nbhd y ∩ X.bigTwin} := if_pos hyA
    rw [hlaby, hlabx] at hlab
    exact ⟨hy, Set.singleton_injective hlab⟩
  · rintro ⟨hy, hTy⟩
    have hyA : y ∈ X.domClass α := h.traceClass_subset_domClass hx rfl ⟨hy, hTy⟩
    refine ⟨hy, ?_, ?_⟩
    · show (X.nbhd y ∩ X.bigTwin).ncard = (X.nbhd x ∩ X.bigTwin).ncard
      rw [hTy]
    · rw [show X.domLab α y = {X.nbhd y ∩ X.bigTwin} from if_pos hyA, hlabx, hTy]

theorem labClass_domLab_of_notMem {x : ↥s} (hx : X.part₁ x) (hx' : x ∉ X.domClass α) :
    labClass {x | X.part₁ x} X.localSize (X.domLab α) x = X.localSizeClass x := by
  classical
  ext y
  constructor
  · rintro ⟨hy, hc, -⟩; exact ⟨hy, hc⟩
  · rintro ⟨hy, hc⟩
    refine ⟨hy, hc, ?_⟩
    rw [show X.domLab α y = ∅ from if_neg (h.notMem_domClass_of_localSize hx hx' hy hc),
      show X.domLab α x = ∅ from if_neg hx']

/-- §9.7, Case 2, the first exit.  A block inside `A` is a twin class of `X*`, and has at
least two points as soon as one of them has. -/
theorem two_le_ncard_traceClass {u v : ↥s} (hu : u ∈ X.domClass α) (hv : v ∈ X.domClass α)
    (huv : u ≠ v) (htr : X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin) {x : ↥s}
    (hx : x ∈ X.domClass α) : 2 ≤ (X.traceClass (X.nbhd x ∩ X.bigTwin)).ncard := by
  have hsub : ({u, v} : Set ↥s) ⊆ X.traceClass (X.nbhd u ∩ X.bigTwin) := by
    rintro z (rfl | rfl)
    · exact ⟨hu.1, rfl⟩
    · exact ⟨hv.1, htr.symm⟩
  have h2 : 2 ≤ (X.traceClass (X.nbhd u ∩ X.bigTwin)).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair huv] at this
  rw [h.ncard_traceClass_eq_of_mem hx hu]
  exact h2

/-- §9.7, Case 2, the first exit.  Every block has at most `αn₁` points: a block inside `A`
has at most `|A|/2 ≤ n₁/2` points, and a block outside `A` is a `c'`-color class other than
`A`, which has fewer than `αn₁` points by the definition of `A`. -/
theorem ncard_labClass_domLab_le {x : ↥s} (hx : X.part₁ x) :
    ((labClass {x | X.part₁ x} X.localSize (X.domLab α) x).ncard : ℝ) ≤ α * (X.n₁ : ℝ) := by
  by_cases hxA : x ∈ X.domClass α
  · rw [h.labClass_domLab_of_mem hxA]
    have h1 := h.two_mul_ncard_traceClass_le hxA
    have h2 : (X.domClass α).ncard ≤ X.n₁ :=
      Set.ncard_le_ncard (X.domClass_subset α) (Set.toFinite _)
    exact le_of_lt (blkDesignOutcome_alphaClass h.alpha_ge h.one_le_n₁ (by omega))
  · rw [h.labClass_domLab_of_notMem hx hxA]
    have : ¬ (α * (X.n₁ : ℝ) ≤ ((X.localSizeClass x).ncard : ℝ)) := fun hc => hxA ⟨hx, hc⟩
    linarith [not_le.1 this]

/-- §9.7, Case 2, the first exit.  ***"`A` is equipartitioned by the twin equivalence
classes in `X*`.  If this is a nontrivial partition, return this partition, exit."***  The
returned partition is a colored `α`-partition of `V₁` (Def. 7.1.1); see entry 80 of
the corrected paper why it is given on `V₁` and not on `A`. -/
theorem domLabPartition_isAlphaPartition (iF : Fintype ↥(Subtype.val '' {x | X.part₁ x}))
    {u v : ↥s} (hu : u ∈ X.domClass α) (hv : v ∈ X.domClass α) (huv : u ≠ v)
    (htr : X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin) :
    @ColoredPartition.IsAlphaPartition _ _
      (labPartition {x | X.part₁ x} X.localSize (X.domLab α)) iF α := by
  obtain ⟨x₀, hx₀⟩ := X.part₁_nonempty
  refine labPartition_isAlphaPartition _ _ _ iF ⟨x₀, hx₀⟩ ?_ (fun x hx => ?_)
  · refine labPartition_isAdmissible _ _ _ (fun x hx hcl => ?_)
    by_cases hxA : x ∈ X.domClass α
    · rw [h.labClass_domLab_of_mem hxA]
      exact h.two_le_ncard_traceClass hu hv huv htr hxA
    · rw [h.labClass_domLab_of_notMem hx hxA]
      exact hcl
  · exact h.ncard_labClass_domLab_le hx


/-! ### The blocks of the partition returned at the boundary exit `|C| = 2d*` -/

/-- The complement of the trace inside `C` has `|C| − d* = d*` blocks. -/
theorem ncard_compl_trace {x : ↥s} (hC : X.bigTwin.ncard = 2 * X.localSize x) :
    (X.bigTwin \ (X.nbhd x ∩ X.bigTwin)).ncard = X.localSize x := by
  have hsub : X.nbhd x ∩ X.bigTwin ⊆ X.bigTwin := Set.inter_subset_right
  have := Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
  have hls : (X.nbhd x ∩ X.bigTwin).ncard = X.localSize x := rfl
  omega

theorem trace_ne_compl {x : ↥s} (hx : x ∈ X.domClass α) :
    X.nbhd x ∩ X.bigTwin ≠ X.bigTwin \ (X.nbhd x ∩ X.bigTwin) := by
  intro hc
  have h1 := h.one_le_localSize hx
  have hempty : X.nbhd x ∩ X.bigTwin = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro B hB
    have : B ∈ X.bigTwin \ (X.nbhd x ∩ X.bigTwin) := hc ▸ hB
    exact this.2 hB
  have hls : (X.nbhd x ∩ X.bigTwin).ncard = X.localSize x := rfl
  rw [hempty, Set.ncard_empty] at hls
  omega

theorem labClass_domPairLab_of_mem {x : ↥s} (hx : x ∈ X.domClass α)
    (hC : X.bigTwin.ncard = 2 * X.localSize x) :
    labClass {x | X.part₁ x} X.localSize (X.domPairLab α) x
      = X.traceClass (X.nbhd x ∩ X.bigTwin)
        ∪ X.traceClass (X.bigTwin \ (X.nbhd x ∩ X.bigTwin)) := by
  classical
  have hcompl := h.ncard_compl_trace (x := x) hC
  have hsub : X.nbhd x ∩ X.bigTwin ⊆ X.bigTwin := Set.inter_subset_right
  have hlabx : X.domPairLab α x
      = {X.nbhd x ∩ X.bigTwin, X.bigTwin \ (X.nbhd x ∩ X.bigTwin)} := if_pos hx
  ext y
  constructor
  · rintro ⟨hy, -, hlab⟩
    have hyA : y ∈ X.domClass α := by
      by_contra hc
      rw [hlabx, show X.domPairLab α y = ∅ from if_neg hc] at hlab
      have : X.nbhd x ∩ X.bigTwin ∈ (∅ : Set (Set (Set ↥s))) := by
        rw [hlab]; exact Set.mem_insert _ _
      exact this
    have hlaby : X.domPairLab α y
        = {X.nbhd y ∩ X.bigTwin, X.bigTwin \ (X.nbhd y ∩ X.bigTwin)} := if_pos hyA
    rw [hlaby, hlabx] at hlab
    have hmem : X.nbhd y ∩ X.bigTwin
        ∈ ({X.nbhd x ∩ X.bigTwin, X.bigTwin \ (X.nbhd x ∩ X.bigTwin)} :
          Set (Set (Set ↥s))) := by
      rw [← hlab]; exact Set.mem_insert _ _
    rcases hmem with h' | h'
    · exact Or.inl ⟨hy, h'⟩
    · exact Or.inr ⟨hy, h'⟩
  · rintro (⟨hy, hTy⟩ | ⟨hy, hTy⟩)
    · have hyA : y ∈ X.domClass α := h.traceClass_subset_domClass hx rfl ⟨hy, hTy⟩
      refine ⟨hy, ?_, ?_⟩
      · show (X.nbhd y ∩ X.bigTwin).ncard = (X.nbhd x ∩ X.bigTwin).ncard
        rw [hTy]
      · rw [show X.domPairLab α y
          = {X.nbhd y ∩ X.bigTwin, X.bigTwin \ (X.nbhd y ∩ X.bigTwin)} from if_pos hyA,
          hlabx, hTy]
    · have hyA : y ∈ X.domClass α :=
        h.traceClass_subset_domClass hx hcompl ⟨hy, hTy⟩
      refine ⟨hy, ?_, ?_⟩
      · show (X.nbhd y ∩ X.bigTwin).ncard = (X.nbhd x ∩ X.bigTwin).ncard
        rw [hTy, hcompl]
        exact rfl
      · rw [show X.domPairLab α y
          = {X.nbhd y ∩ X.bigTwin, X.bigTwin \ (X.nbhd y ∩ X.bigTwin)} from if_pos hyA,
          hlabx, hTy, Set.diff_diff_cancel_left hsub, Set.pair_comm]

theorem labClass_domPairLab_of_notMem {x : ↥s} (hx : X.part₁ x) (hx' : x ∉ X.domClass α) :
    labClass {x | X.part₁ x} X.localSize (X.domPairLab α) x = X.localSizeClass x := by
  classical
  ext y
  constructor
  · rintro ⟨hy, hc, -⟩; exact ⟨hy, hc⟩
  · rintro ⟨hy, hc⟩
    refine ⟨hy, hc, ?_⟩
    rw [show X.domPairLab α y = ∅
        from if_neg (h.notMem_domClass_of_localSize hx hx' hy hc),
      show X.domPairLab α x = ∅ from if_neg hx']

/-- §9.7, Case 2, the boundary exit.  Under the hypothesis that `X*` has no twins in `A`,
a trace class inside `A` is a single point. -/
theorem traceClass_eq_singleton
    (hinj : ∀ u ∈ X.domClass α, ∀ v ∈ X.domClass α,
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v)
    {x : ↥s} (hx : x ∈ X.domClass α) :
    X.traceClass (X.nbhd x ∩ X.bigTwin) = {x} := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · have hyA : y ∈ X.domClass α := h.traceClass_subset_domClass hx rfl hy
    exact hinj y hyA x hx hy.2
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hx.1, rfl⟩

/-- §9.7, Case 2, the boundary exit (entry 83 of the corrected paper).  For `|C| = 2d*` the
blocks inside `A` are the **complementary pairs** `{T, C ∖ T}`, and they have exactly two
points. -/
theorem ncard_labClass_domPairLab
    (hinj : ∀ u ∈ X.domClass α, ∀ v ∈ X.domClass α,
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v)
    {x : ↥s} (hx : x ∈ X.domClass α) (hC : X.bigTwin.ncard = 2 * X.localSize x) :
    (labClass {x | X.part₁ x} X.localSize (X.domPairLab α) x).ncard = 2 := by
  have hcompl := h.ncard_compl_trace (x := x) hC
  have hne : (X.traceClass (X.bigTwin \ (X.nbhd x ∩ X.bigTwin))).Nonempty :=
    X.exists_traceClass h.twin_pairwise hx.1 Set.diff_subset hcompl
  obtain ⟨w, hw⟩ := hne
  have hwA : w ∈ X.domClass α := h.traceClass_subset_domClass hx hcompl hw
  have hw' : X.traceClass (X.bigTwin \ (X.nbhd x ∩ X.bigTwin)) = {w} := by
    have : X.nbhd w ∩ X.bigTwin = X.bigTwin \ (X.nbhd x ∩ X.bigTwin) := hw.2
    rw [← this]
    exact h.traceClass_eq_singleton hinj hwA
  have hxw : x ≠ w := by
    intro hc
    subst hc
    exact h.trace_ne_compl hx hw.2
  rw [h.labClass_domPairLab_of_mem hx hC, h.traceClass_eq_singleton hinj hx, hw',
    Set.singleton_union, Set.ncard_pair hxw]

/-- `n₁ ≥ 3` at the boundary exit: `n₁ > n₂ ≥ |C| = 2d* ≥ 2`. -/
theorem three_le_n₁ {x : ↥s} (hx : x ∈ X.domClass α)
    (hC : X.bigTwin.ncard = 2 * X.localSize x) : 3 ≤ X.n₁ := by
  have h1 := h.one_le_localSize hx
  have h2 : X.bigTwin.ncard ≤ X.n₂ :=
    Set.ncard_le_ncard X.bigTwin_subset_blocks (Set.toFinite _)
  have h3 : (X.n₂ : ℝ) < (X.n₁ : ℝ) := by
    have hn : (0 : ℝ) ≤ (X.n₁ : ℝ) := Nat.cast_nonneg _
    nlinarith [h.numBlocks_lt, h.alpha_lt]
  have h3' : X.n₂ < X.n₁ := by exact_mod_cast h3
  omega

/-- §9.7, Case 2, the boundary exit (entry 83 of the corrected paper).  ***"return instead the
canonical equipartition of `A` into the complementary pairs"***: the partition of `V₁` by
`c'` with `A` refined by the pairs `{X(v) ∩ C, C ∖ X(v)}` is a colored `α`-partition. -/
theorem domPairPartition_isAlphaPartition (iF : Fintype ↥(Subtype.val '' {x | X.part₁ x}))
    (hinj : ∀ u ∈ X.domClass α, ∀ v ∈ X.domClass α,
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v)
    {x₀ : ↥s} (hx₀ : x₀ ∈ X.domClass α)
    (hC : X.bigTwin.ncard = 2 * X.localSize x₀) :
    @ColoredPartition.IsAlphaPartition _ _
      (labPartition {x | X.part₁ x} X.localSize (X.domPairLab α)) iF α := by
  have hCx : ∀ x ∈ X.domClass α, X.bigTwin.ncard = 2 * X.localSize x := by
    intro x hx
    have : x ∈ X.localSizeClass x₀ := (h.domClass_eq hx₀) ▸ hx
    rw [hC, this.2]
  obtain ⟨y₀, hy₀⟩ := X.part₁_nonempty
  have h2α : (2 : ℝ) ≤ α * (X.n₁ : ℝ) := by
    have h3 : (3 : ℝ) ≤ (X.n₁ : ℝ) := by exact_mod_cast h.three_le_n₁ hx₀ hC
    nlinarith [h.alpha_ge]
  refine labPartition_isAlphaPartition _ _ _ iF ⟨y₀, hy₀⟩ ?_ (fun x hx => ?_)
  · refine labPartition_isAdmissible _ _ _ (fun x hx hcl => ?_)
    by_cases hxA : x ∈ X.domClass α
    · rw [h.ncard_labClass_domPairLab hinj hxA (hCx x hxA)]
    · rw [h.labClass_domPairLab_of_notMem hx hxA]
      exact hcl
  · show ((labClass {x | X.part₁ x} X.localSize (X.domPairLab α) x).ncard : ℝ)
      ≤ α * (X.n₁ : ℝ)
    by_cases hxA : x ∈ X.domClass α
    · rw [h.ncard_labClass_domPairLab hinj hxA (hCx x hxA)]
      exact_mod_cast h2α
    · rw [h.labClass_domPairLab_of_notMem hx hxA]
      have : ¬ (α * (X.n₁ : ℝ) ≤ ((X.localSizeClass x).ncard : ℝ)) := fun hc => hxA ⟨hx, hc⟩
      linarith [not_le.1 this]


end DomHyp

/-! ### The last exit: the Johnson scheme `J(|C|, d*)` on `A`

*"Since `C` is a set of twins in `H*`, we are back to Case 1.  Proceed as in Case 1, exit."*
The labels are the traces `X(v) ∩ C`, `v ∈ A`, read as `d*`-subsets of `C`. -/

/-- The trace `X(v) ∩ C`, read as a finite set of vertices of `C`. -/
noncomputable def traceFinset (X : BlkCaseObj s Case) (x : ↥s) : Finset ↥X.bigTwin :=
  (Set.toFinite {B : ↥X.bigTwin | (B : Set ↥s) ∈ X.nbhd x}).toFinset

theorem mem_traceFinset (X : BlkCaseObj s Case) (x : ↥s) (B : ↥X.bigTwin) :
    B ∈ X.traceFinset x ↔ (B : Set ↥s) ∈ X.nbhd x := Set.Finite.mem_toFinset _

theorem coe_traceSet (X : BlkCaseObj s Case) (x : ↥s) :
    {B : ↥X.bigTwin | (B : Set ↥s) ∈ X.nbhd x}
      = {B : ↥X.bigTwin | (B : Set ↥s) ∈ X.nbhd x ∩ X.bigTwin} := by
  ext B
  exact ⟨fun hB => ⟨hB, B.2⟩, fun hB => hB.1⟩

theorem card_traceFinset (X : BlkCaseObj s Case) (x : ↥s) :
    (X.traceFinset x).card = X.localSize x := by
  rw [traceFinset, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _), X.coe_traceSet x,
    ncard_coe_of_subset Set.inter_subset_right]
  rfl

theorem traceFinset_eq_iff (X : BlkCaseObj s Case) (x y : ↥s) :
    X.traceFinset x = X.traceFinset y
      ↔ X.nbhd x ∩ X.bigTwin = X.nbhd y ∩ X.bigTwin := by
  constructor
  · intro hc
    ext A
    constructor
    · rintro ⟨hA, hAC⟩
      have hB : (⟨A, hAC⟩ : ↥X.bigTwin) ∈ X.traceFinset x := (X.mem_traceFinset x _).2 hA
      exact ⟨(X.mem_traceFinset y _).1 (hc ▸ hB), hAC⟩
    · rintro ⟨hA, hAC⟩
      have hB : (⟨A, hAC⟩ : ↥X.bigTwin) ∈ X.traceFinset y := (X.mem_traceFinset y _).2 hA
      exact ⟨(X.mem_traceFinset x _).1 (hc ▸ hB), hAC⟩
  · intro hc
    ext B
    rw [X.mem_traceFinset x B, X.mem_traceFinset y B]
    constructor
    · intro hB
      have hmem : (B : Set ↥s) ∈ X.nbhd x ∩ X.bigTwin := ⟨hB, B.2⟩
      rw [hc] at hmem
      exact hmem.1
    · intro hB
      have hmem : (B : Set ↥s) ∈ X.nbhd y ∩ X.bigTwin := ⟨hB, B.2⟩
      rw [← hc] at hmem
      exact hmem.1

theorem card_traceFinset_sdiff (X : BlkCaseObj s Case) [DecidableEq ↥X.bigTwin]
    (x y : ↥s) :
    ((X.traceFinset x) \ (X.traceFinset y)).card
      = ((X.nbhd x ∩ X.bigTwin) \ (X.nbhd y ∩ X.bigTwin)).ncard := by
  have hset : ((X.traceFinset x) \ (X.traceFinset y))
      = (Set.toFinite {B : ↥X.bigTwin |
        (B : Set ↥s) ∈ (X.nbhd x ∩ X.bigTwin) \ (X.nbhd y ∩ X.bigTwin)}).toFinset := by
    ext B
    simp only [Finset.mem_sdiff, X.mem_traceFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      Set.mem_diff, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, B.2⟩, fun hc => h2 hc.1⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, fun hc => h2 ⟨hc, B.2⟩⟩
  rw [hset, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _),
    ncard_coe_of_subset (fun A hA => hA.1.2)]

/-- §9.7, Case 2, the last exit.  The Johnson coloring of `A` (Def. 3.2.13):
`|X(u) ∩ C ∖ X(v)|`, the coloring of Case 1 read in `X*`. -/
noncomputable def domJohnsonColor (X : BlkCaseObj s Case) (α : ℝ) :
    ↥(Subtype.val '' X.domClass α) → ↥(Subtype.val '' X.domClass α) → ℕ :=
  fun u v => ((X.nbhd (liftPt u) ∩ X.bigTwin) \ (X.nbhd (liftPt v) ∩ X.bigTwin)).ncard

namespace DomHyp

variable {X : BlkDesignObj s} {α : ℝ} (h : DomHyp X α)
include h

/-- §9.7, Case 2, the last exit.  ***"Since `C` is a set of twins in `H*`, we are back to
Case 1.  Proceed as in Case 1, exit."***  The labels `v ↦ X(v) ∩ C` are a bijection of `A`
with the `d*`-subsets of `C` — injective by the branch hypothesis (*"there are no twins in
`A`"*) and surjective by `Babai.BlkCaseObj.exists_traceClass` — so the Johnson coloring of
the labels is a Johnson coloring.

The parameters are checked as in entries 82 and 83 of the corrected paper: `|A| = C(|C|, d*)`
and `|C| < |A|` (`Babai.BlkCaseObj.DomHyp.bigTwin_ncard_lt`) give `2 ≤ d* ≤ |C| − 2`
(`Babai.two_le_and_add_two_le_of_lt_choose`), the boundary `|C| = 2d*` is excluded by
hypothesis (it is the other branch, entry 83), and for `d* > |C|/2` the labels are replaced
by their complements (`Babai.isJohnsonColoring_of_labels`). -/
theorem domIsJohnsonColoring
    (hinj : ∀ u ∈ X.domClass α, ∀ v ∈ X.domClass α,
      X.nbhd u ∩ X.bigTwin = X.nbhd v ∩ X.bigTwin → u = v)
    {x₀ : ↥s} (hx₀ : x₀ ∈ X.domClass α)
    (hC : X.bigTwin.ncard ≠ 2 * X.localSize x₀) :
    IsJohnsonColoring (X.domJohnsonColor α) := by
  classical
  letI : Fintype ↥X.bigTwin := Fintype.ofFinite _
  letI : Fintype ↥(Subtype.val '' X.domClass α) := Fintype.ofFinite _
  have hk : Fintype.card ↥X.bigTwin = X.bigTwin.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- the labels all have `d*` blocks
  have hloc : ∀ z : ↥(Subtype.val '' X.domClass α),
      X.localSize (liftPt z) = X.localSize x₀ := by
    intro z
    have hz : liftPt z ∈ X.domClass α := liftPt_mem z
    have : liftPt z ∈ X.localSizeClass x₀ := (h.domClass_eq hx₀) ▸ hz
    exact this.2
  have hbij : Function.Bijective (fun z : ↥(Subtype.val '' X.domClass α) =>
      (⟨X.traceFinset (liftPt z), by rw [X.card_traceFinset, hloc z]⟩ :
        binom ↥X.bigTwin (X.localSize x₀))) := by
    constructor
    · intro z w hzw
      have hfin : X.traceFinset (liftPt z) = X.traceFinset (liftPt w) :=
        congrArg Subtype.val hzw
      have htr := (X.traceFinset_eq_iff _ _).1 hfin
      exact liftPt_injective (hinj _ (liftPt_mem z) _ (liftPt_mem w) htr)
    · intro F
      set T : Set (Set ↥s) := Subtype.val '' ((F : Finset ↥X.bigTwin) : Set ↥X.bigTwin) with hT
      have hTsub : T ⊆ X.bigTwin := by rintro _ ⟨B, -, rfl⟩; exact B.2
      have hTcard : T.ncard = X.localSize x₀ := by
        rw [hT, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
        exact F.2
      obtain ⟨y, hy, hTy⟩ := X.exists_traceClass h.twin_pairwise hx₀.1 hTsub hTcard
      have hyA : y ∈ X.domClass α := h.traceClass_subset_domClass hx₀ hTcard ⟨hy, hTy⟩
      refine ⟨mkPt hyA, Subtype.ext ?_⟩
      show X.traceFinset (liftPt (mkPt hyA)) = (F : Finset ↥X.bigTwin)
      rw [liftPt_mkPt]
      ext B
      rw [X.mem_traceFinset y B]
      constructor
      · intro hB
        have : (B : Set ↥s) ∈ T := by rw [← hTy]; exact ⟨hB, B.2⟩
        obtain ⟨B', hB', hBB⟩ := this
        have : B' = B := Subtype.ext hBB
        exact this ▸ hB'
      · intro hB
        have : (B : Set ↥s) ∈ T := ⟨B, hB, rfl⟩
        rw [← hTy] at this
        exact this.1
  set φ := Equiv.ofBijective _ hbij with hφ
  -- `|A| = C(|C|, d*)`
  have hchoose : (X.domClass α).ncard = (X.bigTwin.ncard).choose (X.localSize x₀) := by
    have h1 : Fintype.card (binom ↥X.bigTwin (X.localSize x₀))
        = (X.bigTwin.ncard).choose (X.localSize x₀) := by
      rw [← hk]; exact Fintype.card_finset_len _
    have h2 : Fintype.card ↥(Subtype.val '' X.domClass α) = (X.domClass α).ncard :=
      card_image_val _ _
    rw [← h2, Fintype.card_congr φ, h1]
  have hlt : X.bigTwin.ncard < (X.bigTwin.ncard).choose (X.localSize x₀) := by
    rw [← hchoose]; exact h.bigTwin_ncard_lt
  have h1le : 1 ≤ X.bigTwin.ncard := by
    have := h.one_le_localSize hx₀
    have := h.localSize_lt hx₀
    omega
  obtain ⟨hd2, hd2'⟩ := two_le_and_add_two_le_of_lt_choose h1le hlt
  refine isJohnsonColoring_of_labels (V := ↥X.bigTwin) hk
    (le_of_lt (h.localSize_lt hx₀)) φ (fun u v => ?_)
    (johnson_alternative hd2 hd2' (fun hc => hC hc))
  show ((X.nbhd (liftPt u) ∩ X.bigTwin) \ (X.nbhd (liftPt v) ∩ X.bigTwin)).ncard
    = ((X.traceFinset (liftPt u)) \ (X.traceFinset (liftPt v))).card
  rw [X.card_traceFinset_sdiff]

end DomHyp

end BlkCaseObj

namespace BlkCaseObj

variable {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
  {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}

/-- §9.7, Case 2, the last exit.  The Johnson coloring of `A` is canonical: a morphism
carries the trace `X(v) ∩ C` to the trace of the image
(`Babai.BlkCaseObj.IsMorphOn.trace_eq`), and `|S ∖ T|` is preserved by a bijection. -/
theorem IsMorphOn.traceColor_eq (h : X.IsMorphOn Y φ) (x y : ↥s) :
    ((Y.nbhd (φ x) ∩ Y.bigTwin) \ (Y.nbhd (φ y) ∩ Y.bigTwin)).ncard
      = ((X.nbhd x ∩ X.bigTwin) \ (X.nbhd y ∩ X.bigTwin)).ncard := by
  rw [h.trace_eq x, h.trace_eq y, ← Set.image_diff (imgEquiv φ).injective,
    Set.ncard_image_of_injective _ (imgEquiv φ).injective]

end BlkCaseObj

end Babai
