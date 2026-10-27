/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 2: a large twin class of the neighborhood hypergraph.
-/
import Workspace.SplitOrJohnson.BlkExit
import Workspace.SplitOrJohnson.BlkDominant
import Workspace.SplitOrJohnson.HintEqvBlocks
import Workspace.SplitOrJohnson.KerPart

/-!
# §9.7  Case 2

Version 2.5, lines 4252-4274.

The branch splits by a **canonical test** into the *tie* and the *unique class* (entry on
§9.7 Case 2 in the corrected paper):

| Paper | Lean |
|---|---|
| *"there is an `H`-twin class `C` with `\|C\| ≥ n₂/2`"*, made canonical | `Babai.BlkCaseObj.bigTwin` |
| the tie: the twin partition is an equipartition into two halves | `Babai.case_9_7_case2_tie` |
| *"if `V₂ ∖ C` is selected, we have made significant progress"* | `Babai.case_9_7_case2_compl` |
| *"if `C` is selected, …"* | `Babai.case_9_7_case2_sel` |
| *"if all `c'`-color classes have size less than `αn₁`, return this coloring"* | `Babai.case_9_7_case2_small` |
| the two exits at the dominant class `A` | `Babai.case_9_7_case2_dom` |
| *"if this is a nontrivial partition, return this partition"* | `Babai.case_9_7_case2_dom_twin` |
| the boundary `\|C\| = 2d*` (entry 83 of the corrected paper) | `Babai.case_9_7_case2_dom_pair` |
| *"we are back to Case 1.  Proceed as in Case 1"* | `Babai.case_9_7_case2_dom_john` |
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ### The three lemmas about one object of §9.7 that Case 2 needs

They are stated for an object with the two instances left open, so that they unify with
whatever instances the goal carries. -/

namespace BlkCaseObj

variable {s : Set Ω}

open scoped Classical in
/-- §9.7, Case 2, the tie.  The three-color coloring *"equal"*, *"twins"*, *"not twins"* of
the ordered pairs of blocks: the coloring of the equipartition of `V₂` into the two twin
classes, handed back as the hint of §9.5. -/
noncomputable def twinHint
    {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    (X : BlkCaseObj s Case) : Set ↥s → Set ↥s → ℕ :=
  fun A B => if A = B then 0 else if X.IsHTwin A B then 1 else 2

/-- Lemma 9.3.2 at the trivial covering `V₂ = V₂ ∪ V₂`: since `V₁` has no twins in the link
(`Babai.BlkCaseObj.linkGraph_noTwins`), the symmetry defect of `V₁` in the whole graph is at
least `(n₁ − 1)/2`.  This is the symmetry-defect clause of `Babai.restrictObjHint_pred` for
an exit that restricts nothing. -/
theorem symDefect₁_blocks [Fintype ↥s] [inst : DecidableEq ↥s] (X : BlkDesignObj s) :
    ((X.n₁ : ℚ) - 1) / 2 ≤ (X.linkGraph.restrictBlk X.blocks).symDefect₁ := by
  have he : inst = fun a b => Subtype.instDecidableEq a b :=
    funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hno : ∀ x, X.linkGraph.part₁ x → ∀ y, X.linkGraph.part₁ y →
      ¬ @IsTwin ↥s inst X.linkGraph.Aut x y := by
    rw [he]; exact BlkCaseObj.linkGraph_noTwins _
  exact (lemma_9_3_2_blk X.linkGraph hno
    (U₁ := X.blocks) (U₂ := X.blocks) Set.subset_union_left).elim id id

/-- §9.7, Case 2.  Lemma 9.3.2 at the covering `V₂ = C ∪ (V₂ ∖ C)`: if Procedure
Reduce-Part2-by-Color does not select `C`, it selects `V₂ ∖ C`, and the symmetry defect of
`V₁` there is at least `(n₁ − 1)/2`. -/
theorem symDefect₁_compl_bigTwin [Fintype ↥s] [inst : DecidableEq ↥s] (X : BlkDesignObj s)
    (h : ¬ ((X.n₁ : ℚ) - 1) / 2 ≤ (X.linkGraph.restrictBlk X.bigTwin).symDefect₁) :
    ((X.n₁ : ℚ) - 1) / 2 ≤
      (X.linkGraph.restrictBlk (X.blocks \ X.bigTwin)).symDefect₁ := by
  have hcov : X.linkGraph.blocks ⊆ X.bigTwin ∪ (X.blocks \ X.bigTwin) := by
    intro B hB
    by_cases hb : B ∈ X.bigTwin
    · exact Or.inl hb
    · exact Or.inr ⟨hB, hb⟩
  have he : inst = fun a b => Subtype.instDecidableEq a b :=
    funext fun _ => funext fun _ => Subsingleton.elim _ _
  have hno : ∀ x, X.linkGraph.part₁ x → ∀ y, X.linkGraph.part₁ y →
      ¬ @IsTwin ↥s inst X.linkGraph.Aut x y := by
    rw [he]; exact BlkCaseObj.linkGraph_noTwins _
  exact (lemma_9_3_2_blk X.linkGraph hno hcov).resolve_left h

open scoped Classical in
/-- §9.7, Case 2, the tie.  **The twin partition of `V₂` is a hint**: the equipartition of
`V₂` into the two `H`-twin classes, read through `Babai.eqvConfig`
(`Babai.VColBipBlk.hasHint_of_eqvPart`). -/
theorem hasHint_twinHint [Fintype ↥s] [DecidableEq ↥s] (X : BlkDesignObj s)
    (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1) (heq : X.bigTwin = X.blocks) :
    (X.linkGraph.restrictBlkHint X.blocks (twinHint X)).HasHint := by
  classical
  obtain ⟨m, hm2, hmlt, hmall⟩ := X.tie_spec' hlt h1 heq
  have hblk : (X.linkGraph.restrictBlkHint X.blocks (twinHint X)).blocks = X.blocks := by
    show X.linkGraph.blocks ∩ X.blocks = X.blocks
    rw [BlkCaseObj.linkGraph_blocks, Set.inter_self]
  have hnum : (X.linkGraph.restrictBlkHint X.blocks (twinHint X)).numBlocks = X.n₂ := by
    rw [VColBipBlk.numBlocks, hblk]; rfl
  refine VColBipBlk.hasHint_of_eqvPart (r := fun A B => X.IsHTwin A B) (m := m)
    (fun A _ => X.isHTwin_refl A)
    (fun A _ B _ h => X.isHTwin_symm h)
    (fun A _ B _ C _ h h' => X.isHTwin_trans h h')
    (fun A hA => ?_) hm2 ?_ (fun A hA B hB => ?_)
  · rw [hblk] at hA ⊢
    exact hmall A hA
  · rw [hnum]; exact hmlt
  · rw [hblk] at hA hB
    exact VColBipBlk.restrictBlkHint_h (X := X.linkGraph) ⟨hA, hA⟩ ⟨hB, hB⟩

/-- §9.7, Case 2, the tie.  The hint coloring is canonical: twins go to twins
(`Babai.BlkCaseObj.IsMorphOn.isHTwin_iff`). -/
theorem IsMorphOn.twinHint_eq {t : Set Ω}
    {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
    {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}
    {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}
    (h : X.IsMorphOn Y φ) (A B : Set ↥s) :
    Y.twinHint (φ '' A) (φ '' B) = X.twinHint A B := by
  classical
  have hinj : φ '' A = φ '' B ↔ A = B :=
    ⟨fun hc => Set.image_injective.2 φ.injective hc, fun hc => by rw [hc]⟩
  show (if φ '' A = φ '' B then 0 else if Y.IsHTwin (φ '' A) (φ '' B) then 1 else 2)
    = (if A = B then 0 else if X.IsHTwin A B then 1 else 2)
  by_cases hAB : A = B
  · rw [if_pos hAB, if_pos (hinj.2 hAB)]
  · rw [if_neg hAB, if_neg (fun hc => hAB (hinj.1 hc))]
    by_cases ht : X.IsHTwin A B
    · rw [if_pos ((h.isHTwin_iff A B).2 ht), if_pos ht]
    · rw [if_neg (fun hc => ht ((h.isHTwin_iff A B).1 hc)), if_neg ht]

/-- §9.7, Case 2.  The test of Procedure Reduce-Part2-by-Color at `(C, V₂ ∖ C)` is an
isomorphism invariant: `C` is canonical (`Babai.BlkCaseObj.IsMorphOn.mem_bigTwin_iff`) and
the symmetry defect of `V₁` is (`Babai.VColBipBlk.symDefect₁_eq_of_isIsoTo`). -/
theorem IsMorphOn.selP_iff {t : Set Ω} [Fintype ↥s] [DecidableEq ↥s] [Fintype ↥t]
    [DecidableEq ↥t] {X : BlkDesignObj s} {Y : BlkDesignObj t} {φ : ↥s ≃ ↥t}
    (h : X.IsMorphOn Y φ) :
    (((Y.n₁ : ℚ) - 1) / 2 ≤ (Y.linkGraph.restrictBlk Y.bigTwin).symDefect₁)
      ↔ (((X.n₁ : ℚ) - 1) / 2 ≤ (X.linkGraph.restrictBlk X.bigTwin).symDefect₁) := by
  have hd := VColBipBlk.symDefect₁_eq_of_isIsoTo
    (VColBipBlk.restrictBlk_isIsoTo (BlkCaseObj.linkGraph_isIsoTo h)
      (fun B => h.mem_bigTwin_iff B))
  rw [h.n₁_eq, hd]

end BlkCaseObj

/-! ### The category of Case 2, and the two canonical tests -/

open BlkBlockDesignInputs in
/-- §9.7.  The inputs of Case 2: the admissible inputs of §9.7 that are not in Case 1 and
satisfy the branch condition of Case 2. -/
abbrev Case2Cat (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  ((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full (fun s X => Case2P s X.1)

/-- The object of §9.7 underlying an object of `Babai.Case2Cat`. -/
def Case2Cat.objOf {s : Set Ω} (X : (Case2Cat Ω).Obj s) : BlkDesignObj s := X.1.1.1.1

/-- The input of §9.7 underlying an object of `Babai.Case2Cat`. -/
def Case2Cat.bbd (X : Pt (Case2Cat Ω)) : Pt (BlkBlockDesignInputs Ω) :=
  ⟨X.car, X.obj.1.1⟩

theorem Case2Cat.isMorphOn {X Y : Pt (Case2Cat Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (Case2Cat Ω).IsoP X Y) :
    (Case2Cat.objOf X.obj).IsMorphOn (Case2Cat.objOf Y.obj) φ :=
  BlkBlockDesignInputs.isMorphOn_of_iso (X := Case2Cat.bbd X) (Y := Case2Cat.bbd Y) hφ

/-- §9.7, Case 2.  **The tie test.**  `Babai.BlkCaseObj.bigTwin` is all of `V₂` exactly
when two twin classes of size `n₂/2` exhaust `V₂`, and then no rule the paper states picks
one of them; see the entry on §9.7 Case 2 in the corrected paper. -/
def Case2TieP : ∀ s : Set Ω, (Case2Cat Ω).Obj s → Prop :=
  fun _ X => (Case2Cat.objOf X).bigTwin = (Case2Cat.objOf X).blocks

theorem case2TieP_congr {X Y : Pt (Case2Cat Ω)}
    (h : ((Case2Cat Ω).IsoP X Y).Nonempty) (hX : Case2TieP X.car X.obj) :
    Case2TieP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  exact ((Case2Cat.isMorphOn hφ).bigTwin_eq_blocks_iff).2 hX

/-! ### The tie: the equipartition exit -/

open BlkBlockDesignInputs in
/-- §9.7, Case 2, **the tie** (entry on §9.7 Case 2 in the corrected paper).  When two `H`-twin
classes of size `n₂/2` exhaust `V₂`, no canonical rule picks one of them, and the paper's
route cannot be entered.  What the input carries instead is an **equipartition of `V₂` into
two classes of one common size `m = n₂/2` with `2 ≤ m < n₂`** — exactly the situation of
Cases 3a1 and 3b — so the input itself is returned with the `Babai.eqvConfig` hint of the
twin partition attached, the second alternative of `Babai.IsBlkDesignOutcome`
(*"`X₂` moves from clique to UPCC while `n₂` does not increase"*).

Nothing is restricted, so `U = V₂` and the symmetry-defect clause of
`Babai.restrictObjHint_pred` is the input's own: `V₁` has no twins in the link
(`Babai.BlkCaseObj.linkGraph_noTwins`), so Lemma 9.3.2 at the trivial covering
`V₂ = V₂ ∪ V₂` gives a symmetry defect of `n₁ − 1 ≥ (n₁ − 1)/2`
(`Babai.BlkCaseObj.symDefect₁_blocks`).

`2 ≤ m` is `Babai.BlkCaseObj.tie_spec'`: `m = 1` would give `n₂ = 2` and hence
`n₁ ≤ C(2, d₁) ≤ 2`, against `n₂ < n₁`. -/
theorem case_9_7_case2_tie :
    FindsAtMultCost ((Case2Cat Ω).full Case2TieP) (Out97 Ω)
      (fun X => cost97 (Case2Cat.bbd ⟨X.car, X.obj.1⟩))
      (fun X Z => Good97 (Case2Cat.bbd ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine findsAtMultCost_restrictHint (C := (Case2Cat Ω).full Case2TieP)
    (bbd := fun Y => (Case2Cat.bbd ⟨Y.car, Y.obj.1⟩).obj)
    (Sel := fun Y => (Case2Cat.objOf Y.obj.1).blocks)
    (Hint := fun Y => (Case2Cat.objOf Y.obj.1).twinHint)
    (fun {Y Z f} hf => hf) (fun Y => subset_rfl)
    (fun Y => numBlocks_lt_n₁ (Case2Cat.bbd ⟨Y.car, Y.obj.1⟩))
    (fun Y => by
      letI : Fintype ↥Y.car := Fintype.ofFinite _
      letI : DecidableEq ↥Y.car := Classical.decEq _
      exact BlkCaseObj.symDefect₁_blocks _)
    (fun {Y Z f} hf B =>
      (Case2Cat.isMorphOn (X := ⟨Y.car, Y.obj.1⟩) (Y := ⟨Z.car, Z.obj.1⟩) hf).blocks B)
    (fun {Y Z f} hf A B _ _ =>
      (Case2Cat.isMorphOn (X := ⟨Y.car, Y.obj.1⟩) (Y := ⟨Z.car, Z.obj.1⟩) hf).twinHint_eq A B)
    (fun Y => by
      letI : Fintype ↥Y.car := Fintype.ofFinite _
      letI : DecidableEq ↥Y.car := Classical.decEq _
      exact Or.inr ⟨le_rfl, BlkCaseObj.hasHint_twinHint _
        (numBlocks_lt_n₁ (Case2Cat.bbd ⟨Y.car, Y.obj.1⟩)) Y.obj.1.1.2 Y.obj.2⟩)
    _ (fun Y => Nat.one_le_pow _ _ (one_le_numBlocks _))

/-! ### The unique class: Procedure Reduce-Part2-by-Color on `(C, V₂ ∖ C)` -/

open BlkBlockDesignInputs in
/-- §9.7, Case 2.  **The test of Procedure Reduce-Part2-by-Color at `(C, V₂ ∖ C)`**
(§9.3, version 2.5, lines 4076-4084): the procedure returns `C` exactly when the symmetry
defect of `V₁` in `X[V₁, C]` is at least `(n₁ − 1)/2`, which is this condition. -/
noncomputable def Case2SelP : ∀ s : Set Ω, ((Case2Cat Ω).full
    (fun s X => ¬ Case2TieP s X)).Obj s → Prop :=
  fun s X =>
    letI : Fintype ↥s := Fintype.ofFinite _
    letI : DecidableEq ↥s := Classical.decEq _
    (((Case2Cat.objOf X.1).n₁ : ℚ) - 1) / 2 ≤
      ((Case2Cat.objOf X.1).linkGraph.restrictBlk (Case2Cat.objOf X.1).bigTwin).symDefect₁

theorem case2SelP_congr {X Y : Pt ((Case2Cat Ω).full (fun s X => ¬ Case2TieP s X))}
    (h : (((Case2Cat Ω).full (fun s X => ¬ Case2TieP s X)).IsoP X Y).Nonempty)
    (hX : Case2SelP X.car X.obj) : Case2SelP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  letI : Fintype ↥X.car := Fintype.ofFinite _
  letI : DecidableEq ↥X.car := Classical.decEq _
  letI : Fintype ↥Y.car := Fintype.ofFinite _
  letI : DecidableEq ↥Y.car := Classical.decEq _
  exact ((Case2Cat.isMorphOn (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩)
    hφ).selP_iff).2 hX

open BlkBlockDesignInputs in
/-- §9.7, Case 2.  *"Apply procedure Reduce-Part2-by-Color to the coloring `(C, V₂ ∖ C)`.
If `V₂ ∖ C` is selected, we have made significant progress (reduced `|V₂|` by half)."*
(Version 2.5, lines 4256-4258.)

`|C| ≥ n₂/2`, so `|V₂ ∖ C| ≤ n₂/2` and `10|V₂ ∖ C| ≤ 5n₂ ≤ 9n₂`: the first alternative of
`Babai.IsBlkDesignOutcome`, with no hint.  The symmetry-defect clause is Lemma 9.3.2 at the
covering `V₂ = C ∪ (V₂ ∖ C)`, whose other alternative is the negated branch condition
(`Babai.BlkCaseObj.symDefect₁_compl_bigTwin`). -/
theorem case_9_7_case2_compl :
    FindsAtMultCost
      (((Case2Cat Ω).full (fun s X => ¬ Case2TieP s X)).full
        (fun s X => ¬ Case2SelP s X)) (Out97 Ω)
      (fun X => cost97 (Case2Cat.bbd ⟨X.car, X.obj.1.1⟩))
      (fun X Z => Good97 (Case2Cat.bbd ⟨X.car, X.obj.1.1⟩) Z) := by
  classical
  refine findsAtMultCost_restrictHint
    (C := ((Case2Cat Ω).full (fun s X => ¬ Case2TieP s X)).full
      (fun s X => ¬ Case2SelP s X))
    (bbd := fun Y => (Case2Cat.bbd ⟨Y.car, Y.obj.1.1⟩).obj)
    (Sel := fun Y => (Case2Cat.objOf Y.obj.1.1).blocks \ (Case2Cat.objOf Y.obj.1.1).bigTwin)
    (Hint := fun _ _ _ => 0)
    (fun {Y Z f} hf => hf) (fun Y => Set.diff_subset)
    (fun Y => numBlocks_lt_n₁ (Case2Cat.bbd ⟨Y.car, Y.obj.1.1⟩))
    (fun Y => by
      letI : Fintype ↥Y.car := Fintype.ofFinite _
      letI : DecidableEq ↥Y.car := Classical.decEq _
      exact BlkCaseObj.symDefect₁_compl_bigTwin _ Y.obj.2)
    (fun {Y Z f} hf B => ?_) (fun {Y Z f} hf A B _ _ => rfl)
    (fun Y => ?_) _ (fun Y => Nat.one_le_pow _ _ (one_le_numBlocks _))
  · -- `C` is canonical, hence so is its complement in `V₂`
    have hm := Case2Cat.isMorphOn (X := ⟨Y.car, Y.obj.1.1⟩) (Y := ⟨Z.car, Z.obj.1.1⟩) hf
    exact and_congr (hm.blocks B) (not_congr (hm.mem_bigTwin_iff B))
  · -- *"reduced `|V₂|` by half"*
    refine Or.inl ?_
    obtain ⟨hsub, hcard, -, -⟩ :=
      (Case2Cat.objOf Y.obj.1.1).bigTwin_spec Y.obj.1.1.2 Y.obj.1.2
    have hdiff : ((Case2Cat.objOf Y.obj.1.1).blocks \
        (Case2Cat.objOf Y.obj.1.1).bigTwin).ncard
        + (Case2Cat.objOf Y.obj.1.1).bigTwin.ncard = (Case2Cat.objOf Y.obj.1.1).n₂ :=
      Set.ncard_diff_add_ncard_of_subset hsub (Set.toFinite _)
    show 10 * ((Case2Cat.objOf Y.obj.1.1).blocks \
      (Case2Cat.objOf Y.obj.1.1).bigTwin).ncard ≤ 9 * (Case2Cat.objOf Y.obj.1.1).n₂
    omega

/-! ### The unique class, `C` selected: the `c'`-coloring of `V₁` -/

/-- §7.1.  A colored partition whose blocks are the color classes is a colored
`α`-partition as soon as **every** color class is at most `α|W|`, with no uniform integer
bound in between: the maximum `ρ(Π)` is attained at some block, `W` being nonempty.  This
is `Babai.kerPartition_isAlphaPartition` with a real bound in place of the integer `k`. -/
theorem kerPartition_isAlphaPartition_of_le {s : Set Ω} (W : Set ↥s) (col : ↥s → ℕ)
    (iF : Fintype ↥(Subtype.val '' W)) {α : ℝ} (hne : W.Nonempty)
    (h : ∀ x ∈ W, (({y : ↥s | y ∈ W ∧ col y = col x}).ncard : ℝ) ≤ α * (W.ncard : ℝ)) :
    @ColoredPartition.IsAlphaPartition _ _ (kerPartition W col) iF α := by
  refine ⟨kerPartition_isAdmissible W col, ?_⟩
  rw [card_image_val W iF]
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ↥(Subtype.val '' W))
    ⟨mkPt hx₀, Finset.mem_univ _⟩ (fun z => ((kerPartition W col).block z).ncard)
  have h1 : @ColoredPartition.rho _ _ (kerPartition W col) iF
      = ((kerPartition W col).block z).ncard := hz
  have h2 : (((kerPartition W col).block z).ncard : ℝ)
      ≤ (({y : ↥s | y ∈ W ∧ col y = col (liftPt z)}).ncard : ℝ) := by
    exact_mod_cast kerPartition_ncard_block_le W col z
  have h3 := h (liftPt z) (liftPt_mem z)
  rw [h1]
  linarith

open BlkBlockDesignInputs in
/-- §9.7.  The threshold `α` of an object of `Babai.Case2Cat`. -/
def Case2Cat.alphaOf {s : Set Ω} (X : (Case2Cat Ω).Obj s) : ℝ := X.1.1.1.2

/-- §9.7, Case 2.  The inputs of Case 2 on which the paper's route is entered: the class
`C` is unique, and Procedure Reduce-Part2-by-Color selects `C`. -/
abbrev Case2SelCat (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  ((Case2Cat Ω).full (fun s X => ¬ Case2TieP s X)).full (fun s X => Case2SelP s X)

/-- §9.7, Case 2.  *"If all `c'`-color classes have size less than `αn₁`, return this
coloring, exit."*  (Version 2.5, lines 4262-4263.)  The test on the input. -/
def Case2SmallP : ∀ s : Set Ω, (Case2SelCat Ω).Obj s → Prop :=
  fun _ X => ∀ x, (Case2Cat.objOf X.1.1).part₁ x →
    ((({y | (Case2Cat.objOf X.1.1).part₁ y ∧
        (Case2Cat.objOf X.1.1).localSize y
          = (Case2Cat.objOf X.1.1).localSize x}).ncard : ℝ))
      < Case2Cat.alphaOf X.1.1 * ((Case2Cat.objOf X.1.1).n₁ : ℝ)

theorem case2SmallP_congr {X Y : Pt (Case2SelCat Ω)}
    (h : ((Case2SelCat Ω).IsoP X Y).Nonempty) (hX : Case2SmallP X.car X.obj) :
    Case2SmallP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  have hm := Case2Cat.isMorphOn (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) hφ
  have hα : Case2Cat.alphaOf X.obj.1.1 = Case2Cat.alphaOf Y.obj.1.1 := hφ.1
  intro y hy
  have hy' : (Case2Cat.objOf X.obj.1.1).part₁ (φ.symm y) := by
    have hp := (hm.part₁ (φ.symm y)).1
    rw [Equiv.apply_symm_apply] at hp
    exact hp hy
  have hcls := hm.ncard_localSizeClass (φ.symm y)
  rw [Equiv.apply_symm_apply] at hcls
  rw [hcls, ← hα, hm.n₁_eq]
  exact hX _ hy'

open scoped Classical in
open BlkBlockDesignInputs in
/-- §9.7, Case 2.  The colored partition of `V₁` whose blocks are the `c'`-color classes,
as an object of `Babai.Out97` on the subset `V₁` of `□X` — goal (a) of Theorem 9.2.2. -/
noncomputable def case2ColOutcome (X : Pt ((Case2SelCat Ω).full Case2SmallP)) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨BlkBlockDesignInputs.V₁ (Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩),
      BlkBlockDesignInputs.v₁_subset _⟩,
    Sum.inl (Sum.inl (kerPartition {x | (Case2Cat.objOf X.obj.1.1.1).part₁ x}
      (Case2Cat.objOf X.obj.1.1.1).localSize))⟩

open BlkBlockDesignInputs in
/-- §9.7, Case 2.  *"Color each vertex of `V₁` by the size of the corresponding hyperedge
in `H'`: for `v ∈ V₁` let `c'(v) = |X(v) ∩ C|`.  If all `c'`-color classes have size less
than `αn₁`, return this coloring, exit."*  (Version 2.5, lines 4261-4263.)

**Proved.**  The single outcome is `Babai.kerPartition` of the coloring `c'`
(`Babai.BlkCaseObj.localSize`) on `V₁`: its blocks are the `c'`-color classes, so it is
admissible (Def. 7.1.1) and `ρ(Π)` is the size of the largest class, which the branch
condition bounds by `αn₁`.  It is canonical because `c'` is
(`Babai.BlkCaseObj.IsMorphOn.localSize_eq`: neighborhoods go to neighborhoods and `C` goes
to `C`). -/
theorem case_9_7_case2_small :
    FindsAtMultCost ((Case2SelCat Ω).full Case2SmallP) (Out97 Ω)
      (fun X => cost97 (Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩))
      (fun X Z => Good97 (Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub (fun X => {case2ColOutcome X})
    (fun X => ⟨_, rfl⟩) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.one_le_pow _ _ (one_le_numBlocks _)
  · -- the coloring `c'` is canonical
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hm := Case2Cat.isMorphOn (X := ⟨X.car, X.obj.1.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1.1⟩) hf
    refine ⟨case2ColOutcome Y, rfl, ?_⟩
    exact ⟨subEquiv f (fun x => hm.part₁ x), fun _ => rfl,
      kerPartition_mem_iso f (fun x => hm.part₁ x) (fun x => hm.localSize_eq x)⟩
  · -- goal (a) of Theorem 9.2.2 on `V₁`
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    refine ⟨rfl, ?_⟩
    obtain ⟨x₀, hx₀⟩ := (Case2Cat.objOf X.obj.1.1.1).part₁_nonempty
    refine kerPartition_isAlphaPartition_of_le _ _ _ ⟨x₀, hx₀⟩ (fun x hx => ?_)
    exact le_of_lt (X.obj.2 x hx)

/-! ### The unique class, `C` selected: the dominant class

The two exits of the paper at the dominant `c'`-color class `A`, plus the boundary case
`|C| = 2d*` of entry 83 of the corrected paper splits the second of them in two.  The
mathematics is in `Workspace/SplitOrJohnson/BlkDominant.lean`; here it is turned into three
branches of the reduction, separated by two canonical tests. -/

/-- §9.7, Case 2.  The inputs at the dominant `c'`-color class: some `c'`-color class has
at least `αn₁` points. -/
abbrev DomCat (Ω : Type) [Fintype Ω] [DecidableEq Ω] : Cat.{0, 0} Ω :=
  (Case2SelCat Ω).full (fun s X => ¬ Case2SmallP s X)

/-- The object of §9.7 underlying an object of `Babai.DomCat`. -/
def DomCat.objOf {s : Set Ω} (X : (DomCat Ω).Obj s) : BlkDesignObj s :=
  Case2Cat.objOf X.1.1.1

/-- The threshold `α` of an object of `Babai.DomCat`. -/
def DomCat.alphaOf {s : Set Ω} (X : (DomCat Ω).Obj s) : ℝ := Case2Cat.alphaOf X.1.1.1

/-- The input of §9.7 underlying an object of `Babai.DomCat`. -/
def DomCat.bbd (X : Pt (DomCat Ω)) : Pt (BlkBlockDesignInputs Ω) :=
  Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩

theorem DomCat.isMorphOn {X Y : Pt (DomCat Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (DomCat Ω).IsoP X Y) :
    (DomCat.objOf X.obj).IsMorphOn (DomCat.objOf Y.obj) φ :=
  Case2Cat.isMorphOn (X := ⟨X.car, X.obj.1.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1.1⟩) hφ

theorem DomCat.alphaOf_eq {X Y : Pt (DomCat Ω)} {φ : ↥X.car ≃ ↥Y.car}
    (hφ : φ ∈ (DomCat Ω).IsoP X Y) : DomCat.alphaOf X.obj = DomCat.alphaOf Y.obj := hφ.1

open BlkBlockDesignInputs in
/-- §9.7, Case 2, at the dominant class: the hypotheses of
`Babai.BlkCaseObj.DomHyp` all hold for an object of `Babai.DomCat`. -/
theorem DomCat.domHyp (X : Pt (DomCat Ω)) :
    (DomCat.objOf X.obj).DomHyp (DomCat.alphaOf X.obj) := by
  obtain ⟨hα, hα1, hlt⟩ := X.obj.1.1.1.1.1.2
  refine ⟨hα, hα1, hlt, X.obj.1.1.1.2, X.obj.1.1.2, ?_⟩
  have hns := X.obj.2
  unfold Case2SmallP at hns
  push_neg at hns
  obtain ⟨x, hx, hle⟩ := hns
  exact ⟨x, hx, hle⟩

/-! ### The first canonical test: are there twins in `A`? -/

/-- §9.7, Case 2, at the dominant class.  **The first test**: *"`A` is equipartitioned by
the twin equivalence classes in `X*`.  If this is a nontrivial partition, …"* — the
partition is nontrivial exactly when two different points of `A` are twins in `X*`, that
is, have the same trace on `C`. -/
def DomTwinP : ∀ s : Set Ω, (DomCat Ω).Obj s → Prop :=
  fun _ X => ∃ u ∈ (DomCat.objOf X).domClass (DomCat.alphaOf X),
    ∃ v ∈ (DomCat.objOf X).domClass (DomCat.alphaOf X), u ≠ v ∧
      (DomCat.objOf X).nbhd u ∩ (DomCat.objOf X).bigTwin
        = (DomCat.objOf X).nbhd v ∩ (DomCat.objOf X).bigTwin

theorem domTwinP_congr {X Y : Pt (DomCat Ω)} (h : ((DomCat Ω).IsoP X Y).Nonempty)
    (hX : DomTwinP X.car X.obj) : DomTwinP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  have hm := DomCat.isMorphOn hφ
  have hα := DomCat.alphaOf_eq hφ
  obtain ⟨u, hu, v, hv, huv, htr⟩ := hX
  refine ⟨φ u, ?_, φ v, ?_, fun hc => huv (φ.injective hc), ?_⟩
  · rw [← hα]; exact (hm.mem_domClass_iff _ u).2 hu
  · rw [← hα]; exact (hm.mem_domClass_iff _ v).2 hv
  · rw [hm.trace_eq u, hm.trace_eq v, htr]

/-! ### The second canonical test: the boundary `|C| = 2d*` -/

/-- §9.7, Case 2, at the dominant class.  **The second test** (entry 83 of
the corrected paper): the boundary `|C| = 2d*`, at which `J(|C|, d*)` is not a Johnson scheme
in the sense of Def. 3.2.9 and the exit returns the equipartition of `A` into the
complementary pairs instead. -/
def DomBoundP : ∀ s : Set Ω, ((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).Obj s → Prop :=
  fun _ X => ∃ x ∈ (DomCat.objOf X.1).domClass (DomCat.alphaOf X.1),
    (DomCat.objOf X.1).bigTwin.ncard = 2 * (DomCat.objOf X.1).localSize x

theorem domBoundP_congr {X Y : Pt ((DomCat Ω).full (fun s X => ¬ DomTwinP s X))}
    (h : (((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).IsoP X Y).Nonempty)
    (hX : DomBoundP X.car X.obj) : DomBoundP Y.car Y.obj := by
  obtain ⟨φ, hφ⟩ := h
  have hm := DomCat.isMorphOn (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) hφ
  have hα := DomCat.alphaOf_eq (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) hφ
  obtain ⟨x, hx, hC⟩ := hX
  refine ⟨φ x, ?_, ?_⟩
  · rw [← hα]; exact (hm.mem_domClass_iff _ x).2 hx
  · rw [hm.ncard_bigTwin_eq, hm.localSize_eq]; exact hC

/-! ### The three outcomes -/

open scoped Classical in
open BlkBlockDesignInputs in
/-- §9.7, Case 2, the first exit.  The `c'`-partition of `V₁` with the dominant class `A`
replaced by the twin classes of `X*` inside it (entry 80 of the corrected paper), as an object
of `Babai.Out97` on the subset `V₁` of `□X` — goal (a) of Theorem 9.2.2. -/
noncomputable def domTwinOutcome (X : Pt ((DomCat Ω).full DomTwinP)) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨BlkBlockDesignInputs.V₁ (DomCat.bbd ⟨X.car, X.obj.1⟩),
      BlkBlockDesignInputs.v₁_subset _⟩,
    Sum.inl (Sum.inl (labPartition {x | (DomCat.objOf X.obj.1).part₁ x}
      (DomCat.objOf X.obj.1).localSize
      ((DomCat.objOf X.obj.1).domLab (DomCat.alphaOf X.obj.1))))⟩

open scoped Classical in
open BlkBlockDesignInputs in
/-- §9.7, Case 2, the boundary exit (entry 83 of the corrected paper).  The `c'`-partition of
`V₁` with the dominant class `A` replaced by the complementary pairs
`{X(v) ∩ C, C ∖ X(v)}`. -/
noncomputable def domPairOutcome
    (X : Pt (((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).full DomBoundP)) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨BlkBlockDesignInputs.V₁ (DomCat.bbd ⟨X.car, X.obj.1.1⟩),
      BlkBlockDesignInputs.v₁_subset _⟩,
    Sum.inl (Sum.inl (labPartition {x | (DomCat.objOf X.obj.1.1).part₁ x}
      (DomCat.objOf X.obj.1.1).localSize
      ((DomCat.objOf X.obj.1.1).domPairLab (DomCat.alphaOf X.obj.1.1))))⟩

/-- §9.7, Case 2, the last exit.  The Johnson coloring of `A` is a Johnson coloring: the
three hypotheses of `Babai.BlkCaseObj.DomHyp.domIsJohnsonColoring` are the two branch
conditions and `Babai.DomCat.domHyp`. -/
theorem domIsJohnson
    (X : Pt ((((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).full
      (fun s X => ¬ DomBoundP s X)))) :
    IsJohnsonColoring ((DomCat.objOf X.obj.1.1).domJohnsonColor
      (DomCat.alphaOf X.obj.1.1)) := by
  have hd := DomCat.domHyp ⟨X.car, X.obj.1.1⟩
  obtain ⟨x₀, hx₀⟩ := hd.dom
  have hinj : ∀ u ∈ (DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1),
      ∀ v ∈ (DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1),
      (DomCat.objOf X.obj.1.1).nbhd u ∩ (DomCat.objOf X.obj.1.1).bigTwin
        = (DomCat.objOf X.obj.1.1).nbhd v ∩ (DomCat.objOf X.obj.1.1).bigTwin → u = v := by
    intro u hu v hv htr
    by_contra hc
    exact X.obj.1.2 ⟨u, hu, v, hv, hc, htr⟩
  have hC : (DomCat.objOf X.obj.1.1).bigTwin.ncard
      ≠ 2 * (DomCat.objOf X.obj.1.1).localSize x₀ := by
    intro hc
    exact X.obj.2 ⟨x₀, hx₀, hc⟩
  exact hd.domIsJohnsonColoring hinj hx₀ hC

open scoped Classical in
open BlkBlockDesignInputs in
/-- §9.7, Case 2, the last exit.  ***"we are back to Case 1.  Proceed as in Case 1,
exit."***  The Johnson scheme `J(|C|, d*)` on `A`, as an object of `Babai.Out97` on the
subset `A` of `□X` — goal (b) of Theorem 9.2.2. -/
noncomputable def domJohnsonOutcome
    (X : Pt ((((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).full
      (fun s X => ¬ DomBoundP s X)))) :
    (Cat.sub (Out97 Ω)).Obj X.car :=
  ⟨⟨Subtype.val '' ((DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1)),
      by rintro _ ⟨x, -, rfl⟩; exact x.2⟩,
    Sum.inl (Sum.inr ⟨(DomCat.objOf X.obj.1.1).domJohnsonColor (DomCat.alphaOf X.obj.1.1),
      domIsJohnson X⟩)⟩



/-! ### The three branches -/

open BlkBlockDesignInputs in
/-- §9.7, Case 2, the first exit.  ***"Since `Aut(H*)` acts on `C` as the symmetric group,
all edges of `H*` have the same multiplicity.  In other words, `A` is equipartitioned by
the twin equivalence classes in `X*`.  If this is a nontrivial partition, return this
partition, exit."***  (Version 2.5, lines 4270-4272.)

**Proved.**  The single outcome is `Babai.domTwinOutcome`, the `c'`-coloring of `V₁` with
the class `A` refined by the trace `X(v) ∩ C` (entry 80 of the corrected paper why the
partition is returned on `V₁` and not on `A`).  It is a colored `α`-partition
(`Babai.BlkCaseObj.DomHyp.domLabPartition_isAlphaPartition`): a block inside `A` is a trace
class, and all trace classes have the same size
(`Babai.BlkCaseObj.ncard_traceClass_eq`, which is the paper's *"all edges of `H*` have the
same multiplicity"*), so there are at least two of them inside `A` — by the non-triviality
of `X*` (`Babai.BlkCaseObj.DomHyp.one_le_localSize`, `.localSize_lt`, which is
`Babai.case_9_7_2`) — whence a block inside `A` has at most `|A|/2 ≤ n₁/2 < αn₁` points;
and a block outside `A` is a `c'`-color class other than `A`, which has fewer than `αn₁`
points by the definition of `A`.  It is canonical because `c'` and the trace are
(`Babai.BlkCaseObj.IsMorphOn.localSize_eq`, `.domLab_iff`). -/
theorem case_9_7_case2_dom_twin :
    FindsAtMultCost ((DomCat Ω).full DomTwinP) (Out97 Ω)
      (fun X => cost97 (DomCat.bbd ⟨X.car, X.obj.1⟩))
      (fun X Z => Good97 (DomCat.bbd ⟨X.car, X.obj.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub (fun X => {domTwinOutcome X})
    (fun X => ⟨_, rfl⟩) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.one_le_pow _ _ (one_le_numBlocks _)
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hm := DomCat.isMorphOn (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) hf
    have hα := DomCat.alphaOf_eq (X := ⟨X.car, X.obj.1⟩) (Y := ⟨Y.car, Y.obj.1⟩) hf
    refine ⟨domTwinOutcome Y, rfl, ?_⟩
    refine ⟨subEquiv f (fun x => hm.part₁ x), fun _ => rfl, ?_⟩
    refine labPartition_mem_iso f (fun x => hm.part₁ x) (fun x => hm.localSize_eq x)
      (fun x y => ?_)
    rw [← hα]
    exact hm.domLab_iff _ x y
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    refine ⟨rfl, ?_⟩
    obtain ⟨u, hu, v, hv, huv, htr⟩ := X.obj.2
    exact (DomCat.domHyp ⟨X.car, X.obj.1⟩).domLabPartition_isAlphaPartition _ hu hv huv htr

open BlkBlockDesignInputs in
/-- §9.7, Case 2, the boundary exit `|C| = 2d*` (entry 83 of the corrected paper).  There are
no twins in `A`, so `v ↦ X(v) ∩ C` is a bijection of `A` with the `d*`-subsets of `C`; but
for `|C| = 2d*` the coloring `|X(u) ∩ C ∖ X(v)|` is not a Johnson coloring in the sense of
Def. 3.2.9, and the exit returns instead the **canonical equipartition of `A` into the
complementary pairs** `{T, C ∖ T}`.

**Proved.**  The single outcome is `Babai.domPairOutcome`, and it is a colored
`α`-partition by `Babai.BlkCaseObj.DomHyp.domPairPartition_isAlphaPartition`: a block
inside `A` is `{v, w}` with `X(w) ∩ C = C ∖ X(v)` (the partner exists by
`Babai.BlkCaseObj.exists_traceClass` and is unique because there are no twins), so it has
exactly `2 ≤ n₁/2` points. -/
theorem case_9_7_case2_dom_pair :
    FindsAtMultCost (((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).full DomBoundP)
      (Out97 Ω)
      (fun X => cost97 (DomCat.bbd ⟨X.car, X.obj.1.1⟩))
      (fun X Z => Good97 (DomCat.bbd ⟨X.car, X.obj.1.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub (fun X => {domPairOutcome X})
    (fun X => ⟨_, rfl⟩) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.one_le_pow _ _ (one_le_numBlocks _)
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hm := DomCat.isMorphOn (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) hf
    have hα := DomCat.alphaOf_eq (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) hf
    refine ⟨domPairOutcome Y, rfl, ?_⟩
    refine ⟨subEquiv f (fun x => hm.part₁ x), fun _ => rfl, ?_⟩
    refine labPartition_mem_iso f (fun x => hm.part₁ x) (fun x => hm.localSize_eq x)
      (fun x y => ?_)
    rw [← hα]
    exact hm.domPairLab_iff _ x y
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    refine ⟨rfl, ?_⟩
    obtain ⟨x₀, hx₀, hC⟩ := X.obj.2
    have hinj : ∀ u ∈ (DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1),
        ∀ v ∈ (DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1),
        (DomCat.objOf X.obj.1.1).nbhd u ∩ (DomCat.objOf X.obj.1.1).bigTwin
          = (DomCat.objOf X.obj.1.1).nbhd v ∩ (DomCat.objOf X.obj.1.1).bigTwin → u = v := by
      intro u hu v hv htr
      by_contra hc
      exact X.obj.1.2 ⟨u, hu, v, hv, hc, htr⟩
    exact (DomCat.domHyp ⟨X.car, X.obj.1.1⟩).domPairPartition_isAlphaPartition _ hinj hx₀ hC

open BlkBlockDesignInputs in
/-- §9.7, Case 2, the last exit.  ***"Since `X*` is nontrivial, `A` cannot be a set of
twins in `X*`, so the only remaining option is that there are no twins in `A`, i.e. `E*`
has no multiple edges.  Since `C` is a set of twins in `H*`, we are back to Case 1.
Proceed as in Case 1, exit."***  (Version 2.5, lines 4272-4274.)

**Proved.**  The single outcome is `Babai.domJohnsonOutcome`, the Johnson scheme
`J(|C|, d*)` on `A` (`Babai.domIsJohnson`, from
`Babai.BlkCaseObj.DomHyp.domIsJohnsonColoring`).  Goal (b) of Theorem 9.2.2 asks for a
Johnson scheme on a subset of `V₁` of at least `αn₁` points, and `A` is one
(`Babai.BlkCaseObj.DomHyp.alpha_le_ncard_domClass`).  It is canonical because the trace
`X(v) ∩ C` is (`Babai.BlkCaseObj.IsMorphOn.traceColor_eq`). -/
theorem case_9_7_case2_dom_john :
    FindsAtMultCost ((((DomCat Ω).full (fun s X => ¬ DomTwinP s X)).full
      (fun s X => ¬ DomBoundP s X))) (Out97 Ω)
      (fun X => cost97 (DomCat.bbd ⟨X.car, X.obj.1.1⟩))
      (fun X Z => Good97 (DomCat.bbd ⟨X.car, X.obj.1.1⟩) Z) := by
  classical
  refine FindsAtMultCost.of_outcomes_sub (fun X => {domJohnsonOutcome X})
    (fun X => ⟨_, rfl⟩) (fun X => Set.finite_singleton _) (fun X => ?_)
    (fun {X Y f} hf Z hZ => ?_) (fun X Z hZ => ?_)
  · rw [Set.ncard_singleton]
    exact Nat.one_le_pow _ _ (one_le_numBlocks _)
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hm := DomCat.isMorphOn (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) hf
    have hα := DomCat.alphaOf_eq (X := ⟨X.car, X.obj.1.1⟩) (Y := ⟨Y.car, Y.obj.1.1⟩) hf
    have hmem : ∀ x, f x ∈ (DomCat.objOf Y.obj.1.1).domClass (DomCat.alphaOf Y.obj.1.1)
        ↔ x ∈ (DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1) := by
      intro x
      rw [← hα]
      exact hm.mem_domClass_iff _ x
    refine ⟨domJohnsonOutcome Y, rfl, ?_⟩
    refine ⟨subEquiv f hmem, fun _ => rfl, fun u v => ?_⟩
    show ((((DomCat.objOf Y.obj.1.1).nbhd (liftPt (subEquiv f hmem u))
          ∩ (DomCat.objOf Y.obj.1.1).bigTwin)
        \ ((DomCat.objOf Y.obj.1.1).nbhd (liftPt (subEquiv f hmem v))
          ∩ (DomCat.objOf Y.obj.1.1).bigTwin)).ncard) = _
    rw [liftPt_subEquiv, liftPt_subEquiv]
    exact hm.traceColor_eq _ _
  · rw [Set.mem_singleton_iff] at hZ
    subst hZ
    have hd := DomCat.domHyp ⟨X.car, X.obj.1.1⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx.1, rfl⟩
    · have h1 : (BlkBlockDesignInputs.V₁ (DomCat.bbd ⟨X.car, X.obj.1.1⟩)).ncard
          = (DomCat.objOf X.obj.1.1).n₁ :=
        BlkBlockDesignInputs.v₁_ncard _
      have h2 : (Subtype.val '' ((DomCat.objOf X.obj.1.1).domClass
            (DomCat.alphaOf X.obj.1.1))).ncard
          = ((DomCat.objOf X.obj.1.1).domClass (DomCat.alphaOf X.obj.1.1)).ncard :=
        ncard_image_val _
      show BlkBlockDesignInputs.alpha (DomCat.bbd ⟨X.car, X.obj.1.1⟩) *
            ((BlkBlockDesignInputs.V₁ (DomCat.bbd ⟨X.car, X.obj.1.1⟩)).ncard : ℝ)
          ≤ ((Subtype.val '' ((DomCat.objOf X.obj.1.1).domClass
              (DomCat.alphaOf X.obj.1.1))).ncard : ℝ)
      rw [h1, h2]
      exact hd.alpha_le_ncard_domClass

open BlkBlockDesignInputs in
/-- §9.7, Case 2, the two exits at the **dominant `c'`-color class** `A` (version 2.5,
lines 4264-4274).

**Proved.**  The branch condition is that some `c'`-color class has at least `αn₁` points;
*"let `A ⊆ V₁` be the dominant `c'`-color class, so `|A| ≥ αn₁ > n₁/2"*, which is
`Babai.BlkCaseObj.domClass` (it is canonical because `α > 1/2` leaves at most one such
class).  The paper's route is

* *"Let `X* = X[A, C]` … So `X*` is semiregular.  It cannot be trivial because the relative
  sizes of `A` (in `V₁`) and `C` (in `V₂`) add up to more than 1, contradicting
  Cor. 2.4.32."* — `Babai.case_9_7_2`, applied to the link through
  `Babai.BlkCaseObj.linkBipGraph_isSemiregular` and
  `Babai.BlkCaseObj.linkBipGraph_not_isTrivial`; the conclusion is `1 ≤ d* < |C|`
  (`Babai.BlkCaseObj.DomHyp.one_le_localSize`, `.localSize_lt`).
* *"Since `Aut(H*)` acts on `C` as the symmetric group, all edges of `H*` have the same
  multiplicity. … If this is a nontrivial partition, return this partition, exit."* —
  `Babai.case_9_7_case2_dom_twin`, on the test `Babai.DomTwinP`.
* *"Since `C` is a set of twins in `H*`, we are back to Case 1.  Proceed as in Case 1,
  exit."* — `Babai.case_9_7_case2_dom_john`, with the boundary `|C| = 2d*` split off into
  `Babai.case_9_7_case2_dom_pair` by the test `Babai.DomBoundP` (entry 83 of
  the corrected paper).

The three exits are glued by `Babai.FindsAtMultCost.cases` at the two tests, which are
isomorphism invariants (`Babai.domTwinP_congr`, `Babai.domBoundP_congr`).  Both exits
return goal (a) or goal (b) **on `V₁`**, in the shape of `Babai.case2ColOutcome` and
`Babai.case1Outcome`, not in the shape of the restriction. -/
theorem case_9_7_case2_dom :
    FindsAtMultCost ((Case2SelCat Ω).full (fun s X => ¬ Case2SmallP s X)) (Out97 Ω)
      (fun X => cost97 (Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩))
      (fun X Z => Good97 (Case2Cat.bbd ⟨X.car, X.obj.1.1.1⟩) Z) := by
  have hbound := FindsAtMultCost.cases
    (C := (DomCat Ω).full (fun s X => ¬ DomTwinP s X)) (P := DomBoundP)
    (costp := fun Z => cost97 (DomCat.bbd ⟨Z.car, Z.obj.1⟩))
    (costn := fun Z => cost97 (DomCat.bbd ⟨Z.car, Z.obj.1⟩))
    (Good := fun Z W => Good97 (DomCat.bbd ⟨Z.car, Z.obj.1⟩) W)
    (fun {X Y} h hx => domBoundP_congr h hx)
    case_9_7_case2_dom_pair case_9_7_case2_dom_john
  have hbound' := hbound.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  have hall := FindsAtMultCost.cases
    (C := DomCat Ω) (P := DomTwinP)
    (costp := fun Z => cost97 (DomCat.bbd Z))
    (costn := fun Z => cost97 (DomCat.bbd Z))
    (Good := fun Z W => Good97 (DomCat.bbd Z) W)
    (fun {X Y} h hx => domTwinP_congr h hx)
    case_9_7_case2_dom_twin hbound'
  exact hall.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

open BlkBlockDesignInputs in
/-- §9.7, Case 2, *"If `C` is selected"* (version 2.5, lines 4258-4274): the coloring exit
and the dominant-class exits, glued by `Babai.FindsAtMultCost.cases` at the test *"all
`c'`-color classes have size less than `αn₁`"* (`Babai.Case2SmallP`), which is an
isomorphism invariant (`Babai.case2SmallP_congr`). -/
theorem case_9_7_case2_sel :
    FindsAtMultCost (Case2SelCat Ω) (Out97 Ω)
      (fun X => cost97 (Case2Cat.bbd ⟨X.car, X.obj.1.1⟩))
      (fun X Z => Good97 (Case2Cat.bbd ⟨X.car, X.obj.1.1⟩) Z) := by
  have h := FindsAtMultCost.cases
    (C := Case2SelCat Ω) (P := Case2SmallP)
    (costp := fun Z => cost97 (Case2Cat.bbd ⟨Z.car, Z.obj.1.1⟩))
    (costn := fun Z => cost97 (Case2Cat.bbd ⟨Z.car, Z.obj.1.1⟩))
    (Good := fun Z W => Good97 (Case2Cat.bbd ⟨Z.car, Z.obj.1.1⟩) W)
    (fun {X Y} hxy hx => case2SmallP_congr hxy hx)
    case_9_7_case2_small case_9_7_case2_dom
  exact h.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

/-! ### The assembly of Case 2 -/

open BlkBlockDesignInputs in
/-- Case 2 of §9.7.  *"There is an `H`-twin equivalence class `C ⊆ V₂` of size
`|C| ≥ n₂/2`.  So `S(C) ≤ Aut(H)`. … Apply procedure Reduce-Part2-by-Color to the coloring
`(C, V₂ \ C)`.  If `V₂ \ C` is selected, we have made significant progress (reduced `|V₂|`
by half).  If `C` is selected, … If all `c'`-color classes have size less than `αn₁`,
return this coloring, exit.  Otherwise, let `A ⊆ V₁` be the dominant `c'`-color class … If
this is a nontrivial partition, return this partition, exit. … we are back to Case 1.
Proceed as in Case 1, exit."*  (Version 2.5, lines 4252–4274.)

The cost is the one call of Procedure Reduce-Part2-by-Color, `n₂`; it is weakened to the
common cost of `Babai.case_9_7` here.

**`C` is made canonical first.**  The branch condition
`Babai.BlkCaseObj.IsCase2` is the paper's, an existential, while every object this branch
returns is built from `C` and must therefore be carried along by every morphism.  The twin
classes of `Aut(H)` partition `V₂` canonically (`Babai.BlkCaseObj.isHTwin_refl`,
`.isHTwin_symm`, `.isHTwin_trans`), so `C` is determined unless two classes tie.
`Babai.BlkCaseObj.bigTwin`, the union of the classes of size `≥ n₂/2`, is the class when it
is unique (`Babai.BlkCaseObj.bigTwin_spec`) and is all of `V₂` in the tie
(`Babai.BlkCaseObj.tie_spec'`); the test `bigTwin = V₂` separates the two and is an
isomorphism invariant (`Babai.case2TieP_congr`).  See the entry on §9.7 Case 2 in
the corrected paper.

**Status.**  All the exits are **proved**: the tie (`Babai.case_9_7_case2_tie`),
*"if `V₂ ∖ C` is selected"* (`Babai.case_9_7_case2_compl`), *"if all `c'`-color classes
have size less than `αn₁`, return this coloring"* (`Babai.case_9_7_case2_small`), and the
exits at the dominant `c'`-color class (`Babai.case_9_7_case2_dom`). -/
theorem case_9_7_case2 :
    FindsAtMultCost
      (((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
        (fun s X => Case2P s X.1)) (Out97 Ω)
      (fun X => cost97 ⟨X.car, X.obj.1.1⟩)
      (fun X Z => Good97 ⟨X.car, X.obj.1.1⟩ Z) := by
  have hsel := FindsAtMultCost.cases
    (C := (Case2Cat Ω).full (fun s X => ¬ Case2TieP s X))
    (P := Case2SelP)
    (costp := fun Z => cost97 (Case2Cat.bbd ⟨Z.car, Z.obj.1⟩))
    (costn := fun Z => cost97 (Case2Cat.bbd ⟨Z.car, Z.obj.1⟩))
    (Good := fun Z W => Good97 (Case2Cat.bbd ⟨Z.car, Z.obj.1⟩) W)
    (fun {X Y} h hx => case2SelP_congr h hx)
    case_9_7_case2_sel case_9_7_case2_compl
  have hsel' := hsel.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)
  have hall := FindsAtMultCost.cases
    (C := Case2Cat Ω) (P := Case2TieP)
    (costp := fun Z => cost97 (Case2Cat.bbd Z))
    (costn := fun Z => cost97 (Case2Cat.bbd Z))
    (Good := fun Z W => Good97 (Case2Cat.bbd Z) W)
    (fun {X Y} h hx => case2TieP_congr h hx)
    case_9_7_case2_tie hsel'
  exact hall.mono (fun _ => le_of_eq (max_self _)) (fun _ _ h => h)

end Babai
