/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: the Design Lemma as an abstract statement `DL(α)`; Observation 8.1.3 and the
first half of the "Proof of equivalence" (Theorem 8.1.2 ⇒ Theorem 8.1.5).
-/
import Workspace.DesignLemma.Main
import Workspace.Refinement.NamedConfig
import Workspace.SplitOrJohnson.HintBuild
import Workspace.SplitOrJohnson.Step8

/-!
# §8.1 The Design Lemma as a statement about canonical assignments

Theorems 8.1.2 and 8.1.5 are proved in `Workspace/DesignLemma/Main.lean` for the concrete
objects produced by Procedure "Design Lemma" (§8.2).  Observation 8.1.3 and the first half
of the "Proof of equivalence" are not about those objects: they treat the Design Lemma as
an abstract statement, `DL(α)`, which asserts that *some* canonical coloring (and so on)
with the stated properties can be found, and derive one such statement from another by
building new canonical objects out of old ones.  This file formalizes that reading.

## The abstract statement

*Canonicity relative to `x⃗`* (§6): the objects are assigned to every pair (structure `X`,
string `x⃗`), on every finite vertex set, and every isomorphism `f : X → Y` carries the
objects assigned to `(X, x⃗)` to those assigned to `(Y, x⃗^f)`.  An assignment returns a
`Babai.DesignAbstract.DLData`: a coloring `col : Ω → ℕ` of `Ω`, a set `part` of blocks
(the equipartition of case (b)), and an edge coloring `cfg : Ω → Ω → ℕ` (the configuration
of case (c), respectively the configuration `X*` of case (ii)).  Colors are names, and a
canonical object keeps its names under isomorphisms, as in §6.

* `DL812 C α` is Theorem 8.1.2 for `k`-ary structures with relation colors `C`, without the
  running time (pending): there is a canonical assignment such
  that every admissible `X` has a string `x⃗` of `ℓ ≤ k − 1` distinct vertices at which
  outcome (a), (b) or (c) holds;
* `DL815 C α` is Theorem 8.1.5 in the same form, with outcomes (i) and (ii).

## The results

* `Babai.DesignAbstract.observation_8_1_3`: `DL(α) ⇒ DL(α')` for `1/2 ≤ α ≤ α' < 1`,
  by the paper's proof;
* `Babai.DesignAbstract.theorem_8_1_2_imp_8_1_5`: Theorem 8.1.2 ⇒ Theorem 8.1.5, by the
  first half of the paper's "Proof of equivalence".  The second half (8.1.5 ⇒ 8.1.2) is
  `Babai.KAryPartStruct.imprimitive_or_uniprimitive`, used in the proof of
  `Babai.KAryRelStruct.theorem_8_1_2`.
-/

set_option linter.unusedSectionVars false

namespace Babai

namespace DesignAbstract

open KAryRelStruct

variable {C : Type}

/-! ### Data, assignments, canonicity -/

/-- The objects returned by the Design Lemma at one string: a coloring of `Ω`, a set of
blocks (case (b)), and an edge coloring (case (c), or `X*` of case (ii)). -/
structure DLData (Ω : Type) where
  col : Ω → ℕ
  part : Set (Set Ω)
  cfg : Ω → Ω → ℕ

/-- An assignment of Design Lemma data to every `k`-ary structure and every string. -/
def Assignment (C : Type) : Type 1 :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ), KAryRelStruct Ω C k →
    (l : ℕ) → Str Ω l → DLData Ω

/-- `D'` is the image of `D` under the bijection `f`. -/
structure DLData.Corr {Ω Ω' : Type} (f : Ω ≃ Ω') (D : DLData Ω) (D' : DLData Ω') : Prop where
  col : ∀ u, D'.col (f u) = D.col u
  part : D'.part = (fun B => f '' B) '' D.part
  cfg : ∀ u v, D'.cfg (f u) (f v) = D.cfg u v

/-- §6, canonicity relative to `x⃗`: an isomorphism `f : X → Y` carries the data assigned to
`(X, x⃗)` to the data assigned to `(Y, x⃗^f)`. -/
def IsCanonical (A : Assignment C) : Prop :=
  ∀ (Ω Ω' : Type) [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] (k : ℕ)
    (X : KAryRelStruct Ω C k) (Y : KAryRelStruct Ω' C k) (f : Ω ≃ Ω'), f ∈ Iso X Y →
    ∀ (l : ℕ) (x : Str Ω l), DLData.Corr f (A Ω k X l x) (A Ω' k Y l (tupleMap f x))

/-! ### The outcomes -/

section Outcomes

variable {Ω : Type} [Fintype Ω]

/-- Definition 8.1.1: a coloring *with no dominant color*. -/
def NoDom (α : ℝ) (col : Ω → ℕ) : Prop := ∀ c : ℕ, ¬ IsDominant α {v | col v = c}

/-- `S` is the dominant color class of `col` (Definition 8.1.1). -/
def DomClass (α : ℝ) (col : Ω → ℕ) (S : Set Ω) : Prop :=
  (∃ c : ℕ, S = {v | col v = c}) ∧ IsDominant α S

open Classical in
/-- The configuration `(S, cfg|_S)` on a subset `S`. -/
noncomputable def cfgOn (cfg : Ω → Ω → ℕ) (S : Set Ω) : PartitionStructure S :=
  PartitionStructure.ofColoring (fun a b : S => cfg a b)

open Classical in
theorem cfgOn_color_eq_iff (cfg : Ω → Ω → ℕ) (S : Set Ω) (a b x y : S) :
    (cfgOn cfg S).color a b = (cfgOn cfg S).color x y ↔ cfg a b = cfg x y :=
  PartitionStructure.ofColoring_color_eq_iff _ a b x y

/-- The three outcomes of Theorem 8.1.2 for the data `D`:
(a) a coloring with no dominant color; (b) a nontrivial equipartition of the dominant color
class; (c) a UPCC whose vertex set is the dominant color class. -/
def Outcome812 (α : ℝ) (D : DLData Ω) : Prop :=
  NoDom α D.col ∨
    (∃ S, DomClass α D.col S ∧ IsEquipartitionOn D.part S ∧ IsNontrivialPartition D.part) ∨
    (∃ S, DomClass α D.col S ∧ (cfgOn D.cfg S).IsCoherent ∧ (cfgOn D.cfg S).IsUniprimitive)

variable [DecidableEq Ω] in
/-- The two outcomes of Theorem 8.1.5 for the data `D`: (i) a coloring with no dominant
color; (ii) a coherent configuration `X* = (Ω, cfg)` whose subconfiguration induced on its
dominant vertex-color class is not a clique. -/
def Outcome815 (α : ℝ) (D : DLData Ω) : Prop :=
  NoDom α D.col ∨
    ((PartitionStructure.ofColoring D.cfg).IsCoherent ∧
      ∃ S, DomClass α (fun v => D.cfg v v) S ∧
        ¬ (PartitionStructure.ofColoring D.cfg).IsCliqueOn S)

end Outcomes

/-- The hypotheses of Theorems 8.1.2 and 8.1.5: `2 ≤ k ≤ n/2` and symmetry defect
`≥ 1 − α`. -/
def Admissible {Ω : Type} [Fintype Ω] [DecidableEq Ω] {k : ℕ} (α : ℝ)
    (X : KAryRelStruct Ω C k) : Prop :=
  2 ≤ k ∧ 2 * k ≤ Fintype.card Ω ∧ (1 : ℝ) - α ≤ (defect X.Aut : ℝ)

/-- The assignment `A` reaches an outcome of Theorem 8.1.2 on every admissible input. -/
def Reaches812 (α : ℝ) (A : Assignment C) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
    Admissible α X → ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧ Outcome812 α (A Ω k X l x)

/-- The assignment `A` reaches an outcome of Theorem 8.1.5 on every admissible input. -/
def Reaches815 (α : ℝ) (A : Assignment C) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
    Admissible α X → ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧ Outcome815 α (A Ω k X l x)

variable (C) in
/-- **Theorem 8.1.2** (Design lemma) as the abstract statement `DL(α)` of Observation 8.1.3,
without the running time: there is a canonical assignment such that for every admissible
`X` some string of `ℓ ≤ k − 1` distinct vertices reaches outcome (a), (b) or (c). -/
def DL812 (α : ℝ) : Prop :=
  ∃ A : Assignment C, IsCanonical A ∧
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
      Admissible α X → ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧ Outcome812 α (A Ω k X l x)

variable (C) in
/-- **Theorem 8.1.5** (Design lemma, rephrased), in the same form as `DL812`. -/
def DL815 (α : ℝ) : Prop :=
  ∃ A : Assignment C, IsCanonical A ∧
    ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
      Admissible α X → ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧ Outcome815 α (A Ω k X l x)

/-! ### Transport lemmas -/

section Transport

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']

omit [Fintype Ω] [Fintype Ω'] in
/-- A bijection preserves the size of a set. -/
theorem ncard_image_equiv (f : Ω ≃ Ω') (S : Set Ω) : (f '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S f.injective

omit [Fintype Ω] [Fintype Ω'] in
/-- A bijection carries the color classes of `col` to those of `col ∘ f⁻¹`. -/
theorem colorClass_corr {col : Ω → ℕ} {col' : Ω' → ℕ} (f : Ω ≃ Ω')
    (h : ∀ u, col' (f u) = col u) (c : ℕ) : {v | col' v = c} = f '' {v | col v = c} := by
  ext w
  constructor
  · intro hw
    exact ⟨f.symm w, by simpa [← h (f.symm w)] using hw, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    simpa [Set.mem_setOf_eq, h u] using hu

theorem card_eq_of_equiv (f : Ω ≃ Ω') : Fintype.card Ω = Fintype.card Ω' :=
  Fintype.card_congr f

theorem isDominant_image_iff (f : Ω ≃ Ω') {α : ℝ} (S : Set Ω) :
    IsDominant α (f '' S) ↔ IsDominant α S := by
  unfold IsDominant
  rw [ncard_image_equiv, card_eq_of_equiv f]

theorem noDom_corr {col : Ω → ℕ} {col' : Ω' → ℕ} (f : Ω ≃ Ω')
    (h : ∀ u, col' (f u) = col u) {α : ℝ} : NoDom α col' ↔ NoDom α col := by
  unfold NoDom
  refine forall_congr' fun c => ?_
  rw [colorClass_corr f h c, isDominant_image_iff]

end Transport

/-! ### Twins are transported by isomorphisms -/

section Twins

variable {Ω Ω' : Type} [DecidableEq Ω] [DecidableEq Ω'] {k : ℕ}

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem conj_mem_aut {X : KAryRelStruct Ω C k} {Y : KAryRelStruct Ω' C k} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) {σ : Equiv.Perm Ω} (hσ : σ ∈ X.Aut) :
    ((f.symm.trans σ).trans f : Equiv.Perm Ω') ∈ Y.Aut := by
  intro i y
  have hy : y = tupleMap f (tupleMap f.symm y) := by funext j; simp [tupleMap]
  have e1 := hf i (tupleMap f.symm y)
  have e2 := hσ i (tupleMap f.symm y)
  have e3 := hf i (tupleMap σ (tupleMap f.symm y))
  have hτ : tupleMap ((f.symm.trans σ).trans f : Equiv.Perm Ω') y
      = tupleMap f (tupleMap σ (tupleMap f.symm y)) := by
    funext j; simp [tupleMap]
  rw [hτ, ← e3, ← e2, e1, ← hy]

theorem isTwin_iso_iff {X : KAryRelStruct Ω C k} {Y : KAryRelStruct Ω' C k} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) (a b : Ω) : IsTwin Y.Aut (f a) (f b) ↔ IsTwin X.Aut a b := by
  have hfs : f.symm ∈ Iso Y X := by
    intro i y
    have hy : tupleMap f (tupleMap f.symm y) = y := by funext j; simp [tupleMap]
    rw [hf i (tupleMap f.symm y), hy]
  constructor
  · rintro ⟨hne, hmem⟩
    refine ⟨fun h => hne (by rw [h]), ?_⟩
    have := conj_mem_aut hfs hmem
    rwa [show ((f.symm.symm.trans (Equiv.swap (f a) (f b))).trans f.symm : Equiv.Perm Ω)
        = Equiv.swap (f.symm (f a)) (f.symm (f b)) from Equiv.symm_trans_swap_trans _ _ _,
      f.symm_apply_apply, f.symm_apply_apply] at this
  · rintro ⟨hne, hmem⟩
    refine ⟨fun h => hne (f.injective h), ?_⟩
    have := conj_mem_aut hf hmem
    rwa [Equiv.symm_trans_swap_trans] at this

theorem twinClass_iso {X : KAryRelStruct Ω C k} {Y : KAryRelStruct Ω' C k} {f : Ω ≃ Ω'}
    (hf : f ∈ Iso X Y) (v : Ω) : twinClass Y.Aut (f v) = f '' twinClass X.Aut v := by
  ext w
  constructor
  · intro hw
    refine ⟨f.symm w, ?_, by simp⟩
    rcases hw with h | h
    · exact Or.inl (by rw [← h]; simp)
    · refine Or.inr ((isTwin_iso_iff hf v (f.symm w)).1 ?_)
      simpa using h
  · rintro ⟨u, hu | hu, rfl⟩
    · exact Or.inl (by rw [hu])
    · exact Or.inr ((isTwin_iso_iff hf v u).2 hu)

end Twins

/-! ### Observation 8.1.3 -/

section Obs813

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open Classical in
/-- The two-class coloring `(U, Ω ∖ U)` of Case 2 of the proof of Observation 8.1.3: a point
gets color `1` if its twin equivalence class has more than `αn` points.  For `α ≥ 1/2` at
most one twin class is that large, so color `1` is the largest symmetric subset `U`. -/
noncomputable def bigTwinColor {k : ℕ} (α : ℝ) (X : KAryRelStruct Ω C k) (v : Ω) : ℕ :=
  if IsDominant α (twinClass X.Aut v) then 1 else 0

open Classical in
/-- The two-class coloring `(C, Ω ∖ C)` of Case 1 of the proof of Observation 8.1.3: a
point gets color `1` if its color class `C` has size in `(αn, α'n]`. -/
noncomputable def midClassColor (α α' : ℝ) (col : Ω → ℕ) (v : Ω) : ℕ :=
  if IsDominant α {w | col w = col v} ∧ ¬ IsDominant α' {w | col w = col v} then 1 else 0

open Classical in
/-- The assignment built in the proof of Observation 8.1.3 from an assignment `A` for
`DL(α)`. -/
noncomputable def obsAssign (α α' : ℝ) (A : Assignment C) : Assignment C :=
  fun Ω _ _ k X l x =>
    if ∃ v : Ω, IsDominant α (twinClass X.Aut v) then
      ⟨bigTwinColor α X, ∅, fun _ _ => 0⟩
    else if ∃ c : ℕ, IsDominant α {w | (A Ω k X l x).col w = c} ∧
        ¬ IsDominant α' {w | (A Ω k X l x).col w = c} then
      ⟨midClassColor α α' (A Ω k X l x).col, (A Ω k X l x).part, (A Ω k X l x).cfg⟩
    else A Ω k X l x

theorem obsAssign_canonical {α α' : ℝ} {A : Assignment C} (hA : IsCanonical A) :
    IsCanonical (obsAssign α α' A) := by
  classical
  intro Ω Ω' _ _ _ _ k X Y f hf l x
  have hD := hA Ω Ω' k X Y f hf l x
  set D := A Ω k X l x with hDdef
  set D' := A Ω' k Y l (tupleMap f x) with hD'def
  -- the branch conditions are invariant
  have hc1 : (∃ v : Ω', IsDominant α (twinClass Y.Aut v)) ↔
      ∃ v : Ω, IsDominant α (twinClass X.Aut v) := by
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨f.symm w, ?_⟩
      rw [← isDominant_image_iff f, ← twinClass_iso hf]
      simpa using hw
    · rintro ⟨v, hv⟩
      exact ⟨f v, by rw [twinClass_iso hf, isDominant_image_iff]; exact hv⟩
  have hcls : ∀ c, {w | D'.col w = c} = f '' {w | D.col w = c} :=
    colorClass_corr f hD.col
  have hc2 : (∃ c : ℕ, IsDominant α {w | D'.col w = c} ∧ ¬ IsDominant α' {w | D'.col w = c})
      ↔ ∃ c : ℕ, IsDominant α {w | D.col w = c} ∧ ¬ IsDominant α' {w | D.col w = c} := by
    refine exists_congr fun c => ?_
    rw [hcls c, isDominant_image_iff, isDominant_image_iff]
  simp only [obsAssign]
  by_cases h1 : ∃ v : Ω, IsDominant α (twinClass X.Aut v)
  · rw [if_pos h1, if_pos (hc1.2 h1)]
    refine ⟨fun u => ?_, by simp, fun _ _ => rfl⟩
    exact if_congr (by rw [twinClass_iso hf, isDominant_image_iff]) rfl rfl
  · rw [if_neg h1, if_neg (fun h => h1 (hc1.1 h))]
    by_cases h2 : ∃ c : ℕ, IsDominant α {w | D.col w = c} ∧ ¬ IsDominant α' {w | D.col w = c}
    · rw [← hDdef, ← hD'def, if_pos h2, if_pos (hc2.2 h2)]
      refine ⟨fun u => ?_, hD.part, hD.cfg⟩
      exact if_congr (by rw [hD.col u, hcls (D.col u), isDominant_image_iff,
        isDominant_image_iff]) rfl rfl
    · rw [← hDdef, ← hD'def, if_neg h2, if_neg (fun h => h2 (hc2.1 h))]
      exact hD

omit [DecidableEq Ω] in
/-- The arithmetic of both cases of the proof: a two-class coloring whose color-`1` class
`U` has `|U| ≤ α'n` and `|U| > αn ≥ n/2` has no `α'`-dominant color, since
`|Ω ∖ U| < n − αn ≤ n/2 ≤ α'n`. -/
theorem noDom_two_class {α α' : ℝ} (hα : 1 / 2 ≤ α) (hαα' : α ≤ α') (col : Ω → ℕ)
    (hcol : ∀ v, col v = 0 ∨ col v = 1)
    (hU1 : IsDominant α {v | col v = 1}) (hU2 : ¬ IsDominant α' {v | col v = 1}) :
    NoDom α' col := by
  intro c hc
  have hn : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := Nat.cast_nonneg _
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · interval_cases c
    · -- the class `0` is the complement of the class `1`
      have hsum : ({v : Ω | col v = 1}).ncard + ({v : Ω | col v = 0}).ncard
          = Fintype.card Ω := by
        have hcompl : {v : Ω | col v = 0} = {v : Ω | col v = 1}ᶜ := by
          ext v
          rcases hcol v with h | h <;> simp [h]
        rw [hcompl, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
      have hsumR : (({v : Ω | col v = 1}).ncard : ℝ) + (({v : Ω | col v = 0}).ncard : ℝ)
          = (Fintype.card Ω : ℝ) := by exact_mod_cast hsum
      unfold IsDominant at hU1 hc
      nlinarith
    · exact hU2 hc
  · have hempty : {v : Ω | col v = c} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rcases hcol v with h | h <;> omega
    unfold IsDominant at hc
    rw [hempty, Set.ncard_empty, Nat.cast_zero] at hc
    have : 0 ≤ α' * (Fintype.card Ω : ℝ) := by
      have : (0 : ℝ) ≤ α' := by linarith
      positivity
    linarith

/-- In Case 2 the symmetric subset `U` is not `α'`-dominant: its size is at most the
symmetricity `s(Aut X) ≤ α'n`, by the defect hypothesis `1 − α' ≤ 1 − s/n`. -/
theorem not_isDominant_twinClass {k : ℕ} {α' : ℝ} (X : KAryRelStruct Ω C k)
    (hdef : (1 : ℝ) - α' ≤ (defect X.Aut : ℝ)) (hn : 0 < Fintype.card Ω) (v : Ω) :
    ¬ IsDominant α' (twinClass X.Aut v) := by
  classical
  intro hdom
  have hle : (twinClass X.Aut v).ncard ≤ symmetricity X.Aut := by
    have h := le_symmetricity (G := X.Aut) (Ψ := (twinClass X.Aut v).toFinset)
      (by simpa using twinClass_isTwinSet X.Aut v)
    rwa [Set.ncard_eq_toFinset_card']
  have hnR : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hn
  have hd : (defect X.Aut : ℝ) = 1 - (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) := by
    simp [defect, relSymmetricity]
  rw [hd] at hdef
  have hs : (symmetricity X.Aut : ℝ) ≤ α' * (Fintype.card Ω : ℝ) := by
    have h1 : (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) ≤ α' := by linarith
    rwa [div_le_iff₀ hnR] at h1
  have hleR : ((twinClass X.Aut v).ncard : ℝ) ≤ (symmetricity X.Aut : ℝ) := by
    exact_mod_cast hle
  unfold IsDominant at hdom
  linarith

/-- If no twin class is `α`-dominant then `s(Aut X) ≤ αn`, i.e. the defect is `≥ 1 − α`:
this is how Case 1 of the proof of Observation 8.1.3 applies `DL(α)`. -/
theorem defect_ge_of_no_big_twinClass {k : ℕ} {α : ℝ} (X : KAryRelStruct Ω C k)
    (h : ¬ ∃ v : Ω, IsDominant α (twinClass X.Aut v)) (hn : 0 < Fintype.card Ω) :
    (1 : ℝ) - α ≤ (defect X.Aut : ℝ) := by
  classical
  push Not at h
  have hnR : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hn
  -- every set of twins lies in a twin class, whose size is at most `αn`
  have hs : (symmetricity X.Aut : ℝ) ≤ α * (Fintype.card Ω : ℝ) := by
    obtain ⟨Ψ, hΨ, hΨeq⟩ : ∃ Ψ ∈ (Finset.univ.filter fun Ψ : Finset Ω =>
        IsTwinSet X.Aut (↑Ψ : Set Ω)), symmetricity X.Aut = Ψ.card := by
      unfold symmetricity
      exact Finset.exists_mem_eq_sup _ ⟨∅, by simp [IsTwinSet]⟩ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    rw [hΨeq]
    rcases Ψ.eq_empty_or_nonempty with he | ⟨v, hv⟩
    · subst he
      simp only [Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ α * (Fintype.card Ω : ℝ) := by
        have h0 := h (Fintype.card_pos_iff.mp hn).some
        rw [not_isDominant_iff] at h0
        exact le_trans (Nat.cast_nonneg _) h0
      exact this
    · have hsub : (↑Ψ : Set Ω) ⊆ twinClass X.Aut v := hΨ.subset_twinClass hv
      have hle : Ψ.card ≤ (twinClass X.Aut v).ncard := by
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rwa [Set.ncard_coe_finset] at this
      have hle' := (not_isDominant_iff).1 (h v)
      have : (Ψ.card : ℝ) ≤ ((twinClass X.Aut v).ncard : ℝ) := by exact_mod_cast hle
      linarith
  have hd : (defect X.Aut : ℝ) = 1 - (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) := by
    simp [defect, relSymmetricity]
  rw [hd]
  have : (symmetricity X.Aut : ℝ) / (Fintype.card Ω : ℝ) ≤ α := by
    rw [div_le_iff₀ hnR]; exact hs
  linarith

end Obs813

/-- Observation 8.1.3, the objects: if `A` reaches an outcome of `DL(α)` on every input
admissible for `α`, then `obsAssign α α' A` reaches an outcome of `DL(α')` on every input
admissible for `α'`.  The proof is the paper's (see `observation_8_1_3`). -/
theorem obsAssign_reaches {α α' : ℝ} (hα : 1 / 2 ≤ α) (hαα' : α ≤ α') {A : Assignment C}
    (hA : Reaches812 α A) : Reaches812 α' (obsAssign α α' A) := by
  classical
  intro Ω _ _ k X hX
  obtain ⟨hk2, hkn, hdef⟩ := hX
  have hn : 0 < Fintype.card Ω := by omega
  by_cases h1 : ∃ v : Ω, IsDominant α (twinClass X.Aut v)
  · -- Case 2: `α < β ≤ α'`; the empty string and the coloring `(U, Ω ∖ U)`
    refine ⟨0, by omega, Fin.elim0, fun a => Fin.elim0 a, Or.inl ?_⟩
    simp only [obsAssign, if_pos h1]
    obtain ⟨v₀, hv₀⟩ := h1
    have hcol : ∀ v, bigTwinColor α X v = 0 ∨ bigTwinColor α X v = 1 := by
      intro v; unfold bigTwinColor; split_ifs <;> simp
    -- the color-`1` class is the twin class of `v₀`
    have hclass : {v | bigTwinColor α X v = 1} = twinClass X.Aut v₀ := by
      ext v
      simp only [bigTwinColor, Set.mem_setOf_eq]
      constructor
      · intro hv
        split_ifs at hv with hd
        · -- two dominant sets meet, and twin classes are equivalence classes
          have hmeet := hd.not_disjoint hα hv₀
          rw [Set.not_disjoint_iff] at hmeet
          obtain ⟨w, hw1, hw2⟩ := hmeet
          have he := twinOrEq_equivalence X.Aut
          exact he.trans hw2 (he.symm hw1)
      · intro hv
        have he := twinOrEq_equivalence X.Aut
        have heq : twinClass X.Aut v = twinClass X.Aut v₀ := by
          ext w
          exact ⟨fun hw => he.trans hv hw, fun hw => he.trans (he.symm hv) hw⟩
        rw [if_pos (by rw [heq]; exact hv₀)]
    refine noDom_two_class hα hαα' _ hcol (by rw [hclass]; exact hv₀) ?_
    rw [hclass]
    exact not_isDominant_twinClass X hdef hn v₀
  · -- Case 1: `β ≤ α`; apply `DL(α)`
    have hdefα := defect_ge_of_no_big_twinClass X h1 hn
    obtain ⟨l, hl, x, hx, hout⟩ := hA Ω k X ⟨hk2, hkn, hdefα⟩
    refine ⟨l, hl, x, hx, ?_⟩
    simp only [obsAssign, if_neg h1]
    set D := A Ω k X l x with hDdef
    by_cases h2 : ∃ c : ℕ, IsDominant α {w | D.col w = c} ∧ ¬ IsDominant α' {w | D.col w = c}
    · -- `αn < |C| ≤ α'n`: the coloring `(C, Ω ∖ C)`
      rw [if_pos h2]
      refine Or.inl ?_
      obtain ⟨c, hc1, hc2⟩ := h2
      have hcol : ∀ v, midClassColor α α' D.col v = 0 ∨ midClassColor α α' D.col v = 1 := by
        intro v; unfold midClassColor; split_ifs <;> simp
      have hclass : {v | midClassColor α α' D.col v = 1} = {w | D.col w = c} := by
        ext v
        simp only [midClassColor, Set.mem_setOf_eq]
        constructor
        · intro hv
          split_ifs at hv with hd
          · exact IsDominant.subsingleton hα D.col hd.1 hc1
        · intro hv
          rw [if_pos (by rw [hv]; exact ⟨hc1, hc2⟩)]
      exact noDom_two_class hα hαα' _ hcol (by rw [hclass]; exact hc1) (by rw [hclass]; exact hc2)
    · rw [if_neg h2]
      push Not at h2
      -- a class that is `α`-dominant is `α'`-dominant
      have hup : ∀ S, DomClass α D.col S → DomClass α' D.col S := by
        rintro S ⟨⟨c, rfl⟩, hS⟩
        exact ⟨⟨c, rfl⟩, h2 c hS⟩
      rcases hout with ha | ⟨S, hS, hb⟩ | ⟨S, hS, hc⟩
      · refine Or.inl fun c hc => ha c ?_
        unfold IsDominant at hc ⊢
        have : α * (Fintype.card Ω : ℝ) ≤ α' * (Fintype.card Ω : ℝ) :=
          mul_le_mul_of_nonneg_right hαα' (Nat.cast_nonneg _)
        linarith
      · exact Or.inr (Or.inl ⟨S, hup S hS, hb⟩)
      · exact Or.inr (Or.inr ⟨S, hup S hS, hc⟩)

/-- **Observation 8.1.3**, §8.1.

> Let `DL(α)` be the statement of the Design Lemma for a particular `α ≥ 1/2`.  If
> `1 > α' ≥ α ≥ 1/2` then `DL(α')` follows from `DL(α)`.

The bound `α' < 1` is not used by the proof and is omitted (for `α' ≥ 1` the hypothesis
`defect ≥ 1 − α'` holds for every structure, and the proof goes through unchanged).

*Proof* (the paper's).  Let `U` be a largest symmetric subset of `Ω` and `β = |U|/n`;
the hypothesis of `DL(α')` is `β ≤ α'`.  *Case 1*, `β ≤ α`: apply `DL(α)`.  Outcome (a)
stays (a); (b) and (c) stay (b) and (c) if the dominant class `C` has `|C| > α'n`; if
`αn < |C| ≤ α'n`, the coloring `(C, Ω ∖ C)` gives outcome (a) of `DL(α')`.  *Case 2*,
`α < β ≤ α'`: the coloring `(U, Ω ∖ U)` gives outcome (a) of `DL(α')`.

Here `β > α` is read as "some twin equivalence class is `α`-dominant" (the twin classes are
the maximal symmetric subsets, Obs. 2.3.12), and `U` is that class; the two-class colorings
are `Babai.DesignAbstract.bigTwinColor` and `Babai.DesignAbstract.midClassColor`, and they
are canonical because `U` and `C` are (`Babai.DesignAbstract.obsAssign_canonical`).  In a
case (a) the string is the one `DL(α)` returns, or the empty string in Case 2 (no
individualization is needed there).  The paper's "(case (a) or (b) holds for `DL(α')`)"
for an outcome (b) with `αn < |C| ≤ α'n` is outcome (a), as for (c). -/
theorem observation_8_1_3 {α α' : ℝ} (hα : 1 / 2 ≤ α) (hαα' : α ≤ α')
    (h : DL812 C α) : DL812 C α' := by
  obtain ⟨A, hAcan, hA⟩ := h
  exact ⟨obsAssign α α' A, obsAssign_canonical hAcan, obsAssign_reaches hα hαα' hA⟩

/-! ### The glued configuration of the "Proof of equivalence" -/

section Glue

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] (col : Ω → ℕ) (c0 : ℕ) (d : Ω → Ω → ℕ)

/-- The coloring `c''` of the "Proof of equivalence" (8.1.2 ⇒ 8.1.5), with the diagonal
separated (the corrected paper, "Proof of equivalence 8.1.2 ⇒ 8.1.5"): a diagonal pair `(x,x)`
gets the tag `inl (c'(x))`; a pair `x ≠ y` of points of `C = c'⁻¹(c₀)` gets
`inr (inl (d(x,y)))`; every other pair gets `inr (inr (c'(x), c'(y)))`.

The paper gives `(x,x)` the color `(c'(x), c'(x))`, the same color as a pair `x ≠ y` of
points of one non-dominant class; then `c''` is not a configuration (Def. 3.1.2(i)) as soon
as such a class has two points. -/
def glue (x y : Ω) : ℕ ⊕ ℕ ⊕ (ℕ × ℕ) :=
  if x = y then Sum.inl (col x)
  else if col x = c0 ∧ col y = c0 then Sum.inr (Sum.inl (d x y))
  else Sum.inr (Sum.inr (col x, col y))

/-- The hypotheses on the coloring `d` of `C × C` used by the "Proof of equivalence": it is
coherent, homogeneous, and has two off-diagonal pairs of different colors (so `(C, d)` is
not a clique).  Both the UPCC of case (c) and the configuration of an equipartition in
case (b) satisfy them (`Babai.DesignAbstract.goodOn_of_upcc`,
`Babai.DesignAbstract.goodOn_eqvNat`). -/
structure GoodOn : Prop where
  coh : WL.IsCoherentColoring (fun a b : {v : Ω // col v = c0} => d a b)
  homog : ∀ a b, col a = c0 → col b = c0 → d a a = d b b
  wit : ∃ a b a' b', col a = c0 ∧ col b = c0 ∧ col a' = c0 ∧ col b' = c0 ∧ a ≠ b ∧
    a' ≠ b' ∧ d a b ≠ d a' b'

variable {col c0 d}

theorem glue_self (x : Ω) : glue col c0 d x x = Sum.inl (col x) := by simp [glue]

theorem glue_in {x y : Ω} (hxy : x ≠ y) (hx : col x = c0) (hy : col y = c0) :
    glue col c0 d x y = Sum.inr (Sum.inl (d x y)) := by
  simp [glue, hxy, hx, hy]

theorem glue_pr {x y : Ω} (hxy : x ≠ y) (h : ¬ (col x = c0 ∧ col y = c0)) :
    glue col c0 d x y = Sum.inr (Sum.inr (col x, col y)) := by
  simp only [glue, hxy, if_false, if_neg h]

theorem glue_mem_not {x z : Ω} (hx : col x = c0) (hz : col z ≠ c0) :
    glue col c0 d x z = Sum.inr (Sum.inr (col x, col z)) ∧
      glue col c0 d z x = Sum.inr (Sum.inr (col z, col x)) := by
  have hne : x ≠ z := by rintro rfl; exact hz hx
  exact ⟨glue_pr hne (fun h => hz h.2), glue_pr hne.symm (fun h => hz h.1)⟩

/-- The tag of a pair determines the colors of its two ends and whether it is diagonal. -/
theorem glue_col {x y x' y' : Ω} (h : glue col c0 d x y = glue col c0 d x' y') :
    col x = col x' ∧ col y = col y' ∧ (x = y ↔ x' = y') := by
  unfold glue at h
  by_cases hxy : x = y <;> by_cases hxy' : x' = y'
  · subst hxy hxy'
    simp only [if_true, Sum.inl.injEq] at h
    exact ⟨h, h, by simp⟩
  · simp only [hxy, hxy', if_true, if_false] at h
    split_ifs at h
  · simp only [hxy, hxy', if_true, if_false] at h
    split_ifs at h
  · simp only [hxy, hxy', if_false] at h
    split_ifs at h with h1 h2 h2
    · exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm, by simp [hxy, hxy']⟩
    · simp at h
    · simp at h
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact ⟨h.1, h.2, by simp [hxy, hxy']⟩

variable (hG : GoodOn col c0 d)
include hG

/-- On `C` the tags and the colors of `d` have the same classes. -/
theorem glue_kernel_on {a b a' b' : Ω} (ha : col a = c0) (hb : col b = c0)
    (ha' : col a' = c0) (hb' : col b' = c0) :
    glue col c0 d a b = glue col c0 d a' b' ↔ d a b = d a' b' := by
  have hdiag : ∀ u v, col u = c0 → col v = c0 → d u v = d v v → u = v := by
    intro u v hu hv huv
    have := hG.coh.1.1 ⟨u, hu⟩ ⟨v, hv⟩ ⟨v, hv⟩ huv
    exact congrArg Subtype.val this
  constructor
  · intro h
    obtain ⟨-, -, hiff⟩ := glue_col h
    by_cases hab : a = b
    · subst hab
      obtain rfl := hiff.1 rfl
      exact hG.homog a a' ha ha'
    · have hab' : a' ≠ b' := fun h' => hab (hiff.2 h')
      rw [glue_in hab ha hb, glue_in hab' ha' hb'] at h
      simpa using h
  · intro h
    by_cases hab : a = b
    · subst hab
      have hab' : a' = b' := hdiag a' b' ha' hb'
        (h.symm.trans (hG.homog a b' ha hb'))
      subst hab'
      rw [glue_self, glue_self, ha, ha']
    · have hab' : a' ≠ b' := by
        rintro rfl
        exact hab (hdiag a b ha hb (h.trans (hG.homog a' b ha' hb)))
      rw [glue_in hab ha hb, glue_in hab' ha' hb', h]

/-- The tags restricted to `C` form a coherent coloring. -/
theorem glueC_coherent :
    WL.IsCoherentColoring (fun a b : {v : Ω // col v = c0} => glue col c0 d a b) :=
  WL.named_coherent_congr (fun a b x y =>
    (glue_kernel_on hG a.2 b.2 x.2 y.2).symm) hG.coh

/-- `c''` is a configuration (Def. 3.1.2). -/
theorem glue_isConfigColoring : WL.IsConfigColoring (glue col c0 d) := by
  refine ⟨fun x y z h => ?_, fun u v x y h => ?_⟩
  · rw [glue_self] at h
    by_contra hxy
    unfold glue at h
    simp only [hxy, if_false] at h
    split_ifs at h
  · obtain ⟨hcu, hcv, hiff⟩ := glue_col h
    by_cases huv : u = v
    · subst huv
      obtain rfl := hiff.1 rfl
      rw [glue_self, glue_self, hcu]
    · have hxy : x ≠ y := fun h' => huv (hiff.2 h')
      by_cases hC : col u = c0 ∧ col v = c0
      · have hC' : col x = c0 ∧ col y = c0 := ⟨hcu ▸ hC.1, hcv ▸ hC.2⟩
        rw [glue_in huv hC.1 hC.2, glue_in hxy hC'.1 hC'.2] at h
        simp only [Sum.inr.injEq, Sum.inl.injEq] at h
        have := hG.coh.1.2 ⟨u, hC.1⟩ ⟨v, hC.2⟩ ⟨x, hC'.1⟩ ⟨y, hC'.2⟩ h
        rw [glue_in (Ne.symm huv) hC.2 hC.1, glue_in (Ne.symm hxy) hC'.2 hC'.1]
        simpa using this
      · have hC' : ¬ (col x = c0 ∧ col y = c0) := by rw [← hcu, ← hcv]; exact hC
        rw [glue_pr (Ne.symm huv) (fun h' => hC ⟨h'.2, h'.1⟩),
          glue_pr (Ne.symm hxy) (fun h' => hC' ⟨h'.2, h'.1⟩), hcu, hcv]

omit hG in
/-- A permutation that preserves `c'` and fixes `C` pointwise preserves the tags. -/
theorem glue_perm (σ : Equiv.Perm Ω) (hcol : ∀ a, col (σ a) = col a)
    (hfix : ∀ a, col a = c0 → σ a = a) (a b : Ω) :
    glue col c0 d (σ a) (σ b) = glue col c0 d a b := by
  by_cases hab : a = b
  · subst hab; rw [glue_self, glue_self, hcol]
  · have hab' : σ a ≠ σ b := fun h => hab (σ.injective h)
    by_cases hC : col a = c0 ∧ col b = c0
    · rw [glue_in hab hC.1 hC.2, hfix a hC.1, hfix b hC.2, glue_in hab hC.1 hC.2]
    · rw [glue_pr hab hC, glue_pr hab' (by rw [hcol, hcol]; exact hC), hcol, hcol]

omit hG in
theorem count_perm (σ : Equiv.Perm Ω) (hcol : ∀ a, col (σ a) = col a)
    (hfix : ∀ a, col a = c0 → σ a = a) (Q : Ω → Prop) (hQ : ∀ z, Q (σ z) ↔ Q z)
    (x y : Ω) (i j : ℕ ⊕ ℕ ⊕ (ℕ × ℕ)) :
    {z | Q z ∧ glue col c0 d (σ x) z = i ∧ glue col c0 d z (σ y) = j}.ncard
      = {z | Q z ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j}.ncard := by
  have hset : {z | Q z ∧ glue col c0 d (σ x) z = i ∧ glue col c0 d z (σ y) = j}
      = σ '' {z | Q z ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j} := by
    ext w
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨σ.symm w, ⟨(hQ _).1 (by rwa [σ.apply_symm_apply]), ?_, ?_⟩, by simp⟩
      · rw [← glue_perm σ hcol hfix x (σ.symm w), σ.apply_symm_apply]; exact h2
      · rw [← glue_perm σ hcol hfix (σ.symm w) y, σ.apply_symm_apply]; exact h3
    · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨(hQ z).2 h1, by rw [glue_perm σ hcol hfix]; exact h2,
        by rw [glue_perm σ hcol hfix]; exact h3⟩
  rw [hset, Set.ncard_image_of_injective _ σ.injective]

omit hG in
theorem swap_col {a b : Ω} (hab : col a = col b) (z : Ω) :
    col (Equiv.swap a b z) = col z := by
  rcases eq_or_ne z a with rfl | hza
  · rw [Equiv.swap_apply_left, hab]
  rcases eq_or_ne z b with rfl | hzb
  · rw [Equiv.swap_apply_right, hab]
  rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

omit hG in
theorem swap_fix {a b : Ω} (ha : col a ≠ c0) (hb : col b ≠ c0) (z : Ω) (hz : col z = c0) :
    Equiv.swap a b z = z :=
  Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hz) (by rintro rfl; exact hb hz)

omit hG in
theorem ncard_subtype_eq (P : Ω → Prop) :
    {z : {v : Ω // col v = c0} | P z}.ncard = {z : Ω | col z = c0 ∧ P z}.ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
  · rintro ⟨hz, hP⟩; exact ⟨⟨z, hz⟩, hP, rfl⟩

omit hG in
theorem count_split (x y : Ω) (i j : ℕ ⊕ ℕ ⊕ (ℕ × ℕ)) :
    {z | glue col c0 d x z = i ∧ glue col c0 d z y = j}.ncard
      = {z | col z = c0 ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j}.ncard
        + {z | col z ≠ c0 ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j}.ncard := by
  rw [← Set.ncard_inter_add_ncard_diff_eq_ncard
    {z | glue col c0 d x z = i ∧ glue col c0 d z y = j} {z | col z = c0}]
  congr 2 <;> ext z <;> simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq] <;> tauto

/-- "It is easy to see that `X*` is coherent": the glued coloring `c''` is a coherent
coloring.  The proof checks WL-stability (Obs. 4.3.1) pair by pair: on `C × C` the counts
are those of the coherent coloring `d` (its intersection numbers, or its out- and
in-degrees, Obs. 3.3.5); outside `C` they are moved to each other by a permutation that
preserves `c'` and fixes `C` pointwise. -/
theorem glue_isCoherentColoring : WL.IsCoherentColoring (glue col c0 d) := by
  classical
  apply (WL.isStable_iff_isCoherentColoring (glue_isConfigColoring hG)).1
  intro x y x' y' hg
  refine (WL.step_eq_iff _ _ _ _ _).2 ⟨hg, fun i j => ?_⟩
  obtain ⟨hcx, hcy, hxy⟩ := glue_col hg
  have hstC := (WL.isStable_iff_isCoherentColoring (glueC_coherent hG).1).2 (glueC_coherent hG)
  by_cases hx : col x = c0 <;> by_cases hy : col y = c0
  · -- `x, y ∈ C`
    have hx' : col x' = c0 := hcx ▸ hx
    have hy' : col y' = c0 := hcy ▸ hy
    rw [count_split, count_split (x := x')]
    congr 1
    · rw [← ncard_subtype_eq (fun z => glue col c0 d x z = i ∧ glue col c0 d z y = j),
        ← ncard_subtype_eq (fun z => glue col c0 d x' z = i ∧ glue col c0 d z y' = j)]
      have hst := hstC ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩ hg
      exact ((WL.step_eq_iff _ _ _ _ _).1 hst).2 i j
    · congr 1
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hz, h1, h2⟩
        refine ⟨hz, ?_, ?_⟩
        · rw [(glue_mem_not hx' hz).1, hx', ← hx, ← (glue_mem_not hx hz).1]; exact h1
        · rw [(glue_mem_not hy' hz).2, hy', ← hy, ← (glue_mem_not hy hz).2]; exact h2
      · rintro ⟨hz, h1, h2⟩
        refine ⟨hz, ?_, ?_⟩
        · rw [(glue_mem_not hx hz).1, hx, ← hx', ← (glue_mem_not hx' hz).1]; exact h1
        · rw [(glue_mem_not hy hz).2, hy, ← hy', ← (glue_mem_not hy' hz).2]; exact h2
  · -- `x ∈ C`, `y ∉ C`
    have hx' : col x' = c0 := hcx ▸ hx
    have hy' : col y' ≠ c0 := hcy ▸ hy
    rw [count_split, count_split (x := x')]
    congr 1
    · rw [← ncard_subtype_eq (fun z => glue col c0 d x z = i ∧ glue col c0 d z y = j),
        ← ncard_subtype_eq (fun z => glue col c0 d x' z = i ∧ glue col c0 d z y' = j)]
      have hrw : ∀ (u w : Ω), col u = c0 → col w ≠ c0 →
          {z : {v : Ω // col v = c0} | glue col c0 d u z = i ∧ glue col c0 d z w = j}
            = if Sum.inr (Sum.inr (c0, col w)) = j then
                {z : {v : Ω // col v = c0} | glue col c0 d u z = i} else ∅ := by
        intro u w hu hw
        ext z
        simp only [Set.mem_setOf_eq, (glue_mem_not z.2 hw).1, z.2]
        split_ifs with hj <;> simp [hj]
      rw [hrw x y hx hy, hrw x' y' hx' hy', ← hcy]
      split_ifs
      · exact WL.outDeg_eq_of_diag_eq (glueC_coherent hG)
          (u := ⟨x, hx⟩) (u' := ⟨x', hx'⟩) (by simp [glue_self, hx, hx']) i
      · rfl
    · have h1 : {z | col z ≠ c0 ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j}
          = {z | col z ≠ c0 ∧ glue col c0 d x' z = i ∧ glue col c0 d z y = j} := by
        ext z
        simp only [Set.mem_setOf_eq]
        refine and_congr_right fun hz => ?_
        rw [(glue_mem_not hx hz).1, (glue_mem_not hx' hz).1, hcx]
      rw [h1]
      have hs := count_perm (d := d) (Equiv.swap y y') (swap_col hcy) (swap_fix hy hy')
        (fun z => col z ≠ c0) (fun z => by simp only [ne_eq, swap_col hcy]) x' y i j
      rwa [swap_fix hy hy' x' hx', Equiv.swap_apply_left, eq_comm] at hs
  · -- `x ∉ C`, `y ∈ C`
    have hx' : col x' ≠ c0 := hcx ▸ hx
    have hy' : col y' = c0 := hcy ▸ hy
    rw [count_split, count_split (x := x')]
    congr 1
    · rw [← ncard_subtype_eq (fun z => glue col c0 d x z = i ∧ glue col c0 d z y = j),
        ← ncard_subtype_eq (fun z => glue col c0 d x' z = i ∧ glue col c0 d z y' = j)]
      have hrw : ∀ (u w : Ω), col u ≠ c0 → col w = c0 →
          {z : {v : Ω // col v = c0} | glue col c0 d u z = i ∧ glue col c0 d z w = j}
            = if Sum.inr (Sum.inr (col u, c0)) = i then
                {z : {v : Ω // col v = c0} | glue col c0 d z w = j} else ∅ := by
        intro u w hu hw
        ext z
        simp only [Set.mem_setOf_eq, (glue_mem_not z.2 hu).2, z.2]
        split_ifs with hi <;> simp [hi]
      rw [hrw x y hx hy, hrw x' y' hx' hy', ← hcx]
      split_ifs
      · exact WL.inDeg_eq_of_diag_eq (glueC_coherent hG)
          (u := ⟨y, hy⟩) (u' := ⟨y', hy'⟩) (by simp [glue_self, hy, hy']) j
      · rfl
    · have h1 : {z | col z ≠ c0 ∧ glue col c0 d x z = i ∧ glue col c0 d z y = j}
          = {z | col z ≠ c0 ∧ glue col c0 d x z = i ∧ glue col c0 d z y' = j} := by
        ext z
        simp only [Set.mem_setOf_eq]
        refine and_congr_right fun hz => and_congr_right fun _ => ?_
        rw [(glue_mem_not hy hz).2, (glue_mem_not hy' hz).2, hcy]
      rw [h1]
      have hs := count_perm (d := d) (Equiv.swap x x') (swap_col hcx) (swap_fix hx hx')
        (fun z => col z ≠ c0) (fun z => by simp only [ne_eq, swap_col hcx]) x y' i j
      rwa [swap_fix hx hx' y' hy', Equiv.swap_apply_left, eq_comm] at hs
  · -- `x, y ∉ C`: a permutation moving `(x, y)` to `(x', y')`
    have hx' : col x' ≠ c0 := hcx ▸ hx
    have hy' : col y' ≠ c0 := hcy ▸ hy
    have key : ∃ σ : Equiv.Perm Ω, (∀ a, col (σ a) = col a) ∧
        (∀ a, col a = c0 → σ a = a) ∧ σ x = x' ∧ σ y = y' := by
      by_cases hxy0 : x = y
      · subst hxy0
        obtain rfl := hxy.1 rfl
        exact ⟨Equiv.swap x x', swap_col hcx, swap_fix hx hx', Equiv.swap_apply_left _ _,
          Equiv.swap_apply_left _ _⟩
      · have hxy0' : x' ≠ y' := fun h => hxy0 (hxy.2 h)
        set s := Equiv.swap x x' with hs
        have hsy : col (s y) = col y' := by rw [swap_col hcx, hcy]
        refine ⟨s.trans (Equiv.swap (s y) y'), fun a => ?_, fun a ha => ?_, ?_, ?_⟩
        · simp only [Equiv.trans_apply]; rw [swap_col hsy, swap_col hcx]
        · simp only [Equiv.trans_apply]
          rw [swap_fix hx hx' a ha, swap_fix (by rw [hsy]; exact hy') hy' a ha]
        · simp only [Equiv.trans_apply]
          rw [hs, Equiv.swap_apply_left]
          refine Equiv.swap_apply_of_ne_of_ne ?_ hxy0'
          intro h
          have : y = x := s.injective (by rw [hs, Equiv.swap_apply_left]; exact h.symm)
          exact hxy0 this.symm
        · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    obtain ⟨σ, hσc, hσf, hσx, hσy⟩ := key
    have hs := count_perm (d := d) σ hσc hσf (fun _ => True) (fun _ => Iff.rfl) x y i j
    simp only [true_and, hσx, hσy] at hs
    exact hs.symm

end Glue

/-! ### The two inputs of the glued configuration -/

section Inputs

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

open Classical in
/-- Case (b) of the "Proof of equivalence": the coloring `d` of the equivalence relation
`E` of the equipartition `part`: `d(x,x)` is one color, `d(x,y) = d₀` for `(x,y) ∈ E`,
`x ≠ y`, and `d(x,y) = d₁` otherwise.  (The paper's `d(x,x) = c'(x)` is one color on `C`.) -/
noncomputable def eqvNat (part : Set (Set Ω)) (a b : Ω) : ℕ :=
  if a = b then 0 else if ∃ B ∈ part, a ∈ B ∧ b ∈ B then 1 else 2

/-- "The structure `Y = (C, d)` is clearly a non-clique coherent configuration on `C`":
the coloring of an equipartition satisfies `GoodOn`. -/
theorem goodOn_eqvNat {col : Ω → ℕ} {c0 : ℕ} {part : Set (Set Ω)}
    (hP : IsEquipartitionOn part {v | col v = c0}) (hnt : IsNontrivialPartition part) :
    GoodOn col c0 (eqvNat part) := by
  classical
  -- the block of a point
  have hblk : ∀ a, col a = c0 → ∃ B ∈ part, a ∈ B := by
    intro a ha
    have : a ∈ ⋃₀ part := by rw [hP.covers]; exact ha
    simpa using this
  have huniq : ∀ a A B, A ∈ part → B ∈ part → a ∈ A → a ∈ B → A = B := by
    intro a A B hA hB haA haB
    by_contra hAB
    exact Set.disjoint_left.1 (hP.pairwiseDisjoint A hA B hB hAB) haA haB
  obtain ⟨⟨A0, hA0, B0, hB0, hAB0⟩, hntr⟩ := hnt
  set m := A0.ncard with hm
  let β := {v : Ω // col v = c0}
  let R : β → β → Prop := fun a b => ∃ B ∈ part, (a : Ω) ∈ B ∧ (b : Ω) ∈ B
  have hR : Equivalence R := by
    refine ⟨fun a => ?_, fun ⟨B, hB, h1, h2⟩ => ⟨B, hB, h2, h1⟩, ?_⟩
    · obtain ⟨B, hB, h⟩ := hblk a a.2; exact ⟨B, hB, h, h⟩
    · rintro a b c ⟨B1, hB1, h1, h2⟩ ⟨B2, hB2, h3, h4⟩
      obtain rfl := huniq b B1 B2 hB1 hB2 h2 h3
      exact ⟨B1, hB1, h1, h4⟩
  have hcls : ∀ x : β, ({y | R x y} : Set β).ncard = m := by
    intro x
    obtain ⟨B, hB, hxB⟩ := hblk x x.2
    have : ({y | R x y} : Set β) = Subtype.val ⁻¹' B := by
      ext y
      constructor
      · rintro ⟨B', hB', h1, h2⟩
        obtain rfl := huniq x B B' hB hB' hxB h1
        exact h2
      · intro hy; exact ⟨B, hB, hxB, hy⟩
    rw [this, hm, ← hP.equal_size B hB A0 hA0,
      ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hw; exact ⟨⟨w, hP.subset B hB hw⟩, hw, rfl⟩
  have h2m : 2 ≤ m := by
    have := Set.one_lt_ncard_iff_nontrivial.2 (hntr A0 hA0)
    omega
  have hlt : m < Fintype.card β := by
    have hcard : Fintype.card β = ({v | col v = c0} : Set Ω).ncard := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]; rfl
    have hun : (A0 ∪ B0).ncard = m + m := by
      rw [Set.ncard_union_eq (hP.pairwiseDisjoint A0 hA0 B0 hB0 hAB0) (Set.toFinite _)
        (Set.toFinite _), hm, hP.equal_size B0 hB0 A0 hA0]
    have hsub : A0 ∪ B0 ⊆ {v | col v = c0} :=
      Set.union_subset (hP.subset A0 hA0) (hP.subset B0 hB0)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hcoh := eqvConfig_isCoherent hR hcls h2m hlt
  have hcc : WL.IsCoherentColoring (eqvColor R) :=
    ⟨⟨hcoh.1.diag, hcoh.1.converse⟩, hcoh.2⟩
  have hval : ∀ a b : β, eqvNat part a b = (eqvColor R a b : ℕ) := by
    intro a b
    unfold eqvNat eqvColor
    by_cases hab : a = b
    · subst hab; simp
    · have hab' : (a : Ω) ≠ b := fun h => hab (Subtype.ext h)
      rw [if_neg hab', if_neg hab]
      by_cases hr : R a b
      · rw [if_pos hr, if_pos hr]; rfl
      · rw [if_neg hr, if_neg hr]; rfl
  refine ⟨WL.named_coherent_congr (fun a b x y => ?_) hcc, fun a b _ _ => by simp [eqvNat],
    ?_⟩
  · rw [hval, hval, Fin.val_inj]
  · obtain ⟨a, ha, b, hb, hab⟩ := hntr A0 hA0
    obtain ⟨b', hb'⟩ := hP.nonempty B0 hB0
    have hsA := hP.subset A0 hA0
    have hsB := hP.subset B0 hB0
    have hab' : a ≠ b' := by
      rintro rfl
      exact Set.disjoint_left.1 (hP.pairwiseDisjoint A0 hA0 B0 hB0 hAB0) ha hb'
    refine ⟨a, b, a, b', hsA ha, hsA hb, hsA ha, hsB hb', hab, hab', ?_⟩
    have h1 : eqvNat part a b = 1 := by
      simp only [eqvNat, if_neg hab]; rw [if_pos ⟨A0, hA0, ha, hb⟩]
    have h2 : eqvNat part a b' = 2 := by
      simp only [eqvNat, if_neg hab']
      rw [if_neg]
      rintro ⟨B, hB, h1, h2⟩
      obtain rfl := huniq a A0 B hA0 hB ha h1
      exact hAB0 (huniq b' _ _ hB hB0 h2 hb')
    rw [h1, h2]; decide

/-- Case (c) of the "Proof of equivalence": a UPCC `(C, d)` satisfies `GoodOn` (it is
coherent, homogeneous, and of rank `≥ 3`). -/
theorem goodOn_of_upcc {col : Ω → ℕ} {c0 : ℕ} {cfg : Ω → Ω → ℕ}
    (hcoh : (cfgOn cfg {v | col v = c0}).IsCoherent)
    (hup : (cfgOn cfg {v | col v = c0}).IsUniprimitive) : GoodOn col c0 cfg := by
  classical
  have hk := cfgOn_color_eq_iff cfg {v | col v = c0}
  have hcc : WL.IsCoherentColoring (cfgOn cfg {v | col v = c0}).color :=
    ⟨⟨hcoh.1.diag, hcoh.1.converse⟩, hcoh.2⟩
  have hhom : ∀ a b, col a = c0 → col b = c0 → cfg a a = cfg b b := fun a b ha hb =>
    (hk ⟨a, ha⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨b, hb⟩).1 (hup.1.1 ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨WL.named_coherent_congr hk hcc, hhom, ?_⟩
  -- three different colors, at most one of them diagonal
  have h3 := hup.2
  simp only [cfgOn, PartitionStructure.ofColoring] at h3
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := Finset.two_lt_card_iff.1 h3
  obtain ⟨⟨p1, p2⟩, -, hp⟩ := Finset.mem_image.1 hu
  obtain ⟨⟨q1, q2⟩, -, hq⟩ := Finset.mem_image.1 hv
  obtain ⟨⟨r1, r2⟩, -, hr⟩ := Finset.mem_image.1 hw
  subst hp hq hr
  have hoff : ∀ (a b a' b' : {v // col v = c0}), a = b → cfg a' b' ≠ cfg a b → a' ≠ b' := by
    rintro a b a' b' rfl hne rfl
    exact hne (hhom _ _ a'.2 a.2)
  have mk : ∀ (a b a' b' : {v // col v = c0}), a ≠ b → a' ≠ b' → cfg a b ≠ cfg a' b' →
      ∃ a b a' b', col a = c0 ∧ col b = c0 ∧ col a' = c0 ∧ col b' = c0 ∧ a ≠ b ∧
        a' ≠ b' ∧ cfg a b ≠ cfg a' b' := fun a b a' b' h1 h2 h3 =>
    ⟨a, b, a', b', a.2, b.2, a'.2, b'.2, fun h => h1 (Subtype.ext h),
      fun h => h2 (Subtype.ext h), h3⟩
  by_cases hp : p1 = p2
  · exact mk q1 q2 r1 r2 (hoff p1 p2 q1 q2 hp (Ne.symm huv))
      (hoff p1 p2 r1 r2 hp (Ne.symm huw)) hvw
  · by_cases hq : q1 = q2
    · exact mk p1 p2 r1 r2 hp (hoff q1 q2 r1 r2 hq (Ne.symm hvw)) huw
    · exact mk p1 p2 q1 q2 hp hq huv

omit [Fintype Ω] [DecidableEq Ω] in
/-- `GoodOn` is transported by a bijection. -/
theorem goodOn_map {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] (f : Ω ≃ Ω')
    {col : Ω → ℕ} {col' : Ω' → ℕ} {c0 : ℕ} {d : Ω → Ω → ℕ} {d' : Ω' → Ω' → ℕ}
    (hcol : ∀ u, col' (f u) = col u) (hd : ∀ u v, d' (f u) (f v) = d u v)
    (h : GoodOn col c0 d) : GoodOn col' c0 d' := by
  have hcol' : ∀ w, col (f.symm w) = col' w := fun w => by rw [← hcol, f.apply_symm_apply]
  have hd' : ∀ w w', d (f.symm w) (f.symm w') = d' w w' := fun w w' => by
    rw [← hd, f.apply_symm_apply, f.apply_symm_apply]
  let e : {v : Ω' // col' v = c0} ≃ {v : Ω // col v = c0} :=
    f.symm.subtypeEquiv (fun w => by rw [hcol'])
  refine ⟨?_, fun a b ha hb => ?_, ?_⟩
  · have := WL.isCoherentColoring_comp_equiv e h.coh
    convert this using 2 with a b
    simp only [e, Equiv.subtypeEquiv_apply, hd']
  · rw [← hd', ← hd', h.homog _ _ (by rw [hcol']; exact ha) (by rw [hcol']; exact hb)]
  · obtain ⟨a, b, a', b', ha, hb, ha', hb', hab, hab', hne⟩ := h.wit
    refine ⟨f a, f b, f a', f b', by rwa [hcol], by rwa [hcol], by rwa [hcol], by rwa [hcol],
      fun h => hab (f.injective h), fun h => hab' (f.injective h), by rwa [hd, hd]⟩

theorem eqvNat_map {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] (f : Ω ≃ Ω')
    {part : Set (Set Ω)} {part' : Set (Set Ω')} (hp : part' = (fun B => f '' B) '' part)
    (a b : Ω) : eqvNat part' (f a) (f b) = eqvNat part a b := by
  classical
  have hiff : (∃ B ∈ part', f a ∈ B ∧ f b ∈ B) ↔ ∃ B ∈ part, a ∈ B ∧ b ∈ B := by
    subst hp
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, h1, h2⟩
      rw [f.injective.mem_set_image] at h1 h2
      exact ⟨B, hB, h1, h2⟩
    · rintro ⟨B, hB, h1, h2⟩
      exact ⟨_, ⟨B, hB, rfl⟩, Set.mem_image_of_mem f h1, Set.mem_image_of_mem f h2⟩
  unfold eqvNat
  simp only [f.injective.eq_iff]
  split_ifs with h1 h2 h3 h3 <;> first | rfl | exact absurd (hiff.1 h2) h3 |
    exact absurd (hiff.2 h3) h2

omit [Fintype Ω] in
theorem glue_map {Ω' : Type} [Fintype Ω'] [DecidableEq Ω'] (f : Ω ≃ Ω')
    {col : Ω → ℕ} {col' : Ω' → ℕ} {c0 : ℕ} {d : Ω → Ω → ℕ} {d' : Ω' → Ω' → ℕ}
    (hcol : ∀ u, col' (f u) = col u) (hd : ∀ u v, d' (f u) (f v) = d u v) (u v : Ω) :
    glue col' c0 d' (f u) (f v) = glue col c0 d u v := by
  simp only [glue, f.injective.eq_iff, hcol, hd]

end Inputs

/-! ### Theorem 8.1.2 ⇒ Theorem 8.1.5 -/

open Classical in
/-- The choice of `Y = (C, d)`: the given configuration of case (c) if it satisfies
`GoodOn`, otherwise the configuration of the equipartition of case (b). -/
noncomputable def chooseD {Ω : Type} [Fintype Ω] [DecidableEq Ω] (col : Ω → ℕ) (c0 : ℕ)
    (cfg : Ω → Ω → ℕ) (part : Set (Set Ω)) : Ω → Ω → ℕ :=
  if GoodOn col c0 cfg then cfg else eqvNat part

open Classical in
/-- The assignment built in the "Proof of equivalence" from an assignment for
Theorem 8.1.2: keep the coloring `c'`; if it has a dominant color `c₀` (the least one, which
is unique for `α ≥ 1/2`), return `X* = (Ω, c'')` with `c'' = glue c' c₀ d`, encoded in `ℕ`. -/
noncomputable def gluedAssign (α : ℝ) (A : Assignment C) : Assignment C :=
  fun Ω _ _ k X l x =>
    if h : ∃ c : ℕ, IsDominant α {v | (A Ω k X l x).col v = c} then
      ⟨(A Ω k X l x).col, ∅, fun u v => Encodable.encode (glue (A Ω k X l x).col (Nat.find h)
        (chooseD (A Ω k X l x).col (Nat.find h) (A Ω k X l x).cfg (A Ω k X l x).part) u v)⟩
    else A Ω k X l x

theorem gluedAssign_canonical {α : ℝ} {A : Assignment C} (hA : IsCanonical A) :
    IsCanonical (gluedAssign α A) := by
  classical
  intro Ω Ω' _ _ _ _ k X Y f hf l x
  have hD := hA Ω Ω' k X Y f hf l x
  simp only [gluedAssign]
  set D := A Ω k X l x
  set D' := A Ω' k Y l (tupleMap f x)
  have hdom : ∀ c, IsDominant α {w | D'.col w = c} ↔ IsDominant α {w | D.col w = c} :=
    fun c => by rw [colorClass_corr f hD.col c, isDominant_image_iff]
  by_cases hd : ∃ c : ℕ, IsDominant α {v | D.col v = c}
  · have hd' : ∃ c : ℕ, IsDominant α {v | D'.col v = c} :=
      let ⟨c, hc⟩ := hd; ⟨c, (hdom c).2 hc⟩
    rw [dif_pos hd, dif_pos hd']
    have hfind : Nat.find hd' = Nat.find hd :=
      le_antisymm (Nat.find_min' _ ((hdom _).2 (Nat.find_spec hd)))
        (Nat.find_min' _ ((hdom _).1 (Nat.find_spec hd')))
    refine ⟨hD.col, by simp, fun u v => ?_⟩
    simp only
    rw [hfind]
    congr 1
    refine glue_map f hD.col (fun a b => ?_) u v
    unfold chooseD
    have hG : GoodOn D'.col (Nat.find hd) D'.cfg ↔ GoodOn D.col (Nat.find hd) D.cfg := by
      refine ⟨fun h => goodOn_map f.symm (fun w => ?_) (fun w w' => ?_) h,
        goodOn_map f hD.col hD.cfg⟩
      · rw [← hD.col, f.apply_symm_apply]
      · rw [← hD.cfg, f.apply_symm_apply, f.apply_symm_apply]
    by_cases hg : GoodOn D.col (Nat.find hd) D.cfg
    · rw [if_pos hg, if_pos (hG.2 hg), hD.cfg]
    · rw [if_neg hg, if_neg (fun h => hg (hG.1 h)), eqvNat_map f hD.part]
  · have hd' : ¬ ∃ c : ℕ, IsDominant α {v | D'.col v = c} :=
      fun ⟨c, hc⟩ => hd ⟨c, (hdom c).1 hc⟩
    rw [dif_neg hd, dif_neg hd']
    exact hD

/-- Two off-diagonal pairs of `Δ` with different colors witness that `Y` does not induce a
clique configuration on `Δ` (`color_eq_of_rank_two`). -/
theorem not_isCliqueOn_of_two {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (Y : PartitionStructure Ω) (hY : Y.IsConfiguration)
    {Δ : Set Ω} {a b a' b' : Ω} (ha : a ∈ Δ) (hb : b ∈ Δ) (ha' : a' ∈ Δ) (hb' : b' ∈ Δ)
    (hab : a ≠ b) (hab' : a' ≠ b') (hne : Y.color a b ≠ Y.color a' b') :
    ¬ Y.IsCliqueOn Δ := by
  classical
  intro hclique
  have hind := PartitionStructure.color_eq_of_rank_two (Y.induced Δ)
    (Y.induced_isConfiguration Δ hY) hclique
    (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) (u := ⟨a', ha'⟩) (v := ⟨b', hb'⟩)
    (fun hc => hab (congrArg Subtype.val hc)) (fun hc => hab' (congrArg Subtype.val hc))
  rw [Y.induced_color_eq_iff] at hind
  exact hne hind

/-- Theorem 8.1.2 ⇒ Theorem 8.1.5, the objects: if `A` reaches an outcome of Theorem 8.1.2
on every admissible input, then the glued data `gluedAssign α A` (the coloring `c'` and
the configuration `X* = (Ω, c'')`) reach an outcome of Theorem 8.1.5 at the same string.
The proof is the paper's (see `theorem_8_1_2_imp_8_1_5`). -/
theorem gluedAssign_reaches {α : ℝ} (hα : 1 / 2 ≤ α) {A : Assignment C}
    (hA : Reaches812 α A) : Reaches815 α (gluedAssign α A) := by
  classical
  intro Ω _ _ k X hX
  obtain ⟨l, hl, x, hx, hout⟩ := hA Ω k X hX
  refine ⟨l, hl, x, hx, ?_⟩
  simp only [gluedAssign]
  set D := A Ω k X l x
  by_cases hd : ∃ c : ℕ, IsDominant α {v | D.col v = c}
  · rw [dif_pos hd]
    set c0 := Nat.find hd
    have hc0 : IsDominant α {v | D.col v = c0} := Nat.find_spec hd
    set d := chooseD D.col c0 D.cfg D.part
    have hgood : GoodOn D.col c0 d := by
      simp only [d, chooseD]
      split_ifs with hg
      · exact hg
      rcases hout with ha | ⟨S, ⟨⟨c, rfl⟩, hS⟩, hb⟩ | ⟨S, ⟨⟨c, rfl⟩, hS⟩, hc⟩
      · exact absurd hc0 (ha c0)
      · obtain rfl : c = c0 := IsDominant.subsingleton hα D.col hS hc0
        exact goodOn_eqvNat hb.1 hb.2
      · obtain rfl : c = c0 := IsDominant.subsingleton hα D.col hS hc0
        exact absurd (goodOn_of_upcc hc.1 hc.2) hg
    have hcoh : WL.IsCoherentColoring
        (fun u v => Encodable.encode (glue D.col c0 d u v)) :=
      WL.named_coherent_congr (fun a b x y => Encodable.encode_inj.symm)
        (glue_isCoherentColoring hgood)
    have hker : ∀ a b x y : Ω,
        (PartitionStructure.ofColoring
          (fun u v => Encodable.encode (glue D.col c0 d u v))).color a b
          = (PartitionStructure.ofColoring
              (fun u v => Encodable.encode (glue D.col c0 d u v))).color x y ↔
          Encodable.encode (glue D.col c0 d a b) = Encodable.encode (glue D.col c0 d x y) :=
      fun a b x y => PartitionStructure.ofColoring_color_eq_iff _ a b x y
    have hY := PartitionStructure.named_isCoherent_of_kernel _ hcoh
      (fun a b x y => (hker a b x y).symm)
    refine Or.inr ⟨hY, {v | D.col v = c0}, ⟨⟨Encodable.encode (Sum.inl c0 :
      ℕ ⊕ ℕ ⊕ (ℕ × ℕ)), ?_⟩, hc0⟩, ?_⟩
    · ext v
      simp only [Set.mem_setOf_eq, glue_self, Encodable.encode_inj, Sum.inl.injEq]
    · obtain ⟨a, b, a', b', ha, hb, ha', hb', hab, hab', hne⟩ := hgood.wit
      refine not_isCliqueOn_of_two _ hY.toIsConfiguration ha hb ha' hb' hab hab' ?_
      rw [Ne, hker, Encodable.encode_inj, glue_in hab ha hb, glue_in hab' ha' hb']
      simpa using hne
  · rw [dif_neg hd]
    refine Or.inl fun c hc => hd ⟨c, hc⟩

/-- **Theorem 8.1.2 ⇒ Theorem 8.1.5**, the first half of the "Proof of equivalence", §8.1.

> Outcome (a) is identical with outcome (i).  In case (b), let `c'` denote the given
> canonical coloring of `Ω`, `C` the dominant `c'`-class, and `E` the equivalence relation
> on `C` corresponding to the given equipartition. […] The structure `Y = (C,d)` is clearly
> a non-clique coherent configuration on `C`.  In case (c), let `C` be the dominant color
> class and `Y = (C,d)` be the given UPCC.  Let us now define the coherent configuration
> `X' = (Ω, c'')` required by (ii). […] It is easy to see that `X*` is coherent; `C` is its
> dominant color class; and `X*[C] = Y` is not a clique.

Proved with the repaired `c''` (`Babai.DesignAbstract.glue`, diagonal separated; see its
docstring and the corrected paper, "Proof of equivalence 8.1.2 ⇒ 8.1.5").  The paper's
`X*[C] = Y` holds up to the names of the colors: `X*[C]` has the classes of `Y`. -/
theorem theorem_8_1_2_imp_8_1_5 {α : ℝ} (hα : 1 / 2 ≤ α) (h : DL812 C α) : DL815 C α := by
  obtain ⟨A, hAc, hA⟩ := h
  exact ⟨gluedAssign α A, gluedAssign_canonical hAc, gluedAssign_reaches hα hA⟩


end DesignAbstract

end Babai
