/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1: the concrete Design Lemma (the `k`-WL objects of §8.2) as an instance of the
abstract statement `DL(α)`; Observation 8.1.3 and Theorem 8.1.5 for those objects.
-/
import Workspace.DesignLemma.Abstract
import Workspace.DesignLemma.NatRank

/-!
# §8.1 The `k`-WL objects satisfy `DL(α)`

`Workspace/DesignLemma/Abstract.lean` states the Design Lemma as `DL(α)`: *some* canonical
assignment of a coloring, an equipartition and a configuration to every pair (structure,
string) reaches outcome (a), (b) or (c).  This file shows that the objects of
Procedure "Design Lemma" (§8.2), for which `Babai.KAryRelStruct.theorem_8_1_2` is proved,
form such an assignment, `Babai.DesignAbstract.kwlAssign`:

* the coloring is the vertex coloring of `X_x⃗ = kWL(X)` restricted at `x⃗`;
* the blocks are the design partition of `X_x⃗` (outcome (b));
* the edge coloring is `X* = (X_x⃗)^{(2)}` (outcome (c) on the dominant class).

The abstract statement names colors by natural numbers (§6: a canonical object keeps its
names under isomorphisms).  The colors of `kWL(X)` live in a type that depends on `|Ω|`, so
they are named by their rank in a fixed well-order of the occurring colors
(`Babai.natRank`); the names are a bijective relabelling of the colors, so no information is
lost (`natRank_eq_iff`).

## Results

* `kwlAssign_canonical`: the assignment is canonical (§6), across vertex sets;
* `kwlAssign_reaches`: Theorem 8.1.2 for the `k`-WL objects is an instance of `DL(α)`;
* `theorem_8_1_2_DL`: `DL(α)` holds for `1/2 ≤ α < 1`;
* `observation_8_1_3_kWL`: Observation 8.1.3, with the objects built from the `k`-WL
  objects by the paper's proof;
* `theorem_8_1_5_kWL`: Theorem 8.1.5 as printed, with the coloring `c'` and the
  configuration `X* = (Ω, c'')` built from the `k`-WL objects by the paper's
  "Proof of equivalence".
-/

set_option linter.unusedSectionVars false

open scoped Classical

namespace Babai

namespace DesignAbstract

open KAryRelStruct

/-! ### The data of a partition structure -/

section Generic

variable {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {K : Type} {m : ℕ}

/-- The Design Lemma data of a `m`-ary partition structure `Y` (in the application,
`Y = X_x⃗`): its vertex coloring, the design partition of its dominant class, and the edge
coloring of `Y^{(2)}`, with colors named by natural numbers (`natRank`). -/
noncomputable def pdata (α : ℝ) (Y : KAryPartStruct V K m) : DLData V where
  col v := natRank (Set.range Y.vcolor) (Y.vcolor v)
  part := if hm : 2 ≤ m then KAryPartStruct.designPartition α Y hm else ∅
  cfg u v := if hm : 2 ≤ m then
      natRank (Set.range fun p : V × V => Y.pairColor hm p.1 p.2) (Y.pairColor hm u v)
    else 0

theorem pdata_col_eq_iff (α : ℝ) (Y : KAryPartStruct V K m) (u v : V) :
    (pdata α Y).col u = (pdata α Y).col v ↔ Y.vcolor u = Y.vcolor v :=
  natRank_eq_iff (Set.finite_range _) ⟨u, rfl⟩ ⟨v, rfl⟩

theorem pdata_cfg_eq_iff (α : ℝ) (Y : KAryPartStruct V K m) (hm : 2 ≤ m) (a b c d : V) :
    (pdata α Y).cfg a b = (pdata α Y).cfg c d ↔ Y.pairColor hm a b = Y.pairColor hm c d := by
  simp only [pdata, dif_pos hm]
  exact natRank_eq_iff (Set.finite_range _) ⟨(a, b), rfl⟩ ⟨(c, d), rfl⟩

theorem pdata_part (α : ℝ) (Y : KAryPartStruct V K m) (hm : 2 ≤ m) :
    (pdata α Y).part = KAryPartStruct.designPartition α Y hm := by
  simp only [pdata, dif_pos hm]

/-- §6: an isomorphism `f : Y → Y'` carries the data of `Y` to the data of `Y'`. -/
theorem pdata_iso (α : ℝ) {Y : KAryPartStruct V K m} {Y' : KAryPartStruct V' K m}
    {f : V ≃ V'} (hf : f ∈ KAryPartStruct.Iso Y Y') :
    DLData.Corr f (pdata α Y) (pdata α Y') := by
  have hv := KAryPartStruct.vcolor_canonical Y Y' hf
  refine ⟨fun u => ?_, ?_, fun u v => ?_⟩
  · have hr : Set.range Y'.vcolor = Set.range Y.vcolor := by
      ext c
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨f.symm v, by rw [← hv, f.apply_symm_apply]⟩
      · rintro ⟨v, rfl⟩; exact ⟨f v, hv v⟩
    simp only [pdata]
    rw [hr, hv]
  · by_cases hm : 2 ≤ m
    · rw [pdata_part α Y hm, pdata_part α Y' hm]
      exact KAryPartStruct.designPartition_canonical hf
    · simp only [pdata, dif_neg hm, Set.image_empty]
  · by_cases hm : 2 ≤ m
    · have hp := fun a b => KAryPartStruct.pairColor_canonical (hm := hm) hf a b
      have hr : (Set.range fun p : V' × V' => Y'.pairColor hm p.1 p.2)
          = Set.range fun p : V × V => Y.pairColor hm p.1 p.2 := by
        ext c
        constructor
        · rintro ⟨⟨a, b⟩, rfl⟩
          exact ⟨(f.symm a, f.symm b), by
            simp only [← hp, Equiv.apply_symm_apply]⟩
        · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨(f a, f b), hp a b⟩
      simp only [pdata, dif_pos hm]
      rw [hr, hp]
    · simp only [pdata, dif_neg hm]

/-- The data depend only on the colors: transporting the color type changes nothing. -/
theorem pdata_cast (α : ℝ) {K₁ K₂ : Type} (hC : K₁ = K₂) {Y₁ : KAryPartStruct V K₁ m}
    {Y₂ : KAryPartStruct V K₂ m} (hcol : ∀ x, Y₂.color x = cast hC (Y₁.color x)) :
    pdata α Y₂ = pdata α Y₁ := by
  subst hC
  rw [KAryPartStruct.eq_of_color_cast hcol]

/-- Outcome (a): no dominant vertex color of `Y` is no dominant color of the named
coloring. -/
theorem pdata_noDom {α : ℝ} (hα : 0 ≤ α) {Y : KAryPartStruct V K m}
    (h : KAryPartStruct.NoDominantColor α Y) : NoDom α (pdata α Y).col := by
  intro c hc
  rcases Set.eq_empty_or_nonempty {v | (pdata α Y).col v = c} with he | ⟨v₀, hv₀⟩
  · rw [he] at hc
    unfold IsDominant at hc
    simp only [Set.ncard_empty, Nat.cast_zero] at hc
    have : 0 ≤ α * (Fintype.card V : ℝ) := mul_nonneg hα (Nat.cast_nonneg _)
    linarith
  · have hS : {v | (pdata α Y).col v = c} = Y.vclass (Y.vcolor v₀) := by
      ext v
      simp only [Set.mem_setOf_eq, KAryPartStruct.vclass]
      rw [← pdata_col_eq_iff α Y v v₀, hv₀.out]
    rw [hS] at hc
    unfold IsDominant at hc
    linarith [h (Y.vcolor v₀)]

/-- Outcomes (b) and (c): the dominant class of `Y` is the dominant class of the named
coloring. -/
theorem pdata_domClass {α : ℝ} (hα : 1 / 2 ≤ α) {Y : KAryPartStruct V K m}
    (h : KAryPartStruct.HasDominantClass α Y) :
    DomClass α (pdata α Y).col (KAryPartStruct.dominantClass α Y) := by
  obtain ⟨i, hi⟩ := h
  rw [KAryPartStruct.dominantClass_eq hα Y hi]
  refine ⟨?_, hi⟩
  have hpos : 0 < (Y.vclass i).ncard := by
    have : 0 ≤ α * (Fintype.card V : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have h' : (0 : ℝ) < ((Y.vclass i).ncard : ℝ) := lt_of_le_of_lt this hi
    exact_mod_cast h'
  obtain ⟨v₀, hv₀⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
  refine ⟨(pdata α Y).col v₀, ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, KAryPartStruct.vclass]
  rw [pdata_col_eq_iff]
  exact ⟨fun hv => hv.trans hv₀.symm, fun hv => hv.trans hv₀⟩

/-- Outcome (c): on a set `S`, the named edge coloring and `Y^{(2)}[S]` have the same
color classes. -/
theorem cfgOn_pdata_kernel (α : ℝ) (Y : KAryPartStruct V K m) (hm : 2 ≤ m) (S : Set V)
    [Fintype S] (a b c d : S) :
    ((Y.skel2 hm).induced S).color a b = ((Y.skel2 hm).induced S).color c d ↔
      (cfgOn (pdata α Y).cfg S).color a b = (cfgOn (pdata α Y).cfg S).color c d := by
  rw [PartitionStructure.induced_color_eq_iff, cfgOn_color_eq_iff,
    KAryPartStruct.skel2_color_eq_iff', pdata_cfg_eq_iff α Y hm]

/-- Outcome (c): if `Y` is coherent and has a dominant class `C`, then `Y^{(2)}[C]` is a
coherent configuration (the dominant class is a vertex-color class of `Y^{(2)}`, so it is
stable). -/
theorem skel2_induced_dominantClass_isCoherent {α : ℝ} (hα : 1 / 2 ≤ α)
    {Y : KAryPartStruct V K m} (hY : Y.IsCoherent) (hm : 2 ≤ m)
    (h : KAryPartStruct.HasDominantClass α Y) [Fintype (KAryPartStruct.dominantClass α Y)] :
    ((Y.skel2 hm).induced (KAryPartStruct.dominantClass α Y)).IsCoherent := by
  obtain ⟨i, hi⟩ := h
  have hCi := KAryPartStruct.dominantClass_eq hα Y hi
  have hstable : (Y.skel2 hm).IsStable (KAryPartStruct.dominantClass α Y) := by
    rcases Set.eq_empty_or_nonempty (KAryPartStruct.dominantClass α Y) with he | ⟨u₀, hu₀⟩
    · rw [he]; exact ⟨∅, by ext; simp⟩
    · have hu₀' : Y.vcolor u₀ = i := by rw [hCi] at hu₀; exact hu₀
      have hC : KAryPartStruct.dominantClass α Y
          = (Y.skel2 hm).vertexClass ((Y.skel2 hm).vcolor u₀) := by
        rw [KAryPartStruct.skel2_vertexClass_eq, hCi, hu₀']
      rw [hC]; exact PartitionStructure.isStable_vertexClass _ _
  exact PartitionStructure.induced_isCoherent _ (KAryPartStruct.skel2_isCoherent Y hY hm)
    hstable

end Generic

/-! ### The assignment -/

variable {C : Type}

/-- The objects of Procedure "Design Lemma" (§8.2) as an assignment: at the string `x⃗` of
length `ℓ ≤ k`, the data of `X_x⃗ = kWL(X)` restricted at `x⃗`.  (Strings longer than `k`
are never used; they get constant data.) -/
noncomputable def kwlAssign (α : ℝ) : Assignment C :=
  fun _ _ _ k X l x =>
    if hl : l ≤ k then pdata α (X.kWL.restrTo hl x) else ⟨fun _ => 0, ∅, fun _ _ => 0⟩

/-- §6, canonicity relative to `x⃗`, across vertex sets: an isomorphism `f : X → Y` carries
the objects of `(X, x⃗)` to those of `(Y, x⃗^f)`. -/
theorem kwlAssign_canonical (α : ℝ) : IsCanonical (kwlAssign (C := C) α) := by
  intro Ω Ω' _ _ _ _ k X Y f hf l x
  by_cases hl : l ≤ k
  · simp only [kwlAssign, dif_pos hl]
    have hN := KAryPartStruct.card_str_prod_eq (Ω := Ω) (Ω' := Ω') (k := k) f
    rw [pdata_cast α _ (fun y => kWL_restrTo_color_cast (Ω := Ω) Y hN hl (tupleMap f x) y)]
    exact pdata_iso α (kWL_iso_restrTo X Y hf hl x)
  · simp only [kwlAssign, dif_neg hl]
    exact ⟨fun _ => rfl, by simp, fun _ _ => rfl⟩

/-- **Theorem 8.1.2** for the `k`-WL objects is an instance of `DL(α)`: on every admissible
`X` the assignment `kwlAssign α` reaches outcome (a), (b) or (c) at a string of `ℓ ≤ k − 1`
distinct vertices.  The proof reads the three outcomes of
`Babai.KAryRelStruct.theorem_8_1_2` through the naming of the colors. -/
theorem kwlAssign_reaches {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    Reaches812 α (kwlAssign (C := C) α) := by
  intro Ω _ _ k X hX
  obtain ⟨hk2, hkn, hdef⟩ := hX
  obtain ⟨l, hl, x, hx, hout⟩ := theorem_8_1_2 hα hα1 X hk2 hkn hdef
  refine ⟨l, hl, x, hx, ?_⟩
  have hlk : l ≤ k := by omega
  simp only [kwlAssign, dif_pos hlk]
  rcases hout with ha | ⟨h2, hdom, hP, hPnt⟩ | ⟨h2, hdom, huni⟩
  · exact Or.inl (pdata_noDom (by linarith) ha)
  · refine Or.inr (Or.inl ⟨_, pdata_domClass hα hdom, ?_, ?_⟩)
    · rw [pdata_part α _ (by omega)]; exact hP
    · rw [pdata_part α _ (by omega)]; exact hPnt
  · refine Or.inr (Or.inr ⟨_, pdata_domClass hα hdom, ?_, ?_⟩)
    · have hY := X.kWL.restrTo_isCoherent X.kWL_isCoherent hlk x
      exact PartitionStructure.isCoherent_congr
        (fun a b c d => cfgOn_pdata_kernel α _ (by omega) _ a b c d)
        (skel2_induced_dominantClass_isCoherent hα hY (by omega) hdom)
    · exact PartitionStructure.isUniprimitive_congr
        (fun a b c d => cfgOn_pdata_kernel α _ (by omega) _ a b c d) huni

/-- **Theorem 8.1.2** (Design lemma), §8.1, as the statement `DL(α)`, without the running
time: the `k`-WL objects are a canonical assignment reaching outcome (a), (b) or (c) on
every admissible structure. -/
theorem theorem_8_1_2_DL {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) : DL812 C α :=
  ⟨kwlAssign α, kwlAssign_canonical α, kwlAssign_reaches hα hα1⟩

/-- **Observation 8.1.3**, §8.1, for the objects of the paper.

> If `1 > α' ≥ α ≥ 1/2` then `DL(α')` follows from `DL(α)`.

`DL(α)` is supplied by the `k`-WL objects (`theorem_8_1_2_DL`); the objects of `DL(α')` are
the ones the paper's proof builds from them (`obsAssign α α' (kwlAssign α)`: the two-class
colorings `(U, Ω ∖ U)` and `(C, Ω ∖ C)`, or else the `k`-WL objects unchanged).  They are
canonical and reach an outcome of Theorem 8.1.2 for `α'` on every structure with
`2 ≤ k ≤ n/2` and symmetry defect `≥ 1 − α'`. -/
theorem observation_8_1_3_kWL {α α' : ℝ} (hα : 1 / 2 ≤ α) (hαα' : α ≤ α') (hα'1 : α' < 1) :
    IsCanonical (obsAssign α α' (kwlAssign (C := C) α)) ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
        2 ≤ k → 2 * k ≤ Fintype.card Ω → (1 : ℝ) - α' ≤ (defect X.Aut : ℝ) →
          ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧
            Outcome812 α' (obsAssign α α' (kwlAssign α) Ω k X l x) :=
  ⟨obsAssign_canonical (kwlAssign_canonical α),
    fun Ω _ _ k X hk2 hkn hdef =>
      obsAssign_reaches hα hαα' (kwlAssign_reaches hα (by linarith)) Ω k X ⟨hk2, hkn, hdef⟩⟩

/-- **Theorem 8.1.5** (Design lemma, rephrased), §8.1, for the objects of the paper.

*"Let `1/2 ≤ α < 1` be a threshold parameter.  Let `X = (Ω, R)` be a `k`-ary relational
structure with `n = |Ω|` vertices, `2 ≤ k ≤ n/2`, and symmetry defect `≥ 1 − α`.  Then in
time `n^{O(k)}` we can find a value `ℓ ≤ k − 1` and a string `x⃗ = x₁ … x_ℓ ∈ Ω^⟨ℓ⟩` of `ℓ`
distinct vertices such that by individualizing each `x_j` we obtain either*

*(i) a canonical coloring of `Ω` with no dominant color, or*

*(ii) a canonical (classical) coherent configuration `X*` on vertex set `Ω` such that the
subconfiguration induced on the dominant vertex-color class of `X*` is not a clique.*

*Canonicity in the above statements is relative to `x⃗`."*

The objects are the ones of the paper's "Proof of equivalence" (8.1.2 ⇒ 8.1.5) built from
the `k`-WL objects of Theorem 8.1.2: the coloring `c'` of `X_x⃗`, and `X* = (Ω, c'')`
(`gluedAssign α (kwlAssign α)`, with the repaired `c''` of the corrected paper, "Proof of
equivalence 8.1.2 ⇒ 8.1.5").  Canonicity is the first conjunct; outcomes (i) and (ii) are
`Outcome815`.  The running-time clause is pending.

The direct form with `X* = (X_x⃗)^{(2)}` is `Babai.KAryRelStruct.theorem_8_1_5`. -/
theorem theorem_8_1_5_kWL {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) :
    IsCanonical (gluedAssign α (kwlAssign (C := C) α)) ∧
      ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (k : ℕ) (X : KAryRelStruct Ω C k),
        2 ≤ k → 2 * k ≤ Fintype.card Ω → (1 : ℝ) - α ≤ (defect X.Aut : ℝ) →
          ∃ l ≤ k - 1, ∃ x : Str Ω l, Str.Distinct x ∧
            Outcome815 α (gluedAssign α (kwlAssign α) Ω k X l x) :=
  ⟨gluedAssign_canonical (kwlAssign_canonical α),
    fun Ω _ _ k X hk2 hkn hdef =>
      gluedAssign_reaches hα (kwlAssign_reaches hα hα1) Ω k X ⟨hk2, hkn, hdef⟩⟩

/-- Theorem 8.1.5 as the statement `DL(α)`, for `1/2 ≤ α < 1`. -/
theorem theorem_8_1_5_DL {α : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) : DL815 C α :=
  ⟨_, (theorem_8_1_5_kWL hα hα1).1,
    fun Ω _ _ k X hX => (theorem_8_1_5_kWL hα hα1).2 Ω k X hX.1 hX.2.1 hX.2.2⟩

end DesignAbstract

end Babai
