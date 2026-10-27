/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 8.1–8.2: the Design Lemma, definitions and the procedure.
-/
import Workspace.Higher.Classical
import Workspace.Higher.WL
import Workspace.Coherent.LargeClique

/-!
# §8 The Design Lemma: definitions and the procedure

Version 2.5, Section 8 (lines 3680–3925 of `babai-gi-source/quasi25.txt`).

## Numbering map

| Paper | Lean |
|---|---|
| Definition 8.1.1 | `Babai.IsDominant`, `Babai.KAryPartStruct.dominantClass` |
| Definition 8.1.1, the Note | `Babai.IsDominant.subsingleton` |
| Procedure "Design Lemma", lines 02–03 | `Babai.KAryPartStruct.restrTo` |
| Procedure "Design Lemma", lines 04–05 | `Babai.KAryPartStruct.NoDominantColor` |
| Procedure "Design Lemma", line 06 | `Babai.KAryPartStruct.HasDominantClass` |
| Procedure "Design Lemma", line 07 | `Babai.PartitionStructure.IsCliqueOn`, `Babai.KAryPartStruct.skel2` |
| Procedure "Design Lemma" | `Babai.KAryPartStruct.Returns`, `.procedure` |

## Encoding notes

* `restrTo X hl x⃗` is the restriction `X_x⃗` of §5.2.1 (`Babai.KAryPartStruct.restrict`)
  with the arity written `k - ℓ` rather than `m` where `k = ℓ + m`, so that a single
  `k`-ary structure can be restricted by strings of every length `ℓ ≤ k`.

* `(X_x⃗)^{(2)}`, the `2`-skeleton read as a *classical* coherent configuration
  (Def. 3.1.1), is `skel2`; the `2`-skeleton itself (a `2`-ary partition structure over
  the same color type) is `Babai.KAryPartStruct.skeleton`.  The two have the same color
  classes (`skel2_color_eq_iff`); `skel2` renames the colors by `[r]` as Def. 3.1.1
  requires.

* "`X[Δ]` is a clique configuration" is `(X.induced Δ).rank = 2` (Def. 3.1.8 and
  `Babai.PartitionStructure.cliqueConfig_unique`), the form in which the Large Clique
  Lemma 3.4.25 is stated in `Workspace/Coherent/LargeClique.lean`.
-/

open scoped Classical

namespace Babai

variable {Ω C : Type*} {k l m : ℕ}

/-! ### Definition 8.1.1 -/

/-- Definition 8.1.1.  *"Given a threshold parameter `1/2 ≤ α < 1` and a coloring of a set
`Ω`, we call a color, and the corresponding color class `C ⊆ Ω`, dominant if `|C| > αn`
where `n = |Ω|`."* -/
def IsDominant [Fintype Ω] (α : ℝ) (S : Set Ω) : Prop :=
  α * (Fintype.card Ω : ℝ) < (S.ncard : ℝ)

/-- Definition 8.1.1, the Note.  *"since `α ≥ 1/2`, there is at most one dominant color
under any coloring."*  Two disjoint sets cannot both be dominant. -/
theorem IsDominant.not_disjoint [Fintype Ω] {α : ℝ} (hα : 1 / 2 ≤ α) {S T : Set Ω}
    (hS : IsDominant α S) (hT : IsDominant α T) : ¬ Disjoint S T := by
  intro hdisj
  have hcard : S.ncard + T.ncard ≤ Fintype.card Ω := by
    rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    have := Set.ncard_le_ncard (Set.subset_univ (S ∪ T)) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  have hn : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := Nat.cast_nonneg _
  have h1 : (S.ncard : ℝ) + (T.ncard : ℝ) ≤ (Fintype.card Ω : ℝ) := by
    exact_mod_cast hcard
  have h2 : (1 / 2 : ℝ) * (Fintype.card Ω : ℝ) ≤ α * (Fintype.card Ω : ℝ) :=
    mul_le_mul_of_nonneg_right hα hn
  unfold IsDominant at hS hT
  linarith

/-- Definition 8.1.1, the Note: at most one color class is dominant. -/
theorem IsDominant.subsingleton [Fintype Ω] {α : ℝ} (hα : 1 / 2 ≤ α) {κ : Type*}
    (col : Ω → κ) {i j : κ} (hi : IsDominant α {v | col v = i})
    (hj : IsDominant α {v | col v = j}) : i = j := by
  by_contra hij
  refine (hi.not_disjoint hα hj) ?_
  rw [Set.disjoint_left]
  rintro v hv hv'
  exact hij (hv.symm.trans hv')

theorem not_isDominant_iff [Fintype Ω] {α : ℝ} {S : Set Ω} :
    ¬ IsDominant α S ↔ (S.ncard : ℝ) ≤ α * (Fintype.card Ω : ℝ) := by
  unfold IsDominant
  exact not_lt

namespace KAryPartStruct

/-! ### Reindexing and restriction by a string of any length -/

/-- Reindexing a `k`-ary partition structure along an equality of arities. -/
def recast (X : KAryPartStruct Ω C k) {k' : ℕ} (h : k = k') : KAryPartStruct Ω C k' :=
  ⟨fun y => X.color fun i => y (Fin.cast h i)⟩

@[simp] theorem recast_rfl (X : KAryPartStruct Ω C k) : X.recast rfl = X := rfl

theorem recast_isCoherent (X : KAryPartStruct Ω C k) {k' : ℕ} (h : k = k')
    (hX : X.IsCoherent) : (X.recast h).IsCoherent := by
  subst h; exact hX

theorem recast_isConfiguration (X : KAryPartStruct Ω C k) {k' : ℕ} (h : k = k')
    (hX : X.IsConfiguration) : (X.recast h).IsConfiguration := by
  subst h; exact hX

/-- §5.2.1 (Restriction), with the arity of the restriction written `k - ℓ`.  *"Let
`X = (Ω, c)` be a `k`-ary partition structure.  Let `ℓ < k` and `x⃗ ∈ Ω^ℓ`.  We assign a
coloring `c_x⃗` to `Ω^{k-ℓ}` as follows.  For `y⃗ ∈ Ω^{k-ℓ}` we set `c_x⃗(y⃗) = c(x⃗ y⃗)`.  We
denote the resulting `(k-ℓ)`-ary partition structure `(Ω, c_x⃗)` by `X_x⃗`."* -/
def restrTo (X : KAryPartStruct Ω C k) (hl : l ≤ k) (x : Str Ω l) :
    KAryPartStruct Ω C (k - l) :=
  (X.recast (Nat.add_sub_cancel' hl).symm).restrict x

/-- The string `x⃗ y⃗` of total length `k`, written without a cast on the arity. -/
def fill (hl : l ≤ k) (x : Str Ω l) (y : Str Ω (k - l)) : Str Ω k :=
  fun j => if h : (j : ℕ) < l then x ⟨j, h⟩ else y ⟨(j : ℕ) - l, by have := j.isLt; omega⟩

theorem restrTo_color (X : KAryPartStruct Ω C k) (hl : l ≤ k) (x : Str Ω l)
    (y : Str Ω (k - l)) : (X.restrTo hl x).color y = X.color (fill hl x y) := by
  show X.color (fun i => Str.concat x y (Fin.cast _ i)) = X.color (fill hl x y)
  congr 1
  funext j
  rw [fill]
  by_cases hj : (j : ℕ) < l
  · rw [dif_pos hj]
    have : (Fin.cast (Nat.add_sub_cancel' hl).symm j) = Fin.castAdd (k - l) ⟨(j : ℕ), hj⟩ :=
      Fin.ext rfl
    rw [this, Str.concat_left]
  · rw [dif_neg hj]
    have hj' : l ≤ (j : ℕ) := Nat.le_of_not_lt hj
    have hlt : (j : ℕ) - l < k - l := by have := j.isLt; omega
    have : (Fin.cast (Nat.add_sub_cancel' hl).symm j)
        = Fin.natAdd l (⟨(j : ℕ) - l, hlt⟩ : Fin (k - l)) := by
      refine Fin.ext ?_
      simp only [Fin.coe_cast, Fin.coe_natAdd]
      omega
    rw [this, Str.concat_right]

theorem restrTo_isCoherent [Fintype Ω] (X : KAryPartStruct Ω C k) (h : X.IsCoherent)
    (hl : l ≤ k) (x : Str Ω l) : (X.restrTo hl x).IsCoherent :=
  restrict_isCoherent' _ (X.recast_isCoherent _ h) x

theorem restrTo_isConfiguration (X : KAryPartStruct Ω C k) (h : X.IsConfiguration)
    (hl : l ≤ k) (x : Str Ω l) : (X.restrTo hl x).IsConfiguration := by
  exact restrict_isConfiguration _ (X.recast_isConfiguration _ h) x

/-! ### The strings `x⃗u` and `x⃗uv` -/

end KAryPartStruct

namespace Str

/-- The string `x⃗ u` of length `ℓ + 1`. -/
def snoc1 (x : Str Ω l) (u : Ω) : Str Ω (l + 1) := Str.concat x (fun _ => u)

/-- The string `x⃗ u v` of length `ℓ + 2`. -/
def snoc2 (x : Str Ω l) (u v : Ω) : Str Ω (l + 2) := Str.concat x ![u, v]

theorem concat_val_lt (x : Str Ω l) (y : Str Ω m) (j : Fin (l + m)) (i : Fin l)
    (h : (j : ℕ) = (i : ℕ)) : Str.concat x y j = x i := by
  have hj : j = Fin.castAdd m i := Fin.ext (by simpa using h)
  rw [hj, Str.concat_left]

theorem concat_val_ge (x : Str Ω l) (y : Str Ω m) (j : Fin (l + m)) (i : Fin m)
    (h : (j : ℕ) = l + (i : ℕ)) : Str.concat x y j = y i := by
  have hj : j = Fin.natAdd l i := Fin.ext (by simpa using h)
  rw [hj, Str.concat_right]

theorem snoc1_val_lt (x : Str Ω l) (u : Ω) (j : Fin (l + 1)) (i : Fin l)
    (h : (j : ℕ) = (i : ℕ)) : snoc1 x u j = x i := concat_val_lt x _ j i h

theorem snoc1_val_ge (x : Str Ω l) (u : Ω) (j : Fin (l + 1)) (h : l ≤ (j : ℕ)) :
    snoc1 x u j = u := by
  have hj := j.isLt
  exact concat_val_ge x _ j 0 (by simp; omega)

theorem snoc2_val_lt (x : Str Ω l) (u v : Ω) (j : Fin (l + 2)) (i : Fin l)
    (h : (j : ℕ) = (i : ℕ)) : snoc2 x u v j = x i := concat_val_lt x _ j i h

theorem snoc2_val_eq (x : Str Ω l) (u v : Ω) (j : Fin (l + 2)) (h : (j : ℕ) = l) :
    snoc2 x u v j = u := concat_val_ge x _ j 0 (by simp [h])

theorem snoc2_val_gt (x : Str Ω l) (u v : Ω) (j : Fin (l + 2)) (h : l < (j : ℕ)) :
    snoc2 x u v j = v := by
  have hj := j.isLt
  exact concat_val_ge x _ j 1 (by simp; omega)

theorem snoc1_snoc1 (x : Str Ω l) (u v : Ω) : snoc1 (snoc1 x u) v = snoc2 x u v := by
  funext j
  have hj := j.isLt
  rcases Nat.lt_trichotomy (j : ℕ) l with h | h | h
  · rw [snoc1_val_lt (snoc1 x u) v j ⟨(j : ℕ), by omega⟩ rfl,
      snoc1_val_lt x u ⟨(j : ℕ), by omega⟩ ⟨(j : ℕ), h⟩ rfl,
      snoc2_val_lt x u v j ⟨(j : ℕ), h⟩ rfl]
  · rw [snoc1_val_lt (snoc1 x u) v j ⟨(j : ℕ), by omega⟩ rfl,
      snoc1_val_ge x u ⟨(j : ℕ), by omega⟩ (by simp [h]),
      snoc2_val_eq x u v j h]
  · rw [snoc1_val_ge (snoc1 x u) v j (by omega), snoc2_val_gt x u v j h]

theorem snoc1_distinct {x : Str Ω l} (hx : Distinct x) {u : Ω} (hu : u ∉ supp x) :
    Distinct (snoc1 x u) := by
  intro i j hij
  have hi' := i.isLt
  have hj' := j.isLt
  by_cases hi : (i : ℕ) < l <;> by_cases hj : (j : ℕ) < l
  · rw [snoc1_val_lt x u i ⟨(i : ℕ), hi⟩ rfl, snoc1_val_lt x u j ⟨(j : ℕ), hj⟩ rfl] at hij
    have hval : ((⟨(i : ℕ), hi⟩ : Fin l) : ℕ) = ((⟨(j : ℕ), hj⟩ : Fin l) : ℕ) :=
      congrArg Fin.val (hx hij)
    exact Fin.ext hval
  · rw [snoc1_val_lt x u i ⟨(i : ℕ), hi⟩ rfl, snoc1_val_ge x u j (by omega)] at hij
    exact absurd ⟨⟨(i : ℕ), hi⟩, hij⟩ hu
  · rw [snoc1_val_ge x u i (by omega), snoc1_val_lt x u j ⟨(j : ℕ), hj⟩ rfl] at hij
    exact absurd ⟨⟨(j : ℕ), hj⟩, hij.symm⟩ hu
  · exact Fin.ext (by omega)

theorem supp_snoc1 (x : Str Ω l) (u : Ω) : supp (snoc1 x u) = insert u (supp x) := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    have hj := j.isLt
    by_cases h : (j : ℕ) < l
    · exact Or.inr ⟨⟨(j : ℕ), h⟩, (snoc1_val_lt x u j ⟨(j : ℕ), h⟩ rfl).symm⟩
    · exact Or.inl (snoc1_val_ge x u j (by omega))
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last l, snoc1_val_ge x w (Fin.last l) (by simp)⟩
    · exact ⟨Fin.castSucc j, snoc1_val_lt x u (Fin.castSucc j) j (by simp)⟩

/-- The value of a padded `2`-string. -/
theorem pad2_val (h2 : (0 : ℕ) < 2) (u v : Ω) (t : Fin m) :
    Str.pad h2 m ![u, v] t = if (t : ℕ) = 0 then u else v := by
  rw [Str.pad_eq]
  by_cases ht : (t : ℕ) = 0
  · rw [if_pos ht,
      show Str.padIdx 2 h2 (t : ℕ) = 0 from Fin.ext (by show min (t : ℕ) 1 = 0; omega)]
    rfl
  · rw [if_neg ht,
      show Str.padIdx 2 h2 (t : ℕ) = 1 from Fin.ext (by show min (t : ℕ) 1 = 1; omega)]
    rfl

end Str

namespace KAryPartStruct

/-! ### The extended coloring of §5.1.4 read off from a restriction -/

/-- `c_x⃗(u) = c(x⃗u)`: the vertex-coloring of the restriction `X_x⃗` is the extended
coloring (§5.1.4) of the string `x⃗u`. -/
theorem restrTo_vcolor (X : KAryPartStruct Ω C k) (hl : l < k) (h1 : 0 < l + 1)
    (x : Str Ω l) (u : Ω) :
    (X.restrTo hl.le x).vcolor u = X.skeletonColor h1 hl (Str.snoc1 x u) := by
  have hpad : ∀ j : Fin k, ((Str.padIdx (l + 1) h1 (j : ℕ)) : ℕ) = min (j : ℕ) l := fun _ => rfl
  rw [vcolor, restrTo_color, skeletonColor]
  congr 1
  funext j
  have hj := j.isLt
  rw [fill, Str.pad_eq]
  by_cases h : (j : ℕ) < l
  · rw [dif_pos h]
    exact (Str.snoc1_val_lt x u _ ⟨(j : ℕ), h⟩
      (by show ((Str.padIdx (l + 1) h1 (j : ℕ)) : ℕ) = (j : ℕ); rw [hpad]; omega)).symm
  · rw [dif_neg h]
    exact (Str.snoc1_val_ge x u _
      (by show l ≤ ((Str.padIdx (l + 1) h1 (j : ℕ)) : ℕ); rw [hpad]; omega)).symm

/-- `c_x⃗(uv) = c(x⃗uv)`: the extended coloring of the restriction `X_x⃗` at a string of
length `2` is the extended coloring of `X` at `x⃗uv`. -/
theorem restrTo_skeletonColor2 (X : KAryPartStruct Ω C k) (hl : l ≤ k) (h2 : l + 2 ≤ k)
    (hp2 : (0 : ℕ) < 2) (hkl : 2 ≤ k - l) (hp : 0 < l + 2) (x : Str Ω l) (u v : Ω) :
    (X.restrTo hl x).skeletonColor hp2 hkl ![u, v]
      = X.skeletonColor hp h2 (Str.snoc2 x u v) := by
  have hpad : ∀ j : Fin k, ((Str.padIdx (l + 2) hp (j : ℕ)) : ℕ) = min (j : ℕ) (l + 1) :=
    fun _ => rfl
  rw [skeletonColor, restrTo_color, skeletonColor]
  congr 1
  funext j
  have hj := j.isLt
  rw [fill, Str.pad_eq]
  by_cases h : (j : ℕ) < l
  · rw [dif_pos h]
    exact (Str.snoc2_val_lt x u v _ ⟨(j : ℕ), h⟩
      (by show ((Str.padIdx (l + 2) hp (j : ℕ)) : ℕ) = (j : ℕ); rw [hpad]; omega)).symm
  · rw [dif_neg h, Str.pad2_val]
    by_cases h' : (j : ℕ) = l
    · rw [if_pos (by show (j : ℕ) - l = 0; omega)]
      exact (Str.snoc2_val_eq x u v _
        (by show ((Str.padIdx (l + 2) hp (j : ℕ)) : ℕ) = l; rw [hpad]; omega)).symm
    · rw [if_neg (by show ¬ ((j : ℕ) - l = 0); omega)]
      exact (Str.snoc2_val_gt x u v _
        (by show l < ((Str.padIdx (l + 2) hp (j : ℕ)) : ℕ); rw [hpad]; omega)).symm

/-! ### Vertex colors and the dominant class -/

/-- The vertex-color class of the color `i` (Def. 3.1.4 for a `k`-ary structure): the
diagonal color of `v` is `c(v,…,v)`. -/
def vclass (Y : KAryPartStruct Ω C m) (i : C) : Set Ω := {v | Y.vcolor v = i}

theorem mem_vclass (Y : KAryPartStruct Ω C m) (v : Ω) : v ∈ Y.vclass (Y.vcolor v) := rfl

theorem vclass_disjoint (Y : KAryPartStruct Ω C m) {i j : C} (h : i ≠ j) :
    Disjoint (Y.vclass i) (Y.vclass j) := by
  rw [Set.disjoint_left]
  rintro v hv hv'
  exact h (hv.symm.trans hv')

/-- Line 06 of the procedure: *"we have a unique vertex-color class `C(x⃗)` of size
`> αn`"*.  The dominant vertex-color class of `Y`, defined without a choice: it is the
set of vertices whose own vertex-color class is dominant.  By Def. 8.1.1 (the Note) at
most one class is dominant, so this set is that class when one exists, and empty
otherwise. -/
def dominantClass [Fintype Ω] (α : ℝ) (Y : KAryPartStruct Ω C m) : Set Ω :=
  {v | IsDominant α (Y.vclass (Y.vcolor v))}

/-- Line 06: the dominant class is the class of a dominant color. -/
theorem dominantClass_eq [Fintype Ω] {α : ℝ} (hα : 1 / 2 ≤ α) (Y : KAryPartStruct Ω C m)
    {i : C} (hi : IsDominant α (Y.vclass i)) : dominantClass α Y = Y.vclass i := by
  ext v
  constructor
  · intro hv
    exact (IsDominant.subsingleton hα Y.vcolor hv hi : Y.vcolor v = i)
  · intro hv
    show IsDominant α (Y.vclass (Y.vcolor v))
    rw [show Y.vcolor v = i from hv]
    exact hi

/-- Lines 04–05: *"each vertex-color class in the restriction `X_x⃗` has size `≤ αn`"*. -/
def NoDominantColor [Fintype Ω] (α : ℝ) (Y : KAryPartStruct Ω C m) : Prop :=
  ∀ i : C, ((Y.vclass i).ncard : ℝ) ≤ α * (Fintype.card Ω : ℝ)

/-- Line 06: *"we have a unique vertex-color class `C(x⃗)` of size `> αn`"*. -/
def HasDominantClass [Fintype Ω] (α : ℝ) (Y : KAryPartStruct Ω C m) : Prop :=
  ∃ i : C, IsDominant α (Y.vclass i)

theorem not_noDominantColor_iff [Fintype Ω] {α : ℝ} (Y : KAryPartStruct Ω C m) :
    ¬ NoDominantColor α Y ↔ HasDominantClass α Y := by
  unfold NoDominantColor HasDominantClass IsDominant
  push_neg
  rfl

/-! ### The `2`-skeleton as a classical coherent configuration -/

/-- `(X)^{(2)}`, the `2`-skeleton of a `k`-ary partition structure (`k ≥ 2`) read as a
binary partition structure in the sense of Def. 3.1.1: the color of the pair `(u, v)` is
the extended color `c^{(2)}(uv)` of §5.1.4, renamed by `[r]`. -/
noncomputable def skel2 [Fintype Ω] (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) :
    PartitionStructure Ω :=
  PartitionStructure.ofColoring
    (fun u v : Ω => Y.skeletonColor (by norm_num) hm ![u, v])

theorem skel2_color_eq_iff [Fintype Ω] (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (u v u' v' : Ω) :
    (Y.skel2 hm).color u v = (Y.skel2 hm).color u' v'
      ↔ Y.skeletonColor (by norm_num) hm ![u, v]
          = Y.skeletonColor (by norm_num) hm ![u', v'] :=
  PartitionStructure.ofColoring_color_eq_iff _ _ _ _ _

/-- §5.2, *"the `2`-skeleton `X^{(2)}` of a `k`-ary coherent configuration `X` is a
classical coherent configuration"*, for an arbitrary (possibly infinite) color type. -/
theorem skel2_isCoherent [Fintype Ω] (Y : KAryPartStruct Ω C m) (hY : Y.IsCoherent)
    (hm : 2 ≤ m) : (Y.skel2 hm).IsCoherent := by
  classical
  have h2 : (Y.skeleton (by norm_num : (0:ℕ) < 2) hm).IsCoherent :=
    skeleton_isCoherent' Y hY (by norm_num) hm
  refine (PartitionStructure.isCoherent_toKAry_iff _).1 (isCoherent_congr ?_ h2)
  intro a b
  have heta : ∀ z : Str Ω 2, ![z 0, z 1] = z := by
    intro z
    funext i
    rcases (by decide : ∀ t : Fin 2, t = 0 ∨ t = 1) i with rfl | rfl <;> rfl
  show (Y.skeleton (by norm_num : (0:ℕ) < 2) hm).color a
      = (Y.skeleton (by norm_num : (0:ℕ) < 2) hm).color b
    ↔ (Y.skel2 hm).color (a 0) (a 1) = (Y.skel2 hm).color (b 0) (b 1)
  rw [skel2_color_eq_iff, heta a, heta b]
  exact Iff.rfl

/-- The vertex colors of `(X)^{(2)}` are the vertex colors of `X`. -/
theorem skel2_vcolor_eq_iff [Fintype Ω] (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m)
    (u v : Ω) : (Y.skel2 hm).vcolor u = (Y.skel2 hm).vcolor v ↔ Y.vcolor u = Y.vcolor v := by
  rw [PartitionStructure.vcolor, PartitionStructure.vcolor, skel2_color_eq_iff]
  constructor
  · intro h
    show Y.color (fun _ => u) = Y.color (fun _ => v)
    have hp : ∀ w : Ω, Str.pad (by norm_num : (0:ℕ) < 2) m ![w, w] = fun _ => w := by
      intro w
      funext j
      rw [Str.pad_eq]
      rcases (by omega : (Str.padIdx 2 (by norm_num) (j : ℕ) : ℕ) = 0 ∨
          (Str.padIdx 2 (by norm_num) (j : ℕ) : ℕ) = 1) with h0 | h1
      · rw [show Str.padIdx 2 (by norm_num : (0:ℕ) < 2) (j : ℕ) = 0 from Fin.ext h0]
        rfl
      · rw [show Str.padIdx 2 (by norm_num : (0:ℕ) < 2) (j : ℕ) = 1 from Fin.ext h1]
        rfl
    have := h
    rw [skeletonColor, skeletonColor, hp u, hp v] at this
    exact this
  · intro h
    rw [skeletonColor, skeletonColor]
    have hp : ∀ w : Ω, Str.pad (by norm_num : (0:ℕ) < 2) m ![w, w] = fun _ => w := by
      intro w
      funext j
      rw [Str.pad_eq]
      rcases (by omega : (Str.padIdx 2 (by norm_num) (j : ℕ) : ℕ) = 0 ∨
          (Str.padIdx 2 (by norm_num) (j : ℕ) : ℕ) = 1) with h0 | h1
      · rw [show Str.padIdx 2 (by norm_num : (0:ℕ) < 2) (j : ℕ) = 0 from Fin.ext h0]
        rfl
      · rw [show Str.padIdx 2 (by norm_num : (0:ℕ) < 2) (j : ℕ) = 1 from Fin.ext h1]
        rfl
    rw [hp u, hp v]
    exact h

/-- The vertex-color classes of `(X)^{(2)}` (Def. 3.1.4) are the vertex-color classes of
`X` (§5.1.4).  This is what makes the dominant class of the `k`-ary structure `X_x⃗` a
*stable* set of the classical configuration `X* = (X_x⃗)^{(2)}`, so that Obs. 3.3.2
applies to it. -/
theorem skel2_vertexClass_eq [Fintype Ω] (Y : KAryPartStruct Ω C m) (hm : 2 ≤ m) (u : Ω) :
    (Y.skel2 hm).vertexClass ((Y.skel2 hm).vcolor u) = Y.vclass (Y.vcolor u) := by
  ext v
  exact skel2_vcolor_eq_iff Y hm v u

end KAryPartStruct

namespace PartitionStructure

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Line 07 of the procedure: *"the `2`-skeleton `(X_x⃗)^{(2)}` … induce[s] a clique
configuration on `C(x⃗)`"*.  By Def. 3.1.8 and `cliqueConfig_unique`, a configuration is
the clique configuration exactly when it has rank `2`. -/
def IsCliqueOn (Y : PartitionStructure Ω) (Δ : Set Ω) : Prop := (Y.induced Δ).rank = 2

/-- The rank of an induced substructure does not depend on the `Fintype` instance used to
form it (`Fintype` is a subsingleton).  This is needed because the instance synthesized
for a general `Δ : Set Ω` (classical) and the one synthesized for a vertex-color class
(decidable equality of colors) are different terms. -/
theorem induced_rank_congr (Y : PartitionStructure Ω) (Δ : Set Ω) (i₁ i₂ : Fintype Δ) :
    (@PartitionStructure.induced Ω Y Δ i₁).rank
      = (@PartitionStructure.induced Ω Y Δ i₂).rank := by
  rw [Subsingleton.elim i₁ i₂]

theorem isCliqueOn_iff (Y : PartitionStructure Ω) (Δ : Set Ω) (inst : Fintype Δ) :
    Y.IsCliqueOn Δ ↔ (@PartitionStructure.induced Ω Y Δ inst).rank = 2 := by
  unfold PartitionStructure.IsCliqueOn
  rw [induced_rank_congr Y Δ _ inst]

/-- Two vertices of `Δ` whose two ordered pairs have different colors witness that `Y`
does not induce a clique configuration on `Δ`: in a rank-`2` configuration all
off-diagonal pairs have one and the same color (`color_eq_of_rank_two`). -/
theorem not_isCliqueOn_of_color_ne (Y : PartitionStructure Ω) (hY : Y.IsConfiguration)
    {Δ : Set Ω} {u v : Ω} (hu : u ∈ Δ) (hv : v ∈ Δ) (huv : u ≠ v)
    (hne : Y.color u v ≠ Y.color v u) : ¬ Y.IsCliqueOn Δ := by
  intro hclique
  have hind := PartitionStructure.color_eq_of_rank_two (Y.induced Δ)
    (Y.induced_isConfiguration Δ hY) hclique
    (x := ⟨u, hu⟩) (y := ⟨v, hv⟩) (u := ⟨v, hv⟩) (v := ⟨u, hu⟩)
    (fun hc => huv (congrArg Subtype.val hc)) (fun hc => huv (congrArg Subtype.val hc).symm)
  rw [Y.induced_color_eq_iff] at hind
  exact hne hind

end PartitionStructure

namespace KAryPartStruct

variable [Fintype Ω] [DecidableEq Ω]

/-! ### The procedure -/

/-- Lines 04–08 of Procedure "Design Lemma": the test performed at the string `x⃗`.  The
procedure returns at `x⃗` if either no vertex-color class of `X_x⃗` is dominant (line 05,
goal (i)), or `ℓ(x⃗) ≤ k - 2`, there is a dominant class `C(x⃗)`, and the `2`-skeleton
`(X_x⃗)^{(2)}` does not induce a clique configuration on `C(x⃗)` (line 08, goal (ii)). -/
def Returns (α : ℝ) (X : KAryPartStruct Ω C k) (hl : l ≤ k) (x : Str Ω l) : Prop :=
  Str.Distinct x ∧
    (NoDominantColor α (X.restrTo hl x) ∨
      ∃ h2 : l + 2 ≤ k, HasDominantClass α (X.restrTo hl x) ∧
        ¬ ((X.restrTo hl x).skel2 (by omega)).IsCliqueOn
            (dominantClass α (X.restrTo hl x)))

/-- Line 03: the procedure returns at some string of length `ℓ`. -/
def ReturnsAt (α : ℝ) (X : KAryPartStruct Ω C k) (l : ℕ) : Prop :=
  ∃ h : l < k, ∃ x : Str Ω l, Returns α X h.le x

/-- Procedure "Design Lemma" (§8.2).

```
Input: a k-ary structure X = (Ω, R) with symmetry defect ≥ 1 − α where 1/2 ≤ α < 1.
Output: (i) or (ii) of Theorem 8.1.5.
01 apply k-WL to X       (: henceforth we assume X is k-ary coherent :)
02 for ℓ = 0 to k − 1
03   for x⃗ ∈ Ω^⟨ℓ⟩
04     if each vertex-color class in the restriction X_x⃗ has size ≤ αn
05     then return the vertex-coloring, exit           (: goal (i) achieved :)
06     else (: we have a unique vertex-color class C(x⃗) of size > αn :)
07       if ℓ ≤ k − 2 and the 2-skeleton (X_x⃗)^{(2)} does not induce
          a clique configuration on C(x⃗) then
08         return X* := (X_x⃗)^{(2)}, exit              (: goal (ii) achieved :)
```

Line 01 is `Babai.KAryRelStruct.kWL`, applied by the theorems of `Main.lean`; the
procedure below is lines 02–08, run on the `k`-ary coherent configuration produced by
line 01.  It returns the length `ℓ` and the string `x⃗` at which lines 05 or 08 fire; the
objects returned there, the vertex-coloring of `X_x⃗` and the configuration
`X* = (X_x⃗)^{(2)}`, are functions of `x⃗` (`restrTo`, `skel2`), and which of the two fired
is recorded by `Returns`.  The outer loop of line 02 is the search for the *least* `ℓ`;
the paper prescribes no order on `Ω^⟨ℓ⟩` for the inner loop of line 03, and the choice of
`x⃗` among the strings of length `ℓ` at which the procedure returns is immaterial for
Thm. 8.2.1, so it is made by `Exists.choose`. -/
noncomputable def procedure (α : ℝ) (X : KAryPartStruct Ω C k) :
    Option (Σ l : ℕ, Str Ω l) :=
  if h : ∃ l, ReturnsAt α X l then
    some ⟨Nat.find h, ((Nat.find_spec h).choose_spec).choose⟩
  else none

theorem procedure_spec (α : ℝ) (X : KAryPartStruct Ω C k) (h : ∃ l, ReturnsAt α X l) :
    ∃ p : Σ l : ℕ, Str Ω l, X.procedure α = some p ∧
      ∃ hp : p.1 < k, Returns α X hp.le p.2 := by
  refine ⟨⟨Nat.find h, ((Nat.find_spec h).choose_spec).choose⟩, ?_, ?_⟩
  · rw [procedure, dif_pos h]
  · exact ⟨(Nat.find_spec h).choose, ((Nat.find_spec h).choose_spec).choose_spec⟩

end KAryPartStruct

end Babai
