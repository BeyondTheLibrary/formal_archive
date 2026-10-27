/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Sections 9.4-9.8: two more readings of the coherent configuration of the field
`coherent` of the `Case`, used by §9.7 (`Workspace/SplitOrJohnson/BlockDesignCase.lean`).
-/
import Workspace.SplitOrJohnson.BlkDictionary

/-!
# §9.4-§9.8  More of the dictionary of the `Case`

`Workspace/SplitOrJohnson/BlkDictionary.lean` unpacks the field `coherent` of the `Case`
into a `Babai.BipCaseData`.  Case 1 of §9.7 needs two further readings of it, collected
here so that nothing of §9.7 reads a field of the `Case` other than `coherent`.

* `Babai.PartitionStructure.ncard_inter_nbr_eq_interNum` is Def. 3.1.11 read as
  *"isomorphisms preserve the number of common neighbors"* in the form §9.7 uses it: the
  number of common `R_k`-neighbors of `x` and `y` is an intersection number, so it depends
  on `x` and `y` only through the color `c(x,y)`.  It is the displayed step `hinter` of
  `Babai.PartitionStructure.nbr_eq_iff_interNum`, isolated.
* `Babai.PartitionStructure.rank_le_two_of_pair` and
  `Babai.BipCaseData.three_le_ncard_part₁`: a UPCC has at least three vertices, so
  *"`X₁` is a UPCC"* gives `n₁ ≥ 3`.  This is what entry 41 of the corrected paper in
  the boundary case `d₁ = 1` of `n₂ = 2d₁`.  On two vertices `a ≠ b` a coherent
  configuration has `c(a,a) = c(b,b)` (homogeneity) and `c(a,b) = c(b,a)` — the latter by
  Obs. 3.3.5, because otherwise `a` would have an out-neighbor in the color `c(a,b)` and
  `b` would have none — so its rank is at most `2` and it is not uniprimitive.
* `Babai.BipCaseData.induced_isPrimitive₁_kernel` and `.induced_isUniprimitive₁_kernel`
  are `Babai.BipCaseData.induced_isPrimitive₁` and `.induced_isUniprimitive₁` with the
  hypothesis *"the coloring of `X₁` is the coloring of the input"* written as an equality
  of kernels rather than of labels (entry 84 of the corrected paper).
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*}

/-- Definition 3.1.11, Eq. (17).  *"Isomorphisms preserve the number of common
neighbors"* (§9.7, Case 1), in the form the paper uses: the number of common
`R_k`-neighbors of `x` and `y` is the intersection number `p^{c(x,y)}_{k,k⁻}`, hence
depends on the pair `(x,y)` only through its color.

This is the first step of the proof of `Babai.PartitionStructure.nbr_eq_iff_interNum`,
isolated so that §9.7 can use it on its own. -/
theorem ncard_inter_nbr_eq_interNum (X : PartitionStructure Ω) (h : X.IsCoherent)
    (k : Fin X.rank) (x y : Ω) :
    (X.nbr k x ∩ X.nbr k y).ncard = X.interNum k (X.conv k) (X.color x y) := by
  have hset : {z : Ω | X.color x z = k ∧ X.color z y = X.conv k}
      = X.nbr k x ∩ X.nbr k y := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_nbr]
    exact ⟨fun hz => ⟨hz.1, (X.color_conv_iff h.toIsConfiguration k y z).1 hz.2⟩,
      fun hz => ⟨hz.1, (X.color_conv_iff h.toIsConfiguration k y z).2 hz.2⟩⟩
  rw [← hset]
  exact X.interNum_eq h k (X.conv k) (X.color x y) rfl

/-- Definition 3.1.1.  A partition structure on at most two vertices whose coloring is
symmetric and homogeneous has rank at most `2`: every pair of vertices is one of
`(a,a)`, `(a,b)`, `(b,a)`, `(b,b)`, and the four colors collapse to two. -/
theorem rank_le_two_of_pair (X : PartitionStructure Ω) {a b : Ω}
    (hab : ∀ z : Ω, z = a ∨ z = b) (hhom : X.color a a = X.color b b)
    (hsym : X.color a b = X.color b a) : X.rank ≤ 2 := by
  classical
  have hval : ∀ u v : Ω, X.color u v = X.color a a ∨ X.color u v = X.color a b := by
    intro u v
    rcases hab u with hu | hu <;> rcases hab v with hv | hv <;> subst hu <;> subst hv
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr hsym.symm
    · exact Or.inl hhom.symm
  have hsub : (Finset.univ : Finset (Fin X.rank))
      ⊆ ({X.color a a, X.color a b} : Finset (Fin X.rank)) := by
    intro i _
    obtain ⟨x, y, hxy⟩ := X.color_surjective i
    subst hxy
    rcases hval x y with h | h <;> rw [h] <;> simp
  have h1 := Finset.card_le_card hsub
  have h2 : ({X.color a a, X.color a b} : Finset (Fin X.rank)).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h3 : (Finset.univ : Finset (Fin X.rank)).card = X.rank := by simp
  omega

end PartitionStructure

namespace BipCaseData

variable {V : Type} {c : V → V → ℕ} {V₁ V₂ : Set V} (D : BipCaseData c V₁ V₂)

include D

/-- Observation 3.3.5.  If the first part has exactly the two vertices `a ≠ b`, then
`c(a,b) = c(b,a)`.

The out-degree of the color `c(a,b)` is the same at `a` and at `b`
(`Babai.BipCaseData.ncard_nbhd_eq`).  At `a` it is `1`: the only vertex of that color from
`a` is `b`, because the head of an edge of that color lies in the first part (Obs. 3.3.4)
and `c(a,a) = c(a,b)` would force `a = b` (Def. 3.1.2(i)).  So at `b` it is `1` too, and
the only candidate is `a`. -/
theorem color_symm_of_pair [Finite V] {a b : V} (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hall : ∀ z ∈ V₁, z = a ∨ z = b) (hne : a ≠ b) : c a b = c b a := by
  classical
  have hdiag : ∀ u v w : V, c u v = c w w → u = v := fun u v w huv =>
    D.isCoherent.toIsConfiguration.diag u v w ((D.color_eq_iff u v w w).1 huv)
  -- `a` sees exactly one vertex in the color `c(a,b)`, namely `b`
  have hSa : {y | c a y = c a b} = {b} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      have hyV₁ : y ∈ V₁ := (D.head_mem_part₁_iff hy).2 hb
      rcases hall y hyV₁ with h | h
      · rw [h] at hy; exact absurd (hdiag a b a hy.symm) hne
      · exact h
    · intro hy; rw [hy]
  -- the only candidate for the one vertex that `b` sees in that color is `a`
  have hSbsub : ∀ y : V, c b y = c a b → y = a := by
    intro y hy
    have hyV₁ : y ∈ V₁ := (D.head_mem_part₁_iff hy).2 hb
    rcases hall y hyV₁ with h | h
    · exact h
    · rw [h] at hy; exact absurd (hdiag a b b hy.symm) hne
  -- the two out-degrees agree (Obs. 3.3.5)
  have hvc : D.P.vcolor a = D.P.vcolor b := by
    rw [(D.mem_part₁_iff a).1 ha, (D.mem_part₁_iff b).1 hb]
  have hdeg := D.ncard_nbhd_eq hvc (c a b)
  rw [hSa, Set.ncard_singleton] at hdeg
  have hnem : ({y | c b y = c a b} : Set V).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨y, hy⟩ := hnem
  have hya : y = a := hSbsub y hy
  have hy' : c b y = c a b := hy
  rw [hya] at hy'
  exact hy'.symm

/-- Definition 3.2.1.  *"`X₁` is a UPCC"* gives `n₁ ≥ 3`: a uniprimitive coherent
configuration has rank at least `3`, and on at most two vertices the rank is at most `2`
(`Babai.PartitionStructure.rank_le_two_of_pair`, whose hypotheses are homogeneity and
`Babai.BipCaseData.color_symm_of_pair`).

This is the fact that entry 41 of the corrected paper in the boundary case `d₁ = 1` of
`n₂ = 2d₁`, where the labelling of Case 1 gives `n₁ = C(2,1) = 2`. -/
theorem three_le_ncard_part₁ [Fintype V] [Fintype ↥(D.P.vertexClass D.i)]
    (huni : (D.P.induced (D.P.vertexClass D.i)).IsUniprimitive) : 3 ≤ V₁.ncard := by
  classical
  have hcard : Fintype.card ↥(D.P.vertexClass D.i) = V₁.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← D.part₁_eq]
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hrank : 3 ≤ (D.P.induced (D.P.vertexClass D.i)).rank := huni.2
  have hsq := (D.P.induced (D.P.vertexClass D.i)).rank_le_card_sq
  rcases Nat.lt_or_ge (Fintype.card ↥(D.P.vertexClass D.i)) 2 with hc | hc
  · -- at most one vertex: the rank is at most `1`
    have hc1 : Fintype.card ↥(D.P.vertexClass D.i) ≤ 1 := by omega
    have := Nat.mul_le_mul hc1 hc1
    omega
  · -- exactly two vertices
    have hc2 : Nat.card ↥(D.P.vertexClass D.i) = 2 := by
      rw [Nat.card_eq_fintype_card]; omega
    obtain ⟨a, b, hne, huniv⟩ := Nat.card_eq_two_iff.1 hc2
    have hall : ∀ z : ↥(D.P.vertexClass D.i), z = a ∨ z = b := by
      intro z
      have : z ∈ ({a, b} : Set ↥(D.P.vertexClass D.i)) := by
        rw [huniv]; exact Set.mem_univ z
      simpa using this
    have haV₁ : (a : V) ∈ V₁ := (Set.ext_iff.1 D.part₁_eq (a : V)).2 a.2
    have hbV₁ : (b : V) ∈ V₁ := (Set.ext_iff.1 D.part₁_eq (b : V)).2 b.2
    have hne' : (a : V) ≠ (b : V) := fun hc' => hne (Subtype.ext hc')
    have hallV : ∀ z ∈ V₁, z = (a : V) ∨ z = (b : V) := by
      intro z hz
      have hzc : z ∈ D.P.vertexClass D.i := (Set.ext_iff.1 D.part₁_eq z).1 hz
      rcases hall ⟨z, hzc⟩ with hcc | hcc
      · exact Or.inl (congrArg Subtype.val hcc)
      · exact Or.inr (congrArg Subtype.val hcc)
    have hsymc : c (a : V) (b : V) = c (b : V) (a : V) :=
      D.color_symm_of_pair haV₁ hbV₁ hallV hne'
    have hsym : (D.P.induced (D.P.vertexClass D.i)).color a b
        = (D.P.induced (D.P.vertexClass D.i)).color b a := by
      rw [D.P.induced_color_eq_iff]
      exact (D.color_eq_iff _ _ _ _).1 hsymc
    have hhom : (D.P.induced (D.P.vertexClass D.i)).color a a
        = (D.P.induced (D.P.vertexClass D.i)).color b b := huni.1.1 a b
    have := (D.P.induced (D.P.vertexClass D.i)).rank_le_two_of_pair hall hhom hsym
    omega

end BipCaseData

end Babai
