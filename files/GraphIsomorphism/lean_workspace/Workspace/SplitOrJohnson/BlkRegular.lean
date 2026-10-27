/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 2: the link is semiregular, and `X* = X[A, C]` is not trivial.
-/
import Workspace.SplitOrJohnson.BlkTwinClass

/-!
# §9.7, Case 2  The link as a semiregular bipartite graph, and `X*`

Version 2.5, lines 4266-4270:

> *"Let `X* = X[A, C]` and let `H* = (C, E*)` be the corresponding neighborhood hypergraph.
> … It follows that `H*` is regular.  `H*` is also uniform since `A` is a `c'`-color class.
> So `X*` is semiregular.  It cannot be trivial because the relative sizes of `A` (in `V₁`)
> and `C` (in `V₂`) add up to more than 1, contradicting Cor. 2.4.32."*

The corollary is `Babai.case_9_7_2`, and its hypotheses are about the **whole** link
`X = (V₁, V₂; E)`, not about `X*`: the link is semiregular and nontrivial, and then no
induced subgraph `X[A, C]` whose relative sizes add up to more than `1` is trivial.  This
file supplies those two hypotheses for an input of §9.7 and reads the conclusion back in
the language of the neighborhoods:

* `Babai.BlkCaseObj.nbhd_regular` — *"`H` is regular"*: every block lies in the same number
  of neighborhoods.  This is Obs. 3.3.5 again (`Babai.BipCaseData.ncard_nbhd_eq`), applied
  at a vertex of `V₂` and in the **reversed** color `Babai.BlkCaseObj.linkColor⁻`
  (`Babai.BlkCaseObj.exists_revColor`), where `Babai.BlkCaseObj.nbhd_ncard_uniform` applied
  it at a vertex of `V₁`.
* `Babai.BlkCaseObj.linkBipGraph` is `X = (V₁, V₂; E)` as an object of `Babai.BipGraph`;
  it is semiregular and nontrivial.
* `Babai.BlkCaseObj.exists_mem_nbhd_of_sizes` and `.exists_notMem_nbhd_of_sizes` are
  Cor. 2.4.32 read back: `X[A, C]` has an edge and a non-edge.
-/

namespace Babai

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace BlkCaseObj

variable {s : Set Ω} {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-! ### The reversed link color -/

/-- §9.7.  Terminology 3.1.3: the color `Babai.BlkCaseObj.linkColor⁻` reversing the
constituent of the link that §9.7 reads the neighborhoods in.  An edge `(v, u)` has this
color exactly when `(u, v)` has the color `Babai.BlkCaseObj.linkColor`. -/
theorem exists_revColor (X : BlkDesignObj s) :
    ∃ m : ℕ, ∀ u v : ↥X.vtxSet, X.vc v u = m ↔ X.vc u v = X.linkColor := by
  classical
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  set D := X.bipData with hD
  set k : Fin D.P.rank := D.P.color (X.vtxPt hx₀) (X.vtxBlk hB₀) with hk
  have hkval : (k : ℕ) = X.linkColor := by
    rw [hk, ← D.color_val (X.vtxPt hx₀) (X.vtxBlk hB₀)]; exact hcol₀
  refine ⟨((D.P.conv k : Fin D.P.rank) : ℕ), fun u v => ?_⟩
  have h1 : X.vc u v = X.linkColor ↔ D.P.color u v = k := by
    rw [D.color_val u v, ← hkval]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  have h2 : X.vc v u = ((D.P.conv k : Fin D.P.rank) : ℕ) ↔ D.P.color v u = D.P.conv k := by
    rw [D.color_val v u]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [h1, h2]
  exact D.P.color_conv_iff D.isCoherent.toIsConfiguration k u v

/-- §9.7.  The in-neighborhood of a block in the reversed link color, read on the points of
`V₁`: the tail of an edge of that color is a vertex of `V₁`, that is, a point. -/
theorem val_image_setOf_vc_rev (X : BlkDesignObj s) {m : ℕ}
    (hm : ∀ u v : ↥X.vtxSet, X.vc v u = m ↔ X.vc u v = X.linkColor)
    {B : Set ↥s} (hB : B ∈ X.blocks) :
    Subtype.val '' {y : ↥X.vtxSet | X.vc (X.vtxBlk hB) y = m}
      = (fun x : ↥s => ({x} : Set ↥s)) '' {x : ↥s | X.part₁ x ∧ B ∈ X.nbhd x} := by
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  ext A
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : X.vc y (X.vtxBlk hB) = X.linkColor := (hm y (X.vtxBlk hB)).1 hy
    have hcol : X.vc y (X.vtxBlk hB) = X.vc (X.vtxPt hx₀) (X.vtxBlk hB₀) := by
      rw [hy']; exact hcol₀.symm
    have hy₁ : y ∈ {u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet} :=
      (X.bipData.tail_mem_part₁_iff hcol).2 (X.vtxPt_mem₁ hx₀)
    obtain ⟨x, hx, hxy⟩ := hy₁
    refine ⟨x, ⟨hx, hB, ?_⟩, hxy.symm⟩
    show X.c {x} B = X.linkColor
    rw [← hxy]; exact hy'
  · rintro ⟨x, ⟨hx, hBx⟩, rfl⟩
    refine ⟨X.vtxPt hx, ?_, rfl⟩
    show X.vc (X.vtxBlk hB) (X.vtxPt hx) = m
    exact (hm (X.vtxPt hx) (X.vtxBlk hB)).2 hBx.2

/-- §9.7, Case 2.  ***"`H` is regular"***: every block lies in the same number of
neighborhoods `X(v)`, `v ∈ V₁`.

This is Observation 3.3.5 (degree awareness,
`Babai.PartitionStructure.outDegC_eq_of_vcolor_eq`) at a vertex of `V₂`: the out-degree in
the reversed link color `Babai.BlkCaseObj.exists_revColor` depends only on the vertex
color, and all blocks have the same vertex color because `V₂` is a vertex-color class of
the configuration of step 3 of §9.4. -/
theorem nbhd_regular (X : BlkDesignObj s) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) :
    {x : ↥s | X.part₁ x ∧ B ∈ X.nbhd x}.ncard
      = {x : ↥s | X.part₁ x ∧ B' ∈ X.nbhd x}.ncard := by
  classical
  obtain ⟨m, hm⟩ := X.exists_revColor
  have key : ∀ {D : Set ↥s} (hD : D ∈ X.blocks),
      {y : ↥X.vtxSet | X.vc (X.vtxBlk hD) y = m}.ncard
        = {x : ↥s | X.part₁ x ∧ D ∈ X.nbhd x}.ncard := by
    intro D hD
    have h1 := Set.ncard_image_of_injective
      {y : ↥X.vtxSet | X.vc (X.vtxBlk hD) y = m} (Subtype.val_injective (p := (· ∈ X.vtxSet)))
    have h2 := Set.ncard_image_of_injective {x : ↥s | X.part₁ x ∧ D ∈ X.nbhd x}
      (Set.singleton_injective (α := ↥s))
    rw [← h1, X.val_image_setOf_vc_rev hm hD, h2]
  rw [← key hB, ← key hB']
  have hvc : X.bipData.P.vcolor (X.vtxBlk hB) = X.bipData.P.vcolor (X.vtxBlk hB') := by
    rw [(X.bipData.mem_part₂_iff _).1 (X.vtxBlk_mem₂ hB),
      (X.bipData.mem_part₂_iff _).1 (X.vtxBlk_mem₂ hB')]
  exact X.bipData.ncard_nbhd_eq hvc m

/-! ### The link as a bipartite graph -/

/-- §9.7.  The link `X₁₂ = (V₁, V₂; E)` of an input of §9.7, as a bipartite graph in the
sense of §2.4.2: `v ∈ V₁` is joined to the blocks of its neighborhood `X(v)`. -/
def linkBipGraph (X : BlkCaseObj s Case) : BipGraph ↥{x : ↥s | X.part₁ x} ↥X.blocks :=
  ⟨{p | ((p.2 : Set ↥s)) ∈ X.nbhd (p.1 : ↥s)}⟩

theorem degA_linkBipGraph (X : BlkCaseObj s Case) (a : ↥{x : ↥s | X.part₁ x}) :
    X.linkBipGraph.degA a = (X.nbhd (a : ↥s)).ncard := by
  show {b : ↥X.blocks | ((b : Set ↥s)) ∈ X.nbhd (a : ↥s)}.ncard = _
  exact X.ncard_coe_blocks (X.nbhd_subset_blocks (a : ↥s))

theorem degB_linkBipGraph (X : BlkCaseObj s Case) (b : ↥X.blocks) :
    X.linkBipGraph.degB b = {x : ↥s | X.part₁ x ∧ (b : Set ↥s) ∈ X.nbhd x}.ncard := by
  have himg : Subtype.val '' {a : ↥{x : ↥s | X.part₁ x} | ((b : Set ↥s)) ∈ X.nbhd (a : ↥s)}
      = {x : ↥s | X.part₁ x ∧ (b : Set ↥s) ∈ X.nbhd x} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, h2, rfl⟩
  have := Set.ncard_image_of_injective
    {a : ↥{x : ↥s | X.part₁ x} | ((b : Set ↥s)) ∈ X.nbhd (a : ↥s)}
    (Subtype.val_injective (p := (· ∈ {x : ↥s | X.part₁ x})))
  rw [himg] at this
  exact this.symm

/-- §9.7.  *"`X` is semiregular"* (step 8 of §9.4): the link is uniform of rank `d₁` on the
`V₁` side (`Babai.BlkCaseObj.nbhd_ncard_uniform`) and regular on the `V₂` side
(`Babai.BlkCaseObj.nbhd_regular`). -/
theorem linkBipGraph_isSemiregular (X : BlkDesignObj s) : X.linkBipGraph.IsSemiregular := by
  constructor
  · refine ⟨X.d₁, fun a => ?_⟩
    rw [X.degA_linkBipGraph a, X.nbhd_ncard_eq_d₁ a.2]
  · obtain ⟨B₀, hB₀⟩ := BlkBlockDesignInputs.blocks_nonempty_of_case X.case
    refine ⟨{x : ↥s | X.part₁ x ∧ B₀ ∈ X.nbhd x}.ncard, fun b => ?_⟩
    rw [X.degB_linkBipGraph b]
    exact X.nbhd_regular b.2 hB₀

/-- §9.7.  *"the link `X₁₂` is nontrivial"* (the field `link_nontrivial` of
`Babai.IsBipartiteCase`), read as the nontriviality of the bipartite graph: the link has an
edge, because `Babai.BlkCaseObj.linkColor` occurs on `V₁ × V₂`, and a non-edge, because a
second color occurs there. -/
theorem linkBipGraph_not_isTrivial (X : BlkDesignObj s) : ¬ X.linkBipGraph.IsTrivial := by
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  rintro (hempty | huniv)
  · have hmem : ((⟨x₀, hx₀⟩ : ↥{x : ↥s | X.part₁ x}), (⟨B₀, hB₀⟩ : ↥X.blocks))
        ∈ X.linkBipGraph.E := ⟨hB₀, hcol₀⟩
    rw [hempty] at hmem
    exact hmem
  · -- every point of `V₁` sees every block, so only one color occurs on the link
    have hall : ∀ x, X.part₁ x → ∀ B ∈ X.blocks, X.c {x} B = X.linkColor := by
      intro x hx B hB
      have : ((⟨x, hx⟩ : ↥{x : ↥s | X.part₁ x}), (⟨B, hB⟩ : ↥X.blocks))
          ∈ X.linkBipGraph.E := by rw [huniv]; exact Set.mem_univ _
      exact this.2
    obtain ⟨x₁, y₁, x₂, y₂, hne⟩ := X.bipCase'.link_nontrivial
    refine hne ?_
    have hcolor : ∀ (a : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.sglSet})
        (b : ↥{u : ↥X.vtxSet | (u : Set ↥s) ∈ X.blocks}),
        X.vc (a : ↥X.vtxSet) (b : ↥X.vtxSet) = X.linkColor := by
      intro a b
      obtain ⟨x, hx, hax⟩ := a.2
      show X.c ((a : ↥X.vtxSet) : Set ↥s) ((b : ↥X.vtxSet) : Set ↥s) = X.linkColor
      rw [hax]
      exact hall x hx _ b.2
    rw [hcolor x₁ y₁, hcolor x₂ y₂]

/-! ### Corollary 2.4.32 for `X[A, C]` -/

/-- §9.7, Case 2.  ***"`X*` cannot be trivial"***, the edge half: if the relative sizes of
`A ⊆ V₁` and `C ⊆ V₂` add up to more than `1`, then some point of `A` sees some block of
`C`.  This is `Babai.case_9_7_2` (Cor. 2.4.32) applied to the link
(`Babai.BlkCaseObj.linkBipGraph_isSemiregular`,
`Babai.BlkCaseObj.linkBipGraph_not_isTrivial`). -/
theorem exists_mem_nbhd_of_sizes (X : BlkDesignObj s) {A : Set ↥s} {C : Set (Set ↥s)}
    (hA : A ⊆ {x : ↥s | X.part₁ x}) (hC : C ⊆ X.blocks)
    (hsizes : 1 < (A.ncard : ℚ) / (X.n₁ : ℚ) + (C.ncard : ℚ) / (X.n₂ : ℚ)) :
    ∃ x ∈ A, ∃ B ∈ C, B ∈ X.nbhd x := by
  classical
  letI : Fintype ↥{x : ↥s | X.part₁ x} := Fintype.ofFinite _
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  letI : DecidableEq ↥{x : ↥s | X.part₁ x} := Classical.decEq _
  letI : DecidableEq ↥X.blocks := Classical.decEq _
  set A₁ : Set ↥{x : ↥s | X.part₁ x} := {a | (a : ↥s) ∈ A} with hA₁
  set C₁ : Set ↥X.blocks := {b | ((b : Set ↥s)) ∈ C} with hC₁
  have hcardA : Fintype.card ↥{x : ↥s | X.part₁ x} = X.n₁ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hcardB : Fintype.card ↥X.blocks = X.n₂ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hA₁card : A₁.ncard = A.ncard := by
    have himg : Subtype.val '' A₁ = A := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨⟨x, hA hx⟩, hx, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hC₁card : C₁.ncard = C.ncard := by
    have himg : Subtype.val '' C₁ = C := by
      ext B
      constructor
      · rintro ⟨b, hb, rfl⟩; exact hb
      · intro hB; exact ⟨⟨B, hC hB⟩, hB, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hnt := case_9_7_2 X.linkBipGraph X.linkBipGraph_isSemiregular
    X.linkBipGraph_not_isTrivial A₁ C₁ (by rw [hA₁card, hC₁card, hcardA, hcardB]; exact hsizes)
  by_contra hcon
  push_neg at hcon
  refine hnt (Or.inl ?_)
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨a, b⟩ hab
  exact hcon (a : ↥s) a.2 ((b : ↥X.blocks) : Set ↥s) b.2 hab

/-- §9.7, Case 2.  ***"`X*` cannot be trivial"***, the non-edge half: some point of `A`
misses some block of `C`.  See `Babai.BlkCaseObj.exists_mem_nbhd_of_sizes`. -/
theorem exists_notMem_nbhd_of_sizes (X : BlkDesignObj s) {A : Set ↥s} {C : Set (Set ↥s)}
    (hA : A ⊆ {x : ↥s | X.part₁ x}) (hC : C ⊆ X.blocks)
    (hsizes : 1 < (A.ncard : ℚ) / (X.n₁ : ℚ) + (C.ncard : ℚ) / (X.n₂ : ℚ)) :
    ∃ x ∈ A, ∃ B ∈ C, B ∉ X.nbhd x := by
  classical
  letI : Fintype ↥{x : ↥s | X.part₁ x} := Fintype.ofFinite _
  letI : Fintype ↥X.blocks := Fintype.ofFinite _
  letI : DecidableEq ↥{x : ↥s | X.part₁ x} := Classical.decEq _
  letI : DecidableEq ↥X.blocks := Classical.decEq _
  set A₁ : Set ↥{x : ↥s | X.part₁ x} := {a | (a : ↥s) ∈ A} with hA₁
  set C₁ : Set ↥X.blocks := {b | ((b : Set ↥s)) ∈ C} with hC₁
  have hcardA : Fintype.card ↥{x : ↥s | X.part₁ x} = X.n₁ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hcardB : Fintype.card ↥X.blocks = X.n₂ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; rfl
  have hA₁card : A₁.ncard = A.ncard := by
    have himg : Subtype.val '' A₁ = A := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx; exact ⟨⟨x, hA hx⟩, hx, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hC₁card : C₁.ncard = C.ncard := by
    have himg : Subtype.val '' C₁ = C := by
      ext B
      constructor
      · rintro ⟨b, hb, rfl⟩; exact hb
      · intro hB; exact ⟨⟨B, hC hB⟩, hB, rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hnt := case_9_7_2 X.linkBipGraph X.linkBipGraph_isSemiregular
    X.linkBipGraph_not_isTrivial A₁ C₁ (by rw [hA₁card, hC₁card, hcardA, hcardB]; exact hsizes)
  by_contra hcon
  push_neg at hcon
  refine hnt (Or.inr ?_)
  rw [Set.eq_univ_iff_forall]
  rintro ⟨a, b⟩
  exact hcon (a : ↥s) a.2 ((b : ↥X.blocks) : Set ↥s) b.2

end BlkCaseObj

end Babai
