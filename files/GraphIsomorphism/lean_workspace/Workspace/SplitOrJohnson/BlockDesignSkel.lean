/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.7, Case 3b: the `t`-skeleton of the neighborhood hypergraph `H`.
-/
import Workspace.SplitOrJohnson.BlockDesignHyper
import Workspace.SplitOrJohnson.BlockDesign
import Workspace.SplitOrJohnson.BlkRestrict

/-!
# §9.7, Case 3b  The `t`-skeleton of `H`

Version 2.5, lines 4295-4301.

*"Case 3b.  `d₁ > 7/3 log₂ n₁`.  Let `t = ⌈(7/4) log₂ n₁⌉`.  So `t ≤ (3/4)d₁`.  By
Lemma 2.5.12, the symmetry defect of the `t`-skeleton `H^{(t)}` of `H` is greater than
`1/4`.  Let us apply the Design lemma to `H^{(t)}`."*

Case 3a applies the Design Lemma to `H` itself, which
`Workspace/SplitOrJohnson/BlockDesignHyper.lean` prepares.  Case 3b applies it to the
`t`-skeleton instead, and this file checks the hypotheses of Lemma 2.5.12
(`Babai.Hypergraph.skeleton_defect`) and of Theorem 8.1.2 for it.

| Paper | Lean |
|---|---|
| *"`t = ⌈(7/4) log₂ n₁⌉`"* | `Babai.BlkCaseObj.tSkel` |
| *"`t ≤ (3/4)d₁`"*, relaxed to `t ≤ ⌈(3/4)d'⌉` | `Babai.BlkCaseObj.tSkel_le_ceil_d'` |
| *"`k ≤ n/2`"* of Theorem 8.1.2 for `t` | `Babai.BlkCaseObj.two_mul_tSkel_le_n₂` |
| *"`2 ≤ k`"* of Theorem 8.1.2 for `t` | `Babai.BlkCaseObj.two_le_tSkel` |
| `m ≤ n₁`, so *"`(7/4) log₂ m ≤ t`"* | `Babai.BlkCaseObj.nbhdHg_numEdges_le_n₁`, `Babai.BlkCaseObj.logb_numEdges_le_tSkel` |
| *"`H` is nontrivial"* (Lemma 2.5.12), from the negation of Case 1 | `Babai.BlkCaseObj.nbhdHg_not_trivialUniform` |

The file also makes the skeleton a **functor** of the input
(`Babai.BlkCaseObj.map_skelStruct`) and packs the whole call as
`Babai.case3bSetup : Babai.BlkDesignSetup Ω N` on the fiber `Babai.Case3bFiber` of
`t = N`, which is what `Babai.blkDesign_fiber` runs.
-/

namespace Babai

namespace BlkCaseObj

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
  {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-! ### The number of hyperedges of `H` -/

/-- The hyperedges of `H`, read on `Babai.BlkCaseObj.blkAmb`, are the members of
`Babai.BlkCaseObj.edgeFam` read there. -/
theorem coe_edgeFinsetFam (X : BlkCaseObj s Case) :
    (↑X.edgeFinsetFam : Set (Finset ↥X.blkAmb)) = X.toBlkFinset '' X.edgeFam := by
  ext F
  simp only [Finset.mem_coe, X.mem_edgeFinsetFam, Set.mem_image]
  exact ⟨fun ⟨S, hS, hFS⟩ => ⟨S, hS, hFS.symm⟩, fun ⟨S, hS, hFS⟩ => ⟨S, hS, hFS.symm⟩⟩

/-- *"`H` has no multiple edges"*: the number of hyperedges is the number of
neighborhoods. -/
theorem card_edgeFinsetFam (X : BlkCaseObj s Case) :
    X.edgeFinsetFam.card = X.edgeFam.ncard := by
  classical
  have h : (↑X.edgeFinsetFam : Set (Finset ↥X.blkAmb)).ncard = X.edgeFam.ncard := by
    rw [coe_edgeFinsetFam]
    refine Set.ncard_image_of_injOn (fun S hS T hT hST => ?_)
    exact X.toBlkFinset_injOn (X.edgeFam_subset_blocks hS) (X.edgeFam_subset_blocks hT) hST
  rwa [Set.ncard_coe_finset] at h

/-- `m ≤ n₁`: a hyperedge of `H` is the neighborhood of a point of `V₁`.  (There are
exactly `n₁` of them, because there are no twins in `V₁`, but only the bound is used.) -/
theorem card_edgeFinsetFam_le_n₁ (X : BlkCaseObj s Case) : X.edgeFinsetFam.card ≤ X.n₁ := by
  rw [card_edgeFinsetFam]
  have himg : X.edgeFam = X.nbhd '' {x | X.part₁ x} := by
    ext S
    exact ⟨fun ⟨x, hx, hS⟩ => ⟨x, hx, hS⟩, fun ⟨x, hx, hS⟩ => ⟨x, hx, hS⟩⟩
  rw [himg]
  exact Set.ncard_image_le (Set.toFinite _)

/-- `m ≤ n₁` for the hypergraph handed to Lemma 2.5.12.  Complementing does not change the
number of hyperedges. -/
theorem nbhdHg_numEdges_le_n₁ (X : BlkDesignObj s) : X.nbhdHg.numEdges ≤ X.n₁ := by
  have h := X.card_edgeFinsetFam_le_n₁
  rw [nbhdHg]
  split_ifs
  · exact h
  · exact h

/-! ### *"`H` is nontrivial"* -/

/-- Lemma 2.5.12's hypothesis *"`H` is nontrivial"*, from the negation of Case 1.  By
Obs. 2.5.5 (`Babai.Hypergraph.isTrivialUniform_iff_aut_top`) a trivial uniform hypergraph
has `Aut(H) = S(V₂)`, and then every pair of blocks is a pair of `H`-twins
(`Babai.BlkCaseObj.mem_aut_swap_iff_isHTwin`), which is Case 1. -/
theorem nbhdHg_not_trivialUniform (X : BlkDesignObj s) (h1 : ¬ X.IsCase1) :
    ¬ X.nbhdHg.IsTrivialUniform X.d' := by
  intro htriv
  have htop : X.nbhdHg.Aut = ⊤ :=
    (Hypergraph.isTrivialUniform_iff_aut_top X.nbhdHg_isSimple X.nbhdHg_isUniform).1 htriv
  refine h1 fun B hB B' hB' => (X.mem_aut_swap_iff_isHTwin hB hB').1 ?_
  rw [htop]
  trivial

/-! ### `t = ⌈(7/4) log₂ n₁⌉` -/

/-- §9.7, Case 3b.  *"Let `t = ⌈(7/4) log₂ n₁⌉`."*  This is the rank at which the Design
Lemma is applied in Case 3b, and the exponent of the multiplicative cost `n₂^t`. -/
noncomputable def tSkel (X : BlkCaseObj s Case) : ℕ := ⌈7 / 4 * Real.logb 2 (X.n₁ : ℝ)⌉₊

theorem two_le_logb_n₁ (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) :
    (2 : ℝ) ≤ Real.logb 2 (X.n₁ : ℝ) := by
  have h5 : 5 ≤ X.n₁ := X.five_le_n₁ hlt
  have h4 : (4 : ℝ) ≤ (X.n₁ : ℝ) := by exact_mod_cast (by omega : 4 ≤ X.n₁)
  have hlog : Real.logb 2 (4 : ℝ) ≤ Real.logb 2 (X.n₁ : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) h4
  have h4log : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  linarith [h4log ▸ hlog]

theorem logb_n₁_nonneg (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) :
    (0 : ℝ) ≤ Real.logb 2 (X.n₁ : ℝ) := le_trans (by norm_num) (X.two_le_logb_n₁ hlt)

/-- Lemma 2.5.12's hypothesis *"`(7/4) log₂ m ≤ t`"*: the number `m` of hyperedges of `H`
is at most `n₁` (`Babai.BlkCaseObj.nbhdHg_numEdges_le_n₁`), and `t` is the ceiling of
`(7/4) log₂ n₁`. -/
theorem logb_numEdges_le_tSkel (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) :
    (7 / 4 : ℝ) * Real.logb 2 (X.nbhdHg.numEdges : ℝ) ≤ X.tSkel := by
  have hm : ((X.nbhdHg.numEdges : ℕ) : ℝ) ≤ (X.n₁ : ℝ) := by
    exact_mod_cast X.nbhdHg_numEdges_le_n₁
  have hnn : (0 : ℝ) ≤ ((X.nbhdHg.numEdges : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlog : Real.logb 2 (X.nbhdHg.numEdges : ℝ) ≤ Real.logb 2 (X.n₁ : ℝ) := by
    rcases eq_or_lt_of_le hnn with h0 | h0
    · rw [← h0, Real.logb_zero]
      exact X.logb_n₁_nonneg hlt
    · exact Real.logb_le_logb_of_le (by norm_num) h0 hm
  have hceil : (7 / 4 : ℝ) * Real.logb 2 (X.n₁ : ℝ) ≤ X.tSkel := Nat.le_ceil _
  linarith

/-- §9.7, Case 3b.  *"`2 ≤ k`"* of Theorem 8.1.2 at the rank `t`: `n₁ ≥ 5`, so
`log₂ n₁ ≥ 2` and `t ≥ ⌈7/2⌉ = 4`. -/
theorem two_le_tSkel (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) : 2 ≤ X.tSkel := by
  have h : (2 : ℝ) ≤ 7 / 4 * Real.logb 2 (X.n₁ : ℝ) := by
    have := X.two_le_logb_n₁ hlt
    linarith
  have hle : (2 : ℝ) ≤ (X.tSkel : ℝ) := le_trans h (Nat.le_ceil _)
  exact_mod_cast hle

/-- §9.7, Case 3b.  *"So `t ≤ (3/4)d₁`"*, in the relaxed form `t ≤ ⌈(3/4)d'⌉` that
Lemma 2.5.12 is proved with (`Babai.case_9_7_3b_t_le`, entry 42 of the corrected paper), at
the rank `d'` at which `H` is taken. -/
theorem tSkel_le_ceil_d' (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h3a : ¬ X.IsCase3a) :
    X.tSkel ≤ ⌈3 / 4 * (X.d' : ℝ)⌉₊ :=
  (case_9_7_3b_t_le (Real.logb 2 (X.n₁ : ℝ)) (X.logb_n₁_nonneg hlt) X.d'
    (lt_of_not_ge (fun h => h3a h))).1

/-- The upper bound on `t` that keeps the cost `n₂^t` of the Design Lemma call
quasipolynomial: `t < (7/4) log₂ n₁ + 1`. -/
theorem tSkel_lt (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h3a : ¬ X.IsCase3a) :
    ((X.tSkel : ℕ) : ℝ) < 7 / 4 * Real.logb 2 (X.n₁ : ℝ) + 1 :=
  (case_9_7_3b_t_le (Real.logb 2 (X.n₁ : ℝ)) (X.logb_n₁_nonneg hlt) X.d'
    (lt_of_not_ge (fun h => h3a h))).2

/-- In Case 3b the rank is at least `5`: `d' > (7/3) log₂ n₁ ≥ 14/3`. -/
theorem five_le_d' (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h3a : ¬ X.IsCase3a) :
    5 ≤ X.d' := by
  have h : 7 / 3 * Real.logb 2 (X.n₁ : ℝ) < (X.d' : ℝ) := lt_of_not_ge (fun h => h3a h)
  have h2 := X.two_le_logb_n₁ hlt
  have hd : (14 / 3 : ℝ) < (X.d' : ℝ) := by linarith
  have : (4 : ℝ) < (X.d' : ℝ) := by linarith
  have h4 : 4 < X.d' := by exact_mod_cast this
  omega

/-- §9.7, Case 3b.  *"`k ≤ n/2`"* of Theorem 8.1.2 at the rank `t`: `4t ≤ 3d' + 3` by
`Babai.BlkCaseObj.tSkel_le_ceil_d'`, `d' ≥ 5` in Case 3b
(`Babai.BlkCaseObj.five_le_d'`), and `2d' ≤ n₂`
(`Babai.BlkCaseObj.two_mul_d'_le_n₂`). -/
theorem two_mul_tSkel_le_n₂ (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h3a : ¬ X.IsCase3a) :
    2 * X.tSkel ≤ X.n₂ := by
  have ht := X.tSkel_le_ceil_d' hlt h3a
  have hceil : ((⌈3 / 4 * (X.d' : ℝ)⌉₊ : ℕ) : ℝ) < 3 / 4 * (X.d' : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h4 : 4 * ⌈3 / 4 * (X.d' : ℝ)⌉₊ ≤ 3 * X.d' + 3 := by
    have hlt' : (4 : ℝ) * (⌈3 / 4 * (X.d' : ℝ)⌉₊ : ℕ) < 3 * (X.d' : ℝ) + 4 := by linarith
    have : (4 * ⌈3 / 4 * (X.d' : ℝ)⌉₊ : ℝ) < ((3 * X.d' + 4 : ℕ) : ℝ) := by push_cast; linarith
    have hn : 4 * ⌈3 / 4 * (X.d' : ℝ)⌉₊ < 3 * X.d' + 4 := by exact_mod_cast this
    omega
  have h5 := X.five_le_d' hlt h3a
  have hn₂ := X.two_mul_d'_le_n₂
  omega

end BlkCaseObj

/-! ### `H` is regular

Lemma 2.5.12 asks for a **regular** hypergraph, which §9.7 does not check.  `H` is regular
because the bipartite graph `X = (V₁, V₂; Rᵢ)` is semiregular (Cor. 3.4.9): the degree of a
block `B` in `H` is the number of points of `V₁` whose neighborhood contains `B`, that is
the in-degree of `B` in the constituent `Babai.BlkCaseObj.linkColor`, and by Obs. 3.3.5
(degree awareness, `Babai.PartitionStructure.inDegC_eq_of_vcolor_eq`) that in-degree
depends only on the vertex color of `B`, which is the same for all blocks.

This is the mirror image of `Babai.BlkCaseObj.nbhd_ncard_uniform`, which is the same
statement for the out-degrees and gives *"`H` is uniform of rank `d₁`"*. -/

namespace BipCaseData

variable {V : Type} {c : V → V → ℕ} {V₁ V₂ : Set V} (D : BipCaseData c V₁ V₂)

include D

/-- Observation 3.3.5, for the in-degrees: two vertices of the same part have the same
number of in-neighbors in each color.  This is
`Babai.BipCaseData.ncard_nbhd_eq` on the other side. -/
theorem ncard_inNbhd_eq [Finite V] {x u : V} (hxu : D.P.vcolor x = D.P.vcolor u) (k : ℕ) :
    {y | c y x = k}.ncard = {y | c y u = k}.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hset : ∀ w : V, {y | c y w = k} = {y | D.P.natColor y w = k} := by
    intro w; ext y; simp only [Set.mem_setOf_eq, D.color_val y w]; exact Iff.rfl
  rw [hset x, hset u]
  by_cases hk : k < D.P.rank
  · have hcast : ∀ w : V, {y | D.P.natColor y w = k} = {y | D.P.color y w = ⟨k, hk⟩} := by
      intro w; ext y; exact D.P.natColor_eq_iff_color_eq hk y w
    rw [hcast x, hcast u, ← PartitionStructure.inDegC_eq_ncard,
      ← PartitionStructure.inDegC_eq_ncard]
    exact D.P.inDegC_eq_of_vcolor_eq D.isCoherent _ hxu
  · rw [D.P.setOf_natColor_left_eq_empty hk, D.P.setOf_natColor_left_eq_empty hk]

end BipCaseData

namespace Hypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The degree of a vertex of `Babai.Hypergraph.ofFinsetSet`: the number of members of the
family that contain it. -/
theorem degree_ofFinsetSet (E : Finset (Finset V)) (x : V) :
    (ofFinsetSet E).degree x = (E.filter fun A => x ∈ A).card := by
  classical
  refine Finset.card_bij (fun i _ => ((E.equivFin.symm i : {A // A ∈ E}) : Finset V))
    (fun i hi => ?_) (fun i _ j _ hij => ?_) (fun A hA => ?_)
  · rw [Finset.mem_filter] at hi ⊢
    exact ⟨(E.equivFin.symm i).2, hi.2⟩
  · exact E.equivFin.symm.injective (Subtype.ext hij)
  · rw [Finset.mem_filter] at hA
    refine ⟨E.equivFin ⟨A, hA.1⟩, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show x ∈ (ofFinsetSet E).edge (E.equivFin ⟨A, hA.1⟩)
    simpa [ofFinsetSet] using hA.2

/-- The degree of a vertex in the complement: it lies in the complements of exactly the
hyperedges it does not lie in. -/
theorem degree_compl (H : Hypergraph V) (x : V) :
    (compl H).degree x = H.numEdges - H.degree x := by
  have h1 : (Finset.univ.filter fun i : Fin H.numEdges => x ∈ (compl H).edge i)
      = Finset.univ \ (Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i) := by
    ext i; simp [compl_edge]
  show (Finset.univ.filter fun i : Fin H.numEdges => x ∈ (compl H).edge i).card = _
  rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rfl

end Hypergraph

namespace BlkCaseObj

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
  {Case : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}

/-- The points of `V₁` whose neighborhood contains the block `B`: the in-neighborhood of
`B` in the constituent `Babai.BlkCaseObj.linkColor`. -/
def inNbhd (X : BlkCaseObj s Case) (B : Set ↥s) : Set ↥s :=
  {x | X.part₁ x ∧ B ∈ X.nbhd x}

/-- The in-neighborhood of a block, read on the vertex set of the configuration. -/
theorem val_image_setOf_vc_eq_inNbhd (X : BlkDesignObj s) {B : Set ↥s}
    (hB : B ∈ X.blocks) :
    Subtype.val '' {u : ↥X.vtxSet | X.vc u (X.vtxBlk hB) = X.linkColor}
      = (fun x : ↥s => ({x} : Set ↥s)) '' X.inNbhd B := by
  obtain ⟨x₀, hx₀, B₀, hB₀, hcol₀⟩ := X.hasLinkColor_linkColor
  ext A
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : X.vc u (X.vtxBlk hB) = X.linkColor := hu
    have heq : X.vc u (X.vtxBlk hB) = X.vc (X.vtxPt hx₀) (X.vtxBlk hB₀) := by
      rw [hu']; exact hcol₀.symm
    have hmem₁ : (u : Set ↥s) ∈ X.sglSet :=
      (X.bipData.tail_mem_part₁_iff heq).2 (X.vtxPt_mem₁ hx₀)
    obtain ⟨x, hx, hxu⟩ := hmem₁
    refine ⟨x, ⟨hx, hB, ?_⟩, hxu.symm⟩
    rw [← hxu]; exact hu'
  · rintro ⟨x, ⟨hx, -, hxc⟩, rfl⟩
    exact ⟨X.vtxPt hx, hxc, rfl⟩

/-- **`H` is regular**: the number of points of `V₁` whose neighborhood contains a given
block does not depend on the block.  This is Obs. 3.3.5 for the in-degrees
(`Babai.BipCaseData.ncard_inNbhd_eq`), at the constituent
`Babai.BlkCaseObj.linkColor`; all blocks are vertices of the same color. -/
theorem inNbhd_ncard_uniform (X : BlkDesignObj s) {B B' : Set ↥s} (hB : B ∈ X.blocks)
    (hB' : B' ∈ X.blocks) : (X.inNbhd B).ncard = (X.inNbhd B').ncard := by
  classical
  have hvc : X.bipData.P.vcolor (X.vtxBlk hB) = X.bipData.P.vcolor (X.vtxBlk hB') := by
    rw [(X.bipData.mem_part₂_iff _).1 (X.vtxBlk_mem₂ hB),
      (X.bipData.mem_part₂_iff _).1 (X.vtxBlk_mem₂ hB')]
  have h := X.bipData.ncard_inNbhd_eq hvc X.linkColor
  have himg : ∀ {C : Set ↥s} (hC : C ∈ X.blocks),
      {u : ↥X.vtxSet | X.vc u (X.vtxBlk hC) = X.linkColor}.ncard = (X.inNbhd C).ncard := by
    intro C hC
    have h1 : Subtype.val '' {u : ↥X.vtxSet | X.vc u (X.vtxBlk hC) = X.linkColor}
        = (fun x : ↥s => ({x} : Set ↥s)) '' X.inNbhd C :=
      X.val_image_setOf_vc_eq_inNbhd hC
    have h2 := congrArg Set.ncard h1
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_image_of_injective _ Set.singleton_injective] at h2
  rw [← himg hB, ← himg hB']
  exact h

/-- **Lemma 2.5.12's hypothesis *"`H` is regular"***, for the hypergraph of §9.7.  The
degree of a block is the number of points of `V₁` adjacent to it
(`Babai.BlkCaseObj.inNbhd_ncard_uniform`), and complementing turns a regular hypergraph
into a regular one. -/
theorem nbhdHg_isRegular (X : BlkDesignObj s) : ∃ r, X.nbhdHg.IsRegular r := by
  classical
  have hdeg : ∀ b : ↥X.blkAmb,
      (Hypergraph.ofFinsetSet X.edgeFinsetFam).degree b = (X.inNbhd (X.blkOf b)).ncard := by
    intro b
    rw [Hypergraph.degree_ofFinsetSet]
    have hcoe : (↑(X.edgeFinsetFam.filter fun A => b ∈ A) : Set (Finset ↥X.blkAmb))
        = X.toBlkFinset '' {S | S ∈ X.edgeFam ∧ X.blkOf b ∈ S} := by
      ext F
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image, X.mem_edgeFinsetFam]
      constructor
      · rintro ⟨⟨S, hS, rfl⟩, hb⟩
        exact ⟨S, ⟨hS, (X.mem_toBlkFinset S b).1 hb⟩, rfl⟩
      · rintro ⟨S, ⟨hS, hbS⟩, rfl⟩
        exact ⟨⟨S, hS, rfl⟩, (X.mem_toBlkFinset S b).2 hbS⟩
    have h1 : (X.edgeFinsetFam.filter fun A => b ∈ A).card
        = {S | S ∈ X.edgeFam ∧ X.blkOf b ∈ S}.ncard := by
      have h2 := congrArg Set.ncard hcoe
      rw [Set.ncard_coe_finset] at h2
      rw [h2]
      refine Set.ncard_image_of_injOn (fun S hS T hT hST => ?_)
      exact X.toBlkFinset_injOn (X.edgeFam_subset_blocks hS.1)
        (X.edgeFam_subset_blocks hT.1) hST
    have h3 : {S | S ∈ X.edgeFam ∧ X.blkOf b ∈ S} = X.nbhd '' X.inNbhd (X.blkOf b) := by
      ext S
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hbS⟩
        exact ⟨x, ⟨hx, hbS⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hbS⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hbS⟩
    rw [h1, h3]
    refine Set.ncard_image_of_injOn (fun x hx y hy hxy => ?_)
    exact X.nbhd_injective hx.1 hy.1 hxy
  have hconst : ∀ b b' : ↥X.blkAmb,
      (Hypergraph.ofFinsetSet X.edgeFinsetFam).degree b
        = (Hypergraph.ofFinsetSet X.edgeFinsetFam).degree b' := by
    intro b b'
    rw [hdeg b, hdeg b']
    exact X.inNbhd_ncard_uniform (X.blkOf_mem b) (X.blkOf_mem b')
  rw [nbhdHg]
  split_ifs
  · by_cases hne : Nonempty ↥X.blkAmb
    · obtain ⟨b₀⟩ := hne
      exact ⟨_, fun b => hconst b b₀⟩
    · exact ⟨0, fun b => absurd ⟨b⟩ hne⟩
  · by_cases hne : Nonempty ↥X.blkAmb
    · obtain ⟨b₀⟩ := hne
      refine ⟨(Hypergraph.ofFinsetSet X.edgeFinsetFam).numEdges
        - (Hypergraph.ofFinsetSet X.edgeFinsetFam).degree b₀, fun b => ?_⟩
      rw [Hypergraph.degree_compl, hconst b b₀]
    · exact ⟨0, fun b => absurd ⟨b⟩ hne⟩

end BlkCaseObj

/-! ### The `t`-skeleton as an admissible input of Theorem 8.1.2 -/

namespace Hypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Definition 2.5.9.  The `t`-skeleton is `t`-uniform. -/
theorem skeleton_isUniform (H : Hypergraph V) (t : ℕ) : (H.skeleton t).IsUniform t :=
  fun i => ((mem_skeleton_edgeSet H t _).1 ⟨i, rfl⟩).1

/-- Definition 2.5.9.  Two hypergraphs whose edge sets correspond under a bijection `e` of
the vertex sets have `t`-skeletons whose edge sets correspond under `e`: a `t`-set is a
hyperedge of the skeleton exactly if it lies inside a hyperedge, and `e` carries the
hyperedges onto the hyperedges. -/
theorem mem_skeleton_edgeSet_image {W : Type*} [DecidableEq W] [Fintype W]
    (H : Hypergraph V) (K : Hypergraph W) (t : ℕ) (e : V ≃ W)
    (h : ∀ F : Finset V, F.image e ∈ K.edgeSet ↔ F ∈ H.edgeSet) (F : Finset V) :
    F.image e ∈ (K.skeleton t).edgeSet ↔ F ∈ (H.skeleton t).edgeSet := by
  classical
  rw [mem_skeleton_edgeSet, mem_skeleton_edgeSet,
    Finset.card_image_of_injective _ e.injective]
  refine and_congr Iff.rfl ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · have himg : ((K.edge i).image e.symm).image e = K.edge i := by
      rw [Finset.image_image, show ((e : V → W) ∘ (e.symm : W → V)) = id from
        funext fun x => e.apply_symm_apply x, Finset.image_id]
    have hmem : ((K.edge i).image e.symm).image e ∈ K.edgeSet := by
      rw [himg]; exact ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (h ((K.edge i).image e.symm)).1 hmem
    refine ⟨j, ?_⟩
    rw [hj]
    intro x hx
    exact Finset.mem_image.2 ⟨e x, hi (Finset.mem_image_of_mem _ hx), e.symm_apply_apply x⟩
  · obtain ⟨j, hj⟩ := (h (H.edge i)).2 ⟨i, rfl⟩
    refine ⟨j, ?_⟩
    rw [hj]
    exact Finset.image_subset_image hi

end Hypergraph

namespace BlkCaseObj

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}

/-- §9.7, Case 3b.  **Lemma 2.5.12 for the input of §9.7**: *"the symmetry defect of the
`t`-skeleton `H^{(t)}` of `H` is greater than `1/4`"*.  The six hypotheses of
`Babai.Hypergraph.skeleton_defect` are `Babai.BlkCaseObj.nbhdHg_isSimple`,
`Babai.BlkCaseObj.nbhdHg_not_trivialUniform` (the negation of Case 1),
`Babai.BlkCaseObj.nbhdHg_isRegular`, `Babai.BlkCaseObj.nbhdHg_isUniform`,
`Babai.BlkCaseObj.two_mul_d'_le_n₂`, `Babai.BlkCaseObj.logb_numEdges_le_tSkel` and
`Babai.BlkCaseObj.tSkel_le_ceil_d'`. -/
theorem skeleton_defect_nbhdHg (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1)
    (h3a : ¬ X.IsCase3a) : 1 / 4 < (X.nbhdHg.skeleton X.tSkel).defect := by
  obtain ⟨r, hr⟩ := X.nbhdHg_isRegular
  refine Hypergraph.skeleton_defect X.nbhdHg_isSimple (X.nbhdHg_not_trivialUniform h1) hr
    X.nbhdHg_isUniform ?_ (X.logb_numEdges_le_tSkel hlt) (X.tSkel_le_ceil_d' hlt h3a)
  rw [X.card_blkAmb]
  exact X.two_mul_d'_le_n₂

/-- §9.7, Case 3b.  *"Let us apply the Design lemma to `H^{(t)}`"*: the `t`-skeleton, viewed
as a `t`-ary relational structure (§2.5.1, `Babai.Hypergraph.toRelStructureSimple`). -/
noncomputable def skelStruct (X : BlkDesignObj s) (N : ℕ) : RelStructure ↥X.blkAmb :=
  (X.nbhdHg.skeleton X.tSkel).toRelStructureSimple N

theorem skelStruct_isKAry (X : BlkDesignObj s) (N : ℕ) : (X.skelStruct N).IsKAry N :=
  fun _ => rfl

/-- §2.5.1: viewing the skeleton as a relational structure changes no automorphism. -/
theorem aut_skelStruct (X : BlkDesignObj s) {N : ℕ} (hN : X.tSkel = N) :
    (X.skelStruct N).Aut = (X.nbhdHg.skeleton X.tSkel).Aut := by
  subst hN
  exact Hypergraph.aut_toRelStructureSimple (Hypergraph.skeleton_isSimple _ _)
    (Hypergraph.skeleton_isUniform _ _)

/-- §9.7, Case 3b.  **The `t`-skeleton as an admissible input of Theorem 8.1.2** at the
rank `N = t` and the threshold `3/4`: `2 ≤ t` (`Babai.BlkCaseObj.two_le_tSkel`), `2t ≤ n₂`
(`Babai.BlkCaseObj.two_mul_tSkel_le_n₂` — the hypothesis §9.7 skips here too) and the
symmetry defect `≥ 1 − 3/4 = 1/4`, which Lemma 2.5.12 gives as `> 1/4`
(`Babai.BlkCaseObj.skeleton_defect_nbhdHg`). -/
noncomputable def skelDesignObj (X : BlkDesignObj s) (hlt : X.n₂ < X.n₁) (h1 : ¬ X.IsCase1)
    (h3a : ¬ X.IsCase3a) {N : ℕ} (hN : X.tSkel = N) :
    (DesignInputs (Set Ω) N (3 / 4)).Obj X.blkAmb :=
  ⟨⟨X.skelStruct N, X.skelStruct_isKAry N⟩, by
    refine ⟨hN ▸ X.two_le_tSkel hlt, ?_, ?_⟩
    · rw [X.ncard_blkAmb, ← hN]; exact X.two_mul_tSkel_le_n₂ hlt h3a
    · have hdef : (1 : ℚ) / 4 < structDefect (X.skelStruct N) := by
        show (1 : ℚ) / 4 < Babai.defect (X.skelStruct N).Aut
        rw [X.aut_skelStruct hN]
        exact X.skeleton_defect_nbhdHg hlt h1 h3a
      have hdef' : ((1 : ℚ) / 4 : ℝ) ≤ ((structDefect (X.skelStruct N) : ℚ) : ℝ) := by
        exact_mod_cast le_of_lt hdef
      push_cast at hdef' ⊢
      linarith⟩

end BlkCaseObj

/-! ### The transport along a morphism of §9.7, and the fiber of Case 3b -/

namespace BlkCaseObj

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s t : Set Ω}
  {Cs : (Set ↥s → Set ↥s → ℕ) → Set (Set ↥s) → Set (Set ↥s) → Prop}
  {Ct : (Set ↥t → Set ↥t → ℕ) → Set (Set ↥t) → Set (Set ↥t) → Prop}

/-- `t = ⌈(7/4) log₂ n₁⌉` is an isomorphism invariant: it is read off `n₁`. -/
theorem IsMorphOn.tSkel_eq {X : BlkCaseObj s Cs} {Y : BlkCaseObj t Ct} {φ : ↥s ≃ ↥t}
    (h : X.IsMorphOn Y φ) : Y.tSkel = X.tSkel := by
  rw [tSkel, tSkel, h.n₁_eq]

variable {X : BlkDesignObj s} {Y : BlkDesignObj t} {φ : ↥s ≃ ↥t}

/-- §9.7, Case 3b.  The hyperedges of the `t`-skeleton correspond under the bijection of
the vertex sets that a morphism of §9.7 induces: the hyperedges of `H` do
(`Babai.BlkCaseObj.nbhdHg_edgeSet_image`), `t` is an isomorphism invariant, and a `t`-set
lies inside a hyperedge exactly if its image does. -/
theorem skeleton_edgeSet_image (h : X.IsMorphOn Y φ) (F : Finset ↥X.blkAmb) :
    F.image (blkAmbEquiv h) ∈ (Y.nbhdHg.skeleton Y.tSkel).edgeSet ↔
      F ∈ (X.nbhdHg.skeleton X.tSkel).edgeSet := by
  rw [h.tSkel_eq]
  exact Hypergraph.mem_skeleton_edgeSet_image X.nbhdHg Y.nbhdHg X.tSkel (blkAmbEquiv h)
    (nbhdHg_edgeSet_image h) F

/-- §9.7, Case 3b.  The relational structure of the `t`-skeleton is carried to the
relational structure of the `t`-skeleton by the bijection of the vertex sets that a
morphism of §9.7 induces.  This is what makes the assignment *"input ↦ `H^{(t)}`"* a
functor. -/
theorem map_skelStruct (h : X.IsMorphOn Y φ) (N : ℕ) :
    (X.skelStruct N).map ((blkAmbEquiv h : ↥X.blkAmb ≃ ↥Y.blkAmb) : ↥X.blkAmb → ↥Y.blkAmb)
      = Y.skelStruct N :=
  Hypergraph.map_toRelStructureSimple (X.nbhdHg.skeleton X.tSkel)
    (Y.nbhdHg.skeleton Y.tSkel) N (blkAmbEquiv h) (skeleton_edgeSet_image h)

end BlkCaseObj

open BlkBlockDesignInputs in
/-- §9.7, Case 3b.  The inputs of Case 3b with `t = N`: the fiber of
`Babai.FindsAtMultCost.ofFibers` for the isomorphism invariant `t = ⌈(7/4) log₂ n₁⌉`. -/
abbrev Case3bFiber (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) : Cat.{0, 0} Ω :=
  ((((BlkBlockDesignInputs Ω).full (fun s X => ¬ Case1P s X)).full
    (fun s X => ¬ Case2P s X.1)).full (fun s X => ¬ Case3aP s X.1.1)).full
    (fun s X => (obj₀ ⟨s, X.1.1.1⟩).tSkel = N)

namespace Case3bFiber

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- The admissible input of §9.7 underlying an object of the fiber. -/
def bbd (Z : Pt (Case3bFiber Ω N)) : Pt (BlkBlockDesignInputs Ω) := ⟨Z.car, Z.obj.1.1.1.1⟩

/-- The object of §9.7 underlying an object of the fiber. -/
def obj (Z : Pt (Case3bFiber Ω N)) : BlkDesignObj Z.car :=
  BlkBlockDesignInputs.obj₀ (bbd Z)

theorem n₂_lt_n₁ (Z : Pt (Case3bFiber Ω N)) : (obj Z).n₂ < (obj Z).n₁ :=
  BlkBlockDesignInputs.numBlocks_lt_n₁ (bbd Z)

theorem not_isCase1 (Z : Pt (Case3bFiber Ω N)) : ¬ (obj Z).IsCase1 := Z.obj.1.1.1.2

theorem not_isCase3a (Z : Pt (Case3bFiber Ω N)) : ¬ (obj Z).IsCase3a := Z.obj.1.2

theorem tSkel_eq (Z : Pt (Case3bFiber Ω N)) : (obj Z).tSkel = N := Z.obj.2

/-- A morphism of the fiber is a morphism of the objects of §9.7. -/
theorem isMorphOn_of_hom {Z W : Pt (Case3bFiber Ω N)} (f : Hom (Case3bFiber Ω N) Z W) :
    (obj Z).IsMorphOn (obj W) f.1 :=
  BlkBlockDesignInputs.isMorphOn_of_iso (X := bbd Z) (Y := bbd W) f.2

end Case3bFiber

open BlkCaseObj in
/-- §9.7, Case 3b.  The Design Lemma call of Case 3b: the `t`-skeleton of `H`, at the rank
`t = N` (`Babai.BlkCaseObj.skelDesignObj`), carried along by
`Babai.BlkCaseObj.map_skelStruct`. -/
noncomputable def case3bSetup (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) :
    BlkDesignSetup Ω N where
  C := Case3bFiber Ω N
  bbd Z := Z.obj.1.1.1.1
  hbbd hf := hf
  dobj Z := (Case3bFiber.obj Z).skelDesignObj (Case3bFiber.n₂_lt_n₁ Z)
    (Case3bFiber.not_isCase1 Z) (Case3bFiber.not_isCase3a Z) (Case3bFiber.tSkel_eq Z)
  map_dobj f := map_skelStruct (Case3bFiber.isMorphOn_of_hom f) N
  n₂_lt_n₁ := Case3bFiber.n₂_lt_n₁

end Babai
