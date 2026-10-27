/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.4.5: Large clique lemma, Fisher's inequality.
-/
import Workspace.Coherent.Bipartite
import Workspace.Prelim.Hypergraphs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# §3.4.5 Large clique lemma

## Numbering map

| Paper | Lean |
|---|---|
| Lemma 3.4.25 | `Babai.PartitionStructure.large_clique_twinClass`, `.large_clique_links_trivial`, `.large_clique_defect` |
| Definition 3.4.26 | `Babai.Hypergraph.IsPossiblyDegenerateBIBD`, `.IsBIBD` |
| Theorem 3.4.27 | `Babai.Hypergraph.fisher` (paper's version), `Babai.Hypergraph.fisher_classical` (classical version, proved) |
| Remark 3.4.28 | `Babai.Hypergraph.fisher` (covers the degenerate case) |
-/

namespace Babai

open scoped Matrix

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 3.4.26.  "A *possibly degenerate BIBD* with parameters `(v, b, r, k, λ)` is
an `r`-regular `k`-uniform hypergraph with `v` vertices and `b` not necessarily distinct
edges such that each pair of vertices belongs to exactly `λ` 'blocks' (edges) where
`k, r ≥ 1` and `k < v`; the latter is the 'incompleteness' condition." -/
structure IsPossiblyDegenerateBIBD (H : Hypergraph V) (v b r k lam : ℕ) : Prop where
  /-- "`v` vertices". -/
  card_vertices : Fintype.card V = v
  /-- "`b` not necessarily distinct edges". -/
  card_edges : H.numEdges = b
  /-- "`r`-regular". -/
  regular : H.IsRegular r
  /-- "`k`-uniform". -/
  uniform : H.IsUniform k
  /-- "each pair of vertices belongs to exactly `λ` blocks". -/
  pairwise : ∀ x y : V, x ≠ y →
    (Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i ∧ y ∈ H.edge i).card = lam
  /-- "`k ≥ 1`". -/
  k_pos : 1 ≤ k
  /-- "`r ≥ 1`". -/
  r_pos : 1 ≤ r
  /-- "`k < v`; the latter is the 'incompleteness' condition". -/
  incomplete : k < v

/-- Definition 3.4.26.  "A *BIBD* is a possibly degenerate BIBD satisfying `λ ≥ 1`." -/
structure IsBIBD (H : Hypergraph V) (v b r k lam : ℕ) : Prop
    extends IsPossiblyDegenerateBIBD H v b r k lam where
  /-- "`λ ≥ 1`". -/
  lam_pos : 1 ≤ lam

/-- Definition 3.4.26.  "Note that `v ≥ 1` (in fact, `v ≥ 2` because `v > k ≥ 1`)." -/
theorem two_le_v {H : Hypergraph V} {v b r k lam : ℕ}
    (h : H.IsPossiblyDegenerateBIBD v b r k lam) : 2 ≤ v := by
  have h1 := h.k_pos
  have h2 := h.incomplete
  omega

/-- Double counting of incidences: `∑_x deg(x) = ∑_i |Eᵢ|`. -/
theorem sum_degree_eq_sum_card (H : Hypergraph V) :
    (∑ x : V, H.degree x) = ∑ i : Fin H.numEdges, (H.edge i).card := by
  classical
  have h1 : ∀ x : V, H.degree x
      = ∑ i : Fin H.numEdges, if x ∈ H.edge i then 1 else 0 := by
    intro x
    rw [degree, Finset.card_filter]
  have h2 : ∀ i : Fin H.numEdges, (H.edge i).card
      = ∑ x : V, if x ∈ H.edge i then 1 else 0 := by
    intro i
    rw [Finset.card_eq_sum_ones (H.edge i)]
    rw [Finset.sum_ite_mem Finset.univ (H.edge i) (fun _ => 1)]
    simp [Finset.inter_eq_right.2 (Finset.subset_univ _)]
  simp only [h1, h2]
  exact Finset.sum_comm

/-- Definition 3.4.26.  "For a degenerate BIBD we have `λ = 0`, so each block is a
singleton, i.e. `k = 1` and therefore `b = rv ≥ v`." -/
theorem degenerate_k_eq_one {H : Hypergraph V} {v b r k : ℕ}
    (h : H.IsPossiblyDegenerateBIBD v b r k 0) : k = 1 := by
  classical
  by_contra hk
  have hk2 : 2 ≤ k := lt_of_le_of_ne h.k_pos (Ne.symm hk)
  -- `V` is nonempty, and every vertex has degree `r ≥ 1`, so some edge exists
  have hv : Nonempty V := by
    have h2 := two_le_v h
    rw [← h.card_vertices] at h2
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x⟩ := hv
  have hd : (Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i).card = r :=
    h.regular x
  obtain ⟨i, -⟩ : (Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i).Nonempty :=
    Finset.card_pos.1 (by rw [hd]; exact h.r_pos)
  -- that edge has at least two vertices, which then lie in no common block: contradiction
  have hcard : 2 ≤ (H.edge i).card := by rw [h.uniform i]; exact hk2
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 hcard
  have hp := h.pairwise y z hyz
  rw [Finset.card_eq_zero] at hp
  have hmem : i ∈ Finset.univ.filter
      fun i : Fin H.numEdges => y ∈ H.edge i ∧ z ∈ H.edge i := by
    simp [hy, hz]
  rw [hp] at hmem
  exact absurd hmem (Finset.notMem_empty i)

/-- In a BIBD every pair of vertices lies in at most as many blocks as a single vertex
does: `λ ≤ r`, and the inequality is strict.  (Equality would force every block through a
vertex `x` to contain every other vertex, i.e. to be the whole vertex set, contradicting
the incompleteness condition `k < v`.) -/
theorem lam_lt_r {H : Hypergraph V} {v b r k lam : ℕ} (h : H.IsBIBD v b r k lam) :
    lam < r := by
  classical
  have hv2 : 2 ≤ v := two_le_v h.toIsPossiblyDegenerateBIBD
  haveI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rw [h.card_vertices]; omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  set Sx := Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i with hSx
  set Sxy := Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i ∧ y ∈ H.edge i
    with hSxy
  have hsub : Sxy ⊆ Sx := by
    intro i hi
    simp only [hSxy, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.1
  have hcx : Sx.card = r := h.regular x
  have hcxy : Sxy.card = lam := h.pairwise x y hxy
  have hle : lam ≤ r := by
    rw [← hcx, ← hcxy]; exact Finset.card_le_card hsub
  rcases Nat.lt_or_ge lam r with hlt | hge
  · exact hlt
  -- `λ = r`: every block through `x` contains every other vertex, hence is all of `V`
  exfalso
  have heq : Sxy = Sx := Finset.eq_of_subset_of_card_le hsub (by omega)
  -- the same for every `y' ≠ x`
  have hall : ∀ y' : V, y' ≠ x → ∀ i : Fin H.numEdges, x ∈ H.edge i → y' ∈ H.edge i := by
    intro y' hy' i hi
    have hcy : (Finset.univ.filter
        fun i : Fin H.numEdges => x ∈ H.edge i ∧ y' ∈ H.edge i).card = lam :=
      h.pairwise x y' (Ne.symm hy')
    have hsub' : (Finset.univ.filter
        fun i : Fin H.numEdges => x ∈ H.edge i ∧ y' ∈ H.edge i) ⊆ Sx := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj.1
    have heq' : (Finset.univ.filter
        fun i : Fin H.numEdges => x ∈ H.edge i ∧ y' ∈ H.edge i) = Sx :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [hcx, hcy]; omega)
    have himem : i ∈ Sx := by
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
    rw [← heq'] at himem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at himem
    exact himem.2
  -- there is a block through `x` (`r ≥ 1`), and it is the whole vertex set
  obtain ⟨i₀, hi₀⟩ : Sx.Nonempty := Finset.card_pos.1 (by rw [hcx]; exact h.r_pos)
  simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hi₀
  have huniv : H.edge i₀ = Finset.univ := by
    refine Finset.eq_univ_of_forall fun z => ?_
    rcases eq_or_ne z x with rfl | hz
    · exact hi₀
    · exact hall z hz i₀ hi₀
  have hk : k = v := by
    have := h.uniform i₀
    rw [huniv, Finset.card_univ, h.card_vertices] at this
    exact this.symm
  exact absurd h.incomplete (by omega)

/-- Theorem 3.4.27 (Fisher's inequality), the classical statement that the paper recalls:
for a BIBD (so `λ ≥ 1`) with parameters `(v, b, r, k, λ)` we have `b ≥ v`.

The paper gives no reference key: "We recall Fisher's inequality for BIBDs (balanced
incomplete block designs)."  The classical statement allows repeated blocks, which is what
`Hypergraph` records (`b` counts a multiset of edges).

Proof (the standard linear-algebra argument).  Let `N` be the `v × b` incidence matrix
over `ℚ`, `N(x,i) = 1` if `x ∈ Eᵢ` and `0` otherwise.  Then `(N Nᵀ)(x,y)` is the number of
blocks containing both `x` and `y`, so `N Nᵀ = (r − λ)I + λJ`.  For every `z : V → ℚ`,
`zᵀ (N Nᵀ) z = (r − λ)∑ z(x)² + λ (∑ z(x))²`, and `r > λ` (`lam_lt_r`), so `N Nᵀ` sends no
nonzero vector to `0`; hence `det(N Nᵀ) ≠ 0` and `rank(N Nᵀ) = v`.  Since
`rank(N Nᵀ) ≤ rank N ≤ b`, we get `v ≤ b`. -/
theorem fisher_classical {H : Hypergraph V} {v b r k lam : ℕ}
    (h : H.IsBIBD v b r k lam) : v ≤ b := by
  classical
  have hlam : lam < r := lam_lt_r h
  -- the incidence matrix of the design
  set N : Matrix V (Fin H.numEdges) ℚ :=
    Matrix.of fun x i => if x ∈ H.edge i then (1 : ℚ) else 0 with hN
  set M : Matrix V V ℚ := N * Nᵀ with hM
  -- `(N Nᵀ)(x,y)` counts the blocks containing both `x` and `y`
  have hMentry : ∀ x y : V, M x y
      = ((Finset.univ.filter
          fun i : Fin H.numEdges => x ∈ H.edge i ∧ y ∈ H.edge i).card : ℚ) := by
    intro x y
    rw [hM, Matrix.mul_apply, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : x ∈ H.edge i <;> by_cases h2 : y ∈ H.edge i <;>
      simp [hN, Matrix.transpose_apply, h1, h2]
  have hMdiag : ∀ x : V, M x x = (r : ℚ) := by
    intro x
    rw [hMentry x x]
    have hfil : (Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i ∧ x ∈ H.edge i)
        = Finset.univ.filter fun i : Fin H.numEdges => x ∈ H.edge i :=
      Finset.filter_congr (fun i _ => by simp)
    rw [hfil]
    show ((H.degree x : ℕ) : ℚ) = (r : ℚ)
    rw [h.regular x]
  have hMoff : ∀ x y : V, x ≠ y → M x y = (lam : ℚ) := by
    intro x y hxy
    rw [hMentry x y, h.pairwise x y hxy]
  have hMeq : ∀ x y : V, M x y = ((r : ℚ) - lam) * (if x = y then 1 else 0) + lam := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [hMdiag, if_pos rfl]; ring
    · rw [hMoff x y hxy, if_neg hxy]; ring
  -- the quadratic form of `N Nᵀ`: `zᵀ (N Nᵀ) z = (r − λ)∑ z(x)² + λ (∑ z(x))²`
  have hquad : ∀ z : V → ℚ, z ⬝ᵥ M.mulVec z
      = ((r : ℚ) - lam) * (∑ x, z x ^ 2) + (lam : ℚ) * (∑ x, z x) ^ 2 := by
    intro z
    have hstep : z ⬝ᵥ M.mulVec z = ∑ x, ∑ y, z x * (M x y * z y) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    have hinner : ∀ x : V, (∑ y, z x * (M x y * z y))
        = ((r : ℚ) - lam) * z x ^ 2 + (lam : ℚ) * (z x * ∑ y, z y) := by
      intro x
      have key : ∀ y : V, z x * (M x y * z y)
          = ((r : ℚ) - lam) * (if x = y then z x * z y else 0) + (lam : ℚ) * (z x * z y) := by
        intro y
        rw [hMeq x y]
        by_cases hxy : x = y
        · rw [if_pos hxy, if_pos hxy]; ring
        · rw [if_neg hxy, if_neg hxy]; ring
      rw [Finset.sum_congr rfl fun y _ => key y, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_ite_eq Finset.univ x (fun y => z x * z y), if_pos (Finset.mem_univ x),
        ← Finset.mul_sum]
      ring
    rw [hstep, Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  -- `N Nᵀ` is nonsingular, because `r > λ`
  have hdet : M.det ≠ 0 := by
    intro hd
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have h0 : z ⬝ᵥ M.mulVec z = 0 := by rw [hz, dotProduct_zero]
    rw [hquad z] at h0
    have hrl : (0 : ℚ) < (r : ℚ) - lam := by
      have : (lam : ℚ) < r := by exact_mod_cast hlam
      linarith
    have hsq : (0 : ℚ) ≤ ∑ x, z x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
    have hlamnn : (0 : ℚ) ≤ (lam : ℚ) * (∑ x, z x) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hzero : (∑ x, z x ^ 2) = 0 := by nlinarith
    refine hz0 (funext fun x => ?_)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (z x))).1 hzero x
      (Finset.mem_univ x)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx
  -- `v = rank(N Nᵀ) ≤ rank N ≤ b`
  have hrankM : M.rank = Fintype.card V :=
    Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet))
  have hle1 : M.rank ≤ N.rank := by rw [hM]; exact Matrix.rank_mul_le_left N Nᵀ
  have hle2 : N.rank ≤ Fintype.card (Fin H.numEdges) := Matrix.rank_le_card_width N
  rw [Fintype.card_fin] at hle2
  rw [h.card_vertices] at hrankM
  have hb : H.numEdges = b := h.card_edges
  omega

/-- Theorem 3.4.27 (Fisher's inequality), the paper's version.  "For a possibly degenerate
BIBD with parameters `(v, b, r, k, λ)` we have `b ≥ v`."

The degenerate case is *not* part of the textbook statement; the paper extends it and
justifies the extension in the last sentence of Def. 3.4.26 ("For a degenerate BIBD we
have `λ = 0`, so each block is a singleton, i.e. `k = 1` and therefore `b = rv ≥ v`"),
which is carried out here. -/
theorem fisher {H : Hypergraph V} {v b r k lam : ℕ}
    (h : H.IsPossiblyDegenerateBIBD v b r k lam) : v ≤ b := by
  classical
  rcases Nat.eq_zero_or_pos lam with hlam | hlam
  · -- degenerate case: `k = 1`, hence `b = r·v ≥ v`
    subst hlam
    have hk : k = 1 := degenerate_k_eq_one h
    have hsum := H.sum_degree_eq_sum_card
    have hleft : (∑ _x : V, r) = Fintype.card V * r := by
      simp [Finset.card_univ, mul_comm]
    have hright : (∑ _i : Fin H.numEdges, 1) = H.numEdges := by simp
    rw [Finset.sum_congr rfl fun x _ => h.regular x, hleft,
      Finset.sum_congr rfl fun i _ => (h.uniform i).trans hk, hright] at hsum
    rw [h.card_vertices, h.card_edges] at hsum
    calc v = v * 1 := (mul_one v).symm
      _ ≤ v * r := Nat.mul_le_mul_left v h.r_pos
      _ = b := hsum
  · exact fisher_classical ⟨h, hlam⟩

end Hypergraph

/- Remark 3.4.28.  "Fisher's inequality is usually stated for BIBDs; however, as
mentioned above, the degenerate case also satisfies the conclusion."  This is the content
of `Babai.Hypergraph.fisher`, whose hypothesis admits the degenerate case (`λ = 0`), and of
its degenerate branch in the proof. -/

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω) [Fintype Ω] [DecidableEq Ω]

/-! ### The three steps of the proof of Lemma 3.4.25

`C = Ω₁` is the largest vertex-color class and induces a clique configuration.  The steps
are: (1) `C` is a clique with at least two vertices, (2) all links between `C` and the
other colors are trivial (the design argument, using Fisher's inequality), (3) `C` is a
twin equivalence class, and it is the largest one. -/

section LargeCliqueAux

/-- Step 1: `X[C]` is a clique configuration, so `C` has at least two vertices and all
pairs of distinct vertices of `C` have one and the same color `m`. -/
theorem clique_color (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2) :
    ∃ m : Fin X.rank, (∃ v ∈ X.vertexClass i₀, ∃ w ∈ X.vertexClass i₀, v ≠ w) ∧
      ∀ v ∈ X.vertexClass i₀, ∀ w ∈ X.vertexClass i₀, v ≠ w → X.color v w = m := by
  classical
  set Y := X.induced (X.vertexClass i₀) with hY
  have hYcfg : Y.IsConfiguration := X.induced_isConfiguration _ h.toIsConfiguration
  -- two distinct colors of `Y` are realized, so `C` has two distinct vertices
  have h0 : (0 : ℕ) < Y.rank := by rw [hclique]; norm_num
  have h1 : (1 : ℕ) < Y.rank := by rw [hclique]; norm_num
  obtain ⟨a, b, hab⟩ := Y.color_surjective ⟨0, h0⟩
  obtain ⟨a', b', hab'⟩ := Y.color_surjective ⟨1, h1⟩
  have hne : ∃ v ∈ X.vertexClass i₀, ∃ w ∈ X.vertexClass i₀, v ≠ w := by
    by_contra hcon
    push_neg at hcon
    have hsub : ∀ u v : X.vertexClass i₀, u = v := fun u v =>
      Subtype.ext (hcon (u : Ω) u.2 (v : Ω) v.2)
    have : Y.color a b = Y.color a' b' := by rw [hsub a a', hsub b b']
    rw [hab, hab'] at this
    exact absurd (congrArg Fin.val this) (by norm_num)
  obtain ⟨v₀, hv₀, w₀, hw₀, hv₀w₀⟩ := hne
  refine ⟨X.color v₀ w₀, ⟨v₀, hv₀, w₀, hw₀, hv₀w₀⟩, fun v hv w hw hvw => ?_⟩
  have := Y.color_eq_of_rank_two hYcfg hclique
    (x := ⟨v, hv⟩) (y := ⟨w, hw⟩) (u := ⟨v₀, hv₀⟩) (v := ⟨w₀, hw₀⟩)
    (fun hc => hvw (congrArg Subtype.val hc)) (fun hc => hv₀w₀ (congrArg Subtype.val hc))
  exact (X.induced_color_eq_iff _ ⟨v, hv⟩ ⟨w, hw⟩ ⟨v₀, hv₀⟩ ⟨w₀, hw₀⟩).1 this

/-- Step 2, the design argument.  "We need to prove that for all `x ∈ Ω \ C` and all
`y, z ∈ C` we have `c(x,y) = c(x,z)`."

Paper's proof: "For a contradiction assume this is false and let `ℓ` be a color and
`x ∈ Ω \ C` such that `c(x,y) = ℓ` for some but not all `y ∈ C`.  In other words,
`1 ≤ deg⁺_ℓ < |C|`. … the hypergraph `H = (C, {R_ℓ(u) | u ∈ B})` is `k`-uniform with
`k = deg⁺_ℓ` … `r`-regular with `r = deg⁺_{ℓ⁻}` … for `v, w ∈ C`, `v ≠ w` we have
`|B_v ∩ B_w| = p^m_{ℓ⁻,ℓ}` … hence `H` is a possibly degenerate BIBD with
`λ = p^m_{ℓ⁻,ℓ}`.  The number of vertices of this design is `|C|` and the number of (not
necessarily distinct) blocks is `|B|`.  Hence, by Fisher's inequality, `|C| ≤ |B|`, a
contradiction." -/
theorem link_color_const_right (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2)
    {x : Ω} (hx : x ∉ X.vertexClass i₀) {y z : Ω}
    (hy : y ∈ X.vertexClass i₀) (hz : z ∈ X.vertexClass i₀) :
    X.color x y = X.color x z := by
  classical
  by_contra hcon
  obtain ⟨m, -, hm⟩ := X.clique_color h i₀ hclique
  set C := X.vertexClass i₀ with hC
  set l := X.color x y with hl
  set j := X.vcolor x with hj
  set B := X.vertexClass j with hB
  have hxB : x ∈ B := rfl
  have hji : j ≠ i₀ := fun hc => hx (show X.vcolor x = i₀ by rw [← hc])
  -- `tail(ℓ) = j` and `head(ℓ) = i₀`
  have hltail : X.tailColor l = j := (X.vcolor_fst_eq h (k := l) rfl).symm
  have hlhead : X.headColor l = i₀ := by
    rw [← X.vcolor_snd_eq h (k := l) rfl]; exact hy
  -- every `R_ℓ`-neighbour lies in `C`, and every `R_ℓ`-in-neighbour lies in `B`
  have hnbrC : ∀ u w : Ω, X.color u w = l → w ∈ C := by
    intro u w hw
    show X.vcolor w = i₀
    rw [X.vcolor_snd_eq h hw, hlhead]
  have hnbrB : ∀ u w : Ω, X.color u w = l → u ∈ B := by
    intro u w hw
    show X.vcolor u = j
    rw [X.vcolor_fst_eq h hw, hltail]
  -- `k = deg⁺_ℓ`, with `1 ≤ k < |C|`
  set k := X.outDegOf l with hk
  have hdegx : X.outDegC l x = k := X.outDegC_eq_outDegOf h l (by rw [hltail]; rfl)
  have hkpos : 1 ≤ k := X.outDegOf_pos h l
  have hklt : k < C.ncard := by
    rw [← hdegx, outDegC_eq_ncard]
    refine lt_of_le_of_ne (Set.ncard_le_ncard (fun w hw => hnbrC x w hw) (Set.toFinite _)) ?_
    intro heq
    have hsub : X.nbr l x ⊆ C := fun w hw => hnbrC x w hw
    have : X.nbr l x = C := Set.eq_of_subset_of_ncard_le hsub (le_of_eq heq.symm)
      (Set.toFinite _)
    have hzn : z ∈ X.nbr l x := by rw [this]; exact hz
    exact hcon (show X.color x z = l from hzn).symm
  -- the design `H = (C, {R_ℓ(u) | u ∈ B})`
  set Bf : Finset Ω := Finset.univ.filter (fun u => u ∈ B) with hBf
  set e : Fin Bf.card ≃ Bf := Bf.equivFin.symm with he
  set H : Hypergraph (C : Set Ω) :=
    ⟨Bf.card, fun i => Finset.univ.filter (fun v : (C : Set Ω) => X.color (e i : Ω) (v : Ω) = l)⟩
    with hH
  have hBcard : Bf.card = B.ncard := by
    rw [hBf, ← Set.ncard_coe_finset]
    congr 1
    ext u
    simp [hB]
  have hedge : ∀ (i : Fin H.numEdges) (v : (C : Set Ω)),
      v ∈ H.edge i ↔ X.color (e i : Ω) (v : Ω) = l := by
    intro i v
    show v ∈ Finset.univ.filter (fun v : (C : Set Ω) => X.color (e i : Ω) (v : Ω) = l) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemB : ∀ u : Ω, u ∈ B → u ∈ Bf := by
    intro u hu
    simp only [hBf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hu
  have heB : ∀ i : Fin H.numEdges, (e i : Ω) ∈ B := by
    intro i
    have hi := (e i).2
    simp only [hBf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  -- `H` is `k`-uniform
  have huniform : H.IsUniform k := by
    intro i
    have himg : (H.edge i).image Subtype.val = (X.nbr l (e i : Ω)).toFinset := by
      ext w
      simp only [Finset.mem_image, Set.mem_toFinset, mem_nbr]
      constructor
      · rintro ⟨⟨u, hu⟩, hc, rfl⟩
        exact (hedge i ⟨u, hu⟩).1 hc
      · intro hw
        exact ⟨⟨w, hnbrC _ w hw⟩, (hedge i ⟨w, hnbrC _ w hw⟩).2 hw, rfl⟩
    have hcard := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ Subtype.val_injective, ← Set.ncard_eq_toFinset_card',
      ← outDegC_eq_ncard,
      X.outDegC_eq_outDegOf h l (show (e i : Ω) ∈ X.vertexClass (X.tailColor l) by
        rw [hltail]; exact heB i)] at hcard
    exact hcard
  have hregular : H.IsRegular (X.inDegOf l) := by
    intro v
    have himg : ((Finset.univ.filter fun i : Fin H.numEdges => v ∈ H.edge i).image
        fun i => (e i : Ω)) = {u : Ω | X.color u (v : Ω) = l}.toFinset := by
      ext u
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact (hedge i v).1 hi
      · intro hu
        refine ⟨e.symm ⟨u, hmemB u (hnbrB u (v : Ω) hu)⟩, ?_, ?_⟩
        · refine (hedge _ v).2 ?_
          simp only [he, Equiv.apply_symm_apply]
          exact hu
        · simp only [he, Equiv.apply_symm_apply]
    have hinj : Function.Injective fun i : Fin H.numEdges => (e i : Ω) := by
      intro s t hst
      exact e.injective (Subtype.ext hst)
    have hcard := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ hinj, ← Set.ncard_eq_toFinset_card',
      ← inDegC_eq_ncard, X.inDegC_eq_inDegOf h l (by rw [hlhead]; exact v.2)] at hcard
    exact hcard
  -- each pair of vertices of `C` lies in `λ = p^m_{ℓ⁻,ℓ}` blocks
  have hpairwise : ∀ v w : (C : Set Ω), v ≠ w →
      (Finset.univ.filter fun i : Fin H.numEdges => v ∈ H.edge i ∧ w ∈ H.edge i).card
        = X.interNum (X.conv l) l m := by
    intro v w hvw
    have hvwne : (v : Ω) ≠ (w : Ω) := fun hc => hvw (Subtype.ext hc)
    have himg : ((Finset.univ.filter fun i : Fin H.numEdges =>
        v ∈ H.edge i ∧ w ∈ H.edge i).image fun i => (e i : Ω))
        = {u : Ω | X.color (v : Ω) u = X.conv l ∧ X.color u (w : Ω) = l}.toFinset := by
      ext u
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
        exact ⟨(X.color_conv_iff h.toIsConfiguration l _ _).2 ((hedge i v).1 hi1),
          (hedge i w).1 hi2⟩
      · rintro ⟨h1, h2⟩
        have h1' : X.color u (v : Ω) = l := (X.color_conv_iff h.toIsConfiguration l u v).1 h1
        refine ⟨e.symm ⟨u, hmemB u (hnbrB u (v : Ω) h1')⟩, ⟨?_, ?_⟩, ?_⟩
        · refine (hedge _ v).2 ?_
          simp only [he, Equiv.apply_symm_apply]; exact h1'
        · refine (hedge _ w).2 ?_
          simp only [he, Equiv.apply_symm_apply]; exact h2
        · simp only [he, Equiv.apply_symm_apply]
    have hinj : Function.Injective fun i : Fin H.numEdges => (e i : Ω) := by
      intro s t hst
      exact e.injective (Subtype.ext hst)
    have hcard := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ hinj, ← Set.ncard_eq_toFinset_card',
      X.interNum_eq h (X.conv l) l (X.color (v : Ω) (w : Ω))
        (x := (v : Ω)) (y := (w : Ω)) rfl,
      hm (v : Ω) v.2 (w : Ω) w.2 hvwne] at hcard
    exact hcard
  -- `H` is a possibly degenerate BIBD, so Fisher's inequality applies
  have hcardV : Fintype.card (C : Set Ω) = C.ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hbibd : H.IsPossiblyDegenerateBIBD C.ncard B.ncard (X.inDegOf l) k
      (X.interNum (X.conv l) l m) :=
    { card_vertices := hcardV
      card_edges := hBcard
      regular := hregular
      uniform := huniform
      pairwise := fun v w hvw => hpairwise v w hvw
      k_pos := hkpos
      r_pos := X.inDegOf_pos h l
      incomplete := hklt }
  have hfisher := Hypergraph.fisher hbibd
  have hlt : B.ncard < C.ncard := hmax j hji
  omega

/-- Step 2, second half: the color of an edge from `Ω \ C` to `C` does not depend on the
tail either, as long as the tail keeps its vertex color.  (If two vertices `x, x'` of the
same vertex color had different colors to `C`, then `deg⁺_{c(x,y)}(x) = |C| > 0` while
`deg⁺_{c(x,y)}(x') = 0`, contradicting degree awareness, Obs. 3.3.5.) -/
theorem link_color_const (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2)
    {x x' : Ω} (hvc : X.vcolor x = X.vcolor x')
    (hx : x ∉ X.vertexClass i₀) (hx' : x' ∉ X.vertexClass i₀)
    {y y' : Ω} (hy : y ∈ X.vertexClass i₀) (hy' : y' ∈ X.vertexClass i₀) :
    X.color x y = X.color x' y' := by
  classical
  set C := X.vertexClass i₀ with hC
  set l := X.color x y with hl
  by_contra hne
  have hxl : ∀ w ∈ C, X.color x w = l :=
    fun w hw => (X.link_color_const_right h i₀ hmax hclique hx hy hw).symm
  have hx'l : ∀ w ∈ C, X.color x' w = X.color x' y' :=
    fun w hw => (X.link_color_const_right h i₀ hmax hclique hx' hy' hw).symm
  -- every `R_ℓ`-neighbour lies in `C`
  have hhead : X.headColor l = i₀ := by
    rw [← X.vcolor_snd_eq h (k := l) rfl]; exact hy
  have hsub : X.nbr l x' ⊆ C := by
    intro w hw
    show X.vcolor w = i₀
    rw [X.vcolor_snd_eq h (show X.color x' w = l from hw), hhead]
  have hempty : X.nbr l x' = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    exact hne (((hx'l w (hsub hw)).symm.trans (show X.color x' w = l from hw)).symm)
  have h0 : X.outDegC l x' = 0 := by
    rw [outDegC_eq_ncard, hempty, Set.ncard_empty]
  have hpos : 0 < X.outDegC l x := by
    rw [outDegC_eq_ncard]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨y, hxl y hy⟩
  rw [X.outDegC_eq_of_vcolor_eq h l hvc, h0] at hpos
  exact absurd hpos (lt_irrefl 0)

end LargeCliqueAux

/-- Lemma 3.4.25 (Large clique lemma).  "Let `X = (Ω, c)` be a coherent configuration.
Let `Ω₁, …, Ω_s` be the vertex-color classes.  Assume `|Ω₁| > |Ωᵢ|` for all `i ≥ 2` and
`Ω₁` induces a clique configuration in `X`.  Then `Ω₁` is a twin equivalence class
in `X`."

Paper's proof: "Let `C = Ω₁`.  First we prove that all links between `C` and the other
colors is trivial.  Given that `X[C]` is a clique, this immediately implies that `C` is a
twin equivalence class in `X`.  We need to prove that for all `x ∈ Ω \ C` and all
`y, z ∈ C` we have `c(x,y) = c(x,z)`.  For a contradiction assume this is false and let
`ℓ` be a color and `x ∈ Ω \ C` such that `c(x,y) = ℓ` for some but not all `y ∈ C`.  In
other words, `1 ≤ deg⁺_ℓ < |C|`. … the hypergraph `H = (C, {R_ℓ(u) | u ∈ B})` is
`k`-uniform with `k = deg⁺_ℓ` … `r`-regular with `r = deg⁺_{ℓ⁻}` … for `v, w ∈ C`,
`v ≠ w` we have `|B_v ∩ B_w| = p^m_{ℓ⁻,ℓ}` … hence `H` is a possibly degenerate BIBD with
`λ = p^m_{ℓ⁻,ℓ}`.  The number of vertices of this design is `|C|` and the number of (not
necessarily distinct) blocks is `|B|`.  Hence, by Fisher's inequality, `|C| ≤ |B|`, a
contradiction." -/
theorem large_clique_twinClass (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2)
    {x : Ω} (hx : x ∈ X.vertexClass i₀) :
    twinClass X.Aut x = X.vertexClass i₀ := by
  classical
  obtain ⟨m, -, hm⟩ := X.clique_color h i₀ hclique
  set C := X.vertexClass i₀ with hC
  -- the color of a pair with one endpoint in `C` and one outside does not depend on the
  -- endpoint in `C`
  have hleft : ∀ a ∈ C, ∀ a' ∈ C, ∀ b, b ∉ C → X.color a b = X.color a' b := by
    intro a ha a' ha' b hb
    have h1 : X.color b a = X.color b a' :=
      X.link_color_const_right h i₀ hmax hclique hb ha ha'
    rw [X.color_comm h.toIsConfiguration b a, X.color_comm h.toIsConfiguration b a', h1]
  ext y
  constructor
  · rintro (rfl | ⟨-, hswap⟩)
    · exact hx
    · have := (mem_aut (X := X)).1 hswap x x
      rw [Equiv.swap_apply_left] at this
      show X.vcolor y = i₀
      rw [show X.vcolor y = X.color y y from rfl, this]
      exact hx
  · intro hy
    by_cases hxy : x = y
    · exact Or.inl hxy
    refine Or.inr ⟨hxy, ?_⟩
    -- the transposition `(x,y)` preserves every color
    intro u v
    set σ := Equiv.swap x y with hσ
    have hfix : ∀ w : Ω, w ∉ C → σ w = w := by
      intro w hw
      refine Equiv.swap_apply_of_ne_of_ne (fun hc => hw (hc ▸ hx)) (fun hc => hw (hc ▸ hy))
    have hmap : ∀ w : Ω, w ∈ C → σ w ∈ C := by
      intro w hw
      by_cases h1 : w = x
      · rw [h1, Equiv.swap_apply_left]; exact hy
      by_cases h2 : w = y
      · rw [h2, Equiv.swap_apply_right]; exact hx
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hw
    by_cases hu : u ∈ C <;> by_cases hv : v ∈ C
    · -- both endpoints in the clique
      by_cases huv : u = v
      · subst huv
        have h1 : X.color (σ u) (σ u) = i₀ := hmap u hu
        have h2 : X.color u u = i₀ := hu
        rw [h1, h2]
      · have hne : σ u ≠ σ v := fun hc => huv (σ.injective hc)
        rw [hm (σ u) (hmap u hu) (σ v) (hmap v hv) hne, hm u hu v hv huv]
    · rw [hfix v hv]
      exact hleft (σ u) (hmap u hu) u hu v hv
    · rw [hfix u hu]
      have h1 : X.color u (σ v) = X.color u v :=
        X.link_color_const_right h i₀ hmax hclique hu (hmap v hv) hv
      exact h1
    · rw [hfix u hu, hfix v hv]

/-- Lemma 3.4.25.  "In particular, all links between color 1 and the other vertex colors
are trivial." -/
theorem large_clique_links_trivial (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2)
    (j : Fin X.rank) (hj : j ≠ i₀) (hjne : (X.vertexClass j).Nonempty) :
    (X.link i₀ j).IsTrivial := by
  classical
  obtain ⟨m, ⟨v₀, hv₀, -⟩, -⟩ := X.clique_color h i₀ hclique
  obtain ⟨b₀, hb₀⟩ := hjne
  rw [link, BipConfiguration.isTrivial_iff_color_const]
  refine ⟨⟨⟨⟨v₀, hv₀⟩⟩, ⟨⟨b₀, hb₀⟩⟩⟩, fun a a' b b' => ?_⟩
  rw [X.inducedBipConfig_color_eq_iff]
  -- `b, b'` lie outside `C` and have the same vertex color `j`
  have hbC : ∀ w : X.vertexClass j, (w : Ω) ∉ X.vertexClass i₀ := by
    intro w hw
    exact hj ((show X.vcolor (w : Ω) = j from w.2).symm.trans hw)
  have h1 : X.color (b : Ω) (a : Ω) = X.color (b' : Ω) (a' : Ω) :=
    X.link_color_const h i₀ hmax hclique
      ((show X.vcolor (b : Ω) = j from b.2).trans (show X.vcolor (b' : Ω) = j from b'.2).symm)
      (hbC b) (hbC b') a.2 a'.2
  rw [X.color_comm h.toIsConfiguration (b : Ω) (a : Ω),
    X.color_comm h.toIsConfiguration (b' : Ω) (a' : Ω), h1]

/-- Lemma 3.4.25.  "Moreover, the symmetry defect of `X` is `1 - |Ω₁|/|Ω|`."

Paper's proof: "Regarding the last statement, about the symmetry defect, we note that `C`
is the largest twin equivalence class in `X` since by definition, twins have the same
color." -/
theorem large_clique_defect (h : X.IsCoherent) (i₀ : Fin X.rank)
    (hmax : ∀ i : Fin X.rank, i ≠ i₀ →
      (X.vertexClass i).ncard < (X.vertexClass i₀).ncard)
    (hclique : (X.induced (X.vertexClass i₀)).rank = 2) :
    defect X.Aut = 1 - ((X.vertexClass i₀).ncard : ℚ) / (Fintype.card Ω : ℚ) := by
  classical
  obtain ⟨m, ⟨v₀, hv₀, -⟩, -⟩ := X.clique_color h i₀ hclique
  set C := X.vertexClass i₀ with hC
  -- `C` is a set of twins, and it is the largest one: twins have the same vertex color
  have hCtwin : IsTwinSet X.Aut (↑C.toFinset : Set Ω) := by
    intro a ha b hb hab
    rw [Set.coe_toFinset] at ha hb
    have := X.large_clique_twinClass h i₀ hmax hclique ha
    have hmem : b ∈ twinClass X.Aut a := by rw [this]; exact hb
    rcases hmem with hc | hc
    · exact absurd hc hab
    · exact hc
  have hle : symmetricity X.Aut ≤ C.ncard := by
    refine Finset.sup_le fun Ψ hΨ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
    rcases Finset.eq_empty_or_nonempty Ψ with rfl | ⟨a, ha⟩
    · simp
    -- all elements of a set of twins have the same vertex color
    have hsub : (Ψ : Finset Ω) ⊆ (X.vertexClass (X.vcolor a)).toFinset := by
      intro b hb
      rw [Set.mem_toFinset]
      by_cases hab : a = b
      · rw [← hab]; rfl
      · obtain ⟨-, hswap⟩ := hΨ a ha b hb hab
        have := (mem_aut (X := X)).1 hswap a a
        rw [Equiv.swap_apply_left] at this
        exact this
    have hcard : Ψ.card ≤ (X.vertexClass (X.vcolor a)).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      exact Finset.card_le_card hsub
    by_cases hi : X.vcolor a = i₀
    · rw [hi] at hcard; exact hcard
    · exact le_of_lt (lt_of_le_of_lt hcard (hmax _ hi))
  have hge : C.ncard ≤ symmetricity X.Aut := by
    have := le_symmetricity hCtwin
    rwa [← Set.ncard_eq_toFinset_card'] at this
  have hsym : symmetricity X.Aut = C.ncard := le_antisymm hle hge
  rw [defect, relSymmetricity, hsym]

end PartitionStructure

end Babai
