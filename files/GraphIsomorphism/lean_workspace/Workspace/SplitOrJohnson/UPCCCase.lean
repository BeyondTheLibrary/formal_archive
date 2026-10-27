/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.8: the UPCC case (Procedure Reduce-by-UPCC and its Claim).  This section is new
in version 2.5: it repairs the gap found by Harald Helfgott, using Theorem 3.4.19.
-/
import Workspace.SplitOrJohnson.Minor
import Workspace.Coherent.LocalConstituents

/-!
# §9.8 UPCC case

Version 2.5, lines 4302–4355 of `babai-gi-source/quasi25.txt`.

> *Case: Both `X₁` and `X₂` are UPCCs; the link `X₁₂` is nontrivial.*

| Paper | Lean |
|---|---|
| `α`-dominant color in `X₁₂` | `Babai.PartitionStructure.IsAlphaDominant` |
| dominant color | `Babai.PartitionStructure.IsDominant` |
| Procedure Reduce-by-UPCC, step 2 | `Babai.reduceByUPCC_localColoring_small` |
| Procedure Reduce-by-UPCC, step 3 | `Babai.PartitionStructure.localConstituentBip` (§3.4.3) |
| step 3, existence of the non-dominant off-diagonal color `ℓ` | `Babai.PartitionStructure.exists_nondominant_offDiagonal` |
| Claim of §9.8 | `Babai.claim_9_8` |

## The procedure as a specification

Procedure Reduce-by-UPCC branches on its input ("if there is no `α`-dominant color …
else …") and, in the "else" branch, picks the dominant color `m` and *"the first
non-dominant off-diagonal color `ℓ` in `X₂`"*; the choice of the first such color is a
canonical choice among the colors satisfying a condition, and the paper's Claim is about
the object obtained from *any* such choice (only the stated inequalities are used).  We
therefore formalize the two branches as two statements about a color satisfying the branch
condition, rather than as one function.
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (X : PartitionStructure Ω)

/-- §9.8.  *"We say that for some `j ∈ J`, the color `j` is `α`-dominant in `X₁₂` if
`|R_j| > α n₁ n₂`."*  Here `n₁ = |V₁|`, `n₂ = |V₂|` are the sizes of the two vertex-color
classes joined by the link. -/
def IsAlphaDominant (α : ℝ) (i j : Fin X.rank) (k : Fin X.rank) : Prop :=
  α * ((X.vertexClass i).ncard : ℝ) * ((X.vertexClass j).ncard : ℝ) < (X.rel k).ncard

/-- §9.8.  *"We say 'dominant' for `(1/2)`-dominant."* -/
def IsDominant (i j : Fin X.rank) (k : Fin X.rank) : Prop :=
  X.IsAlphaDominant (1 / 2) i j k

/-- The double count behind *"`|R_j| > α n₁ n₂`"*: a constituent has as many edges as its
tail class has vertices, times the common out-degree (Obs. 3.3.5, Notation 3.3.6).  This is
what turns a bound on `|R_j|` into a bound on `|R_j(x)|`, as §9.8 does twice (in step 2 for
the `x`-local coloring, and in step 3 for `|R_ℓ(x)| < n₂/2`). -/
theorem ncard_rel_eq (h : X.IsCoherent) (k : Fin X.rank) :
    (X.rel k).ncard = (X.vertexClass (X.tailColor k)).ncard * X.outDegOf k := by
  classical
  have hsplit : (X.rel k).toFinset
      = Finset.univ.biUnion fun x : Ω => (X.nbr k x).toFinset.image fun y => (x, y) := by
    ext p
    simp only [Set.mem_toFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image, PartitionStructure.rel, PartitionStructure.nbr, Set.mem_setOf_eq]
    exact ⟨fun hp => ⟨p.1, p.2, hp, rfl⟩, by rintro ⟨x, y, hy, rfl⟩; exact hy⟩
  have hdisj : ∀ x ∈ (Finset.univ : Finset Ω), ∀ y ∈ (Finset.univ : Finset Ω), x ≠ y →
      Disjoint ((X.nbr k x).toFinset.image fun z => (x, z))
        ((X.nbr k y).toFinset.image fun z => (y, z)) := by
    intro x _ y _ hxy
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro p ⟨z, -, rfl⟩ ⟨w, -, hw⟩
    exact hxy (congrArg Prod.fst hw).symm
  have hcard : (X.rel k).ncard = ∑ x : Ω, (X.nbr k x).ncard := by
    rw [Set.ncard_eq_toFinset_card', hsplit, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).2),
      ← Set.ncard_eq_toFinset_card']
  rw [hcard, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : Ω => x ∈ X.vertexClass (X.tailColor k))]
  have h1 : (∑ x ∈ Finset.univ.filter fun x : Ω => x ∈ X.vertexClass (X.tailColor k),
      (X.nbr k x).ncard)
      = (X.vertexClass (X.tailColor k)).ncard * X.outDegOf k := by
    rw [Finset.sum_congr rfl (g := fun _ => X.outDegOf k) fun x hx => ?_, Finset.sum_const,
      smul_eq_mul]
    · congr 1
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext x; simp
    · rw [← PartitionStructure.outDegC_eq_ncard,
        X.outDegC_eq_outDegOf h k (Finset.mem_filter.1 hx).2]
  have h2 : (∑ x ∈ Finset.univ.filter fun x : Ω => ¬ x ∈ X.vertexClass (X.tailColor k),
      (X.nbr k x).ncard) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hne : X.vcolor x ≠ X.tailColor k := (Finset.mem_filter.1 hx).2
    rw [X.nbr_eq_empty_of_vcolor_ne h k hne, Set.ncard_empty]
  rw [h1, h2, add_zero]

/-- §9.8, step 3 of Procedure Reduce-by-UPCC: *"let `ℓ` be the first non-dominant
off-diagonal color in `X₂`"*, and the Claim's justification of its existence: *"we need
'uni' (not a clique) to guarantee that a non-dominant off-diagonal color `ℓ` exists in
`X₂`."*

*"Uni"* enters as `3 ≤ rank`: in a homogeneous structure exactly one color is diagonal, so
rank `≥ 3` gives at least **two** off-diagonal colors, and two disjoint relations cannot
both have more than half of the `n²` edges.  (Rank `2`, the clique configuration, has a
single off-diagonal color, which carries all `n² − n` off-diagonal edges and is dominant as
soon as `n ≥ 3`; this is exactly the case the paper has to exclude.) -/
theorem exists_nondominant_offDiagonal [Fintype Ω] [DecidableEq Ω] (hrank : 3 ≤ X.rank)
    {i : Fin X.rank} (hvc : X.vertexClass i = Set.univ) :
    ∃ l : Fin X.rank, X.IsOffDiagonalColor l ∧ ¬ X.IsDominant i i l := by
  classical
  -- every color other than the (unique) vertex color is off-diagonal
  have hoff : ∀ k : Fin X.rank, k ≠ i → X.IsOffDiagonalColor k := by
    intro k hk
    rw [IsOffDiagonalColor, Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, y⟩ ⟨hxy, hdg⟩
    have hxy' : X.color x y = k := hxy
    have hx : x = y := hdg
    have : X.color x x = i := by
      have : x ∈ X.vertexClass i := by rw [hvc]; trivial
      exact this
    rw [← hx] at hxy'
    exact hk (hxy' ▸ this)
  -- rank `≥ 3` gives two distinct colors different from `i`
  have h0 : (0 : ℕ) < X.rank := by omega
  have h1 : (1 : ℕ) < X.rank := by omega
  have h2 : (2 : ℕ) < X.rank := by omega
  set a₀ : Fin X.rank := ⟨0, h0⟩
  set a₁ : Fin X.rank := ⟨1, h1⟩
  set a₂ : Fin X.rank := ⟨2, h2⟩
  have hne01 : a₀ ≠ a₁ := by simp [a₀, a₁, Fin.ext_iff]
  have hne02 : a₀ ≠ a₂ := by simp [a₀, a₂, Fin.ext_iff]
  have hne12 : a₁ ≠ a₂ := by simp [a₁, a₂, Fin.ext_iff]
  obtain ⟨l₁, l₂, hl12, hl1, hl2⟩ :
      ∃ l₁ l₂ : Fin X.rank, l₁ ≠ l₂ ∧ l₁ ≠ i ∧ l₂ ≠ i := by
    by_cases hi0 : a₀ = i
    · exact ⟨a₁, a₂, hne12, fun h => hne01 (hi0.trans h.symm), fun h => hne02 (hi0.trans h.symm)⟩
    · by_cases hi1 : a₁ = i
      · exact ⟨a₀, a₂, hne02, hi0, fun h => hne12 (hi1.trans h.symm)⟩
      · exact ⟨a₀, a₁, hne01, hi0, hi1⟩
  -- if both were dominant, two disjoint relations would each hold more than half of `Ω × Ω`
  by_contra hcon
  push_neg at hcon
  have hd₁ : X.IsDominant i i l₁ := hcon l₁ (hoff l₁ hl1)
  have hd₂ : X.IsDominant i i l₂ := hcon l₂ (hoff l₂ hl2)
  have hsum : (X.rel l₁).ncard + (X.rel l₂).ncard ≤ Fintype.card Ω * Fintype.card Ω := by
    have hdisj : Disjoint (X.rel l₁) (X.rel l₂) := X.rel_disjoint hl12
    have := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
    have hle : (X.rel l₁ ∪ X.rel l₂).ncard ≤ (Set.univ : Set (Ω × Ω)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_prod] at hle
    omega
  have hn : ((X.vertexClass i).ncard : ℝ) = (Fintype.card Ω : ℝ) := by
    rw [hvc, Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [IsDominant, IsAlphaDominant, hn] at hd₁ hd₂
  have hsum' : ((X.rel l₁).ncard : ℝ) + ((X.rel l₂).ncard : ℝ)
      ≤ (Fintype.card Ω : ℝ) * (Fintype.card Ω : ℝ) := by exact_mod_cast hsum
  linarith

end PartitionStructure

/-! ### Step 2 of Procedure Reduce-by-UPCC -/

open scoped Classical in
/-- Procedure Reduce-by-UPCC, step 2.  *"If there is no `α`-dominant color in `X₁₂`,
return the `x`-local coloring `c_x` of `V₁` (set `c_x(y) = c(x,y)` for all `y ∈ V₁`), exit.
(Each `c_x`-class in `V₁` has relative size `≤ α`; goal (a) achieved.)"*

The `c_x`-classes in `V₁` are the sets `R_k(x) ∩ V₁`; the assertion is that each of them
has size `≤ α n₁`.  (Reason: by the semiregularity of the constituents of the link
(Prop. 3.4.5) the in-degree in color `k` is the same for every `y ∈ V₂`, so
`|R_k| = n₂ · |R_k(x) ∩ V₁|`; hence `|R_k(x) ∩ V₁| = |R_k|/n₂ ≤ α n₁` when `k` is not
`α`-dominant.) -/
theorem reduceByUPCC_localColoring_small {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (X : PartitionStructure Ω) (hX : X.IsCoherent) (α : ℝ) {i j : Fin X.rank}
    (hi : X.IsDiagonalColor i) (hj : X.IsDiagonalColor j)
    {x : Ω} (hx : x ∈ X.vertexClass j)
    (hnone : ∀ k : Fin X.rank, ¬ X.IsAlphaDominant α i j k) (k : Fin X.rank) :
    ((X.nbr k x ∩ X.vertexClass i).ncard : ℝ) ≤ α * ((X.vertexClass i).ncard : ℝ) := by
  classical
  set n₁ : ℝ := ((X.vertexClass i).ncard : ℝ) with hn₁
  set n₂ : ℝ := ((X.vertexClass j).ncard : ℝ) with hn₂
  -- no color is `α`-dominant: `|R_c| ≤ α n₁ n₂` for every color `c`
  have hbound : ∀ c : Fin X.rank, ((X.rel c).ncard : ℝ) ≤ α * n₁ * n₂ := fun c =>
    not_lt.1 (hnone c)
  -- `n₂ > 0`, since `x ∈ V₂`
  have hn₂pos : 0 < n₂ := by
    have h : 0 < (X.vertexClass j).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hx⟩
    rw [hn₂]; exact_mod_cast h
  -- every constituent is non-empty, so `α n₁ n₂ ≥ 1 > 0`
  have hαpos : 0 < α * n₁ * n₂ := by
    have h1 : (1 : ℝ) ≤ ((X.rel k).ncard : ℝ) := by
      have : 0 < (X.rel k).ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 (X.rel_nonempty k)
      exact_mod_cast this
    linarith [hbound k]
  have hαn₁ : 0 < α * n₁ := by
    by_contra hle
    push_neg at hle
    nlinarith [hαpos, hn₂pos]
  rw [X.ncard_nbr_inter_vertexClass hX k i x]
  split_ifs with hcond
  · -- `x` is a tail of color `k`, so `|R_k| = n₂ · deg⁺_k`
    have htail : X.tailColor k = j := by
      have hvx : X.vcolor x = j := hx
      rw [← hcond.1, hvx]
    have hrel : ((X.rel k).ncard : ℝ) = n₂ * (X.outDegOf k : ℝ) := by
      rw [X.ncard_rel_eq hX k, htail]
      push_cast [hn₂]
      ring
    have := hbound k
    rw [hrel] at this
    have hstep : n₂ * (X.outDegOf k : ℝ) ≤ n₂ * (α * n₁) := by linarith [this]
    exact le_of_mul_le_mul_left hstep hn₂pos
  · simpa using le_of_lt hαn₁

/-! ### The Claim of §9.8 -/

open scoped Classical in
/-- Claim of §9.8.  *"Procedure Reduce-by-UPCC makes significant progress.  Specifically,
it either achieves goal (a) or reduces `n₂` by half while maintaining symmetry defect
`≥ 1/2` in each part.  The multiplicative cost is `n₂`."*  (Version 2.5, lines 4333–4336.)

This is the "else" branch: `Y` is the local constituent
`Y = X_m[R_m⁻(x), R_ℓ(x)]` of step 3, which in the notation of §3.4.3 (Def. 3.4.18) is the
`x`-`(m, ℓ, m)`-local constituent for the color `m` *pointing from `V₂` to `V₁`*; so in the
hypotheses below `x ∈ Ωᵢ = V₂`, `R_ℓ(x) ⊆ Ωᵢ = V₂` and `R_m(x) ⊆ Ω_j = V₁`, which is the
paper's `Y⁻` (*"It is nontrivial by Theorem 3.4.19, applied to `Y⁻`"*).

Paper's proof: *"Clearly `Y` is canonical relative to the choice of `x`.  `Y` is
semiregular by Observation 3.4.17.  It is nontrivial by Theorem 3.4.19, applied to `Y⁻`.
We need to verify the assumptions of Theorem 3.4.19.  First we note that both `V₁` and
`V₂` are vertex-color classes in `X`.  Second, we need `n₁/2 < |R_m⁻(x)| < n₁`.  The first
of these inequalities follows because `m` is `α`-dominant and therefore dominant.  The
second inequality is equivalent to the nontriviality of the link `X₁₂`.  Finally, we need
that `X₂` is a UPCC.  (Primitivity guarantees that there are no `X_m`-twins in `V₂`; and we
need "uni" (not a clique) to guarantee that a non-dominant off-diagonal color `ℓ` exists in
`X₂`.)  Summarizing, `Y` is a nontrivial semiregular bipartite graph; therefore its
symmetry defect is `≥ 1/2` (Prop. 2.4.30)."*

The two inequalities `n₁/2 < |R_m(x)| < n₁` are hypotheses here, as in Theorem 3.4.19;
the paper derives them from the dominance of `m` and from the nontriviality of the link.

*"`X₂` is a UPCC"* is `huni`: primitivity is what Theorem 3.4.19 needs, and *"uni"* is what
guarantees that the non-dominant off-diagonal color `ℓ` of step 3 exists.  The
non-dominance of `ℓ` is `hlnd`, and it is what halves `n₂`: `V₂` is replaced by `R_ℓ(x)`.

*The halving is `2|R_ℓ(x)| ≤ n₂`, not `<`.*  Step 3 of the procedure writes
*"`|R_ℓ(x)| < n₂/2`"*, but non-dominance of `ℓ` gives only `|R_ℓ| ≤ n₂²/2`, hence
`|R_ℓ(x)| = |R_ℓ|/n₂ ≤ n₂/2`; nothing in §9.8 excludes equality.  The Claim itself —
*"reduces `n₂` by half"*, and `n₂` significantly reduced in the sense of §9.5 — needs only
`≤`.  See the entry for the Claim of §9.8 in the corrected paper. -/
theorem claim_9_8 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (X : PartitionStructure Ω)
    (hX : X.IsCoherent) {i j l m : Fin X.rank}
    (hi : X.IsDiagonalColor i) (hj : X.IsDiagonalColor j)
    (hlm : l ≠ m) (hloff : X.IsOffDiagonalColor l) (hmoff : X.IsOffDiagonalColor m)
    (hlnd : ¬ X.IsDominant i i l)
    {x : Ω} (hx : x ∈ X.vertexClass i)
    (hlx : X.nbr l x ⊆ X.vertexClass i) (hmx : X.nbr m x ⊆ X.vertexClass j)
    (hlne : (X.nbr l x).Nonempty)
    (hhalf : (X.vertexClass j).ncard < 2 * (X.nbr m x).ncard)
    (hlt : (X.nbr m x).ncard < (X.vertexClass j).ncard)
    (huni : (X.induced (X.vertexClass i)).IsUniprimitive) :
    (X.localConstituentBip m l m x).IsSemiregular ∧
      ¬ (X.localConstituentBip m l m x).IsTrivial ∧
      1 / 2 ≤ (X.localConstituentBip m l m x).defect₁ ∧
      1 / 2 ≤ (X.localConstituentBip m l m x).defect₂ ∧
      2 * (X.nbr l x).ncard ≤ (X.vertexClass i).ncard := by
  -- "`Y` is semiregular by Observation 3.4.17."
  have hsr : (X.localConstituentBip m l m x).IsSemiregular :=
    (X.localColoring_isEquitable hX x m).2 l m hlm
  -- "It is nontrivial by Theorem 3.4.19."  (Primitivity of `X₂` is the half of "UPCC" that
  -- Theorem 3.4.19 uses.)
  have hnt : ¬ (X.localConstituentBip m l m x).IsTrivial :=
    X.nontriviality_of_local_constituent hX hi hj hlm hloff hmoff hx hlx hmx hlne hhalf hlt
      huni.1
  -- "the update … reduced `n₂`": `|R_ℓ| = n₂·|R_ℓ(x)| ≤ n₂²/2` because `ℓ` is non-dominant
  have hnpos : 0 < (X.vertexClass i).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hx⟩
  have hi2 : X.tailColor l = i := by
    obtain ⟨y, hy⟩ := hlne
    exact (X.vcolor_fst_eq hX (show X.color x y = l from hy)).symm.trans hx
  have hdeg : X.outDegOf l = (X.nbr l x).ncard := by
    rw [← X.outDegC_eq_outDegOf hX l (by rw [hi2]; exact hx),
      PartitionStructure.outDegC_eq_ncard]
  have hhalfl : 2 * (X.nbr l x).ncard ≤ (X.vertexClass i).ncard := by
    have hrel : (X.rel l).ncard = (X.vertexClass i).ncard * (X.nbr l x).ncard := by
      rw [X.ncard_rel_eq hX l, hi2, hdeg]
    have hnd : ((X.rel l).ncard : ℝ)
        ≤ 1 / 2 * ((X.vertexClass i).ncard : ℝ) * ((X.vertexClass i).ncard : ℝ) :=
      not_lt.1 hlnd
    rw [hrel] at hnd
    push_cast at hnd
    have hnR : (0 : ℝ) < ((X.vertexClass i).ncard : ℝ) := by exact_mod_cast hnpos
    have hfin : 2 * ((X.nbr l x).ncard : ℝ) ≤ ((X.vertexClass i).ncard : ℝ) := by
      nlinarith [hnd, hnR]
    exact_mod_cast hfin
  -- "therefore its symmetry defect is `≥ 1/2` (Prop. 2.4.30)."
  exact ⟨hsr, hnt, (BipGraph.defect_ge_half hnt hsr).1, (BipGraph.defect_ge_half hnt hsr).2,
    hhalfl⟩

end Babai
