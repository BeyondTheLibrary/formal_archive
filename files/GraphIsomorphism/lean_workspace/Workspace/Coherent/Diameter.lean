/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The diameter-2 fact used inside the proof of Lemma 9.3.1 (§9.3).
-/
import Workspace.Coherent.Constituents

/-!
# The complement of an undirected constituent of a UPCC has diameter 2

Inside the proof of Lemma 9.3.1 (version 2.5, lines 4058–4061) the paper says

> Assume now that (say) `d₂ > βn`; so `(V, R₂)` is an undirected graph (since `d₂ ≥ n/2`)
> and its complement has diameter 2 (see the proof of [Ba81, Prop. 4.10]).

and then uses the fact only in the existential form

> Let `(x, z) ∈ R₂` and let `y ∈ V` be such that `(x, y) ∈ Rᵢ` and `(z, y) ∈ R_j`
> where `i, j ≥ 3`.

This file **proves** that existential form from primitivity and coherence, so the
citation `[Ba81, Prop. 4.10]` is not needed as an axiom.  See entry C7 of `CITED.md`.

## The proof

Write `P i` for "`i` is an off-diagonal color and `i ≠ c₂`" (this is the paper's
"`i ≥ 3`": in a homogeneous configuration there is exactly one diagonal color).  Fix a
pair `(x, z) ∈ R₂` and suppose no `y` works for it.  By coherence the number of good `y`
is the same for every pair of color `c₂`; here we only need that it vanishes for one pair
iff it vanishes for all of them, which is the statement that the intersection numbers
`p^{c₂}_{ij}` vanish for all `i, j` with `P i`, `P j` (`interNum_eq`).  So no pair of
color `c₂` has a good midpoint.

Then the relation `E a b := a = b ∨ P (c(a,b))` ("equal, or joined by a color other than
`R₂`") is reflexive, symmetric (because `R₂` is undirected, so `P` is invariant under
`i ↦ i⁻`) and, by the previous paragraph, transitive.  Since the rank is at least `3`
there is an off-diagonal color `c₃ ≠ c₂`; its constituent is connected because `X` is
primitive (Def. 3.2.1), and `E` contains its adjacency relation, so `E` holds of every
pair.  This contradicts `c(x, z) = c₂`.
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

/-- The color of a pair of *distinct* vertices is an off-diagonal color (Terminology
3.1.3, from axiom (i) of Def. 3.1.2). -/
theorem isOffDiagonalColor_color_of_ne (h : X.IsConfiguration) {x y : Ω} (hxy : x ≠ y) :
    X.IsOffDiagonalColor (X.color x y) := by
  rcases X.diagonal_or_offDiagonal h (X.color x y) with hd | ho
  · exact absurd (hd (show (x, y) ∈ X.rel (X.color x y) from rfl)) hxy
  · exact ho

/-- The converse `i⁻` of an off-diagonal color is off-diagonal. -/
theorem isOffDiagonalColor_conv (h : X.IsConfiguration) {i : Fin X.rank}
    (hi : X.IsOffDiagonalColor i) : X.IsOffDiagonalColor (X.conv i) := by
  show X.rel (X.conv i) ∩ diag Ω = ∅
  rw [X.rel_conv h i, Set.eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩ ⟨hmem, hdg⟩
  simp only [mem_invRel] at hmem
  simp only [mem_diag] at hdg
  refine Set.eq_empty_iff_forall_notMem.1 hi (u, v) ⟨?_, hdg⟩
  simpa [hdg] using hmem

/-- In a homogeneous configuration every color other than the vertex color is
off-diagonal: there is exactly one diagonal color. -/
theorem isOffDiagonalColor_of_ne_vcolor (h : X.IsConfiguration) (hhom : X.IsHomogeneous)
    (w : Ω) {i : Fin X.rank} (hi : i ≠ X.vcolor w) : X.IsOffDiagonalColor i := by
  rcases X.diagonal_or_offDiagonal h i with hd | ho
  · exfalso
    obtain ⟨p, hp⟩ := X.rel_nonempty i
    have hdg : p.1 = p.2 := hd hp
    rw [mem_rel] at hp
    refine hi ?_
    rw [← hp, ← hdg]
    exact hhom p.1 w
  · exact ho

/-- **The diameter-2 fact** used in the proof of Lemma 9.3.1 (§9.3, version 2.5, lines
4058–4061), proved here rather than cited from `[Ba81, Prop. 4.10]` (entry C7 of
`CITED.md`).

*"Let `(x, z) ∈ R₂` and let `y ∈ V` be such that `(x, y) ∈ Rᵢ` and `(z, y) ∈ R_j` where
`i, j ≥ 3`."*  The hypotheses are the ones the argument uses: `X` is a UPCC (Def. 3.2.1:
homogeneous, all off-diagonal constituents connected, rank `≥ 3`) and the constituent
`c₂` is undirected (`c₂⁻ = c₂`), which in the paper follows from `d₂ ≥ n/2`.
"`i, j ≥ 3`" is rendered as "off-diagonal and `≠ c₂`", which is what it means in a
homogeneous configuration. -/
theorem exists_mid_of_undirected_constituent [Finite Ω] (h : X.IsCoherent)
    (hprim : X.IsUniprimitive) {c₂ : Fin X.rank} (hc₂ : X.IsOffDiagonalColor c₂)
    (hsymm : X.conv c₂ = c₂) {x z : Ω} (hxz : X.color x z = c₂) :
    ∃ y : Ω, X.IsOffDiagonalColor (X.color x y) ∧ X.color x y ≠ c₂ ∧
      X.IsOffDiagonalColor (X.color z y) ∧ X.color z y ≠ c₂ := by
  classical
  obtain ⟨⟨hhom, hconn⟩, hrank⟩ := hprim
  have hcfg : X.IsConfiguration := h.toIsConfiguration
  -- `P i` is the paper's "`i ≥ 3`".
  set P : Fin X.rank → Prop := fun i => X.IsOffDiagonalColor i ∧ i ≠ c₂ with hPdef
  have hP : ∀ i, P i ↔ (X.IsOffDiagonalColor i ∧ i ≠ c₂) := fun _ => Iff.rfl
  -- `P` is invariant under `i ↦ i⁻`, because `c₂⁻ = c₂`.
  have hPconv : ∀ i, P i → P (X.conv i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := (hP i).1 hi
    refine (hP _).2 ⟨X.isOffDiagonalColor_conv hcfg hi1, fun hc => hi2 ?_⟩
    have := congrArg X.conv hc
    rwa [X.conv_conv hcfg, hsymm] at this
  by_contra hno
  push_neg at hno
  -- Step 1: no pair of color `c₂` has a good midpoint, by coherence.
  have hvanish : ∀ i j : Fin X.rank, P i → P j → X.interNum i j c₂ = 0 := by
    intro i j hi hj
    rw [← X.interNum_eq h i j c₂ hxz, Set.ncard_eq_zero (Set.toFinite _),
      Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have hxy : P (X.color x y) := by rw [hy1]; exact hi
    have hyz : P (X.color y z) := by rw [hy2]; exact hj
    have hzy : P (X.color z y) := by
      rw [X.color_comm hcfg y z]; exact hPconv _ hyz
    exact ((hP _).1 hzy).2
      (hno y ((hP _).1 hxy).1 ((hP _).1 hxy).2 ((hP _).1 hzy).1)
  have hmid : ∀ a c : Ω, X.color a c = c₂ →
      ∀ y : Ω, P (X.color a y) → ¬ P (X.color y c) := by
    intro a c hac y hy hyc
    have hk := X.interNum_eq h (X.color a y) (X.color y c) c₂ hac
    rw [hvanish _ _ hy hyc, Set.ncard_eq_zero (Set.toFinite _),
      Set.eq_empty_iff_forall_notMem] at hk
    exact hk y ⟨rfl, rfl⟩
  -- Step 2: `E` is an equivalence relation.
  set E : Ω → Ω → Prop := fun a b => a = b ∨ P (X.color a b) with hEdef
  have hE : ∀ a b, E a b ↔ (a = b ∨ P (X.color a b)) := fun _ _ => Iff.rfl
  have hErefl : ∀ a, E a a := fun a => (hE a a).2 (Or.inl rfl)
  have hEsymm : ∀ {a b}, E a b → E b a := by
    intro a b hab
    rcases (hE a b).1 hab with rfl | hab
    · exact hErefl _
    · refine (hE b a).2 (Or.inr ?_)
      rw [X.color_comm hcfg a b]
      exact hPconv _ hab
  have hEtrans : ∀ {a b c}, E a b → E b c → E a c := by
    intro a b c hab hbc
    rcases (hE a b).1 hab with rfl | hab'
    · exact hbc
    rcases (hE b c).1 hbc with rfl | hbc'
    · exact (hE a b).2 (Or.inr hab')
    by_contra hac
    have hac' : ¬ (a = c ∨ P (X.color a c)) := fun hh => hac ((hE a c).2 hh)
    push_neg at hac'
    obtain ⟨hne, hnP⟩ := hac'
    have hoff : X.IsOffDiagonalColor (X.color a c) :=
      X.isOffDiagonalColor_color_of_ne hcfg hne
    have hc₂' : X.color a c = c₂ := by
      by_contra hc
      exact hnP ((hP _).2 ⟨hoff, hc⟩)
    exact hmid a c hc₂' b hab' hbc'
  -- Step 3: an off-diagonal color `c₃ ≠ c₂`; its constituent is connected (primitivity).
  obtain ⟨c₃, hc₃v, hc₃2⟩ : ∃ c₃ : Fin X.rank, c₃ ≠ X.vcolor x ∧ c₃ ≠ c₂ := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Set.univ : Set (Fin X.rank)) ⊆ {X.vcolor x, c₂} := by
      intro i _
      by_cases hi : i = X.vcolor x
      · exact Or.inl hi
      · exact Or.inr (hcon i hi)
    have h1 : (Set.univ : Set (Fin X.rank)).ncard ≤ ({X.vcolor x, c₂} : Set _).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : ({X.vcolor x, c₂} : Set (Fin X.rank)).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    omega
  have hc₃off : X.IsOffDiagonalColor c₃ :=
    X.isOffDiagonalColor_of_ne_vcolor hcfg hhom x hc₃v
  have hEall : ∀ a b : Ω, E a b := by
    intro a b
    refine (X.extConstituent c₃).weaklyAccessible_rel hErefl hEsymm hEtrans ?_
      (hconn c₃ hc₃off a b)
    intro u v huv
    have huv' : X.color u v = c₃ := huv
    refine (hE u v).2 (Or.inr ((hP _).2 ⟨?_, ?_⟩)) <;> rw [huv']
    · exact hc₃off
    · exact hc₃2
  -- Step 4: contradiction with `c(x,z) = c₂`.
  rcases (hE x z).1 (hEall x z) with heq | hPxz
  · exact Set.eq_empty_iff_forall_notMem.1 hc₂ (x, z) ⟨hxz, heq⟩
  · exact ((hP _).1 hPxz).2 hxz

/-! ### `d₂ ≥ n/2` makes the constituent `R₂` undirected

The other parenthesis of the same sentence of the proof of Lemma 9.3.1: *"so `(V, R₂)` is
an undirected graph (since `d₂ ≥ n/2`)"*.  A constituent and its converse are disjoint
unless they are equal, and in a homogeneous coherent configuration they have the same
degree (the constituent is eulerian, Cor. 3.3.7(i) via Prop. 3.4.1), so together they
would use up more than `n` out-neighbours. -/
theorem conv_eq_self_of_two_mul_outDeg_gt [Fintype Ω] [DecidableEq Ω] (h : X.IsCoherent)
    (hhom : X.IsHomogeneous) {c₂ : Fin X.rank} {x : Ω}
    (hd : Fintype.card Ω < 2 * (X.nbr c₂ x).ncard) : X.conv c₂ = c₂ := by
  classical
  by_contra hne
  -- the out-neighbourhood in color `c₂⁻` is the in-neighbourhood in color `c₂`
  have heul : X.outDegC c₂ x = X.inDegC c₂ x :=
    X.extConstituent_isEulerian h c₂ (X.tailColor_eq_headColor_of_isHomogeneous hhom c₂) x
  have hB : (X.nbr (X.conv c₂) x).ncard = (X.nbr c₂ x).ncard := by
    have h1 : X.inDegC c₂ x = (X.nbr (X.conv c₂) x).ncard := by
      rw [inDegC_eq_ncard, X.inNbr_eq_nbr_conv h.toIsConfiguration c₂ x]
    rw [← h1, ← heul, outDegC_eq_ncard]
  -- the two neighbourhoods are disjoint
  have hdisj : Disjoint (X.nbr c₂ x) (X.nbr (X.conv c₂) x) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hne (by rw [← (hy' : X.color x y = X.conv c₂), (hy : X.color x y = c₂)])
  have hun : (X.nbr c₂ x ∪ X.nbr (X.conv c₂) x).ncard
      = (X.nbr c₂ x).ncard + (X.nbr (X.conv c₂) x).ncard :=
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : (X.nbr c₂ x ∪ X.nbr (X.conv c₂) x).ncard ≤ Fintype.card Ω := by
    have := Set.ncard_le_ncard (Set.subset_univ (X.nbr c₂ x ∪ X.nbr (X.conv c₂) x))
      (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  omega

/-! ### Semiregularity of the bipartite graph between two cells (Prop. 3.4.5 in §9.3)

In the proof of Lemma 9.3.1 the vertex `x` is individualized, the cells
`Cᵢ = Rᵢ(x) = X.nbr i x` are the resulting canonical subsets, and the bipartite graph used
is `X̄ = (C₂, Cᵢ; (C₂ × Cᵢ) ∩ R_j)`.  The paper says it is semiregular and cites
Prop. 3.4.5; what makes it so is coherence: both degrees are intersection numbers. -/

/-- The bipartite graph between two cells `R_a(x)` and `R_b(x)` of the partition of `Ω`
obtained by individualizing `x`, with the edges of color `j`: the graph
`X̄ = (C_a, C_b; (C_a × C_b) ∩ R_j)` of the proof of Lemma 9.3.1. -/
def cellBip (x : Ω) (a b j : Fin X.rank) : BipGraph ↥(X.nbr a x) ↥(X.nbr b x) :=
  ⟨{p | X.color (p.1 : Ω) (p.2 : Ω) = j}⟩

private theorem ncard_subtype_setOf (S : Set Ω) (p : Ω → Prop) :
    {y : ↥S | p (y : Ω)}.ncard = (S ∩ {y | p y}).ncard := by
  have himg : (Subtype.val : ↥S → Ω) '' {y : ↥S | p (y : Ω)} = S ∩ {y | p y} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨hzS, hz⟩; exact ⟨⟨z, hzS⟩, hz, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The degree of a vertex `u ∈ C_a` in `X̄ = (C_a, C_b; R_j)` is the intersection number
`p^a_{b,j⁻}`, so it does not depend on `u`. -/
theorem degA_cellBip (h : X.IsCoherent) (x : Ω) (a b j : Fin X.rank)
    (u : ↥(X.nbr a x)) : (X.cellBip x a b j).degA u = X.interNum b (X.conv j) a := by
  rw [BipGraph.degA]
  have h1 : {y : ↥(X.nbr b x) | (u, y) ∈ (X.cellBip x a b j).E}
      = {y : ↥(X.nbr b x) | X.color (u : Ω) (y : Ω) = j} := rfl
  rw [h1]
  refine Eq.trans (ncard_subtype_setOf (X.nbr b x) (fun w => X.color (u : Ω) w = j)) ?_
  have h2 : X.nbr b x ∩ {y | X.color (u : Ω) y = j}
      = {z : Ω | X.color x z = b ∧ X.color z (u : Ω) = X.conv j} := by
    ext z
    simp only [Set.mem_inter_iff, mem_nbr, Set.mem_setOf_eq]
    exact and_congr_right fun _ => (X.color_conv_iff h.toIsConfiguration j (u : Ω) z).symm
  rw [h2]
  exact X.interNum_eq h b (X.conv j) a (u.2 : X.color x (u : Ω) = a)

/-- The degree of a vertex `y ∈ C_b` in `X̄ = (C_a, C_b; R_j)` is the intersection number
`p^b_{a,j}`, so it does not depend on `y`. -/
theorem degB_cellBip (h : X.IsCoherent) (x : Ω) (a b j : Fin X.rank)
    (y : ↥(X.nbr b x)) : (X.cellBip x a b j).degB y = X.interNum a j b := by
  rw [BipGraph.degB]
  have h1 : {u : ↥(X.nbr a x) | (u, y) ∈ (X.cellBip x a b j).E}
      = {u : ↥(X.nbr a x) | X.color (u : Ω) (y : Ω) = j} := rfl
  rw [h1]
  refine Eq.trans (ncard_subtype_setOf (X.nbr a x) (fun w => X.color w (y : Ω) = j)) ?_
  have h2 : X.nbr a x ∩ {u | X.color u (y : Ω) = j}
      = {z : Ω | X.color x z = a ∧ X.color z (y : Ω) = j} := rfl
  rw [h2]
  exact X.interNum_eq h a j b (y.2 : X.color x (y : Ω) = b)

/-- **Semiregularity of the bipartite graph between two cells.**  *"`X̄` is a semiregular
(Prop. 3.4.5) bipartite graph"* (proof of Lemma 9.3.1, §9.3, version 2.5, line 4062).
Both degrees are intersection numbers of the coherent configuration, hence constant. -/
theorem cellBip_isSemiregular (h : X.IsCoherent) (x : Ω) (a b j : Fin X.rank) :
    (X.cellBip x a b j).IsSemiregular :=
  ⟨⟨X.interNum b (X.conv j) a, X.degA_cellBip h x a b j⟩,
   ⟨X.interNum a j b, X.degB_cellBip h x a b j⟩⟩

end PartitionStructure

end Babai
