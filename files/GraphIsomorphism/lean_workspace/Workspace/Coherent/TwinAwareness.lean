/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.4.2: Twin awareness.
-/
import Workspace.Coherent.Classes
import Workspace.Coherent.PrelimExtra

/-!
# §3.4.2 Twin awareness

## Numbering map

| Paper | Lean |
|---|---|
| Cor. 3.3.7 (ii), the object `X_k = (Ωᵢ, Ω_j; R_k)` | `Babai.PartitionStructure.bipConstituent` |
| Lemma 3.4.10 | `.twinAwareness₁` (criterion: `.nbr_eq_iff_interNum`) |
| Theorem 3.4.11 | `.no_twins_in_primitive_color` |
| Lemma 3.4.12 | `.twinAwareness₂` (constituent: `.homConstituent`) |
| Lemma 3.4.13 | `.twinAwareness_extConstituent` |
| Theorem 3.4.14 | `.twinAwareness₃` (the digraph `Y`: `.unionConstituent`) |
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

section Bip

variable [Fintype Ω] [DecidableEq Ω]

/-- Corollary 3.3.7 (ii).  The bipartite constituent `X_k = (Ωᵢ, Ω_j; R_k)` of a color
`k` whose tail color `i` and head color `j` are distinct. -/
def bipConstituent (k : Fin X.rank) :
    BipGraph (X.vertexClass (X.tailColor k)) (X.vertexClass (X.headColor k)) :=
  (X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
    (X.vertexClass (X.headColor k))

theorem mem_bipConstituent {k : Fin X.rank}
    {a : X.vertexClass (X.tailColor k)} {b : X.vertexClass (X.headColor k)} :
    (a, b) ∈ (X.bipConstituent k).E ↔ X.color (a : Ω) (b : Ω) = k := Iff.rfl

/-- `R_k(x) ⊆ Ω_j` where `j` is the head color of `k` (Obs. 3.3.4). -/
theorem nbr_subset_headColor (h : X.IsCoherent) (k : Fin X.rank) (x : Ω) :
    X.nbr k x ⊆ X.vertexClass (X.headColor k) := fun _ hy => X.vcolor_snd_eq h hy

/-- `deg⁺_k(x) > 0` for `x` of the tail color of `k`; in particular `R_k(x) ≠ ∅`. -/
theorem nbr_nonempty (h : X.IsCoherent) (k : Fin X.rank) {x : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k)) : (X.nbr k x).Nonempty := by
  have hpos : 0 < (X.nbr k x).ncard := by
    rw [← outDegC_eq_ncard, X.outDegC_eq_outDegOf h k hx]
    exact X.outDegOf_pos h k
  exact (Set.ncard_pos (Set.toFinite _)).1 hpos

/-- The criterion behind Lemma 3.4.10 and Lemma 3.4.12, Case 1: for `x ≠ y` of the same
vertex color, `R_k(x) = R_k(y)` holds exactly if `p^{c(x,y)}_{k,k⁻} = p^{c(x)}_{k,k⁻}`,
a condition on the colors alone. -/
theorem nbr_eq_iff_interNum (h : X.IsCoherent) (k : Fin X.rank) {x y : Ω}
    (hv : X.vcolor x = X.vcolor y) :
    X.nbr k x = X.nbr k y ↔
      X.interNum k (X.conv k) (X.color x y) = X.interNum k (X.conv k) (X.vcolor x) := by
  classical
  -- `|R_k(x) ∩ R_k(y)| = p^{c(x,y)}_{k,k⁻}`
  have hinter : (X.nbr k x ∩ X.nbr k y).ncard = X.interNum k (X.conv k) (X.color x y) := by
    have hset : {z : Ω | X.color x z = k ∧ X.color z y = X.conv k}
        = X.nbr k x ∩ X.nbr k y := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_nbr]
      exact ⟨fun hz => ⟨hz.1, (X.color_conv_iff h.toIsConfiguration k y z).1 hz.2⟩,
        fun hz => ⟨hz.1, (X.color_conv_iff h.toIsConfiguration k y z).2 hz.2⟩⟩
    rw [← hset]
    exact X.interNum_eq h k (X.conv k) (X.color x y) rfl
  -- `|R_k(x)| = |R_k(y)| = p^{c(x)}_{k,k⁻}`
  have hx : (X.nbr k x).ncard = X.interNum k (X.conv k) (X.vcolor x) := by
    rw [← outDegC_eq_ncard]; exact X.outDegC_eq_interNum h k x
  have hy : (X.nbr k y).ncard = X.interNum k (X.conv k) (X.vcolor x) := by
    rw [← outDegC_eq_ncard, X.outDegC_eq_interNum h k y, hv]
  constructor
  · intro hEq
    rw [← hinter, hEq, Set.inter_self, hy]
  · intro hEq
    rw [← hinter] at hEq
    have h1 : X.nbr k x ∩ X.nbr k y = X.nbr k x :=
      (Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hEq, hx])
        (Set.toFinite _))
    have h2 : X.nbr k x ∩ X.nbr k y = X.nbr k y :=
      (Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by rw [hEq, hy])
        (Set.toFinite _))
    rw [← h1, h2]

/-- Observation 2.4.28 for the bipartite constituent: two vertices of `Ωᵢ` are twins in
`X_k` exactly if they have the same `R_k`-neighbourhood. -/
theorem isTwin_bipConstituent_iff (h : X.IsCoherent) (k : Fin X.rank)
    {x y : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k)) (hxy : x ≠ y) :
    IsTwin (X.bipConstituent k).Aut (Sum.inl ⟨x, hx⟩) (Sum.inl ⟨y, hy⟩) ↔
      X.nbr k x = X.nbr k y := by
  classical
  have hnoniso : ∀ {z : Ω} (hz : z ∈ X.vertexClass (X.tailColor k)),
      ¬ (X.bipConstituent k).toDigraph.IsIsolated (Sum.inl ⟨z, hz⟩) := by
    intro z hz hiso
    obtain ⟨w, hw⟩ := X.nbr_nonempty h k hz
    refine absurd (Set.eq_empty_iff_forall_notMem.1 hiso.1
      (Sum.inr ⟨w, X.vcolor_snd_eq h hw⟩) ?_) not_false
    exact ⟨⟨z, hz⟩, ⟨w, X.vcolor_snd_eq h hw⟩, rfl, rfl, hw⟩
  rw [BipGraph.isTwin_iff _ _ _ (hnoniso hx) (hnoniso hy)
    (fun hcon => hxy (congrArg Subtype.val hcon))]
  constructor
  · intro hEq
    ext w
    constructor
    · intro hw
      have : (⟨w, X.vcolor_snd_eq h hw⟩ : X.vertexClass (X.headColor k)) ∈
          {b | ((⟨x, hx⟩ : X.vertexClass (X.tailColor k)), b) ∈ (X.bipConstituent k).E} := hw
      rw [hEq] at this
      exact this
    · intro hw
      have : (⟨w, X.vcolor_snd_eq h hw⟩ : X.vertexClass (X.headColor k)) ∈
          {b | ((⟨y, hy⟩ : X.vertexClass (X.tailColor k)), b) ∈ (X.bipConstituent k).E} := hw
      rw [← hEq] at this
      exact this
  · intro hEq
    ext ⟨w, hw⟩
    simp only [Set.mem_setOf_eq, mem_bipConstituent]
    constructor
    · intro hc; exact (hEq ▸ (hc : w ∈ X.nbr k x) : w ∈ X.nbr k y)
    · intro hc; exact (hEq ▸ (hc : w ∈ X.nbr k y) : w ∈ X.nbr k x)

/-- Lemma 3.4.10 (Twin awareness 1).  "Let `Ωᵢ, Ω_j` be two distinct vertex-color classes
in the coherent configuration `X = (Ω, c)`.  Consider the bipartite constituent
`X_k = (Ω(k), R_k)` where `R_k ⊆ Ωᵢ × Ω_j`.  Then for all pairs `x, y ∈ Ωᵢ`, `x ≠ y`, the
color `c(x,y)` determines whether `x, y` are twins in `X_k`."

Paper's proof: "Let `c(x,y) = ℓ`.  Now `x, y` are twins in `X_k` if and only if
`R_k(x) = R_k(y)`.  The latter is equivalent to saying that `p^ℓ_{k,k⁻} = p^i_{k,k⁻}`.
This equality depends only on the colors involved." -/
theorem twinAwareness₁ (h : X.IsCoherent) (k : Fin X.rank)
    (hij : X.tailColor k ≠ X.headColor k)
    {x y x' y' : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k))
    (hx' : x' ∈ X.vertexClass (X.tailColor k))
    (hy' : y' ∈ X.vertexClass (X.tailColor k))
    (hxy : x ≠ y) (hx'y' : x' ≠ y') (hcol : X.color x y = X.color x' y') :
    (IsTwin (X.bipConstituent k).Aut (Sum.inl ⟨x, hx⟩) (Sum.inl ⟨y, hy⟩) ↔
      IsTwin (X.bipConstituent k).Aut (Sum.inl ⟨x', hx'⟩) (Sum.inl ⟨y', hy'⟩)) := by
  have hvxy : X.vcolor x = X.vcolor y := by rw [hx, hy]
  have hvx'y' : X.vcolor x' = X.vcolor y' := by rw [hx', hy']
  have hvxx' : X.vcolor x = X.vcolor x' := by rw [hx, hx']
  rw [X.isTwin_bipConstituent_iff h k hx hy hxy,
    X.isTwin_bipConstituent_iff h k hx' hy' hx'y',
    X.nbr_eq_iff_interNum h k hvxy, X.nbr_eq_iff_interNum h k hvx'y', hcol, hvxx']

/-- The neighbourhood form of Theorem 3.4.11, with the hypothesis that the two vertex
colors are distinct dropped: in a color `k` whose constituent is non-trivial and whose
tail color class induces a primitive subconfiguration, distinct vertices of the tail
color class have distinct `R_k`-neighbourhoods.

This is what the proof of Theorem 3.4.11 actually establishes (it never uses `i ≠ j`),
and it is what the proof of Theorem 3.4.19 needs: that proof appeals to Theorem 3.4.11
also in the case `i = j`, which Theorem 3.4.11 as stated does not cover.  See
the corrected paper. -/
theorem nbr_ne_of_primitive (h : X.IsCoherent) (k : Fin X.rank)
    (hnt : ¬ (X.bipConstituent k).IsTrivial)
    (hprim : (X.induced (X.vertexClass (X.tailColor k))).IsPrimitive)
    {x y : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k)) (hxy : x ≠ y) :
    X.nbr k x ≠ X.nbr k y := by
  classical
  intro htwin
  set Y := X.induced (X.vertexClass (X.tailColor k)) with hY
  -- the color, inside `X[Ωᵢ]`, of the pair `(x, y)`
  set l : Fin Y.rank := Y.color ⟨x, hx⟩ ⟨y, hy⟩ with hl
  have hYcfg : Y.IsConfiguration := X.induced_isConfiguration _ h.toIsConfiguration
  -- `l` is an off-diagonal color of `X[Ωᵢ]`
  have hloff : Y.IsOffDiagonalColor l := by
    rcases Y.diagonal_or_offDiagonal hYcfg l with hd | ho
    · exfalso
      have hmem : ((⟨x, hx⟩ : X.vertexClass (X.tailColor k)), (⟨y, hy⟩ :
          X.vertexClass (X.tailColor k))) ∈ Y.rel l := hl.symm
      exact hxy (congrArg Subtype.val
        (hd hmem : (⟨x, hx⟩ : X.vertexClass (X.tailColor k)) = ⟨y, hy⟩))
    · exact ho
  -- twins are preserved along `R_l`-edges, by Lemma 3.4.10
  have hstep : ∀ u v : X.vertexClass (X.tailColor k), (Y.extConstituent l).Adj u v →
      X.nbr k (u : Ω) = X.nbr k (v : Ω) := by
    intro u v huv
    by_cases huv' : (u : Ω) = (v : Ω)
    · rw [huv']
    have hc : X.color (u : Ω) (v : Ω) = X.color x y := by
      have hcl : Y.color u v = l := huv
      rw [hl] at hcl
      exact (X.induced_color_eq_iff (X.vertexClass (X.tailColor k)) u v ⟨x, hx⟩ ⟨y, hy⟩).1 hcl
    have hvxy : X.vcolor x = X.vcolor y := by rw [hx, hy]
    have hvuv : X.vcolor (u : Ω) = X.vcolor (v : Ω) := by rw [u.2, v.2]
    have hvxu : X.vcolor x = X.vcolor (u : Ω) := by rw [hx, u.2]
    rw [X.nbr_eq_iff_interNum h k hvuv, hc, ← hvxu]
    rw [X.nbr_eq_iff_interNum h k hvxy] at htwin
    exact htwin
  -- weak connectivity of the `l`-constituent of `X[Ωᵢ]` spreads this to all of `Ωᵢ`
  have hall : ∀ u v : X.vertexClass (X.tailColor k), X.nbr k (u : Ω) = X.nbr k (v : Ω) := by
    intro u v
    exact (Y.extConstituent l).weaklyAccessible_rel
      (r := fun a b : X.vertexClass (X.tailColor k) => X.nbr k (a : Ω) = X.nbr k (b : Ω))
      (fun _ => rfl) (fun hab => hab.symm) (fun hab hbc => hab.trans hbc)
      hstep (hprim.2 l hloff u v)
  -- so `W := R_k(x)` is the common neighbourhood of all of `Ωᵢ`
  have hWsub : X.nbr k x ⊆ X.vertexClass (X.headColor k) := X.nbr_subset_headColor h k x
  have hWne : (X.nbr k x).Nonempty := X.nbr_nonempty h k hx
  -- `W ≠ Ω_j`, else `X_k` would be complete
  have hWne' : X.nbr k x ≠ X.vertexClass (X.headColor k) := by
    intro hWeq
    refine hnt (Or.inr ?_)
    ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simp only [Set.mem_univ, iff_true]
    show X.color a b = k
    have hna : X.nbr k a = X.nbr k x := hall ⟨a, ha⟩ ⟨x, hx⟩
    have : b ∈ X.nbr k a := by rw [hna, hWeq]; exact hb
    exact this
  obtain ⟨u, hu⟩ := hWne
  obtain ⟨v, hv, hvW⟩ : ∃ v ∈ X.vertexClass (X.headColor k), v ∉ X.nbr k x := by
    by_contra hcon
    push_neg at hcon
    exact hWne' (Set.Subset.antisymm hWsub hcon)
  -- `deg⁻_k(u) ≠ 0` but `deg⁻_k(v) = 0`, contradicting degree awareness (Obs. 3.3.5)
  have hdu : X.inDegC k u ≠ 0 := by
    rw [inDegC_eq_ncard]
    intro h0
    rw [Set.ncard_eq_zero (Set.toFinite _)] at h0
    have hxu : x ∈ {z : Ω | X.color z u = k} := hu
    rw [h0] at hxu
    exact hxu
  have hdv : X.inDegC k v = 0 := by
    rw [inDegC_eq_ncard, Set.ncard_eq_zero (Set.toFinite _)]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hzi : z ∈ X.vertexClass (X.tailColor k) := X.vcolor_fst_eq h hz
    refine hvW ?_
    have := hall ⟨z, hzi⟩ ⟨x, hx⟩
    rw [← this]
    exact hz
  have h1 : X.inDegC k u = X.inDegOf k := X.inDegC_eq_inDegOf h k (hWsub hu)
  have h2 : X.inDegC k v = X.inDegOf k := X.inDegC_eq_inDegOf h k hv
  exact hdu (by rw [h1, ← h2, hdv])

/-- Theorem 3.4.11 (No twins in primitive color).  "Let `Ωᵢ, Ω_j` be two distinct
vertex-color classes in the coherent configuration `X = (Ω, c)`.  Consider the bipartite
constituent `X_k = (Ω(k), R_k)` where `R_k ⊆ Ωᵢ × Ω_j`.  Assume `X_k` is non-trivial
(non-empty and not complete).  Assume further that the induced subconfiguration `X[Ωᵢ]`
is primitive.  Then there are no `X_k`-twins in `Ωᵢ`."

Paper's proof: "Assume for a contradiction that `x, y ∈ Ωᵢ` (`x ≠ y`) are twins for `X_k`.
Let `c(x,y) = ℓ`.  By Lemma 3.4.10 it follows that every pair `(x',y') ∈ R_ℓ` are twins.
Now the twin-or-equal relation is an equivalence relation, so the transitive closure of
`R_ℓ` is a subset of the twin-or-equal relation.  But `X[Ωᵢ]` is primitive, so `R_ℓ` is
(strongly) connected and therefore its transitive closure is `Ωᵢ × Ωᵢ`.
We have shown that `Ωᵢ` is a single twin equivalence class.  This means the set `R_ℓ(x)`
is the same for all `x ∈ Ωᵢ`; let us call this set `W ⊆ Ω_j`.  Now `W ≠ ∅` and `W ≠ Ω_j`
since in either of these cases, `X_k` would be trivial.  Let `u ∈ W` and `v ∈ Ω_j \ W`.
Then `deg⁻_k(u) = |Ωᵢ| ≠ 0` and `deg⁻_k(v) = 0`, contradicting the semiregularity
of `X_k`."

(The paper writes `R_ℓ(x)` where it means `R_k(x)`; `ℓ` is the color of the pair `(x,y)`
inside `Ωᵢ`, while the neighbourhoods that are being compared are the `R_k`-ones.  The
argument uses connectivity only through the equivalence relation "same `R_k`-neighbourhood",
which is symmetric, so weak connectivity of `R_ℓ` suffices.) -/
theorem no_twins_in_primitive_color (h : X.IsCoherent) (k : Fin X.rank)
    (hij : X.tailColor k ≠ X.headColor k)
    (hnt : ¬ (X.bipConstituent k).IsTrivial)
    (hprim : (X.induced (X.vertexClass (X.tailColor k))).IsPrimitive)
    {x y : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k)) (hxy : x ≠ y) :
    ¬ IsTwin (X.bipConstituent k).Aut (Sum.inl ⟨x, hx⟩) (Sum.inl ⟨y, hy⟩) := by
  rw [X.isTwin_bipConstituent_iff h k hx hy hxy]
  exact X.nbr_ne_of_primitive h k hnt hprim hx hy hxy

end Bip

section Union

variable [Fintype Ω] [DecidableEq Ω]

/-! ### Lemmas 3.4.12, 3.4.13 and Theorem 3.4.14

The paper proves Lemma 3.4.12 (twins in a homogeneous constituent), then reduces
Lemma 3.4.13 (twins in an extended constituent) to it, and finally reduces
Theorem 3.4.14 (twins in a union of constituents) to Lemma 3.4.13.

Two points of the paper's argument need care, and they lead to the order used here.

* The criterion of Lemma 3.4.12, Case 1 ("`x, y` are twins in `X_k` if and only if
  `R_k(x) = R_k(y)`") fails when `k` is the diagonal color `i` of `Ωᵢ`: then `R_k` is the
  identity relation on `Ωᵢ`, so `R_k(x) = {x} ≠ {y} = R_k(y)` while every transposition is
  an automorphism of `X_k`.  See the corrected paper.  The statement of Lemma 3.4.12 is
  nevertheless true; what is needed is the exact criterion for a transposition to be a
  digraph automorphism (`Digraph.swap_mem_aut_iff`), which compares the neighbourhoods
  outside the pair `{x, y}`, and treats the edges inside `{x,y}` separately.
* For a *digraph* a transposition must also preserve in-neighbourhoods, which the paper's
  criterion does not mention.  This is harmless for the statements (both conditions are
  determined by `c(x,y)`), but it is used in the proofs below.

Consequently the work is done once, for a union `⋃_{k ∈ S} R_k` of constituents
(Theorem 3.4.14), and Lemma 3.4.13 (`S = {k}`) and Lemma 3.4.12 (restriction of the
extended constituent to `Ωᵢ`) are derived from it. -/

/-- The out-neighbourhood of `x` in the union `⋃_{k ∈ S} R_k` of the constituents with
colors in `S`. -/
def nbrS (S : Finset (Fin X.rank)) (x : Ω) : Set Ω := {z | X.color x z ∈ S}

/-- Theorem 3.4.14.  The digraph `Y = (Ω, ⋃_{k ∈ K} R_k)`. -/
def unionConstituent (S : Finset (Fin X.rank)) : Digraph Ω :=
  ⟨{p | X.color p.1 p.2 ∈ S}⟩

/-- The set of colors `k` with `k⁻ ∈ S`; the in-neighbourhoods for `S` are the
out-neighbourhoods for this set. -/
noncomputable def convSet (S : Finset (Fin X.rank)) : Finset (Fin X.rank) :=
  Finset.univ.filter (fun a => X.conv a ∈ S)

theorem mem_convSet {S : Finset (Fin X.rank)} {a : Fin X.rank} :
    a ∈ X.convSet S ↔ X.conv a ∈ S := by simp [convSet]

/-- `|N_S(x)| = ∑_{a ∈ S} p^{c(x)}_{a,a⁻}`: the size of the out-neighbourhood in the
union of the colors in `S` depends only on the vertex color of `x`. -/
theorem ncard_nbrS (h : X.IsCoherent) (S : Finset (Fin X.rank)) (x : Ω) :
    (X.nbrS S x).ncard = ∑ a ∈ S, X.interNum a (X.conv a) (X.vcolor x) := by
  classical
  rw [Set.ncard_eq_toFinset_card',
    Finset.card_eq_sum_card_fiberwise (f := fun z => X.color x z) (t := S)
      (by
        intro z hz
        simp only [Finset.mem_coe, Set.mem_toFinset, nbrS, Set.mem_setOf_eq] at hz ⊢
        exact hz)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hset : ((X.nbrS S x).toFinset.filter fun z => X.color x z = a)
      = (X.nbr a x).toFinset := by
    ext z
    simp only [Finset.mem_filter, Set.mem_toFinset, nbrS, Set.mem_setOf_eq, mem_nbr]
    exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ ha, hz⟩⟩
  rw [hset, ← Set.ncard_eq_toFinset_card', ← outDegC_eq_ncard, X.outDegC_eq_interNum h]

/-- `|N_S(x) ∩ N_S(y)| = ∑ p^{c(x,y)}_{a,b}`, the sum over the pairs `(a,b)` with `a ∈ S`
and `b⁻ ∈ S`: it depends only on the color `c(x,y)`. -/
theorem ncard_nbrS_inter (h : X.IsCoherent) (S : Finset (Fin X.rank)) (x y : Ω) :
    (X.nbrS S x ∩ X.nbrS S y).ncard
      = ∑ p ∈ Finset.univ.filter (fun p : Fin X.rank × Fin X.rank =>
          p.1 ∈ S ∧ X.conv p.2 ∈ S), X.interNum p.1 p.2 (X.color x y) := by
  classical
  have hconv : ∀ u v : Ω, X.color u v = X.conv (X.color v u) :=
    fun u v => X.color_comm h.toIsConfiguration v u
  rw [Set.ncard_eq_toFinset_card',
    Finset.card_eq_sum_card_fiberwise (f := fun z => (X.color x z, X.color z y))
      (t := Finset.univ.filter (fun p : Fin X.rank × Fin X.rank =>
        p.1 ∈ S ∧ X.conv p.2 ∈ S))
      (by
        intro z hz
        simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_inter_iff, nbrS,
          Set.mem_setOf_eq] at hz
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
        exact ⟨hz.1, by rw [← hconv y z]; exact hz.2⟩)]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hset : ((X.nbrS S x ∩ X.nbrS S y).toFinset.filter
      fun z => (X.color x z, X.color z y) = p)
      = {z : Ω | X.color x z = p.1 ∧ X.color z y = p.2}.toFinset := by
    ext z
    simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_inter_iff, nbrS,
      Set.mem_setOf_eq, Prod.ext_iff]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1 ▸ hp.1, by rw [hconv y z, h2]; exact hp.2⟩, h1, h2⟩
  rw [hset, ← Set.ncard_eq_toFinset_card', X.interNum_eq h p.1 p.2 (X.color x y) rfl]

/-- The number of the two points `x ≠ y` that lie in `P` is determined by the two
membership facts. -/
theorem _root_.Babai.ncard_inter_pair {Ω : Type*} [Fintype Ω] (P P' : Set Ω)
    {x y x' y' : Ω} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (h1 : x ∈ P ↔ x' ∈ P') (h2 : y ∈ P ↔ y' ∈ P') :
    (P ∩ ({x, y} : Set Ω)).ncard = (P' ∩ ({x', y'} : Set Ω)).ncard := by
  classical
  have hboth : ∀ (Q : Set Ω) (u v : Ω), u ∈ Q → v ∈ Q → Q ∩ ({u, v} : Set Ω) = {u, v} := by
    intro Q u v hu hv
    refine Set.inter_eq_right.2 ?_
    rintro z (rfl | rfl)
    · exact hu
    · exact hv
  have hfst : ∀ (Q : Set Ω) (u v : Ω), u ∈ Q → v ∉ Q → Q ∩ ({u, v} : Set Ω) = {u} := by
    intro Q u v hu hv
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzQ, rfl | rfl⟩
      · rfl
      · exact absurd hzQ hv
    · rintro rfl; exact ⟨hu, Or.inl rfl⟩
  have hsnd : ∀ (Q : Set Ω) (u v : Ω), u ∉ Q → v ∈ Q → Q ∩ ({u, v} : Set Ω) = {v} := by
    intro Q u v hu hv
    ext z
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzQ, rfl | rfl⟩
      · exact absurd hzQ hu
      · rfl
    · rintro rfl; exact ⟨hv, Or.inr rfl⟩
  have hnone : ∀ (Q : Set Ω) (u v : Ω), u ∉ Q → v ∉ Q → Q ∩ ({u, v} : Set Ω) = ∅ := by
    intro Q u v hu hv
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro z ⟨hzQ, rfl | rfl⟩
    · exact hu hzQ
    · exact hv hzQ
  by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
  · rw [hboth P x y hx hy, hboth P' x' y' (h1.1 hx) (h2.1 hy), Set.ncard_pair hxy,
      Set.ncard_pair hx'y']
  · rw [hfst P x y hx hy, hfst P' x' y' (h1.1 hx) (fun hc => hy (h2.2 hc))]
    simp
  · rw [hsnd P x y hx hy, hsnd P' x' y' (fun hc => hx (h1.2 hc)) (h2.1 hy)]
    simp
  · rw [hnone P x y hx hy, hnone P' x' y' (fun hc => hx (h1.2 hc)) (fun hc => hy (h2.2 hc))]

/-- Equality of the two neighbourhoods outside the pair `{x,y}`, in the form used by the
counting argument: two sets of equal size are equal exactly if their intersection has that
same size. -/
theorem nbrS_sdiff_eq_iff_ncard (S : Finset (Fin X.rank)) (x y : Ω) :
    (X.nbrS S x \ {x, y} = X.nbrS S y \ {x, y}) ↔
      (((X.nbrS S x ∩ X.nbrS S y) \ {x, y}).ncard = (X.nbrS S x \ {x, y}).ncard ∧
        ((X.nbrS S x ∩ X.nbrS S y) \ {x, y}).ncard = (X.nbrS S y \ {x, y}).ncard) := by
  classical
  have hinter : (X.nbrS S x \ {x, y}) ∩ (X.nbrS S y \ {x, y})
      = (X.nbrS S x ∩ X.nbrS S y) \ {x, y} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_diff]
    tauto
  constructor
  · intro heq
    rw [← hinter, heq, Set.inter_self]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← hinter] at h1 h2
    have e1 : (X.nbrS S x \ {x, y}) ∩ (X.nbrS S y \ {x, y}) = X.nbrS S x \ {x, y} :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left (le_of_eq h1.symm) (Set.toFinite _)
    have e2 : (X.nbrS S x \ {x, y}) ∩ (X.nbrS S y \ {x, y}) = X.nbrS S y \ {x, y} :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_right (le_of_eq h2.symm) (Set.toFinite _)
    rw [← e1, e2]

/-- The heart of Lemmas 3.4.12, 3.4.13 and Theorem 3.4.14: for `x ≠ y`, whether `x` and
`y` have the same out-neighbours outside `{x,y}` in the union of the colors of `S` is
determined by the color `c(x,y)`.

All quantities involved are intersection numbers: `|N_S(x)|` and `|N_S(y)|` depend only on
the vertex colors `c(x)` and `c(y)` (Obs. 3.3.5), `|N_S(x) ∩ N_S(y)|` only on `c(x,y)`,
and whether `x` or `y` lies in `N_S(x)` or `N_S(y)` only on `c(x)`, `c(y)`, `c(x,y)` and
`c(y,x) = c(x,y)⁻`. -/
theorem nbrS_sdiff_determined (h : X.IsCoherent) (S : Finset (Fin X.rank))
    {x y x' y' : Ω} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hcol : X.color x y = X.color x' y') :
    (X.nbrS S x \ {x, y} = X.nbrS S y \ {x, y}) ↔
      (X.nbrS S x' \ {x', y'} = X.nbrS S y' \ {x', y'}) := by
  classical
  have hvx : X.vcolor x = X.vcolor x' := (X.vcolor_eq_of_color_eq h hcol).1
  have hvy : X.vcolor y = X.vcolor y' := (X.vcolor_eq_of_color_eq h hcol).2
  have hyx : X.color y x = X.color y' x' := by
    rw [X.color_comm h.toIsConfiguration x y, X.color_comm h.toIsConfiguration x' y', hcol]
  -- the membership facts, each determined by the colors
  have hmem : ∀ (u v : Ω) (a b : Ω), X.color u v = X.color a b →
      (v ∈ X.nbrS S u ↔ b ∈ X.nbrS S a) := by
    intro u v a b hc
    simp only [nbrS, Set.mem_setOf_eq, hc]
  have hxx : X.color x x = X.color x' x' := hvx
  have hyy : X.color y y = X.color y' y' := hvy
  -- the three cardinalities transfer
  have hsplit : ∀ (P : Set Ω) (u v : Ω), (P ∩ ({u, v} : Set Ω)).ncard + (P \ {u, v}).ncard
      = P.ncard := fun P u v => Set.ncard_inter_add_ncard_diff_eq_ncard P _ (Set.toFinite _)
  have hPx : (X.nbrS S x).ncard = (X.nbrS S x').ncard := by
    rw [X.ncard_nbrS h, X.ncard_nbrS h, hvx]
  have hQy : (X.nbrS S y).ncard = (X.nbrS S y').ncard := by
    rw [X.ncard_nbrS h, X.ncard_nbrS h, hvy]
  have hPQ : (X.nbrS S x ∩ X.nbrS S y).ncard = (X.nbrS S x' ∩ X.nbrS S y').ncard := by
    rw [X.ncard_nbrS_inter h, X.ncard_nbrS_inter h, hcol]
  have hc1 : (X.nbrS S x \ {x, y}).ncard = (X.nbrS S x' \ {x', y'}).ncard := by
    have e1 := hsplit (X.nbrS S x) x y
    have e2 := hsplit (X.nbrS S x') x' y'
    have i := Babai.ncard_inter_pair (X.nbrS S x) (X.nbrS S x') hxy hx'y'
      (hmem x x x' x' hxx) (hmem x y x' y' hcol)
    omega
  have hc2 : (X.nbrS S y \ {x, y}).ncard = (X.nbrS S y' \ {x', y'}).ncard := by
    have e1 := hsplit (X.nbrS S y) x y
    have e2 := hsplit (X.nbrS S y') x' y'
    have i := Babai.ncard_inter_pair (X.nbrS S y) (X.nbrS S y') hxy hx'y'
      (hmem y x y' x' hyx) (hmem y y y' y' hyy)
    omega
  have hc3 : ((X.nbrS S x ∩ X.nbrS S y) \ {x, y}).ncard
      = ((X.nbrS S x' ∩ X.nbrS S y') \ {x', y'}).ncard := by
    have e1 := hsplit (X.nbrS S x ∩ X.nbrS S y) x y
    have e2 := hsplit (X.nbrS S x' ∩ X.nbrS S y') x' y'
    have i := Babai.ncard_inter_pair (X.nbrS S x ∩ X.nbrS S y) (X.nbrS S x' ∩ X.nbrS S y')
      hxy hx'y'
      (by
        simp only [Set.mem_inter_iff]
        exact and_congr (hmem x x x' x' hxx) (hmem y x y' x' hyx))
      (by
        simp only [Set.mem_inter_iff]
        exact and_congr (hmem x y x' y' hcol) (hmem y y y' y' hyy))
    omega
  rw [X.nbrS_sdiff_eq_iff_ncard S x y, X.nbrS_sdiff_eq_iff_ncard S x' y', hc1, hc2, hc3]

/-- The pointwise form of `nbrS_sdiff_determined`. -/
theorem out_cond_determined (h : X.IsCoherent) (S : Finset (Fin X.rank))
    {x y x' y' : Ω} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hcol : X.color x y = X.color x' y') :
    ((∀ w, w ≠ x → w ≠ y → (X.color x w ∈ S ↔ X.color y w ∈ S)) ↔
      (∀ w, w ≠ x' → w ≠ y' → (X.color x' w ∈ S ↔ X.color y' w ∈ S))) := by
  classical
  have key : ∀ u v : Ω, u ≠ v →
      ((∀ w, w ≠ u → w ≠ v → (X.color u w ∈ S ↔ X.color v w ∈ S)) ↔
        X.nbrS S u \ {u, v} = X.nbrS S v \ {u, v}) := by
    intro u v huv
    constructor
    · intro hc
      ext w
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, nbrS,
        Set.mem_setOf_eq, not_or]
      exact ⟨fun hw => ⟨(hc w hw.2.1 hw.2.2).1 hw.1, hw.2⟩,
        fun hw => ⟨(hc w hw.2.1 hw.2.2).2 hw.1, hw.2⟩⟩
    · intro heq w hwu hwv
      have h1 : w ∈ X.nbrS S u \ {u, v} ↔ w ∈ X.nbrS S v \ {u, v} := by rw [heq]
      simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, nbrS,
        Set.mem_setOf_eq, not_or] at h1
      constructor
      · intro hw; exact (h1.1 ⟨hw, hwu, hwv⟩).1
      · intro hw; exact (h1.2 ⟨hw, hwu, hwv⟩).1
  rw [key x y hxy, key x' y' hx'y']
  exact X.nbrS_sdiff_determined h S hxy hx'y' hcol

/-- Theorem 3.4.14 (Twin awareness 3).  "Let `K ⊆ [r]` be a set of colors.  Consider the
configuration `Y = (Ω, ⋃_{k ∈ K} R_k)`.  Then for all pairs `x, y ∈ Ω`, `x ≠ y`, the color
`c(x,y)` determines whether `x, y` are twins in `Y`."

Paper's proof: "`x, y` are twins in `Y` if and only if they are twins in the extended
constituent `(Ω, R_k)` for each `k ∈ K`.  So the result follows from Lemma 3.4.13."

That reduction is not used here: the counting argument behind Lemma 3.4.12 works verbatim
for a union of colors, so the union is treated directly and Lemma 3.4.13 is the case
`K = {k}`.  (The reduction the paper uses would require that an automorphism of the union
of the `R_k` preserves each `R_k` separately, which is not immediate.) -/
theorem twinAwareness₃ (h : X.IsCoherent) (S : Finset (Fin X.rank))
    {x y x' y' : Ω} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hcol : X.color x y = X.color x' y') :
    (IsTwin (X.unionConstituent S).Aut x y ↔ IsTwin (X.unionConstituent S).Aut x' y') := by
  classical
  have hvx : X.vcolor x = X.vcolor x' := (X.vcolor_eq_of_color_eq h hcol).1
  have hvy : X.vcolor y = X.vcolor y' := (X.vcolor_eq_of_color_eq h hcol).2
  have hyx : X.color y x = X.color y' x' := by
    rw [X.color_comm h.toIsConfiguration x y, X.color_comm h.toIsConfiguration x' y', hcol]
  have hE : ∀ u v : Ω, ((u, v) ∈ (X.unionConstituent S).E) ↔ X.color u v ∈ S := fun _ _ => Iff.rfl
  -- the in-neighbour condition is the out-neighbour condition for the converse colors
  have hEin : ∀ u v : Ω, ((v, u) ∈ (X.unionConstituent S).E) ↔ X.color u v ∈ X.convSet S := by
    intro u v
    rw [hE, X.mem_convSet, ← X.color_comm h.toIsConfiguration u v]
  simp only [IsTwin, hxy, hx'y', ne_eq, not_false_iff, true_and]
  rw [Digraph.swap_mem_aut_iff, Digraph.swap_mem_aut_iff]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · simp only [hE]
    exact X.out_cond_determined h S hxy hx'y' hcol
  · simp only [hEin]
    exact X.out_cond_determined h (X.convSet S) hxy hx'y' hcol
  · simp only [hE, hcol, hyx]
  · simp only [hE, show X.color x x = X.color x' x' from hvx,
      show X.color y y = X.color y' y' from hvy]

/-- Lemma 3.4.13.  "Let `k ∈ [r]` be a color.  Then for all pairs `x, y ∈ Ω`, `x ≠ y`, the
color `c(x,y)` determines whether `x, y` are twins in the extended constituent
`(Ω, R_k)`."

Paper's proof: "If `c(x) ≠ c(y)` then `x, y` are not twins; and this relation only depends
on `c(x,y)` by vertex-color awareness (Obs. 3.3.4).  Assume now that `c(x) = c(y) = i`.  If
`Ωᵢ ⊄ Ω(k)` then `x, y` are twins in `(Ω, R_k)` because they are isolated.  Finally assume
`Ωᵢ ⊆ Ω(k)`.  In this case, `x, y` are twins in the extended constituent `(Ω, R_k)` if and
only if they are twins in the constituent `X_k`.  So if `X_k` is homogeneous, the result
follows from Lemma 3.4.12; and if `X_k` is bipartite, the result follows by applying
Lemma 3.4.10 to `k` or to `k⁻`."

Here it is the case `K = {k}` of Theorem 3.4.14, whose proof is the counting argument of
Lemma 3.4.12 carried out for the extended constituent directly; see the section
introduction. -/
theorem twinAwareness_extConstituent (h : X.IsCoherent) (k : Fin X.rank)
    {x y x' y' : Ω} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hcol : X.color x y = X.color x' y') :
    (IsTwin (X.extConstituent k).Aut x y ↔ IsTwin (X.extConstituent k).Aut x' y') := by
  classical
  have hset : X.rel k = {p : Ω × Ω | X.color p.1 p.2 ∈ ({k} : Finset (Fin X.rank))} := by
    ext p; simp [rel]
  have hE : X.extConstituent k = X.unionConstituent {k} := congrArg Digraph.mk hset
  rw [hE]
  exact X.twinAwareness₃ h {k} hxy hx'y' hcol

/-- Corollary 3.3.7 (i).  The homogeneous constituent digraph `X_k = (Ωᵢ, R_k)` of a color
`k` whose tail and head colors are both `i`. -/
def homConstituent (k : Fin X.rank) : Digraph (X.vertexClass (X.tailColor k)) :=
  (X.extConstituent k).induced (X.vertexClass (X.tailColor k))

/-- For a homogeneous color `k` (tail color = head color = `i`), twins of `Ωᵢ` in the
constituent `X_k = (Ωᵢ, R_k)` are the same as twins in the extended constituent
`(Ω, R_k)`: all `R_k`-edges have both ends in `Ωᵢ`. -/
theorem isTwin_homConstituent_iff (h : X.IsCoherent) (k : Fin X.rank)
    (hk : X.tailColor k = X.headColor k)
    {x y : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k)) (hxy : x ≠ y) :
    (IsTwin (X.homConstituent k).Aut ⟨x, hx⟩ ⟨y, hy⟩ ↔ IsTwin (X.extConstituent k).Aut x y) := by
  classical
  have hne : (⟨x, hx⟩ : X.vertexClass (X.tailColor k)) ≠ ⟨y, hy⟩ :=
    fun hc => hxy (congrArg Subtype.val hc)
  -- every `R_k`-edge has both ends in `Ωᵢ`
  have hhead : ∀ u w : Ω, X.color u w = k → w ∈ X.vertexClass (X.tailColor k) := by
    intro u w hc
    show X.vcolor w = X.tailColor k
    rw [hk]; exact X.vcolor_snd_eq h hc
  have htail : ∀ u w : Ω, X.color u w = k → u ∈ X.vertexClass (X.tailColor k) :=
    fun u w hc => X.vcolor_fst_eq h hc
  simp only [IsTwin, hne, hxy, ne_eq, not_false_iff, true_and]
  rw [Digraph.swap_mem_aut_iff, Digraph.swap_mem_aut_iff]
  constructor
  · rintro ⟨hout, hin, h3, h4⟩
    refine ⟨fun w hwx hwy => ?_, fun w hwx hwy => ?_, h3, h4⟩
    · by_cases hw : w ∈ X.vertexClass (X.tailColor k)
      · exact hout ⟨w, hw⟩ (fun hc => hwx (congrArg Subtype.val hc))
          (fun hc => hwy (congrArg Subtype.val hc))
      · constructor
        · intro hc; exact absurd (hhead x w hc) hw
        · intro hc; exact absurd (hhead y w hc) hw
    · by_cases hw : w ∈ X.vertexClass (X.tailColor k)
      · exact hin ⟨w, hw⟩ (fun hc => hwx (congrArg Subtype.val hc))
          (fun hc => hwy (congrArg Subtype.val hc))
      · constructor
        · intro hc; exact absurd (htail w x hc) hw
        · intro hc; exact absurd (htail w y hc) hw
  · rintro ⟨hout, hin, h3, h4⟩
    refine ⟨fun w hwx hwy => ?_, fun w hwx hwy => ?_, h3, h4⟩
    · exact hout (w : Ω) (fun hc => hwx (Subtype.ext hc)) (fun hc => hwy (Subtype.ext hc))
    · exact hin (w : Ω) (fun hc => hwx (Subtype.ext hc)) (fun hc => hwy (Subtype.ext hc))

/-- Lemma 3.4.12 (Twin awareness 2).  "Let `Ωᵢ` be a vertex-color class in the coherent
configuration `X = (Ω, c)`.  Consider the homogeneous constituent digraph
`X_k = (Ωᵢ, R_k)` where `R_k ⊆ Ωᵢ × Ωᵢ`.  Then for all pairs `x, y ∈ Ωᵢ`, `x ≠ y`, the
color `c(x,y)` determines whether `x, y` are twins in `X_k`."

Paper's proof: "Let `c(x,y) = ℓ`.  Case 1: `ℓ ∉ {k, k⁻}`.  In this case, `x, y` are twins
in `X_k` if and only if `R_k(x) = R_k(y)` which is again equivalent to saying that
`p^ℓ_{k,k⁻} = p^i_{k,k⁻}`.  Case 2: `ℓ ∈ {k, k⁻}`.  In this case, if `k ≠ k⁻` then `x` and
`y` are not twins.  Assume now `k = k⁻ = ℓ`.  In this case, `x, y` are twins in `X_k` if
and only if `R_k(x) \ {y} = R_k(y) \ {x}` which is equivalent to saying that
`p^k_{k,k} = p^i_{k,k} − 1`."

The Case 1 criterion fails for the diagonal color `k = i` (see the section introduction and
the corrected paper); the statement is proved here from Lemma 3.4.13, whose proof is the same
counting argument applied to the neighbourhoods outside the pair `{x,y}`. -/
theorem twinAwareness₂ (h : X.IsCoherent) (k : Fin X.rank)
    (hk : X.tailColor k = X.headColor k)
    {x y x' y' : Ω} (hx : x ∈ X.vertexClass (X.tailColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k))
    (hx' : x' ∈ X.vertexClass (X.tailColor k))
    (hy' : y' ∈ X.vertexClass (X.tailColor k))
    (hxy : x ≠ y) (hx'y' : x' ≠ y') (hcol : X.color x y = X.color x' y') :
    (IsTwin (X.homConstituent k).Aut ⟨x, hx⟩ ⟨y, hy⟩ ↔
      IsTwin (X.homConstituent k).Aut ⟨x', hx'⟩ ⟨y', hy'⟩) := by
  rw [X.isTwin_homConstituent_iff h k hk hx hy hxy,
    X.isTwin_homConstituent_iff h k hk hx' hy' hx'y']
  exact X.twinAwareness_extConstituent h k hxy hx'y' hcol

end Union

end PartitionStructure


end Babai
