/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.3: Basic combinatorial properties of coherent configurations.
-/
import Workspace.Coherent.Configurations
import Workspace.Coherent.PrelimExtra
import Workspace.Higher.PrelimExtra

/-!
# §3.3 Basic combinatorial properties of coherent configurations

Convention 3.3.1: "For the rest of Section 3, all results will tacitly refer to a
(classical) coherent configuration `X = (Ω, c) = (Ω; R₁,…,R_r)` (where `[r]` is the set
of colors and `c : Ω × Ω → [r]` is the coloring of pairs) except where explicitly stated
otherwise."  In Lean the hypothesis `X.IsCoherent` is carried explicitly.

## Numbering map

| Paper | Lean |
|---|---|
| Convention 3.3.1 | (explicit `IsCoherent` hypotheses) |
| Observation 3.3.2 | `Babai.PartitionStructure.induced_isCoherent` |
| Observation 3.3.3 | `Babai.PartitionStructure.ofDigraph_isCoherent_iff` |
| Observation 3.3.4 | `.tailColor`, `.headColor`, `.vcolor_fst_eq`, `.vcolor_snd_eq`, `.rel_subset` |
| Observation 3.3.5 | `.outDegC_eq_interNum`, `.inDegC_eq_interNum`, `.outDegC_eq_of_vcolor_eq`, `.inDegC_eq_of_vcolor_eq` |
| Notation 3.3.6 | `.outDegOf`, `.inDegOf` |
| Corollary 3.3.7 | `.constituent_homogeneous_or_bipartite` |
| Corollary 3.3.8 | `.vcolor_isEquitableColoring` |
| Notation 3.3.9 | `List (Fin X.rank)`, `Set (List (Fin X.rank))` |
| Definition 3.3.10 | `.IsColorWalk`, `.numWalks` |
| Proposition 3.3.11 | `.exists_walkNum` (paper route: `.numWalks_singleton`, `.numWalks_pair`, Eq. (18) `.numWalks_eq18`), `.numWalks_eq_of_color_eq`; closed form `.numWalks_eq_walkNum` |
| Definition 3.3.12 | `.AccessibleAlong`, `.accessSet` |
| Corollary 3.3.13 | `.exists_accessibilitySet` |
| Theorem 3.3.14 | `.ncard_accessSet_eq` |
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

/-! ### Elementary consequences of Definition 3.1.1 -/

theorem rel_injective {i j : Fin X.rank} (h : X.rel i = X.rel j) : i = j := by
  obtain ⟨p, hp⟩ := X.rel_nonempty i
  have : p ∈ X.rel j := h ▸ hp
  rw [mem_rel] at hp this
  rw [← hp, this]

/-- Terminology 3.1.3.  `(i⁻)⁻ = i`. -/
theorem conv_conv (h : X.IsConfiguration) (i : Fin X.rank) : X.conv (X.conv i) = i := by
  refine X.rel_injective ?_
  rw [X.rel_conv h (X.conv i), X.rel_conv h i]
  ext p
  simp [invRel]

/-- Terminology 3.1.3.  `c(x,y) = i` iff `c(y,x) = i⁻`. -/
theorem color_conv_iff (h : X.IsConfiguration) (i : Fin X.rank) (x y : Ω) :
    X.color y x = X.conv i ↔ X.color x y = i := by
  constructor
  · intro hyx
    have := X.color_comm h y x
    rw [hyx] at this
    rw [this, X.conv_conv h]
  · rintro rfl
    exact X.color_comm h x y

/-! ### Observation 3.3.4: vertex-color awareness -/

/-- Observation 3.3.4.  The color of the tail of an edge of color `k`. -/
noncomputable def tailColor (k : Fin X.rank) : Fin X.rank :=
  X.vcolor (X.colorWitness k).1

/-- Observation 3.3.4.  The color of the head of an edge of color `k`. -/
noncomputable def headColor (k : Fin X.rank) : Fin X.rank :=
  X.vcolor (X.colorWitness k).2

/-- Observation 3.3.4 (Vertex-color awareness).  "The color of an edge determines the
colors of its tail and head."

Paper's proof: "Assume `c(x,y) = c(x',y') = i`.  We need to show that `c(x) = c(x')` and
`c(y) = c(y')`.  Let `c(x) = ℓ`, so `p^i_{ℓ,i} ≥ 1`.  It follows that
`(∃z')(c(x',z') = ℓ and c(z',y') = i)`.  But `ℓ` is a diagonal color, so `z' = x'` and
therefore `c(x') = c(x',x') = ℓ`.  So the color of the tail of the edge `(x,y)` is
determined by `c(x,y)`.  Now apply this fact to the color `i⁻` to see that the color of
the head is also determined." -/
theorem vcolor_fst_eq (h : X.IsCoherent) {x y : Ω} {k : Fin X.rank}
    (hxy : X.color x y = k) : X.vcolor x = X.tailColor k := by
  classical
  set x' := (X.colorWitness k).1 with hx'
  set y' := (X.colorWitness k).2 with hy'
  have hx'y' : X.color x' y' = k := X.color_colorWitness k
  -- `p^k_{c(x),k} ≥ 1` because `z = x` witnesses it for the pair `(x,y)`
  have h1 : {z : Ω | X.color x z = X.vcolor x ∧ X.color z y = k}.ncard
      = X.interNum (X.vcolor x) k k := X.interNum_eq h _ _ _ hxy
  have hxmem : x ∈ {z : Ω | X.color x z = X.vcolor x ∧ X.color z y = k} := ⟨rfl, hxy⟩
  have hfin : {z : Ω | X.color x z = X.vcolor x ∧ X.color z y = k}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton x) ?_
    rintro z ⟨hz, -⟩
    exact (h.diag x z x hz).symm
  have hpos : 0 < X.interNum (X.vcolor x) k k := by
    rw [← h1]
    exact Set.ncard_pos hfin |>.2 ⟨x, hxmem⟩
  -- hence the same intersection number is positive for the pair `(x', y')`
  have h2 : {z : Ω | X.color x' z = X.vcolor x ∧ X.color z y' = k}.ncard
      = X.interNum (X.vcolor x) k k := X.interNum_eq h _ _ _ hx'y'
  have hfin' : {z : Ω | X.color x' z = X.vcolor x ∧ X.color z y' = k}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton x') ?_
    rintro z ⟨hz, -⟩
    exact (h.diag x' z x hz).symm
  obtain ⟨z', hz'⟩ := (Set.ncard_pos hfin').1 (by rw [h2]; exact hpos)
  have hz'x : z' = x' := (h.diag x' z' x hz'.1).symm
  rw [hz'x] at hz'
  rw [tailColor, ← hx']
  show X.vcolor x = X.color x' x'
  exact hz'.1.symm

/-- Observation 3.3.4.  The color of an edge determines the color of its head. -/
theorem vcolor_snd_eq (h : X.IsCoherent) {x y : Ω} {k : Fin X.rank}
    (hxy : X.color x y = k) : X.vcolor y = X.headColor k := by
  classical
  -- apply the tail statement to the color `k⁻`
  have hyx : X.color y x = X.conv k := by rw [← hxy]; exact X.color_comm h.toIsConfiguration x y
  have hw : X.color (X.colorWitness k).2 (X.colorWitness k).1 = X.conv k := by
    have hc := X.color_comm h.toIsConfiguration (X.colorWitness k).1 (X.colorWitness k).2
    rwa [X.color_colorWitness k] at hc
  rw [X.vcolor_fst_eq h hyx, headColor, X.vcolor_fst_eq h hw]

/-- Observation 3.3.4, restated: `R_k ⊆ Ω_{tail} × Ω_{head}`. -/
theorem rel_subset (h : X.IsCoherent) (k : Fin X.rank) :
    X.rel k ⊆ X.vertexClass (X.tailColor k) ×ˢ X.vertexClass (X.headColor k) := by
  rintro ⟨x, y⟩ hxy
  exact ⟨X.vcolor_fst_eq h hxy, X.vcolor_snd_eq h hxy⟩

/-- Observation 3.3.4.  Two edges of the same color have tails of the same color and
heads of the same color. -/
theorem vcolor_eq_of_color_eq (h : X.IsCoherent) {x y x' y' : Ω}
    (hc : X.color x y = X.color x' y') : X.vcolor x = X.vcolor x' ∧ X.vcolor y = X.vcolor y' := by
  refine ⟨?_, ?_⟩
  · rw [X.vcolor_fst_eq h (k := X.color x y) rfl, X.vcolor_fst_eq h (k := X.color x y) hc.symm]
  · rw [X.vcolor_snd_eq h (k := X.color x y) rfl, X.vcolor_snd_eq h (k := X.color x y) hc.symm]

/-! ### Observation 3.3.5: degree awareness -/

section Degrees

variable [Fintype Ω]

/-- Observation 3.3.5 (Degree awareness).  "Let `c(x) = ℓ`.  Then the out-degree of `x` in
color `i` is `p^ℓ_{i,i⁻}`." -/
theorem outDegC_eq_interNum (h : X.IsCoherent) (i : Fin X.rank) (x : Ω) :
    X.outDegC i x = X.interNum i (X.conv i) (X.vcolor x) := by
  have hset : {z : Ω | X.color x z = i ∧ X.color z x = X.conv i} = X.nbr i x := by
    ext z
    simp only [Set.mem_setOf_eq, mem_nbr]
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, (X.color_conv_iff h.toIsConfiguration i x z).2 hz⟩⟩
  rw [outDegC_eq_ncard, ← hset]
  exact X.interNum_eq h i (X.conv i) (X.vcolor x) rfl

/-- Observation 3.3.5.  "…and the in-degree of `x` in color `i` is `p^ℓ_{i⁻,i}`." -/
theorem inDegC_eq_interNum (h : X.IsCoherent) (i : Fin X.rank) (y : Ω) :
    X.inDegC i y = X.interNum (X.conv i) i (X.vcolor y) := by
  have hset : {z : Ω | X.color y z = X.conv i ∧ X.color z y = i}
      = {x : Ω | X.color x y = i} := by
    ext z
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hz => hz.2, fun hz =>
      ⟨(X.color_conv_iff h.toIsConfiguration i z y).2 hz, hz⟩⟩
  rw [inDegC_eq_ncard, ← hset]
  exact X.interNum_eq h (X.conv i) i (X.vcolor y) rfl

/-- Observation 3.3.5 (Degree awareness).  "The color of a vertex determines its out- and
in-degree in any given color." -/
theorem outDegC_eq_of_vcolor_eq (h : X.IsCoherent) (i : Fin X.rank) {x y : Ω}
    (hxy : X.vcolor x = X.vcolor y) : X.outDegC i x = X.outDegC i y := by
  rw [X.outDegC_eq_interNum h, X.outDegC_eq_interNum h, hxy]

/-- Observation 3.3.5. -/
theorem inDegC_eq_of_vcolor_eq (h : X.IsCoherent) (i : Fin X.rank) {x y : Ω}
    (hxy : X.vcolor x = X.vcolor y) : X.inDegC i x = X.inDegC i y := by
  rw [X.inDegC_eq_interNum h, X.inDegC_eq_interNum h, hxy]

/-- Notation 3.3.6.  "Let `R_j ⊆ Ω_ℓ × Ω_m`.  We write `deg⁺_j` to denote the value
`deg⁺_j(x)` for any (and therefore all) `x ∈ Ω_ℓ`." -/
noncomputable def outDegOf (j : Fin X.rank) : ℕ :=
  X.outDegC j (X.colorWitness j).1

/-- Notation 3.3.6.  "…and `deg⁻_j` for `deg⁻_j(y)` for any (and therefore all)
`y ∈ Ω_m`." -/
noncomputable def inDegOf (j : Fin X.rank) : ℕ :=
  X.inDegC j (X.colorWitness j).2

theorem outDegC_eq_outDegOf (h : X.IsCoherent) (j : Fin X.rank) {x : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor j)) : X.outDegC j x = X.outDegOf j :=
  X.outDegC_eq_of_vcolor_eq h j (by rw [hx]; rfl)

theorem inDegC_eq_inDegOf (h : X.IsCoherent) (j : Fin X.rank) {y : Ω}
    (hy : y ∈ X.vertexClass (X.headColor j)) : X.inDegC j y = X.inDegOf j :=
  X.inDegC_eq_of_vcolor_eq h j (by rw [hy]; rfl)

/-- `deg⁺_j > 0`: an edge of color `j` exists, and its tail has color `tailColor j`. -/
theorem outDegOf_pos (h : X.IsCoherent) (j : Fin X.rank) : 0 < X.outDegOf j := by
  classical
  rw [outDegOf, outDegC_eq_ncard]
  refine (Set.ncard_pos (Set.toFinite _)).2 ⟨(X.colorWitness j).2, ?_⟩
  exact X.color_colorWitness j

/-- `deg⁻_j > 0`. -/
theorem inDegOf_pos (h : X.IsCoherent) (j : Fin X.rank) : 0 < X.inDegOf j := by
  classical
  rw [inDegOf, inDegC_eq_ncard]
  refine (Set.ncard_pos (Set.toFinite _)).2 ⟨(X.colorWitness j).1, ?_⟩
  exact X.color_colorWitness j

/-- Every vertex of the tail color of `k` is non-isolated in the extended constituent
`(Ω, R_k)`, i.e. lies in `Ω(k)`. -/
theorem vertexClass_tailColor_subset_effVertex (h : X.IsCoherent) (k : Fin X.rank) :
    X.vertexClass (X.tailColor k) ⊆ X.effVertex k := by
  intro x hx hiso
  have h0 : X.outDegC k x = 0 := by
    rw [outDegC, Digraph.outDeg, hiso.1, Set.ncard_empty]
  rw [X.outDegC_eq_outDegOf h k hx] at h0
  exact (X.outDegOf_pos h k).ne' h0

/-- The bipartite constituent between the tail color class and the head color class of
`k` is semiregular (Cor. 3.3.7 (ii)). -/
theorem inducedBip_isSemiregular (h : X.IsCoherent) (k : Fin X.rank)
    (hne : X.tailColor k ≠ X.headColor k) :
    ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
      (X.vertexClass (X.headColor k))).IsSemiregular := by
  classical
  constructor
  · refine ⟨X.outDegOf k, fun a => ?_⟩
    -- the out-neighbours of `a` in color `k` all lie in the head color class
    have himg : Subtype.val ''
        {b : X.vertexClass (X.headColor k) | (a, b) ∈
          ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
            (X.vertexClass (X.headColor k))).E} = X.nbr k (a : Ω) := by
      ext y
      constructor
      · rintro ⟨⟨b, hb⟩, hmem, rfl⟩
        exact hmem
      · intro hy
        exact ⟨⟨y, X.vcolor_snd_eq h hy⟩, hy, rfl⟩
    have hEq : {b : X.vertexClass (X.headColor k) | (a, b) ∈
        ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
          (X.vertexClass (X.headColor k))).E}.ncard = X.outDegC k (a : Ω) := by
      rw [outDegC_eq_ncard, ← himg,
        Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [BipGraph.degA, hEq, X.outDegC_eq_outDegOf h k a.2]
  · refine ⟨X.inDegOf k, fun b => ?_⟩
    have himg : Subtype.val ''
        {a : X.vertexClass (X.tailColor k) | (a, b) ∈
          ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
            (X.vertexClass (X.headColor k))).E} = {x : Ω | X.color x (b : Ω) = k} := by
      ext x
      constructor
      · rintro ⟨⟨a, ha⟩, hmem, rfl⟩
        exact hmem
      · intro hx
        exact ⟨⟨x, X.vcolor_fst_eq h hx⟩, hx, rfl⟩
    have hEq : {a : X.vertexClass (X.tailColor k) | (a, b) ∈
        ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
          (X.vertexClass (X.headColor k))).E}.ncard = X.inDegC k (b : Ω) := by
      rw [inDegC_eq_ncard, ← himg,
        Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [BipGraph.degB, hEq, X.inDegC_eq_inDegOf h k b.2]

/-! ### Degrees in induced subgraphs of an extended constituent -/

theorem outDeg_induced_ext (k : Fin X.rank) (A : Set Ω) (u : A) :
    ((X.extConstituent k).induced A).outDeg u = (X.nbr k (u : Ω) ∩ A).ncard := by
  have himg : Subtype.val '' (outNbr ((X.extConstituent k).induced A).E u)
      = X.nbr k (u : Ω) ∩ A := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
    · rintro ⟨hw, hwA⟩; exact ⟨⟨w, hwA⟩, hw, rfl⟩
  rw [Digraph.outDeg, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem inDeg_induced_ext (h : X.IsConfiguration) (k : Fin X.rank) (A : Set Ω) (u : A) :
    ((X.extConstituent k).induced A).inDeg u = (X.nbr (X.conv k) (u : Ω) ∩ A).ncard := by
  have himg : Subtype.val '' (inNbr ((X.extConstituent k).induced A).E u)
      = X.nbr (X.conv k) (u : Ω) ∩ A := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩
      exact ⟨(X.color_conv_iff h k z (u : Ω)).2 hmem, hz⟩
    · rintro ⟨hw, hwA⟩
      exact ⟨⟨w, hwA⟩, (X.color_conv_iff h k w (u : Ω)).1 hw, rfl⟩
  rw [Digraph.inDeg, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem degA_inducedBip_ext (k : Fin X.rank) (A B : Set Ω) (u : A) :
    ((X.extConstituent k).inducedBip A B).degA u = (X.nbr k (u : Ω) ∩ B).ncard := by
  have himg : Subtype.val '' {b : B | (u, b) ∈ ((X.extConstituent k).inducedBip A B).E}
      = X.nbr k (u : Ω) ∩ B := by
    ext w
    constructor
    · rintro ⟨⟨z, hz⟩, hmem, rfl⟩; exact ⟨hmem, hz⟩
    · rintro ⟨hw, hwB⟩; exact ⟨⟨w, hwB⟩, hw, rfl⟩
  rw [BipGraph.degA, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem degB_inducedBip_ext (h : X.IsConfiguration) (k : Fin X.rank) (A B : Set Ω)
    (w : B) :
    ((X.extConstituent k).inducedBip A B).degB w
      = (X.nbr (X.conv k) (w : Ω) ∩ A).ncard := by
  have himg : Subtype.val '' {a : A | (a, w) ∈ ((X.extConstituent k).inducedBip A B).E}
      = X.nbr (X.conv k) (w : Ω) ∩ A := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, hmem, rfl⟩
      exact ⟨(X.color_conv_iff h k a (w : Ω)).2 hmem, ha⟩
    · rintro ⟨hz, hzA⟩
      exact ⟨⟨z, hzA⟩, (X.color_conv_iff h k z (w : Ω)).1 hz, rfl⟩
  rw [BipGraph.degB, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]


/-! ### Consequences of vertex-color awareness used in Cor. 3.3.7 and Cor. 3.3.8 -/

theorem vertexClass_disjoint {c c' : Fin X.rank} (hcc : c ≠ c') :
    X.vertexClass c ∩ X.vertexClass c' = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, mem_vertexClass, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hz'
  exact hcc (hz.symm.trans hz')

theorem inNbr_eq_nbr_conv (h : X.IsConfiguration) (k : Fin X.rank) (u : Ω) :
    {z : Ω | X.color z u = k} = X.nbr (X.conv k) u := by
  ext z
  simp only [Set.mem_setOf_eq, mem_nbr]
  exact ⟨fun hz => (X.color_conv_iff h k z u).2 hz, fun hz => (X.color_conv_iff h k z u).1 hz⟩

theorem tailColor_conv (h : X.IsCoherent) (k : Fin X.rank) :
    X.tailColor (X.conv k) = X.headColor k := by
  have hc : X.color (X.colorWitness (X.conv k)).2 (X.colorWitness (X.conv k)).1 = k := by
    have := (X.color_conv_iff h.toIsConfiguration k (X.colorWitness (X.conv k)).2
      (X.colorWitness (X.conv k)).1).1 (X.color_colorWitness (X.conv k))
    exact this
  rw [tailColor, X.vcolor_snd_eq h hc]

theorem headColor_conv (h : X.IsCoherent) (k : Fin X.rank) :
    X.headColor (X.conv k) = X.tailColor k := by
  have hc : X.color (X.colorWitness (X.conv k)).2 (X.colorWitness (X.conv k)).1 = k := by
    have := (X.color_conv_iff h.toIsConfiguration k (X.colorWitness (X.conv k)).2
      (X.colorWitness (X.conv k)).1).1 (X.color_colorWitness (X.conv k))
    exact this
  rw [headColor, X.vcolor_fst_eq h hc]

theorem nbr_eq_empty_of_vcolor_ne (h : X.IsCoherent) (k : Fin X.rank) {u : Ω}
    (hu : X.vcolor u ≠ X.tailColor k) : X.nbr k u = ∅ := by
  ext y
  simp only [mem_nbr, Set.mem_empty_iff_false, iff_false]
  intro hy
  exact hu (X.vcolor_fst_eq h hy)

/-- The basic count behind Cor. 3.3.7 and Cor. 3.3.8: the number of `R_k`-out-neighbours
of `u` inside the vertex-color class `Ω_c`. -/
theorem ncard_nbr_inter_vertexClass (h : X.IsCoherent) (k c : Fin X.rank) (u : Ω) :
    (X.nbr k u ∩ X.vertexClass c).ncard =
      if X.vcolor u = X.tailColor k ∧ c = X.headColor k then X.outDegOf k else 0 := by
  classical
  by_cases hu : X.vcolor u = X.tailColor k
  · by_cases hc : c = X.headColor k
    · have hsub : X.nbr k u ⊆ X.vertexClass c := by
        intro y hy; rw [hc]; exact X.vcolor_snd_eq h hy
      rw [Set.inter_eq_left.2 hsub, if_pos ⟨hu, hc⟩, ← outDegC_eq_ncard,
        X.outDegC_eq_outDegOf h k hu]
    · have hempty : X.nbr k u ∩ X.vertexClass c = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 ?_
        rintro y ⟨hy, hyc⟩
        exact hc ((show X.vcolor y = c from hyc).symm.trans (X.vcolor_snd_eq h hy))
      rw [hempty, Set.ncard_empty, if_neg (by tauto)]
  · rw [X.nbr_eq_empty_of_vcolor_ne h k hu, Set.empty_inter, Set.ncard_empty,
      if_neg (by tauto)]

/-- Every vertex of `Ω(k)` has the tail color or the head color of `k`, and conversely. -/
theorem effVertex_eq (h : X.IsCoherent) (k : Fin X.rank) :
    X.effVertex k = X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k) := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hcon
    simp only [Set.mem_union, not_or, mem_vertexClass] at hcon
    refine hx ⟨?_, ?_⟩
    · exact X.nbr_eq_empty_of_vcolor_ne h k (fun hv => hcon.1 hv)
    · rw [show inNbr (X.extConstituent k).E x = {z : Ω | X.color z x = k} from rfl,
        X.inNbr_eq_nbr_conv h.toIsConfiguration k x]
      refine X.nbr_eq_empty_of_vcolor_ne h (X.conv k) ?_
      rw [X.tailColor_conv h k]
      exact fun hv => hcon.2 hv
  · rintro (hx | hx) hiso
    · obtain ⟨y, hy⟩ := (Set.ncard_pos (Set.toFinite (X.nbr k x))).1
        (by rw [← outDegC_eq_ncard, X.outDegC_eq_outDegOf h k hx]; exact X.outDegOf_pos h k)
      refine absurd (Set.eq_empty_iff_forall_notMem.1 hiso.1 y ?_) not_false
      exact hy
    · obtain ⟨y, hy⟩ := (Set.ncard_pos (Set.toFinite (X.nbr (X.conv k) x))).1
        (by
          rw [← outDegC_eq_ncard, X.outDegC_eq_outDegOf h (X.conv k)
            (by rw [X.tailColor_conv h k]; exact hx)]
          exact X.outDegOf_pos h (X.conv k))
      refine absurd (Set.eq_empty_iff_forall_notMem.1 hiso.2 y ?_) not_false
      show X.color y x = k
      exact (X.color_conv_iff h.toIsConfiguration k y x).1 hy

/-- Corollary 3.3.7 (Constituents: homogeneous or bipartite).  "For `k ≤ r`, the
constituent digraph `X_k = (Ω(k), R_k)` is either
(i) (homogeneous case) a biregular digraph with vertex set `Ω(k) = Ωᵢ` for some vertex
color `i` (in particular, all vertices of `X_k` have the same color), or
(ii) (bipartite case) a semiregular bipartite graph of the form `(Ωᵢ, Ω_j; R_k)` for some
distinct vertex colors `i` and `j` (so `R_k ⊆ Ωᵢ × Ω_j`; in particular, the vertices have
two colors)."

Paper's proof: "The first case arises when the tail and the head of an edge of color `k`
have the same color, `i`; this is in particular the case when `k` is a diagonal color.
The second when the color of the tail is `i` and the color of the head is `j ≠ i`.
Biregularity and semiregularity follow from Obs. 3.3.5." -/
theorem constituent_homogeneous_or_bipartite (h : X.IsCoherent) (k : Fin X.rank) :
    (X.tailColor k = X.headColor k ∧
      X.effVertex k = X.vertexClass (X.tailColor k) ∧
      ((X.extConstituent k).induced (X.vertexClass (X.tailColor k))).IsBiregular) ∨
    (X.tailColor k ≠ X.headColor k ∧
      X.rel k ⊆ X.vertexClass (X.tailColor k) ×ˢ X.vertexClass (X.headColor k) ∧
      X.effVertex k = X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k) ∧
      ((X.extConstituent k).inducedBip (X.vertexClass (X.tailColor k))
        (X.vertexClass (X.headColor k))).IsSemiregular) := by
  classical
  by_cases hij : X.tailColor k = X.headColor k
  · refine Or.inl ⟨hij, ?_, ?_⟩
    · rw [X.effVertex_eq h k, ← hij, Set.union_self]
    · constructor
      · refine ⟨X.outDegOf k, fun u => ?_⟩
        have h1 : ((X.extConstituent k).induced
            (X.vertexClass (X.tailColor k))).outDeg u
            = (X.nbr k (u : Ω) ∩ X.vertexClass (X.tailColor k)).ncard :=
          X.outDeg_induced_ext k _ u
        rw [h1, X.ncard_nbr_inter_vertexClass h k (X.tailColor k) (u : Ω),
          if_pos ⟨u.2, hij⟩]
      · refine ⟨X.outDegOf (X.conv k), fun u => ?_⟩
        have h1 : ((X.extConstituent k).induced
            (X.vertexClass (X.tailColor k))).inDeg u
            = (X.nbr (X.conv k) (u : Ω) ∩ X.vertexClass (X.tailColor k)).ncard :=
          X.inDeg_induced_ext h.toIsConfiguration k _ u
        rw [h1, X.ncard_nbr_inter_vertexClass h (X.conv k) (X.tailColor k) (u : Ω),
          if_pos ⟨by rw [X.tailColor_conv h k, ← hij]; exact u.2,
            by rw [X.headColor_conv h k]⟩]
  · exact Or.inr ⟨hij, X.rel_subset h k, X.effVertex_eq h k,
      X.inducedBip_isSemiregular h k hij⟩

/-- Corollary 3.3.8 (Vertex-coloring is equitable).  "Let `X = (Ω, c)` be a coherent
configuration.  Then the vertex coloring `c : Ω → [r]` is equitable for `X`." -/
theorem vcolor_isEquitableColoring (h : X.IsCoherent) :
    X.IsEquitableColoring X.vcolor := by
  classical
  intro k
  constructor
  · intro c
    constructor
    · refine ⟨if c = X.tailColor k ∧ c = X.headColor k then X.outDegOf k else 0,
        fun u => ?_⟩
      have h1 : ((X.extConstituent k).induced (X.vcolor ⁻¹' {c})).outDeg u
          = (X.nbr k (u : Ω) ∩ X.vertexClass c).ncard := X.outDeg_induced_ext k _ u
      rw [h1, X.ncard_nbr_inter_vertexClass h k c (u : Ω),
        show X.vcolor (u : Ω) = c from u.2]
    · refine ⟨if c = X.headColor k ∧ c = X.tailColor k
          then X.outDegOf (X.conv k) else 0, fun u => ?_⟩
      have h1 : ((X.extConstituent k).induced (X.vcolor ⁻¹' {c})).inDeg u
          = (X.nbr (X.conv k) (u : Ω) ∩ X.vertexClass c).ncard :=
        X.inDeg_induced_ext h.toIsConfiguration k _ u
      rw [h1, X.ncard_nbr_inter_vertexClass h (X.conv k) c (u : Ω),
        X.tailColor_conv h k, X.headColor_conv h k,
        show X.vcolor (u : Ω) = c from u.2]
  · intro c c' _
    constructor
    · refine ⟨if c = X.tailColor k ∧ c' = X.headColor k then X.outDegOf k else 0,
        fun u => ?_⟩
      have h1 : ((X.extConstituent k).inducedBip (X.vcolor ⁻¹' {c})
          (X.vcolor ⁻¹' {c'})).degA u = (X.nbr k (u : Ω) ∩ X.vertexClass c').ncard :=
        X.degA_inducedBip_ext k _ _ u
      rw [h1, X.ncard_nbr_inter_vertexClass h k c' (u : Ω),
        show X.vcolor (u : Ω) = c from u.2]
    · refine ⟨if c' = X.headColor k ∧ c = X.tailColor k
          then X.outDegOf (X.conv k) else 0, fun w => ?_⟩
      have h1 : ((X.extConstituent k).inducedBip (X.vcolor ⁻¹' {c})
          (X.vcolor ⁻¹' {c'})).degB w
          = (X.nbr (X.conv k) (w : Ω) ∩ X.vertexClass c).ncard :=
        X.degB_inducedBip_ext h.toIsConfiguration k _ _ w
      rw [h1, X.ncard_nbr_inter_vertexClass h (X.conv k) c (w : Ω),
        X.tailColor_conv h k, X.headColor_conv h k,
        show X.vcolor (w : Ω) = c' from w.2]

end Degrees

/-! ### §3.3 Walks and accessibility

Notation 3.3.9 (Strings, Kleene star): we use `List (Fin X.rank)` for `[r]*` and
`Set (List (Fin X.rank))` for subsets `L ⊆ [r]*`; concatenation is `List.append`, the
empty string `Λ` is `[]`. -/

/-- Definition 3.3.10 (Walks).  "Let `I = i₁…i_t` be a finite string of colors.  A *walk*
of length `t` of *color composition* `I` from vertex `x` to vertex `y` is a sequence
`(u₀,…,u_t)` of vertices such that `(∀j ≥ 1)(c(u_{j-1}, u_j) = i_j)`, where `u₀ = x` and
`u_t = y`." -/
def IsColorWalk (I : List (Fin X.rank)) (w : Fin (I.length + 1) → Ω) : Prop :=
  ∀ j : Fin I.length, X.color (w j.castSucc) (w j.succ) = I.get j

/-- Definition 3.3.10.  The set of walks of color composition `I` from `x` to `y`. -/
def colorWalks (I : List (Fin X.rank)) (x y : Ω) : Set (Fin (I.length + 1) → Ω) :=
  {w | X.IsColorWalk I w ∧ w 0 = x ∧ w (Fin.last I.length) = y}

/-- Definition 3.3.10.  The number of walks of color composition `I` from `x` to `y`. -/
noncomputable def numWalks (I : List (Fin X.rank)) (x y : Ω) : ℕ :=
  (X.colorWalks I x y).ncard

/-- Definition 3.3.10, in recursive form: there is a walk of color composition `I` from
`x` to `y`.  This is the form in which walks are used in §3.4.1; it is equivalent to the
nonemptiness of `colorWalks` (`isChainWalk_iff`). -/
def IsChainWalk (X : PartitionStructure Ω) : List (Fin X.rank) → Ω → Ω → Prop
  | [], x, y => x = y
  | i :: J, x, y => ∃ z, X.color x z = i ∧ IsChainWalk X J z y

@[simp] theorem isChainWalk_nil (x y : Ω) : X.IsChainWalk [] x y ↔ x = y := Iff.rfl

@[simp] theorem isChainWalk_cons (i : Fin X.rank) (J : List (Fin X.rank)) (x y : Ω) :
    X.IsChainWalk (i :: J) x y ↔ ∃ z, X.color x z = i ∧ X.IsChainWalk J z y := Iff.rfl

/-- The walks of color composition `Λ` (the empty string) from `x` to `y`: there is one if
`x = y`, none otherwise. -/
theorem numWalks_nil [Fintype Ω] [DecidableEq Ω] (x y : Ω) :
    X.numWalks [] x y = if x = y then 1 else 0 := by
  classical
  have hsub : ∀ j : Fin (([] : List (Fin X.rank)).length + 1), j = 0 :=
    fun j => Subsingleton.elim (α := Fin 1) j 0
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, numWalks, show X.colorWalks [] x x = {fun _ => x} from ?_,
      Set.ncard_singleton]
    ext w
    simp only [colorWalks, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h0, -⟩
      funext j
      rw [hsub j]
      exact h0
    · rintro rfl
      exact ⟨fun j => absurd j.2 (by simp), rfl, rfl⟩
  · rw [if_neg hxy, numWalks, Set.ncard_eq_zero (Set.toFinite _)]
    ext w
    simp only [colorWalks, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, h0, hl⟩
    rw [hsub (Fin.last _)] at hl
    exact hxy (h0.symm.trans hl)

/-- The recursion behind Prop. 3.3.11: a walk of color composition `i₁I` from `x` to `y`
is an edge of color `i₁` from `x` to some `z`, followed by a walk of color composition `I`
from `z` to `y`.  (The paper's Eq. (18) splits off the last two letters instead; splitting
off the first letter gives the same induction on the length of the string.) -/
theorem numWalks_cons [Fintype Ω] (i : Fin X.rank) (J : List (Fin X.rank)) (x y : Ω) :
    X.numWalks (i :: J) x y
      = ∑ z ∈ Finset.univ.filter (fun z => X.color x z = i), X.numWalks J z y := by
  classical
  rw [numWalks, Set.ncard_eq_toFinset_card',
    Finset.card_eq_sum_card_fiberwise (f := fun w => w 1)
      (t := Finset.univ.filter (fun z => X.color x z = i))
      (fun w hw => by
        simp only [Finset.mem_coe, Set.mem_toFinset] at hw
        obtain ⟨hwalk, h0, -⟩ := hw
        have hstep := hwalk 0
        simp only [Fin.castSucc_zero, List.get_cons_zero] at hstep
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
        rw [← h0]
        exact hstep)]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
  rw [numWalks, Set.ncard_eq_toFinset_card']
  refine Finset.card_nbij' (fun w => Fin.tail w) (fun v => Fin.cons x v) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    obtain ⟨⟨hwalk, h0, hl⟩, h1⟩ := hw
    simp only [Finset.mem_coe, Set.mem_toFinset]
    refine ⟨fun j => ?_, ?_, ?_⟩
    · have hstep := hwalk j.succ
      rw [← Fin.succ_castSucc] at hstep
      simpa [Fin.tail] using hstep
    · simpa [Fin.tail] using h1
    · simpa [Fin.tail] using hl
  · intro v hv
    simp only [Finset.mem_coe, Set.mem_toFinset] at hv
    obtain ⟨hwalk, h0, hl⟩ := hv
    simp only [Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq]
    refine ⟨⟨fun j => ?_, ?_, ?_⟩, ?_⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simpa [h0] using hz
      · have hstep := hwalk j'
        rw [← Fin.succ_castSucc]
        simpa using hstep
    · simp
    · simpa using hl
    · simpa [h0] using hz
  · intro w hw
    simp only [Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq] at hw
    have hx : w 0 = x := hw.1.2.1
    rw [← hx]
    exact Fin.cons_self_tail w
  · intro v _
    funext j
    rfl

/-- Prop. 3.3.11 and Def. 3.3.12: there is a walk of color composition `I` from `x` to `y`
exactly if the recursive `IsChainWalk` holds. -/
theorem isChainWalk_iff [Fintype Ω] [DecidableEq Ω] (I : List (Fin X.rank)) (x y : Ω) :
    X.IsChainWalk I x y ↔ (X.colorWalks I x y).Nonempty := by
  classical
  have hne : ∀ (I : List (Fin X.rank)) (x y : Ω),
      (X.colorWalks I x y).Nonempty ↔ X.numWalks I x y ≠ 0 := by
    intro I x y
    rw [numWalks, Set.nonempty_iff_ne_empty]
    constructor
    · intro h h0
      exact h ((Set.ncard_eq_zero (Set.toFinite _)).1 h0)
    · intro h h0
      exact h (by rw [h0, Set.ncard_empty])
  induction I generalizing x with
  | nil =>
    rw [hne, numWalks_nil]
    simp only [isChainWalk_nil]
    by_cases hxy : x = y <;> simp [hxy]
  | cons i J ih =>
    rw [hne, numWalks_cons]
    have hzero := Finset.sum_eq_zero_iff (s := Finset.univ.filter (fun z => X.color x z = i))
      (f := fun z => X.numWalks J z y)
    simp only [isChainWalk_cons, ne_eq, hzero, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall]
    constructor
    · rintro ⟨z, hz, hchain⟩
      exact ⟨z, hz, (hne J z y).1 ((ih z).1 hchain)⟩
    · rintro ⟨z, hz, hnz⟩
      exact ⟨z, hz, (ih z).2 ((hne J z y).2 hnz)⟩

/-- Concatenation of walks: a walk of color composition `IJ` is a walk of color
composition `I` followed by a walk of color composition `J`. -/
theorem isChainWalk_append (I J : List (Fin X.rank)) (x y : Ω) :
    X.IsChainWalk (I ++ J) x y ↔ ∃ z, X.IsChainWalk I x z ∧ X.IsChainWalk J z y := by
  induction I generalizing x with
  | nil =>
    simp only [List.nil_append, isChainWalk_nil]
    constructor
    · intro h; exact ⟨x, rfl, h⟩
    · rintro ⟨z, rfl, h⟩; exact h
  | cons i K ih =>
    simp only [List.cons_append, isChainWalk_cons, ih]
    constructor
    · rintro ⟨w, hw, z, h1, h2⟩
      exact ⟨z, ⟨w, hw, h1⟩, h2⟩
    · rintro ⟨z, ⟨w, hw, h1⟩, h2⟩
      exact ⟨w, hw, z, h1, h2⟩

/-- Accessibility in the extended constituent `(Ω, R_k)` is accessibility along the
strings `k* = {Λ, k, kk, …}` of Def. 3.3.12. -/
theorem accessible_extConstituent_iff (k : Fin X.rank) (x y : Ω) :
    (X.extConstituent k).Accessible x y ↔ ∃ t, X.IsChainWalk (List.replicate t k) x y := by
  rw [Digraph.accessible_iff_reflTransGen']
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + 1, ?_⟩
      rw [List.replicate_succ', isChainWalk_append]
      exact ⟨_, ht, ⟨_, hbc, rfl⟩⟩
  · rintro ⟨t, ht⟩
    induction t generalizing x with
    | zero =>
      rw [List.replicate_zero] at ht
      exact (show x = y from ht) ▸ Relation.ReflTransGen.refl
    | succ n ih =>
      rw [List.replicate_succ, isChainWalk_cons] at ht
      obtain ⟨z, hz, hchain⟩ := ht
      exact Relation.ReflTransGen.head (show (X.extConstituent k).Adj x z from hz)
        (ih z hchain)

open Classical in
/-- Proposition 3.3.11, the number `p(I,k)`: `p(Λ,k) = 1` iff `k` is diagonal, and
`p(i₁I, k) = ∑_{m≤r} p^k_{i₁,m}·p(I,m)`.  This explicit first-letter recursion is an
extra closed form (`numWalks_eq_walkNum`); the proof of Prop. 3.3.11 itself
(`exists_walkNum`) follows the paper's Eq. (18). -/
noncomputable def walkNum (X : PartitionStructure Ω) : List (Fin X.rank) → Fin X.rank → ℕ
  | [], k => if X.IsDiagonalColor k then 1 else 0
  | i :: J, k => ∑ m : Fin X.rank, X.interNum i m k * walkNum X J m

open Classical in
theorem walkNum_nil (k : Fin X.rank) :
    X.walkNum [] k = if X.IsDiagonalColor k then 1 else 0 := by
  rw [walkNum]

theorem walkNum_cons (i : Fin X.rank) (J : List (Fin X.rank)) (k : Fin X.rank) :
    X.walkNum (i :: J) k = ∑ m : Fin X.rank, X.interNum i m k * X.walkNum J m := by
  rw [walkNum]

open Classical in
/-- Proposition 3.3.11: the number of walks of color composition `I` from `x` to `y`
depends only on `I` and on the color `c(x,y)`. -/
theorem numWalks_eq_walkNum [Fintype Ω] [DecidableEq Ω] (h : X.IsCoherent)
    (I : List (Fin X.rank)) (x y : Ω) : X.numWalks I x y = X.walkNum I (X.color x y) := by
  induction I generalizing x with
  | nil =>
    rw [X.numWalks_nil, X.walkNum_nil]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos (X.isDiagonalColor_vcolor_aux x h.toIsConfiguration)]
    · rw [if_neg hxy, if_neg ?_]
      intro hd
      exact hxy (hd (show (x, y) ∈ X.rel (X.color x y) from rfl))
  | cons i J ih =>
    rw [X.numWalks_cons, X.walkNum_cons,
      Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ.filter fun z => X.color x z = i) =>
        ih z),
      ← Finset.sum_fiberwise_of_maps_to (g := fun z => X.color z y) (t := Finset.univ)
        (fun z _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_congr rfl (fun z (hz : z ∈ (Finset.univ.filter fun z => X.color x z = i).filter
        fun z => X.color z y = m) => by
      simp only [Finset.mem_filter] at hz
      rw [hz.2]), Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← X.interNum_eq h i m (X.color x y) rfl, Set.ncard_eq_toFinset_card']
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      Set.mem_setOf_eq]

/-- Walks of color composition `IJ` from `x` to `y` split at the vertex reached after `I`
(used for Eq. (18) in the proof of Prop. 3.3.11). -/
theorem numWalks_append [Fintype Ω] [DecidableEq Ω] (I J : List (Fin X.rank)) (x y : Ω) :
    X.numWalks (I ++ J) x y = ∑ z : Ω, X.numWalks I x z * X.numWalks J z y := by
  induction I generalizing x with
  | nil =>
    simp only [List.nil_append, X.numWalks_nil, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  | cons i K ih =>
    rw [List.cons_append, X.numWalks_cons]
    simp only [ih, X.numWalks_cons, Finset.sum_mul]
    exact Finset.sum_comm

/-- Prop. 3.3.11, the case `t = 1`: `p(i₁,k) = 1` if `i₁ = k` and `0` otherwise. -/
theorem numWalks_singleton [Fintype Ω] [DecidableEq Ω] (i : Fin X.rank) (x y : Ω) :
    X.numWalks [i] x y = if X.color x y = i then 1 else 0 := by
  rw [X.numWalks_cons]
  simp only [X.numWalks_nil, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

/-- Prop. 3.3.11, the case `t = 2`: `p(i₁i₂,k) = p^k_{i₁,i₂}`. -/
theorem numWalks_pair [Fintype Ω] [DecidableEq Ω] (h : X.IsCoherent) (a b : Fin X.rank)
    (x y : Ω) : X.numWalks [a, b] x y = X.interNum a b (X.color x y) := by
  rw [X.numWalks_cons]
  simp only [X.numWalks_singleton]
  rw [Finset.sum_boole, Nat.cast_id, ← X.interNum_eq h a b (X.color x y) rfl,
    Set.ncard_eq_toFinset_card', Finset.filter_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq]

/-- Eq. (18) in the proof of Prop. 3.3.11:
`#walks(i₁…i_{t-2}ab; x,y) = ∑_{ℓ≤r} #walks(i₁…i_{t-2}ℓ; x,y)·p^ℓ_{a,b}`. -/
theorem numWalks_eq18 [Fintype Ω] [DecidableEq Ω] (h : X.IsCoherent) (I : List (Fin X.rank))
    (a b : Fin X.rank) (x y : Ω) :
    X.numWalks (I ++ [a, b]) x y
      = ∑ ℓ : Fin X.rank, X.numWalks (I ++ [ℓ]) x y * X.interNum a b ℓ := by
  simp only [X.numWalks_append, X.numWalks_pair h, X.numWalks_singleton, mul_ite, mul_one,
    mul_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Proposition 3.3.11 (Counting walks).  "For every string `I = i₁…i_t` of colors and
color `k` there exists a number `p(I,k)` such that for any `x, y ∈ Ω` satisfying
`c(x,y) = k`, the number of walks of length `t` of color composition `I` from `x` to `y`
is `p(I,k)`."

The proof follows the paper: induction on `t`, with `p(Λ,k) = 1` iff `k` is diagonal,
`p(i₁,k) = 1` iff `i₁ = k` (`numWalks_singleton`), `p(i₁i₂,k) = p^k_{i₁,i₂}`
(`numWalks_pair`), and for the inductive step Eq. (18)
`p(i₁…i_t,k) = ∑_{ℓ≤r} p(i₁…i_{t-2}ℓ, k)·p^ℓ_{i_{t-1},i_t}` (`numWalks_eq18`). -/
theorem exists_walkNum [Fintype Ω] (h : X.IsCoherent) :
    ∃ p : List (Fin X.rank) → Fin X.rank → ℕ,
      ∀ (I : List (Fin X.rank)) (k : Fin X.rank) (x y : Ω), X.color x y = k →
        X.numWalks I x y = p I k := by
  classical
  have key : ∀ (t : ℕ) (I : List (Fin X.rank)), I.length = t →
      ∃ q : Fin X.rank → ℕ, ∀ x y : Ω, X.numWalks I x y = q (X.color x y) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro I hI
      by_cases ht : t ≤ 2
      · match I, hI with
        | [], _ =>
          -- `t = 0`
          refine ⟨fun k => if X.IsDiagonalColor k then 1 else 0, fun x y => ?_⟩
          rw [X.numWalks_nil]
          dsimp only
          by_cases hxy : x = y
          · subst hxy
            rw [if_pos rfl, if_pos (X.isDiagonalColor_vcolor_aux x h.toIsConfiguration)]
          · rw [if_neg hxy, if_neg ?_]
            intro hd
            exact hxy (hd (show (x, y) ∈ X.rel (X.color x y) from rfl))
        | [i], _ =>
          -- `t = 1`
          exact ⟨fun k => if k = i then 1 else 0, fun x y => X.numWalks_singleton i x y⟩
        | [a, b], _ =>
          -- `t = 2`
          exact ⟨X.interNum a b, fun x y => X.numWalks_pair h a b x y⟩
        | _ :: _ :: _ :: _, hI =>
          simp only [List.length_cons] at hI
          omega
      · -- the inductive step, `t ≥ 3`: write `I = J ++ [a, b]` and use Eq. (18)
        have hsplit : I = I.take (t - 2) ++ I.drop (t - 2) := (List.take_append_drop _ _).symm
        obtain ⟨a, b, hab⟩ := List.length_eq_two.1
          (show (I.drop (t - 2)).length = 2 by rw [List.length_drop]; omega)
        rw [hab] at hsplit
        have hJ : ∀ ℓ : Fin X.rank, (I.take (t - 2) ++ [ℓ]).length < t := by
          intro ℓ
          rw [List.length_append, List.length_take]
          simp only [List.length_singleton]
          omega
        choose q hq using fun ℓ : Fin X.rank => ih _ (hJ ℓ) _ rfl
        refine ⟨fun k => ∑ ℓ : Fin X.rank, q ℓ k * X.interNum a b ℓ, fun x y => ?_⟩
        rw [hsplit, X.numWalks_eq18 h]
        exact Finset.sum_congr rfl fun ℓ _ => by rw [hq ℓ x y]
  refine ⟨fun I => (key I.length I rfl).choose, fun I k x y hxy => ?_⟩
  rw [(key I.length I rfl).choose_spec x y, hxy]

/-- Proposition 3.3.11, restated. -/
theorem numWalks_eq_of_color_eq [Fintype Ω] (h : X.IsCoherent)
    (I : List (Fin X.rank)) {x y u v : Ω} (hc : X.color x y = X.color u v) :
    X.numWalks I x y = X.numWalks I u v := by
  obtain ⟨p, hp⟩ := X.exists_walkNum h
  rw [hp I (X.color x y) x y rfl, hp I (X.color x y) u v hc.symm]

/-- Definition 3.3.12 (Accessibility along strings of colors).  "Given a (not necessarily
finite) set `S ⊆ [r]*` of finite strings of colors, we say that vertex `y` is *accessible
from* vertex `x` *along* `S` if `(∃w ∈ S)(y is accessible from x along a walk of color
composition w)`." -/
def AccessibleAlong (S : Set (List (Fin X.rank))) (x y : Ω) : Prop :=
  ∃ I ∈ S, (X.colorWalks I x y).Nonempty

/-- Definition 3.3.12.  "We write `S(x)` to denote the set of vertices accessible from `x`
along `S`." -/
def accessSet (S : Set (List (Fin X.rank))) (x : Ω) : Set Ω :=
  {y | X.AccessibleAlong S x y}

/-- Corollary 3.3.13 (Accessibility set).  "Given a (not necessarily finite) set
`S ⊆ [r]*` of finite strings of colors there exists a set `J ⊆ [r]` of colors such that
`(∀x,y ∈ Ω)(y ∈ S(x) ⟺ c(x,y) ∈ J)`.  We write `J = J(S)` and call this the
*accessibility set* of `S`."

Paper's proof: "Define `J` by letting `j ∈ J ⟺ (∃w ∈ S)(p(wj) ≠ 0)` where the function
`p` is defined in Prop. 3.3.11." -/
theorem exists_accessibilitySet [Fintype Ω] (h : X.IsCoherent)
    (S : Set (List (Fin X.rank))) :
    ∃ J : Set (Fin X.rank), ∀ x y : Ω, y ∈ X.accessSet S x ↔ X.color x y ∈ J := by
  classical
  refine ⟨{j | ∃ I ∈ S, X.numWalks I (X.colorWitness j).1 (X.colorWitness j).2 ≠ 0}, ?_⟩
  intro x y
  constructor
  · rintro ⟨I, hI, hne⟩
    refine ⟨I, hI, ?_⟩
    have heq := X.numWalks_eq_of_color_eq h I
      (x := (X.colorWitness (X.color x y)).1) (y := (X.colorWitness (X.color x y)).2)
      (u := x) (v := y) (X.color_colorWitness (X.color x y))
    rw [heq, numWalks]
    intro hz
    exact (Set.nonempty_iff_ne_empty.1 hne) ((Set.ncard_eq_zero (Set.toFinite _)).1 hz)
  · rintro ⟨I, hI, hne⟩
    refine ⟨I, hI, ?_⟩
    have := X.numWalks_eq_of_color_eq h I
      (x := (X.colorWitness (X.color x y)).1) (y := (X.colorWitness (X.color x y)).2)
      (u := x) (v := y) (X.color_colorWitness (X.color x y))
    rw [this] at hne
    rw [Set.nonempty_iff_ne_empty]
    intro hz
    rw [numWalks, hz, Set.ncard_empty] at hne
    exact hne rfl

/-- Theorem 3.3.14 (Accessibility).  "Let `S ⊆ [r]*` be a (not necessarily finite) set of
finite strings of colors.  Let `x, y ∈ Ω` have the same color: `c(x) = c(y)`.  Then
`|S(x)| = |S(y)|`."

Paper's proof: "Let `i = c(x) = c(y)`.  Let `J = J(S)` be the accessibility set of `S`.
Then `|S(x)| = ∑_{j∈J} deg⁺_j(x)`.  Let `J' ⊆ J` consist of those `j ∈ J` for which the
tail of an edge of color `j` has color `i` (see Obs. 3.3.4).  So
`|S(x)| = ∑_{j∈J'} deg⁺_j = |S(y)|` by the Degree-awareness lemma (Obs. 3.3.5)." -/
theorem ncard_accessSet_eq [Fintype Ω] (h : X.IsCoherent)
    (S : Set (List (Fin X.rank))) {x y : Ω} (hxy : X.vcolor x = X.vcolor y) :
    (X.accessSet S x).ncard = (X.accessSet S y).ncard := by
  classical
  obtain ⟨J, hJ⟩ := X.exists_accessibilitySet h S
  -- `S(x)` is the disjoint union of the sets `R_j(x)` for `j ∈ J`
  have key : ∀ z : Ω, (X.accessSet S z).ncard
      = ∑ j ∈ Finset.univ.filter (fun j => j ∈ J), X.outDegC j z := by
    intro z
    rw [Set.ncard_eq_toFinset_card',
      Finset.card_eq_sum_card_fiberwise (f := fun w => X.color z w)
        (t := Finset.univ.filter (fun j => j ∈ J))
        (fun w hw => by simpa using (hJ z w).1 (Set.mem_toFinset.1 hw))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [outDegC_eq_ncard, Set.ncard_eq_toFinset_card']
    congr 1
    ext w
    simp only [Finset.mem_filter, Set.mem_toFinset, mem_nbr]
    constructor
    · rintro ⟨-, hw⟩; exact hw
    · intro hw
      refine ⟨(hJ z w).2 ?_, hw⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rwa [hw]
  rw [key x, key y]
  exact Finset.sum_congr rfl fun j _ => X.outDegC_eq_of_vcolor_eq h j hxy

/-- Observation 3.3.2 (Stable is coherent).  "If `Δ ⊆ Ω` is a stable subset (see
Def. 3.1.5) then the induced substructure `X[Δ]` is a coherent configuration." -/
theorem induced_isCoherent [Fintype Ω] (h : X.IsCoherent) {Δ : Set Ω} [Fintype Δ]
    (hΔ : X.IsStable Δ) : (X.induced Δ).IsCoherent := by
  classical
  refine ⟨X.induced_isConfiguration Δ h.toIsConfiguration, ?_⟩
  -- The key point: for `x ∈ Δ`, membership of `z` in `Δ` is decided by the color
  -- `c(x,z)`, because `Δ` is a union of vertex-color classes and `c(x,z)` determines
  -- `c(z)` (Obs. 3.3.4).  Hence a count inside `Δ` is a count in the whole of `Ω`.
  rw [isStable_iff] at hΔ
  -- `p'` is read off at the canonical pair realizing the color `k` of `X[Δ]`
  refine ⟨fun i j k => {z : Δ | (X.induced Δ).color ((X.induced Δ).colorWitness k).1 z = i ∧
      (X.induced Δ).color z ((X.induced Δ).colorWitness k).2 = j}.ncard, ?_⟩
  intro i j k x y hxy
  -- reduce to: the count depends only on the `X`-colors of `(x,y)`
  have key : ∀ (a b : Δ), X.color (a : Ω) (b : Ω) = X.color (x : Ω) (y : Ω) →
      {z : Δ | (X.induced Δ).color a z = i ∧ (X.induced Δ).color z b = j}.ncard
        = {z : Δ | (X.induced Δ).color x z = i ∧ (X.induced Δ).color z y = j}.ncard := by
    intro a b hab
    -- witnesses for the induced colors `i` and `j`
    obtain ⟨u₁, u₂, hu⟩ := (X.induced Δ).color_surjective i
    obtain ⟨v₁, v₂, hv⟩ := (X.induced Δ).color_surjective j
    set I := X.color (u₁ : Ω) (u₂ : Ω) with hI
    set J := X.color (v₁ : Ω) (v₂ : Ω) with hJ
    have hmem : ∀ (c : Δ) (z : Ω), X.color (c : Ω) z = I → z ∈ Δ := by
      intro c z hz
      refine hΔ (u₂ : Ω) u₂.2 z ?_
      have h1 : X.vcolor z = X.headColor I := X.vcolor_snd_eq h hz
      have h2 : X.vcolor (u₂ : Ω) = X.headColor I := X.vcolor_snd_eq h hI.symm
      rw [h1, h2]
    -- both sides count `{z ∈ Ω | c(·,z) = I and c(z,·) = J}`, which lies inside `Δ`
    have hcount : ∀ (c d : Δ),
        {z : Δ | (X.induced Δ).color c z = i ∧ (X.induced Δ).color z d = j}.ncard
          = {z : Ω | X.color (c : Ω) z = I ∧ X.color z (d : Ω) = J}.ncard := by
      intro c d
      have himg : Subtype.val ''
          {z : Δ | (X.induced Δ).color c z = i ∧ (X.induced Δ).color z d = j}
          = {z : Ω | X.color (c : Ω) z = I ∧ X.color z (d : Ω) = J} := by
        ext z
        constructor
        · rintro ⟨⟨w, hw⟩, ⟨h1, h2⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · exact (X.induced_color_eq_iff Δ c ⟨w, hw⟩ u₁ u₂).1 (by rw [h1, hu])
          · exact (X.induced_color_eq_iff Δ ⟨w, hw⟩ d v₁ v₂).1 (by rw [h2, hv])
        · rintro ⟨h1, h2⟩
          have hzΔ : z ∈ Δ := hmem c z h1
          refine ⟨⟨z, hzΔ⟩, ⟨?_, ?_⟩, rfl⟩
          · rw [← hu]
            exact (X.induced_color_eq_iff Δ c ⟨z, hzΔ⟩ u₁ u₂).2 h1
          · rw [← hv]
            exact (X.induced_color_eq_iff Δ ⟨z, hzΔ⟩ d v₁ v₂).2 h2
      rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [hcount a b, hcount x y, X.interNum_eq h I J (X.color (a : Ω) (b : Ω)) rfl,
      X.interNum_eq h I J (X.color (x : Ω) (y : Ω)) rfl, hab]
  exact (key _ _ ((X.induced_color_eq_iff Δ _ _ x y).1
    (((X.induced Δ).color_colorWitness k).trans hxy.symm))).symm

/-- The substructure induced on a set of vertices of one and the same color is
homogeneous (Def. 3.1.6).  In particular this applies to a vertex-color class, which is
the case used by the Design Lemma (§8.1). -/
theorem induced_isHomogeneous [Fintype Ω] {Δ : Set Ω} [Fintype Δ]
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, X.vcolor x = X.vcolor y) : (X.induced Δ).IsHomogeneous := by
  intro x y
  show (X.induced Δ).color x x = (X.induced Δ).color y y
  rw [X.induced_color_eq_iff]
  exact hΔ (x : Ω) x.2 (y : Ω) y.2

/-- A vertex-color class induces a homogeneous substructure. -/
theorem induced_vertexClass_isHomogeneous [Fintype Ω] (i : Fin X.rank)
    [Fintype (X.vertexClass i)] :
    (X.induced (X.vertexClass i)).IsHomogeneous :=
  X.induced_isHomogeneous (fun _ hx _ hy => hx.trans hy.symm)

/-- §8.1, "proof of equivalence": a substructure induced on a set of at least two
vertices which is *not* a clique configuration has rank `≥ 3`, hence is a UPCC as soon as
it is primitive (Def. 3.2.1).  Rank `≥ 2` is Def. 3.1.1 (`two_le_rank`), and rank `≠ 2` is
"not a clique" (Def. 3.1.8). -/
theorem three_le_rank_induced [Fintype Ω] (h : X.IsConfiguration) {Δ : Set Ω} [Fintype Δ]
    (hΔ : Δ.Nontrivial) (hne : (X.induced Δ).rank ≠ 2) : 3 ≤ (X.induced Δ).rank := by
  haveI : Nontrivial Δ := hΔ.coe_sort
  have h2 := (X.induced Δ).two_le_rank (X.induced_isConfiguration Δ h)
  omega

open Classical in
/-- Example 3.1.7.  The three-valued coloring behind the configuration `X(X)`: color `0`
on the diagonal, `1` on the edges, `2` on the non-edges. -/
noncomputable def digraphColor [Fintype Ω] [DecidableEq Ω] (Y : Digraph Ω) (x y : Ω) :
    Fin 3 :=
  if x = y then 0 else if (x, y) ∈ Y.E then 1 else 2

theorem ofDigraph_eq_ofColoring [Fintype Ω] [DecidableEq Ω] (Y : Digraph Ω) :
    ofDigraph Y = ofColoring (digraphColor Y) := rfl

/-- Observation 3.3.3.  "For a graph `X`, the configuration `X(X)` defined in
Example 3.1.7 is coherent if and only if `X` is strongly regular, including the case when
`X` is a clique."

Route.  Write `c` for the three-valued coloring (`Babai.PartitionStructure.digraphColor`)
and `N(x,y,a,b)` for the number of `z` with `c(x,z) = a` and `c(z,y) = b`.  For the
direction from coherence to strong regularity, the degree, the number of common
neighbours of an adjacent pair and the number of common neighbours of a non-adjacent pair
are all of the form `N(x,y,1,1)`, which coherence says depends only on `c(x,y)`.  For the
converse, the nine numbers `N(x,y,a,b)` satisfy a linear system whose solution is
determined by `c(x,y)` and by `n, k, λ, μ`: the row `a = 1` sums to `k`, the column
`b = 1` sums to `k`, all nine sum to `n`, the row `a = 0` and the column `b = 0` are
`0/1` vectors read off `c(x,y)`, and `N(x,y,1,1)` is `k`, `λ` or `μ`. -/
theorem ofDigraph_isCoherent_iff [Fintype Ω] [DecidableEq Ω] (Y : Digraph Ω)
    (hY : Y.IsGraph) :
    (ofDigraph Y).IsCoherent ↔
      ∃ n k lam mu : ℕ, Y.IsStronglyRegular n k lam mu := by
  classical
  set c : Ω → Ω → Fin 3 := digraphColor Y with hcdef
  have hcolor : ∀ x y u v : Ω,
      (ofDigraph Y).color x y = (ofDigraph Y).color u v ↔ c x y = c u v := by
    intro x y u v
    rw [ofDigraph_eq_ofColoring]
    exact ofColoring_color_eq_iff _ x y u v
  have hirr : ∀ u : Ω, (u, u) ∉ Y.E := by
    intro u hu
    exact absurd (Set.eq_empty_iff_forall_notMem.1 hY.irrefl (u, u) ⟨hu, rfl⟩) not_false
  have hsymmE : ∀ u v : Ω, (u, v) ∈ Y.E → (v, u) ∈ Y.E := by
    intro u v huv
    have h : ((u, v) : Ω × Ω) ∈ invRel Y.E := by rw [← hY.symm]; exact huv
    exact h
  have hc0 : ∀ x y : Ω, c x y = 0 ↔ x = y := by
    intro x y
    constructor
    · intro h
      by_contra hne
      rw [hcdef, digraphColor, if_neg hne] at h
      by_cases hE : (x, y) ∈ Y.E <;> simp [hE] at h
    · rintro rfl
      rw [hcdef, digraphColor, if_pos rfl]
  have hc1 : ∀ x y : Ω, c x y = 1 ↔ (x, y) ∈ Y.E := by
    intro x y
    constructor
    · intro h
      by_cases hne : x = y
      · rw [hcdef, digraphColor, if_pos hne] at h; simp at h
      · rw [hcdef, digraphColor, if_neg hne] at h
        by_cases hE : (x, y) ∈ Y.E
        · exact hE
        · rw [if_neg hE] at h; simp at h
    · intro hE
      have hne : x ≠ y := by rintro rfl; exact hirr x hE
      rw [hcdef, digraphColor, if_neg hne, if_pos hE]
  have hc2 : ∀ x y : Ω, c x y = 2 ↔ (x ≠ y ∧ (x, y) ∉ Y.E) := by
    intro x y
    constructor
    · intro h
      refine ⟨fun hne => ?_, fun hE => ?_⟩
      · rw [(hc0 x y).2 hne] at h; simp at h
      · rw [(hc1 x y).2 hE] at h; simp at h
    · rintro ⟨hne, hE⟩
      rw [hcdef, digraphColor, if_neg hne, if_neg hE]
  have hcases : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
  have hcsymm : ∀ x y : Ω, c x y = c y x := by
    intro x y
    rcases hcases (c x y) with h | h | h
    · rw [h, ((hc0 y x).2 ((hc0 x y).1 h).symm)]
    · rw [h, ((hc1 y x).2 (hsymmE x y ((hc1 x y).1 h)))]
    · obtain ⟨hne, hE⟩ := (hc2 x y).1 h
      rw [h, (hc2 y x).2 ⟨Ne.symm hne, fun hc => hE (hsymmE y x hc)⟩]
  constructor
  · -- coherent ⟹ strongly regular
    intro hcoh
    obtain ⟨p, hp⟩ := hcoh.intersection
    by_cases hE : ∀ u v : Ω, (u, v) ∉ Y.E
    · -- the empty graph is strongly regular
      have hnbr : ∀ u : Ω, outNbr Y.E u = ∅ := by
        intro u
        ext z
        simp only [mem_outNbr, Set.mem_empty_iff_false, iff_false]
        exact hE u z
      refine ⟨Fintype.card Ω, 0, 0, 0, hY, rfl, fun u => ?_, fun u v huv => ?_,
        fun u v _ _ => ?_⟩
      · show (outNbr Y.E u).ncard = 0
        rw [hnbr u, Set.ncard_empty]
      · exact absurd huv (hE u v)
      · rw [hnbr u, Set.empty_inter, Set.ncard_empty]
    · push_neg at hE
      obtain ⟨u₀, v₀, hu₀v₀⟩ := hE
      set i : Fin (ofDigraph Y).rank := (ofDigraph Y).color u₀ v₀ with hi
      -- the color-`i` neighbourhood of `u` is the neighbourhood of `u` in `Y`
      have hset : ∀ u v : Ω, {z : Ω | (ofDigraph Y).color u z = i ∧
          (ofDigraph Y).color z v = i} = outNbr Y.E u ∩ outNbr Y.E v := by
        intro u v
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_outNbr]
        rw [hi, hcolor, hcolor, (hc1 u₀ v₀).2 hu₀v₀]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(hc1 u z).1 h1, hsymmE z v ((hc1 z v).1 h2)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(hc1 u z).2 h1, (hc1 z v).2 (hsymmE v z h2)⟩
      have hval : ∀ u v : Ω, (outNbr Y.E u ∩ outNbr Y.E v).ncard
          = p i i ((ofDigraph Y).color u v) := by
        intro u v
        rw [← hset u v]
        exact hp i i ((ofDigraph Y).color u v) u v rfl
      have hreg : ∀ u : Ω, (outNbr Y.E u).ncard = (outNbr Y.E u₀).ncard := by
        intro u
        have h1 : outNbr Y.E u ∩ outNbr Y.E u = outNbr Y.E u := Set.inter_self _
        have h2 : outNbr Y.E u₀ ∩ outNbr Y.E u₀ = outNbr Y.E u₀ := Set.inter_self _
        have hcc : (ofDigraph Y).color u u = (ofDigraph Y).color u₀ u₀ :=
          (hcolor u u u₀ u₀).2 (by rw [(hc0 u u).2 rfl, (hc0 u₀ u₀).2 rfl])
        rw [← h1, ← h2, hval u u, hval u₀ u₀, hcc]
      have hadj : ∀ u v : Ω, (u, v) ∈ Y.E →
          (outNbr Y.E u ∩ outNbr Y.E v).ncard = (outNbr Y.E u₀ ∩ outNbr Y.E v₀).ncard := by
        intro u v huv
        have hcc : (ofDigraph Y).color u v = (ofDigraph Y).color u₀ v₀ :=
          (hcolor u v u₀ v₀).2 (by rw [(hc1 u v).2 huv, (hc1 u₀ v₀).2 hu₀v₀])
        rw [hval u v, hval u₀ v₀, hcc]
      by_cases hnon : ∃ a b : Ω, a ≠ b ∧ (a, b) ∉ Y.E
      · obtain ⟨a₀, b₀, hab, hnab⟩ := hnon
        refine ⟨Fintype.card Ω, (outNbr Y.E u₀).ncard,
          (outNbr Y.E u₀ ∩ outNbr Y.E v₀).ncard, (outNbr Y.E a₀ ∩ outNbr Y.E b₀).ncard,
          hY, rfl, hreg, hadj, fun u v hne hnadj => ?_⟩
        have hcc : (ofDigraph Y).color u v = (ofDigraph Y).color a₀ b₀ :=
          (hcolor u v a₀ b₀).2 (by
            rw [(hc2 u v).2 ⟨hne, hnadj⟩, (hc2 a₀ b₀).2 ⟨hab, hnab⟩])
        rw [hval u v, hval a₀ b₀, hcc]
      · refine ⟨Fintype.card Ω, (outNbr Y.E u₀).ncard,
          (outNbr Y.E u₀ ∩ outNbr Y.E v₀).ncard, 0, hY, rfl, hreg, hadj,
          fun u v hne hnadj => absurd ⟨u, v, hne, hnadj⟩ hnon⟩
  · -- strongly regular ⟹ coherent
    rintro ⟨n, k, lam, mu, hsr⟩
    have hn : Fintype.card Ω = n := hsr.card_eq
    -- the nine counts `N(x,y,a,b)`
    set N : Ω → Ω → Fin 3 → Fin 3 → ℕ :=
      fun x y a b => {z : Ω | c x z = a ∧ c z y = b}.ncard with hNdef
    have hsplit : ∀ (P : Ω → Prop) (g : Ω → Fin 3),
        {z : Ω | P z}.ncard = {z : Ω | P z ∧ g z = 0}.ncard
          + {z : Ω | P z ∧ g z = 1}.ncard + {z : Ω | P z ∧ g z = 2}.ncard := by
      intro P g
      have hd12 : Disjoint {z : Ω | P z ∧ g z = 1} {z : Ω | P z ∧ g z = 2} := by
        rw [Set.disjoint_left]
        rintro z ⟨-, h1⟩ ⟨-, h2⟩
        rw [h1] at h2
        simp at h2
      have hd0 : Disjoint {z : Ω | P z ∧ g z = 0}
          ({z : Ω | P z ∧ g z = 1} ∪ {z : Ω | P z ∧ g z = 2}) := by
        rw [Set.disjoint_left]
        rintro z ⟨-, h0⟩ (⟨-, h1⟩ | ⟨-, h2⟩)
        · rw [h0] at h1; simp at h1
        · rw [h0] at h2; simp at h2
      have hU : {z : Ω | P z} = {z : Ω | P z ∧ g z = 0}
          ∪ ({z : Ω | P z ∧ g z = 1} ∪ {z : Ω | P z ∧ g z = 2}) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_union]
        constructor
        · intro hz
          rcases hcases (g z) with h | h | h
          · exact Or.inl ⟨hz, h⟩
          · exact Or.inr (Or.inl ⟨hz, h⟩)
          · exact Or.inr (Or.inr ⟨hz, h⟩)
        · rintro (⟨hz, -⟩ | ⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
      rw [hU, Set.ncard_union_eq hd0 (Set.toFinite _) (Set.toFinite _),
        Set.ncard_union_eq hd12 (Set.toFinite _) (Set.toFinite _), ← add_assoc]
    have hrow : ∀ (x y : Ω) (a : Fin 3), {z : Ω | c x z = a}.ncard
        = N x y a 0 + N x y a 1 + N x y a 2 :=
      fun x y a => hsplit (fun z => c x z = a) (fun z => c z y)
    have hcolsum : ∀ (x y : Ω) (b : Fin 3), {z : Ω | c z y = b}.ncard
        = N x y 0 b + N x y 1 b + N x y 2 b := by
      intro x y b
      have hswap : ∀ a : Fin 3,
          {z : Ω | c z y = b ∧ c x z = a}.ncard = N x y a b := by
        intro a
        show {z : Ω | c z y = b ∧ c x z = a}.ncard = {z : Ω | c x z = a ∧ c z y = b}.ncard
        congr 1
        ext z
        exact and_comm
      rw [hsplit (fun z => c z y = b) (fun z => c x z), hswap 0, hswap 1, hswap 2]
    -- the degree
    have hdeg : ∀ x : Ω, {z : Ω | c x z = 1}.ncard = k := by
      intro x
      have h1 : (outNbr Y.E x).ncard = k := hsr.regular x
      rwa [show outNbr Y.E x = {z : Ω | c x z = 1} from by
        ext z; simp only [mem_outNbr, Set.mem_setOf_eq, hc1]] at h1
    have hdeg' : ∀ y : Ω, {z : Ω | c z y = 1}.ncard = k := by
      intro y
      have h1 : (outNbr Y.E y).ncard = k := hsr.regular y
      rwa [show outNbr Y.E y = {z : Ω | c z y = 1} from by
        ext z
        simp only [mem_outNbr, Set.mem_setOf_eq, hc1]
        exact ⟨fun h => hsymmE y z h, fun h => hsymmE z y h⟩] at h1
    -- the total
    have htot : ∀ x y : Ω, (N x y 0 0 + N x y 0 1 + N x y 0 2)
        + (N x y 1 0 + N x y 1 1 + N x y 1 2)
        + (N x y 2 0 + N x y 2 1 + N x y 2 2) = n := by
      intro x y
      rw [← hrow x y 0, ← hrow x y 1, ← hrow x y 2]
      have e : ∀ a : Fin 3, {z : Ω | True ∧ c x z = a} = {z : Ω | c x z = a} := by
        intro a; ext z; simp
      have h := hsplit (fun _ => True) (fun z => c x z)
      rw [e 0, e 1, e 2] at h
      have huniv : {_z : Ω | True} = (Set.univ : Set Ω) := rfl
      rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, hn] at h
      omega
    -- the row `a = 0` and the column `b = 0`
    have hzeroL : ∀ (x y : Ω) (b : Fin 3), N x y 0 b = if c x y = b then 1 else 0 := by
      intro x y b
      by_cases hb : c x y = b
      · rw [if_pos hb]
        show {z : Ω | c x z = 0 ∧ c z y = b}.ncard = 1
        have hs : {z : Ω | c x z = 0 ∧ c z y = b} = {x} := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, -⟩
            exact ((hc0 x z).1 h1).symm
          · rintro rfl
            exact ⟨(hc0 z z).2 rfl, hb⟩
        rw [hs, Set.ncard_singleton]
      · rw [if_neg hb]
        show {z : Ω | c x z = 0 ∧ c z y = b}.ncard = 0
        have hs : {z : Ω | c x z = 0 ∧ c z y = b} = ∅ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          rw [← ((hc0 x z).1 h1)] at h2
          exact hb h2
        rw [hs, Set.ncard_empty]
    have hzeroR : ∀ (x y : Ω) (a : Fin 3), N x y a 0 = if c x y = a then 1 else 0 := by
      intro x y a
      by_cases ha : c x y = a
      · rw [if_pos ha]
        show {z : Ω | c x z = a ∧ c z y = 0}.ncard = 1
        have hs : {z : Ω | c x z = a ∧ c z y = 0} = {y} := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨-, h2⟩
            exact (hc0 z y).1 h2
          · rintro rfl
            exact ⟨ha, (hc0 z z).2 rfl⟩
        rw [hs, Set.ncard_singleton]
      · rw [if_neg ha]
        show {z : Ω | c x z = a ∧ c z y = 0}.ncard = 0
        have hs : {z : Ω | c x z = a ∧ c z y = 0} = ∅ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          rw [(hc0 z y).1 h2] at h1
          exact ha h1
        rw [hs, Set.ncard_empty]
    -- the number of common neighbours
    have hN11 : ∀ x y : Ω, N x y 1 1 = (outNbr Y.E x ∩ outNbr Y.E y).ncard := by
      intro x y
      show {z : Ω | c x z = 1 ∧ c z y = 1}.ncard = _
      congr 1
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_outNbr]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(hc1 x z).1 h1, hsymmE z y ((hc1 z y).1 h2)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(hc1 x z).2 h1, (hc1 z y).2 (hsymmE y z h2)⟩
    have hN11_0 : ∀ x y : Ω, c x y = 0 → N x y 1 1 = k := by
      intro x y hxy
      rw [hN11, (hc0 x y).1 hxy, Set.inter_self]
      exact hsr.regular y
    have hN11_1 : ∀ x y : Ω, c x y = 1 → N x y 1 1 = lam := by
      intro x y hxy
      rw [hN11]
      exact hsr.common_adj x y ((hc1 x y).1 hxy)
    have hN11_2 : ∀ x y : Ω, c x y = 2 → N x y 1 1 = mu := by
      intro x y hxy
      obtain ⟨hne, hnadj⟩ := (hc2 x y).1 hxy
      rw [hN11]
      exact hsr.common_nonadj x y hne hnadj
    -- the nine counts are determined by the color of `(x,y)`
    have key : ∀ x y x' y' : Ω, c x y = c x' y' → ∀ a b : Fin 3,
        N x y a b = N x' y' a b := by
      intro x y x' y' hcc a b
      have r1 := hrow x y 1
      have r1' := hrow x' y' 1
      have c1 := hcolsum x y 1
      have c1' := hcolsum x' y' 1
      rw [hdeg x] at r1
      rw [hdeg x'] at r1'
      rw [hdeg' y] at c1
      rw [hdeg' y'] at c1'
      have t := htot x y
      have t' := htot x' y'
      have z00 := hzeroL x y 0
      have z01 := hzeroL x y 1
      have z02 := hzeroL x y 2
      have z10 := hzeroR x y 1
      have z20 := hzeroR x y 2
      have z00' := hzeroL x' y' 0
      have z01' := hzeroL x' y' 1
      have z02' := hzeroL x' y' 2
      have z10' := hzeroR x' y' 1
      have z20' := hzeroR x' y' 2
      rw [hcc] at z00 z01 z02 z10 z20
      rcases hcases (c x' y') with hv | hv | hv <;>
        rw [hv] at z00 z01 z02 z10 z20 z00' z01' z02' z10' z20' <;>
        norm_num at z00 z01 z02 z10 z20 z00' z01' z02' z10' z20'
      · have h11 := hN11_0 x y (by rw [hcc]; exact hv)
        have h11' := hN11_0 x' y' hv
        rcases hcases a with rfl | rfl | rfl <;> rcases hcases b with rfl | rfl | rfl <;>
          omega
      · have h11 := hN11_1 x y (by rw [hcc]; exact hv)
        have h11' := hN11_1 x' y' hv
        rcases hcases a with rfl | rfl | rfl <;> rcases hcases b with rfl | rfl | rfl <;>
          omega
      · have h11 := hN11_2 x y (by rw [hcc]; exact hv)
        have h11' := hN11_2 x' y' hv
        rcases hcases a with rfl | rfl | rfl <;> rcases hcases b with rfl | rfl | rfl <;>
          omega
    -- assemble the coherent configuration
    refine ⟨⟨fun x y z hxyz => ?_, fun u v x y huv => ?_⟩, ?_⟩
    · rw [hcolor, (hc0 z z).2 rfl] at hxyz
      exact (hc0 x y).1 hxyz
    · rw [hcolor] at huv ⊢
      rw [hcsymm v u, hcsymm y x]
      exact huv
    · refine ⟨fun i j k => N ((ofDigraph Y).colorWitness k).1
        ((ofDigraph Y).colorWitness k).2 (c ((ofDigraph Y).colorWitness i).1
          ((ofDigraph Y).colorWitness i).2) (c ((ofDigraph Y).colorWitness j).1
          ((ofDigraph Y).colorWitness j).2), ?_⟩
      intro i j k x y hxy
      have hi : ∀ (u v : Ω) (m : Fin (ofDigraph Y).rank),
          (ofDigraph Y).color u v = m ↔
            c u v = c ((ofDigraph Y).colorWitness m).1 ((ofDigraph Y).colorWitness m).2 := by
        intro u v m
        rw [← hcolor u v ((ofDigraph Y).colorWitness m).1 ((ofDigraph Y).colorWitness m).2,
          (ofDigraph Y).color_colorWitness m]
      have hsetN : {z : Ω | (ofDigraph Y).color x z = i ∧ (ofDigraph Y).color z y = j}
          = {z : Ω | c x z = c ((ofDigraph Y).colorWitness i).1
                ((ofDigraph Y).colorWitness i).2
              ∧ c z y = c ((ofDigraph Y).colorWitness j).1
                ((ofDigraph Y).colorWitness j).2} := by
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hi x z i, hi z y j]
      rw [hsetN]
      exact key x y _ _ ((hi x y k).1 hxy) _ _

end PartitionStructure

end Babai
