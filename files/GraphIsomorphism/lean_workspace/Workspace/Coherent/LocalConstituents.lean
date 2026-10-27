/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.4.3: Local constituents.  Theorem 3.4.19 is version 2.5's repair of the error
Harald Helfgott found in Split-or-Johnson (see Sec. 9.8).
-/
import Workspace.Coherent.TwinAwareness

/-!
# §3.4.3 Local constituents

## Numbering map

| Paper | Lean |
|---|---|
| Definition 3.4.15 | `Babai.PartitionStructure.localColoring` |
| Observation 3.4.16 | `.localColoring_refines` |
| Proposition 3.4.17 | `.localColoring_isEquitable` |
| Definition 3.4.18 | `.localConstituentDiag`, `.localConstituentBip` |
| Theorem 3.4.19 | `.nontriviality_of_local_constituent` |
-/

namespace Babai

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

/-- Definition 3.4.15 (Local coloring).  "Let `X = (Ω, c)` be a configuration and `x ∈ Ω`
a vertex.  The *`x`-local coloring* `c_x` of `Ω` is defined as `c_x(y) = c(x,y)` for
`y ∈ Ω`." -/
def localColoring (x : Ω) : Ω → Fin X.rank := fun y => X.color x y

/-- The color classes of the `x`-local coloring are the sets `Rᵢ(x)`. -/
@[simp] theorem localColoring_preimage (x : Ω) (i : Fin X.rank) :
    X.localColoring x ⁻¹' {i} = X.nbr i x := rfl

/-- Observation 3.4.16.  "If `X` is a coherent configuration then the local coloring `c_x`
is a refinement of the coloring `c` of `Ω`, i.e. if
`(∀y,z ∈ Ω)(c_x(y) = c_x(z) ⟹ c(y) = c(z))`."

Paper's proof: "Immediate from vertex-color awareness (Obs. 3.3.4)." -/
theorem localColoring_refines (h : X.IsCoherent) (x : Ω) {y z : Ω}
    (hyz : X.localColoring x y = X.localColoring x z) : X.vcolor y = X.vcolor z :=
  (X.vcolor_eq_of_color_eq h hyz).2

section Equitability

variable [Fintype Ω] [DecidableEq Ω]

/-- The counting identity behind Prop. 3.4.17: `|R_k(u) ∩ R_m(x)| = p^{c(x,u)}_{m,k⁻}`. -/
theorem ncard_nbr_inter_nbr (h : X.IsCoherent) (k m : Fin X.rank) (x u : Ω) :
    (X.nbr k u ∩ X.nbr m x).ncard = X.interNum m (X.conv k) (X.color x u) := by
  have hset : {z : Ω | X.color x z = m ∧ X.color z u = X.conv k}
      = X.nbr k u ∩ X.nbr m x := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_nbr]
    exact ⟨fun hz => ⟨(X.color_conv_iff h.toIsConfiguration k u z).1 hz.2, hz.1⟩,
      fun hz => ⟨hz.2, (X.color_conv_iff h.toIsConfiguration k u z).2 hz.1⟩⟩
  rw [← hset]
  exact X.interNum_eq h m (X.conv k) (X.color x u) rfl

/-- Proposition 3.4.17 (Equitability of local colorings).  "Each local coloring of a
coherent configuration is equitable."

Paper's proof: "Let `x ∈ Ω` and consider the `x`-local coloring `c_x`.  The color classes
are the sets `Rᵢ(x)` for `i ∈ [r]`.  Consider the extended constituent `X̂_k = (Ω, R_k)`.
We need to prove that `c_x` is an equitable coloring for `X̂_k`.  Let `ℓ, m ∈ [r]` be (not
necessarily distinct) colors.  We need to show that for `u ∈ R_ℓ(x)`, the quantities
`|R_k(u) ∩ R_m(x)|` and `|R_{k⁻}(u) ∩ R_m(x)|` do not depend on the particular choice
of `u`, only on the colors `k, ℓ, m`.  Indeed, `|R_k(u) ∩ R_m(x)| = p^ℓ_{m,k⁻}` and
`|R_{k⁻}(u) ∩ R_m(x)| = p^ℓ_{m,k}`." -/
theorem localColoring_isEquitable (h : X.IsCoherent) (x : Ω) :
    X.IsEquitableColoring (X.localColoring x) := by
  intro k
  constructor
  · -- biregularity of `X̂_k[R_ℓ(x)]`
    intro l
    constructor
    · refine ⟨X.interNum l (X.conv k) l, fun u => ?_⟩
      have h1 : ((X.extConstituent k).induced (X.localColoring x ⁻¹' {l})).outDeg u
          = (X.nbr k (u : Ω) ∩ X.nbr l x).ncard := X.outDeg_induced_ext k _ u
      rw [h1, X.ncard_nbr_inter_nbr h k l x (u : Ω)]
      congr 1
      exact u.2
    · refine ⟨X.interNum l k l, fun u => ?_⟩
      have h1 : ((X.extConstituent k).induced (X.localColoring x ⁻¹' {l})).inDeg u
          = (X.nbr (X.conv k) (u : Ω) ∩ X.nbr l x).ncard :=
        X.inDeg_induced_ext h.toIsConfiguration k _ u
      rw [h1, X.ncard_nbr_inter_nbr h (X.conv k) l x (u : Ω),
        X.conv_conv h.toIsConfiguration]
      congr 1
      exact u.2
  · -- semiregularity of `X̂_k[R_ℓ(x), R_m(x)]`
    intro l m _
    constructor
    · refine ⟨X.interNum m (X.conv k) l, fun u => ?_⟩
      have h1 : ((X.extConstituent k).inducedBip (X.localColoring x ⁻¹' {l})
          (X.localColoring x ⁻¹' {m})).degA u = (X.nbr k (u : Ω) ∩ X.nbr m x).ncard :=
        X.degA_inducedBip_ext k _ _ u
      rw [h1, X.ncard_nbr_inter_nbr h k m x (u : Ω)]
      congr 1
      exact u.2
    · refine ⟨X.interNum l k m, fun w => ?_⟩
      have h1 : ((X.extConstituent k).inducedBip (X.localColoring x ⁻¹' {l})
          (X.localColoring x ⁻¹' {m})).degB w
          = (X.nbr (X.conv k) (w : Ω) ∩ X.nbr l x).ncard :=
        X.degB_inducedBip_ext h.toIsConfiguration k _ _ w
      rw [h1, X.ncard_nbr_inter_nbr h (X.conv k) l x (w : Ω),
        X.conv_conv h.toIsConfiguration]
      congr 1
      exact w.2

/-- Definition 3.4.18 (Local constituents), the case `ℓ = m`.  "Let `X = (Ω, c)` be a
configuration, `x ∈ Ω` a vertex, and `k, ℓ, m ∈ [r]` colors; `X_k = (Ω(k), R_k)` is the
color-`k` constituent of `X`.  We define the *`x`-`(k,ℓ,m)`-local constituent* `Y` of `X`.
If `ℓ = m` then we define `Y` as the induced subgraph `X_k[R_ℓ(x)]`." -/
def localConstituentDiag (k l : Fin X.rank) (x : Ω) : Digraph (X.nbr l x) :=
  (X.extConstituent k).induced (X.nbr l x)

/-- Definition 3.4.18, the case `ℓ ≠ m`.  "If `ℓ ≠ m` then we define `Y` as the induced
bipartite subgraph `X_k[R_ℓ(x), R_m(x)]`." -/
def localConstituentBip (k l m : Fin X.rank) (x : Ω) :
    BipGraph (X.nbr l x) (X.nbr m x) :=
  (X.extConstituent k).inducedBip (X.nbr l x) (X.nbr m x)

/-- Theorem 3.4.19 (Nontriviality of local constituent).  "Let `X = (Ω, c)` be a coherent
configuration.  Let `i, j` be diagonal colors, `ℓ ≠ m` off-diagonal colors, and `x ∈ Ωᵢ`
such that `R_ℓ(x) ⊆ Ωᵢ` and `R_m(x) ⊆ Ω_j`.  Assume `|Ω_j|/2 < |R_m(x)| < |Ω_j|`.  Assume
further that the induced subconfiguration `X[Ωᵢ]` is primitive.  Then the
`x`-`(m,ℓ,m)`-local constituent `Y = X_m[R_ℓ(x), R_m(x)]` is nontrivial."

Paper's proof: "`Y` is semiregular by Prop. 3.4.17.  Let `u ∈ R_ℓ(x)`; so `u ∈ Ωᵢ`.
Therefore `deg⁺_m = |R_m(u)| = |R_m(x)| > |Ω_j|/2`, hence `R_m(x) ∩ R_m(u) ≠ ∅`.  Let
`w ∈ R_m(x) ∩ R_m(u)`.  That means `(u,w) ∈ R_m` hence `Y` is not empty.
What we need to prove is that `Y` is not complete.  Suppose for a contradiction that it
is.  So for `u ∈ R_ℓ(x)` we have `R_m(u) ⊇ R_m(x)`.  But `deg⁺_m = |R_m(u)| = |R_m(x)|`
and therefore `R_m(u) = R_m(x)`.  This means `u` and `x` are twins, contradicting the
'no twins in primitive color' theorem (Theorem 3.4.11), given our assumption that
`X[Ωᵢ]` is primitive."

Two hypotheses are added relative to the paper; both are recorded in the corrected paper.
* `hlne : (R_ℓ(x)).Nonempty`.  The paper's proof opens with "Let `u ∈ R_ℓ(x)`"; without
  this the statement is false (if `R_ℓ(x) = ∅` the inclusion `R_ℓ(x) ⊆ Ωᵢ` is vacuous and
  `Y` is the empty bipartite graph, hence trivial).
* The appeal to Theorem 3.4.11 is replaced by `nbr_ne_of_primitive`, which is what the
  proof of Theorem 3.4.11 establishes and which, unlike Theorem 3.4.11 as stated, also
  covers the case `i = j` that the hypotheses of Theorem 3.4.19 allow. -/
theorem nontriviality_of_local_constituent (h : X.IsCoherent)
    {i j l m : Fin X.rank} (hi : X.IsDiagonalColor i) (hj : X.IsDiagonalColor j)
    (hlm : l ≠ m) (hloff : X.IsOffDiagonalColor l) (hmoff : X.IsOffDiagonalColor m)
    {x : Ω} (hx : x ∈ X.vertexClass i)
    (hlx : X.nbr l x ⊆ X.vertexClass i) (hmx : X.nbr m x ⊆ X.vertexClass j)
    (hlne : (X.nbr l x).Nonempty)
    (hhalf : (X.vertexClass j).ncard < 2 * (X.nbr m x).ncard)
    (hlt : (X.nbr m x).ncard < (X.vertexClass j).ncard)
    (hprim : (X.induced (X.vertexClass i)).IsPrimitive) :
    ¬ (X.localConstituentBip m l m x).IsTrivial := by
  classical
  -- `R_m(x)` is nonempty, and `m` has tail color `i` and head color `j`
  have hmne : (X.nbr m x).Nonempty := by
    rcases Set.eq_empty_or_nonempty (X.nbr m x) with hem | hne
    · rw [hem, Set.ncard_empty] at hhalf; omega
    · exact hne
  obtain ⟨w₀, hw₀⟩ := hmne
  have htail : X.tailColor m = i := by rw [← X.vcolor_fst_eq h hw₀]; exact hx
  have hhead : X.headColor m = j := by rw [← X.vcolor_snd_eq h hw₀]; exact hmx hw₀
  -- every `u ∈ R_ℓ(x)` has the same `R_m`-degree as `x`
  have hdeg : ∀ u ∈ X.nbr l x, (X.nbr m u).ncard = (X.nbr m x).ncard := by
    intro u hu
    have hv : X.vcolor u = X.vcolor x := by rw [hlx hu, hx]
    have := X.outDegC_eq_of_vcolor_eq h m hv
    rwa [outDegC_eq_ncard, outDegC_eq_ncard] at this
  rintro (hempty | hcomplete)
  · -- `Y` is not empty
    obtain ⟨u, hu⟩ := hlne
    have hmu : X.nbr m u ⊆ X.vertexClass j := by
      intro z hz; rw [← hhead]; exact X.vcolor_snd_eq h hz
    -- `|R_m(u)| + |R_m(x)| > |Ω_j| ≥ |R_m(u) ∪ R_m(x)|`, so the two meet
    have hunion : (X.nbr m u ∪ X.nbr m x).ncard ≤ (X.vertexClass j).ncard :=
      Set.ncard_le_ncard (Set.union_subset hmu hmx) (Set.toFinite _)
    have hio := Set.ncard_inter_add_ncard_union (X.nbr m u) (X.nbr m x)
      (Set.toFinite _) (Set.toFinite _)
    have hdu := hdeg u hu
    have hpos : 0 < (X.nbr m u ∩ X.nbr m x).ncard := by omega
    obtain ⟨w, hwu, hwx⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    have : ((⟨u, hu⟩ : X.nbr l x), (⟨w, hwx⟩ : X.nbr m x)) ∈ (X.localConstituentBip m l m x).E :=
      hwu
    rw [hempty] at this
    exact this
  · -- `Y` is not complete
    obtain ⟨u, hu⟩ := hlne
    -- `R_m(x) ⊆ R_m(u)`, and the two have the same size, so they are equal
    have hsub : X.nbr m x ⊆ X.nbr m u := by
      intro z hz
      have : ((⟨u, hu⟩ : X.nbr l x), (⟨z, hz⟩ : X.nbr m x)) ∈
          (X.localConstituentBip m l m x).E := by rw [hcomplete]; trivial
      exact this
    have heq : X.nbr m x = X.nbr m u :=
      Set.eq_of_subset_of_ncard_le hsub (le_of_eq (hdeg u hu)) (Set.toFinite _)
    -- `u ≠ x` because `ℓ` is an off-diagonal color
    have hux : x ≠ u := by
      intro hcon
      refine absurd (Set.eq_empty_iff_forall_notMem.1 hloff (x, u) ⟨hu, ?_⟩) not_false
      exact hcon
    -- `X_m` is non-trivial: it is nonempty, and it is not complete because
    -- `|R_m(x)| < |Ω_j|`
    have hnt : ¬ (X.bipConstituent m).IsTrivial := by
      rintro (hE | hE)
      · refine absurd (Set.eq_empty_iff_forall_notMem.1 hE
          ((⟨x, by rw [htail]; exact hx⟩ : X.vertexClass (X.tailColor m)),
            (⟨w₀, by rw [hhead]; exact hmx hw₀⟩ : X.vertexClass (X.headColor m))) ?_) not_false
        exact hw₀
      · have hall : X.vertexClass j ⊆ X.nbr m x := by
          intro z hz
          have : ((⟨x, by rw [htail]; exact hx⟩ : X.vertexClass (X.tailColor m)),
              (⟨z, by rw [hhead]; exact hz⟩ : X.vertexClass (X.headColor m)))
              ∈ (X.bipConstituent m).E := by rw [hE]; trivial
          exact this
        exact absurd (Set.ncard_le_ncard hall (Set.toFinite _)) (by omega)
    have hprim' : (X.induced (X.vertexClass (X.tailColor m))).IsPrimitive := by
      rw [htail]; exact hprim
    exact X.nbr_ne_of_primitive h m hnt hprim'
      (by rw [htail]; exact hx) (by rw [htail]; exact hlx hu) hux heq

end Equitability

end PartitionStructure

end Babai
