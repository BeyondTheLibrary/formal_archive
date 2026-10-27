/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.4.1: Connected components of constituents.
-/
import Workspace.Coherent.Classes

/-!
# §3.4.1 Connected components of constituents

## Numbering map

| Paper | Lean |
|---|---|
| Proposition 3.4.1 | `Babai.PartitionStructure.weak_is_strong` |
| Remark 3.4.2 | `.unionConstituent_isEulerian`, `.weak_is_strong_union` |
| Definition 3.4.3 | `Babai.IsEquipartition` |
| Proposition 3.4.4 | `.homogeneous_components_equipartition` |
| Proposition 3.4.5 | `.bipartite_components_equipartition` (class `Ωᵢ`), `.bipartite_components_equipartition_head` (class `Ω_j`), `.bipartite_components_ncard_eq` ("all weak components have the same number of vertices") |
| Lemma 3.4.6 | `.ncard_outNbhd_component_eq` |
| Lemma 3.4.7 | `.ncard_backNbhd_component_eq` |
| Lemma 3.4.8 | `.ncard_components_meeting_eq` |
| Theorem 3.4.9 | `.contraction_isSemiregular` |
-/

namespace Babai

variable {Ω : Type*}

/-- Definition 3.4.3 (Equipartition).  "An *equipartition* of a set `Ω` is a partition
of `Ω` into blocks of equal size." -/
structure IsEquipartition (P : Set (Set Ω)) : Prop where
  nonempty : ∀ A ∈ P, A.Nonempty
  pairwiseDisjoint : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B
  covers : ⋃₀ P = Set.univ
  equal_size : ∀ A ∈ P, ∀ B ∈ P, A.ncard = B.ncard

namespace PartitionStructure

variable (X : PartitionStructure Ω) [Fintype Ω] [DecidableEq Ω]

/-- Proposition 3.4.1 (Weak is strong).  "The weak components of a homogeneous
constituent digraph are its strong components."

Paper's proof: "Homogeneous constituents are eulerian by part (i) of Cor. 3.3.7.
Therefore their weakly connected components are strongly connected by Prop. 2.4.23." -/
theorem extConstituent_isEulerian (h : X.IsCoherent) (k : Fin X.rank)
    (hhom : X.tailColor k = X.headColor k) : (X.extConstituent k).IsEulerian := by
  classical
  have hconvtail : X.tailColor (X.conv k) = X.tailColor k := by
    rw [X.tailColor_conv h k, ← hhom]
  intro u
  by_cases hu : u ∈ X.vertexClass (X.tailColor k)
  · -- inside the color class the extended constituent agrees with the induced digraph,
    -- which is biregular by Cor. 3.3.7 (i), hence eulerian (Def. 2.4.22)
    have hu' : u ∈ X.vertexClass (X.tailColor (X.conv k)) := by rw [hconvtail]; exact hu
    have hbireg : ((X.extConstituent k).induced (X.vertexClass (X.tailColor k))).IsBiregular := by
      rcases X.constituent_homogeneous_or_bipartite h k with ⟨-, -, hb⟩ | ⟨hne, -⟩
      · exact hb
      · exact absurd hhom hne
    have heul := hbireg.isEulerian ⟨u, hu⟩
    rw [X.outDeg_induced_ext k _ ⟨u, hu⟩, X.inDeg_induced_ext h.toIsConfiguration k _ ⟨u, hu⟩,
      X.ncard_nbr_inter_vertexClass h k (X.tailColor k) u,
      X.ncard_nbr_inter_vertexClass h (X.conv k) (X.tailColor k) u,
      if_pos ⟨hu, hhom⟩,
      if_pos ⟨show X.vcolor u = X.tailColor (X.conv k) from hu',
        show X.tailColor k = X.headColor (X.conv k) from (X.headColor_conv h k).symm⟩] at heul
    show X.outDegC k u = X.inDegC k u
    rw [X.outDegC_eq_outDegOf h k hu, heul, inDegC_eq_ncard,
      X.inNbr_eq_nbr_conv h.toIsConfiguration k u, ← outDegC_eq_ncard,
      X.outDegC_eq_outDegOf h (X.conv k) hu']
  · -- outside the color class both degrees vanish
    show X.outDegC k u = X.inDegC k u
    rw [outDegC_eq_ncard, inDegC_eq_ncard, X.nbr_eq_empty_of_vcolor_ne h k hu,
      X.inNbr_eq_nbr_conv h.toIsConfiguration k u,
      X.nbr_eq_empty_of_vcolor_ne h (X.conv k) (by rw [hconvtail]; exact hu)]

theorem weak_is_strong (h : X.IsCoherent) (k : Fin X.rank)
    (hhom : X.tailColor k = X.headColor k) (x : Ω) :
    (X.extConstituent k).weakComponent x = (X.extConstituent k).strongComponent x :=
  Digraph.weakComponent_eq_strongComponent (X.extConstituent_isEulerian h k hhom) x

/-! ### Components as accessibility sets -/

/-- Prop. 3.4.4: the set of strings `k* = {Λ, k, kk, kkk, …}`. -/
def repStrings (k : Fin X.rank) : Set (List (Fin X.rank)) := {I | ∃ t, I = List.replicate t k}

theorem accessSet_repStrings (k : Fin X.rank) (x : Ω) :
    X.accessSet (X.repStrings k) x = {y | (X.extConstituent k).Accessible x y} := by
  ext y
  simp only [accessSet, AccessibleAlong, repStrings, Set.mem_setOf_eq,
    X.accessible_extConstituent_iff k x y]
  constructor
  · rintro ⟨I, ⟨t, rfl⟩, hne⟩
    exact ⟨t, (X.isChainWalk_iff _ x y).2 hne⟩
  · rintro ⟨t, ht⟩
    exact ⟨List.replicate t k, ⟨t, rfl⟩, (X.isChainWalk_iff _ x y).1 ht⟩

/-- Prop. 3.4.4: the weak component of `x` in a homogeneous constituent is the set of
vertices accessible from `x` along `k*` (this uses Prop. 3.4.1). -/
theorem weakComponent_eq_accessSet (h : X.IsCoherent) (k : Fin X.rank)
    (hhom : X.tailColor k = X.headColor k) (x : Ω) :
    (X.extConstituent k).weakComponent x = X.accessSet (X.repStrings k) x := by
  rw [X.accessSet_repStrings k x]
  ext y
  constructor
  · intro hy
    rw [X.weak_is_strong h k hhom x] at hy
    exact hy.1
  · intro hy
    rw [X.weak_is_strong h k hhom x] at *
    refine ⟨hy, ?_⟩
    -- `y` is accessible from `x`, hence weakly accessible, hence in the weak component,
    -- which by Prop. 3.4.1 is the strong component
    have : y ∈ (X.extConstituent k).weakComponent x := by
      rw [Digraph.weakComponent_eq_weaklyAccessible]
      exact Digraph.weaklyAccessible_of_accessible _ hy
    rw [X.weak_is_strong h k hhom x] at this
    exact this.2

/-- Counting the vertices whose color lies in a finite set of colors, color by color. -/
theorem ncard_mem_finset_eq_sum (f : Ω → Fin X.rank) (K : Finset (Fin X.rank)) :
    {v | f v ∈ K}.ncard = ∑ k ∈ K, {v | f v = k}.ncard := by
  classical
  have e1 : {v | f v ∈ K} = ↑(Finset.univ.filter fun v => f v ∈ K) := by ext; simp
  rw [e1, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun v => f v ∈ K) (f := f)
      (t := K) (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have e2 : {v | f v = k} = ↑(Finset.univ.filter fun v => f v = k) := by ext; simp
  rw [e2, Set.ncard_coe_finset, Finset.filter_filter]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ hk, h⟩

/-- Remark 3.4.2.  *"The proof shows that the same holds if we consider a weak component of
a union of homogeneous constituents."*  The paper's proof of Prop. 3.4.1 carried over: the
union `(Ω, ⋃_{k ∈ K} R_k)` of homogeneous constituents is eulerian, because the relations
`R_k` are disjoint, so each degree is the sum of the degrees in the constituents, and each
constituent is eulerian (`extConstituent_isEulerian`). -/
theorem unionConstituent_isEulerian (h : X.IsCoherent) (K : Finset (Fin X.rank))
    (hK : ∀ k ∈ K, X.tailColor k = X.headColor k) :
    (⟨{p | X.color p.1 p.2 ∈ K}⟩ : Digraph Ω).IsEulerian := by
  intro u
  show (outNbr {p : Ω × Ω | X.color p.1 p.2 ∈ K} u).ncard
    = (inNbr {p : Ω × Ω | X.color p.1 p.2 ∈ K} u).ncard
  have hout : outNbr {p : Ω × Ω | X.color p.1 p.2 ∈ K} u = {v | X.color u v ∈ K} := by
    ext v; simp
  have hin : inNbr {p : Ω × Ω | X.color p.1 p.2 ∈ K} u = {v | X.color v u ∈ K} := by
    ext v; simp
  rw [hout, hin, X.ncard_mem_finset_eq_sum (fun v => X.color u v),
    X.ncard_mem_finset_eq_sum (fun v => X.color v u)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := X.extConstituent_isEulerian h k (hK k hk) u
  have ho : (X.extConstituent k).outDeg u = {v | X.color u v = k}.ncard := by
    rfl
  have hi : (X.extConstituent k).inDeg u = {v | X.color v u = k}.ncard := by
    show (inNbr (X.rel k) u).ncard = _
    congr 1
  rw [← ho, ← hi]
  exact this

/-- Remark 3.4.2.  The weak components of a union of homogeneous constituents are its
strong components (Prop. 2.4.23 applied to `unionConstituent_isEulerian`). -/
theorem weak_is_strong_union (h : X.IsCoherent) (K : Finset (Fin X.rank))
    (hK : ∀ k ∈ K, X.tailColor k = X.headColor k) (x : Ω) :
    (⟨{p | X.color p.1 p.2 ∈ K}⟩ : Digraph Ω).weakComponent x
      = (⟨{p | X.color p.1 p.2 ∈ K}⟩ : Digraph Ω).strongComponent x :=
  Digraph.weakComponent_eq_strongComponent (X.unionConstituent_isEulerian h K hK) x

/-- Proposition 3.4.4 (Homogeneous connected components).  "If `X_k` is a homogeneous
constituent digraph in color class `Ωᵢ` then the components of `X_k` equipartition `Ωᵢ`."

Paper's proof: "Let `x ∈ Ωᵢ` and let `Y(x)` denote the set of vertices of the component
of the constituent `X_k` that contains `x`.  Then `Y(x) ⊆ Ωᵢ` and `Y(x)` consists of
those vertices that are accessible from `x` along a sequence of edges of color `k`.
Using the notation of Cor. 3.3.12, this means that `Y(x) = (k*)(x)` where
`k* = {Λ, k, kk, kkk, …}`.  It follows by the Accessibility Theorem (Thm. 3.3.14) that
`|Y(x)| = |(k*)(x)|` only depends on `k` and `c(x)`." -/
theorem homogeneous_components_equipartition (h : X.IsCoherent) (k : Fin X.rank)
    (hhom : X.tailColor k = X.headColor k) {x y : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k)) (hy : y ∈ X.vertexClass (X.tailColor k)) :
    ((X.extConstituent k).weakComponent x).ncard
      = ((X.extConstituent k).weakComponent y).ncard := by
  rw [X.weakComponent_eq_accessSet h k hhom x, X.weakComponent_eq_accessSet h k hhom y]
  exact X.ncard_accessSet_eq h _ (hx.trans hy.symm)

/-! ### Prop. 3.4.4 for a homogeneous configuration

In a homogeneous configuration (Def. 3.1.6) every constituent is homogeneous, so Prop.
3.4.4 applies to each of them and its weak components equipartition the whole vertex set.
This is the form in which the Design Lemma (§8.1) uses Prop. 3.4.4: the equipartition it
produces is nontrivial, which needs the two extra observations that a *disconnected*
constituent has at least two components (Def. 2.4.21) and that an *off-diagonal* color has
an edge between two distinct vertices, which then lie in a common component. -/

/-- In a homogeneous configuration the tail and the head of an edge have the same color,
so every constituent is homogeneous in the sense of Prop. 3.4.4. -/
theorem tailColor_eq_headColor_of_isHomogeneous (hhom : X.IsHomogeneous)
    (k : Fin X.rank) : X.tailColor k = X.headColor k := hhom _ _

/-- In a homogeneous configuration every vertex has the tail color of every color. -/
theorem mem_vertexClass_tailColor_of_isHomogeneous (hhom : X.IsHomogeneous)
    (k : Fin X.rank) (x : Ω) : x ∈ X.vertexClass (X.tailColor k) := hhom _ _

/-- Proposition 3.4.4 for a homogeneous coherent configuration: the weak components of
any constituent equipartition `Ω`. -/
theorem homogeneous_weakComponents_isEquipartition (h : X.IsCoherent)
    (hhom : X.IsHomogeneous) (k : Fin X.rank) :
    IsEquipartition (X.extConstituent k).weakComponents where
  nonempty _ hA := (X.extConstituent k).weakComponents_nonempty hA
  pairwiseDisjoint _ hA _ hB hAB :=
    (X.extConstituent k).weakComponents_pairwiseDisjoint hA hB hAB
  covers := (X.extConstituent k).sUnion_weakComponents
  equal_size := by
    rintro A ⟨u, rfl⟩ B ⟨v, rfl⟩
    exact X.homogeneous_components_equipartition h k
      (X.tailColor_eq_headColor_of_isHomogeneous hhom k)
      (X.mem_vertexClass_tailColor_of_isHomogeneous hhom k u)
      (X.mem_vertexClass_tailColor_of_isHomogeneous hhom k v)

/-- An off-diagonal constituent has an edge between two distinct vertices, so one of its
weak components has at least two elements; by Prop. 3.4.4 all of them then do. -/
theorem homogeneous_weakComponents_nontrivial (h : X.IsCoherent)
    (hhom : X.IsHomogeneous) (k : Fin X.rank) (hoff : X.IsOffDiagonalColor k)
    {A : Set Ω} (hA : A ∈ (X.extConstituent k).weakComponents) : A.Nontrivial := by
  classical
  obtain ⟨⟨u, v⟩, huv⟩ := X.rel_nonempty k
  have huv' : u ≠ v := by
    intro hc
    have : ((u, v) : Ω × Ω) ∈ X.rel k ∩ diag Ω := ⟨huv, hc⟩
    rw [hoff] at this
    exact this
  have hmem : v ∈ (X.extConstituent k).weakComponent u :=
    (X.extConstituent k).mem_weakComponent_of_adj huv
  have hbig : 1 < ((X.extConstituent k).weakComponent u).ncard := by
    rw [Set.one_lt_ncard_iff_nontrivial]
    exact ⟨u, (X.extConstituent k).mem_weakComponent_self u, v, hmem, huv'⟩
  rw [← Set.one_lt_ncard_iff_nontrivial]
  rw [(X.homogeneous_weakComponents_isEquipartition h hhom k).equal_size A hA
    ((X.extConstituent k).weakComponent u) ⟨u, rfl⟩]
  exact hbig

/-- Prop. 3.4.4 in the form used by the Design Lemma (Thm. 8.1.2): in a homogeneous
coherent configuration, the weak components of a *disconnected off-diagonal* constituent
form an equipartition of `Ω` with at least two blocks, each of size at least `2`. -/
theorem homogeneous_disconnected_weakComponents (h : X.IsCoherent)
    (hhom : X.IsHomogeneous) (k : Fin X.rank) (hoff : X.IsOffDiagonalColor k)
    (hdisc : ¬ (X.extConstituent k).IsWeaklyConnected) :
    IsEquipartition (X.extConstituent k).weakComponents ∧
      (∃ A ∈ (X.extConstituent k).weakComponents,
        ∃ B ∈ (X.extConstituent k).weakComponents, A ≠ B) ∧
      ∀ A ∈ (X.extConstituent k).weakComponents, A.Nontrivial :=
  ⟨X.homogeneous_weakComponents_isEquipartition h hhom k,
    (X.extConstituent k).exists_ne_weakComponents hdisc,
    fun _ hA => X.homogeneous_weakComponents_nontrivial h hhom k hoff hA⟩

/-- Prop. 3.4.5: the string `(kk⁻)^t`. -/
noncomputable def dblString (k : Fin X.rank) (t : ℕ) : List (Fin X.rank) :=
  (List.replicate t [k, X.conv k]).flatten

@[simp] theorem dblString_zero (k : Fin X.rank) : X.dblString k 0 = [] := rfl

theorem dblString_succ (k : Fin X.rank) (t : ℕ) :
    X.dblString k (t + 1) = X.dblString k t ++ [k, X.conv k] := by
  rw [dblString, List.replicate_succ', List.flatten_append]
  simp [dblString]

/-- Prop. 3.4.5: the set of strings `(kk⁻)* = {Λ, kk⁻, kk⁻kk⁻, …}`. -/
noncomputable def dblStrings (k : Fin X.rank) : Set (List (Fin X.rank)) :=
  {I | ∃ t, I = X.dblString k t}

/-- Prop. 3.4.5.  "`Y(x) ∩ Ωᵢ` consists of those vertices accessible from `x` along a
string of colors in the set `(kk⁻)*`."

The inclusion `⊇` is an induction on the number of `kk⁻` blocks; the inclusion `⊆` is an
induction along the weak walk, which alternates between `Ωᵢ` and `Ω_j` because every edge
of color `k` has its tail in `Ωᵢ` and its head in `Ω_j`. -/
theorem weakComponent_inter_eq_accessSet (h : X.IsCoherent) (k : Fin X.rank)
    (hbip : X.tailColor k ≠ X.headColor k) {x : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k)) :
    (X.extConstituent k).weakComponent x ∩ X.vertexClass (X.tailColor k)
      = X.accessSet (X.dblStrings k) x := by
  classical
  -- `⊇`: a chain walk along `(kk⁻)^t` stays in `Ωᵢ` and is a weak walk
  have hback : ∀ (t : ℕ) (y : Ω), X.IsChainWalk (X.dblString k t) x y →
      y ∈ (X.extConstituent k).weakComponent x ∩ X.vertexClass (X.tailColor k) := by
    intro t
    induction t with
    | zero =>
      intro y hy
      rw [dblString_zero, isChainWalk_nil] at hy
      subst hy
      exact ⟨Digraph.mem_weakComponent_self _ x, hx⟩
    | succ n ih =>
      intro y hy
      rw [X.dblString_succ k n, X.isChainWalk_append] at hy
      obtain ⟨z, hz, hstep⟩ := hy
      obtain ⟨u, hzu, w, huw, hwy⟩ := hstep
      rw [← hwy]
      obtain ⟨hzw, -⟩ := ih z hz
      have hyu : X.color w u = k := (X.color_conv_iff h.toIsConfiguration k w u).1 huw
      refine ⟨?_, X.vcolor_fst_eq h hyu⟩
      -- `x ⟶ z ⟶ u ⟵ y` is a weak walk
      rw [Digraph.weakComponent_eq_weaklyAccessible] at hzw ⊢
      refine Digraph.accessible_trans _ hzw ?_
      refine Digraph.accessible_trans _
        (Digraph.accessible_of_adj _ (show (X.extConstituent k).symmetrization.Adj z u from
          Or.inl hzu)) ?_
      exact Digraph.accessible_of_adj _
        (show (X.extConstituent k).symmetrization.Adj u w from Or.inr hyu)
  -- `⊆`: induction along the weak walk
  have hfwd : ∀ b : Ω, Relation.ReflTransGen (X.extConstituent k).symmetrization.Adj x b →
      (b ∈ X.vertexClass (X.tailColor k) → ∃ t, X.IsChainWalk (X.dblString k t) x b) ∧
      (b ∈ X.vertexClass (X.headColor k) →
        ∃ t, X.IsChainWalk (X.dblString k t ++ [k]) x b) := by
    intro b hb
    induction hb with
    | refl =>
      refine ⟨fun _ => ⟨0, rfl⟩, fun hxj => absurd ?_ hbip⟩
      exact (show X.vcolor x = X.tailColor k from hx).symm.trans hxj
    | @tail b c _ hbc ih =>
      rcases hbc with hbc | hbc
      · -- `c(b,c) = k`: `b ∈ Ωᵢ`, `c ∈ Ω_j`
        have hbi : b ∈ X.vertexClass (X.tailColor k) := X.vcolor_fst_eq h hbc
        have hcj : c ∈ X.vertexClass (X.headColor k) := X.vcolor_snd_eq h hbc
        refine ⟨fun hci => absurd ((show X.vcolor c = X.tailColor k from hci).symm.trans hcj)
          hbip, fun _ => ?_⟩
        obtain ⟨t, ht⟩ := ih.1 hbi
        exact ⟨t, (X.isChainWalk_append _ _ x c).2 ⟨b, ht, ⟨c, hbc, rfl⟩⟩⟩
      · -- `c(c,b) = k`: `c ∈ Ωᵢ`, `b ∈ Ω_j`
        have hci : c ∈ X.vertexClass (X.tailColor k) := X.vcolor_fst_eq h hbc
        have hbj : b ∈ X.vertexClass (X.headColor k) := X.vcolor_snd_eq h hbc
        refine ⟨fun _ => ?_, fun hch => absurd ((show X.vcolor c = X.tailColor k from hci).symm.trans
          hch) hbip⟩
        obtain ⟨t, ht⟩ := ih.2 hbj
        refine ⟨t + 1, ?_⟩
        rw [X.dblString_succ k t, show X.dblString k t ++ [k, X.conv k]
          = (X.dblString k t ++ [k]) ++ [X.conv k] by simp, X.isChainWalk_append]
        exact ⟨b, ht, ⟨c, (X.color_conv_iff h.toIsConfiguration k c b).2 hbc, rfl⟩⟩
  ext y
  constructor
  · rintro ⟨hw, hy⟩
    rw [Digraph.weakComponent_eq_weaklyAccessible] at hw
    obtain ⟨t, ht⟩ := (hfwd y ((Digraph.accessible_iff_reflTransGen' _ x y).1 hw)).1 hy
    exact ⟨X.dblString k t, ⟨t, rfl⟩, (X.isChainWalk_iff _ x y).1 ht⟩
  · rintro ⟨I, ⟨t, rfl⟩, hne⟩
    exact hback t y ((X.isChainWalk_iff _ x y).2 hne)

/-- Proposition 3.4.5 (Bipartite connected components).  "If `X_k = (Ω(k), R_k)` is a
bipartite constituent digraph with `R_k ⊆ Ωᵢ × Ω_j` then the weak components of `X_k`
equipartition each of the two color classes, `Ωᵢ` and `Ω_j`.  In particular, all weak
components of `X_k` have the same number of vertices."

Paper's proof: "`Y(x) ∩ Ωᵢ` consists of those vertices accessible from `x` along a string
of colors in the set `(kk⁻)* = {Λ, kk⁻, kk⁻kk⁻, …}` … It follows by the Accessibility
Theorem (Thm. 3.3.14) that `|Y(x) ∩ Ωᵢ| = |((kk⁻)*)(x)|` only depends on `k` and `c(x)`.
The case `x ∈ Ω_j` follows by applying the foregoing to `k⁻` in the place of `k`." -/
theorem bipartite_components_equipartition (h : X.IsCoherent) (k : Fin X.rank)
    (hbip : X.tailColor k ≠ X.headColor k) {x y : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k)) (hy : y ∈ X.vertexClass (X.tailColor k)) :
    ((X.extConstituent k).weakComponent x ∩ X.vertexClass (X.tailColor k)).ncard
      = ((X.extConstituent k).weakComponent y ∩ X.vertexClass (X.tailColor k)).ncard := by
  rw [X.weakComponent_inter_eq_accessSet h k hbip hx,
    X.weakComponent_inter_eq_accessSet h k hbip hy]
  exact X.ncard_accessSet_eq h _ (hx.trans hy.symm)

/-- The constituents `X_k` and `X_{k⁻}` have the same weak components: `R_{k⁻} = R_k⁻`, so
the two digraphs have the same symmetrization. -/
theorem weakComponent_conv (h : X.IsConfiguration) (k : Fin X.rank) (x : Ω) :
    (X.extConstituent (X.conv k)).weakComponent x = (X.extConstituent k).weakComponent x := by
  have hsym : (X.extConstituent (X.conv k)).symmetrization
      = (X.extConstituent k).symmetrization := by
    show (⟨X.rel (X.conv k) ∪ invRel (X.rel (X.conv k))⟩ : Digraph Ω)
      = ⟨X.rel k ∪ invRel (X.rel k)⟩
    rw [X.rel_conv h, invRel_invRel, Set.union_comm]
  simp only [Digraph.weakComponent, hsym]

/-- Proposition 3.4.5, the second color class.  *"The case `x ∈ Ω_j` follows by applying the
foregoing to `k⁻` in the place of `k` (swapping the roles of `i` and `j`)."* -/
theorem bipartite_components_equipartition_head (h : X.IsCoherent) (k : Fin X.rank)
    (hbip : X.tailColor k ≠ X.headColor k) {x y : Ω}
    (hx : x ∈ X.vertexClass (X.headColor k)) (hy : y ∈ X.vertexClass (X.headColor k)) :
    ((X.extConstituent k).weakComponent x ∩ X.vertexClass (X.headColor k)).ncard
      = ((X.extConstituent k).weakComponent y ∩ X.vertexClass (X.headColor k)).ncard := by
  have hbip' : X.tailColor (X.conv k) ≠ X.headColor (X.conv k) := by
    rw [X.tailColor_conv h, X.headColor_conv h]
    exact hbip.symm
  have := X.bipartite_components_equipartition h (X.conv k) hbip'
    (x := x) (y := y) (by rw [X.tailColor_conv h]; exact hx) (by rw [X.tailColor_conv h]; exact hy)
  rwa [X.tailColor_conv h, X.weakComponent_conv h.toIsConfiguration,
    X.weakComponent_conv h.toIsConfiguration] at this

/-- Proposition 3.4.5.  The weak component of a vertex of `Ω(k) = Ωᵢ ∪ Ω_j` stays in
`Ω(k)`: every edge of the symmetrization of `X_k` ends in `Ωᵢ ∪ Ω_j`. -/
theorem weakComponent_subset_union (h : X.IsCoherent) (k : Fin X.rank) {x : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k)) :
    (X.extConstituent k).weakComponent x
      ⊆ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k) := by
  intro y hy
  rw [Digraph.weakComponent_eq_weaklyAccessible] at hy
  replace hy := (Digraph.accessible_iff_reflTransGen' _ x y).1 hy
  rcases Relation.ReflTransGen.cases_tail hy with rfl | ⟨b, -, hb⟩
  · exact hx
  · rcases hb with hb | hb
    · exact Or.inr (X.vcolor_snd_eq h hb)
    · exact Or.inl (X.vcolor_fst_eq h hb)

/-- Proposition 3.4.5.  Every weak component of `X_k` through a vertex of `Ω(k)` contains
an edge of color `k`, hence meets both `Ωᵢ` and `Ω_j`. -/
theorem exists_edge_weakComponent (h : X.IsCoherent) (k : Fin X.rank) {x : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k)) :
    ∃ a b : Ω, X.color a b = k ∧
      (X.extConstituent k).weakComponent x = (X.extConstituent k).weakComponent a := by
  have hnbr : ∀ {j : Fin X.rank} {u : Ω}, u ∈ X.vertexClass (X.tailColor j) →
      ∃ v, X.color u v = j := by
    intro j u hu
    have hpos : 0 < (X.nbr j u).ncard := by
      rw [← outDegC_eq_ncard, X.outDegC_eq_outDegOf h j hu]
      exact X.outDegOf_pos h j
    exact (Set.ncard_pos (Set.toFinite _)).1 hpos
  rcases hx with hx | hx
  · obtain ⟨b, hb⟩ := hnbr hx
    exact ⟨x, b, hb, rfl⟩
  · obtain ⟨a, ha⟩ := hnbr (j := X.conv k) (by rw [X.tailColor_conv h]; exact hx)
    have hax : X.color a x = k := (X.color_conv_iff h.toIsConfiguration k a x).1 ha
    obtain ⟨b, hb⟩ := hnbr (X.vcolor_fst_eq h hax)
    exact ⟨a, b, hb, ((X.extConstituent k).weakComponent_eq_of_mem
      ((X.extConstituent k).mem_weakComponent_of_adj hax))⟩

/-- Proposition 3.4.5.  *"In particular, all weak components of `X_k` have the same number
of vertices."*  (The vertex set of `X_k` is `Ω(k) = Ωᵢ ∪ Ω_j`.)  A weak component through
`x ∈ Ω(k)` lies in `Ωᵢ ∪ Ω_j` and meets both classes, so its size is the sum of the two
sizes that the two halves of Prop. 3.4.5 show to be independent of the component. -/
theorem bipartite_components_ncard_eq (h : X.IsCoherent) (k : Fin X.rank)
    (hbip : X.tailColor k ≠ X.headColor k) {x y : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k))
    (hy : y ∈ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k)) :
    ((X.extConstituent k).weakComponent x).ncard
      = ((X.extConstituent k).weakComponent y).ncard := by
  have hdisj : Disjoint (X.vertexClass (X.tailColor k)) (X.vertexClass (X.headColor k)) :=
    Set.disjoint_left.2 fun u hi hj => hbip (hi.symm.trans hj)
  -- the size of a component through `x ∈ Ω(k)` is the sum of its two halves
  have hsplit : ∀ {u : Ω}, u ∈ X.vertexClass (X.tailColor k) ∪ X.vertexClass (X.headColor k) →
      ((X.extConstituent k).weakComponent u).ncard
        = ((X.extConstituent k).weakComponent u ∩ X.vertexClass (X.tailColor k)).ncard
          + ((X.extConstituent k).weakComponent u ∩ X.vertexClass (X.headColor k)).ncard := by
    intro u hu
    rw [← Set.ncard_union_eq (hdisj.mono Set.inter_subset_right Set.inter_subset_right)
      (Set.toFinite _) (Set.toFinite _), ← Set.inter_union_distrib_left,
      Set.inter_eq_self_of_subset_left (X.weakComponent_subset_union h k hu)]
  obtain ⟨a, b, hab, hxa⟩ := X.exists_edge_weakComponent h k hx
  obtain ⟨a', b', hab', hya⟩ := X.exists_edge_weakComponent h k hy
  have ha : a ∈ X.vertexClass (X.tailColor k) := X.vcolor_fst_eq h hab
  have hb : b ∈ X.vertexClass (X.headColor k) := X.vcolor_snd_eq h hab
  have ha' : a' ∈ X.vertexClass (X.tailColor k) := X.vcolor_fst_eq h hab'
  have hb' : b' ∈ X.vertexClass (X.headColor k) := X.vcolor_snd_eq h hab'
  have hba : (X.extConstituent k).weakComponent b = (X.extConstituent k).weakComponent a :=
    (X.extConstituent k).weakComponent_eq_of_mem ((X.extConstituent k).mem_weakComponent_of_adj hab)
  have hba' : (X.extConstituent k).weakComponent b' = (X.extConstituent k).weakComponent a' :=
    (X.extConstituent k).weakComponent_eq_of_mem
      ((X.extConstituent k).mem_weakComponent_of_adj hab')
  have hhead := X.bipartite_components_equipartition_head h k hbip hb hb'
  rw [hba, hba'] at hhead
  rw [hsplit hx, hsplit hy, hxa, hya, X.bipartite_components_equipartition h k hbip ha ha', hhead]

/-! ### Lemmas 3.4.6–3.4.8 and the Contraction Theorem 3.4.9

Notation of Lemma 3.4.6: `Ω₁` and `Ω₂` are two distinct vertex-color classes, `X₃` is a
homogeneous constituent digraph inside `Ω₁`, and `X₄` a bipartite constituent between
`Ω₁` and `Ω₂` (so `R₄ ⊆ Ω₁ × Ω₂`).  `B₁, …, B_m` are the connected components of `X₃`. -/

section Contraction

variable (c₃ c₄ : Fin X.rank)

/-- The component of `X₃` containing `x`. -/
def compOf (x : Ω) : Set Ω := (X.extConstituent c₃).weakComponent x

/-- Lemma 3.4.6.  `M_j`, the set of `R₄`-out-neighbours of the component of `x`:
"the set of vertices `v ∈ Ω₂` such that there exists `w ∈ B_j` such that
`c(w,v) = 4`." -/
def outNbhdComp (x : Ω) : Set Ω :=
  {v : Ω | ∃ w ∈ X.compOf c₃ x, X.color w v = c₄}

/-- Lemma 3.4.6: the set of strings `3*4`. -/
def repThenStrings : Set (List (Fin X.rank)) :=
  {I | ∃ t, I = List.replicate t c₃ ++ [c₄]}

/-- Lemma 3.4.6.  "`y ∈ M_j ⟺ y` is accessible from `x` along `3*4`", i.e.
`M_j = (3*4)(x)`. -/
theorem outNbhdComp_eq_accessSet (h : X.IsCoherent)
    (h3 : X.tailColor c₃ = X.headColor c₃) (x : Ω) :
    X.outNbhdComp c₃ c₄ x = X.accessSet (X.repThenStrings c₃ c₄) x := by
  classical
  have hcomp : ∀ w : Ω, w ∈ X.compOf c₃ x ↔ ∃ t, X.IsChainWalk (List.replicate t c₃) x w := by
    intro w
    rw [compOf, X.weakComponent_eq_accessSet h c₃ h3 x, X.accessSet_repStrings]
    exact (X.accessible_extConstituent_iff c₃ x w)
  ext v
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨t, ht⟩ := (hcomp w).1 hw
    refine ⟨List.replicate t c₃ ++ [c₄], ⟨t, rfl⟩, (X.isChainWalk_iff _ x v).1 ?_⟩
    exact (X.isChainWalk_append _ _ x v).2 ⟨w, ht, ⟨v, hwv, rfl⟩⟩
  · rintro ⟨I, ⟨t, rfl⟩, hne⟩
    obtain ⟨w, hxw, hwv⟩ := (X.isChainWalk_append _ _ x v).1 ((X.isChainWalk_iff _ x v).2 hne)
    obtain ⟨v', hv', hv'v⟩ := hwv
    rw [hv'v] at hv'
    exact ⟨w, (hcomp w).2 ⟨t, hxw⟩, hv'⟩

/-- Lemma 3.4.6 (Neighborhood of connected component of constituent).  "Then
`|M₁| = ⋯ = |M_m|`."

Paper's proof: "Let `x ∈ B_j`.  Then `y ∈ M_j ⟺ y` is accessible from `x` along `3*4`.
Using the notation of Cor. 3.3.12, this means that `M_j = (3*4)(x)`.  It follows by the
Accessibility Theorem (Thm. 3.3.14) that `|M_j| = |(3*4)(x)|` only depends on the colors
`3, 4`, and `c(x) = 1`, which are given; so it is the same number for all `x ∈ Ω₁`, it
does not depend on `j`." -/
theorem ncard_outNbhd_component_eq (h : X.IsCoherent)
    (h3 : X.tailColor c₃ = X.headColor c₃) (h4 : X.tailColor c₄ = X.tailColor c₃)
    (h34 : X.headColor c₄ ≠ X.tailColor c₃) {x y : Ω}
    (hx : x ∈ X.vertexClass (X.tailColor c₃))
    (hy : y ∈ X.vertexClass (X.tailColor c₃)) :
    (X.outNbhdComp c₃ c₄ x).ncard = (X.outNbhdComp c₃ c₄ y).ncard := by
  rw [X.outNbhdComp_eq_accessSet c₃ c₄ h h3 x, X.outNbhdComp_eq_accessSet c₃ c₄ h h3 y]
  exact X.ncard_accessSet_eq h _ (hx.trans hy.symm)

/-- Lemma 3.4.7.  `M(x,y) = {z ∈ B_i | c(z,y) = 4}` for an edge `(x,y)` of color `4` with
`x ∈ B_i`. -/
def backNbhdComp (x y : Ω) : Set Ω := {z : Ω | z ∈ X.compOf c₃ x ∧ X.color z y = c₄}

/-- Lemma 3.4.7.  "Using the notation of Lemma 3.4.6, let `x ∈ Ω₁` and `y ∈ Ω₂` be joined
by an edge of color `c(x,y) = 4`.  Assume `x ∈ B_i`.  Let `M(x,y) = {z ∈ B_i |
c(z,y) = 4}`.  Then `|M(x,y)|` does not depend on the choice of `x` and `y` (and in
particular on `i`)."

Paper's proof: "Let `J` be the set of those colors `j` for which the head of an edge of
color `j` is accessible from its tail along edges of color `3`.  Now
`z ∈ M(x,y) ⟺ c(x,z) ∈ J and c(z,y) = 4`.  Therefore `|M(x,y)| = ∑_{j∈J} p_4^{j,3}`."

The displayed formula is a typo: with `J` and the characterization as stated, the count
is `∑_{j∈J} p^4_{j,4}` (the summand must have `4` as its second lower index, since the
condition on `z` is `c(z,y) = 4`, and `4 = c(x,y)` as the upper index).  This affects the
proof only, not the statement; see the corrected paper. -/
theorem ncard_backNbhd_component_eq (h : X.IsCoherent)
    (h3 : X.tailColor c₃ = X.headColor c₃) (h4 : X.tailColor c₄ = X.tailColor c₃)
    (h34 : X.headColor c₄ ≠ X.tailColor c₃) {x y x' y' : Ω}
    (hxy : X.color x y = c₄) (hx'y' : X.color x' y' = c₄) :
    (X.backNbhdComp c₃ c₄ x y).ncard = (X.backNbhdComp c₃ c₄ x' y').ncard := by
  classical
  obtain ⟨J, hJ⟩ := X.exists_accessibilitySet h (X.repStrings c₃)
  have key : ∀ a b : Ω, X.color a b = c₄ → (X.backNbhdComp c₃ c₄ a b).ncard
      = ∑ j ∈ Finset.univ.filter (fun j => j ∈ J), X.interNum j c₄ c₄ := by
    intro a b hab
    have hmem : ∀ z : Ω, z ∈ X.compOf c₃ a ↔ X.color a z ∈ J := by
      intro z
      rw [compOf, X.weakComponent_eq_accessSet h c₃ h3 a]
      exact hJ a z
    rw [backNbhdComp, Set.ncard_eq_toFinset_card',
      Finset.card_eq_sum_card_fiberwise (f := fun z => X.color a z)
        (t := Finset.univ.filter (fun j => j ∈ J)) (fun z hz => by
          simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq] at hz
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
          exact (hmem z).1 hz.1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjJ : j ∈ J := by simpa using (Finset.mem_filter.1 hj).2
    rw [← X.interNum_eq h j c₄ c₄ hab, Set.ncard_eq_toFinset_card']
    congr 1
    ext z
    simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(hmem z).2 (by rw [h1]; exact hjJ), h2⟩, h1⟩
  rw [key x y hxy, key x' y' hx'y']

/-- Lemma 3.4.8.  `E(y)`, "the set of those `i` for which there exists `x ∈ B_i`
satisfying `c(x,y) = 4`", recorded as the set of the components themselves. -/
def componentsMeeting (y : Ω) : Set (Set Ω) :=
  {B : Set Ω | (∃ x ∈ X.vertexClass (X.tailColor c₃), B = X.compOf c₃ x) ∧
    ∃ x ∈ B, X.color x y = c₄}

/-- Lemma 3.4.8.  "Using the notation of Lemma 3.4.6, for `y ∈ Ω₂` let `E(y)` denote the
set of those `i` for which there exists `x ∈ B_i` satisfying `c(x,y) = 4`.  Then `|E(y)|`
does not depend on `y`."

Paper's proof: "Let `q = |M(x,y)| > 0` be the quantity shown not to depend on `x, y` in
Lemma 3.4.7 (as long as `c(x,y) = 4`).  Recall that `c(y) = 2`.  Now
`p²_{4⁻,4} = deg⁻₄(y) = q|E(y)|`." -/
theorem ncard_components_meeting_eq (h : X.IsCoherent)
    (h3 : X.tailColor c₃ = X.headColor c₃) (h4 : X.tailColor c₄ = X.tailColor c₃)
    (h34 : X.headColor c₄ ≠ X.tailColor c₃) {y y' : Ω}
    (hy : y ∈ X.vertexClass (X.headColor c₄)) (hy' : y' ∈ X.vertexClass (X.headColor c₄)) :
    (X.componentsMeeting c₃ c₄ y).ncard = (X.componentsMeeting c₃ c₄ y').ncard := by
  classical
  -- `q = |M(x,y)| > 0`, the quantity of Lemma 3.4.7
  set a₀ := (X.colorWitness c₄).1 with ha₀
  set b₀ := (X.colorWitness c₄).2 with hb₀
  have hab₀ : X.color a₀ b₀ = c₄ := X.color_colorWitness c₄
  set q := (X.backNbhdComp c₃ c₄ a₀ b₀).ncard with hq
  have hqpos : 0 < q := by
    rw [hq]
    exact (Set.ncard_pos (Set.toFinite _)).2
      ⟨a₀, Digraph.mem_weakComponent_self _ a₀, hab₀⟩
  -- `deg⁻₄(b) = q·|E(b)|`
  have key : ∀ b : Ω, X.inDegC c₄ b = (X.componentsMeeting c₃ c₄ b).ncard * q := by
    intro b
    set T := (Finset.univ.filter (fun z => X.color z b = c₄)).image (fun z => X.compOf c₃ z)
      with hT
    have hCM : X.componentsMeeting c₃ c₄ b = (↑T : Set (Set Ω)) := by
      ext B
      simp only [hT, Finset.coe_image, Set.mem_image, Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨x₁, -, hBx⟩, ⟨z, hz, hzb⟩⟩
        refine ⟨z, hzb, ?_⟩
        rw [hBx] at hz ⊢
        exact Digraph.weakComponent_eq_of_mem _ hz
      · rintro ⟨z, hzb, rfl⟩
        refine ⟨⟨z, ?_, rfl⟩, ⟨z, Digraph.mem_weakComponent_self _ z, hzb⟩⟩
        show X.vcolor z = X.tailColor c₃
        rw [← h4]
        exact X.vcolor_fst_eq h hzb
    have hfiber : ∀ B ∈ T,
        ({x : Ω | X.color x b = c₄}.toFinset.filter fun z => X.compOf c₃ z = B).card = q := by
      intro B hB
      obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.1 hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz₀
      have hset : ({x : Ω | X.color x b = c₄}.toFinset.filter
          fun z => X.compOf c₃ z = X.compOf c₃ z₀)
          = (X.backNbhdComp c₃ c₄ z₀ b).toFinset := by
        ext z
        simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq, backNbhdComp,
          compOf]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by rw [← h2]; exact Digraph.mem_weakComponent_self _ z, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, Digraph.weakComponent_eq_of_mem _ h1⟩
      rw [hset, ← Set.ncard_eq_toFinset_card', hq]
      exact X.ncard_backNbhd_component_eq c₃ c₄ h h3 h4 h34 hz₀ hab₀
    have hmaps : ∀ z ∈ ({x : Ω | X.color x b = c₄}.toFinset : Set Ω),
        X.compOf c₃ z ∈ T := by
      intro z hz
      simp only [Finset.mem_coe, Set.mem_toFinset, Set.mem_setOf_eq] at hz
      exact Finset.mem_image.2 ⟨z, by simp [hz], rfl⟩
    rw [inDegC_eq_ncard, Set.ncard_eq_toFinset_card',
      Finset.card_eq_sum_card_fiberwise (f := fun z => X.compOf c₃ z) (t := T) hmaps,
      Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hCM,
      Set.ncard_coe_finset]
  have hdeg : X.inDegC c₄ y = X.inDegC c₄ y' :=
    X.inDegC_eq_of_vcolor_eq h c₄ (hy.trans hy'.symm)
  rw [key y, key y'] at hdeg
  exact Nat.eq_of_mul_eq_mul_right hqpos hdeg

/-- Theorem 3.4.9 (Contraction).  "Using the notation of Lemma 3.4.6, let `Y` be the
bipartite graph `Y = ([m], Ω₂; E)` where `(i,y) ∈ E` if `(∃x ∈ B_i)(c(x,y) = 4)`.  Then
`Y` is semiregular."

The index set `[m]` of the components is rendered as the type of the components of `X₃`
inside `Ω₁`. -/
def contraction :
    BipGraph {B : Set Ω // ∃ x ∈ X.vertexClass (X.tailColor c₃), B = X.compOf c₃ x}
      (X.vertexClass (X.headColor c₄)) :=
  ⟨{p | ∃ x ∈ (p.1 : Set Ω), X.color x (p.2 : Ω) = c₄}⟩

/-- Theorem 3.4.9 (Contraction).  "Then `Y` is semiregular."

Paper's proof: "Regularity on the `[m]` side is the content of Lemma 3.4.6.  Regularity
on the `Ω₂` side is the content of Lemma 3.4.8." -/
theorem contraction_isSemiregular (h : X.IsCoherent)
    (h3 : X.tailColor c₃ = X.headColor c₃) (h4 : X.tailColor c₄ = X.tailColor c₃)
    (h34 : X.headColor c₄ ≠ X.tailColor c₃) :
    (X.contraction c₃ c₄).IsSemiregular := by
  classical
  -- the `[m]` side: the degree of a component is `|M_j|` (Lemma 3.4.6)
  have hA : ∀ (B : {B : Set Ω // ∃ x ∈ X.vertexClass (X.tailColor c₃), B = X.compOf c₃ x})
      (x : Ω), (B : Set Ω) = X.compOf c₃ x →
      (X.contraction c₃ c₄).degA B = (X.outNbhdComp c₃ c₄ x).ncard := by
    intro B x hBx
    have himg : Subtype.val '' {v : X.vertexClass (X.headColor c₄) |
        (B, v) ∈ (X.contraction c₃ c₄).E} = X.outNbhdComp c₃ c₄ x := by
      ext v
      constructor
      · rintro ⟨⟨w, hw⟩, ⟨z, hz, hzv⟩, rfl⟩
        exact ⟨z, by rw [← hBx]; exact hz, hzv⟩
      · rintro ⟨z, hz, hzv⟩
        exact ⟨⟨v, X.vcolor_snd_eq h hzv⟩, ⟨z, by rw [hBx]; exact hz, hzv⟩, rfl⟩
    rw [BipGraph.degA, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  -- the `Ω₂` side: the degree of `y` is `|E(y)|` (Lemma 3.4.8)
  have hB : ∀ y : X.vertexClass (X.headColor c₄),
      (X.contraction c₃ c₄).degB y = (X.componentsMeeting c₃ c₄ (y : Ω)).ncard := by
    intro y
    have himg : Subtype.val '' {B : {B : Set Ω // ∃ x ∈ X.vertexClass (X.tailColor c₃),
        B = X.compOf c₃ x} | (B, y) ∈ (X.contraction c₃ c₄).E}
        = X.componentsMeeting c₃ c₄ (y : Ω) := by
      ext C
      constructor
      · rintro ⟨⟨B, hB⟩, hmem, rfl⟩
        exact ⟨hB, hmem⟩
      · rintro ⟨hC, hmeet⟩
        exact ⟨⟨C, hC⟩, hmeet, rfl⟩
    rw [BipGraph.degB, ← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  constructor
  · refine ⟨(X.outNbhdComp c₃ c₄ (X.colorWitness c₃).1).ncard, fun B => ?_⟩
    obtain ⟨x, hx, hBx⟩ := B.2
    rw [hA B x hBx]
    exact X.ncard_outNbhd_component_eq c₃ c₄ h h3 h4 h34 hx
      (show X.vcolor (X.colorWitness c₃).1 = X.tailColor c₃ from rfl)
  · refine ⟨(X.componentsMeeting c₃ c₄ (X.colorWitness c₄).2).ncard, fun y => ?_⟩
    rw [hB y]
    exact X.ncard_components_meeting_eq c₃ c₄ h h3 h4 h34 y.2
      (show X.vcolor (X.colorWitness c₄).2 = X.headColor c₄ from rfl)

end Contraction

end PartitionStructure

end Babai
