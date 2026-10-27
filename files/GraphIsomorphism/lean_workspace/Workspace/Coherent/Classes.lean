/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 3.2: Important classes of homogeneous coherent configurations.
-/
import Workspace.Coherent.Basic
import Workspace.Coherent.JohnsonCliques

/-!
# §3.2 Important classes of homogeneous coherent configurations

## Numbering map

| Paper | Lean |
|---|---|
| Definition 3.2.1 | `Babai.PartitionStructure.IsPrimitive`, `.IsUniprimitive` |
| Notation 3.2.2 | `.IsUniprimitive` ("UPCC") |
| Observation 3.2.3 | `.orbitalConfig_isPrimitive_iff`, `.orbitalConfig_isClique_iff`, `.orbitalConfig_isUniprimitive_iff` |
| §3.2.2 association scheme | `.IsAssociationScheme`, `.isHomogeneous_of_isAssociationScheme` |
| §3.2.2 distance configuration | `Babai.Digraph.dist`, `Babai.distConfig` |
| Observation 3.2.4 | `Babai.iso_distConfig`, `Babai.aut_distConfig` |
| Definition 3.2.5 | `Babai.Digraph.IsDistanceRegular`, `Babai.metricScheme` |
| Observation 3.2.6 | `Babai.isDistanceRegular_iff_stronglyRegular` |
| Definition 3.2.7 | `Babai.Digraph.IsDistanceTransitive` |
| Observation 3.2.8 | `Babai.Digraph.IsDistanceTransitive.isDistanceRegular` |
| Definition 3.2.9 | `Babai.johnsonGraph`, `Babai.IsJohnsonGraphParams` |
| Observation 3.2.10 | `Babai.dist_johnsonGraph` |
| Proposition 3.2.11 | `Babai.aut_johnsonGraph` (proved, not cited) |
| Observation 3.2.12 | `Babai.johnsonGraph_isDistanceTransitive` |
| Definition 3.2.13 | `Babai.johnsonScheme` |
| Observation 3.2.14 | `Babai.johnsonScheme_isUniprimitive` |
| §14.1 Align, the map `Aut(J(Γ,t)) → S(Γ)` | `Babai.aut_johnsonScheme`, `Babai.exists_unique_perm_of_mem_aut_johnsonScheme`, `Babai.permEquivAutJohnsonScheme` |
| Remark 3.2.15 | `Babai.johnsonGraph_one_adj_iff`, `Babai.johnsonScheme_one_not_isUniprimitive` |
-/

namespace Babai

/-! ### §3.2.1 Primitive and uniprimitive coherent configurations -/

namespace PartitionStructure

variable {Ω : Type*} (X : PartitionStructure Ω)

/-- Definition 3.2.1 (UPCC).  "`X` is *primitive* if it is homogeneous and all
constituents other than the diagonal are connected."

For a homogeneous configuration every off-diagonal constituent has `Ω(k) = Ω`
(`vertexClass_tailColor_subset_effVertex`), so the constituent `X_k = (Ω(k), R_k)` and
the extended constituent `(Ω, R_k)` coincide and we may phrase connectivity for the
latter.  "Connected" is read as weakly connected (Def. 2.4.21); by Prop. 3.4.1 this is
the same as strongly connected for a homogeneous constituent. -/
def IsPrimitive : Prop :=
  X.IsHomogeneous ∧
    ∀ k : Fin X.rank, X.IsOffDiagonalColor k → (X.extConstituent k).IsWeaklyConnected

/-- Definition 3.2.1, Notation 3.2.2.  "`X` is *uniprimitive* if it is primitive and has
rank ≥ 3, i.e. it is not the clique configuration."  We abbreviate "uniprimitive coherent
configuration" as UPCC. -/
def IsUniprimitive : Prop := X.IsPrimitive ∧ 3 ≤ X.rank

/-- Definition 3.1.1 depends on the coloring only through its kernel: two colorings of
`Ω × Ω` with the same color classes have the same rank.  (Companion of
`PartitionStructure.isCoherent_congr`; this is the paper's silent convention that the
names of the colors do not matter.) -/
theorem rank_congr {Y Y' : PartitionStructure Ω}
    (hker : ∀ x y u v : Ω, Y.color x y = Y.color u v ↔ Y'.color x y = Y'.color u v) :
    Y.rank = Y'.rank := by
  classical
  have hbij : Function.Bijective
      (fun i : Fin Y.rank => Y'.color (Y.colorWitness i).1 (Y.colorWitness i).2) := by
    constructor
    · intro i j hij
      have h := (hker (Y.colorWitness i).1 (Y.colorWitness i).2
        (Y.colorWitness j).1 (Y.colorWitness j).2).2 hij
      rwa [Y.color_colorWitness, Y.color_colorWitness] at h
    · intro i'
      refine ⟨Y.color (Y'.colorWitness i').1 (Y'.colorWitness i').2, ?_⟩
      have h : Y.color (Y.colorWitness (Y.color (Y'.colorWitness i').1
          (Y'.colorWitness i').2)).1 (Y.colorWitness (Y.color (Y'.colorWitness i').1
          (Y'.colorWitness i').2)).2
          = Y.color (Y'.colorWitness i').1 (Y'.colorWitness i').2 :=
        Y.color_colorWitness _
      have h' := (hker _ _ _ _).1 h
      show Y'.color (Y.colorWitness (Y.color (Y'.colorWitness i').1
        (Y'.colorWitness i').2)).1 (Y.colorWitness (Y.color (Y'.colorWitness i').1
        (Y'.colorWitness i').2)).2 = i'
      rw [h', Y'.color_colorWitness]
  have h := Fintype.card_of_bijective hbij
  simpa using h

/-- Definition 3.2.1 depends on the coloring only through its kernel. -/
theorem isPrimitive_congr {Y Y' : PartitionStructure Ω}
    (hker : ∀ x y u v : Ω, Y.color x y = Y.color u v ↔ Y'.color x y = Y'.color u v)
    (h : Y.IsPrimitive) : Y'.IsPrimitive := by
  obtain ⟨hhom, hconn⟩ := h
  refine ⟨fun x y => (hker x x y y).1 (hhom x y), fun i' hoff => ?_⟩
  set p := Y'.colorWitness i' with hp
  set i := Y.color p.1 p.2 with hi
  have hrel : Y'.rel i' = Y.rel i := by
    ext q
    simp only [mem_rel]
    constructor
    · intro hq
      have h1 : Y'.color q.1 q.2 = Y'.color p.1 p.2 := by
        rw [hq, hp, Y'.color_colorWitness]
      exact (hker q.1 q.2 p.1 p.2).2 h1
    · intro hq
      have h1 : Y'.color q.1 q.2 = Y'.color p.1 p.2 := (hker q.1 q.2 p.1 p.2).1 hq
      rw [h1, hp, Y'.color_colorWitness]
  have hoff' : Y.IsOffDiagonalColor i := by
    rw [IsOffDiagonalColor, ← hrel]
    exact hoff
  have hc := hconn i hoff'
  have hdig : Y'.extConstituent i' = Y.extConstituent i := by
    rw [extConstituent, extConstituent, hrel]
  rw [hdig]
  exact hc

/-- Definition 3.2.1 and Notation 3.2.2 depend on the coloring only through its kernel. -/
theorem isUniprimitive_congr {Y Y' : PartitionStructure Ω}
    (hker : ∀ x y u v : Ω, Y.color x y = Y.color u v ↔ Y'.color x y = Y'.color u v)
    (h : Y.IsUniprimitive) : Y'.IsUniprimitive :=
  ⟨isPrimitive_congr hker h.1, by rw [← rank_congr hker]; exact h.2⟩

/-- Observation 3.2.3.  "Let `G ≤ S(Ω)` be a permutation group.  The orbital configuration
`X(G)` is primitive if and only if the group `G` is primitive." -/
theorem orbitalConfig_isPrimitive_iff [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω]
    (G : Subgroup (Equiv.Perm Ω)) :
    (orbitalConfig G).IsPrimitive ↔ Babai.IsPrimitive G := by
  classical
  have hcfg : (orbitalConfig G).IsConfiguration :=
    (orbitalConfig_isCoherent G).toIsConfiguration
  constructor
  · -- a block with two points would cut every orbital through it into several components
    rintro ⟨hhom, hconn⟩
    have htrans : IsTransitive G := (orbitalConfig_isHomogeneous_iff G).1 hhom
    obtain ⟨x₀, y₀, hx₀y₀⟩ := exists_pair_ne Ω
    refine ⟨?_, ?_⟩
    · -- `|G| ≥ 2`: transitivity moves `x₀` to `y₀`
      obtain ⟨σ, hσG, hσ⟩ : ∃ σ ∈ G, (σ : Equiv.Perm Ω) x₀ = y₀ := by
        have huniv := (isTransitive_iff_orbit_eq_univ G).1 htrans x₀
        have hy : y₀ ∈ MulAction.orbit G x₀ := by rw [huniv]; trivial
        obtain ⟨g, hg⟩ := hy
        exact ⟨(g : Equiv.Perm Ω), g.2, hg⟩
      have hne : (1 : G) ≠ ⟨σ, hσG⟩ := by
        intro hc
        refine hx₀y₀ ?_
        have h1 : (1 : Equiv.Perm Ω) = σ := congrArg Subtype.val hc
        rw [← hσ, ← h1]; rfl
      have hnt : Nontrivial G := ⟨⟨1, ⟨σ, hσG⟩, hne⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.2 hnt
    · intro B hB
      by_cases hsingle : ∃ x, B = {x}
      · exact Or.inr hsingle
      refine Or.inl ?_
      obtain ⟨x, hx⟩ := hB.1
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ B, y ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact hsingle ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun z hz => hcon z hz⟩⟩
      obtain ⟨ℬ, hℬ, hBmem⟩ := (isBlockOfImprimitivity_iff_mem_invariantPartition G B).1 hB
      set k := (orbitalConfig G).color x y with hk
      have hoff : (orbitalConfig G).IsOffDiagonalColor k := by
        rcases (orbitalConfig G).diagonal_or_offDiagonal hcfg k with hd | ho
        · exact absurd (hd (show ((x, y)) ∈ (orbitalConfig G).rel k from rfl))
            (fun hc => hyx hc.symm)
        · exact ho
      -- every `R_k`-edge has both ends in one part of the block system
      have hedge : ∀ u v : Ω, (orbitalConfig G).color u v = k → ∃ C ∈ ℬ, u ∈ C ∧ v ∈ C := by
        intro u v huv
        obtain ⟨σ, hσG, hσ⟩ := (orbitalConfig_color_eq_iff G u v x y).1 huv
        exact ⟨(σ : Equiv.Perm Ω) '' B, hℬ.permutes σ hσG B hBmem,
          ⟨x, hx, congrArg Prod.fst hσ⟩, ⟨y, hy, congrArg Prod.snd hσ⟩⟩
      have hsame : ∀ u v : Ω, (orbitalConfig G).color u v = k → ∀ C ∈ ℬ, (u ∈ C ↔ v ∈ C) := by
        intro u v huv C hC
        obtain ⟨D, hD, huD, hvD⟩ := hedge u v huv
        have hCD : ∀ w : Ω, w ∈ C → w ∈ D → C = D := by
          intro w hwC hwD
          by_contra hne
          exact (Set.disjoint_left.1 (hℬ.pairwiseDisjoint C hC D hD hne) hwC) hwD
        exact ⟨fun huC => by rw [hCD u huC huD]; exact hvD,
          fun hvC => by rw [hCD v hvC hvD]; exact huD⟩
      -- so weak accessibility never leaves a part
      have hacc : ∀ u v : Ω, ((orbitalConfig G).extConstituent k).WeaklyAccessible u v →
          ∀ C ∈ ℬ, (u ∈ C ↔ v ∈ C) := by
        intro u v hw
        exact ((orbitalConfig G).extConstituent k).weaklyAccessible_rel
          (r := fun a b => ∀ C ∈ ℬ, (a ∈ C ↔ b ∈ C)) (fun _ _ _ => Iff.rfl)
          (fun hab C hC => (hab C hC).symm)
          (fun hab hbc C hC => (hab C hC).trans (hbc C hC))
          (fun a b hab => hsame a b hab) hw
      ext z
      simp only [Set.mem_univ, iff_true]
      exact (hacc x z (hconn k hoff x z) B hBmem).1 hx
  · -- the weak components of an orbital are blocks
    intro hprim
    have htrans : IsTransitive G := hprim.isTransitive
    refine ⟨(orbitalConfig_isHomogeneous_iff G).2 htrans, ?_⟩
    intro k hoff
    set Y := (orbitalConfig G).extConstituent k with hY
    obtain ⟨u₀, v₀, huv⟩ := (orbitalConfig G).color_surjective k
    have hu₀v₀ : u₀ ≠ v₀ := by
      intro hc
      have hmem : ((u₀, v₀)) ∈ (orbitalConfig G).rel k ∩ diag Ω := ⟨huv, hc⟩
      rw [hoff] at hmem
      exact hmem
    have hadj : ∀ σ ∈ G, ∀ u v : Ω,
        Y.Adj ((σ : Equiv.Perm Ω) u) ((σ : Equiv.Perm Ω) v) ↔ Y.Adj u v := by
      intro σ hσ u v
      show (orbitalConfig G).color _ _ = k ↔ (orbitalConfig G).color u v = k
      rw [le_aut_orbitalConfig G hσ u v]
    have hpres : ∀ σ ∈ G, ∀ u v : Ω, Y.WeaklyAccessible u v →
        Y.WeaklyAccessible ((σ : Equiv.Perm Ω) u) ((σ : Equiv.Perm Ω) v) := by
      intro σ hσ u v hw
      refine Y.weaklyAccessible_rel
        (r := fun a b => Y.WeaklyAccessible ((σ : Equiv.Perm Ω) a) ((σ : Equiv.Perm Ω) b))
        (fun a => Y.symmetrization.accessible_refl _)
        (fun hab => Y.symmetrization.accessible_symm Y.symmetrization_adj_symm hab)
        (fun hab hbc => Y.symmetrization.accessible_trans hab hbc)
        (fun a b hab => Y.symmetrization.accessible_of_adj (Or.inl ((hadj σ hσ a b).2 hab))) hw
    have hcompimg : ∀ σ ∈ G,
        (σ : Equiv.Perm Ω) '' Y.weakComponent u₀ = Y.weakComponent ((σ : Equiv.Perm Ω) u₀) := by
      intro σ hσ
      have hmemw : ∀ u v : Ω, v ∈ Y.weakComponent u ↔ Y.WeaklyAccessible u v := by
        intro u v; rw [Y.weakComponent_eq_weaklyAccessible]; exact Iff.rfl
      ext w
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hmemw _ _).2 (hpres σ hσ u₀ a ((hmemw _ _).1 ha))
      · intro hw
        refine ⟨(σ : Equiv.Perm Ω)⁻¹ w, (hmemw _ _).2 ?_, by simp⟩
        have h1 := hpres σ⁻¹ (G.inv_mem hσ) ((σ : Equiv.Perm Ω) u₀) w ((hmemw _ _).1 hw)
        simpa using h1
    have hblock : IsBlockOfImprimitivity G (Y.weakComponent u₀) := by
      refine ⟨⟨u₀, Y.mem_weakComponent_self u₀⟩, fun σ hσ => ?_⟩
      rw [hcompimg σ hσ]
      by_cases hmem : (σ : Equiv.Perm Ω) u₀ ∈ Y.weakComponent u₀
      · exact Or.inl (Y.weakComponent_eq_of_mem hmem)
      · refine Or.inr (Set.eq_empty_iff_forall_notMem.2 fun w hw => hmem ?_)
        have h1 := Y.weakComponent_eq_of_mem hw.1
        have h2 := Y.weakComponent_eq_of_mem hw.2
        have heq : Y.weakComponent ((σ : Equiv.Perm Ω) u₀) = Y.weakComponent u₀ := by
          rw [← h1, h2]
        rw [← heq]
        exact Y.mem_weakComponent_self _
    rcases hprim.2 _ hblock with huniv | ⟨w, hw⟩
    · intro u v
      have hu : u ∈ Y.weakComponent u₀ := by rw [huniv]; trivial
      have hv : v ∈ Y.weakComponent u₀ := by rw [huniv]; trivial
      rw [Y.weakComponent_eq_weaklyAccessible] at hu hv
      exact Y.symmetrization.accessible_trans
        (Y.symmetrization.accessible_symm Y.symmetrization_adj_symm hu) hv
    · exfalso
      have h1 : u₀ ∈ Y.weakComponent u₀ := Y.mem_weakComponent_self u₀
      have h2 : v₀ ∈ Y.weakComponent u₀ := by
        rw [Y.weakComponent_eq_weaklyAccessible]
        exact Y.symmetrization.accessible_of_adj (Or.inl huv)
      rw [hw] at h1 h2
      exact hu₀v₀ (h1.trans h2.symm)

/-- Observation 3.2.3 is false on a one-point set as Def. 3.2.1 and §2.2.1 are worded, and
this is why `orbitalConfig_isPrimitive_iff` carries `[Nontrivial Ω]`.  On `Ω = {0}` the
orbital configuration is primitive by Def. 3.2.1 read literally (it is homogeneous, and it
has no off-diagonal constituent at all, so the condition "all constituents other than the
diagonal are connected" is vacuous), while the trivial group on one point is not primitive,
since §2.2.1 asks `|G| ≥ 2`.  This is a degenerate case of the definitions, not an error of
the paper; see the corrected paper. -/
example :
    (orbitalConfig (⊤ : Subgroup (Equiv.Perm (Fin 1)))).IsPrimitive ∧
      ¬ Babai.IsPrimitive (⊤ : Subgroup (Equiv.Perm (Fin 1))) := by
  classical
  refine ⟨⟨fun x y => by rw [Subsingleton.elim x y], fun k hk => ?_⟩, ?_⟩
  · exfalso
    obtain ⟨⟨x, y⟩, hxy⟩ := (orbitalConfig (⊤ : Subgroup (Equiv.Perm (Fin 1)))).rel_nonempty k
    have hmem : ((x, y) : Fin 1 × Fin 1)
        ∈ (orbitalConfig (⊤ : Subgroup (Equiv.Perm (Fin 1)))).rel k ∩ diag (Fin 1) :=
      ⟨hxy, Subsingleton.elim x y⟩
    rw [hk] at hmem
    exact hmem
  · rintro ⟨hc, -⟩
    have hGsub : Subsingleton (⊤ : Subgroup (Equiv.Perm (Fin 1))) :=
      ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
    have hGcard : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 1))) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨hGsub, ⟨1⟩⟩
    omega

/-- Double transitivity, spelled out on ordered pairs of distinct points: this is the
paper's reading, "the induced action on the set of `n(n-1)` ordered pairs is
transitive" (§2.2.2). -/
theorem isDoublyTransitive_iff_pairs [Fintype Ω] [DecidableEq Ω] [Nontrivial Ω]
    (G : Subgroup (Equiv.Perm Ω)) :
    IsDoublyTransitive G ↔
      ∀ x y u v : Ω, x ≠ y → u ≠ v →
        ∃ σ ∈ G, (σ : Equiv.Perm Ω) u = x ∧ (σ : Equiv.Perm Ω) v = y := by
  classical
  -- the embedding `Fin 2 ↪ Ω` given by an ordered pair of distinct points
  have hemb : ∀ u v : Ω, u ≠ v → ∃ e : Fin 2 ↪ Ω, e 0 = u ∧ e 1 = v := by
    intro u v huv
    refine ⟨⟨![u, v], ?_⟩, rfl, rfl⟩
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  constructor
  · intro hG x y u v hxy huv
    have hpre : MulAction.IsPretransitive G (Fin 2 ↪ Ω) := hG.isPretransitive
    obtain ⟨e₁, he₁0, he₁1⟩ := hemb u v huv
    obtain ⟨e₂, he₂0, he₂1⟩ := hemb x y hxy
    obtain ⟨g, hg⟩ := hpre.exists_smul_eq e₁ e₂
    refine ⟨(g : Equiv.Perm Ω), g.2, ?_, ?_⟩
    · have := congrArg (fun e : Fin 2 ↪ Ω => e 0) hg
      simpa [he₁0, he₂0] using this
    · have := congrArg (fun e : Fin 2 ↪ Ω => e 1) hg
      simpa [he₁1, he₂1] using this
  · intro hpairs
    obtain ⟨x₀, y₀, hx₀y₀⟩ := exists_pair_ne Ω
    obtain ⟨e₀, he₀0, he₀1⟩ := hemb x₀ y₀ hx₀y₀
    refine ⟨e₀, ?_⟩
    ext e
    simp only [Set.mem_univ, iff_true]
    have hne : e 0 ≠ e 1 := fun hc => (by decide : (0 : Fin 2) ≠ 1) (e.injective hc)
    obtain ⟨σ, hσG, h1, h2⟩ := hpairs (e 0) (e 1) x₀ y₀ hne hx₀y₀
    refine ⟨⟨σ, hσG⟩, ?_⟩
    refine Function.Embedding.ext ?_
    intro i
    fin_cases i
    · show σ (e₀ 0) = e 0
      rw [he₀0, h1]
    · show σ (e₀ 1) = e 1
      rw [he₀1, h2]

/-- Observation 3.2.3.  "`X(G)` is a clique configuration if and only if `G` is doubly
transitive." -/
theorem orbitalConfig_rank_eq_two_iff [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) :
    (orbitalConfig G).rank = 2 ↔ IsDoublyTransitive G := by
  classical
  rcases subsingleton_or_nontrivial Ω with hsub | hnt
  · -- `|Ω| ≤ 1`: both sides are false.  The rank is at most `1` (there is at most one
    -- pair), and `G` is not doubly transitive because there is no injective pair at all.
    have h1 : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have hr : (orbitalConfig G).rank ≤ 1 := by
      have h2 := (orbitalConfig G).rank_le_card_sq
      calc (orbitalConfig G).rank ≤ Fintype.card Ω * Fintype.card Ω := h2
        _ ≤ 1 * 1 := Nat.mul_le_mul h1 h1
        _ = 1 := by norm_num
    constructor
    · intro h; omega
    · intro h
      have := ((isMultiplyTransitive_iff G 2).1 h).1
      omega
  haveI := hnt
  have hcfg : (orbitalConfig G).IsConfiguration :=
    (orbitalConfig_isCoherent G).toIsConfiguration
  obtain ⟨x₀, y₀, hx₀y₀⟩ := exists_pair_ne Ω
  rw [isDoublyTransitive_iff_pairs]
  constructor
  · -- rank 2: all off-diagonal pairs have the same color, i.e. they form one orbital
    intro hr x y u v hxy huv
    have hc : (orbitalConfig G).color x y = (orbitalConfig G).color u v :=
      (orbitalConfig G).color_eq_of_rank_two hcfg hr hxy huv
    obtain ⟨σ, hσG, hσ⟩ := (orbitalConfig_color_eq_iff G x y u v).1 hc
    exact ⟨σ, hσG, congrArg Prod.fst hσ, congrArg Prod.snd hσ⟩
  · -- doubly transitive: there are exactly two orbitals, the diagonal and its complement
    intro hpairs
    -- double transitivity implies transitivity, so all diagonal pairs have one color
    have htrans : ∀ x u : Ω, ∃ σ ∈ G, (σ : Equiv.Perm Ω) u = x := by
      intro x u
      by_cases hxu : x = u
      · exact ⟨1, one_mem G, by rw [hxu]; rfl⟩
      · obtain ⟨σ, hσG, h1, -⟩ := hpairs x u u x hxu (Ne.symm hxu)
        exact ⟨σ, hσG, h1⟩
    have hdiag : ∀ x u : Ω, (orbitalConfig G).color x x = (orbitalConfig G).color u u := by
      intro x u
      obtain ⟨σ, hσG, hσ⟩ := htrans x u
      exact (orbitalConfig_color_eq_iff G x x u u).2 ⟨σ, hσG, by rw [hσ]⟩
    have hoff : ∀ x y u v : Ω, x ≠ y → u ≠ v →
        (orbitalConfig G).color x y = (orbitalConfig G).color u v := by
      intro x y u v hxy huv
      obtain ⟨σ, hσG, h1, h2⟩ := hpairs x y u v hxy huv
      exact (orbitalConfig_color_eq_iff G x y u v).2 ⟨σ, hσG, by rw [h1, h2]⟩
    -- hence at most two colors
    have hle : (orbitalConfig G).rank ≤ 2 := by
      have hsub : (Finset.univ : Finset (Fin (orbitalConfig G).rank)) ⊆
          {(orbitalConfig G).color x₀ x₀, (orbitalConfig G).color x₀ y₀} := by
        intro i _
        obtain ⟨u, v, huv⟩ := (orbitalConfig G).color_surjective i
        by_cases he : u = v
        · refine Finset.mem_insert.2 (Or.inl ?_)
          rw [← huv, he]
          exact hdiag v x₀
        · refine Finset.mem_insert_of_mem (Finset.mem_singleton.2 ?_)
          rw [← huv, hoff x₀ y₀ u v hx₀y₀ he]
      have h1 := Finset.card_le_card hsub
      have h2 : ({(orbitalConfig G).color x₀ x₀,
          (orbitalConfig G).color x₀ y₀} : Finset (Fin (orbitalConfig G).rank)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hge : 2 ≤ (orbitalConfig G).rank := (orbitalConfig G).two_le_rank hcfg
    omega

/-- Observation 3.2.3.  "Therefore `X(G)` is a UPCC if and only if `G` is uniprimitive
(primitive but not doubly transitive)." -/
theorem orbitalConfig_isUniprimitive_iff [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) :
    (orbitalConfig G).IsUniprimitive ↔ Babai.IsPrimitive G ∧ ¬ IsDoublyTransitive G := by
  classical
  rcases subsingleton_or_nontrivial Ω with hsub | hnt
  · -- `|Ω| ≤ 1`: both sides are false.  The rank is at most `1 < 3`, and `S(Ω)` is the
    -- trivial group, so `|G| = 1` and `G` is not primitive (§2.2.1 asks `|G| ≥ 2`).
    have h1 : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have hr : (orbitalConfig G).rank ≤ 1 := by
      have h2 := (orbitalConfig G).rank_le_card_sq
      calc (orbitalConfig G).rank ≤ Fintype.card Ω * Fintype.card Ω := h2
        _ ≤ 1 * 1 := Nat.mul_le_mul h1 h1
        _ = 1 := by norm_num
    have hGsub : Subsingleton G :=
      ⟨fun a b => Subtype.ext (Equiv.ext fun x => Subsingleton.elim _ _)⟩
    have hGcard : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hGsub, ⟨1⟩⟩
    constructor
    · rintro ⟨-, h3⟩; omega
    · rintro ⟨⟨hc, -⟩, -⟩; omega
  haveI := hnt
  have hcfg : (orbitalConfig G).IsConfiguration :=
    (orbitalConfig_isCoherent G).toIsConfiguration
  have h2 : 2 ≤ (orbitalConfig G).rank := (orbitalConfig G).two_le_rank hcfg
  rw [IsUniprimitive, orbitalConfig_isPrimitive_iff G]
  refine and_congr_right fun _ => ?_
  rw [← orbitalConfig_rank_eq_two_iff G]
  omega

/-! ### §3.2.2 Association schemes -/

/-- §3.2.2.  "We say that the coherent configuration `X` is an *association scheme* if
`c(x,y) = c(y,x)` for every `x, y ∈ Ω`." -/
def IsAssociationScheme : Prop := ∀ x y : Ω, X.color x y = X.color y x

/-- §3.2.2.  "It follows that association schemes are homogeneous." -/
theorem isHomogeneous_of_isAssociationScheme [Fintype Ω] [DecidableEq Ω]
    (hc : X.IsCoherent) (h : X.IsAssociationScheme) : X.IsHomogeneous := by
  intro x y
  -- `c(x) = tail color of c(x,y) = tail color of c(y,x) = c(y)` (Obs. 3.3.4)
  rw [X.vcolor_fst_eq hc (k := X.color x y) rfl,
    X.vcolor_fst_eq hc (k := X.color x y) (h y x)]

end PartitionStructure

/-! ### §3.2.2 Distance configurations, metric schemes -/

namespace Digraph

variable {Ω : Type*}

/-- §3.2.2.  "`dist_X(x,y)` is the length of a shortest path between `x` and `y`
in `X`." -/
noncomputable def dist (Y : Digraph Ω) (x y : Ω) : ℕ :=
  sInf {t : ℕ | ∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = x ∧ w (Fin.last t) = y}

/-- In a graph (Def. 2.4.13, `E` symmetric) the distance is symmetric: reversing a walk
from `x` to `y` gives a walk of the same length from `y` to `x`. -/
theorem dist_comm (Y : Digraph Ω) (hY : Y.IsGraph) (x y : Ω) : Y.dist x y = Y.dist y x := by
  have hsymm : ∀ u v : Ω, Y.Adj u v → Y.Adj v u := by
    intro u v huv
    have : ((u, v) : Ω × Ω) ∈ invRel Y.E := by rw [← hY.symm]; exact huv
    exact this
  have key : ∀ (a b : Ω) (t : ℕ),
      (∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = a ∧ w (Fin.last t) = b) →
      (∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = b ∧ w (Fin.last t) = a) := by
    rintro a b t ⟨w, hw, h0, hl⟩
    refine ⟨fun i => w i.rev, fun i => ?_, ?_, ?_⟩
    · have e1 : (i.castSucc).rev = (i.rev).succ := by
        refine Fin.ext ?_
        have h1 := i.isLt
        simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
        omega
      have e2 : (i.succ).rev = (i.rev).castSucc := by
        refine Fin.ext ?_
        have h1 := i.isLt
        simp only [Fin.val_rev, Fin.val_succ, Fin.coe_castSucc]
        omega
      show Y.Adj (w (i.castSucc).rev) (w (i.succ).rev)
      rw [e1, e2]
      exact hsymm _ _ (hw i.rev)
    · show w (0 : Fin (t + 1)).rev = b
      rw [Fin.rev_zero]
      exact hl
    · show w (Fin.last t).rev = a
      rw [Fin.rev_last]
      exact h0
  have hset : {t : ℕ | ∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = x ∧ w (Fin.last t) = y}
      = {t : ℕ | ∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = y ∧ w (Fin.last t) = x} := by
    ext t
    exact ⟨key x y t, key y x t⟩
  show sInf _ = sInf _
  rw [hset]

/-- In a graph the vertices at distance one are exactly the adjacent ones. -/
theorem adj_iff_dist_eq_one (Y : Digraph Ω) (hY : Y.IsGraph) (u v : Ω) :
    Y.Adj u v ↔ Y.dist u v = 1 := by
  set L : Ω → Ω → Set ℕ := fun x y =>
    {t : ℕ | ∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = x ∧ w (Fin.last t) = y} with hL
  have hdist : ∀ x y : Ω, Y.dist x y = sInf (L x y) := fun _ _ => rfl
  constructor
  · intro huv
    have hne : u ≠ v := by
      intro hc'
      exact absurd (Set.eq_empty_iff_forall_notMem.1 hY.irrefl (u, v) ⟨huv, hc'⟩) not_false
    have hmem : (1 : ℕ) ∈ L u v := by
      refine ⟨![u, v], fun i => ?_, rfl, rfl⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using huv
    have hle : Y.dist u v ≤ 1 := by rw [hdist]; exact Nat.sInf_le hmem
    have hne0 : Y.dist u v ≠ 0 := by
      intro h0
      rw [hdist] at h0
      have hne' : (L u v).Nonempty := ⟨1, hmem⟩
      have h := Nat.sInf_mem hne'
      rw [h0] at h
      obtain ⟨w, -, hw0, hwl⟩ := h
      exact hne (by rw [← hw0, ← hwl]; rfl)
    omega
  · intro hd
    have hne' : (L u v).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hdist, hcon] at hd
      simp at hd
    have hmem := Nat.sInf_mem hne'
    rw [hdist] at hd
    rw [hd] at hmem
    obtain ⟨w, hw, hw0, hwl⟩ := hmem
    have h := hw 0
    rw [show ((0 : Fin 1).castSucc) = (0 : Fin 2) from rfl, hw0,
      show ((0 : Fin 1).succ) = Fin.last 1 from rfl, hwl] at h
    exact h

/-- A graph is its own symmetrization (Def. 2.4.16), because its edge relation is already
symmetric. -/
theorem symmetrization_eq_self (Y : Digraph Ω) (hY : Y.IsGraph) : Y.symmetrization = Y := by
  unfold Digraph.symmetrization
  rw [← hY.symm, Set.union_self]

/-- In a connected graph the vertices at distance zero are exactly the equal ones.
(Connectivity is needed: `Babai.Digraph.dist` is an infimum, and the infimum of the empty
set of walk lengths is `0`.) -/
theorem dist_eq_zero_iff (Y : Digraph Ω) (hY : Y.IsGraph) (hc : Y.IsWeaklyConnected)
    (x y : Ω) : Y.dist x y = 0 ↔ x = y := by
  set L : Ω → Ω → Set ℕ := fun x y =>
    {t : ℕ | ∃ w : Fin (t + 1) → Ω, Y.IsWalk w ∧ w 0 = x ∧ w (Fin.last t) = y} with hL
  have hdist : ∀ x y : Ω, Y.dist x y = sInf (L x y) := fun _ _ => rfl
  constructor
  · intro h0
    have hacc : Y.Accessible x y := by
      have h := hc x y
      rwa [symmetrization_eq_self Y hY] at h
    obtain ⟨t, w, hw, hw0, hwl⟩ := hacc
    have hne : (L x y).Nonempty := ⟨t, w, hw, hw0, hwl⟩
    have hmem := Nat.sInf_mem hne
    rw [hdist] at h0
    rw [h0] at hmem
    obtain ⟨w', -, hw'0, hw'l⟩ := hmem
    rw [← hw'0, ← hw'l]
    rfl
  · rintro rfl
    have hmem : (0 : ℕ) ∈ L x x := ⟨fun _ => x, fun i => absurd i.2 (by omega), rfl, rfl⟩
    have := Nat.sInf_le hmem
    rw [hdist]
    omega

/-- Observation 3.2.6, the diameter bound. When `mu = 0`, equality or
adjacency is transitive, so connectedness makes the graph complete. When `mu > 0`,
every nonadjacent pair has a common neighbor. -/
theorem IsStronglyRegular.dist_le_two [Fintype Ω] {Y : Digraph Ω}
    {n k lam mu : ℕ} (h : Y.IsStronglyRegular n k lam mu)
    (hc : Y.IsWeaklyConnected) (x y : Ω) : Y.dist x y ≤ 2 := by
  have hsymm : ∀ u v : Ω, Y.Adj u v → Y.Adj v u := by
    intro u v huv
    have : (u, v) ∈ invRel Y.E := by rw [← h.isGraph.symm]; exact huv
    exact this
  by_cases hmu : mu = 0
  · have htrans : ∀ {a b c : Ω}, (a = b ∨ Y.Adj a b) →
        (b = c ∨ Y.Adj b c) → (a = c ∨ Y.Adj a c) := by
      intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      by_cases hac : a = c ∨ Y.Adj a c
      · exact hac
      have hzero := h.common_nonadj a c (fun he => hac (.inl he))
        (fun he => hac (.inr he))
      rw [hmu] at hzero
      have hempty := (Set.ncard_eq_zero (Set.toFinite _)).1 hzero
      have hb : b ∈ outNbr Y.E a ∩ outNbr Y.E c := ⟨hab, hsymm _ _ hbc⟩
      rw [hempty] at hb
      exact hb.elim
    have hacc : Y.Accessible x y := by
      have hxy := hc x y
      rwa [symmetrization_eq_self Y h.isGraph] at hxy
    rcases Y.accessible_rel (r := fun a b => a = b ∨ Y.Adj a b)
      (fun a => Or.inl rfl) htrans (fun _ _ he => Or.inr he) hacc with he | he
    · rw [(dist_eq_zero_iff Y h.isGraph hc x y).2 he]
      omega
    · rw [(adj_iff_dist_eq_one Y h.isGraph x y).1 he]
      omega
  · by_cases he : x = y
    · rw [(dist_eq_zero_iff Y h.isGraph hc x y).2 he]
      omega
    by_cases ha : Y.Adj x y
    · rw [(adj_iff_dist_eq_one Y h.isGraph x y).1 ha]
      omega
    have hpos : 0 < (outNbr Y.E x ∩ outNbr Y.E y).ncard := by
      rw [h.common_nonadj x y he ha]
      omega
    obtain ⟨z, hxz, hyz⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
    apply Nat.sInf_le
    refine ⟨![x, z, y], ?_, rfl, rfl⟩
    intro i
    fin_cases i
    · simpa using hxz
    · simpa using hsymm _ _ hyz

/-- Definition 2.3.4 for digraphs: bijections that preserve the edge relation. -/
def Iso {Ω' : Type*} (X : Digraph Ω) (Y : Digraph Ω') : Set (Ω ≃ Ω') :=
  {f | ∀ x y, X.Adj x y ↔ Y.Adj (f x) (f y)}

/-- A graph isomorphism preserves all walk lengths, hence distances. This also
holds for disconnected digraphs with the chosen value of the empty infimum. -/
theorem dist_eq_of_mem_iso {Ω' : Type*} {X : Digraph Ω} {Y : Digraph Ω'}
    {f : Ω ≃ Ω'} (hf : f ∈ X.Iso Y) (x y : Ω) :
    Y.dist (f x) (f y) = X.dist x y := by
  unfold dist
  congr 1
  ext t
  constructor
  · rintro ⟨w, hw, h0, hl⟩
    refine ⟨fun i => f.symm (w i), fun i => ?_, ?_, ?_⟩
    · exact (hf _ _).2 (by simpa using hw i)
    · simp [h0]
    · simp [hl]
  · rintro ⟨w, hw, h0, hl⟩
    exact ⟨fun i => f (w i), fun i => (hf _ _).1 (hw i),
      congrArg f h0, congrArg f hl⟩

/-- Definition 3.2.7.  "A connected undirected graph `X` is *distance-transitive* if for
every pair `{(x,y),(x',y')}` of pairs of vertices, if `dist(x,y) = dist(x',y')` then
`(∃σ ∈ Aut(X))(x^σ = x' and y^σ = y')`." -/
def IsDistanceTransitive (Y : Digraph Ω) : Prop :=
  Y.IsGraph ∧ Y.IsWeaklyConnected ∧
    ∀ x y x' y' : Ω, Y.dist x y = Y.dist x' y' →
      ∃ σ ∈ Y.Aut, (σ : Equiv.Perm Ω) x = x' ∧ (σ : Equiv.Perm Ω) y = y'

end Digraph

variable {Ω : Type*}

/-- §3.2.2.  "Let `X = (Ω, E)` be a connected undirected graph.  The
*distance-configuration generated by `X`* is the configuration `M(X) = (Ω, dist_X)`." -/
noncomputable def distConfig [Fintype Ω] (Y : Digraph Ω) : PartitionStructure Ω :=
  PartitionStructure.ofColoring (C := ℕ) fun x y => Y.dist x y

/-- Recover the distance label from the finite color number of `distConfig`.
`ofColoring` uses an arbitrary enumeration of its palette. Comparing decoded
labels keeps the paper's fixed distance colors, without allowing color renaming. -/
noncomputable def distConfigLabel [Fintype Ω] (X : Digraph Ω) :
    Fin (distConfig X).rank → ℕ :=
  fun i => ((Finset.univ.image fun p : Ω × Ω => X.dist p.1 p.2).equivFin.symm i).val

@[simp] theorem distConfigLabel_color [Fintype Ω] (X : Digraph Ω) (x y : Ω) :
    distConfigLabel X ((distConfig X).color x y) = X.dist x y := by
  unfold distConfigLabel distConfig PartitionStructure.ofColoring
  simp

/-- §3.2.2. Isomorphisms of distance configurations preserve the actual distance
labels. The finite palettes are decoded with `distConfigLabel`. -/
def distConfigIso {Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (X : Digraph Ω) (Y : Digraph Ω') : Set (Ω ≃ Ω') :=
  {f | ∀ x y, distConfigLabel Y ((distConfig Y).color (f x) (f y)) =
    distConfigLabel X ((distConfig X).color x y)}

/-- Observation 3.2.4. `Iso(M(X), M(Y)) = Iso(X,Y)`, with the distance colors
fixed. This holds for two vertex types and does not need connectedness. -/
theorem iso_distConfig {Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (X : Digraph Ω) (Y : Digraph Ω') (hX : X.IsGraph) (hY : Y.IsGraph) :
    distConfigIso X Y = X.Iso Y := by
  ext f
  change (∀ x y, distConfigLabel Y ((distConfig Y).color (f x) (f y)) =
    distConfigLabel X ((distConfig X).color x y)) ↔ _
  simp only [distConfigLabel_color]
  constructor
  · intro hf x y
    rw [X.adj_iff_dist_eq_one hX, Y.adj_iff_dist_eq_one hY, hf x y]
  · exact fun hf x y => Digraph.dist_eq_of_mem_iso hf x y

/-- Observation 3.2.4, the automorphism case. -/
theorem aut_distConfig [Fintype Ω] (Y : Digraph Ω) (hY : Y.IsGraph)
    (hc : Y.IsWeaklyConnected) : (distConfig Y).Aut = Y.Aut := by
  classical
  ext σ
  have h := Set.ext_iff.1 (iso_distConfig Y Y hY hY) σ
  simp only [distConfigIso, Set.mem_setOf_eq, distConfigLabel_color, Digraph.Iso] at h
  rw [PartitionStructure.mem_aut, Digraph.mem_aut]
  simpa only [distConfig, PartitionStructure.ofColoring_color_eq_iff, Digraph.adj_def,
    Iff.comm] using h

/-- Definition 3.2.5 (Distance-regular graph, metric scheme).  "The connected undirected
graph `X` is said to be *distance-regular* if `M(X)` is an association scheme; in this
case we call `M(X)` the *metric scheme generated by `X`*." -/
def Digraph.IsDistanceRegular [Fintype Ω] (Y : Digraph Ω) : Prop :=
  Y.IsGraph ∧ Y.IsWeaklyConnected ∧ (distConfig Y).IsCoherent ∧
    (distConfig Y).IsAssociationScheme

/-- Definition 3.2.5.  "…we call `M(X)` the *metric scheme generated by `X`*." -/
noncomputable def metricScheme [Fintype Ω] (Y : Digraph Ω) : PartitionStructure Ω :=
  distConfig Y

/-- The distance and diagonal/edge/nonedge colorings agree when the diameter
is at most two. This is the coloring step in Observation 3.2.6. -/
theorem isDistanceRegular_iff_stronglyRegular_of_diameter_le_two [Fintype Ω] (Y : Digraph Ω)
    (hY : Y.IsGraph) (hc : Y.IsWeaklyConnected) (hdiam : ∀ x y : Ω, Y.dist x y ≤ 2) :
    Y.IsDistanceRegular ↔ ∃ n k lam mu : ℕ, Y.IsStronglyRegular n k lam mu := by
  classical
  -- with `hdiam` the distance is exactly the three-valued coloring of Example 3.1.7
  have hdc : ∀ x y : Ω,
      Y.dist x y = ((PartitionStructure.digraphColor Y x y : Fin 3) : ℕ) := by
    intro x y
    by_cases hxy : x = y
    · rw [(Digraph.dist_eq_zero_iff Y hY hc x y).2 hxy,
        PartitionStructure.digraphColor, if_pos hxy]
      rfl
    · by_cases hadj : (x, y) ∈ Y.E
      · rw [PartitionStructure.digraphColor, if_neg hxy, if_pos hadj]
        show Y.dist x y = 1
        exact (Digraph.adj_iff_dist_eq_one Y hY x y).1 hadj
      · have h0 : Y.dist x y ≠ 0 := fun h => hxy ((Digraph.dist_eq_zero_iff Y hY hc x y).1 h)
        have h1 : Y.dist x y ≠ 1 := fun h =>
          hadj ((Digraph.adj_iff_dist_eq_one Y hY x y).2 h)
        have h2 := hdiam x y
        rw [PartitionStructure.digraphColor, if_neg hxy, if_neg hadj]
        show Y.dist x y = 2
        omega
  -- so `M(Y)` and `X(Y)` have the same color classes
  have hker : ∀ x y u v : Ω, (distConfig Y).color x y = (distConfig Y).color u v ↔
      (PartitionStructure.ofDigraph Y).color x y
        = (PartitionStructure.ofDigraph Y).color u v := by
    intro x y u v
    rw [distConfig, PartitionStructure.ofColoring_color_eq_iff,
      PartitionStructure.ofDigraph_eq_ofColoring,
      PartitionStructure.ofColoring_color_eq_iff, hdc x y, hdc u v]
    exact ⟨fun h => Fin.val_injective h, fun h => by rw [h]⟩
  constructor
  · rintro ⟨-, -, hcoh, -⟩
    rw [← PartitionStructure.ofDigraph_isCoherent_iff Y hY]
    exact PartitionStructure.isCoherent_congr hker hcoh
  · intro hsr
    refine ⟨hY, hc, ?_, ?_⟩
    · exact PartitionStructure.isCoherent_congr (fun x y u v => (hker x y u v).symm)
        ((PartitionStructure.ofDigraph_isCoherent_iff Y hY).2 hsr)
    · intro x y
      exact (PartitionStructure.ofColoring_color_eq_iff
        (fun x y : Ω => Y.dist x y) _ _ y x).2 (Y.dist_comm hY x y)

/-- Observation 3.2.6. The connected strongly regular graphs are precisely
the distance-regular graphs of diameter at most two. -/
theorem isDistanceRegular_iff_stronglyRegular [Fintype Ω] (Y : Digraph Ω)
    (hY : Y.IsGraph) (hc : Y.IsWeaklyConnected) :
    (∃ n k lam mu : ℕ, Y.IsStronglyRegular n k lam mu) ↔
      (Y.IsDistanceRegular ∧ ∀ x y : Ω, Y.dist x y ≤ 2) := by
  constructor
  · intro hsr
    obtain ⟨n, k, lam, mu, h⟩ := hsr
    have hd := h.dist_le_two hc
    exact ⟨(isDistanceRegular_iff_stronglyRegular_of_diameter_le_two Y hY hc hd).2
      ⟨n, k, lam, mu, h⟩, hd⟩
  · rintro ⟨h, hd⟩
    exact (isDistanceRegular_iff_stronglyRegular_of_diameter_le_two Y hY hc hd).1 h

/-- Observation 3.2.8.  "A distance-transitive graph is necessarily
distance-regular." -/
theorem Digraph.IsDistanceTransitive.isDistanceRegular [Fintype Ω] {Y : Digraph Ω}
    (h : Y.IsDistanceTransitive) : Y.IsDistanceRegular := by
  classical
  obtain ⟨hY, hc, htr⟩ := h
  refine ⟨hY, hc, ?_, ?_⟩
  · -- the color classes of `M(Y)` are exactly the orbitals of `Aut(Y)`, so `M(Y)` is the
    -- orbital configuration `X(Aut(Y))` up to the names of the colors (Obs. 3.1.12)
    refine PartitionStructure.isCoherent_congr
      (X := PartitionStructure.orbitalConfig Y.Aut) ?_
      (PartitionStructure.orbitalConfig_isCoherent Y.Aut)
    intro x y u v
    rw [PartitionStructure.orbitalConfig_color_eq_iff]
    show (∃ σ ∈ Y.Aut, ((σ : Equiv.Perm Ω) u, (σ : Equiv.Perm Ω) v) = (x, y))
      ↔ (distConfig Y).color x y = (distConfig Y).color u v
    rw [distConfig, PartitionStructure.ofColoring_color_eq_iff]
    constructor
    · rintro ⟨σ, hσ, hσ'⟩
      -- an automorphism of `Y` preserves the distance (Obs. 3.2.4)
      have hmem : σ ∈ (distConfig Y).Aut := by rw [aut_distConfig Y hY hc]; exact hσ
      have hpres := PartitionStructure.mem_aut.1 hmem u v
      have hd : Y.dist ((σ : Equiv.Perm Ω) u) ((σ : Equiv.Perm Ω) v) = Y.dist u v :=
        (PartitionStructure.ofColoring_color_eq_iff
          (fun x y : Ω => Y.dist x y) _ _ u v).1 hpres
      obtain ⟨hx, hy⟩ := Prod.mk.injEq .. ▸ hσ'
      rw [← hx, ← hy]
      exact hd
    · intro hd
      obtain ⟨σ, hσ, h1, h2⟩ := htr u v x y hd.symm
      exact ⟨σ, hσ, by rw [h1, h2]⟩
  · -- an association scheme, because the distance is symmetric (`Digraph.dist_comm`)
    intro x y
    exact (PartitionStructure.ofColoring_color_eq_iff
      (fun x y : Ω => Y.dist x y) _ _ y x).2 (Y.dist_comm hY x y)

/-! ### §3.2.2 Johnson graphs and Johnson schemes -/

section Johnson

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- Definition 3.2.9 (Johnson graph).  "Let `t ≥ 2` and let `Γ` be a set of size
`|Γ| = k ≥ 2t + 1`.  The *Johnson graph* `J(Γ,t) = (Ω; c)` is an undirected graph with
`k choose t` vertices corresponding to the `t`-subsets of a `k`-set `Γ`,
`Ω = {v_T | T ∈ (Γ choose t)}`.  For `S, T ∈ (Γ choose t)`, the vertices `v_S` and `v_T`
are adjacent if `|S \ T| = 1`."

The parameter constraints `t ≥ 2` and `|Γ| ≥ 2t + 1` of the definition are recorded
separately in `IsJohnsonGraphParams`; Remark 3.2.15 is about exactly the excluded
degenerate case `t = 1`. -/
def johnsonGraph (Γ : Type*) [DecidableEq Γ] (t : ℕ) : Digraph (binom Γ t) :=
  ⟨{p | ((p.1 : Finset Γ) \ (p.2 : Finset Γ)).card = 1}⟩

/-- Definition 3.2.9.  The parameter constraints: `t ≥ 2` and `|Γ| = k ≥ 2t + 1`. -/
def IsJohnsonGraphParams (Γ : Type*) [Fintype Γ] (t : ℕ) : Prop :=
  2 ≤ t ∧ 2 * t + 1 ≤ Fintype.card Γ

/-- Adjacency in the Johnson graph, unfolded. -/
theorem johnsonGraph_adj_iff (t : ℕ) (S T : binom Γ t) :
    (johnsonGraph Γ t).Adj S T ↔ ((S : Finset Γ) \ (T : Finset Γ)).card = 1 := Iff.rfl

/-- A permutation of `Γ` acting on `t`-sets preserves `|S \ T|`, the color of the Johnson
scheme (Def. 3.2.13). -/
theorem card_sdiff_tAction (t : ℕ) (π : Equiv.Perm Γ) (S T : binom Γ t) :
    (((tAction t π S : binom Γ t) : Finset Γ) \
      ((tAction t π T : binom Γ t) : Finset Γ)).card
      = ((S : Finset Γ) \ (T : Finset Γ)).card := by
  rw [tAction_apply_coe, tAction_apply_coe,
    ← Finset.image_sdiff _ _ π.injective, Finset.card_image_of_injective _ π.injective]

/-- Proposition 3.2.11, the easy inclusion `Aut(J(Γ,t)) ≥ S^(t)(Γ)`: a permutation of `Γ`
acting on `t`-sets preserves `|S \ T|`, hence adjacency. -/
theorem tAction_mem_aut_johnsonGraph (t : ℕ) (π : Equiv.Perm Γ) :
    tAction t π ∈ (johnsonGraph Γ t).Aut := by
  refine Digraph.mem_aut.2 fun S T => ?_
  show ((((tAction t π S : binom Γ t) : Finset Γ) \
      ((tAction t π T : binom Γ t) : Finset Γ)).card = 1) ↔ _
  rw [card_sdiff_tAction]
  rfl

/-- Proposition 3.2.11, the easy inclusion `Aut(J(Γ,t)) ≥ S^(t)(Γ)`. -/
theorem inducedOnTSets_le_aut_johnsonGraph (t : ℕ) :
    inducedOnTSets (⊤ : Subgroup (Equiv.Perm Γ)) t ≤ (johnsonGraph Γ t).Aut := by
  rintro _ hσ
  obtain ⟨π, -, rfl⟩ := Subgroup.mem_map.1 hσ
  exact tAction_mem_aut_johnsonGraph t π

/-- Proposition 3.2.11, main step.  An automorphism of `J(Γ,t+1)` carries the star of a
`t`-set `A` onto the star of a `t`-set `A'`.  Reason: the image of a star is a clique of
the same size `|Γ| - t`, every clique with two vertices lies in a star or in a top
(`Babai.Johnson.clique_star_or_top`), a top has at most `t + 2` vertices, and
`|Γ| - t > t + 2` because `|Γ| ≥ 2t + 3`. -/
theorem exists_star_image {t : ℕ} (hk : 2 * t + 3 ≤ Fintype.card Γ)
    {σ : Equiv.Perm (binom Γ (t + 1))} (hσ : σ ∈ (johnsonGraph Γ (t + 1)).Aut)
    (A : binom Γ t) :
    ∃ A' : binom Γ t, ∀ S : binom Γ (t + 1),
      ((A : Finset Γ) ⊆ (S : Finset Γ) ↔
        (A' : Finset Γ) ⊆ ((σ S : binom Γ (t + 1)) : Finset Γ)) := by
  classical
  set C := (Johnson.star t (A : Finset Γ)).image σ with hC
  have hcardC : C.card = Fintype.card Γ - t := by
    rw [hC, Finset.card_image_of_injective _ σ.injective, Johnson.card_star A.2]
  -- the image of a star is a clique
  have hclique : ∀ U ∈ C, ∀ V ∈ C, U ≠ V → ((U : Finset Γ) \ (V : Finset Γ)).card = 1 := by
    intro U hU V hV hUV
    rw [hC, Finset.mem_image] at hU hV
    obtain ⟨U₀, hU₀, rfl⟩ := hU
    obtain ⟨V₀, hV₀, rfl⟩ := hV
    have hne : U₀ ≠ V₀ := fun h => hUV (by rw [h])
    have := Johnson.star_clique A.2 U₀.2 V₀.2 (Johnson.mem_star.1 hU₀)
      (Johnson.mem_star.1 hV₀) (fun h => hne (Subtype.ext h))
    exact (Digraph.mem_aut.1 hσ U₀ V₀).2 this
  -- two distinct vertices in the image
  obtain ⟨U, hU, V, hV, hUV⟩ := Finset.one_lt_card.1 (by omega : 1 < C.card)
  have hUVadj := hclique U hU V hV hUV
  rcases Johnson.clique_star_or_top C hclique hU hV hUV with hcase | hcase
  · -- the image lies in the star of `U ∩ V`, and has the same size, so it is that star
    have hA'card : ((U : Finset Γ) ∩ (V : Finset Γ)).card = t :=
      Johnson.card_inter_of_card_sdiff_eq_one U.2 hUVadj
    refine ⟨⟨(U : Finset Γ) ∩ (V : Finset Γ), hA'card⟩, ?_⟩
    have hCsub : C ⊆ Johnson.star t ((U : Finset Γ) ∩ (V : Finset Γ)) :=
      fun W hW => Johnson.mem_star.2 (hcase W hW)
    have hCeq : C = Johnson.star t ((U : Finset Γ) ∩ (V : Finset Γ)) := by
      refine Finset.eq_of_subset_of_card_le hCsub ?_
      rw [Johnson.card_star hA'card]
      omega
    intro S
    constructor
    · intro hAS
      have hmem : σ S ∈ C := by
        rw [hC]; exact Finset.mem_image_of_mem _ (Johnson.mem_star.2 hAS)
      rw [hCeq] at hmem
      exact Johnson.mem_star.1 hmem
    · intro hA'
      have hmem : σ S ∈ C := by rw [hCeq]; exact Johnson.mem_star.2 hA'
      rw [hC, Finset.mem_image] at hmem
      obtain ⟨S₀, hS₀, hS₀eq⟩ := hmem
      have hSS : S₀ = S := σ.injective hS₀eq
      exact Johnson.mem_star.1 (hSS ▸ hS₀)
  · -- a top is too small
    exfalso
    have hB : ((U : Finset Γ) ∪ (V : Finset Γ)).card = t + 2 :=
      Johnson.card_union_of_card_sdiff_eq_one U.2 V.2 hUVadj
    have := Johnson.card_le_of_subset_top hB hcase
    omega

/-- Proposition 3.2.11 for all `t ≥ 1` (Def. 3.2.9 asks for `t ≥ 2`; the proof needs the
case `t = 1`, where `J(Γ,1)` is the complete graph).

Route, by induction on `t`.  For `t = 1` every permutation of the `1`-sets comes from a
permutation of `Γ`.  For the step, an automorphism of `J(Γ,t+1)` permutes the stars
(`Babai.exists_star_image`), so it induces a permutation `f` of the `t`-sets.  Two
`t`-sets lie in a common `(t+1)`-set exactly when they are adjacent in `J(Γ,t)`
(`Babai.Johnson.card_sdiff_eq_one_iff`), so `f` is an automorphism of `J(Γ,t)`, hence by
induction is induced by a permutation `π` of `Γ`.  Finally every `(t+1)`-set is the union
of its `t`-subsets, so the automorphism agrees with `π` on every vertex. -/
theorem aut_johnsonGraph_of_one_le :
    ∀ t : ℕ, 1 ≤ t → 2 * t + 1 ≤ Fintype.card Γ →
      (johnsonGraph Γ t).Aut = inducedOnTSets (⊤ : Subgroup (Equiv.Perm Γ)) t := by
  classical
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
    intro _ hk
    refine le_antisymm ?_ (inducedOnTSets_le_aut_johnsonGraph (t + 1))
    intro σ hσ
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · -- base case `t = 1`: `J(Γ,1)` is the complete graph on the points of `Γ`
      set e := Johnson.oneEquiv Γ with he
      refine Subgroup.mem_map.2 ⟨e.trans (σ.trans e.symm), trivial, ?_⟩
      refine Equiv.ext fun S => Subtype.ext ?_
      obtain ⟨x, rfl⟩ : ∃ x, S = e x := ⟨e.symm S, by simp⟩
      show ((e x : binom Γ 1) : Finset Γ).image _ = _
      rw [Johnson.oneEquiv_apply, Finset.image_singleton]
      show ({(e.symm (σ (e x)) : Γ)} : Finset Γ) = ((σ (e x) : binom Γ 1) : Finset Γ)
      rw [← Johnson.oneEquiv_apply, ← he, Equiv.apply_symm_apply]
    · -- induction step
      have hk3 : 2 * t + 3 ≤ Fintype.card Γ := by omega
      have hIH := ih ht (by omega)
      choose f hf using exists_star_image hk3 hσ
      choose g hg using exists_star_image hk3 (Subgroup.inv_mem _ hσ)
      -- `f` and `g` are mutually inverse
      have hgf : ∀ A : binom Γ t, g (f A) = A := by
        intro A
        refine Subtype.ext (Johnson.eq_of_forall_supset A.2 (g (f A)).2 (by omega) ?_)
        intro S hS hsub
        have h1 : ((f A : binom Γ t) : Finset Γ) ⊆ ((σ ⟨S, hS⟩ : binom Γ (t + 1)) : Finset Γ) :=
          (hf A ⟨S, hS⟩).1 hsub
        have h2 := (hg (f A) (σ ⟨S, hS⟩)).1 h1
        simpa using h2
      have hfg : ∀ A : binom Γ t, f (g A) = A := by
        intro A
        refine Subtype.ext (Johnson.eq_of_forall_supset A.2 (f (g A)).2 (by omega) ?_)
        intro S hS hsub
        have h1 : ((g A : binom Γ t) : Finset Γ)
            ⊆ ((σ⁻¹ ⟨S, hS⟩ : binom Γ (t + 1)) : Finset Γ) := (hg A ⟨S, hS⟩).1 hsub
        have h2 := (hf (g A) (σ⁻¹ ⟨S, hS⟩)).1 h1
        simpa using h2
      set F : Equiv.Perm (binom Γ t) := ⟨f, g, hgf, hfg⟩ with hF
      -- `F` is an automorphism of `J(Γ,t)`
      have hFaut : F ∈ (johnsonGraph Γ t).Aut := by
        refine Digraph.mem_aut.2 fun A B => ?_
        show ((f A : Finset Γ) \ (f B : Finset Γ)).card = 1 ↔
          ((A : Finset Γ) \ (B : Finset Γ)).card = 1
        refine (Johnson.card_sdiff_eq_one_iff (f A).2 (f B).2).trans
          (Iff.trans ?_ (Johnson.card_sdiff_eq_one_iff A.2 B.2).symm)
        constructor
        · rintro ⟨hne, S, hS, hAS, hBS⟩
          refine ⟨fun h => hne (by rw [Subtype.ext h]),
            ((σ⁻¹ ⟨S, hS⟩ : binom Γ (t + 1)) : Finset Γ), (σ⁻¹ ⟨S, hS⟩).2, ?_, ?_⟩
          · refine (hf A (σ⁻¹ ⟨S, hS⟩)).2 ?_
            simpa using hAS
          · refine (hf B (σ⁻¹ ⟨S, hS⟩)).2 ?_
            simpa using hBS
        · rintro ⟨hne, S, hS, hAS, hBS⟩
          refine ⟨fun h => hne ?_, ((σ ⟨S, hS⟩ : binom Γ (t + 1)) : Finset Γ), (σ ⟨S, hS⟩).2,
            (hf A ⟨S, hS⟩).1 hAS, (hf B ⟨S, hS⟩).1 hBS⟩
          have h1 : f A = f B := Subtype.ext h
          have h2 := congrArg g h1
          rw [hgf, hgf] at h2
          exact congrArg Subtype.val h2
      -- by induction, `F` comes from a permutation `π` of `Γ`
      rw [hIH] at hFaut
      obtain ⟨π, -, hπ⟩ := Subgroup.mem_map.1 hFaut
      refine Subgroup.mem_map.2 ⟨π, trivial, ?_⟩
      have hfπ : ∀ A : binom Γ t, ((f A : binom Γ t) : Finset Γ) = (A : Finset Γ).image π := by
        intro A
        have h1 : (tAction t π) A = f A := by rw [hπ]; rfl
        exact (congrArg Subtype.val h1).symm.trans (tAction_apply_coe t π A)
      refine Equiv.ext fun S => Subtype.ext ?_
      show (S : Finset Γ).image π = ((σ S : binom Γ (t + 1)) : Finset Γ)
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.1 hz
        -- a `t`-subset of `S` containing `y`
        obtain ⟨w, hwS, hwy⟩ : ∃ w ∈ (S : Finset Γ), w ≠ y := by
          obtain ⟨p, hp, q, hq, hpq⟩ :=
            Finset.one_lt_card.1 (by rw [S.2]; omega : 1 < (S : Finset Γ).card)
          by_cases h : p = y
          · exact ⟨q, hq, fun hqy => hpq (h.trans hqy.symm)⟩
          · exact ⟨p, hp, h⟩
        have hAcard : ((S : Finset Γ).erase w).card = t := by
          rw [Finset.card_erase_of_mem hwS, S.2]
          omega
        have hsub : ((S : Finset Γ).erase w) ⊆ (S : Finset Γ) := Finset.erase_subset _ _
        have hy : y ∈ (S : Finset Γ).erase w := Finset.mem_erase.2 ⟨fun h => hwy h.symm, hyS⟩
        have := (hf ⟨_, hAcard⟩ S).1 hsub
        rw [hfπ ⟨_, hAcard⟩] at this
        exact this (Finset.mem_image_of_mem π hy)
      · rw [(σ S).2, Finset.card_image_of_injective _ π.injective, S.2]

/-- Observation 3.2.10, the lower bound.  Along a walk of the Johnson graph the quantity
`|S \ T|` grows by at most one per step, so a walk from `S` to `T` has length at least
`|S \ T|`. -/
theorem card_sdiff_le_of_isWalk (t : ℕ) : ∀ (n : ℕ) (w : Fin (n + 1) → binom Γ t),
    (johnsonGraph Γ t).IsWalk w →
      (((w 0 : binom Γ t) : Finset Γ) \
        ((w (Fin.last n) : binom Γ t) : Finset Γ)).card ≤ n := by
  intro n
  induction n with
  | zero =>
    intro w _
    have h0 : (Fin.last 0) = (0 : Fin 1) := rfl
    rw [h0]
    simp
  | succ n ih =>
    intro w hw
    have hw' : (johnsonGraph Γ t).IsWalk (fun i : Fin (n + 1) => w i.succ) := by
      intro i
      show (johnsonGraph Γ t).Adj (w i.castSucc.succ) (w i.succ.succ)
      rw [Fin.succ_castSucc]
      exact hw i.succ
    have hlast : ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.succ_last n
    have hstep : (((w ((0 : Fin (n + 1)).succ) : binom Γ t) : Finset Γ) \
        ((w ((Fin.last n).succ) : binom Γ t) : Finset Γ)).card ≤ n :=
      ih (fun i : Fin (n + 1) => w i.succ) hw'
    have hedge : (((w 0 : binom Γ t) : Finset Γ) \
        ((w (0 : Fin (n + 1)).succ : binom Γ t) : Finset Γ)).card = 1 := hw 0
    have htri := Johnson.card_sdiff_le_add ((w 0 : binom Γ t) : Finset Γ)
      ((w (0 : Fin (n + 1)).succ : binom Γ t) : Finset Γ)
      ((w (Fin.last (n + 1)) : binom Γ t) : Finset Γ)
    rw [hlast] at hstep
    omega

/-- Observation 3.2.10, the upper bound.  Exchanging one element of `S \ T` for one of
`T \ S` at a time gives a walk of length `|S \ T|` from `S` to `T`. -/
theorem exists_walk_johnsonGraph (t : ℕ) : ∀ (d : ℕ) (S T : binom Γ t),
    ((S : Finset Γ) \ (T : Finset Γ)).card = d →
      ∃ w : Fin (d + 1) → binom Γ t, (johnsonGraph Γ t).IsWalk w ∧
        w 0 = S ∧ w (Fin.last d) = T := by
  intro d
  induction d with
  | zero =>
    intro S T hd
    have hST : S = T := by
      refine Subtype.ext (Finset.eq_of_subset_of_card_le ?_ (by rw [S.2, T.2]))
      exact Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hd)
    exact ⟨fun _ => S, fun i => absurd i.2 (by omega), rfl, by rw [hST]⟩
  | succ d ih =>
    intro S T hd
    -- one element to drop and one to pick up
    obtain ⟨x, hx⟩ : ∃ x, x ∈ (S : Finset Γ) \ (T : Finset Γ) :=
      Finset.card_pos.1 (by omega) |>.imp fun _ h => h
    obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.1 hx
    have hTS : ((T : Finset Γ) \ (S : Finset Γ)).card = d + 1 := by
      have h1 := Finset.card_inter_add_card_sdiff (S : Finset Γ) (T : Finset Γ)
      have h2 := Finset.card_inter_add_card_sdiff (T : Finset Γ) (S : Finset Γ)
      rw [Finset.inter_comm] at h2
      have := S.2; have := T.2
      omega
    obtain ⟨y, hy⟩ : ∃ y, y ∈ (T : Finset Γ) \ (S : Finset Γ) :=
      Finset.card_pos.1 (by omega) |>.imp fun _ h => h
    obtain ⟨hyT, hyS⟩ := Finset.mem_sdiff.1 hy
    have hxy : x ≠ y := fun h => hyS (h ▸ hxS)
    set S' : Finset Γ := insert y ((S : Finset Γ).erase x) with hS'
    have hyerase : y ∉ (S : Finset Γ).erase x := fun h => hyS (Finset.mem_of_mem_erase h)
    have hS'card : S'.card = t := by
      rw [hS', Finset.card_insert_of_notMem hyerase, Finset.card_erase_of_mem hxS, S.2]
      have : 1 ≤ t := by rw [← S.2]; exact Finset.card_pos.2 ⟨x, hxS⟩
      omega
    -- `S'` is adjacent to `S`
    have hadj : ((S : Finset Γ) \ S').card = 1 := by
      have : (S : Finset Γ) \ S' = {x} := by
        ext z
        simp only [Finset.mem_sdiff, hS', Finset.mem_insert, Finset.mem_erase,
          Finset.mem_singleton, not_or]
        constructor
        · rintro ⟨hzS, hz⟩
          by_contra hzx
          exact hz.2 ⟨hzx, hzS⟩
        · rintro rfl
          exact ⟨hxS, fun h => hxy h, fun h => h.1 rfl⟩
      rw [this, Finset.card_singleton]
    -- `S'` is one step closer to `T`
    have hS'T : (S' \ (T : Finset Γ)).card = d := by
      have heq : S' \ (T : Finset Γ) = ((S : Finset Γ) \ (T : Finset Γ)).erase x := by
        ext z
        simp only [Finset.mem_sdiff, hS', Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hz | hz, hzT⟩
          · exact absurd (hz ▸ hyT) hzT
          · exact ⟨hz.1, hz.2, hzT⟩
        · rintro ⟨hzx, hzS, hzT⟩
          exact ⟨Or.inr ⟨hzx, hzS⟩, hzT⟩
      rw [heq, Finset.card_erase_of_mem hx, hd]
      omega
    obtain ⟨w', hw', hw'0, hw'l⟩ := ih ⟨S', hS'card⟩ T hS'T
    refine ⟨Fin.cons S w', ?_, Fin.cons_zero _ _, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · show (johnsonGraph Γ t).Adj ((Fin.cons S w' : Fin (d + 2) → binom Γ t) 0)
          ((Fin.cons S w' : Fin (d + 2) → binom Γ t) (0 : Fin (d + 1)).succ)
        rw [Fin.cons_zero, Fin.cons_succ, hw'0]
        exact hadj
      · intro j
        show (johnsonGraph Γ t).Adj ((Fin.cons S w' : Fin (d + 2) → binom Γ t) j.succ.castSucc)
          ((Fin.cons S w' : Fin (d + 2) → binom Γ t) j.succ.succ)
        rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hw' j
    · rw [show Fin.last (d + 1) = (Fin.last d).succ from (Fin.succ_last d).symm,
        Fin.cons_succ, hw'l]

/-- Observation 3.2.10.  "Consider the Johnson graph `J(Γ,t) = (Ω, E)`.  For
`S, T ∈ (Γ choose t)`, the distance between the vertices `v_S` and `v_T` is
`|S \ T|`." -/
theorem dist_johnsonGraph (t : ℕ) (h : IsJohnsonGraphParams Γ t) (S T : binom Γ t) :
    (johnsonGraph Γ t).dist S T = ((S : Finset Γ) \ (T : Finset Γ)).card := by
  classical
  set L : Set ℕ := {n : ℕ | ∃ w : Fin (n + 1) → binom Γ t, (johnsonGraph Γ t).IsWalk w ∧
    w 0 = S ∧ w (Fin.last n) = T} with hL
  have hmem : ((S : Finset Γ) \ (T : Finset Γ)).card ∈ L :=
    exists_walk_johnsonGraph t _ S T rfl
  refine le_antisymm (Nat.sInf_le hmem) ?_
  obtain ⟨w, hw, hw0, hwl⟩ := Nat.sInf_mem (⟨_, hmem⟩ : L.Nonempty)
  have := card_sdiff_le_of_isWalk t _ w hw
  rw [hw0, hwl] at this
  exact this

/-- Proposition 3.2.11.  "Let us identify the vertex set of the Johnson graph `J(Γ,t)`
with `(Γ choose t)`.  Then `Aut(J(Γ,t)) = S^(t)(Γ)`."

The paper gives no proof: "The inclusion `Aut(J(Γ,t)) ≥ S^(t)(Γ)` is straightforward.
The opposite inclusion can be derived for instance from the Erdős–Ko–Rado theorem."  No
reference key is given, so this is proved here, not axiomatized ("for instance" leaves
the route free; we use cliques instead of Erdős–Ko–Rado).  See
`Babai.aut_johnsonGraph_of_one_le` for the route.  The hypothesis `|Γ| ≥ 2t + 1` is
load-bearing: at `|Γ| = 2t` the complementation map is an extra automorphism. -/
theorem aut_johnsonGraph (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    (johnsonGraph Γ t).Aut = inducedOnTSets (⊤ : Subgroup (Equiv.Perm Γ)) t :=
  aut_johnsonGraph_of_one_le t (le_trans (by norm_num) h.1) h.2

/-- Observation 3.2.12, the group-theoretic step.  If `|S \ T| = |S' \ T'|` then some
permutation of `Γ` carries the pair `(S,T)` to the pair `(S',T')`: the four blocks
`S ∩ T`, `S \ T`, `T \ S` and the rest have the same sizes as the primed ones, so we may
match them up block by block. -/
theorem exists_perm_map_pair {t : ℕ} (S T S' T' : binom Γ t)
    (hd : ((S : Finset Γ) \ (T : Finset Γ)).card
      = ((S' : Finset Γ) \ (T' : Finset Γ)).card) :
    ∃ π : Equiv.Perm Γ, tAction t π S = S' ∧ tAction t π T = T' := by
  classical
  -- the four blocks have matching sizes
  have hi1 := Finset.card_inter_add_card_sdiff (S : Finset Γ) (T : Finset Γ)
  have hi2 := Finset.card_inter_add_card_sdiff (T : Finset Γ) (S : Finset Γ)
  have hi3 := Finset.card_inter_add_card_sdiff (S' : Finset Γ) (T' : Finset Γ)
  have hi4 := Finset.card_inter_add_card_sdiff (T' : Finset Γ) (S' : Finset Γ)
  have hu1 := Finset.card_union_add_card_inter (S : Finset Γ) (T : Finset Γ)
  have hu2 := Finset.card_union_add_card_inter (S' : Finset Γ) (T' : Finset Γ)
  have hc1 : (((S : Finset Γ) ∪ (T : Finset Γ))ᶜ).card
      = Fintype.card Γ - ((S : Finset Γ) ∪ (T : Finset Γ)).card := Finset.card_compl _
  have hc2 : (((S' : Finset Γ) ∪ (T' : Finset Γ))ᶜ).card
      = Fintype.card Γ - ((S' : Finset Γ) ∪ (T' : Finset Γ)).card := Finset.card_compl _
  have hsym1 : ((T : Finset Γ) ∩ (S : Finset Γ)) = ((S : Finset Γ) ∩ (T : Finset Γ)) :=
    Finset.inter_comm _ _
  have hsym2 : ((T' : Finset Γ) ∩ (S' : Finset Γ)) = ((S' : Finset Γ) ∩ (T' : Finset Γ)) :=
    Finset.inter_comm _ _
  rw [hsym1] at hi2
  rw [hsym2] at hi4
  have hS := S.2; have hT := T.2; have hS' := S'.2; have hT' := T'.2
  have hle1 : ((S : Finset Γ) ∪ (T : Finset Γ)).card ≤ Fintype.card Γ :=
    Finset.card_le_univ _
  have hle2 : ((S' : Finset Γ) ∪ (T' : Finset Γ)).card ≤ Fintype.card Γ :=
    Finset.card_le_univ _
  -- the four block equivalences
  obtain ⟨e1⟩ : Nonempty (↥((S : Finset Γ) ∩ (T : Finset Γ))
      ≃ ↥((S' : Finset Γ) ∩ (T' : Finset Γ))) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; omega)⟩
  obtain ⟨e2⟩ : Nonempty (↥((S : Finset Γ) \ (T : Finset Γ))
      ≃ ↥((S' : Finset Γ) \ (T' : Finset Γ))) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; omega)⟩
  obtain ⟨e3⟩ : Nonempty (↥((T : Finset Γ) \ (S : Finset Γ))
      ≃ ↥((T' : Finset Γ) \ (S' : Finset Γ))) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; omega)⟩
  obtain ⟨e4⟩ : Nonempty (↥(((S : Finset Γ) ∪ (T : Finset Γ))ᶜ)
      ≃ ↥(((S' : Finset Γ) ∪ (T' : Finset Γ))ᶜ)) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe]; omega)⟩
  -- the permutation, defined block by block
  set f : Γ → Γ := fun z =>
    if h1 : z ∈ (S : Finset Γ) ∩ (T : Finset Γ) then (e1 ⟨z, h1⟩ : Γ)
    else if h2 : z ∈ (S : Finset Γ) \ (T : Finset Γ) then (e2 ⟨z, h2⟩ : Γ)
    else if h3 : z ∈ (T : Finset Γ) \ (S : Finset Γ) then (e3 ⟨z, h3⟩ : Γ)
    else (e4 ⟨z, by
      simp only [Finset.mem_compl, Finset.mem_union, not_or]
      simp only [Finset.mem_inter, not_and] at h1
      simp only [Finset.mem_sdiff, not_and, not_not] at h2 h3
      exact ⟨fun hzS => h1 hzS (h2 hzS), fun hzT => (h1 (h3 hzT) hzT)⟩⟩ : Γ) with hfdef
  -- `f` keeps track of the block
  have hmem : ∀ z : Γ, (f z ∈ (S' : Finset Γ) ↔ z ∈ (S : Finset Γ)) ∧
      (f z ∈ (T' : Finset Γ) ↔ z ∈ (T : Finset Γ)) := by
    intro z
    by_cases h1 : z ∈ (S : Finset Γ) ∩ (T : Finset Γ)
    · have hf : f z = (e1 ⟨z, h1⟩ : Γ) := by rw [hfdef]; simp only [dif_pos h1]
      have hb := (e1 ⟨z, h1⟩).2
      rw [Finset.mem_inter] at h1 hb
      rw [hf]
      exact ⟨iff_of_true hb.1 h1.1, iff_of_true hb.2 h1.2⟩
    by_cases h2 : z ∈ (S : Finset Γ) \ (T : Finset Γ)
    · have hf : f z = (e2 ⟨z, h2⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1, dif_pos h2]
      have hb := (e2 ⟨z, h2⟩).2
      rw [Finset.mem_sdiff] at h2 hb
      rw [hf]
      exact ⟨iff_of_true hb.1 h2.1, iff_of_false hb.2 h2.2⟩
    by_cases h3 : z ∈ (T : Finset Γ) \ (S : Finset Γ)
    · have hf : f z = (e3 ⟨z, h3⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1, dif_neg h2, dif_pos h3]
      have hb := (e3 ⟨z, h3⟩).2
      rw [Finset.mem_sdiff] at h3 hb
      rw [hf]
      exact ⟨iff_of_false hb.2 h3.2, iff_of_true hb.1 h3.1⟩
    · have hf : ∃ hz, f z = (e4 ⟨z, hz⟩ : Γ) := by
        refine ⟨?_, by rw [hfdef]; simp only [dif_neg h1, dif_neg h2, dif_neg h3]⟩
        simp only [Finset.mem_compl, Finset.mem_union, not_or]
        simp only [Finset.mem_inter, not_and] at h1
        simp only [Finset.mem_sdiff, not_and, not_not] at h2 h3
        exact ⟨fun hzS => h1 hzS (h2 hzS), fun hzT => (h1 (h3 hzT) hzT)⟩
      obtain ⟨hz, hf⟩ := hf
      have hb := (e4 ⟨z, hz⟩).2
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hb
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hz
      rw [hf]
      exact ⟨iff_of_false hb.1 hz.1, iff_of_false hb.2 hz.2⟩
  -- `f` is injective: it is injective on each block, and blocks go to blocks
  have hinj : Function.Injective f := by
    intro z w hzw
    have hSzw : z ∈ (S : Finset Γ) ↔ w ∈ (S : Finset Γ) := by
      rw [← (hmem z).1, ← (hmem w).1, hzw]
    have hTzw : z ∈ (T : Finset Γ) ↔ w ∈ (T : Finset Γ) := by
      rw [← (hmem z).2, ← (hmem w).2, hzw]
    by_cases h1 : z ∈ (S : Finset Γ) ∩ (T : Finset Γ)
    · have h1' : w ∈ (S : Finset Γ) ∩ (T : Finset Γ) := by
        rw [Finset.mem_inter] at h1 ⊢
        exact ⟨hSzw.1 h1.1, hTzw.1 h1.2⟩
      have hz : f z = (e1 ⟨z, h1⟩ : Γ) := by rw [hfdef]; simp only [dif_pos h1]
      have hw : f w = (e1 ⟨w, h1'⟩ : Γ) := by rw [hfdef]; simp only [dif_pos h1']
      rw [hz, hw] at hzw
      exact congrArg Subtype.val (e1.injective (Subtype.ext hzw))
    by_cases h2 : z ∈ (S : Finset Γ) \ (T : Finset Γ)
    · have h1' : w ∉ (S : Finset Γ) ∩ (T : Finset Γ) := by
        rw [Finset.mem_inter] at h1 ⊢
        exact fun hc => h1 ⟨hSzw.2 hc.1, hTzw.2 hc.2⟩
      have h2' : w ∈ (S : Finset Γ) \ (T : Finset Γ) := by
        rw [Finset.mem_sdiff] at h2 ⊢
        exact ⟨hSzw.1 h2.1, fun hc => h2.2 (hTzw.2 hc)⟩
      have hz : f z = (e2 ⟨z, h2⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1, dif_pos h2]
      have hw : f w = (e2 ⟨w, h2'⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1', dif_pos h2']
      rw [hz, hw] at hzw
      exact congrArg Subtype.val (e2.injective (Subtype.ext hzw))
    by_cases h3 : z ∈ (T : Finset Γ) \ (S : Finset Γ)
    · have h1' : w ∉ (S : Finset Γ) ∩ (T : Finset Γ) := by
        rw [Finset.mem_inter] at h1 ⊢
        exact fun hc => h1 ⟨hSzw.2 hc.1, hTzw.2 hc.2⟩
      have h2' : w ∉ (S : Finset Γ) \ (T : Finset Γ) := by
        rw [Finset.mem_sdiff] at h2 ⊢
        exact fun hc => h2 ⟨hSzw.2 hc.1, fun hc' => hc.2 (hTzw.1 hc')⟩
      have h3' : w ∈ (T : Finset Γ) \ (S : Finset Γ) := by
        rw [Finset.mem_sdiff] at h3 ⊢
        exact ⟨hTzw.1 h3.1, fun hc => h3.2 (hSzw.2 hc)⟩
      have hz : f z = (e3 ⟨z, h3⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1, dif_neg h2, dif_pos h3]
      have hw : f w = (e3 ⟨w, h3'⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1', dif_neg h2', dif_pos h3']
      rw [hz, hw] at hzw
      exact congrArg Subtype.val (e3.injective (Subtype.ext hzw))
    · have h1' : w ∉ (S : Finset Γ) ∩ (T : Finset Γ) := by
        rw [Finset.mem_inter] at h1 ⊢
        exact fun hc => h1 ⟨hSzw.2 hc.1, hTzw.2 hc.2⟩
      have h2' : w ∉ (S : Finset Γ) \ (T : Finset Γ) := by
        rw [Finset.mem_sdiff] at h2 ⊢
        exact fun hc => h2 ⟨hSzw.2 hc.1, fun hc' => hc.2 (hTzw.1 hc')⟩
      have h3' : w ∉ (T : Finset Γ) \ (S : Finset Γ) := by
        rw [Finset.mem_sdiff] at h3 ⊢
        exact fun hc => h3 ⟨hTzw.2 hc.1, fun hc' => hc.2 (hSzw.1 hc')⟩
      have hzc : z ∈ ((S : Finset Γ) ∪ (T : Finset Γ))ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_union, not_or]
        simp only [Finset.mem_inter, not_and] at h1
        simp only [Finset.mem_sdiff, not_and, not_not] at h2 h3
        exact ⟨fun hzS => h1 hzS (h2 hzS), fun hzT => (h1 (h3 hzT) hzT)⟩
      have hwc : w ∈ ((S : Finset Γ) ∪ (T : Finset Γ))ᶜ := by
        simp only [Finset.mem_compl, Finset.mem_union, not_or]
        simp only [Finset.mem_inter, not_and] at h1'
        simp only [Finset.mem_sdiff, not_and, not_not] at h2' h3'
        exact ⟨fun hzS => h1' hzS (h2' hzS), fun hzT => (h1' (h3' hzT) hzT)⟩
      have hz : f z = (e4 ⟨z, hzc⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1, dif_neg h2, dif_neg h3]
      have hw : f w = (e4 ⟨w, hwc⟩ : Γ) := by
        rw [hfdef]; simp only [dif_neg h1', dif_neg h2', dif_neg h3']
      rw [hz, hw] at hzw
      exact congrArg Subtype.val (e4.injective (Subtype.ext hzw))
  set π : Equiv.Perm Γ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj) with hπ
  refine ⟨π, ?_, ?_⟩
  · refine Subtype.ext (Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (by rw [S'.2, (tAction t π S).2])))
    intro z hz
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.1 hz
    exact (hmem y).1.2 hyS
  · refine Subtype.ext (Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (by rw [T'.2, (tAction t π T).2])))
    intro z hz
    obtain ⟨y, hyT, rfl⟩ := Finset.mem_image.1 hz
    exact (hmem y).2.2 hyT

/-- Observation 3.2.12.  "The Johnson graphs are distance-transitive and therefore
distance-regular."  "The following is immediate from the trivial direction of
Prop. 3.2.11." -/
theorem johnsonGraph_isDistanceTransitive (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    (johnsonGraph Γ t).IsDistanceTransitive := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- irreflexive: `|S \ S| = 0`
    ext p
    simp only [Set.mem_inter_iff, mem_diag, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hdiag
    have hp' : (((p.1 : binom Γ t) : Finset Γ) \ ((p.2 : binom Γ t) : Finset Γ)).card = 1 := hp
    rw [hdiag, Finset.sdiff_self] at hp'
    simp at hp'
  · -- symmetric: `|S \ T| = |T \ S|` for two `t`-sets
    ext p
    show (((p.1 : binom Γ t) : Finset Γ) \ ((p.2 : binom Γ t) : Finset Γ)).card = 1 ↔
      (((p.2 : binom Γ t) : Finset Γ) \ ((p.1 : binom Γ t) : Finset Γ)).card = 1
    have h1 := Finset.card_inter_add_card_sdiff ((p.1 : binom Γ t) : Finset Γ)
      ((p.2 : binom Γ t) : Finset Γ)
    have h2 := Finset.card_inter_add_card_sdiff ((p.2 : binom Γ t) : Finset Γ)
      ((p.1 : binom Γ t) : Finset Γ)
    rw [Finset.inter_comm] at h2
    have := p.1.2; have := p.2.2
    omega
  · -- connected: there is a walk between any two vertices
    intro S T
    obtain ⟨w, hw, h0, hl⟩ := exists_walk_johnsonGraph t _ S T rfl
    exact Digraph.weaklyAccessible_of_accessible _ ⟨_, w, hw, h0, hl⟩
  · -- distance-transitive, by Obs. 3.2.10 and `exists_perm_map_pair`
    intro S T S' T' hdist
    rw [dist_johnsonGraph t h, dist_johnsonGraph t h] at hdist
    obtain ⟨π, h1, h2⟩ := exists_perm_map_pair S T S' T' hdist
    exact ⟨tAction t π, tAction_mem_aut_johnsonGraph t π, h1, h2⟩

/-- Definition 3.2.13 (Johnson scheme).  "A *Johnson scheme* is the metric scheme
generated by a Johnson graph.  In other words, let `t ≥ 2` and let `Γ` be a set of size
`|Γ| = k ≥ 2t + 1`.  The *Johnson scheme* `J(Γ,t) = (Ω; c)` is an association scheme with
`k choose t` vertices corresponding to the `t`-subsets of a `k`-set `Γ`.  For
`S, T ∈ (Γ choose t)`, the color of the edge `(v_S, v_T)` is `c(v_S, v_T) = |S \ T|`." -/
noncomputable def johnsonScheme (Γ : Type*) [Fintype Γ] [DecidableEq Γ] (t : ℕ) :
    PartitionStructure (binom Γ t) :=
  PartitionStructure.ofColoring (C := ℕ) fun S T => ((S : Finset Γ) \ (T : Finset Γ)).card

/-- Definition 3.2.13.  The Johnson scheme is the metric scheme of the Johnson graph
(Obs. 3.2.10). -/
theorem johnsonScheme_eq_metricScheme (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    johnsonScheme Γ t = metricScheme (johnsonGraph Γ t) := by
  have hcol : (fun S T : binom Γ t => ((S : Finset Γ) \ (T : Finset Γ)).card)
      = fun S T : binom Γ t => (johnsonGraph Γ t).dist S T := by
    funext S T
    exact (dist_johnsonGraph t h S T).symm
  show PartitionStructure.ofColoring (C := ℕ) _ = PartitionStructure.ofColoring (C := ℕ) _
  rw [hcol]

/-- Observation 3.2.14.  "The Johnson schemes are UPCCs." -/
theorem johnsonScheme_isUniprimitive (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    (johnsonScheme Γ t).IsUniprimitive := by
  classical
  obtain ⟨ht, hk⟩ := h
  set G : Subgroup (Equiv.Perm (binom Γ t)) :=
    inducedOnTSets (⊤ : Subgroup (Equiv.Perm Γ)) t with hG
  -- the Johnson scheme is the orbital configuration of `S^(t)(Γ)` (Obs. 3.2.12)
  have hker : ∀ S T S' T' : binom Γ t,
      ((PartitionStructure.orbitalConfig G).color S T
          = (PartitionStructure.orbitalConfig G).color S' T' ↔
        (johnsonScheme Γ t).color S T = (johnsonScheme Γ t).color S' T') := by
    intro S T S' T'
    rw [PartitionStructure.orbitalConfig_color_eq_iff, johnsonScheme,
      PartitionStructure.ofColoring_color_eq_iff]
    constructor
    · rintro ⟨σ, hσ, hσ'⟩
      obtain ⟨π, -, rfl⟩ := Subgroup.mem_map.1 hσ
      obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hσ'
      rw [← h1, ← h2]
      exact card_sdiff_tAction t π S' T'
    · intro hd
      obtain ⟨π, h1, h2⟩ := exists_perm_map_pair S' T' S T hd.symm
      exact ⟨tAction t π, Subgroup.mem_map.2 ⟨π, trivial, rfl⟩, by rw [h1, h2]⟩
  refine PartitionStructure.isUniprimitive_congr hker ?_
  rw [PartitionStructure.orbitalConfig_isUniprimitive_iff]
  refine ⟨isPrimitive_inducedOnTSets_top (by omega) hk, ?_⟩
  -- not doubly transitive: `|S \ T|` is an invariant of a pair, and it takes the values
  -- `1` and `2` (here `t ≥ 2` and `|Γ| ≥ 2t + 1` are used)
  intro hdt
  obtain ⟨S₀, hS₀sub, hS₀⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ : Finset Γ).card by rw [Finset.card_univ]; omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by rw [hS₀]; omega : 1 < S₀.card)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1
    (by rw [Finset.card_compl, hS₀]; omega : 1 < (S₀ᶜ : Finset Γ).card)
  rw [Finset.mem_compl] at ha hb
  -- the three vertices
  have hTcard : (insert a (S₀.erase x)).card = t := by
    rw [Finset.card_insert_of_notMem (fun hc => ha (Finset.mem_of_mem_erase hc)),
      Finset.card_erase_of_mem hx, hS₀]
    omega
  have hUcard : (insert a (insert b ((S₀.erase x).erase y))).card = t := by
    have hy' : y ∈ S₀.erase x := Finset.mem_erase.2 ⟨fun hc => hxy hc.symm, hy⟩
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, not_or]
        exact ⟨hab, fun hc => ha (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))⟩),
      Finset.card_insert_of_notMem (fun hc =>
        hb (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))),
      Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx, hS₀]
    omega
  set S : binom Γ t := ⟨S₀, hS₀⟩ with hS
  set T : binom Γ t := ⟨insert a (S₀.erase x), hTcard⟩ with hT
  set U : binom Γ t := ⟨insert a (insert b ((S₀.erase x).erase y)), hUcard⟩ with hU
  have hST : ((S : Finset Γ) \ (T : Finset Γ)).card = 1 := by
    have : (S : Finset Γ) \ (T : Finset Γ) = {x} := by
      ext z
      simp only [hS, hT, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hzS, hz⟩
        by_contra hzx
        exact hz.2 ⟨hzx, hzS⟩
      · rintro rfl
        exact ⟨hx, fun hc => ha (hc ▸ hx), fun hc => hc.1 rfl⟩
    rw [this, Finset.card_singleton]
  have hSU : ((S : Finset Γ) \ (U : Finset Γ)).card = 2 := by
    have : (S : Finset Γ) \ (U : Finset Γ) = {x, y} := by
      ext z
      simp only [hS, hU, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hzS, hz⟩
        by_contra hzxy
        push_neg at hzxy
        exact hz.2.2 ⟨hzxy.2, hzxy.1, hzS⟩
      · rintro (rfl | rfl)
        · exact ⟨hx, fun hc => ha (hc ▸ hx), fun hc => hb (hc ▸ hx),
            fun hc => hc.2.1 rfl⟩
        · exact ⟨hy, fun hc => ha (hc ▸ hy), fun hc => hb (hc ▸ hy),
            fun hc => hc.1 rfl⟩
    rw [this, Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  -- two pairs that no element of `G` can match up
  have hSTne : S ≠ T := by
    intro hc
    rw [hc] at hST
    simp at hST
  have hSUne : S ≠ U := by
    intro hc
    rw [hc] at hSU
    simp at hSU
  set e1 : Fin 2 ↪ binom Γ t :=
    ⟨![S, T], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩ with he1
  set e2 : Fin 2 ↪ binom Γ t :=
    ⟨![S, U], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩ with he2
  obtain ⟨x₀, hx₀⟩ := hdt
  obtain ⟨g1, hg1⟩ := MulAction.mem_orbit_iff.1 (Set.eq_univ_iff_forall.1 hx₀ e1)
  obtain ⟨g2, hg2⟩ := MulAction.mem_orbit_iff.1 (Set.eq_univ_iff_forall.1 hx₀ e2)
  -- every element of `G` preserves `|A \ B|`
  have key : ∀ (g : G) (A B : binom Γ t),
      (((g • A : binom Γ t) : Finset Γ) \ ((g • B : binom Γ t) : Finset Γ)).card
        = ((A : Finset Γ) \ (B : Finset Γ)).card := by
    intro g A B
    obtain ⟨π, -, hπ⟩ := Subgroup.mem_map.1 g.2
    have h1 : (g : Equiv.Perm (binom Γ t)) = tAction t π := hπ.symm
    show ((((g : Equiv.Perm (binom Γ t)) A : binom Γ t) : Finset Γ) \
      (((g : Equiv.Perm (binom Γ t)) B : binom Γ t) : Finset Γ)).card
      = ((A : Finset Γ) \ (B : Finset Γ)).card
    rw [h1]
    exact card_sdiff_tAction t π A B
  have h10 : (g1 • (x₀ 0) : binom Γ t) = S := by
    have h := congrArg (fun f : Fin 2 ↪ binom Γ t => f 0) hg1
    simpa [he1] using h
  have h11 : (g1 • (x₀ 1) : binom Γ t) = T := by
    have h := congrArg (fun f : Fin 2 ↪ binom Γ t => f 1) hg1
    simpa [he1] using h
  have h20 : (g2 • (x₀ 0) : binom Γ t) = S := by
    have h := congrArg (fun f : Fin 2 ↪ binom Γ t => f 0) hg2
    simpa [he2] using h
  have h21 : (g2 • (x₀ 1) : binom Γ t) = U := by
    have h := congrArg (fun f : Fin 2 ↪ binom Γ t => f 1) hg2
    simpa [he2] using h
  have hk1 := key g1 (x₀ 0) (x₀ 1)
  have hk2 := key g2 (x₀ 0) (x₀ 1)
  rw [h10, h11, hST] at hk1
  rw [h20, h21, hSU] at hk2
  omega

/-! ### §14.1 The automorphism group of a Johnson scheme

Procedure Align (§14.1, line 8) uses the Johnson scheme `J(m,t)` through the map that
undoes `π ↦ π^(t)`: it needs that an automorphism of the scheme comes from exactly one
permutation of `Γ`. -/

/-- The automorphism group of the Johnson *scheme* is the automorphism group of the
Johnson *graph*, namely `S^(t)(Γ)` (Prop. 3.2.11).  The scheme has more colors than the
graph, so its automorphism group is squeezed between `S^(t)(Γ)` and `Aut(J(Γ,t))`. -/
theorem aut_johnsonScheme (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    (johnsonScheme Γ t).Aut = inducedOnTSets (⊤ : Subgroup (Equiv.Perm Γ)) t := by
  refine le_antisymm ?_ ?_
  · -- an automorphism of the scheme preserves `|S \ T|`, hence is one of the graph
    intro σ hσ
    rw [← aut_johnsonGraph t h]
    refine Digraph.mem_aut.2 fun S T => ?_
    have hcard : ((((σ S : binom Γ t) : Finset Γ) \
        ((σ T : binom Γ t) : Finset Γ)).card = ((S : Finset Γ) \ (T : Finset Γ)).card) :=
      (PartitionStructure.ofColoring_color_eq_iff
        (fun S T : binom Γ t => ((S : Finset Γ) \ (T : Finset Γ)).card) _ _ S T).1
        (PartitionStructure.mem_aut.1 hσ S T)
    show ((((σ S : binom Γ t) : Finset Γ) \
      ((σ T : binom Γ t) : Finset Γ)).card = 1) ↔ _
    rw [hcard]
    rfl
  · -- a permutation of `Γ` preserves `|S \ T|`, which is the color
    rintro _ hσ
    obtain ⟨π, -, rfl⟩ := Subgroup.mem_map.1 hσ
    refine PartitionStructure.mem_aut.2 fun S T => ?_
    exact (PartitionStructure.ofColoring_color_eq_iff
      (fun S T : binom Γ t => ((S : Finset Γ) \ (T : Finset Γ)).card) _ _ S T).2
      (card_sdiff_tAction t π S T)

/-- The action on `t`-sets is faithful for `1 ≤ t < |Γ|`: a permutation fixing every
`t`-set is the identity.  (For `t = 0` and for `t = |Γ|` there is only one `t`-set, so the
hypotheses are needed.) -/
theorem tAction_injective {t : ℕ} (ht : 1 ≤ t) (hk : t < Fintype.card Γ) :
    Function.Injective (tAction (Ω := Γ) t) := by
  classical
  rw [injective_iff_map_eq_one]
  intro π hπ
  refine Equiv.ext fun x => ?_
  by_contra hne
  -- a `t`-set containing `x` but not `π x`
  have hcompl : t - 1 ≤ (({x, π x} : Finset Γ)ᶜ).card := by
    have hpair : ({x, π x} : Finset Γ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using fun hc => hne hc.symm),
        Finset.card_singleton]
    rw [Finset.card_compl, hpair]
    omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcompl
  have hxA : x ∉ A := by
    intro hc
    have := hAsub hc
    simp at this
  have hyA : π x ∉ A := by
    intro hc
    have := hAsub hc
    simp at this
  have hScard : (insert x A).card = t := by
    rw [Finset.card_insert_of_notMem hxA, hAcard]
    omega
  have hfix : tAction t π ⟨insert x A, hScard⟩ = ⟨insert x A, hScard⟩ := by
    rw [hπ]; rfl
  have himg : (insert x A).image π = insert x A :=
    congrArg Subtype.val hfix
  have hmem : π x ∈ insert x A := by
    rw [← himg]
    exact Finset.mem_image_of_mem π (Finset.mem_insert_self x A)
  rcases Finset.mem_insert.1 hmem with hc | hc
  · exact hne hc
  · exact hyA hc

/-- §14.1, Procedure Align.  An automorphism of the Johnson scheme `J(Γ,t)` is induced by
exactly one permutation of `Γ`.  Existence is Prop. 3.2.11 and `Babai.aut_johnsonScheme`,
uniqueness is `Babai.tAction_injective`.  So the map `Aut(J(Γ,t)) → S(Γ)` undoing
`π ↦ π^(t)` is well defined and onto. -/
theorem exists_unique_perm_of_mem_aut_johnsonScheme (t : ℕ) (h : IsJohnsonGraphParams Γ t)
    {σ : Equiv.Perm (binom Γ t)} (hσ : σ ∈ (johnsonScheme Γ t).Aut) :
    ∃! π : Equiv.Perm Γ, tAction t π = σ := by
  rw [aut_johnsonScheme t h] at hσ
  obtain ⟨π, -, hπ⟩ := Subgroup.mem_map.1 hσ
  refine ⟨π, hπ, fun π' hπ' => ?_⟩
  exact tAction_injective (by have := h.1; omega) (by have := h.1; have := h.2; omega)
    (hπ'.trans hπ.symm)

/-- §14.1, Procedure Align.  The group isomorphism `S(Γ) ≃ Aut(J(Γ,t))`, `π ↦ π^(t)`.
Its inverse is the map that Procedure Align applies to an automorphism of the Johnson
scheme. -/
noncomputable def permEquivAutJohnsonScheme (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    Equiv.Perm Γ ≃* (johnsonScheme Γ t).Aut :=
  (MonoidHom.ofInjective (tAction_injective (Γ := Γ) (t := t)
      (by have := h.1; omega) (by have := h.1; have := h.2; omega))).trans
    (MulEquiv.subgroupCongr (by
      rw [aut_johnsonScheme t h, inducedOnTSets, ← MonoidHom.range_eq_map]))

@[simp] theorem permEquivAutJohnsonScheme_apply (t : ℕ) (h : IsJohnsonGraphParams Γ t)
    (π : Equiv.Perm Γ) :
    ((permEquivAutJohnsonScheme t h π : (johnsonScheme Γ t).Aut) :
      Equiv.Perm (binom Γ t)) = tAction t π := rfl

/-- Remark 3.2.15 (Degenerate Johnson schemes).  *"We may view the complete graph `K_k` as
a degenerate Johnson graph `J(k,1)`"*: in `J(Γ,1)` two vertices are adjacent exactly when
they are distinct. -/
theorem johnsonGraph_one_adj_iff (S T : binom Γ 1) :
    (johnsonGraph Γ 1).Adj S T ↔ S ≠ T := by
  rw [johnsonGraph_adj_iff]
  have hle : ((S : Finset Γ) \ (T : Finset Γ)).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans S.2.le
  constructor
  · intro h hST
    rw [hST, Finset.sdiff_self, Finset.card_empty] at h
    exact absurd h (by decide)
  · intro hST
    refine le_antisymm hle (Nat.one_le_iff_ne_zero.2 fun h0 => hST ?_)
    have hsub : (S : Finset Γ) ⊆ (T : Finset Γ) :=
      Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 h0)
    exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [S.2, T.2]))

/-- Remark 3.2.15.  *"… and the clique configuration the corresponding degenerate Johnson
scheme `J(k,1)`.  We excluded them from among the Johnson graphs/schemes for the sake of
Obs. 3.2.14."*  The degenerate scheme `J(Γ,1)` has rank at most `2` (the only colors are
`|S \ T| ∈ {0, 1}`), so it is not a UPCC; this is why Obs. 3.2.14
(`johnsonScheme_isUniprimitive`) needs `t ≥ 2`. -/
theorem johnsonScheme_one_not_isUniprimitive :
    ¬ (johnsonScheme Γ 1).IsUniprimitive := by
  rintro ⟨-, h3⟩
  have hsub : (Finset.univ.image fun p : binom Γ 1 × binom Γ 1 =>
      ((p.1 : Finset Γ) \ (p.2 : Finset Γ)).card) ⊆ Finset.range 2 := by
    intro c hc
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hc
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Finset.card_le_card Finset.sdiff_subset).trans p.1.2.le)
  have hrank : (johnsonScheme Γ 1).rank ≤ 2 := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_range] at this
  omega

end Johnson

end Babai
