/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.5: Hypergraphs.
-/
import Workspace.Prelim.BinaryRelations
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# §2.5 Hypergraphs

"A hypergraph `H = (V, E)` consists of a vertex set `V` and a multiset
`E = {E₁,…,E_m}` of hyperedges, where `Eᵢ ⊆ V`."

We record the multiset of hyperedges as an indexed family `edge : Fin m → Finset V`,
which is what the paper uses as well: it speaks of the indices `i ∈ [m]`, of the
multiplicity of a set among the `Eᵢ`, and of the incidence graph on `[m] ∪ V`.

## Numbering map

| Paper | Lean |
|---|---|
| §2.5.1 hypergraph, simple, `d`-uniform, empty, complete, trivial | `Babai.Hypergraph`, `.IsSimple`, `.IsUniform`, `.IsEmptyHg`, `Babai.Hypergraph.completeUniform`, `.IsTrivialUniform` |
| §2.5.1 degree, `r`-regular | `Babai.Hypergraph.degree`, `.IsRegular` |
| §2.5.1 incidence graph | `Babai.Hypergraph.incidenceGraph`, `Babai.Hypergraph.incidence_twins_iff` |
| Definition 2.5.1 | `Babai.Hypergraph.inducedSub` |
| Definition 2.5.2 | `Babai.Hypergraph.trace` |
| Definition 2.5.3 | `Babai.Hypergraph.IsIsoOf`, `Babai.Hypergraph.Aut` |
| §2.5.1 hypergraph as a `d`-ary relational structure | `Babai.Hypergraph.toRelStructureSimple`, `Babai.Hypergraph.toRelStructure`, `Babai.Hypergraph.aut_toRelStructure`, `Babai.Hypergraph.aut_toRelStructureSimple`, `Babai.Hypergraph.defect_toRelStructure` |
| Observation 2.5.4 | `Babai.Hypergraph.incidence_restrict_range`, `Babai.Hypergraph.incidence_restrict_injective_iff_simple` |
| Observation 2.5.5 | `Babai.Hypergraph.isTrivialUniform_iff_aut_top` |
| Definition 2.5.6 | `Babai.Hypergraph.IsTwin`, `Babai.Hypergraph.symmetricity`, `Babai.Hypergraph.defect` |
| Remark 2.5.7 | `Babai.Hypergraph.twins_complete_not_twins_incidence`, `Babai.Hypergraph.no_twins_indices_completeUniform` |
| Observation 2.5.8 | `Babai.Hypergraph.decidableMemAut`; RAM: `Algo.rawHypIsoTest_spec`, `Algo.polyFun_rawHypIsoTest`, `Algo.hypTwinClasses_spec`, `Algo.hypSymDefect_spec`, `Algo.polyFun_hypSymDefect` |
| Definition 2.5.9 | `Babai.Hypergraph.skeleton` |
| Proposition 2.5.10 | `Babai.Hypergraph.exists_nontrivial_skeleton` |
| Proposition 2.5.11 | `Babai.Hypergraph.exists_edge_large_intersection` |
| Lemma 2.5.12 | `Babai.Hypergraph.skeleton_defect` (with `t ≤ ⌈(3/4)d⌉`, see the corrected paper §9.7 Case 3b), `Babai.Hypergraph.skeleton_defect_of_lt`, `Babai.Hypergraph.skeleton_defect_of_le` (the printed hypothesis `t ≤ (3/4)d`) |
-/

namespace Babai

open Equiv Equiv.Perm

variable {V : Type*}

/-- §2.5.1.  "A *hypergraph* `H = (V, E)` consists of a vertex set `V` and a multiset
`E = {E₁,…,E_m}` of hyperedges, where `Eᵢ ⊆ V`." -/
structure Hypergraph (V : Type*) where
  /-- The number `m` of hyperedges (counted with multiplicity). -/
  numEdges : ℕ
  /-- The hyperedges `E₁,…,E_m`. -/
  edge : Fin numEdges → Finset V

namespace Hypergraph

/-- The set of hyperedges of `H`, forgetting multiplicities. -/
def edgeSet (H : Hypergraph V) : Set (Finset V) := Set.range H.edge

/-- §2.5.1.  "If there are no multiple edges (`Eᵢ = Eⱼ ⟹ i = j`) we say that `H` is a
*simple* hypergraph.  In this case `E` can be viewed as a subset of the power-set
of `V`." -/
def IsSimple (H : Hypergraph V) : Prop := Function.Injective H.edge

/-- §2.5.1.  "We say that `H` is *`d`-uniform* if `|Eᵢ| = d` for all `i ≤ m`." -/
def IsUniform (H : Hypergraph V) (d : ℕ) : Prop := ∀ i, (H.edge i).card = d

/-- §2.5.1.  "We say that `H` is an *empty hypergraph* if `E = ∅`." -/
def IsEmptyHg (H : Hypergraph V) : Prop := H.numEdges = 0

/-- §2.5.1.  "The *complete `d`-uniform hypergraph* is the simple hypergraph with edge
set `E = V choose d`." -/
noncomputable def completeUniform (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    Hypergraph V where
  numEdges := Fintype.card (binom V d)
  edge i := ((Fintype.equivFin (binom V d)).symm i : Finset V)

/-- §2.5.1.  "The *trivial* `d`-uniform hypergraphs are the empty and the complete
ones."  We phrase this through the edge set, as the notion is used for simple
hypergraphs. -/
def IsTrivialUniform (H : Hypergraph V) (d : ℕ) : Prop :=
  H.edgeSet = ∅ ∨ H.edgeSet = {F : Finset V | F.card = d}

/-- §2.5.1.  "The *degree* of a vertex `x ∈ V` is the number of indices `i` such that
`x ∈ Eᵢ`." -/
def degree [DecidableEq V] (H : Hypergraph V) (x : V) : ℕ :=
  (Finset.univ.filter fun i => x ∈ H.edge i).card

/-- §2.5.1.  "The hypergraph `H` is *`r`-regular* if every vertex has degree `r`." -/
def IsRegular [DecidableEq V] (H : Hypergraph V) (r : ℕ) : Prop := ∀ x, H.degree x = r

/-- §2.5.1.  "The *incidence graph* of the hypergraph `H` is the bipartite graph
`X(H) = ([m], V; I)` where `I` is the incidence relation: `(i,x) ∈ [m] × V` belongs
to `I` if `x ∈ Eᵢ`." -/
def incidenceGraph (H : Hypergraph V) : BipGraph (Fin H.numEdges) V :=
  ⟨{p | p.2 ∈ H.edge p.1}⟩

/-- §2.5.1.  "Two vertices `i, j ∈ [m]` are twins in `X(H)` exactly if `Eᵢ = Eⱼ`, so there
are no twins in `[m]` with respect to `X(H)` if and only if `H` is simple." -/
theorem incidence_twins_iff [DecidableEq V] (H : Hypergraph V) (i j : Fin H.numEdges)
    (hij : i ≠ j) :
    Babai.IsTwin H.incidenceGraph.Aut (Sum.inl i) (Sum.inl j) ↔ H.edge i = H.edge j := by
  classical
  rw [BipGraph.isTwin_inl_iff_aux H.incidenceGraph i j hij]
  constructor
  · intro h
    ext v
    have := Set.ext_iff.1 h v
    simpa [incidenceGraph] using this
  · intro h
    ext v
    simp only [Set.mem_setOf_eq, incidenceGraph]
    rw [h]

/-- Definition 2.5.1 (Induced subhypergraph).  "For a subset `W ⊆ V` we define the induced
subhypergraph `H[W]` as follows: the vertex set of `H[W]` is `W` and `Eᵢ ∈ E` is an edge
of `H[W]` if and only if `Eᵢ ⊆ W`."

"In particular, every induced subhypergraph of a `d`-uniform hypergraph is
`d`-uniform." -/
noncomputable def inducedSub [DecidableEq V] (H : Hypergraph V) (W : Finset V) :
    Hypergraph W where
  numEdges := (Finset.univ.filter fun i => H.edge i ⊆ W).card
  edge i :=
    let j := (Finset.univ.filter fun i => H.edge i ⊆ W).equivFin.symm i
    (H.edge j.1).subtype (· ∈ W)

/-- Definition 2.5.2 (Trace of hypergraph).  "Let `H = (V, E)` be a hypergraph.  The
*trace* `E_S` on the set `S ⊆ V` is the multiset `{E ∩ S | E ∈ E}`, and the trace of `H`
is `H_S = (S, E_S)`." -/
noncomputable def trace [DecidableEq V] (H : Hypergraph V) (S : Finset V) :
    Hypergraph S where
  numEdges := H.numEdges
  edge i := (H.edge i).subtype (· ∈ S)

/-- Definition 2.5.3 (Isomorphism).  "An isomorphism `H₁ → H₂` is a bijection
`f : V₁ → V₂` such that for every subset `A ⊆ V₁` the multiplicity of `A` in `E₁` is equal
to the multiplicity of `A^f` in `E₂`."

`mult H A` is the multiplicity of `A` among the hyperedges of `H`. -/
def mult [DecidableEq V] (H : Hypergraph V) (A : Finset V) : ℕ :=
  (Finset.univ.filter fun i => H.edge i = A).card

/-- Definition 2.5.3 (Isomorphism). -/
def IsIsoOf {V' : Type*} [DecidableEq V] [DecidableEq V'] (f : V ≃ V')
    (H₁ : Hypergraph V) (H₂ : Hypergraph V') : Prop :=
  ∀ A : Finset V, H₁.mult A = H₂.mult (A.image f)

/-- Definition 2.5.3.  "In particular, `Aut(H) ≤ S(V)`." -/
def Aut [DecidableEq V] (H : Hypergraph V) : Subgroup (Equiv.Perm V) where
  carrier := {σ | ∀ A : Finset V, H.mult (A.image σ) = H.mult A}
  one_mem' := by intro A; simp
  mul_mem' := by
    intro a b ha hb A
    have : A.image ((a * b : Equiv.Perm V) : V → V) = (A.image b).image a := by
      rw [Finset.image_image]; rfl
    rw [this, ha, hb]
  inv_mem' := by
    intro a ha A
    have h2 := ha (A.image ((a⁻¹ : Equiv.Perm V) : V → V))
    rw [Finset.image_image, show ((a : Equiv.Perm V) : V → V) ∘ ((a⁻¹ : Equiv.Perm V) : V → V)
      = id from funext fun x => by simp, Finset.image_id] at h2
    exact h2.symm

instance [DecidableEq V] : IsStructure (Hypergraph V) V := ⟨Hypergraph.Aut⟩

/-! ### §2.5.1: a uniform hypergraph as a `d`-ary relational structure

The paragraph of §2.5.1 that closes the "Basic terminology" subsection:

> "We can treat a simple `d`-uniform hypergraph as a `d`-ary relational structure `(V, R)`
> with a symmetric relation `R ⊆ Ω^d`, i.e. `(∀π ∈ S_d)(R^π = R)`, with the additional
> condition that if `(x₁,…,x_d) ∈ R` then all the `xᵢ` are distinct.
>
> Moreover, if `H` is not simple, we can still treat `H` as a `d`-ary relational structure
> `(V; R₁,…,R_t)` where `Rᵢ` corresponds to the `d`-subsets that occur with multiplicity
> `i` in `E`.
>
> So some results on `d`-ary relational structures apply to `d`-uniform hypergraphs.  We
> shall in particular apply the Design Lemma (Theorem 8.1.2) to uniform hypergraphs."

This is the bridge used in §9.7: Case 3a applies the Design Lemma "to `H`, viewed as a
`d₁`-ary relational structure", and Case 3b applies it to the `t`-skeleton `H^{(t)}`
(which is simple).  What the transfer needs is that the passage to the relational
structure does not change the automorphism group (`aut_toRelStructure`), hence changes
neither the twins nor the symmetry defect (`isTwin_toRelStructure`,
`defect_toRelStructure`). -/

/-- The `d`-subsets occurring with multiplicity `i + 1` in `E`, read as a `d`-ary
relation: the `d`-tuples with pairwise distinct entries whose underlying set has
multiplicity `i + 1`.  (The paper indexes the relations by the multiplicity `i ≥ 1`;
`Fin t` is `0`-based, so the relation with Lean index `i` is the paper's `R_{i+1}`.) -/
def multRel [DecidableEq V] (H : Hypergraph V) (d i : ℕ) : Set (Fin d → V) :=
  {x | Function.Injective x ∧ H.mult (Finset.univ.image x) = i + 1}

/-- §2.5.1.  "If `H` is not simple, we can still treat `H` as a `d`-ary relational
structure `(V; R₁,…,R_t)` where `Rᵢ` corresponds to the `d`-subsets that occur with
multiplicity `i` in `E`."

Here `t` is any bound on the multiplicities of `H` (see `aut_toRelStructure`). -/
def toRelStructure [DecidableEq V] (H : Hypergraph V) (d t : ℕ) : RelStructure V where
  numRel := t
  arity _ := d
  rel i := H.multRel d (i : ℕ)

/-- §2.5.1.  The structure of `toRelStructure` is `d`-ary. -/
theorem isKAry_toRelStructure [DecidableEq V] (H : Hypergraph V) (d t : ℕ) :
    (H.toRelStructure d t).IsKAry d := fun _ => rfl

/-- §2.5.1.  "…with a symmetric relation `R ⊆ Ω^d`, i.e. `(∀π ∈ S_d)(R^π = R)`":
each relation of `toRelStructure` is invariant under permuting the coordinates. -/
theorem multRel_symmetric [DecidableEq V] (H : Hypergraph V) (d i : ℕ)
    (π : Equiv.Perm (Fin d)) (x : Fin d → V) :
    x ∘ π ∈ H.multRel d i ↔ x ∈ H.multRel d i := by
  have himg : Finset.univ.image (x ∘ (π : Fin d → Fin d)) = Finset.univ.image x := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨j, hj⟩ => ⟨π j, hj⟩, fun ⟨j, hj⟩ => ⟨π.symm j, by simpa using hj⟩⟩
  simp only [multRel, Set.mem_setOf_eq, himg]
  constructor
  · rintro ⟨hinj, hm⟩
    refine ⟨fun a b hab => ?_, hm⟩
    have h2 : π.symm a = π.symm b :=
      hinj (show (x ∘ (π : Fin d → Fin d)) (π.symm a) = (x ∘ (π : Fin d → Fin d)) (π.symm b) by
        simpa using hab)
    simpa using h2
  · rintro ⟨hinj, hm⟩
    exact ⟨fun a b hab => π.injective (hinj hab), hm⟩

/-- §2.5.1.  "…with the additional condition that if `(x₁,…,x_d) ∈ R` then all the `xᵢ`
are distinct." -/
theorem injective_of_mem_multRel [DecidableEq V] {H : Hypergraph V} {d i : ℕ}
    {x : Fin d → V} (hx : x ∈ H.multRel d i) : Function.Injective x := hx.1

/-- A `d`-set of a `d`-uniform hypergraph that occurs as a hyperedge has positive
multiplicity, and a set that is not of size `d` has multiplicity `0`. -/
theorem mult_eq_zero_of_card_ne [DecidableEq V] {H : Hypergraph V} {d : ℕ}
    (hu : H.IsUniform d) {A : Finset V} (h : A.card ≠ d) : H.mult A = 0 := by
  rw [mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ hi
  exact h (hi ▸ hu i)

/-- Every `d`-set is the underlying set of an injective `d`-tuple. -/
theorem exists_injective_image [DecidableEq V] {A : Finset V} {d : ℕ} (h : A.card = d) :
    ∃ x : Fin d → V, Function.Injective x ∧ Finset.univ.image x = A := by
  subst h
  refine ⟨fun j => (A.equivFin.symm j : V), ?_, ?_⟩
  · intro a b hab
    exact A.equivFin.symm.injective (Subtype.ext hab)
  · ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨by rintro ⟨j, rfl⟩; exact (A.equivFin.symm j).2,
      fun hv => ⟨A.equivFin ⟨v, hv⟩, by simp⟩⟩

/-- §2.5.1.  Viewing a `d`-uniform hypergraph as a `d`-ary relational structure does not
change its automorphism group.  This is what makes "some results on `d`-ary relational
structures apply to `d`-uniform hypergraphs" (in particular the Design Lemma,
Theorem 8.1.2, as applied in §9.7).

The parameter `t` is any bound on the multiplicities of `H`; for a simple `H` one may
take `t = 1` (see `aut_toRelStructureSimple`). -/
theorem aut_toRelStructure [DecidableEq V] (H : Hypergraph V) {d : ℕ}
    (hu : H.IsUniform d) (t : ℕ) (ht : ∀ A : Finset V, H.mult A ≤ t) :
    (H.toRelStructure d t).Aut = H.Aut := by
  have himg : ∀ (σ : Equiv.Perm V) (x : Fin d → V),
      Finset.univ.image (tupleMap (σ : V → V) x) = (Finset.univ.image x).image σ := by
    intro σ x
    rw [Finset.image_image]
    rfl
  have hinj : ∀ (σ : Equiv.Perm V) (x : Fin d → V),
      Function.Injective (tupleMap (σ : V → V) x) ↔ Function.Injective x := by
    intro σ x
    exact ⟨fun h a b hab => h (by simp [tupleMap, hab]),
      fun h a b hab => h (σ.injective hab)⟩
  ext σ
  simp only [RelStructure.mem_aut_iff, Subgroup.mem_carrier]
  constructor
  · intro h A
    -- the membership test of `Aut(H)` on the single set `A`
    show H.mult (A.image (σ : V → V)) = H.mult A
    have hcardσ : (A.image (σ : V → V)).card = A.card :=
      Finset.card_image_of_injective _ σ.injective
    by_cases hcard : A.card = d
    · obtain ⟨x, hxinj, hxA⟩ := exists_injective_image hcard
      have hspec : ∀ (k : ℕ) (hk : k < t), ∀ y : Fin d → V,
          tupleMap (σ : V → V) y ∈ H.multRel d k ↔ y ∈ H.multRel d k :=
        fun k hk => h ⟨k, hk⟩
      have hstep : ∀ k : ℕ, H.mult A = k + 1 → H.mult (A.image (σ : V → V)) = k + 1 := by
        intro k hk
        have hklt : k < t := by have := ht A; omega
        have hx : x ∈ H.multRel d k := ⟨hxinj, by rw [hxA]; exact hk⟩
        obtain ⟨-, hm⟩ := (hspec k hklt x).2 hx
        rwa [himg, hxA] at hm
      have hstep' : ∀ k : ℕ, H.mult (A.image (σ : V → V)) = k + 1 → H.mult A = k + 1 := by
        intro k hk
        have hklt : k < t := by have := ht (A.image (σ : V → V)); omega
        have hx : tupleMap (σ : V → V) x ∈ H.multRel d k := by
          refine ⟨(hinj σ x).2 hxinj, ?_⟩
          rw [himg, hxA]; exact hk
        obtain ⟨-, hm⟩ := (hspec k hklt x).1 hx
        rwa [hxA] at hm
      rcases Nat.eq_zero_or_pos (H.mult A) with h0 | hpos
      · rcases Nat.eq_zero_or_pos (H.mult (A.image (σ : V → V))) with h0' | hpos'
        · rw [h0, h0']
        · obtain ⟨k, hk⟩ : ∃ k, H.mult (A.image (σ : V → V)) = k + 1 :=
            ⟨H.mult (A.image (σ : V → V)) - 1, by omega⟩
          have := hstep' k hk; omega
      · obtain ⟨k, hk⟩ : ∃ k, H.mult A = k + 1 := ⟨H.mult A - 1, by omega⟩
        rw [hk, hstep k hk]
    · rw [mult_eq_zero_of_card_ne hu hcard,
        mult_eq_zero_of_card_ne hu (by rw [hcardσ]; exact hcard)]
  · intro h i x
    have hmem : ∀ y : Fin d → V, tupleMap (σ : V → V) y ∈ H.multRel d (i : ℕ) ↔
        y ∈ H.multRel d (i : ℕ) := by
      intro y
      simp only [multRel, Set.mem_setOf_eq, himg, hinj]
      rw [show H.mult ((Finset.univ.image y).image (σ : V → V))
        = H.mult (Finset.univ.image y) from h _]
    exact hmem x

/-- §2.5.1.  "We can treat a simple `d`-uniform hypergraph as a `d`-ary relational
structure `(V, R)`": the single relation consists of the `d`-tuples with pairwise
distinct entries whose underlying set is a hyperedge. -/
def toRelStructureSimple [DecidableEq V] (H : Hypergraph V) (d : ℕ) : RelStructure V where
  numRel := 1
  arity _ := d
  rel _ := {x : Fin d → V | Function.Injective x ∧ Finset.univ.image x ∈ H.edgeSet}

/-- For a simple hypergraph a set is a hyperedge exactly if it has multiplicity `1`. -/
theorem mult_eq_one_iff [DecidableEq V] {H : Hypergraph V} (hs : H.IsSimple)
    (A : Finset V) : H.mult A = 1 ↔ A ∈ H.edgeSet := by
  constructor
  · intro h
    have : (Finset.univ.filter fun i => H.edge i = A).Nonempty :=
      Finset.card_pos.1 (by rw [← mult]; omega)
    obtain ⟨i, hi⟩ := this
    exact ⟨i, (Finset.mem_filter.1 hi).2⟩
  · rintro ⟨i, rfl⟩
    rw [mult]
    refine le_antisymm ?_ ?_
    · refine Finset.card_le_one.2 fun a ha b hb => ?_
      exact hs (((Finset.mem_filter.1 ha).2).trans ((Finset.mem_filter.1 hb).2).symm)
    · exact Finset.card_pos.2 ⟨i, by simp⟩

/-- For a simple hypergraph every multiplicity is at most `1`. -/
theorem mult_le_one [DecidableEq V] {H : Hypergraph V} (hs : H.IsSimple) (A : Finset V) :
    H.mult A ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb =>
    hs (((Finset.mem_filter.1 ha).2).trans ((Finset.mem_filter.1 hb).2).symm)

/-- §2.5.1.  For a simple hypergraph the one-relation structure is the case `t = 1` of the
general construction. -/
theorem toRelStructureSimple_eq [DecidableEq V] {H : Hypergraph V} (hs : H.IsSimple)
    (d : ℕ) : H.toRelStructureSimple d = H.toRelStructure d 1 := by
  have : ∀ i : Fin 1, {x : Fin d → V | Function.Injective x ∧
      Finset.univ.image x ∈ H.edgeSet} = H.multRel d (i : ℕ) := by
    intro i
    have hi : (i : ℕ) = 0 := by omega
    ext x
    simp only [multRel, Set.mem_setOf_eq, hi]
    rw [show (0 : ℕ) + 1 = 1 from rfl, mult_eq_one_iff hs]
  simp only [toRelStructureSimple, toRelStructure, RelStructure.mk.injEq, heq_eq_eq,
    true_and]
  exact funext this

/-- §2.5.1.  Viewing a simple `d`-uniform hypergraph as a `d`-ary relational structure
does not change its automorphism group. -/
theorem aut_toRelStructureSimple [DecidableEq V] {H : Hypergraph V} {d : ℕ}
    (hs : H.IsSimple) (hu : H.IsUniform d) :
    (H.toRelStructureSimple d).Aut = H.Aut := by
  rw [toRelStructureSimple_eq hs d]
  exact aut_toRelStructure H hu 1 (mult_le_one hs)


/-- Two finite sets of the same size are carried onto each other by a permutation of the
ambient type. -/
theorem exists_perm_image_eq [DecidableEq V] {A B : Finset V} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm V, A.image σ = B := by
  obtain ⟨x, hx, hxA⟩ := exists_injective_image (A := A) (d := A.card) rfl
  obtain ⟨y, hy, hyB⟩ := exists_injective_image (A := B) (d := A.card) h.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding (⟨x, hx⟩ : Fin A.card ↪ V) ⟨y, hy⟩
  have hσx : ∀ i, σ (x i) = y i := fun i => congrArg (fun f : Fin A.card ↪ V => f i) hσ
  refine ⟨σ, ?_⟩
  rw [← hxA, Finset.image_image, ← hyB]
  exact Finset.image_congr (fun i _ => hσx i)

/-- Two functions from a finite type with the same fibre sizes differ by a permutation of
the domain.  (Used for Observation 2.5.4: an automorphism of `H` permutes the multiset of
hyperedges, hence lifts to a permutation of the edge indices.) -/
private theorem exists_perm_comp {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f g : α → β)
    (h : ∀ b : β, (Finset.univ.filter fun i => f i = b).card
        = (Finset.univ.filter fun i => g i = b).card) :
    ∃ π : Equiv.Perm α, ∀ i, f (π i) = g i := by
  classical
  have hcard : ∀ b : β, Fintype.card {x : α // g x = b} = Fintype.card {x : α // f x = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype, h b]
  have e : ∀ b : β, {x : α // g x = b} ≃ {x : α // f x = b} :=
    fun b => Fintype.equivOfCardEq (hcard b)
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), fun i => ?_⟩
  exact (e (g i) ⟨i, rfl⟩).2

/-- Observation 2.5.4.  Membership of `Aut(X(H))` for a part-preserving permutation
`(π, σ)` of `[m] ⊕ V` says exactly that `π` relabels the hyperedges along `σ`. -/
theorem sumCongr_mem_aut_incidence_iff [DecidableEq V] (H : Hypergraph V)
    (π : Equiv.Perm (Fin H.numEdges)) (σ : Equiv.Perm V) :
    Equiv.sumCongr π σ ∈ BipGraph.Aut H.incidenceGraph ↔
      ∀ i, H.edge (π i) = (H.edge i).image σ := by
  classical
  constructor
  · intro hmem i
    have haut := Digraph.mem_aut.1 hmem
    have hstep : ∀ x : V, σ x ∈ H.edge (π i) ↔ x ∈ H.edge i := by
      intro x
      have h := haut (Sum.inl i) (Sum.inr x)
      simpa [BipGraph.toDigraph, incidenceGraph] using h
    ext v
    simp only [Finset.mem_image]
    constructor
    · intro hv
      exact ⟨σ.symm v, (hstep (σ.symm v)).1 (by simpa using hv), by simp⟩
    · rintro ⟨w, hw, rfl⟩
      exact (hstep w).2 hw
  · intro hedge
    refine Digraph.mem_aut.2 fun u v => ?_
    rcases u with i | x <;> rcases v with j | y
    · simp [BipGraph.toDigraph, incidenceGraph]
    · have h : σ y ∈ H.edge (π i) ↔ y ∈ H.edge i := by
        rw [hedge i]
        simp only [Finset.mem_image]
        exact ⟨by rintro ⟨w, hw, hwy⟩; rwa [σ.injective hwy] at hw, fun hy => ⟨y, hy, rfl⟩⟩
      simpa [BipGraph.toDigraph, incidenceGraph] using h
    · simp [BipGraph.toDigraph, incidenceGraph]
    · simp [BipGraph.toDigraph, incidenceGraph]

/-- Observation 2.5.4.  "Note that `Aut(H)` is the restriction of `Aut(X(H))` to the
set `V`."

A permutation of `V` is an automorphism of `H` exactly if it extends, by some permutation
of the edge indices, to an automorphism of the incidence graph. -/
theorem mem_aut_iff_incidence [DecidableEq V] (H : Hypergraph V) (σ : Equiv.Perm V) :
    σ ∈ H.Aut ↔ ∃ π : Equiv.Perm (Fin H.numEdges),
      Equiv.sumCongr π σ ∈ BipGraph.Aut H.incidenceGraph := by
  classical
  constructor
  · intro hσ
    -- `σ` preserves multiplicities, so the two indexings of the edge multiset by `[m]`
    -- have the same fibres; `exists_perm_comp` turns this into a permutation of `[m]`.
    have hfib : ∀ A : Finset V, (Finset.univ.filter fun i => H.edge i = A).card
        = (Finset.univ.filter fun i => (H.edge i).image (σ : V → V) = A).card := by
      intro A
      have hss : ∀ B : Finset V, (B.image ((σ : Equiv.Perm V) : V → V)).image
          ((σ⁻¹ : Equiv.Perm V) : V → V) = B := by
        intro B
        rw [Finset.image_image, show ((σ⁻¹ : Equiv.Perm V) : V → V) ∘
          ((σ : Equiv.Perm V) : V → V) = id from funext fun x => by simp, Finset.image_id]
      have hss' : ∀ B : Finset V, (B.image ((σ⁻¹ : Equiv.Perm V) : V → V)).image
          ((σ : Equiv.Perm V) : V → V) = B := by
        intro B
        rw [Finset.image_image, show ((σ : Equiv.Perm V) : V → V) ∘
          ((σ⁻¹ : Equiv.Perm V) : V → V) = id from funext fun x => by simp, Finset.image_id]
      have himg : ∀ i, (H.edge i).image (σ : V → V) = A ↔
          H.edge i = A.image ((σ⁻¹ : Equiv.Perm V) : V → V) := by
        intro i
        constructor
        · intro h; rw [← h, hss]
        · intro h; rw [h, hss']
      have h1 : (Finset.univ.filter fun i => (H.edge i).image (σ : V → V) = A)
          = Finset.univ.filter fun i => H.edge i = A.image ((σ⁻¹ : Equiv.Perm V) : V → V) := by
        apply Finset.filter_congr
        intro i _
        simpa using himg i
      rw [h1]
      show H.mult A = H.mult (A.image ((σ⁻¹ : Equiv.Perm V) : V → V))
      have h2 : H.mult ((A.image ((σ⁻¹ : Equiv.Perm V) : V → V)).image (σ : V → V))
          = H.mult (A.image ((σ⁻¹ : Equiv.Perm V) : V → V)) := hσ _
      have h3 : (A.image ((σ⁻¹ : Equiv.Perm V) : V → V)).image (σ : V → V) = A := hss' A
      rw [h3] at h2
      exact h2
    obtain ⟨π, hπ⟩ := exists_perm_comp H.edge (fun i => (H.edge i).image (σ : V → V)) hfib
    exact ⟨π, (H.sumCongr_mem_aut_incidence_iff π σ).2 hπ⟩
  · rintro ⟨π, hπ⟩
    have hedge := (H.sumCongr_mem_aut_incidence_iff π σ).1 hπ
    intro A
    show H.mult (A.image (σ : V → V)) = H.mult A
    rw [mult, mult]
    refine Finset.card_nbij' (fun i => π.symm i) (fun i => π i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have h := hedge (π.symm i)
      rw [Equiv.apply_symm_apply] at h
      exact Finset.image_injective σ.injective (h.symm.trans hi)
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hedge i, hi]
    · intro i _; simp
    · intro i _; simp

/-- Observation 2.5.4.  "This restriction is an isomorphism if and only if `H` is
simple."  The restriction of an automorphism of `X(H)` to `V` determines the permutation
of the edge indices exactly when `H` has no repeated edges. -/
theorem aut_restriction_injective_iff_simple [DecidableEq V] (H : Hypergraph V) :
    (∀ (π π' : Equiv.Perm (Fin H.numEdges)) (σ : Equiv.Perm V),
        Equiv.sumCongr π σ ∈ BipGraph.Aut H.incidenceGraph →
        Equiv.sumCongr π' σ ∈ BipGraph.Aut H.incidenceGraph → π = π') ↔ H.IsSimple := by
  classical
  constructor
  · -- contrapositive: a repeated edge `Eᵢ = Eⱼ` is transposed by an automorphism
    intro h i j hij
    by_contra hne
    have h1 : Equiv.sumCongr (1 : Equiv.Perm (Fin H.numEdges)) (1 : Equiv.Perm V)
        ∈ BipGraph.Aut H.incidenceGraph := by
      refine (H.sumCongr_mem_aut_incidence_iff 1 1).2 fun k => ?_
      simp
    have h2 : Equiv.sumCongr (Equiv.swap i j) (1 : Equiv.Perm V)
        ∈ BipGraph.Aut H.incidenceGraph := by
      refine (H.sumCongr_mem_aut_incidence_iff (Equiv.swap i j) 1).2 fun k => ?_
      simp only [Equiv.Perm.coe_one, Finset.image_id]
      by_cases hk : k = i
      · subst hk; rw [Equiv.swap_apply_left]; exact hij.symm
      by_cases hk' : k = j
      · subst hk'; rw [Equiv.swap_apply_right]; exact hij
      · rw [Equiv.swap_apply_of_ne_of_ne hk hk']
    have heq := h 1 (Equiv.swap i j) 1 h1 h2
    have hi := congrArg (fun f : Equiv.Perm (Fin H.numEdges) => f i) heq
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_left] at hi
    exact hne hi
  · intro hs π π' σ hπ hπ'
    have h1 := (H.sumCongr_mem_aut_incidence_iff π σ).1 hπ
    have h2 := (H.sumCongr_mem_aut_incidence_iff π' σ).1 hπ'
    exact Equiv.ext fun i => hs ((h1 i).trans (h2 i).symm)

/-- Observation 2.5.4. The image of the restriction of the part-preserving
incidence automorphism group to the vertices is exactly `Aut(H)`. -/
theorem incidence_restrict_range [DecidableEq V] (H : Hypergraph V) :
    H.incidenceGraph.restrictPartB.range = H.Aut := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    apply (H.mem_aut_iff_incidence _).2
    refine ⟨(H.incidenceGraph.partAutParts g).1, ?_⟩
    change Equiv.sumCongr (H.incidenceGraph.partAutParts g).1
      (H.incidenceGraph.partAutParts g).2 ∈ H.incidenceGraph.Aut
    rw [BipGraph.partAutParts_spec]
    exact g.property.1
  · intro hσ
    obtain ⟨π, hπ⟩ := (H.mem_aut_iff_incidence σ).1 hσ
    exact ⟨H.incidenceGraph.partAutOfPerms π σ hπ,
      H.incidenceGraph.restrictPartB_ofPerms π σ hπ⟩

/-- Observation 2.5.4. Restriction from the part-preserving incidence
 automorphism group is injective exactly when there are no repeated edges. -/
theorem incidence_restrict_injective_iff_simple [DecidableEq V] (H : Hypergraph V) :
    Function.Injective H.incidenceGraph.restrictPartB ↔ H.IsSimple := by
  rw [← H.aut_restriction_injective_iff_simple]
  constructor
  · intro h π π' σ hπ hπ'
    have heq := h (by simp : H.incidenceGraph.restrictPartB
      (H.incidenceGraph.partAutOfPerms π σ hπ) = H.incidenceGraph.restrictPartB
      (H.incidenceGraph.partAutOfPerms π' σ hπ'))
    have hp := congrArg H.incidenceGraph.partAutParts heq
    simpa using congrArg Prod.fst hp
  · intro h g g' heq
    have hright : (H.incidenceGraph.partAutParts g).2 =
        (H.incidenceGraph.partAutParts g').2 := heq
    have hg : Equiv.sumCongr (H.incidenceGraph.partAutParts g).1
        (H.incidenceGraph.partAutParts g).2 ∈ H.incidenceGraph.Aut := by
      rw [BipGraph.partAutParts_spec]
      exact g.property.1
    have hg' : Equiv.sumCongr (H.incidenceGraph.partAutParts g').1
        (H.incidenceGraph.partAutParts g).2 ∈ H.incidenceGraph.Aut := by
      rw [hright, BipGraph.partAutParts_spec]
      exact g'.property.1
    have hleft := h _ _ _ hg hg'
    apply Subtype.ext
    rw [← H.incidenceGraph.partAutParts_spec g,
      ← H.incidenceGraph.partAutParts_spec g', hleft, hright]

/-- A simple hypergraph with one vertex and one empty edge. Its incidence digraph
has two isolated vertices, so the full automorphism group can exchange the parts. -/
def singleEmptyEdge : Hypergraph (Fin 1) where
  numEdges := 1
  edge := fun _ => ∅

theorem singleEmptyEdge_isSimple : singleEmptyEdge.IsSimple := by
  intro i j _
  change Fin 1 at i j
  exact Subsingleton.elim i j

/-- The exchange of the two isolated vertices belongs only to the full group. -/
theorem singleEmptyEdge_exchangeParts :
    Equiv.sumComm (Fin 1) (Fin 1) ∈ singleEmptyEdge.incidenceGraph.Aut ∧
      Equiv.sumComm (Fin 1) (Fin 1) ∉ singleEmptyEdge.incidenceGraph.PartAut := by
  constructor
  · apply Digraph.mem_aut.2
    intro u v
    change (∃ a b, Equiv.sumComm (Fin 1) (Fin 1) u = Sum.inl a ∧
      Equiv.sumComm (Fin 1) (Fin 1) v = Sum.inr b ∧ b ∈ (∅ : Finset (Fin 1))) ↔
      (∃ a b, u = Sum.inl a ∧ v = Sum.inr b ∧ b ∈ (∅ : Finset (Fin 1)))
    simp
  · rintro ⟨_, ⟨⟨π, σ⟩, h⟩⟩
    have h0 := Equiv.congr_fun h (Sum.inr 0)
    change Sum.inr (σ 0) = Sum.inl (0 : Fin 1) at h0
    cases h0

/-- The part-preserving group can be strictly smaller than the full digraph group. -/
theorem singleEmptyEdge_partAut_lt_aut :
    singleEmptyEdge.incidenceGraph.PartAut < singleEmptyEdge.incidenceGraph.Aut := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  exact singleEmptyEdge_exchangeParts.2 (heq.symm ▸ singleEmptyEdge_exchangeParts.1)

/-- Observation 2.5.5.  "With this definition we note that a simple `d`-uniform hypergraph
`H = (V, E)` is trivial if and only if its automorphism group is `S(V)`." -/
theorem isTrivialUniform_iff_aut_top [Fintype V] [DecidableEq V] {H : Hypergraph V}
    {d : ℕ} (hsimple : H.IsSimple) (huniform : H.IsUniform d) :
    H.IsTrivialUniform d ↔ H.Aut = ⊤ := by
  classical
  constructor
  · intro htriv
    refine (Subgroup.eq_top_iff' _).2 fun σ A => ?_
    show H.mult (A.image (σ : V → V)) = H.mult A
    have hcard : (A.image (σ : V → V)).card = A.card :=
      Finset.card_image_of_injective _ σ.injective
    rcases htriv with hempty | hfull
    · -- no edges at all: every multiplicity is `0`
      have hempty' : IsEmpty (Fin H.numEdges) := Set.range_eq_empty_iff.1 hempty
      have hzero : ∀ B : Finset V, H.mult B = 0 := by
        intro B
        rw [mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun i _ => (hempty'.false i).elim
      rw [hzero, hzero]
    · -- every `d`-set is an edge, and `σ` preserves cardinalities
      have hval : ∀ B : Finset V, H.mult B = if B.card = d then 1 else 0 := by
        intro B
        by_cases hB : B.card = d
        · rw [if_pos hB, mult_eq_one_iff hsimple, hfull]
          exact hB
        · rw [if_neg hB]
          exact mult_eq_zero_of_card_ne huniform hB
      rw [hval, hval, hcard]
  · intro htop
    by_cases hempty : H.edgeSet = ∅
    · exact Or.inl hempty
    refine Or.inr ?_
    obtain ⟨E₀, hE₀⟩ := Set.nonempty_iff_ne_empty.2 hempty
    obtain ⟨i₀, rfl⟩ := hE₀
    ext F
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact huniform i
    · intro hF
      obtain ⟨σ, hσ⟩ := exists_perm_image_eq (A := H.edge i₀) (B := F) (by rw [huniform i₀, hF])
      have hmem : σ ∈ H.Aut := by rw [htop]; trivial
      have h1 : H.mult ((H.edge i₀).image (σ : V → V)) = H.mult (H.edge i₀) := hmem _
      rw [hσ] at h1
      have h2 : H.mult (H.edge i₀) = 1 := (mult_eq_one_iff hsimple _).2 ⟨i₀, rfl⟩
      rw [h2] at h1
      exact (mult_eq_one_iff hsimple F).1 h1

/-- §2.5.1.  The complete `d`-uniform hypergraph is simple. -/
theorem completeUniform_isSimple (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    (completeUniform V d).IsSimple := fun i j h =>
  (Fintype.equivFin (binom V d)).symm.injective (Subtype.ext h)

/-- §2.5.1.  The complete `d`-uniform hypergraph is `d`-uniform. -/
theorem completeUniform_isUniform (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    (completeUniform V d).IsUniform d := fun i => ((Fintype.equivFin (binom V d)).symm i).2

/-- §2.5.1.  "The *complete `d`-uniform hypergraph* is the simple hypergraph with edge
set `E = V choose d`." -/
theorem completeUniform_edgeSet (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    (completeUniform V d).edgeSet = {F : Finset V | F.card = d} := by
  ext F
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Fintype.equivFin (binom V d)).symm i).2
  · intro hF
    exact ⟨Fintype.equivFin (binom V d) ⟨F, hF⟩, by simp [completeUniform]⟩

/-- §2.5.1.  The complete `d`-uniform hypergraph is a trivial `d`-uniform hypergraph. -/
theorem completeUniform_isTrivialUniform (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    (completeUniform V d).IsTrivialUniform d :=
  Or.inr (completeUniform_edgeSet V d)

/-- Observation 2.5.5 for the complete `d`-uniform hypergraph: its automorphism group is
all of `S(V)`. -/
theorem completeUniform_aut_top (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) :
    (completeUniform V d).Aut = ⊤ :=
  (isTrivialUniform_iff_aut_top (completeUniform_isSimple V d)
    (completeUniform_isUniform V d)).1 (completeUniform_isTrivialUniform V d)

/-- Definition 2.5.6 (Twins).  "The definition of twins in a hypergraph is implied by the
definition of automorphisms (see Def. 2.3.16): `x, y ∈ V` (`x ≠ y`) are twins in `H` if
the transposition `τ = (x,y)` is an automorphism of `H`." -/
def IsTwin [DecidableEq V] (H : Hypergraph V) (x y : V) : Prop :=
  Babai.IsTwin H.Aut x y

/-- Definition 2.5.6.  "The *symmetricity* … of `H` [is] defined as the corresponding
parameter of its automorphism group (Def. 2.3.13)." -/
noncomputable def symmetricity [Fintype V] [DecidableEq V] (H : Hypergraph V) : ℕ :=
  Babai.symmetricity H.Aut

/-- Definition 2.5.6.  "The … symmetry defect of `H` [is] defined as the corresponding
parameter of its automorphism group (Def. 2.3.13)." -/
noncomputable def defect [Fintype V] [DecidableEq V] (H : Hypergraph V) : ℚ :=
  Babai.defect H.Aut

/-- §2.5.1.  The twins of a `d`-uniform hypergraph are the twins of the associated
`d`-ary relational structure (Def. 2.5.6 and `aut_toRelStructure`). -/
theorem isTwin_toRelStructure [DecidableEq V] (H : Hypergraph V) {d : ℕ}
    (hu : H.IsUniform d) (t : ℕ) (ht : ∀ A : Finset V, H.mult A ≤ t) (x y : V) :
    Babai.IsTwin (H.toRelStructure d t).Aut x y ↔ H.IsTwin x y := by
  rw [Hypergraph.IsTwin, aut_toRelStructure H hu t ht]

/-- §2.5.1.  The symmetry defect of a `d`-uniform hypergraph is the symmetry defect of the
associated `d`-ary relational structure.  This is what lets §9.7 (Cases 3a and 3b) read
the output of the Design Lemma (Theorem 8.1.2) as information about `H`. -/
theorem defect_toRelStructure [Fintype V] [DecidableEq V] (H : Hypergraph V) {d : ℕ}
    (hu : H.IsUniform d) (t : ℕ) (ht : ∀ A : Finset V, H.mult A ≤ t) :
    Babai.defect (H.toRelStructure d t).Aut = H.defect := by
  rw [Hypergraph.defect, aut_toRelStructure H hu t ht]

/-- Remark 2.5.7.  "Note that twins in `H` are not necessarily twins in the incidence
graph `X(H)`.  For instance, if `H` is the complete `d`-uniform hypergraph where
`1 ≤ d < |V|` then all vertices are twins in `H` but there are no twins in `X(H)`."

The content of the remark is the contrast between the two conjuncts: any two distinct
vertices `x ≠ y` are twins in `H`, yet they are *not* twins in the incidence graph
`X(H)`, because with `1 ≤ d < |V|` some `d`-set contains `x` and not `y`.  The side
conditions are exactly the paper's `1 ≤ d < |V|`: for `d = 0` and for `d = |V|` the
hypergraph has a single edge and the two vertices *are* twins in `X(H)`.

`X(H)` also has no twins among the edge indices, since the complete `d`-uniform
hypergraph is simple; that is `no_twins_indices_completeUniform` below, a corollary of
`incidence_twins_iff`, not the point of the remark. -/
theorem twins_complete_not_twins_incidence [Fintype V] [DecidableEq V] {d : ℕ}
    (hd : 1 ≤ d) (hdV : d < Fintype.card V) :
    (∀ x y : V, x ≠ y → (completeUniform V d).IsTwin x y) ∧
      (∀ x y : V, x ≠ y →
        ¬ Babai.IsTwin (completeUniform V d).incidenceGraph.Aut (Sum.inr x) (Sum.inr y)) := by
  classical
  constructor
  · intro x y hxy
    exact ⟨hxy, by rw [completeUniform_aut_top]; trivial⟩
  · intro x y hxy htwin
    rw [BipGraph.isTwin_inr_iff_aux _ x y hxy] at htwin
    -- a `d`-set containing `x` and avoiding `y` exists because `1 ≤ d < |V|`
    have hcard : ((Finset.univ.erase y).erase x).card = Fintype.card V - 2 := by
      rw [Finset.card_erase_of_mem (by simp [hxy]), Finset.card_erase_of_mem (by simp),
        Finset.card_univ]
      omega
    obtain ⟨t, hts, htc⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ.erase y).erase x) (n := d - 1)
        (by rw [hcard]; omega)
    have hxt : x ∉ t := fun hx => (Finset.mem_erase.1 (hts hx)).1 rfl
    have hyt : y ∉ t := fun hy =>
      (Finset.mem_erase.1 (Finset.mem_of_mem_erase (hts hy))).1 rfl
    set A : Finset V := insert x t with hA
    have hAcard : A.card = d := by
      rw [hA, Finset.card_insert_of_notMem hxt, htc]
      omega
    have hAmem : A ∈ (completeUniform V d).edgeSet := by
      rw [completeUniform_edgeSet]
      exact hAcard
    obtain ⟨i, hi⟩ := hAmem
    have hx : i ∈ {k | (k, x) ∈ (completeUniform V d).incidenceGraph.E} := by
      show x ∈ (completeUniform V d).edge i
      rw [hi, hA]
      exact Finset.mem_insert_self x t
    have hy : i ∉ {k | (k, y) ∈ (completeUniform V d).incidenceGraph.E} := by
      show ¬ y ∈ (completeUniform V d).edge i
      rw [hi, hA, Finset.mem_insert]
      rintro (rfl | hmem)
      · exact hxy rfl
      · exact hyt hmem
    exact hy (htwin ▸ hx)

/-- §2.5.1, applied to the complete `d`-uniform hypergraph of Remark 2.5.7: "there are no
twins in `[m]` with respect to `X(H)` if and only if `H` is simple", and the complete
`d`-uniform hypergraph is simple. -/
theorem no_twins_indices_completeUniform [Fintype V] [DecidableEq V] {d : ℕ}
    (i j : Fin (completeUniform V d).numEdges) (hij : i ≠ j) :
    ¬ Babai.IsTwin (completeUniform V d).incidenceGraph.Aut (Sum.inl i) (Sum.inl j) := by
  intro htwin
  rw [incidence_twins_iff _ i j hij] at htwin
  exact hij (completeUniform_isSimple V d htwin)

/-- Observation 2.5.8.  "Candidate isomorphisms (and therefore automorphisms) of explicit
hypergraphs can be tested in polynomial time (cf. Prop. 2.3.6).  In particular, one can
find the twin equivalence classes of an explicit hypergraph in polynomial time.
Consequently, the symmetry defect of a hypergraph can also be computed in polynomial
time."

The content recorded here is decidability of the test.  On the RAM
(`Workspace/Algo/ExplicitStructures.lean`): the isomorphism test `Algo.rawHypIsoTest_spec`,
`Algo.polyFun_rawHypIsoTest`; the twin classes, symmetricity and symmetry defect
`Algo.hypTwinClasses_spec`, `Algo.hypSymmetricity_spec`, `Algo.hypSymDefect_spec`, with their
`polyFun_` lemmas. -/
instance decidableMemAut [Fintype V] [DecidableEq V] (H : Hypergraph V)
    (σ : Equiv.Perm V) : Decidable (σ ∈ H.Aut) :=
  decidable_of_iff (∀ A : Finset V, H.mult (A.image σ) = H.mult A) Iff.rfl

/-! ### §2.5.3 Skeletons -/

/-- Definition 2.5.9.  "The *`t`-skeleton* of the hypergraph `H = (V, E)` is the
`t`-uniform simple hypergraph `H^(t) = (V, E^(t))` where `F ∈ V choose t` belongs to
`E^(t)` exactly if there exists `E ∈ E` such that `F ⊆ E`." -/
noncomputable def skeleton [Fintype V] [DecidableEq V] (H : Hypergraph V) (t : ℕ) :
    Hypergraph V where
  numEdges := Fintype.card {F : binom V t // ∃ i, (F : Finset V) ⊆ H.edge i}
  edge i :=
    (((Fintype.equivFin {F : binom V t // ∃ i, (F : Finset V) ⊆ H.edge i}).symm i : _) :
      binom V t)

@[simp] theorem mem_skeleton_edgeSet [Fintype V] [DecidableEq V] (H : Hypergraph V)
    (t : ℕ) (F : Finset V) :
    F ∈ (H.skeleton t).edgeSet ↔ F.card = t ∧ ∃ i, F ⊆ H.edge i := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨((Fintype.equivFin _).symm i).1.2, ((Fintype.equivFin _).symm i).2⟩
  · rintro ⟨hcard, hsub⟩
    exact ⟨(Fintype.equivFin _) ⟨⟨F, hcard⟩, hsub⟩, by simp [skeleton]⟩

/-- Proposition 2.5.10.  "Let `H` be a nontrivial `d`-uniform simple hypergraph with `n`
vertices and `m` edges, where `d ≤ n/2`.  Then there exists `t ≤ min{d, 1 + log₂ m}` such
that the `t`-skeleton `H^(t)` is nontrivial."

Paper's proof: choose `t = d` if `d ≤ 1 + log₂ m`, otherwise `t = 1 + ⌊log₂ m⌋`.  For
independently uniformly random vertices `x₁,…,x_t`, the probability that all belong to a
fixed edge `E` is `(|E|/n)^t ≤ 1/2^t`, so the probability that they all belong to some
edge is less than `m/2^t < 1`; hence `H^(t)` is not complete, and it is not empty since
`t ≤ d`. -/
theorem exists_nontrivial_skeleton [Fintype V] [DecidableEq V] {H : Hypergraph V} {d : ℕ}
    (hsimple : H.IsSimple) (huniform : H.IsUniform d) (hnt : ¬ H.IsTrivialUniform d)
    (hd : 2 * d ≤ Fintype.card V) :
    ∃ t : ℕ, (t : ℝ) ≤ min (d : ℝ) (1 + Real.logb 2 H.numEdges) ∧
      ¬ (H.skeleton t).IsTrivialUniform t := by
  classical
  -- `H` has at least one edge, and its edges are nonempty
  have hm : 0 < H.numEdges := by
    rcases Nat.eq_zero_or_pos H.numEdges with h0 | h
    · exfalso
      refine hnt (Or.inl ?_)
      have : IsEmpty (Fin H.numEdges) := by rw [h0]; infer_instance
      rw [edgeSet, Set.range_eq_empty_iff]
      exact this
    · exact h
  set i₀ : Fin H.numEdges := ⟨0, hm⟩ with hi₀
  have hd1 : 1 ≤ d := by
    by_contra hc
    have hd0 : d = 0 := by omega
    refine hnt (Or.inr ?_)
    ext F
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact huniform i
    · intro hF
      have hE : H.edge i₀ = ∅ := Finset.card_eq_zero.1 (by rw [huniform i₀, hd0])
      have hF0 : F = ∅ := Finset.card_eq_zero.1 (by rw [hF, hd0])
      exact ⟨i₀, by rw [hE, hF0]⟩
  by_cases hcase : (d : ℝ) ≤ 1 + Real.logb 2 H.numEdges
  · -- `t = d`: the `d`-skeleton of a `d`-uniform hypergraph is `H` itself
    refine ⟨d, le_min le_rfl hcase, ?_⟩
    have hsk : (H.skeleton d).edgeSet = H.edgeSet := by
      ext F
      rw [mem_skeleton_edgeSet]
      constructor
      · rintro ⟨hcard, i, hsub⟩
        exact ⟨i, (Finset.eq_of_subset_of_card_le hsub (by rw [huniform i, hcard])).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨huniform i, i, subset_rfl⟩
    simpa only [IsTrivialUniform, hsk] using hnt
  · -- `t = 1 + ⌊log₂ m⌋`: fewer than `n^t` tuples lie inside an edge
    push_neg at hcase
    set t : ℕ := Nat.log 2 H.numEdges + 1 with htdef
    have hlog : (Nat.log 2 H.numEdges : ℝ) ≤ Real.logb 2 H.numEdges := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hm), Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have ht1 : (t : ℝ) ≤ 1 + Real.logb 2 H.numEdges := by
      rw [htdef]
      push_cast
      linarith
    have htd : (t : ℝ) ≤ (d : ℝ) := le_of_lt (lt_of_le_of_lt ht1 hcase)
    have htdn : t ≤ d := by exact_mod_cast htd
    refine ⟨t, le_min htd ht1, ?_⟩
    rintro (hempty | hfull)
    · -- a `t`-subset of any edge belongs to the `t`-skeleton
      obtain ⟨F, hFsub, hFcard⟩ :=
        Finset.exists_subset_card_eq (s := H.edge i₀) (n := t) (by rw [huniform i₀]; exact htdn)
      have hmem : F ∈ (H.skeleton t).edgeSet :=
        (mem_skeleton_edgeSet H t F).2 ⟨hFcard, i₀, hFsub⟩
      rw [hempty] at hmem
      exact hmem
    · -- counting: `m d^t < (2d)^t ≤ n^t`, so some `t`-tuple lies in no edge
      set Bad : Finset (Fin t → V) :=
        Finset.univ.biUnion fun i : Fin H.numEdges =>
          Fintype.piFinset fun _ : Fin t => H.edge i with hBad
      have h1 : Bad.card ≤ H.numEdges * d ^ t := by
        refine le_trans Finset.card_biUnion_le ?_
        have hpi : ∀ i : Fin H.numEdges,
            (Fintype.piFinset fun _ : Fin t => H.edge i).card = d ^ t := by
          intro i
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            huniform i]
        rw [Finset.sum_congr rfl (fun i _ => hpi i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      have hdpos : 0 < d ^ t := Nat.pow_pos hd1
      have h2 : H.numEdges * d ^ t < Fintype.card V ^ t := by
        have hmlt : H.numEdges < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) _
        calc H.numEdges * d ^ t < 2 ^ t * d ^ t := by
              exact Nat.mul_lt_mul_of_lt_of_le hmlt le_rfl hdpos
          _ = (2 * d) ^ t := by rw [mul_pow]
          _ ≤ Fintype.card V ^ t := Nat.pow_le_pow_left hd t
      have h3 : (Finset.univ : Finset (Fin t → V)).card = Fintype.card V ^ t := by
        rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      obtain ⟨x, -, hx⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card (s := Bad) (t := (Finset.univ : Finset (Fin t → V)))
          (by omega)
      set S : Finset V := Finset.univ.image x with hS
      have hSsub : ∀ i : Fin H.numEdges, ¬ S ⊆ H.edge i := by
        intro i hsub
        refine hx ?_
        rw [hBad, Finset.mem_biUnion]
        refine ⟨i, Finset.mem_univ _, ?_⟩
        rw [Fintype.mem_piFinset]
        intro j
        exact hsub (by rw [hS]; exact Finset.mem_image_of_mem x (Finset.mem_univ j))
      have hScard : S.card ≤ t := by
        rw [hS]
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_univ, Fintype.card_fin]
      obtain ⟨F, hSF, -, hFcard⟩ :=
        Finset.exists_subsuperset_card_eq (s := S) (t := (Finset.univ : Finset V))
          (Finset.subset_univ _) hScard (by rw [Finset.card_univ]; omega)
      have hFmem : F ∈ (H.skeleton t).edgeSet := by
        rw [hfull]
        exact hFcard
      obtain ⟨-, i, hFsub⟩ := (mem_skeleton_edgeSet H t F).1 hFmem
      exact hSsub i (hSF.trans hFsub)

/-- Double counting of the incidences between a set `T ⊆ V` and the hyperedges:
`∑_i |Eᵢ ∩ T| = ∑_{x ∈ T} deg(x)`.  (Used for Prop. 2.5.11 and Lemma 2.5.12.) -/
theorem sum_card_inter [Fintype V] [DecidableEq V] (H : Hypergraph V) (T : Finset V) :
    (∑ i, ((H.edge i) ∩ T).card) = ∑ x ∈ T, H.degree x := by
  classical
  have h1 : ∀ i : Fin H.numEdges,
      ((H.edge i) ∩ T).card = ∑ x ∈ T, if x ∈ H.edge i then 1 else 0 := by
    intro i
    rw [← Finset.card_filter]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
  have h2 : ∀ x : V, H.degree x = ∑ i : Fin H.numEdges, if x ∈ H.edge i then 1 else 0 := by
    intro x
    rw [degree, ← Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

/-- §2.5.1.  In an `r`-regular `d`-uniform hypergraph, `m d = n r` (both sides count the
incidences).  (Used for Prop. 2.5.11 and Lemma 2.5.12.) -/
theorem numEdges_mul_uniform [Fintype V] [DecidableEq V] {H : Hypergraph V} {d r : ℕ}
    (hreg : H.IsRegular r) (huniform : H.IsUniform d) :
    H.numEdges * d = Fintype.card V * r := by
  classical
  have h1 : (∑ i, ((H.edge i) ∩ Finset.univ).card) = H.numEdges * d := by
    have hval : ∀ i : Fin H.numEdges, ((H.edge i) ∩ Finset.univ).card = d := by
      intro i; rw [Finset.inter_univ]; exact huniform i
    rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have h2 : (∑ x : V, H.degree x) = Fintype.card V * r := by
    rw [Finset.sum_congr rfl (fun x _ => hreg x), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  rw [← h1, H.sum_card_inter Finset.univ, h2]

/-- Proposition 2.5.11.  "Let `H = (V, E)` be a nonempty, regular, `d`-uniform hypergraph.
Let `S ⊆ V`.  Let `α = |S|/|V|`.  Then there is an edge `Eᵢ ∈ E` such that
`|Eᵢ ∩ S| ≥ α d`."

Paper's proof: each vertex belongs to `md/n` edges, so for a random edge the expected
size of `S ∩ Eᵢ` is `|S| d / n = α d`. -/
theorem exists_edge_large_intersection [Fintype V] [DecidableEq V] {H : Hypergraph V}
    {d r : ℕ} (hne : ¬ H.IsEmptyHg) (hreg : H.IsRegular r) (huniform : H.IsUniform d)
    (S : Finset V) :
    ∃ i, ((S.card : ℚ) / (Fintype.card V : ℚ)) * (d : ℚ) ≤ ((H.edge i ∩ S).card : ℚ) := by
  classical
  have hm : 0 < H.numEdges := Nat.pos_of_ne_zero hne
  -- double counting of the incidences between `S` and the hyperedges
  have hcount : ∀ T : Finset V,
      (∑ i, ((H.edge i) ∩ T).card) = ∑ x ∈ T, H.degree x := by
    intro T
    have h1 : ∀ i : Fin H.numEdges,
        ((H.edge i) ∩ T).card = ∑ x ∈ T, if x ∈ H.edge i then 1 else 0 := by
      intro i
      rw [← Finset.card_filter]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
    have h2 : ∀ x : V, H.degree x = ∑ i : Fin H.numEdges, if x ∈ H.edge i then 1 else 0 := by
      intro x
      rw [degree, ← Finset.card_filter]
    simp only [h1, h2]
    exact Finset.sum_comm
  -- `|S| r` incidences with `S`, and `n r = m d` overall
  have hS : (∑ i, ((H.edge i) ∩ S).card) = S.card * r := by
    rw [hcount S, Finset.sum_congr rfl (fun x _ => hreg x), Finset.sum_const, smul_eq_mul]
  have hall : H.numEdges * d = Fintype.card V * r := by
    have h1 : (∑ i, ((H.edge i) ∩ Finset.univ).card) = H.numEdges * d := by
      have : ∀ i : Fin H.numEdges, ((H.edge i) ∩ Finset.univ).card = d := by
        intro i; rw [Finset.inter_univ]; exact huniform i
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have h2 : (∑ x : V, H.degree x) = Fintype.card V * r := by
      rw [Finset.sum_congr rfl (fun x _ => hreg x), Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
    rw [← h1, hcount Finset.univ, h2]
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hn0 | hn
  · -- an empty vertex set: `S = ∅` and the left-hand side is `0`
    have hS0 : S.card = 0 := by
      have := Finset.card_le_univ S
      simp only [Finset.card_univ] at this
      omega
    exact ⟨⟨0, hm⟩, by rw [hS0]; simp⟩
  · have hnq : (0 : ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast hn
    have hmq : (0 : ℚ) < (H.numEdges : ℚ) := by exact_mod_cast hm
    refine Finset.exists_le_of_sum_le (f := fun _ : Fin H.numEdges =>
      ((S.card : ℚ) / (Fintype.card V : ℚ)) * (d : ℚ))
      (g := fun i => (((H.edge i) ∩ S).card : ℚ)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ ?_ |>.imp
      fun i hi => hi.2
    have hsumq : (∑ i, (((H.edge i) ∩ S).card : ℚ)) = (S.card : ℚ) * (r : ℚ) := by
      rw [← Nat.cast_sum, hS]
      push_cast
      ring
    have hallq : (H.numEdges : ℚ) * (d : ℚ) = (Fintype.card V : ℚ) * (r : ℚ) := by
      exact_mod_cast hall
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsumq]
    rw [div_mul_eq_mul_div, mul_div_assoc']
    rw [div_le_iff₀ hnq]
    nlinarith [hallq]

/-- Definition 2.5.9.  The `t`-skeleton is a simple hypergraph (its edges are indexed by
the *set* of `t`-subsets contained in an edge). -/
theorem skeleton_isSimple [Fintype V] [DecidableEq V] (H : Hypergraph V) (t : ℕ) :
    (H.skeleton t).IsSimple := fun i j h =>
  (Fintype.equivFin _).symm.injective (Subtype.ext (Subtype.ext h))

/-- Auxiliary for Lemma 2.5.12: two subsets of `S` of the same size are carried onto each
other by a permutation of `V` that fixes `V ∖ S` pointwise, i.e. by an element of `S(S)`
(Convention 2.3.8). -/
theorem exists_symOn_image_eq [DecidableEq V] {S T₀ T : Finset V}
    (h₀ : T₀ ⊆ S) (h : T ⊆ S) (hcard : T₀.card = T.card) :
    ∃ σ ∈ symOn (↑S : Set V), T₀.image ((σ : Equiv.Perm V) : V → V) = T := by
  classical
  have hA : (T₀.subtype (· ∈ S)).card = (T.subtype (· ∈ S)).card := by
    rw [Finset.card_subtype, Finset.card_subtype,
      Finset.filter_true_of_mem (fun x hx => h₀ hx),
      Finset.filter_true_of_mem (fun x hx => h hx)]
    exact hcard
  obtain ⟨f, hf⟩ := exists_perm_image_eq hA
  refine ⟨Equiv.Perm.ofSubtype f, ?_, ?_⟩
  · intro x hx
    exact Equiv.Perm.ofSubtype_apply_of_not_mem f (by simpa using hx)
  · have hsub : T₀.image ((Equiv.Perm.ofSubtype f : Equiv.Perm V) : V → V) ⊆ T := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      have hxS : x ∈ S := h₀ hx
      rw [Equiv.Perm.ofSubtype_apply_of_mem f hxS]
      have hmem : (⟨x, hxS⟩ : {a : V // a ∈ S}) ∈ T₀.subtype (· ∈ S) :=
        Finset.mem_subtype.2 hx
      have him : f ⟨x, hxS⟩ ∈ T.subtype (· ∈ S) := by
        rw [← hf]
        exact Finset.mem_image_of_mem f hmem
      exact Finset.mem_subtype.1 him
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective _ (Equiv.injective _)]
    exact le_of_eq hcard.symm

/-- Auxiliary for Lemma 2.5.12, Eq. (15): for `d ≤ s` we have
`binom(s,t)/binom(d,t) ≥ (s/d)^t`, in cross-multiplied form.  Each of the `t` factors
`(s-j)/(d-j)` of the quotient is at least `s/d`. -/
theorem pow_mul_choose_le (s d t : ℕ) (hds : d ≤ s) :
    s ^ t * d.choose t ≤ d ^ t * s.choose t := by
  have hfac : 0 < Nat.factorial t := Nat.factorial_pos t
  have key : Nat.factorial t * (s ^ t * d.choose t) ≤ Nat.factorial t * (d ^ t * s.choose t) := by
    have e1 : Nat.factorial t * (s ^ t * d.choose t) = s ^ t * (Nat.factorial t * d.choose t) := by ring
    have e2 : Nat.factorial t * (d ^ t * s.choose t) = d ^ t * (Nat.factorial t * s.choose t) := by ring
    rw [e1, e2, ← Nat.descFactorial_eq_factorial_mul_choose,
      ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
      show s ^ t = ∏ _j ∈ Finset.range t, s by simp,
      show d ^ t = ∏ _j ∈ Finset.range t, d by simp,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' ?_
    intro j _
    rcases le_or_gt d j with hj | hj
    · simp [Nat.sub_eq_zero_of_le hj]
    · have h1 : d - j ≤ s - j := Nat.sub_le_sub_right hds j
      have h2 : s = j + (s - j) := by omega
      have h3 : d = j + (d - j) := by omega
      calc s * (d - j) = (j + (s - j)) * (d - j) := by rw [← h2]
        _ = j * (d - j) + (s - j) * (d - j) := by ring
        _ ≤ j * (s - j) + (d - j) * (s - j) :=
            Nat.add_le_add (Nat.mul_le_mul_left j h1) (le_of_eq (Nat.mul_comm _ _))
        _ = (j + (d - j)) * (s - j) := by ring
        _ = d * (s - j) := by rw [← h3]
  exact Nat.le_of_mul_le_mul_left key hfac

/-- Lemma 2.5.12 (Skeleton defect lemma).  "Let `H = (V, E)` be a nontrivial, regular,
`d`-uniform simple hypergraph with `n` vertices and `m` edges where `d ≤ n/2`.  Let
`(7/4) log₂ m ≤ t ≤ (3/4) d`.  Then the symmetry defect of the `t`-skeleton `H^(t)` is
greater than `1/4`."

The upper bound on `t` is stated here in the slightly more general form
`t ≤ ⌈(3/4) d⌉`; the printed hypothesis is the corollary
`Babai.Hypergraph.skeleton_defect_of_le`.  The generalization is free: the proof uses the
upper bound only to choose a `t`-subset of `S ∩ E` where `|S ∩ E| ≥ (3/4) d`, and `|S ∩ E|`
is an integer, so `|S ∩ E| ≥ ⌈(3/4) d⌉ ≥ t`.  It is what §9.7, Case 3b needs: there
`t = ⌈(7/4) log₂ n₁⌉` and only `(7/4) log₂ n₁ < (3/4) d₁` is available, which gives
`t ≤ ⌈(3/4) d₁⌉` but not `t ≤ (3/4) d₁` (see the corrected paper entry on §9.7 Case 3b).

Paper's proof: let `S` be a set of twins in `H` and suppose `|S| ≥ 3n/4`.  By
Prop. 2.5.11 there is an edge `E` with `|S ∩ E| ≥ (3/4)d ≥ t`; a `t`-subset `T ⊆ S ∩ E`
lies in `E^(t)`, and since `S` is a set of twins, all of `S choose t` lies in `E^(t)`.
Every edge of `H` contains at most `d choose t` of these `t`-sets, so
`m ≥ binom(|S|,t)/binom(d,t) > (3n/(4d))^t ≥ (3/2)^t > m`, Eq. (15), a contradiction.

Reading of the paper's proof: the proof must start from a
set `S` of twins **of `H^{(t)}`**, not of `H`.  The conclusion bounds the symmetry defect
of `H^{(t)}`, so the set to be bounded is a twin set of `H^{(t)}`; and the only place `S`
is used as a set of twins is the step `binom(S,t) ⊆ E^{(t)}`, which needs
`S(S) ≤ Aut(H^{(t)})` (Obs. 2.3.12).  Since `Aut(H) ≤ Aut(H^{(t)})`, a twin set of `H` is
a twin set of `H^{(t)}`, so the paper's phrasing is the weaker special case and the rest
of the argument goes through verbatim. -/
theorem skeleton_defect [Fintype V] [DecidableEq V] {H : Hypergraph V} {d r t : ℕ}
    (hsimple : H.IsSimple) (hnt : ¬ H.IsTrivialUniform d) (hreg : H.IsRegular r)
    (huniform : H.IsUniform d) (hd : 2 * d ≤ Fintype.card V)
    (ht₁ : (7 / 4 : ℝ) * Real.logb 2 H.numEdges ≤ t) (ht₂ : t ≤ ⌈(3 / 4 : ℝ) * d⌉₊) :
    1 / 4 < (H.skeleton t).defect := by
  classical
  -- `H` has an edge, its edges are nonempty, and (regularity) it has at least two of them
  have hm : 0 < H.numEdges := by
    rcases Nat.eq_zero_or_pos H.numEdges with h0 | h
    · exfalso
      refine hnt (Or.inl ?_)
      have hemp : IsEmpty (Fin H.numEdges) := by rw [h0]; infer_instance
      rw [edgeSet, Set.range_eq_empty_iff]
      exact hemp
    · exact h
  set i₀ : Fin H.numEdges := ⟨0, hm⟩ with hi₀
  have hd1 : 1 ≤ d := by
    by_contra hc
    have hd0 : d = 0 := by omega
    refine hnt (Or.inr ?_)
    ext F
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact huniform i
    · intro hF
      have hE : H.edge i₀ = ∅ := Finset.card_eq_zero.1 (by rw [huniform i₀, hd0])
      have hF0 : F = ∅ := Finset.card_eq_zero.1 (by rw [hF, hd0])
      exact ⟨i₀, by rw [hE, hF0]⟩
  have hn : 0 < Fintype.card V := by omega
  have hr1 : 1 ≤ r := by
    obtain ⟨x, hx⟩ : (H.edge i₀).Nonempty := Finset.card_pos.1 (by rw [huniform i₀]; omega)
    have hdx : 1 ≤ H.degree x := by
      rw [degree]
      exact Finset.card_pos.2 ⟨i₀, by simp [hx]⟩
    rwa [hreg x] at hdx
  have hm2 : 2 ≤ H.numEdges := by
    have hid := numEdges_mul_uniform hreg huniform
    have h1 : 2 * d ≤ H.numEdges * d :=
      calc 2 * d ≤ Fintype.card V := hd
        _ ≤ Fintype.card V * r := Nat.le_mul_of_pos_right _ hr1
        _ = H.numEdges * d := hid.symm
    exact Nat.le_of_mul_le_mul_right h1 hd1
  -- the two hypotheses on `t`, in arithmetic form.  `t ≤ ⌈(3/4)d⌉` says `t - 1 < (3/4)d`.
  have h4t3d : 4 * t < 3 * d + 4 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · omega
    · have h1 : t - 1 < ⌈(3 / 4 : ℝ) * d⌉₊ := by omega
      have h2 : ((t - 1 : ℕ) : ℝ) < (3 / 4 : ℝ) * d := Nat.lt_ceil.1 h1
      have h3 : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht0]; norm_num
      rw [h3] at h2
      have h4 : (4 * t : ℝ) < 3 * d + 4 := by linarith
      exact_mod_cast h4
  have htd : t ≤ d := by omega
  have hlogm : (1 : ℝ) ≤ Real.logb 2 (H.numEdges : ℝ) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hm), Real.rpow_one]
    exact_mod_cast hm2
  have ht1 : 1 ≤ t := by
    have h1 : (1 : ℝ) ≤ (t : ℝ) := by linarith
    exact_mod_cast h1
  -- Eq. (15): `t ≥ (7/4) log₂ m` gives `m^7 ≤ 2^{4t}`
  have hm7 : H.numEdges ^ 7 ≤ 2 ^ (4 * t) := by
    have hlog : Real.logb 2 ((H.numEdges : ℝ) ^ 7) ≤ ((4 * t : ℕ) : ℝ) := by
      rw [Real.logb_pow]
      push_cast
      linarith
    have hle := (Real.logb_le_iff_le_rpow one_lt_two
      (by positivity : (0 : ℝ) < (H.numEdges : ℝ) ^ 7)).1 hlog
    rw [Real.rpow_natCast] at hle
    exact_mod_cast hle
  -- the core claim: every set of twins of `H^{(t)}` has fewer than `3n/4` elements
  have hclaim : ∀ Ψ : Finset V, IsTwinSet (H.skeleton t).Aut (↑Ψ : Set V) →
      4 * Ψ.card < 3 * Fintype.card V := by
    intro Ψ hΨ
    by_contra hcon
    push_neg at hcon
    set s := Ψ.card with hs
    have hds : d ≤ s := by omega
    -- (a) Prop. 2.5.11: some edge meets `Ψ` in at least `(3/4)d ≥ t` points
    obtain ⟨i, hi⟩ := exists_edge_large_intersection (H := H) (d := d) (r := r)
      (by intro h; rw [IsEmptyHg] at h; omega) hreg huniform Ψ
    have hti : t ≤ (H.edge i ∩ Ψ).card := by
      have hnq : (0 : ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast hn
      have h1 : (3 : ℚ) * (Fintype.card V : ℚ) ≤ 4 * (s : ℚ) := by exact_mod_cast hcon
      have hdq : (0 : ℚ) ≤ (d : ℚ) := by positivity
      -- `(3/4)d ≤ (s/n)d ≤ |E ∩ Ψ|`, and `|E ∩ Ψ|` is an integer, so `⌈(3/4)d⌉ ≤ |E ∩ Ψ|`
      have h3 : (3 / 4 : ℚ) * (d : ℚ) ≤ ((s : ℚ) / (Fintype.card V : ℚ)) * (d : ℚ) := by
        refine mul_le_mul_of_nonneg_right ?_ hdq
        rw [le_div_iff₀ hnq]; linarith
      have h4 : (3 : ℚ) * (d : ℚ) ≤ 4 * ((H.edge i ∩ Ψ).card : ℚ) := by
        linarith [le_trans h3 hi]
      have h5 : 3 * d ≤ 4 * (H.edge i ∩ Ψ).card := by exact_mod_cast h4
      omega
    obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq hti
    have hT₀mem : T₀ ∈ (H.skeleton t).edgeSet :=
      (mem_skeleton_edgeSet H t T₀).2
        ⟨hT₀card, i, hT₀sub.trans Finset.inter_subset_left⟩
    -- (b) `S(Ψ) ≤ Aut(H^{(t)})` carries `T₀` to every `t`-subset of `Ψ`
    have hskel : ∀ T : Finset V, T ⊆ Ψ → T.card = t → T ∈ (H.skeleton t).edgeSet := by
      intro T hTΨ hTcard
      obtain ⟨σ, hσmem, hσimg⟩ := exists_symOn_image_eq (S := Ψ) (T₀ := T₀) (T := T)
        (hT₀sub.trans Finset.inter_subset_right) hTΨ (by rw [hT₀card, hTcard])
      have hσaut : σ ∈ (H.skeleton t).Aut :=
        (isTwinSet_iff_symOn_le _ _).1 hΨ hσmem
      have h1 : (H.skeleton t).mult (T₀.image ((σ : Equiv.Perm V) : V → V))
          = (H.skeleton t).mult T₀ := hσaut _
      rw [hσimg, (mult_eq_one_iff (skeleton_isSimple H t) T₀).2 hT₀mem] at h1
      exact (mult_eq_one_iff (skeleton_isSimple H t) T).1 h1
    -- (c) every edge of `H` contains at most `binom(d,t)` of the `t`-subsets of `Ψ`
    have hsub : Ψ.powersetCard t ⊆
        Finset.univ.biUnion fun j : Fin H.numEdges => (H.edge j).powersetCard t := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨-, j, hj⟩ := (mem_skeleton_edgeSet H t T).1 (hskel T hT.1 hT.2)
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_powersetCard.2 ⟨hj, hT.2⟩⟩
    have hcount : s.choose t ≤ H.numEdges * d.choose t := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_powersetCard, ← hs] at h1
      refine le_trans h1 (le_trans Finset.card_biUnion_le ?_)
      have hval : ∀ j : Fin H.numEdges, ((H.edge j).powersetCard t).card = d.choose t := by
        intro j; rw [Finset.card_powersetCard, huniform j]
      rw [Finset.sum_congr rfl (fun j _ => hval j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    -- (d) Eq. (15): `(3/2)^t ≤ binom(s,t)/binom(d,t) ≤ m`, contradicting `m^7 ≤ 2^{4t}`
    have hchoose : 0 < d.choose t := Nat.choose_pos htd
    have hstep2 : s ^ t ≤ H.numEdges * d ^ t := by
      have h1 : s ^ t * d.choose t ≤ (H.numEdges * d ^ t) * d.choose t :=
        calc s ^ t * d.choose t ≤ d ^ t * s.choose t := pow_mul_choose_le s d t hds
          _ ≤ d ^ t * (H.numEdges * d.choose t) := Nat.mul_le_mul_left _ hcount
          _ = (H.numEdges * d ^ t) * d.choose t := by ring
      exact Nat.le_of_mul_le_mul_right h1 hchoose
    have hdt : 0 < d ^ t := Nat.pow_pos hd1
    have hstep4 : 3 ^ t ≤ 2 ^ t * H.numEdges := by
      have h1 : 3 ^ t * d ^ t ≤ (2 ^ t * H.numEdges) * d ^ t :=
        calc 3 ^ t * d ^ t = (3 * d) ^ t := (mul_pow 3 d t).symm
          _ ≤ (2 * s) ^ t := Nat.pow_le_pow_left (by omega) t
          _ = 2 ^ t * s ^ t := mul_pow 2 s t
          _ ≤ 2 ^ t * (H.numEdges * d ^ t) := Nat.mul_le_mul_left _ hstep2
          _ = (2 ^ t * H.numEdges) * d ^ t := by ring
      exact Nat.le_of_mul_le_mul_right h1 hdt
    have hfinal : (2 ^ t * H.numEdges) ^ 7 < (3 ^ t) ^ 7 :=
      calc (2 ^ t * H.numEdges) ^ 7 = 2 ^ (7 * t) * H.numEdges ^ 7 := by
            rw [mul_pow, ← pow_mul, mul_comm t 7]
        _ ≤ 2 ^ (7 * t) * 2 ^ (4 * t) := Nat.mul_le_mul_left _ hm7
        _ = 2048 ^ t := by rw [← pow_add, show 7 * t + 4 * t = 11 * t by ring,
              pow_mul, show (2:ℕ) ^ 11 = 2048 by norm_num]
        _ < 2187 ^ t := Nat.pow_lt_pow_left (by norm_num) (by omega)
        _ = (3 ^ t) ^ 7 := by
            rw [← pow_mul, mul_comm t 7, pow_mul, show (3:ℕ) ^ 7 = 2187 by norm_num]
    have hmono := Nat.pow_le_pow_left hstep4 7
    omega
  -- the claim bounds the symmetricity, hence the symmetry defect
  have hsym : 4 * Babai.symmetricity (H.skeleton t).Aut < 3 * Fintype.card V := by
    have hle : Babai.symmetricity (H.skeleton t).Aut ≤ (3 * Fintype.card V - 1) / 4 :=
      symmetricity_le (fun Ψ hΨ => by have := hclaim Ψ hΨ; omega)
    omega
  have hnq : (0 : ℚ) < (Fintype.card V : ℚ) := by exact_mod_cast hn
  have hsymq : 4 * (Babai.symmetricity (H.skeleton t).Aut : ℚ) < 3 * (Fintype.card V : ℚ) := by
    exact_mod_cast hsym
  rw [Hypergraph.defect, Babai.defect, Babai.relSymmetricity]
  rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hnq]
  linarith

/-- Lemma 2.5.12 (Skeleton defect lemma), with the upper bound on `t` in its equivalent
natural-number form `4(t-1) < 3d`.  See `Babai.Hypergraph.skeleton_defect`. -/
theorem skeleton_defect_of_lt [Fintype V] [DecidableEq V] {H : Hypergraph V} {d r t : ℕ}
    (hsimple : H.IsSimple) (hnt : ¬ H.IsTrivialUniform d) (hreg : H.IsRegular r)
    (huniform : H.IsUniform d) (hd : 2 * d ≤ Fintype.card V)
    (ht₁ : (7 / 4 : ℝ) * Real.logb 2 H.numEdges ≤ t) (ht₂ : 4 * t < 3 * d + 4) :
    1 / 4 < (H.skeleton t).defect := by
  refine skeleton_defect hsimple hnt hreg huniform hd ht₁ ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · exact Nat.zero_le _
  · have h1 : ((t - 1 : ℕ) : ℝ) < (3 / 4 : ℝ) * d := by
      rw [Nat.cast_sub ht0]
      have : (4 * t : ℝ) < 3 * d + 4 := by exact_mod_cast ht₂
      push_cast
      linarith
    have := Nat.lt_ceil.2 h1
    omega

/-- Lemma 2.5.12 (Skeleton defect lemma), §2.5.4, exactly as printed: "Let `H = (V, E)` be
a nontrivial, regular, `d`-uniform simple hypergraph with `n` vertices and `m` edges where
`d ≤ n/2`.  Let `(7/4) log₂ m ≤ t ≤ (3/4) d`.  Then the symmetry defect of the
`t`-skeleton `H^(t)` is greater than `1/4`."

A corollary of `Babai.Hypergraph.skeleton_defect`, which asks only `t ≤ ⌈(3/4) d⌉`. -/
theorem skeleton_defect_of_le [Fintype V] [DecidableEq V] {H : Hypergraph V} {d r t : ℕ}
    (hsimple : H.IsSimple) (hnt : ¬ H.IsTrivialUniform d) (hreg : H.IsRegular r)
    (huniform : H.IsUniform d) (hd : 2 * d ≤ Fintype.card V)
    (ht₁ : (7 / 4 : ℝ) * Real.logb 2 H.numEdges ≤ t) (ht₂ : (t : ℝ) ≤ (3 / 4 : ℝ) * d) :
    1 / 4 < (H.skeleton t).defect := by
  refine skeleton_defect hsimple hnt hreg huniform hd ht₁ ?_
  exact_mod_cast le_trans ht₂ (Nat.le_ceil ((3 / 4 : ℝ) * d))

end Hypergraph

end Babai
