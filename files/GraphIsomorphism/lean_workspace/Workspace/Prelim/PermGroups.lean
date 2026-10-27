/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.1 (Fraktur) and Section 2.2 (Permutation groups).
-/
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Workspace.Prelim.SchreierHypothesis

/-!
# §2.2 Permutation groups

This file formalizes the notation, terminology and results of Section 2.2 of the paper.

## Left versus right actions

The paper acts on the **right**: it writes `x^σ` for the image of `x` under `σ`, and
`x^(στ) = (x^σ)^τ`.  Mathlib acts on the **left**: `σ • x = σ x` and `(σ * τ) x = σ (τ x)`.

Our uniform translation is:

* the paper's `x^σ` is Lean's `σ • x` (that is, `σ x`);
* consequently the paper's product `στ` ("first `σ`, then `τ`") is Lean's `τ * σ`.

The map `σ ↦ σ⁻¹` is an isomorphism between `S(Ω)` with the paper's multiplication and
`Equiv.Perm Ω` with Lean's multiplication, and it is the identity on subsets that are
subgroups.  Every notion of §2.2 (subgroup, index, orbit, stabilizer, invariant set,
block, primitivity, support, degree of transitivity) is invariant under this
anti-isomorphism, so no statement of the paper changes meaning under the translation.
The paper's "representation" `ϕ : G → S(Ω)` (a homomorphism for the paper's product) is
Lean's `ϕ : G →* Equiv.Perm Ω`.

**Warning: the translation swaps left and right cosets.**  Because the paper's product
`στ` is Lean's `τ * σ`, the paper's *left* coset `σN = {στ | τ ∈ N}` is Lean's *right*
coset `N * σ`, and the paper's right coset `Nσ` is Lean's left coset `σ * N`.  For a
normal subgroup the two coincide, so nothing changes for kernels (Proposition 2.2.6 (b),
`Babai.preimage_eq_coset_of_nonempty`).  From Sec. 11 on the paper also uses cosets of
**non-normal** subgroups (for instance `Iso(x,y)` as a coset of `Aut(x)`), and there the
side has to be flipped when a statement is transcribed.

## Numbering map

| Paper | Lean |
|---|---|
| §2.2.1 `S(Ω)`, `A(Ω)` | `Equiv.Perm Ω` (as `⊤`), `alternatingGroup Ω` |
| §2.2.1 giants | `Babai.IsGiant` |
| §2.2.1 giant representation | `Babai.IsGiantRep` |
| §2.2.1 `G`-invariant set | `Babai.IsInvariant` |
| Notation 2.2.1 `G^Δ` | `Babai.restrictTo` |
| §2.2.1 `G^ϕ ≅ G/ker ϕ` | `Babai.quotientKerEquivRange` |
| §2.2.1 stabilizer, orbit, Eq. (10) | `MulAction.stabilizer`, `MulAction.orbit`, `Babai.card_orbit_eq_index` |
| §2.2.1 "the orbits partition `Ω`" | `Babai.isInvariantPartition_orbits` |
| §2.2.1 "the `G`-invariant sets are the unions of orbits" | `Babai.isInvariant_iff_sUnion_orbits` |
| §2.2.1 `G_T`, `G_(T)` (Eq. (11), (12)) | `Babai.setwiseStabilizer`, `Babai.pointwiseStabilizer` |
| §2.2.1 `G_(T) = ker(G_T → S(T))`, `G_(T) ⊴ G_T` | `Babai.pointwiseStabilizer_subgroupOf_eq_ker`, `Babai.pointwiseStabilizer_normal_in_setwiseStabilizer` |
| §2.2.1 induced action on `t`-sets, `G^(t)` | `Babai.tAction`, `Babai.inducedOnTSets` |
| §2.2.1 Johnson groups | `Babai.JohnsonS`, `Babai.JohnsonA` |
| §2.2.1 transitive | `Babai.IsTransitiveAction`, `Babai.IsTransitive` (paper's notion; bridge `Babai.isTransitiveAction_iff`) |
| §2.2.1 `G`-invariant partition, blocks | `Babai.IsInvariantPartition` |
| §2.2.1 block of imprimitivity | `Babai.IsBlockOfImprimitivity`, `Babai.isBlockOfImprimitivity_iff_mem_invariantPartition` |
| §2.2.1 system of imprimitivity | `Babai.IsSystemOfImprimitivity`, `Babai.IsSystemOfImprimitivity.eq_images` |
| §2.2.1 action on the blocks, `G → S_m` | `Babai.blockHom`, `Babai.onBlocks` |
| §2.2.1 maximal system of imprimitivity | `Babai.IsMaximalSystemOfImprimitivity` |
| §11.1 minimal system of imprimitivity (blocks maximal) | `Babai.IsMinimalSystemOfImprimitivity` |
| §2.2.1 primitive | `Babai.IsPrimitive` |
| §2.2.1 examples of primitive groups | `Babai.isPrimitive_cyclicTranslations`, `Babai.isPrimitive_JohnsonS`, `Babai.isPrimitive_JohnsonA` |
| Definition 2.2.2 | `Babai.support`, `Babai.permDegree`, `Babai.minimalDegree` |
| §2.2.2 `t`-transitive, doubly transitive | `Babai.IsMultiplyTransitive`, `Babai.IsDoublyTransitive` (bridge `Babai.isMultiplyTransitive_iff`) |
| §2.2.2 monotonicity of `t`-transitivity | `Babai.IsMultiplyTransitive.mono` |
| Definition 2.2.3 | `Babai.degtrans`, `Babai.degtrans_spec`, `Babai.degtrans_eq_of_spec` |
| §2.2.2 `degtrans(S_n) = n`, `degtrans(A_n) = n-2` | `Babai.degtrans_top`, `Babai.degtrans_alternating` |
| Theorem 2.2.4 | `Babai.degtrans_le_five` (CITED axiom in `Workspace/Cited/Prelim.lean`, used in §13.2), `Babai.Theorem_2_2_4_b_statement` (cited, unused: statement only) |
| Theorem 2.2.5 | `Babai.Theorem_2_2_5_a_statement`, `Babai.Theorem_2_2_5_b_statement` (cited, unused: statements only) |
| Schreier's Hypothesis (§10.2) | `Babai.SchreierHypothesis` in `Workspace/Prelim/SchreierHypothesis.lean` |
| Proposition 2.2.6 | `Babai.preimage_eq_coset_of_nonempty`; RAM: (a) `Algo.decGroup_actKerGens`, `Algo.polyFun_actKerGens`; (b) `Algo.actPreimage_eq_some`, `Algo.actPreimage_eq_none_iff`, `Algo.polyFun_actPreimage` |
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*}

/-! ### §2.1 Fraktur

The paper's Section 2.1 only lists the Roman equivalents of the Fraktur letters it uses
(`𝔵`–x, `𝔶`–y, `𝔷`–z, `𝔄`–A, `𝔅`–B, `𝔊`–G, `ℌ`–H, `𝔍`–J, `𝔏`–L, `𝔓`–P, `𝔖`–S, `𝔛`–X,
`𝔜`–Y, `ℨ`–Z).  There is nothing to formalize; we use the Roman letters throughout. -/

/-! ### §2.2.1 Notation and terminology -/

section Basic

/-- §2.2.1.  "We refer to `S(Ω)` and `A(Ω)`, the two largest permutation groups on `Ω`,
as the *giants* on `Ω`." -/
def IsGiant [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  G = ⊤ ∨ G = alternatingGroup Ω

/-- §2.2.1.  "If `G^ϕ ≥ A(Ω)` we say `ϕ` is a *giant representation* and `G` acts on `Ω`
as a giant."  Here `ϕ : G →* S(Ω)` is a (permutation) representation of `G`. -/
def IsGiantRep {G : Type*} [Group G] [Fintype Ω] [DecidableEq Ω]
    (ϕ : G →* Equiv.Perm Ω) : Prop :=
  alternatingGroup Ω ≤ ϕ.range

/-- §2.2.1.  A subgroup of `S(Ω)` containing `A(Ω)` is a giant: the paper's two
descriptions of "giant" (being one of the two largest permutation groups, and containing
`A(Ω)`) agree.  Indeed `A(Ω)` has index `2` in `S(Ω)` when `|Ω| ≥ 2`, and equals `S(Ω)`
otherwise. -/
theorem isGiant_iff_alternating_le [Fintype Ω] [DecidableEq Ω]
    (G : Subgroup (Equiv.Perm Ω)) : IsGiant G ↔ alternatingGroup Ω ≤ G := by
  constructor
  · rintro (rfl | rfl)
    · exact le_top
    · exact le_rfl
  · intro h
    rcases subsingleton_or_nontrivial Ω with hΩ | hΩ
    · left
      refine (Subgroup.eq_top_iff' G).2 fun x => ?_
      have hx : x = 1 := Equiv.ext fun a => Subsingleton.elim _ _
      simpa [hx] using G.one_mem
    · have h2 : (alternatingGroup Ω).index = 2 := alternatingGroup.index_eq_two
      have key : (alternatingGroup Ω).relIndex G * G.index = (alternatingGroup Ω).index :=
        Subgroup.relIndex_mul_index h
      have hdvd : G.index ∣ 2 :=
        ⟨(alternatingGroup Ω).relIndex G, by rw [← h2, ← key]; ring⟩
      rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
      · left; exact Subgroup.index_eq_one.1 h1
      · right
        rw [h1, h2] at key
        have : (alternatingGroup Ω).relIndex G = 1 := by omega
        exact le_antisymm (Subgroup.relIndex_eq_one.1 this) h

/-- §2.2.1.  "A subset `Δ ⊆ Ω` is `G`-invariant if `Δ^G = Δ`", i.e. `Δ^σ = Δ` for every
`σ ∈ G`. -/
def IsInvariant (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) : Prop :=
  ∀ σ ∈ G, (σ : Equiv.Perm Ω) '' Δ = Δ

theorem isInvariant_iff_mem (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    IsInvariant G Δ ↔ ∀ σ ∈ G, ∀ x, x ∈ Δ ↔ σ x ∈ Δ := by
  constructor
  · intro h σ hσ x
    constructor
    · intro hx; rw [← h σ hσ]; exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h σ hσ] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact (σ.injective hxy) ▸ hy
  · intro h σ hσ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (h σ hσ x).1 hx
    · intro hy
      exact ⟨σ.symm y, (h σ hσ (σ.symm y)).2 (by simpa using hy), by simp⟩

/-- Notation 2.2.1.  The restriction homomorphism `G → S(Δ)` for a `G`-invariant set
`Δ ⊆ Ω`. -/
def restrictHom (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant G Δ) :
    G →* Equiv.Perm Δ where
  toFun σ := Equiv.Perm.subtypePerm (σ : Equiv.Perm Ω)
    (fun x => ((isInvariant_iff_mem G Δ).1 h σ σ.2 x).symm)
  map_one' := rfl
  map_mul' σ τ := rfl

/-- Notation 2.2.1.  "If `Δ ⊆ Ω` is `G`-invariant then `G^Δ` denotes the image of the
representation `G → S(Δ)` defined by restriction to `Δ`.  So `G^Δ ≤ S(Δ)`." -/
def restrictTo (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant G Δ) :
    Subgroup (Equiv.Perm Δ) :=
  (restrictHom G Δ h).range

/-- §2.2.1, Eq. (10).  "A simple bijection shows that `|x^G| = |G : G_x|`." -/
theorem card_orbit_eq_index (G : Subgroup (Equiv.Perm Ω)) (x : Ω) :
    Nat.card (orbit G x) = (stabilizer G x).index :=
  Nat.card_congr (orbitEquivQuotientStabilizer G x)

/-- §2.2.1, Eq. (11).  `G_T = {α ∈ G | T^α = T}`, the *setwise stabilizer* of `T ⊆ Ω`. -/
def setwiseStabilizer (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    Subgroup (Equiv.Perm Ω) where
  carrier := {α | α ∈ G ∧ (α : Equiv.Perm Ω) '' T = T}
  one_mem' := ⟨G.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨G.mul_mem ha hb, ?_⟩
    rw [show ((a * b : Equiv.Perm Ω) : Ω → Ω) = (a : Ω → Ω) ∘ (b : Ω → Ω) from rfl,
      Set.image_comp, hb', ha']
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨G.inv_mem ha, ?_⟩
    conv_lhs => rw [← ha']
    rw [← Set.image_comp]
    simp [Function.comp_def]

/-- §2.2.1, Eq. (12).  `G_(T) = {α ∈ G | (∀ x ∈ T)(x^α = x)}`, the *pointwise stabilizer*
of `T ⊆ Ω`. -/
def pointwiseStabilizer (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    Subgroup (Equiv.Perm Ω) where
  carrier := {α | α ∈ G ∧ ∀ x ∈ T, (α : Equiv.Perm Ω) x = x}
  one_mem' := ⟨G.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨G.mul_mem ha hb, fun x hx => by simp [Equiv.Perm.mul_apply, hb' x hx, ha' x hx]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨G.inv_mem ha, fun x hx => ?_⟩
    conv_lhs => rw [← ha' x hx]
    simp

@[simp] theorem mem_setwiseStabilizer {G : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    {α : Equiv.Perm Ω} :
    α ∈ setwiseStabilizer G T ↔ α ∈ G ∧ (α : Equiv.Perm Ω) '' T = T := Iff.rfl

@[simp] theorem mem_pointwiseStabilizer {G : Subgroup (Equiv.Perm Ω)} {T : Set Ω}
    {α : Equiv.Perm Ω} :
    α ∈ pointwiseStabilizer G T ↔ α ∈ G ∧ ∀ x ∈ T, α x = x := Iff.rfl

/-- §2.2.1.  "So `G_(T)` is the kernel of the `G_T → S(T)` homomorphism obtained by
restriction to `T`; in particular, `G_(T) ⊴ G_T`."  We record the inclusion. -/
theorem pointwiseStabilizer_le_setwiseStabilizer (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    pointwiseStabilizer G T ≤ setwiseStabilizer G T := by
  rintro α ⟨hα, hα'⟩
  refine ⟨hα, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [hα' x hx]; exact hx
  · intro hy; exact ⟨y, hy, hα' y hy⟩

/-- `T` is invariant under its own setwise stabilizer, so the restriction homomorphism
`G_T → S(T)` of §2.2.1 is defined. -/
theorem isInvariant_setwiseStabilizer (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    IsInvariant (setwiseStabilizer G T) T := fun _ hσ => hσ.2

/-- §2.2.1.  The restriction homomorphism `G_T → S(T)` of §2.2.1, whose kernel is
`G_(T)`. -/
def setwiseRestrictHom (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    setwiseStabilizer G T →* Equiv.Perm T :=
  restrictHom (setwiseStabilizer G T) T (isInvariant_setwiseStabilizer G T)

/-- §2.2.1.  "So `G_(T)` is the kernel of the `G_T → S(T)` homomorphism obtained by
restriction to `T`."

The kernel lives inside `G_T`; we state the equality after pushing it forward into
`S(Ω)`. -/
theorem pointwiseStabilizer_eq_map_ker (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    Subgroup.map (setwiseStabilizer G T).subtype (setwiseRestrictHom G T).ker
      = pointwiseStabilizer G T := by
  ext σ
  constructor
  · rintro ⟨⟨τ, hτ⟩, hker, rfl⟩
    refine ⟨hτ.1, fun x hx => ?_⟩
    have := congrArg (fun p : Equiv.Perm T => ((p ⟨x, hx⟩ : T) : Ω)) (MonoidHom.mem_ker.1 hker)
    simpa [setwiseRestrictHom, restrictHom] using this
  · rintro ⟨hσG, hσ⟩
    have hmem : σ ∈ setwiseStabilizer G T :=
      pointwiseStabilizer_le_setwiseStabilizer G T ⟨hσG, hσ⟩
    refine ⟨⟨σ, hmem⟩, ?_, rfl⟩
    show setwiseRestrictHom G T ⟨σ, hmem⟩ = 1
    ext x
    simpa [setwiseRestrictHom, restrictHom] using hσ x x.2

/-- §2.2.1.  `G_(T)`, viewed inside `G_T`, is the kernel of the restriction
homomorphism. -/
theorem pointwiseStabilizer_subgroupOf_eq_ker (G : Subgroup (Equiv.Perm Ω)) (T : Set Ω) :
    (pointwiseStabilizer G T).subgroupOf (setwiseStabilizer G T)
      = (setwiseRestrictHom G T).ker := by
  rw [Subgroup.subgroupOf, ← pointwiseStabilizer_eq_map_ker,
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]

/-- §2.2.1.  "in particular, `G_(T) ⊴ G_T`."  This is immediate from
`Babai.pointwiseStabilizer_subgroupOf_eq_ker`, since a kernel is normal. -/
instance pointwiseStabilizer_normal_in_setwiseStabilizer (G : Subgroup (Equiv.Perm Ω))
    (T : Set Ω) : ((pointwiseStabilizer G T).subgroupOf (setwiseStabilizer G T)).Normal := by
  rw [pointwiseStabilizer_subgroupOf_eq_ker]
  infer_instance

/-- §2.2.1.  "We denote the image of `G` under `ϕ` by `G^ϕ`, so `G^ϕ ≅ G/ker(ϕ)`." -/
noncomputable def quotientKerEquivRange {G : Type*} [Group G] {Γ : Type*}
    (ϕ : G →* Equiv.Perm Γ) : G ⧸ ϕ.ker ≃* ϕ.range :=
  QuotientGroup.quotientKerEquivRange ϕ

end Basic

/-! ### §2.2.1 The induced action on `t`-sets, Johnson groups -/

section TSets

variable [DecidableEq Ω]

/-- §2.2.1.  `binom Ω t` is the paper's `Ω choose t`, the set of `t`-subsets of `Ω`. -/
@[reducible] def binom (Ω : Type*) (t : ℕ) := {s : Finset Ω // s.card = t}

/-- The action of a permutation of `Ω` on the finite subsets of `Ω`. -/
def permFinsetEquiv (σ : Equiv.Perm Ω) : Equiv.Perm (Finset Ω) where
  toFun s := s.image σ
  invFun s := s.image σ.symm
  left_inv s := by simp [Finset.image_image, Function.comp_def]
  right_inv s := by simp [Finset.image_image, Function.comp_def]

@[simp] theorem permFinsetEquiv_apply (σ : Equiv.Perm Ω) (s : Finset Ω) :
    permFinsetEquiv σ s = s.image σ := rfl

/-- The induced action of `S(Ω)` on the finite subsets of `Ω`, as a homomorphism. -/
def permFinset : Equiv.Perm Ω →* Equiv.Perm (Finset Ω) where
  toFun := permFinsetEquiv
  map_one' := by ext s a; simp
  map_mul' σ τ := by
    ext s a
    simp [Finset.image_image, Function.comp_def]

@[simp] theorem permFinset_apply (σ : Equiv.Perm Ω) (s : Finset Ω) :
    permFinset σ s = s.image σ := rfl

/-- §2.2.1.  "A permutation group `G ≤ S(Ω)` naturally acts on `Ω choose t`; we refer to
this as the *induced action on `t`-sets*."  This is the underlying homomorphism
`S(Ω) →* S(Ω choose t)`. -/
def tAction (t : ℕ) : Equiv.Perm Ω →* Equiv.Perm (binom Ω t) where
  toFun σ := Equiv.Perm.subtypePerm (permFinset σ)
    (by intro s; simp [Finset.card_image_of_injective _ σ.injective])
  map_one' := by
    ext s
    simp [Equiv.Perm.subtypePerm]
  map_mul' σ τ := by
    ext s
    simp [Equiv.Perm.subtypePerm, Finset.image_image, Function.comp_def]

@[simp] theorem tAction_apply_coe (t : ℕ) (σ : Equiv.Perm Ω) (s : binom Ω t) :
    ((tAction t σ s : binom Ω t) : Finset Ω) = (s : Finset Ω).image σ := rfl

/-- §2.2.1.  `G^(t)`, the image of `G` in `S(Ω choose t)` under the induced action on
`t`-sets. -/
def inducedOnTSets (G : Subgroup (Equiv.Perm Ω)) (t : ℕ) :
    Subgroup (Equiv.Perm (binom Ω t)) :=
  G.map (tAction t)

/-- §2.2.1.  The Johnson group `S_k^(t)`: the symmetric group `S_k` in its induced action
on `t`-sets.  "We refer to `S_k^(t)` and `A_k^(t)` as *Johnson groups* since they act on
the Johnson schemes." -/
def JohnsonS (k t : ℕ) : Subgroup (Equiv.Perm (binom (Fin k) t)) :=
  inducedOnTSets (⊤ : Subgroup (Equiv.Perm (Fin k))) t

/-- §2.2.1.  The Johnson group `A_k^(t)`: the alternating group `A_k` in its induced
action on `t`-sets. -/
def JohnsonA (k t : ℕ) : Subgroup (Equiv.Perm (binom (Fin k) t)) :=
  inducedOnTSets (alternatingGroup (Fin k)) t

/-- §2.2.1.  The paper's `Ω choose t` is Mathlib's `Set.powersetCard Ω t`, on which Mathlib
records the induced action of a group acting on `Ω`. -/
def binomEquiv (Ω : Type*) (t : ℕ) : binom Ω t ≃ ↥(Set.powersetCard Ω t) :=
  ⟨fun s => ⟨s.1, s.2⟩, fun s => ⟨s.1, s.2⟩, fun _ => rfl, fun _ => rfl⟩

open scoped Pointwise in
set_option backward.isDefEq.respectTransparency false in
/-- §2.2.1.  Primitivity transfers from the action of `G ≤ S(Ω)` on `t`-subsets (Mathlib's
`Set.powersetCard`) to the induced group `G^{(t)} ≤ S(Ω choose t)`: the two actions are
carried into each other by `binomEquiv`. -/
theorem isPreprimitive_inducedOnTSets {t : ℕ} (G : Subgroup (Equiv.Perm Ω))
    (hpre : IsPreprimitive G (Set.powersetCard Ω t)) :
    IsPreprimitive (inducedOnTSets G t) (binom Ω t) := by
  classical
  set e := binomEquiv Ω t with he
  have hmem : ∀ σ : G, (tAction t (σ : Equiv.Perm Ω)) ∈ inducedOnTSets G t :=
    fun σ => Subgroup.mem_map.2 ⟨(σ : Equiv.Perm Ω), σ.2, rfl⟩
  have hpt : ∀ (σ : G) (s : binom Ω t),
      e ((⟨tAction t (σ : Equiv.Perm Ω), hmem σ⟩ : inducedOnTSets G t) • s)
        = σ • e s := by
    intro σ s
    apply Subtype.ext
    show ((tAction t (σ : Equiv.Perm Ω) s : binom Ω t) : Finset Ω) = _
    rw [tAction_apply_coe, Set.powersetCard.coe_smul]
    rfl
  have hset : ∀ (σ : G) (B : Set (binom Ω t)),
      e '' ((⟨tAction t (σ : Equiv.Perm Ω), hmem σ⟩ : inducedOnTSets G t) • B)
        = σ • (e '' B) := by
    intro σ B
    rw [← Set.image_smul, ← Set.image_smul, ← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' (fun s => hpt σ s)
  haveI : IsPretransitive (inducedOnTSets G t) (binom Ω t) := by
    constructor
    intro s s'
    obtain ⟨σ, hσ⟩ := hpre.toIsPretransitive.exists_smul_eq (e s) (e s')
    exact ⟨⟨tAction t (σ : Equiv.Perm Ω), hmem σ⟩,
      e.injective (by rw [hpt σ s]; exact hσ)⟩
  constructor
  intro B hB
  have hB' : IsBlock G (e '' B) := by
    rw [MulAction.isBlock_iff_smul_eq_or_disjoint]
    intro σ
    rw [← hset σ B]
    rcases (MulAction.isBlock_iff_smul_eq_or_disjoint.1 hB)
      ⟨tAction t (σ : Equiv.Perm Ω), hmem σ⟩ with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr ((Set.disjoint_image_iff e.injective).2 h)
  rcases hpre.isTrivialBlock_of_isBlock hB' with h | h
  · refine Or.inl fun x hx y hy => e.injective (h ?_ ?_)
    · exact Set.mem_image_of_mem e hx
    · exact Set.mem_image_of_mem e hy
  · refine Or.inr ?_
    ext x
    simp only [Set.mem_univ, iff_true]
    have hx : e x ∈ e '' B := by rw [h]; trivial
    obtain ⟨y, hy, hey⟩ := hx
    rwa [e.injective hey] at hy

end TSets

/-! ### §2.2.1 Transitivity, blocks, primitivity -/

section Blocks

/-- §2.2.1.  "The group `G` is *transitive* if it has only one orbit, i.e. `x^G = Ω` for
some (and therefore any) `x ∈ Ω`."

This is the paper's notion, stated for an arbitrary action: there is a point whose orbit
is everything.  It is **not** Mathlib's `MulAction.IsPretransitive`, which is vacuously
true on the empty set: an action on `∅` has no orbit at all, so it is not transitive in
the paper's sense.  The bridge is `Babai.isTransitiveAction_iff`. -/
def IsTransitiveAction (G : Type*) [Group G] (α : Type*) [MulAction G α] : Prop :=
  ∃ x : α, orbit G x = Set.univ

/-- The paper's "transitive" is Mathlib's `IsPretransitive` together with nonemptiness of
the domain. -/
theorem isTransitiveAction_iff (G : Type*) [Group G] (α : Type*) [MulAction G α] :
    IsTransitiveAction G α ↔ Nonempty α ∧ IsPretransitive G α := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨⟨x⟩, ⟨fun a b => ?_⟩⟩
    have ha : a ∈ orbit G x := by rw [hx]; trivial
    have hb : b ∈ orbit G x := by rw [hx]; trivial
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 ha
    obtain ⟨k, hk⟩ := mem_orbit_iff.1 hb
    exact ⟨k * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hk]⟩
  · rintro ⟨⟨x⟩, h⟩
    refine ⟨x, ?_⟩
    ext y
    exact ⟨fun _ => trivial, fun _ => h.exists_smul_eq x y⟩

/-- The Mathlib instance obtained from the paper's transitivity. -/
theorem IsTransitiveAction.isPretransitive {G : Type*} [Group G] {α : Type*}
    [MulAction G α] (h : IsTransitiveAction G α) : IsPretransitive G α :=
  ((isTransitiveAction_iff G α).1 h).2

theorem IsTransitiveAction.nonempty {G : Type*} [Group G] {α : Type*}
    [MulAction G α] (h : IsTransitiveAction G α) : Nonempty α :=
  ((isTransitiveAction_iff G α).1 h).1

/-- §2.2.1.  The group `G ≤ S(Ω)` is *transitive* if it has only one orbit. -/
abbrev IsTransitive (G : Subgroup (Equiv.Perm Ω)) : Prop := IsTransitiveAction G Ω

/-- §2.2.1.  "…i.e. `x^G = Ω` for some (and therefore any) `x ∈ Ω`." -/
theorem isTransitive_iff_orbit_eq_univ [Nonempty Ω] (G : Subgroup (Equiv.Perm Ω)) :
    IsTransitive G ↔ ∀ x : Ω, orbit G x = Set.univ := by
  rw [IsTransitive, isTransitiveAction_iff]
  constructor
  · rintro ⟨_, h⟩ x
    ext y
    exact ⟨fun _ => trivial, fun _ => h.exists_smul_eq x y⟩
  · intro h
    obtain ⟨x⟩ := ‹Nonempty Ω›
    exact (isTransitiveAction_iff _ _).1 ⟨x, h x⟩

/-- The image of an orbit under an element of `G` is again an orbit: `(x^G)^σ = (x^σ)^G`
for `σ ∈ G`. -/
theorem image_orbit {G : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω} (hσ : σ ∈ G) (x : Ω) :
    σ '' orbit G x = orbit G (σ x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hz
    exact ⟨⟨σ, hσ⟩ * g * ⟨σ, hσ⟩⁻¹, by
      simp [Subgroup.smul_def, Equiv.Perm.mul_apply]⟩
  · rintro hy
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hy
    refine ⟨(⟨σ, hσ⟩⁻¹ * g * ⟨σ, hσ⟩ : G) • x, ⟨_, rfl⟩, ?_⟩
    simp [Subgroup.smul_def, Equiv.Perm.mul_apply]

/-- §2.2.1.  "The `G`-invariant sets are the unions of orbits." -/
theorem isInvariant_iff_orbit_subset (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    IsInvariant G Δ ↔ ∀ x ∈ Δ, orbit G x ⊆ Δ := by
  rw [isInvariant_iff_mem]
  constructor
  · intro h x hx y hy
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 hy
    exact (h (g : Equiv.Perm Ω) g.2 x).1 hx
  · intro h σ hσ x
    refine ⟨fun hx => h x hx ⟨⟨σ, hσ⟩, rfl⟩, fun hx => ?_⟩
    have : σ⁻¹ (σ x) ∈ Δ := h _ hx ⟨(⟨σ, hσ⟩ : G)⁻¹, rfl⟩
    simpa using this

/-- §2.2.1.  Every orbit is a `G`-invariant set. -/
theorem isInvariant_orbit (G : Subgroup (Equiv.Perm Ω)) (z : Ω) : IsInvariant G (orbit G z) := by
  rw [isInvariant_iff_orbit_subset]
  intro x hx
  rw [orbit_eq_iff.2 hx]

/-- §2.2.1.  "The `G`-invariant sets are the unions of orbits." -/
theorem isInvariant_iff_sUnion_orbits (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) :
    IsInvariant G Δ ↔ Δ = ⋃₀ {B | ∃ x ∈ Δ, B = orbit G x} := by
  rw [isInvariant_iff_orbit_subset]
  constructor
  · intro h
    ext y
    constructor
    · intro hy; exact ⟨orbit G y, ⟨y, hy, rfl⟩, mem_orbit_self y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩; exact h x hx hy
  · intro h x hx y hy
    rw [h]
    exact ⟨orbit G x, ⟨x, hx, rfl⟩, hy⟩

/-- §2.2.1.  "A `G`-invariant partition of `Ω` is a partition `{B₁,…,B_m}` where the `Bᵢ`
are nonempty, pairwise disjoint subsets of which the union is `Ω` such that `G` permutes
these subsets, i.e. `(∀σ ∈ G)(∀i)(∃j)(Bᵢ^σ = B_j)`.  The `Bᵢ` are the *blocks* of this
partition."

We record the partition as a set `ℬ` of subsets of `Ω`. -/
structure IsInvariantPartition (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω)) : Prop where
  nonempty : ∀ B ∈ ℬ, B.Nonempty
  pairwiseDisjoint : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B'
  covers : ⋃₀ ℬ = Set.univ
  permutes : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ

/-- §2.2.1.  "The orbits partition `Ω`."  The set of orbits is a `G`-invariant partition
of `Ω`. -/
theorem isInvariantPartition_orbits (G : Subgroup (Equiv.Perm Ω)) :
    IsInvariantPartition G {B | ∃ x : Ω, B = orbit G x} where
  nonempty := by rintro _ ⟨x, rfl⟩; exact ⟨x, mem_orbit_self x⟩
  pairwiseDisjoint := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    rw [Set.disjoint_left]
    intro z hzx hzy
    exact hne (by rw [← orbit_eq_iff.2 hzx, ← orbit_eq_iff.2 hzy])
  covers := by
    ext x
    exact ⟨fun _ => trivial, fun _ => ⟨orbit G x, ⟨x, rfl⟩, mem_orbit_self x⟩⟩
  permutes := by
    rintro σ hσ _ ⟨x, rfl⟩
    exact ⟨σ x, image_orbit hσ x⟩

/-- §2.2.1.  "A nonempty subset `B ⊆ Ω` is a *block of imprimitivity* for `G` if
`(∀g ∈ G)(B^g = B or B^g ∩ B = ∅)`." -/
def IsBlockOfImprimitivity (G : Subgroup (Equiv.Perm Ω)) (B : Set Ω) : Prop :=
  B.Nonempty ∧ ∀ g ∈ G, (g : Equiv.Perm Ω) '' B = B ∨ ((g : Equiv.Perm Ω) '' B) ∩ B = ∅

/-- The paper's block of imprimitivity is Mathlib's `MulAction.IsBlock` together with
nonemptiness (Mathlib allows `∅` to be a block). -/
theorem isBlockOfImprimitivity_iff (G : Subgroup (Equiv.Perm Ω)) (B : Set Ω) :
    IsBlockOfImprimitivity G B ↔ B.Nonempty ∧ IsBlock G B := by
  rw [IsBlockOfImprimitivity, and_congr_right_iff]
  intro _
  rw [isBlock_iff_smul_eq_or_disjoint]
  constructor
  · intro h g
    rcases h (g : Equiv.Perm Ω) g.2 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 h')
  · intro h g hg
    rcases h ⟨g, hg⟩ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1 h')

/-- Composing images: `(B^τ)^σ = B^(στ)` in Lean's order. -/
theorem image_image_eq_mul_image (σ τ : Equiv.Perm Ω) (B : Set Ω) :
    σ '' (τ '' B) = (σ * τ : Equiv.Perm Ω) '' B := by
  rw [← Set.image_comp]
  rfl

/-- §2.2.1.  "A subset `B ⊆ Ω` is a block of imprimitivity if and only if it is a block in
an invariant partition."

For the forward direction we take the partition consisting of the `G`-images of `B`
together with the singletons of the points outside their union; that union is
`G`-invariant, so the singletons are permuted among themselves. -/
theorem isBlockOfImprimitivity_iff_mem_invariantPartition
    (G : Subgroup (Equiv.Perm Ω)) (B : Set Ω) :
    IsBlockOfImprimitivity G B ↔ ∃ ℬ, IsInvariantPartition G ℬ ∧ B ∈ ℬ := by
  constructor
  · rintro ⟨hne, hblock⟩
    set U : Set Ω := ⋃₀ {C | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B} with hUdef
    have hsub : ∀ σ ∈ G, (σ : Equiv.Perm Ω) '' B ⊆ U := fun σ hσ _ hy => ⟨_, ⟨σ, hσ, rfl⟩, hy⟩
    have himg : ∀ σ ∈ G, ∀ τ ∈ G,
        (σ : Equiv.Perm Ω) '' B = (τ : Equiv.Perm Ω) '' B ∨
          Disjoint ((σ : Equiv.Perm Ω) '' B) ((τ : Equiv.Perm Ω) '' B) := by
      intro σ hσ τ hτ
      have hmul : (τ * (τ⁻¹ * σ) : Equiv.Perm Ω) = σ := by group
      rcases hblock (τ⁻¹ * σ) (G.mul_mem (G.inv_mem hτ) hσ) with h | h
      · left
        have h2 : τ '' ((τ⁻¹ * σ : Equiv.Perm Ω) '' B) = τ '' B := by rw [h]
        rwa [image_image_eq_mul_image, hmul] at h2
      · right
        rw [Set.disjoint_iff_inter_eq_empty]
        have h2 : τ '' (((τ⁻¹ * σ : Equiv.Perm Ω) '' B) ∩ B) = τ '' (∅ : Set Ω) := by rw [h]
        rwa [Set.image_inter τ.injective, image_image_eq_mul_image, hmul,
          Set.image_empty] at h2
    have hUinv : ∀ σ ∈ G, ∀ x, x ∈ U → σ x ∈ U := by
      rintro σ hσ x ⟨C, ⟨τ, hτ, rfl⟩, hx⟩
      exact ⟨(σ * τ : Equiv.Perm Ω) '' B, ⟨σ * τ, G.mul_mem hσ hτ, rfl⟩, by
        rw [← image_image_eq_mul_image]; exact ⟨x, hx, rfl⟩⟩
    have hUout : ∀ σ ∈ G, ∀ x, x ∉ U → σ x ∉ U := by
      intro σ hσ x hx hmem
      exact hx (by simpa using hUinv σ⁻¹ (G.inv_mem hσ) (σ x) hmem)
    refine ⟨{C | (∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B) ∨ (∃ x ∉ U, C = {x})},
      ⟨?_, ?_, ?_, ?_⟩, Or.inl ⟨1, G.one_mem, by simp⟩⟩
    · rintro C (⟨σ, _, rfl⟩ | ⟨x, _, rfl⟩)
      · exact hne.image _
      · exact ⟨x, rfl⟩
    · rintro C (⟨σ, hσ, rfl⟩ | ⟨x, hx, rfl⟩) C' (⟨τ, hτ, rfl⟩ | ⟨y, hy, rfl⟩) hCC'
      · rcases himg σ hσ τ hτ with h | h
        · exact absurd h hCC'
        · exact h
      · rw [Set.disjoint_right]
        intro z hzy hz'
        rw [Set.mem_singleton_iff] at hzy
        subst hzy
        exact hy (hsub σ hσ hz')
      · rw [Set.disjoint_left]
        rintro z hz hz'
        rw [Set.mem_singleton_iff] at hz
        exact hx (hz ▸ hsub τ hτ hz')
      · exact Set.disjoint_singleton.2 fun h => hCC' (by rw [h])
    · ext x
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      by_cases hx : x ∈ U
      · obtain ⟨C, ⟨σ, hσ, rfl⟩, hxC⟩ := hx
        exact ⟨_, Or.inl ⟨σ, hσ, rfl⟩, hxC⟩
      · exact ⟨{x}, Or.inr ⟨x, hx, rfl⟩, rfl⟩
    · rintro σ hσ C (⟨τ, hτ, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact Or.inl ⟨σ * τ, G.mul_mem hσ hτ, image_image_eq_mul_image _ _ _⟩
      · exact Or.inr ⟨σ x, hUout σ hσ x hx, by simp⟩
  · rintro ⟨ℬ, hℬ, hB⟩
    refine ⟨hℬ.nonempty B hB, fun g hg => ?_⟩
    by_cases h : (g : Equiv.Perm Ω) '' B = B
    · exact Or.inl h
    · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1
        (hℬ.pairwiseDisjoint _ (hℬ.permutes g hg B hB) _ hB h))

/-- §2.2.1.  "A *system of imprimitivity* for `G` is a `G`-invariant partition
`ℬ = {B₁,…,B_m}` of a `G`-invariant subset `Δ ⊆ Ω` such that `G` acts transitively
on `ℬ`." -/
structure IsSystemOfImprimitivity (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (ℬ : Set (Set Ω)) : Prop where
  invariant : IsInvariant G Δ
  nonempty : ∀ B ∈ ℬ, B.Nonempty
  pairwiseDisjoint : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, B ≠ B' → Disjoint B B'
  covers : ⋃₀ ℬ = Δ
  permutes : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ
  /-- `G` acts transitively on the set of blocks: there is exactly one orbit, so `ℬ` is
  nonempty (the paper's "transitive", see `Babai.IsTransitiveAction`). -/
  blocks_nonempty : ℬ.Nonempty
  /-- `G` acts transitively on the set of blocks. -/
  transitiveOnBlocks : ∀ B ∈ ℬ, ∀ B' ∈ ℬ, ∃ σ ∈ G, (σ : Equiv.Perm Ω) '' B = B'

/-- §2.2.1.  "The `Bᵢ` are then blocks of imprimitivity." -/
theorem IsSystemOfImprimitivity.isBlockOfImprimitivity {G : Subgroup (Equiv.Perm Ω)}
    {Δ : Set Ω} {ℬ : Set (Set Ω)} (h : IsSystemOfImprimitivity G Δ ℬ) {B : Set Ω}
    (hB : B ∈ ℬ) : IsBlockOfImprimitivity G B := by
  refine ⟨h.nonempty B hB, fun g hg => ?_⟩
  by_cases hgB : (g : Equiv.Perm Ω) '' B = B
  · exact Or.inl hgB
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.1
      (h.pairwiseDisjoint _ (h.permutes g hg B hB) _ hB hgB))

/-- §2.2.1.  "…and every system of imprimitivity arises as the set of `G`-images of a
block of imprimitivity." -/
theorem IsSystemOfImprimitivity.eq_images {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    {ℬ : Set (Set Ω)} (h : IsSystemOfImprimitivity G Δ ℬ) {B₀ : Set Ω} (hB₀ : B₀ ∈ ℬ) :
    ℬ = {C | ∃ σ ∈ G, C = (σ : Equiv.Perm Ω) '' B₀} := by
  ext C
  constructor
  · intro hC
    obtain ⟨σ, hσ, hσC⟩ := h.transitiveOnBlocks B₀ hB₀ C hC
    exact ⟨σ, hσ, hσC.symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact h.permutes σ hσ B₀ hB₀

/-! #### The induced action on the blocks

§2.2.1: "The group `G` acts on `ℬ` by permuting the blocks; this defines a representation
`G → S_m`."

`Babai.blockHom` is that representation, and `Babai.onBlocks` is its image `G^ℬ ≤ S(ℬ)`.
They are defined from the "permutes" clause alone, so that they apply verbatim to a
`G`-invariant partition (`Babai.IsInvariantPartition`) and to a system of imprimitivity
(`Babai.IsSystemOfImprimitivity`). -/

/-- The permutation of the block set `ℬ` induced by `σ ∈ G`. -/
def blockPerm (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) (σ : G) : Equiv.Perm ℬ where
  toFun B := ⟨(σ : Equiv.Perm Ω) '' (B : Set Ω), hperm σ σ.2 B B.2⟩
  invFun B := ⟨((σ⁻¹ : G) : Equiv.Perm Ω) '' (B : Set Ω), hperm (σ⁻¹ : G) (σ⁻¹ : G).2 B B.2⟩
  left_inv B := by
    ext1
    simp [image_image_eq_mul_image]
  right_inv B := by
    ext1
    simp [image_image_eq_mul_image]

@[simp] theorem blockPerm_apply_coe (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) (σ : G) (B : ℬ) :
    ((blockPerm G ℬ hperm σ B : ℬ) : Set Ω) = (σ : Equiv.Perm Ω) '' (B : Set Ω) := rfl

/-- §2.2.1.  "The group `G` acts on `ℬ` by permuting the blocks; this defines a
representation `G → S_m`." -/
def blockHom (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) : G →* Equiv.Perm ℬ where
  toFun := blockPerm G ℬ hperm
  map_one' := by
    ext B
    simp [blockPerm]
  map_mul' σ τ := by
    ext B
    simp [blockPerm, image_image_eq_mul_image]

@[simp] theorem blockHom_apply_coe (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) (σ : G) (B : ℬ) :
    ((blockHom G ℬ hperm σ B : ℬ) : Set Ω) = (σ : Equiv.Perm Ω) '' (B : Set Ω) := rfl

/-- §2.2.1.  `G^ℬ`, the image of `G` in `S(ℬ)` under the action on the blocks. -/
def onBlocks (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) : Subgroup (Equiv.Perm ℬ) :=
  (blockHom G ℬ hperm).range

/-- The kernel of the action on the blocks is the subgroup of `G` fixing every block
setwise. -/
theorem mem_ker_blockHom {G : Subgroup (Equiv.Perm Ω)} {ℬ : Set (Set Ω)}
    {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ} {σ : G} :
    σ ∈ (blockHom G ℬ hperm).ker ↔ ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B = B := by
  constructor
  · intro h B hB
    have := congrArg (fun p : Equiv.Perm ℬ => ((p ⟨B, hB⟩ : ℬ) : Set Ω))
      (MonoidHom.mem_ker.1 h)
    simpa using this
  · intro h
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun B => Subtype.ext ?_
    simpa using h (B : Set Ω) B.2

/-- §2.2.1.  For a system of imprimitivity, `G` acts transitively on `ℬ` — in the paper's
sense (`Babai.IsTransitiveAction`: exactly one orbit, so `ℬ ≠ ∅`). -/
theorem IsSystemOfImprimitivity.isTransitive_onBlocks {G : Subgroup (Equiv.Perm Ω)}
    {Δ : Set Ω} {ℬ : Set (Set Ω)} (h : IsSystemOfImprimitivity G Δ ℬ) :
    IsTransitive (onBlocks G ℬ h.permutes) := by
  obtain ⟨B₀, hB₀⟩ := h.blocks_nonempty
  refine ⟨⟨B₀, hB₀⟩, ?_⟩
  ext C
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨σ, hσ, hσC⟩ := h.transitiveOnBlocks B₀ hB₀ (C : Set Ω) C.2
  refine ⟨⟨blockHom G ℬ h.permutes ⟨σ, hσ⟩, ⟨⟨σ, hσ⟩, rfl⟩⟩, ?_⟩
  exact Subtype.ext (by simpa using hσC)

/-- §2.2.1.  "A *maximal system of imprimitivity* for `G` is a system of imprimitivity of
blocks of size `≥ 2` that cannot be refined, i.e. where the blocks are minimal (do not
properly contain any block of imprimitivity of size `≥ 2`)."

Conventions.  `Set.ncard` of an infinite set is `0`, so `2 ≤ B.ncard` inverts its meaning
for an infinite block; the paper's `Ω` is always finite ("All groups in this paper are
finite", §2.2), so this never arises, and we keep the definition as the paper words it.

Version 2.5 never uses this notion again.  What Secs. 1.2.1, 11.1, 11.2 and 16.1 use is
the opposite notion, a *minimal* system of imprimitivity (at least two blocks, blocks
maximal), which version 2.5 defines only parenthetically in Sec. 11.1; it is
`Babai.IsMinimalSystemOfImprimitivity` below. -/
structure IsMaximalSystemOfImprimitivity (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (ℬ : Set (Set Ω)) : Prop extends IsSystemOfImprimitivity G Δ ℬ where
  blocks_large : ∀ B ∈ ℬ, 2 ≤ B.ncard
  blocks_minimal : ∀ B ∈ ℬ, ∀ C : Set Ω, C ⊂ B → 2 ≤ C.ncard → ¬ IsBlockOfImprimitivity G C

/-- §11.1 (after the Luks reduction).  A *minimal system of imprimitivity*:

> Luks applied this reduction with great effect to minimal systems of imprimitivity
> (systems with at least two blocks that cannot be made coarser, i. e., the blocks are
> maximal) so `Ḡ` is a primitive group.

"The blocks are maximal" is read as: a block of imprimitivity `C ⊆ Δ` containing a block
`B ∈ ℬ` is either `B` itself or all of `Δ` (making the system coarser would mean
replacing `B` by a strictly larger block that is not the whole of `Δ`).

This is *not* the "maximal system of imprimitivity" of §2.2.1
(`Babai.IsMaximalSystemOfImprimitivity`, blocks minimal).  The definition is placed here
because both Sec. 10 (Theorem 10.5.1 (g)) and Sec. 11 use it. -/
structure IsMinimalSystemOfImprimitivity (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (ℬ : Set (Set Ω)) : Prop extends IsSystemOfImprimitivity G Δ ℬ where
  /-- "systems with at least two blocks" -/
  two_blocks : 2 ≤ ℬ.ncard
  /-- "the blocks are maximal" -/
  blocks_maximal : ∀ B ∈ ℬ, ∀ C : Set Ω, C ⊆ Δ → B ⊆ C → IsBlockOfImprimitivity G C →
    C = B ∨ C = Δ

/-- §2.2.1.  "`G ≤ S(Ω)` is *primitive* if `|G| ≥ 2` and `G` has no blocks of
imprimitivity other than `Ω` and the singletons (sets of one element)."

Convention.  `Nat.card G = 0` for an infinite `G`, so the clause `2 ≤ Nat.card G` would
call a hypothetical infinite `G` imprimitive.  The paper's groups are always finite
("All groups in this paper are finite", §2.2), where `2 ≤ Nat.card G` is exactly
`Nontrivial G`, so we keep the paper's wording. -/
def IsPrimitive (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  2 ≤ Nat.card G ∧ ∀ B : Set Ω, IsBlockOfImprimitivity G B → B = Set.univ ∨ ∃ x, B = {x}

/-- §2.2.1.  "In particular, a primitive group is transitive."

(The orbits are blocks of imprimitivity; if all of them were singletons then `G = 1`,
contradicting `|G| ≥ 2`.) -/
theorem IsPrimitive.isTransitive {G : Subgroup (Equiv.Perm Ω)}
    (h : IsPrimitive G) : IsTransitive G := by
  obtain ⟨hcard, hblocks⟩ := h
  have horb : ∀ x : Ω, IsBlockOfImprimitivity G (orbit G x) := by
    intro x
    rw [isBlockOfImprimitivity_iff]
    exact ⟨⟨x, mem_orbit_self x⟩, (IsFixedBlock.orbit x).isBlock⟩
  by_cases hall : ∀ x : Ω, ∃ y, orbit G x = {y}
  · exfalso
    have hfix : ∀ (g : G) (x : Ω), (g : Equiv.Perm Ω) x = x := by
      intro g x
      obtain ⟨y, hy⟩ := hall x
      have hx : x ∈ orbit G x := mem_orbit_self x
      have hgx : (g : Equiv.Perm Ω) x ∈ orbit G x := ⟨g, rfl⟩
      rw [hy, Set.mem_singleton_iff] at hx hgx
      rw [hgx, hx]
    have hsub : Subsingleton G := by
      refine ⟨fun g k => Subtype.ext (Equiv.ext fun x => ?_)⟩
      rw [hfix g x, hfix k x]
    have : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
    omega
  · push_neg at hall
    obtain ⟨x, hx⟩ := hall
    rcases hblocks _ (horb x) with h | ⟨y, hy⟩
    · exact ⟨x, h⟩
    · exact absurd hy (hx y)

/-- §2.2.1, bridge to Mathlib.  For `|Ω| ≥ 2`, the paper's primitivity is Mathlib's
`MulAction.IsPreprimitive`.

The two notions differ exactly when `|Ω| ≤ 1`: there the (only) group `G = 1` is
preprimitive in Mathlib's sense but is not primitive in the paper's sense, because
`|G| = 1 < 2`. -/
theorem isPrimitive_iff_isPreprimitive [Finite Ω] [Nontrivial Ω] (G : Subgroup (Equiv.Perm Ω)) :
    IsPrimitive G ↔ IsPreprimitive G Ω := by
  constructor
  · intro h
    haveI : IsPretransitive G Ω := h.isTransitive.isPretransitive
    refine ⟨fun {B} hB => ?_⟩
    rcases B.eq_empty_or_nonempty with rfl | hne
    · exact Or.inl Set.subsingleton_empty
    · rcases h.2 B ((isBlockOfImprimitivity_iff G B).2 ⟨hne, hB⟩) with h' | ⟨x, rfl⟩
      · exact Or.inr h'
      · exact Or.inl Set.subsingleton_singleton
  · intro h
    constructor
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
      obtain ⟨g, hg⟩ := h.exists_smul_eq x y
      have hg1 : g ≠ 1 := by
        rintro rfl
        exact hxy (by simpa using hg)
      have hne1 : Nat.card G ≠ 1 := by
        intro h1
        rw [Nat.card_eq_one_iff_unique] at h1
        exact hg1 (h1.1.elim g 1)
      have hpos : 0 < Nat.card G := Nat.card_pos
      omega
    · intro B hB
      obtain ⟨hne, hBlock⟩ := (isBlockOfImprimitivity_iff G B).1 hB
      rcases h.isTrivialBlock_of_isBlock hBlock with h' | h'
      · exact Or.inr ⟨hne.choose, h'.eq_singleton_of_mem hne.choose_spec⟩
      · exact Or.inl h'

end Blocks

/-! ### §2.2.1 Examples of primitive groups

"Examples of primitive groups include the cyclic group of prime order `p` acting
naturally on a set of `p` elements, and the Johnson groups `S_k^(t)` and `A_k^(t)` for
`t ≥ 1` and `k ≥ 2t + 1`."  The paper asserts these without proof. -/

section PrimitiveExamples

/-- The cyclic group of order `n` in its natural action on `n` points: `ℤ/n` acting on
itself by translations. -/
def cyclicTranslations (n : ℕ) : Subgroup (Equiv.Perm (ZMod n)) where
  carrier := Set.range (fun a : ZMod n => Equiv.addLeft a)
  one_mem' := ⟨0, by ext x; simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by ext x; simp [add_assoc]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by ext x; simp⟩

theorem isPretransitive_cyclicTranslations (n : ℕ) :
    IsPretransitive (cyclicTranslations n) (ZMod n) :=
  ⟨fun x y => ⟨⟨Equiv.addLeft (y - x), ⟨y - x, rfl⟩⟩, by simp [Subgroup.smul_def]⟩⟩

/-- §2.2.1.  "Examples of primitive groups include the cyclic group of prime order `p`
acting naturally on a set of `p` elements." -/
theorem isPrimitive_cyclicTranslations (p : ℕ) [hp : Fact p.Prime] :
    IsPrimitive (cyclicTranslations p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  haveI := isPretransitive_cyclicTranslations p
  rw [isPrimitive_iff_isPreprimitive]
  refine IsPreprimitive.of_prime_card ?_
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact hp.out

/-- §2.2.1.  "Examples of primitive groups include … the Johnson groups `S_k^(t)` and
`A_k^(t)` for `t ≥ 1` and `k ≥ 2t + 1`."

The paper asserts this without proof; we prove it from the primitivity of the actions of
`S_k` and `A_k` on `t`-subsets. -/
theorem isPrimitive_inducedOnTSets_top {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {t : ℕ}
    (ht : 1 ≤ t) (hk : 2 * t + 1 ≤ Fintype.card Ω) :
    IsPrimitive (inducedOnTSets (⊤ : Subgroup (Equiv.Perm Ω)) t) := by
  have hcard : Nat.card Ω = Fintype.card Ω := Nat.card_eq_fintype_card
  haveI : Nontrivial (binom Ω t) :=
    (binomEquiv Ω t).nontrivial_congr.2
      (Set.powersetCard.nontrivial' (by omega) (by rw [hcard]; omega))
  rw [isPrimitive_iff_isPreprimitive]
  refine isPreprimitive_inducedOnTSets _ ?_
  haveI : IsPreprimitive (Equiv.Perm Ω) (Set.powersetCard Ω t) :=
    Set.powersetCard.isPreprimitive_perm ht (by rw [hcard]; omega) (by rw [hcard]; omega)
  exact (MulAction.isPreprimitive_congr (φ := (⊤ : Subgroup (Equiv.Perm Ω)).subtype)
    (f := (⟨id, fun m x => rfl⟩ :
      Set.powersetCard Ω t →ₑ[(⊤ : Subgroup (Equiv.Perm Ω)).subtype]
        Set.powersetCard Ω t)) (fun g => ⟨⟨g, trivial⟩, rfl⟩) Function.bijective_id).2 ‹_›

/-- §2.2.1.  "Examples of primitive groups include … the Johnson groups `S_k^(t)` and
`A_k^(t)` for `t ≥ 1` and `k ≥ 2t + 1`."  The case `Ω = Fin k` of
`Babai.isPrimitive_inducedOnTSets_top`. -/
theorem isPrimitive_JohnsonS {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t + 1 ≤ k) :
    IsPrimitive (JohnsonS k t) :=
  isPrimitive_inducedOnTSets_top ht (by simpa using hk)

set_option backward.isDefEq.respectTransparency false in
/-- §2.2.1.  The alternating Johnson group `A_k^(t)` is primitive for `t ≥ 1` and
`k ≥ 2t + 1`.  Asserted without proof by the paper. -/
theorem isPrimitive_JohnsonA {k t : ℕ} (ht : 1 ≤ t) (hk : 2 * t + 1 ≤ k) :
    IsPrimitive (JohnsonA k t) := by
  haveI : Nontrivial (binom (Fin k) t) :=
    (binomEquiv (Fin k) t).nontrivial_congr.2
      (Set.powersetCard.nontrivial' (by omega) (by simp; omega))
  rw [isPrimitive_iff_isPreprimitive]
  refine isPreprimitive_inducedOnTSets _ ?_
  have hcard : Nat.card (Fin k) = k := by simp
  have hn : t < Nat.card (Fin k) := by rw [hcard]; omega
  haveI : IsPretransitive (alternatingGroup (Fin k)) (Set.powersetCard (Fin k) t) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by rw [hcard]; omega)
  haveI : Nontrivial (Set.powersetCard (Fin k) t) :=
    Set.powersetCard.nontrivial' (by omega) hn
  obtain ⟨s⟩ := (inferInstance : Nontrivial (Set.powersetCard (Fin k) t)).to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s, Set.powersetCard.stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [Set.powersetCard.coe_nonempty_iff]; omega
  · simp only [Set.nonempty_compl, ne_eq, Set.eq_univ_iff_ncard, Set.powersetCard.ncard_eq]
    exact ne_of_lt hn
  · simp only [Set.powersetCard.ncard_eq]
    rw [hcard]; omega

end PrimitiveExamples

/-! ### Definition 2.2.2: support and minimal degree -/

section MinimalDegree

variable [Fintype Ω] [DecidableEq Ω]

/-- Definition 2.2.2.  "The *support* of a permutation `σ ∈ S(Ω)` is the set of elements
that `σ` moves: `supp(σ) = {x ∈ Ω | x^σ ≠ x}`." -/
def support (σ : Equiv.Perm Ω) : Finset Ω := Equiv.Perm.support σ

theorem mem_support {σ : Equiv.Perm Ω} {x : Ω} : x ∈ support σ ↔ σ x ≠ x :=
  Equiv.Perm.mem_support

/-- Definition 2.2.2.  "The *degree* of `σ` is the size of its support."

Name clash warning.  §2.2.1 uses "degree" for a second, unrelated notion: "The size of
the permutation domain, `|Ω|`, is called the *degree* of `G`", and likewise the degree of
a representation is the size of its domain.  That notion is `Fintype.card Ω` here and is
what later sections mean by "degree" of a group or a representation; `permDegree` is only
Definition 2.2.2's degree of a *permutation*. -/
def permDegree (σ : Equiv.Perm Ω) : ℕ := (support σ).card

/-- Definition 2.2.2.  "The *minimal degree* of a permutation group `G` is
`min_{σ ∈ G, σ ≠ 1} |supp(σ)|`."

Convention.  For the trivial group the paper's minimum is over the empty set and is
undefined (the usual convention being `+∞`); `sInf ∅ = 0` in Lean, so `minimalDegree 1`
is `0`.  Version 2.5 uses "minimal degree" nowhere else (only in Definition 2.2.2), so no
later statement depends on this, and we keep the definition as the paper words it. -/
noncomputable def minimalDegree (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  sInf {n | ∃ σ ∈ G, σ ≠ 1 ∧ permDegree σ = n}

end MinimalDegree

/-! ### §2.2.2 Degree of transitivity -/

section DegreeOfTransitivity

variable [Fintype Ω] [DecidableEq Ω]

/-- §2.2.2.  "`G ≤ S(Ω)` is *`t`-transitive* if its induced action on the set of
`n(n-1)⋯(n-t+1)` ordered `t`-tuples of distinct elements is transitive."

The ordered `t`-tuples of distinct elements are `Fin t ↪ Ω`, and "transitive" is the
paper's notion (`Babai.IsTransitiveAction`: exactly one orbit).  In particular, if `G` is
`t`-transitive then such tuples exist, so `t ≤ |Ω|` (`Babai.le_card_of_multiplyTransitive`);
this is what distinguishes the notion from Mathlib's
`MulAction.IsMultiplyPretransitive`, which holds vacuously for `t > |Ω|`.  The bridge is
`Babai.isMultiplyTransitive_iff`.

"`G` is *doubly transitive*" (§2.2.2) is the case `t = 2`. -/
def IsMultiplyTransitive (G : Subgroup (Equiv.Perm Ω)) (t : ℕ) : Prop :=
  IsTransitiveAction G (Fin t ↪ Ω)

/-- §2.2.2.  "A group `G ≤ S(Ω)` is *doubly transitive* if its induced action on the set
of `n(n-1)` ordered pairs is transitive." -/
abbrev IsDoublyTransitive (G : Subgroup (Equiv.Perm Ω)) : Prop := IsMultiplyTransitive G 2

/-- Bridge to Mathlib: the paper's `t`-transitivity is Mathlib's
`IsMultiplyPretransitive` together with the existence of injective `t`-tuples. -/
theorem isMultiplyTransitive_iff (G : Subgroup (Equiv.Perm Ω)) (t : ℕ) :
    IsMultiplyTransitive G t ↔ t ≤ Fintype.card Ω ∧ IsMultiplyPretransitive G Ω t := by
  rw [IsMultiplyTransitive, isTransitiveAction_iff]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨by simpa using Function.Embedding.nonempty_iff_card_le.1 hne, h⟩
  · rintro ⟨hle, h⟩
    exact ⟨Function.Embedding.nonempty_of_card_le (by simpa using hle), h⟩

/-- §2.2.2.  If `G` is `t`-transitive and `s ≤ t`, then `G` is `s`-transitive.

This is what makes Definition 2.2.3 well posed: the `t` of "`t`-transitive but not
`(t+1)`-transitive" is unique (`Babai.degtrans_eq_of_spec`). -/
theorem IsMultiplyTransitive.mono {G : Subgroup (Equiv.Perm Ω)} {s t : ℕ}
    (hst : s ≤ t) (h : IsMultiplyTransitive G t) : IsMultiplyTransitive G s := by
  rw [isMultiplyTransitive_iff] at h ⊢
  obtain ⟨hc, hp⟩ := h
  haveI := hp
  exact ⟨le_trans hst hc, isMultiplyPretransitive_of_le hst (by simpa using hc)⟩

/-- §2.2.2.  A `t`-transitive group has `t ≤ n`: there must exist ordered `t`-tuples of
distinct elements for the action on them to have an orbit. -/
theorem le_card_of_multiplyTransitive {G : Subgroup (Equiv.Perm Ω)} {t : ℕ}
    (h : IsMultiplyTransitive G t) : t ≤ Fintype.card Ω :=
  ((isMultiplyTransitive_iff G t).1 h).1

/-- Every group is `0`-transitive: there is exactly one empty tuple. -/
theorem isMultiplyTransitive_zero (G : Subgroup (Equiv.Perm Ω)) :
    IsMultiplyTransitive G 0 := by
  refine ⟨⟨Fin.elim0, fun a => a.elim0⟩, ?_⟩
  ext e
  refine ⟨fun _ => trivial, fun _ => ⟨1, ?_⟩⟩
  ext a
  exact a.elim0

theorem bddAbove_multiplyTransitive (G : Subgroup (Equiv.Perm Ω)) :
    BddAbove {t | IsMultiplyTransitive G t} :=
  ⟨Fintype.card Ω, fun _ ht => le_card_of_multiplyTransitive ht⟩

/-- Definition 2.2.3.  "We say that `degtrans(G)`, the *degree of transitivity* of `G`,
is `t` if `G` is `t`-transitive but not `(t+1)`-transitive."

We take the largest `t` for which `G` is `t`-transitive; `degtrans_spec` shows this is
exactly the paper's description.  (The set is nonempty, as every group is
`0`-transitive, and bounded above by `|Ω|`.) -/
noncomputable def degtrans (G : Subgroup (Equiv.Perm Ω)) : ℕ :=
  sSup {t | IsMultiplyTransitive G t}

/-- Definition 2.2.3.  `degtrans(G)` is the `t` such that `G` is `t`-transitive but not
`(t+1)`-transitive. -/
theorem degtrans_spec (G : Subgroup (Equiv.Perm Ω)) :
    IsMultiplyTransitive G (degtrans G) ∧ ¬ IsMultiplyTransitive G (degtrans G + 1) := by
  have hne : {t | IsMultiplyTransitive G t}.Nonempty :=
    ⟨0, isMultiplyTransitive_zero G⟩
  have hmem := Nat.sSup_mem hne (bddAbove_multiplyTransitive G)
  refine ⟨hmem, fun h => ?_⟩
  have hle : degtrans G + 1 ≤ degtrans G := le_csSup (bddAbove_multiplyTransitive G) h
  omega

/-- Definition 2.2.3.  `degtrans G` is *the* `t` such that `G` is `t`-transitive but not
`(t+1)`-transitive, so the paper's definition determines a unique value. -/
theorem degtrans_eq_of_spec {G : Subgroup (Equiv.Perm Ω)} {t : ℕ}
    (h1 : IsMultiplyTransitive G t) (h2 : ¬ IsMultiplyTransitive G (t + 1)) :
    degtrans G = t := by
  have hmem : IsMultiplyTransitive G (degtrans G) := (degtrans_spec G).1
  have hle : t ≤ degtrans G := le_csSup (bddAbove_multiplyTransitive G) h1
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq.symm
  · exact absurd (hmem.mono hlt) h2

/-- §2.2.2.  "The giants have high degree of transitivity: `degtrans(S_n) = n`." -/
theorem degtrans_top : degtrans (⊤ : Subgroup (Equiv.Perm Ω)) = Fintype.card Ω := by
  refine degtrans_eq_of_spec ?_ (fun hc => ?_)
  · rw [isMultiplyTransitive_iff]
    refine ⟨le_rfl, ?_⟩
    rw [MulAction.isMultiplyPretransitive_iff]
    intro x y
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding x y
    exact ⟨⟨σ, trivial⟩, hσ⟩
  · have := le_card_of_multiplyTransitive hc
    omega

/-- §2.2.2.  "`degtrans(A_n) = n - 2`."

The hypothesis `n ≠ 1` repairs the paper's formula, which is false at `n = 1`
there `A_1 = S_1` is `1`-transitive and not
`2`-transitive, so `degtrans(A_1) = 1`, while `n - 2` is `-1` (`0` with truncated
subtraction).  At `n = 0` and `n = 2` the formula does hold with truncated subtraction,
both sides being `0`, so `n ≠ 1` is the weakest repair. -/
theorem degtrans_alternating (h : Fintype.card Ω ≠ 1) :
    degtrans (alternatingGroup Ω) = Fintype.card Ω - 2 := by
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · have hz : Fintype.card Ω - 2 = 0 := by omega
    rw [hz]
    refine degtrans_eq_of_spec (isMultiplyTransitive_zero _) (fun hc => ?_)
    have := le_card_of_multiplyTransitive hc
    omega
  · have h2 : 2 ≤ Fintype.card Ω := by omega
    refine degtrans_eq_of_spec ?_ (fun hc => ?_)
    · rw [isMultiplyTransitive_iff]
      refine ⟨by omega, ?_⟩
      have hmt := alternatingGroup.isMultiplyPretransitive Ω
      rwa [Nat.card_eq_fintype_card] at hmt
    · rw [isMultiplyTransitive_iff] at hc
      have hc2 : IsMultiplyPretransitive (alternatingGroup Ω) Ω (Nat.card Ω - 1) := by
        have h' := hc.2
        rwa [show Nat.card Ω - 1 = Fintype.card Ω - 2 + 1 by
          rw [Nat.card_eq_fintype_card]; omega]
      have htop := Equiv.Perm.eq_top_of_isMultiplyPretransitive hc2
      haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
      have hidx : (alternatingGroup Ω).index = 2 := alternatingGroup.index_eq_two
      rw [htop, Subgroup.index_top] at hidx
      omega

/-! Theorem 2.2.4 (a) (Degree of transitivity; Curtis, Kantor, Seitz).
"Let `G ≤ S_n` be `t`-transitive.  Assume `G` is not a giant.  Then `t ≤ 5`."

The paper cites this without proof and says it depends on the Classification of Finite
Simple Groups, so it is an `axiom`, `Babai.degtrans_le_five` in
`Workspace/Cited/Prelim.lean`.  It is the only part of Theorems 2.2.4 and 2.2.5 that the
paper uses in a proof (Sec. 13.2, item 2b). -/

/-- Theorem 2.2.4 (b) ([CuKS]).  "If `n ≥ 25` then `t ≤ 3`."

Cited by the paper, not used in any proof or algorithm (it appears only in the remark of
Sec. 16.1).  Recorded as a statement only, not asserted. -/
-- CITED: Charles W. Curtis, William M. Kantor, Gary M. Seitz: The 2-transitive permutation
-- representations of the finite Chevalley groups. Trans. Amer. Math. Soc. 218 (1976), 1-59.
def Theorem_2_2_4_b_statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)), ¬ IsGiant G →
    25 ≤ Fintype.card Ω → ∀ t : ℕ, IsMultiplyTransitive G t → t ≤ 3

/-- Theorem 2.2.5 (a) (Wielandt).  "Let `G ≤ S_n` be `t`-transitive.  Assume `G` is not a
giant.  Then `t < 3 ln n`."

(Version 2.5 prints `t < 3 ln k` although the degree is called `n` in the same sentence;
the original source and the use of this theorem in §14 show that the degree is meant.
We write `n = |Ω|`.)

The paper gives no proof; it cites Wielandt's 1934 dissertation.  This result does not
depend on the CFSG.  It is used only in the concluding remarks (Sec. 16.1, line 5976:
"By Wielandt's 1934 result (Thm. 2.2.5) we have `d < 3 ln n`"), inside the alternative
algorithm sketched there, and on no path of the main algorithm; §14 of the original
source used it.  Recorded as a statement only, not asserted. -/
-- CITED: Helmut Wielandt: Abschätzungen für den Grad einer Permutationsgruppe von
-- vorgeschriebenem Transitivitätsgrad. Dissertation, Berlin, 1934. Schriften Math.
-- Seminars Inst. Angew. Math. Univ. Berlin 2 (1934) 151-174; cited in the Remarks after
-- Thm. 9.7 in H. Wielandt: Finite Permutation Groups, Acad. Press, New York 1964.
def Theorem_2_2_5_a_statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)), ¬ IsGiant G →
    ∀ t : ℕ, IsMultiplyTransitive G t → (t : ℝ) < 3 * Real.log (Fintype.card Ω)

/-- Theorem 2.2.5 (b) (Wielandt).  "`t ≤ 7` assuming Schreier's Hypothesis."

Schreier's Hypothesis (`Babai.SchreierHypothesis`: the outer automorphism group of every
finite simple group is solvable) is a known consequence of the CFSG; the paper carries it
as an explicit hypothesis, and so do we.

Cited by the paper, not used in any proof or algorithm (it appears only in the remark of
Sec. 16.1).  Recorded as a statement only, not asserted.

The hypothesis is taken at the same universe `u` as the permutation domain, so that the
implication is exactly the paper's and not a formally stronger one.  (By
`Babai.schreierHypothesis_iff` the universe is immaterial.) -/
-- CITED: Helmut Wielandt: Über den Transitivitätsgrad von Permutationsgruppen.
-- Math. Z. 74 (1960) 297-298; see [DiM, Thm. 7.3A].
def Theorem_2_2_5_b_statement : Prop :=
  SchreierHypothesis.{u} →
    ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)), ¬ IsGiant G →
      ∀ t : ℕ, IsMultiplyTransitive G t → t ≤ 7

end DegreeOfTransitivity

/-! ### §2.2.3 Polynomial-time algorithms in permutation groups

Section 2.2.3 of version 2.5 is marked "TO BE WRITTEN" and contains only
Proposition 2.2.6, on computing kernels of actions and on lifting.  This file records the
mathematical content of part (b).  Part (a) (the kernel of an action is computable in
polynomial time) has no mathematical content beyond `MonoidHom.ker`.  Both running-time
claims are proved on the RAM of `Workspace/Machine/`:

* part (a): `Algo.decGroup_actKerGens` with `Algo.polyFun_actKerGens`
  (`Workspace/Algo/Extend.lean`);
* part (b): `Algo.actPreimage_eq_some`, `Algo.actPreimage_eq_none_iff` with
  `Algo.polyFun_actPreimage` (`Workspace/Algo/TopLift.lean`), built on the window
  preimage `Algo.rawPreimage` (`Workspace/Algo/Labelled.lean`). -/

section Algorithms

variable {G : Type*} [Group G]

/-- Proposition 2.2.6 (b) [Lifting].  "Let `ϕ : G → S(Γ)` be a `G`-action on `Γ` and let
`τ ∈ S(Γ)`.  Then one can, in polynomial time, determine the set `ϕ⁻¹(τ)` (which is
either empty or a coset of `ker(ϕ)` in `G`)."

We prove the parenthetical mathematical statement here.  The running-time claim is proved
on the RAM as `Algo.polyFun_actPreimage`, with the specification `Algo.actPreimage_eq_some`
and `Algo.actPreimage_eq_none_iff` (`Workspace/Algo/TopLift.lean`). -/
theorem preimage_eq_coset_of_nonempty {Γ : Type*} (ϕ : G →* Equiv.Perm Γ)
    (τ : Equiv.Perm Γ) :
    ϕ ⁻¹' {τ} = ∅ ∨ ∃ g₀ : G, ϕ ⁻¹' {τ} = (fun h => g₀ * h) '' (ϕ.ker : Set G) := by
  rcases Set.eq_empty_or_nonempty (ϕ ⁻¹' {τ}) with h | ⟨g₀, hg₀⟩
  · exact Or.inl h
  · refine Or.inr ⟨g₀, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg₀
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe,
      MonoidHom.mem_ker]
    constructor
    · intro hg
      exact ⟨g₀⁻¹ * g, by simp [map_mul, hg, hg₀], by group⟩
    · rintro ⟨h, hh, rfl⟩
      simp [map_mul, hh, hg₀]

end Algorithms

end Babai
