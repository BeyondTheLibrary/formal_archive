/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Schreier's Hypothesis, as stated by the paper in Sec. 10.2 (before Lemma 10.2.5) and
used in Theorem 2.2.5 (b) and in Lemma 10.2.5.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.TransferInstance

/-!
# Schreier's Hypothesis

The paper (Sec. 10.2, before Lemma 10.2.5): "The proof depends on the CFSG through
'Schreier's Hypothesis' (a known consequence of the CFSG) which states that the outer
automorphism group of every finite simple group is solvable."

We build the outer automorphism group as `MulAut G ⧸ Inn G`, where `Inn G` is the group
of inner automorphisms, i.e. the range of `MulAut.conj : G →* MulAut G`.  Mathlib has no
`Out` construction, so we provide one here.

`SchreierHypothesis` is a `Prop`, *not* an axiom: nothing in this development asserts it.
Statements depending on it take it as an explicit hypothesis, as the paper does.
-/

universe u

namespace Babai

/-- The group of inner automorphisms of `G`, the range of `MulAut.conj`. -/
def Inn (G : Type*) [Group G] : Subgroup (MulAut G) := (MulAut.conj (G := G)).range

/-- Inner automorphisms form a normal subgroup of the automorphism group:
`φ (conj g) φ⁻¹ = conj (φ g)`. -/
instance Inn.instNormal (G : Type*) [Group G] : (Inn G).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ φ
    refine ⟨φ g, ?_⟩
    ext x
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.coe_mk]
    simp [map_mul, map_inv]

/-- The outer automorphism group `Out(G) = Aut(G)/Inn(G)`. -/
abbrev Out (G : Type*) [Group G] : Type _ := MulAut G ⧸ Inn G

/-! ### Transfer along group isomorphisms

Sec. 10 applies Schreier's Hypothesis to simple groups that are only given up to
isomorphism (subquotients of `S(Ω)`, constituents of a quotient, …).  The following
transfer tools let the hypothesis be applied there, and reconcile the universe in which
the hypothesis is stated with the universe in which such a group lives. -/

/-- The isomorphism `Aut(G) ≃* Aut(H)` induced by an isomorphism `e : G ≃* H`,
namely `φ ↦ e ∘ φ ∘ e⁻¹`. -/
def MulAut.congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) : MulAut G ≃* MulAut H where
  toFun φ := (e.symm.trans φ).trans e
  invFun ψ := (e.trans ψ).trans e.symm
  left_inv φ := by ext x; simp
  right_inv ψ := by ext x; simp
  map_mul' φ ψ := by ext x; simp

@[simp] theorem MulAut.congr_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (φ : MulAut G) (x : H) : MulAut.congr e φ x = e (φ (e.symm x)) := rfl

/-- The isomorphism `Aut(G) ≃* Aut(H)` carries inner automorphisms to inner
automorphisms: `e ∘ (conj g) ∘ e⁻¹ = conj (e g)`. -/
theorem MulAut.congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem Inn.map_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Inn G).map (MulAut.congr e).toMonoidHom = Inn H := by
  ext ψ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨φ, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (MulAut.congr_conj e g).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨MulAut.conj (e.symm h), ⟨e.symm h, rfl⟩, by
      rw [MulAut.congr_conj e (e.symm h), e.apply_symm_apply]⟩

/-- `Out` is functorial in group isomorphisms: an isomorphism `G ≃* H` induces
`Out G ≃* Out H`. -/
def Out.congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) : Out G ≃* Out H :=
  QuotientGroup.congr (Inn G) (Inn H) (MulAut.congr e) (Inn.map_congr e)

/-- Schreier's Hypothesis, as stated in Sec. 10.2 of the paper: "the outer automorphism
group of every finite simple group is solvable".  It is a known consequence of the
Classification of Finite Simple Groups.

This is a statement, not an axiom: it is never asserted in this development. -/
def SchreierHypothesis : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], IsSolvable (Out S)

/-! ### The hypothesis does not depend on the universe

Schreier's Hypothesis speaks about *finite* simple groups, and every finite group is
isomorphic to a group carried by a type in any given universe
(`Finite.exists_type_univ_nonempty_mulEquiv`).  Simplicity, finiteness and solvability all
transfer along a `MulEquiv`, the last one through `Out.congr`.  So the statement at one
universe implies it at every other universe. -/

/-- Solvability of `Out` transfers along an isomorphism of groups. -/
theorem isSolvable_out_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [IsSolvable (Out H)] : IsSolvable (Out G) :=
  solvable_of_surjective (f := (Out.congr e).symm.toMonoidHom) (Out.congr e).symm.surjective

theorem schreierHypothesis_lift (h : SchreierHypothesis.{0}) : SchreierHypothesis.{u} := by
  intro S _ _ _
  obtain ⟨S', _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} S
  haveI : IsSimpleGroup S' := e.symm.isSimpleGroup
  haveI : IsSolvable (Out S') := h S'
  exact isSolvable_out_of_mulEquiv e

theorem schreierHypothesis_descend (h : SchreierHypothesis.{u}) : SchreierHypothesis.{0} := by
  intro S _ _ _
  haveI : IsSimpleGroup (ULift.{u} S) := (MulEquiv.ulift (α := S)).isSimpleGroup
  haveI : IsSolvable (Out (ULift.{u} S)) := h (ULift.{u} S)
  exact isSolvable_out_of_mulEquiv (MulEquiv.ulift (α := S)).symm

/-- Schreier's Hypothesis is universe-independent. -/
theorem schreierHypothesis_iff : SchreierHypothesis.{u} ↔ SchreierHypothesis.{0} :=
  ⟨schreierHypothesis_descend, schreierHypothesis_lift⟩

end Babai
