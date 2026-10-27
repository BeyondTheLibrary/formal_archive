/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: general lemmas about earlier sections, used by the local certificates
algorithm but belonging to Sections 2, 10 and 11.
-/
import Workspace.AltQuotients.MainStructure
import Workspace.Luks.Instances

/-!
# Auxiliary material for §13.1

Section 13 works with a giant representation `ϕ : G → S(Γ)` for an *arbitrary* finite set
`Γ`, and with the restrictions `ψ_A : G_A → S(A)` to subsets `A ⊆ Γ`, whereas Section 10
is stated throughout for the target `S_k = S(Fin k)`.  This file carries the notions and
the three results of Section 10 that §13.1 uses (Definition 10.3.4, Theorem 10.3.5,
Corollary 10.3.7) over to an arbitrary finite target, by transport along a bijection
`Δ ≃ Fin |Δ|`.  Nothing here is new mathematics: each statement is the Section 10
statement with `S_k` replaced by `S(Δ)`.

It also collects the elementary facts about the window automorphism sets of §11.1
(`Babai.wAut`) that the algorithm of §13.1 uses.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### Transporting `A(Δ)` along a bijection -/

section Alternating

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The alternating group is carried onto the alternating group by the isomorphism
`S(α) ≃ S(β)` induced by a bijection `α ≃ β`. -/
theorem map_alternatingGroup_permCongrHom (e : α ≃ β) :
    (alternatingGroup α).map (Equiv.permCongrHom e).toMonoidHom = alternatingGroup β := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have : (Equiv.permCongrHom e).toMonoidHom f = e.permCongr f := rfl
    rw [this, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.1 hf
  · intro hg
    refine ⟨e.symm.permCongr g, ?_, ?_⟩
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
      exact Equiv.Perm.mem_alternatingGroup.1 hg
    · show e.permCongr (e.symm.permCongr g) = g
      ext b
      simp [Equiv.permCongr_apply]

/-- The alternating group is invariant under conjugation (it is normal in `S(α)`). -/
theorem map_alternatingGroup_conj (a : Equiv.Perm α) :
    (alternatingGroup α).map (MulAut.conj a).toMonoidHom = alternatingGroup α := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup] at hf
    rw [Equiv.Perm.mem_alternatingGroup]
    show Equiv.Perm.sign (a * f * a⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hf]
    simp
  · intro hg
    refine ⟨a⁻¹ * g * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
      rw [Equiv.Perm.mem_alternatingGroup] at hg
      rw [map_mul, map_mul, map_inv, hg]
      simp
    · show a * (a⁻¹ * g * a) * a⁻¹ = g
      group

/-- `A(β) ≤ K^e` if and only if `A(α) ≤ K`, for `K ≤ S(α)` and a bijection `e : α ≃ β`. -/
theorem alternating_le_map_permCongrHom_iff (e : α ≃ β) (K : Subgroup (Equiv.Perm α)) :
    alternatingGroup β ≤ K.map (Equiv.permCongrHom e).toMonoidHom ↔
      alternatingGroup α ≤ K := by
  rw [← map_alternatingGroup_permCongrHom e,
    Subgroup.map_le_map_iff_of_injective (Equiv.permCongrHom e).injective]

end Alternating

/-! ### Definition 10.3.4 with an arbitrary finite target

Definition 10.3.4 (`Babai.Affected`) is stated for `ϕ : G → S_k`.  Section 13 uses it for
`ψ : H → S(Δ)` with `Δ` an arbitrary finite set (Definition 13.1.4 and Eq. (68)); the two
readings agree when `Δ = Fin k` (`Babai.affectedIn_eq_affected`). -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Definition 10.3.4 (Affected), with an arbitrary finite target `Δ` in place of `S_k`:
`u` is affected by `ψ : H → S(Δ)` if `H_u^ψ ≱ A(Δ)`.  This is the notion used in
Definition 13.1.4. -/
def AffectedIn {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (ψ : H →* Equiv.Perm Δ) (u : Ω) : Prop :=
  ¬ alternatingGroup Δ ≤ (stabilizer H u).map ψ

/-- The set of points not affected by `ψ` (Theorem 10.3.5's set `D`). -/
def unaffectedIn {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (ψ : H →* Equiv.Perm Δ) : Set Ω :=
  {u | ¬ AffectedIn ψ u}

/-- For the target `S_k` the general notion is Definition 10.3.4 on the nose. -/
theorem affectedIn_eq_affected {H : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ψ : H →* Equiv.Perm (Fin k)) (u : Ω) : AffectedIn ψ u = Affected ψ u := rfl

section Transport

variable {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
  (ψ : H →* Equiv.Perm Δ)

/-- The transported representation `H → S(Fin |Δ|)`. -/
private noncomputable def toFinRep : H →* Equiv.Perm (Fin (Fintype.card Δ)) :=
  (Equiv.permCongrHom (Fintype.equivFin Δ)).toMonoidHom.comp ψ

private theorem isGiantRep_toFinRep (hψ : IsGiantRep ψ) : IsGiantRep (toFinRep ψ) := by
  have hrange : (toFinRep ψ).range
      = ψ.range.map (Equiv.permCongrHom (Fintype.equivFin Δ)).toMonoidHom := by
    ext g
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨ψ h, ⟨h, rfl⟩, rfl⟩
    · rintro ⟨f, ⟨h, rfl⟩, rfl⟩; exact ⟨h, rfl⟩
  rw [IsGiantRep, hrange, alternating_le_map_permCongrHom_iff]
  exact hψ

private theorem affected_toFinRep (u : Ω) : Affected (toFinRep ψ) u ↔ AffectedIn ψ u := by
  have hmap : (stabilizer H u).map (toFinRep ψ)
      = ((stabilizer H u).map ψ).map (Equiv.permCongrHom (Fintype.equivFin Δ)).toMonoidHom := by
    rw [toFinRep, Subgroup.map_map]
  unfold Affected AffectedIn
  rw [hmap, alternating_le_map_permCongrHom_iff]

private theorem unaffectedSet_toFinRep : unaffectedSet (toFinRep ψ) = unaffectedIn ψ := by
  ext u
  simp only [unaffectedSet, unaffectedIn, Set.mem_setOf_eq, affected_toFinRep ψ u]

/-- **Theorem 10.3.5** (Unaffected Stabilizers Lemma) with an arbitrary finite target.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S_k` a giant representation.  Assume
> `k > max{8, 2 + log₂ n₀}` where `n₀ = n₀(G)` denotes the length of the largest orbit of
> `G`.  Let `D` be the set of elements of `Ω` not affected by `ϕ`.  Then `G_(D)^ϕ ≥ A_k`.

Transported from `Babai.theorem_10_3_5` along a bijection `Δ ≃ Fin |Δ|`. -/
theorem theorem_10_3_5_gen (hψ : IsGiantRep ψ)
    (hk : LargeK (Nat.card Δ) (maxOrbitLength H)) :
    alternatingGroup Δ ≤ (pointwiseStab H (unaffectedIn ψ)).map ψ := by
  have hcard : Nat.card Δ = Fintype.card Δ := Nat.card_eq_fintype_card
  have h := theorem_10_3_5 (toFinRep ψ) (isGiantRep_toFinRep ψ hψ) (by rwa [hcard] at hk)
  rw [unaffectedSet_toFinRep ψ, toFinRep, ← Subgroup.map_map,
    alternating_le_map_permCongrHom_iff] at h
  exact h

/-- **Corollary 10.3.7** (Affected Orbit Lemma) with an arbitrary finite target.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S_k` a giant representation.  Assume
> `k ≥ 5`.  Then, if `∆` is an affected `G`-orbit, i.e. `∆ ∩ D = ∅`, then `ker(ϕ)` is not
> transitive on `∆`; in fact, each orbit of `ker(ϕ)` in `∆` has length `≤ |∆|/k`.

Transported from `Babai.corollary_10_3_7` along a bijection `Δ ≃ Fin |Δ|`. -/
theorem corollary_10_3_7_gen (hψ : IsGiantRep ψ) (hk5 : 5 ≤ Nat.card Δ) (u : Ω)
    (hΔ : ∀ z ∈ orbit H u, AffectedIn ψ z) (v : Ω) (hv : v ∈ orbit H u) :
    Nat.card Δ * Nat.card (orbit ψ.ker v) ≤ Nat.card (orbit H u) ∧
      Nat.card (orbit ψ.ker v) < Nat.card (orbit H u) := by
  have hcard : Nat.card Δ = Fintype.card Δ := Nat.card_eq_fintype_card
  have hker : (toFinRep ψ).ker = ψ.ker := by
    ext h
    simp only [MonoidHom.mem_ker, toFinRep, MonoidHom.comp_apply]
    constructor
    · intro hh
      refine (Equiv.permCongrHom (Fintype.equivFin Δ)).injective ?_
      rw [map_one]
      exact hh
    · intro hh
      rw [hh, map_one]
  have h := corollary_10_3_7 (toFinRep ψ) (isGiantRep_toFinRep ψ hψ) (by rw [hcard] at hk5; exact hk5)
    u (fun z hz => (affected_toFinRep ψ z).2 (hΔ z hz)) v hv
  rw [hker] at h
  rw [hcard]
  exact h

end Transport

/-! ### Window automorphisms (§11.1) -/

section Windows

variable {A : Type*} {W W' : Set Ω} {K L : Set (Equiv.Perm Ω)} {x : Ω → A}

/-- The window automorphisms shrink when the group shrinks. -/
theorem wAut_mono_group (h : K ⊆ L) : wAut W K x ⊆ wAut W L x :=
  fun _ hσ => ⟨h hσ.1, hσ.2⟩

/-- The window automorphisms shrink when the window grows. -/
theorem wAut_anti_window (h : W ⊆ W') : wAut W' K x ⊆ wAut W K x :=
  fun _ hσ => ⟨hσ.1, fun u hu => hσ.2 u (h hu)⟩

/-- Enlarging the window of a group that already respects the old window: the two-step
description of `Aut^{W'}_K(x)` used in Procedure Recompute `H(W)`. -/
theorem wAut_wAut (h : W ⊆ W') : wAut W' (wAut W K x) x = wAut W' K x := by
  ext σ
  constructor
  · rintro ⟨⟨hσK, -⟩, hσ⟩; exact ⟨hσK, hσ⟩
  · rintro ⟨hσK, hσ⟩
    exact ⟨⟨hσK, fun u hu => hσ u (h hu)⟩, hσ⟩

/-- The empty window imposes no condition. -/
@[simp] theorem wAut_empty : wAut (∅ : Set Ω) K x = K := by
  ext σ; simp [wAut, wIso]

end Windows

end Babai
