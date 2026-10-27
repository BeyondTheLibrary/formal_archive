import Workspace.Master.Line2
import Workspace.TopAction.CosetRounds

/-! # Supplied enumerations for Luks reductions

The image list must cover the image group and meet its cardinality bound.
The orbit list can use any order of the same orbits.
-/

universe u v w
namespace Babai
open Equiv MulAction
open scoped Classical Pointwise

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {G N : Subgroup (Perm Ω)} {H : Type w} [Group H]

noncomputable def OrbitEnum.chain (E : OrbitEnum N) (I : SIInstance Ω A) :
    SIReduction Ω A (Set (Perm Ω)) := cosetChain I.x I.y E.windows I.K

theorem OrbitEnum.run_chain_eq (E : OrbitEnum N) (I : SIInstance Ω A)
    (hΔ : I.Δ = Set.univ) : (E.chain I).run = I.answer := E.run_chain I hΔ

theorem OrbitEnum.calls_length_chain (E : OrbitEnum N) (I : SIInstance Ω A) :
    (E.chain I).calls.length ≤ (orbitList N).length := by
  exact ((calls_cosetChain _ _ _ _).1).trans_eq E.spec.length_eq

theorem OrbitEnum.calls_chain_window (E : OrbitEnum N) (I : SIInstance Ω A) :
    ∀ J ∈ (E.chain I).calls, J.Δ ∈ orbitList N :=
  fun J hJ => E.spec.mem_iff.1 ((calls_cosetChain _ _ _ _).2 J hJ)

theorem OrbitEnum.calls_chain_K (E : OrbitEnum N) (I : SIInstance Ω A) :
    ∀ J ∈ (E.chain I).calls, J.K ⊆ I.K := calls_cosetChain_K _ _ _ _

theorem OrbitEnum.calls_chain_coset (E : OrbitEnum N) (hNG : N ≤ G) (I : SIInstance Ω A)
    (hK : ∃ (M : Subgroup (Perm Ω)) (σ : Perm Ω), M ≤ N ∧ σ ∈ G ∧
      I.K = σ • (M : Set (Perm Ω))) :
    ∀ J ∈ (E.chain I).calls, IsCosetInstance G J :=
  isCosetInstance_calls_cosetChain hNG I.x I.y E.windows I.K E.invariant hK

structure Line2Enum [Fintype H] (ϕ : G →* H) where
  elements : List H
  cover : ∀ σ : H, σ ∈ elements
  length : elements.length ≤ Fintype.card H
  orbits : OrbitEnum (kerSubgroup ϕ)

noncomputable def Line2Enum.default [Fintype H] (ϕ : G →* H) : Line2Enum ϕ :=
  ⟨allElements H, mem_allElements, le_of_eq length_allElements, .default _⟩

noncomputable def cosetLuksBruteForceWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (cosetLiftAll ϕ x y E.elements).bind fun L => .done (⋃ s ∈ L, s)


theorem run_cosetLuksBruteForceWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    (cosetLuksBruteForceWith ϕ x y E).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  classical
  rw [cosetLuksBruteForceWith, SIReduction.run_bind, SIReduction.run_done, run_cosetLiftAll,
    ← iUnion_liftingSet ϕ x y]
  ext τ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨s, ⟨σ, -, rfl⟩, hτ⟩
    exact ⟨σ, hτ⟩
  · rintro ⟨σ, hτ⟩
    exact ⟨_, ⟨σ, E.cover σ, rfl⟩, hτ⟩

theorem calls_length_cosetLuksBruteForceWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    (cosetLuksBruteForceWith ϕ x y E).calls.length ≤ Fintype.card H := by
  classical
  rw [cosetLuksBruteForceWith, SIReduction.calls_bind, SIReduction.calls_done,
    calls_cosetLiftAll]
  simpa only [List.length_append, List.length_map, List.length_nil, add_zero] using E.length


theorem calls_cosetLuksBruteForceWith_wrt [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    ∀ I ∈ (cosetLuksBruteForceWith ϕ x y E).calls,
      (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ := by
  classical
  rw [cosetLuksBruteForceWith, SIReduction.calls_bind, SIReduction.calls_done,
    calls_cosetLiftAll]
  intro I hI
  simp only [List.append_nil, List.mem_map] at hI
  obtain ⟨σ, -, rfl⟩ := hI
  exact ⟨⟨σ, rfl⟩, rfl⟩


noncomputable def cosetLine2ReductionWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  (cosetLuksBruteForceWith ϕ x y E).expand E.orbits.chain


theorem run_cosetChainWith_of_wrt [Fintype H] {ϕ : G →* H} (E : Line2Enum ϕ) {I : SIInstance Ω A}
    (hI : (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ) :
    (E.orbits.chain I).run = I.answer :=
  E.orbits.run_chain_eq _ hI.2


theorem run_cosetLine2ReductionWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    (cosetLine2ReductionWith ϕ x y E).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [cosetLine2ReductionWith,
    SIReduction.run_expand_of_calls
      (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
      (fun I hI => run_cosetChainWith_of_wrt E hI) _
      (calls_cosetLuksBruteForceWith_wrt ϕ x y E)]
  exact run_cosetLuksBruteForceWith ϕ x y E


theorem calls_length_cosetLine2ReductionWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    (cosetLine2ReductionWith ϕ x y E).calls.length ≤
      Fintype.card H * (orbitList (kerSubgroup ϕ)).length := by
  have h := SIReduction.calls_expand_length_le_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainWith_of_wrt E hI)
    (c := (orbitList (kerSubgroup ϕ)).length)
    (fun I _ => E.orbits.calls_length_chain I)
    (cosetLuksBruteForceWith ϕ x y E) (calls_cosetLuksBruteForceWith_wrt ϕ x y E)
  rw [cosetLine2ReductionWith]
  exact h.trans (Nat.mul_le_mul_right _ (calls_length_cosetLuksBruteForceWith ϕ x y E))


theorem calls_cosetLine2ReductionWith_window [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    ∀ J ∈ (cosetLine2ReductionWith ϕ x y E).calls, J.Δ ∈ orbitList (kerSubgroup ϕ) := by
  rw [cosetLine2ReductionWith]
  exact SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainWith_of_wrt E hI)
    (fun I _ => E.orbits.calls_chain_window I)
    (cosetLuksBruteForceWith ϕ x y E) (calls_cosetLuksBruteForceWith_wrt ϕ x y E)


theorem calls_cosetLine2ReductionWith_K [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    ∀ J ∈ (cosetLine2ReductionWith ϕ x y E).calls, J.K ⊆ (G : Set (Equiv.Perm Ω)) := by
  rw [cosetLine2ReductionWith]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainWith_of_wrt E hI)
    (fun I hI J hJ => ?_)
    (cosetLuksBruteForceWith ϕ x y E) (calls_cosetLuksBruteForceWith_wrt ϕ x y E)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hI
  refine subset_trans (E.orbits.calls_chain_K I J hJ) ?_
  rw [hσ]
  exact preimageSet_subset ϕ σ


theorem isCosetInstance_calls_cosetLine2ReductionWith [Fintype H] (ϕ : G →* H) (x y : Ω → A) (E : Line2Enum ϕ) :
    ∀ J ∈ (cosetLine2ReductionWith ϕ x y E).calls, IsCosetInstance G J := by
  rw [cosetLine2ReductionWith]
  refine SIReduction.mem_calls_expand_of_calls
    (P := fun I => (∃ σ : H, I.K = preimageSet ϕ σ) ∧ I.Δ = Set.univ)
    (fun I hI => run_cosetChainWith_of_wrt E hI)
    (fun I hI J hJ => ?_)
    (cosetLuksBruteForceWith ϕ x y E) (calls_cosetLuksBruteForceWith_wrt ϕ x y E)
  obtain ⟨⟨σ, hσ⟩, -⟩ := hI
  by_cases hr : σ ∈ ϕ.range
  · refine E.orbits.calls_chain_coset (kerSubgroup_le ϕ) I ?_ J hJ
    exact ⟨kerSubgroup ϕ, liftRep ϕ σ, le_rfl, (liftRep_mem ϕ hr).1,
      by rw [hσ]; exact preimageSet_eq_smul_kerSubgroup ϕ hr⟩
  · exfalso
    have hempty : I.K = (∅ : Set (Equiv.Perm Ω)) := by
      rw [hσ]; exact preimageSet_eq_empty ϕ hr
    rw [OrbitEnum.chain, hempty, calls_cosetChain_empty] at hJ
    exact absurd hJ (List.not_mem_nil)


end Babai
