import Workspace.Master.CosetForms
import Workspace.TopAction.TopAction2

/-! # The top-action rounds in coset form

The old reductions keep their bodies for the machine value interfaces. These
rounds ask for preimages and cosets with the original strings. Orbit orders are
parameters, with a permutation specification.
-/

universe u v w

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {G : Subgroup (Perm Ω)} {H : Type w} [Group H]

/-- Prop. 12.0.5, with the lifting calls in coset form. -/
noncomputable def cosetTopAction1 (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    SIReduction Ω A (Option (Set (Perm Ω))) :=
  (cosetLiftAll ϕ x y (1 :: S)).bind fun L =>
    .done (if ∀ s ∈ L, s.Nonempty then some (subcosetClosure (⋃ s ∈ L, s)) else none)

theorem run_cosetTopAction1_eq (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    (cosetTopAction1 ϕ x y S).run = (TopAction1Reduction ϕ x y S).run := by
  simp only [cosetTopAction1, TopAction1Reduction, SIReduction.run_bind,
    run_cosetLiftAll, run_liftAll]

theorem calls_cosetTopAction1 (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    (cosetTopAction1 ϕ x y S).calls =
      (1 :: S).map (fun σ => (⟨preimageSet ϕ σ, Set.univ, x, y⟩ : SIInstance Ω A)) := by
  simp only [cosetTopAction1, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, calls_cosetLiftAll]

/-- The orbit list is supplied by the caller, including its order. -/
structure OrbitEnum (N : Subgroup (Perm Ω)) where
  windows : List (Set Ω)
  spec : windows.Perm (orbitList N)

noncomputable def OrbitEnum.default (N : Subgroup (Perm Ω)) : OrbitEnum N :=
  ⟨orbitList N, List.Perm.refl _⟩

namespace OrbitEnum

variable {N : Subgroup (Perm Ω)} (E : OrbitEnum N)

theorem cover : (⋃ Δ ∈ E.windows, Δ) = Set.univ := by
  simpa only [E.spec.mem_iff] using iUnion_orbitList N

theorem invariant : ∀ Δ ∈ E.windows, IsInvariant N Δ :=
  fun _ h => isInvariant_of_mem_orbitList (E.spec.mem_iff.1 h)

theorem run_chain (I : SIInstance Ω A) (hΔ : I.Δ = Set.univ) :
    (cosetChain I.x I.y E.windows I.K).run = I.answer := by
  rw [run_cosetChain, E.cover, SIInstance.answer, hΔ]

end OrbitEnum

/-- Cor. 12.0.6, the alternating image case: three lifts followed by the kernel
orbit chain. Empty preimages make no calls. -/
noncomputable def cosetGiantA {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Perm Ω))) :=
  (cosetTopAction1 ψ x y (altGens m)).expand
    (fun J => cosetChain J.x J.y E.windows J.K)

theorem run_cosetGiantA_eq {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    (cosetGiantA ψ E x y).run = (giantAReduction ψ x y).run := by
  rw [cosetGiantA, SIReduction.run_expand_of_calls
    (P := fun J : SIInstance Ω A => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)]
  · rw [run_cosetTopAction1_eq, giantAReduction,
      SIReduction.run_expand_of_calls (fun J hJ => run_chainOverOrbits hJ.1 hJ.2)
        _ (calls_wrt_TopAction1 ψ x y)]
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl

theorem calls_length_cosetGiantA {m : ℕ} (hm : 3 ≤ m)
    (ψ : G →* alternatingGroup (Fin m)) (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    (cosetGiantA ψ E x y).calls.length ≤ 3 * (orbitList (kerSubgroup ψ)).length := by
  have hs : ∀ J ∈ (cosetTopAction1 ψ x y (altGens m)).calls, J.Δ = Set.univ := by
    intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl
  have hb := SIReduction.calls_expand_length_le_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := fun J => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)
    (fun J _ => (calls_cosetChain J.x J.y E.windows J.K).1) _ hs
  simpa only [cosetGiantA, calls_cosetTopAction1, List.length_map, List.length_cons,
    (altGens_spec m hm).1, E.spec.length_eq] using hb

theorem calls_cosetGiantA_window {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    ∀ J ∈ (cosetGiantA ψ E x y).calls, J.Δ ∈ E.windows := by
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := fun J => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)
    (fun J _ => (calls_cosetChain J.x J.y E.windows J.K).2) _ ?_
  intro J hJ
  rw [calls_cosetTopAction1, List.mem_map] at hJ
  obtain ⟨σ, _, rfl⟩ := hJ
  rfl

theorem isCosetInstance_calls_cosetGiantA {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    ∀ J ∈ (cosetGiantA ψ E x y).calls, IsCosetInstance G J := by
  let P := fun J : SIInstance Ω A => J.Δ = Set.univ ∧
    ∃ σ : alternatingGroup (Fin m), J.K = preimageSet ψ σ
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := P) (fun J hJ => E.run_chain J hJ.1) ?_ _ ?_
  · intro J hJ K hK
    dsimp only at hK
    obtain ⟨σ, hσ⟩ := hJ.2
    by_cases hs : σ ∈ ψ.range
    · exact isCosetInstance_calls_cosetChain (kerSubgroup_le ψ) J.x J.y E.windows J.K
        E.invariant ⟨_, liftRep ψ σ, le_rfl, (liftRep_mem ψ hs).1,
          hσ.trans (preimageSet_eq_smul_kerSubgroup ψ hs)⟩ K hK
    · rw [hσ, preimageSet_eq_empty ψ hs, cosetChain_empty_calls] at hK
      simp at hK
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    exact ⟨rfl, σ, rfl⟩

theorem cosetUnion_smul_left (σ : Perm Ω) (s t : Set (Perm Ω)) :
    cosetUnion (σ • s) t = σ • cosetUnion s t := by
  ext τ
  constructor
  · intro hτ
    obtain ⟨ρ, ⟨ν, hν, hρ⟩, μ, hμ, he⟩ := Set.mem_iUnion₂.1 hτ
    have hρ' : σ * ν = ρ := hρ
    have he' : ρ * μ = τ := he
    refine ⟨ν * μ, Set.mem_iUnion₂.2 ⟨ν, hν, μ, hμ, rfl⟩, ?_⟩
    change σ * (ν * μ) = τ
    rw [← mul_assoc, hρ', he']
  · rintro ⟨ρ, hρ, he⟩
    obtain ⟨ν, hν, μ, hμ, hρ⟩ := Set.mem_iUnion₂.1 hρ
    have hρ' : ν * μ = ρ := hρ
    have he' : σ * ρ = τ := he
    refine Set.mem_iUnion₂.2 ⟨σ * ν, ⟨ν, hν, rfl⟩, μ, hμ, ?_⟩
    change (σ * ν) * μ = τ
    rw [mul_assoc, hρ', he']

/-- The same kernel orbit order serves the alternating preimage. -/
noncomputable def OrbitEnum.alt {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) : OrbitEnum (kerSubgroup (altHom ϕ)) :=
  ⟨E.windows, by rw [kerSubgroup_altHom]; exact E.spec⟩

/-- Cor. 12.0.8: compute the alternating automorphisms, then test the even and
odd kernel cosets. The odd branch keeps the original target string. -/
noncomputable def cosetTopAction3 {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Perm Ω))) :=
  (cosetGiantA (altHom ϕ) (E.alt ϕ) x x).bind fun r0 =>
    if r0 = none then .done none else
      (cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).bind fun s1 =>
        if ϕ.range ≤ alternatingGroup (Fin m) then
          .done (some (cosetUnion s1 (r0.getD ∅)))
        else
          (cosetChain x y E.windows ((oddRep ϕ) • (kerSubgroup ϕ : Set (Perm Ω)))).bind
            fun s2 => .done (some (cosetUnion s1 (r0.getD ∅) ∪ cosetUnion s2 (r0.getD ∅)))

theorem run_cosetTopAction3_eq {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    (cosetTopAction3 ϕ E x y).run = (topAction3Reduction ϕ x y).run := by
  rw [cosetTopAction3, topAction3Reduction, SIReduction.run_bind, SIReduction.run_bind,
    run_cosetGiantA_eq]
  by_cases hz : (giantAReduction (altHom ϕ) x x).run = none
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz, SIReduction.run_bind, SIReduction.run_bind,
      run_cosetChain, E.cover, wIso_univ, run_nOrbitReduction]
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, SIReduction.run_bind, SIReduction.run_bind,
        run_cosetChain, E.cover, wIso_smul, wIso_univ, run_nOrbitReduction,
        SIReduction.run_done, SIReduction.run_done, cosetUnion_smul_left]

theorem calls_length_cosetTopAction3 {m : ℕ} (hm : 3 ≤ m)
    (ϕ : G →* Perm (Fin m)) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    (cosetTopAction3 ϕ E x y).calls.length ≤ 6 * orbCount ϕ := by
  have h0 := calls_length_cosetGiantA hm (altHom ϕ) (E.alt ϕ) x x
  have hk : (orbitList (kerSubgroup ϕ)).length = orbCount ϕ := length_orbitList _
  rw [orbitList_altHom, hk] at h0
  have h1 := (calls_cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).1
  have h2 := (calls_cosetChain x y E.windows ((oddRep ϕ) • (kerSubgroup ϕ : Set (Perm Ω)))).1
  rw [E.spec.length_eq, hk] at h1 h2
  rw [cosetTopAction3, SIReduction.calls_bind, List.length_append]
  split
  · simp only [SIReduction.calls_done, List.length_nil]
    omega
  · rw [SIReduction.calls_bind, List.length_append]
    split
    · simp only [SIReduction.calls_done, List.length_nil]
      omega
    · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
      omega

theorem calls_cosetTopAction3_window {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3 ϕ E x y).calls, J.Δ ∈ E.windows := by
  rw [cosetTopAction3, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with hJ | hJ
  · exact calls_cosetGiantA_window (altHom ϕ) (E.alt ϕ) x x J hJ
  · split at hJ
    · simp at hJ
    · rw [SIReduction.calls_bind] at hJ
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact (calls_cosetChain _ _ _ _).2 J hJ
      · split at hJ
        · simp at hJ
        · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
          exact (calls_cosetChain _ _ _ _).2 J hJ

theorem isCosetInstance_calls_cosetTopAction3 {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3 ϕ E x y).calls, IsCosetInstance G J := by
  rw [cosetTopAction3, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨N, σ, hN, hσ, he, hi⟩ :=
      isCosetInstance_calls_cosetGiantA (altHom ϕ) (E.alt ϕ) x x J hJ
    exact ⟨N, σ, hN.trans (preimageAlt_le ϕ), preimageAlt_le ϕ hσ, he, hi⟩
  · split at hJ
    · simp at hJ
    · rw [SIReduction.calls_bind] at hJ
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact isCosetInstance_calls_cosetChain (kerSubgroup_le ϕ) x y E.windows _ E.invariant
          ⟨_, 1, le_rfl, G.one_mem, by simp⟩ J hJ
      · split at hJ
        · simp at hJ
        · next hr =>
            simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
            exact isCosetInstance_calls_cosetChain (kerSubgroup_le ϕ) x y E.windows _ E.invariant
              ⟨_, oddRep ϕ, le_rfl, (oddRep_spec ϕ (exists_odd_of_not_range_le hr)).1, rfl⟩ J hJ

theorem calls_cosetTopAction3_K {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3 ϕ E x y).calls, J.K ⊆ (G : Set (Perm Ω)) :=
  fun J hJ => (isCosetInstance_calls_cosetTopAction3 ϕ E x y J hJ).K_subset

theorem cosetCorollary_12_0_8 {m : ℕ} (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Fintype.card Ω ∧
      (cosetTopAction3 ϕ E x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (cosetTopAction3 ϕ E x y).calls,
        orbCount ϕ * I.windowSize ≤ Fintype.card Ω) ∧
      (cosetTopAction3 ϕ E x y).run =
        if MapsOntoGiant ϕ x then some (strIso (G : Set (Perm Ω)) x y) else none := by
  obtain ⟨hmk, hkn, hlen⟩ := orbCount_spec hG ϕ hϕ hm
  have hm3 : 3 ≤ m := by have := hm.eight_lt; omega
  refine ⟨hmk, hkn, calls_length_cosetTopAction3 hm3 ϕ E x y, ?_, ?_⟩
  · intro I hI
    obtain ⟨u, hu⟩ := mem_orbitList (E.spec.mem_iff.1
      (calls_cosetTopAction3_window ϕ E x y I hI))
    rw [SIInstance.windowSize, hu, mul_comm, hlen u]
  · rw [run_cosetTopAction3_eq, run_topAction3Reduction hm3]

/-! ### Supplied ordered generators

Generation determines the returned set, but not the ordered lifting calls.
-/

/-- Cor. 12.0.6, the alternating image case: three lifts followed by the kernel
orbit chain. Empty preimages make no calls. -/
noncomputable def cosetGiantAWith {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Perm Ω))) :=
  (cosetTopAction1 ψ x y S).expand
    (fun J => cosetChain J.x J.y E.windows J.K)

/-- Cor. 12.0.6, §12: every generating list gives the stated answer. -/
theorem run_cosetGiantAWith {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    (cosetGiantAWith ψ S E x y).run =
      if MapsOnto ψ x y then some (strIso (G : Set (Perm Ω)) x y) else none := by
  rw [cosetGiantAWith, SIReduction.run_expand_of_calls
    (P := fun J : SIInstance Ω A => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)]
  · rw [run_cosetTopAction1_eq, run_TopAction1Reduction ψ x y S hS]
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl

theorem run_cosetGiantAWith_eq {m : ℕ} (hm : 3 ≤ m)
    (ψ : G →* alternatingGroup (Fin m)) (S : List (alternatingGroup (Fin m)))
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    (cosetGiantAWith ψ S E x y).run = (giantAReduction ψ x y).run := by
  rw [run_cosetGiantAWith ψ S hS, run_giantAReduction hm]

theorem calls_length_cosetGiantAWith {m : ℕ}
    (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m))) (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    (cosetGiantAWith ψ S E x y).calls.length ≤ (S.length + 1) * (orbitList (kerSubgroup ψ)).length := by
  have hs : ∀ J ∈ (cosetTopAction1 ψ x y S).calls, J.Δ = Set.univ := by
    intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl
  have hb := SIReduction.calls_expand_length_le_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := fun J => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)
    (fun J _ => (calls_cosetChain J.x J.y E.windows J.K).1) _ hs
  simpa only [cosetGiantAWith, calls_cosetTopAction1, List.length_map, List.length_cons,
    E.spec.length_eq] using hb

theorem calls_cosetGiantAWith_window {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    ∀ J ∈ (cosetGiantAWith ψ S E x y).calls, J.Δ ∈ E.windows := by
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := fun J => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)
    (fun J _ => (calls_cosetChain J.x J.y E.windows J.K).2) _ ?_
  intro J hJ
  rw [calls_cosetTopAction1, List.mem_map] at hJ
  obtain ⟨σ, _, rfl⟩ := hJ
  rfl

theorem isCosetInstance_calls_cosetGiantAWith {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (S : List (alternatingGroup (Fin m)))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    ∀ J ∈ (cosetGiantAWith ψ S E x y).calls, IsCosetInstance G J := by
  let P := fun J : SIInstance Ω A => J.Δ = Set.univ ∧
    ∃ σ : alternatingGroup (Fin m), J.K = preimageSet ψ σ
  refine SIReduction.mem_calls_expand_of_calls
    (f := fun J : SIInstance Ω A => cosetChain J.x J.y E.windows J.K)
    (P := P) (fun J hJ => E.run_chain J hJ.1) ?_ _ ?_
  · intro J hJ K hK
    dsimp only at hK
    obtain ⟨σ, hσ⟩ := hJ.2
    by_cases hs : σ ∈ ψ.range
    · exact isCosetInstance_calls_cosetChain (kerSubgroup_le ψ) J.x J.y E.windows J.K
        E.invariant ⟨_, liftRep ψ σ, le_rfl, (liftRep_mem ψ hs).1,
          hσ.trans (preimageSet_eq_smul_kerSubgroup ψ hs)⟩ K hK
    · rw [hσ, preimageSet_eq_empty ψ hs, cosetChain_empty_calls] at hK
      simp at hK
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    exact ⟨rfl, σ, rfl⟩

/-- Cor. 12.0.8, §12: the representative used only when the top image contains
an odd permutation. The specification is needed only in that branch. -/
structure TopActionOdd {m : ℕ} (ϕ : G →* Perm (Fin m)) where
  representative : Perm Ω
  spec : ¬ ϕ.range ≤ alternatingGroup (Fin m) →
    ∃ h : representative ∈ G, ϕ ⟨representative, h⟩ ∉ alternatingGroup (Fin m)

noncomputable def TopActionOdd.default {m : ℕ} (ϕ : G →* Perm (Fin m)) :
    TopActionOdd ϕ :=
  ⟨oddRep ϕ, fun hr => oddRep_spec ϕ (exists_odd_of_not_range_le hr)⟩

/-- Cor. 12.0.8: compute the alternating automorphisms, then test the even and
odd kernel cosets. The odd branch keeps the original target string. -/
noncomputable def cosetTopAction3With {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    SIReduction Ω A (Option (Set (Perm Ω))) :=
  (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).bind fun r0 =>
    if r0 = none then .done none else
      (cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).bind fun s1 =>
        if ϕ.range ≤ alternatingGroup (Fin m) then
          .done (some (cosetUnion s1 (r0.getD ∅)))
        else
          (cosetChain x y E.windows (O.representative • (kerSubgroup ϕ : Set (Perm Ω)))).bind
            fun s2 => .done (some (cosetUnion s1 (r0.getD ∅) ∪ cosetUnion s2 (r0.getD ∅)))

/-- Cor. 12.0.8, §12: the corrected proof works for every supplied ordered
pair and every odd-image representative. -/
theorem run_cosetTopAction3With {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    (cosetTopAction3With ϕ S O E x y).run =
      if MapsOntoGiant ϕ x then some (strIso (G : Set (Perm Ω)) x y) else none := by
  rw [cosetTopAction3With, SIReduction.run_bind, run_cosetGiantAWith _ S hS]
  by_cases hA : MapsOntoGiant ϕ x
  · rw [if_pos ((mapsOnto_altHom_self_iff ϕ x).2 hA), if_pos hA,
      if_neg (by simp : ¬ (some (strIso (preimageAlt ϕ : Set (Perm Ω)) x x)) = none),
      SIReduction.run_bind, run_cosetChain, E.cover, wIso_univ, Option.getD_some]
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · rw [if_pos hr, SIReduction.run_done, cosetUnion_strIso_ker ϕ hA,
        preimageAlt_eq_of_range_le hr]
    · obtain ⟨hσG, hσodd⟩ := O.spec hr
      rw [if_neg hr, SIReduction.run_bind, SIReduction.run_done, run_cosetChain,
        E.cover, wIso_smul, wIso_univ, cosetUnion_smul_left,
        cosetUnion_strIso_ker ϕ hA, cosetUnion_strIso_ker ϕ hA,
        ← strIso_descent ϕ hσG hσodd x y]
  · rw [if_neg (fun hc => hA ((mapsOnto_altHom_self_iff ϕ x).1 hc)), if_pos rfl,
      SIReduction.run_done, if_neg hA]

theorem run_cosetTopAction3With_eq {m : ℕ} (hm : 3 ≤ m) (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    (cosetTopAction3With ϕ S O E x y).run = (topAction3Reduction ϕ x y).run := by
  rw [run_cosetTopAction3With ϕ S O hS, run_topAction3Reduction hm]

theorem calls_length_cosetTopAction3With {m : ℕ}
    (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    (cosetTopAction3With ϕ S O E x y).calls.length ≤ (S.length + 3) * orbCount ϕ := by
  have h0 := calls_length_cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x
  have hk : (orbitList (kerSubgroup ϕ)).length = orbCount ϕ := length_orbitList _
  rw [orbitList_altHom, hk] at h0
  have h1 := (calls_cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm Ω))).1
  have h2 := (calls_cosetChain x y E.windows (O.representative • (kerSubgroup ϕ : Set (Perm Ω)))).1
  rw [E.spec.length_eq, hk] at h1 h2
  rw [cosetTopAction3With, SIReduction.calls_bind, List.length_append]
  split
  · simp only [SIReduction.calls_done, List.length_nil]
    nlinarith
  · rw [SIReduction.calls_bind, List.length_append]
    split
    · simp only [SIReduction.calls_done, List.length_nil]
      nlinarith
    · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]
      nlinarith

theorem calls_cosetTopAction3With_window {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3With ϕ S O E x y).calls, J.Δ ∈ E.windows := by
  rw [cosetTopAction3With, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with hJ | hJ
  · exact calls_cosetGiantAWith_window (altHom ϕ) S (E.alt ϕ) x x J hJ
  · split at hJ
    · simp at hJ
    · rw [SIReduction.calls_bind] at hJ
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact (calls_cosetChain _ _ _ _).2 J hJ
      · split at hJ
        · simp at hJ
        · simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
          exact (calls_cosetChain _ _ _ _).2 J hJ

theorem isCosetInstance_calls_cosetTopAction3With {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3With ϕ S O E x y).calls, IsCosetInstance G J := by
  rw [cosetTopAction3With, SIReduction.calls_bind]
  intro J hJ
  rcases List.mem_append.1 hJ with hJ | hJ
  · obtain ⟨N, σ, hN, hσ, he, hi⟩ :=
      isCosetInstance_calls_cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x J hJ
    exact ⟨N, σ, hN.trans (preimageAlt_le ϕ), preimageAlt_le ϕ hσ, he, hi⟩
  · split at hJ
    · simp at hJ
    · rw [SIReduction.calls_bind] at hJ
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact isCosetInstance_calls_cosetChain (kerSubgroup_le ϕ) x y E.windows _ E.invariant
          ⟨_, 1, le_rfl, G.one_mem, by simp⟩ J hJ
      · split at hJ
        · simp at hJ
        · next hr =>
            simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil] at hJ
            exact isCosetInstance_calls_cosetChain (kerSubgroup_le ϕ) x y E.windows _ E.invariant
              ⟨_, O.representative, le_rfl, (O.spec hr).1, rfl⟩ J hJ

theorem calls_cosetTopAction3With_K {m : ℕ} (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    ∀ J ∈ (cosetTopAction3With ϕ S O E x y).calls, J.K ⊆ (G : Set (Perm Ω)) :=
  fun J hJ => (isCosetInstance_calls_cosetTopAction3With ϕ S O E x y J hJ).K_subset

/-- Cor. 12.0.8, §12: correctness and the `6k` bound for a supplied generating pair. -/
theorem cosetCorollary_12_0_8_with {m : ℕ} (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ)
    (hS : S.length = 2 ∧ Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (hϕ : IsGiantRep ϕ) (hm : LargeK m (Nat.card Ω))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    m ≤ orbCount ϕ ∧ orbCount ϕ ≤ Fintype.card Ω ∧
      (cosetTopAction3With ϕ S O E x y).calls.length ≤ 6 * orbCount ϕ ∧
      (∀ I ∈ (cosetTopAction3With ϕ S O E x y).calls,
        orbCount ϕ * I.windowSize ≤ Fintype.card Ω) ∧
      (cosetTopAction3With ϕ S O E x y).run =
        if MapsOntoGiant ϕ x then some (strIso (G : Set (Perm Ω)) x y) else none := by
  obtain ⟨hmk, hkn, hlen⟩ := orbCount_spec hG ϕ hϕ hm
  have hm3 : 3 ≤ m := by have := hm.eight_lt; omega
  have hcalls : (cosetTopAction3With ϕ S O E x y).calls.length ≤ 6 * orbCount ϕ := by
    have hb := calls_length_cosetTopAction3With ϕ S O E x y
    rw [hS.1] at hb
    omega
  refine ⟨hmk, hkn, hcalls, ?_, ?_⟩
  · intro I hI
    obtain ⟨u, hu⟩ := mem_orbitList (E.spec.mem_iff.1
      (calls_cosetTopAction3With_window ϕ S O E x y I hI))
    rw [SIInstance.windowSize, hu, mul_comm, hlen u]
  · rw [run_cosetTopAction3With_eq hm3 ϕ S O hS.2, run_topAction3Reduction hm3]

/-- Supplying the old ordered list gives exactly the old tree, at every answer. -/
theorem cosetGiantAWith_default {m : ℕ} (ψ : G →* alternatingGroup (Fin m))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → A) :
    cosetGiantAWith ψ (altGens m) E x y = cosetGiantA ψ E x y := rfl

theorem cosetTopAction3With_default {m : ℕ} (ϕ : G →* Perm (Fin m))
    (E : OrbitEnum (kerSubgroup ϕ)) (x y : Ω → A) :
    cosetTopAction3With ϕ (altGens m) (.default ϕ) E x y = cosetTopAction3 ϕ E x y := rfl

end Babai
