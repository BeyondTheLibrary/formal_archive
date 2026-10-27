import Workspace.LocalCertificates.StrongAggregate
import Workspace.Master.CosetCompose

/-! # Alignment for strong descent in Sec. 13

The kernel preserves each listed window. A coset representative need only belong to
`G`, which can move that window. We keep these two groups separate in the chain lemma.
The final round aligns its two phases as in Remark 11.1.4.
-/

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

universe w

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω]
  {G N : Subgroup (Perm Ω)}

theorem IsCosetInstance.ambient_mono {I : SIInstance Ω Λ}
    (h : IsCosetInstance N I) (hNG : N ≤ G) : IsCosetInstance G I := by
  obtain ⟨M, σ, hM, hσ, hK, hΔ⟩ := h
  exact ⟨M, σ, hM.trans hNG, hNG hσ, hK, hΔ⟩

/-- Remark 11.1.5(ii), keeping the window-preserving group separate from the ambient group. -/
theorem wIso_smul_subgroup_of_invariant {M : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hMN : M ≤ N) (hNG : N ≤ G) (hΔ : IsInvariant N Δ) (x y : Ω → Λ)
    {σ : Perm Ω} (hσ : σ ∈ G) :
    wIso Δ (σ • (M : Set (Perm Ω))) x y = ∅ ∨
      ∃ (M' : Subgroup (Perm Ω)) (ρ : Perm Ω), M' ≤ N ∧ ρ ∈ G ∧
        wIso Δ (σ • (M : Set (Perm Ω))) x y = ρ • (M' : Set (Perm Ω)) := by
  rcases Set.eq_empty_or_nonempty (wIso Δ (σ • (M : Set (Perm Ω))) x y) with he | ⟨ρ, hρ⟩
  · exact Or.inl he
  · refine Or.inr ⟨M ⊓ autWindow N Δ x, ρ, inf_le_left.trans hMN, ?_, ?_⟩
    · obtain ⟨μ, hμ, rfl⟩ := hρ.1
      exact G.mul_mem hσ (hNG (hMN hμ))
    · rw [wIso_eq_smul_wAut (fun τ hτ => hΔ τ (hMN hτ)) σ hρ,
        ← wAut_eq_inf hMN hΔ x]

/-- Every call is a coset of a subgroup of `N`, even when its representative lies in
`G`. This is `isCosetInstance_calls_cosetChain` in its two-group form (Master round 26). -/
theorem isCosetInstance_calls_cosetChain_over (hNG : N ≤ G) (x y : Ω → Λ) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)),
      (∀ Δ ∈ Δs, IsInvariant N Δ) →
      (∃ (M : Subgroup (Perm Ω)) (σ : Perm Ω), M ≤ N ∧ σ ∈ G ∧
        C = σ • (M : Set (Perm Ω))) →
      ∀ J ∈ (cosetChain x y Δs C).calls, IsCosetInstance G J :=
  isCosetInstance_calls_cosetChain hNG x y

theorem isCosetInstance_calls_strongDescent (hNG : N ≤ G) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω))
    (hinv : ∀ Δ ∈ Δs, IsInvariant N Δ) (hL : ∀ σ ∈ L, σ ∈ G)
    {I : SIInstance Ω Λ} (hI : I ∈ (strongDescent N x y L Δs).calls) :
    IsCosetInstance G I := by
  rw [calls_strongDescent, List.mem_flatMap] at hI
  obtain ⟨σ, hσ, hI⟩ := hI
  exact isCosetInstance_calls_cosetChain_over hNG x y Δs _ hinv
    ⟨N, σ, le_rfl, hL σ hσ, rfl⟩ I hI

/-- A listed representative belongs to the union of its cosets, since `1 ∈ N`. -/
theorem strongRep_mem_cover (N : Subgroup (Perm Ω)) (L : List (Perm Ω))
    {C : Set (Perm Ω)} (hc : C = ⋃ σ ∈ L, σ • (N : Set (Perm Ω)))
    {σ : Perm Ω} (hσ : σ ∈ L) : σ ∈ C := by
  rw [hc]
  exact Set.mem_iUnion₂.2 ⟨σ, hσ, ⟨1, N.one_mem, by simp⟩⟩

variable [Fintype Γ] [DecidableEq Γ] {ϕ : G →* Perm Γ} {x y : Ω → Λ} {T : Set Γ}

theorem isCosetInstance_calls_recomputeStrong (s : Stage ϕ x T)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) (hc : StrongStageCover s L Δs)
    (hinv : ∀ Δ ∈ Δs, IsInvariant (kerN s) Δ)
    {I : SIInstance Ω Λ} (hI : I ∈ (recomputeStrong s L Δs).calls) :
    IsCosetInstance G I :=
  isCosetInstance_calls_strongDescent (kerN_le_ambient s) x x L Δs hinv
    (fun σ hσ => stage_H_le_ambient s (strongRep_mem_cover _ _ hc.cosets hσ)) hI

theorem isCosetInstance_calls_localCertStrong (L : ℕ → List (Perm Ω))
    (Δs : ℕ → List (Set Ω))
    (hc : ∀ i < haltIndex ϕ x T, StrongStageCover (stages ϕ x T i) (L i) (Δs i))
    (hinv : ∀ i < haltIndex ϕ x T, ∀ Δ ∈ Δs i, IsInvariant (kerN (stages ϕ x T i)) Δ)
    {I : SIInstance Ω Λ} (hI : I ∈ (localCertStrong ϕ x T L Δs).calls) :
    IsCosetInstance G I := by
  rw [calls_localCertStrong] at hI
  obtain ⟨i, hi, hI⟩ := mem_calls_loopStrong L Δs _ I hI
  exact isCosetInstance_calls_recomputeStrong _ _ _ (hc i hi) (hinv i hi) hI

theorem isCosetInstance_calls_compareStrong {T' : Set Γ} (σ : Option (Perm Ω))
    (E : StrongPairEnum Ω) (hσ : StrongTransporterSpec ϕ T T' σ)
    (hc : ∀ ρ, σ = some ρ → StrongPairCover ϕ x y T ρ E)
    (hinv : ∀ i < haltIndex ϕ x T, ∀ Δ ∈ E.windows i,
      IsInvariant (kerN (stages ϕ x T i)) Δ)
    {I : SIInstance Ω Λ} (hI : I ∈ (compareStrong ϕ x T y σ E).calls) :
    IsCosetInstance G I := by
  cases σ with
  | none => simp [compareStrong] at hI
  | some ρ =>
    obtain ⟨hρ, _⟩ := hσ
    rw [compareStrong, calls_pairedComparisonStrong_eq] at hI
    obtain ⟨i, hi, hI⟩ := mem_calls_pairedLoopStrong ρ E _ hI
    rcases hI with hI | hI
    · exact isCosetInstance_calls_recomputeStrong _ _ _ ((hc ρ rfl).source i hi) (hinv i hi) hI
    · exact isCosetInstance_calls_strongDescent (kerN_le_ambient _) x y _ _ (hinv i hi)
        (fun τ hτ => pairedQ_subset_ambient y hρ i
          (strongRep_mem_cover _ _ ((hc ρ rfl).comparison i hi) hτ)) hI

theorem isCosetInstance_calls_certPhaseStrong (E : AggEnum Ω Γ)
    (hc : E.Cover ϕ x y) (hinv : E.Invariant ϕ x y)
    {I : SIInstance Ω Λ} (hI : I ∈ (certPhaseStrong ϕ x y E).calls) :
    IsCosetInstance G I := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  obtain ⟨b, T, hT, rfl⟩ := (mem_certRunsStrong E).1 hS
  rw [calls_certRunStrong] at hI
  exact isCosetInstance_calls_localCertStrong _ _ (hc.cert b T hT) (hinv.cert b T hT) hI

theorem isCosetInstance_calls_comparePhaseStrong (E : AggEnum Ω Γ)
    (hc : E.Cover ϕ x y) (hinv : E.Invariant ϕ x y)
    {I : SIInstance Ω Λ} (hI : I ∈ (comparePhaseStrong ϕ x y E).calls) :
    IsCosetInstance G I := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  obtain ⟨b, T, hT, T', hT', rfl⟩ := (mem_compareRunsStrong E).1 hS
  exact isCosetInstance_calls_compareStrong _ _ (hc.transporter b T hT T' hT')
    (hc.pair b T hT T' hT') (hinv.pair b T hT T' hT') hI

/-- All calls are coset instances if the continuation has that property. -/
theorem isCosetInstance_calls_aggregateRoundStrong (E : AggEnum Ω Γ)
    (hc : E.Cover ϕ x y) (hinv : E.Invariant ϕ x y) {α : Type w}
    (R : SIReduction Ω Λ α) (hR : ∀ I ∈ R.calls, IsCosetInstance G I)
    {I : SIInstance Ω Λ} (hI : I ∈ (aggregateRoundStrong ϕ x y E R).calls) :
    IsCosetInstance G I := by
  rw [calls_aggregateRoundStrong, List.mem_append, List.mem_append] at hI
  rcases hI with hI | hI | hI
  · exact isCosetInstance_calls_certPhaseStrong E hc hinv hI
  · exact isCosetInstance_calls_comparePhaseStrong E hc hinv hI
  · exact hR I hI

/-- Sec. 13.2 and Remark 11.1.4: align the two strong-descent phases. -/
noncomputable def alignedAggregateRoundStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ)
    (E : AggEnum Ω Γ) {α : Type w} (R : SIReduction Ω Λ α) : SIReduction Ω Λ α :=
  (certPhaseStrong ϕ x y E).alignCalls.bind fun _ =>
    (comparePhaseStrong ϕ x y E).alignCalls.bind fun _ => R

/-- Sec. 13.2 and Remark 11.1.4: when the continuation is aligned, the complete
strong round is the alignment of its coset form. This is an equality of trees. -/
theorem alignedAggregateRoundStrong_eq_alignRed (E : AggEnum Ω Γ)
    (I : SIInstance Ω Λ) (R : SIReduction Ω Λ (Set (Perm Ω))) :
    alignedAggregateRoundStrong ϕ x y E (SIReduction.alignRed I R) =
      SIReduction.alignRed I (aggregateRoundStrong ϕ x y E R) := by
  simp only [alignedAggregateRoundStrong, aggregateRoundStrong, SIReduction.alignRed_bind]

@[simp] theorem run_alignedAggregateRoundStrong (E : AggEnum Ω Γ) {α : Type w}
    (R : SIReduction Ω Λ α) : (alignedAggregateRoundStrong ϕ x y E R).run = R.run := by
  simp [alignedAggregateRoundStrong]

theorem calls_alignedAggregateRoundStrong (E : AggEnum Ω Γ) {α : Type w}
    (R : SIReduction Ω Λ α) :
    (alignedAggregateRoundStrong ϕ x y E R).calls = (certPhaseStrong ϕ x y E).calls.map alignInst ++
      ((comparePhaseStrong ϕ x y E).calls.map alignInst ++ R.calls) := by
  simp [alignedAggregateRoundStrong, calls_alignCalls]

/-- The new phase calls are group instances in `G`. Calls of the continuation are separate. -/
theorem mem_calls_alignedAggregateRoundStrong {t : ℕ} (E : AggEnum Ω Γ)
    (h : E.Spec ϕ x y t) (h5 : 5 ≤ t) {α : Type w} (R : SIReduction Ω Λ α)
    {I : SIInstance Ω Λ} (hI : I ∈ (alignedAggregateRoundStrong ϕ x y E R).calls) :
    (I.K ⊆ (G : Set (Perm Ω)) ∧ IsGroupInstance I ∧ t * I.Δ.ncard ≤ Nat.card Ω) ∨
      I ∈ R.calls := by
  rw [calls_alignedAggregateRoundStrong, List.mem_append, List.mem_append] at hI
  rcases hI with hI | hI | hI
  · obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
    have hc := isCosetInstance_calls_certPhaseStrong E h.toCover h.toBound.invariant hJ
    exact Or.inl ⟨K_alignInst_subset hc, isGroupInstance_alignInst hc,
      window_calls_certPhaseStrong E h.toBound h5 (I := J) hJ⟩
  · obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hI
    have hc := isCosetInstance_calls_comparePhaseStrong E h.toCover h.toBound.invariant hJ
    exact Or.inl ⟨K_alignInst_subset hc, isGroupInstance_alignInst hc,
      window_calls_comparePhaseStrong E h.toBound h5 (I := J) hJ⟩
  · exact Or.inr hI

theorem isGroupInstance_calls_alignedAggregateRoundStrong {t : ℕ} (E : AggEnum Ω Γ)
    (h : E.Spec ϕ x y t) (h5 : 5 ≤ t) {α : Type w} (R : SIReduction Ω Λ α)
    (hR : ∀ I ∈ R.calls, IsGroupInstance I) :
    ∀ I ∈ (alignedAggregateRoundStrong ϕ x y E R).calls, IsGroupInstance I := by
  intro I hI
  rcases mem_calls_alignedAggregateRoundStrong E h h5 R hI with ⟨_, hI, _⟩ | hI
  · exact hI
  · exact hR I hI

theorem calls_length_alignedAggregateRoundStrong {t : ℕ} (E : AggEnum Ω Γ)
    (h : E.Bound ϕ x y t) (h5 : 5 ≤ t) {α : Type w} (R : SIReduction Ω Λ α) :
    (alignedAggregateRoundStrong ϕ x y E R).calls.length ≤
      R.calls.length + aggregateRoundCost (Fintype.card Γ) t (Nat.card Ω) := by
  rw [calls_alignedAggregateRoundStrong, List.length_append, List.length_append,
    List.length_map, List.length_map]
  have := calls_length_strong_phases E h h5
  omega

end Babai
