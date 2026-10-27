import Workspace.LocalCertificates.StrongDescent
import Workspace.LocalCertificates.CompareCanonical

/-! # Strong descent for the comparison in Sec. 13.1

The initial transporter and all coset and window lists are parameters. The comparison
list covers the current `Q`. When `Q` is nonempty, line 04c0 and Eq. (69) give such a
list by translating the source list. This choice is made only in the existence proof.
-/

namespace Babai

open MulAction Equiv
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {x y : Ω → Λ} {T T' : Set Γ}

/-- List inputs of one paired run. The two coset lists share the source kernel windows. -/
structure StrongPairEnum (Ω : Type*) where
  reps : ℕ → List (Perm Ω)
  compareReps : ℕ → List (Perm Ω)
  windows : ℕ → List (Set Ω)

/-- The two cover equations of lines 04e1 and 04e2, up to the source halt index. -/
structure StrongPairCover (ϕ : G →* Perm Γ) (x y : Ω → Λ) (T : Set Γ)
    (σ : Perm Ω) (E : StrongPairEnum Ω) : Prop where
  source : ∀ i < haltIndex ϕ x T,
    StrongStageCover (stages ϕ x T i) (E.reps i) (E.windows i)
  comparison : ∀ i < haltIndex ϕ x T, pairedQ ϕ x y T σ i =
    ⋃ ρ ∈ E.compareReps i, ρ • (kerN (stages ϕ x T i) : Set (Perm Ω))

/-- The size and orbit hypotheses for Proposition 13.1.11. -/
structure StrongPairBound (ϕ : G →* Perm Γ) (x : Ω → Λ) (T : Set Γ)
    (E : StrongPairEnum Ω) : Prop where
  source : ∀ i < haltIndex ϕ x T,
    StrongStageBound (stages ϕ x T i) (E.reps i) (E.windows i)
  comparison : ∀ i < haltIndex ϕ x T, (E.compareReps i).length ≤ Nat.factorial T.ncard

variable (ϕ x T y)

/-- Proposition 13.1.11, the paired loop. A rejected comparison stops later calls.
Each live round computes both sets from strong-descent answers. -/
noncomputable def pairedLoopStrong (σ : Perm Ω) (E : StrongPairEnum Ω) :
    ℕ → SIReduction Ω Λ (Option (Set Ω × Set (Perm Ω) × Set (Perm Ω)))
  | 0 => .done (comparisonState ∅ (bigGT ϕ T : Set (Perm Ω))
      (σ • (bigGT ϕ T : Set (Perm Ω))))
  | i + 1 => (pairedLoopStrong σ E i).bind fun
      | none => .done none
      | some p =>
        (recomputeStrong (stages ϕ x T i) (E.reps i) (E.windows i)).bind fun H =>
        (strongDescent (kerN (stages ϕ x T i)) x y
          (E.compareReps i) (E.windows i)).bind fun Q =>
          .done (comparisonState (affOf ϕ T p.2.1) (p.2.1 ∩ H) Q)

/-- Proposition 13.1.11, comparison with a supplied initial transporter. -/
noncomputable def pairedComparisonStrong (σ : Perm Ω) (E : StrongPairEnum Ω) :
    SIReduction Ω Λ (Set (Perm Ω)) :=
  (pairedLoopStrong ϕ x y T σ E (haltIndex ϕ x T)).bind fun p =>
    .done (p.elim ∅ fun q => q.2.2)

variable {ϕ x T y}

theorem run_pairedLoopStrong (σ : Perm Ω) (E : StrongPairEnum Ω)
    (h : StrongPairCover ϕ x y T σ E) (i : ℕ) (hi : i ≤ haltIndex ϕ x T) :
    (pairedLoopStrong ϕ x y T σ E i).run =
      comparisonState (stages ϕ x T i).W ((stages ϕ x T i).H : Set (Perm Ω))
        (pairedQ ϕ x y T σ i) := by
  induction i with
  | zero =>
    have hQ : pairedQ ϕ x y T σ 0 = σ • (bigGT ϕ T : Set (Perm Ω)) := by
      ext ρ
      simp [pairedQ, stages, Stage.init, wIso]
    rw [hQ]
    rfl
  | succ i ih =>
    rw [pairedLoopStrong, SIReduction.run_bind, ih (by omega)]
    by_cases hQ : (pairedQ ϕ x y T σ i).Nonempty
    · rw [comparisonState, if_pos hQ]
      simp only [SIReduction.run_bind, SIReduction.run_done]
      rw [run_recomputeStrong _ _ _ (h.source i (by omega)), run_strongDescent,
        (h.source i (by omega)).windows, ← h.comparison i (by omega),
        ← pairedQ_succ, affOf_coe,
        Set.inter_eq_self_of_subset_right (stages ϕ x T i).step_H_le]
      rfl
    · rw [comparisonState, if_neg hQ, pairedQ_succ_empty y σ i hQ]
      simp [comparisonState]

/-- Proposition 13.1.11. Any transporter carrying `T` to `T'` gives the same value,
by `pairedQ_out_eq_compareIso`; no agreement with a chosen transporter is required. -/
theorem run_pairedComparisonStrong (σ : Perm Ω) (E : StrongPairEnum Ω)
    (h : StrongPairCover ϕ x y T σ E)
    (hset : LocalCertSetting G ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) (hT' : T'.ncard = T.ncard) [Nonempty Ω]
    (hσ : σ ∈ G) (hmap : testImage ϕ T ⟨σ, hσ⟩ = T') :
    (pairedComparisonStrong ϕ x y T σ E).run = compareIso ϕ x y T T' := by
  rw [pairedComparisonStrong, SIReduction.run_bind, run_pairedLoopStrong σ E h _ le_rfl,
    SIReduction.run_done, ← pairedQ_out_eq_compareIso hset ht htm hT' σ hσ hmap]
  unfold comparisonState
  split
  · rfl
  · rename_i hn
    exact (Set.not_nonempty_iff_eq_empty.1 hn).symm

theorem length_calls_pairedLoopStrong (σ : Perm Ω) (E : StrongPairEnum Ω)
    (h : StrongPairBound ϕ x T E) (i : ℕ) (hi : i ≤ haltIndex ϕ x T) :
    (pairedLoopStrong ϕ x y T σ E i).calls.length ≤
      i * (2 * (Nat.factorial T.ncard * Nat.card Ω)) := by
  induction i with
  | zero => simp [pairedLoopStrong]
  | succ i ih =>
    have ih := ih (by omega)
    rw [pairedLoopStrong, SIReduction.calls_bind, List.length_append]
    cases hp : (pairedLoopStrong ϕ x y T σ E i).run with
    | none => simpa using ih.trans (Nat.mul_le_mul_right _ (Nat.le_succ i))
    | some p =>
      simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
        List.length_append]
      have hs := h.source i (by omega)
      have hL := (length_calls_recomputeStrong (stages ϕ x T i) _ _).trans
        (Nat.mul_le_mul hs.reps hs.length)
      have hR := (length_calls_strongDescent (kerN (stages ϕ x T i)) x y
        (E.compareReps i) (E.windows i)).trans
        (Nat.mul_le_mul (h.comparison i (by omega)) hs.length)
      nlinarith

/-- Every paired call comes from one of the two strong descents at an earlier stage. -/
theorem mem_calls_pairedLoopStrong (σ : Perm Ω) (E : StrongPairEnum Ω) (i : ℕ)
    {I : SIInstance Ω Λ} (hI : I ∈ (pairedLoopStrong ϕ x y T σ E i).calls) :
    ∃ j < i, I ∈ (recomputeStrong (stages ϕ x T j) (E.reps j) (E.windows j)).calls ∨
      I ∈ (strongDescent (kerN (stages ϕ x T j)) x y
        (E.compareReps j) (E.windows j)).calls := by
  induction i with
  | zero => simp [pairedLoopStrong] at hI
  | succ i ih =>
    rw [pairedLoopStrong, SIReduction.calls_bind, List.mem_append] at hI
    rcases hI with hI | hI
    · obtain ⟨j, hj, hI⟩ := ih hI
      exact ⟨j, by omega, hI⟩
    · cases hp : (pairedLoopStrong ϕ x y T σ E i).run with
      | none => simp [hp] at hI
      | some p =>
        simp only [hp, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
          List.mem_append] at hI
        exact ⟨i, by omega, hI⟩

@[simp] theorem calls_pairedComparisonStrong_eq (σ : Perm Ω) (E : StrongPairEnum Ω) :
    (pairedComparisonStrong ϕ x y T σ E).calls =
      (pairedLoopStrong ϕ x y T σ E (haltIndex ϕ x T)).calls := by
  simp [pairedComparisonStrong]

/-- Proposition 13.1.11, counting both lines 04e1 and 04e2 as in the existing bound. -/
theorem calls_pairedComparisonStrong (h5 : 5 ≤ T.ncard) (σ : Perm Ω)
    (E : StrongPairEnum Ω) (h : StrongPairBound ϕ x T E) :
    (pairedComparisonStrong ϕ x y T σ E).calls.length ≤
        2 * Nat.factorial T.ncard * (Nat.card Ω)^2 ∧
      ∀ I ∈ (pairedComparisonStrong ϕ x y T σ E).calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  rw [calls_pairedComparisonStrong_eq]
  refine ⟨(length_calls_pairedLoopStrong σ E h _ le_rfl).trans ?_, ?_⟩
  · calc
      _ ≤ Nat.card Ω * (2 * (Nat.factorial T.ncard * Nat.card Ω)) :=
        Nat.mul_le_mul_right _ haltIndex_le_card
      _ = _ := by ring
  · intro I hI
    obtain ⟨i, hi, hI⟩ := mem_calls_pairedLoopStrong σ E _ hI
    have hm : I.Δ ∈ E.windows i := by
      rcases hI with hI | hI
      · exact (mem_calls_recomputeStrong _ _ _ hI).1
      · exact (mem_calls_strongDescent _ _ _ _ _ hI).1
    obtain ⟨u, hu, he⟩ := (h.source i hi).orbits I.Δ hm
    rw [he]
    exact orbit_kerN_card_le _ (loopCond_of_lt_haltIndex ϕ x T hi).1 h5 hu

/-- Specification of the supplied transporter of line 01. -/
def StrongTransporterSpec (ϕ : G →* Perm Γ) (T T' : Set Γ) : Option (Perm Ω) → Prop
  | none => ¬ ∃ σ : G, testImage ϕ T σ = T'
  | some σ => ∃ hσ : σ ∈ G, testImage ϕ T ⟨σ, hσ⟩ = T'

/-- Proposition 13.1.11 with an optional transporter as input. -/
noncomputable def compareStrong (ϕ : G →* Perm Γ) (x : Ω → Λ) (T : Set Γ) (y : Ω → Λ)
    (σ : Option (Perm Ω)) (E : StrongPairEnum Ω) : SIReduction Ω Λ (Set (Perm Ω)) :=
  match σ with
  | none => .done ∅
  | some ρ => pairedComparisonStrong ϕ x y T ρ E

/-- Proposition 13.1.11, the value for either outcome of the transporter search. -/
theorem run_compareStrong (σ : Option (Perm Ω)) (E : StrongPairEnum Ω)
    (hσ : StrongTransporterSpec ϕ T T' σ)
    (h : ∀ ρ, σ = some ρ → StrongPairCover ϕ x y T ρ E)
    (hset : LocalCertSetting G ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) (hT' : T'.ncard = T.ncard) [Nonempty Ω] :
    (compareStrong ϕ x T y σ E).run = compareIso ϕ x y T T' := by
  cases σ with
  | some ρ =>
    obtain ⟨hρ, hm⟩ := hσ
    exact run_pairedComparisonStrong ρ E (h ρ rfl) hset ht htm hT' hρ hm
  | none =>
    change ∅ = compareIso ϕ x y T T'
    symm
    apply Set.eq_empty_iff_forall_notMem.2
    intro ρ hρ
    obtain ⟨hG, hm⟩ := compareIso_testImage ϕ x y T T' hset ht htm hT' hρ
    exact hσ ⟨⟨ρ, hG⟩, hm⟩

theorem calls_compareStrong (h5 : 5 ≤ T.ncard) (σ : Option (Perm Ω))
    (E : StrongPairEnum Ω) (h : StrongPairBound ϕ x T E) :
    (compareStrong ϕ x T y σ E).calls.length ≤
        2 * Nat.factorial T.ncard * (Nat.card Ω)^2 ∧
      ∀ I ∈ (compareStrong ϕ x T y σ E).calls, T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  cases σ with
  | none => simp [compareStrong]
  | some ρ => exact calls_pairedComparisonStrong h5 ρ E h

/-- The comparison cosets can be enumerated within the same factorial bound. -/
theorem strongComparisonReps_exists (σ : Perm Ω) (hσ : σ ∈ G) (i : ℕ) :
    ∃ QL : List (Perm Ω),
      pairedQ ϕ x y T σ i = ⋃ ρ ∈ QL, ρ • (kerN (stages ϕ x T i) : Set (Perm Ω)) ∧
      QL.length ≤ Nat.factorial T.ncard := by
  by_cases hQ : (pairedQ ϕ x y T σ i).Nonempty
  · obtain ⟨π, hπ⟩ := hQ
    refine ⟨(strongReps (stages ϕ x T i)).map (π * ·), ?_, ?_⟩
    · rw [pairedQ_eq_coset hσ i hπ, strongReps_cover]
      simp [Set.smul_set_iUnion, smul_smul]
    · rw [List.length_map, strongReps_length]
      exact card_imgOn_le_factorial _
  · exact ⟨[], by simp [Set.not_nonempty_iff_eq_empty.1 hQ], by simp⟩

theorem strongPairEnum_exists (σ : Perm Ω) (hσ : σ ∈ G) :
    ∃ E : StrongPairEnum Ω, StrongPairCover ϕ x y T σ E ∧ StrongPairBound ϕ x T E ∧
      ∀ i, (E.windows i).Nodup := by
  obtain ⟨L, Δs, hs⟩ := localCertStrong_lists_exist (ϕ := ϕ) (x := x) (T := T)
  choose QL hQL using fun i => strongComparisonReps_exists (ϕ := ϕ) (x := x) (y := y)
    (T := T) σ hσ i
  exact ⟨⟨L, QL, Δs⟩, ⟨fun i _ => (hs i).1, fun i _ => (hQL i).1⟩,
    ⟨fun i _ => (hs i).2.1, fun i _ => (hQL i).2⟩, fun i => (hs i).2.2.2⟩

theorem strongTransporter_exists (ϕ : G →* Perm Γ) (T T' : Set Γ) :
    ∃ σ, StrongTransporterSpec ϕ T T' σ := by
  by_cases h : ∃ σ : G, testImage ϕ T σ = T'
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨some σ, σ.2, hσ⟩
  · exact ⟨none, h⟩

/-- All comparison inputs can be chosen together, including a failed transporter search. -/
theorem strongCompareEnum_exists (ϕ : G →* Perm Γ) (x y : Ω → Λ) (T T' : Set Γ) :
    ∃ (σ : Option (Perm Ω)) (E : StrongPairEnum Ω),
      StrongTransporterSpec ϕ T T' σ ∧
      (∀ ρ, σ = some ρ → StrongPairCover ϕ x y T ρ E) ∧
      StrongPairBound ϕ x T E ∧ ∀ i, (E.windows i).Nodup := by
  obtain ⟨σ, hσ⟩ := strongTransporter_exists ϕ T T'
  cases σ with
  | none =>
    obtain ⟨E, _, hb, hn⟩ := strongPairEnum_exists (ϕ := ϕ) (x := x) (y := y)
      (T := T) 1 G.one_mem
    exact ⟨none, E, hσ, by simp, hb, hn⟩
  | some ρ =>
    obtain ⟨hρ, _⟩ := id hσ
    obtain ⟨E, hc, hb, hn⟩ := strongPairEnum_exists (ϕ := ϕ) (x := x) (y := y)
      (T := T) ρ hρ
    exact ⟨some ρ, E, hσ, by intro τ ht; cases ht; exact hc, hb, hn⟩

end Babai
