import Workspace.LocalCertificates.Calls
import Workspace.TopAction.CosetChain

/-! # Strong descent in Sec. 13.1

The lists are inputs. For each coset we apply the Chain Rule in the listed order.
Each answer is the candidate set of the next call. Correctness only needs the two
cover equations. Orbit windows give the size bound of Theorem 13.1.3.
-/

namespace Babai

open MulAction Equiv
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Sec. 11.1, strong descent: descent to `N`, then the Chain Rule on each coset. -/
noncomputable def strongDescent (N : Subgroup (Perm Ω)) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) : SIReduction Ω Λ (Set (Perm Ω)) :=
  unionAnswers (L.map fun σ => cosetChain x y Δs (σ • (N : Set (Perm Ω))))

theorem run_strongDescent (N : Subgroup (Perm Ω)) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    (strongDescent N x y L Δs).run =
      wIso (⋃ Δ ∈ Δs, Δ) (⋃ σ ∈ L, σ • (N : Set (Perm Ω))) x y := by
  rw [strongDescent, run_unionAnswers]
  ext τ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨R, ⟨σ, hσ, rfl⟩, hτ⟩
    rw [run_cosetChain] at hτ
    exact ⟨Set.mem_iUnion₂.2 ⟨σ, hσ, hτ.1⟩, hτ.2⟩
  · rintro ⟨hτ, hw⟩
    obtain ⟨σ, hσ, hτ⟩ := Set.mem_iUnion₂.1 hτ
    exact ⟨_, ⟨σ, hσ, rfl⟩, by rw [run_cosetChain]; exact ⟨hτ, hw⟩⟩

theorem calls_strongDescent (N : Subgroup (Perm Ω)) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    (strongDescent N x y L Δs).calls =
      L.flatMap fun σ => (cosetChain x y Δs (σ • (N : Set (Perm Ω)))).calls := by
  simp [strongDescent, List.flatMap_map, Function.comp_def]

theorem length_calls_strongDescent (N : Subgroup (Perm Ω)) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) :
    (strongDescent N x y L Δs).calls.length ≤ L.length * Δs.length := by
  rw [calls_strongDescent, List.length_flatMap]
  calc
    _ ≤ (L.map fun σ => (cosetChain x y Δs (σ • (N : Set (Perm Ω)))).calls.length).length * Δs.length := by
      apply List.sum_le_card_nsmul
      intro k hk
      obtain ⟨σ, _, rfl⟩ := List.mem_map.1 hk
      exact (calls_cosetChain x y Δs _).1
    _ = _ := by rw [List.length_map]

theorem mem_calls_strongDescent (N : Subgroup (Perm Ω)) (x y : Ω → Λ)
    (L : List (Perm Ω)) (Δs : List (Set Ω)) {I : SIInstance Ω Λ}
    (hI : I ∈ (strongDescent N x y L Δs).calls) :
    I.Δ ∈ Δs ∧ ∃ σ ∈ L, I.K ⊆ σ • (N : Set (Perm Ω)) := by
  rw [calls_strongDescent, List.mem_flatMap] at hI
  obtain ⟨σ, hσ, hI⟩ := hI
  exact ⟨(calls_cosetChain x y Δs _).2 I hI, σ, hσ,
    calls_cosetChain_K x y Δs _ I hI⟩

variable [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- The list specification for one round. The cover equation is in the form supplied
by `Algo.cover_lcPerms`. No orbit condition is needed for the value. -/
structure StrongStageCover (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) : Prop where
  cosets : (s.H : Set (Perm Ω)) = ⋃ σ ∈ L, σ • (kerN s : Set (Perm Ω))
  windows : (⋃ Δ ∈ Δs, Δ) = s.aff

/-- The extra list conditions used for the cost in Theorem 13.1.3. -/
structure StrongStageBound (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) : Prop where
  reps : L.length ≤ Nat.factorial T.ncard
  length : Δs.length ≤ Nat.card Ω
  orbits : ∀ Δ ∈ Δs, ∃ u ∈ s.aff, Δ = orbit (kerN s) u

/-- Procedure Recompute, line 04e of Sec. 13.1, with its enumerations supplied. -/
noncomputable def recomputeStrong (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) : SIReduction Ω Λ (Set (Perm Ω)) :=
  strongDescent (kerN s) x x L Δs

/-- Eq. (69) and the Chain Rule give the next group. The windows need not be orbits. -/
theorem run_recomputeStrong (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) (h : StrongStageCover s L Δs) :
    (recomputeStrong s L Δs).run = (s.step.H : Set (Perm Ω)) := by
  rw [recomputeStrong, run_strongDescent, h.windows, ← h.cosets]
  rw [eq_69 s (certLift s) (certLift_spec s)]
  have he : wIso s.aff (⋃ sb, certLift s sb • (kerN s : Set (Perm Ω))) x x =
      recompute s (certLift s) := by
    ext τ
    simp only [mem_wIso, recompute, mem_wAut, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨sb, hsb⟩, hr⟩
      exact ⟨sb, hsb, hr⟩
    · rintro ⟨sb, hsb, hr⟩
      exact ⟨⟨sb, hsb⟩, hr⟩
  exact he.trans (recompute_eq s (certLift s) (certLift_spec s))

theorem calls_recomputeStrong (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) :
    (recomputeStrong s L Δs).calls =
      L.flatMap fun σ => (cosetChain x x Δs (σ • (kerN s : Set (Perm Ω)))).calls :=
  calls_strongDescent _ _ _ _ _

theorem length_calls_recomputeStrong (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) :
    (recomputeStrong s L Δs).calls.length ≤ L.length * Δs.length :=
  length_calls_strongDescent _ _ _ _ _

theorem mem_calls_recomputeStrong (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) {I : SIInstance Ω Λ}
    (hI : I ∈ (recomputeStrong s L Δs).calls) :
    I.Δ ∈ Δs ∧ ∃ σ ∈ L, I.K ⊆ σ • (kerN s : Set (Perm Ω)) :=
  mem_calls_strongDescent _ _ _ _ _ hI

theorem calls_recomputeStrong_bound (s : Stage ϕ x T) (L : List (Perm Ω))
    (Δs : List (Set Ω)) (h : StrongStageBound s L Δs)
    (hg : alternatingGroup T ≤ imgOn ϕ T s.le) (h5 : 5 ≤ T.ncard) :
    (recomputeStrong s L Δs).calls.length ≤ Nat.factorial T.ncard * Nat.card Ω ∧
      ∀ I ∈ (recomputeStrong s L Δs).calls, T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  refine ⟨(length_calls_recomputeStrong s L Δs).trans (Nat.mul_le_mul h.reps h.length), ?_⟩
  intro I hI
  obtain ⟨u, hu, he⟩ := h.orbits I.Δ (mem_calls_recomputeStrong s L Δs hI).1
  rw [he]
  exact orbit_kerN_card_le s hg h5 hu

variable (ϕ x T)

/-- Sec. 13.1, lines 02--05, with one pair of lists per stage. -/
noncomputable def loopStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    ℕ → SIReduction Ω Λ (Set Ω × Set (Perm Ω))
  | 0 => .done (∅, (bigGT ϕ T : Set (Perm Ω)))
  | i + 1 => (loopStrong L Δs i).bind fun p =>
      (recomputeStrong (stages ϕ x T i) (L i) (Δs i)).bind fun cur =>
        .done (affOf ϕ T p.2, p.2 ∩ cur)

/-- Sec. 13.1, Procedure LocalCertificates in strong-descent form. -/
noncomputable def localCertStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    SIReduction Ω Λ (Set Ω × Subgroup (Perm Ω) × Subgroup (Perm T)) :=
  (loopStrong ϕ x T L Δs (haltIndex ϕ x T)).bind fun p =>
    .done (p.1, certKOf ϕ T p.1 p.2, certMOf ϕ T p.2)

variable {ϕ x T}

theorem run_loopStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) (i : ℕ)
    (h : ∀ j < i, StrongStageCover (stages ϕ x T j) (L j) (Δs j)) :
    (loopStrong ϕ x T L Δs i).run =
      ((stages ϕ x T i).W, ((stages ϕ x T i).H : Set (Perm Ω))) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [loopStrong, SIReduction.run_bind, ih (fun j hj => h j (by omega)),
      SIReduction.run_bind, run_recomputeStrong _ _ _ (h i (by omega)), SIReduction.run_done]
    refine Prod.ext (affOf_coe _) ?_
    exact Set.inter_eq_self_of_subset_right (stages ϕ x T i).step_H_le

theorem calls_loopStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) (i : ℕ) :
    (loopStrong ϕ x T L Δs (i + 1)).calls = (loopStrong ϕ x T L Δs i).calls ++
      (recomputeStrong (stages ϕ x T i) (L i) (Δs i)).calls := by
  simp [loopStrong]

theorem mem_calls_loopStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    ∀ i, ∀ I ∈ (loopStrong ϕ x T L Δs i).calls,
      ∃ j < i, I ∈ (recomputeStrong (stages ϕ x T j) (L j) (Δs j)).calls := by
  intro i
  induction i with
  | zero => simp [loopStrong]
  | succ i ih =>
    intro I hI
    rw [calls_loopStrong, List.mem_append] at hI
    rcases hI with hI | hI
    · obtain ⟨j, hj, hI⟩ := ih I hI
      exact ⟨j, by omega, hI⟩
    · exact ⟨i, by omega, hI⟩

theorem length_calls_loopStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) (i : ℕ)
    (h : ∀ j < i, StrongStageBound (stages ϕ x T j) (L j) (Δs j)) :
    (loopStrong ϕ x T L Δs i).calls.length ≤ i * (Nat.factorial T.ncard * Nat.card Ω) := by
  induction i with
  | zero => simp [loopStrong]
  | succ i ih =>
    rw [calls_loopStrong, List.length_append, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun j hj => h j (by omega)))
      ((length_calls_recomputeStrong _ _ _).trans
        (Nat.mul_le_mul (h i (by omega)).reps (h i (by omega)).length))

theorem run_localCertStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω))
    (h : ∀ i < haltIndex ϕ x T, StrongStageCover (stages ϕ x T i) (L i) (Δs i)) :
    (localCertStrong ϕ x T L Δs).run = (windowOut ϕ x T, certK ϕ x T, certM ϕ x T) := by
  rw [localCertStrong, SIReduction.run_bind, run_loopStrong L Δs _ h, SIReduction.run_done]
  exact Prod.ext rfl (Prod.ext (certKOf_coe _ _) (certMOf_coe _))

@[simp] theorem calls_localCertStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    (localCertStrong ϕ x T L Δs).calls = (loopStrong ϕ x T L Δs (haltIndex ϕ x T)).calls := by
  simp [localCertStrong]

/-- Theorem 13.1.3, the call bound and window bound for strong descent. -/
theorem theorem_13_1_3_strong_calls (h5 : 5 ≤ T.ncard)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω))
    (h : ∀ i < haltIndex ϕ x T, StrongStageBound (stages ϕ x T i) (L i) (Δs i)) :
    (localCertStrong ϕ x T L Δs).calls.length ≤ Nat.factorial T.ncard * (Nat.card Ω)^2 ∧
      ∀ I ∈ (localCertStrong ϕ x T L Δs).calls, T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  rw [calls_localCertStrong]
  refine ⟨(length_calls_loopStrong L Δs _ h).trans ?_, ?_⟩
  · calc
      _ ≤ Nat.card Ω * (Nat.factorial T.ncard * Nat.card Ω) :=
        Nat.mul_le_mul_right _ haltIndex_le_card
      _ = _ := by ring
  · intro I hI
    obtain ⟨i, hi, hI⟩ := mem_calls_loopStrong L Δs _ I hI
    exact (calls_recomputeStrong_bound _ _ _ (h i hi)
      (loopCond_of_lt_haltIndex ϕ x T hi).1 h5).2 I hI

/-- One representative for each image element, used only to show that the lists exist. -/
noncomputable def strongReps (s : Stage ϕ x T) : List (Perm Ω) :=
  (Finset.univ : Finset (imgOn ϕ T s.le)).toList.map (certLift s)

/-- Each affected kernel orbit is listed once. -/
noncomputable def strongWindows (s : Stage ϕ x T) : List (Set Ω) :=
  (orbitList (kerN s)).filter fun Δ => Δ ⊆ s.aff

theorem strongReps_length (s : Stage ϕ x T) :
    (strongReps s).length = Nat.card (imgOn ϕ T s.le) := by
  simp [strongReps, Nat.card_eq_fintype_card]

theorem strongReps_cover (s : Stage ϕ x T) :
    (s.H : Set (Perm Ω)) = ⋃ σ ∈ strongReps s, σ • (kerN s : Set (Perm Ω)) := by
  rw [eq_69 s (certLift s) (certLift_spec s)]
  ext τ
  simp [strongReps]

theorem strongWindows_orbits (s : Stage ϕ x T) :
    ∀ Δ ∈ strongWindows s, ∃ u ∈ s.aff, Δ = orbit (kerN s) u := by
  intro Δ hΔ
  obtain ⟨hΔ, hsub⟩ := List.mem_filter.1 hΔ
  obtain ⟨u, rfl⟩ := mem_orbitList hΔ
  exact ⟨u, of_decide_eq_true hsub (mem_orbit_self u), rfl⟩

theorem strongWindows_cover (s : Stage ϕ x T) :
    (⋃ Δ ∈ strongWindows s, Δ) = s.aff := by
  ext u
  constructor
  · intro hu
    obtain ⟨Δ, hΔ, hu⟩ := Set.mem_iUnion₂.1 hu
    exact of_decide_eq_true (List.mem_filter.1 hΔ).2 hu
  · intro hu
    have hall : u ∈ ⋃ Δ ∈ orbitList (kerN s), Δ := by rw [iUnion_orbitList]; trivial
    obtain ⟨Δ, hΔ, huΔ⟩ := Set.mem_iUnion₂.1 hall
    refine Set.mem_iUnion₂.2 ⟨Δ, List.mem_filter.2 ⟨hΔ, ?_⟩, huΔ⟩
    obtain ⟨v, rfl⟩ := mem_orbitList hΔ
    have he : orbit (kerN s) v = orbit (kerN s) u := ((orbit_eq_iff).2 huΔ).symm
    apply decide_eq_true
    rw [he]
    exact orbit_kerN_subset_aff s hu

theorem strongWindows_nodup (s : Stage ϕ x T) : (strongWindows s).Nodup := by
  apply List.Nodup.filter
  letI : Fintype (orbitRel.Quotient (kerN s) Ω) := Fintype.ofFinite _
  refine List.Nodup.map ?_ (Finset.nodup_toList _)
  intro q q' h
  have hq : (q.out : Ω) ∈ orbitRel.Quotient.orbit q :=
    (orbitRel.Quotient.mem_orbit (G := kerN s)).2 q.out_eq'
  have hq' : (q.out : Ω) ∈ orbitRel.Quotient.orbit q' := by rw [← h]; exact hq
  rw [orbitRel.Quotient.mem_orbit (G := kerN s)] at hq hq'
  rw [← hq, hq']

theorem strongStage_exists (s : Stage ϕ x T) :
    ∃ L Δs, StrongStageCover s L Δs ∧ StrongStageBound s L Δs ∧
      L.length = Nat.card (imgOn ϕ T s.le) ∧ Δs.Nodup := by
  refine ⟨strongReps s, strongWindows s, ⟨strongReps_cover s, strongWindows_cover s⟩,
    ⟨?_, ?_, strongWindows_orbits s⟩, strongReps_length s, strongWindows_nodup s⟩
  · rw [strongReps_length]
    exact card_imgOn_le_factorial s.le
  · exact (List.length_filter_le _ _).trans (length_orbitList_le _)

theorem localCertStrong_lists_exist :
    ∃ (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)),
      ∀ i, StrongStageCover (stages ϕ x T i) (L i) (Δs i) ∧
        StrongStageBound (stages ϕ x T i) (L i) (Δs i) ∧
        (L i).length = Nat.card (imgOn ϕ T (stages ϕ x T i).le) ∧ (Δs i).Nodup := by
  choose L Δs h using fun i => strongStage_exists (stages ϕ x T i)
  exact ⟨L, Δs, h⟩

end Babai
