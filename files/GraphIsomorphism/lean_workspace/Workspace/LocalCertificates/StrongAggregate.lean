import Workspace.LocalCertificates.StrongCompare
import Workspace.LocalCertificates.AggregateRound

/-! # Sec. 13.2 with supplied enumerations

`AggEnum.tests` is the order of the test sets. The Boolean index selects `x` or `y`.
All other lists and initial transporters are fields of the same record. Its specification
uses a permutation of `testSetList`, the form proved by `Algo.aggTestSetsOn_perm`.
-/

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

universe w

/-- The enumerations for Sec. 13.2. `false` selects the source string, `true` the target. -/
structure AggEnum (Ω Γ : Type*) where
  tests : List (Set Γ)
  certReps : Bool → Set Γ → ℕ → List (Perm Ω)
  certWindows : Bool → Set Γ → ℕ → List (Set Ω)
  transporter : Bool → Set Γ → Set Γ → Option (Perm Ω)
  pair : Bool → Set Γ → Set Γ → StrongPairEnum Ω

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {x y : Ω → Λ} {t : ℕ}

/-- Cover and transporter conditions, with no size or orbit assumptions. -/
structure AggEnum.Cover (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) : Prop where
  cert : ∀ b T, T ∈ E.tests → ∀ i < haltIndex ϕ (cond b y x) T,
    StrongStageCover (stages ϕ (cond b y x) T i) (E.certReps b T i) (E.certWindows b T i)
  transporter : ∀ b T, T ∈ E.tests → ∀ T', T' ∈ E.tests →
    StrongTransporterSpec ϕ T T' (E.transporter b T T')
  pair : ∀ b T, T ∈ E.tests → ∀ T', T' ∈ E.tests → ∀ σ,
    E.transporter b T T' = some σ → StrongPairCover ϕ x (cond b y x) T σ (E.pair b T T')

/-- The size and orbit conditions for the calls of Sec. 13.2. -/
structure AggEnum.Bound (ϕ : G →* Perm Γ) (x y : Ω → Λ) (t : ℕ)
    (E : AggEnum Ω Γ) : Prop where
  tests : E.tests.Perm (testSetList Γ t)
  cert : ∀ b T, T ∈ E.tests → ∀ i < haltIndex ϕ (cond b y x) T,
    StrongStageBound (stages ϕ (cond b y x) T i) (E.certReps b T i) (E.certWindows b T i)
  pair : ∀ b T, T ∈ E.tests → ∀ T', T' ∈ E.tests → StrongPairBound ϕ x T (E.pair b T T')

/-- All hypotheses on an aggregate enumeration hold together. -/
structure AggEnum.Spec (ϕ : G →* Perm Γ) (x y : Ω → Λ) (t : ℕ)
    (E : AggEnum Ω Γ) : Prop where
  toCover : E.Cover ϕ x y
  toBound : E.Bound ϕ x y t

/-- Kernel invariance is enough for the coset shape of the calls. -/
structure AggEnum.Invariant (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) : Prop where
  cert : ∀ b T, T ∈ E.tests → ∀ i < haltIndex ϕ (cond b y x) T,
    ∀ Δ ∈ E.certWindows b T i, IsInvariant (kerN (stages ϕ (cond b y x) T i)) Δ
  pair : ∀ b T, T ∈ E.tests → ∀ T', T' ∈ E.tests → ∀ i < haltIndex ϕ x T,
    ∀ Δ ∈ (E.pair b T T').windows i, IsInvariant (kerN (stages ϕ x T i)) Δ

theorem AggEnum.Bound.invariant {E : AggEnum Ω Γ} (h : E.Bound ϕ x y t) :
    E.Invariant ϕ x y := by
  constructor
  · intro b T hT i hi Δ hΔ
    obtain ⟨u, _, rfl⟩ := (h.cert b T hT i hi).orbits Δ hΔ
    exact isInvariant_orbit' _ _
  · intro b T hT T' hT' i hi Δ hΔ
    obtain ⟨u, _, rfl⟩ := ((h.pair b T hT T' hT').source i hi).orbits Δ hΔ
    exact isInvariant_orbit' _ _

theorem AggEnum.Bound.ncard {E : AggEnum Ω Γ} (h : E.Bound ϕ x y t)
    {T : Set Γ} (hT : T ∈ E.tests) : T.ncard = t :=
  ncard_of_mem_testSetList (h.tests.mem_iff.1 hT)

theorem AggEnum.Bound.length {E : AggEnum Ω Γ} (h : E.Bound ϕ x y t) :
    E.tests.length = (Fintype.card Γ).choose t :=
  h.tests.length_eq.trans (length_testSetList t)

/-- Sec. 13.2, one certificate run with the image group omitted from the result. -/
noncomputable def certRunStrong (ϕ : G →* Perm Γ) (x : Ω → Λ) (T : Set Γ)
    (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω)) :
    SIReduction Ω Λ (Set Ω × Subgroup (Perm Ω)) :=
  (localCertStrong ϕ x T L Δs).bind fun p => .done (p.1, p.2.1)

theorem run_certRunStrong (L : ℕ → List (Perm Ω)) (Δs : ℕ → List (Set Ω))
    {T : Set Γ} (h : ∀ i < haltIndex ϕ x T,
      StrongStageCover (stages ϕ x T i) (L i) (Δs i)) :
    (certRunStrong ϕ x T L Δs).run = (windowOut ϕ x T, certK ϕ x T) := by
  rw [certRunStrong, SIReduction.run_bind, run_localCertStrong L Δs h, SIReduction.run_done]

@[simp] theorem calls_certRunStrong (T : Set Γ) (L : ℕ → List (Perm Ω))
    (Δs : ℕ → List (Set Ω)) :
    (certRunStrong ϕ x T L Δs).calls = (localCertStrong ϕ x T L Δs).calls := by
  simp [certRunStrong]

/-- The `2 C(m,t)` runs, in the supplied test-set order. -/
noncomputable def certRunsStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) :
    List (SIReduction Ω Λ (Set Ω × Subgroup (Perm Ω))) :=
  [false, true].flatMap fun b => E.tests.map fun T =>
    certRunStrong ϕ (cond b y x) T (E.certReps b T) (E.certWindows b T)

/-- The `2 C(m,t)^2` paired comparisons, in the supplied test-set order. -/
noncomputable def compareRunsStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) :
    List (SIReduction Ω Λ (Set (Perm Ω))) :=
  [false, true].flatMap fun b => E.tests.flatMap fun T => E.tests.map fun T' =>
    compareStrong ϕ x T (cond b y x) (E.transporter b T T') (E.pair b T T')

theorem mem_certRunsStrong (E : AggEnum Ω Γ) {S} : S ∈ certRunsStrong ϕ x y E ↔
    ∃ b T, T ∈ E.tests ∧
      S = certRunStrong ϕ (cond b y x) T (E.certReps b T) (E.certWindows b T) := by
  simp only [certRunsStrong, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨b, _, T, hT, rfl⟩
    exact ⟨b, T, hT, rfl⟩
  · rintro ⟨b, T, hT, rfl⟩
    exact ⟨b, by cases b <;> simp, T, hT, rfl⟩

theorem mem_compareRunsStrong (E : AggEnum Ω Γ) {S} : S ∈ compareRunsStrong ϕ x y E ↔
    ∃ b T, T ∈ E.tests ∧ ∃ T', T' ∈ E.tests ∧
      S = compareStrong ϕ x T (cond b y x) (E.transporter b T T') (E.pair b T T') := by
  simp only [compareRunsStrong, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨b, _, T, hT, T', hT', rfl⟩
    exact ⟨b, T, hT, T', hT', rfl⟩
  · rintro ⟨b, T, hT, T', hT', rfl⟩
    exact ⟨b, by cases b <;> simp, T, hT, T', hT', rfl⟩

/-- Sec. 13.2, the certificate phase. -/
noncomputable def certPhaseStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) :=
  SIReduction.sequence (certRunsStrong ϕ x y E)

/-- Sec. 13.2, the comparison phase. -/
noncomputable def comparePhaseStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ) (E : AggEnum Ω Γ) :=
  SIReduction.sequence (compareRunsStrong ϕ x y E)

/-- Sec. 13.2, the two phases followed by the continuation of the Master Algorithm. -/
noncomputable def aggregateRoundStrong (ϕ : G →* Perm Γ) (x y : Ω → Λ)
    (E : AggEnum Ω Γ) {α : Type w} (R : SIReduction Ω Λ α) : SIReduction Ω Λ α :=
  (certPhaseStrong ϕ x y E).bind fun _ => (comparePhaseStrong ϕ x y E).bind fun _ => R

@[simp] theorem run_aggregateRoundStrong (E : AggEnum Ω Γ) {α : Type w}
    (R : SIReduction Ω Λ α) : (aggregateRoundStrong ϕ x y E R).run = R.run := by
  simp [aggregateRoundStrong]

theorem calls_aggregateRoundStrong (E : AggEnum Ω Γ) {α : Type w} (R : SIReduction Ω Λ α) :
    (aggregateRoundStrong ϕ x y E R).calls = (certPhaseStrong ϕ x y E).calls ++
      ((comparePhaseStrong ϕ x y E).calls ++ R.calls) := by
  simp [aggregateRoundStrong]

/-- Each listed certificate computes its stated window and certificate. -/
theorem run_certPhaseStrong (E : AggEnum Ω Γ) (h : E.Cover ϕ x y) :
    (certPhaseStrong ϕ x y E).run = [false, true].flatMap fun b =>
      E.tests.map fun T => (windowOut ϕ (cond b y x) T, certK ϕ (cond b y x) T) := by
  rw [certPhaseStrong, SIReduction.run_sequence, certRunsStrong, List.map_flatMap]
  congr 1
  funext b
  rw [List.map_map]
  exact List.map_congr_left fun T hT => run_certRunStrong _ _ (h.cert b T hT)

/-- Each listed comparison has the value of Proposition 13.1.11. -/
theorem run_comparePhaseStrong (E : AggEnum Ω Γ) (h : E.Spec ϕ x y t)
    (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card Ω))
    (htm : 10 * t ≤ Nat.card Γ) [Nonempty Ω] :
    (comparePhaseStrong ϕ x y E).run = [false, true].flatMap fun b =>
      E.tests.flatMap fun T => E.tests.map fun T' => compareIso ϕ x (cond b y x) T T' := by
  rw [comparePhaseStrong, SIReduction.run_sequence, compareRunsStrong, List.map_flatMap]
  congr 1
  funext b
  rw [List.map_flatMap]
  rw [List.flatMap_def, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro T hT
  rw [List.map_map]
  apply List.map_congr_left
  intro T' hT'
  have hc := h.toBound.ncard hT
  have hc' := h.toBound.ncard hT'
  exact run_compareStrong _ _ (h.toCover.transporter b T hT T' hT')
    (h.toCover.pair b T hT T' hT') hset (hc ▸ ht) (hc ▸ htm) (hc'.trans hc.symm)

theorem certRunsStrong_bound (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t) (h5 : 5 ≤ t)
    {S} (hS : S ∈ certRunsStrong ϕ x y E) :
    S.calls.length ≤ Nat.factorial t * (Nat.card Ω)^2 ∧
      ∀ I ∈ S.calls, t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨b, T, hT, rfl⟩ := (mem_certRunsStrong E).1 hS
  have hc := h.ncard hT
  simpa only [calls_certRunStrong, hc] using
    theorem_13_1_3_strong_calls (hc ▸ h5) (E.certReps b T) (E.certWindows b T) (h.cert b T hT)

theorem compareRunsStrong_bound (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t) (h5 : 5 ≤ t)
    {S} (hS : S ∈ compareRunsStrong ϕ x y E) :
    S.calls.length ≤ 2 * Nat.factorial t * (Nat.card Ω)^2 ∧
      ∀ I ∈ S.calls, t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨b, T, hT, T', hT', rfl⟩ := (mem_compareRunsStrong E).1 hS
  have hc := h.ncard hT
  simpa only [hc] using calls_compareStrong (y := cond b y x) (hc ▸ h5)
    (E.transporter b T T') (E.pair b T T') (h.pair b T hT T' hT')

theorem window_calls_certPhaseStrong (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t) (h5 : 5 ≤ t)
    {I : SIInstance Ω Λ} (hI : I ∈ (certPhaseStrong ϕ x y E).calls) :
    t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  exact (certRunsStrong_bound E h h5 hS).2 I hI

theorem window_calls_comparePhaseStrong (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t) (h5 : 5 ≤ t)
    {I : SIInstance Ω Λ} (hI : I ∈ (comparePhaseStrong ϕ x y E).calls) :
    t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨S, hS, hI⟩ := SIReduction.mem_calls_sequence hI
  exact (compareRunsStrong_bound E h h5 hS).2 I hI

theorem calls_length_strong_phases (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t) (h5 : 5 ≤ t) :
    (certPhaseStrong ϕ x y E).calls.length + (comparePhaseStrong ϕ x y E).calls.length ≤
      aggregateRoundCost (Fintype.card Γ) t (Nat.card Ω) := by
  have hc := SIReduction.calls_length_sequence_le (fun S hS => (certRunsStrong_bound E h h5 hS).1)
  have hp := SIReduction.calls_length_sequence_le (fun S hS => (compareRunsStrong_bound E h h5 hS).1)
  have hcl : (certRunsStrong ϕ x y E).length = 2 * (Fintype.card Γ).choose t := by
    simp [certRunsStrong, h.length, two_mul]
  have hpl : (compareRunsStrong ϕ x y E).length ≤ 2 * ((Fintype.card Γ).choose t)^2 := by
    have key : ∀ b : Bool, (E.tests.flatMap fun T => E.tests.map fun T' =>
        compareStrong ϕ x T (cond b y x) (E.transporter b T T') (E.pair b T T')).length ≤
        ((Fintype.card Γ).choose t)^2 := by
      intro b
      refine (length_flatMap_le _ _ E.tests.length (fun T _ => by rw [List.length_map])).trans ?_
      rw [h.length, pow_two]
    simpa [compareRunsStrong, two_mul] using Nat.add_le_add (key false) (key true)
  rw [hcl] at hc
  have hp := hp.trans (Nat.mul_le_mul_right _ hpl)
  exact Nat.add_le_add hc hp

theorem calls_length_aggregateRoundStrong (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t)
    (h5 : 5 ≤ t) {α : Type w} (R : SIReduction Ω Λ α) :
    (aggregateRoundStrong ϕ x y E R).calls.length ≤
      R.calls.length + aggregateRoundCost (Fintype.card Γ) t (Nat.card Ω) := by
  rw [calls_aggregateRoundStrong, List.length_append, List.length_append]
  have := calls_length_strong_phases E h h5
  omega

theorem window_calls_aggregateRoundStrong (E : AggEnum Ω Γ) (h : E.Bound ϕ x y t)
    (h5 : 5 ≤ t) {α : Type w} (R : SIReduction Ω Λ α) {I : SIInstance Ω Λ}
    (hI : I ∈ (aggregateRoundStrong ϕ x y E R).calls) :
    t * I.Δ.ncard ≤ Nat.card Ω ∨ I ∈ R.calls := by
  rw [calls_aggregateRoundStrong, List.mem_append, List.mem_append] at hI
  rcases hI with hI | hI | hI
  · exact Or.inl (window_calls_certPhaseStrong E h h5 hI)
  · exact Or.inl (window_calls_comparePhaseStrong E h h5 hI)
  · exact Or.inr hI

/-- All enumerations exist together for any prescribed order of the test sets. -/
theorem aggEnum_exists (ϕ : G →* Perm Γ) (x y : Ω → Λ) (t : ℕ)
    (ts : List (Set Γ)) (hts : ts.Perm (testSetList Γ t)) :
    ∃ E : AggEnum Ω Γ, E.tests = ts ∧ E.Spec ϕ x y t ∧ E.Invariant ϕ x y ∧
      (∀ b T i, (E.certWindows b T i).Nodup) ∧
      ∀ b T T' i, ((E.pair b T T').windows i).Nodup := by
  choose L Δs hs using fun b T =>
    localCertStrong_lists_exist (ϕ := ϕ) (x := cond b y x) (T := T)
  choose σ P hp using fun b T T' => strongCompareEnum_exists ϕ x (cond b y x) T T'
  let E : AggEnum Ω Γ := ⟨ts, L, Δs, σ, P⟩
  have hb : E.Bound ϕ x y t :=
    ⟨hts, fun b T _ i _ => (hs b T i).2.1, fun b T _ T' _ => (hp b T T').2.2.1⟩
  have hc : E.Cover ϕ x y :=
    ⟨fun b T _ i _ => (hs b T i).1, fun b T _ T' _ => (hp b T T').1,
      fun b T _ T' _ => (hp b T T').2.1⟩
  exact ⟨E, rfl, ⟨hc, hb⟩, hb.invariant, fun b T i => (hs b T i).2.2.2,
    fun b T T' i => (hp b T T').2.2.2 i⟩

theorem aggEnum_nonempty (ϕ : G →* Perm Γ) (x y : Ω → Λ) (t : ℕ) :
    Nonempty {E : AggEnum Ω Γ // E.Spec ϕ x y t} := by
  obtain ⟨E, _, h, _⟩ := aggEnum_exists ϕ x y t (testSetList Γ t) (List.Perm.refl _)
  exact ⟨E, h⟩

end Babai
