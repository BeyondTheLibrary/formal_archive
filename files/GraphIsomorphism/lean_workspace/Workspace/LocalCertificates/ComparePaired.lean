/-
Section 13.1 of Babai, version 2.5: counted comparison calls for Proposition 13.1.11.
-/
import Workspace.LocalCertificates.CompareInvariant

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ}
  {x : Ω → Λ} {T : Set Γ}

/-- Line 04d1: choose a lift of each element of the image on `T`. -/
noncomputable def comparisonLift (s : Stage ϕ x T) (sb : imgOn ϕ T s.le) :
    Equiv.Perm Ω := (Classical.choose sb.property : s.H)

theorem comparisonLift_spec (s : Stage ϕ x T) (sb : imgOn ϕ T s.le) :
    ∃ h : comparisonLift s sb ∈ s.H,
      psiOn ϕ T s.le ⟨comparisonLift s sb, h⟩ = (sb : Equiv.Perm T) :=
  ⟨(Classical.choose sb.property).property, Classical.choose_spec sb.property⟩

/-- The calls of line 04e2 for one coset. Enumerating points can repeat an orbit, but
uses at most `n` calls and keeps the same intersection of answers. -/
noncomputable def comparisonInstances (s : Stage ϕ x T)
    (K : Set (Equiv.Perm Ω)) (y : Ω → Λ) : List (SIInstance Ω Λ) :=
  s.aff.toFinset.toList.map fun u => ⟨K, orbit (kerN s) u, x, y⟩

theorem mem_comparisonInstances (s : Stage ϕ x T) (K : Set (Equiv.Perm Ω))
    (y : Ω → Λ) {I : SIInstance Ω Λ} :
    I ∈ comparisonInstances s K y ↔
      ∃ u ∈ s.aff, I = ⟨K, orbit (kerN s) u, x, y⟩ := by
  simp [comparisonInstances, eq_comm]

/-- Strong descent on the kernel orbits gives exactly the comparison on the new window. -/
theorem run_comparisonInter (s : Stage ϕ x T) (K : Set (Equiv.Perm Ω)) (y : Ω → Λ) :
    (interAnswers K (comparisonInstances s K y)).run = wIso s.aff K x y := by
  rw [run_interAnswers]
  ext σ
  constructor
  · rintro ⟨hK, hr⟩
    refine ⟨hK, fun u hu => ?_⟩
    have hI := Set.mem_iInter₂.1 hr _ ((mem_comparisonInstances s K y).2 ⟨u, hu, rfl⟩)
    exact hI.2 u (mem_orbit_self u)
  · rintro ⟨hK, hr⟩
    refine ⟨hK, Set.mem_iInter₂.2 ?_⟩
    intro I hI
    obtain ⟨u, hu, rfl⟩ := (mem_comparisonInstances s K y).1 hI
    exact ⟨hK, fun v hv => hr v (orbit_kerN_subset_aff s hu hv)⟩

/-- Lines 04c0--04f2: for `π ∈ Q_old`, split `π H(W_old)` into the cosets
`(π * σ) N`, compare the strings on each kernel orbit, and unite the answers. -/
noncomputable def comparisonRound (s : Stage ϕ x T) (π : Equiv.Perm Ω) (y : Ω → Λ) :
    SIReduction Ω Λ (Set (Equiv.Perm Ω)) :=
  unionAnswers ((Finset.univ : Finset (imgOn ϕ T s.le)).toList.map fun sb =>
    let K := (π * comparisonLift s sb) • (kerN s : Set (Equiv.Perm Ω))
    interAnswers K (comparisonInstances s K y))

theorem run_comparisonRound (s : Stage ϕ x T) (π : Equiv.Perm Ω) (y : Ω → Λ) :
    (comparisonRound s π y).run = wIso s.aff (π • (s.H : Set (Equiv.Perm Ω))) x y := by
  rw [recomputeQ_eq s (comparisonLift s) (comparisonLift_spec s) π,
    comparisonRound, run_unionAnswers]
  ext σ
  simp only [Set.mem_iUnion, List.mem_map, exists_prop]
  constructor
  · rintro ⟨R, ⟨sb, -, rfl⟩, hr⟩
    exact ⟨sb, by rwa [run_comparisonInter] at hr⟩
  · rintro ⟨sb, hr⟩
    refine ⟨_, ⟨sb, Finset.mem_toList.2 (Finset.mem_univ _), rfl⟩, ?_⟩
    rwa [run_comparisonInter]

theorem calls_comparisonRound (s : Stage ϕ x T) (π : Equiv.Perm Ω) (y : Ω → Λ) :
    (comparisonRound s π y).calls =
      (Finset.univ : Finset (imgOn ϕ T s.le)).toList.flatMap fun sb =>
        comparisonInstances s ((π * comparisonLift s sb) • (kerN s : Set (Equiv.Perm Ω))) y := by
  simp [comparisonRound, List.flatMap_map]

theorem length_calls_comparisonRound (s : Stage ϕ x T) (π : Equiv.Perm Ω) (y : Ω → Λ) :
    (comparisonRound s π y).calls.length ≤ Nat.factorial T.ncard * Nat.card Ω := by
  rw [calls_comparisonRound, List.length_flatMap]
  have hb : ∀ k ∈ ((Finset.univ : Finset (imgOn ϕ T s.le)).toList.map fun sb =>
      (comparisonInstances s ((π * comparisonLift s sb) • (kerN s : Set (Equiv.Perm Ω))) y).length),
      k ≤ Nat.card Ω := by
    intro k hk
    obtain ⟨sb, -, rfl⟩ := List.mem_map.1 hk
    simp only [comparisonInstances, List.length_map, Finset.length_toList]
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _
  refine le_trans (List.sum_le_card_nsmul _ _ hb) ?_
  simp only [List.length_map, Finset.length_toList, Finset.card_univ, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (by
    rw [← Nat.card_eq_fintype_card]
    exact card_imgOn_le_factorial s.le)

theorem mem_calls_comparisonRound (s : Stage ϕ x T) (π : Equiv.Perm Ω) (y : Ω → Λ)
    {I : SIInstance Ω Λ} (hI : I ∈ (comparisonRound s π y).calls) :
    ∃ u ∈ s.aff, I.Δ = (orbit (kerN s) u : Set Ω) := by
  rw [calls_comparisonRound, List.mem_flatMap] at hI
  obtain ⟨sb, -, hI⟩ := hI
  obtain ⟨u, hu, rfl⟩ := (mem_comparisonInstances s _ y).1 hI
  exact ⟨u, hu, rfl⟩

/-- Line 04x: the empty comparison set stays empty. Otherwise use a representative
from the answers already collected, as line 04c0 requires. -/
noncomputable def updateComparison (s : Stage ϕ x T) (y : Ω → Λ)
    (Q : Set (Equiv.Perm Ω)) : SIReduction Ω Λ (Set (Equiv.Perm Ω)) :=
  if h : Q.Nonempty then comparisonRound s h.some y else .done ∅

theorem run_updateComparison (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G) (i : ℕ) :
    (updateComparison (stages ϕ x T i) y (pairedQ ϕ x y T σ₀ i)).run =
      pairedQ ϕ x y T σ₀ (i + 1) := by
  rw [updateComparison]
  split
  · rename_i h
    rw [run_comparisonRound, ← pairedQ_eq_coset hσ₀ i h.some_mem, ← pairedQ_succ]
  · rename_i h
    have he : pairedQ ϕ x y T σ₀ i = ∅ := Set.not_nonempty_iff_eq_empty.1 h
    rw [SIReduction.run_done, pairedQ_succ, he]
    ext σ
    simp [wIso]

theorem length_calls_updateComparison (s : Stage ϕ x T) (y : Ω → Λ)
    (Q : Set (Equiv.Perm Ω)) :
    (updateComparison s y Q).calls.length ≤ Nat.factorial T.ncard * Nat.card Ω := by
  unfold updateComparison
  split
  · exact length_calls_comparisonRound _ _ _
  · simp

theorem mem_calls_updateComparison (s : Stage ϕ x T) (y : Ω → Λ)
    (Q : Set (Equiv.Perm Ω)) {I : SIInstance Ω Λ}
    (hI : I ∈ (updateComparison s y Q).calls) :
    ∃ u ∈ s.aff, I.Δ = (orbit (kerN s) u : Set Ω) := by
  unfold updateComparison at hI
  split at hI
  · exact mem_calls_comparisonRound _ _ _ hI
  · simp at hI

/-- The live state carries `(W, H(W), Q)`. An empty `Q` rejects the comparison. -/
noncomputable def comparisonState (W : Set Ω) (H Q : Set (Equiv.Perm Ω)) :
    Option (Set Ω × Set (Equiv.Perm Ω) × Set (Equiv.Perm Ω)) :=
  if Q.Nonempty then some (W, H, Q) else none

variable (ϕ x T)

/-- The paired loop of Proposition 13.1.11, §13.1. Each live round computes both
`L` (line 04e1) and `R` (line 04e2) from oracle answers. Line 04x stops all later calls
when `R` is empty. The source stages supply the same round schedule as `loopReduction`.
The target windows are transported by a representative of `Q`, as `pairedQ_window`
proves. Thus no second run of automorphism calls is needed. -/
noncomputable def pairedLoopReduction (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) :
    ℕ → SIReduction Ω Λ (Option (Set Ω × Set (Equiv.Perm Ω) × Set (Equiv.Perm Ω)))
  | 0 => .done (comparisonState ∅ (bigGT ϕ T : Set (Equiv.Perm Ω))
      (σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω))))
  | i + 1 => (pairedLoopReduction y σ₀ i).bind fun
      | none => .done none
      | some p =>
        (recomputeReduction (stages ϕ x T i) (comparisonLift (stages ϕ x T i))).bind fun L =>
        (updateComparison (stages ϕ x T i) y p.2.2).bind fun R =>
          .done (comparisonState (affOf ϕ T p.2.1) (p.2.1 ∩ L) R)

variable {ϕ x T}

theorem pairedQ_succ_empty (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) (i : ℕ)
    (h : ¬ (pairedQ ϕ x y T σ₀ i).Nonempty) :
    pairedQ ϕ x y T σ₀ (i + 1) = ∅ := by
  rw [pairedQ_succ, Set.not_nonempty_iff_eq_empty.1 h]
  ext σ
  simp [wIso]

/-- The true oracle maintains the repaired invariant at every stage. This includes the
source group, read from the automorphism answers, and `Q`, read from the comparison
answers. Rejection is exactly the case when the repaired `Q` is empty. -/
theorem run_pairedLoopReduction (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G) (i : ℕ) :
    (pairedLoopReduction ϕ x T y σ₀ i).run =
      comparisonState (stages ϕ x T i).W ((stages ϕ x T i).H : Set (Equiv.Perm Ω))
        (pairedQ ϕ x y T σ₀ i) := by
  induction i with
  | zero =>
    have hQ : pairedQ ϕ x y T σ₀ 0 = σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω)) := by
      ext σ
      simp [pairedQ, stages, Stage.init, wIso]
    rw [hQ]
    rfl
  | succ i ih =>
    rw [pairedLoopReduction, SIReduction.run_bind, ih]
    by_cases hQ : (pairedQ ϕ x y T σ₀ i).Nonempty
    · rw [comparisonState, if_pos hQ]
      simp only [SIReduction.run_bind, SIReduction.run_done]
      rw [run_recomputeReduction _ _ (comparisonLift_spec _),
        run_updateComparison y σ₀ hσ₀ i, affOf_coe]
      have he : ((stages ϕ x T i).H : Set (Equiv.Perm Ω)) ∩
          ((stages ϕ x T i).step.H : Set (Equiv.Perm Ω)) =
          ((stages ϕ x T i).step.H : Set (Equiv.Perm Ω)) :=
        Set.inter_eq_self_of_subset_right (fun _ h => (stages ϕ x T i).step_H_le h)
      rw [he]
      rfl
    · rw [comparisonState, if_neg hQ, pairedQ_succ_empty y σ₀ i hQ]
      simp [comparisonState]

theorem length_calls_pairedLoopReduction (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) (i : ℕ) :
    (pairedLoopReduction ϕ x T y σ₀ i).calls.length ≤
      i * (2 * (Nat.factorial T.ncard * Nat.card Ω)) := by
  induction i with
  | zero => simp [pairedLoopReduction]
  | succ i ih =>
    rw [pairedLoopReduction, SIReduction.calls_bind, List.length_append]
    cases hp : (pairedLoopReduction ϕ x T y σ₀ i).run with
    | none => simpa using ih.trans (Nat.mul_le_mul_right _ (Nat.le_succ i))
    | some p =>
      simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
        List.length_append]
      have hL := length_calls_recomputeReduction (stages ϕ x T i)
        (comparisonLift (stages ϕ x T i))
      have hR := length_calls_updateComparison (stages ϕ x T i) y p.2.2
      nlinarith

theorem mem_calls_pairedLoopReduction (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) (i : ℕ)
    {I : SIInstance Ω Λ} (hI : I ∈ (pairedLoopReduction ϕ x T y σ₀ i).calls) :
    ∃ j < i, ∃ u ∈ (stages ϕ x T j).aff,
      I.Δ = (orbit (kerN (stages ϕ x T j)) u : Set Ω) := by
  induction i with
  | zero => simp [pairedLoopReduction] at hI
  | succ i ih =>
    rw [pairedLoopReduction, SIReduction.calls_bind, List.mem_append] at hI
    rcases hI with hI | hI
    · obtain ⟨j, hj, hu⟩ := ih hI
      exact ⟨j, by omega, hu⟩
    · cases hp : (pairedLoopReduction ϕ x T y σ₀ i).run with
      | none => simp [hp] at hI
      | some p =>
        simp only [hp, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
          List.mem_append] at hI
        rcases hI with hI | hI
        · obtain ⟨u, hu, hΔ⟩ := mem_calls_recomputeReduction _ _ hI
          exact ⟨i, by omega, u, hu, hΔ⟩
        · obtain ⟨u, hu, hΔ⟩ := mem_calls_updateComparison _ _ _ hI
          exact ⟨i, by omega, u, hu, hΔ⟩

variable (ϕ x T)

/-- **Proposition 13.1.11**, §13.1, as a named reduction. Line 01 starts with the coset
of a permutation carrying `T` to `T'`. The final value is assembled from the comparison
answers. Its specification is `compareIso`, proved in `run_pairedComparisonReduction`. -/
noncomputable def pairedComparisonReduction (y : Ω → Λ) (σ₀ : Equiv.Perm Ω) :
    SIReduction Ω Λ (Set (Equiv.Perm Ω)) :=
  (pairedLoopReduction ϕ x T y σ₀ (haltIndex ϕ x T)).bind fun p =>
    .done (p.elim ∅ fun q => q.2.2)

variable {ϕ x T}

theorem run_pairedComparisonReduction (y : Ω → Λ) (hset : LocalCertSetting G ϕ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ)
    {T' : Set Γ} (hT' : T'.ncard = T.ncard) [Nonempty Ω]
    (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G)
    (hmap : testImage ϕ T ⟨σ₀, hσ₀⟩ = T') :
    (pairedComparisonReduction ϕ x T y σ₀).run = compareIso ϕ x y T T' := by
  rw [pairedComparisonReduction, SIReduction.run_bind,
    run_pairedLoopReduction y σ₀ hσ₀, SIReduction.run_done,
    ← pairedQ_out_eq_compareIso hset ht htm hT' σ₀ hσ₀ hmap]
  unfold comparisonState
  split
  · rfl
  · rename_i h
    exact (Set.not_nonempty_iff_eq_empty.1 h).symm

/-- **Proposition 13.1.11**, §13.1, all calls of the paired reduction. Both line 04e1
and line 04e2 are charged. This proves `2 * t! * n²`, twice the printed bound, on windows
of size at most `n/t`. The printed bound `t!·n²` is
`Babai.proposition_13_1_11_paired_calls_sharp`; see entry 102 of the corrected paper. -/
theorem proposition_13_1_11_paired_calls (y : Ω → Λ) (h5 : 5 ≤ T.ncard)
    (σ₀ : Equiv.Perm Ω) :
    (pairedComparisonReduction ϕ x T y σ₀).calls.length ≤
        2 * Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (pairedComparisonReduction ϕ x T y σ₀).calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  have hc : (pairedComparisonReduction ϕ x T y σ₀).calls =
      (pairedLoopReduction ϕ x T y σ₀ (haltIndex ϕ x T)).calls := by
    simp [pairedComparisonReduction]
  rw [hc]
  constructor
  · refine (length_calls_pairedLoopReduction y σ₀ _).trans ?_
    calc haltIndex ϕ x T * (2 * (Nat.factorial T.ncard * Nat.card Ω))
        ≤ Nat.card Ω * (2 * (Nat.factorial T.ncard * Nat.card Ω)) :=
          Nat.mul_le_mul_right _ haltIndex_le_card
      _ = 2 * Nat.factorial T.ncard * (Nat.card Ω) ^ 2 := by ring
  · intro I hI
    obtain ⟨j, hj, u, hu, hΔ⟩ := mem_calls_pairedLoopReduction y σ₀ _ hI
    rw [hΔ]
    exact orbit_kerN_card_le (stages ϕ x T j)
      (loopCond_of_lt_haltIndex ϕ x T hj).1 h5 hu

variable (ϕ x T)

/-- **Proposition 13.1.11**, §13.1, for any pair of test sets. Choose the initial
transporter on line 01 from the group and the test sets. If none exists, the test-set
condition already rules out the comparison. This selection inspects no string letters. -/
noncomputable def compareReduction (y : Ω → Λ) (T' : Set Γ) :
    SIReduction Ω Λ (Set (Equiv.Perm Ω)) :=
  if h : ∃ σ : G, testImage ϕ T σ = T' then
    pairedComparisonReduction ϕ x T y (h.choose : Equiv.Perm Ω)
  else .done ∅

variable {ϕ x T}

/-- **Proposition 13.1.11**, §13.1: the true oracle returns `compareIso` for all pairs
of test sets of the stated size. -/
theorem run_compareReduction (y : Ω → Λ) (T' : Set Γ)
    (hset : LocalCertSetting G ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) (hT' : T'.ncard = T.ncard) [Nonempty Ω] :
    (compareReduction ϕ x T y T').run = compareIso ϕ x y T T' := by
  unfold compareReduction
  split
  · rename_i h
    exact run_pairedComparisonReduction y hset ht htm hT' _ h.choose.property h.choose_spec
  · rename_i h
    rw [SIReduction.run_done]
    symm
    apply Set.eq_empty_iff_forall_notMem.2
    intro σ hσ
    obtain ⟨hG, hm⟩ := compareIso_testImage ϕ x y T T' hset ht htm hT' hσ
    exact h ⟨⟨σ, hG⟩, hm⟩

/-- **Proposition 13.1.11**, §13.1: a reduction, its value, and the count of both kinds
of calls. The factor two charges lines 04e1 and 04e2 separately. These hypotheses are
inhabited: take the natural symmetric action on `Fin 90`, the identity representation,
a nine-point test set, and `T' = T`, as in `Correctness.lean`'s satisfiability example.
The same example works with `Fin 100`. The strings may be arbitrary. -/
theorem proposition_13_1_11_reduction (y : Ω → Λ) (T' : Set Γ)
    (hset : LocalCertSetting G ϕ) (ht : LargeK T.ncard (Nat.card Ω))
    (htm : 10 * T.ncard ≤ Nat.card Γ) (hT' : T'.ncard = T.ncard) [Nonempty Ω] :
    (compareReduction ϕ x T y T').run = compareIso ϕ x y T T' ∧
      (compareReduction ϕ x T y T').calls.length ≤
        2 * Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (compareReduction ϕ x T y T').calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  refine ⟨run_compareReduction y T' hset ht htm hT', ?_⟩
  have h5 : 5 ≤ T.ncard := by have := ht.eight_lt; omega
  unfold compareReduction
  split
  · exact proposition_13_1_11_paired_calls y h5 _
  · simp

/-- The union of the comparison calls is exactly the colored, truncated comparison
of line 04e2. This connects the original-alphabet oracle calls to the printed routine. -/
theorem run_comparisonRound_colored (y : Ω → Λ) (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (σ₀ : Equiv.Perm Ω) (hσ₀ : σ₀ ∈ G) (i : ℕ) (π : Equiv.Perm Ω)
    (hπ : π ∈ pairedQ ϕ x y T σ₀ i) :
    (comparisonRound (stages ϕ x T i) π y).run =
      strIso (pairedQ ϕ x y T σ₀ i)
        (truncate (colorByFace ϕ x T) (stages ϕ x T i).aff)
        (truncate (colorByFace ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩))
          (stages ϕ y (testImage ϕ T ⟨σ₀, hσ₀⟩) (i + 1)).W) := by
  rw [run_comparisonRound, ← pairedQ_eq_coset hσ₀ i hπ]
  exact pairedQ_colored_round hset hk σ₀ hσ₀ i _ (Set.Subset.refl _)

section ComparisonSatisfiable

private def comparisonTest100 : Set (Fin 100) := ↑((Finset.univ : Finset (Fin 100)).filter fun i => i.val < 9)

private theorem ncard_comparisonTest100 : comparisonTest100.ncard = 9 := by
  rw [comparisonTest100, Set.ncard_coe_finset]
  decide

private theorem comparison_logb_100_lt_seven : Real.logb 2 100 < 7 := by
  have h : Real.logb 2 100 < Real.logb 2 128 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 128 = 7 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one] <;>
      norm_num
  linarith

/-- The hypotheses of the paired comparison theorem hold for the natural symmetric
action with `n = m = 100` and `t = 9`. Take the second test set equal to the first and
any two strings to obtain a pair satisfying every hypothesis. Transitivity has a
witness point, so this example does not use an empty action. -/
theorem comparison_hypotheses_satisfiable : ∃ (G : Subgroup (Equiv.Perm (Fin 100))) (ϕ : G →* Equiv.Perm (Fin 100))
    (T : Set (Fin 100)),
    LocalCertSetting G ϕ ∧ T.ncard = 9 ∧ LargeK T.ncard (Nat.card (Fin 100)) ∧
      10 * T.ncard ≤ Nat.card (Fin 100) := by
  refine ⟨⊤, (⊤ : Subgroup (Equiv.Perm (Fin 100))).subtype, comparisonTest100, ⟨?_, ?_, ?_⟩, ncard_comparisonTest100, ?_, ?_⟩
  · -- `S(Ω)` is transitive: the orbit of `0` is everything
    refine ⟨0, ?_⟩
    ext b
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact mem_orbit_iff.2 ⟨⟨Equiv.swap 0 b, Subgroup.mem_top _⟩, by simp [Subgroup.smul_def]⟩
  · -- `ϕ = id` is a giant representation
    intro g _
    exact ⟨⟨g, Subgroup.mem_top _⟩, rfl⟩
  · -- `10 log₂ n ≤ m`
    have := comparison_logb_100_lt_seven
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast
    linarith
  · -- `max{8, 2 + log₂ n} < t`
    rw [LargeK, ncard_comparisonTest100, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := comparison_logb_100_lt_seven
    refine max_lt (by norm_num) ?_
    push_cast
    linarith
  · rw [ncard_comparisonTest100, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num

end ComparisonSatisfiable

end Babai
