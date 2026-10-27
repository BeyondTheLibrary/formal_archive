import Workspace.Algo.TopSuppliedPhase

/-! # The ordered lifting fold and the checked top-action tree

The machine keeps a coset accumulator. The checked reduction keeps the list
of lifting answers until all tests have finished. Both make the same ordered
calls and return the same value. The matching transport below preserves
every raw encoding of a correct answer, as required by `LoopMatchK`.
-/

namespace Algo

open Babai Equiv
open scoped Classical

universe u v w

/-- A phase depends on the ordered calls and its returned value along the
correct-answer path. All raw encodings of each such answer are still
universally quantified by this theorem. -/
theorem topcsLoopMatchK_congr {ι ω α Ω Λ β : Type*}
    {R : Round ι ω α} {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)} {I : ι}
    {w j : ℕ} {s : ω} {T : SIReduction Ω Λ β} {Q : β → ℕ → ℕ → ω → Prop}
    (h : LoopMatchK R decI decA I w j s T Q) :
    ∀ U : SIReduction Ω Λ β, T.calls = U.calls → T.run = U.run →
      LoopMatchK R decI decA I w j s U Q := by
  induction h with
  | done w j s b Q hb =>
    intro U hc hv
    cases U with
    | done b' =>
      simp only [SIReduction.run_done] at hv
      subst b'
      exact .done _ _ _ _ _ hb
    | call J k => simp only [SIReduction.calls_done, SIReduction.calls_call] at hc; cases hc
  | call w j s J k Q hc hn ih =>
    intro U he hv
    cases U with
    | done b => simp only [SIReduction.calls_done, SIReduction.calls_call] at he; cases he
    | call J' k' =>
      simp only [SIReduction.calls_call] at he
      obtain ⟨hJ, ht⟩ := List.cons.inj he
      subst J'
      simp only [SIReduction.run_call] at hv
      exact .call _ _ _ _ _ _ hc (fun a ha => ih a ha _ ht hv)

theorem topcsPhaseMatch_congr {ι ω α Ω Λ β : Type*}
    {R : Round ι ω α} {decI : ι → SIInstance Ω Λ} {decA : α → Set (Perm Ω)} {I : ι}
    {c j : ℕ} {s : ω} {T U : SIReduction Ω Λ β} {Q : β → ℕ → ω → Prop}
    (h : PhaseMatch R decI decA I c j s T Q) (hc : T.calls = U.calls) (hv : T.run = U.run) :
    PhaseMatch R decI decA I c j s U Q :=
  fun r => topcsLoopMatchK_congr (h r) U hc hv

/-- Fold the independent lifting chains in the supplied order. -/
noncomputable def topcsLiftFold {Ω Λ : Type*} (x y : Ω → Λ) (ws : List (Set Ω)) :
    List (Set (Perm Ω)) → Option (Set (Perm Ω)) → SIReduction Ω Λ (Option (Set (Perm Ω)))
  | [], acc => .done acc
  | C :: Cs, acc => (Babai.cosetChain x y ws C).bind
      (fun a => topcsLiftFold x y ws Cs (top1JoinSet acc a))

theorem topcsLiftFold_run {Ω Λ : Type*} (x y : Ω → Λ) (ws : List (Set Ω))
    (Cs : List (Set (Perm Ω))) (acc : Option (Set (Perm Ω))) :
    (topcsLiftFold x y ws Cs acc).run =
      (Cs.map (fun C => (Babai.cosetChain x y ws C).run)).foldl top1JoinSet acc := by
  induction Cs generalizing acc with
  | nil => rfl
  | cons C Cs ih => simp only [topcsLiftFold, SIReduction.run_bind, List.map_cons, List.foldl_cons, ih]

theorem topcsLiftFold_calls {Ω Λ : Type*} (x y : Ω → Λ) (ws : List (Set Ω))
    (Cs : List (Set (Perm Ω))) (acc : Option (Set (Perm Ω))) :
    (topcsLiftFold x y ws Cs acc).calls =
      Cs.flatMap (fun C => (Babai.cosetChain x y ws C).calls) := by
  induction Cs generalizing acc with
  | nil => rfl
  | cons C Cs ih => simp only [topcsLiftFold, SIReduction.calls_bind, List.flatMap_cons, ih]

theorem topcsCalls_expand {Ω Λ β : Type*}
    {f : SIInstance Ω Λ → SIReduction Ω Λ (Set (Perm Ω))} {P : SIInstance Ω Λ → Prop}
    (hf : ∀ I, P I → (f I).run = I.answer) :
    ∀ R : SIReduction Ω Λ β, (∀ I ∈ R.calls, P I) →
      (R.expand f).calls = R.calls.flatMap (fun I => (f I).calls) := by
  intro R
  induction R with
  | done a => intro _; rfl
  | call I k ih =>
    intro hR
    have hI := hR I (by simp [SIReduction.calls])
    rw [SIReduction.expand, SIReduction.calls_bind, hf I hI,
      SIReduction.calls_call, List.flatMap_cons, ih I.answer]
    intro J hJ
    exact hR J (by simp [SIReduction.calls, hJ])

section Giant

variable {Ω Λ : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)}
    {m : ℕ} (ψ : G →* alternatingGroup (Fin m)) (S : List (alternatingGroup (Fin m)))
    (E : OrbitEnum (kerSubgroup ψ)) (x y : Ω → Λ)

theorem topcsLiftFold_giant_calls :
    (topcsLiftFold x y E.windows ((1 :: S).map (preimageSet ψ)) (some ∅)).calls =
      (cosetGiantAWith ψ S E x y).calls := by
  rw [cosetGiantAWith, topcsCalls_expand
    (P := fun J : SIInstance Ω Λ => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)]
  · rw [topcsLiftFold_calls, calls_cosetTopAction1]
    simp only [List.flatMap_map]
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl

theorem topcsLiftFold_giant_run :
    (topcsLiftFold x y E.windows ((1 :: S).map (preimageSet ψ)) (some ∅)).run =
      (cosetGiantAWith ψ S E x y).run := by
  rw [cosetGiantAWith, SIReduction.run_expand_of_calls
    (P := fun J : SIInstance Ω Λ => J.Δ = Set.univ) (fun J hJ => E.run_chain J hJ)]
  · rw [topcsLiftFold_run, cosetTopAction1, SIReduction.run_bind, run_cosetLiftAll,
      SIReduction.run_done]
    have he : (((1 :: S).map (preimageSet ψ)).map
        (fun C => (Babai.cosetChain x y E.windows C).run)) =
        (1 :: S).map (liftingSet ψ x y) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro σ _
      rw [Function.comp_apply, Babai.run_cosetChain, E.cover, wIso_univ_preimageSet]
    rw [he]
    have hf := fold_top1JoinSet_empty ((1 :: S).map (liftingSet ψ x y)) (by simp)
    by_cases hh : ∀ A ∈ (1 :: S).map (liftingSet ψ x y), A.Nonempty
    · rw [if_pos hh] at hf ⊢
      exact hf
    · rw [if_neg hh] at hf ⊢
      exact hf
  · intro J hJ
    rw [calls_cosetTopAction1, List.mem_map] at hJ
    obtain ⟨σ, _, rfl⟩ := hJ
    rfl

end Giant

end Algo
