import Workspace.Master.Line4cdCore
import Workspace.Master.CosetHintTransport

/-! # Lifting a coset round and aligning once

This is an output interface for the rounds already built from live choice data.
The round is lifted to the ambient domain before any call is aligned.
-/

universe u v
namespace Babai
open Equiv
open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- The facts needed to lift a coset round. No live choice selects a reduction here. -/
structure CosetCore (W : Type u) [Fintype W] [DecidableEq W] (A : Type v)
    (G : Subgroup (Perm W)) (x y : W → A) (par cost : ℕ) where
  red : SIReduction W A (Set (Perm W))
  hint : (J : SIInstance W A) → Option (JohnsonCaseData J)
  run_red : red.run = strIso (G : Set (Perm W)) x y
  calls_coset : ∀ J ∈ red.calls, IsCosetInstance G J
  calls_length : red.calls.length ≤ cost
  hint_le : ∀ J d, hint J = some d → d.K ≤ G ∧ 2 * d.m ≤ par
  calls_progress : ∀ J ∈ red.calls,
    5 * J.windowSize ≤ 4 * Fintype.card W ∨ (hint (alignInst J)).isSome = true

theorem CosetCore.calls_K {G : Subgroup (Perm W)} {x y : W → A} {par cost : ℕ}
    (C : CosetCore W A G x y par cost) : ∀ J ∈ C.red.calls, J.K ⊆ (G : Set (Perm W)) :=
  fun J hJ => (C.calls_coset J hJ).K_subset

noncomputable def Line4cdData.toCosetCore {G : Subgroup (Perm W)} {x y : W → A}
    {par cost : ℕ} (C : Line4cdData W A G x y par cost) : CosetCore W A G x y par cost where
  red := C.shape.red
  hint := C.shape.hint
  run_red := C.run_red
  calls_coset := C.calls_coset
  calls_length := C.calls_length
  hint_le := C.hint_le
  calls_progress := C.calls_progress

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
  {K : Subgroup (Perm Ω)} {Δ : Set Ω} {hinv : IsInvariant K Δ}
  {x y : Ω → A} {par cost : ℕ}

/-- The value is unchanged when the root is a group instance. -/
theorem run_alignLiftWindow_core
    (C : CosetCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (I : SIInstance Ω A) (hK : I.K = (K : Set (Perm Ω))) (hΔ : I.Δ = Δ)
    (hx : I.x = x) (hy : I.y = y) :
    (SIReduction.alignRed I (liftWindow K Δ hinv x C.red)).run = I.answer := by
  rw [run_alignRed_of_one_mem (show (1 : Perm Ω) ∈ I.K by rw [hK]; exact K.one_mem),
    run_liftWindow hinv x y C.red C.calls_K C.run_red, SIInstance.answer, hK, hΔ, hx, hy]

theorem calls_alignLiftWindow_core_group
    (C : CosetCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (I : SIInstance Ω A) (x₀ : Ω → A) :
    ∀ J ∈ (SIReduction.alignRed I (liftWindow K Δ hinv x₀ C.red)).calls, IsGroupInstance J := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  exact isGroupInstance_alignInst
    (calls_liftWindow_isCosetInstance hinv x₀ C.red C.calls_K C.calls_coset J' hJ')

theorem calls_length_alignLiftWindow_core
    (C : CosetCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (I : SIInstance Ω A) (x₀ : Ω → A) :
    (SIReduction.alignRed I (liftWindow K Δ hinv x₀ C.red)).calls.length ≤ cost := by
  rw [calls_length_alignRed, calls_length_liftWindow hinv x₀ C.red C.calls_K]
  exact C.calls_length

/-- The final alignment preserves window sizes and the halved Johnson parameter. -/
theorem decreases_alignLiftWindow_core
    (C : CosetCore Δ A (restrictTo K Δ hinv) (restrictStr Δ x) (restrictStr Δ y) par cost)
    (I : SIInstance Ω A) (x₀ : Ω → A) (hcard : Fintype.card Δ = Δ.ncard) :
    ∀ J ∈ (SIReduction.alignRed I (liftWindow K Δ hinv x₀ C.red)).calls,
      5 * J.windowSize ≤ 4 * Δ.ncard ∨
        (J.windowSize ≤ Δ.ncard ∧
          2 * param (⟨J, cosetWindowHintLift hinv x₀ C.hint J⟩ : HintedInstance Ω A) ≤ par) := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J₀, hJ₀, rfl⟩ := hJ
  have hsize : (alignInst J₀).windowSize ≤ Δ.ncard :=
    windowSize_le_of_calls_liftWindow x₀ C.red C.calls_K (Set.toFinite _) J₀ hJ₀
  rw [calls_liftWindow hinv x₀ C.red C.calls_K, List.mem_map] at hJ₀
  obtain ⟨J', hJ', rfl⟩ := hJ₀
  rcases C.calls_progress J' hJ' with hsmall | hhint
  · left
    rw [windowSize_alignInst, windowSize_windowInstance hinv x₀ J', ← hcard]
    exact hsmall
  · refine Or.inr ⟨hsize, ?_⟩
    have hrec : CosetLiftedHint K Δ hinv x₀ C.hint
        (alignInst (windowInstance K Δ hinv x₀ J')) :=
      ⟨alignInst J', (K_alignInst_windowInstance hinv x₀ (C.calls_coset J' hJ')).symm,
        rfl, hhint, fun d hd => (C.hint_le _ d hd).1⟩
    obtain ⟨J'', d, hd, hp⟩ := param_cosetWindowHintLift hinv x₀ hrec
    rw [hp]
    exact (C.hint_le J'' d hd).2

end Babai
