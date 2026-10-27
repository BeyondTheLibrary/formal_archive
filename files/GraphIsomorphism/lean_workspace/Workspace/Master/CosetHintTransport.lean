import Workspace.Master.HintTransport

/-! # Hints after the final window lift

Alignment and the window lift can choose different representatives. Their groups
and windows agree. Johnson data depends on these two fields, so it can be carried
to either instance without making the representatives agree.
-/

namespace Babai
open Equiv
open scoped Pointwise

variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Changing the strings leaves all Johnson case data valid. -/
def JohnsonCaseData.retarget {I J : SIInstance Ω A} (d : JohnsonCaseData I)
    (hK : I.K = J.K) (hΔ : I.Δ = J.Δ) : JohnsonCaseData J := by
  rcases I with ⟨K, Δ, x, y⟩
  rcases J with ⟨K', Δ', x', y'⟩
  dsimp only at hK hΔ
  subst K'
  subst Δ'
  exact { d with }

@[simp] theorem JohnsonCaseData.retarget_m {I J : SIInstance Ω A} (d : JohnsonCaseData I)
    (hK : I.K = J.K) (hΔ : I.Δ = J.Δ) : (d.retarget hK hΔ).m = d.m := by
  rcases I with ⟨K, Δ, x, y⟩
  rcases J with ⟨K', Δ', x', y'⟩
  dsimp only at hK hΔ
  subst K'
  subst Δ'
  rfl

/-- A hinted window instance has the same group and window as the lifted call. -/
def CosetLiftedHint (K : Subgroup (Perm Ω)) (Δ : Set Ω) (hinv : IsInvariant K Δ)
    (x₀ : Ω → A) (H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J'))
    (J : SIInstance Ω A) : Prop :=
  ∃ J' : SIInstance Δ A,
    (windowInstance K Δ hinv x₀ J').K = J.K ∧
    (windowInstance K Δ hinv x₀ J').Δ = J.Δ ∧ (H J').isSome = true ∧
    ∀ d : JohnsonCaseData J', H J' = some d → d.K ≤ restrictTo K Δ hinv

open scoped Classical in
/-- Lift Johnson data using the group and window shared by the two aligned calls. -/
noncomputable def cosetWindowHintLift {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    (H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J')) (J : SIInstance Ω A) :
    Option (JohnsonCaseData J) :=
  if h : CosetLiftedHint K Δ hinv x₀ H J then
    some ((((H h.choose).get h.choose_spec.2.2.1).ofWindow hinv x₀
      (h.choose_spec.2.2.2 _ (Option.some_get h.choose_spec.2.2.1).symm)).retarget
        h.choose_spec.1 h.choose_spec.2.1)
  else none

theorem param_cosetWindowHintLift {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant K Δ) (x₀ : Ω → A)
    {H : (J' : SIInstance Δ A) → Option (JohnsonCaseData J')} {J : SIInstance Ω A}
    (h : CosetLiftedHint K Δ hinv x₀ H J) :
    ∃ (J' : SIInstance Δ A) (d : JohnsonCaseData J'), H J' = some d ∧
      param (⟨J, cosetWindowHintLift hinv x₀ H J⟩ : HintedInstance Ω A) = d.m := by
  classical
  refine ⟨h.choose, (H h.choose).get h.choose_spec.2.2.1,
    (Option.some_get h.choose_spec.2.2.1).symm, ?_⟩
  rw [cosetWindowHintLift, dif_pos h]
  exact (JohnsonCaseData.retarget_m _ _ _).trans (JohnsonCaseData.ofWindow_m _ _ _ _)

/-- The two orders of lifting and alignment have the same candidate group. -/
theorem K_alignInst_windowInstance {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    (h : IsInvariant K Δ) (x₀ : Ω → A) {J : SIInstance Δ A}
    (hJ : IsCosetInstance (restrictTo K Δ h) J) :
    (alignInst (windowInstance K Δ h x₀ J)).K =
      (windowInstance K Δ h x₀ (alignInst J)).K := by
  obtain ⟨N, σ, hN, hσ, hK, hi⟩ := hJ
  obtain ⟨⟨τ, hτ⟩, he⟩ := MonoidHom.mem_range.1 hσ
  have hdown : (alignInst J).K = (N : Set (Perm Δ)) := by
    rcases J with ⟨C, D, x, y⟩
    dsimp only at hK
    subst C
    exact K_alignInst_smul_coe _ _ _ _ _
  have hup : (windowInstance K Δ h x₀ J).K =
      τ • (windowPreimSubgroup K Δ h N : Set (Perm Ω)) := by
    change windowPreim K Δ h J.K = _
    rw [hK, windowPreim_smul h hτ he]
  have ha : (alignInst (windowInstance K Δ h x₀ J)).K =
      (windowPreimSubgroup K Δ h N : Set (Perm Ω)) := by
    generalize windowInstance K Δ h x₀ J = L at hup ⊢
    rcases L with ⟨C, D, x, y⟩
    dsimp only at hup
    subst C
    exact K_alignInst_smul_coe _ _ _ _ _
  rw [ha, coe_windowPreimSubgroup]
  change _ = windowPreim K Δ h (alignInst J).K
  rw [hdown]

end Babai
