/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1: the coset form of Eqs. (62)-(63) on a window.
-/
import Workspace.Master.CosetForms
import Workspace.Master.GroupInstance

/-!
# The coset forms on a window

`Babai.alignInst` and `Babai.windowInstance` do **not** commute, so a branch that runs on a
window and is carried back to `Ω` has to be written in coset form all the way and aligned
once, at the top, over `Ω`.  What is needed for that is here: the full preimage of a coset
is a coset of the full preimage, so the lift of a coset instance is a coset instance.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ## The coset forms on a window

A branch that runs on the window `Δ` and is carried back to `Ω` by `Babai.liftWindow` has to
be written in coset form **all the way**, and aligned once at the top, over `Ω`.  The reason
is that `Babai.alignInst` and `Babai.windowInstance` do **not** commute: the representative
of the lifted coset `Babai.windowPreim K Δ h (σ · N)` is chosen by `Babai.cosetRepOf` on `Ω`,
and there is no reason for it to restrict to the representative chosen on `Δ`.

What is true, and is all that is needed, is that the lift of a coset instance is a coset
instance: `Babai.windowPreim` of a coset of `N` is a coset of `Babai.windowPreimSubgroup`. -/

section CosetWindow

variable {Ω : Type u} {A : Type v} {K : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

/-- **The full preimage of a coset is a coset of the full preimage.**  `σ̃` is any member of
`K` that restricts to `σ`. -/
theorem windowPreim_smul (h : IsInvariant K Δ) {N : Subgroup (Equiv.Perm Δ)}
    {σ : Equiv.Perm Δ} {σt : Equiv.Perm Ω} (hσK : σt ∈ K)
    (hres : restrictHom K Δ h ⟨σt, hσK⟩ = σ) :
    windowPreim K Δ h (σ • (N : Set (Equiv.Perm Δ)))
      = σt • ((windowPreimSubgroup K Δ h N : Subgroup (Equiv.Perm Ω)) :
          Set (Equiv.Perm Ω)) := by
  ext τ
  constructor
  · rintro ⟨hτK, hmem⟩
    obtain ⟨ν, hν, hνeq⟩ := hmem
    have hνeq' : σ * ν = restrictHom K Δ h ⟨τ, hτK⟩ := hνeq
    have hprod : σt⁻¹ * τ ∈ K := mul_mem (inv_mem hσK) hτK
    refine ⟨σt⁻¹ * τ, mem_windowPreimSubgroup.2 ⟨hprod, ?_⟩, ?_⟩
    · have hsplit : (⟨σt⁻¹ * τ, hprod⟩ : K) = (⟨σt, hσK⟩ : K)⁻¹ * ⟨τ, hτK⟩ := rfl
      rw [hsplit, map_mul, map_inv, hres, ← hνeq', inv_mul_cancel_left]
      exact hν
    · show σt * (σt⁻¹ * τ) = τ
      group
  · rintro ⟨μ, hμ, hτ⟩
    obtain ⟨hμK, hμN⟩ := mem_windowPreimSubgroup.1 hμ
    have hτ' : σt * μ = τ := hτ
    subst hτ'
    have hprod : σt * μ ∈ K := mul_mem hσK hμK
    refine ⟨hprod, ?_⟩
    have hsplit : (⟨σt * μ, hprod⟩ : K) = (⟨σt, hσK⟩ : K) * ⟨μ, hμK⟩ := rfl
    rw [hsplit, map_mul, hres]
    exact ⟨restrictHom K Δ h ⟨μ, hμK⟩, hμN, rfl⟩

/-- **The lift of a coset instance is a coset instance.**  This is what lets a branch be
written in coset form on the window and aligned once on `Ω`. -/
theorem isCosetInstance_windowInstance (h : IsInvariant K Δ) (x₀ : Ω → A)
    {J : SIInstance Δ A} (hJ : IsCosetInstance (restrictTo K Δ h) J) :
    IsCosetInstance K (windowInstance K Δ h x₀ J) := by
  obtain ⟨N, σ, hNle, hσ, hK, hinv⟩ := hJ
  obtain ⟨⟨σt, hσK⟩, hres⟩ := MonoidHom.mem_range.1 hσ
  refine ⟨windowPreimSubgroup K Δ h N, σt, windowPreimSubgroup_le h N, hσK, ?_, ?_⟩
  · show windowPreim K Δ h J.K = _
    rw [hK]
    exact windowPreim_smul h hσK hres
  · intro ρ hρ
    obtain ⟨hρK, hρN⟩ := mem_windowPreimSubgroup.1 hρ
    have hi := hinv _ hρN
    show (ρ : Equiv.Perm Ω) '' (Subtype.val '' J.Δ) = Subtype.val '' J.Δ
    rw [← Set.image_comp]
    have hcomp : ((ρ : Equiv.Perm Ω) : Ω → Ω) ∘ (Subtype.val : Δ → Ω) =
        (Subtype.val : Δ → Ω) ∘ (restrictHom K Δ h ⟨ρ, hρK⟩ : Equiv.Perm Δ) := by
      funext w
      exact (coe_restrictHom_apply h ⟨ρ, hρK⟩ w).symm
    rw [hcomp, Set.image_comp, hi]

end CosetWindow

end Babai
