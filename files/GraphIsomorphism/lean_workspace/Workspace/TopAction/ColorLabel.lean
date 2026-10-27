import Workspace.TopAction.TopAction4

/-! # A supplied labeling of the dominant color class

Section 12 uses the action on `C`. Naming its points by `Fin C.ncard` is data,
so a raw algorithm can use the labels it computes.
-/

universe u v
namespace Babai
open Equiv MulAction
open scoped Pointwise Classical
variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- §12, proof of Cor. 12.0.10: the giant representation of the window group with the
target `S([|C|])` that Cor. 12.0.8 asks for — `Babai.phiC` transported along
the supplied labeling. -/
noncomputable def phiCFinWith (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (e : C ≃ Fin C.ncard) :
    restrictTo (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C) →*
      Equiv.Perm (Fin C.ncard) :=
  (Equiv.permCongrHom e).toMonoidHom.comp (phiC hG ϕ hϕ hk C hC)

theorem isGiantRep_phiCFinWith (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (e : C ≃ Fin C.ncard) : IsGiantRep (phiCFinWith hG ϕ hϕ hk C hC e) := by
  intro δ hδ
  set β : Equiv.Perm (C : Set (Fin m)) := e.symm.permCongr δ with hβ
  have h1 : β ∈ alternatingGroup (C : Set (Fin m)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hβ, Equiv.Perm.sign_permCongr]
    exact hδ
  obtain ⟨g, hg⟩ := isGiantRep_phiC hG ϕ hϕ hk C hC h1
  refine ⟨g, ?_⟩
  rw [phiCFinWith, MonoidHom.comp_apply, hg]
  show e.permCongr β = δ
  rw [hβ, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- §12, proof of Cor. 12.0.10: the hypothesis *"the restriction of `Aut_G(x)^ϕ` to `C` is
a giant"* is exactly what Cor. 12.0.8 needs on the window, namely that `ϕ_C` maps
`Aut(x|_{Ω(C)})` onto a giant.

Given an even `δ ∈ A([|C|])`, transport it to `β ∈ A(C)` and extend it by the identity to
an even permutation `α` of `Γ` fixing `Γ ∖ C` pointwise.  The hypothesis produces a
`τ ∈ Aut_G(x)` with `τ^ϕ|_C = α|_C`; then `τ^ϕ` preserves `C`, so `τ ∈ G_C`, its
restriction to `Ω(C)` is an automorphism of `x|_{Ω(C)}`, and its `ϕ_C`-image is `β`,
i.e. its `phiCFinWith`-image is `δ`. -/
theorem mapsOntoGiant_phiCFinWith (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (e : C ≃ Fin C.ncard) (x : Ω → A)
    (hgiantC : ∀ α : Equiv.Perm (Fin m), α ∈ alternatingGroup (Fin m) →
      (∀ γ, γ ∉ C → α γ = γ) →
      ∃ β ∈ homImage ϕ (strAut (G : Set (Equiv.Perm Ω)) x), ∀ γ ∈ C, β γ = α γ) :
    MapsOntoGiant (phiCFinWith hG ϕ hϕ hk C hC e)
      (restrictStr (omegaOf ϕ C) x) := by
  intro δ hδ
  set β : Equiv.Perm (C : Set (Fin m)) := e.symm.permCongr δ with hβdef
  have hβ : β ∈ alternatingGroup (C : Set (Fin m)) := by
    rw [Equiv.Perm.mem_alternatingGroup, hβdef, Equiv.Perm.sign_permCongr]
    exact hδ
  set α : Equiv.Perm (Fin m) := Equiv.Perm.ofSubtype β with hαdef
  have hval : ∀ γ (hγ : γ ∈ C), α γ = ((β ⟨γ, hγ⟩ : C) : Fin m) :=
    fun γ hγ => Equiv.Perm.ofSubtype_apply_of_mem β hγ
  have hαalt : α ∈ alternatingGroup (Fin m) := by
    rw [Equiv.Perm.mem_alternatingGroup, hαdef, Equiv.Perm.sign_ofSubtype]
    exact hβ
  have hαfix : ∀ γ, γ ∉ C → α γ = γ := fun γ hγ =>
    Equiv.Perm.ofSubtype_apply_of_not_mem β hγ
  obtain ⟨b, hbmem, hbC⟩ := hgiantC α hαalt hαfix
  obtain ⟨τ, hτaut, hτG, hτϕ⟩ := hbmem
  -- `τ^ϕ` preserves `C` setwise
  have himgsub : (ϕ ⟨τ, hτG⟩) '' C ⊆ C := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hτϕ, hbC γ hγ, hval γ hγ]
    exact (β ⟨γ, hγ⟩).2
  have himg : (ϕ ⟨τ, hτG⟩) '' C = C :=
    Set.eq_of_subset_of_ncard_le himgsub
      (le_of_eq (Set.ncard_image_of_injective _ (ϕ ⟨τ, hτG⟩).injective).symm)
      (Set.toFinite _)
  have hτC : τ ∈ stabOn ϕ C := mem_stabOn.2 ⟨hτG, himg⟩
  -- the restriction of `τ` to the window
  set ρ : restrictTo (stabOn ϕ C) (omegaOf ϕ C)
      (isInvariant_omegaOf_stabOn ϕ hϕ hk C) :=
    ⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C) (isInvariant_omegaOf_stabOn ϕ hϕ hk C)
      ⟨τ, hτC⟩, ⟨⟨τ, hτC⟩, rfl⟩⟩ with hρdef
  refine ⟨(ρ : Equiv.Perm (omegaOf ϕ C)), ⟨ρ.2, ?_⟩, ρ.2, ?_⟩
  · -- `ρ` fixes the restricted string
    have hxτ : strAct x τ = x := hτaut.2
    funext w
    show restrictStr (omegaOf ϕ C) x ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) =
      restrictStr (omegaOf ϕ C) x w
    have h1 : ((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) : omegaOf ϕ C) : Ω) =
        (τ : Equiv.Perm Ω)⁻¹ (w : Ω) := by
      have h2 : (ρ : Equiv.Perm (omegaOf ϕ C))
          ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w) = w := by simp
      have h3 : ((((ρ : Equiv.Perm (omegaOf ϕ C))
          ((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) =
          (τ : Equiv.Perm Ω) (((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) :=
        rfl
      rw [h2] at h3
      rw [h3]
      simp
    show x (((((ρ : Equiv.Perm (omegaOf ϕ C))⁻¹ w)) : omegaOf ϕ C) : Ω) = x (w : Ω)
    rw [h1]
    exact congrFun hxτ (w : Ω)
  · -- the `phiCFinWith`-image of `ρ` is `δ`
    have hphi : phiC hG ϕ hϕ hk C hC ρ = psiC ϕ C ⟨τ, hτC⟩ :=
      phiC_restrictHom hG ϕ hϕ hk C hC ⟨τ, hτC⟩
    have hpsi : psiC ϕ C ⟨τ, hτC⟩ = β := by
      refine Equiv.ext fun γ => Subtype.ext ?_
      rw [coe_psiC_apply]
      have : (⟨(τ : Equiv.Perm Ω), stabOn_le ϕ C hτC⟩ : G) = ⟨τ, hτG⟩ := rfl
      rw [this, hτϕ, hbC (γ : Fin m) γ.2, hval (γ : Fin m) γ.2]
    rw [phiCFinWith, MonoidHom.comp_apply, hphi, hpsi]
    show e.permCongr β = δ
    rw [hβdef, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- The old representation is the supplied form at the old labeling. -/
theorem phiCFinWith_default (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) :
    phiCFinWith hG ϕ hϕ hk C hC (colorEquivFin C) = phiCFin hG ϕ hϕ hk C hC := rfl

/-- Cor. 12.0.10, §12: restricting a group element and then reading its supplied
color labels gives the labeled restriction of its top action. -/
theorem phiCFinWith_restrictHom (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m))
    (hC : m < 2 * C.ncard) (e : C ≃ Fin C.ncard) (g : stabOn ϕ C) :
    phiCFinWith hG ϕ hϕ hk C hC e
      ⟨restrictHom (stabOn ϕ C) (omegaOf ϕ C)
        (isInvariant_omegaOf_stabOn ϕ hϕ hk C) g, ⟨g, rfl⟩⟩ =
      e.permCongr (psiC ϕ C g) := by
  rw [phiCFinWith, MonoidHom.comp_apply, phiC_restrictHom]
  rfl

end Babai
