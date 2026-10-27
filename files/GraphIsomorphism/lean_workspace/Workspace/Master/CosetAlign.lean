import Workspace.Master.Bridge
import Workspace.Master.CosetForms

/-! # Procedure Align with unshifted strings

Sec. 14.1, lines 1–6, in the coset form of Eqs. (62)–(63). The initial candidate
set is the transporter of the two structures. Each color class is then a window
of `cosetChain`. Both the version order and the window order are inputs.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} {Γ 𝒳 : Type*}
  [MulAction (Perm Γ) 𝒳] {G : Subgroup (Perm Ω)}

/-- Sec. 14.1, lines 1–3: the preimage of the structure transporter. -/
def alignTransporter (ϕ : G →* Perm Γ) (X Y : 𝒳) : Set (Perm Ω) :=
  {τ | ∃ h : τ ∈ G, (ϕ ⟨τ, h⟩) • X = Y}

/-- Eq. (70): any structure isomorphism gives the same coset of the source stabilizer. -/
theorem alignTransporter_eq_smul (ϕ : G →* Perm Γ) (X Y : 𝒳) (σ : G)
    (hσ : (ϕ σ) • X = Y) :
    alignTransporter ϕ X Y =
      (σ : Perm Ω) • (preimageSubgroup ϕ (structAut X) : Set (Perm Ω)) := by
  ext τ
  rw [mem_perm_smul_set]
  constructor
  · rintro ⟨hτ, hτX⟩
    refine mem_preimageSubgroup.2 ⟨G.mul_mem (G.inv_mem σ.2) hτ, mem_structAut.2 ?_⟩
    change ϕ (σ⁻¹ * ⟨τ, hτ⟩) • X = X
    rw [map_mul, map_inv, mul_smul, hτX, ← hσ, inv_smul_smul]
  · intro hτ
    obtain ⟨hρ, hfix⟩ := mem_preimageSubgroup.1 hτ
    have hG : τ ∈ G := by
      have := G.mul_mem σ.2 hρ
      simpa only [mul_inv_cancel_left] using this
    refine ⟨hG, ?_⟩
    have he : (⟨τ, hG⟩ : G) = σ * ⟨(σ : Perm Ω)⁻¹ * τ, hρ⟩ :=
      Subtype.ext (by simp)
    rw [he, map_mul, mul_smul, mem_structAut.1 hfix, hσ]

/-- The transporter restricts the string isomorphisms to one pair of versions. -/
theorem strIso_alignTransporter (ϕ : G →* Perm Γ) (x y : Ω → A) (X Y : 𝒳) :
    strIso (alignTransporter ϕ X Y) x y = versionPiece ϕ x y X Y := by
  ext τ
  constructor
  · rintro ⟨⟨hG, hXY⟩, hxy⟩
    exact ⟨⟨hG, hxy⟩, hG, hXY⟩
  · rintro ⟨⟨_, hxy⟩, hG, hXY⟩
    exact ⟨⟨hG, hXY⟩, hxy⟩

/-- Sec. 14.1, lines 1–6: process the supplied color classes without shifting the strings. -/
noncomputable def cosetAlignChain (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X Y : 𝒳) (windows : List (Set Ω)) : SIReduction Ω A (Set (Perm Ω)) :=
  cosetChain x y windows (alignTransporter ϕ X Y)

/-- The coset form computes the part of Eq. (70) belonging to this pair of versions. -/
theorem run_cosetAlignChain (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X Y : 𝒳) (windows : List (Set Ω))
    (hcover : (⋃ Δ ∈ windows, Δ) = Set.univ) :
    (cosetAlignChain ϕ x y X Y windows).run = versionPiece ϕ x y X Y := by
  rw [cosetAlignChain, run_cosetChain, hcover, wIso_univ, strIso_alignTransporter]

/-- Line 5 asks at most one question per supplied color class. -/
theorem calls_length_cosetAlignChain (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X Y : 𝒳) (windows : List (Set Ω)) :
    (cosetAlignChain ϕ x y X Y windows).calls.length ≤ windows.length :=
  (calls_cosetChain x y windows _).1

/-- Every question has a window in the supplied list. -/
theorem calls_cosetAlignChain_window (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X Y : 𝒳) (windows : List (Set Ω)) :
    ∀ J ∈ (cosetAlignChain ϕ x y X Y windows).calls, J.Δ ∈ windows :=
  (calls_cosetChain x y windows _).2

/-- Eq. (71), in coset form: process the supplied versions in their supplied order. -/
noncomputable def cosetDesignAlign (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X : 𝒳) (versions : List 𝒳) (windows : List (Set Ω)) :
    SIReduction Ω A (Set (Perm Ω)) :=
  SIReduction.unionOver versions (fun Y => cosetAlignChain ϕ x y X Y windows)

/-- Eq. (71): any list covering the versions gives the same value. -/
theorem run_cosetDesignAlign (ϕ : G →* Perm Γ) (x y : Ω → A)
    {Vers : (Ω → A) → Set 𝒳} (hcan : IsCanonicalVersions ϕ Vers)
    (X : 𝒳) (hX : X ∈ Vers x) (versions : List 𝒳)
    (hversions : ∀ Y, Y ∈ versions ↔ Y ∈ Vers y) (windows : List (Set Ω))
    (hcover : (⋃ Δ ∈ windows, Δ) = Set.univ) :
    (cosetDesignAlign ϕ x y X versions windows).run = strIso (G : Set (Perm Ω)) x y := by
  rw [cosetDesignAlign, SIReduction.run_unionOver,
    strIso_eq_iUnion_versionPiece hcan x y hX]
  simp only [run_cosetAlignChain ϕ x y _ _ windows hcover, hversions]

/-- Eq. (71): the number of questions is at most versions times color classes. -/
theorem calls_length_cosetDesignAlign (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X : 𝒳) (versions : List 𝒳) (windows : List (Set Ω)) :
    (cosetDesignAlign ϕ x y X versions windows).calls.length ≤
      versions.length * windows.length :=
  SIReduction.calls_length_unionOver _
    (fun Y => calls_length_cosetAlignChain ϕ x y X Y windows) versions

section CosetInstances

variable [Fintype Ω] [DecidableEq Ω]

/-- Remark 11.1.5(ii): each question is a coset instance, because the source
stabilizer preserves each listed color class. -/
theorem isCosetInstance_calls_cosetAlignChain (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X Y : 𝒳) (windows : List (Set Ω))
    (hinv : ∀ Δ ∈ windows, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ) :
    ∀ J ∈ (cosetAlignChain ϕ x y X Y windows).calls, IsCosetInstance G J := by
  intro J hJ
  by_cases h : (alignTransporter ϕ X Y).Nonempty
  · obtain ⟨σ, hσ, hXY⟩ := h
    exact isCosetInstance_calls_cosetChain (preimageSubgroup_le ϕ _) x y windows _ hinv
      ⟨_, σ, le_rfl, hσ, alignTransporter_eq_smul ϕ X Y ⟨σ, hσ⟩ hXY⟩ J hJ
  · have he : alignTransporter ϕ X Y = ∅ := Set.not_nonempty_iff_eq_empty.1 h
    simp [cosetAlignChain, he] at hJ

/-- All questions in Eq. (71) are coset instances in the original group. -/
theorem isCosetInstance_calls_cosetDesignAlign (ϕ : G →* Perm Γ) (x y : Ω → A)
    (X : 𝒳) (versions : List 𝒳) (windows : List (Set Ω))
    (hinv : ∀ Δ ∈ windows, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ) :
    ∀ J ∈ (cosetDesignAlign ϕ x y X versions windows).calls, IsCosetInstance G J :=
  SIReduction.mem_calls_unionOver _
    (fun Y => isCosetInstance_calls_cosetAlignChain ϕ x y X Y windows hinv) versions

/-- Remark 11.1.4 turns all questions of the coset form into group instances. -/
theorem isGroupInstance_calls_alignRed_cosetDesignAlign (I : SIInstance Ω A)
    (ϕ : G →* Perm Γ) (x y : Ω → A) (X : 𝒳) (versions : List 𝒳)
    (windows : List (Set Ω))
    (hinv : ∀ Δ ∈ windows, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ) :
    ∀ J ∈ (SIReduction.alignRed I (cosetDesignAlign ϕ x y X versions windows)).calls,
      IsGroupInstance J ∧ J.K ⊆ (G : Set (Perm Ω)) := by
  intro J hJ
  rw [calls_alignRed, List.mem_map] at hJ
  obtain ⟨J', hJ', rfl⟩ := hJ
  have h := isCosetInstance_calls_cosetDesignAlign ϕ x y X versions windows hinv J' hJ'
  exact ⟨isGroupInstance_alignInst h, K_alignInst_subset h⟩

end CosetInstances

end Babai
