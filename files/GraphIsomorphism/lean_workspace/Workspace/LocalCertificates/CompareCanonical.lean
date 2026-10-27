/-
Section 13.1 of Babai, version 2.5: transport of the comparison output.
-/
import Workspace.LocalCertificates.ComparePaired

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm Γ)

/-- Notations 13.1.9--13.1.10, §13.1: coloring and truncation transport with the input.
The hypotheses ensure the equivariance of the standard-block face. -/
theorem coloredWindow_strAct (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (x : Ω → Λ) (T : Set Γ) (τ : G) :
    truncate (colorByFace ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ))
        (windowOut ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)) =
      strAct (truncate (colorByFace ϕ x T) (windowOut ϕ x T)) (τ : Equiv.Perm Ω) := by
  symm
  apply (strAct_eq_iff).2
  intro u
  have hW := canonical_windowOut ϕ x T τ
  have hF := face_image ϕ T hset hk τ
  have hw : (τ : Equiv.Perm Ω) u ∈
      windowOut ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) ↔
      u ∈ windowOut ϕ x T := by
    rw [hW, Set.mem_image_equiv]
    simp
  have hf : (u ∈ face ϕ T) ↔ (τ : Equiv.Perm Ω) u ∈ face ϕ (testImage ϕ T τ) := by
    change _ ↔ (τ : Equiv.Perm Ω) u ∈ face ϕ ((ϕ τ : Equiv.Perm Γ) '' T)
    rw [← hF, Set.mem_image_equiv]
    simp
  by_cases hu : u ∈ windowOut ϕ x T
  · rw [truncate_of_mem hu, truncate_of_mem (hw.2 hu)]
    apply congrArg some
    exact Prod.ext (strAct_apply x (τ : Equiv.Perm Ω) u).symm (decide_eq_decide.2 hf)
  · rw [truncate_of_not_mem hu, truncate_of_not_mem (fun hv => hu (hw.1 hv))]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Transport both inputs independently. In Lean's left-action convention an arrow
`σ : x → y` becomes `β * σ * α⁻¹`. -/
theorem strIso_transport_pair {A : Type*} (a b : Ω → A) (α β : G) :
    strIso (G : Set (Equiv.Perm Ω)) (strAct a (α : Equiv.Perm Ω))
        (strAct b (β : Equiv.Perm Ω)) =
      (fun σ => (β : Equiv.Perm Ω) * σ * (α : Equiv.Perm Ω)⁻¹) ''
        strIso (G : Set (Equiv.Perm Ω)) a b := by
  ext τ
  constructor
  · rintro ⟨hτ, hr⟩
    refine ⟨(β : Equiv.Perm Ω)⁻¹ * τ * (α : Equiv.Perm Ω),
      ⟨G.mul_mem (G.mul_mem (G.inv_mem β.2) hτ) α.2, ?_⟩, by group⟩
    rw [strAct_eq_iff] at hr ⊢
    intro u
    have h := hr ((α : Equiv.Perm Ω) u)
    simpa [strAct, Equiv.Perm.mul_apply] using h
  · rintro ⟨σ, ⟨hσ, hr⟩, rfl⟩
    refine ⟨G.mul_mem (G.mul_mem β.2 hσ) (G.inv_mem α.2), ?_⟩
    rw [strAct_eq_iff] at hr ⊢
    intro u
    simpa [strAct, Equiv.Perm.mul_apply] using hr ((α : Equiv.Perm Ω)⁻¹ u)

/-- **Proposition 13.1.11**, §13.1, canonicity needed by the local guide of §13.2.
Independent isomorphisms of the two inputs transport the comparison output by the map
`σ ↦ β * σ * α⁻¹`. In particular, changing both inputs by the same isomorphism conjugates
this set. -/
theorem canonical_compareIso (hset : LocalCertSetting G ϕ)
    (hk : VeryLargeK (Nat.card Γ) (maxOrbitLength G))
    (x y : Ω → Λ) (T T' : Set Γ) (α β : G) :
    compareIso ϕ (strAct x (α : Equiv.Perm Ω)) (strAct y (β : Equiv.Perm Ω))
        (testImage ϕ T α) (testImage ϕ T' β) =
      (fun σ => (β : Equiv.Perm Ω) * σ * (α : Equiv.Perm Ω)⁻¹) '' compareIso ϕ x y T T' := by
  unfold compareIso
  rw [coloredWindow_strAct ϕ hset hk, coloredWindow_strAct ϕ hset hk]
  exact strIso_transport_pair _ _ α β

/-- **Proposition 13.1.11**, §13.1: the value computed by the paired reduction is
canonical under independent isomorphisms of its two inputs. The map on the answer is
`σ ↦ β * σ * α⁻¹`, the same map used by the local guide. -/
theorem canonical_compareReduction (hset : LocalCertSetting G ϕ)
    (x y : Ω → Λ) (T T' : Set Γ)
    (ht : LargeK T.ncard (Nat.card Ω)) (htm : 10 * T.ncard ≤ Nat.card Γ)
    (hT' : T'.ncard = T.ncard) [Nonempty Ω] (α β : G) :
    (compareReduction ϕ (strAct x (α : Equiv.Perm Ω)) (testImage ϕ T α)
        (strAct y (β : Equiv.Perm Ω)) (testImage ϕ T' β)).run =
      (fun σ => (β : Equiv.Perm Ω) * σ * (α : Equiv.Perm Ω)⁻¹) ''
        (compareReduction ϕ x T y T').run := by
  have ha : (testImage ϕ T α).ncard = T.ncard :=
    Set.ncard_image_of_injective _ (ϕ α).injective
  have hb : (testImage ϕ T' β).ncard = T'.ncard :=
    Set.ncard_image_of_injective _ (ϕ β).injective
  have hta : LargeK (testImage ϕ T α).ncard (Nat.card Ω) := by rwa [ha]
  have htma : 10 * (testImage ϕ T α).ncard ≤ Nat.card Γ := by rwa [ha]
  have he : (testImage ϕ T' β).ncard = (testImage ϕ T α).ncard := by rw [ha, hb, hT']
  rw [run_compareReduction _ _ hset hta htma he, run_compareReduction y T' hset ht htm hT']
  exact canonical_compareIso ϕ hset
    (veryLargeK_of_setting ϕ hset (by have := ht.eight_lt; omega)) x y T T' α β

end Babai
