/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: the canonicity of the families produced by Procedure LocalCertificates
(last sentence of Theorem 13.1.3, and Proposition 13.1.8 (v)).
-/
import Workspace.LocalCertificates.Window

/-!
# §13.1 Canonicity of the local certificates

Theorem 13.1.3 ends with

> The families `{(T, K(T)) : T ∈ F(x)}` and `{(T, M(T)) : T ∈ F̄(x)}` are canonical.

and Proposition 13.1.8 (v) says that the assignment `T ↦ W(T)` is canonical.

## What canonicity says here

The category (§6) is `GStrings`: the objects are the strings `x : Ω → Σ` on the fixed
domain `Ω`, and the morphisms `x → y` are the `G`-isomorphisms, i.e. the `τ ∈ G` with
`x^τ = y` (`Babai.GStrings`, §6).  An assignment defined on the objects is canonical
exactly when it is a functor, i.e. when it commutes with the morphisms; since all objects
have the same underlying set `Ω` and the morphisms are the elements of `G`, this is
equivariance: applying `τ ∈ G` to the input transforms the output by `τ`.

The input of Procedure LocalCertificates is a pair (string, test set), and `τ ∈ G` carries
`(x, T)` to `(x^τ, T^{τ^ϕ})`; the three outputs are a subset of `Ω`, a subgroup of `S(Ω)`
and a subgroup of `S(T)`, so they transform by `W ↦ W^τ`, `K ↦ τ⁻¹Kτ` (conjugation) and
`M ↦ M^{ψ_T(τ)}` (transport along the bijection `T → T^{τ^ϕ}` induced by `τ^ϕ`).

## Status

The proofs are by induction along the stages of the while loop: every line of the
procedure is built from `G_T`, `Aut^W`, `Aff` and the pointwise stabilizer, each of which
is equivariant, so `Stage.init`, `Stage.step`, `Stage.LoopCond` and hence `haltIndex` and
the outputs are equivariant.  Carrying this out means transporting a whole `Babai.Stage`
along `τ`, which is not done here; see the report.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ)

/-- The image `T^{τ^ϕ}` of the test set under `τ ∈ G`. -/
def testImage (τ : G) : Set Γ := (ϕ τ : Equiv.Perm Γ) '' T

theorem testImage_def (τ : G) : testImage ϕ T τ = (ϕ τ : Equiv.Perm Γ) '' T := rfl

@[simp] theorem mem_testImage {τ : G} {b : Γ} :
    b ∈ testImage ϕ T τ ↔ ∃ a ∈ T, (ϕ τ : Equiv.Perm Γ) a = b := Iff.rfl

/-! ### Conjugation by `τ`

Every object of the procedure is built from `G_T`, `Aut^W`, `Aff` and the pointwise
stabilizer, each of which is equivariant.  The elementary conjugation lemmas come first. -/

section Conj

variable {ϕ T}

/-- The bijection `T → T^{τ^ϕ}` induced by `τ^ϕ`.  It is the map along which the group
`M(T) ≤ S(T)` is transported. -/
def testEquiv (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) (τ : G) :
    (T : Set Γ) ≃ (testImage ϕ T τ : Set Γ) where
  toFun a := ⟨(ϕ τ : Equiv.Perm Γ) (a : Γ), ⟨(a : Γ), a.2, rfl⟩⟩
  invFun b := ⟨(ϕ τ : Equiv.Perm Γ).symm (b : Γ), by
    obtain ⟨c, hc, hb⟩ := b.2
    simpa [← hb] using hc⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp

@[simp] theorem testEquiv_apply (τ : G) (a : (T : Set Γ)) :
    ((testEquiv ϕ T τ a : (testImage ϕ T τ : Set Γ)) : Γ) = (ϕ τ : Equiv.Perm Γ) (a : Γ) := rfl

theorem mem_map_conj {K : Subgroup (Equiv.Perm Ω)} {τ σ : Equiv.Perm Ω} :
    σ ∈ K.map (MulAut.conj τ).toMonoidHom ↔ τ⁻¹ * σ * τ ∈ K := by
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    have h : τ⁻¹ * ((MulAut.conj τ).toMonoidHom ρ) * τ = ρ := by
      show τ⁻¹ * (τ * ρ * τ⁻¹) * τ = ρ
      group
    rwa [h]
  · intro h
    refine ⟨τ⁻¹ * σ * τ, h, ?_⟩
    show τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ
    group

/-- `ϕ` of a conjugate, as an element of `S(Γ)`. -/
theorem phi_conj (τ : G) {σ : Equiv.Perm Ω} (hσ : σ ∈ G)
    (h : (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ G) :
    (ϕ ⟨(τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω), h⟩ : Equiv.Perm Γ)
      = (ϕ τ : Equiv.Perm Γ)⁻¹ * (ϕ ⟨σ, hσ⟩ : Equiv.Perm Γ) * (ϕ τ : Equiv.Perm Γ) := by
  have he : (⟨(τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω), h⟩ : G)
      = τ⁻¹ * ⟨σ, hσ⟩ * τ := Subtype.ext rfl
  rw [he, map_mul, map_mul, map_inv]

/-- `ϕ(τστ⁻¹) = τ^ϕ σ^ϕ (τ^ϕ)⁻¹`. -/
theorem phi_conj' (τ : G) {σ : Equiv.Perm Ω} (hσ : σ ∈ G)
    (h : (τ : Equiv.Perm Ω) * σ * (τ : Equiv.Perm Ω)⁻¹ ∈ G) :
    (ϕ ⟨(τ : Equiv.Perm Ω) * σ * (τ : Equiv.Perm Ω)⁻¹, h⟩ : Equiv.Perm Γ)
      = (ϕ τ : Equiv.Perm Γ) * (ϕ ⟨σ, hσ⟩ : Equiv.Perm Γ) * (ϕ τ : Equiv.Perm Γ)⁻¹ := by
  have he : (⟨(τ : Equiv.Perm Ω) * σ * (τ : Equiv.Perm Ω)⁻¹, h⟩ : G)
      = τ * ⟨σ, hσ⟩ * τ⁻¹ := Subtype.ext rfl
  rw [he, map_mul, map_mul, map_inv]

theorem perm_mul_image {α : Type*} (a b : Equiv.Perm α) (S : Set α) :
    ((a * b : Equiv.Perm α) : α → α) '' S = (a : α → α) '' ((b : α → α) '' S) := by
  rw [← Set.image_comp]; rfl

/-- `(τ⁻¹στ)(S) = S` iff `σ(τ(S)) = τ(S)`. -/
theorem conj_image_eq_iff {α : Type*} (a s : Equiv.Perm α) (S : Set α) :
    ((a⁻¹ * s * a : Equiv.Perm α) : α → α) '' S = S
      ↔ (s : α → α) '' ((a : α → α) '' S) = (a : α → α) '' S := by
  rw [perm_mul_image, perm_mul_image]
  constructor
  · intro h
    have := congrArg (fun U => (a : α → α) '' U) h
    simpa [← Set.image_comp] using this
  · intro h
    rw [h, ← Set.image_comp]
    simp

/-- `G_{T^{τ̄}} = τ G_T τ⁻¹`: the setwise stabilizer of the test set is equivariant. -/
theorem bigGT_testImage (τ : G) :
    bigGT ϕ (testImage ϕ T τ)
      = (bigGT ϕ T).map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom := by
  ext σ
  rw [mem_map_conj, mem_stabIn, mem_stabIn]
  constructor
  · rintro ⟨hmem, himg⟩
    have hmem' : (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem τ.2) hmem) τ.2
    refine ⟨hmem', ?_⟩
    rw [phi_conj τ hmem hmem', conj_image_eq_iff]
    exact himg
  · rintro ⟨hmem, himg⟩
    have hmem' : σ ∈ G := by
      have hrw : σ = (τ : Equiv.Perm Ω) * ((τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω)) *
          (τ : Equiv.Perm Ω)⁻¹ := by group
      rw [hrw]
      exact G.mul_mem (G.mul_mem τ.2 hmem) (G.inv_mem τ.2)
    refine ⟨hmem', ?_⟩
    exact (conj_image_eq_iff (ϕ τ) (ϕ ⟨σ, hmem'⟩) T).1
      (by rw [← phi_conj τ hmem' hmem]; exact himg)

/-- `ψ_{T^{τ̄}}(τστ⁻¹)` is `ψ_T(σ)` transported along the bijection `T → T^{τ̄}`. -/
theorem psiOn_conj {L L' : Subgroup (Equiv.Perm Ω)} (hL : L ≤ bigGT ϕ T) (τ : G)
    (hL' : L' ≤ bigGT ϕ (testImage ϕ T τ)) {σ : Equiv.Perm Ω}
    (hσ' : σ ∈ L') (hσ : (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ L) :
    psiOn ϕ (testImage ϕ T τ) hL' ⟨σ, hσ'⟩
      = Equiv.permCongrHom (testEquiv ϕ T τ)
          (psiOn ϕ T hL ⟨(τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω), hσ⟩) := by
  refine Equiv.ext fun b => Subtype.ext ?_
  have hG : σ ∈ G := stabIn_le_top (hL' hσ')
  have hG' : (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ G := stabIn_le_top (hL hσ)
  have hlhs : ((psiOn ϕ (testImage ϕ T τ) hL' ⟨σ, hσ'⟩ b :
      (testImage ϕ T τ : Set Γ)) : Γ) = (ϕ ⟨σ, hG⟩ : Equiv.Perm Γ) (b : Γ) := rfl
  have hrhs : ((Equiv.permCongrHom (testEquiv ϕ T τ)
      (psiOn ϕ T hL ⟨(τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω), hσ⟩) b :
        (testImage ϕ T τ : Set Γ)) : Γ)
      = (ϕ τ : Equiv.Perm Γ) ((ϕ ⟨(τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω), hG'⟩ :
          Equiv.Perm Γ) ((ϕ τ : Equiv.Perm Γ).symm (b : Γ))) := rfl
  rw [hlhs, hrhs, phi_conj τ hG hG']
  simp [Equiv.Perm.mul_apply]

theorem mem_imgOn {L : Subgroup (Equiv.Perm Ω)} {A : Set Γ} (hL : L ≤ bigGT ϕ A)
    {g : Equiv.Perm (A : Set Γ)} :
    g ∈ imgOn ϕ A hL ↔ ∃ (σ : Equiv.Perm Ω) (h : σ ∈ L), psiOn ϕ A hL ⟨σ, h⟩ = g := by
  constructor
  · rintro ⟨⟨σ, hσ⟩, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

/-- `L'^{T^{τ̄}}` is `L^T` transported along the bijection `T → T^{τ̄}`, whenever `L'` is the
`τ`-conjugate of `L`. -/
theorem imgOn_conj {L L' : Subgroup (Equiv.Perm Ω)} (hL : L ≤ bigGT ϕ T) (τ : G)
    (hL' : L' ≤ bigGT ϕ (testImage ϕ T τ))
    (hLL' : ∀ σ : Equiv.Perm Ω,
      σ ∈ L' ↔ (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ L) :
    imgOn ϕ (testImage ϕ T τ) hL'
      = (imgOn ϕ T hL).map (Equiv.permCongrHom (testEquiv ϕ T τ)).toMonoidHom := by
  ext g
  rw [mem_imgOn]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (mem_imgOn hL).2 ⟨_, (hLL' σ).1 hσ, rfl⟩, (psiOn_conj hL τ hL' hσ _).symm⟩
  · rintro ⟨g₀, hg₀, rfl⟩
    obtain ⟨ρ, hρ, rfl⟩ := (mem_imgOn hL).1 hg₀
    have hσ' : (τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹ ∈ L' := by
      refine (hLL' _).2 ?_
      have hrw : (τ : Equiv.Perm Ω)⁻¹ * ((τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹) *
          (τ : Equiv.Perm Ω) = ρ := by group
      rw [hrw]; exact hρ
    refine ⟨_, hσ', ?_⟩
    have harg : (⟨(τ : Equiv.Perm Ω)⁻¹ * ((τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹) *
        (τ : Equiv.Perm Ω), (hLL' _).1 hσ'⟩ : ↥L) = ⟨ρ, hρ⟩ := Subtype.ext (by group)
    rw [psiOn_conj hL τ hL' hσ' ((hLL' _).1 hσ'), harg]
    rfl

/-- Affectedness is equivariant: `τu` is affected by `(L', ψ_{T^{τ̄}})` exactly when `u` is
affected by `(L, ψ_T)`, for `L'` the `τ`-conjugate of `L`. -/
theorem affectedIn_psiOn_conj {L L' : Subgroup (Equiv.Perm Ω)} (hL : L ≤ bigGT ϕ T) (τ : G)
    (hL' : L' ≤ bigGT ϕ (testImage ϕ T τ))
    (hLL' : ∀ σ : Equiv.Perm Ω,
      σ ∈ L' ↔ (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ L) (u : Ω) :
    AffectedIn (psiOn ϕ (testImage ϕ T τ) hL') ((τ : Equiv.Perm Ω) u)
      ↔ AffectedIn (psiOn ϕ T hL) u := by
  have hmap : (stabilizer L' ((τ : Equiv.Perm Ω) u)).map (psiOn ϕ (testImage ϕ T τ) hL')
      = ((stabilizer L u).map (psiOn ϕ T hL)).map
          (Equiv.permCongrHom (testEquiv ϕ T τ)).toMonoidHom := by
    ext g
    constructor
    · rintro ⟨⟨σ, hσ'⟩, hstab, rfl⟩
      have hσ : (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ L := (hLL' σ).1 hσ'
      have hfix : σ ((τ : Equiv.Perm Ω) u) = (τ : Equiv.Perm Ω) u := by
        have := hstab
        rw [SetLike.mem_coe, mem_stabilizer_iff] at this
        simpa [Subgroup.smul_def] using this
      refine ⟨psiOn ϕ T hL ⟨_, hσ⟩, ⟨⟨_, hσ⟩, ?_, rfl⟩, (psiOn_conj hL τ hL' hσ' hσ).symm⟩
      have hval : ((τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω)) u = u := by
        simp only [Equiv.Perm.mul_apply, hfix]
        simp
      rw [SetLike.mem_coe, mem_stabilizer_iff]
      simpa [Subgroup.smul_def] using hval
    · rintro ⟨g₀, hg₀, rfl⟩
      obtain ⟨⟨ρ, hρ⟩, hstab, rfl⟩ := hg₀
      have hfix : ρ u = u := by
        have := hstab
        rw [SetLike.mem_coe, mem_stabilizer_iff] at this
        simpa [Subgroup.smul_def] using this
      have hσ' : (τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹ ∈ L' := by
        refine (hLL' _).2 ?_
        have hrw : (τ : Equiv.Perm Ω)⁻¹ * ((τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹) *
            (τ : Equiv.Perm Ω) = ρ := by group
        rw [hrw]; exact hρ
      refine ⟨⟨_, hσ'⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_stabilizer_iff]
        have hval : ((τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹) ((τ : Equiv.Perm Ω) u)
            = (τ : Equiv.Perm Ω) u := by
          simp only [Equiv.Perm.mul_apply]
          simp [hfix]
        simpa [Subgroup.smul_def] using hval
      · have harg : (⟨(τ : Equiv.Perm Ω)⁻¹ * ((τ : Equiv.Perm Ω) * ρ * (τ : Equiv.Perm Ω)⁻¹) *
            (τ : Equiv.Perm Ω), (hLL' _).1 hσ'⟩ : ↥L) = ⟨ρ, hρ⟩ := Subtype.ext (by group)
        rw [psiOn_conj hL τ hL' hσ' ((hLL' _).1 hσ'), harg]
        rfl
  rw [AffectedIn, AffectedIn, hmap, alternating_le_map_congr_iff]

/-! ### Conjugating a window and a stage -/

theorem mem_wAut_conj {W : Set Ω} {K K' : Set (Equiv.Perm Ω)} {x : Ω → Λ}
    {τ σ : Equiv.Perm Ω} (hK : ∀ ρ : Equiv.Perm Ω, ρ ∈ K' ↔ τ⁻¹ * ρ * τ ∈ K) :
    σ ∈ wAut ((τ : Equiv.Perm Ω) '' W) K' (strAct x τ) ↔ τ⁻¹ * σ * τ ∈ wAut W K x := by
  constructor
  · rintro ⟨hmem, hresp⟩
    refine ⟨(hK σ).1 hmem, fun u hu => ?_⟩
    have h := hresp (τ u) ⟨u, hu, rfl⟩
    simpa [strAct, Equiv.Perm.mul_apply] using h
  · rintro ⟨hmem, hresp⟩
    refine ⟨(hK σ).2 hmem, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have h := hresp u hu
    simpa [strAct, Equiv.Perm.mul_apply] using h

theorem isInvariant_conj {W : Set Ω} {K K' : Subgroup (Equiv.Perm Ω)} {τ : Equiv.Perm Ω}
    (hK : ∀ ρ : Equiv.Perm Ω, ρ ∈ K' ↔ τ⁻¹ * ρ * τ ∈ K) (h : IsInvariant K W) :
    IsInvariant K' ((τ : Equiv.Perm Ω) '' W) := by
  intro σ hσ
  exact (conj_image_eq_iff τ σ W).1 (h _ ((hK σ).1 hσ))

theorem pointwiseStabilizer_conj (K : Subgroup (Equiv.Perm Ω)) (S : Set Ω)
    (τ : Equiv.Perm Ω) :
    pointwiseStabilizer (K.map (MulAut.conj τ).toMonoidHom) (τ '' S)
      = (pointwiseStabilizer K S).map (MulAut.conj τ).toMonoidHom := by
  ext σ
  rw [mem_map_conj, mem_pointwiseStabilizer, mem_pointwiseStabilizer, mem_map_conj]
  refine and_congr Iff.rfl ?_
  constructor
  · rintro h z hz
    have h' := h (τ z) ⟨z, hz, rfl⟩
    simp only [Equiv.Perm.mul_apply, h']
    simp
  · rintro h _ ⟨z, hz, rfl⟩
    have h' := h z hz
    simp only [Equiv.Perm.mul_apply] at h'
    have := congrArg (fun w => τ w) h'
    simpa using this

namespace Stage

theorem ext' {ϕ : G →* Equiv.Perm Γ} {x : Ω → Λ} {T : Set Γ} {s t : Stage ϕ x T}
    (hW : s.W = t.W) (hH : s.H = t.H) : s = t := by
  obtain ⟨W₁, H₁, _, _, _, _⟩ := s
  obtain ⟨W₂, H₂, _, _, _, _⟩ := t
  simp only at hW hH
  subst hW; subst hH; rfl

variable {ϕ : G →* Equiv.Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- The `τ`-conjugate of a stage of the run on `(x, T)`: a stage of the run on
`(x^τ, T^{τ̄})`. -/
noncomputable def conj (s : Stage ϕ x T) (τ : G) :
    Stage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) where
  W := (τ : Equiv.Perm Ω) '' s.W
  H := s.H.map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom
  le := by
    rw [bigGT_testImage (ϕ := ϕ) (T := T) τ]
    exact Subgroup.map_mono s.le
  isAut := by
    ext σ
    have hK : ∀ ρ : Equiv.Perm Ω,
        ρ ∈ (bigGT ϕ (testImage ϕ T τ) : Set (Equiv.Perm Ω))
          ↔ (τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω) ∈ (bigGT ϕ T : Set (Equiv.Perm Ω)) := by
      intro ρ
      rw [SetLike.mem_coe, SetLike.mem_coe, bigGT_testImage (ϕ := ϕ) (T := T) τ, mem_map_conj]
    rw [mem_wAut_conj hK]
    show σ ∈ s.H.map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom ↔ _
    rw [mem_map_conj, ← SetLike.mem_coe, s.isAut]
  inv := isInvariant_conj (fun ρ => mem_map_conj) s.inv
  sub := by
    rintro _ ⟨u, hu, rfl⟩
    exact (affectedIn_psiOn_conj s.le τ _ (fun ρ => mem_map_conj) u).2 (s.sub hu)

@[simp] theorem conj_W (s : Stage ϕ x T) (τ : G) :
    (s.conj τ).W = (τ : Equiv.Perm Ω) '' s.W := rfl

@[simp] theorem conj_H (s : Stage ϕ x T) (τ : G) :
    (s.conj τ).H = s.H.map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom := rfl

theorem conj_aff (s : Stage ϕ x T) (τ : G) :
    (s.conj τ).aff = (τ : Equiv.Perm Ω) '' s.aff := by
  have key : ∀ v : Ω,
      AffectedIn (psiOn ϕ (testImage ϕ T τ) (s.conj τ).le) ((τ : Equiv.Perm Ω) v)
        ↔ AffectedIn (psiOn ϕ T s.le) v :=
    fun v => affectedIn_psiOn_conj s.le τ (s.conj τ).le (fun ρ => mem_map_conj) v
  ext u
  simp only [Stage.aff, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro hu
    exact ⟨(τ : Equiv.Perm Ω)⁻¹ u, (key _).1 (by simpa using hu), by simp⟩
  · rintro ⟨v, hv, rfl⟩
    exact (key v).2 hv

theorem conj_step (s : Stage ϕ x T) (τ : G) : (s.step).conj τ = (s.conj τ).step := by
  refine ext' ?_ ?_
  · show (τ : Equiv.Perm Ω) '' s.aff = (s.conj τ).aff
    rw [conj_aff]
  · refine SetLike.ext fun σ => ?_
    show σ ∈ (wAutSubgroup s.H s.aff s.isInvariant_aff x).map
        (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom ↔
      σ ∈ wAutSubgroup (s.conj τ).H (s.conj τ).aff (s.conj τ).isInvariant_aff
        (strAct x (τ : Equiv.Perm Ω))
    rw [mem_map_conj]
    have hmem : σ ∈ wAutSubgroup (s.conj τ).H (s.conj τ).aff (s.conj τ).isInvariant_aff
        (strAct x (τ : Equiv.Perm Ω))
        ↔ σ ∈ wAut ((τ : Equiv.Perm Ω) '' s.aff)
            ((s.H.map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom : Subgroup (Equiv.Perm Ω)) :
              Set (Equiv.Perm Ω)) (strAct x (τ : Equiv.Perm Ω)) := by
      rw [← conj_aff s τ]
      exact Iff.rfl
    rw [hmem, mem_wAut_conj (fun ρ => mem_map_conj)]
    exact Iff.rfl

theorem conj_loopCond (s : Stage ϕ x T) (τ : G) : (s.conj τ).LoopCond ↔ s.LoopCond := by
  have h1 : alternatingGroup (testImage ϕ T τ : Set Γ) ≤ imgOn ϕ (testImage ϕ T τ) (s.conj τ).le
      ↔ alternatingGroup (T : Set Γ) ≤ imgOn ϕ T s.le := by
    rw [imgOn_conj s.le τ (s.conj τ).le (fun ρ => mem_map_conj),
      alternating_le_map_congr_iff]
  have h2 : ((s.conj τ).aff ⊆ (s.conj τ).W) ↔ (s.aff ⊆ s.W) := by
    rw [conj_aff, conj_W]
    constructor
    · intro h u hu
      obtain ⟨v, hv, hvu⟩ := h ⟨u, hu, rfl⟩
      rwa [(τ : Equiv.Perm Ω).injective hvu] at hv
    · intro h
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨u, h hu, rfl⟩
  rw [LoopCond, LoopCond]
  exact and_congr h1 (not_congr h2)

theorem init_conj (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) (τ : G) :
    Stage.init ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)
      = (Stage.init ϕ x T).conj τ := by
  refine ext' ?_ ?_
  · show (∅ : Set Ω) = (τ : Equiv.Perm Ω) '' (∅ : Set Ω)
    simp
  · show bigGT ϕ (testImage ϕ T τ) = (bigGT ϕ T).map _
    exact bigGT_testImage (ϕ := ϕ) (T := T) τ

end Stage

theorem stages_conj (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) (τ : G) (i : ℕ) :
    stages ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) i = (stages ϕ x T i).conj τ := by
  induction i with
  | zero => exact Stage.init_conj ϕ x T τ
  | succ i ih => rw [stages_succ, ih, stages_succ, Stage.conj_step]

theorem haltIndex_conj (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) (τ : G) :
    haltIndex ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) = haltIndex ϕ x T := by
  have key : ∀ i : ℕ,
      ¬ (stages ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) i).LoopCond
        ↔ ¬ (stages ϕ x T i).LoopCond := by
    intro i
    rw [stages_conj ϕ x T τ i, Stage.conj_loopCond]
  refine le_antisymm ?_ ?_
  · exact Nat.find_le ((key _).2 (not_loopCond_outStage ϕ x T))
  · exact Nat.find_le ((key _).1
      (not_loopCond_outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)))

theorem outStage_conj (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (T : Set Γ) (τ : G) :
    outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) = (outStage ϕ x T).conj τ := by
  rw [outStage, haltIndex_conj ϕ x T τ, stages_conj ϕ x T τ]
  rfl

/-- The setwise stabilizer of the test set is equivariant, for any pair of `τ`-conjugate
subgroups `L`, `L'` of `G`. -/
theorem stabIn_conj_iff {L L' : Subgroup (Equiv.Perm Ω)} (hL : L ≤ G) (hL' : L' ≤ G) (τ : G)
    (hmem : ∀ ρ : Equiv.Perm Ω,
      ρ ∈ L' ↔ (τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω) ∈ L) (σ : Equiv.Perm Ω) :
    σ ∈ stabIn ϕ hL' (testImage ϕ T τ)
      ↔ (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ stabIn ϕ hL T := by
  rw [mem_stabIn, mem_stabIn]
  constructor
  · rintro ⟨h, himg⟩
    refine ⟨(hmem σ).1 h, ?_⟩
    rw [phi_conj τ (hL' h) (hL ((hmem σ).1 h)), conj_image_eq_iff]
    exact himg
  · rintro ⟨h, himg⟩
    have h' : σ ∈ L' := (hmem σ).2 h
    refine ⟨h', ?_⟩
    exact (conj_image_eq_iff (ϕ τ) (ϕ ⟨σ, hL' h'⟩) T).1
      (by rw [← phi_conj τ (hL' h') (hL h)]; exact himg)

/-- `Aut_G(x^τ) = τ Aut_G(x) τ⁻¹`. -/
theorem mem_autG_strAct (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ) (τ : G) {σ : Equiv.Perm Ω} :
    σ ∈ autG G (strAct x (τ : Equiv.Perm Ω))
      ↔ (τ : Equiv.Perm Ω)⁻¹ * σ * (τ : Equiv.Perm Ω) ∈ autG G x := by
  have hK : ∀ ρ : Equiv.Perm Ω, ρ ∈ (G : Set (Equiv.Perm Ω))
      ↔ (τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω) ∈ (G : Set (Equiv.Perm Ω)) := by
    intro ρ
    constructor
    · intro h; exact G.mul_mem (G.mul_mem (G.inv_mem τ.2) h) τ.2
    · intro h
      have hrw : ρ = (τ : Equiv.Perm Ω) * ((τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω)) *
          (τ : Equiv.Perm Ω)⁻¹ := by group
      rw [hrw]
      exact G.mul_mem (G.mul_mem τ.2 h) (G.inv_mem τ.2)
  have hkey := mem_wAut_conj (W := (Set.univ : Set Ω)) (K := (G : Set (Equiv.Perm Ω)))
    (K' := (G : Set (Equiv.Perm Ω))) (x := x) (τ := (τ : Equiv.Perm Ω)) (σ := σ) hK
  have huniv : (τ : Equiv.Perm Ω) '' (Set.univ : Set Ω) = Set.univ := by
    rw [Set.image_univ]
    exact (τ : Equiv.Perm Ω).surjective.range_eq
  rw [huniv] at hkey
  exact hkey

end Conj

/-! ### The outputs -/

theorem outStage_H_conj_eq (τ : G) :
    (outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)).H
      = (outStage ϕ x T).H.map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom := by
  rw [outStage_conj ϕ x T τ]
  rfl

theorem outStage_H_conj (τ : G) (ρ : Equiv.Perm Ω) :
    ρ ∈ (outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)).H
      ↔ (τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω) ∈ (outStage ϕ x T).H := by
  rw [outStage_H_conj_eq ϕ x T τ]
  exact mem_map_conj

/-- **Proposition 13.1.8 (v)**, §13.1: "the assignment `T ↦ W(T)` is canonical."

Canonicity in the sense of §6, spelled out as equivariance (see the module docstring). -/
theorem canonical_windowOut (τ : G) :
    windowOut ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)
      = (τ : Equiv.Perm Ω) '' windowOut ϕ x T := by
  show (outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)).W = _
  rw [outStage_conj ϕ x T τ]
  rfl

/-- **Theorem 13.1.3**, last sentence, §13.1: the family `{(T, K(T)) : T ∈ F(x)}` is
canonical.

The membership of the index set is equivariant (`Babai.canonical_isFull`) and the
certificate transforms by conjugation. -/
theorem canonical_certK (τ : G) :
    certK ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)
      = (certK ϕ x T).map (MulAut.conj (τ : Equiv.Perm Ω)).toMonoidHom := by
  have hcompl : ((τ : Equiv.Perm Ω) '' windowOut ϕ x T)ᶜ
      = (τ : Equiv.Perm Ω) '' (windowOut ϕ x T)ᶜ :=
    (Equiv.image_compl (τ : Equiv.Perm Ω) (windowOut ϕ x T)).symm
  show pointwiseStabilizer (outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)).H
      (windowOut ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ))ᶜ = _
  rw [outStage_H_conj_eq ϕ x T τ, canonical_windowOut ϕ x T τ, hcompl,
    pointwiseStabilizer_conj]
  rfl

/-- **Definition 13.1.2**: fullness is invariant under the isomorphisms of the input, so
the index sets `F(x)` and `F̄(x)` of the two families of Theorem 13.1.3 are canonical. -/
theorem canonical_isFull (τ : G) :
    IsFull ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ) ↔ IsFull ϕ x T := by
  have hLL' : ∀ ρ : Equiv.Perm Ω,
      ρ ∈ stabIn ϕ (autG_le G (strAct x (τ : Equiv.Perm Ω))) (testImage ϕ T τ)
        ↔ (τ : Equiv.Perm Ω)⁻¹ * ρ * (τ : Equiv.Perm Ω) ∈ stabIn ϕ (autG_le G x) T :=
    stabIn_conj_iff (autG_le G x) (autG_le G (strAct x (τ : Equiv.Perm Ω))) τ
      (fun ρ => mem_autG_strAct ϕ x τ)
  show alternatingGroup (testImage ϕ T τ : Set Γ)
      ≤ imgOn ϕ (testImage ϕ T τ)
        (autStab_le ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)) ↔ _
  rw [imgOn_conj (autStab_le ϕ x T) τ
      (autStab_le ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)) hLL',
    alternating_le_map_congr_iff]
  exact Iff.rfl

/-- **Theorem 13.1.3**, last sentence, §13.1: the family `{(T, M(T)) : T ∈ F̄(x)}` is
canonical.

`M(T) ≤ S(T)` and `M(T^{τ^ϕ}) ≤ S(T^{τ^ϕ})` are groups on different sets, so the
statement transports `M(T)` along the bijection `T → T^{τ^ϕ}` induced by `τ^ϕ`. -/
theorem canonical_certM (τ : G) (e : (T : Set Γ) ≃ (testImage ϕ T τ : Set Γ))
    (he : ∀ a : (T : Set Γ), ((e a : Γ)) = (ϕ τ : Equiv.Perm Γ) (a : Γ)) :
    certM ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)
      = (certM ϕ x T).map (Equiv.permCongrHom e).toMonoidHom := by
  have hee : e = testEquiv ϕ T τ := Equiv.ext fun a => Subtype.ext (he a)
  rw [hee]
  exact imgOn_conj (outStage ϕ x T).le τ
    (outStage ϕ (strAct x (τ : Equiv.Perm Ω)) (testImage ϕ T τ)).le (outStage_H_conj ϕ x T τ)

end Babai
