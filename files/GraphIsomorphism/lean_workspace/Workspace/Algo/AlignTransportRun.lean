/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Eq. (71) of Sec. 14.1 for lists of versions that move with the
isomorphisms of the input.
-/
import Workspace.Master.CosetAlignExpand

/-!
# Eq. (71) from the transport of the fixed version

`Babai.run_cosetDesignAlign` and `Babai.run_cosetAlignExpand` read the versions of `X(y)` off a
canonical assignment `Vers` of sets of versions to *all* strings (`Babai.IsCanonicalVersions`).
Eq. (71) only uses one consequence of canonicity: every `σ ∈ Iso_G(x, y)` carries the fixed
version `X'` of `X(x)` to a listed version of `X(y)`.  Then

  `Iso_G(x, y) = ⋃_{Y' listed} Iso_G^{X' ↦ Y'}(x, y)`,

since every piece lies in `Iso_G(x, y)` and every `σ ∈ Iso_G(x, y)` lies in the piece of
`Y' = X'^{σ^ϕ}`.

This is the form in which the machine of Sec. 15, lines 5–7 provides its versions: it lists
the versions of `X(x)` and of `X(y)` it computes, and proves that `ϕ(σ)` carries each version of
`x` to a listed version of `y` (`Algo.aggnContinuation_transport_of_bip`).  These are the same
statements as `Babai.run_cosetDesignAlign` and `Babai.run_cosetAlignExpand`, with the
hypothesis of transport in place of canonicity.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise Classical

variable {Ω : Type u} {A : Type v} {Γ 𝒳 : Type*} [MulAction (Perm Γ) 𝒳] {G : Subgroup (Perm Ω)}

/-- Eq. (71): **the union of the pieces over the listed versions is `Iso_G(x, y)`** when every
`σ ∈ Iso_G(x, y)` carries `X'` to a listed version. -/
theorem strIso_eq_iUnion_versionPiece_of_transport (ϕ : G →* Perm Γ) (x y : Ω → A) (X : 𝒳)
    (versions : List 𝒳)
    (hT : ∀ σ : G, strAct x (σ : Perm Ω) = y → (ϕ σ) • X ∈ versions) :
    strIso (G : Set (Perm Ω)) x y = ⋃ Y ∈ versions, versionPiece ϕ x y X Y := by
  refine Set.Subset.antisymm ?_ (Set.iUnion₂_subset fun Y _ => versionPiece_subset ϕ x y X Y)
  intro τ hτ
  obtain ⟨hτG, hτxy⟩ := hτ
  exact Set.mem_iUnion₂.2 ⟨(ϕ ⟨τ, hτG⟩) • X, hT ⟨τ, hτG⟩ hτxy, ⟨⟨hτG, hτxy⟩, hτG, rfl⟩⟩

/-- Eq. (71), **the value of the round over the listed versions**, from the transport of the
fixed version (`Babai.run_cosetDesignAlign` with transport in place of canonicity). -/
theorem run_cosetDesignAlign_of_transport (ϕ : G →* Perm Γ) (x y : Ω → A) (X : 𝒳)
    (versions : List 𝒳)
    (hT : ∀ σ : G, strAct x (σ : Perm Ω) = y → (ϕ σ) • X ∈ versions)
    (windows : List (Set Ω)) (hcover : (⋃ Δ ∈ windows, Δ) = Set.univ) :
    (cosetDesignAlign ϕ x y X versions windows).run = strIso (G : Set (Perm Ω)) x y := by
  rw [cosetDesignAlign, SIReduction.run_unionOver,
    strIso_eq_iUnion_versionPiece_of_transport ϕ x y X versions hT]
  simp only [run_cosetAlignChain ϕ x y _ _ windows hcover]

variable [Fintype Ω] [DecidableEq Ω]

/-- Sec. 14.1, lines 1–11, **the value of the round with the first window expanded**, from the
transport of the fixed version (`Babai.run_cosetAlignExpand` with transport in place of
canonicity). -/
theorem run_cosetAlignExpand_of_transport {ϕ : G →* Perm Γ} {x y : Ω → A} {X : 𝒳}
    {versions : List 𝒳} {head : Set Ω} {tail : List (Set Ω)}
    {g : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))}
    (hT : ∀ σ : G, strAct x (σ : Perm Ω) = y → (ϕ σ) • X ∈ versions) (hne : head ∉ tail)
    (hinv : ∀ Δ ∈ head :: tail, IsInvariant (preimageSubgroup ϕ (structAut X)) Δ)
    (hcover : (⋃ Δ ∈ head :: tail, Δ) = Set.univ)
    (hg : ∀ J, CosetAlignCall G (preimageSubgroup ϕ (structAut X)) head tail J →
      J.Δ = head → (g J).run = J.answer) :
    (cosetAlignExpand ϕ x y X versions head tail g).run = strIso (G : Set (Perm Ω)) x y := by
  rw [cosetAlignExpand]
  rw [SIReduction.run_expand_of_calls (P := CosetAlignCall G
    (preimageSubgroup ϕ (structAut X)) head tail)
    (fun J hJ => by
      try dsimp only
      split
      · next h => exact hg J hJ h
      · rfl)
    _ (calls_cosetDesignAlign_spec ϕ x y X versions head tail hne hinv)]
  exact run_cosetDesignAlign_of_transport ϕ x y X versions hT _ hcover

end Babai
