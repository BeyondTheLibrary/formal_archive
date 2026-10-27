/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, line 7: numbering the reduced set `Γ*`.
-/
import Workspace.Master.AlignDominant

/-!
# Line 7: the reduced set `Γ*` is numbered by `Fin m*`

> 7. (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>    relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then identify
>    `Δ_j` with `(Γ* choose t*)`, `|Γ*| = m*`, and let `Y` denote this Johnson scheme

In the paper `Γ*` is a set — the set of blocks, or the vertex set of the Johnson scheme.
In the formalization it has to be `Fin m*`, because the recursion of Sec. 15 runs on
instances whose giant representation goes into `S(Fin m)`.  So the blocks have to be
*numbered*, and a numbering is a choice.

`Babai.AlignDominantABlocks` and `Babai.AlignDominantBBlocks` are line 7's data with `Γ*`
still an arbitrary finite type `B`, and `Babai.AlignDominantABlocks.toAlignDominantA` and
`Babai.AlignDominantBBlocks.toAlignDominantB` number it by `Fintype.equivFin`.

**The choice is harmless.**  The numbering is made once per call of Procedure Align.  Both
strings of the instance are read through the same pair `(G*, ϕ*)`, and renumbering `Γ*` by a
bijection `e` replaces `ψ` by `e ψ e⁻¹` and `ϕ*` by `e ϕ* e⁻¹`, hence changes neither `G*`
(the preimage of `H`, which lives on `Γ`, not on `Γ*`), nor the window `Ω(Δ_j)`, nor the
answer `Iso_{G*}(x, y')`.  It is the same kind of choice as `Babai.johnsonData` and
`Babai.primitiveCaseId`.
-/

namespace Babai

open Equiv

universe u

section Numbering

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-! ### Line 7 (A): a nontrivial equipartition of `Δ_j`, with unnumbered blocks -/

/-- §14.1, **line 7 (A)**: the data of `Babai.AlignDominantA` with the set of blocks left as
an arbitrary finite type `B` instead of `Fin m*`. -/
structure AlignDominantABlocks (Ω : Type u) [Fintype Ω] [DecidableEq Ω] where
  /-- Sec. 14, Situation: the group of the instance. -/
  G : Subgroup (Equiv.Perm Ω)
  /-- Sec. 14, Situation: *"a transitive group `G ≤ S(Ω)`"*. -/
  transitive : IsTransitive G
  /-- `|Γ| = m`. -/
  m : ℕ
  /-- Sec. 14, Situation: the giant representation `ϕ : G → S(Γ)`. -/
  ϕ : G →* Equiv.Perm (Fin m)
  /-- `ϕ` is a giant representation. -/
  giant : IsGiantRep ϕ
  /-- The numeric hypothesis of Theorem 10.5.1 for `(G, ϕ)`. -/
  veryLarge : VeryLargeK m (maxOrbitLength G)
  /-- Theorem 10.5.1 (c): the common size of the labels. -/
  t : ℕ
  /-- `t` is the label size of every point. -/
  t_const : ∀ u : Ω, tPoint ϕ u = t
  /-- Line 6: the dominant color class `Δ_j ⊆ Γ`. -/
  Δj : Set (Fin m)
  /-- Line 6: *"`|Δ_j| > m/2`"*. -/
  dominant : m < 2 * Δj.ncard
  /-- Line 8: `H = Aut(Y)`. -/
  H : Subgroup (Equiv.Perm (Fin m))
  /-- An automorphism of `Y` permutes the vertex set `Δ_j` of `Y`. -/
  stab : ∀ h ∈ H, h '' Δj = Δj
  /-- Line 7 (A): `Γ*`, the set of blocks, not yet numbered. -/
  B : Type
  /-- `Γ*` is finite. -/
  fintypeB : Fintype B
  /-- Line 8: the natural epimorphism `ψ : H → S(Γ*)`, on the unnumbered `Γ*`. -/
  ψB : H →* Equiv.Perm B
  /-- Line 8: `ψ` is onto. -/
  ψB_surj : Function.Surjective ψB
  /-- Eq. (73): `m* ≤ m/2`. -/
  param_halved : 2 * @Fintype.card B fintypeB ≤ m
  /-- *Nontrivial*: there are at least two blocks. -/
  ms_two : 2 ≤ @Fintype.card B fintypeB
  /-- The common size of a block. -/
  blockSize : ℕ
  /-- *Nontrivial*: each block has at least two points. -/
  blockSize_two : 2 ≤ blockSize
  /-- The block map of the equipartition, on the unnumbered `Γ*`. -/
  blockB : Fin m → B
  /-- *Equi*-partition: every block meets `Δ_j` in the same number of points. -/
  block_card : ∀ b : B, (Δj ∩ blockB ⁻¹' {b}).ncard = blockSize
  /-- Line 8: `ψ` is the induced action on the blocks. -/
  psi_block : ∀ (h : H) (d : Fin m), d ∈ Δj →
    blockB ((h : Equiv.Perm (Fin m)) d) = ψB h (blockB d)

namespace AlignDominantABlocks

variable (D : AlignDominantABlocks Ω)

attribute [instance] AlignDominantABlocks.fintypeB

/-- The chosen numbering of the blocks. -/
noncomputable def enum : D.B ≃ Fin (Fintype.card D.B) := Fintype.equivFin D.B

/-- §14.1, **line 7 (A)**: the data with the blocks numbered by `Fin m*`.

The only content is that a bijection `e : Γ* ≃ Fin m*` carries the action on the blocks to
an action on `Fin m*` by conjugation (`Equiv.permCongrHom`); see the module docstring for
why the choice of `e` does not matter. -/
noncomputable def toAlignDominantA : AlignDominantA Ω where
  G := D.G
  transitive := D.transitive
  m := D.m
  ϕ := D.ϕ
  giant := D.giant
  veryLarge := D.veryLarge
  t := D.t
  t_const := D.t_const
  Δj := D.Δj
  dominant := D.dominant
  ms := Fintype.card D.B
  H := D.H
  stab := D.stab
  ψ := (Equiv.permCongrHom D.enum).toMonoidHom.comp D.ψB
  ψ_surj := by
    intro π
    obtain ⟨h, hh⟩ := D.ψB_surj ((Equiv.permCongrHom D.enum).symm π)
    refine ⟨h, ?_⟩
    show (Equiv.permCongrHom D.enum) (D.ψB h) = π
    rw [hh]
    exact (Equiv.permCongrHom D.enum).apply_symm_apply π
  param_halved := D.param_halved
  ms_two := D.ms_two
  blockSize := D.blockSize
  blockSize_two := D.blockSize_two
  block := fun γ => D.enum (D.blockB γ)
  block_card := by
    intro γ
    have hpre : (fun γ => D.enum (D.blockB γ)) ⁻¹' {γ} = D.blockB ⁻¹' {D.enum.symm γ} := by
      ext δ
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
        fun h => by rw [h, Equiv.apply_symm_apply]⟩
    rw [hpre]
    exact D.block_card _
  psi_block := by
    intro h d hd
    show D.enum (D.blockB ((h : Equiv.Perm (Fin D.m)) d))
      = (Equiv.permCongrHom D.enum) (D.ψB h) (D.enum (D.blockB d))
    rw [D.psi_block h d hd]
    show _ = D.enum (D.ψB h (D.enum.symm (D.enum (D.blockB d))))
    rw [Equiv.symm_apply_apply]

@[simp] theorem toAlignDominantA_ms : D.toAlignDominantA.ms = Fintype.card D.B := rfl

@[simp] theorem toAlignDominantA_G : D.toAlignDominantA.G = D.G := rfl

@[simp] theorem toAlignDominantA_H : D.toAlignDominantA.H = D.H := rfl

@[simp] theorem toAlignDominantA_phi : D.toAlignDominantA.ϕ = D.ϕ := rfl

@[simp] theorem toAlignDominantA_Δj : D.toAlignDominantA.Δj = D.Δj := rfl

end AlignDominantABlocks

/-! ### Line 7 (B): a Johnson scheme on `Δ_j`, with an unnumbered vertex set -/

/-- §14.1, **line 7 (B)**: the data of `Babai.AlignDominantB` with the vertex set `Γ*` of
the Johnson scheme left as an arbitrary finite type `B` instead of `Fin m*`. -/
structure AlignDominantBBlocks (Ω : Type u) [Fintype Ω] [DecidableEq Ω] where
  /-- Sec. 14, Situation: the group of the instance. -/
  G : Subgroup (Equiv.Perm Ω)
  /-- Sec. 14, Situation: *"a transitive group `G ≤ S(Ω)`"*. -/
  transitive : IsTransitive G
  /-- `|Γ| = m`. -/
  m : ℕ
  /-- Sec. 14, Situation: the giant representation `ϕ : G → S(Γ)`. -/
  ϕ : G →* Equiv.Perm (Fin m)
  /-- `ϕ` is a giant representation. -/
  giant : IsGiantRep ϕ
  /-- The numeric hypothesis of Theorem 10.5.1 for `(G, ϕ)`. -/
  veryLarge : VeryLargeK m (maxOrbitLength G)
  /-- Theorem 10.5.1 (c): the common size of the labels. -/
  t : ℕ
  /-- `t` is the label size of every point. -/
  t_const : ∀ u : Ω, tPoint ϕ u = t
  /-- Line 6: the dominant color class `Δ_j ⊆ Γ`. -/
  Δj : Set (Fin m)
  /-- Line 6: *"`|Δ_j| > m/2`"*. -/
  dominant : m < 2 * Δj.ncard
  /-- Line 8: `H = Aut(Y)`. -/
  H : Subgroup (Equiv.Perm (Fin m))
  /-- An automorphism of `Y` permutes the vertex set `Δ_j` of `Y`. -/
  stab : ∀ h ∈ H, h '' Δj = Δj
  /-- Line 7 (B): `Γ*`, the vertex set of the Johnson scheme, not yet numbered. -/
  B : Type
  /-- `Γ*` is finite. -/
  fintypeB : Fintype B
  /-- Line 8: the natural epimorphism `ψ : H → S(Γ*)`, on the unnumbered `Γ*`. -/
  ψB : H →* Equiv.Perm B
  /-- Line 8: `ψ` is onto. -/
  ψB_surj : Function.Surjective ψB
  /-- Eq. (73): `m* ≤ m/2`. -/
  param_halved : 2 * @Fintype.card B fintypeB ≤ m
  /-- Line 7 (B): `t* ≥ 2`. -/
  ts : ℕ
  /-- Line 7 (B): *"`t* ≥ 2`"*. -/
  ts_two : 2 ≤ ts
  /-- Def. 3.2.9: `m* ≥ 2t* + 1`. -/
  ms_ge : 2 * ts + 1 ≤ @Fintype.card B fintypeB
  /-- The identification of `Δ_j` with `(Γ* choose t*)`, on the unnumbered `Γ*`. -/
  labelB : Fin m → Set B
  /-- On `Δ_j` the label is a `t*`-subset. -/
  label_ncard : ∀ d ∈ Δj, (labelB d).ncard = ts
  /-- The identification is injective on `Δ_j`. -/
  label_inj : ∀ d ∈ Δj, ∀ d' ∈ Δj, labelB d = labelB d' → d = d'
  /-- The identification is onto `(Γ* choose t*)`. -/
  label_surj : ∀ T : Set B, T.ncard = ts → ∃ d ∈ Δj, labelB d = T
  /-- Line 8: `ψ` returns the permutation of `Γ*` that induces the automorphism. -/
  psi_label : ∀ (h : H) (d : Fin m), d ∈ Δj →
    labelB ((h : Equiv.Perm (Fin m)) d) = ψB h '' labelB d

namespace AlignDominantBBlocks

variable (D : AlignDominantBBlocks Ω)

attribute [instance] AlignDominantBBlocks.fintypeB

/-- The chosen numbering of the vertex set of the Johnson scheme. -/
noncomputable def enum : D.B ≃ Fin (Fintype.card D.B) := Fintype.equivFin D.B

/-- §14.1, **line 7 (B)**: the data with the vertex set numbered by `Fin m*`. -/
noncomputable def toAlignDominantB : AlignDominantB Ω where
  G := D.G
  transitive := D.transitive
  m := D.m
  ϕ := D.ϕ
  giant := D.giant
  veryLarge := D.veryLarge
  t := D.t
  t_const := D.t_const
  Δj := D.Δj
  dominant := D.dominant
  ms := Fintype.card D.B
  H := D.H
  stab := D.stab
  ψ := (Equiv.permCongrHom D.enum).toMonoidHom.comp D.ψB
  ψ_surj := by
    intro π
    obtain ⟨h, hh⟩ := D.ψB_surj ((Equiv.permCongrHom D.enum).symm π)
    refine ⟨h, ?_⟩
    show (Equiv.permCongrHom D.enum) (D.ψB h) = π
    rw [hh]
    exact (Equiv.permCongrHom D.enum).apply_symm_apply π
  param_halved := D.param_halved
  ts := D.ts
  ts_two := D.ts_two
  ms_ge := D.ms_ge
  label := fun γ => D.enum '' D.labelB γ
  label_ncard := by
    intro d hd
    rw [Set.ncard_image_of_injective _ D.enum.injective]
    exact D.label_ncard d hd
  label_inj := by
    intro d hd d' hd' h
    exact D.label_inj d hd d' hd' (Set.image_injective.2 D.enum.injective h)
  label_surj := by
    intro T hT
    obtain ⟨d, hd, hdl⟩ := D.label_surj (D.enum.symm '' T)
      (by rw [Set.ncard_image_of_injective _ D.enum.symm.injective]; exact hT)
    refine ⟨d, hd, ?_⟩
    rw [hdl, ← Set.image_comp]
    simp
  psi_label := by
    intro h d hd
    show D.enum '' D.labelB ((h : Equiv.Perm (Fin D.m)) d)
      = (Equiv.permCongrHom D.enum) (D.ψB h) '' (D.enum '' D.labelB d)
    rw [D.psi_label h d hd, ← Set.image_comp, ← Set.image_comp]
    congr 1
    funext b
    show D.enum (D.ψB h b) = D.enum (D.ψB h (D.enum.symm (D.enum b)))
    rw [Equiv.symm_apply_apply]

@[simp] theorem toAlignDominantB_ms : D.toAlignDominantB.ms = Fintype.card D.B := rfl

@[simp] theorem toAlignDominantB_G : D.toAlignDominantB.G = D.G := rfl

@[simp] theorem toAlignDominantB_H : D.toAlignDominantB.H = D.H := rfl

@[simp] theorem toAlignDominantB_phi : D.toAlignDominantB.ϕ = D.ϕ := rfl

@[simp] theorem toAlignDominantB_Δj : D.toAlignDominantB.Δj = D.Δj := rfl

end AlignDominantBBlocks

end Numbering

end Babai
