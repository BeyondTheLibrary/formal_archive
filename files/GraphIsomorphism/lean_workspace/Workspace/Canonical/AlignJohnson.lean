/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, Procedure Align, lines 7–11: the epimorphism `ψ : Aut(Y) → S(Γ*)` and the
size of `Γ*`.
-/
import Workspace.Canonical.Align
import Workspace.Coherent.Classes

/-!
# Procedure Align, lines 7–11: the reduced set `Γ*` and its giant representation

> 7. While processing window `Ω(Δ_j)`
>    (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>        relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then
>        identify `Δ_j` with `Δ_j = (Γ* choose t*)` where `|Γ*| = m*` and let `Y` denote
>        this Johnson scheme on `Δ_j`
> 8. let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural epimorphism
> 9. let `G* = ϕ⁻¹(H)`
> 10. let `ϕ* : G* → S(Γ*)` be the composition of `ϕ` restricted to `G*` and `ψ`
>     (: this is a giant representation :)

`Babai.Align_phiStar_isGiant` (`Workspace/Canonical/Align.lean`) proves line 10 for any
`H` and any **onto** `ψ`.  This file discharges *"the natural epimorphism"* in case (B):
for a Johnson scheme `Y = J(Γ*, t*)` the map `ψ` is the inverse of `π ↦ π^{(t*)}`, and it is
onto because that map is an isomorphism `S(Γ*) ≃ Aut(J(Γ*,t*))` (Prop. 3.2.11 and
`Babai.permEquivAutJohnsonScheme`, `Workspace/Coherent/Classes.lean`).

It also puts together, in both cases of line 7, the arithmetic of Sec. 14.2 that says the
Johnson parameter is at least halved:

> In the case of an equipartition, `Γ*` is the set of blocks of the partition, so
> `|Γ*| ≤ m/2`.  In case of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) with vertex set
> `Δ_j = (Γ* choose t*)` we have `m ≥ |Δ_j| = C(m*, t*) ≥ C(m*, 2) > (m* − 1)²/2`, so
> `m* < 1 + √(2m) < m/2` (for `m ≥ 12`).

This is Eq. (73), the drop of the second component of the measure of
`Workspace/Master/Procedure.lean`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-! ### Line 8 in case (B): the epimorphism of a Johnson scheme -/

/-- §14.1, line 8, case (B): *"let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural
epimorphism"*, for `Y` the Johnson scheme `J(Γ*, t*)`.

An automorphism of a Johnson scheme is `π^{(t*)}` for exactly one permutation `π` of `Γ*`
(`Babai.exists_unique_perm_of_mem_aut_johnsonScheme`), and `ψ` sends it to that `π`. -/
noncomputable def johnsonSchemePsi (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    (johnsonScheme Γ t).Aut →* Equiv.Perm Γ :=
  (permEquivAutJohnsonScheme t h).symm.toMonoidHom

/-- §14.1, line 8: the map of case (B) really is an **epimorphism**.  This is the clause of
line 8 that `Babai.Align_phiStar_isGiant` takes as a hypothesis. -/
theorem surjective_johnsonSchemePsi (t : ℕ) (h : IsJohnsonGraphParams Γ t) :
    Function.Surjective (johnsonSchemePsi t h) :=
  (permEquivAutJohnsonScheme t h).symm.surjective

/-- `ψ` undoes `π ↦ π^{(t)}`. -/
@[simp] theorem johnsonSchemePsi_tAction (t : ℕ) (h : IsJohnsonGraphParams Γ t)
    (π : Equiv.Perm Γ) (hmem : tAction t π ∈ (johnsonScheme Γ t).Aut) :
    johnsonSchemePsi t h ⟨tAction t π, hmem⟩ = π := by
  have : (permEquivAutJohnsonScheme t h) π = ⟨tAction t π, hmem⟩ := by
    apply Subtype.ext
    rw [permEquivAutJohnsonScheme_apply]
  rw [johnsonSchemePsi, MulEquiv.coe_toMonoidHom, ← this, MulEquiv.symm_apply_apply]

/-- §14.1, **line 10 in case (B)**: `ϕ*` is a giant representation when `Y` is the Johnson
scheme `J(Γ*, t*)` on the whole of `Γ`.

This is `Babai.Align_phiStar_isGiant` with the epimorphism of line 8 supplied: the
hypothesis `Function.Surjective ψ` is `Babai.surjective_johnsonSchemePsi`. -/
theorem Align_phiStar_isGiant_johnsonScheme {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)}
    (t : ℕ) (h : IsJohnsonGraphParams Γ t) (ϕ : G →* Equiv.Perm (binom Γ t))
    (hϕ : alternatingGroup (binom Γ t) ≤ ϕ.range) :
    alternatingGroup Γ ≤
      (((johnsonSchemePsi t h).comp (phiStar ϕ (johnsonScheme Γ t).Aut))).range :=
  Align_phiStar_isGiant ϕ hϕ (johnsonScheme Γ t).Aut (johnsonSchemePsi t h)
    (surjective_johnsonSchemePsi t h)

/-! ### Line 8 in case (A): the epimorphism of a nontrivial equipartition

An equipartition of `Δ` is given by the map `f : Δ → Γ*` that sends a point to its block.
Its automorphism group is the group of permutations of `Δ` that permute the blocks, and
`ψ` is the induced action on the blocks.  It is onto because all the blocks have the same
size: any permutation of the blocks can be realized by choosing a bijection between each
block and its image. -/

section Equipartition

variable {Δ Γ' : Type*} {f : Δ → Γ'}

/-- §14.1, line 7 (A): the automorphism group of the equipartition with block map `f` —
the permutations of `Δ` that permute the blocks. -/
def equipartitionAut (f : Δ → Γ') : Subgroup (Equiv.Perm Δ) where
  carrier := {σ | ∃ β : Equiv.Perm Γ', ∀ d, f (σ d) = β (f d)}
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨βa, ha⟩ ⟨βb, hb⟩
    exact ⟨βa * βb, fun d => by rw [Equiv.Perm.mul_apply, ha, hb, Equiv.Perm.mul_apply]⟩
  inv_mem' := by
    rintro a ⟨βa, ha⟩
    refine ⟨βa⁻¹, fun d => ?_⟩
    have h := ha (a⁻¹ d)
    rw [show (a : Equiv.Perm Δ) (a⁻¹ d) = d from by simp] at h
    rw [h]
    simp

theorem mem_equipartitionAut {σ : Equiv.Perm Δ} :
    σ ∈ equipartitionAut f ↔ ∃ β : Equiv.Perm Γ', ∀ d, f (σ d) = β (f d) := Iff.rfl

/-- The permutation of the blocks induced by an automorphism is unique, because every
block is nonempty. -/
theorem equipartition_beta_unique (hf : Function.Surjective f) {σ : Equiv.Perm Δ}
    {β₁ β₂ : Equiv.Perm Γ'} (h1 : ∀ d, f (σ d) = β₁ (f d)) (h2 : ∀ d, f (σ d) = β₂ (f d)) :
    β₁ = β₂ := by
  refine Equiv.ext fun γ => ?_
  obtain ⟨d, rfl⟩ := hf γ
  rw [← h1 d, ← h2 d]

open scoped Classical in
/-- §14.1, line 8, case (A): *"`ψ : H → S(Γ*)` the natural epimorphism"* — the action of an
automorphism of the equipartition on the blocks. -/
noncomputable def equipartitionPsi (hf : Function.Surjective f) :
    equipartitionAut f →* Equiv.Perm Γ' where
  toFun σ := σ.2.choose
  map_one' :=
    equipartition_beta_unique hf (σ := (1 : Equiv.Perm Δ))
      (Subgroup.one_mem (equipartitionAut f)).choose_spec (fun _ => rfl)
  map_mul' a b := by
    refine equipartition_beta_unique hf (σ := (a : Equiv.Perm Δ) * b)
      (a * b).2.choose_spec (fun d => ?_)
    rw [Equiv.Perm.mul_apply, a.2.choose_spec, b.2.choose_spec, Equiv.Perm.mul_apply]

theorem equipartitionPsi_spec (hf : Function.Surjective f) (σ : equipartitionAut f) (d : Δ) :
    f ((σ : Equiv.Perm Δ) d) = equipartitionPsi hf σ (f d) := σ.2.choose_spec d

/-- §14.1, line 8: the map of case (A) really is an **epimorphism**, provided the blocks all
have the same size — which is what *"equipartition"* means.

*Proof.*  Write `Δ` as the disjoint union of the blocks (`Equiv.sigmaFiberEquiv`).  A
permutation `β` of the blocks and a bijection from each block onto its image assemble into
a permutation of `Δ` that induces `β`; the bijections exist because the blocks have equal
size. -/
theorem surjective_equipartitionPsi [Fintype Δ] [DecidableEq Γ']
    (hf : Function.Surjective f)
    (hcard : ∀ γ δ : Γ', Fintype.card {d // f d = γ} = Fintype.card {d // f d = δ}) :
    Function.Surjective (equipartitionPsi hf) := by
  classical
  intro β
  -- a bijection from each block onto its image
  have hE : ∀ γ : Γ', {d // f d = γ} ≃ {d // f d = β γ} := fun γ =>
    Fintype.equivOfCardEq (hcard γ (β γ))
  set E : (Σ γ : Γ', {d // f d = γ}) ≃ Δ := Equiv.sigmaFiberEquiv f with hEdef
  set σ : Equiv.Perm Δ := E.symm.trans ((Equiv.sigmaCongr β hE).trans E) with hσ
  have hstep : ∀ d, f (σ d) = β (f d) := by
    intro d
    have h1 : E.symm d = ⟨f d, ⟨d, rfl⟩⟩ := rfl
    have h2 : σ d = ((hE (f d)) ⟨d, rfl⟩ : {d' // f d' = β (f d)}) := by
      rw [hσ]
      simp only [Equiv.trans_apply, h1]
      rfl
    rw [h2]
    exact ((hE (f d)) ⟨d, rfl⟩).2
  exact ⟨⟨σ, ⟨β, hstep⟩⟩, equipartition_beta_unique hf
    (equipartitionPsi_spec hf ⟨σ, ⟨β, hstep⟩⟩) hstep⟩

/-- §14.1, **line 10 in case (A)**: `ϕ*` is a giant representation when `Y` is a nontrivial
equipartition of the whole of `Γ`.  This is `Babai.Align_phiStar_isGiant` with the
epimorphism of line 8 supplied. -/
theorem Align_phiStar_isGiant_equipartition {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)}
    [Fintype Γ] [DecidableEq Γ] [Fintype Γ'] [DecidableEq Γ'] {f : Γ → Γ'}
    (hf : Function.Surjective f)
    (hcard : ∀ γ δ : Γ', Fintype.card {d // f d = γ} = Fintype.card {d // f d = δ})
    (ϕ : G →* Equiv.Perm Γ) (hϕ : alternatingGroup Γ ≤ ϕ.range) :
    alternatingGroup Γ' ≤
      (((equipartitionPsi hf).comp (phiStar ϕ (equipartitionAut f)))).range :=
  Align_phiStar_isGiant ϕ hϕ (equipartitionAut f) (equipartitionPsi hf)
    (surjective_equipartitionPsi hf hcard)

end Equipartition

/-! ### Eq. (73): the Johnson parameter is at least halved -/

/-- §14.2, case (B) of line 7: **the Johnson parameter is more than halved**.

From `t* ≥ 2` and `m* ≥ 2t* + 1` (the parameters of a Johnson scheme, Def. 3.2.9) and
`C(m*, t*) ≤ m` we get `(m* − 1)² < 2 C(m*,t*) ≤ 2m` (`Babai.Align_johnson_sq_lt`), and
then `2m* < m` for `m ≥ 12` (`Babai.Align_johnson_card`). -/
theorem Align_johnson_param_halved {ms ts m : ℕ} (h2 : 2 ≤ ts) (hp : 2 * ts + 1 ≤ ms)
    (hm : 12 ≤ m) (hcard : ms.choose ts ≤ m) : 2 * ms < m :=
  Align_johnson_card hm (lt_of_lt_of_le (Align_johnson_sq_lt h2 hp)
    (Nat.mul_le_mul_left 2 hcard))

/-- §14.2, case (A) of line 7: **the Johnson parameter is at least halved**.  A nontrivial
equipartition of `Δ` into `nb` blocks of common size `b ≥ 2` has `2·nb ≤ |Δ| ≤ m`. -/
theorem Align_equipartition_param_halved {b nb d m : ℕ} (hb : 2 ≤ b) (h : nb * b = d)
    (hd : d ≤ m) : 2 * nb ≤ m :=
  le_trans (Align_equipartition_card hb h) hd

end Babai
