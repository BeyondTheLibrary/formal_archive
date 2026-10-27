/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: Proposition 12.0.9 (setwise stabilizers through a giant representation).
-/
import Workspace.TopAction.PrelimExtra

/-!
# §12 Proposition 12.0.9

The mathematical content of Proposition 12.0.9 is the identity `G_C = ϕ⁻¹((G^ϕ)_C)`; the
running-time claim ("can be found in polynomial time") is pending, see the corrected paper.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Equiv.Perm Ω)}

/-- §12, Proposition 12.0.9.  The setwise stabilizer
`G_C = {σ ∈ G | C^{σ^ϕ} = C}` of `C ⊆ Γ` *through* the representation `ϕ`. -/
def setwiseStabViaHom (ϕ : G →* Equiv.Perm Γ) (C : Set Γ) : Subgroup G :=
  Subgroup.comap ϕ (setwiseStabilizer ⊤ C)

@[simp] theorem mem_setwiseStabViaHom {ϕ : G →* Equiv.Perm Γ} {C : Set Γ} {σ : G} :
    σ ∈ setwiseStabViaHom ϕ C ↔ (ϕ σ) '' C = C := by
  simp [setwiseStabViaHom, Subgroup.mem_comap, mem_setwiseStabilizer]

/-- §12, **Proposition 12.0.9**.

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S(Γ)` a giant representation.  Let
> `C ⊆ Γ`.  Then the setwise stabilizer `G_C = {σ ∈ G | C^{σ^ϕ} = C}` can be found in
> polynomial time.
>
> *Proof.*  Let `H = (G^ϕ)_C`.  Given that `G^ϕ` is a giant, finding `H` is
> straightforward.  Now `G_C = ϕ⁻¹(H)`.

The mathematical content is the last equation, `G_C = ϕ⁻¹((G^ϕ)_C)`.  ("Finding `H`" and
the polynomial time bound are on the RAM in `Workspace/Algo/TopStab.lean`:
`Algo.polyFun_topStab`, `Algo.topStab_spec_of_wf`.) -/
theorem Proposition_12_0_9 (ϕ : G →* Equiv.Perm Γ) (_hϕ : IsGiantRep ϕ) (C : Set Γ) :
    setwiseStabViaHom ϕ C = Subgroup.comap ϕ (setwiseStabilizer ϕ.range C) := by
  ext σ
  rw [mem_setwiseStabViaHom, Subgroup.mem_comap, mem_setwiseStabilizer]
  exact ⟨fun h => ⟨⟨σ, rfl⟩, h⟩, fun h => h.2⟩

end Babai
