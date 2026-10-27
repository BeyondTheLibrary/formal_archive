/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.2: the wreath product in its product action (Definition 11.2.2).
-/
import Workspace.Luks.Defs

/-!
# The base group of a wreath product in its product action

Definition 11.2.2 puts a Cameron group `G` between the base group `(A_k^(t))^s` and the
wreath product `S_k^(t) ≀ S_s` in its product action.  The proof of Theorem 11.2.1 takes
`N = (A_k^(t))^s` and needs two facts about that pair of groups, which are proved here in
general form, for a subgroup `H` of `S(Γ)` that is normal in a subgroup `K` of `S(Γ)`:

* `Babai.basePower_isNormalIn_wreathProduct`: `H^s` is normal in `K ≀ S_s`;
* `Babai.card_basePower`: `|H^s| = |H|^s`.

Nothing here corresponds to a numbered item of the paper.
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Γ : Type*} {s : ℕ}

/-! ### Computing with `wreathPerm` -/

@[simp] theorem wreathPerm_one_apply (h : Fin s → Equiv.Perm Γ) (f : Fin s → Γ) (i : Fin s) :
    wreathPerm h 1 f i = h i (f i) := by
  simp [wreathPerm]

/-- The inverse of a wreath element: `(h, π)⁻¹ = ((h ∘ π)⁻¹, π⁻¹)`. -/
theorem wreathPerm_inv (h : Fin s → Equiv.Perm Γ) (π : Equiv.Perm (Fin s)) :
    (wreathPerm h π)⁻¹ = wreathPerm (fun i => (h (π i))⁻¹) π⁻¹ := by
  ext f i
  simp [wreathPerm, Equiv.Perm.inv_def]

/-- Conjugating an element of the base group by an element of the wreath product stays in
the base group: the `i`-th coordinate becomes `h i * g (π⁻¹ i) * (h i)⁻¹`. -/
theorem wreathPerm_conj (h g : Fin s → Equiv.Perm Γ) (π : Equiv.Perm (Fin s)) :
    wreathPerm h π * wreathPerm g 1 * (wreathPerm h π)⁻¹ =
      wreathPerm (fun i => h i * g (π⁻¹ i) * (h i)⁻¹) 1 := by
  ext f i
  simp [wreathPerm, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]

/-! ### Normality of the base group -/

/-- If `H` is closed under conjugation by the elements of `K`, then the base group `H^s`
is normal in the wreath product `K ≀ S_s` (both in the product action on `Fin s → Γ`).

This is the fact behind the choice of `N` in the proof of Theorem 11.2.1 (§11.2). -/
theorem basePower_isNormalIn_wreathProduct {H K : Subgroup (Equiv.Perm Γ)}
    (hHK : H ≤ K) (hconj : ∀ σ ∈ K, ∀ a ∈ H, σ * a * σ⁻¹ ∈ H) (s : ℕ) :
    IsNormalIn (basePower H s) (wreathProduct K s) where
  le := le_trans (fun w hw => by
      obtain ⟨g, hg, rfl⟩ := hw
      exact ⟨g, fun i => hHK (hg i), rfl⟩ :
    basePower H s ≤ basePower K s) (basePower_le_wreathProduct K s)
  conj_mem := by
    rintro w ⟨h, π, hh, rfl⟩ b ⟨g, hg, rfl⟩
    refine ⟨fun i => h i * g (π⁻¹ i) * (h i)⁻¹, fun i => hconj (h i) (hh i) _ (hg _), ?_⟩
    exact wreathPerm_conj h g π

/-! ### The order of the base group -/

/-- The base group `H^s` has order `|H|^s`: the tuple `h` is determined by the permutation
`wreathPerm h 1` as soon as `Γ` is nonempty. -/
theorem card_basePower [Nonempty Γ] (H : Subgroup (Equiv.Perm Γ)) (s : ℕ) :
    Nat.card (basePower H s) = Nat.card H ^ s := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty Γ›
  have hbij : Function.Bijective
      (fun h : Fin s → H =>
        (⟨wreathPerm (fun i => ((h i : Equiv.Perm Γ))) 1,
          ⟨fun i => ((h i : Equiv.Perm Γ)), fun i => (h i).2, rfl⟩⟩ : basePower H s)) := by
    constructor
    · intro h h' hEq
      have hEq' : wreathPerm (fun i => ((h i : Equiv.Perm Γ))) 1
          = wreathPerm (fun i => ((h' i : Equiv.Perm Γ))) 1 := congrArg Subtype.val hEq
      funext i
      refine Subtype.ext (Equiv.ext fun x => ?_)
      have := congrArg (fun p : Equiv.Perm (Fin s → Γ) =>
        p (fun j => if j = i then x else x₀) i) hEq'
      simpa using this
    · rintro ⟨w, g, hg, rfl⟩
      exact ⟨fun i => ⟨g i, hg i⟩, rfl⟩
  calc Nat.card (basePower H s) = Nat.card (Fin s → H) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card H ^ s := by simp [Nat.card_pi]

end Babai
