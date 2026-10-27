/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background group theory used by Section 10: solvability of `S_n` for `n ≤ 4`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Workspace.Prelim.AlternatingSimple

/-!
# Solvability of the small symmetric groups

Proposition 10.2.3 of the paper says, in its base case `s = 1`: "For `s = 1` we need to
prove `n ≥ 5`.  This follows from the solvability of `S₄`."  This file proves that
`S(Ω)` is solvable for `|Ω| ≤ 4` and deduces the statement the paper uses: a nonabelian
simple group is not involved in `S(Ω)` for `|Ω| ≤ 4`.

The chain used is `1 ◁ V₄ ◁ A₄ ◁ S₄` with abelian quotients: Mathlib's
`alternatingGroup.kleinFour` is normal in `A₄` with quotient of order `3`, and `A₄` is
the kernel of `Equiv.Perm.sign`.  A general `Ω` with `|Ω| ≤ 4` is handled by the
injection `S(Ω) → S₄` of `Equiv.Perm.viaEmbeddingHom`.
-/

namespace Babai

open Equiv Equiv.Perm Subgroup

/-- `A₄` is solvable: `1 ◁ V₄ ◁ A₄` with abelian quotients. -/
theorem isSolvable_alternatingGroup_fin_four : IsSolvable (alternatingGroup (Fin 4)) := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  haveI hnorm : (alternatingGroup.kleinFour (Fin 4)).Normal :=
    alternatingGroup.normal_kleinFour h4
  haveI hV : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
    alternatingGroup.kleinFour_isKleinFour h4
  haveI : IsSolvable (alternatingGroup.kleinFour (Fin 4)) :=
    isSolvable_of_comm
      (isMulCommutative_iff.1 (IsKleinFour.isMulCommutative
        (G := alternatingGroup.kleinFour (Fin 4))))
  have hq : Nat.card (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) = 3 := by
    have h1 : Nat.card (alternatingGroup (Fin 4)) = 12 :=
      alternatingGroup.card_of_card_eq_four h4
    have h2 : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
      alternatingGroup.kleinFour_card_of_card_eq_four h4
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (alternatingGroup.kleinFour (Fin 4))
    rw [h1, h2] at h3
    omega
  haveI : IsSolvable (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) :=
    isSolvable_of_comm (isMulCommutative_iff.1 (isMulCommutative_of_card_eq_three hq))
  exact solvable_of_ker_le_range (alternatingGroup.kleinFour (Fin 4)).subtype
    (QuotientGroup.mk' (alternatingGroup.kleinFour (Fin 4)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- `S₄` is solvable. -/
theorem isSolvable_perm_fin_four : IsSolvable (Equiv.Perm (Fin 4)) := by
  haveI := isSolvable_alternatingGroup_fin_four
  refine solvable_of_ker_le_range (alternatingGroup (Fin 4)).subtype
    (Equiv.Perm.sign) ?_
  rw [Subgroup.range_subtype]
  exact le_of_eq (_root_.alternatingGroup_eq_sign_ker (α := Fin 4)).symm

/-- `S(Ω)` is solvable for `|Ω| ≤ 4`. -/
theorem isSolvable_perm_of_card_le_four {Ω : Type*} [Finite Ω] (h : Nat.card Ω ≤ 4) :
    IsSolvable (Equiv.Perm Ω) := by
  haveI := Fintype.ofFinite Ω
  obtain ⟨e⟩ : Nonempty (Ω ↪ Fin 4) := by
    refine Function.Embedding.nonempty_iff_card_le.2 ?_
    have h4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    rw [h4, ← Nat.card_eq_fintype_card]
    exact h
  haveI := isSolvable_perm_fin_four
  exact solvable_of_solvable_injective (Equiv.Perm.viaEmbeddingHom_injective (ι := e))

/-- Background, used in the base case `s = 1` of Prop. 10.2.3: "For `s = 1` we need to
prove `n ≥ 5`.  This follows from the solvability of `S_4`."

A nonabelian simple group is not involved in `S(Ω)` for `|Ω| ≤ 4`, because `S_4` is
solvable and sections of a solvable group are solvable. -/
theorem five_le_card_of_involved_nonabelian_simple {Ω : Type*} [Finite Ω] (R : Type*)
    [Group R] [Finite R] [IsSimpleGroup R] (hR : ¬ ∀ a b : R, a * b = b * a)
    (h : ∃ (H : Subgroup (Equiv.Perm Ω)) (f : H →* R), Function.Surjective f) :
    5 ≤ Nat.card Ω := by
  by_contra hcon
  obtain ⟨H, f, hf⟩ := h
  haveI := isSolvable_perm_of_card_le_four (Ω := Ω) (by omega)
  haveI : IsSolvable H := solvable_of_solvable_injective H.subtype_injective
  haveI : IsSolvable R := solvable_of_surjective hf
  exact hR (IsSimpleGroup.comm_iff_isSolvable.2 ‹IsSolvable R›)

end Babai
