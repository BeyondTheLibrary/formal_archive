/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background group theory used by Section 10: the smallest index of a proper subgroup of
`A_k` (and of a subgroup of `S_k` not containing `A_k`) is `k`.
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Workspace.Prelim.AlternatingSimple

/-!
# The index of a subgroup that does not contain `A(Ω)`

The paper uses, in the proof of Cor. 10.3.7: "For `k ≥ 5`, the largest proper subgroup of
`A_k` has index `k`, and the largest subgroup of `S_k` not containing `A_k` also has index
`k`."  Both halves are `Babai.card_le_relIndex_of_not_alternating_le` below.

The proof is the standard coset-action argument, which uses the simplicity of `A(Ω)`
(`Workspace/Prelim/AlternatingSimple.lean`): if `S < A(Ω)` had index `m < |Ω|`, then the
action of `A(Ω)` on the `m` cosets of `S` would be faithful (its kernel is the normal core
of `S`, a proper normal subgroup of the simple group `A(Ω)`, hence trivial), giving
`|Ω|!/2 = |A(Ω)| ≤ m! ≤ (|Ω| - 1)!`, which fails for `|Ω| ≥ 3`.
-/

namespace Babai

open Equiv Equiv.Perm Subgroup MulAction

/-- In a finite simple group, a proper subgroup `H` satisfies `|G| ≤ |G : H|!`:
the action on the cosets of `H` is faithful. -/
theorem card_le_factorial_index_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) : Nat.card G ≤ Nat.factorial H.index := by
  have hne : H.normalCore ≠ ⊤ := fun hc => hH (top_le_iff.1 (hc ▸ H.normalCore_le))
  have hbot : H.normalCore = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ (H.normalCore_normal)).resolve_right hne
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hbot]
  calc Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.factorial (Nat.card (G ⧸ H)) := Nat.card_perm
    _ = Nat.factorial H.index := rfl

/-- Background, used in the proof of Cor. 10.3.7: "For `k ≥ 5`, the largest proper
subgroup of `A_k` has index `k`, and the largest subgroup of `S_k` not containing `A_k`
also has index `k`."

Both halves are the single statement below with `K = A(Ω)` resp. `K = S(Ω)`: if
`A(Ω) ≤ K ≤ S(Ω)` and `H ≤ K` does not contain `A(Ω)`, then `|K : H| ≥ |Ω|`. -/
theorem card_le_relIndex_of_not_alternating_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : 5 ≤ Fintype.card Ω) {K H : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) (hHK : H ≤ K) (hH : ¬ alternatingGroup Ω ≤ H) :
    Fintype.card Ω ≤ H.relIndex K := by
  haveI : Nontrivial Ω := by
    rw [← Fintype.one_lt_card_iff_nontrivial]; omega
  -- Step 1: `|A : A ∩ H| ≤ |K : H|`, since `A/(A ∩ H) → K/H` is injective.
  have hne : H.relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
  have step1 : H.relIndex (alternatingGroup Ω) ≤ H.relIndex K :=
    Subgroup.relIndex_le_of_le_right hK hne
  -- Step 2: `|Ω| ≤ |A : A ∩ H|`.
  have step2 : Fintype.card Ω ≤ H.relIndex (alternatingGroup Ω) := by
    haveI : IsSimpleGroup (alternatingGroup Ω) := isSimpleGroup_alternatingGroup h5
    have hSne : H.subgroupOf (alternatingGroup Ω) ≠ ⊤ := by
      intro hc
      exact hH (Subgroup.subgroupOf_eq_top.1 hc)
    have hcard := card_le_factorial_index_of_simple (G := alternatingGroup Ω) hSne
    by_contra hcon
    rw [not_le] at hcon
    set m : ℕ := H.relIndex (alternatingGroup Ω) with hm
    -- `2 * |A| = |Ω|!` and `|A| ≤ m!` with `m < |Ω|`.
    have h2 : 2 * Nat.card (alternatingGroup Ω) = Nat.card (Equiv.Perm Ω) :=
      two_mul_nat_card_alternatingGroup
    rw [Nat.card_perm] at h2
    obtain ⟨p, hp⟩ : ∃ p, Nat.card Ω = p + 1 := by
      refine ⟨Nat.card Ω - 1, ?_⟩
      rw [Nat.card_eq_fintype_card]
      omega
    have hmp : m ≤ p := by
      rw [Nat.card_eq_fintype_card] at hp
      omega
    have hfac : Nat.factorial m ≤ Nat.factorial p := Nat.factorial_le hmp
    have hppos : 0 < Nat.factorial p := Nat.factorial_pos p
    have hcard' : Nat.card (alternatingGroup Ω) ≤ Nat.factorial p :=
      le_trans hcard hfac
    rw [hp, Nat.factorial_succ] at h2
    have hple : 5 ≤ p + 1 := by
      rw [Nat.card_eq_fintype_card] at hp; omega
    nlinarith [hcard', h2, hppos]
  omega

end Babai
