/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 2.3: the symmetry defect from a bound on the twin equivalence classes.
-/
import Workspace.Prelim.Structures

/-!
# §2.3  Reading the symmetry defect off the twin equivalence classes

Definition 2.3.13 defines the symmetricity `s(G)` as the largest size of a *set of twins*
(Def. 2.3.11), and the relative symmetry defect as `1 − s(G)/|Ω|`.  Every argument in the
paper that bounds a symmetry defect from below does it by bounding the **twin equivalence
classes**: for instance §9.7, Case 3, *"the relative symmetry defect of `H` is `≥ 1/2`"*,
is the negation of Case 2, *"there is an `H`-twin equivalence class `C ⊆ V₂` of size
`|C| ≥ n₂/2`"*.

The step between the two is Observation 2.3.12: a set of twins is contained in a twin
equivalence class (`Babai.IsTwinSet.subset_twinClass`), so the largest set of twins *is* a
largest twin equivalence class.  This file records that step in the two forms §9.7 uses.
-/

namespace Babai

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Def. 2.3.13 and Obs. 2.3.12.  If every twin equivalence class has at most `m` points,
then `s(G) ≤ m`: a set of twins is empty, or contained in the twin equivalence class of
any one of its points. -/
theorem symmetricity_le_of_twinClass_ncard_le (G : Subgroup (Equiv.Perm Ω)) {m : ℕ}
    (h : ∀ x : Ω, (twinClass G x).ncard ≤ m) : symmetricity G ≤ m := by
  classical
  refine Finset.sup_le fun Ψ hΨ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hΨ
  rcases Finset.eq_empty_or_nonempty Ψ with rfl | ⟨x, hx⟩
  · simp
  refine le_trans ?_ (h x)
  have hsub : (↑Ψ : Set Ω) ⊆ twinClass G x := hΨ.subset_twinClass (by exact_mod_cast hx)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset] at hle

/-- Def. 2.3.13.  A bound on the twin equivalence classes is a lower bound on the relative
symmetry defect: if every twin equivalence class has at most `m` points then
`defect(G) ≥ 1 − m/|Ω|`.

For `|Ω| = 0` both sides are Lean's `1 − 0/0 = 1`, so the statement is still true; the
paper's range assumes `Ω ≠ ∅`. -/
theorem defect_ge_of_twinClass_ncard_le (G : Subgroup (Equiv.Perm Ω)) {m : ℕ}
    (h : ∀ x : Ω, (twinClass G x).ncard ≤ m) :
    1 - (m : ℚ) / (Fintype.card Ω : ℚ) ≤ defect G := by
  have hs := symmetricity_le_of_twinClass_ncard_le G h
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | hpos
  · rw [defect, relSymmetricity, h0]
    simp
  have hn : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast hpos
  have hle : (symmetricity G : ℚ) ≤ (m : ℚ) := by exact_mod_cast hs
  rw [defect, relSymmetricity, sub_le_sub_iff_left]
  gcongr

end Babai
