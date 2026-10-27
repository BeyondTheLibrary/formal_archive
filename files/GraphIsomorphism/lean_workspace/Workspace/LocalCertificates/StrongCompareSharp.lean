/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1: Proposition 13.1.11 with the printed constant, for the strong-descent form.
-/
import Workspace.LocalCertificates.StrongCompare
import Workspace.LocalCertificates.ComparePairedCount

/-!
# Proposition 13.1.11 with the printed `t!·n²`, strong descent

`Babai.calls_pairedComparisonStrong` bounds the calls of the strong-descent comparison
(lines 04e1 and 04e2 of Procedure Recompute `H(W)` and `Q`) by `2·t!·n²`: at most `n`
rounds, each with at most `t!` cosets and at most `n` kernel-orbit calls for each of the two
lines.  The printed bound is `t!·n²`.  The sharper round count of
`Workspace/LocalCertificates/ComparePairedCount.lean` (the window grows by at least `t`
points per round, so there are at most `n/t` rounds; `Babai.haltIndex_mul_le_card`) gives the
printed constant here too, exactly as `Babai.proposition_13_1_11_paired_calls_sharp` does for
the older form.
-/

namespace Babai

open MulAction Equiv
open scoped Pointwise Classical

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {x y : Ω → Λ} {T : Set Γ}

/-- **Proposition 13.1.11**, §13.1, strong-descent form, with the printed constant: the
paired comparison makes at most `t!·n²` calls, each on a window of at most `n/t` points. -/
theorem calls_pairedComparisonStrong_sharp (h5 : 5 ≤ T.ncard) (σ : Perm Ω)
    (E : StrongPairEnum Ω) (h : StrongPairBound ϕ x T E) :
    (pairedComparisonStrong ϕ x y T σ E).calls.length ≤
        Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (pairedComparisonStrong ϕ x y T σ E).calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  refine ⟨?_, (calls_pairedComparisonStrong (y := y) h5 σ E h).2⟩
  rw [calls_pairedComparisonStrong_eq]
  exact (length_calls_pairedLoopStrong (y := y) σ E h _ le_rfl).trans
    (rounds_calls_le (haltIndex_mul_le_card h5) (by omega))

/-- **Proposition 13.1.11**, §13.1, strong-descent form with an optional transporter, with
the printed constant `t!·n²`. -/
theorem calls_compareStrong_sharp (h5 : 5 ≤ T.ncard) (σ : Option (Perm Ω))
    (E : StrongPairEnum Ω) (h : StrongPairBound ϕ x T E) :
    (compareStrong ϕ x T y σ E).calls.length ≤ Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (compareStrong ϕ x T y σ E).calls, T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  cases σ with
  | none => simp [compareStrong]
  | some ρ => exact calls_pairedComparisonStrong_sharp h5 ρ E h

end Babai
