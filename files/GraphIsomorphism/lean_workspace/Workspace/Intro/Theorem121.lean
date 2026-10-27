/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 1.2: Theorem 1.2.1, the affected/unaffected dichotomy, as stated in the introduction.
-/
import Workspace.AltQuotients.Unaffected

/-!
# §1.2 Theorem 1.2.1

The paper states Theorem 1.2.1 in the introduction and proves it in Section 10: *"Part (b) is
a simple observation (Corollary 10.3.7).  Part (a) is the main content of the result; it
appears as Theorem 10.3.5 in Section 10."*  This file restates the two parts as they are
printed in §1.2, including the sentence *"In particular, `U ≠ Ω` (at least one element is
affected)"* of part (a), which Theorem 10.3.5 does not state.

## Numbering map

| Paper | Lean |
|---|---|
| Theorem 1.2.1 (a) | `Babai.theorem_1_2_1_a` (from `Babai.theorem_10_3_5`) |
| Theorem 1.2.1 (b) | `Babai.theorem_1_2_1_b` (= `Babai.corollary_10_3_7`) |
| Remark 1.2.2 | Remark 10.2.6 of Section 10 |
| Definition 1.2.3 | Definition 3.2.9, `Babai.johnsonGraph` |
| Theorem 1.2.4 | Theorem 9.2.1 of Section 9 ("The full statement can be found in Theorem 9.2.1") |
-/

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Theorem 1.2.1 (a)** (Unaffected Stabilizers Lemma), §1.2.  "Let `G ≤ S(Ω)` be a
permutation group and let `n₀` denote the length of the largest orbit of `G`.  Let
`ϕ : G → S_m` be a giant representation.  Let `U ⊆ Ω` denote the set of elements of `Ω` not
affected by `ϕ`. … Assume `m > max{8, 2 + log₂ n₀}`.  Then `ϕ` maps `G_(U)`, the pointwise
stabilizer of `U`, onto `A_m` or `S_m` (so `ϕ : G_(U) → S_m` is still a giant
representation).  In particular, `U ≠ Ω` (at least one element is affected)."

The first conclusion is Theorem 10.3.5 (`theorem_10_3_5`): a subgroup of `S_m` containing
`A_m` is `A_m` or `S_m`.  For the second: if `U = Ω` then `G_(U) = 1`, so its image is
trivial, while `A_m` is not, since `m ≥ 9`. -/
theorem theorem_1_2_1_a {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (hϕ : IsGiantRep ϕ) (hk : LargeK k (maxOrbitLength G)) :
    alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ ∧
      unaffectedSet ϕ ≠ Set.univ := by
  have hA := theorem_10_3_5 ϕ hϕ hk
  refine ⟨hA, fun hU => ?_⟩
  have hk3 : 3 ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    have h8 : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
    have : (8 : ℕ) < k := by exact_mod_cast h8
    omega
  haveI := alternatingGroup.nontrivial_of_three_le_card hk3
  obtain ⟨σ, hσ⟩ := exists_ne (1 : alternatingGroup (Fin k))
  obtain ⟨g, hg, hgσ⟩ := hA σ.2
  rw [hU] at hg
  have hg1 : g = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    exact (mem_pointwiseStab.1 hg) z (Set.mem_univ z)
  apply hσ
  apply Subtype.ext
  rw [← hgσ, hg1, map_one]
  rfl

/-- **Theorem 1.2.1 (b)** (Affected Orbit Lemma), §1.2.  "Assume `m ≥ 5`.  If `Δ` is an
affected `G`-orbit, i.e. `Δ ∩ U = ∅`, then `ker(ϕ)` is not transitive on `Δ`; in fact, each
orbit of `ker(ϕ)` in `Δ` has length `≤ |Δ|/m`."  This is Corollary 10.3.7
(`corollary_10_3_7`). -/
theorem theorem_1_2_1_b {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
    (ϕ : G →* Equiv.Perm (Fin k)) (hϕ : IsGiantRep ϕ) (hk5 : 5 ≤ k) (x : Ω)
    (hΔ : ∀ z ∈ orbit G x, Affected ϕ z) (y : Ω) (hy : y ∈ orbit G x) :
    k * Nat.card (orbit ϕ.ker y) ≤ Nat.card (orbit G x) ∧
      Nat.card (orbit ϕ.ker y) < Nat.card (orbit G x) :=
  corollary_10_3_7 ϕ hϕ hk5 x hΔ y hy

end Babai
