/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the statement with exponent 5.
Not part of the faithful formalization.
-/
import Workspace.Explicit.Top.Final

/-!
# Theorem 1.1.1 with exponent 5

* `Explicit.Theorem_1_1_1_exponent5_statement`: one RAM program solves String Isomorphism, for
  every degree and alphabet, within `2^{c (log₂ N + 2)^5}` steps on inputs of size `N`. This is
  the running time of Babai's analysis (Eq. (74) of Sec. 11.4 with `q = exp(O(log³ n))` from
  Sec. 9, as `(ℓ!)^{O(log n)} · q^{O(log² n)}` of Eq. (6)).
* `Explicit.theorem_1_1_1_of_exponent5`: it implies `RAM.Targets.Theorem_1_1_1_statement`.
* `Explicit.theorem_1_1_1_exponent5_of_bounds`: it holds once the parameters of the variant
  Master meet their specifications and the costs of one node are explicit
  (`Explicit.ParamsOK`, `Explicit.StepBounds`, part 1), with the Cameron routine
  `Algo.masterCameron` of the cited Theorem 11.2.3.
-/

namespace Explicit

open RAM RAM.Targets Algo Babai

/-- **Theorem 1.1.1 with exponent 5.** -/
def Theorem_1_1_1_exponent5_statement : Prop :=
  ∃ (c : ℕ) (P : Program), ∀ n s : ℕ,
    SolvesInTime P (SIRel n s) (fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5))

/-- `c·L^5 ≤ L^{c+5}` for `L ≥ 2`. -/
theorem mul_pow_five_le (c L : ℕ) (hL : 2 ≤ L) : c * L ^ 5 ≤ L ^ (c + 5) := by
  have h1 : c ≤ L ^ c := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hL c)
  rw [pow_add]
  exact Nat.mul_le_mul_right _ h1

/-- **The explicit form implies the target of the formalization.** -/
theorem theorem_1_1_1_of_exponent5 (h : Theorem_1_1_1_exponent5_statement) :
    Theorem_1_1_1_statement := by
  obtain ⟨c, P, hP⟩ := h
  refine ⟨P, fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5), ⟨c + 5, fun N => ?_⟩, hP⟩
  exact Nat.pow_le_pow_right (by norm_num) (mul_pow_five_le c _ (by omega))

/-- **Theorem 1.1.1 with exponent 5, from the explicit costs of one node.** -/
theorem theorem_1_1_1_exponent5_of_bounds
    (h : ∃ p : Params, ParamsOK p ∧ Nonempty (StepBounds p masterCameron)) :
    Theorem_1_1_1_exponent5_statement := by
  obtain ⟨p, ok, ⟨sb⟩⟩ := h
  exact main_of_bounds masterCameron_spec.1 masterCameron_spec.2 ok sb

end Explicit
