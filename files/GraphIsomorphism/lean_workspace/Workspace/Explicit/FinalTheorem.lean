/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the final statements, with no
hypotheses. Not part of the faithful formalization.
-/
import Workspace.Explicit.L57Route5
import Workspace.Explicit.Tier2.PolyAssembly

/-!
# Theorem 1.1.1 with exponent 5: the final statements

Both theorems apply the assembly to the bounds of route 5 (`Explicit.route5Bounds`, part 1),
which hold at every parameter set with `t = 3`.

* `Explicit.theorem_1_1_1_exponent5_explicit`: one RAM program solves String Isomorphism within
  `2^{cFinal sb (log₂ N + 2)^5}` steps, for step bounds `sb` at parameters with the explicit
  line-1 thresholds `B = 25`, `C₀ = (max 64 25!)! + 1`.
* `Explicit.theorem_1_1_1_exponent5_caps`: the same, where moreover `a = 4096`, `b = 4` and
  `sb` has `kB = 15`, `dB = 4`, `kM = 6`, `dM = 3`, `Aw = 6`.
* `Explicit.theorem_1_1_1_exponent5_poly`: the same, where moreover `kP = 208752199`,
  `dP = 3686480`.

`cFinal sb` is the closed formula of `Explicit.cFinal_closed` in the fields of `sb`; the fields
`As ds kS Ap` are still existential (`DESIGN.md`, section 7).
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- **Theorem 1.1.1 (Sec. 1.1) with exponent 5, at the explicit line-1 thresholds**: for step
bounds `sb` at parameters with `B = 25`, `C₀ = (max 64 25!)! + 1`, one RAM program solves
String Isomorphism within `2^{cFinal sb (log₂ N + 2)^5}` steps. -/
theorem theorem_1_1_1_exponent5_explicit :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) :=
  theorem_1_1_1_exponent5_of_route5 (fun p _ _ _ h3 _ _ _ => route5Bounds p (by omega))

/-- **Theorem 1.1.1 (Sec. 1.1) with exponent 5, at the numeral caps**: as
`Explicit.theorem_1_1_1_exponent5_explicit`, where moreover `a = 4096`, `b = 4`, and the step
bounds have `kB = 15`, `dB = 4`, `kM = 6`, `dM = 3`, `Aw = 6`. -/
theorem theorem_1_1_1_exponent5_caps :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.a = capAX ∧ p.b = capBX ∧
      p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      sb.kB = 15 ∧ sb.dB = 4 ∧ sb.kM = 6 ∧ sb.dM = 3 ∧ sb.Aw = 6 ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) :=
  theorem_1_1_1_exponent5_of_route5_caps
    (fun p _ _ _ _ _ h3 _ _ _ => route5Bounds p (by omega))

/-- **Theorem 1.1.1 (Sec. 1.1) with exponent 5, with the numerals `kP dP`**: as
`Explicit.theorem_1_1_1_exponent5_caps`, where moreover the step bounds have
`kP = 208752199`, `dP = 3686480`. -/
theorem theorem_1_1_1_exponent5_poly :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.a = capAX ∧ p.b = capBX ∧
      p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      sb.kB = 15 ∧ sb.dB = 4 ∧ sb.kM = 6 ∧ sb.dM = 3 ∧ sb.Aw = 6 ∧
      sb.kP = kPX ∧ sb.dP = dPX ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) :=
  theorem_1_1_1_exponent5_of_route5_poly
    (fun p _ _ _ _ _ h3 _ _ _ => route5Bounds p (by omega))

end Explicit
