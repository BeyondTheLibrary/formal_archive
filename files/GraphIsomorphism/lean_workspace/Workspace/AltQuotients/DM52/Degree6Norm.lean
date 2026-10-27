/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 6, kernel checks.
-/
import Workspace.AltQuotients.DM52.Degree6Model

/-!
# Kernel checks for degree `6`

The check behind `inPGL6_of_normalizes` of `Degree6`, split by the value `g 0`, so that no
single kernel evaluation holds all cases at once.
-/

namespace Babai.DM52

open Equiv Equiv.Perm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 0`. -/
theorem d6norm_0 : ∀ g : Perm (Fin 6), g 0 = 0 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 1`. -/
theorem d6norm_1 : ∀ g : Perm (Fin 6), g 0 = 1 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 2`. -/
theorem d6norm_2 : ∀ g : Perm (Fin 6), g 0 = 2 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 3`. -/
theorem d6norm_3 : ∀ g : Perm (Fin 6), g 0 = 3 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 4`. -/
theorem d6norm_4 : ∀ g : Perm (Fin 6), g 0 = 4 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `inPGL6_of_normalizes`, for `g 0 = 5`. -/
theorem d6norm_5 : ∀ g : Perm (Fin 6), g 0 = 5 → InC6 (g * c6 * g⁻¹) →
    InC6 (g * nu6 * g⁻¹) → InC6 (g * t6 * g⁻¹) → InPGL6 g := by
  decide +kernel

end Babai.DM52
