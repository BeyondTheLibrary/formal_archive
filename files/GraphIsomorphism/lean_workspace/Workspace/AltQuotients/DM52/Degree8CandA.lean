/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 8, part A.
-/
import Workspace.AltQuotients.DM52.Degree8Model

/-!
# Kernel checks for degree `8`, part A

The checks behind `aff8_base` and `degree_eight_candidates1` of `Degree8`. Each check runs over the
permutations `lift68 p` of `Fin 8` fixing `0` and `7` (`p : Perm (Fin 6)`), split by the value
`p 0`, so that no single kernel evaluation holds all cases at once.
-/

namespace Babai.DM52

open Equiv Equiv.Perm

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `aff8_base`, over `g = lift68 p`. -/
theorem d8aff : ∀ p : Perm (Fin 6), IsAff8 (lift68 p) → lift68 p 1 = 1 →
    (lift68 p 2 = 2 ∨ lift68 p 2 = 4 ∨ lift68 p 2 = 5 ∨ lift68 p 2 = 6) ∧
      (lift68 p 2 = 2 → lift68 p = 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 0`. -/
theorem d8c1_0 : ∀ p : Perm (Fin 6), p 0 = 0 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 1`. -/
theorem d8c1_1 : ∀ p : Perm (Fin 6), p 0 = 1 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 2`. -/
theorem d8c1_2 : ∀ p : Perm (Fin 6), p 0 = 2 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 3`. -/
theorem d8c1_3 : ∀ p : Perm (Fin 6), p 0 = 3 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 4`. -/
theorem d8c1_4 : ∀ p : Perm (Fin 6), p 0 = 4 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates1`, over `g = lift68 p` with `p 0 = 5`. -/
theorem d8c1_5 : ∀ p : Perm (Fin 6), p 0 = 5 → sign (lift68 p) = 1 →
    lift68 p ≠ 1 → lift68 p ≠ mu8 → lift68 p ≠ mu8 ^ 2 →
    IsAff8 (lift68 p) ∨ IsAff8 (rho8⁻¹ * lift68 p * rho8) ∨
      Bad35 [c8, mu8, lift68 p, (lift68 p)⁻¹] words7 := by
  decide +kernel

end Babai.DM52
