/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 8, part B.
-/
import Workspace.AltQuotients.DM52.Degree8Model

/-!
# Kernel checks for degree `8`, part B

The check behind `degree_eight_candidates2` of `Degree8`, over `g = (0 7) · lift68 p`. Each check runs over the
permutations `lift68 p` of `Fin 8` fixing `0` and `7` (`p : Perm (Fin 6)`), split by the value
`p 0`, so that no single kernel evaluation holds all cases at once.
-/

namespace Babai.DM52

open Equiv Equiv.Perm

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 0`. -/
theorem d8c2_0 : ∀ p : Perm (Fin 6), p 0 = 0 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 1`. -/
theorem d8c2_1 : ∀ p : Perm (Fin 6), p 0 = 1 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 2`. -/
theorem d8c2_2 : ∀ p : Perm (Fin 6), p 0 = 2 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 3`. -/
theorem d8c2_3 : ∀ p : Perm (Fin 6), p 0 = 3 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 4`. -/
theorem d8c2_4 : ∀ p : Perm (Fin 6), p 0 = 4 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_eight_candidates2`, over `g = (0 7) · lift68 p` with
`p 0 = 5`. -/
theorem d8c2_5 : ∀ p : Perm (Fin 6), p 0 = 5 → sign (swap 0 7 * lift68 p) = 1 →
    IsAff8 (swap 0 7 * lift68 p) ∨
      Bad35 [c8, mu8, s8, swap 0 7 * lift68 p, (swap 0 7 * lift68 p)⁻¹] words8 := by
  decide +kernel

end Babai.DM52
