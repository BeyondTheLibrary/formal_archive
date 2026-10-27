/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 9, the finite check.
-/
import Workspace.AltQuotients.DM52.Degree9Model

/-!
# Degree 9: the finite check of the recognition, in parts

The check of `Babai.DM52.degree_nine_candidates` over the `720` permutations `p` of `Fin 6`,
split by the values `p 0` and `p 1` into `30` parts of `24` permutations each. Each part is a
separate kernel computation, so the memory of one check stays small. This file has the parts
with `p 0 ∈ {0, 1}`.
-/

namespace Babai.DM52
open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_0_1 : ∀ p : Perm (Fin 6), p 0 = 0 → p 1 = 1 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_0_2 : ∀ p : Perm (Fin 6), p 0 = 0 → p 1 = 2 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_0_3 : ∀ p : Perm (Fin 6), p 0 = 0 → p 1 = 3 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_0_4 : ∀ p : Perm (Fin 6), p 0 = 0 → p 1 = 4 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_0_5 : ∀ p : Perm (Fin 6), p 0 = 0 → p 1 = 5 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_1_0 : ∀ p : Perm (Fin 6), p 0 = 1 → p 1 = 0 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_1_2 : ∀ p : Perm (Fin 6), p 0 = 1 → p 1 = 2 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_1_3 : ∀ p : Perm (Fin 6), p 0 = 1 → p 1 = 3 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_1_4 : ∀ p : Perm (Fin 6), p 0 = 1 → p 1 = 4 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem d9cand_1_5 : ∀ p : Perm (Fin 6), p 0 = 1 → p 1 = 5 →
    sign (swap 0 7 * lift6 p) = 1 →
    (swap 0 7 * lift6 p = t9 ∨ swap 0 7 * lift6 p = t9 * mu9 ∨
      swap 0 7 * lift6 p = t9 * mu9 ^ 2) ∨
    (rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ∨
      rho9⁻¹ * (swap 0 7 * lift6 p) * rho9 = t9 * mu9 ^ 2) ∨
    Bad35 [c9, mu9, io9, swap 0 7 * lift6 p, (swap 0 7 * lift6 p)⁻¹] words9 := by
  decide +kernel

end Babai.DM52
