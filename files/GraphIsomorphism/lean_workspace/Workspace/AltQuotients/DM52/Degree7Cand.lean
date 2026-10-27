/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 7, kernel checks.
-/
import Workspace.AltQuotients.DM52.Degree7Model

/-!
# Kernel checks for degree `7`

The checks behind `fanoMatrix_spec` and `degree_seven_candidates` of `Degree7`.  They run over
`g = (0 a) · lift67 p` with `p : Perm (Fin 6)` (for `fanoMatrix_spec`, one declaration per
value `a = g 0`) and over `g = lift67 p` (for `degree_seven_candidates`, one declaration per
value `p 0`), so that no single kernel evaluation holds all cases at once.
-/

namespace Babai.DM52

open Equiv Equiv.Perm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 0) · lift67 p`. -/
theorem d7fano_0 : ∀ p : Perm (Fin 6), IsFano (swap 0 0 * lift67 p) →
    (fanoMatrix (swap 0 0 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 0 * lift67 p)) i =
        (swap 0 0 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 1) · lift67 p`. -/
theorem d7fano_1 : ∀ p : Perm (Fin 6), IsFano (swap 0 1 * lift67 p) →
    (fanoMatrix (swap 0 1 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 1 * lift67 p)) i =
        (swap 0 1 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 2) · lift67 p`. -/
theorem d7fano_2 : ∀ p : Perm (Fin 6), IsFano (swap 0 2 * lift67 p) →
    (fanoMatrix (swap 0 2 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 2 * lift67 p)) i =
        (swap 0 2 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 3) · lift67 p`. -/
theorem d7fano_3 : ∀ p : Perm (Fin 6), IsFano (swap 0 3 * lift67 p) →
    (fanoMatrix (swap 0 3 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 3 * lift67 p)) i =
        (swap 0 3 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 4) · lift67 p`. -/
theorem d7fano_4 : ∀ p : Perm (Fin 6), IsFano (swap 0 4 * lift67 p) →
    (fanoMatrix (swap 0 4 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 4 * lift67 p)) i =
        (swap 0 4 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 5) · lift67 p`. -/
theorem d7fano_5 : ∀ p : Perm (Fin 6), IsFano (swap 0 5 * lift67 p) →
    (fanoMatrix (swap 0 5 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 5 * lift67 p)) i =
        (swap 0 5 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `fanoMatrix_spec`, over `g = (0 6) · lift67 p`. -/
theorem d7fano_6 : ∀ p : Perm (Fin 6), IsFano (swap 0 6 * lift67 p) →
    (fanoMatrix (swap 0 6 * lift67 p)).det = 1 ∧
      ∀ i, psi7F (fanoMatrix (swap 0 6 * lift67 p)) i =
        (swap 0 6 * lift67 p : Perm (Fin 7)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 0`. -/
theorem d7cand_0 : ∀ p : Perm (Fin 6), p 0 = 0 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 1`. -/
theorem d7cand_1 : ∀ p : Perm (Fin 6), p 0 = 1 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 2`. -/
theorem d7cand_2 : ∀ p : Perm (Fin 6), p 0 = 2 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 3`. -/
theorem d7cand_3 : ∀ p : Perm (Fin 6), p 0 = 3 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 4`. -/
theorem d7cand_4 : ∀ p : Perm (Fin 6), p 0 = 4 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The check behind `degree_seven_candidates`, over `g = lift67 p` with `p 0 = 5`. -/
theorem d7cand_5 : ∀ p : Perm (Fin 6), p 0 = 5 → sign (lift67 p) = 1 → lift67 p ≠ 1 →
    lift67 p ≠ mu7 → lift67 p ≠ mu7 ^ 2 →
    IsFano (lift67 p) ∨ IsFano (rho7⁻¹ * lift67 p * rho7) ∨
      Bad35 [c7, mu7, lift67 p, (lift67 p)⁻¹] words7 := by
  decide +kernel

end Babai.DM52
