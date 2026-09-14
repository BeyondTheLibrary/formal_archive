import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim2RimPath

/-!
# The wheel-to-path step in claim (2) of 19.2

Stated without the Berge hypothesis this step is false, and it stays false even when
`A = A₁`: a wheel can offer two disjoint hub-complete rim edges of which only one survives
on a path whose interior stays in `A`.  This version therefore includes the Berge and
complete-end hypotheses used in the parity argument, and requires the inductive wheel to
have its rim in `{x₀,x₁,z} ∪ A`; that wheel is supplied by
`Thm192Claim2Localization.inductive_wheel_with_rim_in_A`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm192Claim2Gap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (printed p. 118, claim (2)): *"From the minimality of `|Y|`, `z` is
`Y₀`-complete and therefore `Y`-complete, and there is a path as in the claim."*

Given the wheel in the required set, deleting `z` gives the path. The two complete
rim edges at `z` are removed, and 2.3 makes the remaining positive edge count even.
Minimality of `A` is not needed for this step. -/
theorem path_in_minimal_A_of_inductive_wheel (G : SimpleGraph V) (hG : Berge G) (z : V) (A₀ : Set V)
    (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2) (Y : Set V) (y : V)
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hx0 : VertexComplete G (x 0) (Y \ {y}))
    (hx1 : VertexComplete G (x 1) (Y \ {y}))
    (hcon : VertexComplete G z (Y \ {y}) ∧
      ∃ C : List V, IsWheel G C (Y \ {y}) ∧
        x 0 ∈ C ∧ x 1 ∈ C ∧ z ∈ C ∧
        {v : V | v ∈ C} ⊆ ({x 0, x 1, z} : Set V) ∪ A) :
    ∃ P : List V, IsPathFrom G P (x 0) (x 1) ∧
      (∀ w ∈ SPGT.interior P, w ∈ A) ∧
      2 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧
        EdgeComplete G (Y \ {y}) u v}.ncard := by
  obtain ⟨hz, C, hC, hx0C, hx1C, hzC, hsub⟩ := hcon
  have hne : x 0 ≠ x 1 := by
    intro he
    have := hws.2.1 0 (by omega) 1 (by omega) he
    omega
  exact Thm192Claim2RimPath.path_of_local_wheel hG hC hzC hx0C hx1C hne
    (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega))
    hz hx0 hx1 hsub (fun v hv => wheelSystemA_no_z v (hA.1 hv))

end Workspace.ProofLemmas.Thm192Claim2Gap
