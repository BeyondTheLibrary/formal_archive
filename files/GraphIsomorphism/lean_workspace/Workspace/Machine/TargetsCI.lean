import Workspace.Machine.Targets
import Workspace.Luks.CosetToString

/-! # The Coset Intersection target -/

namespace RAM.Targets

/-- The two generator lists and two representatives. The paper's right cosets
`Gσ` and `Hτ` are Lean's left translates `σ * G` and `τ * H`.
All permutations are encoded by their lists of images, as for String Isomorphism. -/
abbrev CIInput (n : ℕ) :=
  List (Equiv.Perm (Fin n)) × List (Equiv.Perm (Fin n)) ×
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

/-- Whether the two cosets in the input have a common permutation. -/
def CIYes {n : ℕ} (a : CIInput n) : Prop :=
  (Babai.CosetToString.coset (genGroup a.1) a.2.2.1 ∩
    Babai.CosetToString.coset (genGroup a.2.1) a.2.2.2).Nonempty

/-- **Corollary 1.1.2, Sec. 1.1, CI part.** The paper cites Luks [Lu82, Lu93]
for the polynomial equivalence with SI. `Babai.CosetToString.decision` proves
the mathematical reduction. `RAM.CIReduction.corollary_1_1_2_CI_of_workspaceRoutine`
proves this target from the SI workspace routine in `Machine/CIFinal.lean`.
This definition is a target proposition and introduces no axiom. -/
def Corollary_1_1_2_CI_statement : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ ∀ n : ℕ,
    ∃ f : CIInput n → Bool,
      (∀ a, f a = true ↔ CIYes a) ∧ ComputesInTime P f T

end RAM.Targets
