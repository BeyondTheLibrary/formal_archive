import Workspace.Machine.Bridge
import Workspace.Machine.Targets

/-!
# The final obligation of the algorithmic layer

*Status (2026-09-23).* The obligation stated here is proved: `Algo.siWorkspaceRoutine`
(`Workspace/Algo/TopMasterClose.lean`), which gives `Algo.theorem_1_1_1`. The text below is the
original statement of what had to be built.

`RAM.Targets.Theorem_1_1_1_statement` asks for one program and one quasipolynomial bound solving
`RAM.Targets.SIRel n s` for every `n` and every `s`.  The machine layer can now reduce that to a
single statement about *one* routine of the workspace convention.  This file states the
reduction, so that the algorithmic layer knows exactly what it has to build.

What has to be built is `RAM.SIWorkspaceRoutine`: one program `P`, one quasipolynomial step
bound `T` and one polynomial size bound `S` such that, for every `n` and every `s`, `P` started
in the workspace convention on an input of String Isomorphism halts cleanly with an answer that
is both admissible and of size at most `S` of the input size.

Two points about the shape of that statement.

* The size bound sits **inside** the relation.  It is a bound on the answer the routine returns,
  not on every admissible answer.  Every admissible answer is *not* small: an answer carries a
  list of generators of `Aut_G(x)`, and any generating list is admissible, so admissible lists
  can be arbitrarily long.  See the section "Only the answer that is returned has to be small"
  of `Workspace/Machine/Bridge.lean`.
* The bound must hold for **one** pair `T`, `S` for the whole family, since
  `RAM.Targets.Theorem_1_1_1_statement` quantifies over `n` and `s` inside the bound.

## Main results

* `RAM.SIWorkspaceRoutine`, the obligation;
* `RAM.theorem_1_1_1_of_workspaceRoutine`: the obligation gives `Theorem_1_1_1_statement`.
-/

namespace RAM

open Targets

/-- **The obligation of the algorithmic layer.**  One clean routine of the workspace convention
which solves String Isomorphism for every domain size and every alphabet size, within one
quasipolynomial step bound, returning an answer of polynomially bounded size. -/
def SIWorkspaceRoutine : Prop :=
  ∃ (P : Program) (T S : ℕ → ℕ), QuasiPolyBound T ∧ PolyBound S ∧
    (∀ n n' : ℕ, n ≤ n' → S n ≤ S n') ∧
    ∀ n s : ℕ, CleanSolveAt 16 P
      (fun (a : SIInput n s) (b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))) =>
        SIRel n s a b ∧ Enc.size b ≤ S (Enc.size a)) T

/-- **Theorem 1.1.1 follows from one workspace routine.**  The bridge frames that routine by
`up` and `down`, which costs two linear passes, so one program and one quasipolynomial bound
serve the whole family. -/
theorem theorem_1_1_1_of_workspaceRoutine (h : SIWorkspaceRoutine) :
    Theorem_1_1_1_statement := by
  obtain ⟨P, T, S, hT, hSb, hSmono, hP⟩ := h
  obtain ⟨Q, T', hT', hQ⟩ :=
    quasiPolyTimeRel_uniform_small (ι := ℕ × ℕ) (A := fun p => SIInput p.1 p.2)
      (B := fun p => Option (List (Equiv.Perm (Fin p.1)) × Equiv.Perm (Fin p.1)))
      (R := fun p => SIRel p.1 p.2) (P := P) (T := T) (S := S) hT hSb hSmono
      (fun p => hP p.1 p.2)
  exact ⟨Q, T', hT', fun n s => hQ (n, s)⟩

end RAM
