/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: correctness of Procedure String-Isomorphism.
-/
import Workspace.Master.Procedure
import Workspace.Luks.Framework

/-!
# Correctness of the Master Algorithm

Procedure String-Isomorphism (Sec. 15) answers the instances one round produces by starting
over.  The recursion terminates because each round makes progress in the sense of
`Babai.MasterStep.decreases`: the window shrinks to `2n/3`, or the Johnson parameter `m` is
at least halved without the window growing.  `Babai.MasterStep.rank_lt`
(`Workspace/Master/Procedure.lean`) turns that into a natural number that strictly drops at
every call, so a recursion depth of `rank I + 1` is enough:

* `Babai.MasterStep.solve_eq_answer` — with enough fuel the procedure returns the true
  answer `Iso^Δ_K(x,y)` of the instance;
* `Babai.MasterStep.solve_eq_strIso` — for a full instance (window `Ω`) this is
  `Iso_G(x,y)`, the output line of Sec. 15.
-/

universe u v w

namespace Babai

variable {Ω : Type u} {A : Type v} {ι : Type w}

namespace MasterStep

variable (M : MasterStep Ω A ι)

/-- §15, **correctness**: `f` levels of recursion return the true answer as soon as `f`
exceeds the measure of the instance.

*Proof.* Induction on `f`.  There is nothing to prove for `f = 0`, since `rank I < 0` is
impossible.  For `f + 1`, every instance `J` the round asks under the true oracle has
`rank J < rank I ≤ f` (`Babai.MasterStep.rank_lt`), so by the induction hypothesis the
recursion one level down answers all of them correctly.  Hence the round, run against the
recursion, takes the same path as under the true oracle
(`Babai.SIReduction.callsWith_eq_calls_of_agree`) and returns `(M.step I).run`, which is
`I.answer` by `round_correct`. -/
theorem solve_eq_answer : ∀ (f : ℕ) (i : ι), IsGroupInstance (M.inst i) → M.rank i < f →
    M.solve f i = (M.inst i).answer := by
  intro f
  induction f with
  | zero => intro i _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro i hgrp hI
    have hagree : ∀ J, (∃ hJ : J ∈ (M.step i).calls,
        IsGroupInstance (M.inst (M.lift i J)) ∧ M.rank (M.lift i J) < M.rank i) →
        solveFuel M.step M.lift f (M.lift i J) = J.answer := by
      rintro J ⟨hJ, hJg, hJr⟩
      have := ih (M.lift i J) hJg (show M.rank (M.lift i J) < f by omega)
      rw [show solveFuel M.step M.lift f (M.lift i J) = M.solve f (M.lift i J) from rfl,
        this, M.lift_inst i J hJ]
    obtain ⟨-, hrun⟩ :=
      SIReduction.callsWith_eq_calls_of_agree
        (O := fun J => solveFuel M.step M.lift f (M.lift i J)) hagree (M.step i)
        (fun J hJ => ⟨hJ, by
            rw [M.lift_inst i J hJ]; exact M.calls_isGroupInstance i hgrp J hJ,
          M.rank_lt i hgrp J hJ⟩)
    show (M.step i).runWith (fun J => solveFuel M.step M.lift f (M.lift i J)) =
      (M.inst i).answer
    rw [hrun]
    exact M.round_correct i hgrp

/-- The recursion depth `rank I + 1` always suffices. -/
theorem solve_succ_rank (i : ι) (hi : IsGroupInstance (M.inst i)) :
    M.solve (M.rank i + 1) i = (M.inst i).answer :=
  M.solve_eq_answer _ i hi (Nat.lt_succ_self _)

/-- §15, the **output line**: for the instance with full window `Ω` and no hint, Procedure
String-Isomorphism returns `Iso_G(x,y)`. -/
theorem solve_eq_strIso (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) (f : ℕ)
    (hf : M.rank (M.top ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩) < f) :
    M.solve f (M.top ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩) =
      strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [M.solve_eq_answer f _ (by
      rw [M.inst_top]; exact isGroupInstance_full G x y) hf, M.inst_top]
  exact wIso_univ _ x y

end MasterStep

end Babai
