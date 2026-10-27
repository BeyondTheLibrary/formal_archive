import Workspace.Master.CosetForms

/-! # Alignment and sequential composition

These equalities are equalities of reduction trees. They let a phase stay in
coset form until the whole round is aligned, as in Remark 11.1.4.
-/

universe u v w w' w''

namespace Babai

open scoped Pointwise

namespace SIReduction

variable {Ω : Type u} {A : Type v} {α : Type w} {β : Type w'} {γ : Type w''}

theorem bind_assoc (R : SIReduction Ω A α) (f : α → SIReduction Ω A β)
    (g : β → SIReduction Ω A γ) :
    (R.bind f).bind g = R.bind (fun a => (f a).bind g) := by
  induction R with
  | done a => rfl
  | call I k ih => exact congrArg (SIReduction.call I) (funext ih)

/-- Aligning a composite aligns its phases in the same order. -/
theorem alignCalls_bind (R : SIReduction Ω A α) (f : α → SIReduction Ω A β) :
    (R.bind f).alignCalls = R.alignCalls.bind (fun a => (f a).alignCalls) := by
  induction R with
  | done a => rfl
  | call I k ih =>
    exact congrArg (SIReduction.call (alignInst I))
      (funext fun a => ih ((cosetRepOf I.K) • a))

/-- The shift of the final value is made after all phases. -/
theorem alignRed_bind (I : SIInstance Ω A) (R : SIReduction Ω A α)
    (f : α → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    alignRed I (R.bind f) = R.alignCalls.bind (fun a => alignRed I (f a)) := by
  rw [alignRed, alignCalls_bind, bind_assoc]
  rfl

end SIReduction

end Babai
