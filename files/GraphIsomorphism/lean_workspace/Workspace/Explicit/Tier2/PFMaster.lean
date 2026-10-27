/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the polynomial
routines around the top loop with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFLists2
import Workspace.Algo.TopMasterAdmission
import Workspace.Explicit.Interface

/-!
# The routines of the fields `kP dP` with explicit constants

The `Explicit.PF` forms of `Algo.polyFun_masterDegree`, `Algo.polyFun_masterWindowSize`,
`Algo.polyFun_masterParameter` and of the read-off `x.2.2.join` of `Explicit.StepBounds`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- `Algo.polyFun_masterDegree`. -/
theorem pf_masterDegree : PF masterDegree 101 2 16 1 := by
  have h := (((((PF.fst (α := RawWinSI) (β := Option RawMasterHint)).comp PF.snd).comp
    PF.snd).comp PF.snd).comp PF.fst).comp pf_length
  exact h

/-- `Algo.polyFun_masterWindowSize`. -/
theorem pf_masterWindowSize : PF masterWindowSize 95 2 13 1 := by
  have h := ((PF.fst (α := RawWinSI) (β := Option RawMasterHint)).comp PF.fst).comp pf_length
  exact h

/-- `Algo.polyFun_masterParameter`. -/
theorem pf_masterParameter : PF masterParameter 124 2 22 1 := by
  have hbody := (((PF.fst (α := RawMasterHint) (β := RawMasterSI)).comp PF.fst).comp
    PF.fst).comp pf_length
  have hg := ((PF.const (α := RawMasterSI) (2 : ℕ)).pair pf_masterWindowSize).comp pf_mul
  have h := ((PF.snd (α := RawWinSI) (β := Option RawMasterHint)).pair PF.id).comp
    (PF.optionElim hg hbody)
  exact h.of_eq (fun p => by obtain ⟨W, o⟩ := p; cases o <;> rfl)

/-- The read-off of `Explicit.StepBounds`: the answer `x.2.2.join` of a final state. -/
theorem pf_readOff : PF (fun x : ℕ × EvalStateE => x.2.2.join) 29 1 9 1 := by
  have h := ((PF.snd (α := ℕ) (β := EvalStateE)).comp PF.snd).comp pf_join
  exact h

end Explicit
