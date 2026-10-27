/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the entry routine
with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFTable
import Workspace.Explicit.Tier2.PFMasterCheck

/-!
# The entry routine, with explicit constants

The `Explicit.PF` forms of `Algo.polyFun_rawNormSI`, `Algo.polyFun_masterRoot` and of the entry
`masterRoot ∘ rawNormSI` of `Explicit.exists_polyFields`, proved along the same compositions.
-/

set_option synthInstance.maxSize 4096
set_option maxRecDepth 100000

namespace Explicit

open RAM Algo Babai

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- `Algo.polyFun_rawNormSI`. -/
theorem pf_rawNormSI : PF rawNormSI 208752198 3686480 90174 1600 := by
  have hx := (PF.snd (α := RawGens) (β := RawStr × RawStr)).comp PF.fst
  have hy := (PF.snd (α := RawGens) (β := RawStr × RawStr)).comp PF.snd
  have hl := (hx.pair hy).comp pf_append
  have h := ((hx.pair PF.fst).comp pf_tidyGens).pair
    (((hl.pair hx).comp pf_rawRenameStr).pair ((hl.pair hy).comp pf_rawRenameStr))
  exact h.of_eq (fun _ => rfl)

/-- `Algo.polyFun_masterRoot`. -/
theorem pf_masterRoot : PF masterRoot 512 5 40 2 := by
  have hx := (PF.snd (α := RawGens) (β := RawStr × RawStr)).comp PF.fst
  have hy := (PF.snd (α := RawGens) (β := RawStr × RawStr)).comp PF.snd
  have hr := hx.comp pf_rangeLength
  have h := (hr.pair (PF.fst.pair (hr.pair (hx.pair hy)))).pair
    (PF.const (α := RawSI) (none : Option RawMasterHint))
  exact h.of_eq (fun _ => rfl)

/-- The entry of `Explicit.exists_polyFields`: `masterRoot ∘ rawNormSI`. -/
theorem pf_entry : PF (fun I : RawSI => masterRoot (rawNormSI I)) 208752199 3686480 180390 3200 := by
  have h := pf_rawNormSI.comp pf_masterRoot
  exact h

end Explicit
