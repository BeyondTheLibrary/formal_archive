/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the admission test of
the master calls with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PFSize
import Workspace.Explicit.Tier2.PFMaster
import Workspace.Explicit.Tier2.Caps

/-!
# The input check of the master calls, with explicit constants

The `Explicit.PF` forms of `Algo.polyFun_top4aStrBound`, `Algo.polyFun_topcsChainBound`,
`Algo.polyFun_masterInputCap` (at the caps `capAX = 4096`, `capBX = 4` of Tier2/Caps) and
`Algo.polyFun_masterInputCheck`, proved along the same compositions.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- `Algo.polyFun_top4aStrBound`: `strBound m = 1 + m (2 (m + 2) + 1)`. -/
theorem pf_strBound : PF strBound 61 2 26 1 := by
  have h1 := ((PF.id (α := ℕ)).pair (PF.const (α := ℕ) (2 : ℕ))).comp pf_add
  have h2 := ((PF.const (α := ℕ) (2 : ℕ)).pair h1).comp pf_mul
  have h3 := (h2.pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h4 := ((PF.id (α := ℕ)).pair h3).comp pf_mul
  have h := ((PF.const (α := ℕ) (1 : ℕ)).pair h4).comp pf_add
  exact h.of_eq (fun m => rfl)

/-- `gensBound m = 1 + m m (2 strBound m + 1)` (as in `Algo.polyFun_topcsChainBound`). -/
theorem pf_gensBound : PF gensBound 101 2 44 1 := by
  have h1 := ((PF.const (α := ℕ) (2 : ℕ)).pair pf_strBound).comp pf_mul
  have h2 := (h1.pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h3 := ((PF.id (α := ℕ)).pair PF.id).comp pf_mul
  have h4 := (h3.pair h2).comp pf_mul
  have h := ((PF.const (α := ℕ) (1 : ℕ)).pair h4).comp pf_add
  exact h.of_eq (fun m => rfl)

/-- `Algo.polyFun_topcsChainBound`: `chainBound m = 16 (gensBound m + m + 1)`. -/
theorem pf_chainBound : PF chainBound 131 2 57 1 := by
  have h1 := (pf_gensBound.pair PF.id).comp pf_add
  have h2 := (h1.pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h := ((PF.const (α := ℕ) (16 : ℕ)).pair h2).comp pf_mul
  exact h.of_eq (fun m => rfl)

/-- `aggnCheckedWindowBound n = 32 (gensBound n + strBound (2 n + 1) + 1)` (as in
`Algo.polyFun_masterInputCap`). -/
theorem pf_checkedWindowBound : PF aggnCheckedWindowBound 131 2 57 1 := by
  have h1 := (((PF.const (α := ℕ) (2 : ℕ)).pair PF.id).comp pf_mul).pair
    (PF.const (α := ℕ) (1 : ℕ)) |>.comp pf_add
  have h2 := (pf_gensBound.pair (h1.comp pf_strBound)).comp pf_add
  have h3 := (h2.pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h := ((PF.const (α := ℕ) (32 : ℕ)).pair h3).comp pf_mul
  exact h.of_eq (fun m => rfl)

/-- `Algo.polyFun_topcsContextCap` at the caps: `4096 (n + 1)^4`. -/
theorem pf_contextCapX : PF (topcsContextCap capAX capBX) 50 2 22 1 := by
  have h1 := ((PF.id (α := ℕ)).pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h2 := (h1.pair h1).comp pf_mul
  have h3 := (h2.pair h2).comp pf_mul
  have h := ((PF.const (α := ℕ) (4096 : ℕ)).pair h3).comp pf_mul
  exact h.of_eq (fun n => by simp only [topcsContextCap, capAX, capBX]; ring)

/-- `Algo.polyFun_masterInputCap` at the caps `capAX`, `capBX`. -/
theorem pf_masterInputCapX : PF (masterInputCap capAX capBX) 171 2 74 1 := by
  have h1 := (pf_contextCapX.pair pf_checkedWindowBound).comp pf_add
  have h2 := (h1.pair pf_chainBound).comp pf_add
  have h3 := (h2.pair (PF.const (α := ℕ) (1 : ℕ))).comp pf_add
  have h := ((PF.const (α := ℕ) (4 : ℕ)).pair h3).comp pf_mul
  exact h.of_eq (fun n => rfl)

/-- The size of a master input (`Algo.AggnSizeRoutine.polyFun_size` at `RawMasterSI`). -/
theorem pf_sizeMasterSI : PF (Enc.size : RawMasterSI → ℕ) 8556 3 345 1 := by
  have h := PFSize.pf (α := RawMasterSI)
  exact h

/-- `Algo.polyFun_masterInputCheck` at the caps `capAX`, `capBX`. -/
theorem pf_masterInputCheckX : PF (masterInputCheck capAX capBX) 8586 3 2 0 := by
  have c1 := (pf_sizeMasterSI.pair (pf_masterDegree.comp pf_masterInputCapX)).comp pf_le
  have c2 := (pf_masterWindowSize.pair pf_masterDegree).comp pf_le
  have c3 := (pf_masterParameter.pair (((PF.const (α := RawMasterSI) (2 : ℕ)).pair
    pf_masterWindowSize).comp pf_mul)).comp pf_le
  have c12 := PF.ite c1 c2 (PF.const (α := RawMasterSI) false)
  have h := PF.ite c12 c3 (PF.const (α := RawMasterSI) false)
  exact h.of_eq (fun p => by
    simp only [masterInputCheck]
    cases decide (Enc.size p ≤ masterInputCap capAX capBX (masterDegree p)) <;>
      cases decide (masterWindowSize p ≤ masterDegree p) <;> rfl)

end Explicit
