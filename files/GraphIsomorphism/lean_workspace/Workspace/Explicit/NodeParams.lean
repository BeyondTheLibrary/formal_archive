/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 1: parameters meeting
their specifications. Not part of the faithful formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Explicit.Sec9Count
import Workspace.Explicit.Sec9Family

/-!
# Parameters of the variant Master that meet `Explicit.ParamsOK`

Tier 1: the fuel exponents of the recursion of Section 9 are fixed, `t = tt = 3`
(`Explicit.sbipRun_count_three`); the thresholds of line 1, the admission caps and the
window caps are the ones `Algo.theorem_1_1_1` chooses; the storage caps `dd d dc dp` and
the reserve exponent `E` are existential.

`E` is the exponent of the reserve `2^{(log₂ m+2)^E}` of the width of the round of lines 5–7
(`Algo.MasterL57EOK`). It bounds the header calls of the round at *every* state of the
aggregate carrier, reachable or not (`Algo.aggnL57Cap` is a supremum over all states), and
it is not bounded by `3` here: see `Explicit/INTERFACE_REQUESTS.md`, R3.
-/

namespace Explicit

open Algo RAM Babai

/-- **Parameters meeting their specifications exist, with `t = tt = 3`.** -/
theorem exists_paramsOK : ∃ p : Params, ParamsOK p ∧ p.t = 3 ∧ p.tt = 3 := by
  obtain ⟨dd, h4⟩ := exists_line4cBounds_three 0
  obtain ⟨d, hbip, hgood⟩ := exists_restoredEntry_good_bip_three 0
  obtain ⟨dc, dp, -, hok⟩ := exists_aggnPhasesOK 2
  obtain ⟨E, hE⟩ := exists_masterL57EOK 2 0 3 d dc dp masterTopE masterTopF
  refine ⟨⟨masterLine1B, masterLine1C₀, masterCapA, masterCapB, masterTopE, masterTopF,
    masterTopU, masterTopV, (l57UV masterTopE masterTopF).1, (l57UV masterTopE masterTopF).2,
    3, dd, 3, d, dc, dp, E⟩, ?_, rfl, rfl⟩
  exact
    { line1 := ⟨rfl, rfl⟩
      topwp := masterTopEF_spec
      top4w := masterTopUV_spec
      l57 := ⟨rfl, rfl⟩
      cap := masterCap_spec
      l4c := h4
      l57entry := hgood 2
      l57bip := hbip
      phases := hok
      reserve := hE }

/-- **Parameters meeting their specifications, with the runs of Section 9 exact**: the caps
`dd` (line 4c) and `d` (lines 5–7) are ones at which `Algo.sbipRun 0 3 _` returns the value of
the recursion on every valid node (`Explicit.SbipExact`), which the counts of versions need
(`Explicit.extendedSplitFamily_length_le`). -/
theorem exists_paramsOK_exact : ∃ p : Params, ParamsOK p ∧ p.t = 3 ∧ p.tt = 3 ∧
    SbipExact p.tt p.dd ∧ SbipExact p.t p.d := by
  obtain ⟨dd, he4⟩ := exists_sbipRun_exact_three 0
  obtain ⟨d, he5⟩ := exists_sbipRun_exact_three 0
  obtain ⟨hbip, hgood⟩ := restoredEntry_good_bip_of_exact he5
  obtain ⟨dc, dp, -, hok⟩ := exists_aggnPhasesOK 2
  obtain ⟨E, hE⟩ := exists_masterL57EOK 2 0 3 d dc dp masterTopE masterTopF
  refine ⟨⟨masterLine1B, masterLine1C₀, masterCapA, masterCapB, masterTopE, masterTopF,
    masterTopU, masterTopV, (l57UV masterTopE masterTopF).1, (l57UV masterTopE masterTopF).2,
    3, dd, 3, d, dc, dp, E⟩, ?_, rfl, rfl, he4, he5⟩
  exact
    { line1 := ⟨rfl, rfl⟩
      topwp := masterTopEF_spec
      top4w := masterTopUV_spec
      l57 := ⟨rfl, rfl⟩
      cap := masterCap_spec
      l4c := line4cBounds_of_exact he4
      l57entry := hgood 2
      l57bip := hbip
      phases := hok
      reserve := hE }

end Explicit
