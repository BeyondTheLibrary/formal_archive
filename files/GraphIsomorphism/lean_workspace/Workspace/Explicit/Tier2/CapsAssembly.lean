import Workspace.Explicit.AssemblyInv
import Workspace.Explicit.Tier2.Caps

/-!
# Tier 2: the numeral caps in the final theorem

The parameters `a b` of `Algo.masterInputCap` are set to the numerals `capAX = 4096`,
`capBX = 4` (`Explicit.cap_X` gives `ParamsOK.cap` there), and the step bounds get the numerals
`kB = 15`, `dB = 4`, `kM = 6`, `dM = 3` (`Explicit.masterInputCap_le_X`,
`Explicit.masterMeasureBound_le_X`). No other parameter depends on `a b`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- **Parameters at the numeral caps** `a = 4096`, `b = 4` and the explicit line-1 thresholds
`B = 25`, `C₀ = (max 64 25!)! + 1`, with the other parameters of
`Explicit.exists_paramsOKX_exact`. -/
theorem exists_paramsOKX_caps : ∃ p : Params, ParamsOKX p ∧ p.a = capAX ∧ p.b = capBX ∧
    p.B = line1BX ∧ p.C₀ = line1C₀X ∧ p.t = 3 ∧ p.tt = 3 ∧ SbipExact p.tt p.dd ∧
    SbipExact p.t p.d := by
  obtain ⟨p, ok, hB, hC, h3, htt, he4, he5⟩ := exists_paramsOKX_exact
  refine ⟨{ p with a := capAX, b := capBX }, ⟨ok.line1, ?_⟩, rfl, rfl, hB, hC, h3, htt, he4,
    he5⟩
  have r := ok.rest
  exact
    { line1 := r.line1, topwp := r.topwp, top4w := r.top4w, l57 := r.l57, cap := cap_X,
      l4c := r.l4c, l57entry := r.l57entry, l57bip := r.l57bip, phases := r.phases,
      reserve := r.reserve }

/-- **Step bounds with the numeral caps**: at `a = 4096`, `b = 4`, a set of step bounds whose
bounds on instances and on the measure are `Algo.masterInputCap p.a p.b` and
`Algo.masterMeasureBound` gets `kB = 15`, `dB = 4`, `kM = 6`, `dM = 3`; the other fields are
unchanged. -/
def StepBounds.withCaps {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (sb : StepBounds p cam) (hB : sb.cost.bound = masterInputCap p.a p.b)
    (hM : sb.cost.measureBound = masterMeasureBound) (ha : p.a = capAX) (hb : p.b = capBX) :
    StepBounds p cam :=
  { sb with
    kB := 15, dB := 4
    bound_le := fun n => by rw [hB, ha, hb]; exact masterInputCap_le_X n
    kM := 6, dM := 3
    measure_le := fun n => by rw [hM]; exact masterMeasureBound_le_X n }

/-- **Theorem 1.1.1 with exponent 5, at the numeral caps and the explicit line-1 thresholds**,
from the bounds of route 5 at every parameter set of `Explicit.exists_paramsOKX_caps`: one RAM
program solves String Isomorphism within `2^{cFinal sb · (log₂ N + 2)^5}` steps, where `sb`
are step bounds with `kB = 15`, `dB = 4`, `kM = 6`, `dM = 3`, `Aw = 6`, at parameters with
`a = 4096`, `b = 4`, `B = 25`, `C₀ = (max 64 25!)! + 1`. -/
theorem theorem_1_1_1_exponent5_of_route5_caps
    (H : ∀ p : Params, ParamsOKX p → p.a = capAX → p.b = capBX → p.B = line1BX →
      p.C₀ = line1C₀X → p.t = 3 → p.tt = 3 → SbipExact p.tt p.dd → SbipExact p.t p.d →
      Route5Bounds p) :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.a = capAX ∧ p.b = capBX ∧
      p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      sb.kB = 15 ∧ sb.dB = 4 ∧ sb.kM = 6 ∧ sb.dM = 3 ∧ sb.Aw = 6 ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨p, ok, ha, hb, hB, hC, h3, htt, he4, he5⟩ := exists_paramsOKX_caps
  obtain ⟨R5, J5, K5, h5, s5, hR5⟩ := H p ok ha hb hB hC h3 htt he4 he5
  obtain ⟨sb, hsB, hsM, -, hAw⟩ := exists_stepBounds_route5X ok he4 he5 masterCameron_spec.1
    masterCameron_spec.2 (by omega) h5 s5 hR5
  let sb' := sb.withCaps hsB hsM ha hb
  exact ⟨p, sb', ha, hb, hB, hC, rfl, rfl, rfl, rfl, hAw,
    theorem_1_1_1_exponent5_numeral_of_bounds ok sb'⟩

end Explicit
