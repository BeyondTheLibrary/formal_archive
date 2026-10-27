/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the numerals `kP dP`
in the final theorem. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.CapsAssembly
import Workspace.Explicit.Tier2.PFEntry

/-!
# Tier 2: the numerals `kP dP` in the final theorem

The polynomial routines around the loop of `Explicit.StepBounds` (the entry
`masterRoot ∘ rawNormSI`, `ground = masterDegree`, the test `masterInputCheck 4096 4` and the
read-off) all run within `2^{kPX} (N+1)^{dPX}` steps, with `kPX = 208752199` and
`dPX = 3686480` (`Explicit.pf_entry`, `Explicit.pf_masterDegree`,
`Explicit.pf_masterInputCheckX`, `Explicit.pf_readOff`). The entry dominates; its constants
come from the Schreier–Sims table of `Algo.rawShorten` (`Explicit.pf_rawBuildTable`).
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- The explicit time constant of the polynomial routines of `Explicit.StepBounds`. -/
def kPX : ℕ := 208752199

/-- The explicit time degree of the polynomial routines of `Explicit.StepBounds`. -/
def dPX : ℕ := 3686480

/-- **Step bounds with the numerals `kP dP`**: at `a = 4096`, `b = 4`, a set of step bounds whose
well-formedness test is `Algo.masterInputCheck p.a p.b` gets `kP = kPX`, `dP = dPX`; the other
fields are unchanged. -/
def StepBounds.withPoly {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (sb : StepBounds p cam) (hW : sb.cost.wfCheck = masterInputCheck p.a p.b)
    (ha : p.a = capAX) (hb : p.b = capBX) : StepBounds p cam :=
  { sb with
    kP := kPX, dP := dPX
    entry := (pf_entry.mono (k' := kPX) (d' := dPX) (s' := kPX) (e' := dPX) (by decide)
      (by decide) (by decide) (by decide)).time
    entry_size := (pf_entry.mono (k' := kPX) (d' := dPX) (s' := kPX) (e' := dPX) (by decide)
      (by decide) (by decide) (by decide)).size
    ground := (pf_masterDegree.mono (k' := kPX) (d' := dPX) (s' := 16) (e' := 1) (by decide)
      (by decide) le_rfl le_rfl).time
    wfCheck := by
      rw [hW, ha, hb]
      exact (pf_masterInputCheckX.mono (k' := kPX) (d' := dPX) (s' := 2) (e' := 0) (by decide)
        (by decide) le_rfl le_rfl).time
    readOff := (pf_readOff.mono (k' := kPX) (d' := dPX) (s' := 9) (e' := 1) (by decide)
      (by decide) le_rfl le_rfl).time }

/-- **Theorem 1.1.1 with exponent 5, with the numerals `kB dB kM dM kP dP`**, at the numeral caps
and the explicit line-1 thresholds, from the bounds of route 5 at every parameter set of
`Explicit.exists_paramsOKX_caps`: one RAM program solves String Isomorphism within
`2^{cFinal sb · (log₂ N + 2)^5}` steps, where `sb` are step bounds with `kB = 15`, `dB = 4`,
`kM = 6`, `dM = 3`, `Aw = 6`, `kP = 208752199`, `dP = 3686480`. -/
theorem theorem_1_1_1_exponent5_of_route5_poly
    (H : ∀ p : Params, ParamsOKX p → p.a = capAX → p.b = capBX → p.B = line1BX →
      p.C₀ = line1C₀X → p.t = 3 → p.tt = 3 → SbipExact p.tt p.dd → SbipExact p.t p.d →
      Route5Bounds p) :
    ∃ (p : Params) (sb : StepBounds p masterCameron), p.a = capAX ∧ p.b = capBX ∧
      p.B = line1BX ∧ p.C₀ = line1C₀X ∧
      sb.kB = 15 ∧ sb.dB = 4 ∧ sb.kM = 6 ∧ sb.dM = 3 ∧ sb.Aw = 6 ∧
      sb.kP = kPX ∧ sb.dP = dPX ∧
      Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨p, ok, ha, hb, hB, hC, h3, htt, he4, he5⟩ := exists_paramsOKX_caps
  obtain ⟨R5, J5, K5, h5, s5, hR5⟩ := H p ok ha hb hB hC h3 htt he4 he5
  obtain ⟨sb, hsB, hsM, hsW, hAw⟩ := exists_stepBounds_route5X ok he4 he5 masterCameron_spec.1
    masterCameron_spec.2 (by omega) h5 s5 hR5
  let sb' := (sb.withCaps hsB hsM ha hb).withPoly hsW ha hb
  exact ⟨p, sb', ha, hb, hB, hC, rfl, rfl, rfl, rfl, hAw, rfl, rfl,
    theorem_1_1_1_exponent5_numeral_of_bounds ok sb'⟩

end Explicit
