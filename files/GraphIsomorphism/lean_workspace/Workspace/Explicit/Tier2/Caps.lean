/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: explicit admission caps
and the bounds `kB dB kM dM` of `Explicit.StepBounds` as numerals. Not part of the faithful
formalization.
-/
import Workspace.Explicit.Interface

/-!
# Explicit admission caps

`Explicit.ParamsOK.cap` asks `masterCameronChildBound n ≤ masterInputCap a b n`; the existing
constants `Algo.masterCapA`, `Algo.masterCapB` are chosen by `Classical.choose`. Here:

* `Explicit.capAX = 4096`, `Explicit.capBX = 4`, with `Explicit.cap_X` (the cap field);
* `Explicit.masterInputCap_le_X`: `masterInputCap 4096 4 n ≤ 2^15 (n+1)^4` (`kB = 15`,
  `dB = 4`);
* `Explicit.masterMeasureBound_le_X`: `masterMeasureBound n ≤ 2^6 (n+1)^3` (`kM = 6`,
  `dM = 3`).
-/

namespace Explicit

open RAM Algo

/-- The explicit context cap `a` of the admission test. -/
def capAX : ℕ := 4096

/-- The explicit context exponent `b` of the admission test. -/
def capBX : ℕ := 4

theorem gensBound_le (n : ℕ) : gensBound n ≤ 18 * (n + 1) ^ 4 := by
  unfold gensBound strBound
  ring_nf
  omega

theorem strBound_two_le (n : ℕ) : strBound (2 * n + 1) ≤ 8 * (n + 1) ^ 4 := by
  unfold strBound
  ring_nf
  omega

theorem strBound_le (n : ℕ) : strBound n ≤ 3 * (n + 1) ^ 4 := by
  unfold strBound
  ring_nf
  omega

theorem aggnCheckedWindowBound_le (n : ℕ) : aggnCheckedWindowBound n ≤ 864 * (n + 1) ^ 4 := by
  have h1 := gensBound_le n
  have h2 := strBound_two_le n
  have h3 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold aggnCheckedWindowBound
  omega

theorem chainBound_le (n : ℕ) : chainBound n ≤ 320 * (n + 1) ^ 4 := by
  have h1 := gensBound_le n
  have h3 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold chainBound
  omega

/-- **The cap field of `Explicit.ParamsOK` at the explicit caps.** -/
theorem cap_X (n : ℕ) : masterCameronChildBound n ≤ masterInputCap capAX capBX n := by
  have h1 := aggnCheckedWindowBound_le n
  have h2 := gensBound_le n
  have h3 := strBound_le n
  have h4 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold masterCameronChildBound masterInputCap topcsContextCap capAX capBX
  omega

/-- **`kB = 15`, `dB = 4`.** -/
theorem masterInputCap_le_X (n : ℕ) :
    masterInputCap capAX capBX n ≤ 2 ^ 15 * (n + 1) ^ 4 := by
  have h1 := aggnCheckedWindowBound_le n
  have h2 := chainBound_le n
  have h3 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold masterInputCap topcsContextCap capAX capBX
  norm_num
  omega

/-- **`kM = 6`, `dM = 3`.** -/
theorem masterMeasureBound_le_X (n : ℕ) : masterMeasureBound n ≤ 2 ^ 6 * (n + 1) ^ 3 := by
  unfold masterMeasureBound masterRankWeight masterRankCap
  ring_nf
  omega

end Explicit
