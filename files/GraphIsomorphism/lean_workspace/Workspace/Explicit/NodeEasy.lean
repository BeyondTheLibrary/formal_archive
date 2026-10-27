/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the polynomial fields of
`Explicit.StepBounds`. Not part of the faithful formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Algo.TopMasterRecursion

/-!
# The polynomial fields of `Explicit.StepBounds`

* `Explicit.exists_nodeCost`: the cost datum of the variant round (`Algo.masterNodeH_cost`).
* `Explicit.polyBound_explicit`, `Explicit.polyFun_explicit`: a polynomial bound, and a
  polynomial-time routine, in the form `2^k·(N+1)^d` that `StepBounds` asks for.
* `Explicit.exists_polyFields`: one pair `(kP, dP)` for the entry, its size, `ground`, the
  well-formedness test and the read-off.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- `c ≤ 2^c`. -/
theorem le_two_pow_self (c : ℕ) : c ≤ 2 ^ c := Nat.lt_two_pow_self.le

/-- `2^k·(N+1)^d` is monotone in `k` and `d`. -/
theorem two_pow_mul_le {k k' d d' : ℕ} (hk : k ≤ k') (hd : d ≤ d') (N : ℕ) :
    2 ^ k * (N + 1) ^ d ≤ 2 ^ k' * (N + 1) ^ d' :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk)
    (Nat.pow_le_pow_right (by omega) hd)

/-- **A polynomial bound in the form of `StepBounds`.** -/
theorem polyBound_explicit {T : ℕ → ℕ} (h : PolyBound T) :
    ∃ k d, ∀ n, T n ≤ 2 ^ k * (n + 1) ^ d := by
  obtain ⟨c, d, hc⟩ := h
  exact ⟨c, d, fun n => (hc n).trans (Nat.mul_le_mul_right _ (le_two_pow_self c))⟩

/-- **A polynomial-time routine in the form of `StepBounds`**, time and size. -/
theorem polyFun_explicit {α β : Type*} [Enc α] [Enc β] {f : α → β} (h : PolyFun f) :
    ∃ k d, (∃ Q, CleanComputeAt 16 Q f (fun N => 2 ^ k * (N + 1) ^ d)) ∧
      ∀ a, Enc.size (f a) ≤ 2 ^ k * (Enc.size a + 1) ^ d := by
  obtain ⟨⟨Q, T, hT, hQ⟩, ⟨c, d, hs⟩⟩ := h.time, h.size
  obtain ⟨k₁, d₁, h₁⟩ := polyBound_explicit hT
  refine ⟨k₁ + c, d₁ + d, ⟨Q, hQ.mono fun N => (h₁ N).trans
    (two_pow_mul_le (by omega) (by omega) N)⟩, fun a => (hs a).trans ?_⟩
  exact (Nat.mul_le_mul_right _ (le_two_pow_self c)).trans (two_pow_mul_le (by omega)
    (by omega) _)

/-- **The cost datum of the variant round.** -/
theorem exists_nodeCost (p : Params) {cam : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cam) : Nonempty (MasterOpsCost p.a p.b (masterOpsE p cam)) :=
  masterNodeH_cost p.a p.b hc default ((line4dDomOps_cost (c := 0) (tt := p.tt) (dd := p.dd)
    p.a p.b).some) (quasiFun_line4dDomHint 0 p.tt p.dd)
    (quasiFun_masterL57Hint 2 0 p.t p.d p.dc p.dp p.u' p.v' p.e p.f)

/-- The round's bound on instances and answers is `Algo.masterInputCap`. -/
theorem runCostQ_bound {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (C : MasterOpsCost p.a p.b (masterOpsE p cam)) :
    C.runCostQ.bound = masterInputCap p.a p.b := rfl

/-- The round's bound on the measure is `Algo.masterMeasureBound`. -/
theorem runCostQ_measureBound {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (C : MasterOpsCost p.a p.b (masterOpsE p cam)) :
    C.runCostQ.measureBound = masterMeasureBound := rfl

/-- The round's well-formedness test is `Algo.masterInputCheck`. -/
theorem runCostQ_wfCheck {p : Params} {cam : RawGens × List ℕ → Option RawCameron}
    (C : MasterOpsCost p.a p.b (masterOpsE p cam)) :
    C.runCostQ.wfCheck = masterInputCheck p.a p.b := rfl

/-- **The polynomial fields**: the bounds on instances and on the measure, and one pair
`(kP, dP)` for the entry, its size, `ground`, the well-formedness test and the read-off. -/
theorem exists_polyFields (p : Params) :
    (∃ kB dB, ∀ n, masterInputCap p.a p.b n ≤ 2 ^ kB * (n + 1) ^ dB) ∧
    (∃ kM dM, ∀ n, masterMeasureBound n ≤ 2 ^ kM * (n + 1) ^ dM) ∧
    ∃ kP dP,
      (∃ Q, CleanComputeAt 16 Q (fun I : RawSI => masterRoot (rawNormSI I))
        (fun N => 2 ^ kP * (N + 1) ^ dP)) ∧
      (∀ I : RawSI, Enc.size (masterRoot (rawNormSI I)) ≤ 2 ^ kP * (Enc.size I + 1) ^ dP) ∧
      (∃ Q, CleanComputeAt 16 Q masterDegree (fun N => 2 ^ kP * (N + 1) ^ dP)) ∧
      (∃ Q, CleanComputeAt 16 Q (masterInputCheck p.a p.b) (fun N => 2 ^ kP * (N + 1) ^ dP)) ∧
      (∃ Q, CleanComputeAt 16 Q (fun x : ℕ × EvalStateE => x.2.2.join)
        (fun N => 2 ^ kP * (N + 1) ^ dP)) := by
  refine ⟨polyBound_explicit (polyBound_masterInputCap p.a p.b),
    polyBound_explicit polyBound_masterMeasureBound, ?_⟩
  obtain ⟨k₁, d₁, ⟨Q₁, h₁⟩, hs₁⟩ := polyFun_explicit (polyFun_rawNormSI.comp polyFun_masterRoot)
  obtain ⟨k₂, d₂, ⟨Q₂, h₂⟩, -⟩ := polyFun_explicit polyFun_masterDegree
  obtain ⟨k₃, d₃, ⟨Q₃, h₃⟩, -⟩ := polyFun_explicit (polyFun_masterInputCheck p.a p.b)
  obtain ⟨k₄, d₄, ⟨Q₄, h₄⟩, -⟩ := polyFun_explicit
    ((polyFun_snd.comp polyFun_snd).comp polyFun_join :
      PolyFun (fun x : ℕ × EvalStateE => x.2.2.join))
  refine ⟨k₁ + k₂ + k₃ + k₄, d₁ + d₂ + d₃ + d₄, ⟨Q₁, h₁.mono fun N =>
      two_pow_mul_le (by omega) (by omega) N⟩,
    fun I => (hs₁ I).trans (two_pow_mul_le (by omega) (by omega) _),
    ⟨Q₂, h₂.mono fun N => two_pow_mul_le (by omega) (by omega) N⟩,
    ⟨Q₃, h₃.mono fun N => two_pow_mul_le (by omega) (by omega) N⟩,
    ⟨Q₄, h₄.mono fun N => two_pow_mul_le (by omega) (by omega) N⟩⟩

end Explicit
