/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the set-up of the
top loop as a two-scale routine. Not part of the faithful formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Explicit.NodeMachine
import Workspace.Explicit.Top.Q5

/-!
# The set-up of the top loop

On a well-formed root `J` the loop starts from `(countE K n, startState J)`, where `n` is the
degree. This file makes that a two-scale routine (`Explicit.TS`) with exponent 5, the
degree read as the size of `J`:

* `Explicit.polyFun_countE`: the step count is a polynomial-time routine
  (as `Algo.Round.polyFun_roundCount`);
* `Explicit.TS.ofCleanComputeAt`: a clean routine with time `2^{A(log₂ N+2)^5}(N+1)^b`;
* `Explicit.ts_setUpE`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

/-- **The step count is a routine** (the proof of `Algo.Round.polyFun_roundCount`). -/
theorem polyFun_countE (K : ℕ) : PolyFun (countE K) := by
  have hL : PolyFun (fun n : ℕ => Nat.log 2 n + 2) :=
    polyFun_log2.add (polyFun_const 2)
  have hpow : PolyFun (fun n : ℕ => (Nat.log 2 n + 2) ^ 5) :=
    hL.pow (polyFun_const 5) (q := fun _ => 5) (fun _ => le_refl _)
      ⟨5, 0, fun _ => by simp⟩
  have hE : PolyFun (fun n : ℕ => K * (Nat.log 2 n + 2) ^ 5) :=
    (polyFun_const K).mul hpow
  have hq : ∀ n : ℕ, K * (Nat.log 2 n + 2) ^ 5 ≤ K * (Enc.size n + 1) ^ 5 :=
    fun n => Nat.mul_le_mul_left K
      (Nat.pow_le_pow_left (by have := Algo.Round.log_succ_le_size n; omega) _)
  have h2E : PolyFun (fun n : ℕ => (2 : ℕ) ^ (K * (Nat.log 2 n + 2) ^ 5)) :=
    (polyFun_const 2).pow hE (q := fun m => K * (m + 1) ^ 5) hq ⟨K, 5, fun _ => le_refl _⟩
  exact ((polyFun_const 3).mul h2E).add (polyFun_const 1)

namespace TS

variable {α β : Type*} [Enc α] [Enc β]

/-- **A clean routine with time `2^{A(log₂ N+2)^5}(N+1)^b`** is two-scale with the size as
degree, once its outputs are bounded. -/
theorem ofCleanComputeAt {f : α → β} {P : Program} {A b : ℕ}
    (h : CleanComputeAt 16 P f (fun N => 2 ^ (A * (Nat.log 2 N + 2) ^ 5) * (N + 1) ^ b))
    (Pre : α → Prop) (hs : ∀ a, Pre a → Enc.size (f a) ≤ tsB A 5 b (Enc.size a) (Enc.size a)) :
    TS f Pre Enc.size A 5 b := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨⟨[], fun i hi => by simp at hi, fun a => (hα.false a).elim⟩, hs⟩
  exact ⟨⟨P, (h (Classical.arbitrary _)).wf, fun a _ => h a⟩, hs⟩

end TS

variable {p : Params} {cam : RawGens × List ℕ → Option RawCameron}

/-- **The set-up of the top loop**: the step count at the degree, and the start state. -/
noncomputable def setUpE (p : Params) (cam : RawGens × List ℕ → Option RawCameron) (K : ℕ)
    (J : RawMasterSI) : ℕ × EvalStateE :=
  (countE K ((masterRoundE p cam).ground J), (masterRoundE p cam).startState J)

/-- The precondition of the set-up: a well-formed good root without hint. -/
def RootPre (p : Params) (cam : RawGens × List ℕ → Option RawCameron) (J : RawMasterSI) :
    Prop :=
  (masterRoundE p cam).WF J ∧ J.2 = none ∧ MasterNodeGood (masterDegree J) J

/-- The fold state of a one-frame stack is no larger than the stack. -/
theorem size_state_le_start (J : RawMasterSI) (st : StateE) :
    Enc.size st ≤ Enc.size ((([(J, 0, st)], none) : EvalStateE)) := by
  have h1 : Enc.size st ≤ Enc.size (((0 : ℕ), st) : ℕ × StateE) := size_snd_le' ((0 : ℕ), st)
  have h2 : Enc.size (((0 : ℕ), st) : ℕ × StateE)
      ≤ Enc.size ((J, 0, st) : RawMasterSI × ℕ × StateE) := size_snd_le' (J, (0 : ℕ), st)
  have h3 : Enc.size ((J, 0, st) : RawMasterSI × ℕ × StateE)
      ≤ Enc.size [((J, 0, st) : RawMasterSI × ℕ × StateE)] :=
    size_mem_le (List.mem_singleton_self _)
  have h4 : Enc.size [((J, 0, st) : RawMasterSI × ℕ × StateE)]
      ≤ Enc.size ((([(J, 0, st)], none) : EvalStateE)) :=
    size_fst_le' ((([(J, 0, st)], none) : EvalStateE))
  exact h1.trans (h2.trans (h3.trans h4))

/-- The fold state of a frame is no larger than the start state. -/
theorem size_init_le_startState (J : RawMasterSI) :
    Enc.size ((masterRoundE p cam).init J) ≤ Enc.size ((masterRoundE p cam).startState J) :=
  size_state_le_start J _

/-- The fold state `init J` of a good root is below the two-scale bound in the size
(`StepBounds.inv_start`, `StepBounds.inv_size`). -/
theorem size_initE_le (sb : StepBounds p cam) (J : RawMasterSI) (hJ : RootPre p cam J) :
    Enc.size ((masterRoundE p cam).init J) ≤ tsB sb.kS 5 0 (Enc.size J) (Enc.size J) := by
  have h1 := sb.inv_size _ _ (sb.inv_start J hJ.1 hJ.2.2)
  have h3 : masterDegree J ≤ Enc.size J := sb.cost.ground_le J
  have h4 : 2 ^ (sb.kS * (Nat.log 2 (masterDegree J) + 2) ^ 5)
      ≤ tsB sb.kS 5 0 (Enc.size J) (Enc.size J) := by
    unfold tsB
    simp only [pow_zero, mul_one]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (lg_pow_mono h3 le_rfl))
  exact (size_init_le_startState J).trans (h1.trans h4)

/-- **The set-up is two-scale**, with exponent 5, on good roots, the size as degree. -/
theorem ts_setUpE (sb : StepBounds p cam) (K : ℕ) :
    ∃ A b, TS (setUpE p cam K) (RootPre p cam) Enc.size A 5 b := by
  obtain ⟨A₁, b₁, h₁⟩ := TS.ofPoly (sb.cost.polyFun_ground.comp (polyFun_countE K))
  obtain ⟨Q, hQw, hQ⟩ := sb.init
  have hinit : TS (masterRoundE p cam).init (RootPre p cam) Enc.size
      (sb.As + sb.kS) 5 sb.ds := by
    refine ⟨⟨Q, hQw, fun J hJ => (hQ J hJ.1 hJ.2.1).mono ?_⟩, fun J hJ => ?_⟩
    · exact (tsB_mono (Nat.le_add_right _ _) le_rfl le_rfl le_rfl le_rfl :
        tsB sb.As 5 sb.ds (Enc.size J) (Enc.size J)
          ≤ tsB (sb.As + sb.kS) 5 sb.ds (Enc.size J) (Enc.size J))
    · exact (size_initE_le sb J hJ).trans
        (tsB_mono (Nat.le_add_left _ _) le_rfl (Nat.zero_le _) le_rfl le_rfl)
  obtain ⟨A₂, b₂, h₂⟩ := TS.id' (α := RawMasterSI) (Pre := RootPre p cam) (D := Enc.size) 5
  have hpairJ := h₂.pair hinit
  have hbuild : PolyFun (fun q : RawMasterSI × StateE =>
      (([(q.1, 0, q.2)], none) : EvalStateE)) :=
    ((polyFun_fst.pair ((polyFun_const 0).pair polyFun_snd)).comp polyFun_singleton).pair
      polyFun_none
  obtain ⟨A₃, b₃, h₃⟩ := TS.ofPoly hbuild
  have hstart := hpairJ.comp0 (h₃ Any Enc.size 0)
  have hset := (h₁ (RootPre p cam) Enc.size 5).pair hstart
  exact ⟨_, _, hset.of_eq fun J => rfl⟩

end Explicit
