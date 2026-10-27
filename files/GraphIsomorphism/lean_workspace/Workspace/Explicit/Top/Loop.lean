/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the bounded loop
with a per-iteration precondition. Not part of the faithful formalization.
-/
import Workspace.Machine.Iterate

/-!
# The bounded loop, pointwise

`RAM.runsTo_iterateAt` runs `whileNz (K + 2) Q` for `N` rounds when `Q` is a clean routine for
`(k, s) ↦ (k - 1, step s)` on *every* input. The DFS step of the Master has an explicit cost only
on the states a run passes through (the invariant `Explicit.StepBounds.Inv`), so here `Q` is
asked to run only on the states of the orbit, each within `B` steps. The proof is the proof of
`RAM.runsTo_iterateAt`.

* `Explicit.runsTo_iterateAt_pw`;
* `Explicit.runsTo_recursion_pw`: set-up, loop, read-off, with the times added.
-/

namespace Explicit

open RAM

variable {α β σ : Type*}

/-- **The loop, pointwise.** If, at every round `j < N` of the orbit of `s₀`, `Q` takes
`(N - j, step^[j] s₀)` to `(N - j - 1, step^[j+1] s₀)` cleanly within `B` steps, then
`whileNz (K + 2) Q` iterates `step` exactly `N` times within `N * (B + 2) + 1` steps. -/
theorem runsTo_iterateAt_pw [Enc σ] {K : ℕ} {Q : Program} {step : σ → σ}
    (N : ℕ) (s₀ : σ) (B : ℕ)
    (hQ : ∀ j < N, RunsTo Q
      (fun m => m = initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)))
      (fun m' => m' = initMemAt K
        (Enc.encode (((N - j) - 1, step (step^[j] s₀)) : ℕ × σ))) B)
    (hwf : Wf Q) :
    RunsTo (whileNz (K + 2) Q) (fun m => m = initMemAt K (Enc.encode ((N, s₀) : ℕ × σ)))
      (fun m' => m' = initMemAt K (Enc.encode ((0, step^[N] s₀) : ℕ × σ))) (N * (B + 2) + 1) := by
  set inv : Mem → Prop :=
    fun m => ∃ j ≤ N, m = initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hinv
  have hbody : ∀ n : ℕ, RunsTo Q (fun m => inv m ∧ m (K + 2) ≠ 0 ∧ m (K + 2) = n)
      (fun m' => inv m' ∧ m' (K + 2) < n) B := by
    intro n
    refine ⟨hwf, fun m hm => ?_⟩
    obtain ⟨⟨j, hjN, rfl⟩, hne, hμ⟩ := hm
    rw [initMemAt_prod_counter] at hne hμ
    have hj : j < N := by omega
    obtain ⟨k, hk, hhalt, hmem⟩ := (hQ j hj).spec _ rfl
    refine ⟨k, hk, hhalt, ?_⟩
    rw [hmem]
    have key : ((N - j - 1, step (step^[j] s₀)) : ℕ × σ)
        = ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) := by
      have h1 : N - j - 1 = N - (j + 1) := by omega
      simp [h1, Function.iterate_succ_apply']
    rw [key]
    exact ⟨⟨j + 1, by omega, rfl⟩, by rw [initMemAt_prod_counter]; omega⟩
  have hN : ∀ m, inv m → m (K + 2) ≤ N := by
    rintro m ⟨j, hjN, rfl⟩
    rw [initMemAt_prod_counter]
    omega
  refine ((runsTo_whileNz (μ := fun m => m (K + 2)) hbody hN).conseq ?_ ?_ (le_refl _))
  · rintro m rfl
    exact ⟨0, Nat.zero_le _, by simp⟩
  · rintro m' ⟨⟨j, hjN, rfl⟩, hz⟩
    rw [initMemAt_prod_counter] at hz
    have hjeq : j = N := by omega
    subst hjeq
    rw [Nat.sub_self]

/-- **Set-up, loop, read-off, pointwise.** On the input `a`: the set-up `P₁` computes
`(N, s₀) = setUp a` within `t₁`, the loop runs `N` rounds of `Q` within `B` each, and `P₃`
reads the answer off `(0, step^[N] s₀)` within `t₃`. -/
theorem runsTo_recursion_pw [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} (a : α) {t₁ B t₃ : ℕ}
    (h₁ : RunsTo P₁ (fun m => m = initMemAt K (Enc.encode a))
      (fun m' => m' = initMemAt K (Enc.encode (setUp a))) t₁)
    (hQ : ∀ j < (setUp a).1, RunsTo Q
      (fun m => m = initMemAt K
        (Enc.encode (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)))
      (fun m' => m' = initMemAt K
        (Enc.encode ((((setUp a).1 - j) - 1, step (step^[j] (setUp a).2)) : ℕ × σ))) B)
    (hwf : Wf Q)
    (h₃ : RunsTo P₃
      (fun m => m = initMemAt K
        (Enc.encode ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)))
      (fun m' => m' = initMemAt K (Enc.encode (readOff (step^[(setUp a).1] (setUp a).2)))) t₃) :
    RunsTo (seq P₁ (seq (whileNz (K + 2) Q) P₃)) (fun m => m = initMemAt K (Enc.encode a))
      (fun m' => m' = initMemAt K (Enc.encode (readOff (step^[(setUp a).1] (setUp a).2))))
      (t₁ + ((setUp a).1 * (B + 2) + 1 + t₃)) := by
  have hloop := runsTo_iterateAt_pw (K := K) (step := step) (setUp a).1 (setUp a).2 B hQ hwf
  have h1 : RunsTo P₁ (fun m => m = initMemAt K (Enc.encode a))
      (fun m' => m' = initMemAt K (Enc.encode (((setUp a).1, (setUp a).2) : ℕ × σ))) t₁ := by
    simpa using h₁
  exact h1.seq (hloop.seq h₃)

end Explicit
