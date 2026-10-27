import Workspace.Machine.Small

/-!
# Packaging a binary routine whose cost depends on its input

`RAM.Small.cleanCompute_binary` (`Workspace/Machine/Small.lean`) packages a routine on
`ℕ × ℕ` as a clean routine of the top-level convention, but it takes a **constant** step
bound `T`.  That is enough for `+`, `-`, `min`, `max`, `≤`, whose routines are straight-line
blocks, and it is not enough for multiplication and division: their cost is
`O((Nat.size b) ^ 2)`, which depends on the input.

This file states the same lemma with a step bound `T a b` depending on the two arguments,
together with a bound `T a b + 10 ≤ U (Enc.size (a, b))` turning it into a bound in the input
size, which is the form `RAM.CleanCompute` asks for.  The proof is the proof of
`RAM.Small.cleanCompute_binary` with that one change; nothing else differs.

The bound is always available, because `Nat.size a + 2 ≤ Enc.size (a, b)` and
`Nat.size b + 2 ≤ Enc.size (a, b)` (`RAM.size_fst_nat`, `RAM.size_snd_nat` in
`Workspace/Machine/PolyFun.lean`).

## Main results

* `RAM.Small.cleanCompute_binary_var`.
-/

namespace RAM
namespace Small

/-- **A binary routine on `ℕ × ℕ` whose running time depends on its arguments.**  `R` is run on
the input registers `2` and `4`, leaves its answer in register `5` and writes only inside the
scratch block; it may take `T a b` steps.  The packaged program is clean and runs within
`U (Enc.size (a, b))` steps. -/
theorem cleanCompute_binary_var {β : Type*} [Enc β] {R : Program} {f : ℕ × ℕ → β}
    {v : ℕ → ℕ → ℕ} {T : ℕ → ℕ → ℕ} {U : ℕ → ℕ} {S : List ℕ}
    (hv : ∀ p : ℕ × ℕ, Enc.encode (f p) = [v p.1 p.2])
    (hR : ∀ m₀ : Mem, RunsTo R (fun m => m = m₀)
      (fun m' => m' 5 = v (m₀ 2) (m₀ 4) ∧ Outside S m₀ m') (T (m₀ 2) (m₀ 4)))
    (hS : ∀ i ∈ S, i ∈ scratch)
    (hU : ∀ a b : ℕ, T a b + 10 ≤ U (Enc.size ((a, b) : ℕ × ℕ))) :
    CleanCompute (seq R (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch)))) f U := by
  intro p
  obtain ⟨a, b⟩ := p
  have hmem : initMem (Enc.encode ((a, b) : ℕ × ℕ)) = initMem [1, a, 1, b] := rfl
  rw [hmem]
  set m₀ : Mem := initMem [1, a, 1, b] with hdef
  have e2 : m₀ 2 = a := by simp [hdef, initMem]
  have e4 : m₀ 4 = b := by simp [hdef, initMem]
  have ehigh : ∀ z, 5 ≤ z → m₀ z = 0 := by
    intro z hz
    simp only [hdef, initMem, if_neg (by omega : z ≠ 0)]
    rw [List.getD_eq_default _ _ (by simp; omega)]
  refine RunsTo.mono (T := T a b + (1 + (1 + scratch.length))) ?_ (by
    simpa [scratch] using hU a b)
  refine RunsTo.seq (mid := fun m => m 5 = v a b ∧ Outside S m₀ m) ?_ ?_
  · have h := hR m₀
    rw [e2, e4] at h
    exact h
  · refine runsTo_of_pointwise (fun m₁ => ?_)
    refine RunsTo.seq (mid := fun m => m = m₁.update 1 (m₁ 5) ∧ (m₁ 5 = v a b ∧ Outside S m₀ m₁))
      (runsTo_copyTo 1 5 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine RunsTo.seq (mid := fun m => m = (m₁.update 1 (m₁ 5)).update 0 1 ∧
        (m₁ 5 = v a b ∧ Outside S m₀ m₁))
      (runsTo_assign 0 1 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine (runsTo_clearRegs_const scratch ((m₁.update 1 (m₁ 5)).update 0 1)
      (m₁ 5 = v a b ∧ Outside S m₀ m₁)).weaken (fun m' hm' => ?_)
    obtain ⟨⟨hzero, hrest⟩, hval, hout⟩ := hm'
    rw [hv (a, b)]
    refine eq_initMem_singleton ?_ ?_ ?_
    · rw [hrest 0 (by simp [mem_scratch_iff]), Mem.update_self]
    · rw [hrest 1 (by simp [mem_scratch_iff]),
        Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 0), Mem.update_self, hval]
    · intro z hz
      by_cases hzs : z ∈ scratch
      · exact hzero z hzs
      · have hz10 : 10 ≤ z := by
          rw [mem_scratch_iff] at hzs
          omega
        rw [hrest z hzs, Mem.update_of_ne _ _ (by omega : z ≠ 0),
          Mem.update_of_ne _ _ (by omega : z ≠ 1),
          hout z (fun hzS => hzs (hS z hzS)), ehigh z (by omega)]

end Small
end RAM
