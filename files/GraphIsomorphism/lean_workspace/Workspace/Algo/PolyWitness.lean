/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Machine-layer helpers: one monotone polynomial witness for a routine.
-/
import Workspace.Machine.PolyFun
import Workspace.Machine.Compose

/-!
# One monotone witness for a polynomial routine

`RAM.PolyFun f` gives a time bound and a size bound, each with its own constants. The cost
proofs of Corollary 1.1.3 and of the procedures of §13 need one monotone function
`pw c d m = c (m + 1)^d` that bounds both.
-/

namespace Algo
open RAM

/-- A polynomial routine with one monotone witness for its time and for its output size. -/
theorem polyFun_witness {α β : Type*} [Enc α] [Enc β] {f : α → β} (h : PolyFun f) :
    ∃ (Pf : Program) (c d : ℕ), CleanComputeAt 16 Pf f (fun m => c * (m + 1) ^ d) ∧
      ∀ a, Enc.size (f a) ≤ c * (Enc.size a + 1) ^ d := by
  obtain ⟨Pf, T, ⟨c₁, d₁, hT⟩, hPf⟩ := h.time
  obtain ⟨c₂, d₂, hS⟩ := h.size
  have hmono : ∀ m, c₁ * (m + 1) ^ d₁ + c₂ * (m + 1) ^ d₂ ≤ (c₁ + c₂) * (m + 1) ^ (d₁ + d₂) := by
    intro m
    have h1 : (m + 1) ^ d₁ ≤ (m + 1) ^ (d₁ + d₂) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (m + 1) ^ d₂ ≤ (m + 1) ^ (d₁ + d₂) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
  refine ⟨Pf, c₁ + c₂, d₁ + d₂, hPf.mono (fun m => ?_), fun a => ?_⟩
  · exact le_trans (hT m) (le_trans (Nat.le_add_right _ _) (hmono m))
  · exact le_trans (hS a) (le_trans (Nat.le_add_left _ _) (hmono _))

/-- The polynomial witness form. -/
def pw (c d m : ℕ) : ℕ := c * (m + 1) ^ d

theorem pw_mono (c d : ℕ) : Monotone (pw c d) := fun _ _ h => polyBound_witness_mono c d h

theorem polyBound_pw (c d : ℕ) : PolyBound (pw c d) := polyBound_witness c d

theorem one_le_size {α : Type*} [Enc α] (a : α) : 1 ≤ Enc.size a := by
  have := length_lt_listSize (Enc.encode a)
  change 1 ≤ listSize (Enc.encode a)
  omega


end Algo
