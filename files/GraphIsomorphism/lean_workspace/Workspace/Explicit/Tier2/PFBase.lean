/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the machine
primitives with explicit polynomial time. Not part of the faithful formalization.
-/
import Workspace.Explicit.Tier2.PF
import Workspace.Machine.Build
import Workspace.Machine.Mul

/-!
# The primitives of `Workspace/Machine` with explicit constants

Each lemma is the `Explicit.PF` form of the `RAM.PolyFun` lemma of the same name, with the step
count of the machine lemma it rests on: the list primitives (`rawLength`, `tail`, `uncons`,
`cons`, `some`), the arithmetic on pairs of naturals (`add`, `sub`, `min`, `max`, `le`, `mul`,
`Nat.size`), and the derived `natEq` and `length`.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

namespace PF

/-- A routine of the workspace convention with time `c n + e`. -/
theorem ofLinAt {f : α → β} {P : Program} {T : ℕ → ℕ} (c e : ℕ) {k s' e' : ℕ}
    (h : CleanComputeAt 16 P f T) (hT : ∀ n, T n ≤ c * n + e) (hk : c + e ≤ 2 ^ k)
    (hs : ∀ a, Enc.size (f a) ≤ 2 ^ s' * (Enc.size a + 1) ^ e') : PF f k 1 s' e' := by
  refine ⟨⟨P, h.mono fun N => ?_⟩, hs⟩
  have e1 : (c + e) * (N + 1) = c * N + e + (c + e * N) := by ring
  have h2 : (c + e) * (N + 1) ≤ 2 ^ k * (N + 1) := Nat.mul_le_mul_right _ hk
  have h3 := hT N
  simp only [pow_one]
  omega

end PF

/-! ## Lists and options -/

theorem pf_rawLength : PF (rawLength : α → ℕ) 7 1 0 1 := by
  refine PF.ofLinAt 5 66 (cleanComputeAt_rawLength (K := 16) (by norm_num))
    (fun n => by omega) (by decide)
    (fun a => ?_)
  have h1 : Enc.size (rawLength a) = Nat.size (rawLength a) + 2 := Small.size_nat _
  have h2 : Nat.size (rawLength a) ≤ rawLength a := size_le_self _
  have h3 := rawLength_lt_size a
  norm_num
  omega

theorem pf_tail : PF (List.tail : List α → List α) 7 1 0 1 :=
  PF.ofLinAt 19 79 (cleanComputeAt_tail (K := 16) (by norm_num))
    (fun n => by omega) (by decide)
    (fun l => by have := size_tail_le l; norm_num; omega)

theorem pf_uncons : PF (uncons : List α → Option (α × List α)) 8 1 1 1 :=
  PF.ofLinAt 19 124 (cleanComputeAt_uncons (K := 16) (by norm_num))
    (fun n => by omega) (by decide)
    (fun l => by have := sizeBound_uncons l; norm_num at this ⊢; omega)

theorem pf_cons : PF (fun p : β × List β => p.1 :: p.2) 7 1 0 1 :=
  PF.ofLinAt 19 104 (cleanComputeAt_cons (K := 16) (by norm_num))
    (fun n => by omega) (by decide)
    (fun ⟨x, l⟩ => by
      have := size_cons_le x l
      show Enc.size (x :: l) ≤ 2 ^ 0 * (Enc.size (x, l) + 1) ^ 1
      norm_num
      omega)

theorem pf_some : PF (Option.some : β → Option β) 7 1 1 1 :=
  PF.ofLinAt 19 80 (cleanComputeAt_some (K := 16) (by norm_num))
    (fun n => by omega) (by decide)
    (fun b => by have := size_some_eq b; norm_num; omega)

/-! ## Arithmetic -/

theorem pf_add : PF (fun p : ℕ × ℕ => p.1 + p.2) 7 1 1 1 := by
  refine PF.ofClean Small.cleanCompute_add (fun N => by norm_num; omega) (fun p => ?_)
  have h1 := size_fst_nat p
  have h2 := size_snd_nat p
  set s := max (Nat.size p.1) (Nat.size p.2) with hs
  have hb1 : p.1 < 2 ^ s := lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb2 : p.2 < 2 ^ s := lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have : p.1 + p.2 < 2 ^ (s + 1) := by rw [pow_succ]; omega
  have := Nat.size_le.2 this
  have h4 : Enc.size (p.1 + p.2) = Nat.size (p.1 + p.2) + 2 := Small.size_nat _
  norm_num
  omega

/-- A binary operation whose value is at most one of its arguments is no larger than its
input. -/
theorem size_binop_le {f : ℕ × ℕ → ℕ} (h : ∀ p : ℕ × ℕ, f p ≤ max p.1 p.2) (p : ℕ × ℕ) :
    Enc.size (f p) ≤ Enc.size p := by
  have h1 := size_fst_nat p
  have h2 := size_snd_nat p
  have h3 : Nat.size (f p) ≤ Nat.size (max p.1 p.2) := Nat.size_le_size (h p)
  have h4 : Nat.size (max p.1 p.2) ≤ max (Nat.size p.1) (Nat.size p.2) := by
    rcases le_total p.1 p.2 with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _
  have h5 : Enc.size (f p) = Nat.size (f p) + 2 := Small.size_nat _
  omega

theorem pf_sub : PF (fun p : ℕ × ℕ => p.1 - p.2) 7 1 0 1 :=
  PF.ofClean Small.cleanCompute_sub (fun N => by norm_num; omega) (fun p => by
    have := size_binop_le (f := fun p : ℕ × ℕ => p.1 - p.2)
      (fun _ => le_trans (Nat.sub_le _ _) (le_max_left _ _)) p
    norm_num; omega)

theorem pf_min : PF (fun p : ℕ × ℕ => min p.1 p.2) 8 1 0 1 :=
  PF.ofClean Small.cleanCompute_min (fun N => by norm_num; omega) (fun p => by
    have := size_binop_le (f := fun p : ℕ × ℕ => min p.1 p.2)
      (fun _ => le_trans (min_le_left _ _) (le_max_left _ _)) p
    norm_num; omega)

theorem pf_max : PF (fun p : ℕ × ℕ => max p.1 p.2) 8 1 0 1 :=
  PF.ofClean Small.cleanCompute_max (fun N => by norm_num; omega) (fun p => by
    have := size_binop_le (f := fun p : ℕ × ℕ => max p.1 p.2) (fun _ => le_refl _) p
    norm_num; omega)

theorem size_bool_le (b : Bool) : Enc.size b ≤ 3 := Combine.size_bool_le b

theorem pf_le : PF (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) 8 1 2 0 :=
  PF.ofClean Small.cleanCompute_le (fun N => by norm_num; omega) (fun p => by
    have := size_bool_le (decide (p.1 ≤ p.2))
    norm_num; omega)

theorem pf_mul : PF (fun p : ℕ × ℕ => p.1 * p.2) 8 2 2 1 := by
  refine PF.ofClean Small.cleanCompute_mul (fun N => ?_) (fun p => ?_)
  · show 10 * (19 * (N + 1) ^ 2) + 4 ≤ 2 ^ 8 * (N + 1) ^ 2
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    norm_num
    omega
  · have h1 := size_fst_nat p
    have h2 := size_snd_nat p
    have h3 : Nat.size (p.1 * p.2) ≤ Nat.size p.1 + Nat.size p.2 := size_mul_le _ _
    have h4 : Enc.size (p.1 * p.2) = Nat.size (p.1 * p.2) + 2 := Small.size_nat _
    norm_num
    omega

theorem pf_natSize : PF (fun a : ℕ => Nat.size a) 8 1 0 1 :=
  PF.ofClean Small.cleanCompute_size (fun N => by norm_num; omega) (fun a => by
    have h1 : Nat.size (Nat.size a) ≤ Nat.size a := size_le_self _
    have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
    have h3 : Enc.size (Nat.size a) = Nat.size (Nat.size a) + 2 := Small.size_nat _
    norm_num; omega)

end Explicit
