/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: Bochert's theorem.
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
# Bochert's theorem ([DiM, Thm. 3.3B])

The proof of [DiM, Thm. 5.2A] (Dixon–Mortimer, *Permutation Groups*, GTM 163, Springer
1996, p. 148) begins: "if `G` is primitive, and `G ≠ A`, then by Bochert's Theorem
(Theorem 3.3B) we have `h ≥ ½⌊(n+1)/2⌋!`".  This file proves Bochert's theorem along
[DiM, §3.3]:

* **Exercise 1.6.7** (`Babai.DM52.isThreeCycle_commutator`): if the supports of `x` and `y`
  meet in exactly one point, then the commutator `[x, y]` is a 3-cycle;
* **Exercise 3.3.2** (`Babai.DM52.card_le_descFactorial_of_isBase`): a group with a base of
  size `b` has order at most `n(n-1)⋯(n-b+1)`;
* **Theorem 3.3B** (`Babai.DM52.bochert`): a primitive group `G ≤ Sym(n)` not containing
  `Alt(n)` has a base of size at most `n/2`, hence `|G| ≤ n(n-1)⋯(n-⌊n/2⌋+1)`, i.e.
  `|Sym(n) : G| ≥ ⌈n/2⌉!`;
* **Exercise 5.2.1** (`Babai.DM52.choose_lt_half_factorial`): `½⌊(n+1)/2⌋! > C(n, ⌊n/2⌋)`
  for `n ≥ 15` and for `n = 13`.

The primitivity hypothesis is Mathlib's `MulAction.IsPreprimitive`; for `|Ω| ≥ 2` it is the
paper's `Babai.IsPrimitive` (`Babai.isPrimitive_iff_isPreprimitive`).
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem perm_inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x :=
  Perm.inv_eq_iff_eq.mpr rfl

omit [DecidableEq α] in
@[simp] theorem perm_apply_inv_self (f : Perm α) (x : α) : f (f⁻¹ x) = x :=
  (Equiv.apply_eq_iff_eq_symm_apply f).mpr rfl

/-! ### Exercise 1.6.7: a commutator which is a 3-cycle -/

/-- **[DiM, Exercise 1.6.7].**  If `x` and `y` both move `a` and no other point is moved by
both, then the commutator `x⁻¹ y⁻¹ x y` is a 3-cycle (namely `(y⁻¹a, a, x⁻¹a)`). -/
theorem isThreeCycle_commutator [Fintype α] {x y : Perm α} {a : α} (hxa : x a ≠ a)
    (hya : y a ≠ a) (hxy : ∀ z, x z ≠ z → y z ≠ z → z = a) :
    IsThreeCycle (x⁻¹ * y⁻¹ * x * y) := by
  set a₁ := y⁻¹ a with ha₁
  set a₂ := x⁻¹ a with ha₂
  -- the moved points
  have hy_a₁ : y a₁ = a := by simp [ha₁]
  have hx_a₂ : x a₂ = a := by simp [ha₂]
  have ha₁a : a₁ ≠ a := by
    intro h; apply hya; rw [← h, hy_a₁, h]
  have ha₂a : a₂ ≠ a := by
    intro h; apply hxa; rw [← h, hx_a₂, h]
  have hya₁ : y a₁ ≠ a₁ := by rw [hy_a₁]; exact ha₁a.symm
  have hxa₂ : x a₂ ≠ a₂ := by rw [hx_a₂]; exact ha₂a.symm
  -- `a₁` is not moved by `x`, `a₂` not by `y`
  have hxa₁ : x a₁ = a₁ := by
    by_contra h; exact ha₁a (hxy a₁ h hya₁)
  have hya₂ : y a₂ = a₂ := by
    by_contra h; exact ha₂a (hxy a₂ hxa₂ h)
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h; apply hxa₂; rw [← h]; exact hxa₁
  -- general facts: a point moved by `x` other than `a` is fixed by `y`, and conversely
  have hx_fix : ∀ z, x z ≠ z → z ≠ a → y z = z := by
    intro z hz hza; by_contra h; exact hza (hxy z hz h)
  have hy_fix : ∀ z, y z ≠ z → z ≠ a → x z = z := by
    intro z hz hza; by_contra h; exact hza (hxy z h hz)
  have hinv_x : ∀ z, x z = z → x⁻¹ z = z := fun z hz => by
    rw [Perm.inv_eq_iff_eq]; exact hz.symm
  have hinv_y : ∀ z, y z = z → y⁻¹ z = z := fun z hz => by
    rw [Perm.inv_eq_iff_eq]; exact hz.symm
  suffices h : x⁻¹ * y⁻¹ * x * y = swap a₁ a₂ * swap a₁ a by
    rw [h]; exact isThreeCycle_swap_mul_swap_same ha₁a₂ ha₁a ha₂a
  ext z
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hz1 : z = a₁
  · rw [hz1, hy_a₁, swap_apply_left, swap_apply_of_ne_of_ne ha₁a.symm ha₂a.symm]
    -- `x a` is moved by `x` and differs from `a`, so it is fixed by `y`
    have hxa' : x (x a) ≠ x a := fun h => hxa (x.injective h)
    have hxaa : x a ≠ a := hxa
    have hya' : y (x a) = x a := hx_fix _ hxa' hxaa
    rw [hinv_y _ hya', perm_inv_apply_self]
  by_cases hz0 : z = a
  · rw [hz0, swap_apply_right, swap_apply_left]
    have hyy : y (y a) ≠ y a := fun h => hya (y.injective h)
    have hxy' : x (y a) = y a := hy_fix _ hyy hya
    rw [hxy', perm_inv_apply_self]
  by_cases hz2 : z = a₂
  · rw [hz2, swap_apply_of_ne_of_ne (Ne.symm ha₁a₂) ha₂a, swap_apply_right, hya₂, hx_a₂,
      ← ha₁, hinv_x _ hxa₁]
  -- `z` is none of `a₁, a, a₂`: the commutator fixes it
  rw [swap_apply_of_ne_of_ne hz1 hz0, swap_apply_of_ne_of_ne hz1 hz2]
  by_cases hyz : y z = z
  · rw [hyz]
    by_cases hxz : x z = z
    · rw [hxz, hinv_y _ hyz, hinv_x _ hxz]
    · have hxz' : x (x z) ≠ x z := fun h => hxz (x.injective h)
      have hxza : x z ≠ a := by
        intro h; apply hz2; rw [ha₂, ← h, perm_inv_apply_self]
      rw [hinv_y _ (hx_fix _ hxz' hxza), perm_inv_apply_self]
  · have hyz' : y (y z) ≠ y z := fun h => hyz (y.injective h)
    have hyza : y z ≠ a := by
      intro h; apply hz1; rw [ha₁, ← h, perm_inv_apply_self]
    rw [hy_fix _ hyz' hyza, perm_inv_apply_self, hinv_x _ (hy_fix _ hyz hz0)]

/-! ### Bases -/

/-- A *base* for `G` (§3.3 of [DiM]): a set of points whose pointwise stabilizer in `G` is
trivial. -/
def IsBase (G : Subgroup (Perm α)) (B : Finset α) : Prop :=
  ∀ g ∈ G, (∀ x ∈ B, g x = x) → g = 1

omit [DecidableEq α] in
/-- **[DiM, Exercise 3.3.2]** (upper bound).  If `G` has a base of size `b`, then
`|G| ≤ n(n-1)⋯(n-b+1)`: an element of `G` is determined by the images of the base
points. -/
theorem card_le_descFactorial_of_isBase [Fintype α] {G : Subgroup (Perm α)} {B : Finset α}
    (hB : IsBase G B) : Nat.card G ≤ (Fintype.card α).descFactorial B.card := by
  classical
  let f : G → (B ↪ α) := fun g =>
    ⟨fun x => (g : Perm α) x, fun x y h => Subtype.ext ((g : Perm α).injective h)⟩
  have hf : Function.Injective f := by
    intro g h hgh
    have : (h⁻¹ * g : G) = 1 := by
      have := hB ((h⁻¹ * g : G) : Perm α) (h⁻¹ * g).2 (fun x hx => by
        have := congrArg (fun e : (B ↪ α) => e ⟨x, hx⟩) hgh
        simp only [f, Function.Embedding.coeFn_mk] at this
        simp [Perm.mul_apply, this])
      exact Subtype.ext this
    rw [inv_mul_eq_one] at this
    exact this.symm
  calc Nat.card G ≤ Nat.card (B ↪ α) := Nat.card_le_card_of_injective f hf
    _ = (Fintype.card α).descFactorial B.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_coe]

/-- `n(n-1)⋯(n-k+1)` is monotone in the number of factors `k ≤ n`. -/
theorem descFactorial_mono_right {n k m : ℕ} (hkm : k ≤ m) (hm : m ≤ n) :
    n.descFactorial k ≤ n.descFactorial m := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hkm ih =>
    rw [Nat.descFactorial_succ]
    calc n.descFactorial k ≤ n.descFactorial m := ih (by omega)
      _ ≤ (n - m) * n.descFactorial m := Nat.le_mul_of_pos_left _ (by omega)

/-! ### Theorem 3.3B -/

/-- **[DiM, Thm. 3.3B]** (Bochert 1889), first statement.  A primitive group `G ≤ Sym(n)`
which does not contain `Alt(n)` has a base of size at most `n/2`.

Proof of [DiM]: let `Σ` be a base of minimal size and suppose `|Σ| > n/2`.  Then
`Δ := Ω \ Σ` is not a base, so some `x ≠ 1` has support inside `Σ`; pick `a ∈ supp(x)`.
`Σ \ {a}` is not a base, so some `y ≠ 1` has support inside `Δ ∪ {a}`; as `Σ` is a base,
`a ∈ supp(y)`.  Hence `supp(x) ∩ supp(y) = {a}` and `G` contains a 3-cycle
(Exercise 1.6.7), so `G ≥ Alt(n)` by Theorem 3.3A (Mathlib's
`Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`). -/
theorem exists_isBase_card_le [Fintype α] (G : Subgroup (Perm α)) (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) :
    ∃ B : Finset α, IsBase G B ∧ 2 * B.card ≤ Fintype.card α := by
  classical
  -- a base of minimal size
  have hex : ∃ k, ∃ B : Finset α, IsBase G B ∧ B.card = k :=
    ⟨_, Finset.univ, fun g _ hg => Equiv.ext fun x => hg x (Finset.mem_univ x), rfl⟩
  obtain ⟨S₀, hS, hSk⟩ := Nat.find_spec hex
  have hmin : ∀ B : Finset α, IsBase G B → S₀.card ≤ B.card := by
    intro B hB
    rw [hSk]
    exact Nat.find_min' hex ⟨B, hB, rfl⟩
  refine ⟨S₀, hS, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  apply hA
  -- `Δ = Ω \ Σ` is not a base
  have hΔ : ¬ IsBase G S₀ᶜ := by
    intro h
    have := hmin _ h
    rw [Finset.card_compl] at this
    omega
  simp only [IsBase, not_forall] at hΔ
  obtain ⟨x, hxG, hxfix, hx1⟩ := hΔ
  obtain ⟨a, hxa⟩ : ∃ a, x a ≠ a := by
    by_contra h
    exact hx1 (Equiv.ext fun z => by by_contra hz; exact h ⟨z, hz⟩)
  have haS : a ∈ S₀ := by
    by_contra h; exact hxa (hxfix a (Finset.mem_compl.2 h))
  -- `Σ \ {a}` is not a base
  have hSa : ¬ IsBase G (S₀.erase a) := by
    intro h
    have := hmin _ h
    rw [Finset.card_erase_of_mem haS] at this
    have : 0 < S₀.card := Finset.card_pos.2 ⟨a, haS⟩
    omega
  simp only [IsBase, not_forall] at hSa
  obtain ⟨y, hyG, hyfix, hy1⟩ := hSa
  have hya : y a ≠ a := by
    intro hya
    exact hy1 (hS y hyG (fun z hz => by
      by_cases hza : z = a
      · rw [hza]; exact hya
      · exact hyfix z (Finset.mem_erase.2 ⟨hza, hz⟩)))
  have hxy : ∀ z, x z ≠ z → y z ≠ z → z = a := by
    intro z hxz hyz
    have hzS : z ∈ S₀ := by
      by_contra h; exact hxz (hxfix z (Finset.mem_compl.2 h))
    by_contra hza
    exact hyz (hyfix z (Finset.mem_erase.2 ⟨hza, hzS⟩))
  have h3 := isThreeCycle_commutator hxa hya hxy
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG h3
    (G.mul_mem (G.mul_mem (G.mul_mem (G.inv_mem hxG) (G.inv_mem hyG)) hxG) hyG)

/-- **[DiM, Thm. 3.3B]** (Bochert), second statement.  A primitive group `G ≤ Sym(n)` not
containing `Alt(n)` has order at most `n(n-1)⋯(n-⌊n/2⌋+1)`. -/
theorem card_le_bochert [Fintype α] (G : Subgroup (Perm α)) (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) :
    Nat.card G ≤ (Fintype.card α).descFactorial (Fintype.card α / 2) := by
  obtain ⟨B, hB, hcard⟩ := exists_isBase_card_le G hG hA
  exact (card_le_descFactorial_of_isBase hB).trans
    (descFactorial_mono_right (by omega) (Nat.div_le_self _ _))

/-- **[DiM, Thm. 3.3B]**, in the form used in the proof of Theorem 5.2A: the index of a
primitive group `G ≤ Sym(n)` not containing `Alt(n)` satisfies `|Sym(n) : G| ≥ ⌈n/2⌉!`,
i.e. `|G| · (n - ⌊n/2⌋)! ≤ n!`. -/
theorem bochert [Fintype α] (G : Subgroup (Perm α)) (hG : IsPreprimitive G α)
    (hA : ¬ alternatingGroup α ≤ G) :
    Nat.card G * (Fintype.card α - Fintype.card α / 2)! ≤ (Fintype.card α)! := by
  have h := card_le_bochert G hG hA
  calc Nat.card G * (Fintype.card α - Fintype.card α / 2)!
      ≤ (Fintype.card α).descFactorial (Fintype.card α / 2) *
          (Fintype.card α - Fintype.card α / 2)! := Nat.mul_le_mul_right _ h
    _ = (Fintype.card α)! := by
      rw [mul_comm, Nat.factorial_mul_descFactorial (Nat.div_le_self _ _)]

/-! ### Exercise 5.2.1 -/

/-- `k! ≥ 2^(2k+2)` for `k ≥ 11`. -/
theorem pow_le_factorial_of_ge : ∀ k, 11 ≤ k → 2 ^ (2 * k + 2) ≤ k ! := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, pow_add]
    calc 2 ^ (2 * k + 2) * 2 ^ 2 = 4 * 2 ^ (2 * k + 2) := by ring
      _ ≤ (k + 1) * k ! := Nat.mul_le_mul (by omega) ih

/-- **[DiM, Exercise 5.2.1].**  `½⌊(n+1)/2⌋! > C(n, ⌊n/2⌋)` for all `n ≥ 15` and for
`n = 13`; in the form `2 · C(n, ⌊n/2⌋) < ⌊(n+1)/2⌋!`. -/
theorem choose_lt_half_factorial (n : ℕ) (hn : 15 ≤ n ∨ n = 13) :
    2 * n.choose (n / 2) < ((n + 1) / 2)! := by
  rcases Nat.lt_or_ge n 22 with h | h
  · rcases hn with hn | rfl
    · interval_cases n <;> decide
    · decide
  · have hk : 11 ≤ (n + 1) / 2 := by omega
    have h1 := pow_le_factorial_of_ge _ hk
    have h2 : n.choose (n / 2) < 2 ^ n := by
      have := Nat.choose_le_two_pow n (n / 2)
      rcases this.lt_or_eq with h | h
      · exact h
      · exfalso
        have hsum := Nat.sum_range_choose n
        have hlt : n.choose (n / 2) < ∑ i ∈ Finset.range (n + 1), n.choose i := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_range.2 (by omega : n / 2 < n + 1))]
          have : 0 < ∑ i ∈ (Finset.range (n + 1)).erase (n / 2), n.choose i := by
            apply Finset.sum_pos'
            · intro i _; exact Nat.zero_le _
            · refine ⟨0, Finset.mem_erase.2 ⟨by omega, by simp⟩, by simp⟩
          omega
        omega
    have h3 : 2 ^ (n + 1) ≤ 2 ^ (2 * ((n + 1) / 2) + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at h3
    omega

end Babai.DM52
