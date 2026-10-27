import Workspace.Machine.Block

/-!
# Arithmetic routines

The machine of `RAM.lean` has no comparison, no multiplication and no division: exactly as in
Cook-Reckhow, the instruction set is constants, copy, addition, truncated subtraction, indirect
load and store, and a jump on zero.  Everything else has to be programmed, and its cost has to be
accounted for.  This file does that, for the operations the paper's procedures use.

Truncated subtraction already decides comparisons: `x ≤ y` exactly when `x - y = 0`, so a
comparison is one subtraction and one conditional.  Multiplication and division are the
substantial ones, because their cost must be **polynomial in the bit length** of the operands and
not in their value: repeated addition would be exponential.  Both are done by the school method
in base two, in the form that needs no halving (the machine cannot halve): the multiplier is
consumed from the top, one binary digit at a time,

```
acc := 0;  rem := y
repeat  Nat.size y  times:
   if rem ≠ 0 then
      find the largest power of two  p ≤ rem,  together with  q = x * p,
        by doubling  p  from 1  and  q  from  x  while  2 * p ≤ rem;
      rem := rem - p;  acc := acc + q
```

and division is the same loop with `q = p` and the roles of the operands exchanged.  Both loops
run `Nat.size y` times and the inner one runs `Nat.size y` times as well, so the cost is
quadratic in the bit length.

## The register discipline

Every routine takes its arguments and its result register below a **scratch base** `s`, and uses
exactly the registers `s, s+1, ..., s+c-1` as scratch (`c` is fixed per routine).  So the
hypotheses of every specification are of the form `r < s`, `x < s`, and the postcondition carries
a frame clause `Outside [r, s, s+1, ...] m₀ m'`: nothing outside the result register and the
scratch block has changed.  Callers place their live data below `s` or above `s + c`.

## Main results

* `RAM.Arith.runsTo_leTo`, `..._ltTo`, `..._eqTo`, `..._minTo`, `..._maxTo`: comparisons and
  extrema, in 5 or 7 steps;
* `RAM.Arith.runsTo_sizeTo`: the bit length `Nat.size`, in `6 * Nat.size a + 6` steps;
* `RAM.Arith.runsTo_sizeTo`-style routines for multiplication and for division with remainder
  are not in this file: see `RAM.Arith.runsTo_mulCore` (`Workspace/Machine/Mul.lean`) and
  `RAM.Arith.runsTo_divModCore` (`Workspace/Machine/Div.lean`), both in
  `O((Nat.size a + Nat.size b)^2)` steps.
-/

namespace RAM
namespace Arith

/-! ## Comparisons

`x ≤ y` holds exactly when the truncated difference `x - y` is zero, so one subtraction and one
conditional decide it. -/

/-- `R r ← 1` if `R x ≤ R y`, and `R r ← 0` otherwise; `s` is the scratch base (one register). -/
def leTo (r x y s : ℕ) : Program := seq (subTo s x y) (ifz s (assign r 0) (assign r 1))

/-- `R r ← 1` if `R x ≤ R y`, else `0`, in five steps. -/
theorem runsTo_leTo (r x y s : ℕ) (m₀ : Mem) :
    RunsTo (leTo r x y s) (fun m => m = m₀)
      (fun m' => m' r = (if m₀ x ≤ m₀ y then 1 else 0) ∧ Outside [r, s] m₀ m') 5 := by
  refine RunsTo.mono (T := 1 + (1 + 1 + 2)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ x - m₀ y))
    (runsTo_subTo s x y (fun m hm => by rw [hm])) (RunsTo.ifz ?_ ?_)
  · refine runsTo_assign r 0 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_neg (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]
  · refine runsTo_assign r 1 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_pos (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]

/-- `R r ← 1` if `R x < R y`, and `R r ← 0` otherwise. -/
def ltTo (r x y s : ℕ) : Program := seq (subTo s y x) (ifz s (assign r 1) (assign r 0))

/-- `R r ← 1` if `R x < R y`, else `0`, in five steps. -/
theorem runsTo_ltTo (r x y s : ℕ) (m₀ : Mem) :
    RunsTo (ltTo r x y s) (fun m => m = m₀)
      (fun m' => m' r = (if m₀ x < m₀ y then 1 else 0) ∧ Outside [r, s] m₀ m') 5 := by
  refine RunsTo.mono (T := 1 + (1 + 1 + 2)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ y - m₀ x))
    (runsTo_subTo s y x (fun m hm => by rw [hm])) (RunsTo.ifz ?_ ?_)
  · refine runsTo_assign r 1 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_pos (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]
  · refine runsTo_assign r 0 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_neg (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]

/-- `R r ← 1` if `R x = R y`, and `R r ← 0` otherwise.  Scratch: `s`, `s+1`. -/
def eqTo (r x y s : ℕ) : Program :=
  seq (subTo s x y) (seq (subTo (s + 1) y x)
    (seq (addTo s s (s + 1)) (ifz s (assign r 0) (assign r 1))))

/-- `R r ← 1` if `R x = R y`, else `0`, in seven steps.  The two operands must lie below the
scratch base. -/
theorem runsTo_eqTo (r x y s : ℕ) (hx : x < s) (hy : y < s) (m₀ : Mem) :
    RunsTo (eqTo r x y s) (fun m => m = m₀)
      (fun m' => m' r = (if m₀ x = m₀ y then 1 else 0) ∧ Outside [r, s, s + 1] m₀ m') 7 := by
  have dx : x ≠ s := by omega
  have dy : y ≠ s := by omega
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1 + 2)))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ x - m₀ y))
    (runsTo_subTo s x y (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq
    (mid := fun m => m = (m₀.update s (m₀ x - m₀ y)).update (s + 1) (m₀ y - m₀ x))
    (runsTo_subTo (s + 1) y x (fun m hm => by
      rw [hm, Mem.update_of_ne _ _ dy, Mem.update_of_ne _ _ dx])) ?_
  refine RunsTo.seq
    (mid := fun m => m = ((m₀.update s (m₀ x - m₀ y)).update (s + 1) (m₀ y - m₀ x)).update s
      ((m₀ x - m₀ y) + (m₀ y - m₀ x)))
    (runsTo_addTo s s (s + 1) (fun m hm => by
      rw [hm, Mem.update_self, Mem.update_of_ne _ _ (by omega : s ≠ s + 1), Mem.update_self]))
    (RunsTo.ifz ?_ ?_)
  · refine runsTo_assign r 0 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_neg (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Mem.update_of_ne _ _ h1, Mem.update_of_ne _ _ h2, Mem.update_of_ne _ _ h3,
      Mem.update_of_ne _ _ h2]
  · refine runsTo_assign r 1 (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    refine ⟨by rw [Mem.update_self, if_pos (by omega)], fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Mem.update_of_ne _ _ h1, Mem.update_of_ne _ _ h2, Mem.update_of_ne _ _ h3,
      Mem.update_of_ne _ _ h2]

/-- `R r ← min (R x) (R y)`. -/
def minTo (r x y s : ℕ) : Program := seq (subTo s x y) (ifz s (copyTo r y) (copyTo r x))

/-- `R r ← min (R x) (R y)`, in five steps. -/
theorem runsTo_minTo (r x y s : ℕ) (hx : x < s) (hy : y < s) (m₀ : Mem) :
    RunsTo (minTo r x y s) (fun m => m = m₀)
      (fun m' => m' r = min (m₀ x) (m₀ y) ∧ Outside [r, s] m₀ m') 5 := by
  have dx : x ≠ s := by omega
  have dy : y ≠ s := by omega
  refine RunsTo.mono (T := 1 + (1 + 1 + 2)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ x - m₀ y))
    (runsTo_subTo s x y (fun m hm => by rw [hm])) (RunsTo.ifz ?_ ?_)
  · refine runsTo_copyTo r y (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    rw [Mem.update_of_ne _ _ dy]
    refine ⟨by rw [Mem.update_self]; omega, fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]
  · refine runsTo_copyTo r x (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    rw [Mem.update_of_ne _ _ dx]
    refine ⟨by rw [Mem.update_self]; omega, fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]

/-- `R r ← max (R x) (R y)`. -/
def maxTo (r x y s : ℕ) : Program := seq (subTo s x y) (ifz s (copyTo r x) (copyTo r y))

/-- `R r ← max (R x) (R y)`, in five steps. -/
theorem runsTo_maxTo (r x y s : ℕ) (hx : x < s) (hy : y < s) (m₀ : Mem) :
    RunsTo (maxTo r x y s) (fun m => m = m₀)
      (fun m' => m' r = max (m₀ x) (m₀ y) ∧ Outside [r, s] m₀ m') 5 := by
  have dx : x ≠ s := by omega
  have dy : y ≠ s := by omega
  refine RunsTo.mono (T := 1 + (1 + 1 + 2)) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ x - m₀ y))
    (runsTo_subTo s x y (fun m hm => by rw [hm])) (RunsTo.ifz ?_ ?_)
  · refine runsTo_copyTo r x (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    rw [Mem.update_of_ne _ _ dx]
    refine ⟨by rw [Mem.update_self]; omega, fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]
  · refine runsTo_copyTo r y (fun m hm => ?_)
    obtain ⟨hm1, hm2⟩ := hm
    rw [hm1] at hm2 ⊢
    rw [Mem.update_self] at hm2
    rw [Mem.update_of_ne _ _ dy]
    refine ⟨by rw [Mem.update_self]; omega, fun z hz => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [Mem.update_of_ne _ _ hz.1, Mem.update_of_ne _ _ hz.2]

/-! ## Bit length

`R r ← Nat.size (R x)`.  A power of two is doubled from `1` until it exceeds the argument, and
the number of doublings is the bit length.  Scratch registers: `s` holds the power, `s+1` the
constant `1`, `s+2` the difference `power - argument` (zero exactly while the power is still at
most the argument) and `s+3` the loop control, `1` minus that difference. -/

/-- The loop body of `sizeTo`: double the power, increment the counter, recompute the test. -/
def sizeBody (r x s : ℕ) : Program :=
  seq (addTo s s s)
    (seq (addTo r r (s + 1)) (seq (subTo (s + 2) s x) (subTo (s + 3) (s + 1) (s + 2))))

/-- The prelude of `sizeTo`: counter to `0`, power to `1`, and the first test. -/
def sizePre (r x s : ℕ) : Program :=
  seq (assign r 0) (seq (assign s 1) (seq (assign (s + 1) 1)
    (seq (subTo (s + 2) s x) (subTo (s + 3) (s + 1) (s + 2)))))

/-- `R r ← Nat.size (R x)`, the bit length of the argument.  Scratch: `s, s+1, s+2, s+3`. -/
def sizeTo (r x s : ℕ) : Program := seq (sizePre r x s) (whileNz (s + 3) (sizeBody r x s))

/-- The registers `sizeTo` may write. -/
def sizeBlock (r s : ℕ) : List ℕ := [r, s, s + 1, s + 2, s + 3]

/-- The loop invariant of `sizeTo`: the power in `s` is `2` to the counter in `r`, the test
registers hold what they should, and the counter has not overshot the bit length. -/
def SizeInv (r x s a : ℕ) (m₀ m : Mem) : Prop :=
  m x = a ∧ m (s + 1) = 1 ∧ m s = 2 ^ (m r) ∧ m (s + 2) = m s - a ∧
    m (s + 3) = 1 - m (s + 2) ∧ (m r ≠ 0 → 2 ^ (m r - 1) ≤ a) ∧ Outside (sizeBlock r s) m₀ m

theorem runsTo_sizePre (r x s : ℕ) (hr : r < s) (hx : x < s) (hrx : r ≠ x) (m₀ : Mem) :
    RunsTo (sizePre r x s) (fun m => m = m₀) (fun m' => SizeInv r x s (m₀ x) m₀ m') 5 := by
  have hxr : x ≠ r := fun h => hrx h.symm
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m r = 0 ∧ Outside (sizeBlock r s) m₀ m)
    (runsTo_assign r 0 (fun m hm => by
      subst hm
      exact ⟨Mem.update_self _ _ _, (Outside.refl _ _).upd (by simp [sizeBlock]) _⟩)) ?_
  refine RunsTo.seq (mid := fun m => m r = 0 ∧ m s = 1 ∧ Outside (sizeBlock r s) m₀ m)
    (runsTo_assign s 1 (fun m hm => ⟨by
      rw [Mem.update_of_ne _ _ (show r ≠ s by omega)]; exact hm.1,
      Mem.update_self _ _ _, hm.2.upd (by simp [sizeBlock]) _⟩)) ?_
  refine RunsTo.seq
    (mid := fun m => m r = 0 ∧ m s = 1 ∧ m (s + 1) = 1 ∧ Outside (sizeBlock r s) m₀ m)
    (runsTo_assign (s + 1) 1 (fun m hm => ⟨by
      rw [Mem.update_of_ne _ _ (show r ≠ s + 1 by omega)]; exact hm.1, by
      rw [Mem.update_of_ne _ _ (show s ≠ s + 1 by omega)]; exact hm.2.1,
      Mem.update_self _ _ _, hm.2.2.upd (by simp [sizeBlock]) _⟩)) ?_
  refine RunsTo.seq
    (mid := fun m => m r = 0 ∧ m s = 1 ∧ m (s + 1) = 1 ∧ m (s + 2) = 1 - m₀ x ∧
      Outside (sizeBlock r s) m₀ m)
    (runsTo_subTo (s + 2) s x (fun m hm => ⟨by
      rw [Mem.update_of_ne _ _ (show r ≠ s + 2 by omega)]; exact hm.1, by
      rw [Mem.update_of_ne _ _ (show s ≠ s + 2 by omega)]; exact hm.2.1, by
      rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 2 by omega)]; exact hm.2.2.1, by
      rw [Mem.update_self, hm.2.1, hm.2.2.2 x (by simp only [sizeBlock, List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)],
      hm.2.2.2.upd (by simp [sizeBlock]) _⟩)) ?_
  refine runsTo_subTo (s + 3) (s + 1) (s + 2) (fun m hm => ?_)
  obtain ⟨h0, h1, h2, h3, hout⟩ := hm
  have hx' : m x = m₀ x := hout x (by simp only [sizeBlock, List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (show x ≠ s + 3 by omega)]; exact hx'
  · rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 3 by omega)]; exact h2
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show r ≠ s + 3 by omega), h1, h0, pow_zero]
  · rw [Mem.update_of_ne _ _ (show s + 2 ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 3 by omega), h1, h3]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 2 ≠ s + 3 by omega), h2]
  · rw [Mem.update_of_ne _ _ (show r ≠ s + 3 by omega), h0]
    intro h; exact absurd rfl h
  · exact hout.upd (by simp [sizeBlock]) _

/-- One iteration of the `sizeTo` loop: it preserves the invariant and strictly decreases
`Nat.size a - r`. -/
theorem runsTo_sizeBody (r x s a : ℕ) (hr : r < s) (hx : x < s) (hrx : r ≠ x) (m₀ : Mem)
    (n : ℕ) :
    RunsTo (sizeBody r x s)
      (fun m => SizeInv r x s a m₀ m ∧ m (s + 3) ≠ 0 ∧ Nat.size a - m r = n)
      (fun m' => SizeInv r x s a m₀ m' ∧ Nat.size a - m' r < n) 4 := by
  have hxr : x ≠ r := fun h => hrx h.symm
  refine RunsTo.mono (T := 1 + (1 + (1 + 1))) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  -- `K` is the precondition at the fixed starting memory `m₁`, carried along the block.
  set K : Prop := SizeInv r x s a m₀ m₁ ∧ m₁ (s + 3) ≠ 0 ∧ Nat.size a - m₁ r = n with hK
  have hKs : K → m₁ s = 2 ^ (m₁ r) := fun h => h.1.2.2.1
  have hKpow : K → 2 ^ (m₁ r) ≤ a := by
    rintro ⟨⟨ix, ione, ip, ie, ic, ilow, iout⟩, hne, -⟩
    rw [← ip]; omega
  refine RunsTo.seq (mid := fun m => (m s = m₁ s + m₁ s ∧ m r = m₁ r ∧ m x = a ∧
      m (s + 1) = 1 ∧ Outside (sizeBlock r s) m₀ m) ∧ K)
    (runsTo_addTo s s s (fun m hm => ?_)) ?_
  · obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨⟨ix, ione, ip, ie, ic, ilow, iout⟩, -, -⟩ := id hpre
    exact ⟨⟨Mem.update_self _ _ _,
      by rw [Mem.update_of_ne _ _ (show r ≠ s by omega)],
      by rw [Mem.update_of_ne _ _ (show x ≠ s by omega)]; exact ix,
      by rw [Mem.update_of_ne _ _ (show s + 1 ≠ s by omega)]; exact ione,
      iout.upd (by simp [sizeBlock]) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m s = m₁ s + m₁ s ∧ m r = m₁ r + 1 ∧ m x = a ∧
      m (s + 1) = 1 ∧ Outside (sizeBlock r s) m₀ m) ∧ K)
    (runsTo_addTo r r (s + 1) (fun m hm => ?_)) ?_
  · obtain ⟨⟨e1, e2, e3, e4, e5⟩, hpre⟩ := hm
    refine ⟨⟨by rw [Mem.update_of_ne _ _ (show s ≠ r by omega)]; exact e1, by
      rw [Mem.update_self, e2, e4], by
      rw [Mem.update_of_ne _ _ hxr]; exact e3, by
      rw [Mem.update_of_ne _ _ (show s + 1 ≠ r by omega)]; exact e4,
      e5.upd (by simp [sizeBlock]) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m s = m₁ s + m₁ s ∧ m r = m₁ r + 1 ∧ m x = a ∧
      m (s + 1) = 1 ∧ m (s + 2) = (m₁ s + m₁ s) - a ∧ Outside (sizeBlock r s) m₀ m) ∧ K)
    (runsTo_subTo (s + 2) s x (fun m hm => ?_)) ?_
  · obtain ⟨⟨e1, e2, e3, e4, e5⟩, hpre⟩ := hm
    refine ⟨⟨by rw [Mem.update_of_ne _ _ (show s ≠ s + 2 by omega)]; exact e1, by
      rw [Mem.update_of_ne _ _ (show r ≠ s + 2 by omega)]; exact e2, by
      rw [Mem.update_of_ne _ _ (show x ≠ s + 2 by omega)]; exact e3, by
      rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 2 by omega)]; exact e4, by
      rw [Mem.update_self, e1, e3],
      e5.upd (by simp [sizeBlock]) _⟩, hpre⟩
  refine runsTo_subTo (s + 3) (s + 1) (s + 2) (fun m hm => ?_)
  obtain ⟨⟨e1, e2, e3, e4, e5, e6⟩, hpre⟩ := hm
  have hpow : 2 ^ (m₁ r) ≤ a := hKpow hpre
  have hs : m₁ s = 2 ^ (m₁ r) := hKs hpre
  have hn : Nat.size a - m₁ r = n := hpre.2.2
  have hlt : m₁ r < Nat.size a := Nat.lt_size.2 hpow
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (show x ≠ s + 3 by omega)]; exact e3
  · rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 3 by omega)]; exact e4
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show r ≠ s + 3 by omega), e1, e2, hs, pow_succ]
    ring
  · rw [Mem.update_of_ne _ _ (show s + 2 ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 3 by omega), e1, e5]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 2 ≠ s + 3 by omega), e4]
  · rw [Mem.update_of_ne _ _ (show r ≠ s + 3 by omega), e2]
    intro _
    simpa using hpow
  · exact e6.upd (by simp [sizeBlock]) _
  · rw [Mem.update_of_ne _ _ (show r ≠ s + 3 by omega), e2]
    omega

/-- **Bit length.**  `sizeTo r x s` leaves `Nat.size (R x)` in `R r` in `6 * Nat.size (R x) + 6`
steps, touching only `r` and the scratch block `s, s+1, s+2, s+3`. -/
theorem runsTo_sizeTo (r x s : ℕ) (hr : r < s) (hx : x < s) (hrx : r ≠ x) (m₀ : Mem) :
    RunsTo (sizeTo r x s) (fun m => m = m₀)
      (fun m' => m' r = Nat.size (m₀ x) ∧ Outside (sizeBlock r s) m₀ m')
      (6 * Nat.size (m₀ x) + 6) := by
  refine RunsTo.mono (T := 5 + (Nat.size (m₀ x) * (4 + 2) + 1)) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => SizeInv r x s (m₀ x) m₀ m)
    (runsTo_sizePre r x s hr hx hrx m₀) ?_
  refine (runsTo_whileNz (μ := fun m => Nat.size (m₀ x) - m r)
    (fun n => runsTo_sizeBody r x s (m₀ x) hr hx hrx m₀ n) (fun m _ => Nat.sub_le _ _)).weaken ?_
  rintro m' ⟨⟨ix, ione, ip, ie, ic, ilow, iout⟩, hz⟩
  refine ⟨?_, iout⟩
  have hgt : m₀ x < 2 ^ (m' r) := by rw [← ip]; omega
  have hup : Nat.size (m₀ x) ≤ m' r := Nat.size_le.2 hgt
  rcases Nat.eq_zero_or_pos (m' r) with h0 | h0
  · omega
  · have h1 := ilow (by omega)
    have h2 : m' r - 1 < Nat.size (m₀ x) := Nat.lt_size.2 h1
    omega

end Arith
end RAM
