import Workspace.Machine.SmallTime
import Workspace.Machine.PolyFun

/-!
# Multiplication, and the shift-and-subtract loop it shares with division

The machine has no multiplication, so it has to be programmed, and its cost has to be
polynomial in the **bit length** of the operands: repeated addition costs the *value* of an
operand, which is exponential in its length.

The routine is the school method in base two, in the form that needs no halving (the machine
cannot halve).  It is written once, for both multiplication and division, because the two are the
same loop with the roles of the operands exchanged.  Write `x₀` and `y₀` for two numbers with
`x₀ ≥ 1`, and `rem₀` for a third one.  The loop keeps a remainder `rem` (starting at `rem₀`) and
an accumulator `acc` (starting at `0`), and while `x₀ ≤ rem` it does one round:

```
x := x₀;  y := y₀
while  x + x ≤ rem  do  x := x + x;  y := y + y
rem := rem - x;  acc := acc + y
```

The inner loop doubles `x` and `y` together, so `x * y₀ = y * x₀` throughout, and it stops with
`x ≤ rem < x + x`.  Therefore one round subtracts from `rem` the largest multiple `x` of `x₀` by
a power of two with `x ≤ rem`, and adds the matching `y` to `acc`.  The invariant of the outer
loop is `acc * x₀ = (rem₀ - rem) * y₀`, and the loop ends with `rem < x₀`.

* With `x₀ = 1`, `y₀ = a` and `rem₀ = b` the loop ends with `rem = 0` and `acc = b * a`: this is
  **multiplication**.
* With `x₀ = b`, `y₀ = 1` and `rem₀ = a` it ends with `rem < b` and `acc * b = a - rem`: this is
  **division with remainder**, done in `Workspace/Machine/Div.lean`.

Both loops are counted in bits.  One round of the inner loop doubles `x`, so it raises
`Nat.size x` by one, and `x ≤ rem` keeps `Nat.size x ≤ Nat.size rem`: the variant is
`Nat.size rem - Nat.size x`.  One round of the outer loop replaces `rem` by `rem - x` with
`x ≤ rem < x + x`, so it lowers `Nat.size rem` by at least one: the variant is `Nat.size rem`.
The whole loop therefore costs `O((Nat.size rem₀) ^ 2)` steps.

## The registers

The input of `RAM.Small.cleanCompute_binary_var` sits in registers `2` and `4`, the answer has to
be left in register `5`, and the registers `2, ..., 9` are free to use.  The loop uses

| register | meaning |
| --- | --- |
| `2` | the remainder `rem` |
| `3` | the accumulator `acc` |
| `5` | the loop control (nonzero exactly while the test holds) |
| `6` | the current `x` |
| `7` | the current `y` |
| `8` | the constant `1` |
| `9` | a temporary |

and it reads `x₀` and `y₀` from two further registers `xz`, `yz`, which must be outside the
block above.  For multiplication `x₀ = 1`, so `xz` is register `8` itself and `yz = 4`; for
division `y₀ = 1`, so `yz = 8` and `xz = 4`.

Both `while` loops of the machine test "register nonzero", while the tests of the algorithm are
`x + x ≤ rem` and `x₀ ≤ rem`.  A test `u ≤ v` is turned into a nonzero register by two truncated
subtractions: `t := u - v` is zero exactly when `u ≤ v`, so `1 - t` is nonzero exactly then.

## Main results

* `RAM.Arith.runsTo_sadLoop`: the loop above, in `Nat.size rem₀ * (Nat.size rem₀ * 7 + 12) + 1`
  steps;
* `RAM.Arith.runsTo_mulCore`: multiplication of the registers `2` and `4` into register `5`;
* `RAM.Small.cleanCompute_mul`, `RAM.Small.polyTimeClean_mul`, `RAM.polyFun_mul`,
  `RAM.PolyFun.mul`.
-/

namespace RAM
namespace Arith

/-! ## Two facts about the bit length -/

/-- Doubling a nonzero number raises its bit length by exactly one. -/
theorem size_add_self (p : ℕ) (hp : 1 ≤ p) : Nat.size (p + p) = Nat.size p + 1 := by
  have h1 : p < 2 ^ Nat.size p := Nat.lt_size_self p
  have h3 : 0 < Nat.size p := Nat.lt_size.2 (by simpa using hp)
  have h4 : 2 ^ (Nat.size p - 1) ≤ p := Nat.lt_size.1 (by omega)
  have hs : Nat.size p = (Nat.size p - 1) + 1 := by omega
  have h2 : Nat.size (p + p) ≤ Nat.size p + 1 := by
    refine Nat.size_le.2 ?_
    rw [pow_succ]
    omega
  have h5 : Nat.size p < Nat.size (p + p) := by
    refine Nat.lt_size.2 ?_
    rw [hs, pow_succ]
    omega
  omega
/-- One round of the outer loop: subtracting from `r` a number `x` with `x ≤ r < x + x` lowers
the bit length. -/
theorem size_sub_lt {x r : ℕ} (h1 : x ≤ r) (h2 : r < x + x) :
    Nat.size (r - x) < Nat.size r := by
  have hr : 1 ≤ r := by omega
  have hs : 0 < Nat.size r := Nat.lt_size.2 (by simpa using hr)
  have hlt : r < 2 ^ Nat.size r := Nat.lt_size_self r
  have key : r - x < 2 ^ (Nat.size r - 1) := by
    rcases Nat.lt_or_ge (r - x) (2 ^ (Nat.size r - 1)) with h | hcon
    · exact h
    have hbig : 2 ^ Nat.size r ≤ r := by
      have hs' : Nat.size r = (Nat.size r - 1) + 1 := by omega
      rw [hs', pow_succ]
      omega
    omega
  have := Nat.size_le.2 key
  omega

/-! ## The loop -/

/-- The registers the shift-and-subtract loop writes. -/
def sadBlock : List ℕ := [2, 3, 5, 6, 7, 9]

/-- The body of the inner loop: double `x` and `y`, then recompute the test `x + x ≤ rem`. -/
def sadInner : Program :=
  seq (addTo 6 6 6) (seq (addTo 7 7 7)
    (seq (addTo 9 6 6) (seq (subTo 9 9 2) (subTo 5 8 9))))

/-- The body of the outer loop: set `x := x₀`, `y := y₀`, run the inner loop, subtract and
accumulate, then recompute the test `x₀ ≤ rem`. -/
def sadOuter (xz yz : ℕ) : Program :=
  seq (copyTo 6 xz) (seq (copyTo 7 yz) (seq (addTo 9 6 6) (seq (subTo 9 9 2) (seq (subTo 5 8 9)
    (seq (whileNz 5 sadInner)
      (seq (subTo 2 2 6) (seq (addTo 3 3 7) (seq (subTo 9 xz 2) (subTo 5 8 9)))))))))

/-- The whole shift-and-subtract loop. -/
def sadLoop (xz yz : ℕ) : Program := whileNz 5 (sadOuter xz yz)

/-- The invariant of the inner loop: `x` is at least one and at most the remainder `ρ`, the pair
`(x, y)` still satisfies `x * y₀ = y * x₀`, and the two test registers hold what they should. -/
def SadIn (ρ acc x₀ y₀ : ℕ) (m₀ m : Mem) : Prop :=
  m 2 = ρ ∧ m 3 = acc ∧ 1 ≤ m 6 ∧ m 6 ≤ ρ ∧ m 6 * y₀ = m 7 * x₀ ∧
    m 9 = (m 6 + m 6) - ρ ∧ m 5 = 1 - m 9 ∧ Outside sadBlock m₀ m

/-- The invariant of the outer loop: the accumulator and the remainder together still describe
`rem₀`, and the test register holds `1 - (x₀ - rem)`. -/
def SadOut (rem₀ x₀ y₀ : ℕ) (m₀ m : Mem) : Prop :=
  m 2 ≤ rem₀ ∧ m 3 * x₀ = (rem₀ - m 2) * y₀ ∧ m 9 = x₀ - m 2 ∧ m 5 = 1 - m 9 ∧
    Outside sadBlock m₀ m

/-- One round of the inner loop: it preserves the invariant and lowers
`Nat.size ρ - Nat.size x`. -/
theorem runsTo_sadInner (ρ acc x₀ y₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1) (n : ℕ) :
    RunsTo sadInner
      (fun m => SadIn ρ acc x₀ y₀ m₀ m ∧ m 5 ≠ 0 ∧ Nat.size ρ - Nat.size (m 6) = n)
      (fun m' => SadIn ρ acc x₀ y₀ m₀ m' ∧ Nat.size ρ - Nat.size (m' 6) < n) 5 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  set K : Prop :=
    SadIn ρ acc x₀ y₀ m₀ m₁ ∧ m₁ 5 ≠ 0 ∧ Nat.size ρ - Nat.size (m₁ 6) = n with hK
  refine RunsTo.seq (mid := fun m => (m 2 = ρ ∧ m 3 = acc ∧ m 6 = m₁ 6 + m₁ 6 ∧
      m 7 = m₁ 7 ∧ Outside sadBlock m₀ m) ∧ K)
    (runsTo_addTo 6 6 6 (fun m hm => ?_)) ?_
  · obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨i2, i3, -, -, -, -, -, iout⟩ := hpre.1
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 6)]; exact i2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 6)]; exact i3,
      Mem.update_self _ _ _,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 6)],
      iout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = ρ ∧ m 3 = acc ∧ m 6 = m₁ 6 + m₁ 6 ∧
      m 7 = m₁ 7 + m₁ 7 ∧ Outside sadBlock m₀ m) ∧ K)
    (runsTo_addTo 7 7 7 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 7)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 7)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 7)]; exact e6,
      by rw [Mem.update_self, e7],
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = ρ ∧ m 3 = acc ∧ m 6 = m₁ 6 + m₁ 6 ∧
      m 7 = m₁ 7 + m₁ 7 ∧ m 9 = (m₁ 6 + m₁ 6) + (m₁ 6 + m₁ 6) ∧ Outside sadBlock m₀ m) ∧ K)
    (runsTo_addTo 9 6 6 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 9)]; exact e6,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 9)]; exact e7,
      by rw [Mem.update_self, e6],
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = ρ ∧ m 3 = acc ∧ m 6 = m₁ 6 + m₁ 6 ∧
      m 7 = m₁ 7 + m₁ 7 ∧ m 9 = ((m₁ 6 + m₁ 6) + (m₁ 6 + m₁ 6)) - ρ ∧
      Outside sadBlock m₀ m) ∧ K)
    (runsTo_subTo 9 9 2 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, e9, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 9)]; exact e6,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 9)]; exact e7,
      by rw [Mem.update_self, e9, e2],
      eout.upd (by decide) _⟩, hpre⟩
  refine runsTo_subTo 5 8 9 (fun m hm => ?_)
  obtain ⟨⟨e2, e3, e6, e7, e9, eout⟩, hpre⟩ := hm
  obtain ⟨i2, i3, i6, i6', i67, i9, i5, iout⟩ := hpre.1
  have hne : m₁ 5 ≠ 0 := hpre.2.1
  have hn : Nat.size ρ - Nat.size (m₁ 6) = n := hpre.2.2
  have hm8 : m 8 = 1 := by rw [eout 8 (by decide), h8]
  -- the test held, so the old `x` satisfied `x + x ≤ ρ`
  have hx2 : m₁ 6 + m₁ 6 ≤ ρ := by omega
  have hsize : Nat.size (m₁ 6 + m₁ 6) = Nat.size (m₁ 6) + 1 := size_add_self _ i6
  have hle : Nat.size (m₁ 6 + m₁ 6) ≤ Nat.size ρ := Nat.size_le_size hx2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5)]; exact e2
  · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 5)]; exact e3
  · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5)]; omega
  · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5)]; omega
  · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5),
      Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 5), e6, e7, add_mul, add_mul, i67]
  · rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5),
      Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5), e6, e9]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5), hm8]
  · exact eout.upd (by decide) _
  · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5), e6]
    omega

/-- The inner loop.  It runs at most `Nat.size rem₀` times, so it costs
`Nat.size rem₀ * 7 + 1` steps; the hypothesis `ρ ≤ rem₀` sits in the precondition so that the
bound is a constant. -/
theorem runsTo_sadInnerLoop (ρ acc x₀ y₀ rem₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1) :
    RunsTo (whileNz 5 sadInner) (fun m => SadIn ρ acc x₀ y₀ m₀ m ∧ ρ ≤ rem₀)
      (fun m' => SadIn ρ acc x₀ y₀ m₀ m' ∧ m' 5 = 0) (Nat.size rem₀ * 7 + 1) := by
  have hwf : Wf (whileNz 5 sadInner) :=
    (runsTo_whileNz (μ := fun m => Nat.size ρ - Nat.size (m 6))
      (fun n => runsTo_sadInner ρ acc x₀ y₀ m₀ h8 n) (fun m _ => Nat.sub_le _ _)).wf
  by_cases hρ : ρ ≤ rem₀
  · refine ((runsTo_whileNz (μ := fun m => Nat.size ρ - Nat.size (m 6))
      (fun n => runsTo_sadInner ρ acc x₀ y₀ m₀ h8 n)
      (fun m _ => le_trans (Nat.sub_le _ _) (Nat.size_le_size hρ))).mono
        (by omega)).strengthen (fun m hm => hm.1)
  · exact runsTo_of_false hwf (fun m hm => hρ hm.2)

/-- The inner loop, carrying a proposition that does not mention the memory.  This is the rule of
constancy, in the form `RAM.Small.runsTo_clearRegs_const` has it: the caller needs the facts it
knew before the loop after the loop as well. -/
theorem runsTo_sadInnerLoopK (ρ acc x₀ y₀ rem₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1) (K : Prop) :
    RunsTo (whileNz 5 sadInner) (fun m => (SadIn ρ acc x₀ y₀ m₀ m ∧ ρ ≤ rem₀) ∧ K)
      (fun m' => (SadIn ρ acc x₀ y₀ m₀ m' ∧ m' 5 = 0) ∧ K) (Nat.size rem₀ * 7 + 1) := by
  by_cases hK : K
  · exact ((runsTo_sadInnerLoop ρ acc x₀ y₀ rem₀ m₀ h8).weaken
      (fun m hm => ⟨hm, hK⟩)).strengthen (fun m hm => hm.1)
  · exact runsTo_of_false (runsTo_sadInnerLoop ρ acc x₀ y₀ rem₀ m₀ h8).wf
      (fun m hm => hK hm.2)

/-- One round of the outer loop: it preserves the invariant and lowers `Nat.size rem`. -/
theorem runsTo_sadOuter (xz yz rem₀ x₀ y₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1)
    (hxz : xz ∉ sadBlock) (hyz : yz ∉ sadBlock) (hx : m₀ xz = x₀) (hy : m₀ yz = y₀)
    (hx1 : 1 ≤ x₀) (n : ℕ) :
    RunsTo (sadOuter xz yz)
      (fun m => SadOut rem₀ x₀ y₀ m₀ m ∧ m 5 ≠ 0 ∧ Nat.size (m 2) = n)
      (fun m' => SadOut rem₀ x₀ y₀ m₀ m' ∧ Nat.size (m' 2) < n)
      (Nat.size rem₀ * 7 + 10) := by
  have hxz' := hxz
  have hyz' := hyz
  simp only [sadBlock, List.mem_cons, List.not_mem_nil, or_false, not_or] at hxz' hyz'
  obtain ⟨x2, x3, x5, x6, x7, x9⟩ := hxz'
  obtain ⟨y2, y3, y5, y6, y7, y9⟩ := hyz'
  refine RunsTo.mono
    (T := 1 + (1 + (1 + (1 + (1 + ((Nat.size rem₀ * 7 + 1) + (1 + (1 + (1 + 1))))))))) ?_
    (by omega)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  set K : Prop :=
    SadOut rem₀ x₀ y₀ m₀ m₁ ∧ m₁ 5 ≠ 0 ∧ Nat.size (m₁ 2) = n with hK
  -- the five instructions that set up one round
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 ∧ m 3 = m₁ 3 ∧ m 6 = x₀ ∧
      Outside sadBlock m₀ m) ∧ K)
    (runsTo_copyTo 6 xz (fun m hm => ?_)) ?_
  · obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨-, -, -, -, iout⟩ := hpre.1
    refine ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 6)],
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 6)],
      by rw [Mem.update_self, iout xz hxz, hx],
      iout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 ∧ m 3 = m₁ 3 ∧ m 6 = x₀ ∧ m 7 = y₀ ∧
      Outside sadBlock m₀ m) ∧ K)
    (runsTo_copyTo 7 yz (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, eout⟩, hpre⟩ := hm
    refine ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 7)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 7)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 7)]; exact e6,
      by rw [Mem.update_self, eout yz hyz, hy],
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 ∧ m 3 = m₁ 3 ∧ m 6 = x₀ ∧ m 7 = y₀ ∧
      m 9 = x₀ + x₀ ∧ Outside sadBlock m₀ m) ∧ K)
    (runsTo_addTo 9 6 6 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 9)]; exact e6,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 9)]; exact e7,
      by rw [Mem.update_self, e6],
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 ∧ m 3 = m₁ 3 ∧ m 6 = x₀ ∧ m 7 = y₀ ∧
      m 9 = (x₀ + x₀) - m₁ 2 ∧ Outside sadBlock m₀ m) ∧ K)
    (runsTo_subTo 9 9 2 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, e9, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 9)]; exact e6,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 9)]; exact e7,
      by rw [Mem.update_self, e9, e2],
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq
    (mid := fun m => (SadIn (m₁ 2) (m₁ 3) x₀ y₀ m₀ m ∧ m₁ 2 ≤ rem₀) ∧ K)
    (runsTo_subTo 5 8 9 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, e9, eout⟩, hpre⟩ := hm
    obtain ⟨j2, j3, j9, j5, jout⟩ := hpre.1
    have hne : m₁ 5 ≠ 0 := hpre.2.1
    have hxρ : x₀ ≤ m₁ 2 := by omega
    have hm8 : m 8 = 1 := by rw [eout 8 (by decide), h8]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, j2⟩, hpre⟩
    · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5)]; exact e2
    · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 5)]; exact e3
    · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5)]; omega
    · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5)]; omega
    · rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5),
        Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 5), e6, e7, mul_comm]
    · rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5),
        Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 5), e6, e9]
    · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5), hm8]
    · exact eout.upd (by decide) _
  -- the inner loop
  refine RunsTo.seq (mid := fun m => (SadIn (m₁ 2) (m₁ 3) x₀ y₀ m₀ m ∧ m 5 = 0) ∧ K)
    (runsTo_sadInnerLoopK (m₁ 2) (m₁ 3) x₀ y₀ rem₀ m₀ h8 K) ?_
  -- the four instructions that finish the round
  refine runsTo_of_pointwise (fun m₂ => ?_)
  set K₂ : Prop := (SadIn (m₁ 2) (m₁ 3) x₀ y₀ m₀ m₂ ∧ m₂ 5 = 0) ∧ K with hK₂
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 - m₂ 6 ∧ m 3 = m₁ 3 ∧ m 6 = m₂ 6 ∧
      m 7 = m₂ 7 ∧ Outside sadBlock m₀ m) ∧ K₂)
    (runsTo_subTo 2 2 6 (fun m hm => ?_)) ?_
  · obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨i2, i3, -, -, -, -, -, iout⟩ := hpre.1.1
    exact ⟨⟨by rw [Mem.update_self, i2],
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 2)]; exact i3,
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 2)],
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 2)],
      iout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 - m₂ 6 ∧ m 3 = m₁ 3 + m₂ 7 ∧ m 6 = m₂ 6 ∧
      m 7 = m₂ 7 ∧ Outside sadBlock m₀ m) ∧ K₂)
    (runsTo_addTo 3 3 7 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3)]; exact e2,
      by rw [Mem.update_self, e3, e7],
      by rw [Mem.update_of_ne _ _ (by omega : (6:ℕ) ≠ 3)]; exact e6,
      by rw [Mem.update_of_ne _ _ (by omega : (7:ℕ) ≠ 3)]; exact e7,
      eout.upd (by decide) _⟩, hpre⟩
  refine RunsTo.seq (mid := fun m => (m 2 = m₁ 2 - m₂ 6 ∧ m 3 = m₁ 3 + m₂ 7 ∧
      m 9 = x₀ - (m₁ 2 - m₂ 6) ∧ Outside sadBlock m₀ m) ∧ K₂)
    (runsTo_subTo 9 xz 2 (fun m hm => ?_)) ?_
  · obtain ⟨⟨e2, e3, e6, e7, eout⟩, hpre⟩ := hm
    exact ⟨⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_self, eout xz hxz, hx, e2],
      eout.upd (by decide) _⟩, hpre⟩
  refine runsTo_subTo 5 8 9 (fun m hm => ?_)
  obtain ⟨⟨e2, e3, e9, eout⟩, hpre⟩ := hm
  obtain ⟨⟨i2, i3, i6, i6', i67, i9, i5, iout⟩, izero⟩ := hpre.1
  obtain ⟨j2, jacc, j9, j5, jout⟩ := hpre.2.1
  have hn : Nat.size (m₁ 2) = n := hpre.2.2.2
  have hm8 : m 8 = 1 := by rw [eout 8 (by decide), h8]
  -- at the exit of the inner loop the test failed: `ρ < x + x`
  have hlt : m₁ 2 < m₂ 6 + m₂ 6 := by omega
  have hxle : m₂ 6 ≤ m₁ 2 := i6'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5), e2]
    omega
  · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 5),
      Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5), e3, e2]
    have hrw : rem₀ - (m₁ 2 - m₂ 6) = (rem₀ - m₁ 2) + m₂ 6 := by omega
    rw [hrw, add_mul, add_mul, ← jacc, ← i67]
  · rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5),
      Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5), e9, e2]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5), hm8]
  · exact eout.upd (by decide) _
  · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5), e2, ← hn]
    exact size_sub_lt hxle hlt

/-- **The shift-and-subtract loop.**  From `rem = rem₀`, `acc = 0` it ends with `rem < x₀` and
`acc * x₀ = (rem₀ - rem) * y₀`, in `Nat.size rem₀ * (Nat.size rem₀ * 7 + 12) + 1` steps. -/
theorem runsTo_sadLoop (xz yz rem₀ x₀ y₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1)
    (hxz : xz ∉ sadBlock) (hyz : yz ∉ sadBlock) (hx : m₀ xz = x₀) (hy : m₀ yz = y₀)
    (hx1 : 1 ≤ x₀) :
    RunsTo (sadLoop xz yz) (fun m => SadOut rem₀ x₀ y₀ m₀ m)
      (fun m' => SadOut rem₀ x₀ y₀ m₀ m' ∧ m' 5 = 0)
      (Nat.size rem₀ * (Nat.size rem₀ * 7 + 12) + 1) := by
  refine (runsTo_whileNz (μ := fun m => Nat.size (m 2))
    (fun n => runsTo_sadOuter xz yz rem₀ x₀ y₀ m₀ h8 hxz hyz hx hy hx1 n)
    (fun m hm => Nat.size_le_size hm.1)).mono (le_of_eq (by ring))

/-- The shift-and-subtract loop, carrying a proposition that does not mention the memory. -/
theorem runsTo_sadLoopK (xz yz rem₀ x₀ y₀ : ℕ) (m₀ : Mem) (h8 : m₀ 8 = 1)
    (hxz : xz ∉ sadBlock) (hyz : yz ∉ sadBlock) (hx : m₀ xz = x₀) (hy : m₀ yz = y₀)
    (hx1 : 1 ≤ x₀) (K : Prop) :
    RunsTo (sadLoop xz yz) (fun m => SadOut rem₀ x₀ y₀ m₀ m ∧ K)
      (fun m' => (SadOut rem₀ x₀ y₀ m₀ m' ∧ m' 5 = 0) ∧ K)
      (Nat.size rem₀ * (Nat.size rem₀ * 7 + 12) + 1) := by
  by_cases hK : K
  · exact ((runsTo_sadLoop xz yz rem₀ x₀ y₀ m₀ h8 hxz hyz hx hy hx1).weaken
      (fun m hm => ⟨hm, hK⟩)).strengthen (fun m hm => hm.1)
  · exact runsTo_of_false (runsTo_sadLoop xz yz rem₀ x₀ y₀ m₀ h8 hxz hyz hx hy hx1).wf
      (fun m hm => hK hm.2)

/-- The loop is a well-formed program.  (Read off a harmless instance of the loop: the
specification's hypotheses hold for the constant memory `1`.) -/
theorem wf_sadLoop (xz yz : ℕ) (hxz : xz ∉ sadBlock) (hyz : yz ∉ sadBlock) :
    Wf (sadLoop xz yz) :=
  (runsTo_sadLoop xz yz 0 1 1 (fun _ => 1) rfl hxz hyz rfl rfl (by omega)).wf

/-- The shift-and-subtract loop in the form a caller uses it: the three facts about the reference
memory sit in the precondition, so that the caller need not prove them before the call. -/
theorem runsTo_sadLoopK' (xz yz rem₀ x₀ y₀ : ℕ) (m₀ : Mem)
    (hxz : xz ∉ sadBlock) (hyz : yz ∉ sadBlock) (hx1 : 1 ≤ x₀) (K : Prop) :
    RunsTo (sadLoop xz yz)
      (fun m => SadOut rem₀ x₀ y₀ m₀ m ∧ (m₀ 8 = 1 ∧ m₀ xz = x₀ ∧ m₀ yz = y₀) ∧ K)
      (fun m' => (SadOut rem₀ x₀ y₀ m₀ m' ∧ m' 5 = 0) ∧
        (m₀ 8 = 1 ∧ m₀ xz = x₀ ∧ m₀ yz = y₀) ∧ K)
      (Nat.size rem₀ * (Nat.size rem₀ * 7 + 12) + 1) := by
  by_cases h : m₀ 8 = 1 ∧ m₀ xz = x₀ ∧ m₀ yz = y₀
  · exact runsTo_sadLoopK xz yz rem₀ x₀ y₀ m₀ h.1 hxz hyz h.2.1 h.2.2 hx1 _
  · exact runsTo_of_false (wf_sadLoop xz yz hxz hyz) (fun m hm => h hm.2.1)

/-! ## Multiplication -/

/-- Multiplication of the registers `2` and `4` into register `5`.  The prelude moves the
multiplier `b` into the remainder register `2` and the multiplicand `a` into register `4`, which
is the `y₀` of the loop, sets the constant `1` — which is also the `x₀` of the loop — and computes
the first test; the loop then runs, and the accumulator is the answer. -/
def mulCore : Program :=
  seq (assign 8 1) (seq (copyTo 9 2) (seq (copyTo 2 4) (seq (copyTo 4 9) (seq (assign 3 0)
    (seq (subTo 9 8 2) (seq (subTo 5 8 9) (seq (sadLoop 8 4) (copyTo 5 3))))))))

/-- The registers `mulCore` writes. -/
def mulBlock : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9]

/-- **Multiplication.**  `mulCore` leaves `R2 * R4` in register `5` in
`Nat.size (R4) * (Nat.size (R4) * 7 + 12) + 9` steps. -/
theorem runsTo_mulCore (m₀ : Mem) :
    RunsTo mulCore (fun m => m = m₀)
      (fun m' => m' 5 = m₀ 2 * m₀ 4 ∧ Outside mulBlock m₀ m')
      (Nat.size (m₀ 4) * (Nat.size (m₀ 4) * 7 + 12) + 9) := by
  set a := m₀ 2 with ha
  set b := m₀ 4 with hb
  refine RunsTo.mono
    (T := 1 + (1 + (1 + (1 + (1 + (1 + (1 +
      ((Nat.size b * (Nat.size b * 7 + 12) + 1) + 1)))))))) ?_ (by omega)
  -- the prelude
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 4 = b ∧ m 8 = 1 ∧ Outside mulBlock m₀ m)
    (runsTo_assign 8 1 (fun m hm => ?_)) ?_
  · subst hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 8)],
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 8)],
      Mem.update_self _ _ _, (Outside.refl _ _).upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 4 = b ∧ m 8 = 1 ∧ m 9 = a ∧
      Outside mulBlock m₀ m)
    (runsTo_copyTo 9 2 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e4, e8, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 9)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 9)]; exact e8,
      by rw [Mem.update_self, e2], eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = b ∧ m 4 = b ∧ m 8 = 1 ∧ m 9 = a ∧
      Outside mulBlock m₀ m)
    (runsTo_copyTo 2 4 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e4, e8, e9, eout⟩ := hm
    exact ⟨by rw [Mem.update_self, e4],
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 2)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 2)]; exact e8,
      by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 2)]; exact e9,
      eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = b ∧ m 4 = a ∧ m 8 = 1 ∧ Outside mulBlock m₀ m)
    (runsTo_copyTo 4 9 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e4, e8, e9, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 4)]; exact e2,
      by rw [Mem.update_self, e9],
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 4)]; exact e8,
      eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = b ∧ m 3 = 0 ∧ m 4 = a ∧ m 8 = 1 ∧
      Outside mulBlock m₀ m)
    (runsTo_assign 3 0 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e4, e8, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3)]; exact e2,
      Mem.update_self _ _ _,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 3)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 3)]; exact e8,
      eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = b ∧ m 3 = 0 ∧ m 4 = a ∧ m 8 = 1 ∧ m 9 = 1 - b ∧
      Outside mulBlock m₀ m)
    (runsTo_subTo 9 8 2 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e3, e4, e8, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 9)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 9)]; exact e8,
      by rw [Mem.update_self, e8, e2], eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = b ∧ m 3 = 0 ∧ m 4 = a ∧ m 8 = 1 ∧ m 9 = 1 - b ∧
      m 5 = 1 - (1 - b) ∧ Outside mulBlock m₀ m)
    (runsTo_subTo 5 8 9 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e3, e4, e8, e9, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 5)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 5)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 5)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 5)]; exact e8,
      by rw [Mem.update_of_ne _ _ (by omega : (9:ℕ) ≠ 5)]; exact e9,
      by rw [Mem.update_self, e8, e9], eout.upd (by decide) _⟩
  -- the loop, with the reference memory taken at its entry
  refine runsTo_of_pointwise (fun m₂ => ?_)
  set K : Prop := m₂ 2 = b ∧ m₂ 3 = 0 ∧ m₂ 4 = a ∧ m₂ 8 = 1 ∧ m₂ 9 = 1 - b ∧
    m₂ 5 = 1 - (1 - b) ∧ Outside mulBlock m₀ m₂ with hK
  refine RunsTo.seq (mid := fun m => (SadOut b 1 a m₂ m ∧ m 5 = 0) ∧
      (m₂ 8 = 1 ∧ m₂ 8 = 1 ∧ m₂ 4 = a) ∧ K) ?_ ?_
  · refine (runsTo_sadLoopK' 8 4 b 1 a m₂ (by decide) (by decide) (by omega) K).strengthen
      (fun m hm => ?_)
    obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨p2, p3, p4, p8, p9, p5, pout⟩ := id hpre
    exact ⟨⟨by omega, by rw [p3, p2]; simp, by rw [p9, p2], by rw [p5, p9], Outside.refl _ _⟩,
      ⟨p8, p8, p4⟩, hpre⟩
  refine runsTo_copyTo 5 3 (fun m hm => ?_)
  obtain ⟨⟨⟨j2, jacc, j9, j5, jout⟩, jz⟩, -, hpre⟩ := hm
  obtain ⟨p2, p3, p4, p8, p9, p5, pout⟩ := id hpre
  have hrem : m 2 = 0 := by omega
  have hval : m 3 = b * a := by
    have h := jacc
    rw [hrem] at h
    simpa using h
  refine ⟨by rw [Mem.update_self, hval, mul_comm], fun z hz => ?_⟩
  have hz' : z ∉ sadBlock := by
    simp only [mulBlock, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp only [sadBlock, List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  rw [Mem.update_of_ne _ _ (by
    simp only [mulBlock, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    omega : z ≠ 5), jout z hz', pout z hz]

end Arith

/-! ## Multiplication as a clean routine, and as a `PolyFun` -/

namespace Small

/-- The time bound of the multiplication routine, as a function of the input size. -/
def mulTime (n : ℕ) : ℕ := 19 * (n + 1) ^ 2

theorem polyBound_mulTime : PolyBound mulTime := ⟨19, 2, fun _ => le_refl _⟩

/-- The multiplication routine, packaged for the top-level convention. -/
def mulProg : Program :=
  seq Arith.mulCore (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch)))

theorem cleanCompute_mul : CleanCompute mulProg (fun p : ℕ × ℕ => p.1 * p.2) mulTime := by
  refine cleanCompute_binary_var (v := fun a b => a * b)
    (T := fun _ b => Nat.size b * (Nat.size b * 7 + 12) + 9)
    (S := Arith.mulBlock) (fun p => rfl) (fun m₀ => Arith.runsTo_mulCore m₀)
    (by decide) (fun a b => ?_)
  have hZ : Nat.size b ≤ Enc.size ((a, b) : ℕ × ℕ) := by
    have h : Nat.size b + 2 ≤ Enc.size ((a, b) : ℕ × ℕ) := size_snd_nat ((a, b) : ℕ × ℕ)
    omega
  set n := Enc.size ((a, b) : ℕ × ℕ) with hn
  set Z := Nat.size b with hZdef
  show Z * (Z * 7 + 12) + 9 + 10 ≤ 19 * (n + 1) ^ 2
  have h1 : Z * (Z * 7 + 12) = 7 * (Z * Z) + 12 * Z := by ring
  have h2 : Z * Z ≤ n * n := Nat.mul_le_mul hZ hZ
  have h3 : 12 * Z ≤ 12 * n := Nat.mul_le_mul_left _ hZ
  have h4 : 7 * (Z * Z) ≤ 7 * (n * n) := Nat.mul_le_mul_left _ h2
  have h5 : 19 * (n + 1) ^ 2 = 19 * (n * n) + 38 * n + 19 := by ring
  omega

theorem polyTimeClean_mul : PolyTimeClean (fun p : ℕ × ℕ => p.1 * p.2) :=
  ⟨mulProg, mulTime, polyBound_mulTime, cleanCompute_mul⟩

end Small

/-- The bit length of a product is at most the sum of the bit lengths. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  refine Nat.size_le.2 ?_
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h1 : a < 2 ^ Nat.size a := Nat.lt_size_self a
  have h2 : b < 2 ^ Nat.size b := Nat.lt_size_self b
  calc a * b < 2 ^ Nat.size a * 2 ^ Nat.size b := by
        exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
    _ = 2 ^ (Nat.size a + Nat.size b) := by rw [pow_add]

theorem sizeBound_mul : SizeBound (fun p : ℕ × ℕ => p.1 * p.2) := by
  refine ⟨3, 1, fun p => ?_⟩
  show Enc.size (p.1 * p.2) ≤ 3 * (Enc.size p + 1) ^ 1
  have h1 := size_fst_nat p
  have h2 := size_snd_nat p
  have h3 : Nat.size (p.1 * p.2) ≤ Nat.size p.1 + Nat.size p.2 := size_mul_le _ _
  have h4 : Enc.size (p.1 * p.2) = Nat.size (p.1 * p.2) + 2 := Small.size_nat _
  have h5 : 3 * (Enc.size p + 1) ^ 1 = 3 * Enc.size p + 3 := by ring
  omega

/-- **Multiplication is a `PolyFun`.** -/
theorem polyFun_mul : PolyFun (fun p : ℕ × ℕ => p.1 * p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_mul sizeBound_mul

/-- The product of two `PolyFun`s. -/
theorem PolyFun.mul {α : Type*} [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a * g a) := hf.op₂ hg polyFun_mul

end RAM
