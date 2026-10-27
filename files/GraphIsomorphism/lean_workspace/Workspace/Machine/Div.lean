import Workspace.Machine.Mul

/-!
# Division with remainder

Division is the loop of `Workspace/Machine/Mul.lean` with the roles of the two operands
exchanged: with `x₀ = b`, `y₀ = 1` and `rem₀ = a` the loop subtracts from `a` the multiples of
`b` by the powers of two, largest first, and counts them in the accumulator.  It ends with
`rem < b` and `acc * b = a - rem`, that is, with the quotient in the accumulator and the
remainder in the remainder register.

The machine has one register for `a` and one for `b`, and Lean's convention at `b = 0` is
`a / 0 = 0` and `a % 0 = a`.  So the routine begins with a conditional on the register holding
`b`: the zero branch sets the accumulator to zero and leaves the remainder register alone, which
is exactly Lean's convention.

The quotient and the remainder are computed by the *same* program `divModCore`, which leaves the
quotient in register `3` and the remainder in register `2`; the two routines differ only in which
of them they copy into the answer register `5`.  A pair `(a / b, a % b)` is then assembled with
`RAM.PolyFun.pair`, because `RAM.Small.cleanCompute_binary_var` packages a routine whose answer
is a single register.

## Main results

* `RAM.Arith.runsTo_divModCore`: quotient and remainder of the registers `2` and `4`;
* `RAM.polyFun_div`, `RAM.polyFun_mod`, `RAM.polyFun_divMod`, `RAM.PolyFun.div`,
  `RAM.PolyFun.mod`.
-/

namespace RAM
namespace Arith

/-- Uniqueness of quotient and remainder, in the form the loop invariant produces it. -/
theorem div_mod_of_eq {a b q r : ℕ} (hb : 0 < b) (hlt : r < b) (h : a = r + q * b) :
    a / b = q ∧ a % b = r := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hlt, zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

/-- The registers the division routine writes.  Register `4`, which holds the divisor, is not
among them. -/
def divBlock : List ℕ := [2, 3, 5, 6, 7, 8, 9]

/-- The division loop for a nonzero divisor: set the constant `1` and the accumulator, compute
the first test `b ≤ a`, and run the shift-and-subtract loop with `x₀ = b`, `y₀ = 1`. -/
def divCoreMain : Program :=
  seq (assign 8 1) (seq (assign 3 0) (seq (subTo 9 4 2) (seq (subTo 5 8 9) (sadLoop 4 8))))

/-- **Division with remainder, nonzero divisor.**  `divCoreMain` leaves the quotient in register
`3` and the remainder in register `2`. -/
theorem runsTo_divMain (m₀ : Mem) (hb : m₀ 4 ≠ 0) :
    RunsTo divCoreMain (fun m => m = m₀)
      (fun m' => m' 3 = m₀ 2 / m₀ 4 ∧ m' 2 = m₀ 2 % m₀ 4 ∧ Outside divBlock m₀ m')
      (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 5) := by
  set a := m₀ 2 with ha
  set b := m₀ 4 with hbdef
  refine RunsTo.mono
    (T := 1 + (1 + (1 + (1 + (Nat.size a * (Nat.size a * 7 + 12) + 1))))) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 4 = b ∧ m 8 = 1 ∧ Outside divBlock m₀ m)
    (runsTo_assign 8 1 (fun m hm => ?_)) ?_
  · subst hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 8)],
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 8)],
      Mem.update_self _ _ _, (Outside.refl _ _).upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 3 = 0 ∧ m 4 = b ∧ m 8 = 1 ∧
      Outside divBlock m₀ m)
    (runsTo_assign 3 0 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e4, e8, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3)]; exact e2,
      Mem.update_self _ _ _,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 3)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 3)]; exact e8,
      eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 3 = 0 ∧ m 4 = b ∧ m 8 = 1 ∧ m 9 = b - a ∧
      Outside divBlock m₀ m)
    (runsTo_subTo 9 4 2 (fun m hm => ?_)) ?_
  · obtain ⟨e2, e3, e4, e8, eout⟩ := hm
    exact ⟨by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 9)]; exact e2,
      by rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 9)]; exact e3,
      by rw [Mem.update_of_ne _ _ (by omega : (4:ℕ) ≠ 9)]; exact e4,
      by rw [Mem.update_of_ne _ _ (by omega : (8:ℕ) ≠ 9)]; exact e8,
      by rw [Mem.update_self, e4, e2], eout.upd (by decide) _⟩
  refine RunsTo.seq (mid := fun m => m 2 = a ∧ m 3 = 0 ∧ m 4 = b ∧ m 8 = 1 ∧ m 9 = b - a ∧
      m 5 = 1 - (b - a) ∧ Outside divBlock m₀ m)
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
  set K : Prop := m₂ 2 = a ∧ m₂ 3 = 0 ∧ m₂ 4 = b ∧ m₂ 8 = 1 ∧ m₂ 9 = b - a ∧
    m₂ 5 = 1 - (b - a) ∧ Outside divBlock m₀ m₂ with hK
  refine ((runsTo_sadLoopK' 4 8 a b 1 m₂ (by decide) (by decide) (by omega) K).conseq
    (fun m hm => ?_) (fun m' hm' => ?_) (le_refl _))
  · obtain ⟨rfl, hpre⟩ := hm
    obtain ⟨p2, p3, p4, p8, p9, p5, pout⟩ := id hpre
    exact ⟨⟨by omega, by rw [p3, p2]; simp, by rw [p9, p2], by rw [p5, p9], Outside.refl _ _⟩,
      ⟨p8, p4, p8⟩, hpre⟩
  · obtain ⟨⟨⟨j2, jacc, j9, j5, jout⟩, jz⟩, -, hpre⟩ := hm'
    obtain ⟨p2, p3, p4, p8, p9, p5, pout⟩ := id hpre
    have hlt : m' 2 < b := by omega
    have hsum : a = m' 2 + m' 3 * b := by rw [jacc]; omega
    obtain ⟨hq, hr⟩ := div_mod_of_eq (by omega : 0 < b) hlt hsum
    refine ⟨hq.symm, hr.symm, fun z hz => ?_⟩
    have hz' : z ∉ sadBlock := by
      simp only [divBlock, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp only [sadBlock, List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega
    rw [jout z hz', pout z hz]

/-- The division loop is a well-formed program. -/
theorem wf_divCoreMain : Wf divCoreMain :=
  (runsTo_divMain (fun _ => 1) (by norm_num)).wf

/-- Quotient and remainder, with Lean's convention at zero: the conditional on register `4`
sets the quotient to zero and leaves the remainder register alone when the divisor is zero. -/
def divModCore : Program := ifz 4 divCoreMain (assign 3 0)

/-- **Division with remainder.**  `divModCore` leaves `R2 / R4` in register `3` and `R2 % R4`
in register `2`. -/
theorem runsTo_divModCore (m₀ : Mem) :
    RunsTo divModCore (fun m => m = m₀)
      (fun m' => m' 3 = m₀ 2 / m₀ 4 ∧ m' 2 = m₀ 2 % m₀ 4 ∧ Outside divBlock m₀ m')
      (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 8) := by
  have hP : RunsTo divCoreMain (fun m => m = m₀ ∧ m 4 ≠ 0)
      (fun m' => m' 3 = m₀ 2 / m₀ 4 ∧ m' 2 = m₀ 2 % m₀ 4 ∧ Outside divBlock m₀ m')
      (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 5) := by
    by_cases hb : m₀ 4 = 0
    · exact runsTo_of_false wf_divCoreMain (fun m hm => hm.2 (by rw [hm.1]; exact hb))
    · exact (runsTo_divMain m₀ hb).strengthen (fun m hm => hm.1)
  have hQ : RunsTo (assign 3 0) (fun m => m = m₀ ∧ m 4 = 0)
      (fun m' => m' 3 = m₀ 2 / m₀ 4 ∧ m' 2 = m₀ 2 % m₀ 4 ∧ Outside divBlock m₀ m') 1 := by
    refine runsTo_assign 3 0 (fun m hm => ?_)
    obtain ⟨rfl, hz⟩ := hm
    rw [hz]
    exact ⟨by rw [Mem.update_self, Nat.div_zero],
      by rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3), Nat.mod_zero],
      (Outside.refl _ _).upd (by decide) _⟩
  exact (hP.ifz hQ).mono (by omega)

/-- The quotient, in the answer register `5`. -/
def divCore : Program := seq divModCore (copyTo 5 3)

/-- The remainder, in the answer register `5`. -/
def modCore : Program := seq divModCore (copyTo 5 2)

theorem runsTo_divCore (m₀ : Mem) :
    RunsTo divCore (fun m => m = m₀)
      (fun m' => m' 5 = m₀ 2 / m₀ 4 ∧ Outside divBlock m₀ m')
      (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 9) := by
  refine RunsTo.mono
    (T := (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 8) + 1) ?_ (by omega)
  refine RunsTo.seq (runsTo_divModCore m₀) (runsTo_copyTo 5 3 (fun m hm => ?_))
  obtain ⟨e3, e2, eout⟩ := hm
  exact ⟨by rw [Mem.update_self, e3], eout.upd (by decide) _⟩

theorem runsTo_modCore (m₀ : Mem) :
    RunsTo modCore (fun m => m = m₀)
      (fun m' => m' 5 = m₀ 2 % m₀ 4 ∧ Outside divBlock m₀ m')
      (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 9) := by
  refine RunsTo.mono
    (T := (Nat.size (m₀ 2) * (Nat.size (m₀ 2) * 7 + 12) + 8) + 1) ?_ (by omega)
  refine RunsTo.seq (runsTo_divModCore m₀) (runsTo_copyTo 5 2 (fun m hm => ?_))
  obtain ⟨e3, e2, eout⟩ := hm
  exact ⟨by rw [Mem.update_self, e2], eout.upd (by decide) _⟩

end Arith

/-! ## Division as a clean routine, and as a `PolyFun` -/

namespace Small

/-- The step bound of the division routines, in the size of the input. -/
theorem div_time_le (a b : ℕ) :
    Nat.size a * (Nat.size a * 7 + 12) + 9 + 10 ≤ mulTime (Enc.size ((a, b) : ℕ × ℕ)) := by
  have hZ : Nat.size a ≤ Enc.size ((a, b) : ℕ × ℕ) := by
    have h : Nat.size a + 2 ≤ Enc.size ((a, b) : ℕ × ℕ) := size_fst_nat ((a, b) : ℕ × ℕ)
    omega
  set n := Enc.size ((a, b) : ℕ × ℕ) with hn
  set Z := Nat.size a with hZdef
  show Z * (Z * 7 + 12) + 9 + 10 ≤ 19 * (n + 1) ^ 2
  have h1 : Z * (Z * 7 + 12) = 7 * (Z * Z) + 12 * Z := by ring
  have h2 : Z * Z ≤ n * n := Nat.mul_le_mul hZ hZ
  have h3 : 12 * Z ≤ 12 * n := Nat.mul_le_mul_left _ hZ
  have h4 : 7 * (Z * Z) ≤ 7 * (n * n) := Nat.mul_le_mul_left _ h2
  have h5 : 19 * (n + 1) ^ 2 = 19 * (n * n) + 38 * n + 19 := by ring
  omega

/-- The quotient routine, packaged for the top-level convention. -/
def divProg : Program :=
  seq Arith.divCore (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch)))

/-- The remainder routine, packaged for the top-level convention. -/
def modProg : Program :=
  seq Arith.modCore (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch)))

theorem cleanCompute_div : CleanCompute divProg (fun p : ℕ × ℕ => p.1 / p.2) mulTime :=
  cleanCompute_binary_var (v := fun a b => a / b)
    (T := fun a _ => Nat.size a * (Nat.size a * 7 + 12) + 9)
    (S := Arith.divBlock) (fun p => rfl) (fun m₀ => Arith.runsTo_divCore m₀)
    (by decide) div_time_le

theorem cleanCompute_mod : CleanCompute modProg (fun p : ℕ × ℕ => p.1 % p.2) mulTime :=
  cleanCompute_binary_var (v := fun a b => a % b)
    (T := fun a _ => Nat.size a * (Nat.size a * 7 + 12) + 9)
    (S := Arith.divBlock) (fun p => rfl) (fun m₀ => Arith.runsTo_modCore m₀)
    (by decide) div_time_le

theorem polyTimeClean_div : PolyTimeClean (fun p : ℕ × ℕ => p.1 / p.2) :=
  ⟨divProg, mulTime, polyBound_mulTime, cleanCompute_div⟩

theorem polyTimeClean_mod : PolyTimeClean (fun p : ℕ × ℕ => p.1 % p.2) :=
  ⟨modProg, mulTime, polyBound_mulTime, cleanCompute_mod⟩

end Small

/-- **Division is a `PolyFun`.** -/
theorem polyFun_div : PolyFun (fun p : ℕ × ℕ => p.1 / p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_div
    (sizeBound_binop_le (fun _ => le_trans (Nat.div_le_self _ _) (le_max_left _ _)))

/-- **The remainder is a `PolyFun`.** -/
theorem polyFun_mod : PolyFun (fun p : ℕ × ℕ => p.1 % p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_mod
    (sizeBound_binop_le (fun _ => le_trans (Nat.mod_le _ _) (le_max_left _ _)))

/-- **Division with remainder**, as one function into a pair. -/
theorem polyFun_divMod : PolyFun (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2)) :=
  polyFun_div.pair polyFun_mod

/-- The quotient of two `PolyFun`s. -/
theorem PolyFun.div {α : Type*} [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a / g a) := hf.op₂ hg polyFun_div

/-- The remainder of two `PolyFun`s. -/
theorem PolyFun.mod {α : Type*} [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a % g a) := hf.op₂ hg polyFun_mod

end RAM
