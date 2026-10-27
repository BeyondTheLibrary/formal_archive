import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Basic

/-!
# A random access machine (RAM)

This file fixes the machine model in which every running-time claim of this formalization is
stated.  Babai's paper, like the rest of the algorithms literature, never fixes a model: it
relies on the convention that any model polynomially equivalent to multitape Turing machines
will do.  We fix a *successor/addition RAM with unit cost*, in the style of

* S. A. Cook and R. A. Reckhow, *Time bounded random access machines*,
  J. Comput. System Sci. **7** (1973) 354-375;
* A. V. Aho, J. E. Hopcroft, J. D. Ullman, *The Design and Analysis of Computer Algorithms*,
  Addison-Wesley, 1974, Sec. 1.2 (the RAM and its uniform and logarithmic cost criteria).

## How this machine relates to the machines of those two references

Cook and Reckhow's RAM has an infinite sequence of registers `X_0, X_1, ...` holding integers,
an accumulator-free instruction set with load-constant, register-to-register addition and
subtraction, indirect addressing (`X_i ← X_{X_j}`, `X_{X_i} ← X_j`), a conditional transfer of
control (`TRA m if X_i > 0`), and a halt; each instruction costs one unit of time.  The machine
here is that machine with three inessential changes.

1. Registers hold natural numbers rather than integers, and subtraction is truncated
   (`Nat.sub`).  Every quantity the paper computes is a natural number, and truncated
   subtraction simulates the integer machine on the segment of a computation where all values
   are nonnegative; conversely sign bits can be carried in extra registers.  This changes
   running times by a constant factor only.
2. The conditional jump tests for zero (`jz`) rather than for positivity; the two are
   interdefinable in two instructions, so again only a constant factor is involved.
3. There is an explicit `copy` and a three-address `add`/`sub`, as in Aho-Hopcroft-Ullman's
   informal RAM code, rather than Cook and Reckhow's two-address form.  This is pure sugar.

Crucially, and exactly as in both references, **there is no multiplication, no division, no
shift and no bitwise instruction**.  This is what makes the unit-cost criterion legitimate: see
`RAM.mem_le_run` below.

## The cost measure

Running time is the number of executed instructions (`Aho-Hopcroft-Ullman`'s *uniform cost
criterion*, Sec. 1.3).  Taken literally on a machine with multiplication this measure is
unreasonable, because repeated squaring would build numbers of `2^T` bits in `T` steps and one
unit-cost step would hide an unbounded amount of work.  On the present instruction set
`RAM.mem_le_run` shows that after `T` steps every register holds a number below `2^T * B`,
where `B` bounds the initial contents and the constants of the program; so every register fits
in `T + log B + 1` bits, each step manipulates numbers of at most that many bits, and the
logarithmic-cost time (`RAM.logTime`, and `RAM.logTime_le` for the inequality) exceeds the
unit-cost time by at most the factor `T + log B + 2`.  Logarithmic-cost RAM time is polynomially
equivalent to multitape Turing machine time (Cook-Reckhow, Theorem 2), so on this instruction
set unit-cost RAM time, logarithmic-cost RAM time and Turing machine time are all polynomially
related, and "polynomial time" and "quasipolynomial time" mean the same thing in all three.

## Main definitions

* `RAM.Instr`, `RAM.Program`, `RAM.Config`;
* `RAM.step`, a total step function (halted configurations are its fixed points),
  `RAM.run P c k` its `k`-fold iterate, `RAM.Halted`;
* `RAM.mem_le_run`, the bit-growth lemma, and `RAM.mem_eq_run` the companion statement that
  no address above `2 ^ k * B` is touched in `k` steps;
* `RAM.logTime`, the logarithmic cost of a run, with `RAM.le_logTime` and `RAM.logTime_le`.
-/

namespace RAM

/-- The memory of the machine: register `a` holds the natural number `m a`.  All registers are
available; the input convention of `Workspace/Machine/Encoding.lean` puts zeros in all but
finitely many of them. -/
abbrev Mem := ℕ → ℕ

/-- `m.update a v` is the memory `m` with register `a` set to `v`. -/
def Mem.update (m : Mem) (a v : ℕ) : Mem := fun x => if x = a then v else m x

@[simp] theorem Mem.update_self (m : Mem) (a v : ℕ) : m.update a v a = v := by
  simp [Mem.update]

theorem Mem.update_of_ne (m : Mem) {a x : ℕ} (v : ℕ) (h : x ≠ a) : m.update a v x = m x := by
  simp [Mem.update, h]

/-- An instruction of the machine.  Register indices and constants are natural numbers;
jump targets are absolute positions in the program. -/
inductive Instr where
  /-- `R i ← c`. -/
  | const (i c : ℕ)
  /-- `R i ← R j`. -/
  | copy (i j : ℕ)
  /-- `R i ← R j + R k`. -/
  | add (i j k : ℕ)
  /-- `R i ← R j - R k`, truncated subtraction. -/
  | sub (i j k : ℕ)
  /-- `R i ← R (R j)`, indirect load. -/
  | load (i j : ℕ)
  /-- `R (R i) ← R j`, indirect store. -/
  | store (i j : ℕ)
  /-- `pc ← t`. -/
  | jump (t : ℕ)
  /-- `if R i = 0 then pc ← t else pc ← pc + 1`. -/
  | jz (i t : ℕ)
  /-- Stop. -/
  | halt
  deriving DecidableEq, Repr, Inhabited

/-- A program is a finite list of instructions.  The program counter indexes into it; a program
counter past the end of the list is a halted state, just like the `halt` instruction. -/
abbrev Program := List Instr

/-- A configuration: the program counter and the memory. -/
structure Config where
  pc : ℕ
  mem : Mem

/-- The effect of one (non-halting) instruction on a configuration. -/
def exec : Instr → Config → Config
  | .const i c, ⟨p, m⟩ => ⟨p + 1, m.update i c⟩
  | .copy i j, ⟨p, m⟩ => ⟨p + 1, m.update i (m j)⟩
  | .add i j k, ⟨p, m⟩ => ⟨p + 1, m.update i (m j + m k)⟩
  | .sub i j k, ⟨p, m⟩ => ⟨p + 1, m.update i (m j - m k)⟩
  | .load i j, ⟨p, m⟩ => ⟨p + 1, m.update i (m (m j))⟩
  | .store i j, ⟨p, m⟩ => ⟨p + 1, m.update (m i) (m j)⟩
  | .jump t, ⟨_, m⟩ => ⟨t, m⟩
  | .jz i t, ⟨p, m⟩ => ⟨if m i = 0 then t else p + 1, m⟩
  | .halt, c => c

/-- A configuration is halted when the program counter is past the end of the program or points
at a `halt` instruction. -/
def Halted (P : Program) (c : Config) : Prop :=
  P[c.pc]? = none ∨ P[c.pc]? = some Instr.halt

instance (P : Program) (c : Config) : Decidable (Halted P c) := by
  unfold Halted; infer_instance

/-- One step of the machine.  This is a *total* function: a halted configuration is a fixed
point of it, so that `run` below is defined for every number of steps. -/
def step (P : Program) (c : Config) : Config :=
  match h : P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some i => exec i c

theorem step_of_halted {P : Program} {c : Config} (h : Halted P c) : step P c = c := by
  unfold step
  rcases h with h | h <;> split <;> rename_i h' <;> simp_all

theorem step_of_get {P : Program} {c : Config} {i : Instr} (h : P[c.pc]? = some i)
    (hi : i ≠ Instr.halt) : step P c = exec i c := by
  unfold step
  split <;> rename_i h' <;> simp_all

/-- `run P c k` is the configuration after `k` steps from `c`. -/
def run (P : Program) (c : Config) : ℕ → Config
  | 0 => c
  | k + 1 => step P (run P c k)

@[simp] theorem run_zero (P : Program) (c : Config) : run P c 0 = c := rfl

@[simp] theorem run_succ (P : Program) (c : Config) (k : ℕ) :
    run P c (k + 1) = step P (run P c k) := rfl

theorem run_add (P : Program) (c : Config) (k l : ℕ) :
    run P c (k + l) = run P (run P c k) l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [run, ih, ← Nat.add_assoc]

/-- Once halted, always halted. -/
theorem halted_run_of_le {P : Program} {c : Config} {k l : ℕ} (hkl : k ≤ l)
    (h : Halted P (run P c k)) : Halted P (run P c l) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have hs : run P c (k + (d + 1)) = step P (run P c (k + d)) := by
        rw [← Nat.add_assoc]; rfl
      rw [hs, step_of_halted ih]
      exact ih

theorem run_of_halted {P : Program} {c : Config} {k l : ℕ} (hkl : k ≤ l)
    (h : Halted P (run P c k)) : run P c l = run P c k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => rfl
  | succ d ih =>
      have hstep : run P c (k + (d + 1)) = step P (run P c (k + d)) := by
        rw [← Nat.add_assoc]; rfl
      rw [hstep, ih, step_of_halted h]

/-- The machine halts starting from `c`. -/
def Halts (P : Program) (c : Config) : Prop := ∃ k, Halted P (run P c k)

/-- The running time: the number of executed instructions, that is, the first `k` at which the
machine is halted. -/
noncomputable def time (P : Program) (c : Config) (h : Halts P c) : ℕ := Nat.find h

theorem halted_run_time (P : Program) (c : Config) (h : Halts P c) :
    Halted P (run P c (time P c h)) := Nat.find_spec h

theorem time_le {P : Program} {c : Config} {h : Halts P c} {k : ℕ}
    (hk : Halted P (run P c k)) : time P c h ≤ k := Nat.find_le hk

/-! ## The bit-growth lemma -/

/-- The largest register index, constant or jump target occurring in an instruction. -/
def Instr.bound : Instr → ℕ
  | .const i c => max i c
  | .copy i j => max i j
  | .add i j k => max i (max j k)
  | .sub i j k => max i (max j k)
  | .load i j => max i j
  | .store i j => max i j
  | .jump t => t
  | .jz i t => max i t
  | .halt => 0

/-- The largest register index, constant or jump target occurring in a program. -/
def Program.bound (P : Program) : ℕ := (P.map Instr.bound).foldr max 0

theorem Instr.bound_le_program_bound {P : Program} {i : Instr} (h : i ∈ P) :
    i.bound ≤ P.bound := by
  induction P with
  | nil => cases h
  | cons a P ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp [Program.bound]
      · exact le_trans (ih h) (by simp [Program.bound])

theorem bound_of_get {P : Program} {n : ℕ} {i : Instr} (h : P[n]? = some i) :
    i.bound ≤ P.bound :=
  Instr.bound_le_program_bound (List.mem_of_getElem? h)

/-- One step at most doubles the largest value in memory, provided the program's constants are
themselves below that value.  This is where the absence of a multiplication instruction is
used. -/
theorem Mem.update_le {m : Mem} {x v C : ℕ} (hm : ∀ a, m a ≤ C) (hv : v ≤ 2 * C) (a : ℕ) :
    m.update x v a ≤ 2 * C := by
  unfold Mem.update
  split
  · exact hv
  · exact le_trans (hm a) (by omega)

theorem step_mem_le {P : Program} {c : Config} {C : ℕ} (hP : P.bound ≤ C)
    (h : ∀ a, c.mem a ≤ C) : ∀ a, (step P c).mem a ≤ 2 * C := by
  intro a
  have hC : ∀ x, c.mem x ≤ 2 * C := fun x => le_trans (h x) (by omega)
  unfold step
  split <;> rename_i hget
  · exact hC a
  · exact hC a
  · rename_i i _
    have hb : i.bound ≤ C := le_trans (bound_of_get hget) hP
    obtain ⟨p, m⟩ := c
    simp only at h hC hb ⊢
    cases i with
    | const x v =>
        simp only [Instr.bound] at hb
        exact Mem.update_le h (by omega) a
    | copy x y => exact Mem.update_le h (hC y) a
    | add x y z => exact Mem.update_le h (by have := h y; have := h z; omega) a
    | sub x y z => exact Mem.update_le h (by have := h y; omega) a
    | load x y => exact Mem.update_le h (hC (m y)) a
    | store x y => exact Mem.update_le h (hC y) a
    | jump t => exact hC a
    | jz x t => exact hC a
    | halt => exact hC a

/-- One step does not touch any address above the current bound. -/
theorem step_mem_eq {P : Program} {c : Config} {C : ℕ} (hP : P.bound ≤ C)
    (h : ∀ a, c.mem a ≤ C) : ∀ a, C < a → (step P c).mem a = c.mem a := by
  intro a ha
  unfold step
  split <;> rename_i hget
  · rfl
  · rfl
  · rename_i i _
    have hb : i.bound ≤ C := le_trans (bound_of_get hget) hP
    obtain ⟨p, m⟩ := c
    simp only at h hb ⊢
    cases i with
    | const x v =>
        simp only [Instr.bound] at hb
        exact Mem.update_of_ne _ _ (by omega)
    | copy x y =>
        simp only [Instr.bound] at hb
        exact Mem.update_of_ne _ _ (by omega)
    | add x y z =>
        simp only [Instr.bound] at hb
        exact Mem.update_of_ne _ _ (by omega)
    | sub x y z =>
        simp only [Instr.bound] at hb
        exact Mem.update_of_ne _ _ (by omega)
    | load x y =>
        simp only [Instr.bound] at hb
        exact Mem.update_of_ne _ _ (by omega)
    | store x y =>
        have := h x
        exact Mem.update_of_ne _ _ (by omega)
    | jump t => rfl
    | jz x t => rfl
    | halt => rfl

/-- **Bit growth.**  If every register of the initial configuration holds a value at most `B`,
and every constant, register index and jump target of `P` is at most `B`, then after `k` steps
every register holds a value at most `2 ^ k * B`.

This is the justification of the unit-cost measure: `k` steps of the machine produce numbers of
at most `k + Nat.size B` bits, so each unit-cost step hides at most `O(k + log B)` bit
operations, and unit-cost time is within a polynomial factor of logarithmic-cost time, hence of
Turing machine time. -/
theorem mem_le_run {P : Program} {c : Config} {B : ℕ} (hP : P.bound ≤ B)
    (h : ∀ a, c.mem a ≤ B) (k : ℕ) : ∀ a, (run P c k).mem a ≤ 2 ^ k * B := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hPk : P.bound ≤ 2 ^ k * B :=
        le_trans hP (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      intro a
      have := step_mem_le hPk ih a
      calc (run P c (k + 1)).mem a ≤ 2 * (2 ^ k * B) := this
        _ = 2 ^ (k + 1) * B := by ring

/-- Companion to `mem_le_run`: in `k` steps the machine touches no address above `2 ^ k * B`. -/
theorem mem_eq_run {P : Program} {c : Config} {B : ℕ} (hP : P.bound ≤ B)
    (h : ∀ a, c.mem a ≤ B) (k : ℕ) : ∀ a, 2 ^ k * B < a → (run P c k).mem a = c.mem a := by
  induction k with
  | zero => intro a _; rfl
  | succ k ih =>
      intro a ha
      have hPk : P.bound ≤ 2 ^ k * B :=
        le_trans hP (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
      have hmono : 2 ^ k * B ≤ 2 ^ (k + 1) * B := by
        have : (2:ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact Nat.mul_le_mul_right _ this
      have h1 : (run P c (k + 1)).mem a = (run P c k).mem a :=
        step_mem_eq hPk (mem_le_run hP h k) a (by omega)
      rw [h1, ih a (by omega)]

/-- Every register value after `k` steps fits in `k + Nat.size B` bits. -/
theorem size_mem_le_run {P : Program} {c : Config} {B : ℕ} (hP : P.bound ≤ B)
    (h : ∀ a, c.mem a ≤ B) (k a : ℕ) : Nat.size ((run P c k).mem a) ≤ k + Nat.size B := by
  have hle := mem_le_run hP h k a
  have : (2:ℕ) ^ k * B < 2 ^ (k + Nat.size B) := by
    have hB : B < 2 ^ Nat.size B := Nat.lt_size_self B
    calc (2:ℕ) ^ k * B < 2 ^ k * 2 ^ Nat.size B :=
          mul_lt_mul_of_pos_left hB (Nat.two_pow_pos k)
      _ = 2 ^ (k + Nat.size B) := by rw [pow_add]
  exact Nat.size_le.2 (lt_of_le_of_lt hle this)

/-- The register indices of an instruction are bounded by its `bound`, hence by the program's. -/
theorem size_index_le {P : Program} {B : ℕ} (hP : P.bound ≤ B) {i : Instr} {n : ℕ}
    (h : P[n]? = some i) : Nat.size i.bound ≤ Nat.size B :=
  Nat.size_le_size (le_trans (bound_of_get h) hP)

/-! ## Logarithmic cost

The logarithmic cost of a step is the number of bits of the largest value it touches, plus one
(so that every step costs at least one).  We only need the two inequalities relating it to the
unit cost; both are proved below. -/

/-- The logarithmic cost of one instruction: one plus the sum of the bit lengths of the
addresses and of the values it reads or writes (Aho-Hopcroft-Ullman, Sec. 1.3, with `l(i)`
taken to be `Nat.size i`). -/
def Instr.cost : Instr → Mem → ℕ
  | .const i c, _ => 1 + Nat.size i + Nat.size c
  | .copy i j, m => 1 + Nat.size i + Nat.size j + Nat.size (m j)
  | .add i j k, m => 1 + Nat.size i + Nat.size j + Nat.size k + Nat.size (m j) + Nat.size (m k)
  | .sub i j k, m => 1 + Nat.size i + Nat.size j + Nat.size k + Nat.size (m j) + Nat.size (m k)
  | .load i j, m => 1 + Nat.size i + Nat.size j + Nat.size (m j) + Nat.size (m (m j))
  | .store i j, m => 1 + Nat.size i + Nat.size j + Nat.size (m i) + Nat.size (m j)
  | .jump t, _ => 1 + Nat.size t
  | .jz i t, m => 1 + Nat.size i + Nat.size t + Nat.size (m i)
  | .halt, _ => 0

/-- The logarithmic cost of executing one step of `P` in configuration `c`. -/
def stepCost (P : Program) (c : Config) : ℕ :=
  match P[c.pc]? with
  | none => 0
  | some i => i.cost c.mem

/-- The logarithmic cost of the first `k` steps: the sum of the costs of the steps executed. -/
def logTime (P : Program) (c : Config) : ℕ → ℕ
  | 0 => 0
  | k + 1 => logTime P c k + stepCost P (run P c k)

/-- Unit cost never exceeds logarithmic cost: every executed step costs at least one. -/
theorem Instr.one_le_cost {i : Instr} (hi : i ≠ Instr.halt) (m : Mem) : 1 ≤ i.cost m := by
  cases i <;> simp only [Instr.cost] <;> try omega
  exact absurd rfl hi

theorem one_le_stepCost {P : Program} {c : Config} (h : ¬ Halted P c) : 1 ≤ stepCost P c := by
  unfold stepCost
  split <;> rename_i hget
  · exact absurd (Or.inl hget) h
  · rename_i i _
    exact Instr.one_le_cost (fun hi => h (Or.inr (hi ▸ hget))) _

theorem le_logTime {P : Program} {c : Config} {k : ℕ} (h : ¬ Halted P (run P c k)) :
    k + 1 ≤ logTime P c (k + 1) := by
  induction k with
  | zero => simpa [logTime] using one_le_stepCost h
  | succ k ih =>
      have hk : ¬ Halted P (run P c k) := fun hk =>
        h (halted_run_of_le (Nat.le_succ k) hk)
      have hih := ih hk
      have hcost : 1 ≤ stepCost P (run P c (k + 1)) := one_le_stepCost h
      have hunf : logTime P c (k + 1 + 1)
          = logTime P c (k + 1) + stepCost P (run P c (k + 1)) := rfl
      omega

/-- Logarithmic cost is at most the unit cost times the bit length available after the run: this
is the quantitative form of "unit cost and logarithmic cost are polynomially related" for this
instruction set. -/
theorem Instr.cost_le {i : Instr} {m : Mem} {M : ℕ}
    (hb : Nat.size i.bound ≤ M) (hm : ∀ x, Nat.size (m x) ≤ M) : i.cost m ≤ 1 + 6 * M := by
  have key : ∀ x : ℕ, x ≤ i.bound → Nat.size x ≤ M := fun x hx =>
    le_trans (Nat.size_le_size hx) hb
  cases i with
  | const a b =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      simp only [Instr.cost]; omega
  | copy a b =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      have v1 := hm b
      simp only [Instr.cost]; omega
  | add a b c =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      have h3 := key c (by simp [Instr.bound])
      have v1 := hm b; have v2 := hm c
      simp only [Instr.cost]; omega
  | sub a b c =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      have h3 := key c (by simp [Instr.bound])
      have v1 := hm b; have v2 := hm c
      simp only [Instr.cost]; omega
  | load a b =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      have v1 := hm b; have v2 := hm (m b)
      simp only [Instr.cost]; omega
  | store a b =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key b (by simp [Instr.bound])
      have v1 := hm a; have v2 := hm b
      simp only [Instr.cost]; omega
  | jump t =>
      have h1 := key t (by simp [Instr.bound])
      simp only [Instr.cost]; omega
  | jz a t =>
      have h1 := key a (by simp [Instr.bound])
      have h2 := key t (by simp [Instr.bound])
      have v1 := hm a
      simp only [Instr.cost]; omega
  | halt => simp only [Instr.cost]; omega

theorem stepCost_le {P : Program} {c : Config} {B : ℕ} (hP : P.bound ≤ B)
    (h : ∀ a, c.mem a ≤ B) (k : ℕ) :
    stepCost P (run P c k) ≤ 1 + 6 * (k + Nat.size B) := by
  have hval : ∀ a, Nat.size ((run P c k).mem a) ≤ k + Nat.size B := size_mem_le_run hP h k
  unfold stepCost
  split <;> rename_i hget
  · omega
  · rename_i i _
    exact Instr.cost_le (le_trans (size_index_le hP hget) (by omega)) hval

theorem logTime_le {P : Program} {c : Config} {B : ℕ} (hP : P.bound ≤ B)
    (h : ∀ a, c.mem a ≤ B) (k : ℕ) : logTime P c k ≤ k * (1 + 6 * (k + Nat.size B)) := by
  induction k with
  | zero => simp [logTime]
  | succ k ih =>
      have hcost := stepCost_le hP h k
      have hmono : k * (1 + 6 * (k + Nat.size B)) ≤ k * (1 + 6 * (k + 1 + Nat.size B)) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [logTime]
      have : (k + 1) * (1 + 6 * (k + 1 + Nat.size B))
          = k * (1 + 6 * (k + 1 + Nat.size B)) + (1 + 6 * (k + 1 + Nat.size B)) := by ring
      omega

end RAM
