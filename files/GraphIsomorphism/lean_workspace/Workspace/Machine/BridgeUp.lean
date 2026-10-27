import Workspace.Machine.BridgeDown

set_option maxRecDepth 8000

/-!
# The bridge up: from the input convention to the workspace convention

`initMem l` puts the length in register `0` and the entries in registers `1, ..., n`.  For an
input longer than every constant occurring in a program, no register with a fixed index is free.
This file builds the program `up` that moves the whole picture up by sixteen registers, so that
the routines of the workspace convention `initMemAt 16` apply.  The result is *exact*: from
`initMem l` the program halts in exactly `initMemAt 16 l`.

## Two facts that shape the program

* At the input convention the only free memory is above `n`, and the only address above `n` a
  program can name in one step is `2 n`, by `add 0 0 0`, which **destroys** `n`.  So `n` has to
  be recovered afterwards, and the only way to recover it is to count: `upHalve` subtracts
  `1024` from `1024 n` until nothing is left, adding one to a counter each time.  This costs
  `O(n)` steps, which is within budget.
* A shift loop that moves `mem[16 + i] := mem[i]` with `i` *decreasing* is correct for the
  overlapping upward move, and it may start at `i = 2 n` rather than `i = n`: the cells
  `n+1, ..., 2n` hold zeros, and their images have to be zero anyway.  So the loop itself never
  needs `n`.

## The program

`up = ifz 0 upBody []`: when `n = 0` both `initMem []` and `initMemAt 16 []` are the all-zero
memory, so there is nothing to do.  For `n ≥ 1`, `upBody` is

* `upPark`: five doublings put `32 n` in register `0`, and `parkRun` then saves the five
  registers `1, ..., 5` at the addresses `32 n, 64 n, ..., 512 n`, doubling the pointer between
  two saves, so that no second register is needed.  All these addresses lie above `16 + 2 n`,
  which is the top of everything the shift loop touches, because `32 n > 16 + 2 n` for
  `n ≥ 1`.
* `upHalve`: recovers `n` in register `4` from `1024 n` in register `0`.
* `upSetup`: register `0` the source pointer (from `2 n`), register `1` the destination pointer
  (from `16 + 2 n`), register `2` the value in transit, register `3` the constant `1`,
  register `4` the counter `2 n - 5`, register `5` the length `n`.
* `upLoop`: the descending shift, filling `[16 + 6, 16 + 2 n]`.
* `upFinal`: writes `n` into register `16` and reads the five parked values back into the
  registers `17, ..., 21`, then zeroes the parking cells.
* `Layout.clearRange 16`: zeroes the registers `0, ..., 15`.

## Main results

* `RAM.Bridge.runsTo_up`: from `initMem l` the program `up` halts in exactly `initMemAt 16 l`
  within `18 * l.length + 78` steps.
-/

namespace RAM
namespace Bridge

/-! ## Doubling register `0` -/

/-- `doubleZero k` doubles register `0` `k` times, one instruction each. -/
def doubleZero : ℕ → Program
  | 0 => []
  | k + 1 => seq (doubleZero k) (addTo 0 0 0)

theorem wf_doubleZero (k : ℕ) : Wf (doubleZero k) := by
  induction k with
  | zero => intro i hi; exact absurd hi (by simp [doubleZero])
  | succ k ih => exact wf_seq ih (Layout.wf_addTo _ _ _)

theorem runsTo_doubleZero (m₀ : Mem) (k : ℕ) :
    RunsTo (doubleZero k) (fun m => m = m₀)
      (fun m' => m' 0 = 2 ^ k * m₀ 0 ∧ ∀ z, z ≠ 0 → m' z = m₀ z) k := by
  induction k with
  | zero => exact runsTo_nil (fun m hm => by subst hm; exact ⟨by simp, fun _ _ => rfl⟩)
  | succ k ih =>
      refine RunsTo.mono (T := k + 1) ?_ (le_refl _)
      refine RunsTo.seq (mid := fun m => m 0 = 2 ^ k * m₀ 0 ∧ ∀ z, z ≠ 0 → m z = m₀ z) ih ?_
      refine runsTo_addTo 0 0 0 (fun m hm => ⟨?_, ?_⟩)
      · rw [Mem.update_self, hm.1]; ring
      · intro z hz; rw [Mem.update_of_ne _ _ hz]; exact hm.2 z hz

/-! ## The pieces of `up` -/

/-- The registers parked by `upPark`: `1, 2, 3, 4, 5`. -/
def upRegs (j : ℕ) : ℕ := j + 1

/-- The registers filled by `upFinal`: `17, ..., 21`. -/
def upBack (j : ℕ) : ℕ := 17 + j

/-- Put `32 n` in register `0` and park the registers `1, ..., 5`. -/
def upPark : Program := seq (doubleZero 5) (parkRun upRegs 5)

/-- One step of the counting loop that recovers `n`. -/
def upHalveBody : Program := seq (subTo 0 0 3) (addTo 4 4 2)

/-- Recover `n` in register `4` from `1024 n` in register `0`. -/
def upHalve : Program :=
  seq (assign 2 1) (seq (assign 3 1024) (seq (assign 4 0) (whileNz 0 upHalveBody)))

/-- The pointers and the counter of the shift loop. -/
def upSetup : Program :=
  seq (copyTo 5 4) (seq (addTo 0 5 5) (seq (assign 1 16) (seq (addTo 1 1 0)
    (seq (assign 3 1) (seq (assign 2 5) (subTo 4 0 2))))))

/-- One entry of the upward shift. -/
def upBody : Program :=
  seq (loadTo 2 0) (seq (storeTo 1 2) (seq (subTo 0 0 3) (seq (subTo 1 1 3) (subTo 4 4 3))))

/-- The descending shift of `[6, 2 n]` to `[22, 16 + 2 n]`. -/
def upLoop : Program := whileNz 4 upBody

/-- Write `n` into register `16`, read the five parked values back into the registers
`17, ..., 21`, and zero the parking cells. -/
def upFinal : Program :=
  seq (copyTo 16 5) (seq (copyTo 0 5) (seq (doubleZero 5)
    (seq (unparkRun upBack 5) (seq (copyTo 0 5) (seq (doubleZero 5)
      (parkRun (fun _ => 4) 5))))))

/-- The body of `up`, run when the input is nonempty. -/
def upMain : Program :=
  seq upPark (seq upHalve (seq upSetup (seq upLoop (seq upFinal (Layout.clearRange 16)))))

/-- **The bridge up.**  From `initMem l` to exactly `initMemAt 16 l`. -/
def up : Program := RAM.ifz 0 upMain []

/-! ## The stage predicates -/

section

variable (l : List ℕ) (n : ℕ)

/-- The state during the counting loop that recovers `n`. -/
def HalveInv (m : Mem) : Prop :=
  ∃ i, i ≤ n ∧ m 0 = 1024 * (n - i) ∧ m 2 = 1 ∧ m 3 = 1024 ∧ m 4 = i ∧
    (∀ j < 5, m (2 ^ j * (32 * n)) = initMem l (j + 1)) ∧
    (∀ z, 6 ≤ z → (∀ j < 5, z ≠ 2 ^ j * (32 * n)) → m z = initMem l z)

/-- The state during the descending shift: the cells above `16 + i` are in place. -/
def ShiftInv (m : Mem) : Prop :=
  ∃ i, i ≤ 2 * n ∧ m 0 = i ∧ m 1 = 16 + i ∧ m 3 = 1 ∧ m 4 = i - 5 ∧ m 5 = n ∧
    (∀ j < 5, m (2 ^ j * (32 * n)) = initMem l (j + 1)) ∧
    (∀ x, i < x → x ≤ 2 * n → m (16 + x) = initMem l x) ∧
    (∀ z, 6 ≤ z → ¬(16 + i < z ∧ z ≤ 16 + 2 * n) → (∀ j < 5, z ≠ 2 ^ j * (32 * n)) →
      m z = initMem l z)

/-- The state after the shift, with the progress variable eliminated. -/
def Shifted (m : Mem) : Prop :=
  m 4 = 0 ∧ m 5 = n ∧
    (∀ j < 5, m (2 ^ j * (32 * n)) = initMem l (j + 1)) ∧
    (∀ x, 6 ≤ x → x ≤ 2 * n → m (16 + x) = initMem l x) ∧
    (∀ z, 16 + 2 * n < z → (∀ j < 5, z ≠ 2 ^ j * (32 * n)) → m z = initMem l z)

/-- The state during `upFinal`, after register `16` has received `n`. -/
def FinalInv (m : Mem) : Prop :=
  m 16 = n ∧ m 5 = n ∧ m 4 = 0 ∧
    (∀ j < 5, m (2 ^ j * (32 * n)) = initMem l (j + 1)) ∧
    (∀ x, 6 ≤ x → x ≤ 2 * n → m (16 + x) = initMem l x) ∧
    (∀ z, 21 < z → 16 + 2 * n < z → (∀ j < 5, z ≠ 2 ^ j * (32 * n)) → m z = initMem l z)

end

/-! ## Elementary facts about the parking addresses -/

section

variable {n : ℕ}

theorem park_ge (hn : 1 ≤ n) (j : ℕ) : 32 * n ≤ 2 ^ j * (32 * n) :=
  le_two_pow_mul j (32 * n)

theorem park_big (hn : 1 ≤ n) (j : ℕ) : 16 + 2 * n < 2 ^ j * (32 * n) := by
  have := park_ge hn j
  omega

end

/-! ## The phases -/

theorem runsTo_upPark {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) (hnl : n = l.length) :
    RunsTo upPark (fun m => m = initMem l) (ParkedAt (initMem l) (32 * n) upRegs 5) 15 := by
  have h0 : initMem l 0 = n := by rw [hnl]; simp [initMem]
  refine RunsTo.mono (T := 5 + 2 * 5) ?_ (by norm_num)
  refine RunsTo.seq (mid := ParkedAt (initMem l) (32 * n) upRegs 0) ?_ ?_
  · refine (runsTo_doubleZero (initMem l) 5).weaken (fun m' hm' => ?_)
    refine ⟨?_, by intro j hj; omega, fun z hz _ => hm'.2 z hz⟩
    rw [hm'.1, h0]; ring
  · exact runsTo_parkRun (by omega) 5
      (fun j hj => ⟨by simp only [upRegs]; omega, by simp only [upRegs]; omega⟩)

theorem runsTo_upHalveBody {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    RunsTo upHalveBody
      (fun m => HalveInv l n m ∧ m 0 ≠ 0 ∧ m 0 / 1024 = k)
      (fun m' => HalveInv l n m' ∧ m' 0 / 1024 < k) 2 := by
  refine ⟨wf_seq (Layout.wf_subTo _ _ _) (Layout.wf_addTo _ _ _), ?_⟩
  intro m₁ hm₁
  obtain ⟨⟨i, hin, e0, e2, e3, e4, epk, efr⟩, hne, hk⟩ := hm₁
  have hilt : i < n := by
    by_contra hc
    have : n - i = 0 := by omega
    rw [this] at e0; simp at e0; omega
  have hk' : k = n - i := by rw [← hk, e0, Nat.mul_div_cancel_left _ (by norm_num)]
  refine (?_ : RunsTo upHalveBody (fun m => m = m₁)
    (fun m' => HalveInv l n m' ∧ m' 0 / 1024 < k) 2).spec m₁ rfl
  refine RunsTo.mono (T := 1 + 1) ?_ (le_refl _)
  refine RunsTo.seq (mid := fun m => m = m₁.update 0 (1024 * (n - (i + 1))))
    (runsTo_subTo 0 0 3 (fun m hm => by
      rw [hm, e0, e3, show 1024 * (n - i) - 1024 = 1024 * (n - (i + 1)) from by omega])) ?_
  refine runsTo_addTo 4 4 2 (fun m hm => ?_)
  subst hm
  have h4 : (m₁.update 0 (1024 * (n - (i + 1)))) 4 = i := by
    rw [Mem.update_of_ne _ _ (by omega), e4]
  have h2 : (m₁.update 0 (1024 * (n - (i + 1)))) 2 = 1 := by
    rw [Mem.update_of_ne _ _ (by omega), e2]
  rw [h4, h2]
  have hfr : ∀ z, z ≠ 0 → z ≠ 4 →
      ((m₁.update 0 (1024 * (n - (i + 1)))).update 4 (i + 1)) z = m₁ z := by
    intro z hz0 hz4
    rw [Mem.update_of_ne _ _ hz4, Mem.update_of_ne _ _ hz0]
  have hz0 : ((m₁.update 0 (1024 * (n - (i + 1)))).update 4 (i + 1)) 0
      = 1024 * (n - (i + 1)) := by
    rw [Mem.update_of_ne _ _ (by omega), Mem.update_self]
  refine ⟨⟨i + 1, by omega, hz0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hfr 2 (by omega) (by omega), e2]
  · rw [hfr 3 (by omega) (by omega), e3]
  · rw [Mem.update_self]
  · intro j hj
    have := park_ge hn (n := n) j
    rw [hfr _ (by omega) (by omega)]
    exact epk j hj
  · intro z hz hzj
    rw [hfr _ (by omega) (by omega)]
    exact efr z hz hzj
  · rw [hz0, Nat.mul_div_cancel_left _ (by norm_num)]
    omega

theorem runsTo_upHalve {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) :
    RunsTo upHalve (ParkedAt (initMem l) (32 * n) upRegs 5)
      (fun m' => HalveInv l n m' ∧ m' 0 = 0) (4 * n + 4) := by
  have hpg : ∀ j, 32 * n ≤ 2 ^ j * (32 * n) := fun j => park_ge hn j
  refine RunsTo.mono (T := 1 + (1 + (1 + (n * (2 + 2) + 1)))) ?_ (by omega)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq (mid := fun m => m = m₁.update 2 1 ∧ ParkedAt (initMem l) (32 * n) upRegs 5 m₁)
    (runsTo_assign 2 1 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m => m = (m₁.update 2 1).update 3 1024 ∧
      ParkedAt (initMem l) (32 * n) upRegs 5 m₁)
    (runsTo_assign 3 1024 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := HalveInv l n) ?_ ?_
  · refine runsTo_assign 4 0 (fun m hm => ?_)
    obtain ⟨hme, hz0, hpk, hfr⟩ := hm
    subst hme
    have hfr' : ∀ z, z ≠ 2 → z ≠ 3 → z ≠ 4 →
        (((m₁.update 2 1).update 3 1024).update 4 0) z = m₁ z := by
      intro z h2 h3 h4
      rw [Mem.update_of_ne _ _ h4, Mem.update_of_ne _ _ h3, Mem.update_of_ne _ _ h2]
    refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfr' 0 (by omega) (by omega) (by omega), hz0]
      simp only [Nat.sub_zero]
      ring
    · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 4),
        Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3), Mem.update_self]
    · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 4), Mem.update_self]
    · rw [Mem.update_self]
    · intro j hj
      have := hpg j
      rw [hfr' _ (by omega) (by omega) (by omega)]
      exact hpk j hj
    · intro z hz hzj
      rw [hfr' _ (by omega) (by omega) (by omega)]
      exact hfr z (by omega) (fun j hj => hzj j hj)
  · refine runsTo_whileNz (μ := fun m => m 0 / 1024) (N := n)
      (fun k => runsTo_upHalveBody hn k) ?_
    rintro m ⟨i, hin, e0, -⟩
    show m 0 / 1024 ≤ n
    rw [e0, Nat.mul_div_cancel_left _ (by norm_num)]
    omega

theorem runsTo_upSetup {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) :
    RunsTo upSetup (fun m => HalveInv l n m ∧ m 0 = 0) (ShiftInv l n) 7 := by
  have hpg : ∀ j, 32 * n ≤ 2 ^ j * (32 * n) := fun j => park_ge hn j
  refine ⟨wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_addTo _ _ _)
    (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
        (Layout.wf_subTo _ _ _)))))), ?_⟩
  intro m₀ hm₀
  obtain ⟨⟨i, hin, e0, e2, e3, e4, epk, efr⟩, hzero⟩ := hm₀
  have hi : i = n := by
    rw [hzero] at e0
    omega
  rw [hi] at e4
  refine (?_ : RunsTo upSetup (fun m => m = m₀) (ShiftInv l n) 7).spec m₀ rfl
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + (1 + (1 + 1)))))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update 5 n)
    (runsTo_copyTo 5 4 (fun m hm => by rw [hm, e4])) ?_
  set u1 : Mem := m₀.update 5 n with hu1
  have hu1_5 : u1 5 = n := by rw [hu1, Mem.update_self]
  refine RunsTo.seq (mid := fun m => m = u1.update 0 (2 * n))
    (runsTo_addTo 0 5 5 (fun m hm => by rw [hm, hu1_5]; congr 1; ring)) ?_
  set u2 : Mem := u1.update 0 (2 * n) with hu2
  refine RunsTo.seq (mid := fun m => m = u2.update 1 16)
    (runsTo_assign 1 16 (fun m hm => by rw [hm])) ?_
  set u3 : Mem := u2.update 1 16 with hu3
  have hu3_1 : u3 1 = 16 := by rw [hu3, Mem.update_self]
  have hu3_0 : u3 0 = 2 * n := by
    rw [hu3, Mem.update_of_ne _ _ (by omega), hu2, Mem.update_self]
  refine RunsTo.seq (mid := fun m => m = u3.update 1 (16 + 2 * n))
    (runsTo_addTo 1 1 0 (fun m hm => by rw [hm, hu3_1, hu3_0])) ?_
  set u4 : Mem := u3.update 1 (16 + 2 * n) with hu4
  refine RunsTo.seq (mid := fun m => m = u4.update 3 1)
    (runsTo_assign 3 1 (fun m hm => by rw [hm])) ?_
  set u5 : Mem := u4.update 3 1 with hu5
  refine RunsTo.seq (mid := fun m => m = u5.update 2 5)
    (runsTo_assign 2 5 (fun m hm => by rw [hm])) ?_
  set u6 : Mem := u5.update 2 5 with hu6
  have hu6_0 : u6 0 = 2 * n := by
    simp only [hu6, hu5, hu4, hu3, Mem.update, if_neg (by omega : (0:ℕ) ≠ 2),
      if_neg (by omega : (0:ℕ) ≠ 3), if_neg (by omega : (0:ℕ) ≠ 1)]
    exact hu3_0
  have hu6_2 : u6 2 = 5 := by rw [hu6, Mem.update_self]
  refine runsTo_subTo 4 0 2 (fun m hm => ?_)
  subst hm
  rw [hu6_0, hu6_2]
  have hframe : ∀ z, z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 3 → z ≠ 4 → z ≠ 5 →
      (u6.update 4 (2 * n - 5)) z = m₀ z := by
    intro z h0 h1 h2 h3 h4 h5
    simp only [hu6, hu5, hu4, hu3, hu2, hu1, Mem.update, if_neg h0, if_neg h1, if_neg h2,
      if_neg h3, if_neg h4, if_neg h5]
  refine ⟨2 * n, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega), hu6_0]
  · rw [Mem.update_of_ne _ _ (by omega), hu6, Mem.update_of_ne _ _ (by omega), hu5,
      Mem.update_of_ne _ _ (by omega), hu4, Mem.update_self]
  · rw [Mem.update_of_ne _ _ (by omega), hu6, Mem.update_of_ne _ _ (by omega), hu5,
      Mem.update_self]
  · rw [Mem.update_self]
  · rw [Mem.update_of_ne _ _ (by omega), hu6, Mem.update_of_ne _ _ (by omega), hu5,
      Mem.update_of_ne _ _ (by omega), hu4, Mem.update_of_ne _ _ (by omega), hu3,
      Mem.update_of_ne _ _ (by omega), hu2, Mem.update_of_ne _ _ (by omega), hu1_5]
  · intro j hj
    have := hpg j
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact epk j hj
  · intro x hx1 hx2; omega
  · intro z hz _ hzj
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact efr z hz hzj

theorem runsTo_upBody {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    RunsTo upBody (fun m => ShiftInv l n m ∧ m 4 = k + 1)
      (fun m' => ShiftInv l n m' ∧ m' 4 = k) 5 := by
  have hpg : ∀ j, 32 * n ≤ 2 ^ j * (32 * n) := fun j => park_ge hn j
  refine ⟨wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_storeTo _ _)
    (wf_seq (Layout.wf_subTo _ _ _) (wf_seq (Layout.wf_subTo _ _ _)
      (Layout.wf_subTo _ _ _)))), ?_⟩
  intro m₁ hm₁
  obtain ⟨⟨i, hin, e0, e1, e3, e4, e5, epk, ewr, efr⟩, hc⟩ := hm₁
  have hi6 : 6 ≤ i := by omega
  have hsrc : m₁ i = initMem l i := by
    refine efr i hi6 (by omega) (fun j hj => ?_)
    have := hpg j
    omega
  refine (?_ : RunsTo upBody (fun m => m = m₁)
    (fun m' => ShiftInv l n m' ∧ m' 4 = k) 5).spec m₁ rfl
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₁.update 2 (initMem l i))
    (runsTo_loadTo 2 0 (fun m hm => by rw [hm, e0, hsrc])) ?_
  set v1 : Mem := m₁.update 2 (initMem l i) with hv1
  have hv1_1 : v1 1 = 16 + i := by rw [hv1, Mem.update_of_ne _ _ (by omega), e1]
  have hv1_2 : v1 2 = initMem l i := by rw [hv1, Mem.update_self]
  refine RunsTo.seq (mid := fun m => m = v1.update (16 + i) (initMem l i))
    (runsTo_storeTo 1 2 (fun m hm => by rw [hm, hv1_1, hv1_2])) ?_
  set v2 : Mem := v1.update (16 + i) (initMem l i) with hv2
  have hv2_0 : v2 0 = i := by
    rw [hv2, Mem.update_of_ne _ _ (by omega), hv1, Mem.update_of_ne _ _ (by omega), e0]
  have hv2_3 : v2 3 = 1 := by
    rw [hv2, Mem.update_of_ne _ _ (by omega), hv1, Mem.update_of_ne _ _ (by omega), e3]
  refine RunsTo.seq (mid := fun m => m = v2.update 0 (i - 1))
    (runsTo_subTo 0 0 3 (fun m hm => by rw [hm, hv2_0, hv2_3])) ?_
  set v3 : Mem := v2.update 0 (i - 1) with hv3
  have hv3_1 : v3 1 = 16 + i := by
    rw [hv3, Mem.update_of_ne _ _ (by omega), hv2, Mem.update_of_ne _ _ (by omega), hv1_1]
  have hv3_3 : v3 3 = 1 := by rw [hv3, Mem.update_of_ne _ _ (by omega), hv2_3]
  refine RunsTo.seq (mid := fun m => m = v3.update 1 (16 + i - 1))
    (runsTo_subTo 1 1 3 (fun m hm => by rw [hm, hv3_1, hv3_3])) ?_
  set v4 : Mem := v3.update 1 (16 + i - 1) with hv4
  have hv4_3 : v4 3 = 1 := by rw [hv4, Mem.update_of_ne _ _ (by omega), hv3_3]
  have hv4_4 : v4 4 = k + 1 := by
    rw [hv4, Mem.update_of_ne _ _ (by omega), hv3, Mem.update_of_ne _ _ (by omega), hv2,
      Mem.update_of_ne _ _ (by omega), hv1, Mem.update_of_ne _ _ (by omega), hc]
  refine runsTo_subTo 4 4 3 (fun m hm => ?_)
  subst hm
  rw [hv4_3, hv4_4]
  have hframe : ∀ z, z ≠ 0 → z ≠ 1 → z ≠ 2 → z ≠ 4 → z ≠ 16 + i →
      (v4.update 4 (k + 1 - 1)) z = m₁ z := by
    intro z h0 h1 h2 h4 h16
    simp only [hv4, hv3, hv2, hv1, Mem.update, if_neg h0, if_neg h1, if_neg h2, if_neg h4,
      if_neg h16]
  have hnew : (v4.update 4 (k + 1 - 1)) (16 + i) = initMem l i := by
    rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_of_ne _ _ (by omega), hv3,
      Mem.update_of_ne _ _ (by omega), hv2, Mem.update_self]
  refine ⟨⟨i - 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [Mem.update_self]; omega⟩
  · rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_of_ne _ _ (by omega), hv3,
      Mem.update_self]
  · rw [Mem.update_of_ne _ _ (by omega), hv4, Mem.update_self]; omega
  · rw [Mem.update_of_ne _ _ (by omega), hv4_3]
  · rw [Mem.update_self]; omega
  · rw [hframe 5 (by omega) (by omega) (by omega) (by omega) (by omega), e5]
  · intro j hj
    have := hpg j
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact epk j hj
  · intro x hx1 hx2
    rcases Nat.lt_or_ge i x with h | h
    · rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact ewr x h hx2
    · have hxi : x = i := by omega
      subst hxi
      exact hnew
  · intro z hz hzr hzj
    rw [hframe _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact efr z hz (by omega) hzj

theorem runsTo_upLoop {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) :
    RunsTo upLoop (ShiftInv l n) (Shifted l n) (14 * n + 1) := by
  refine RunsTo.mono (T := 2 * n * (5 + 2) + 1) ?_ (by omega)
  refine (runsTo_forLoop (fun k => runsTo_upBody hn k) ?_).weaken ?_
  · rintro m ⟨i, hin, e0, e1, e3, e4, e5, epk, ewr, efr⟩
    omega
  · rintro m ⟨⟨i, hin, e0, e1, e3, e4, e5, epk, ewr, efr⟩, hz⟩
    have hi5 : i ≤ 5 := by omega
    refine ⟨hz, e5, epk, ?_, ?_⟩
    · intro x hx1 hx2; exact ewr x (by omega) hx2
    · intro z hz1 hzj; exact efr z (by omega) (by omega) hzj

/-! ## The final phase -/

theorem runsTo_upFinal {l : List ℕ} {n : ℕ} (hn : 1 ≤ n) (hnl : n = l.length) :
    RunsTo upFinal (Shifted l n) (fun m' => ∀ z, 16 ≤ z → m' z = initMemAt 16 l z) 33 := by
  have hpg : ∀ j, 32 * n ≤ 2 ^ j * (32 * n) := fun j => park_ge hn j
  refine RunsTo.mono (T := 1 + (1 + (5 + (2 * 5 + (1 + (5 + 2 * 5)))))) ?_ (by norm_num)
  -- (a) write `n` into register `16`
  refine RunsTo.seq (mid := FinalInv l n) ?_ ?_
  · refine ⟨Layout.wf_copyTo _ _, ?_⟩
    intro m₀ hm₀
    obtain ⟨g4, g5, gpk, gwr, gfr⟩ := hm₀
    refine (?_ : RunsTo (copyTo 16 5) (fun m => m = m₀) (FinalInv l n) 1).spec m₀ rfl
    refine runsTo_copyTo 16 5 (fun m hm => ?_)
    subst hm
    rw [g5]
    refine ⟨by rw [Mem.update_self], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.update_of_ne _ _ (by omega), g5]
    · rw [Mem.update_of_ne _ _ (by omega), g4]
    · intro j hj
      have := hpg j
      rw [Mem.update_of_ne _ _ (by omega)]
      exact gpk j hj
    · intro x hx1 hx2
      rw [Mem.update_of_ne _ _ (by omega)]
      exact gwr x hx1 hx2
    · intro z hz1 hz2 hzj
      rw [Mem.update_of_ne _ _ (by omega)]
      exact gfr z hz2 hzj
  -- (b), (c), (d)
  refine ⟨wf_seq (Layout.wf_copyTo _ _) (wf_seq (wf_doubleZero _)
    (wf_seq (wf_unparkRun _ _) (wf_seq (Layout.wf_copyTo _ _)
      (wf_seq (wf_doubleZero _) (wf_parkRun _ _))))), ?_⟩
  intro mA hmA
  obtain ⟨a16, a5, a4, apk, awr, afr⟩ := hmA
  refine (?_ : RunsTo (seq (copyTo 0 5) (seq (doubleZero 5) (seq (unparkRun upBack 5)
    (seq (copyTo 0 5) (seq (doubleZero 5) (parkRun (fun _ => 4) 5))))))
    (fun m => m = mA) (fun m' => ∀ z, 16 ≤ z → m' z = initMemAt 16 l z)
    (1 + (5 + (2 * 5 + (1 + (5 + 2 * 5)))))).spec mA rfl
  refine RunsTo.seq (mid := fun m => m = mA.update 0 n)
    (runsTo_copyTo 0 5 (fun m hm => by rw [hm, a5])) ?_
  set p1 : Mem := mA.update 0 n with hp1
  refine RunsTo.seq (mid := UnparkedAt mA (32 * n) upBack 0) ?_ ?_
  · refine (runsTo_doubleZero p1 5).weaken (fun m' hm' => ?_)
    refine ⟨?_, by intro j hj; omega, fun z hz _ => ?_⟩
    · rw [hm'.1, hp1, Mem.update_self]; ring
    · rw [hm'.2 z hz, hp1, Mem.update_of_ne _ _ hz]
  refine RunsTo.seq (mid := UnparkedAt mA (32 * n) upBack 5) ?_ ?_
  · refine runsTo_unparkRun (by omega) 5
      (fun j hj => ⟨by simp only [upBack]; omega, by simp only [upBack]; omega⟩) ?_
    intro i j hij hj
    simp only [upBack]
    omega
  -- now the five parked values are in the registers `17, ..., 21`
  refine ⟨wf_seq (Layout.wf_copyTo _ _) (wf_seq (wf_doubleZero _) (wf_parkRun _ _)), ?_⟩
  intro mB hmB
  obtain ⟨b0, bpk, bfr⟩ := hmB
  have hb5 : mB 5 = n := by
    rw [bfr 5 (by omega) (fun j hj => by simp only [upBack]; omega), a5]
  have hb4 : mB 4 = 0 := by
    rw [bfr 4 (by omega) (fun j hj => by simp only [upBack]; omega), a4]
  refine (?_ : RunsTo (seq (copyTo 0 5) (seq (doubleZero 5) (parkRun (fun _ => 4) 5)))
    (fun m => m = mB) (fun m' => ∀ z, 16 ≤ z → m' z = initMemAt 16 l z)
    (1 + (5 + 2 * 5))).spec mB rfl
  refine RunsTo.seq (mid := fun m => m = mB.update 0 n)
    (runsTo_copyTo 0 5 (fun m hm => by rw [hm, hb5])) ?_
  set q1 : Mem := mB.update 0 n with hq1
  refine RunsTo.seq (mid := ParkedAt mB (32 * n) (fun _ => 4) 0) ?_ ?_
  · refine (runsTo_doubleZero q1 5).weaken (fun m' hm' => ?_)
    refine ⟨?_, by intro j hj; omega, fun z hz _ => ?_⟩
    · rw [hm'.1, hq1, Mem.update_self]; ring
    · rw [hm'.2 z hz, hq1, Mem.update_of_ne _ _ hz]
  refine (runsTo_parkRun (M := mB) (by omega) 5 (fun j hj => ⟨by omega, by omega⟩)).weaken ?_
  -- the audit
  rintro m ⟨c0, cpk, cfr⟩ z hz
  rw [initMemAt_of_ge l hz]
  have hzero : ∀ j, j < 5 → m (2 ^ j * (32 * n)) = 0 := by
    intro j hj
    rw [cpk j hj, hb4]
  have hout : ∀ x, n < x → initMem l x = 0 := fun x hx =>
    initMem_eq_zero_of_gt (by omega)
  have hbackfr : ∀ z, z ≠ 0 → (z < 17 ∨ 21 < z) → mB z = mA z := by
    intro z h0 hcase
    exact bfr z h0 (fun j hj => by simp only [upBack]; omega)
  by_cases hpark : ∃ j, j < 5 ∧ z = 2 ^ j * (32 * n)
  · obtain ⟨j, hj, rfl⟩ := hpark
    have hb := hpg j
    rw [hzero j hj, hout _ (by omega)]
  push_neg at hpark
  have hmz : m z = mB z := cfr z (by omega) (fun j hj => hpark j hj)
  rcases Nat.lt_or_ge z 17 with hz17 | hz17
  · have hz16 : z = 16 := by omega
    subst hz16
    rw [hmz, hbackfr 16 (by omega) (Or.inl (by omega)), a16]
    simp [initMem, hnl]
  rcases Nat.lt_or_ge z 22 with hz22 | hz22
  · have hj : upBack (z - 17) = z := by simp only [upBack]; omega
    have hbk := bpk (z - 17) (by omega)
    rw [hj] at hbk
    rw [hmz, hbk, apk (z - 17) (by omega)]
    congr 1
    omega
  rcases Nat.lt_or_ge (16 + 2 * n) z with hhi | hlo
  · have := afr z (by omega) hhi (fun j hj => hpark j hj)
    rw [hmz, hbackfr z (by omega) (Or.inr (by omega)), this,
      hout _ (by omega), hout _ (by omega)]
  · have hw := awr (z - 16) (by omega) (by omega)
    rw [show 16 + (z - 16) = z by omega] at hw
    rw [hmz, hbackfr z (by omega) (Or.inr (by omega)), hw]

/-! ## Putting `up` together -/

theorem wf_upMain : Wf upMain := by
  refine wf_seq (wf_seq (wf_doubleZero _) (wf_parkRun _ _)) (wf_seq ?_ (wf_seq ?_
    (wf_seq (wf_whileNz ?_) (wf_seq ?_ ?_))))
  · exact wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
      (wf_seq (Layout.wf_assign _ _) (wf_whileNz
        (wf_seq (Layout.wf_subTo _ _ _) (Layout.wf_addTo _ _ _)))))
  · exact wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_addTo _ _ _)
      (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_addTo _ _ _)
        (wf_seq (Layout.wf_assign _ _) (wf_seq (Layout.wf_assign _ _)
          (Layout.wf_subTo _ _ _))))))
  · exact wf_seq (Layout.wf_loadTo _ _) (wf_seq (Layout.wf_storeTo _ _)
      (wf_seq (Layout.wf_subTo _ _ _) (wf_seq (Layout.wf_subTo _ _ _)
        (Layout.wf_subTo _ _ _))))
  · exact wf_seq (Layout.wf_copyTo _ _) (wf_seq (Layout.wf_copyTo _ _)
      (wf_seq (wf_doubleZero _) (wf_seq (wf_unparkRun _ _) (wf_seq (Layout.wf_copyTo _ _)
        (wf_seq (wf_doubleZero _) (wf_parkRun _ _))))))
  · exact (Layout.runsTo_clearRange 16 (fun _ => 0)).wf

theorem runsTo_upMain {l : List ℕ} (hn : 1 ≤ l.length) :
    RunsTo upMain (fun m => m = initMem l) (fun m' => m' = initMemAt 16 l)
      (18 * l.length + 76) := by
  set n := l.length with hnl
  refine RunsTo.mono
    (T := 15 + ((4 * n + 4) + (7 + ((14 * n + 1) + (33 + 16))))) ?_ (by omega)
  refine (runsTo_upPark hn hnl).seq ((runsTo_upHalve hn).seq ((runsTo_upSetup hn).seq
    ((runsTo_upLoop hn).seq ((runsTo_upFinal hn hnl).seq ?_))))
  refine ⟨(Layout.runsTo_clearRange 16 (fun _ => 0)).wf, ?_⟩
  intro m₁ hm₁
  refine (?_ : RunsTo (Layout.clearRange 16) (fun m => m = m₁)
    (fun m' => m' = initMemAt 16 l) 16).spec m₁ rfl
  refine (Layout.runsTo_clearRange 16 m₁).weaken (fun m' hm' => ?_)
  subst hm'
  funext z
  simp only [Layout.zeroBelow]
  split
  · rw [initMemAt_of_lt l (by omega)]
  · exact hm₁ z (by omega)

/-- **The bridge up.**  From exactly `initMem l`, the program `up` halts in exactly
`initMemAt 16 l` within `18 * l.length + 78` steps. -/
theorem runsTo_up (l : List ℕ) :
    RunsTo up (fun m => m = initMem l) (fun m' => m' = initMemAt 16 l)
      (18 * l.length + 78) := by
  have hnil : l.length = 0 → initMem l = initMemAt 16 l := by
    intro hlen
    have hl : l = [] := by
      cases l with
      | nil => rfl
      | cons a t => simp at hlen
    subst hl
    funext z
    simp [initMem, initMemAt]
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · have hmain : RunsTo upMain (fun m => m = initMem l ∧ m 0 ≠ 0)
        (fun m' => m' = initMemAt 16 l) 0 := by
      refine runsTo_of_false wf_upMain (fun m hm => ?_)
      obtain ⟨hme, hne⟩ := hm
      subst hme
      exact hne (by simpa [initMem] using h0)
    have hnilb : RunsTo [] (fun m => m = initMem l ∧ m 0 = 0)
        (fun m' => m' = initMemAt 16 l) 0 :=
      runsTo_nil (fun m hm => by rw [hm.1, hnil h0])
    exact (RunsTo.ifz hmain hnilb).mono (by omega)
  · have hmain := (runsTo_upMain (l := l) hpos).strengthen
      (fun m (hm : m = initMem l ∧ m 0 ≠ 0) => hm.1)
    have hnilb : RunsTo [] (fun m => m = initMem l ∧ m 0 = 0)
        (fun m' => m' = initMemAt 16 l) 0 := by
      refine runsTo_of_false (fun i hi => absurd hi (by simp)) (fun m hm => ?_)
      obtain ⟨hme, h0⟩ := hm
      subst hme
      have : l.length = 0 := by simpa [initMem] using h0
      omega
    exact (RunsTo.ifz hmain hnilb).mono (by omega)

end Bridge
end RAM
