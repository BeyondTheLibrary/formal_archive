import Workspace.Machine.Arith
import Workspace.Machine.Compose

/-!
# Routines on inputs of fixed shape

The routines of `Workspace/Machine/Arith.lean` take a *scratch base* `s` and require the caller's
data to lie below it.  At the top-level convention that is a real obstacle for inputs of
unbounded length (see the "Doubts" section of `Workspace/Machine/DESIGN.md`), but not for an
input whose encoding occupies a **fixed number of registers**, and several of the operations the
paper needs are of that kind:

* a natural number `a` is encoded as `[a]`, so `initMem` is `R0 = 1`, `R1 = a`, and every register
  from `2` on is free;
* a pair of natural numbers `(a, b)` is encoded as `[1, a, 1, b]`, so `R0 = 4`, `R2 = a`,
  `R4 = b`, and every register from `5` on is free.

So the scratch base may be a fixed number, the routines of `Arith.lean` apply verbatim, and the
only extra work is to move the result into register `1`, to put the length into register `0` and
to zero the scratch — which makes the routine *clean* in the sense of `Compose.lean`.

## Main results

* `RAM.Small.cleanCompute_unary`, `RAM.Small.cleanCompute_binary`: the two packaging lemmas;
* `RAM.Small.polyTimeClean_size`: `a ↦ Nat.size a`, the bit length;
* `RAM.Small.polyTimeClean_log2`: `a ↦ Nat.log 2 a` (the same routine, one subtraction more);
* `RAM.Small.polyTimeClean_add`, `..._sub`, `..._min`, `..._max`, `..._le`: addition, truncated
  subtraction, the extrema and the comparison of a pair, in a constant number of steps.
-/

namespace RAM
namespace Small

/-! ## Two helpers -/

/-- `clearRegs S` sets every register in the list `S` to zero, one instruction each. -/
def clearRegs : List ℕ → Program
  | [] => []
  | i :: rest => seq (assign i 0) (clearRegs rest)

theorem runsTo_clearRegs (S : List ℕ) (m₀ : Mem) :
    RunsTo (clearRegs S) (fun m => m = m₀)
      (fun m' => (∀ i ∈ S, m' i = 0) ∧ (∀ z, z ∉ S → m' z = m₀ z)) S.length := by
  induction S generalizing m₀ with
  | nil =>
      refine runsTo_nil (fun m hm => ?_)
      subst hm
      exact ⟨fun i hi => absurd hi (by simp), fun _ _ => rfl⟩
  | cons i S ih =>
      refine RunsTo.mono (T := 1 + S.length) ?_ (by simp; omega)
      refine RunsTo.seq (mid := fun m => m = m₀.update i 0)
        (runsTo_assign i 0 (fun m hm => by rw [hm])) ?_
      refine (ih (m₀.update i 0)).weaken (fun m' hm' => ?_)
      obtain ⟨hzero, hrest⟩ := hm'
      refine ⟨fun j hj => ?_, fun z hz => ?_⟩
      · rcases List.mem_cons.1 hj with rfl | hj
        · by_cases hjS : j ∈ S
          · exact hzero j hjS
          · rw [hrest j hjS, Mem.update_self]
        · exact hzero j hj
      · simp only [List.mem_cons, not_or] at hz
        rw [hrest z hz.2, Mem.update_of_ne _ _ hz.1]

/-- The rule of constancy for the clearing block: a proposition not mentioning the memory is
carried across it. -/
theorem runsTo_clearRegs_const (S : List ℕ) (m₀ : Mem) (K : Prop) :
    RunsTo (clearRegs S) (fun m => m = m₀ ∧ K)
      (fun m' => ((∀ i ∈ S, m' i = 0) ∧ (∀ z, z ∉ S → m' z = m₀ z)) ∧ K) S.length := by
  by_cases hK : K
  · exact ((runsTo_clearRegs S m₀).weaken (fun m' h => ⟨h, hK⟩)).strengthen (fun m hm => hm.1)
  · exact runsTo_of_false (runsTo_clearRegs S m₀).wf (fun m hm => hK hm.2)

/-- A memory holding `v` in register `1`, `1` in register `0` and zero from register `2` on is
the initial memory of the one-entry list `[v]`. -/
theorem eq_initMem_singleton {m : Mem} {v : ℕ} (h0 : m 0 = 1) (h1 : m 1 = v)
    (h2 : ∀ z, 2 ≤ z → m z = 0) : m = initMem [v] := by
  funext z
  match z with
  | 0 => simpa [initMem] using h0
  | 1 => simpa [initMem] using h1
  | (k + 2) =>
      rw [h2 (k + 2) (by omega)]
      simp only [initMem, if_neg (by omega : k + 2 ≠ 0)]
      rw [List.getD_eq_default _ _ (by simp)]

/-- The scratch registers cleared by the packaging lemmas: everything from `2` to `9`. -/
def scratch : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9]

theorem mem_scratch_iff (z : ℕ) : z ∈ scratch ↔ 2 ≤ z ∧ z ≤ 9 := by
  simp only [scratch, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-! ## Packaging a scratch-based routine as a clean routine -/

/-- **A unary routine on `ℕ`.**  `R` is run on the input register `1`, leaves its answer in
register `2` and writes only inside the scratch block.  The packaged program is clean. -/
theorem cleanCompute_unary {β : Type*} [Enc β] {R : Program} {f : ℕ → β} {v : ℕ → ℕ} {T : ℕ → ℕ}
    {S : List ℕ} {U : ℕ → ℕ}
    (hv : ∀ a, Enc.encode (f a) = [v a])
    (hR : ∀ m₀ : Mem, RunsTo R (fun m => m = m₀)
      (fun m' => m' 2 = v (m₀ 1) ∧ Outside S m₀ m') (T (m₀ 1)))
    (hS : ∀ i ∈ S, i ∈ scratch)
    (hU : ∀ a : ℕ, T a + 10 ≤ U (Enc.size a)) :
    CleanCompute (seq R (seq (copyTo 1 2) (seq (assign 0 1) (clearRegs scratch)))) f U := by
  intro a
  have hmem : initMem (Enc.encode a) = initMem [a] := rfl
  rw [hmem]
  set m₀ : Mem := initMem [a] with hdef
  have e0 : m₀ 0 = 1 := by simp [hdef, initMem]
  have e1 : m₀ 1 = a := by simp [hdef, initMem]
  have e2 : ∀ z, 2 ≤ z → m₀ z = 0 := by
    intro z hz
    simp only [hdef, initMem, if_neg (by omega : z ≠ 0)]
    rw [List.getD_eq_default _ _ (by simp; omega)]
  refine RunsTo.mono (T := T a + (1 + (1 + scratch.length))) ?_ (by simp [scratch]; exact hU a)
  refine RunsTo.seq (mid := fun m => m 2 = v a ∧ Outside S m₀ m) ?_ ?_
  · have h := hR m₀
    rw [e1] at h
    exact h
  · refine runsTo_of_pointwise (fun m₁ => ?_)
    refine RunsTo.seq (mid := fun m => m = m₁.update 1 (m₁ 2) ∧ (m₁ 2 = v a ∧ Outside S m₀ m₁))
      (runsTo_copyTo 1 2 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine RunsTo.seq (mid := fun m => m = (m₁.update 1 (m₁ 2)).update 0 1 ∧
        (m₁ 2 = v a ∧ Outside S m₀ m₁))
      (runsTo_assign 0 1 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
    refine (runsTo_clearRegs_const scratch ((m₁.update 1 (m₁ 2)).update 0 1)
      (m₁ 2 = v a ∧ Outside S m₀ m₁)).weaken (fun m' hm' => ?_)
    obtain ⟨⟨hzero, hrest⟩, hval, hout⟩ := hm'
    rw [hv a]
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
          hout z (fun hzS => hzs (hS z hzS)), e2 z (by omega)]

/-- **A binary routine on `ℕ × ℕ`.**  `R` is run on the input registers `2` and `4`, leaves its
answer in register `5` and writes only inside the scratch block. -/
theorem cleanCompute_binary {β : Type*} [Enc β] {R : Program} {f : ℕ × ℕ → β} {v : ℕ → ℕ → ℕ}
    {T : ℕ} {S : List ℕ}
    (hv : ∀ p : ℕ × ℕ, Enc.encode (f p) = [v p.1 p.2])
    (hR : ∀ m₀ : Mem, RunsTo R (fun m => m = m₀)
      (fun m' => m' 5 = v (m₀ 2) (m₀ 4) ∧ Outside S m₀ m') T)
    (hS : ∀ i ∈ S, i ∈ scratch) :
    CleanCompute (seq R (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch)))) f
      (fun _ => T + 10) := by
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
  refine RunsTo.mono (T := T + (1 + (1 + scratch.length))) ?_ (by simp [scratch])
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

/-! ## The size of the input of fixed shape -/

/-- `Enc.size a = Nat.size a + 2` for a natural number: one register for the length, one for the
entry. -/
theorem size_nat (a : ℕ) : Enc.size a = Nat.size a + 2 := by
  simp [Enc.size, listSize, Enc.encode]
  omega

/-! ## The bit length and the binary logarithm -/

/-- `Nat.log 2 a = Nat.size a - 1`: the bit length is one more than the binary logarithm, and
both are `0` at `0`. -/
theorem log_two_eq_size_sub_one (a : ℕ) : Nat.log 2 a = Nat.size a - 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h1 : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
    have h2 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have h3 : Nat.size a ≤ Nat.log 2 a + 1 := Nat.size_le.2 h2
    have h4 : Nat.log 2 a < Nat.size a := Nat.lt_size.2 h1
    omega

/-- The bit length as a clean routine: `sizeTo` into register `2`, then the packaging. -/
def sizeProg : Program :=
  seq (Arith.sizeTo 2 1 3) (seq (copyTo 1 2) (seq (assign 0 1) (clearRegs scratch)))

theorem cleanCompute_size :
    CleanCompute sizeProg (fun a : ℕ => Nat.size a) (fun n => 6 * n + 16) := by
  refine cleanCompute_unary (v := fun a => Nat.size a) (T := fun a => 6 * Nat.size a + 6)
    (S := Arith.sizeBlock 2 3) (fun a => rfl)
    (fun m₀ => Arith.runsTo_sizeTo 2 1 3 (by omega) (by omega) (by omega) m₀)
    (by decide) (fun a => ?_)
  show 6 * Nat.size a + 6 + 10 ≤ 6 * Enc.size a + 16
  rw [size_nat a]
  omega

theorem polyTimeClean_size : PolyTimeClean (fun a : ℕ => Nat.size a) :=
  ⟨sizeProg, _, ((polyBound_const 6).mul polyBound_id).add (polyBound_const 16),
    cleanCompute_size⟩

/-- The binary logarithm: the bit length, less one. -/
def log2Prog : Program :=
  seq (seq (Arith.sizeTo 2 1 4) (seq (assign 3 1) (subTo 2 2 3)))
    (seq (copyTo 1 2) (seq (assign 0 1) (clearRegs scratch)))

theorem runsTo_log2Core (m₀ : Mem) :
    RunsTo (seq (Arith.sizeTo 2 1 4) (seq (assign 3 1) (subTo 2 2 3))) (fun m => m = m₀)
      (fun m' => m' 2 = Nat.size (m₀ 1) - 1 ∧ Outside [2, 3, 4, 5, 6, 7] m₀ m')
      (6 * Nat.size (m₀ 1) + 8) := by
  refine RunsTo.mono (T := (6 * Nat.size (m₀ 1) + 6) + (1 + 1)) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => m 2 = Nat.size (m₀ 1) ∧ Outside (Arith.sizeBlock 2 4) m₀ m)
    (Arith.runsTo_sizeTo 2 1 4 (by omega) (by omega) (by omega) m₀) ?_
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq (mid := fun m => m = m₁.update 3 1 ∧
      (m₁ 2 = Nat.size (m₀ 1) ∧ Outside (Arith.sizeBlock 2 4) m₀ m₁))
    (runsTo_assign 3 1 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine runsTo_subTo 2 2 3 (fun m hm => ?_)
  obtain ⟨hm1, hval, hout⟩ := hm
  rw [hm1]
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3), Mem.update_self, hval]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨z2, z3, z4, z5, z6, z7⟩ := hz
    rw [Mem.update_of_ne _ _ z2, Mem.update_of_ne _ _ z3]
    exact hout z (by
      simp only [Arith.sizeBlock, List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega)

theorem cleanCompute_log2 :
    CleanCompute log2Prog (fun a : ℕ => Nat.log 2 a) (fun n => 6 * n + 18) := by
  refine cleanCompute_unary (v := fun a => Nat.size a - 1) (T := fun a => 6 * Nat.size a + 8)
    (S := [2, 3, 4, 5, 6, 7]) (fun a => by rw [log_two_eq_size_sub_one]; rfl)
    runsTo_log2Core (by decide) (fun a => ?_)
  show 6 * Nat.size a + 8 + 10 ≤ 6 * Enc.size a + 18
  rw [size_nat a]
  omega

theorem polyTimeClean_log2 : PolyTimeClean (fun a : ℕ => Nat.log 2 a) :=
  ⟨log2Prog, _, ((polyBound_const 6).mul polyBound_id).add (polyBound_const 18),
    cleanCompute_log2⟩

/-! ## The binary operations -/

theorem cleanCompute_add :
    CleanCompute (seq (addTo 5 2 4) (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch))))
      (fun p : ℕ × ℕ => p.1 + p.2) (fun _ => 11) :=
  cleanCompute_binary (v := fun a b => a + b) (S := [5]) (fun p => rfl)
    (fun m₀ => runsTo_addTo 5 2 4 (fun m hm => by
      subst hm
      exact ⟨Mem.update_self _ _ _, fun z hz => Mem.update_of_ne _ _ (by simpa using hz)⟩))
    (by decide)

theorem polyTimeClean_add : PolyTimeClean (fun p : ℕ × ℕ => p.1 + p.2) :=
  ⟨_, _, polyBound_const 11, cleanCompute_add⟩

theorem cleanCompute_sub :
    CleanCompute (seq (subTo 5 2 4) (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch))))
      (fun p : ℕ × ℕ => p.1 - p.2) (fun _ => 11) :=
  cleanCompute_binary (v := fun a b => a - b) (S := [5]) (fun p => rfl)
    (fun m₀ => runsTo_subTo 5 2 4 (fun m hm => by
      subst hm
      exact ⟨Mem.update_self _ _ _, fun z hz => Mem.update_of_ne _ _ (by simpa using hz)⟩))
    (by decide)

theorem polyTimeClean_sub : PolyTimeClean (fun p : ℕ × ℕ => p.1 - p.2) :=
  ⟨_, _, polyBound_const 11, cleanCompute_sub⟩

theorem cleanCompute_min :
    CleanCompute
      (seq (Arith.minTo 5 2 4 6) (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch))))
      (fun p : ℕ × ℕ => min p.1 p.2) (fun _ => 15) :=
  cleanCompute_binary (v := fun a b => min a b) (fun p => rfl)
    (fun m₀ => Arith.runsTo_minTo 5 2 4 6 (by omega) (by omega) m₀) (by decide)

theorem polyTimeClean_min : PolyTimeClean (fun p : ℕ × ℕ => min p.1 p.2) :=
  ⟨_, _, polyBound_const 15, cleanCompute_min⟩

theorem cleanCompute_max :
    CleanCompute
      (seq (Arith.maxTo 5 2 4 6) (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch))))
      (fun p : ℕ × ℕ => max p.1 p.2) (fun _ => 15) :=
  cleanCompute_binary (v := fun a b => max a b) (fun p => rfl)
    (fun m₀ => Arith.runsTo_maxTo 5 2 4 6 (by omega) (by omega) m₀) (by decide)

theorem polyTimeClean_max : PolyTimeClean (fun p : ℕ × ℕ => max p.1 p.2) :=
  ⟨_, _, polyBound_const 15, cleanCompute_max⟩

/-- The comparison of a pair, as a `Bool`. -/
theorem cleanCompute_le :
    CleanCompute
      (seq (Arith.leTo 5 2 4 6) (seq (copyTo 1 5) (seq (assign 0 1) (clearRegs scratch))))
      (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) (fun _ => 15) :=
  cleanCompute_binary (v := fun a b => if a ≤ b then 1 else 0)
    (fun p => by by_cases h : p.1 ≤ p.2 <;> simp [Enc.encode, h])
    (fun m₀ => Arith.runsTo_leTo 5 2 4 6 m₀) (by decide)

theorem polyTimeClean_le : PolyTimeClean (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) :=
  ⟨_, _, polyBound_const 15, cleanCompute_le⟩

end Small
end RAM
