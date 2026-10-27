import Workspace.Machine.Compose

/-!
# Locality: what a program does depends only on the part of memory it can reach

This file supplies the semantic ingredient that layer (b) was missing (see the "Doubts" section
of `Workspace/Machine/DESIGN.md`).

## The problem it solves

`CleanCompute P f T` (`Workspace/Machine/Compose.lean`) constrains `P` on *one* memory per
input: the run started in exactly `initMem (Enc.encode a)`.  Every combinator that wants to run
a clean routine `P` while keeping data of its own — pairing `a ↦ (f a, g a)`, a conditional on a
computed bit, an iteration that has to remember a counter — must first put that data somewhere,
and then the memory is no longer `initMem (Enc.encode a)`, so `CleanCompute P f T` says nothing
at all about the run.  Saving the data "above the scratch block", as one does inside a routine,
is not enough: `P` is a black box, and `CleanCompute` promises nothing about the registers it
touches on the way.

What is true is that a `T`-step run cannot touch an address above `2 ^ T * B`, where `B` bounds
the initial register contents and the program's constants (`RAM.mem_le_run`, `RAM.mem_eq_run`;
this is the bit-growth lemma, and it is exactly where the absence of a multiplication
instruction is used).  So data stored above that bound survives the call, and the call is
unaffected by it.  The results below turn that observation into usable lemmas.

## Main results

* `RAM.AgreeBelow`: two memories agree at every address below `A`;
* `RAM.run_agree`: if `m₁` has all registers at most `B`, if `2 ^ k * B < A`, and if `m₂` agrees
  with `m₁` below `A`, then for `j ≤ k` steps the two runs have the same program counter, their
  memories agree below `A`, and the run from `m₂` has changed nothing at `A` or above;
* `RAM.CleanCompute.frame`: a clean routine run in a memory that agrees with
  `initMem (Enc.encode a)` below `A` halts, in the same number of steps, in a memory that agrees
  with `initMem (Enc.encode (f a))` below `A` and is unchanged at `A` and above.  This is the
  frame rule for procedure calls: the caller may keep data above `A`.
* `RAM.CleanSolve.frame`: the same for the relational form.

The price is that `A` is exponential in the running time.  That is affordable: the *address*
`2 ^ T` has only `T` bits, and a machine can produce it in `T` steps by doubling a register, so a
caller that saves its data there pays a polynomial number of steps for a polynomial `T`.  What it
costs is a routine that computes the address; see the "Doubts" section of `DESIGN.md` for what is
still missing before this can be assembled into the pairing and conditional combinators.
-/

namespace RAM

variable {α β : Type*}

/-! ## Agreement below an address -/

/-- `AgreeBelow A m₁ m₂`: the memories `m₁` and `m₂` hold the same value in every register below
address `A`.  Nothing is said about the registers at `A` and above. -/
def AgreeBelow (A : ℕ) (m₁ m₂ : Mem) : Prop := ∀ z, z < A → m₁ z = m₂ z

theorem AgreeBelow.refl (A : ℕ) (m : Mem) : AgreeBelow A m m := fun _ _ => rfl

theorem AgreeBelow.symm {A : ℕ} {m₁ m₂ : Mem} (h : AgreeBelow A m₁ m₂) :
    AgreeBelow A m₂ m₁ := fun z hz => (h z hz).symm

theorem AgreeBelow.trans {A : ℕ} {m₁ m₂ m₃ : Mem} (h : AgreeBelow A m₁ m₂)
    (h' : AgreeBelow A m₂ m₃) : AgreeBelow A m₁ m₃ := fun z hz => (h z hz).trans (h' z hz)

theorem AgreeBelow.mono {A A' : ℕ} {m₁ m₂ : Mem} (h : AgreeBelow A m₁ m₂) (hA : A' ≤ A) :
    AgreeBelow A' m₁ m₂ := fun z hz => h z (lt_of_lt_of_le hz hA)

/-- Writing the same value at the same address on both sides preserves agreement. -/
theorem AgreeBelow.update {A : ℕ} {m₁ m₂ : Mem} (h : AgreeBelow A m₁ m₂) (x v : ℕ) :
    AgreeBelow A (m₁.update x v) (m₂.update x v) := by
  intro z hz
  unfold Mem.update
  split
  · rfl
  · exact h z hz

/-- A write below `A` does not change any register at `A` or above. -/
theorem update_eq_of_high {m : Mem} {x v A z : ℕ} (hx : x < A) (hz : A ≤ z) :
    m.update x v z = m z := Mem.update_of_ne _ _ (by omega)

/-! ## One step -/

/-- **One step is local.**  Two configurations with the same program counter, whose memories
agree below `A`, and where the first one has all its registers below `A` (so that no address at
or above `A` can be named), take the same step: the program counters stay equal, the memories
still agree below `A`, and the second run has written nothing at `A` or above. -/
theorem step_agree {P : Program} {c₁ c₂ : Config} {A : ℕ}
    (hPA : P.bound < A) (hval : ∀ a, c₁.mem a < A)
    (hpc : c₁.pc = c₂.pc) (hmem : AgreeBelow A c₁.mem c₂.mem) :
    (step P c₁).pc = (step P c₂).pc ∧ AgreeBelow A (step P c₁).mem (step P c₂).mem ∧
      ∀ z, A ≤ z → (step P c₂).mem z = c₂.mem z := by
  by_cases h : Halted P c₁
  · have h2 : Halted P c₂ := by
      unfold Halted at h ⊢; rw [← hpc]; exact h
    rw [step_of_halted h, step_of_halted h2]
    exact ⟨hpc, hmem, fun _ _ => rfl⟩
  · obtain ⟨i, hi, hne⟩ := not_halted_iff.1 h
    have hi2 : P[c₂.pc]? = some i := by rw [← hpc]; exact hi
    have hb : i.bound ≤ P.bound := bound_of_get hi
    rw [step_of_get hi hne, step_of_get hi2 hne]
    obtain ⟨p₁, m₁⟩ := c₁
    obtain ⟨p₂, m₂⟩ := c₂
    simp only at hpc hval hmem hb ⊢
    subst hpc
    -- every register index named by `i` is below `A`
    cases i with
    | const x v =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        refine ⟨rfl, ?_, fun z hz => ?_⟩
        · show AgreeBelow A (m₁.update x v) (m₂.update x v)
          exact hmem.update x v
        · show (m₂.update x v) z = m₂ z
          exact update_eq_of_high hx hz
    | copy x y =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        have hy : y < A := by omega
        refine ⟨rfl, ?_, fun z hz => ?_⟩
        · show AgreeBelow A (m₁.update x (m₁ y)) (m₂.update x (m₂ y))
          rw [← hmem y hy]
          exact hmem.update x _
        · show (m₂.update x (m₂ y)) z = m₂ z
          exact update_eq_of_high hx hz
    | add x y z =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        have hy : y < A := by omega
        have hz' : z < A := by omega
        refine ⟨rfl, ?_, fun w hw => ?_⟩
        · show AgreeBelow A (m₁.update x (m₁ y + m₁ z)) (m₂.update x (m₂ y + m₂ z))
          rw [← hmem y hy, ← hmem z hz']
          exact hmem.update x _
        · show (m₂.update x (m₂ y + m₂ z)) w = m₂ w
          exact update_eq_of_high hx hw
    | sub x y z =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        have hy : y < A := by omega
        have hz' : z < A := by omega
        refine ⟨rfl, ?_, fun w hw => ?_⟩
        · show AgreeBelow A (m₁.update x (m₁ y - m₁ z)) (m₂.update x (m₂ y - m₂ z))
          rw [← hmem y hy, ← hmem z hz']
          exact hmem.update x _
        · show (m₂.update x (m₂ y - m₂ z)) w = m₂ w
          exact update_eq_of_high hx hw
    | load x y =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        have hy : y < A := by omega
        have haddr : m₁ y = m₂ y := hmem y hy
        have hlt : m₁ y < A := hval y
        refine ⟨rfl, ?_, fun z hz => ?_⟩
        · show AgreeBelow A (m₁.update x (m₁ (m₁ y))) (m₂.update x (m₂ (m₂ y)))
          rw [← haddr, ← hmem (m₁ y) hlt]
          exact hmem.update x _
        · show (m₂.update x (m₂ (m₂ y))) z = m₂ z
          exact update_eq_of_high hx hz
    | store x y =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        have hy : y < A := by omega
        have haddr : m₁ x = m₂ x := hmem x hx
        have hlt : m₂ x < A := by rw [← haddr]; exact hval x
        refine ⟨rfl, ?_, fun z hz => ?_⟩
        · show AgreeBelow A (m₁.update (m₁ x) (m₁ y)) (m₂.update (m₂ x) (m₂ y))
          rw [← haddr, ← hmem y hy]
          exact hmem.update _ _
        · show (m₂.update (m₂ x) (m₂ y)) z = m₂ z
          exact update_eq_of_high hlt hz
    | jump t => exact ⟨rfl, hmem, fun _ _ => rfl⟩
    | jz x t =>
        simp only [Instr.bound] at hb
        have hx : x < A := by omega
        refine ⟨?_, hmem, fun _ _ => rfl⟩
        show (if m₁ x = 0 then t else p₁ + 1) = (if m₂ x = 0 then t else p₁ + 1)
        rw [hmem x hx]
    | halt => exact absurd rfl hne

/-! ## The whole run -/

/-- **Locality of a run.**  Let `P` have all its constants and register indices at most `B`, let
`m₁` hold values at most `B` in every register, and let `A` be above `2 ^ k * B`, the bound of
`RAM.mem_le_run` on what `k` steps can reach.  Then a memory `m₂` that agrees with `m₁` below `A`
— however it is filled at `A` and above — leads to the same run for `j ≤ k` steps: same program
counter, memories agreeing below `A`, and nothing at `A` or above touched. -/
theorem run_agree {P : Program} {m₁ m₂ : Mem} {A B k : ℕ}
    (hP : P.bound ≤ B) (hm₁ : ∀ a, m₁ a ≤ B) (hA : 2 ^ k * B < A)
    (hagree : AgreeBelow A m₁ m₂) :
    ∀ j ≤ k, (run P ⟨0, m₁⟩ j).pc = (run P ⟨0, m₂⟩ j).pc ∧
      AgreeBelow A (run P ⟨0, m₁⟩ j).mem (run P ⟨0, m₂⟩ j).mem ∧
      (∀ z, A ≤ z → (run P ⟨0, m₂⟩ j).mem z = m₂ z) := by
  have hBA : B < A := by
    have : B ≤ 2 ^ k * B := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
    omega
  have hPA : P.bound < A := by omega
  intro j
  induction j with
  | zero => exact fun _ => ⟨rfl, hagree, fun _ _ => rfl⟩
  | succ j ih =>
      intro hjk
      obtain ⟨hpc, hmem, hhigh⟩ := ih (by omega)
      have hval : ∀ a, (run P ⟨0, m₁⟩ j).mem a < A := by
        intro a
        have h1 := mem_le_run (P := P) (c := ⟨0, m₁⟩) hP hm₁ j a
        have h2 : (2:ℕ) ^ j * B ≤ 2 ^ k * B :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        omega
      obtain ⟨h1, h2, h3⟩ := step_agree (P := P) hPA hval hpc hmem
      refine ⟨h1, h2, fun z hz => ?_⟩
      rw [run_succ, h3 z hz, hhigh z hz]

/-! ## The frame rule for clean routines -/

/-- The largest value occurring in the initial memory of a list: the length and the entries. -/
def listBound (l : List ℕ) : ℕ := max l.length (l.foldr max 0)

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact le_trans (ih h) (by simp)

theorem initMem_le_listBound (l : List ℕ) : ∀ a, initMem l a ≤ listBound l :=
  initMem_le l _ (le_max_left _ _) (fun _ hx => le_trans (le_foldr_max hx) (le_max_right _ _))

/-- **The frame rule.**  A clean routine `P` for `f`, started in a memory that agrees with
`initMem (Enc.encode a)` below `A`, with `A` above the reach `2 ^ T * B` of the run, halts within
the same number of steps in a memory that agrees with `initMem (Enc.encode (f a))` below `A` and
that is unchanged at `A` and above.

This is what a caller needs in order to run a clean routine while keeping data of its own: put
the data at addresses `A` and above. -/
theorem CleanCompute.frame [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : CleanCompute P f T) (a : α) {A B : ℕ}
    (hP : P.bound ≤ B) (hB : ∀ z, initMem (Enc.encode a) z ≤ B)
    (hA : 2 ^ (T (Enc.size a)) * B < A)
    (m : Mem) (hm : AgreeBelow A (initMem (Enc.encode a)) m) :
    ∃ k ≤ T (Enc.size a), Halted P (run P ⟨0, m⟩ k) ∧
      AgreeBelow A (initMem (Enc.encode (f a))) (run P ⟨0, m⟩ k).mem ∧
      (∀ z, A ≤ z → (run P ⟨0, m⟩ k).mem z = m z) := by
  obtain ⟨k, hk, hhalt, hmem⟩ := (h a).spec (initMem (Enc.encode a)) rfl
  obtain ⟨hpc, hag, hhigh⟩ :=
    run_agree (P := P) (m₁ := initMem (Enc.encode a)) (m₂ := m) (A := A) (B := B)
      (k := T (Enc.size a)) hP hB hA hm k hk
  refine ⟨k, hk, ?_, ?_, hhigh⟩
  · unfold Halted at hhalt ⊢; rw [← hpc]; exact hhalt
  · rw [← hmem]; exact hag

/-- The frame rule with the bound `B` chosen: the program's own constants and the contents of the
input memory. -/
theorem CleanCompute.frame' [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : CleanCompute P f T) (a : α) {A : ℕ}
    (hA : 2 ^ (T (Enc.size a)) * (max P.bound (listBound (Enc.encode a))) < A)
    (m : Mem) (hm : AgreeBelow A (initMem (Enc.encode a)) m) :
    ∃ k ≤ T (Enc.size a), Halted P (run P ⟨0, m⟩ k) ∧
      AgreeBelow A (initMem (Enc.encode (f a))) (run P ⟨0, m⟩ k).mem ∧
      (∀ z, A ≤ z → (run P ⟨0, m⟩ k).mem z = m z) :=
  h.frame a (le_max_left _ _)
    (fun z => le_trans (initMem_le_listBound _ z) (le_max_right _ _)) hA m hm

/-- **The frame rule, relational form.**  The same statement for a routine that solves a search
problem: some admissible answer is delivered below `A`, and the caller's data above `A` is
intact. -/
theorem CleanSolve.frame [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T : ℕ → ℕ}
    (h : CleanSolve P R T) (a : α) {A B : ℕ}
    (hP : P.bound ≤ B) (hB : ∀ z, initMem (Enc.encode a) z ≤ B)
    (hA : 2 ^ (T (Enc.size a)) * B < A)
    (m : Mem) (hm : AgreeBelow A (initMem (Enc.encode a)) m) :
    ∃ b : β, R a b ∧ ∃ k ≤ T (Enc.size a), Halted P (run P ⟨0, m⟩ k) ∧
      AgreeBelow A (initMem (Enc.encode b)) (run P ⟨0, m⟩ k).mem ∧
      (∀ z, A ≤ z → (run P ⟨0, m⟩ k).mem z = m z) := by
  obtain ⟨b, hb, hrun⟩ := h a
  obtain ⟨k, hk, hhalt, hmem⟩ := hrun.spec (initMem (Enc.encode a)) rfl
  obtain ⟨hpc, hag, hhigh⟩ :=
    run_agree (P := P) (m₁ := initMem (Enc.encode a)) (m₂ := m) (A := A) (B := B)
      (k := T (Enc.size a)) hP hB hA hm k hk
  refine ⟨b, hb, k, hk, ?_, ?_, hhigh⟩
  · unfold Halted at hhalt ⊢; rw [← hpc]; exact hhalt
  · rw [← hmem]; exact hag

/-! ## A reach bound in the form a caller uses

The address a caller must go above is `2 ^ T * B`.  The two lemmas below record that this is
also an upper bound on the addresses a run can *write*, which is the form in which a caller
argues that its own data is safe. -/

/-- In `k` steps a program writes no register above `2 ^ k * B`. -/
theorem run_untouched_above {P : Program} {m : Mem} {B k : ℕ} (hP : P.bound ≤ B)
    (hm : ∀ a, m a ≤ B) {z : ℕ} (hz : 2 ^ k * B < z) : (run P ⟨0, m⟩ k).mem z = m z :=
  mem_eq_run hP hm k z hz

end RAM
