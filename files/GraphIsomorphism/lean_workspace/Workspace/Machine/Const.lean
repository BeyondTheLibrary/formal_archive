import Workspace.Machine.Compose

/-!
# Erasing the input, and the constant functions

Every clean routine has to leave the memory *exactly* `initMem` of its output
(`Workspace/Machine/Compose.lean`), so the very first thing a routine of this model needs is a
way to wipe the input region.  This file writes that routine, and with it the first family of
clean programs at the top-level convention: the constant functions.

## Why this is the first routine that can be written

At the top-level convention the input occupies registers `0, 1, ..., n` with `n` the value of
register `0`, so for a large input *no* register with a fixed index is free: a routine cannot
even initialize a loop counter without destroying a register it may still need.  (See the
"Doubts" section of `Workspace/Machine/DESIGN.md`.)  A routine that is *allowed* to destroy the
input has no such problem, and erasing is exactly that routine.

`eraseProg` keeps its five scratch cells at the fixed addresses `0, 1, 2, 3, 4`:

* register `0` doubles as the pointer, walking down from `n`;
* register `1` holds the constant `1` (the decrement), register `2` the constant `0` (the value
  stored), register `3` the constant `3`;
* register `4` holds `R0 - 3` and controls the loop, so the loop stops before the pointer reaches
  the cells holding the constants.

The loop zeroes registers `n, n - 1, ..., 4`; registers `0, 1, 2, 3, 4` are then zeroed by five
constant assignments, and registers above `n` were zero to begin with.  The result is the
all-zero memory, that is, `initMem []`.  The cost is `5 * n + 10` steps.

## Main results

* `RAM.runsTo_eraseProg`: from any `initMem l` the program halts in the all-zero memory;
* `RAM.runsTo_writeFrom`, `RAM.runsTo_writeMem`: writing a fixed list into the memory;
* `RAM.cleanCompute_const`, `RAM.polyTimeClean_const`: a constant function is computed by a clean
  program in linear time, hence lies in `PolyTimeClean` (and so in `QuasiPolyTimeClean`).
-/

namespace RAM

variable {α β : Type*}

/-! ## The erasing loop -/

/-- The body of the erasing loop: store `0` at the address in register `0`, step the pointer
down, recompute the loop control `R0 - 3`. -/
def eraseBody : Program := seq (storeTo 0 2) (seq (subTo 0 0 1) (subTo 4 0 3))

/-- The set-up of the erasing loop: the constants `1`, `0`, `3` and the loop control. -/
def erasePre : Program := seq (assign 1 1) (seq (assign 2 0) (seq (assign 3 3) (subTo 4 0 3)))

/-- The five constant assignments that clear the scratch cells after the loop. -/
def erasePost : Program :=
  seq (assign 0 0) (seq (assign 1 0) (seq (assign 2 0) (seq (assign 3 0) (assign 4 0))))

/-- `eraseProg` zeroes the whole memory of the input convention. -/
def eraseProg : Program := seq erasePre (seq (whileNz 4 eraseBody) erasePost)

/-- The invariant of the erasing loop: the three constants are in place, register `4` holds
`R0 - 3`, the pointer has not passed `n`, and every register at `4` or above that the pointer has
already passed is zero. -/
def EraseInv (n : ℕ) (m : Mem) : Prop :=
  m 1 = 1 ∧ m 2 = 0 ∧ m 3 = 3 ∧ m 4 = m 0 - 3 ∧ m 0 ≤ n ∧ ∀ z, 4 ≤ z → m 0 < z → m z = 0

theorem runsTo_erasePre (l : List ℕ) :
    RunsTo erasePre (fun m => m = initMem l)
      (fun m' => EraseInv l.length m' ∧ m' 0 = l.length) 4 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + 1))) ?_ (by norm_num)
  set m₀ : Mem := initMem l with hm₀
  have h0 : m₀ 0 = l.length := by simp [hm₀, initMem]
  have hzero : ∀ z, l.length < z → m₀ z = 0 := by
    intro z hz
    simp only [hm₀, initMem]
    rw [if_neg (by omega), List.getD_eq_default _ _ (by omega)]
  refine RunsTo.seq (mid := fun m => m = m₀.update 1 1)
    (runsTo_assign 1 1 (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := fun m => m = (m₀.update 1 1).update 2 0)
    (runsTo_assign 2 0 (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := fun m => m = ((m₀.update 1 1).update 2 0).update 3 3)
    (runsTo_assign 3 3 (fun m hm => by rw [hm])) ?_
  refine runsTo_subTo 4 0 3 (fun m hm => ?_)
  rw [hm]
  set m₁ : Mem := ((m₀.update 1 1).update 2 0).update 3 3 with hm₁
  have e0 : m₁ 0 = l.length := by
    rw [hm₁, Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 3),
      Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 2),
      Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 1), h0]
  have e1 : m₁ 1 = 1 := by
    rw [hm₁, Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 3),
      Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 2), Mem.update_self]
  have e2 : m₁ 2 = 0 := by
    rw [hm₁, Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 3), Mem.update_self]
  have e3 : m₁ 3 = 3 := by rw [hm₁, Mem.update_self]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 4), e1]
  · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 4), e2]
  · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 4), e3]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), e0, e3]
  · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), e0]
  · intro z hz4 hz
    rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), e0] at hz
    have hzl : l.length < z := hz
    by_cases h4 : z = 4
    · subst h4
      rw [Mem.update_self, e0, e3]
      omega
    · rw [Mem.update_of_ne _ _ h4, hm₁, Mem.update_of_ne _ _ (by omega : z ≠ 3),
        Mem.update_of_ne _ _ (by omega : z ≠ 2), Mem.update_of_ne _ _ (by omega : z ≠ 1)]
      exact hzero z hzl
  · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), e0]

/-- One iteration of the erasing loop: zero the register the pointer names, step down. -/
theorem runsTo_eraseBody (n k : ℕ) :
    RunsTo eraseBody (fun m => EraseInv n m ∧ m 4 = k + 1)
      (fun m' => EraseInv n m' ∧ m' 4 = k) 3 := by
  refine RunsTo.mono (T := 1 + (1 + 1)) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  set K : Prop := EraseInv n m₁ ∧ m₁ 4 = k + 1 with hK
  refine RunsTo.seq (mid := fun m => m = m₁.update (m₁ 0) (m₁ 2) ∧ K)
    (runsTo_storeTo 0 2 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m =>
      m = (m₁.update (m₁ 0) (m₁ 2)).update 0 (m₁ 0 - m₁ 1) ∧ K)
    (runsTo_subTo 0 0 1 (fun m hm => ⟨?_, hm.2⟩)) ?_
  · obtain ⟨hm1, ⟨e1, e2, e3, e4, e5, e6⟩, hk⟩ := hm
    have hptr : 4 ≤ m₁ 0 := by omega
    rw [hm1]
    congr 1
    rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ m₁ 0),
      Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ m₁ 0)]
  refine runsTo_subTo 4 0 3 (fun m hm => ?_)
  obtain ⟨hm1, hpre⟩ := hm
  obtain ⟨⟨e1, e2, e3, e4, e5, e6⟩, hk⟩ := id hpre
  have hptr : 4 ≤ m₁ 0 := by omega
  rw [hm1]
  set m₂ : Mem := (m₁.update (m₁ 0) (m₁ 2)).update 0 (m₁ 0 - m₁ 1) with hm₂
  have f0 : m₂ 0 = m₁ 0 - 1 := by rw [hm₂, Mem.update_self, e1]
  have f1 : m₂ 1 = 1 := by
    rw [hm₂, Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 0),
      Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ m₁ 0), e1]
  have f2 : m₂ 2 = 0 := by
    rw [hm₂, Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 0),
      Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ m₁ 0), e2]
  have f3 : m₂ 3 = 3 := by
    rw [hm₂, Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 0),
      Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ m₁ 0), e3]
  have fhigh : ∀ z, 4 ≤ z → m₁ 0 - 1 < z → z ≠ 4 → m₂ z = 0 := by
    intro z hz4 hz hz'
    rcases Nat.lt_or_ge (m₁ 0) z with h | h
    · rw [hm₂, Mem.update_of_ne _ _ (by omega : z ≠ 0),
        Mem.update_of_ne _ _ (by omega : z ≠ m₁ 0)]
      exact e6 z hz4 h
    · have hzm : z = m₁ 0 := by omega
      rw [hm₂, Mem.update_of_ne _ _ (by omega : z ≠ 0), hzm, Mem.update_self, e2]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 4), f1]
  · rw [Mem.update_of_ne _ _ (by omega : (2:ℕ) ≠ 4), f2]
  · rw [Mem.update_of_ne _ _ (by omega : (3:ℕ) ≠ 4), f3]
  · rw [Mem.update_self, Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), f0, f3]
  · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), f0]; omega
  · intro z hz4 hz
    rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 4), f0] at hz
    by_cases hz' : z = 4
    · subst hz'
      rw [Mem.update_self, f0, f3]
      omega
    · rw [Mem.update_of_ne _ _ hz']
      exact fhigh z hz4 (by omega) hz'
  · rw [Mem.update_self, f0, f3]
    omega

/-- The five assignments that clear the scratch cells: from a memory satisfying the invariant
with the loop finished, the memory becomes all zero. -/
theorem runsTo_erasePost (n : ℕ) :
    RunsTo erasePost (fun m => EraseInv n m ∧ m 4 = 0) (fun m' => m' = fun _ => 0) 5 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  set K : Prop := EraseInv n m₁ ∧ m₁ 4 = 0 with hK
  refine RunsTo.seq (mid := fun m => m = m₁.update 0 0 ∧ K)
    (runsTo_assign 0 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m => m = (m₁.update 0 0).update 1 0 ∧ K)
    (runsTo_assign 1 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m => m = ((m₁.update 0 0).update 1 0).update 2 0 ∧ K)
    (runsTo_assign 2 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq
    (mid := fun m => m = (((m₁.update 0 0).update 1 0).update 2 0).update 3 0 ∧ K)
    (runsTo_assign 3 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine runsTo_assign 4 0 (fun m hm => ?_)
  obtain ⟨hm1, ⟨e1, e2, e3, e4, e5, e6⟩, hk⟩ := hm
  have hsmall : m₁ 0 ≤ 3 := by omega
  rw [hm1]
  funext z
  by_cases h4 : z = 4
  · subst h4; rw [Mem.update_self]
  rw [Mem.update_of_ne _ _ h4]
  by_cases h3 : z = 3
  · subst h3; rw [Mem.update_self]
  rw [Mem.update_of_ne _ _ h3]
  by_cases h2 : z = 2
  · subst h2; rw [Mem.update_self]
  rw [Mem.update_of_ne _ _ h2]
  by_cases h1 : z = 1
  · subst h1; rw [Mem.update_self]
  rw [Mem.update_of_ne _ _ h1]
  by_cases h0 : z = 0
  · subst h0; rw [Mem.update_self]
  rw [Mem.update_of_ne _ _ h0]
  exact e6 z (by omega) (by omega)

/-- **Erasing the input.**  From `initMem l` the program `eraseProg` halts in the all-zero
memory, in `5 * l.length + 10` steps. -/
theorem runsTo_eraseProg (l : List ℕ) :
    RunsTo eraseProg (fun m => m = initMem l) (fun m' => m' = fun _ => 0)
      (5 * l.length + 10) := by
  refine RunsTo.mono (T := 4 + (l.length * (3 + 2) + 1 + 5)) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => EraseInv l.length m ∧ m 0 = l.length)
    (runsTo_erasePre l) ?_
  refine RunsTo.seq (mid := fun m => EraseInv l.length m ∧ m 4 = 0) ?_ (runsTo_erasePost _)
  refine (runsTo_forLoop (N := l.length)
    (fun k => runsTo_eraseBody l.length k) ?_).strengthen (fun m hm => hm.1)
  rintro m ⟨e1, e2, e3, e4, e5, e6⟩
  omega

/-! ## Writing a fixed list into the memory -/

/-- `writeFrom i l` writes the entries of `l` into the registers `i, i + 1, ...`, one
`R x ← c` instruction each. -/
def writeFrom (i : ℕ) : List ℕ → Program
  | [] => []
  | x :: l => seq (assign i x) (writeFrom (i + 1) l)

theorem runsTo_writeFrom (i : ℕ) (l : List ℕ) (m₀ : Mem) :
    RunsTo (writeFrom i l) (fun m => m = m₀)
      (fun m' => (∀ j, j < l.length → m' (i + j) = l.getD j 0) ∧
        (∀ z, z < i → m' z = m₀ z) ∧ (∀ z, i + l.length ≤ z → m' z = m₀ z))
      l.length := by
  induction l generalizing i m₀ with
  | nil =>
      refine runsTo_nil (fun m hm => ?_)
      subst hm
      exact ⟨fun j hj => by simp at hj, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x l ih =>
      refine RunsTo.mono (T := 1 + l.length) ?_ (by simp; omega)
      refine RunsTo.seq (mid := fun m => m = m₀.update i x)
        (runsTo_assign i x (fun m hm => by rw [hm])) ?_
      refine (ih (i + 1) (m₀.update i x)).weaken (fun m' hm' => ?_)
      obtain ⟨hval, hlow, hhigh⟩ := hm'
      have hi : m' i = x := by
        rw [hlow i (by omega), Mem.update_self]
      refine ⟨fun j hj => ?_, fun z hz => ?_, fun z hz => ?_⟩
      · cases j with
        | zero => simpa using hi
        | succ j =>
            have hj' : j < l.length := by simpa using hj
            have := hval j hj'
            rw [show i + (j + 1) = i + 1 + j by omega, this]
            simp [List.getD]
      · rw [hlow z (by omega), Mem.update_of_ne _ _ (by omega : z ≠ i)]
      · rw [hhigh z (by simp at hz ⊢; omega), Mem.update_of_ne _ _ (by simp at hz; omega : z ≠ i)]

/-- Writing a fixed list into the all-zero memory produces exactly `initMem l`. -/
theorem runsTo_writeMem (l : List ℕ) :
    RunsTo (seq (writeFrom 1 l) (assign 0 l.length)) (fun m => m = fun _ => 0)
      (fun m' => m' = initMem l) (l.length + 1) := by
  refine RunsTo.seq (T := l.length) (T' := 1)
    (mid := fun m => (∀ j, j < l.length → m (1 + j) = l.getD j 0) ∧
      (∀ z, 1 + l.length ≤ z → m z = 0)) ?_ ?_
  · exact (runsTo_writeFrom 1 l (fun _ => 0)).weaken
      (fun m' hm' => ⟨hm'.1, fun z hz => hm'.2.2 z hz⟩)
  · refine runsTo_assign 0 l.length (fun m hm => ?_)
    obtain ⟨hval, hhigh⟩ := hm
    funext z
    by_cases h0 : z = 0
    · subst h0
      rw [Mem.update_self]
      simp [initMem]
    rw [Mem.update_of_ne _ _ h0]
    have hz : 1 ≤ z := by omega
    by_cases hlt : z - 1 < l.length
    · have := hval (z - 1) hlt
      rw [show 1 + (z - 1) = z by omega] at this
      rw [this]
      simp [initMem, h0]
    · rw [hhigh z (by omega)]
      simp only [initMem, if_neg h0]
      rw [List.getD_eq_default _ _ (by omega)]

/-! ## The constant functions -/

/-- The program of a constant function: erase the input, then write the fixed encoding. -/
def constProg (l : List ℕ) : Program := seq eraseProg (seq (writeFrom 1 l) (assign 0 l.length))

/-- The time bound of `constProg l`: erasing costs `5 n + 10` steps and writing the answer one
step per register. -/
def constTime (l : List ℕ) (n : ℕ) : ℕ := 5 * n + (10 + (l.length + 1))

theorem polyBound_constTime (l : List ℕ) : PolyBound (constTime l) :=
  ((polyBound_const 5).mul polyBound_id).add (polyBound_const (10 + (l.length + 1)))

/-- **A constant function is computed by a clean program in linear time.** -/
theorem cleanCompute_const [Enc α] [Enc β] (c : β) :
    CleanCompute (constProg (Enc.encode c)) (fun _ : α => c) (constTime (Enc.encode c)) := by
  intro a
  refine ((runsTo_eraseProg (Enc.encode a)).seq (runsTo_writeMem (Enc.encode c))).mono ?_
  have h : (Enc.encode a).length < Enc.size a := length_lt_listSize _
  show 5 * (Enc.encode a).length + 10 + ((Enc.encode c).length + 1)
    ≤ constTime (Enc.encode c) (Enc.size a)
  simp only [constTime]
  omega

theorem polyTimeClean_const [Enc α] [Enc β] (c : β) : PolyTimeClean (fun _ : α => c) :=
  ⟨constProg (Enc.encode c), _, polyBound_constTime _, cleanCompute_const c⟩

theorem quasiPolyTimeClean_const [Enc α] [Enc β] (c : β) : QuasiPolyTimeClean (fun _ : α => c) :=
  (polyTimeClean_const c).quasiPolyTimeClean

/-! ## Functions of a bit

A function defined on `Bool` is a two-way case distinction between two constants, so it is
computed by one conditional around two constant programs.  Composed with a clean predicate
(`RAM.PolyTimeClean.comp`) this is the conditional `fun a => if p a then c₁ else c₂`: the
branches must be constants, because the predicate's routine has consumed the input.  A
conditional whose branches use the input again needs the frame rule of
`Workspace/Machine/Locality.lean` and the missing work described in `DESIGN.md`. -/

/-- The program of a function on `Bool`: test register `1`, which holds the bit, and write the
corresponding constant. -/
def boolProg (l₁ l₀ : List ℕ) : Program := ifz 1 (constProg l₁) (constProg l₀)

/-- **A function of one bit is computed by a clean program in linear time.** -/
theorem cleanCompute_ofBool [Enc β] (f : Bool → β) :
    CleanCompute (boolProg (Enc.encode (f true)) (Enc.encode (f false))) f
      (fun n => constTime (Enc.encode (f true)) n + constTime (Enc.encode (f false)) n + 2) := by
  have hwf₁ : Wf (constProg (Enc.encode (f true))) :=
    (cleanCompute_const (α := Bool) (f true) true).wf
  have hwf₀ : Wf (constProg (Enc.encode (f false))) :=
    (cleanCompute_const (α := Bool) (f false) false).wf
  intro b
  cases b with
  | true =>
      have hone : (initMem (Enc.encode true)) 1 = 1 := by
        show (initMem [1]) 1 = 1
        simp [initMem]
      refine (RunsTo.ifz (i := 1)
        ((cleanCompute_const (α := Bool) (f true) true).strengthen (fun m hm => hm.1))
        (runsTo_of_false (T := 0) hwf₀ (fun m hm => ?_))).mono ?_
      · have h1 : m 1 = 1 := by rw [hm.1]; exact hone
        omega
      · show constTime (Enc.encode (f true)) (Enc.size true) + 0 + 2
          ≤ constTime (Enc.encode (f true)) (Enc.size true)
            + constTime (Enc.encode (f false)) (Enc.size true) + 2
        omega
  | false =>
      have hzero : (initMem (Enc.encode false)) 1 = 0 := by
        show (initMem [0]) 1 = 0
        simp [initMem]
      refine (RunsTo.ifz (i := 1)
        (runsTo_of_false (T := 0) hwf₁ (fun m hm => ?_))
        ((cleanCompute_const (α := Bool) (f false) false).strengthen (fun m hm => hm.1))).mono ?_
      · exact hm.2 (by rw [hm.1]; exact hzero)
      · show 0 + constTime (Enc.encode (f false)) (Enc.size false) + 2
          ≤ constTime (Enc.encode (f true)) (Enc.size false)
            + constTime (Enc.encode (f false)) (Enc.size false) + 2
        omega

theorem polyTimeClean_ofBool [Enc β] (f : Bool → β) : PolyTimeClean f := by
  refine ⟨boolProg (Enc.encode (f true)) (Enc.encode (f false)), _, ?_,
    cleanCompute_ofBool f⟩
  exact ((polyBound_constTime _).add (polyBound_constTime _)).add (polyBound_const 2)

/-- **The conditional with constant branches.**  If the predicate is clean and polynomial time,
so is `fun a => if p a then c₁ else c₂`. -/
theorem polyTimeClean_ifConst [Enc α] [Enc β] {p : α → Bool} (hp : PolyTimeClean p) (c₁ c₀ : β) :
    PolyTimeClean (fun a => if p a then c₁ else c₀) :=
  hp.comp (polyTimeClean_ofBool (fun b : Bool => if b then c₁ else c₀))
    (polyBound_const 3) (fun a => by
      cases p a <;> simp [Enc.size, listSize, Enc.encode, Nat.size])

end RAM
