import Workspace.Machine.Arith

/-!
# Arrays in memory

An array is a block of consecutive registers.  A routine is told where a block starts and how
long it is by two registers holding the base address and the length, and walks the block with a
counter loop (`RAM.runsTo_forLoop`), one indirect load or store per entry.  The cost of a
traversal is therefore `length * (body + 2) + 1`, which is the shape the paper's procedures need:
linear in the number of entries, with the cost of the body visible.

The register discipline is the one of `Workspace/Machine/Arith.lean`: arguments below the
scratch base `s`, scratch in `s, s+1, ...`.  Blocks are required to lie **above** the scratch
block (`s + 4 ≤ base`); this is the "bump-allocated heap above a known bound" of `DESIGN.md`, and
it is what keeps an indirect store from destroying the routine's own scratch.

## Main results

* `RAM.Arrays.runsTo_fillZero`: zero a block of `n` registers in `5 * n + 5` steps.  This is the
  primitive behind the cleanliness discipline of `Workspace/Machine/Compose.lean`: a routine that
  has used a heap region erases it before returning.
* `RAM.Arrays.runsTo_copyBlock`: copy a block of `n` registers in `7 * n + 5` steps.  The loop
  copies in increasing index order, so the destination block may lie anywhere below the source
  block — overlapping or not — or strictly above it; this is the hypothesis `hdisj`, and the
  downward case is what a routine uses to move a computed result back to the base of its
  workspace.
-/

namespace RAM
namespace Arrays

/-! ## Zeroing a block -/

/-- The body of `fillZero`: store `0` at the current address, advance, count down. -/
def fillBody (s : ℕ) : Program :=
  seq (storeTo s (s + 2)) (seq (addTo s s (s + 3)) (subTo (s + 1) (s + 1) (s + 3)))

/-- `fillZero b n s` writes `0` into the `R n` registers starting at address `R b`.
Scratch: `s` (the running address), `s+1` (the counter), `s+2` (the constant `0`), `s+3` (the
constant `1`). -/
def fillPre (b n s : ℕ) : Program :=
  seq (copyTo s b) (seq (copyTo (s + 1) n) (seq (assign (s + 2) 0) (assign (s + 3) 1)))

/-- `fillZero b n s` writes `0` into the `R n` registers starting at address `R b`. -/
def fillZero (b n s : ℕ) : Program := seq (fillPre b n s) (whileNz (s + 1) (fillBody s))

/-- The loop invariant of `fillZero`: `i` entries have been zeroed, the address register points
just past them, the counter holds what is left, and nothing outside the block and the scratch has
changed. -/
def FillInv (b n s : ℕ) (m₀ : Mem) (m : Mem) : Prop :=
  ∃ i ≤ m₀ n, m s = m₀ b + i ∧ m (s + 1) = m₀ n - i ∧ m (s + 2) = 0 ∧ m (s + 3) = 1 ∧
    (∀ z, m₀ b ≤ z → z < m₀ b + i → m z = 0) ∧
    (∀ z, ¬ (m₀ b ≤ z ∧ z < m₀ b + i) → z ∉ [s, s + 1, s + 2, s + 3] → m z = m₀ z)

theorem runsTo_fillPre (b n s : ℕ) (hb : b < s) (hn : n < s) (m₀ : Mem) :
    RunsTo (fillPre b n s) (fun m => m = m₀) (fun m' => FillInv b n s m₀ m') 4 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + 1))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ b))
    (runsTo_copyTo s b (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := fun m => m = (m₀.update s (m₀ b)).update (s + 1) (m₀ n))
    (runsTo_copyTo (s + 1) n (fun m hm => by
      rw [hm, Mem.update_of_ne _ _ (show n ≠ s by omega)])) ?_
  refine RunsTo.seq
    (mid := fun m => m = ((m₀.update s (m₀ b)).update (s + 1) (m₀ n)).update (s + 2) 0)
    (runsTo_assign (s + 2) 0 (fun m hm => by rw [hm])) ?_
  refine runsTo_assign (s + 3) 1 (fun m hm => ?_)
  rw [hm]
  refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 2 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 1 by omega), Mem.update_self]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s + 1 ≠ s + 2 by omega), Mem.update_self]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 2 ≠ s + 3 by omega), Mem.update_self]
  · rw [Mem.update_self]
  · intro z _ hz; omega
  · intro z _ hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨z1, z2, z3, z4⟩ := hz
    rw [Mem.update_of_ne _ _ z4, Mem.update_of_ne _ _ z3, Mem.update_of_ne _ _ z2,
      Mem.update_of_ne _ _ z1]

/-- One iteration of the `fillZero` loop. -/
theorem runsTo_fillBody (b n s : ℕ) (hb : b < s) (hn : n < s) (m₀ : Mem)
    (hblock : s + 4 ≤ m₀ b) (k : ℕ) :
    RunsTo (fillBody s) (fun m => FillInv b n s m₀ m ∧ m (s + 1) = k + 1)
      (fun m' => FillInv b n s m₀ m' ∧ m' (s + 1) = k) 3 := by
  refine RunsTo.mono (T := 1 + (1 + 1)) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq (mid := fun m => m = m₁.update (m₁ s) (m₁ (s + 2)) ∧
      (FillInv b n s m₀ m₁ ∧ m₁ (s + 1) = k + 1))
    (runsTo_storeTo s (s + 2) (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m =>
      m = (m₁.update (m₁ s) (m₁ (s + 2))).update s (m₁ s + m₁ (s + 3)) ∧
      (FillInv b n s m₀ m₁ ∧ m₁ (s + 1) = k + 1))
    (runsTo_addTo s s (s + 3) (fun m hm => ⟨?_, hm.2⟩)) ?_
  · obtain ⟨hm1, ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, -⟩ := hm
    have hne1 : s ≠ m₁ s := by omega
    have hne3 : s + 3 ≠ m₁ s := by omega
    rw [hm1]
    congr 1
    rw [Mem.update_of_ne _ _ hne1, Mem.update_of_ne _ _ hne3]
  refine runsTo_subTo (s + 1) (s + 1) (s + 3) (fun m hm => ?_)
  obtain ⟨hm1, hpre⟩ := hm
  obtain ⟨⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hk⟩ := id hpre
  have hi : i = m₀ n - (k + 1) := by omega
  have hik : i < m₀ n := by omega
  rw [hm1]
  have haddr : m₁ s = m₀ b + i := e1
  refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 1 by omega), Mem.update_self, e1, e4]
    omega
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 1 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 1 ≠ m₁ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ m₁ s by omega), e2, e4]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 2 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 2 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 2 ≠ m₁ s by omega), e3]
  · rw [Mem.update_of_ne _ _ (show s + 3 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ m₁ s by omega), e4]
  · intro z hz1 hz2
    rw [Mem.update_of_ne _ _ (show z ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show z ≠ s by omega)]
    rcases Nat.lt_or_ge z (m₀ b + i) with h | h
    · rw [Mem.update_of_ne _ _ (by omega : z ≠ m₁ s)]
      exact e5 z hz1 h
    · have : z = m₁ s := by omega
      rw [this, Mem.update_self, e3]
  · intro z hz1 hz2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz2
    obtain ⟨z1, z2, z3, z4⟩ := hz2
    rw [Mem.update_of_ne _ _ z2, Mem.update_of_ne _ _ z1,
      Mem.update_of_ne _ _ (by omega : z ≠ m₁ s)]
    exact e6 z (by omega) (by simp [z1, z2, z3, z4])
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 1 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 1 ≠ m₁ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ m₁ s by omega), e4]
    omega

/-- **Zeroing a block.**  `fillZero b n s` writes `0` into the `R n` registers starting at
`R b`, in `5 * R n + 5` steps, and changes nothing outside that block and its own scratch.  The
block must lie above the scratch block. -/
theorem runsTo_fillZero (b n s : ℕ) (hb : b < s) (hn : n < s) (m₀ : Mem)
    (hblock : s + 4 ≤ m₀ b) :
    RunsTo (fillZero b n s) (fun m => m = m₀)
      (fun m' => (∀ z, m₀ b ≤ z → z < m₀ b + m₀ n → m' z = 0) ∧
        (∀ z, ¬ (m₀ b ≤ z ∧ z < m₀ b + m₀ n) → z ∉ [s, s + 1, s + 2, s + 3] → m' z = m₀ z))
      (5 * m₀ n + 5) := by
  refine RunsTo.mono (T := 4 + (m₀ n * (3 + 2) + 1)) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => FillInv b n s m₀ m) (runsTo_fillPre b n s hb hn m₀) ?_
  refine (runsTo_forLoop (fun k => runsTo_fillBody b n s hb hn m₀ hblock k) ?_).weaken ?_
  · rintro m ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩
    omega
  · rintro m' ⟨⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hz⟩
    have hiN' : i = m₀ n := by omega
    subst hiN'
    exact ⟨e5, e6⟩

/-! ## Copying a block -/

/-- The body of `copyBlock`: load from the source, store to the destination, advance both
pointers, count down. -/
def copyBody (s : ℕ) : Program :=
  seq (loadTo (s + 2) s) (seq (storeTo (s + 1) (s + 2))
    (seq (addTo s s (s + 4)) (seq (addTo (s + 1) (s + 1) (s + 4))
      (subTo (s + 3) (s + 3) (s + 4)))))

/-- `copyBlock src dst n s` copies the `R n` registers starting at `R src` to the block starting
at `R dst`.  Scratch: `s` (source pointer), `s+1` (destination pointer), `s+2` (the value in
transit), `s+3` (the counter), `s+4` (the constant `1`). -/
def copyPre (src dst n s : ℕ) : Program :=
  seq (copyTo s src) (seq (copyTo (s + 1) dst) (seq (copyTo (s + 3) n) (assign (s + 4) 1)))

/-- `copyBlock src dst n s` copies `R n` registers from `R src` to `R dst`. -/
def copyBlock (src dst n s : ℕ) : Program :=
  seq (copyPre src dst n s) (whileNz (s + 3) (copyBody s))

/-- The loop invariant of `copyBlock`: `i` entries have been copied. -/
def CopyInv (src dst n s : ℕ) (m₀ : Mem) (m : Mem) : Prop :=
  ∃ i ≤ m₀ n, m s = m₀ src + i ∧ m (s + 1) = m₀ dst + i ∧ m (s + 3) = m₀ n - i ∧
    m (s + 4) = 1 ∧
    (∀ j < i, m (m₀ dst + j) = m₀ (m₀ src + j)) ∧
    (∀ z, ¬ (m₀ dst ≤ z ∧ z < m₀ dst + i) → z ∉ [s, s + 1, s + 2, s + 3, s + 4] →
      m z = m₀ z)

theorem runsTo_copyPre (src dst n s : ℕ) (hsrc : src < s) (hdst : dst < s) (hn : n < s)
    (m₀ : Mem) :
    RunsTo (copyPre src dst n s) (fun m => m = m₀)
      (fun m' => CopyInv src dst n s m₀ m') 4 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + 1))) ?_ (by norm_num)
  refine RunsTo.seq (mid := fun m => m = m₀.update s (m₀ src))
    (runsTo_copyTo s src (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := fun m => m = (m₀.update s (m₀ src)).update (s + 1) (m₀ dst))
    (runsTo_copyTo (s + 1) dst (fun m hm => by
      rw [hm, Mem.update_of_ne _ _ (show dst ≠ s by omega)])) ?_
  refine RunsTo.seq
    (mid := fun m => m = ((m₀.update s (m₀ src)).update (s + 1) (m₀ dst)).update (s + 3) (m₀ n))
    (runsTo_copyTo (s + 3) n (fun m hm => by
      rw [hm, Mem.update_of_ne _ _ (show n ≠ s + 1 by omega),
        Mem.update_of_ne _ _ (show n ≠ s by omega)])) ?_
  refine runsTo_assign (s + 4) 1 (fun m hm => ?_)
  rw [hm]
  refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 4 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 1 by omega), Mem.update_self]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 4 by omega),
      Mem.update_of_ne _ _ (show s + 1 ≠ s + 3 by omega), Mem.update_self]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 3 ≠ s + 4 by omega), Mem.update_self]
    omega
  · rw [Mem.update_self]
  · intro j hj; omega
  · intro z _ hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨z1, z2, z3, z4, z5⟩ := hz
    rw [Mem.update_of_ne _ _ z5, Mem.update_of_ne _ _ z4, Mem.update_of_ne _ _ z2,
      Mem.update_of_ne _ _ z1]

/-- One iteration of the `copyBlock` loop. -/
theorem runsTo_copyBody (src dst n s : ℕ) (hsrc : src < s) (hdst : dst < s) (hn : n < s)
    (m₀ : Mem) (hsb : s + 5 ≤ m₀ src) (hdb : s + 5 ≤ m₀ dst)
    (hdisj : m₀ dst ≤ m₀ src ∨ m₀ src + m₀ n ≤ m₀ dst) (k : ℕ) :
    RunsTo (copyBody s) (fun m => CopyInv src dst n s m₀ m ∧ m (s + 3) = k + 1)
      (fun m' => CopyInv src dst n s m₀ m' ∧ m' (s + 3) = k) 5 := by
  refine RunsTo.mono (T := 1 + (1 + (1 + (1 + 1)))) ?_ (by norm_num)
  refine runsTo_of_pointwise (fun m₁ => ?_)
  set K : Prop := CopyInv src dst n s m₀ m₁ ∧ m₁ (s + 3) = k + 1 with hK
  refine RunsTo.seq (mid := fun m => m = m₁.update (s + 2) (m₁ (m₁ s)) ∧ K)
    (runsTo_loadTo (s + 2) s (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m =>
      m = (m₁.update (s + 2) (m₁ (m₁ s))).update (m₁ (s + 1)) (m₁ (m₁ s)) ∧ K)
    (runsTo_storeTo (s + 1) (s + 2) (fun m hm => ⟨?_, hm.2⟩)) ?_
  · obtain ⟨hm1, ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hk⟩ := hm
    rw [hm1, Mem.update_of_ne _ _ (show s + 1 ≠ s + 2 by omega), Mem.update_self]
  refine RunsTo.seq (mid := fun m =>
      m = ((m₁.update (s + 2) (m₁ (m₁ s))).update (m₁ (s + 1)) (m₁ (m₁ s))).update s
        (m₁ s + m₁ (s + 4)) ∧ K)
    (runsTo_addTo s s (s + 4) (fun m hm => ⟨?_, hm.2⟩)) ?_
  · obtain ⟨hm1, ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hk⟩ := hm
    have h1 : s ≠ m₁ (s + 1) := by omega
    have h2 : s + 4 ≠ m₁ (s + 1) := by omega
    rw [hm1]
    congr 1
    rw [Mem.update_of_ne _ _ h1, Mem.update_of_ne _ _ (show s ≠ s + 2 by omega),
      Mem.update_of_ne _ _ h2, Mem.update_of_ne _ _ (show s + 4 ≠ s + 2 by omega)]
  refine RunsTo.seq (mid := fun m =>
      m = (((m₁.update (s + 2) (m₁ (m₁ s))).update (m₁ (s + 1)) (m₁ (m₁ s))).update s
        (m₁ s + m₁ (s + 4))).update (s + 1) (m₁ (s + 1) + m₁ (s + 4)) ∧ K)
    (runsTo_addTo (s + 1) (s + 1) (s + 4) (fun m hm => ⟨?_, hm.2⟩)) ?_
  · obtain ⟨hm1, ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hk⟩ := hm
    have h1 : s + 1 ≠ m₁ (s + 1) := by omega
    have h2 : s + 4 ≠ m₁ (s + 1) := by omega
    rw [hm1]
    congr 1
    rw [Mem.update_of_ne _ _ (show s + 1 ≠ s by omega), Mem.update_of_ne _ _ h1,
      Mem.update_of_ne _ _ (show s + 1 ≠ s + 2 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s by omega), Mem.update_of_ne _ _ h2,
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 2 by omega)]
  refine runsTo_subTo (s + 3) (s + 3) (s + 4) (fun m hm => ?_)
  obtain ⟨hm1, hpre⟩ := hm
  obtain ⟨⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hk⟩ := id hpre
  have hik : i < m₀ n := by omega
  have hsrcaddr : m₁ s = m₀ src + i := e1
  have hdstaddr : m₁ (s + 1) = m₀ dst + i := e2
  have hval : m₁ (m₁ s) = m₀ (m₀ src + i) := by
    rw [e1]
    exact e6 (m₀ src + i) (by omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
  rw [hm1]
  refine ⟨⟨i + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Mem.update_of_ne _ _ (show s ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s ≠ s + 1 by omega), Mem.update_self, e1, e4]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 1 ≠ s + 3 by omega), Mem.update_self, e2, e4]
    omega
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 3 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ m₁ (s + 1) by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s + 2 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ m₁ (s + 1) by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 2 by omega), e3, e4]
    omega
  · rw [Mem.update_of_ne _ _ (show s + 4 ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ m₁ (s + 1) by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 2 by omega), e4]
  · intro j hj
    rw [Mem.update_of_ne _ _ (show m₀ dst + j ≠ s + 3 by omega),
      Mem.update_of_ne _ _ (show m₀ dst + j ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show m₀ dst + j ≠ s by omega)]
    rcases Nat.lt_or_ge j i with h | h
    · rw [Mem.update_of_ne _ _ (by omega : m₀ dst + j ≠ m₁ (s + 1)),
        Mem.update_of_ne _ _ (show m₀ dst + j ≠ s + 2 by omega)]
      exact e5 j h
    · have hj' : j = i := by omega
      subst hj'
      rw [show m₀ dst + j = m₁ (s + 1) by omega, Mem.update_self, hval]
  · intro z hz1 hz2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz2
    obtain ⟨z1, z2, z3, z4, z5⟩ := hz2
    rw [Mem.update_of_ne _ _ z4, Mem.update_of_ne _ _ z2, Mem.update_of_ne _ _ z1,
      Mem.update_of_ne _ _ (by omega : z ≠ m₁ (s + 1)), Mem.update_of_ne _ _ z3]
    exact e6 z (by omega) (by simp [z1, z2, z3, z4, z5])
  · rw [Mem.update_self, Mem.update_of_ne _ _ (show s + 3 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ m₁ (s + 1) by omega),
      Mem.update_of_ne _ _ (show s + 3 ≠ s + 2 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 1 by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ m₁ (s + 1) by omega),
      Mem.update_of_ne _ _ (show s + 4 ≠ s + 2 by omega), e3, e4]
    omega

/-- **Copying a block.**  `copyBlock src dst n s` copies the `R n` registers at `R src` to the
block at `R dst`, in `7 * R n + 5` steps.  Both blocks lie above the scratch block, and either
the destination is at or below the source — the entries are copied in increasing order, so an
overlap is harmless — or it lies entirely above it. -/
theorem runsTo_copyBlock (src dst n s : ℕ) (hsrc : src < s) (hdst : dst < s) (hn : n < s)
    (m₀ : Mem) (hsb : s + 5 ≤ m₀ src) (hdb : s + 5 ≤ m₀ dst)
    (hdisj : m₀ dst ≤ m₀ src ∨ m₀ src + m₀ n ≤ m₀ dst) :
    RunsTo (copyBlock src dst n s) (fun m => m = m₀)
      (fun m' => (∀ j < m₀ n, m' (m₀ dst + j) = m₀ (m₀ src + j)) ∧
        (∀ z, ¬ (m₀ dst ≤ z ∧ z < m₀ dst + m₀ n) →
          z ∉ [s, s + 1, s + 2, s + 3, s + 4] → m' z = m₀ z))
      (7 * m₀ n + 5) := by
  refine RunsTo.mono (T := 4 + (m₀ n * (5 + 2) + 1)) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => CopyInv src dst n s m₀ m)
    (runsTo_copyPre src dst n s hsrc hdst hn m₀) ?_
  refine (runsTo_forLoop
    (fun k => runsTo_copyBody src dst n s hsrc hdst hn m₀ hsb hdb hdisj k) ?_).weaken ?_
  · rintro m ⟨i, hiN, e1, e2, e3, e4, e5, e6⟩
    omega
  · rintro m' ⟨⟨i, hiN, e1, e2, e3, e4, e5, e6⟩, hz⟩
    have hiN' : i = m₀ n := by omega
    subst hiN'
    exact ⟨e5, e6⟩

end Arrays
end RAM
