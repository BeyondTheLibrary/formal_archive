import Workspace.Machine.TimeClasses

/-!
# Building RAM programs compositionally

Layer (b) of the machine model (see `Workspace/Machine/DESIGN.md`).  The paper's procedures must
be assembled without writing raw machine code, so we prove, once and for all against the
semantics of `RAM.lean`, how programs combine.

The central judgment is

`Runs P pre T f`: `P` is well formed, and from *every* memory `m` satisfying `pre`, the machine
started at program counter `0` halts after at most `T` steps with final memory `f m`.

Two points of discipline (both discussed in `DESIGN.md`).

* The judgment quantifies over all memories satisfying `pre`, and `pre` constrains only the
  registers the program reads.  Nothing is assumed about uninitialized registers, so a program
  may be run in the middle of another program's dirty memory.
* Where a program writes is recorded in `f`: `Frame w f` says that `f` changes no register at
  address `w` or above.  Frames compose (`Frame.comp`), which is what lets a caller keep data
  across a call.

Well-formed programs (`Wf`) have all jump targets at most `P.length` and contain no `halt`:
they exit by falling off the end, at program counter exactly `P.length`.  This makes
concatenation work: the code that follows simply starts executing.

Everything rests on one simulation lemma, `run_middle`: a block `Q` placed at offset `A.length`
inside a larger program, with its jump targets shifted, simulates `Q` run on its own.
-/

namespace RAM

/-! ## Well-formed programs and relocation -/

/-- The jump target of an instruction (`0` if it does not jump). -/
def Instr.target : Instr → ℕ
  | .jump t => t
  | .jz _ t => t
  | _ => 0

/-- Relocation: add `d` to every jump target. -/
def Instr.shift (d : ℕ) : Instr → Instr
  | .jump t => .jump (t + d)
  | .jz i t => .jz i (t + d)
  | i => i

/-- A program is well formed when every jump target is at most its length and it contains no
`halt`: it exits by falling off the end, at program counter exactly `P.length`. -/
def Wf (P : Program) : Prop := ∀ i ∈ P, i.target ≤ P.length ∧ i ≠ Instr.halt

@[simp] theorem Instr.shift_zero (i : Instr) : i.shift 0 = i := by
  cases i <;> simp [Instr.shift]

@[simp] theorem map_shift_zero (P : Program) : P.map (Instr.shift 0) = P := by
  induction P with
  | nil => rfl
  | cons i P ih => simp [ih]

theorem Instr.target_shift_le (d : ℕ) (i : Instr) : (i.shift d).target ≤ i.target + d := by
  cases i <;> simp [Instr.shift, Instr.target]

theorem Instr.shift_ne_halt {i : Instr} (h : i ≠ Instr.halt) (d : ℕ) :
    i.shift d ≠ Instr.halt := by
  cases i <;> simp [Instr.shift] at h ⊢

@[simp] theorem Config.mk_eta (c : Config) : (⟨c.pc, c.mem⟩ : Config) = c := rfl

/-! ## The simulation lemma -/

theorem not_halted_iff {P : Program} {c : Config} :
    ¬ Halted P c ↔ ∃ i, P[c.pc]? = some i ∧ i ≠ Instr.halt := by
  constructor
  · intro h
    unfold Halted at h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨i, hi⟩ : ∃ i, P[c.pc]? = some i := by
      cases hc : P[c.pc]? with
      | none => exact absurd hc h1
      | some i => exact ⟨i, rfl⟩
    exact ⟨i, hi, fun hh => h2 (by rw [hi, hh])⟩
  · rintro ⟨i, hi, hne⟩ (h | h)
    · rw [hi] at h; exact absurd h (by simp)
    · rw [hi] at h; exact hne (Option.some.inj h)

theorem lt_length_of_getElem? {P : Program} {n : ℕ} {i : Instr} (h : P[n]? = some i) :
    n < P.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

/-- One step of a block `Q` sitting at offset `A.length` inside `A ++ Q' ++ B`, where `Q'` is
`Q` with its jump targets shifted by `A.length`. -/
theorem step_middle {A Q B : Program} {p : ℕ} {m : Mem} (h : ¬ Halted Q ⟨p, m⟩) :
    step (A ++ (Q.map (Instr.shift A.length) ++ B)) ⟨A.length + p, m⟩
      = ⟨A.length + (step Q ⟨p, m⟩).pc, (step Q ⟨p, m⟩).mem⟩ := by
  obtain ⟨i, hi, hne⟩ := not_halted_iff.1 h
  simp only at hi
  have hilt : p < Q.length := lt_length_of_getElem? hi
  have hget : (A ++ (Q.map (Instr.shift A.length) ++ B))[A.length + p]?
      = some (i.shift A.length) := by
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left (by simpa using hilt), List.getElem?_map, hi]
    rfl
  rw [step_of_get hget (Instr.shift_ne_halt hne _), step_of_get hi hne]
  cases i <;>
    simp only [Instr.shift, exec, Config.mk.injEq, Mem.update, true_and, and_true] <;>
    first
      | omega
      | (constructor <;> [skip; rfl] <;> split <;> omega)
      | (split <;> omega)

/-- The `k`-step version of `step_middle`. -/
theorem run_middle {A Q B : Program} {m : Mem} (k : ℕ)
    (h : ∀ j < k, ¬ Halted Q (run Q ⟨0, m⟩ j)) :
    run (A ++ (Q.map (Instr.shift A.length) ++ B)) ⟨A.length, m⟩ k
      = ⟨A.length + (run Q ⟨0, m⟩ k).pc, (run Q ⟨0, m⟩ k).mem⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [run_succ, ih (fun j hj => h j (by omega)), run_succ]
      exact step_middle (A := A) (Q := Q) (B := B) (h k (by omega))

/-- A program placed at the front of a longer program behaves as on its own, until it would
halt. -/
theorem run_prefix {P B : Program} {m : Mem} (k : ℕ)
    (h : ∀ j < k, ¬ Halted P (run P ⟨0, m⟩ j)) :
    run (P ++ B) ⟨0, m⟩ k = run P ⟨0, m⟩ k := by
  have := run_middle (A := []) (Q := P) (B := B) k h
  simpa using this

/-! ## Reachable program counters -/

theorem step_pc_le {P : Program} {c : Config} (hw : Wf P) (h : c.pc ≤ P.length) :
    (step P c).pc ≤ P.length := by
  by_cases hh : Halted P c
  · rw [step_of_halted hh]; exact h
  · obtain ⟨i, hi, hne⟩ := not_halted_iff.1 hh
    have hlt : c.pc < P.length := lt_length_of_getElem? hi
    have hb := (hw i (List.mem_of_getElem? hi)).1
    rw [step_of_get hi hne]
    obtain ⟨p, m⟩ := c
    cases i <;> simp only [exec, Instr.target] at hb hlt ⊢ <;>
      first
        | omega
        | (split <;> omega)

theorem run_pc_le {P : Program} {m : Mem} (hw : Wf P) (k : ℕ) :
    (run P ⟨0, m⟩ k).pc ≤ P.length := by
  induction k with
  | zero => simp
  | succ k ih => exact step_pc_le hw ih

/-- A well-formed program halts exactly by falling off its end. -/
theorem pc_eq_length {P : Program} {m : Mem} {k : ℕ} (hw : Wf P)
    (h : Halted P (run P ⟨0, m⟩ k)) : (run P ⟨0, m⟩ k).pc = P.length := by
  have hle := run_pc_le (m := m) hw k
  rcases h with h | h
  · rw [List.getElem?_eq_none_iff] at h; omega
  · exact absurd (hw _ (List.mem_of_getElem? h)).2 (by simp)

theorem halted_of_pc_length {P : Program} {c : Config} (h : c.pc = P.length) : Halted P c := by
  left
  rw [List.getElem?_eq_none_iff, h]

/-- The first time a program halts. -/
theorem exists_first_halt {P : Program} {c : Config} (h : ∃ k, Halted P (run P c k)) :
    ∃ k₀, Halted P (run P c k₀) ∧ (∀ j < k₀, ¬ Halted P (run P c j)) ∧
      ∀ k, Halted P (run P c k) → k₀ ≤ k :=
  ⟨Nat.find h, Nat.find_spec h, fun j hj => Nat.find_min h hj, fun k hk => Nat.find_le hk⟩

/-! ## The specification judgment -/

/-- `Runs P pre T f`: `P` is well formed and, from every memory satisfying `pre`, halts within
`T` steps with final memory `f m`. -/
structure Runs (P : Program) (pre : Mem → Prop) (T : ℕ) (f : Mem → Mem) : Prop where
  /-- The program is well formed: jump targets in range, no `halt`. -/
  wf : Wf P
  /-- From any memory satisfying the precondition, the program halts in time with the stated
  final memory. -/
  spec : ∀ m, pre m → ∃ k ≤ T, Halted P (run P ⟨0, m⟩ k) ∧ (run P ⟨0, m⟩ k).mem = f m

/-- `Frame w f`: the memory transformation `f` changes no register at address `w` or above. -/
def Frame (w : ℕ) (f : Mem → Mem) : Prop := ∀ m a, w ≤ a → f m a = m a

theorem Frame.comp {w w' : ℕ} {f g : Mem → Mem} (hf : Frame w f) (hg : Frame w' g) :
    Frame (max w w') (fun m => g (f m)) := fun m a ha => by
  show g (f m) a = m a
  rw [hg _ _ (le_trans (le_max_right _ _) ha), hf _ _ (le_trans (le_max_left _ _) ha)]

theorem Runs.mono {P : Program} {pre pre' : Mem → Prop} {T T' : ℕ} {f : Mem → Mem}
    (h : Runs P pre T f) (hT : T ≤ T') (hpre : ∀ m, pre' m → pre m) : Runs P pre' T' f := by
  refine ⟨h.wf, fun m hm => ?_⟩
  obtain ⟨k, hk, rest⟩ := h.spec m (hpre m hm)
  exact ⟨k, le_trans hk hT, rest⟩

/-- The exact number of steps and the final configuration of a well-formed program that runs
according to its specification. -/
theorem Runs.halt_at {P : Program} {pre : Mem → Prop} {T : ℕ} {f : Mem → Mem}
    (h : Runs P pre T f) {m : Mem} (hm : pre m) :
    ∃ k ≤ T, run P ⟨0, m⟩ k = ⟨P.length, f m⟩ ∧ ∀ j < k, ¬ Halted P (run P ⟨0, m⟩ j) := by
  obtain ⟨k, hkT, hk, hkm⟩ := h.spec m hm
  obtain ⟨k₀, hk₀, hmin, hle⟩ := exists_first_halt ⟨k, hk⟩
  refine ⟨k₀, le_trans (hle k hk) hkT, ?_, hmin⟩
  have hrun : run P ⟨0, m⟩ k = run P ⟨0, m⟩ k₀ := run_of_halted (hle k hk) hk₀
  have hpc : (run P ⟨0, m⟩ k₀).pc = P.length := pc_eq_length h.wf hk₀
  have hmem : (run P ⟨0, m⟩ k₀).mem = f m := by rw [← hkm, hrun]
  rw [← Config.mk_eta (run P ⟨0, m⟩ k₀), hpc, hmem]

/-! ## Sequencing -/

/-- `seq P Q` runs `P` and then `Q`. -/
def seq (P Q : Program) : Program := P ++ Q.map (Instr.shift P.length)

@[simp] theorem length_seq (P Q : Program) : (seq P Q).length = P.length + Q.length := by
  simp [seq]

theorem wf_seq {P Q : Program} (hP : Wf P) (hQ : Wf Q) : Wf (seq P Q) := by
  intro i hi
  rw [seq, List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨h1, h2⟩ := hP i hi
    exact ⟨by simp [seq]; omega, h2⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    obtain ⟨h1, h2⟩ := hQ j hj
    have := Instr.target_shift_le P.length j
    exact ⟨by simp [seq] at *; omega, Instr.shift_ne_halt h2 _⟩

theorem run_seq_left {P Q : Program} {m : Mem} (k : ℕ)
    (h : ∀ j < k, ¬ Halted P (run P ⟨0, m⟩ j)) :
    run (seq P Q) ⟨0, m⟩ k = run P ⟨0, m⟩ k := run_prefix k h

theorem run_seq_right {P Q : Program} {m : Mem} (k : ℕ)
    (h : ∀ j < k, ¬ Halted Q (run Q ⟨0, m⟩ j)) :
    run (seq P Q) ⟨P.length, m⟩ k
      = ⟨P.length + (run Q ⟨0, m⟩ k).pc, (run Q ⟨0, m⟩ k).mem⟩ := by
  have := run_middle (A := P) (Q := Q) (B := []) k h
  simpa [seq] using this

/-- **Composition.**  Running `P` and then `Q` costs the sum of their times, and the memory
transformations compose. -/
theorem Runs.seq {P Q : Program} {pre pre' : Mem → Prop} {T T' : ℕ} {f g : Mem → Mem}
    (hP : Runs P pre T f) (hQ : Runs Q pre' T' g) (hpre : ∀ m, pre m → pre' (f m)) :
    Runs (seq P Q) pre (T + T') (fun m => g (f m)) := by
  refine ⟨wf_seq hP.wf hQ.wf, fun m hm => ?_⟩
  obtain ⟨k, hkT, hkrun, hkmin⟩ := hP.halt_at hm
  obtain ⟨l, hlT, hlrun, hlmin⟩ := hQ.halt_at (hpre m hm)
  refine ⟨k + l, by omega, ?_, ?_⟩
  · rw [run_add]
    rw [run_seq_left k hkmin, hkrun, run_seq_right l hlmin, hlrun]
    exact halted_of_pc_length (by simp)
  · rw [run_add, run_seq_left k hkmin, hkrun, run_seq_right l hlmin, hlrun]

/-! ## The conditional -/

/-- `ifz i P Q` runs `P` if register `i` holds `0`, and `Q` otherwise. -/
def ifz (i : ℕ) (P Q : Program) : Program :=
  Instr.jz i (P.length + 2) :: (P.map (Instr.shift 1) ++
    (Instr.jump (P.length + Q.length + 2) :: Q.map (Instr.shift (P.length + 2))))

@[simp] theorem length_ifz (i : ℕ) (P Q : Program) :
    (ifz i P Q).length = P.length + Q.length + 2 := by
  simp [ifz]; omega

theorem wf_ifz {i : ℕ} {P Q : Program} (hP : Wf P) (hQ : Wf Q) : Wf (ifz i P Q) := by
  intro j hj
  rw [ifz, List.mem_cons, List.mem_append, List.mem_cons] at hj
  simp only [length_ifz]
  rcases hj with rfl | hj | rfl | hj
  · exact ⟨by simp [Instr.target], by simp⟩
  · obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
    obtain ⟨h1, h2⟩ := hP j' hj'
    have := Instr.target_shift_le 1 j'
    exact ⟨by omega, Instr.shift_ne_halt h2 _⟩
  · exact ⟨by simp [Instr.target], by simp⟩
  · obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
    obtain ⟨h1, h2⟩ := hQ j' hj'
    have := Instr.target_shift_le (P.length + 2) j'
    exact ⟨by omega, Instr.shift_ne_halt h2 _⟩

/-- A block `Q` sitting at offset `d` inside a program `R`, with its jump targets shifted,
simulates `Q` run on its own.  This is `run_middle` in the form in which the combinators use
it: the caller supplies the decomposition of `R` and the offset as equations. -/
theorem run_block {R A Q B : Program} {m : Mem} {d : ℕ}
    (hR : R = A ++ (Q.map (Instr.shift A.length) ++ B)) (hd : d = A.length) (k : ℕ)
    (h : ∀ j < k, ¬ Halted Q (run Q ⟨0, m⟩ j)) :
    run R ⟨d, m⟩ k = ⟨d + (run Q ⟨0, m⟩ k).pc, (run Q ⟨0, m⟩ k).mem⟩ := by
  subst hR; subst hd; exact run_middle k h

/-- **The conditional.**  `ifz i P Q` runs `Q` when register `i` holds `0` and `P` otherwise. -/
theorem Runs.ifz {i : ℕ} {P Q : Program} {pre : Mem → Prop} {T T' : ℕ} {f g : Mem → Mem}
    (hP : Runs P (fun m => pre m ∧ m i ≠ 0) T f)
    (hQ : Runs Q (fun m => pre m ∧ m i = 0) T' g) :
    Runs (RAM.ifz i P Q) pre (T + T' + 2) (fun m => if m i = 0 then g m else f m) := by
  refine ⟨wf_ifz hP.wf hQ.wf, fun m hm => ?_⟩
  have hjz : (RAM.ifz i P Q)[(0:ℕ)]? = some (Instr.jz i (P.length + 2)) := rfl
  by_cases h0 : m i = 0
  · obtain ⟨l, hlT, hlrun, hlmin⟩ := hQ.halt_at ⟨hm, h0⟩
    have hstep : run (RAM.ifz i P Q) ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
      rw [run_succ, run_zero, step_of_get hjz (by simp)]
      simp [exec, h0]
    refine ⟨1 + l, by omega, ?_, ?_⟩ <;>
      rw [run_add, hstep,
        run_block (A := Instr.jz i (P.length + 2) ::
            (P.map (Instr.shift 1) ++ [Instr.jump (P.length + Q.length + 2)]))
          (Q := Q) (B := []) (by simp [RAM.ifz]) (by simp) l hlmin, hlrun]
    · exact halted_of_pc_length (by simp; omega)
    · simp [h0]
  · obtain ⟨k, hkT, hkrun, hkmin⟩ := hP.halt_at ⟨hm, h0⟩
    have hstep : run (RAM.ifz i P Q) ⟨0, m⟩ 1 = ⟨1, m⟩ := by
      rw [run_succ, run_zero, step_of_get hjz (by simp)]
      simp [exec, h0]
    have hmid : run (RAM.ifz i P Q) ⟨1, m⟩ k = ⟨1 + P.length, f m⟩ := by
      rw [run_block (A := [Instr.jz i (P.length + 2)]) (Q := P)
        (B := Instr.jump (P.length + Q.length + 2) :: Q.map (Instr.shift (P.length + 2)))
        (by simp [RAM.ifz]) (by simp) k hkmin, hkrun]
    have hjump : (RAM.ifz i P Q)[1 + P.length]?
        = some (Instr.jump (P.length + Q.length + 2)) := by
      simp [RAM.ifz, List.getElem?_cons_succ, Nat.add_comm]
    refine ⟨1 + k + 1, by omega, ?_, ?_⟩ <;>
      rw [run_add, run_add, hstep, hmid, run_succ, run_zero,
        step_of_get (by simpa using hjump) (by simp)]
    · exact halted_of_pc_length (by simp [exec])
    · simp [exec, h0]

/-! ## One-instruction programs -/

theorem runs_single {i : Instr} (hne : i ≠ Instr.halt) (ht : i.target ≤ 1)
    (hpc : ∀ (p : ℕ) (m : Mem), (exec i ⟨p, m⟩).pc = p + 1) :
    Runs [i] (fun _ => True) 1 (fun m => (exec i ⟨0, m⟩).mem) := by
  have hget : ∀ m : Mem, ([i] : Program)[(⟨0, m⟩ : Config).pc]? = some i := fun _ => rfl
  refine ⟨?_, fun m _ => ⟨1, le_refl _, ?_, ?_⟩⟩
  · intro j hj
    rw [List.mem_singleton] at hj
    subst hj
    exact ⟨by simpa using ht, hne⟩
  · apply halted_of_pc_length
    rw [run_succ, run_zero, step_of_get (hget m) hne, hpc]
    simp
  · rw [run_succ, run_zero, step_of_get (hget m) hne]

/-- `R x ← c`. -/
def assign (x c : ℕ) : Program := [Instr.const x c]

theorem runs_assign (x c : ℕ) :
    Runs (assign x c) (fun _ => True) 1 (fun m => m.update x c) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-- `R x ← R y`. -/
def copyTo (x y : ℕ) : Program := [Instr.copy x y]

theorem runs_copyTo (x y : ℕ) :
    Runs (copyTo x y) (fun _ => True) 1 (fun m => m.update x (m y)) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-- `R x ← R y + R z`. -/
def addTo (x y z : ℕ) : Program := [Instr.add x y z]

theorem runs_addTo (x y z : ℕ) :
    Runs (addTo x y z) (fun _ => True) 1 (fun m => m.update x (m y + m z)) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-- `R x ← R y - R z` (truncated). -/
def subTo (x y z : ℕ) : Program := [Instr.sub x y z]

theorem runs_subTo (x y z : ℕ) :
    Runs (subTo x y z) (fun _ => True) 1 (fun m => m.update x (m y - m z)) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-- `R x ← R (R y)`, indirect load. -/
def loadTo (x y : ℕ) : Program := [Instr.load x y]

theorem runs_loadTo (x y : ℕ) :
    Runs (loadTo x y) (fun _ => True) 1 (fun m => m.update x (m (m y))) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-- `R (R x) ← R y`, indirect store. -/
def storeTo (x y : ℕ) : Program := [Instr.store x y]

theorem runs_storeTo (x y : ℕ) :
    Runs (storeTo x y) (fun _ => True) 1 (fun m => m.update (m x) (m y)) :=
  runs_single (by simp) (by simp [Instr.target]) (fun _ _ => rfl)

/-! ## From `Runs` to the time classes

The bridge to layer (a): a program specified by `Runs`, run from the initial memory of the
input convention, computes a function within the stated time bound. -/

theorem Runs.computesInTime {α β : Type*} [Enc α] [Enc β] {P : Program} {f : α → β}
    {T : ℕ → ℕ} {F : Mem → Mem}
    (h : ∀ a : α, Runs P (fun m => m = initMem (Enc.encode a)) (T (Enc.size a)) F)
    (hout : ∀ a : α, OutputAt (F (initMem (Enc.encode a))) (Enc.encode (f a))) :
    ComputesInTime P f T := by
  intro a
  obtain ⟨k, hk, hhalt, hmem⟩ := (h a).spec (initMem (Enc.encode a)) rfl
  refine ⟨k, hk, hhalt, ?_⟩
  rw [show (Config.init (Enc.encode a)) = ⟨0, initMem (Enc.encode a)⟩ from rfl, hmem]
  exact hout a

theorem Runs.solvesInTime {α β : Type*} [Enc α] [Enc β] {P : Program} {R : α → β → Prop}
    {T : ℕ → ℕ} {F : Mem → Mem} (b : α → β)
    (h : ∀ a : α, Runs P (fun m => m = initMem (Enc.encode a)) (T (Enc.size a)) F)
    (hR : ∀ a, R a (b a))
    (hout : ∀ a : α, OutputAt (F (initMem (Enc.encode a))) (Enc.encode (b a))) :
    SolvesInTime P R T := by
  intro a
  obtain ⟨k, hk, hhalt, hmem⟩ := (h a).spec (initMem (Enc.encode a)) rfl
  refine ⟨b a, hR a, k, hk, hhalt, ?_⟩
  rw [show (Config.init (Enc.encode a)) = ⟨0, initMem (Enc.encode a)⟩ from rfl, hmem]
  exact hout a

/-! ## Bounded iteration

`whileNz i P` repeats `P` while register `i` is nonzero.  Termination is supplied by the
caller as a bound `N` on the number of iterations: `loopRun f i N` is the effect of at most `N`
iterations of the body, and the hypothesis is that `N` iterations already reach a memory with
register `i` zero.  This is the form in which the paper's loops appear: the number of rounds is
always bounded explicitly (by the number of points, of colours, of blocks, ...). -/

/-- `whileNz i P`: while register `i` is nonzero, run `P`. -/
def whileNz (i : ℕ) (P : Program) : Program :=
  Instr.jz i (P.length + 2) :: (P.map (Instr.shift 1) ++ [Instr.jump 0])

@[simp] theorem length_whileNz (i : ℕ) (P : Program) :
    (whileNz i P).length = P.length + 2 := by
  simp [whileNz]

theorem wf_whileNz {i : ℕ} {P : Program} (hP : Wf P) : Wf (whileNz i P) := by
  intro j hj
  rw [whileNz, List.mem_cons, List.mem_append, List.mem_singleton] at hj
  simp only [length_whileNz]
  rcases hj with rfl | hj | rfl
  · exact ⟨by simp [Instr.target], by simp⟩
  · obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
    obtain ⟨h1, h2⟩ := hP j' hj'
    have := Instr.target_shift_le 1 j'
    exact ⟨by omega, Instr.shift_ne_halt h2 _⟩
  · exact ⟨by simp [Instr.target], by simp⟩

/-- The effect of at most `N` iterations of a loop body `f` controlled by register `i`. -/
def loopRun (f : Mem → Mem) (i : ℕ) : ℕ → Mem → Mem
  | 0, m => m
  | N + 1, m => if m i = 0 then m else loopRun f i N (f m)

@[simp] theorem loopRun_zero (f : Mem → Mem) (i : ℕ) (m : Mem) : loopRun f i 0 m = m := rfl

theorem loopRun_succ_of_ne (f : Mem → Mem) (i : ℕ) (N : ℕ) {m : Mem} (h : m i ≠ 0) :
    loopRun f i (N + 1) m = loopRun f i N (f m) := by simp [loopRun, h]

theorem loopRun_of_eq (f : Mem → Mem) (i : ℕ) (N : ℕ) {m : Mem} (h : m i = 0) :
    loopRun f i N m = m := by cases N <;> simp [loopRun, h]

/-- **Bounded iteration.**  If the body runs in time `T` and preserves the precondition, and
`N` iterations suffice to make register `i` zero, then the loop runs in time
`N * (T + 2) + 1`. -/
theorem runs_whileNz {i : ℕ} {P : Program} {pre : Mem → Prop} {T : ℕ} {f : Mem → Mem}
    (hP : Runs P (fun m => pre m ∧ m i ≠ 0) T f)
    (hinv : ∀ m, pre m → m i ≠ 0 → pre (f m))
    (N : ℕ) (hterm : ∀ m, pre m → (loopRun f i N m) i = 0) :
    Runs (whileNz i P) pre (N * (T + 2) + 1) (fun m => loopRun f i N m) := by
  refine ⟨wf_whileNz hP.wf, ?_⟩
  set W := whileNz i P with hW
  have hjz : ∀ m : Mem, W[(⟨0, m⟩ : Config).pc]? = some (Instr.jz i (P.length + 2)) :=
    fun _ => rfl
  have hjump : W[1 + P.length]? = some (Instr.jump 0) := by
    simp [hW, whileNz, Nat.add_comm]
  have key : ∀ (N : ℕ) (m : Mem), pre m → (loopRun f i N m) i = 0 →
      ∃ k ≤ N * (T + 2) + 1, Halted W (run W ⟨0, m⟩ k) ∧
        (run W ⟨0, m⟩ k).mem = loopRun f i N m := by
    intro N
    induction N with
    | zero =>
        intro m hm hz
        simp only [loopRun_zero] at hz ⊢
        have hstep : run W ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
          rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
          simp [exec, hz]
        exact ⟨1, by omega, by rw [hstep]; exact halted_of_pc_length (by simp [hW]),
          by rw [hstep]⟩
    | succ N ih =>
        intro m hm hz
        by_cases h0 : m i = 0
        · rw [loopRun_of_eq f i (N + 1) h0]
          have hstep : run W ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
            rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
            simp [exec, h0]
          exact ⟨1, by omega, by rw [hstep]; exact halted_of_pc_length (by simp [hW]),
            by rw [hstep]⟩
        · rw [loopRun_succ_of_ne f i N h0] at hz ⊢
          obtain ⟨k, hkT, hkrun, hkmin⟩ := hP.halt_at ⟨hm, h0⟩
          obtain ⟨k', hk'T, hk'halt, hk'mem⟩ := ih (f m) (hinv m hm h0) hz
          have hstep : run W ⟨0, m⟩ 1 = ⟨1, m⟩ := by
            rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
            simp [exec, h0]
          have hbody : run W ⟨1, m⟩ k = ⟨1 + P.length, f m⟩ := by
            rw [run_block (A := [Instr.jz i (P.length + 2)]) (Q := P)
              (B := [Instr.jump 0]) (by simp [hW, whileNz]) (by simp) k hkmin, hkrun]
          have hback : run W ⟨1 + P.length, f m⟩ 1 = ⟨0, f m⟩ := by
            rw [run_succ, run_zero, step_of_get (by simpa using hjump) (by simp)]
            simp [exec]
          have hexp : (N + 1) * (T + 2) = N * (T + 2) + (T + 2) := by ring
          refine ⟨1 + k + 1 + k', by omega, ?_, ?_⟩ <;>
            rw [run_add, run_add, run_add, hstep, hbody, hback]
          · exact hk'halt
          · exact hk'mem
  exact fun m hm => key N m hm (hterm m hm)

/-- Two programs with the same effect on the memories allowed by the precondition have the same
specification. -/
theorem Runs.congr {P : Program} {pre : Mem → Prop} {T : ℕ} {f g : Mem → Mem}
    (h : Runs P pre T f) (hfg : ∀ m, pre m → f m = g m) : Runs P pre T g := by
  refine ⟨h.wf, fun m hm => ?_⟩
  obtain ⟨k, hk, hhalt, hmem⟩ := h.spec m hm
  exact ⟨k, hk, hhalt, by rw [hmem, hfg m hm]⟩

/-- A loop whose body decrements the control register runs it exactly `m i` times. -/
theorem loopRun_counter {f : Mem → Mem} {i : ℕ} {inv : Mem → Prop}
    (hinv : ∀ m, inv m → m i ≠ 0 → inv (f m))
    (hdec : ∀ m, inv m → m i ≠ 0 → (f m) i = m i - 1) :
    ∀ (N : ℕ) (m : Mem), inv m → m i ≤ N →
      loopRun f i N m = f^[m i] m ∧ (f^[m i] m) i = 0 := by
  intro N
  induction N with
  | zero =>
      intro m hm hle
      have h0 : m i = 0 := by omega
      simp [loopRun, h0]
  | succ N ih =>
      intro m hm hle
      by_cases h0 : m i = 0
      · simp [loopRun_of_eq f i (N + 1) h0, h0]
      · have hfi : (f m) i = m i - 1 := hdec m hm h0
        have hle' : (f m) i ≤ N := by omega
        obtain ⟨h1, h2⟩ := ih (f m) (hinv m hm h0) hle'
        have hiter : f^[(f m) i] (f m) = f^[m i] m := by
          rw [hfi, show m i = (m i - 1) + 1 by omega, Function.iterate_succ_apply]
          simp
        rw [loopRun_succ_of_ne f i N h0, h1, hiter]
        refine ⟨rfl, ?_⟩
        rw [← hiter]; exact h2

/-- **The counter loop.**  If the body preserves an invariant and decrements the control
register `i` by one, then `whileNz i P` runs the body `m i` times, in time
`(m i) * (T + 2) + 1`.  This is the shape of every loop over an array in the paper. -/
theorem runs_whileNz_counter {i : ℕ} {P : Program} {inv : Mem → Prop} {T N : ℕ} {f : Mem → Mem}
    (hP : Runs P (fun m => (inv m ∧ m i ≤ N) ∧ m i ≠ 0) T f)
    (hinv : ∀ m, inv m → m i ≠ 0 → inv (f m))
    (hdec : ∀ m, inv m → m i ≠ 0 → (f m) i = m i - 1) :
    Runs (whileNz i P) (fun m => inv m ∧ m i ≤ N) (N * (T + 2) + 1) (fun m => f^[m i] m) := by
  have hkey := loopRun_counter hinv hdec N
  refine Runs.congr (runs_whileNz hP ?_ N ?_) ?_
  · exact fun m hm h0 => ⟨hinv m hm.1 h0, by rw [hdec m hm.1 h0]; omega⟩
  · exact fun m hm => by rw [(hkey m hm.1 hm.2).1]; exact (hkey m hm.1 hm.2).2
  · exact fun m hm => (hkey m hm.1 hm.2).1

end RAM
