import Workspace.Machine.Combinators

/-!
# A Hoare logic for RAM programs

`Workspace/Machine/Combinators.lean` specifies a program by the *exact* memory transformation it
performs (`RAM.Runs P pre T f`).  That is the right primitive notion — it is what the simulation
lemmas prove — but it is unusable as a specification language: a loop transforms the memory by an
iterate whose closed form nobody wants to write down, and a caller almost never needs the whole
final memory, only the contents of a few registers.

This file adds the derived judgment

`RunsTo P pre post T`: `P` is well formed and, from every memory satisfying `pre`, halts within
`T` steps in a memory satisfying `post`.

`pre` and `post` are *unary* predicates on memories.  Relations between the initial and the final
memory (for example "register `r` holds the product of the initial contents of `x` and `y`", or a
frame condition "no register outside the scratch block has changed") are expressed by quantifying
over ghost parameters *outside* the judgment, in the usual way:

```
∀ (m₀ : Mem) (a b : ℕ), RunsTo P (fun m => m = m₀ ∧ m x = a ∧ m y = b)
  (fun m' => m' r = a * b ∧ ∀ z, z ∉ scratch → m' z = m₀ z) T
```

With unary predicates the rules are the textbook ones: sequencing is transitive composition of
pre/postconditions, and the loop rule is the invariant-plus-variant rule.  Everything is derived
from the combinators of `Combinators.lean`; no new facts about the machine are proved here.

## Main results

* `RAM.RunsTo`, `RAM.Runs.runsTo`, `RAM.RunsTo.conseq` (the rule of consequence);
* the assignment rules `RAM.runsTo_assign`, `..._copyTo`, `..._addTo`, `..._subTo`,
  `..._loadTo`, `..._storeTo`, each in weakest-precondition form;
* `RAM.RunsTo.seq`, `RAM.RunsTo.ifz`;
* `RAM.runsTo_whileNz`, the while rule with an invariant and a variant, and
  `RAM.runsTo_forLoop`, its specialization to a counter register, which is the `for` loop used
  for every array traversal;
* `RAM.RunsTo.computesInTime`, `RAM.RunsTo.solvesInTime`, the bridge to the time classes.
-/

namespace RAM

/-! ## The judgment -/

/-- `RunsTo P pre post T`: `P` is well formed and, started at program counter `0` in any memory
satisfying `pre`, halts after at most `T` steps in a memory satisfying `post`. -/
structure RunsTo (P : Program) (pre post : Mem → Prop) (T : ℕ) : Prop where
  /-- The program is well formed: jump targets in range, no `halt`. -/
  wf : Wf P
  /-- Partial correctness together with the time bound. -/
  spec : ∀ m, pre m → ∃ k ≤ T, Halted P (run P ⟨0, m⟩ k) ∧ post (run P ⟨0, m⟩ k).mem

/-- An exact specification is a specification: `Runs` implies `RunsTo` for any postcondition the
final memory satisfies. -/
theorem Runs.runsTo {P : Program} {pre : Mem → Prop} {T : ℕ} {f : Mem → Mem}
    (h : Runs P pre T f) {post : Mem → Prop} (hpost : ∀ m, pre m → post (f m)) :
    RunsTo P pre post T := by
  refine ⟨h.wf, fun m hm => ?_⟩
  obtain ⟨k, hk, hhalt, hmem⟩ := h.spec m hm
  exact ⟨k, hk, hhalt, by rw [hmem]; exact hpost m hm⟩

/-- **The rule of consequence.**  Strengthen the precondition, weaken the postcondition, raise
the time bound. -/
theorem RunsTo.conseq {P : Program} {pre pre' post post' : Mem → Prop} {T T' : ℕ}
    (h : RunsTo P pre post T) (hpre : ∀ m, pre' m → pre m) (hpost : ∀ m, post m → post' m)
    (hT : T ≤ T') : RunsTo P pre' post' T' := by
  refine ⟨h.wf, fun m hm => ?_⟩
  obtain ⟨k, hk, hhalt, hp⟩ := h.spec m (hpre m hm)
  exact ⟨k, le_trans hk hT, hhalt, hpost _ hp⟩

theorem RunsTo.mono {P : Program} {pre post : Mem → Prop} {T T' : ℕ}
    (h : RunsTo P pre post T) (hT : T ≤ T') : RunsTo P pre post T' :=
  h.conseq (fun _ hm => hm) (fun _ hp => hp) hT

theorem RunsTo.weaken {P : Program} {pre post post' : Mem → Prop} {T : ℕ}
    (h : RunsTo P pre post T) (hpost : ∀ m, post m → post' m) : RunsTo P pre post' T :=
  h.conseq (fun _ hm => hm) hpost (le_refl _)

theorem RunsTo.strengthen {P : Program} {pre pre' post : Mem → Prop} {T : ℕ}
    (h : RunsTo P pre post T) (hpre : ∀ m, pre' m → pre m) : RunsTo P pre' post T :=
  h.conseq hpre (fun _ hp => hp) (le_refl _)

/-- A program is vacuously specified from an impossible precondition.  (Used to dispose of the
degenerate branch of the counter loop, where the counter is both zero and nonzero.) -/
theorem runsTo_of_false {P : Program} {pre post : Mem → Prop} {T : ℕ} (hw : Wf P)
    (h : ∀ m, ¬ pre m) : RunsTo P pre post T :=
  ⟨hw, fun m hm => absurd hm (h m)⟩

/-- A specification may be proved one starting memory at a time.  This is how every
straight-line block below is proved: the precondition is replaced by the single memory `m₁`, so
that the weakest-precondition rules chain on explicit `Mem.update`s. -/
theorem runsTo_of_pointwise {P : Program} {pre post : Mem → Prop} {T : ℕ}
    (h : ∀ m₁ : Mem, RunsTo P (fun m => m = m₁ ∧ pre m₁) post T) : RunsTo P pre post T :=
  ⟨(h (fun _ => 0)).wf, fun m hm => (h m).spec m ⟨rfl, hm⟩⟩

/-! ## Frame conditions

A routine declares the registers it may write as a list `S`; `Outside S m₀ m` says that it has
written nowhere else.  This is the clause that lets a caller keep its data across a call. -/

/-- `Outside S m₀ m`: the memory `m` agrees with `m₀` at every address outside the list `S`. -/
def Outside (S : List ℕ) (m₀ m : Mem) : Prop := ∀ z, z ∉ S → m z = m₀ z

theorem Outside.refl (S : List ℕ) (m₀ : Mem) : Outside S m₀ m₀ := fun _ _ => rfl

theorem Outside.trans {S S' : List ℕ} {m₀ m₁ m₂ : Mem} (h : Outside S m₀ m₁)
    (h' : Outside S' m₁ m₂) : Outside (S ++ S') m₀ m₂ := by
  intro z hz
  simp only [List.mem_append, not_or] at hz
  rw [h' z hz.2, h z hz.1]

/-- Writing inside the declared block preserves the frame condition. -/
theorem Outside.upd {S : List ℕ} {m₀ m : Mem} (h : Outside S m₀ m) {a : ℕ} (ha : a ∈ S)
    (v : ℕ) : Outside S m₀ (m.update a v) := by
  intro z hz
  have hza : z ≠ a := fun h' => hz (by rw [h']; exact ha)
  rw [Mem.update_of_ne _ _ hza]
  exact h z hz

theorem Outside.mono {S S' : List ℕ} {m₀ m : Mem} (h : Outside S m₀ m)
    (hS : ∀ z, z ∈ S → z ∈ S') : Outside S' m₀ m :=
  fun z hz => h z (fun hzS => hz (hS z hzS))

/-- The exact number of steps and the final configuration: a well-formed program that meets its
specification halts by falling off its end. -/
theorem RunsTo.halt_at {P : Program} {pre post : Mem → Prop} {T : ℕ}
    (h : RunsTo P pre post T) {m : Mem} (hm : pre m) :
    ∃ k ≤ T, ∃ m', run P ⟨0, m⟩ k = ⟨P.length, m'⟩ ∧ post m' ∧
      ∀ j < k, ¬ Halted P (run P ⟨0, m⟩ j) := by
  obtain ⟨k, hkT, hk, hkm⟩ := h.spec m hm
  obtain ⟨k₀, hk₀, hmin, hle⟩ := exists_first_halt ⟨k, hk⟩
  have hrun : run P ⟨0, m⟩ k = run P ⟨0, m⟩ k₀ := run_of_halted (hle k hk) hk₀
  have hpc : (run P ⟨0, m⟩ k₀).pc = P.length := pc_eq_length h.wf hk₀
  refine ⟨k₀, le_trans (hle k hk) hkT, (run P ⟨0, m⟩ k₀).mem, ?_, ?_, hmin⟩
  · rw [← Config.mk_eta (run P ⟨0, m⟩ k₀), hpc]
  · rw [← hrun]; exact hkm

/-! ## The assignment rules

Each one-instruction program is given in weakest-precondition form: to prove `post` of the final
memory it suffices to prove it of the updated memory. -/

theorem runsTo_single {i : Instr} (hne : i ≠ Instr.halt) (ht : i.target ≤ 1)
    (hpc : ∀ (p : ℕ) (m : Mem), (exec i ⟨p, m⟩).pc = p + 1) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post ((exec i ⟨0, m⟩).mem)) : RunsTo [i] pre post 1 :=
  ((runs_single hne ht hpc).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R x ← c`. -/
theorem runsTo_assign (x c : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update x c)) : RunsTo (assign x c) pre post 1 :=
  ((runs_assign x c).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R x ← R y`. -/
theorem runsTo_copyTo (x y : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update x (m y))) : RunsTo (copyTo x y) pre post 1 :=
  ((runs_copyTo x y).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R x ← R y + R z`. -/
theorem runsTo_addTo (x y z : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update x (m y + m z))) : RunsTo (addTo x y z) pre post 1 :=
  ((runs_addTo x y z).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R x ← R y - R z`, truncated. -/
theorem runsTo_subTo (x y z : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update x (m y - m z))) : RunsTo (subTo x y z) pre post 1 :=
  ((runs_subTo x y z).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R x ← R (R y)`, indirect load. -/
theorem runsTo_loadTo (x y : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update x (m (m y)))) : RunsTo (loadTo x y) pre post 1 :=
  ((runs_loadTo x y).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- `R (R x) ← R y`, indirect store. -/
theorem runsTo_storeTo (x y : ℕ) {pre post : Mem → Prop}
    (h : ∀ m, pre m → post (m.update (m x) (m y))) : RunsTo (storeTo x y) pre post 1 :=
  ((runs_storeTo x y).mono (le_refl 1) (fun _ _ => trivial)).runsTo h

/-- The empty program: zero steps, nothing happens. -/
theorem runsTo_nil {pre post : Mem → Prop} (h : ∀ m, pre m → post m) : RunsTo [] pre post 0 :=
  ⟨fun i hi => absurd hi (by simp), fun m hm => ⟨0, le_refl _, Or.inl rfl, h m hm⟩⟩

/-! ## Sequencing -/

/-- **Sequencing.**  The postcondition of the first program is the precondition of the second,
and the times add. -/
theorem RunsTo.seq {P Q : Program} {pre mid post : Mem → Prop} {T T' : ℕ}
    (hP : RunsTo P pre mid T) (hQ : RunsTo Q mid post T') :
    RunsTo (RAM.seq P Q) pre post (T + T') := by
  refine ⟨wf_seq hP.wf hQ.wf, fun m hm => ?_⟩
  obtain ⟨k, hkT, m', hkrun, hmid, hkmin⟩ := hP.halt_at hm
  obtain ⟨l, hlT, m'', hlrun, hpost, hlmin⟩ := hQ.halt_at hmid
  refine ⟨k + l, by omega, ?_, ?_⟩ <;>
    rw [run_add, run_seq_left k hkmin, hkrun, run_seq_right l hlmin, hlrun]
  · exact halted_of_pc_length (by simp)
  · exact hpost

/-- Sequencing with a slack in the time bound, the form used when assembling a routine from
several blocks. -/
theorem RunsTo.seq' {P Q : Program} {pre mid post : Mem → Prop} {T T' S : ℕ}
    (hP : RunsTo P pre mid T) (hQ : RunsTo Q mid post T') (hS : T + T' ≤ S) :
    RunsTo (RAM.seq P Q) pre post S := (hP.seq hQ).mono hS

/-! ## The conditional -/

/-- **The conditional.**  `ifz i P Q` runs `Q` when register `i` holds `0` and `P` otherwise. -/
theorem RunsTo.ifz {i : ℕ} {P Q : Program} {pre post : Mem → Prop} {T T' : ℕ}
    (hP : RunsTo P (fun m => pre m ∧ m i ≠ 0) post T)
    (hQ : RunsTo Q (fun m => pre m ∧ m i = 0) post T') :
    RunsTo (RAM.ifz i P Q) pre post (T + T' + 2) := by
  refine ⟨wf_ifz hP.wf hQ.wf, fun m hm => ?_⟩
  have hjz : (RAM.ifz i P Q)[(0:ℕ)]? = some (Instr.jz i (P.length + 2)) := rfl
  by_cases h0 : m i = 0
  · obtain ⟨l, hlT, m'', hlrun, hpost, hlmin⟩ := hQ.halt_at ⟨hm, h0⟩
    have hstep : run (RAM.ifz i P Q) ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
      rw [run_succ, run_zero, step_of_get hjz (by simp)]
      simp [exec, h0]
    refine ⟨1 + l, by omega, ?_, ?_⟩ <;>
      rw [run_add, hstep,
        run_block (A := Instr.jz i (P.length + 2) ::
            (P.map (Instr.shift 1) ++ [Instr.jump (P.length + Q.length + 2)]))
          (Q := Q) (B := []) (by simp [RAM.ifz]) (by simp) l hlmin, hlrun]
    · exact halted_of_pc_length (by simp; omega)
    · exact hpost
  · obtain ⟨k, hkT, m', hkrun, hpost, hkmin⟩ := hP.halt_at ⟨hm, h0⟩
    have hstep : run (RAM.ifz i P Q) ⟨0, m⟩ 1 = ⟨1, m⟩ := by
      rw [run_succ, run_zero, step_of_get hjz (by simp)]
      simp [exec, h0]
    have hmid : run (RAM.ifz i P Q) ⟨1, m⟩ k = ⟨1 + P.length, m'⟩ := by
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
    · exact hpost

/-! ## The loop rule

The textbook rule: an invariant preserved by the body, and a variant `μ` strictly decreased by
it.  The number of iterations is bounded by any `N` with `μ m ≤ N` on memories satisfying the
invariant, and the running time is `N * (T + 2) + 1`: `N` executions of the body, each preceded
by the test and followed by the jump back, plus the final test. -/

/-- **The while rule.**  If the body preserves `inv` and strictly decreases the variant `μ`,
and `μ` is bounded by `N` on the invariant, then `whileNz i P` terminates within
`N * (T + 2) + 1` steps in a memory satisfying `inv` with register `i` zero. -/
theorem runsTo_whileNz {i : ℕ} {P : Program} {inv : Mem → Prop} {μ : Mem → ℕ} {T N : ℕ}
    (hP : ∀ n : ℕ, RunsTo P (fun m => inv m ∧ m i ≠ 0 ∧ μ m = n)
      (fun m' => inv m' ∧ μ m' < n) T)
    (hN : ∀ m, inv m → μ m ≤ N) :
    RunsTo (whileNz i P) inv (fun m' => inv m' ∧ m' i = 0) (N * (T + 2) + 1) := by
  refine ⟨wf_whileNz (hP 0).wf, ?_⟩
  set W := whileNz i P with hW
  have hjz : ∀ m : Mem, W[(⟨0, m⟩ : Config).pc]? = some (Instr.jz i (P.length + 2)) :=
    fun _ => rfl
  have hjump : W[1 + P.length]? = some (Instr.jump 0) := by
    simp [hW, whileNz, Nat.add_comm]
  have hexit : ∀ m : Mem, m i = 0 → run W ⟨0, m⟩ 1 = ⟨P.length + 2, m⟩ := by
    intro m h0
    rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
    simp [exec, h0]
  have key : ∀ (N' : ℕ) (m : Mem), inv m → μ m ≤ N' →
      ∃ k ≤ N' * (T + 2) + 1, Halted W (run W ⟨0, m⟩ k) ∧
        (inv (run W ⟨0, m⟩ k).mem ∧ (run W ⟨0, m⟩ k).mem i = 0) := by
    intro N'
    induction N' with
    | zero =>
        intro m hm hμ
        by_cases h0 : m i = 0
        · exact ⟨1, by omega, by rw [hexit m h0]; exact halted_of_pc_length (by simp [hW]),
            by rw [hexit m h0]; exact ⟨hm, h0⟩⟩
        · obtain ⟨k, -, m', -, hpost, -⟩ := (hP (μ m)).halt_at ⟨hm, h0, rfl⟩
          omega
    | succ N' ih =>
        intro m hm hμ
        by_cases h0 : m i = 0
        · exact ⟨1, by omega, by rw [hexit m h0]; exact halted_of_pc_length (by simp [hW]),
            by rw [hexit m h0]; exact ⟨hm, h0⟩⟩
        · obtain ⟨k, hkT, m', hkrun, ⟨hinv', hμ'⟩, hkmin⟩ := (hP (μ m)).halt_at ⟨hm, h0, rfl⟩
          obtain ⟨k', hk'T, hk'halt, hk'post⟩ := ih m' hinv' (by omega)
          have hstep : run W ⟨0, m⟩ 1 = ⟨1, m⟩ := by
            rw [run_succ, run_zero, step_of_get (hjz m) (by simp)]
            simp [exec, h0]
          have hbody : run W ⟨1, m⟩ k = ⟨1 + P.length, m'⟩ := by
            rw [run_block (A := [Instr.jz i (P.length + 2)]) (Q := P)
              (B := [Instr.jump 0]) (by simp [hW, whileNz]) (by simp) k hkmin, hkrun]
          have hback : run W ⟨1 + P.length, m'⟩ 1 = ⟨0, m'⟩ := by
            rw [run_succ, run_zero, step_of_get (by simpa using hjump) (by simp)]
            simp [exec]
          have hexp : (N' + 1) * (T + 2) = N' * (T + 2) + (T + 2) := by ring
          refine ⟨1 + k + 1 + k', by omega, ?_, ?_⟩ <;>
            rw [run_add, run_add, run_add, hstep, hbody, hback]
          · exact hk'halt
          · exact hk'post
  exact fun m hm => key N m hm (hN m hm)

/-- **The counter loop.**  The body is run once for each unit of the counter register `i`, which
it decrements by one; this is the `for` loop of every array traversal.  The running time is
`N * (body + 2) + 1` where `N` bounds the initial value of the counter. -/
theorem runsTo_forLoop {i : ℕ} {P : Program} {inv : Mem → Prop} {T N : ℕ}
    (hP : ∀ n : ℕ, RunsTo P (fun m => inv m ∧ m i = n + 1) (fun m' => inv m' ∧ m' i = n) T)
    (hN : ∀ m, inv m → m i ≤ N) :
    RunsTo (whileNz i P) inv (fun m' => inv m' ∧ m' i = 0) (N * (T + 2) + 1) := by
  refine runsTo_whileNz (μ := fun m => m i) (fun n => ?_) hN
  cases n with
  | zero => exact runsTo_of_false (hP 0).wf (fun m hm => hm.2.1 hm.2.2)
  | succ n =>
      exact (hP n).conseq (fun m hm => ⟨hm.1, hm.2.2⟩)
        (fun m' hm' => ⟨hm'.1, Nat.lt_succ_of_le (le_of_eq hm'.2)⟩) (le_refl _)

/-! ## The bridge to the time classes -/

theorem RunsTo.computesInTime {α β : Type*} [Enc α] [Enc β] {P : Program} {f : α → β}
    {T : ℕ → ℕ}
    (h : ∀ a : α, RunsTo P (fun m => m = initMem (Enc.encode a))
      (fun m' => OutputAt m' (Enc.encode (f a))) (T (Enc.size a))) :
    ComputesInTime P f T := by
  intro a
  obtain ⟨k, hk, hhalt, hout⟩ := (h a).spec (initMem (Enc.encode a)) rfl
  exact ⟨k, hk, hhalt, hout⟩

theorem RunsTo.solvesInTime {α β : Type*} [Enc α] [Enc β] {P : Program} {R : α → β → Prop}
    {T : ℕ → ℕ} (b : α → β) (hR : ∀ a, R a (b a))
    (h : ∀ a : α, RunsTo P (fun m => m = initMem (Enc.encode a))
      (fun m' => OutputAt m' (Enc.encode (b a))) (T (Enc.size a))) :
    SolvesInTime P R T := by
  intro a
  obtain ⟨k, hk, hhalt, hout⟩ := (h a).spec (initMem (Enc.encode a)) rfl
  exact ⟨b a, hR a, k, hk, hhalt, hout⟩

end RAM
