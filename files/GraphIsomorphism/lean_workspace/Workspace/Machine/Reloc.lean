import Workspace.Machine.Offset

/-!
# Relocation: running a procedure in a region of memory chosen by the caller

This file supplies the procedure-call mechanism that the clean classes were missing (see the
"Doubts" section of `Workspace/Machine/DESIGN.md`).

## The problem

`CleanCompute P f T` says: started in *exactly* `initMem (Enc.encode a)`, the program `P` halts in
*exactly* `initMem (Enc.encode (f a))`.  A caller that wants to keep data of its own across the
call is stuck: once it has written the data anywhere, the memory is no longer
`initMem (Enc.encode a)`, and the specification says nothing at all.  The frame rule
`RAM.CleanCompute.frame` (`Locality.lean`) repairs this for data stored above `2 ^ T * B`, the
reach of a `T`-step run, but producing that address costs the caller a routine that evaluates the
time bound.

## The mechanism: relocate the callee

`relocate b u v P` runs `P` with every address shifted by the value `d` of the **base register**
`b`, which `P` itself never sees.  Each instruction of `P` becomes a block of exactly ten
instructions using two reserved scratch registers `u`, `v`; a jump to position `t` becomes a jump
to position `10 * t`.  The simulated register `x` of `P` is the physical register `d + x`, so:

* everything `P` does happens at addresses `d` and above, hence the caller's data below `d` — of
  any length, and without any bound on the callee's running time — is untouched, apart from the
  three reserved registers `b`, `u`, `v`, which lie below `d`;
* the cost is exactly ten times the cost of `P` (`run_reloc`), so polynomial and quasipolynomial
  bounds are preserved.

## Main results

* `RAM.Reloc.relocate`, `RAM.Reloc.length_relocate`, `RAM.Reloc.wf_relocate`;
* `RAM.Reloc.Shifted d m m'`: `m'` holds, from address `d` on, the memory `m`;
* `RAM.Reloc.step_reloc`, `RAM.Reloc.run_reloc`: the simulation theorems;
* `RAM.CleanCompute.runsTo_reloc`: the call rule — a clean routine, relocated to a base `d` the
  caller has put in register `b`, transforms a memory holding `Enc.encode a` from `d` on into one
  holding `Enc.encode (f a)` from `d` on, in `10 * T (Enc.size a)` steps, changing nothing below
  `d` except `u` and `v`;
* `RAM.cleanComputeAt_of_cleanCompute`, `RAM.polyTimeCleanAt_of_polyTimeClean`,
  `RAM.quasiPolyTimeCleanAt_of_quasiPolyTimeClean`: every clean routine of the top-level
  convention is a clean routine of the workspace convention of `Offset.lean`, for every `K ≥ 3`.
-/

namespace RAM

/-- Writing into a register the value it already holds changes nothing. -/
@[simp] theorem Mem.update_eq_self (m : Mem) (a : ℕ) : m.update a (m a) = m := by
  funext z
  unfold Mem.update
  split <;> simp_all

namespace Reloc

/-! ## Straight-line blocks

A jump-free program is run by `lineMem`, the composite of the effects of its instructions.  Every
block below consists of jump-free instructions, except for a final jump in the two blocks that
simulate a jump. -/

/-- An instruction that neither jumps nor halts: it falls through to the next position, and
relocation leaves it where it is. -/
def NoJump : Instr → Prop
  | .jump _ => False
  | .jz _ _ => False
  | .halt => False
  | _ => True

theorem shift_of_noJump {i : Instr} (h : NoJump i) (d : ℕ) : i.shift d = i := by
  cases i <;> simp_all [NoJump, Instr.shift]

theorem map_shift_of_noJump {P : Program} (h : ∀ i ∈ P, NoJump i) (d : ℕ) :
    P.map (Instr.shift d) = P := by
  induction P with
  | nil => rfl
  | cons i P ih =>
      simp only [List.map_cons, shift_of_noJump (h i (by simp)) d,
        ih (fun j hj => h j (by simp [hj]))]

/-- The effect of a jump-free program on the memory: apply the instructions in turn. -/
def lineMem : Program → Mem → Mem
  | [], m => m
  | i :: P, m => lineMem P (exec i ⟨0, m⟩).mem

@[simp] theorem lineMem_nil (m : Mem) : lineMem [] m = m := rfl

theorem lineMem_append (P Q : Program) (m : Mem) :
    lineMem (P ++ Q) m = lineMem Q (lineMem P m) := by
  induction P generalizing m with
  | nil => rfl
  | cons i P ih => simp only [List.cons_append, lineMem, ih]

/-- The no-op used to pad the blocks: `R u ← R u`. -/
def nop (u : ℕ) : Instr := Instr.copy u u

@[simp] theorem lineMem_replicate_nop (n u : ℕ) (m : Mem) :
    lineMem (List.replicate n (nop u)) m = m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      show lineMem (List.replicate n (nop u)) ((exec (nop u) ⟨0, m⟩).mem) = m
      simp only [nop, exec, Mem.update_eq_self]
      exact ih m

theorem noJump_nop (u : ℕ) : NoJump (nop u) := trivial

/-- **A jump-free program runs in one step per instruction**, with the memory effect
`lineMem`. -/
theorem runs_line : ∀ (P : Program), (∀ i ∈ P, NoJump i) →
    Runs P (fun _ => True) P.length (lineMem P) := by
  intro P
  induction P with
  | nil =>
      exact fun _ => ⟨fun i hi => absurd hi (by simp),
        fun m _ => ⟨0, le_refl _, Or.inl rfl, rfl⟩⟩
  | cons i P ih =>
      intro h
      have hi : NoJump i := h i (by simp)
      have hP : ∀ j ∈ P, NoJump j := fun j hj => h j (by simp [hj])
      have hsingle : Runs [i] (fun _ => True) 1 (fun m => (exec i ⟨0, m⟩).mem) :=
        runs_single (by cases i <;> simp_all [NoJump])
          (by cases i <;> simp_all [NoJump, Instr.target])
          (by intro p m; cases i <;> simp_all [NoJump, exec])
      have hseq := hsingle.seq (ih hP) (fun _ _ => trivial)
      rw [seq, List.length_singleton, map_shift_of_noJump hP, List.singleton_append] at hseq
      exact hseq.mono (by simp; omega) (fun _ _ => trivial)

/-! ## The blocks -/

/-- The block of ten instructions simulating one instruction of the callee.  The simulated
register `x` is the physical register `d + x`, where `d` is the value of the base register `b`;
`u` and `v` are the two reserved scratch registers.  A jump to `t` becomes a jump to `10 * t`,
and the jump is the last instruction of its block, so that falling through lands exactly at the
beginning of the next block. -/
def blk (b u v : ℕ) : Instr → Program
  | .const i c =>
      [.const u i, .add u u b, .const v c, .store u v] ++ List.replicate 6 (nop u)
  | .copy i j =>
      [.const u j, .add u u b, .load v u, .const u i, .add u u b, .store u v] ++
        List.replicate 4 (nop u)
  | .add i j k =>
      [.const u j, .add u u b, .load v u, .const u k, .add u u b, .load u u, .add v v u,
        .const u i, .add u u b, .store u v]
  | .sub i j k =>
      [.const u j, .add u u b, .load v u, .const u k, .add u u b, .load u u, .sub v v u,
        .const u i, .add u u b, .store u v]
  | .load i j =>
      [.const u j, .add u u b, .load u u, .add u u b, .load v u, .const u i, .add u u b,
        .store u v] ++ List.replicate 2 (nop u)
  | .store i j =>
      [.const u j, .add u u b, .load v u, .const u i, .add u u b, .load u u, .add u u b,
        .store u v] ++ List.replicate 2 (nop u)
  | .jump t => Instr.jump (10 * t) :: List.replicate 9 (nop u)
  | .jz i t =>
      ([.const u i, .add u u b, .load u u] ++ List.replicate 6 (nop u)) ++ [.jz u (10 * t)]
  | .halt => List.replicate 10 (nop u)

@[simp] theorem length_blk (b u v : ℕ) (i : Instr) : (blk b u v i).length = 10 := by
  cases i <;> simp [blk]

/-- Every instruction of a block has jump target at most ten times the target of the instruction
it simulates, and none of them is `halt`. -/
theorem blk_target (b u v : ℕ) (i : Instr) :
    ∀ j ∈ blk b u v i, j.target ≤ 10 * i.target ∧ j ≠ Instr.halt := by
  cases i <;> simp [blk, nop, Instr.target]

/-- The relocated program: the blocks of the instructions, concatenated. -/
def relocate (b u v : ℕ) (P : Program) : Program := (P.map (blk b u v)).flatten

@[simp] theorem relocate_nil (b u v : ℕ) : relocate b u v [] = [] := rfl

theorem relocate_cons (b u v : ℕ) (i : Instr) (P : Program) :
    relocate b u v (i :: P) = blk b u v i ++ relocate b u v P := by
  simp [relocate]

@[simp] theorem length_relocate (b u v : ℕ) (P : Program) :
    (relocate b u v P).length = 10 * P.length := by
  induction P with
  | nil => rfl
  | cons i P ih => rw [relocate_cons, List.length_append, ih, length_blk]; simp; ring

theorem wf_relocate {b u v : ℕ} {P : Program} (hP : Wf P) : Wf (relocate b u v P) := by
  intro j hj
  rw [relocate, List.mem_flatten] at hj
  obtain ⟨l, hl, hjl⟩ := hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
  obtain ⟨ht, _⟩ := hP i hi
  obtain ⟨h1, h2⟩ := blk_target b u v i j hjl
  refine ⟨?_, h2⟩
  rw [length_relocate]
  exact le_trans h1 (Nat.mul_le_mul_left 10 ht)

/-- The decomposition of a relocated program around the block of the instruction at position
`p`. -/
theorem relocate_decomp {b u v : ℕ} {P : Program} {p : ℕ} {i : Instr} (h : P[p]? = some i) :
    ∃ A B, relocate b u v P = A ++ (blk b u v i ++ B) ∧ A.length = 10 * p := by
  induction P generalizing p with
  | nil => simp at h
  | cons a P ih =>
      cases p with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          exact ⟨[], relocate b u v P, by rw [relocate_cons]; simp, by simp⟩
      | succ q =>
          simp only [List.getElem?_cons_succ] at h
          obtain ⟨A, B, hAB, hA⟩ := ih h
          refine ⟨blk b u v a ++ A, B, ?_, ?_⟩
          · rw [relocate_cons, hAB, List.append_assoc]
          · rw [List.length_append, hA, length_blk]; ring

theorem getElem?_append_offset (A C : Program) (n : ℕ) : (A ++ C)[A.length + n]? = C[n]? := by
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-! ## The relation between the callee's memory and the caller's -/

/-- `Shifted d m m'`: the caller's memory `m'` holds, from address `d` on, the callee's memory
`m`.  Nothing is said about the caller's own registers, which are below `d`. -/
def Shifted (d : ℕ) (m m' : Mem) : Prop := ∀ x, m' (d + x) = m x

/-- `LowAgree d u v m₀ m`: below `d`, the memory `m` agrees with `m₀` except possibly at the two
reserved scratch registers. -/
def LowAgree (d u v : ℕ) (m₀ m : Mem) : Prop := ∀ z, z < d → z ≠ u → z ≠ v → m z = m₀ z

theorem LowAgree.rfl' {d u v : ℕ} (m : Mem) : LowAgree d u v m m := fun _ _ _ _ => rfl

theorem LowAgree.trans {d u v : ℕ} {m₀ m₁ m₂ : Mem} (h : LowAgree d u v m₀ m₁)
    (h' : LowAgree d u v m₁ m₂) : LowAgree d u v m₀ m₂ :=
  fun z hz hu hv => (h' z hz hu hv).trans (h z hz hu hv)

/-- A write at the scratch registers or above the base keeps the caller's registers. -/
theorem LowAgree.upd {d u v : ℕ} {m₀ m : Mem} (h : LowAgree d u v m₀ m) {a c : ℕ}
    (ha : a = u ∨ a = v ∨ d ≤ a) : LowAgree d u v m₀ (m.update a c) := by
  intro z hz hu hv
  rw [Mem.update_of_ne _ _ (by rcases ha with rfl | rfl | ha <;> omega)]
  exact h z hz hu hv

/-- A write below the base does not disturb the simulated memory. -/
theorem Shifted.low {d : ℕ} {m m' : Mem} (hs : Shifted d m m') {z : ℕ} (hz : z < d) (c : ℕ) :
    Shifted d m (m'.update z c) := by
  intro x
  rw [Mem.update_of_ne _ _ (by omega : d + x ≠ z)]
  exact hs x

/-- A write at the physical address of the simulated register `i` is the simulated write. -/
theorem Shifted.high {d a i c : ℕ} (ha : a = d + i) {m m' : Mem} (hs : Shifted d m m') :
    Shifted d (m.update i c) (m'.update a c) := by
  intro x
  subst ha
  by_cases h : x = i
  · subst h; simp
  · rw [Mem.update_of_ne _ _ (by omega : d + x ≠ d + i), Mem.update_of_ne _ _ h]
    exact hs x

/-! ## Running a straight-line block inside the relocated program -/

/-- A jump-free prefix `Q` of the block of the instruction at position `p` runs, inside the
relocated program, exactly as it runs on its own. -/
theorem run_prefixBlock {b u v : ℕ} {P : Program} {p : ℕ} {i : Instr} (hget : P[p]? = some i)
    {Q R : Program} (hblk : blk b u v i = Q ++ R) (hQ : ∀ j ∈ Q, NoJump j) (m : Mem) :
    ∃ k ≤ Q.length, run (relocate b u v P) ⟨10 * p, m⟩ k
      = ⟨10 * p + Q.length, lineMem Q m⟩ := by
  obtain ⟨A, B, hdec, hA⟩ := relocate_decomp (b := b) (u := u) (v := v) hget
  obtain ⟨k, hk, hkrun, hkmin⟩ := (runs_line Q hQ).halt_at (m := m) trivial
  refine ⟨k, hk, ?_⟩
  have hR : relocate b u v P = A ++ (Q.map (Instr.shift A.length) ++ (R ++ B)) := by
    rw [map_shift_of_noJump hQ, hdec, hblk, List.append_assoc]
  rw [run_block hR hA.symm k hkmin, hkrun]

/-- The instruction at the start of the block at position `p`. -/
theorem getElem?_block {b u v : ℕ} {P : Program} {p : ℕ} {i : Instr} (hget : P[p]? = some i)
    (n : ℕ) : (relocate b u v P)[10 * p + n]? = (blk b u v i)[n]? ∨
      10 ≤ n := by
  rcases Nat.lt_or_ge n 10 with hn | hn
  · left
    obtain ⟨A, B, hdec, hA⟩ := relocate_decomp (b := b) (u := u) (v := v) hget
    rw [hdec, ← hA, getElem?_append_offset, List.getElem?_append_left (by simp [hn])]
  · exact Or.inr hn

/-! ## The simulation of one step -/

/-- The three reserved registers of a call: the base register `b`, holding the base address `d`,
and the two scratch registers `u`, `v`.  All three lie below `d`, so they belong to the caller's
part of the memory, and they are pairwise distinct. -/
structure Ok (b u v d : ℕ) : Prop where
  /-- The base register is a register of the caller. -/
  hbd : b < d
  /-- The first scratch register is a register of the caller. -/
  hud : u < d
  /-- The second scratch register is a register of the caller. -/
  hvd : v < d
  /-- The base register is not the first scratch register. -/
  hbu : b ≠ u
  /-- The base register is not the second scratch register. -/
  hbv : b ≠ v
  /-- The two scratch registers are distinct. -/
  huv : u ≠ v

/-- **One step of the callee is simulated by its block.**  From the start of the block of the
instruction at position `p`, in a memory holding the callee's memory from `d` on and the base
address in register `b`, the relocated program reaches, in at most ten steps, the start of the
block of the instruction the callee goes to, in a memory holding the callee's new memory from
`d` on and agreeing with the old one below `d` except at the two scratch registers. -/
theorem step_reloc {b u v d : ℕ} {P : Program} {p : ℕ} {i : Instr} (hok : Ok b u v d)
    (hget : P[p]? = some i) (hne : i ≠ Instr.halt) {m m' : Mem} (hs : Shifted d m m')
    (hb : m' b = d) :
    ∃ n ≤ 10, ∃ m'', run (relocate b u v P) ⟨10 * p, m'⟩ n
        = ⟨10 * (exec i ⟨p, m⟩).pc, m''⟩ ∧
      Shifted d (exec i ⟨p, m⟩).mem m'' ∧ LowAgree d u v m' m'' := by
  obtain ⟨hbd, hud, hvd, hbu, hbv, huv⟩ := hok
  have hU : ∀ (w : Mem) (c x : ℕ), (w.update u c) (x + d) = w (x + d) :=
    fun w c x => Mem.update_of_ne _ _ (by omega)
  have hV : ∀ (w : Mem) (c x : ℕ), (w.update v c) (x + d) = w (x + d) :=
    fun w c x => Mem.update_of_ne _ _ (by omega)
  have hBu : ∀ (w : Mem) (c : ℕ), (w.update u c) b = w b := fun w c => Mem.update_of_ne _ _ hbu
  have hBv : ∀ (w : Mem) (c : ℕ), (w.update v c) b = w b := fun w c => Mem.update_of_ne _ _ hbv
  have hUv : ∀ (w : Mem) (c : ℕ), (w.update v c) u = w u := fun w c => Mem.update_of_ne _ _ huv
  have hVu : ∀ (w : Mem) (c : ℕ), (w.update u c) v = w v :=
    fun w c => Mem.update_of_ne _ _ (Ne.symm huv)
  have hs' : ∀ x, m' (x + d) = m x := fun x => by rw [Nat.add_comm]; exact hs x
  cases i with
  | const i c =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.const i c)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.const i c)) m'
          = (((m'.update u i).update u (i + d)).update v c).update (i + d) c := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hb, hUv]
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.const i c)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring) (((hs.low hud _).low hud _).low hvd _)
      · rw [hfin]
        exact ((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)
  | copy i j =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.copy i j)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.copy i j)) m'
          = (((((m'.update u j).update u (j + d)).update v (m j)).update u i).update u
              (i + d)).update (i + d) (m j) := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hBv, hb, hUv, hVu, hU, hV, hs']
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.copy i j)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring)
          ((((((hs.low hud _).low hud _).low hvd _).low hud _).low hud _))
      · rw [hfin]
        exact ((((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)
  | add i j k =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.add i j k)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.add i j k)) m'
          = (((((((((m'.update u j).update u (j + d)).update v (m j)).update u k).update u
              (k + d)).update u (m k)).update v (m j + m k)).update u i).update u
              (i + d)).update (i + d) (m j + m k) := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hBv, hb, hUv, hVu, hU, hV, hs']
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.add i j k)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring)
          ((((((((((hs.low hud _).low hud _).low hvd _).low hud _).low hud _).low hud _).low
            hvd _).low hud _).low hud _))
      · rw [hfin]
        exact ((((((((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)
  | sub i j k =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.sub i j k)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.sub i j k)) m'
          = (((((((((m'.update u j).update u (j + d)).update v (m j)).update u k).update u
              (k + d)).update u (m k)).update v (m j - m k)).update u i).update u
              (i + d)).update (i + d) (m j - m k) := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hBv, hb, hUv, hVu, hU, hV, hs']
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.sub i j k)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring)
          ((((((((((hs.low hud _).low hud _).low hvd _).low hud _).low hud _).low hud _).low
            hvd _).low hud _).low hud _))
      · rw [hfin]
        exact ((((((((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)
  | load i j =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.load i j)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.load i j)) m'
          = (((((((m'.update u j).update u (j + d)).update u (m j)).update u
              (m j + d)).update v (m (m j))).update u i).update u (i + d)).update (i + d)
              (m (m j)) := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hBv, hb, hUv, hVu, hU, hV, hs']
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.load i j)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring)
          ((((((((hs.low hud _).low hud _).low hud _).low hud _).low hvd _).low hud _).low
            hud _))
      · rw [hfin]
        exact ((((((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)
  | store i j =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget (Q := blk b u v (Instr.store i j)) (R := [])
        (by simp) (by simp [blk, nop, NoJump]) m'
      have hfin : lineMem (blk b u v (Instr.store i j)) m'
          = (((((((m'.update u j).update u (j + d)).update v (m j)).update u i).update u
              (i + d)).update u (m i)).update u (m i + d)).update (m i + d) (m j) := by
        simp only [blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hBv, hb, hUv, hVu, hU, hV, hs']
      refine ⟨n, le_trans hn (by simp), lineMem (blk b u v (Instr.store i j)) m', ?_, ?_, ?_⟩
      · rw [hrun]; simp only [length_blk, exec, Config.mk.injEq, and_true]; ring
      · rw [hfin]
        exact Shifted.high (by ring)
          ((((((((hs.low hud _).low hud _).low hvd _).low hud _).low hud _).low hud _).low
            hud _))
      · rw [hfin]
        exact ((((((((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd (by omega)).upd
          (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)
  | jump t =>
      obtain ⟨A, B, hdec, hA⟩ := relocate_decomp (b := b) (u := u) (v := v) hget
      have hget' : (relocate b u v P)[10 * p]? = some (Instr.jump (10 * t)) := by
        have h0 : (relocate b u v P)[10 * p + 0]? = (blk b u v (Instr.jump t))[0]? := by
          rw [hdec, ← hA, getElem?_append_offset,
            List.getElem?_append_left (by simp)]
        simpa [blk] using h0
      refine ⟨1, by omega, m', ?_, hs, LowAgree.rfl' m'⟩
      rw [run_succ, run_zero, step_of_get hget' (by simp)]
      simp [exec]
  | jz i t =>
      obtain ⟨n, hn, hrun⟩ := run_prefixBlock (b := b) (u := u) (v := v) hget
        (Q := [Instr.const u i, Instr.add u u b, Instr.load u u] ++ List.replicate 6 (nop u))
        (R := [Instr.jz u (10 * t)]) rfl (by simp [nop, NoJump]) m'
      set Q : Program :=
        [Instr.const u i, Instr.add u u b, Instr.load u u] ++ List.replicate 6 (nop u) with hQdef
      have hlen : Q.length = 9 := by simp [hQdef]
      have hfin : lineMem Q m' = ((m'.update u i).update u (i + d)).update u (m i) := by
        simp only [hQdef, blk, lineMem_append, lineMem_replicate_nop, lineMem, exec,
          Mem.update_self, hBu, hb, hU, hs']
      have hval : (lineMem Q m') u = m i := by rw [hfin, Mem.update_self]
      obtain ⟨A, B, hdec, hA⟩ := relocate_decomp (b := b) (u := u) (v := v) hget
      have hget' : (relocate b u v P)[10 * p + 9]? = some (Instr.jz u (10 * t)) := by
        have hb' : blk b u v (Instr.jz i t) ++ B = Q ++ ([Instr.jz u (10 * t)] ++ B) := by
          rw [hQdef]; simp [blk, List.append_assoc]
        rw [hdec, ← hA, getElem?_append_offset, hb']
        rw [show (9 : ℕ) = Q.length + 0 by omega, getElem?_append_offset]
        rfl
      refine ⟨n + 1, by omega, lineMem Q m', ?_, ?_, ?_⟩
      · rw [run_succ, hrun, hlen, step_of_get (by rw [← hget']) (by simp)]
        simp only [exec, hval, Config.mk.injEq, and_true]
        split_ifs <;> omega
      · rw [hfin]
        exact ((hs.low hud _).low hud _).low hud _
      · rw [hfin]
        exact (((LowAgree.rfl' m').upd (by omega)).upd (by omega)).upd (by omega)
  | halt => exact absurd rfl hne

/-! ## The simulation of a whole run -/

/-- **Simulation.**  `k` steps of the callee are simulated by at most `10 * k` steps of the
relocated program: the program counters correspond (`p ↦ 10 * p`), the memory from `d` on is the
callee's memory, and below `d` nothing has changed except the two scratch registers. -/
theorem run_reloc {b u v d : ℕ} {P : Program} (hwf : Wf P) (hok : Ok b u v d)
    {m m' : Mem} (hs : Shifted d m m') (hb : m' b = d) (k : ℕ) :
    ∃ n ≤ 10 * k, ∃ m'', run (relocate b u v P) ⟨0, m'⟩ n
        = ⟨10 * (run P ⟨0, m⟩ k).pc, m''⟩ ∧
      Shifted d (run P ⟨0, m⟩ k).mem m'' ∧ LowAgree d u v m' m'' := by
  induction k with
  | zero => exact ⟨0, by omega, m', by simp, hs, LowAgree.rfl' m'⟩
  | succ k ih =>
      obtain ⟨n, hn, m'', hrun, hs'', hlow⟩ := ih
      by_cases hh : Halted P (run P ⟨0, m⟩ k)
      · rw [run_succ, step_of_halted hh]
        exact ⟨n, by omega, m'', hrun, hs'', hlow⟩
      · obtain ⟨i, hi, hine⟩ := not_halted_iff.1 hh
        have hb'' : m'' b = d := by rw [hlow b hok.hbd hok.hbu hok.hbv, hb]
        obtain ⟨n', hn', m₃, hrun3, hs3, hlow3⟩ := step_reloc hok hi hine hs'' hb''
        refine ⟨n + n', by omega, m₃, ?_, ?_, hlow.trans hlow3⟩
        · rw [run_add, hrun, hrun3, run_succ, step_of_get hi hine]
        · rw [run_succ, step_of_get hi hine]; exact hs3

/-- A halted configuration of the callee corresponds to a halted configuration of the relocated
program. -/
theorem halted_reloc {b u v : ℕ} {P : Program} (hwf : Wf P) {m : Mem} {k : ℕ}
    (h : Halted P (run P ⟨0, m⟩ k)) {c : Config} (hc : c.pc = 10 * (run P ⟨0, m⟩ k).pc) :
    Halted (relocate b u v P) c := by
  refine halted_of_pc_length ?_
  rw [hc, pc_eq_length hwf h, length_relocate]

end Reloc

/-! ## The call rule -/

/-- **Calling a routine on a region of memory chosen by the caller.**  If, started in exactly
`initMem l`, the program `P` halts within `T` steps in exactly `initMem l'`, and if the caller
has put the base address `d` in register `b` and the list `l` from address `d` on, then the
relocated program halts within `10 * T` steps in a memory that holds `l'` from `d` on and that
agrees with the caller's memory below `d` except at the two scratch registers.

This is the procedure call the pairing, conditional and iteration combinators are built from: the
caller's data below `d` — of unbounded length, and whatever the callee's running time — survives
the call. -/
theorem runsTo_reloc {P : Program} {l l' : List ℕ} {T : ℕ}
    (h : RunsTo P (fun m => m = initMem l) (fun m' => m' = initMem l') T)
    {b u v d : ℕ} (hok : Reloc.Ok b u v d) (m₀ : Mem)
    (hs : Reloc.Shifted d (initMem l) m₀) (hb : m₀ b = d) :
    RunsTo (Reloc.relocate b u v P) (fun m => m = m₀)
      (fun m' => Reloc.Shifted d (initMem l') m' ∧ Reloc.LowAgree d u v m₀ m') (10 * T) := by
  refine ⟨Reloc.wf_relocate h.wf, fun m hm => ?_⟩
  subst hm
  obtain ⟨k, hk, hhalt, hmem⟩ := h.spec (initMem l) rfl
  obtain ⟨n, hn, m'', hrun, hs'', hlow⟩ := Reloc.run_reloc h.wf hok hs hb k
  refine ⟨n, le_trans hn (Nat.mul_le_mul_left 10 hk), ?_, ?_⟩
  · exact Reloc.halted_reloc h.wf hhalt (by rw [hrun])
  · rw [hrun]
    exact ⟨by rw [← hmem]; exact hs'', hlow⟩

/-- The call rule for a clean routine computing a function. -/
theorem CleanCompute.runsTo_reloc {α β : Type*} [Enc α] [Enc β] {P : Program} {f : α → β}
    {T : ℕ → ℕ} (h : CleanCompute P f T) {b u v d : ℕ} (hok : Reloc.Ok b u v d) (a : α)
    (m₀ : Mem) (hs : Reloc.Shifted d (initMem (Enc.encode a)) m₀) (hb : m₀ b = d) :
    RunsTo (Reloc.relocate b u v P) (fun m => m = m₀)
      (fun m' => Reloc.Shifted d (initMem (Enc.encode (f a))) m' ∧
        Reloc.LowAgree d u v m₀ m') (10 * T (Enc.size a)) :=
  RAM.runsTo_reloc (h a) hok m₀ hs hb

/-- The call rule for a clean routine solving a search problem: it delivers *some* admissible
answer from the base on, and the caller's data below the base survives. -/
theorem CleanSolve.runsTo_reloc {α β : Type*} [Enc α] [Enc β] {P : Program} {R : α → β → Prop}
    {T : ℕ → ℕ} (h : CleanSolve P R T) {b u v d : ℕ} (hok : Reloc.Ok b u v d) (a : α)
    (m₀ : Mem) (hs : Reloc.Shifted d (initMem (Enc.encode a)) m₀) (hb : m₀ b = d) :
    ∃ c : β, R a c ∧ RunsTo (Reloc.relocate b u v P) (fun m => m = m₀)
      (fun m' => Reloc.Shifted d (initMem (Enc.encode c)) m' ∧
        Reloc.LowAgree d u v m₀ m') (10 * T (Enc.size a)) := by
  obtain ⟨c, hc, hrun⟩ := h a
  exact ⟨c, hc, RAM.runsTo_reloc hrun hok m₀ hs hb⟩

/-! ## From the top-level convention to the workspace convention

A clean routine of the top-level convention becomes a clean routine of the workspace convention
of `Workspace/Machine/Offset.lean` by relocation to the base `K`: register `0` holds the base,
registers `1` and `2` are the scratch of the simulation, and all three are cleared at the end.
Three work registers are needed, so this requires `3 ≤ K`. -/

/-- Running the clean routine `P` of the top-level convention at the workspace convention with
`K` work registers. -/
def relocAt (K : ℕ) (P : Program) : Program :=
  seq (assign 0 K) (seq (Reloc.relocate 0 1 2 P)
    (seq (assign 0 0) (seq (assign 1 0) (assign 2 0))))

/-- The generic step from the call rule to the workspace convention: setting the base register,
calling, and clearing the three reserved registers turns a run of the relocated program from a
shifted memory into a run at the workspace convention. -/
theorem runsTo_relocAt {K : ℕ} (hK : 3 ≤ K) {P : Program} {l l' : List ℕ} {T : ℕ}
    (h : ∀ m₀ : Mem, Reloc.Shifted K (initMem l) m₀ → m₀ 0 = K →
      RunsTo (Reloc.relocate 0 1 2 P) (fun m => m = m₀)
        (fun m' => Reloc.Shifted K (initMem l') m' ∧ Reloc.LowAgree K 1 2 m₀ m') T) :
    RunsTo (relocAt K P) (fun m => m = initMemAt K l)
      (fun m' => m' = initMemAt K l') (T + 4) := by
  set m₀ : Mem := initMemAt K l with hm₀
  have hs : Reloc.Shifted K (initMem l) (m₀.update 0 K) := by
    intro x
    rw [Mem.update_of_ne _ _ (by omega : K + x ≠ 0), hm₀, initMemAt_add]
  have hb : (m₀.update 0 K) 0 = K := Mem.update_self _ _ _
  refine RunsTo.mono (T := 1 + (T + (1 + (1 + 1)))) ?_ (by omega)
  refine RunsTo.seq (mid := fun m => m = m₀.update 0 K)
    (runsTo_assign 0 K (fun m hm => by rw [hm])) ?_
  refine RunsTo.seq (mid := fun m => Reloc.Shifted K (initMem l') m ∧
      Reloc.LowAgree K 1 2 (m₀.update 0 K) m) (h (m₀.update 0 K) hs hb) ?_
  refine runsTo_of_pointwise (fun m₁ => ?_)
  refine RunsTo.seq (mid := fun m => m = m₁.update 0 0 ∧
      (Reloc.Shifted K (initMem l') m₁ ∧ Reloc.LowAgree K 1 2 (m₀.update 0 K) m₁))
    (runsTo_assign 0 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine RunsTo.seq (mid := fun m => m = (m₁.update 0 0).update 1 0 ∧
      (Reloc.Shifted K (initMem l') m₁ ∧ Reloc.LowAgree K 1 2 (m₀.update 0 K) m₁))
    (runsTo_assign 1 0 (fun m hm => ⟨by rw [hm.1], hm.2⟩)) ?_
  refine runsTo_assign 2 0 (fun m hm => ?_)
  obtain ⟨hm1, hsh, hlow⟩ := hm
  rw [hm1]
  refine eq_initMemAt (fun z hz => ?_) (fun x => ?_)
  · rcases (by omega : z = 0 ∨ z = 1 ∨ z = 2 ∨ 3 ≤ z) with rfl | rfl | rfl | hz3
    · rw [Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 2),
        Mem.update_of_ne _ _ (by omega : (0:ℕ) ≠ 1), Mem.update_self]
    · rw [Mem.update_of_ne _ _ (by omega : (1:ℕ) ≠ 2), Mem.update_self]
    · rw [Mem.update_self]
    · rw [Mem.update_of_ne _ _ (by omega : z ≠ 2), Mem.update_of_ne _ _ (by omega : z ≠ 1),
        Mem.update_of_ne _ _ (by omega : z ≠ 0), hlow z hz (by omega) (by omega),
        Mem.update_of_ne _ _ (by omega : z ≠ 0), hm₀, initMemAt_of_lt _ hz]
  · rw [Mem.update_of_ne _ _ (by omega : K + x ≠ 2), Mem.update_of_ne _ _ (by omega : K + x ≠ 1),
      Mem.update_of_ne _ _ (by omega : K + x ≠ 0)]
    exact hsh x

/-- **Every clean routine of the top-level convention is a clean routine of the workspace
convention**, at ten times the cost plus four steps. -/
theorem cleanComputeAt_of_cleanCompute {α β : Type*} [Enc α] [Enc β] {P : Program} {f : α → β}
    {T : ℕ → ℕ} {K : ℕ} (hK : 3 ≤ K) (h : CleanCompute P f T) :
    CleanComputeAt K (relocAt K P) f (fun n => 10 * T n + 4) := fun a =>
  runsTo_relocAt hK (fun m₀ hs hb =>
    h.runsTo_reloc ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ a m₀ hs hb)

/-- **Every clean search routine of the top-level convention is one of the workspace
convention.** -/
theorem cleanSolveAt_of_cleanSolve {α β : Type*} [Enc α] [Enc β] {P : Program}
    {R : α → β → Prop} {T : ℕ → ℕ} {K : ℕ} (hK : 3 ≤ K) (h : CleanSolve P R T) :
    CleanSolveAt K (relocAt K P) R (fun n => 10 * T n + 4) := by
  intro a
  obtain ⟨c, hc, hrun⟩ := h a
  exact ⟨c, hc, runsTo_relocAt hK (fun m₀ hs hb =>
    RAM.runsTo_reloc hrun ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ m₀ hs hb)⟩

theorem polyTimeCleanAt_of_polyTimeClean {α β : Type*} [Enc α] [Enc β] {f : α → β} {K : ℕ}
    (hK : 3 ≤ K) (h : PolyTimeClean f) : PolyTimeCleanAt K f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨relocAt K P, _, ((polyBound_const 10).mul hT).add (polyBound_const 4),
    cleanComputeAt_of_cleanCompute hK hP⟩

theorem quasiPolyTimeCleanAt_of_quasiPolyTimeClean {α β : Type*} [Enc α] [Enc β] {f : α → β}
    {K : ℕ} (hK : 3 ≤ K) (h : QuasiPolyTimeClean f) : QuasiPolyTimeCleanAt K f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨relocAt K P, _,
    (((polyBound_const 10).quasiPoly).mul hT).add ((polyBound_const 4).quasiPoly),
    cleanComputeAt_of_cleanCompute hK hP⟩


theorem polyTimeCleanRelAt_of_polyTimeCleanRel {α β : Type*} [Enc α] [Enc β] {R : α → β → Prop}
    {K : ℕ} (hK : 3 ≤ K) (h : PolyTimeCleanRel R) : PolyTimeCleanRelAt K R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨relocAt K P, _, ((polyBound_const 10).mul hT).add (polyBound_const 4),
    cleanSolveAt_of_cleanSolve hK hP⟩

theorem quasiPolyTimeCleanRelAt_of_quasiPolyTimeCleanRel {α β : Type*} [Enc α] [Enc β]
    {R : α → β → Prop} {K : ℕ} (hK : 3 ≤ K) (h : QuasiPolyTimeCleanRel R) :
    QuasiPolyTimeCleanRelAt K R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨relocAt K P, _,
    (((polyBound_const 10).quasiPoly).mul hT).add ((polyBound_const 4).quasiPoly),
    cleanSolveAt_of_cleanSolve hK hP⟩

end RAM
