import Workspace.Machine.Block

/-!
# Running one procedure after another

This is the procedure-call discipline of the machine layer (`DESIGN.md`, layer (b), goal 3).

## Why composition is not free

`ComputesInTime P f T` says: started in `initMem (encode a)` — the input in registers
`0 .. n`, **zeros everywhere else** — the program halts with the output in registers `0 .. n'`.
Nothing is said about the other registers, and indirect addressing lets `P` write anywhere.  So
after `P` has run, the memory is *not* `initMem (encode (f a))`: it has `P`'s scratch in it, and
a second program `Q` started there may read that scratch and compute something else.

One cannot repair this by erasing the scratch afterwards.  A `T`-step program can put the value
`2 ^ T` in a register (doubling it `T` times) and store there, so its scratch can sit at address
`2 ^ T`, and a second `T`-step program can read that address.  Erasing the whole region
`[0, 2 ^ T)` costs exponential time.  (This is `RAM.mem_eq_run`: after `k` steps nothing above
`2 ^ k * B` has been touched, and that bound is attained.)

## The discipline: routines clean up after themselves

The way out is to make cleanliness part of the specification instead of repairing it afterwards:

`CleanCompute P f T`: from `initMem (encode a)` the program halts within `T (Enc.size a)` steps
in **exactly** `initMem (encode (f a))`.

A clean program leaves no scratch at all, so clean programs compose by plain concatenation
(`CleanCompute.comp`), with no erasing step and no overhead beyond the sum of the two running
times.  The obligation it imposes is local and cheap: a routine built with the combinators of
`Workspace/Machine/Block.lean` writes only in its declared scratch block (its `Outside` clause),
and zeroing a declared block costs one instruction per register, or one bounded loop for an array
region.

`CleanCompute` is stronger than `ComputesInTime`, so it is a legitimate way to *prove*
membership in the time classes (`CleanCompute.computesInTime`), and the classes
`PolyTimeClean`, `QuasiPolyTimeClean` below imply `PolyTime`, `QuasiPolyTime`.

## The size hypothesis

Composition needs a bound `Enc.size (f a) ≤ S (Enc.size a)` on the size of the intermediate
result, supplied by the caller.  It does not follow from the running time: a `T`-step program can
set register `0` to `2 ^ T`, and the output convention then reads `2 ^ T` registers, so the
output *encoding* can be exponentially long even though only `T` registers were written.  This is
why the statements below take `S` as a hypothesis, exactly as the informal statement "and
`|f a|` is bounded by `S(|a|)`" does.

## Main results

* `RAM.CleanCompute`, `RAM.CleanSolve`, and the bridges to `ComputesInTime` / `SolvesInTime`;
* `RAM.CleanCompute.comp`, `RAM.CleanSolve.comp`: `Q` after `P` in time `T₁ n + T₂ (S n)`;
* `RAM.PolyTimeClean`, `RAM.QuasiPolyTimeClean` and their closure under composition
  (`RAM.PolyTimeClean.comp`, `RAM.QuasiPolyTimeClean.comp_poly`,
  `RAM.PolyTimeClean.comp_quasi`).
-/

namespace RAM

variable {α β γ : Type*}

/-! ## Clean computation -/

/-- `CleanCompute P f T`: on input `a` the program halts within `T (Enc.size a)` steps in exactly
the initial memory of the output — the output in registers `0 .. length`, zeros everywhere else.
A clean program leaves no scratch behind, which is what makes programs composable. -/
def CleanCompute [Enc α] [Enc β] (P : Program) (f : α → β) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, RunsTo P (fun m => m = initMem (Enc.encode a))
    (fun m' => m' = initMem (Enc.encode (f a))) (T (Enc.size a))

/-- The relational version: on input `a` the program halts cleanly holding *some* `b` with
`R a b`.  This is the shape of the paper's outputs (generating sets, coset representatives). -/
def CleanSolve [Enc α] [Enc β] (P : Program) (R : α → β → Prop) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, ∃ b : β, R a b ∧ RunsTo P (fun m => m = initMem (Enc.encode a))
    (fun m' => m' = initMem (Enc.encode b)) (T (Enc.size a))

theorem CleanCompute.mono [Enc α] [Enc β] {P : Program} {f : α → β} {T T' : ℕ → ℕ}
    (h : CleanCompute P f T) (hT : ∀ n, T n ≤ T' n) : CleanCompute P f T' :=
  fun a => (h a).mono (hT _)

theorem CleanSolve.mono [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T T' : ℕ → ℕ}
    (h : CleanSolve P R T) (hT : ∀ n, T n ≤ T' n) : CleanSolve P R T' := by
  intro a
  obtain ⟨b, hb, hrun⟩ := h a
  exact ⟨b, hb, hrun.mono (hT _)⟩

/-- A clean program computes in the sense of `ComputesInTime`: the final memory is the initial
memory of the output, and an initial memory displays its list. -/
theorem CleanCompute.computesInTime [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : CleanCompute P f T) : ComputesInTime P f T :=
  RunsTo.computesInTime (fun a =>
    (h a).weaken (fun m' hm' => by rw [hm']; exact outputAt_initMem _))

theorem CleanSolve.solvesInTime [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T : ℕ → ℕ}
    (h : CleanSolve P R T) : SolvesInTime P R T := by
  intro a
  obtain ⟨b, hb, hrun⟩ := h a
  obtain ⟨k, hk, hhalt, hmem⟩ := hrun.spec (initMem (Enc.encode a)) rfl
  refine ⟨b, hb, k, hk, hhalt, ?_⟩
  rw [show (Config.init (Enc.encode a)) = ⟨0, initMem (Enc.encode a)⟩ from rfl, hmem]
  exact outputAt_initMem _

/-- A clean program solving a function's graph. -/
theorem CleanCompute.cleanSolve [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : CleanCompute P f T) : CleanSolve P (fun a b => b = f a) T :=
  fun a => ⟨f a, rfl, h a⟩

/-! ## Composition -/

/-- **Composition.**  `Q` after `P`.  The intermediate result is delivered in exactly the memory
`Q` expects, so the two programs are simply concatenated and the times add, the second one
evaluated at a bound `S` on the size of the intermediate result. -/
theorem CleanCompute.comp [Enc α] [Enc β] [Enc γ] {P Q : Program} {f : α → β} {g : β → γ}
    {T₁ T₂ S : ℕ → ℕ} (hP : CleanCompute P f T₁) (hQ : CleanCompute Q g T₂)
    (hT₂ : ∀ n n', n ≤ n' → T₂ n ≤ T₂ n') (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) :
    CleanCompute (seq P Q) (fun a => g (f a)) (fun n => T₁ n + T₂ (S n)) := by
  intro a
  exact ((hP a).seq (hQ (f a))).mono (Nat.add_le_add_left (hT₂ _ _ (hS a)) _)

/-- **Composition, relational version.**  The composite solves the relational composite
`fun a c => ∃ b, R a b ∧ R' b c`. -/
theorem CleanSolve.comp [Enc α] [Enc β] [Enc γ] {P Q : Program} {R : α → β → Prop}
    {R' : β → γ → Prop} {T₁ T₂ S : ℕ → ℕ} (hP : CleanSolve P R T₁) (hQ : CleanSolve Q R' T₂)
    (hT₂ : ∀ n n', n ≤ n' → T₂ n ≤ T₂ n')
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    CleanSolve (seq P Q) (fun a c => ∃ b, R a b ∧ R' b c) (fun n => T₁ n + T₂ (S n)) := by
  intro a
  obtain ⟨b, hb, hrun⟩ := hP a
  obtain ⟨c, hc, hrun'⟩ := hQ b
  exact ⟨c, ⟨b, hb, hc⟩,
    (hrun.seq hrun').mono (Nat.add_le_add_left (hT₂ _ _ (hS a b hb)) _)⟩

/-! ## Monotone representatives of the bounds

To compose we need the second time bound to be monotone.  This is no restriction: a polynomial
bound may be replaced by the polynomial `c * (n+1)^d` that bounds it, and a quasipolynomial bound
by `2 ^ ((Nat.log 2 n + 2) ^ c)`; both are monotone. -/

theorem polyBound_witness (c d : ℕ) : PolyBound (fun n => c * (n + 1) ^ d) :=
  ⟨c, d, fun _ => le_refl _⟩

theorem polyBound_witness_mono (c d : ℕ) {n n' : ℕ} (h : n ≤ n') :
    c * (n + 1) ^ d ≤ c * (n' + 1) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem quasiPolyBound_witness (c : ℕ) :
    QuasiPolyBound (fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) := ⟨c, fun _ => le_refl _⟩

theorem quasiPolyBound_witness_mono (c : ℕ) {n n' : ℕ} (h : n ≤ n') :
    (2:ℕ) ^ ((Nat.log 2 n + 2) ^ c) ≤ 2 ^ ((Nat.log 2 n' + 2) ^ c) :=
  Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) h; omega) _)

/-- A polynomial of a polynomial is a polynomial. -/
theorem PolyBound.comp {T S : ℕ → ℕ} (hT : PolyBound T) (hS : PolyBound S) :
    PolyBound (fun n => T (S n)) := by
  obtain ⟨c, d, hc⟩ := hT
  obtain ⟨c', d', hc'⟩ := hS
  refine ⟨c * (c' + 1) ^ d, d' * d, fun n => ?_⟩
  have h1 : S n + 1 ≤ (c' + 1) * (n + 1) ^ d' := by
    have := hc' n
    have h2 : (1:ℕ) ≤ (n + 1) ^ d' := Nat.one_le_pow _ _ (by omega)
    calc S n + 1 ≤ c' * (n + 1) ^ d' + (n + 1) ^ d' := by omega
      _ = (c' + 1) * (n + 1) ^ d' := by ring
  calc T (S n) ≤ c * (S n + 1) ^ d := hc (S n)
    _ ≤ c * ((c' + 1) * (n + 1) ^ d') ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = c * (c' + 1) ^ d * (n + 1) ^ (d' * d) := by
        rw [mul_pow, ← pow_mul]; ring

/-! ## The clean time classes -/

/-- A function computed in polynomial time by a *clean* program.  This implies `PolyTime`, and
unlike `PolyTime` it is closed under composition. -/
def PolyTimeClean [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ CleanCompute P f T

/-- A function computed in quasipolynomial time by a clean program. -/
def QuasiPolyTimeClean [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ CleanCompute P f T

/-- A search problem solved in polynomial time by a clean program. -/
def PolyTimeCleanRel [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ CleanSolve P R T

/-- A search problem solved in quasipolynomial time by a clean program.  This is the class in
which Theorem 1.1.1 is proved. -/
def QuasiPolyTimeCleanRel [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ CleanSolve P R T

theorem PolyTimeClean.polyTime [Enc α] [Enc β] {f : α → β} (h : PolyTimeClean f) :
    PolyTime f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.computesInTime⟩

theorem QuasiPolyTimeClean.quasiPolyTime [Enc α] [Enc β] {f : α → β}
    (h : QuasiPolyTimeClean f) : QuasiPolyTime f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.computesInTime⟩

theorem PolyTimeCleanRel.polyTimeRel [Enc α] [Enc β] {R : α → β → Prop}
    (h : PolyTimeCleanRel R) : PolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.solvesInTime⟩

theorem QuasiPolyTimeCleanRel.quasiPolyTimeRel [Enc α] [Enc β] {R : α → β → Prop}
    (h : QuasiPolyTimeCleanRel R) : QuasiPolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.solvesInTime⟩

theorem PolyTimeClean.quasiPolyTimeClean [Enc α] [Enc β] {f : α → β} (h : PolyTimeClean f) :
    QuasiPolyTimeClean f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT.quasiPoly, hP⟩

/-! ## Closure under composition -/

/-- **Polynomial time is closed under composition**, given a polynomial bound on the size of the
intermediate result. -/
theorem PolyTimeClean.comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : PolyTimeClean f) (hg : PolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : PolyTimeClean (fun a => g (f a)) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hf
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hg
  refine ⟨seq P Q, fun n => T₁ n + c * (S n + 1) ^ d,
    hT₁.add ((polyBound_witness c d).comp hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => c * (n + 1) ^ d) (hQ.mono hc)
    (fun _ _ h => polyBound_witness_mono c d h) hS

/-- **Quasipolynomial time composed with polynomial-size data stays quasipolynomial.**  This is
the closure the paper's chains of reductions need. -/
theorem QuasiPolyTimeClean.comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} {S : ℕ → ℕ}
    (hf : QuasiPolyTimeClean f) (hg : QuasiPolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hf
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hg
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp_poly hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

/-- Composing a polynomial-time function with a quasipolynomial-time one, on either side, stays
quasipolynomial. -/
theorem QuasiPolyTimeClean.comp_poly [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    {S : ℕ → ℕ} (hf : QuasiPolyTimeClean f) (hg : PolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) :=
  hf.comp hg.quasiPolyTimeClean hSpoly hS

theorem PolyTimeClean.comp_quasi [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    {S : ℕ → ℕ} (hf : PolyTimeClean f) (hg : QuasiPolyTimeClean g) (hSpoly : PolyBound S)
    (hS : ∀ a, Enc.size (f a) ≤ S (Enc.size a)) : QuasiPolyTimeClean (fun a => g (f a)) :=
  hf.quasiPolyTimeClean.comp hg hSpoly hS

/-- The relational form of closure under composition in polynomial time. -/
theorem PolyTimeCleanRel.comp [Enc α] [Enc β] [Enc γ] {R : α → β → Prop} {R' : β → γ → Prop}
    {S : ℕ → ℕ} (hR : PolyTimeCleanRel R) (hR' : PolyTimeCleanRel R') (hSpoly : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    PolyTimeCleanRel (fun a c => ∃ b, R a b ∧ R' b c) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hR
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hR'
  refine ⟨seq P Q, fun n => T₁ n + c * (S n + 1) ^ d,
    hT₁.add ((polyBound_witness c d).comp hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => c * (n + 1) ^ d) (hQ.mono hc)
    (fun _ _ h => polyBound_witness_mono c d h) hS

/-- The relational form of closure under composition in quasipolynomial time. -/
theorem QuasiPolyTimeCleanRel.comp [Enc α] [Enc β] [Enc γ] {R : α → β → Prop}
    {R' : β → γ → Prop} {S : ℕ → ℕ} (hR : QuasiPolyTimeCleanRel R)
    (hR' : QuasiPolyTimeCleanRel R') (hSpoly : PolyBound S)
    (hS : ∀ a b, R a b → Enc.size b ≤ S (Enc.size a)) :
    QuasiPolyTimeCleanRel (fun a c => ∃ b, R a b ∧ R' b c) := by
  obtain ⟨P, T₁, hT₁, hP⟩ := hR
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hR'
  refine ⟨seq P Q, fun n => T₁ n + 2 ^ ((Nat.log 2 (S n) + 2) ^ c),
    hT₁.add ((quasiPolyBound_witness c).comp_poly hSpoly), ?_⟩
  exact hP.comp (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (hQ.mono hc)
    (fun _ _ h => quasiPolyBound_witness_mono c h) hS

/-! ## The identity, and a first sanity check

The empty program is clean and computes the identity in zero steps. -/

theorem cleanCompute_id [Enc α] : CleanCompute [] (id : α → α) (fun _ => 0) :=
  fun _ => runsTo_nil (fun _ hm => hm)

theorem polyTimeClean_id [Enc α] : PolyTimeClean (id : α → α) :=
  ⟨[], fun _ => 0, polyBound_const 0, cleanCompute_id⟩

end RAM
