import Workspace.Machine.Compose

/-!
# The recursion theorem for the machine

Sec. 11.4 of the paper analyses its procedures by the scheme: *each call does at most `p(n)`
work outside its recursive calls, and the recursion tree has at most `q(n)` nodes, hence the
total cost is at most about `q(n) * p(n)`*.  (Concretely this is how `cost_iii`, `cost_66` and
`cost_resolution` are used there.)  This file proves that scheme for the RAM.

## The stack discipline

A recursion is run on the machine by keeping the pending calls as *data*.  The state of the
computation is a value `s : σ` — in the intended use, a stack of pending subproblems together
with the partial results — and one "local step" of the procedure is a function `step : σ → σ`
which pops the top of the stack, does the `p(n)` work of that call, and pushes the subcalls.
Running the whole recursion is iterating `step` as many times as the recursion tree has nodes.

The machine then needs no call stack of its own, and no saving and restoring of registers: the
stack is part of the input/output convention of the step routine, and the step routine is an
ordinary clean routine in the sense of `Workspace/Machine/Compose.lean`.  What has to be
programmed is the *loop*, and the loop counter cannot live in a scratch register — a clean
routine leaves scratch registers zero.  It lives in the state instead: the iterated function is

`(k, s) ↦ (k - 1, step s)`  on `ℕ × σ`,

and the counter `k` is, by the encoding of a pair (`Workspace/Machine/Encoding.lean`), always in
**register 2**, whatever `σ` is (`RAM.initMem_prod_counter`).  So the loop is literally
`whileNz 2 Q` where `Q` is the clean routine for one step.

## Main results

* `RAM.runsTo_iterate`: `whileNz 2 Q` runs `N` steps of `step` in `N * (B + 2) + 1` steps of the
  machine, where `B` bounds the cost of one step along the iteration;
* `RAM.cleanCompute_recursion`: the recursion theorem — `q(n)` calls, `p(n)` work per call, plus
  the cost of setting up and of reading off the answer;
* `RAM.polyTimeClean_recursion`: its polynomial-time form, and
  `RAM.quasiPolyTimeClean_recursion`: its quasipolynomial-time form, which is the one Sec. 11.4
  uses.
-/

namespace RAM

variable {α β σ : Type*}

/-! ## The counter register -/

/-- The first component of a pair is always in register `2`: the encoding of `(k, s)` is
`1 :: k :: (length of the second block) :: ...`, and `initMem` puts the `i`-th entry of the list
in register `i + 1`. -/
theorem initMem_prod_counter [Enc σ] (k : ℕ) (s : σ) :
    initMem (Enc.encode ((k, s) : ℕ × σ)) 2 = k := by
  show initMem (frame (Enc.encode k) ++ frame (Enc.encode s)) 2 = k
  show initMem (frame [k] ++ frame (Enc.encode s)) 2 = k
  simp [initMem, frame]

/-! ## Bounded iteration of a clean routine -/

/-- **Iteration.**  If `Q` is a clean routine for the single step `(k, s) ↦ (k - 1, step s)`,
then `whileNz 2 Q` iterates `step` exactly `N` times, in `N * (B + 2) + 1` machine steps, where
`B` bounds the cost of one step at every state the iteration passes through.

The loop control is register `2`, which holds the counter `k` by `initMem_prod_counter`; the
counter reaches `0` after `N` iterations, which is the termination argument. -/
theorem runsTo_iterate [Enc σ] {Q : Program} {step : σ → σ} {T : ℕ → ℕ}
    (hQ : CleanCompute Q (fun p : ℕ × σ => (p.1 - 1, step p.2)) T)
    (N : ℕ) (s₀ : σ) (B : ℕ)
    (hB : ∀ j < N, T (Enc.size ((N - j, step^[j] s₀) : ℕ × σ)) ≤ B) :
    RunsTo (whileNz 2 Q) (fun m => m = initMem (Enc.encode ((N, s₀) : ℕ × σ)))
      (fun m' => m' = initMem (Enc.encode ((0, step^[N] s₀) : ℕ × σ))) (N * (B + 2) + 1) := by
  set inv : Mem → Prop :=
    fun m => ∃ j ≤ N, m = initMem (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hinv
  have hbody : ∀ n : ℕ, RunsTo Q (fun m => inv m ∧ m 2 ≠ 0 ∧ m 2 = n)
      (fun m' => inv m' ∧ m' 2 < n) B := by
    intro n
    refine ⟨(hQ ((0 : ℕ), s₀)).wf, fun m hm => ?_⟩
    obtain ⟨⟨j, hjN, rfl⟩, hne, hμ⟩ := hm
    rw [initMem_prod_counter] at hne hμ
    have hj : j < N := by omega
    obtain ⟨k, hk, hhalt, hmem⟩ :=
      (hQ ((N - j, step^[j] s₀) : ℕ × σ)).spec _ rfl
    refine ⟨k, le_trans hk (hB j hj), hhalt, ?_⟩
    rw [hmem]
    have key : (fun x : ℕ × σ => (x.1 - 1, step x.2)) ((N - j, step^[j] s₀) : ℕ × σ)
        = ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) := by
      have h1 : N - j - 1 = N - (j + 1) := by omega
      simp [h1, Function.iterate_succ_apply']
    rw [key]
    exact ⟨⟨j + 1, by omega, rfl⟩, by rw [initMem_prod_counter]; omega⟩
  have hN : ∀ m, inv m → m 2 ≤ N := by
    rintro m ⟨j, hjN, rfl⟩
    rw [initMem_prod_counter]
    omega
  refine ((runsTo_whileNz (μ := fun m => m 2) hbody hN).conseq ?_ ?_ (le_refl _))
  · rintro m rfl
    exact ⟨0, Nat.zero_le _, by simp⟩
  · rintro m' ⟨⟨j, hjN, rfl⟩, hz⟩
    rw [initMem_prod_counter] at hz
    have hjeq : j = N := by omega
    subst hjeq
    rw [Nat.sub_self]

/-! ## The recursion theorem -/

/-- **The recursion theorem.**  A recursive procedure is presented by

* `setUp : α → ℕ × σ`, which turns the input into the number of calls the recursion will make
  and the initial state (the stack holding the single top-level call), computed by a clean
  routine `P₁`;
* `step : σ → σ`, one call of the procedure — pop a pending subproblem, do its local work, push
  its subcalls — computed, in the counting form `(k, s) ↦ (k - 1, step s)`, by a clean routine
  `Q`;
* `readOff : σ → β`, which reads the answer off the final state, computed by a clean routine
  `P₃`.

If one call costs at most `p (Enc.size a)` and the recursion makes `(setUp a).1` calls, then the
whole procedure runs in `T₁ n + (q n * (p n + 2) + 1) + u n` steps, where `q` bounds the number
of calls and `u` the cost of reading off the answer. -/
theorem cleanCompute_recursion [Enc α] [Enc β] [Enc σ] {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanCompute P₁ setUp T₁)
    (hQ : CleanCompute Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanCompute P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a))
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a)) :
    CleanCompute (seq P₁ (seq (whileNz 2 Q) P₃))
      (fun a => readOff (step^[(setUp a).1] (setUp a).2))
      (fun n => T₁ n + (q n * (p n + 2) + 1) + u n) := by
  intro a
  have hloop := runsTo_iterate hQ (setUp a).1 (setUp a).2 (p (Enc.size a)) (hp a)
  have hlast := hP₃ ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)
  have hfirst := hP₁ a
  refine ((hfirst.seq (hloop.seq hlast)).mono ?_)
  show _ ≤ T₁ (Enc.size a) + (q (Enc.size a) * (p (Enc.size a) + 2) + 1) + u (Enc.size a)
  have h1 : (setUp a).1 * (p (Enc.size a) + 2) + 1
      ≤ q (Enc.size a) * (p (Enc.size a) + 2) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (hq a)) 1
  have h2 := hu a
  omega

/-- **The recursion theorem in polynomial time.**  Polynomially many calls, polynomial work per
call, polynomial set-up and read-off: polynomial time. -/
theorem polyTimeClean_recursion [Enc α] [Enc β] [Enc σ] {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanCompute P₁ setUp T₁) (hT₁ : PolyBound T₁)
    (hQ : CleanCompute Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanCompute P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : PolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : PolyBound u) :
    PolyTimeClean (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  ⟨seq P₁ (seq (whileNz 2 Q) P₃), _,
    (hT₁.add ((hqb.mul (hpb.add (polyBound_const 2))).add (polyBound_const 1))).add hub,
    cleanCompute_recursion hP₁ hQ hP₃ hq hp hu⟩

/-- **The recursion theorem in quasipolynomial time.**  This is the form Sec. 11.4 uses: the
number of calls is quasipolynomial, the work per call is quasipolynomial, and the total is
quasipolynomial. -/
theorem quasiPolyTimeClean_recursion [Enc α] [Enc β] [Enc σ] {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanCompute P₁ setUp T₁) (hT₁ : QuasiPolyBound T₁)
    (hQ : CleanCompute Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanCompute P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : QuasiPolyBound u) :
    QuasiPolyTimeClean (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  ⟨seq P₁ (seq (whileNz 2 Q) P₃), _,
    (hT₁.add ((hqb.mul (hpb.add (polyBound_const 2).quasiPoly)).add
      (polyBound_const 1).quasiPoly)).add hub,
    cleanCompute_recursion hP₁ hQ hP₃ hq hp hu⟩

end RAM
