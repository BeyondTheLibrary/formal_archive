import Workspace.Machine.Combine
import Workspace.Machine.Recursion

/-!
# Bounded iteration at the workspace convention

`Workspace/Machine/Recursion.lean` runs a bounded loop at the *top-level* convention: the counter
of the iterated function `(k, s) ↦ (k - 1, step s)` lives in register `2`, and the loop is
`whileNz 2 Q`.  A routine of the workspace convention keeps the same input in registers
`K, K+1, ...`, so the counter lives in register `K + 2` and the loop is `whileNz (K + 2) Q`.
Everything else is unchanged, and this file repeats the three statements of that file at the
workspace convention.

## Main results

* `RAM.initMemAt_prod_counter`: the counter of a pair is register `K + 2`;
* `RAM.runsTo_iterateAt`: `whileNz (K + 2) Q` iterates `step` exactly `N` times;
* `RAM.cleanComputeAt_recursion`, `RAM.polyTimeCleanAt_recursion`,
  `RAM.quasiPolyTimeCleanAt_recursion`: set-up, loop, read-off;
* `RAM.polyTimeCleanAt_iterate`, `RAM.quasiPolyTimeCleanAt_iterate`: the bounded iteration
  `a ↦ step^[k a] a`, with the honest hypotheses — a bound on the number `k a` of iterations and
  a bound on the size of every value the iteration passes through.  Both bounds are genuinely
  needed: a single clean step may double the length of its output, so without a size bound the
  states, and with them the cost of one step, grow exponentially along the iteration.
-/

namespace RAM

variable {α β σ : Type*}

/-! ## The counter register -/

/-- The first component of a pair is in register `K + 2` of the workspace convention: the
encoding of `(k, s)` is `1 :: k :: ...`, and `initMemAt K` puts the `i`-th entry of the list in
register `K + i + 1`. -/
theorem initMemAt_prod_counter [Enc σ] (K k : ℕ) (s : σ) :
    initMemAt K (Enc.encode ((k, s) : ℕ × σ)) (K + 2) = k := by
  rw [initMemAt_add]
  exact initMem_prod_counter k s

/-! ## Bounded iteration of a clean routine -/

/-- **Iteration at the workspace convention.**  If `Q` is a clean routine of the workspace
convention for the single step `(k, s) ↦ (k - 1, step s)`, then `whileNz (K + 2) Q` iterates
`step` exactly `N` times, in `N * (B + 2) + 1` machine steps, where `B` bounds the cost of one
step at every state the iteration passes through. -/
theorem runsTo_iterateAt [Enc σ] {K : ℕ} {Q : Program} {step : σ → σ} {T : ℕ → ℕ}
    (hQ : CleanComputeAt K Q (fun p : ℕ × σ => (p.1 - 1, step p.2)) T)
    (N : ℕ) (s₀ : σ) (B : ℕ)
    (hB : ∀ j < N, T (Enc.size ((N - j, step^[j] s₀) : ℕ × σ)) ≤ B) :
    RunsTo (whileNz (K + 2) Q) (fun m => m = initMemAt K (Enc.encode ((N, s₀) : ℕ × σ)))
      (fun m' => m' = initMemAt K (Enc.encode ((0, step^[N] s₀) : ℕ × σ))) (N * (B + 2) + 1) := by
  set inv : Mem → Prop :=
    fun m => ∃ j ≤ N, m = initMemAt K (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hinv
  have hbody : ∀ n : ℕ, RunsTo Q (fun m => inv m ∧ m (K + 2) ≠ 0 ∧ m (K + 2) = n)
      (fun m' => inv m' ∧ m' (K + 2) < n) B := by
    intro n
    refine ⟨(hQ ((0 : ℕ), s₀)).wf, fun m hm => ?_⟩
    obtain ⟨⟨j, hjN, rfl⟩, hne, hμ⟩ := hm
    rw [initMemAt_prod_counter] at hne hμ
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
    exact ⟨⟨j + 1, by omega, rfl⟩, by rw [initMemAt_prod_counter]; omega⟩
  have hN : ∀ m, inv m → m (K + 2) ≤ N := by
    rintro m ⟨j, hjN, rfl⟩
    rw [initMemAt_prod_counter]
    omega
  refine ((runsTo_whileNz (μ := fun m => m (K + 2)) hbody hN).conseq ?_ ?_ (le_refl _))
  · rintro m rfl
    exact ⟨0, Nat.zero_le _, by simp⟩
  · rintro m' ⟨⟨j, hjN, rfl⟩, hz⟩
    rw [initMemAt_prod_counter] at hz
    have hjeq : j = N := by omega
    subst hjeq
    rw [Nat.sub_self]

/-! ## The recursion theorem at the workspace convention -/

/-- **The recursion theorem at the workspace convention**, the copy of
`RAM.cleanCompute_recursion` with `initMemAt K` in place of `initMem` and the loop on register
`K + 2`. -/
theorem cleanComputeAt_recursion [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanComputeAt K P₁ setUp T₁)
    (hQ : CleanComputeAt K Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanComputeAt K P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a))
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a)) :
    CleanComputeAt K (seq P₁ (seq (whileNz (K + 2) Q) P₃))
      (fun a => readOff (step^[(setUp a).1] (setUp a).2))
      (fun n => T₁ n + (q n * (p n + 2) + 1) + u n) := by
  intro a
  have hloop := runsTo_iterateAt hQ (setUp a).1 (setUp a).2 (p (Enc.size a)) (hp a)
  have hlast := hP₃ ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)
  have hfirst := hP₁ a
  refine ((hfirst.seq (hloop.seq hlast)).mono ?_)
  show _ ≤ T₁ (Enc.size a) + (q (Enc.size a) * (p (Enc.size a) + 2) + 1) + u (Enc.size a)
  have h1 : (setUp a).1 * (p (Enc.size a) + 2) + 1
      ≤ q (Enc.size a) * (p (Enc.size a) + 2) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (hq a)) 1
  have h2 := hu a
  omega

/-- **The recursion theorem in polynomial time**, at the workspace convention. -/
theorem polyTimeCleanAt_recursion [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanComputeAt K P₁ setUp T₁) (hT₁ : PolyBound T₁)
    (hQ : CleanComputeAt K Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanComputeAt K P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : PolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : PolyBound u) :
    PolyTimeCleanAt K (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  ⟨seq P₁ (seq (whileNz (K + 2) Q) P₃), _,
    (hT₁.add ((hqb.mul (hpb.add (polyBound_const 2))).add (polyBound_const 1))).add hub,
    cleanComputeAt_recursion hP₁ hQ hP₃ hq hp hu⟩

/-- **The recursion theorem in quasipolynomial time**, at the workspace convention. -/
theorem quasiPolyTimeCleanAt_recursion [Enc α] [Enc β] [Enc σ] {K : ℕ} {P₁ Q P₃ : Program}
    {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {T₁ T₂ T₃ p q u : ℕ → ℕ}
    (hP₁ : CleanComputeAt K P₁ setUp T₁) (hT₁ : QuasiPolyBound T₁)
    (hQ : CleanComputeAt K Q (fun x : ℕ × σ => (x.1 - 1, step x.2)) T₂)
    (hP₃ : CleanComputeAt K P₃ (fun x : ℕ × σ => readOff x.2) T₃)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j < (setUp a).1,
      T₂ (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p)
    (hu : ∀ a : α,
      T₃ (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ u (Enc.size a))
    (hub : QuasiPolyBound u) :
    QuasiPolyTimeCleanAt K (fun a => readOff (step^[(setUp a).1] (setUp a).2)) :=
  ⟨seq P₁ (seq (whileNz (K + 2) Q) P₃), _,
    (hT₁.add ((hqb.mul (hpb.add (polyBound_const 2).quasiPoly)).add
      (polyBound_const 1).quasiPoly)).add hub,
    cleanComputeAt_recursion hP₁ hQ hP₃ hq hp hu⟩

/-! ## Bounded iteration

`a ↦ step^[k a] a` is the recursion scheme with set-up `a ↦ (k a, a)` and read-off the identity,
whose routine is the projection `Prod.snd` of `Workspace/Machine/Combine.lean`. -/

/-- **Bounded iteration in polynomial time.**  `hq` bounds the number of iterations and `hp`
bounds the size of every value the iteration passes through (including the last one); both
bounds are hypotheses, not consequences, since one clean step may double the size of its
state. -/
theorem polyTimeCleanAt_iterate [Enc α] {K : ℕ} (hK : 16 ≤ K) {step : α → α} {k : α → ℕ}
    {q p : ℕ → ℕ}
    (hstep : PolyTimeCleanAt K (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : PolyTimeCleanAt K (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : PolyBound p) :
    PolyTimeCleanAt K (fun a => step^[k a] a) := by
  obtain ⟨P₁, T₁, hT₁, hP₁⟩ := hk
  obtain ⟨Q, T₂, ⟨c, d, hc⟩, hQ⟩ := hstep
  refine polyTimeCleanAt_recursion (setUp := fun a => (k a, a)) (step := step)
    (readOff := fun a : α => a) (T₂ := fun n => c * (n + 1) ^ d)
    (p := fun n => c * (p n + 1) ^ d) (q := q) (u := fun n => 24 * p n + K + 80)
    hP₁ hT₁ (hQ.mono hc) (Combine.cleanComputeAt_snd hK) hq hqb ?_
    ((polyBound_witness c d).comp hpb) ?_
    (((polyBound_const 24).mul hpb).add (polyBound_const (K + 80)))
  · intro a j hj
    exact polyBound_witness_mono c d (hp a j (le_of_lt hj))
  · intro a
    have h := hp a (k a) (le_refl _)
    rw [Nat.sub_self] at h
    dsimp only
    omega

/-- **Bounded iteration in quasipolynomial time**: quasipolynomially many iterations, each of
quasipolynomial cost, over states of quasipolynomially bounded size.

The bound `p` on the intermediate sizes may itself be quasipolynomial, because
`RAM.QuasiPolyBound` is closed under composition (`RAM.QuasiPolyBound.comp`,
`Workspace/Machine/TimeClasses.lean`): a quasipolynomial cost evaluated at a quasipolynomially
bounded size is again quasipolynomial. -/
theorem quasiPolyTimeCleanAt_iterate [Enc α] {K : ℕ} (hK : 16 ≤ K) {step : α → α} {k : α → ℕ}
    {q p : ℕ → ℕ}
    (hstep : QuasiPolyTimeCleanAt K (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : QuasiPolyTimeCleanAt K (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : QuasiPolyBound p) :
    QuasiPolyTimeCleanAt K (fun a => step^[k a] a) := by
  obtain ⟨P₁, T₁, hT₁, hP₁⟩ := hk
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hstep
  refine quasiPolyTimeCleanAt_recursion (setUp := fun a => (k a, a)) (step := step)
    (readOff := fun a : α => a) (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c))
    (p := fun n => 2 ^ ((Nat.log 2 (p n) + 2) ^ c)) (q := q)
    (u := fun n => 24 * p n + K + 80)
    hP₁ hT₁ (hQ.mono hc) (Combine.cleanComputeAt_snd hK) hq hqb ?_
    ((quasiPolyBound_witness c).comp hpb) ?_
    (((polyBound_const 24).quasiPoly.mul hpb).add (polyBound_const (K + 80)).quasiPoly)
  · intro a j hj
    exact quasiPolyBound_witness_mono c (hp a j (le_of_lt hj))
  · intro a
    have h := hp a (k a) (le_refl _)
    rw [Nat.sub_self] at h
    dsimp only
    omega

end RAM
