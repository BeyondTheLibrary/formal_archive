import Workspace.Machine.PolyFun

/-!
# Iteration from a set-up: the size bound along one orbit

`RAM.QuasiPolyFun.iterate` (`Workspace/Machine/PolyFun.lean`) asks for the size of the
intermediate states **at every state of the state type**, because the function it builds,
`a ↦ step^[k a] a`, is a total function of a state.  A depth-first evaluator does not meet that
demand: its state is a stack, and a stack that no run can reach carries no invariant at all, so
one step may grow it and the growth compounds along quasipolynomially many rounds.

What the evaluator does satisfy is the same bound *along the orbit of a start state*.  This file
states the iteration in that shape.  The loop is preceded by a set-up `setUp : α → ℕ × σ` which
turns the real input into a round count and a start state, and is followed by a read-off
`readOff : σ → β`, and the size hypothesis speaks only of `step^[j] (setUp a).2`, the states the
run from `setUp a` actually passes through.

Nothing new happens on the machine: this is `RAM.quasiPolyTimeCleanAt_recursion`
(`Workspace/Machine/Iterate.lean`) with the size bounds discharged the way
`RAM.QuasiPolyFun.iterate` discharges them, so `RAM.QuasiPolyFun.iterate` and the theorem below
are two packagings of one loop.  No axiom, no `sorry`.

## Main results

* `RAM.size_counter_le`: a counter below a quasipolynomial bound is polynomially short;
* `RAM.QuasiPolyFun.iterateSetup`.
-/

namespace RAM

variable {α β σ : Type*}

/-! ## A counter below a quasipolynomial bound is short

The state of the loop is the pair `(counter, state)`.  The counter is a quasipolynomially large
number, so it cannot be bounded by a polynomial; its *encoding* can, because `Enc ℕ` measures a
natural by its bit length. -/

/-- A natural at most `2 ^ ((log₂ n + 2) ^ c)` has at most `(log₂ n + 2) ^ c + 1` bits. -/
theorem size_counter_le {c m n : ℕ} (h : m ≤ 2 ^ ((Nat.log 2 n + 2) ^ c)) :
    Nat.size m ≤ (Nat.log 2 n + 2) ^ c + 1 := by
  refine Nat.size_le.2 (lt_of_le_of_lt h ?_)
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `fun n => (log₂ n + 2) ^ c` is bounded by a polynomial: the logarithm is at most `n`. -/
theorem polyBound_logPow (c : ℕ) : PolyBound (fun n => (Nat.log 2 n + 2) ^ c) := by
  refine PolyBound.mono (polyBound_witness (2 ^ c) c) (fun n => ?_)
  have h1 : Nat.log 2 n + 2 ≤ 2 * (n + 1) := by
    have := Nat.log_le_self 2 n
    omega
  calc (Nat.log 2 n + 2) ^ c ≤ (2 * (n + 1)) ^ c := Nat.pow_le_pow_left h1 c
    _ = 2 ^ c * (n + 1) ^ c := by rw [mul_pow]

/-! ## The iteration -/

/-- **Bounded iteration from a set-up, in quasipolynomial time.**  The routine computes
`setUp a = (k, s)`, iterates `step` exactly `k` times from `s`, and reads the answer off the
final state.

The size hypothesis `hp` is asked **only along the orbit of the start state** `(setUp a).2`,
which is the difference to `RAM.QuasiPolyFun.iterate`.  It must be a *polynomial* bound, for the
reason given in `Workspace/Machine/PolyFun.lean`: the size bound of a `RAM.QuasiPolyFun` is
polynomial, and a quasipolynomial cost evaluated at a polynomially bounded state is again
quasipolynomial. -/
theorem QuasiPolyFun.iterateSetup [Enc α] [Enc β] [Enc σ] {setUp : α → ℕ × σ} {step : σ → σ}
    {readOff : σ → β} {q p : ℕ → ℕ}
    (hsetUp : QuasiPolyFun setUp)
    (hstep : QuasiPolyFun (fun x : ℕ × σ => (x.1 - 1, step x.2)))
    (hread : QuasiPolyFun readOff)
    (hq : ∀ a : α, (setUp a).1 ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ (setUp a).1, Enc.size (step^[j] (setUp a).2) ≤ p (Enc.size a))
    (hpb : PolyBound p) :
    QuasiPolyFun (fun a => readOff (step^[(setUp a).1] (setUp a).2)) := by
  obtain ⟨cq, hcq⟩ := hqb
  -- the size of the pair `(counter, state)` along the orbit
  set P : ℕ → ℕ := fun n => 2 * ((Nat.log 2 n + 2) ^ cq + 3) + 2 * p n with hPdef
  have hPb : PolyBound P :=
    ((polyBound_const 2).mul ((polyBound_logPow cq).add (polyBound_const 3))).add
      ((polyBound_const 2).mul hpb)
  have hpair : ∀ (a : α), ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ P (Enc.size a) := by
    intro a j hj
    have h1 := Combine.size_pair_le ((setUp a).1 - j) (step^[j] (setUp a).2)
    have h2 : Enc.size ((setUp a).1 - j) = Nat.size ((setUp a).1 - j) + 2 :=
      Small.size_nat _
    have h3 : (setUp a).1 - j ≤ 2 ^ ((Nat.log 2 (Enc.size a) + 2) ^ cq) :=
      le_trans (Nat.sub_le _ _) (le_trans (hq a) (hcq _))
    have h4 : Nat.size ((setUp a).1 - j) ≤ (Nat.log 2 (Enc.size a) + 2) ^ cq + 1 :=
      size_counter_le h3
    have h5 := hp a j hj
    simp only [hPdef]
    omega
  -- the time bound
  obtain ⟨P₁, T₁, hT₁, hP₁⟩ := hsetUp.time
  obtain ⟨Q, T₂, ⟨c, hc⟩, hQ⟩ := hstep.time
  obtain ⟨P₃, T₃, ⟨c₃, hc₃⟩, hP₃⟩ :=
    ((polyFun_snd (α := ℕ) (β := σ)).quasiPolyFun.comp hread).time
  refine ⟨quasiPolyTimeCleanAt_recursion (setUp := setUp) (step := step) (readOff := readOff)
    (T₂ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c)) (T₃ := fun n => 2 ^ ((Nat.log 2 n + 2) ^ c₃))
    (p := fun n => 2 ^ ((Nat.log 2 (P n) + 2) ^ c)) (q := q)
    (u := fun n => 2 ^ ((Nat.log 2 (P n) + 2) ^ c₃))
    hP₁ hT₁ (hQ.mono hc) (hP₃.mono hc₃) hq ⟨cq, hcq⟩ ?_
    ((quasiPolyBound_witness c).comp_poly hPb) ?_
    ((quasiPolyBound_witness c₃).comp_poly hPb), ?_⟩
  · intro a j hj
    exact quasiPolyBound_witness_mono c (hpair a j (le_of_lt hj))
  · intro a
    have h := hpair a (setUp a).1 (le_refl _)
    rw [Nat.sub_self] at h
    exact quasiPolyBound_witness_mono c₃ h
  · -- the size bound: a polynomial of a polynomial
    have hf₁ : SizeBound (fun a : α => step^[(setUp a).1] (setUp a).2) := by
      obtain ⟨cp, dp, hcp⟩ := hpb
      exact ⟨cp, dp, fun a => le_trans (hp a (setUp a).1 (le_refl _)) (hcp _)⟩
    exact hf₁.comp hread.size

end RAM
