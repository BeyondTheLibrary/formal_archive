import Workspace.Machine.Div
import Mathlib.Data.Nat.Choose.Basic

/-!
# Powering with a bounded exponent

`a ^ b` is **not** a `RAM.PolyFun` of the pair `(a, b)`, and not because of a missing routine:
the answer has about `b * Nat.size a` bits, which is exponential in the length of `b`, so no
program can even write it down in polynomial time.  What is true, and what the paper's procedures
use, is powering with an exponent that is polynomially bounded in the size of the input.  That is
the statement proved here:

`RAM.PolyFun.pow`: from `PolyFun f`, `PolyFun g` and a polynomial bound `g a ≤ q (Enc.size a)`,
the function `a ↦ f a ^ g a` is a `PolyFun`.

The route is `RAM.PolyFun.iterate`, and the one point that needs care is its hypothesis `hq`: the
number of rounds has to be bounded by a polynomial in the size of **the state**, for every state,
not only for the states the iteration really passes through.  The state is
`(a, c, r)` — the original input, the exponent still to consume, and the power accumulated so far
— and the number of rounds is read off as `min c (g a)`.  The minimum is what makes `hq` true:
`min c (g a) ≤ g a ≤ q (Enc.size a) ≤ q (Enc.size (a, c, r))` because `a` is a component of the
state and the bound is monotone, while `c` alone is a binary number and can be huge.  At the
starting state `(a, g a, 1)` the minimum is `g a`, which is the count we want.

One round is `(a, c, r) ↦ (a, c - 1, r * f a)`, so after `j` rounds the state is
`(a, c - j, r * f a ^ j)`, and after `g a` rounds from `(a, g a, 1)` the accumulator is
`f a ^ g a`.  No conditional is needed, because the iteration is run exactly `g a` times.

## Main results

* `RAM.size_pow_le`: `Nat.size (x ^ j) ≤ j * Nat.size x + 1`;
* `RAM.PolyFun.pow`;
* `RAM.polyFun_pow_of_le`: the same for `fun p : ℕ × ℕ => p.1 ^ p.2` with the exponent cut down
  to a polynomial bound;
* `RAM.PolyFun.factorial`: `a ↦ (f a)!` for a `f` that a polynomial bounds — the same loop with
  the round multiplying by the counter;
* `RAM.PolyFun.choose`: `a ↦ Nat.choose (f a) (g a)` for an `f` that a polynomial bounds, as
  three factorials and one division.

The binary logarithm `Nat.log 2` is already a `PolyFun` (`RAM.polyFun_log2`), and so is the bit
length `Nat.size` (`RAM.polyFun_natSize`).
-/

namespace RAM

/-- The bit length of a power: `x ^ j` has at most `j * Nat.size x + 1` bits. -/
theorem size_pow_le (x j : ℕ) : Nat.size (x ^ j) ≤ j * Nat.size x + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have h := size_mul_le (x ^ j) x
      have h2 : (j + 1) * Nat.size x + 1 = j * Nat.size x + 1 + Nat.size x := by ring
      omega

/-- One round of the powering loop: consume one unit of the exponent and multiply the
accumulator by the base. -/
def powStep {α : Type*} (f : α → ℕ) (s : α × ℕ × ℕ) : α × ℕ × ℕ :=
  (s.1, s.2.1 - 1, s.2.2 * f s.1)

theorem powStep_iterate {α : Type*} (f : α → ℕ) (a : α) (c r j : ℕ) :
    (powStep f)^[j] (a, c, r) = (a, c - j, r * f a ^ j) := by
  induction j generalizing c r with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      show (powStep f)^[j] (a, c - 1, r * f a) = _
      rw [ih]
      have h1 : c - 1 - j = c - (j + 1) := by omega
      have h2 : r * f a * f a ^ j = r * f a ^ (j + 1) := by rw [pow_succ]; ring
      rw [h1, h2]

/-- **Powering with a bounded exponent.**  If `f` and `g` are `PolyFun`s and the exponent `g a`
is bounded by a polynomial in the size of `a`, then `a ↦ f a ^ g a` is a `PolyFun`.  The bound on
the exponent cannot be dropped: `f a ^ g a` has about `g a * Nat.size (f a)` bits. -/
theorem PolyFun.pow {α : Type*} [Enc α] {f g : α → ℕ} {q : ℕ → ℕ}
    (hf : PolyFun f) (hg : PolyFun g) (hq : ∀ a, g a ≤ q (Enc.size a)) (hqb : PolyBound q) :
    PolyFun (fun a => f a ^ g a) := by
  classical
  obtain ⟨cq, dq, hcq⟩ := hqb
  obtain ⟨Sf, hSfb, hSfmono, hSf⟩ := hf.size.exists_polyBound
  set Q : ℕ → ℕ := fun n => cq * (n + 1) ^ dq with hQdef
  have hQb : PolyBound Q := polyBound_witness cq dq
  have hQmono : ∀ {n n' : ℕ}, n ≤ n' → Q n ≤ Q n' := fun {_ _} h => polyBound_witness_mono cq dq h
  have hgQ : ∀ a, g a ≤ Q (Enc.size a) := fun a => le_trans (hq a) (hcq _)
  -- the number of rounds, read off the state
  set k : α × ℕ × ℕ → ℕ := fun s => min s.2.1 (g s.1) with hkdef
  -- the size bound of the intermediate states
  set P : ℕ → ℕ := fun n => 2 * Q n + 20 * n + 8 * (Q n * Sf n) + 28 with hPdef
  have hPb : PolyBound P :=
    ((((polyBound_const 2).mul hQb).add ((polyBound_const 20).mul polyBound_id)).add
      ((polyBound_const 8).mul (hQb.mul hSfb))).add (polyBound_const 28)
  -- one round is a `PolyFun`
  have hA : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.1) := polyFun_snd.comp polyFun_fst
  have hstep : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => (x.1 - 1, powStep f x.2)) := by
    have h1 : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.1 - 1) :=
      PolyFun.sub polyFun_fst (polyFun_const 1)
    have hB : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.2.1 - 1) :=
      PolyFun.sub ((polyFun_snd.comp polyFun_snd).comp polyFun_fst) (polyFun_const 1)
    have hC : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.2.2 * f x.2.1) :=
      PolyFun.mul ((polyFun_snd.comp polyFun_snd).comp polyFun_snd) (hA.comp hf)
    exact (h1.pair (hA.pair (hB.pair hC))).of_eq (fun x => rfl)
  -- the number of rounds is a `PolyFun`
  have hkf : PolyFun (fun s : α × ℕ × ℕ => (k s, s)) :=
    ((PolyFun.min' (polyFun_snd.comp polyFun_fst)
      (polyFun_fst.comp hg)).pair polyFun_id).of_eq (fun s => rfl)
  -- the number of rounds is polynomially bounded in the size of the state
  have hq' : ∀ s : α × ℕ × ℕ, k s ≤ Q (Enc.size s) := by
    intro s
    have h1 : k s ≤ g s.1 := min_le_right _ _
    have h3 : Enc.size s.1 ≤ Enc.size s := by
      have h := Combine.size_fst_le s.1 s.2
      simpa using h
    exact le_trans h1 (le_trans (hgQ s.1) (hQmono h3))
  -- the states the iteration passes through are polynomially large
  have hp' : ∀ s : α × ℕ × ℕ, ∀ j ≤ k s,
      Enc.size ((k s - j, (powStep f)^[j] s) : ℕ × (α × ℕ × ℕ)) ≤ P (Enc.size s) := by
    rintro ⟨a, c, r⟩ j hj
    rw [powStep_iterate]
    set n := Enc.size ((a, c, r) : α × ℕ × ℕ) with hn
    have e1 : Enc.size a ≤ n := by
      have h := Combine.size_fst_le a ((c, r) : ℕ × ℕ)
      simpa using h
    have e2' : Enc.size ((c, r) : ℕ × ℕ) ≤ n := by
      have h := Combine.size_snd_le a ((c, r) : ℕ × ℕ)
      simpa using h
    have e2 : Enc.size c ≤ n := le_trans (Combine.size_fst_le c r) e2'
    have e3 : Enc.size r ≤ n := le_trans (Combine.size_snd_le c r) e2'
    have hsc : Enc.size c = Nat.size c + 2 := Small.size_nat c
    have hsr : Enc.size r = Nat.size r + 2 := Small.size_nat r
    -- the three components
    have hA' : Enc.size (k ((a, c, r) : α × ℕ × ℕ) - j) ≤ Q n + 2 := by
      have h1 : Nat.size (k ((a, c, r) : α × ℕ × ℕ) - j)
          ≤ Nat.size (k ((a, c, r) : α × ℕ × ℕ)) := Nat.size_le_size (by omega)
      have h2 : Nat.size (k ((a, c, r) : α × ℕ × ℕ)) ≤ k ((a, c, r) : α × ℕ × ℕ) :=
        size_le_self _
      have h3 : k ((a, c, r) : α × ℕ × ℕ) ≤ Q n := hq' ((a, c, r) : α × ℕ × ℕ)
      have h4 : Enc.size (k ((a, c, r) : α × ℕ × ℕ) - j)
          = Nat.size (k ((a, c, r) : α × ℕ × ℕ) - j) + 2 := Small.size_nat _
      omega
    have hB' : Enc.size (c - j) ≤ n := by
      have h1 : Nat.size (c - j) ≤ Nat.size c := Nat.size_le_size (by omega)
      have h2 : Enc.size (c - j) = Nat.size (c - j) + 2 := Small.size_nat _
      omega
    have hC' : Enc.size (r * f a ^ j) ≤ n + Q n * Sf n + 3 := by
      have h1 : Nat.size (r * f a ^ j) ≤ Nat.size r + Nat.size (f a ^ j) := size_mul_le _ _
      have h2 : Nat.size (f a ^ j) ≤ j * Nat.size (f a) + 1 := size_pow_le _ _
      have h3 : Nat.size (f a) ≤ Sf n := by
        have h4 : Enc.size (f a) ≤ Sf (Enc.size a) := hSf a
        have h5 : Enc.size (f a) = Nat.size (f a) + 2 := Small.size_nat _
        have h6 : Sf (Enc.size a) ≤ Sf n := hSfmono _ _ e1
        omega
      have h7 : j ≤ Q n := le_trans hj (hq' ((a, c, r) : α × ℕ × ℕ))
      have h8 : j * Nat.size (f a) ≤ Q n * Sf n := Nat.mul_le_mul h7 h3
      have h9 : Enc.size (r * f a ^ j) = Nat.size (r * f a ^ j) + 2 := Small.size_nat _
      omega
    -- assemble the three of them
    have hD : Enc.size ((c - j, r * f a ^ j) : ℕ × ℕ)
        ≤ 2 * n + 2 * (n + Q n * Sf n + 3) := by
      have h := Combine.size_pair_le (c - j) (r * f a ^ j)
      omega
    have hE : Enc.size ((a, c - j, r * f a ^ j) : α × ℕ × ℕ)
        ≤ 2 * n + 2 * (2 * n + 2 * (n + Q n * Sf n + 3)) := by
      have h := Combine.size_pair_le a ((c - j, r * f a ^ j) : ℕ × ℕ)
      omega
    have hF := Combine.size_pair_le (k ((a, c, r) : α × ℕ × ℕ) - j)
      ((a, c - j, r * f a ^ j) : α × ℕ × ℕ)
    show Enc.size ((k ((a, c, r) : α × ℕ × ℕ) - j, ((a, c - j, r * f a ^ j) : α × ℕ × ℕ))
      : ℕ × (α × ℕ × ℕ)) ≤ 2 * Q n + 20 * n + 8 * (Q n * Sf n) + 28
    omega
  -- the iteration, and the read-off
  have hiter : PolyFun (fun s : α × ℕ × ℕ => (powStep f)^[k s] s) :=
    PolyFun.iterate hstep hkf hq' hQb hp' hPb
  have hinit : PolyFun (fun a : α => ((a, g a, 1) : α × ℕ × ℕ)) :=
    (polyFun_id.pair (hg.pair (polyFun_const 1))).of_eq (fun a => rfl)
  refine ((hinit.comp hiter).comp
    ((polyFun_snd : PolyFun (Prod.snd : α × ℕ × ℕ → ℕ × ℕ)).comp polyFun_snd)).of_eq (fun a => ?_)
  have hk0 : k ((a, g a, 1) : α × ℕ × ℕ) = g a := by
    simp [hkdef]
  show ((powStep f)^[k ((a, g a, 1) : α × ℕ × ℕ)] ((a, g a, 1) : α × ℕ × ℕ)).2.2 = f a ^ g a
  rw [hk0, powStep_iterate]
  simp

/-- **Powering on a pair, with the exponent cut down.**  `fun p => p.1 ^ min p.2 (q (size p))`
is not expressible, because `q` need not be computable; this is the usable form: the exponent is
any `PolyFun` of the input that a polynomial bounds. -/
theorem polyFun_pow_of_le {q : ℕ → ℕ} (hq : ∀ p : ℕ × ℕ, p.2 ≤ q (Enc.size p))
    (hqb : PolyBound q) : PolyFun (fun p : ℕ × ℕ => p.1 ^ p.2) :=
  PolyFun.pow polyFun_fst polyFun_snd hq hqb

/-! ## The factorial of a bounded argument

`Nat.factorial n` has about `n * Nat.size n` bits, so it is polynomially large exactly when `n`
is polynomially bounded, and then the same loop computes it: one round is
`(a, c, r) ↦ (a, c - 1, r * c)`, so after `j` rounds the accumulator is
`Nat.descFactorial c j`, and after `n` rounds from `(a, n, 1)` it is `Nat.descFactorial n n`,
which is `n !`. -/

/-- One round of the factorial loop: multiply the accumulator by the counter, and lower the
counter. -/
def factStep {α : Type*} (s : α × ℕ × ℕ) : α × ℕ × ℕ := (s.1, s.2.1 - 1, s.2.2 * s.2.1)

theorem factStep_iterate {α : Type*} (a : α) (c r j : ℕ) :
    (factStep (α := α))^[j] (a, c, r) = (a, c - j, r * Nat.descFactorial c j) := by
  induction j generalizing c r with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      show (factStep (α := α))^[j] (a, c - 1, r * c) = _
      rw [ih]
      have h1 : c - 1 - j = c - (j + 1) := by omega
      have h2 : r * c * Nat.descFactorial (c - 1) j = r * Nat.descFactorial c (j + 1) := by
        match c with
        | 0 => simp
        | (n + 1) =>
            rw [Nat.succ_descFactorial_succ]
            simp [mul_assoc]
      rw [h1, h2]

/-- **The factorial of a bounded argument.**  If `f` is a `PolyFun` and `f a` is bounded by a
polynomial in the size of `a`, then `a ↦ (f a)!` is a `PolyFun`.  The bound cannot be dropped:
`(f a)!` has about `f a * Nat.size (f a)` bits. -/
theorem PolyFun.factorial {α : Type*} [Enc α] {f : α → ℕ} {q : ℕ → ℕ}
    (hf : PolyFun f) (hq : ∀ a, f a ≤ q (Enc.size a)) (hqb : PolyBound q) :
    PolyFun (fun a => Nat.factorial (f a)) := by
  classical
  obtain ⟨cq, dq, hcq⟩ := hqb
  set Q : ℕ → ℕ := fun n => cq * (n + 1) ^ dq with hQdef
  have hQb : PolyBound Q := polyBound_witness cq dq
  have hQmono : ∀ {n n' : ℕ}, n ≤ n' → Q n ≤ Q n' := fun {_ _} h => polyBound_witness_mono cq dq h
  have hgQ : ∀ a, f a ≤ Q (Enc.size a) := fun a => le_trans (hq a) (hcq _)
  set k : α × ℕ × ℕ → ℕ := fun s => min s.2.1 (f s.1) with hkdef
  set P : ℕ → ℕ := fun n => 2 * Q n + 20 * n + 8 * (Q n * n) + 28 with hPdef
  have hPb : PolyBound P :=
    ((((polyBound_const 2).mul hQb).add ((polyBound_const 20).mul polyBound_id)).add
      ((polyBound_const 8).mul (hQb.mul polyBound_id))).add (polyBound_const 28)
  have hA : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.1) := polyFun_snd.comp polyFun_fst
  have hstep : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => (x.1 - 1, factStep x.2)) := by
    have h1 : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.1 - 1) :=
      PolyFun.sub polyFun_fst (polyFun_const 1)
    have hB : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.2.1 - 1) :=
      PolyFun.sub ((polyFun_snd.comp polyFun_snd).comp polyFun_fst) (polyFun_const 1)
    have hC : PolyFun (fun x : ℕ × (α × ℕ × ℕ) => x.2.2.2 * x.2.2.1) :=
      PolyFun.mul ((polyFun_snd.comp polyFun_snd).comp polyFun_snd)
        ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
    exact (h1.pair (hA.pair (hB.pair hC))).of_eq (fun x => rfl)
  have hkf : PolyFun (fun s : α × ℕ × ℕ => (k s, s)) :=
    ((PolyFun.min' (polyFun_snd.comp polyFun_fst)
      (polyFun_fst.comp hf)).pair polyFun_id).of_eq (fun s => rfl)
  have hq' : ∀ s : α × ℕ × ℕ, k s ≤ Q (Enc.size s) := by
    intro s
    have h1 : k s ≤ f s.1 := min_le_right _ _
    have h3 : Enc.size s.1 ≤ Enc.size s := by
      have h := Combine.size_fst_le s.1 s.2
      simpa using h
    exact le_trans h1 (le_trans (hgQ s.1) (hQmono h3))
  have hp' : ∀ s : α × ℕ × ℕ, ∀ j ≤ k s,
      Enc.size ((k s - j, (factStep (α := α))^[j] s) : ℕ × (α × ℕ × ℕ)) ≤ P (Enc.size s) := by
    rintro ⟨a, c, r⟩ j hj
    rw [factStep_iterate]
    set n := Enc.size ((a, c, r) : α × ℕ × ℕ) with hn
    have e1 : Enc.size a ≤ n := by
      have h := Combine.size_fst_le a ((c, r) : ℕ × ℕ)
      simpa using h
    have e2' : Enc.size ((c, r) : ℕ × ℕ) ≤ n := by
      have h := Combine.size_snd_le a ((c, r) : ℕ × ℕ)
      simpa using h
    have e2 : Enc.size c ≤ n := le_trans (Combine.size_fst_le c r) e2'
    have e3 : Enc.size r ≤ n := le_trans (Combine.size_snd_le c r) e2'
    have hsc : Enc.size c = Nat.size c + 2 := Small.size_nat c
    have hsr : Enc.size r = Nat.size r + 2 := Small.size_nat r
    have hA' : Enc.size (k ((a, c, r) : α × ℕ × ℕ) - j) ≤ Q n + 2 := by
      have h1 : Nat.size (k ((a, c, r) : α × ℕ × ℕ) - j)
          ≤ Nat.size (k ((a, c, r) : α × ℕ × ℕ)) := Nat.size_le_size (by omega)
      have h2 : Nat.size (k ((a, c, r) : α × ℕ × ℕ)) ≤ k ((a, c, r) : α × ℕ × ℕ) :=
        size_le_self _
      have h3 : k ((a, c, r) : α × ℕ × ℕ) ≤ Q n := hq' ((a, c, r) : α × ℕ × ℕ)
      have h4 : Enc.size (k ((a, c, r) : α × ℕ × ℕ) - j)
          = Nat.size (k ((a, c, r) : α × ℕ × ℕ) - j) + 2 := Small.size_nat _
      omega
    have hB' : Enc.size (c - j) ≤ n := by
      have h1 : Nat.size (c - j) ≤ Nat.size c := Nat.size_le_size (by omega)
      have h2 : Enc.size (c - j) = Nat.size (c - j) + 2 := Small.size_nat _
      omega
    have hC' : Enc.size (r * Nat.descFactorial c j) ≤ n + Q n * n + 3 := by
      have h1 : Nat.size (r * Nat.descFactorial c j)
          ≤ Nat.size r + Nat.size (Nat.descFactorial c j) := size_mul_le _ _
      have h2 : Nat.size (Nat.descFactorial c j) ≤ Nat.size (c ^ j) :=
        Nat.size_le_size (Nat.descFactorial_le_pow c j)
      have h3 : Nat.size (c ^ j) ≤ j * Nat.size c + 1 := size_pow_le _ _
      have h4 : Nat.size c ≤ n := by omega
      have h7 : j ≤ Q n := le_trans hj (hq' ((a, c, r) : α × ℕ × ℕ))
      have h8 : j * Nat.size c ≤ Q n * n := Nat.mul_le_mul h7 h4
      have h9 : Enc.size (r * Nat.descFactorial c j)
          = Nat.size (r * Nat.descFactorial c j) + 2 := Small.size_nat _
      omega
    have hD : Enc.size ((c - j, r * Nat.descFactorial c j) : ℕ × ℕ)
        ≤ 2 * n + 2 * (n + Q n * n + 3) := by
      have h := Combine.size_pair_le (c - j) (r * Nat.descFactorial c j)
      omega
    have hE : Enc.size ((a, c - j, r * Nat.descFactorial c j) : α × ℕ × ℕ)
        ≤ 2 * n + 2 * (2 * n + 2 * (n + Q n * n + 3)) := by
      have h := Combine.size_pair_le a ((c - j, r * Nat.descFactorial c j) : ℕ × ℕ)
      omega
    have hF := Combine.size_pair_le (k ((a, c, r) : α × ℕ × ℕ) - j)
      ((a, c - j, r * Nat.descFactorial c j) : α × ℕ × ℕ)
    show Enc.size ((k ((a, c, r) : α × ℕ × ℕ) - j,
      ((a, c - j, r * Nat.descFactorial c j) : α × ℕ × ℕ)) : ℕ × (α × ℕ × ℕ))
        ≤ 2 * Q n + 20 * n + 8 * (Q n * n) + 28
    omega
  have hiter : PolyFun (fun s : α × ℕ × ℕ => (factStep (α := α))^[k s] s) :=
    PolyFun.iterate hstep hkf hq' hQb hp' hPb
  have hinit : PolyFun (fun a : α => ((a, f a, 1) : α × ℕ × ℕ)) :=
    (polyFun_id.pair (hf.pair (polyFun_const 1))).of_eq (fun a => rfl)
  refine ((hinit.comp hiter).comp
    ((polyFun_snd : PolyFun (Prod.snd : α × ℕ × ℕ → ℕ × ℕ)).comp polyFun_snd)).of_eq (fun a => ?_)
  have hk0 : k ((a, f a, 1) : α × ℕ × ℕ) = f a := by
    simp [hkdef]
  show ((factStep (α := α))^[k ((a, f a, 1) : α × ℕ × ℕ)] ((a, f a, 1) : α × ℕ × ℕ)).2.2
      = Nat.factorial (f a)
  rw [hk0, factStep_iterate]
  simp [Nat.descFactorial_self]

/-! ## Binomial coefficients

`Nat.choose n k` is at most `2 ^ n`, so it is polynomially large exactly when `n` is polynomially
bounded, and then it is three factorials and one division:
`n.choose k = n ! / (k ! * (n - k)!)` for `k ≤ n`, and `0` for `k > n`.  The second argument is
cut down to `min (g a) (f a)` so that it, too, is bounded; on the branch that is taken the two
agree. -/

/-- **Binomial coefficients with a bounded upper index.** -/
theorem PolyFun.choose {α : Type*} [Enc α] {f g : α → ℕ} {q : ℕ → ℕ}
    (hf : PolyFun f) (hg : PolyFun g) (hq : ∀ a, f a ≤ q (Enc.size a)) (hqb : PolyBound q) :
    PolyFun (fun a => Nat.choose (f a) (g a)) := by
  have h1 : PolyFun (fun a => Nat.factorial (f a)) := hf.factorial hq hqb
  have h2 : PolyFun (fun a => Nat.factorial (min (g a) (f a))) :=
    (hg.min' hf).factorial (fun a => le_trans (min_le_right _ _) (hq a)) hqb
  have h3 : PolyFun (fun a => Nat.factorial (f a - g a)) :=
    (hf.sub hg).factorial (fun a => le_trans (Nat.sub_le _ _) (hq a)) hqb
  refine (PolyFun.ite (hg.le hf) (h1.div (h2.mul h3)) (polyFun_const 0)).of_eq (fun a => ?_)
  by_cases h : g a ≤ f a
  · simp only [h, decide_true, if_true, min_eq_left h]
    exact (Nat.choose_eq_factorial_div_factorial h).symm
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

end RAM
