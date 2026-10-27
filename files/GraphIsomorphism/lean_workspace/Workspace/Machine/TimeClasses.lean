import Workspace.Machine.Encoding

/-!
# Running time classes

What it means for a RAM program to compute a function, or to solve a search problem, within a
given time bound, and the two classes of bounds we need: polynomial and quasipolynomial.

Three shapes of problem occur in Babai's paper.

* A **function** `f : α → β` (for instance: the coherent closure of a configuration).
* A **relation** `R : α → β → Prop` whose solutions are not unique.  Most outputs of the paper
  are of this kind: a *generating set* of `Aut_G(x)` is not determined by the input, nor is the
  coset representative in `Iso_G(x,y)`.  `SolvesInTime` asks the program to output *some* `b`
  with `R a b`.
* A **decision problem**, a predicate `α → Prop`, handled as a function into `Bool`.

The time bound is a function of the *input size*, `Enc.size a`, the total bit length of the
encoding (`Workspace/Machine/Encoding.lean`).

Quasipolynomial is taken in the form `T n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c)`, that is,
`exp(O((log n)^{O(1)}))`, as in Theorem 1.1.1 of the paper.  The additive constant `2` inside
makes the bound meaningful at `n = 0, 1` as well; without it the class would not even contain
the constant functions, and would not contain the polynomial bounds (`PolyBound.quasiPoly`).
-/

namespace RAM

variable {α β γ : Type*}

/-! ## Computing within a time bound -/

/-- `ComputesInTime P f T`: started on the encoding of `a` in the input convention and with all
other registers zero, `P` halts after at most `T (Enc.size a)` executed instructions, with the
encoding of `f a` in the output convention. -/
def ComputesInTime [Enc α] [Enc β] (P : Program) (f : α → β) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, ∃ k ≤ T (Enc.size a),
    Halted P (run P (Config.init (Enc.encode a)) k) ∧
      OutputAt (run P (Config.init (Enc.encode a)) k).mem (Enc.encode (f a))

/-- `SolvesInTime P R T`: the search version.  On input `a` the program halts within
`T (Enc.size a)` steps with the encoding of *some* `b` satisfying `R a b`.  This is the form
the paper's outputs take, since generating sets and coset representatives are not unique. -/
def SolvesInTime [Enc α] [Enc β] (P : Program) (R : α → β → Prop) (T : ℕ → ℕ) : Prop :=
  ∀ a : α, ∃ b : β, R a b ∧ ∃ k ≤ T (Enc.size a),
    Halted P (run P (Config.init (Enc.encode a)) k) ∧
      OutputAt (run P (Config.init (Enc.encode a)) k).mem (Enc.encode b)

/-- `DecidesInTime P p T`: the decision version, a function into `Bool`. -/
def DecidesInTime [Enc α] (P : Program) (p : α → Prop) [DecidablePred p] (T : ℕ → ℕ) : Prop :=
  ComputesInTime P (fun a => decide (p a)) T

/-- A program computing `f` solves the graph of `f`. -/
theorem ComputesInTime.solvesInTime [Enc α] [Enc β] {P : Program} {f : α → β} {T : ℕ → ℕ}
    (h : ComputesInTime P f T) : SolvesInTime P (fun a b => b = f a) T := by
  intro a
  obtain ⟨k, hk, hhalt, hout⟩ := h a
  exact ⟨f a, rfl, k, hk, hhalt, hout⟩

theorem ComputesInTime.mono [Enc α] [Enc β] {P : Program} {f : α → β} {T T' : ℕ → ℕ}
    (h : ComputesInTime P f T) (hT : ∀ n, T n ≤ T' n) : ComputesInTime P f T' := by
  intro a
  obtain ⟨k, hk, h'⟩ := h a
  exact ⟨k, le_trans hk (hT _), h'⟩

theorem SolvesInTime.mono [Enc α] [Enc β] {P : Program} {R : α → β → Prop} {T T' : ℕ → ℕ}
    (h : SolvesInTime P R T) (hT : ∀ n, T n ≤ T' n) : SolvesInTime P R T' := by
  intro a
  obtain ⟨b, hb, k, hk, h'⟩ := h a
  exact ⟨b, hb, k, le_trans hk (hT _), h'⟩

/-- A program solving a relation also solves any weaker relation. -/
theorem SolvesInTime.imp [Enc α] [Enc β] {P : Program} {R R' : α → β → Prop} {T : ℕ → ℕ}
    (h : SolvesInTime P R T) (hRR : ∀ a b, R a b → R' a b) : SolvesInTime P R' T := by
  intro a
  obtain ⟨b, hb, rest⟩ := h a
  exact ⟨b, hRR a b hb, rest⟩

/-! ## Polynomial and quasipolynomial bounds -/

/-- A polynomial bound on a time function.  Written with `(n + 1) ^ d` rather than `n ^ d`:
this is the same class of bounds (every polynomial in `n` is below some `c * (n+1)^d`, and
conversely), and it avoids the degenerate behaviour of `n ^ d` at `n = 0`. -/
def PolyBound (T : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, T n ≤ c * (n + 1) ^ d

/-- A quasipolynomial bound on a time function: `T n ≤ exp((log n)^{O(1)})`. -/
def QuasiPolyBound (T : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ n, T n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c)

theorem PolyBound.mono {T T' : ℕ → ℕ} (h : PolyBound T) (hT : ∀ n, T' n ≤ T n) :
    PolyBound T' := by
  obtain ⟨c, d, hc⟩ := h
  exact ⟨c, d, fun n => le_trans (hT n) (hc n)⟩

theorem QuasiPolyBound.mono {T T' : ℕ → ℕ} (h : QuasiPolyBound T) (hT : ∀ n, T' n ≤ T n) :
    QuasiPolyBound T' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun n => le_trans (hT n) (hc n)⟩

theorem polyBound_const (c : ℕ) : PolyBound (fun _ => c) := ⟨c, 0, fun _ => by simp⟩

theorem polyBound_id : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩

theorem PolyBound.add {T S : ℕ → ℕ} (hT : PolyBound T) (hS : PolyBound S) :
    PolyBound (fun n => T n + S n) := by
  obtain ⟨c, d, hc⟩ := hT
  obtain ⟨c', d', hc'⟩ := hS
  refine ⟨c + c', max d d', fun n => ?_⟩
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ max d d' :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : (n + 1) ^ d' ≤ (n + 1) ^ max d d' :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc T n + S n ≤ c * (n + 1) ^ d + c' * (n + 1) ^ d' := Nat.add_le_add (hc n) (hc' n)
    _ ≤ c * (n + 1) ^ max d d' + c' * (n + 1) ^ max d d' :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (c + c') * (n + 1) ^ max d d' := by ring

theorem PolyBound.mul {T S : ℕ → ℕ} (hT : PolyBound T) (hS : PolyBound S) :
    PolyBound (fun n => T n * S n) := by
  obtain ⟨c, d, hc⟩ := hT
  obtain ⟨c', d', hc'⟩ := hS
  refine ⟨c * c', d + d', fun n => ?_⟩
  calc T n * S n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') := Nat.mul_le_mul (hc n) (hc' n)
    _ = c * c' * (n + 1) ^ (d + d') := by rw [pow_add]; ring

/-! ### Polynomial implies quasipolynomial -/

theorem le_two_pow_log (n : ℕ) : n ≤ 2 ^ (Nat.log 2 n + 1) :=
  le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)

theorem succ_le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 n + 2) := by
  have h1 := le_two_pow_log n
  have h2 : (1:ℕ) ≤ 2 ^ (Nat.log 2 n + 1) := Nat.one_le_two_pow
  have h3 : (2:ℕ) ^ (Nat.log 2 n + 1) + 2 ^ (Nat.log 2 n + 1) = 2 ^ (Nat.log 2 n + 2) := by
    rw [pow_succ]; ring
  omega

/-- The key inequality behind both `PolyBound.quasiPoly` and `QuasiPolyBound.comp_poly`:
a value bounded by `c * (n+1)^d` is bounded by `2 ^ (Nat.size (c+1) + (Nat.log 2 n + 2) * d)`. -/
theorem poly_le_two_pow (c d n : ℕ) :
    c * (n + 1) ^ d ≤ 2 ^ (Nat.size (c + 1) + (Nat.log 2 n + 2) * d) := by
  set L := Nat.log 2 n + 2 with hL
  have hnd : (n + 1) ^ d ≤ 2 ^ (L * d) := by
    calc (n + 1) ^ d ≤ (2 ^ L) ^ d := Nat.pow_le_pow_left (succ_le_two_pow_log n) d
      _ = 2 ^ (L * d) := by rw [← pow_mul]
  have hcs : c ≤ 2 ^ Nat.size (c + 1) :=
    le_trans (by omega) (le_of_lt (Nat.lt_size_self (c + 1)))
  calc c * (n + 1) ^ d ≤ 2 ^ Nat.size (c + 1) * 2 ^ (L * d) := Nat.mul_le_mul hcs hnd
    _ = 2 ^ (Nat.size (c + 1) + L * d) := by rw [pow_add]

theorem PolyBound.quasiPoly {T : ℕ → ℕ} (h : PolyBound T) : QuasiPolyBound T := by
  obtain ⟨c, d, hc⟩ := h
  set s := Nat.size (c + 1) with hs
  refine ⟨s + d + 1, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hmain : T n ≤ 2 ^ (s + L * d) := le_trans (hc n) (poly_le_two_pow c d n)
  refine le_trans hmain (Nat.pow_le_pow_right (by norm_num) ?_)
  have hbig : 2 ^ (s + d) * L ≤ L ^ (s + d + 1) := by
    calc 2 ^ (s + d) * L ≤ L ^ (s + d) * L := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL2 _)
      _ = L ^ (s + d + 1) := by rw [pow_succ]
  have hsd : s + d + 1 ≤ 2 ^ (s + d) := Nat.lt_two_pow_self
  have hexp : (s + d + 1) * L ≤ 2 ^ (s + d) * L := Nat.mul_le_mul_right _ hsd
  have hring : (s + d + 1) * L = s * L + d * L + L := by ring
  have h3 : s ≤ s * L := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : L * d = d * L := by ring
  omega

/-! ### Closure of quasipolynomial bounds -/

theorem QuasiPolyBound.add {T S : ℕ → ℕ} (hT : QuasiPolyBound T) (hS : QuasiPolyBound S) :
    QuasiPolyBound (fun n => T n + S n) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨c', hc'⟩ := hS
  refine ⟨max c c' + 1, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have h1 : T n ≤ 2 ^ (L ^ max c c') :=
    le_trans (hc n) (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by omega) (le_max_left _ _)))
  have h2 : S n ≤ 2 ^ (L ^ max c c') :=
    le_trans (hc' n) (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
  have hstep : (2:ℕ) ^ (L ^ max c c') + 2 ^ (L ^ max c c') = 2 ^ (L ^ max c c' + 1) := by
    rw [pow_succ]; ring
  have hle : L ^ max c c' + 1 ≤ L ^ (max c c' + 1) := by
    have : L ^ max c c' * 2 ≤ L ^ max c c' * L := Nat.mul_le_mul_left _ hL2
    have h4 : L ^ max c c' * L = L ^ (max c c' + 1) := by rw [pow_succ]
    have h5 : (1:ℕ) ≤ L ^ max c c' := Nat.one_le_pow _ _ (by omega)
    omega
  calc T n + S n ≤ 2 ^ (L ^ max c c') + 2 ^ (L ^ max c c') := by omega
    _ = 2 ^ (L ^ max c c' + 1) := hstep
    _ ≤ 2 ^ (L ^ (max c c' + 1)) := Nat.pow_le_pow_right (by norm_num) hle

theorem QuasiPolyBound.mul {T S : ℕ → ℕ} (hT : QuasiPolyBound T) (hS : QuasiPolyBound S) :
    QuasiPolyBound (fun n => T n * S n) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨c', hc'⟩ := hS
  refine ⟨max c c' + 1, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  set M := max c c' with hM
  have h1 : T n ≤ 2 ^ (L ^ M) :=
    le_trans (hc n) (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by omega) (le_max_left _ _)))
  have h2 : S n ≤ 2 ^ (L ^ M) :=
    le_trans (hc' n) (Nat.pow_le_pow_right (by norm_num)
      (Nat.pow_le_pow_right (by omega) (le_max_right _ _)))
  have hle : L ^ M + L ^ M ≤ L ^ (M + 1) := by
    have h3 : L ^ M * 2 ≤ L ^ M * L := Nat.mul_le_mul_left _ hL2
    have h4 : L ^ M * L = L ^ (M + 1) := by rw [pow_succ]
    omega
  calc T n * S n ≤ 2 ^ (L ^ M) * 2 ^ (L ^ M) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (L ^ M + L ^ M) := by rw [pow_add]
    _ ≤ 2 ^ (L ^ (M + 1)) := Nat.pow_le_pow_right (by norm_num) hle

/-! ### Composing a quasipolynomial bound with a polynomially bounded input size

The paper's reductions feed the output of one polynomial-time procedure into the next; the
input size of the second is polynomially bounded in the original input size, and this is what
keeps the composite quasipolynomial. -/

theorem log_poly_le (c d : ℕ) (n : ℕ) :
    Nat.log 2 (c * (n + 1) ^ d) + 2 ≤ (Nat.size (c + 1) + d + 2) * (Nat.log 2 n + 2) := by
  set L := Nat.log 2 n + 2 with hL
  set s := Nat.size (c + 1) with hs
  have hval := poly_le_two_pow c d n
  have hlog : Nat.log 2 (c * (n + 1) ^ d) ≤ s + L * d := by
    calc Nat.log 2 (c * (n + 1) ^ d) ≤ Nat.log 2 (2 ^ (s + L * d)) := Nat.log_mono_right hval
      _ = s + L * d := Nat.log_pow (by norm_num) _
  have hring : (s + d + 2) * L = s * L + d * L + 2 * L := by ring
  have h3 : s ≤ s * L := Nat.le_mul_of_pos_right _ (by omega)
  have h4 : L * d = d * L := by ring
  have h5 : (2:ℕ) ≤ 2 * L := by omega
  omega

/-- A quasipolynomial bound composed with a polynomial bound on the input size is
quasipolynomial.  This is what keeps the paper's chains of reductions quasipolynomial: each
step blows the input size up by at most a polynomial. -/
theorem QuasiPolyBound.comp_poly {T S : ℕ → ℕ} (hT : QuasiPolyBound T) (hS : PolyBound S) :
    QuasiPolyBound (fun n => T (S n)) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨a, d, ha⟩ := hS
  set e := Nat.size (a + 1) + d + 2 with he
  refine ⟨Nat.size (e + 1) * c + c, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have h1 : T (S n) ≤ 2 ^ ((Nat.log 2 (S n) + 2) ^ c) := hc (S n)
  have h2 : Nat.log 2 (S n) + 2 ≤ e * L := by
    have hmonolog : Nat.log 2 (S n) ≤ Nat.log 2 (a * (n + 1) ^ d) := Nat.log_mono_right (ha n)
    have hlp := log_poly_le a d n
    rw [← he, ← hL] at hlp
    omega
  have h3 : (Nat.log 2 (S n) + 2) ^ c ≤ (e * L) ^ c := Nat.pow_le_pow_left h2 c
  have h4 : (e * L) ^ c = e ^ c * L ^ c := by rw [mul_pow]
  have he1 : e + 1 ≤ 2 ^ Nat.size (e + 1) := le_of_lt (Nat.lt_size_self (e + 1))
  have h5 : e ^ c ≤ L ^ (Nat.size (e + 1) * c) := by
    calc e ^ c ≤ (2 ^ Nat.size (e + 1)) ^ c := Nat.pow_le_pow_left (by omega) c
      _ = (2 ^ c) ^ Nat.size (e + 1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (L ^ c) ^ Nat.size (e + 1) := Nat.pow_le_pow_left (Nat.pow_le_pow_left hL2 c) _
      _ = L ^ (c * Nat.size (e + 1)) := by rw [← pow_mul]
      _ = L ^ (Nat.size (e + 1) * c) := by rw [Nat.mul_comm]
  have h6 : e ^ c * L ^ c ≤ L ^ (Nat.size (e + 1) * c + c) := by
    calc e ^ c * L ^ c ≤ L ^ (Nat.size (e + 1) * c) * L ^ c := Nat.mul_le_mul_right _ h5
      _ = L ^ (Nat.size (e + 1) * c + c) := by rw [← pow_add]
  calc T (S n) ≤ 2 ^ ((Nat.log 2 (S n) + 2) ^ c) := h1
    _ ≤ 2 ^ ((e * L) ^ c) := Nat.pow_le_pow_right (by norm_num) h3
    _ ≤ 2 ^ (L ^ (Nat.size (e + 1) * c + c)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rw [h4]; exact h6

/-! ### Composing two quasipolynomial bounds

A quasipolynomial of a quasipolynomial is quasipolynomial: writing `L = log n + 2`, from
`S n ≤ 2 ^ (L ^ a)` we get `log (S n) + 2 ≤ L ^ a + 2 ≤ L ^ (a + 1)`, so
`T (S n) ≤ 2 ^ ((L ^ (a+1)) ^ c) = 2 ^ (L ^ ((a+1) * c))`.  This is the identity
`exp((log exp((log n)^a))^c) = exp((log n)^{ac})` of the informal statement. -/

/-- The witness of a quasipolynomial bound may always be taken with a positive exponent: this is
the form in which `QuasiPolyBound.comp` uses it, because `L ^ a ≥ 2` is needed. -/
theorem QuasiPolyBound.pos_witness {S : ℕ → ℕ} (h : QuasiPolyBound S) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ n, S n ≤ 2 ^ ((Nat.log 2 n + 2) ^ a) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨max a 1, le_max_right _ _, fun n => ?_⟩
  refine le_trans (ha n) (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Nat.pow_le_pow_right (by omega) (le_max_left _ _)

/-- **A quasipolynomial of a quasipolynomial is quasipolynomial.** -/
theorem QuasiPolyBound.comp {T S : ℕ → ℕ} (hT : QuasiPolyBound T) (hS : QuasiPolyBound S) :
    QuasiPolyBound (fun n => T (S n)) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨a, ha1, ha⟩ := hS.pos_witness
  refine ⟨(a + 1) * c, fun n => ?_⟩
  set L := Nat.log 2 n + 2 with hL
  have hL2 : 2 ≤ L := by omega
  have hLa : 2 ≤ L ^ a := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ L ^ 1 := Nat.pow_le_pow_left hL2 1
      _ ≤ L ^ a := Nat.pow_le_pow_right (by omega) ha1
  have hlog : Nat.log 2 (S n) ≤ L ^ a := by
    calc Nat.log 2 (S n) ≤ Nat.log 2 (2 ^ (L ^ a)) := Nat.log_mono_right (ha n)
      _ = L ^ a := Nat.log_pow (by norm_num) _
  have hstep : Nat.log 2 (S n) + 2 ≤ L ^ (a + 1) := by
    have : L ^ a * 2 ≤ L ^ a * L := Nat.mul_le_mul_left _ hL2
    have h2 : L ^ a * L = L ^ (a + 1) := by rw [pow_succ]
    omega
  calc T (S n) ≤ 2 ^ ((Nat.log 2 (S n) + 2) ^ c) := hc (S n)
    _ ≤ 2 ^ ((L ^ (a + 1)) ^ c) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hstep c)
    _ = 2 ^ (L ^ ((a + 1) * c)) := by rw [← pow_mul]

/-- **A polynomial of a quasipolynomial is quasipolynomial.** -/
theorem PolyBound.comp_quasiPoly {T S : ℕ → ℕ} (hT : PolyBound T) (hS : QuasiPolyBound S) :
    QuasiPolyBound (fun n => T (S n)) := hT.quasiPoly.comp hS

/-! ## The time classes -/

/-- A function computable in polynomial time on the RAM. -/
def PolyTime [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ ComputesInTime P f T

/-- A function computable in quasipolynomial time on the RAM. -/
def QuasiPolyTime [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ ComputesInTime P f T

/-- A search problem solvable in polynomial time on the RAM. -/
def PolyTimeRel [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), PolyBound T ∧ SolvesInTime P R T

/-- A search problem solvable in quasipolynomial time on the RAM.  This is the form of
Theorem 1.1.1 of the paper. -/
def QuasiPolyTimeRel [Enc α] [Enc β] (R : α → β → Prop) : Prop :=
  ∃ (P : Program) (T : ℕ → ℕ), QuasiPolyBound T ∧ SolvesInTime P R T

/-- A decision problem solvable in polynomial time on the RAM. -/
def PolyTimeDec [Enc α] (p : α → Prop) [DecidablePred p] : Prop :=
  PolyTime (fun a => decide (p a))

/-- A decision problem solvable in quasipolynomial time on the RAM. -/
def QuasiPolyTimeDec [Enc α] (p : α → Prop) [DecidablePred p] : Prop :=
  QuasiPolyTime (fun a => decide (p a))

theorem PolyTime.quasiPolyTime [Enc α] [Enc β] {f : α → β} (h : PolyTime f) :
    QuasiPolyTime f := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT.quasiPoly, hP⟩

theorem PolyTimeRel.quasiPolyTimeRel [Enc α] [Enc β] {R : α → β → Prop} (h : PolyTimeRel R) :
    QuasiPolyTimeRel R := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT.quasiPoly, hP⟩

theorem PolyTime.polyTimeRel [Enc α] [Enc β] {f : α → β} (h : PolyTime f) :
    PolyTimeRel (fun a b => b = f a) := by
  obtain ⟨P, T, hT, hP⟩ := h
  exact ⟨P, T, hT, hP.solvesInTime⟩

end RAM
