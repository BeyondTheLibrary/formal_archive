import Workspace.Machine.Closure

/-!
# A function-level interface: `PolyFun` and `QuasiPolyFun`

Every combinator of `Workspace/Machine/Closure.lean` carries two kinds of side condition: the
number `K` of work registers of the workspace convention, and a *polynomial bound on the size of
the intermediate results*.  The second one is genuinely necessary (`DESIGN.md`, "Doubts" item 3:
a `T`-step clean routine may output an encoding of length `2 ^ T`), but it is a nuisance to carry
through every step of an assembly.  This file discharges both once and for all, by packing them
into the predicate a later section actually wants:

`PolyFun f` : `f` is computed by a clean polynomial-time routine at the workspace convention
with `K = 16` work registers, **and** the encoding of `f a` is polynomially bounded in the
encoding of `a`.

`QuasiPolyFun f` is the same with a quasipolynomial time bound (the size bound stays polynomial:
it is what keeps the composition of quasipolynomial routines quasipolynomial, see
`RAM.QuasiPolyBound.comp_poly`).

With these, a later agent proves "this procedure of the paper runs in polynomial time" by
structural steps only: `PolyFun.comp`, `PolyFun.pair`, `PolyFun.ite`, `PolyFun.iterate`, and the
base cases below.  No size hypothesis appears in any of them except in `iterate`, where it cannot
be avoided.

## The size bound

`RAM.SizeBound f` is stated in the explicit form `Enc.size (f a) ≤ c * (Enc.size a + 1) ^ d`
rather than as `∃ S, PolyBound S ∧ ...`: the explicit witness is monotone, which is what the
composition lemmas need, and it is the normal form `RAM.polyBound_witness` produces anyway.

## What is still missing

`PolyFun f → PolyTime f` — the bridge from the workspace convention down to the top-level
convention of `RAM.PolyTime` — is **not** available yet; see "What remains" item 1 of
`Workspace/Machine/DESIGN.md`.  Everything else in this file is proved.
-/

namespace RAM

variable {α β γ σ : Type*}

/-! ## Polynomially bounded output size -/

/-- `SizeBound f`: the encoding of `f a` is polynomially bounded in the encoding of `a`.  The
bound is given in the explicit monotone form `c * (n + 1) ^ d`. -/
def SizeBound [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ c d : ℕ, ∀ a, Enc.size (f a) ≤ c * (Enc.size a + 1) ^ d

namespace SizeBound

/-- The bound as a `PolyBound`, in the form the combinators of `Closure.lean` take. -/
theorem exists_polyBound [Enc α] [Enc β] {f : α → β} (h : SizeBound f) :
    ∃ S : ℕ → ℕ, PolyBound S ∧ (∀ n n', n ≤ n' → S n ≤ S n') ∧
      ∀ a, Enc.size (f a) ≤ S (Enc.size a) := by
  obtain ⟨c, d, hc⟩ := h
  exact ⟨fun n => c * (n + 1) ^ d, polyBound_witness c d,
    fun _ _ h => polyBound_witness_mono c d h, hc⟩

theorem of_bounded [Enc α] [Enc β] {f : α → β} {c : ℕ} (h : ∀ a, Enc.size (f a) ≤ c) :
    SizeBound f := ⟨c, 0, fun a => by simpa using h a⟩

theorem of_le [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hg : SizeBound g)
    (h : ∀ a, Enc.size (f a) ≤ Enc.size (g a)) : SizeBound f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun a => le_trans (h a) (hc a)⟩

theorem id' [Enc α] : SizeBound (id : α → α) :=
  ⟨1, 1, fun a => by simp⟩

theorem const [Enc α] [Enc β] (b : β) : SizeBound (fun _ : α => b) :=
  of_bounded (c := Enc.size b) (fun _ => le_refl _)

/-- A polynomial of a polynomial is a polynomial: the size bounds compose. -/
theorem comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : SizeBound f)
    (hg : SizeBound g) : SizeBound (fun a => g (f a)) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨c', d', hc'⟩ := hg
  refine ⟨c' * (c + 1) ^ d', d * d', fun a => ?_⟩
  set n := Enc.size a with hn
  have hca : Enc.size (f a) ≤ c * (n + 1) ^ d := hc a
  have h1 : Enc.size (f a) + 1 ≤ (c + 1) * (n + 1) ^ d := by
    have h2 : (1:ℕ) ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    calc Enc.size (f a) + 1 ≤ c * (n + 1) ^ d + (n + 1) ^ d := by omega
      _ = (c + 1) * (n + 1) ^ d := by ring
  calc Enc.size (g (f a)) ≤ c' * (Enc.size (f a) + 1) ^ d' := hc' (f a)
    _ ≤ c' * ((c + 1) * (n + 1) ^ d) ^ d' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d')
    _ = c' * (c + 1) ^ d' * (n + 1) ^ (d * d') := by rw [mul_pow, ← pow_mul]; ring

theorem pair [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hf : SizeBound f)
    (hg : SizeBound g) : SizeBound (fun a => (f a, g a)) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨c', d', hc'⟩ := hg
  refine ⟨2 * c + 2 * c', max d d', fun a => ?_⟩
  set n := Enc.size a with hn
  have hca : Enc.size (f a) ≤ c * (n + 1) ^ d := hc a
  have hca' : Enc.size (g a) ≤ c' * (n + 1) ^ d' := hc' a
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ max d d' :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : (n + 1) ^ d' ≤ (n + 1) ^ max d d' :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc Enc.size ((f a, g a) : β × γ) ≤ 2 * Enc.size (f a) + 2 * Enc.size (g a) :=
        Combine.size_pair_le _ _
    _ ≤ 2 * (c * (n + 1) ^ d) + 2 * (c' * (n + 1) ^ d') := by omega
    _ ≤ 2 * (c * (n + 1) ^ max d d') + 2 * (c' * (n + 1) ^ max d d') := by
        have := Nat.mul_le_mul_left c h1
        have := Nat.mul_le_mul_left c' h2
        omega
    _ = (2 * c + 2 * c') * (n + 1) ^ max d d' := by ring

theorem fst [Enc α] [Enc β] : SizeBound (Prod.fst : α × β → α) :=
  of_le (g := id) id' (fun p => Combine.size_fst_le p.1 p.2)

theorem snd [Enc α] [Enc β] : SizeBound (Prod.snd : α × β → β) :=
  of_le (g := id) id' (fun p => Combine.size_snd_le p.1 p.2)

theorem ite' [Enc α] [Enc β] {p : α → Bool} {f g : α → β} (hf : SizeBound f)
    (hg : SizeBound g) : SizeBound (fun a => if p a then f a else g a) := by
  obtain ⟨c, d, hc⟩ := hf
  obtain ⟨c', d', hc'⟩ := hg
  refine ⟨c + c', max d d', fun a => ?_⟩
  set n := Enc.size a with hn
  have h1 : c * (n + 1) ^ d ≤ (c + c') * (n + 1) ^ max d d' := by
    have := Nat.mul_le_mul_left c (Nat.pow_le_pow_right (show 0 < n + 1 by omega)
      (le_max_left d d'))
    have h2 : c * (n + 1) ^ max d d' ≤ (c + c') * (n + 1) ^ max d d' :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : c' * (n + 1) ^ d' ≤ (c + c') * (n + 1) ^ max d d' := by
    have := Nat.mul_le_mul_left c' (Nat.pow_le_pow_right (show 0 < n + 1 by omega)
      (le_max_right d d'))
    have h3 : c' * (n + 1) ^ max d d' ≤ (c + c') * (n + 1) ^ max d d' :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  by_cases hp : p a
  · simp only [hp, if_true]
    exact le_trans (hc a) h1
  · simp only [hp, if_false, Bool.false_eq_true]
    exact le_trans (hc' a) h2

/-- A natural-number valued function whose result has at most as many bits as the input
encoding.  This is the shape of every arithmetic primitive below. -/
theorem of_nat [Enc α] {f : α → ℕ} (h : ∀ a, Nat.size (f a) ≤ Enc.size a) : SizeBound f := by
  refine ⟨3, 1, fun a => ?_⟩
  have h1 := h a
  have h2 : Enc.size (f a) = Nat.size (f a) + 2 := Small.size_nat _
  have : 3 * (Enc.size a + 1) ^ 1 = 3 * Enc.size a + 3 := by ring
  omega

end SizeBound

/-! ## The two classes -/

/-- `PolyFun f`: `f` is computed by a clean polynomial-time routine at the workspace convention
with sixteen work registers, and the size of the output is polynomially bounded in the size of
the input. -/
structure PolyFun [Enc α] [Enc β] (f : α → β) : Prop where
  /-- A clean polynomial-time routine at the workspace convention `K = 16`. -/
  time : PolyTimeCleanAt 16 f
  /-- The encoding of `f a` is polynomially bounded in the encoding of `a`. -/
  size : SizeBound f

/-- `QuasiPolyFun f`: the quasipolynomial-time version of `RAM.PolyFun`.  The size bound stays
*polynomial*: that is what keeps a composition of quasipolynomial routines quasipolynomial
(`RAM.QuasiPolyBound.comp_poly`). -/
structure QuasiPolyFun [Enc α] [Enc β] (f : α → β) : Prop where
  /-- A clean quasipolynomial-time routine at the workspace convention `K = 16`. -/
  time : QuasiPolyTimeCleanAt 16 f
  /-- The encoding of `f a` is polynomially bounded in the encoding of `a`. -/
  size : SizeBound f

theorem PolyFun.quasiPolyFun [Enc α] [Enc β] {f : α → β} (h : PolyFun f) : QuasiPolyFun f :=
  ⟨h.time.quasiPolyTimeCleanAt, h.size⟩

/-- Every clean polynomial-time routine of the *top-level* convention is a `PolyFun`, once its
output size is bounded.  This is how the primitives of `Workspace/Machine/Small.lean` enter. -/
theorem polyFun_of_polyTimeClean [Enc α] [Enc β] {f : α → β} (ht : PolyTimeClean f)
    (hs : SizeBound f) : PolyFun f :=
  ⟨polyTimeCleanAt_of_polyTimeClean (by omega) ht, hs⟩

/-! ## The structural closure rules

Each of these is the corresponding rule of `Workspace/Machine/Closure.lean` with the register
count and the size hypotheses discharged. -/

theorem polyFun_id [Enc α] : PolyFun (id : α → α) :=
  ⟨polyTimeCleanAt_id 16, SizeBound.id'⟩

theorem polyFun_const [Enc α] [Enc β] (b : β) : PolyFun (fun _ : α => b) :=
  polyFun_of_polyTimeClean (polyTimeClean_const b) (SizeBound.const b)

theorem quasiPolyFun_const [Enc α] [Enc β] (b : β) : QuasiPolyFun (fun _ : α => b) :=
  (polyFun_const b).quasiPolyFun

/-- **Composition.** -/
theorem PolyFun.comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : PolyFun f)
    (hg : PolyFun g) : PolyFun (fun a => g (f a)) := by
  obtain ⟨S, hSb, -, hS⟩ := hf.size.exists_polyBound
  exact ⟨hf.time.comp hg.time hSb hS, hf.size.comp hg.size⟩

/-- **Composition, quasipolynomial time.** -/
theorem QuasiPolyFun.comp [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : QuasiPolyFun f)
    (hg : QuasiPolyFun g) : QuasiPolyFun (fun a => g (f a)) := by
  obtain ⟨S, hSb, -, hS⟩ := hf.size.exists_polyBound
  exact ⟨hf.time.comp hg.time hSb hS, hf.size.comp hg.size⟩

theorem QuasiPolyFun.comp_poly [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ}
    (hf : QuasiPolyFun f) (hg : PolyFun g) : QuasiPolyFun (fun a => g (f a)) :=
  hf.comp hg.quasiPolyFun

theorem PolyFun.comp_quasi [Enc α] [Enc β] [Enc γ] {f : α → β} {g : β → γ} (hf : PolyFun f)
    (hg : QuasiPolyFun g) : QuasiPolyFun (fun a => g (f a)) :=
  hf.quasiPolyFun.comp hg

/-- **Pairing.** -/
theorem PolyFun.pair [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hf : PolyFun f)
    (hg : PolyFun g) : PolyFun (fun a => (f a, g a)) := by
  obtain ⟨Sf, hSfb, -, hSf⟩ := hf.size.exists_polyBound
  obtain ⟨Sg, hSgb, -, hSg⟩ := hg.size.exists_polyBound
  exact ⟨polyTimeCleanAt_pair (by omega) hf.time hg.time hSfb hSgb hSf hSg,
    hf.size.pair hg.size⟩

/-- **Pairing, quasipolynomial time.** -/
theorem QuasiPolyFun.pair [Enc α] [Enc β] [Enc γ] {f : α → β} {g : α → γ} (hf : QuasiPolyFun f)
    (hg : QuasiPolyFun g) : QuasiPolyFun (fun a => (f a, g a)) := by
  obtain ⟨Sf, hSfb, -, hSf⟩ := hf.size.exists_polyBound
  obtain ⟨Sg, hSgb, -, hSg⟩ := hg.size.exists_polyBound
  exact ⟨quasiPolyTimeCleanAt_pair (by omega) hf.time hg.time hSfb hSgb hSf hSg,
    hf.size.pair hg.size⟩

/-- **The projections.** -/
theorem polyFun_fst [Enc α] [Enc β] : PolyFun (Prod.fst : α × β → α) :=
  ⟨polyTimeCleanAt_fst (by omega), SizeBound.fst⟩

theorem polyFun_snd [Enc α] [Enc β] : PolyFun (Prod.snd : α × β → β) :=
  ⟨polyTimeCleanAt_snd (by omega), SizeBound.snd⟩

/-- **The conditional.** -/
theorem PolyFun.ite [Enc α] [Enc β] {p : α → Bool} {f g : α → β} (hp : PolyFun p)
    (hf : PolyFun f) (hg : PolyFun g) : PolyFun (fun a => if p a then f a else g a) :=
  ⟨polyTimeCleanAt_ite (by omega) hp.time hf.time hg.time, hf.size.ite' hg.size⟩

/-- **Bounded iteration** `a ↦ step^[k a] a`.  The two hypotheses `hq` (how many rounds) and
`hp` (how large the intermediate states are) cannot be dropped: a single clean step may double
the length of its output, so without `hp` the states, and with them the cost of one step, grow
exponentially along the iteration (`DESIGN.md`, "Doubts" item 3). -/
theorem PolyFun.iterate [Enc α] {step : α → α} {k : α → ℕ} {q p : ℕ → ℕ}
    (hstep : PolyFun (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : PolyFun (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : PolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : PolyBound p) : PolyFun (fun a => step^[k a] a) := by
  refine ⟨polyTimeCleanAt_iterate (by omega) hstep.time hk.time hq hqb hp hpb, ?_⟩
  obtain ⟨c, d, hc⟩ := hpb
  refine ⟨c, d, fun a => ?_⟩
  have h1 : Enc.size ((k a - k a, step^[k a] a) : ℕ × α) ≤ p (Enc.size a) :=
    hp a (k a) (le_refl _)
  have h2 : Enc.size (step^[k a] a) ≤ Enc.size ((k a - k a, step^[k a] a) : ℕ × α) :=
    Combine.size_snd_le _ _
  exact le_trans (le_trans h2 h1) (hc _)

/-- **Bounded iteration, quasipolynomial time.** -/
theorem QuasiPolyFun.iterate [Enc α] {step : α → α} {k : α → ℕ} {q p : ℕ → ℕ}
    (hstep : QuasiPolyFun (fun x : ℕ × α => (x.1 - 1, step x.2)))
    (hk : QuasiPolyFun (fun a => (k a, a)))
    (hq : ∀ a : α, k a ≤ q (Enc.size a)) (hqb : QuasiPolyBound q)
    (hp : ∀ (a : α), ∀ j ≤ k a, Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ p (Enc.size a))
    (hpb : PolyBound p) : QuasiPolyFun (fun a => step^[k a] a) := by
  refine ⟨quasiPolyTimeCleanAt_iterate (by omega) hstep.time hk.time hq hqb hp hpb.quasiPoly, ?_⟩
  obtain ⟨c, d, hc⟩ := hpb
  refine ⟨c, d, fun a => ?_⟩
  have h1 : Enc.size ((k a - k a, step^[k a] a) : ℕ × α) ≤ p (Enc.size a) :=
    hp a (k a) (le_refl _)
  have h2 : Enc.size (step^[k a] a) ≤ Enc.size ((k a - k a, step^[k a] a) : ℕ × α) :=
    Combine.size_snd_le _ _
  exact le_trans (le_trans h2 h1) (hc _)

/-! ## The arithmetic primitives

For an input of *fixed shape* — a natural number, or a pair of natural numbers — the scratch
registers may have fixed indices, so these routines live already at the top-level convention
(`Workspace/Machine/Small.lean`); `polyFun_of_polyTimeClean` lifts them. -/

theorem size_fst_nat (p : ℕ × ℕ) : Nat.size p.1 + 2 ≤ Enc.size p := by
  have h := Combine.size_fst_le p.1 p.2
  rw [Small.size_nat] at h
  simpa using h

theorem size_snd_nat (p : ℕ × ℕ) : Nat.size p.2 + 2 ≤ Enc.size p := by
  have h := Combine.size_snd_le p.1 p.2
  rw [Small.size_nat] at h
  simpa using h

theorem polyFun_add : PolyFun (fun p : ℕ × ℕ => p.1 + p.2) := by
  refine polyFun_of_polyTimeClean Small.polyTimeClean_add (SizeBound.of_nat (fun p => ?_))
  have h1 := size_fst_nat p
  have h2 := size_snd_nat p
  set s := max (Nat.size p.1) (Nat.size p.2) with hs
  have hb1 : p.1 < 2 ^ s := lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb2 : p.2 < 2 ^ s := lt_of_lt_of_le (Nat.lt_size_self _)
    (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have : p.1 + p.2 < 2 ^ (s + 1) := by rw [pow_succ]; omega
  have := Nat.size_le.2 this
  omega

/-- A common shape: a binary operation whose value is at most one of its arguments. -/
theorem sizeBound_binop_le {f : ℕ × ℕ → ℕ} (h : ∀ p : ℕ × ℕ, f p ≤ max p.1 p.2) :
    SizeBound f := by
  refine SizeBound.of_nat (fun p => ?_)
  have h1 := size_fst_nat p
  have h2 := size_snd_nat p
  have h3 : Nat.size (f p) ≤ Nat.size (max p.1 p.2) := Nat.size_le_size (h p)
  have h4 : Nat.size (max p.1 p.2) ≤ max (Nat.size p.1) (Nat.size p.2) := by
    rcases le_total p.1 p.2 with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _
  have h5 : max (Nat.size p.1) (Nat.size p.2) ≤ max (Nat.size p.1 + 2) (Nat.size p.2 + 2) := by
    omega
  omega

theorem polyFun_sub : PolyFun (fun p : ℕ × ℕ => p.1 - p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_sub
    (sizeBound_binop_le (fun _ => le_trans (Nat.sub_le _ _) (le_max_left _ _)))

theorem polyFun_min : PolyFun (fun p : ℕ × ℕ => min p.1 p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_min
    (sizeBound_binop_le (fun _ => le_trans (min_le_left _ _) (le_max_left _ _)))

theorem polyFun_max : PolyFun (fun p : ℕ × ℕ => max p.1 p.2) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_max (sizeBound_binop_le (fun _ => le_refl _))

theorem polyFun_le : PolyFun (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) :=
  polyFun_of_polyTimeClean Small.polyTimeClean_le
    (SizeBound.of_bounded (c := 3) (fun p => by
      by_cases h : p.1 ≤ p.2 <;>
        simp [h, Enc.size, listSize, Enc.encode, Nat.size]))

theorem polyFun_natSize : PolyFun (fun a : ℕ => Nat.size a) := by
  refine polyFun_of_polyTimeClean Small.polyTimeClean_size (SizeBound.of_nat (fun a => ?_))
  have h1 : Nat.size (Nat.size a) ≤ Nat.size a := size_le_self _
  have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
  omega

/-! ## Derived forms

The shapes a procedure of the paper is actually written in: an operation applied to two
functions of the same argument, and the equality test. -/

/-- Membership in the class depends only on the function, so a pointwise identity transfers
it.  This is the step that turns an assembled composite into the function one meant to write. -/
theorem PolyFun.of_eq [Enc α] [Enc β] {f g : α → β} (h : PolyFun f) (hfg : ∀ a, f a = g a) :
    PolyFun g := by
  have : f = g := funext hfg
  exact this ▸ h

theorem QuasiPolyFun.of_eq [Enc α] [Enc β] {f g : α → β} (h : QuasiPolyFun f)
    (hfg : ∀ a, f a = g a) : QuasiPolyFun g := by
  have : f = g := funext hfg
  exact this ▸ h

/-- A binary operation applied to two functions of the same argument. -/
theorem PolyFun.op₂ [Enc α] [Enc β] [Enc γ] [Enc σ] {f : α → β} {g : α → γ} {h : β × γ → σ}
    (hf : PolyFun f) (hg : PolyFun g) (hh : PolyFun h) : PolyFun (fun a => h (f a, g a)) :=
  (hf.pair hg).comp hh

theorem PolyFun.add [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a + g a) := hf.op₂ hg polyFun_add

theorem PolyFun.sub [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => f a - g a) := hf.op₂ hg polyFun_sub

theorem PolyFun.min' [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => min (f a) (g a)) := hf.op₂ hg polyFun_min

theorem PolyFun.max' [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => max (f a) (g a)) := hf.op₂ hg polyFun_max

theorem PolyFun.le [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => decide (f a ≤ g a)) := hf.op₂ hg polyFun_le

/-- Swapping the two components of a pair. -/
theorem polyFun_swap [Enc α] [Enc β] : PolyFun (fun p : α × β => (p.2, p.1)) :=
  polyFun_snd.pair polyFun_fst

theorem polyFun_ge : PolyFun (fun p : ℕ × ℕ => decide (p.2 ≤ p.1)) :=
  polyFun_swap.comp polyFun_le

/-- Equality of naturals: `a = b` is `a ≤ b` and `b ≤ a`. -/
theorem polyFun_natEq : PolyFun (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  refine (PolyFun.ite polyFun_le polyFun_ge (polyFun_const false)).of_eq (fun p => ?_)
  by_cases h : p.1 ≤ p.2
  · simp only [h, decide_true, if_true]
    by_cases h' : p.2 ≤ p.1 <;> simp [h'] <;> omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    symm
    simpa using (by omega : p.1 ≠ p.2)

theorem PolyFun.natEq [Enc α] {f g : α → ℕ} (hf : PolyFun f) (hg : PolyFun g) :
    PolyFun (fun a => decide (f a = g a)) := hf.op₂ hg polyFun_natEq

theorem polyFun_log2 : PolyFun (fun a : ℕ => Nat.log 2 a) := by
  refine polyFun_of_polyTimeClean Small.polyTimeClean_log2 (SizeBound.of_nat (fun a => ?_))
  have h0 : Nat.log 2 a = Nat.size a - 1 := Small.log_two_eq_size_sub_one a
  have h1 : Nat.size (Nat.log 2 a) ≤ Nat.log 2 a := size_le_self _
  have h2 : Enc.size a = Nat.size a + 2 := Small.size_nat a
  omega

end RAM
