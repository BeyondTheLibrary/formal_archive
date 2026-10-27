/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: polynomial-time
routines with explicit constants. Not part of the faithful formalization.
-/
import Workspace.Machine.PolyFun
import Workspace.Machine.Iterate
import Workspace.Machine.Pairing
import Workspace.Machine.Reloc
import Workspace.Machine.Const

/-!
# Routines with an explicit polynomial time

`RAM.PolyFun f` states its polynomial with `∃`. Here `Explicit.PF f k d s e` states that `f`
is a clean routine at the workspace convention (`K = 16`) with time at most `2^k (N+1)^d` and
outputs of size at most `2^s (N+1)^e`, for inputs of size `N`. These are the shapes of the
fields `kP dP` of `Explicit.StepBounds` (with `k = s`, `d = e`).

Time and size have separate constants because a composition multiplies the time degree of the
second routine by the size degree of the first; most routines have linear size (`e = 1`), and
then degrees add up only through `max`.

The rules mirror those of `RAM.PolyFun` (`Workspace/Machine/PolyFun.lean`) and use the same
machine lemmas, which already have explicit step counts:

* `Explicit.PF.comp`, `Explicit.PF.pair`, `Explicit.PF.fst`, `Explicit.PF.snd`,
  `Explicit.PF.id`, `Explicit.PF.const`;
* `Explicit.PF.ite`: from the conditional on a pair (`RAM.Combine.cleanComputeAt_iteOfPair`);
* `Explicit.PF.iterate`: bounded iteration (`RAM.cleanComputeAt_recursion`).

The constants of a rule are closed expressions (sums, products and `max`) in those of its parts.
A lemma about a fixed routine states them as numerals, which the kernel checks by evaluation.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*} [Enc α] [Enc β] [Enc γ] [Enc σ]

/-! ## Arithmetic of `2^k (N+1)^d` -/

theorem pw_mono {k k' d d' N : ℕ} (hk : k ≤ k') (hd : d ≤ d') :
    2 ^ k * (N + 1) ^ d ≤ 2 ^ k' * (N + 1) ^ d' :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk)
    (Nat.pow_le_pow_right (by omega) hd)

theorem one_le_pw (k d N : ℕ) : 1 ≤ 2 ^ k * (N + 1) ^ d :=
  Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.one_le_pow _ _ (by omega))

theorem pw_add_le {x y k d N : ℕ} (hx : x ≤ 2 ^ k * (N + 1) ^ d)
    (hy : y ≤ 2 ^ k * (N + 1) ^ d) : x + y ≤ 2 ^ (k + 1) * (N + 1) ^ d := by
  rw [pow_succ]
  have : 2 ^ k * 2 * (N + 1) ^ d = 2 ^ k * (N + 1) ^ d + 2 ^ k * (N + 1) ^ d := by ring
  omega

/-- `c · 2^k (N+1)^d ≤ 2^{k+j} (N+1)^d` for `c ≤ 2^j`. -/
theorem const_mul_pw_le {c j k d N : ℕ} (hc : c ≤ 2 ^ j) :
    c * (2 ^ k * (N + 1) ^ d) ≤ 2 ^ (k + j) * (N + 1) ^ d := by
  rw [pow_add]
  calc c * (2 ^ k * (N + 1) ^ d) ≤ 2 ^ j * (2 ^ k * (N + 1) ^ d) := Nat.mul_le_mul_right _ hc
    _ = 2 ^ k * 2 ^ j * (N + 1) ^ d := by ring

theorem self_le_pw (N : ℕ) : N ≤ 2 ^ 0 * (N + 1) ^ 1 := by simp

/-- **A polynomial of a polynomial**: `2^{k'} (2^k (N+1)^d + 1)^{d'} ≤ 2^{k' + (k+1) d'} (N+1)^{d d'}`. -/
theorem pw_comp_le (k d k' d' N : ℕ) :
    2 ^ k' * (2 ^ k * (N + 1) ^ d + 1) ^ d' ≤ 2 ^ (k' + (k + 1) * d') * (N + 1) ^ (d * d') := by
  have h1 : 2 ^ k * (N + 1) ^ d + 1 ≤ 2 ^ (k + 1) * (N + 1) ^ d := by
    have := one_le_pw k d N
    rw [pow_succ]
    have e : 2 ^ k * 2 * (N + 1) ^ d = 2 ^ k * (N + 1) ^ d + 2 ^ k * (N + 1) ^ d := by ring
    omega
  calc 2 ^ k' * (2 ^ k * (N + 1) ^ d + 1) ^ d'
      ≤ 2 ^ k' * (2 ^ (k + 1) * (N + 1) ^ d) ^ d' :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = 2 ^ (k' + (k + 1) * d') * (N + 1) ^ (d * d') := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring

/-- `a ≤ 2^k (N+1)^d` and `N ≤ N'` give `a ≤ 2^k (N'+1)^d`. -/
theorem pw_le_of_le {k d N N' : ℕ} (h : N ≤ N') : 2 ^ k * (N + 1) ^ d ≤ 2 ^ k * (N' + 1) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-! ## The class -/

/-- **Explicit polynomial time**: a clean routine at the workspace convention with time
`2^k (N+1)^d`, whose outputs have size at most `2^s (N+1)^e`. -/
structure PF (f : α → β) (k d s e : ℕ) : Prop where
  time : ∃ P, CleanComputeAt 16 P f (fun N => 2 ^ k * (N + 1) ^ d)
  size : ∀ a, Enc.size (f a) ≤ 2 ^ s * (Enc.size a + 1) ^ e

namespace PF

theorem mono {f : α → β} {k d s e k' d' s' e' : ℕ} (h : PF f k d s e) (hk : k ≤ k')
    (hd : d ≤ d') (hs : s ≤ s') (he : e ≤ e') : PF f k' d' s' e' := by
  obtain ⟨⟨P, hP⟩, hsz⟩ := h
  exact ⟨⟨P, hP.mono fun N => pw_mono hk hd⟩, fun a => (hsz a).trans (pw_mono hs he)⟩

theorem of_eq {f g : α → β} {k d s e : ℕ} (h : PF f k d s e) (eq : ∀ a, f a = g a) :
    PF g k d s e := by
  have : f = g := funext eq
  exact this ▸ h

/-- An explicit routine is a `RAM.PolyFun`. -/
theorem polyFun {f : α → β} {k d s e : ℕ} (h : PF f k d s e) : PolyFun f := by
  obtain ⟨⟨P, hP⟩, hsz⟩ := h
  exact ⟨⟨P, _, ⟨2 ^ k, d, fun _ => le_rfl⟩, hP⟩, ⟨2 ^ s, e, hsz⟩⟩

/-- **Composition** (`f` first). -/
theorem comp {f : α → β} {g : β → γ} {k d s e k' d' s' e' : ℕ} (hf : PF f k d s e)
    (hg : PF g k' d' s' e') :
    PF (fun a => g (f a)) (max k (k' + (s + 1) * d') + 1) (max d (e * d'))
      (s' + (s + 1) * e') (e * e') := by
  obtain ⟨⟨P, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQ⟩, hsg⟩ := hg
  refine ⟨⟨seq P Q, (CleanComputeAt.comp hP hQ (fun n n' h => pw_le_of_le h)
    (S := fun N => 2 ^ s * (N + 1) ^ e) hsf).mono fun N => ?_⟩, fun a => ?_⟩
  · exact pw_add_le (pw_mono (by omega) (by omega))
      ((pw_comp_le s e k' d' N).trans (pw_mono (by omega) (by omega)))
  · refine (hsg (f a)).trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by have := hsf a; omega) _)).trans (pw_comp_le s e s' e' _))

/-- **Pairing.** -/
theorem pair {f : α → β} {g : α → γ} {k d s e k' d' s' e' : ℕ} (hf : PF f k d s e)
    (hg : PF g k' d' s' e') :
    PF (fun a => (f a, g a)) (max (max k k') (max s s') + 9) (max (max d d') (max (max e e') 1))
      (max s s' + 2) (max e e') := by
  obtain ⟨⟨P, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQ⟩, hsg⟩ := hg
  set A := max (max k k') (max s s') with hA
  set B := max (max d d') (max (max e e') 1) with hB
  refine ⟨⟨Pairing.pairProg 16 P Q, (Pairing.cleanComputeAt_pair (K := 16) (by norm_num) hP hQ
    (Sf := fun N => 2 ^ s * (N + 1) ^ e) (Sg := fun N => 2 ^ s' * (N + 1) ^ e') hsf hsg).mono
    fun N => ?_⟩, fun a => ?_⟩
  · have hN : N ≤ 2 ^ A * (N + 1) ^ B :=
      (self_le_pw N).trans (pw_mono (by omega) (by omega))
    have h1 := one_le_pw A B N
    have h2 : 2 ^ k * (N + 1) ^ d ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have h3 : 2 ^ k' * (N + 1) ^ d' ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have h4 : 2 ^ s * (N + 1) ^ e ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have h5 : 2 ^ s' * (N + 1) ^ e' ≤ 2 ^ A * (N + 1) ^ B := pw_mono (by omega) (by omega)
    have c := const_mul_pw_le (c := 512) (j := 9) (k := A) (d := B) (N := N) (by norm_num)
    omega
  · have h := Combine.size_pair_le (f a) (g a)
    have h2 : Enc.size (f a) ≤ 2 ^ max s s' * (Enc.size a + 1) ^ max e e' :=
      (hsf a).trans (pw_mono (by omega) (by omega))
    have h3 : Enc.size (g a) ≤ 2 ^ max s s' * (Enc.size a + 1) ^ max e e' :=
      (hsg a).trans (pw_mono (by omega) (by omega))
    have c := const_mul_pw_le (c := 4) (j := 2) (k := max s s') (d := max e e')
      (N := Enc.size a) (by norm_num)
    omega

theorem fst : PF (Prod.fst : α × β → α) 7 1 0 1 :=
  ⟨⟨_, (Combine.cleanComputeAt_fst (K := 16) (by norm_num)).mono fun N => by
    norm_num; omega⟩, fun ⟨x, y⟩ => by have := Combine.size_fst_le x y; norm_num; omega⟩

theorem snd : PF (Prod.snd : α × β → β) 7 1 0 1 :=
  ⟨⟨_, (Combine.cleanComputeAt_snd (K := 16) (by norm_num)).mono fun N => by
    norm_num; omega⟩, fun ⟨x, y⟩ => by have := Combine.size_snd_le x y; norm_num; omega⟩

theorem id : PF (fun a : α => a) 0 0 0 1 :=
  ⟨⟨[], (cleanComputeAt_id 16).mono fun N => by simp⟩, fun a => by simp⟩

/-- **A routine of the top-level convention**, at ten times its cost plus four steps
(`RAM.cleanComputeAt_of_cleanCompute`). -/
theorem ofClean {f : α → β} {P : Program} {T : ℕ → ℕ} {k d s e : ℕ} (h : CleanCompute P f T)
    (hT : ∀ N, 10 * T N + 4 ≤ 2 ^ k * (N + 1) ^ d)
    (hs : ∀ a, Enc.size (f a) ≤ 2 ^ s * (Enc.size a + 1) ^ e) : PF f k d s e :=
  ⟨⟨_, (cleanComputeAt_of_cleanCompute (K := 16) (by decide) h).mono hT⟩, hs⟩

/-- **A constant** of size `S`. -/
theorem const (x : β) : PF (fun _ : α => x) (Enc.size x + 7) 1 (Enc.size x) 0 := by
  refine ofClean (cleanCompute_const (α := α) x) (fun N => ?_) (fun a => ?_)
  · have hl : (Enc.encode x).length < Enc.size x := length_lt_listSize _
    have h1 : Enc.size x + 1 ≤ 2 ^ Enc.size x := Nat.lt_two_pow_self
    show 10 * (5 * N + (10 + ((Enc.encode x).length + 1))) + 4 ≤
      2 ^ (Enc.size x + 7) * (N + 1) ^ 1
    rw [pow_add, pow_one]
    have e : 2 ^ Enc.size x * 2 ^ 7 * (N + 1) = 128 * (2 ^ Enc.size x * (N + 1)) := by ring
    rw [e]
    have h2 : Enc.size x + 1 ≤ 2 ^ Enc.size x * (N + 1) :=
      h1.trans (Nat.le_mul_of_pos_right _ (by omega))
    have h3 : N + 1 ≤ 2 ^ Enc.size x * (N + 1) :=
      Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
    omega
  · have h1 : Enc.size x < 2 ^ Enc.size x := Nat.lt_two_pow_self
    simp only [pow_zero, mul_one]
    exact h1.le

/-! ## The conditional -/

/-- **The conditional on a pair** `(b, x) ↦ if b then f x else g x`. -/
theorem iteOfPair {f g : α → β} {k d s e k' d' s' e' : ℕ} (hf : PF f k d s e)
    (hg : PF g k' d' s' e') :
    PF (fun q : Bool × α => if q.1 then f q.2 else g q.2) (max k k' + 8) (max (max d d') 1)
      (max s s') (max e e') := by
  obtain ⟨⟨P, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQ⟩, hsg⟩ := hg
  refine ⟨⟨_, (Combine.cleanComputeAt_iteOfPair (K := 16) (by norm_num) hP hQ
    (fun n n' h => pw_le_of_le h) (fun n n' h => pw_le_of_le h)).mono fun N => ?_⟩,
    fun q => ?_⟩
  · have hN : N ≤ 2 ^ max k k' * (N + 1) ^ max (max d d') 1 :=
      (self_le_pw N).trans (pw_mono (by omega) (by omega))
    have h1 := one_le_pw (max k k') (max (max d d') 1) N
    have h2 : 2 ^ k * (N + 1) ^ d ≤ 2 ^ max k k' * (N + 1) ^ max (max d d') 1 :=
      pw_mono (by omega) (by omega)
    have h3 : 2 ^ k' * (N + 1) ^ d' ≤ 2 ^ max k k' * (N + 1) ^ max (max d d') 1 :=
      pw_mono (by omega) (by omega)
    have c := const_mul_pw_le (c := 256) (j := 8) (k := max k k') (d := max (max d d') 1)
      (N := N) (by norm_num)
    omega
  · obtain ⟨b, x⟩ := q
    have hx : Enc.size x ≤ Enc.size ((b, x) : Bool × α) := Combine.size_snd_le b x
    have h2 : Enc.size (f x) ≤ 2 ^ max s s' * (Enc.size ((b, x) : Bool × α) + 1) ^ max e e' :=
      (hsf x).trans ((pw_le_of_le hx).trans (pw_mono (by omega) (by omega)))
    have h3 : Enc.size (g x) ≤ 2 ^ max s s' * (Enc.size ((b, x) : Bool × α) + 1) ^ max e e' :=
      (hsg x).trans ((pw_le_of_le hx).trans (pw_mono (by omega) (by omega)))
    cases b
    · exact h3
    · exact h2

/-- **The conditional**: the pair `(p a, a)`, then the conditional on a pair. -/
theorem ite {p : α → Bool} {f g : α → β} {kp dp sp ep k d s e k' d' s' e' : ℕ}
    (hp : PF p kp dp sp ep) (hf : PF f k d s e) (hg : PF g k' d' s' e') :
    PF (fun a => if p a then f a else g a)
      (max (max (max kp 0) (max sp 0) + 9) (max k k' + 8 + (max sp 0 + 2 + 1) *
        max (max d d') 1) + 1)
      (max (max (max dp 0) (max (max ep 1) 1)) (max ep 1 * max (max d d') 1))
      (max s s' + (max sp 0 + 2 + 1) * max e e') (max ep 1 * max e e') :=
  (hp.pair PF.id).comp (iteOfPair hf hg)

/-! ## Bounded iteration -/

/-- **Bounded iteration** `a ↦ step^[k a] a`, as `RAM.PolyFun.iterate` with explicit bounds:
the set-up `a ↦ (k a, a)` has time `2^{kk} (N+1)^{dk}`, one round has time `2^{ks} (N+1)^{ds}`,
the number of rounds is at most `2^{kq} (N+1)^{dq}` and every intermediate pair has size at
most `2^{kp} (N+1)^{dp}`. -/
theorem iterate {step : α → α} {k : α → ℕ} {kk dk sk ek ks ds ss es kq dq kp dp : ℕ}
    (hstep : PF (fun x : ℕ × α => (x.1 - 1, step x.2)) ks ds ss es)
    (hk : PF (fun a => (k a, a)) kk dk sk ek)
    (hq : ∀ a : α, k a ≤ 2 ^ kq * (Enc.size a + 1) ^ dq)
    (hp : ∀ (a : α), ∀ j ≤ k a,
      Enc.size ((k a - j, step^[j] a) : ℕ × α) ≤ 2 ^ kp * (Enc.size a + 1) ^ dp) :
    PF (fun a => step^[k a] a) (max (max kk (kq + ks + (kp + 1) * ds + 3)) (kp + 7) + 2)
      (max (max dk (dq + dp * ds)) dp) kp dp := by
  obtain ⟨⟨P₁, hP₁⟩, -⟩ := hk
  obtain ⟨⟨Q, hQ⟩, -⟩ := hstep
  set E := max (max kk (kq + ks + (kp + 1) * ds + 3)) (kp + 7) with hE
  set D := max (max dk (dq + dp * ds)) dp with hD
  have hX : ∀ N, 2 ^ ks * (2 ^ kp * (N + 1) ^ dp + 1) ^ ds ≤
      2 ^ (ks + (kp + 1) * ds) * (N + 1) ^ (dp * ds) := fun N => pw_comp_le kp dp ks ds N
  refine ⟨⟨_, (cleanComputeAt_recursion (setUp := fun a => (k a, a)) (step := step)
    (readOff := fun a : α => a) (T₂ := fun N => 2 ^ ks * (N + 1) ^ ds)
    (p := fun N => 2 ^ ks * (2 ^ kp * (N + 1) ^ dp + 1) ^ ds)
    (q := fun N => 2 ^ kq * (N + 1) ^ dq) (u := fun N => 24 * (2 ^ kp * (N + 1) ^ dp) + 16 + 80)
    hP₁ hQ (Combine.cleanComputeAt_snd (K := 16) (by norm_num)) hq
    (fun a j hj => pw_le_of_le (hp a j hj.le)) (fun a => ?_)).mono fun N => ?_⟩, fun a => ?_⟩
  · have h := hp a (k a) le_rfl
    rw [Nat.sub_self] at h
    show 24 * Enc.size ((0, step^[k a] a) : ℕ × α) + 16 + 80 ≤
      24 * (2 ^ kp * (Enc.size a + 1) ^ dp) + 16 + 80
    omega
  · -- the three terms, each at most `2^E (N+1)^D`
    have t1 : 2 ^ kk * (N + 1) ^ dk ≤ 2 ^ E * (N + 1) ^ D := pw_mono (by omega) (by omega)
    have hA := one_le_pw kp dp N
    have hXN := hX N
    have hX1 := one_le_pw (ks + (kp + 1) * ds) (dp * ds) N
    set X := 2 ^ ks * (2 ^ kp * (N + 1) ^ dp + 1) ^ ds with hXd
    set Y := 2 ^ (ks + (kp + 1) * ds) * (N + 1) ^ (dp * ds) with hY
    have hQ2 : 2 ^ kq * (N + 1) ^ dq * (X + 2) + 1 ≤ 2 ^ E * (N + 1) ^ D := by
      have a1 : X + 2 ≤ 4 * Y := by omega
      have a2 : 2 ^ kq * (N + 1) ^ dq * (4 * Y) =
          2 ^ (kq + ks + (kp + 1) * ds + 2) * (N + 1) ^ (dq + dp * ds) := by
        rw [hY]; simp only [pow_add]; ring
      have a3 : 2 ^ (kq + ks + (kp + 1) * ds + 2) * (N + 1) ^ (dq + dp * ds) + 1 ≤
          2 ^ (kq + ks + (kp + 1) * ds + 3) * (N + 1) ^ (dq + dp * ds) := by
        have := one_le_pw (kq + ks + (kp + 1) * ds + 2) (dq + dp * ds) N
        rw [pow_succ 2 (kq + ks + (kp + 1) * ds + 2)]
        have e : 2 ^ (kq + ks + (kp + 1) * ds + 2) * 2 * (N + 1) ^ (dq + dp * ds) =
            2 ^ (kq + ks + (kp + 1) * ds + 2) * (N + 1) ^ (dq + dp * ds) +
            2 ^ (kq + ks + (kp + 1) * ds + 2) * (N + 1) ^ (dq + dp * ds) := by ring
        omega
      have a4 := Nat.mul_le_mul_left (2 ^ kq * (N + 1) ^ dq) a1
      exact le_trans (by omega) (a3.trans (pw_mono (by omega) (by omega)))
    have hU : 24 * (2 ^ kp * (N + 1) ^ dp) + 16 + 80 ≤ 2 ^ E * (N + 1) ^ D := by
      have e := const_mul_pw_le (c := 128) (j := 7) (k := kp) (d := dp) (N := N) (by norm_num)
      exact le_trans (by omega) (e.trans (pw_mono (by omega) (by omega)))
    have e3 := const_mul_pw_le (c := 4) (j := 2) (k := E) (d := D) (N := N) (by norm_num)
    omega
  · have h := hp a (k a) le_rfl
    have h2 : Enc.size (step^[k a] a) ≤ Enc.size ((k a - k a, step^[k a] a) : ℕ × α) :=
      Combine.size_snd_le _ _
    exact h2.trans h

end PF

end Explicit
