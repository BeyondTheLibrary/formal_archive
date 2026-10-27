/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): routines whose time is
bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeMachine

/-!
# Routines bounded at an external degree

`Explicit.TN f Pre k`: one well-formed clean program computes `f`, and on every input `a` with
`Pre n a` it halts within `2^{A (log₂ n + 2)^k}·(size a + 1)^b` steps, with output of at most
that size, for constants `A`, `b`. The degree `n` is not read off the input: it is the degree
of the run the input belongs to (for a step of the evaluator, the degree of the root). This is
the form of `Explicit.StepBounds.step`. Only the exponent `k` is explicit.

The closure rules are those of `Explicit.TS` (`Workspace/Explicit/NodeMachine.lean`), with the
degree function replaced by the external degree.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*}

/-- **Bounded at an external degree, with explicit constants.** -/
structure TNB [Enc α] [Enc β] (f : α → β) (Pre : ℕ → α → Prop) (A k b : ℕ) : Prop where
  time : ∃ P, Wf P ∧ ∀ n a, Pre n a → RunsTo P (fun m => m = initMemAt 16 (Enc.encode a))
    (fun m' => m' = initMemAt 16 (Enc.encode (f a))) (tsB A k b n (Enc.size a))
  size : ∀ n a, Pre n a → Enc.size (f a) ≤ tsB A k b n (Enc.size a)

/-- **Bounded at an external degree**, with exponent `k`. -/
def TN [Enc α] [Enc β] (f : α → β) (Pre : ℕ → α → Prop) (k : ℕ) : Prop :=
  ∃ A b, TNB f Pre A k b

namespace TNB

variable [Enc α] [Enc β] [Enc γ] [Enc σ]

theorem mono {f : α → β} {Pre Pre' : ℕ → α → Prop} {A A' k k' b b' : ℕ} (h : TNB f Pre A k b)
    (hPre : ∀ n a, Pre' n a → Pre n a) (hA : A ≤ A') (hk : k ≤ k') (hb : b ≤ b') :
    TNB f Pre' A' k' b' := by
  obtain ⟨⟨P, hw, hP⟩, hs⟩ := h
  exact ⟨⟨P, hw, fun n a ha => (hP n a (hPre n a ha)).mono
      (tsB_mono hA hk hb le_rfl le_rfl)⟩,
    fun n a ha => (hs n a (hPre n a ha)).trans (tsB_mono hA hk hb le_rfl le_rfl)⟩

/-- A polynomial change of the degree. -/
theorem scale {f : α → β} {Pre : ℕ → α → Prop} {Pre' : ℕ → α → Prop} {A k b r₀ r : ℕ}
    (h : TNB f Pre A k b)
    (hPre : ∀ n a, Pre' n a → ∃ n', n' ≤ 2 ^ r₀ * (n + 1) ^ r ∧ Pre n' a) :
    TNB f Pre' (A * (r₀ + 2 * r + 3) ^ k) k b := by
  obtain ⟨⟨P, hw, hP⟩, hs⟩ := h
  refine ⟨⟨P, hw, fun n a ha => ?_⟩, fun n a ha => ?_⟩
  · obtain ⟨n', hn', ha'⟩ := hPre n a ha
    exact (hP n' a ha').mono (tsB_le_of_poly hn')
  · obtain ⟨n', hn', ha'⟩ := hPre n a ha
    exact (hs n' a ha').trans (tsB_le_of_poly hn')

end TNB

namespace TN

variable [Enc α] [Enc β] [Enc γ] [Enc σ]

theorem of_eq {f g : α → β} {Pre : ℕ → α → Prop} {k : ℕ} (h : TN f Pre k)
    (hfg : ∀ a, f a = g a) : TN g Pre k := by
  have : f = g := funext hfg
  exact this ▸ h

/-- Equality only on the inputs that meet the precondition. -/
theorem of_eq_on {f g : α → β} {Pre : ℕ → α → Prop} {k : ℕ} (h : TN f Pre k)
    (hfg : ∀ n a, Pre n a → f a = g a) : TN g Pre k := by
  obtain ⟨A, b, ⟨P, hw, hP⟩, hs⟩ := h
  exact ⟨A, b, ⟨P, hw, fun n a ha => hfg n a ha ▸ hP n a ha⟩,
    fun n a ha => hfg n a ha ▸ hs n a ha⟩

theorem restrict {f : α → β} {Pre Pre' : ℕ → α → Prop} {k : ℕ} (h : TN f Pre k)
    (hPre : ∀ n a, Pre' n a → Pre n a) : TN f Pre' k := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨A, b, h.mono hPre le_rfl le_rfl le_rfl⟩

theorem mono_k {f : α → β} {Pre : ℕ → α → Prop} {k k' : ℕ} (h : TN f Pre k) (hk : k ≤ k') :
    TN f Pre k' := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨A, b, h.mono (fun _ _ h => h) le_rfl hk le_rfl⟩

/-- A polynomial change of the degree. -/
theorem scale {f : α → β} {Pre Pre' : ℕ → α → Prop} {k : ℕ} (h : TN f Pre k) (r₀ r : ℕ)
    (hPre : ∀ n a, Pre' n a → ∃ n', n' ≤ 2 ^ r₀ * (n + 1) ^ r ∧ Pre n' a) : TN f Pre' k := by
  obtain ⟨A, b, h⟩ := h
  exact ⟨_, _, h.scale hPre⟩

/-- **Every `RAM.PolyFun` is bounded at every degree**, with every precondition. -/
theorem ofPoly {f : α → β} (h : PolyFun f) (Pre : ℕ → α → Prop) (k : ℕ) : TN f Pre k := by
  obtain ⟨A, b, hTS⟩ := TS.ofPoly h
  obtain ⟨⟨P, hw, hP⟩, hs⟩ := hTS (fun _ : α => True) (fun _ : α => 0) 0
  refine ⟨A, b, ⟨P, hw, fun n a _ => (hP a trivial).mono ?_⟩, fun n a _ => (hs a trivial).trans ?_⟩
  · exact (tsB_zero_k A b 0 n _).le.trans (tsB_mono le_rfl (Nat.zero_le k) le_rfl le_rfl le_rfl)
  · exact (tsB_zero_k A b 0 n _).le.trans (tsB_mono le_rfl (Nat.zero_le k) le_rfl le_rfl le_rfl)

/-- **Composition.** -/
theorem comp {f : α → β} {g : β → γ} {Pre : ℕ → α → Prop} {Pre' : ℕ → β → Prop} {k : ℕ}
    (hf : TN f Pre k) (hg : TN g Pre' k) (hPre : ∀ n a, Pre n a → Pre' n (f a)) :
    TN (fun a => g (f a)) Pre k := by
  obtain ⟨A, b, ⟨P, hPw, hP⟩, hsf⟩ := hf
  obtain ⟨A', b', ⟨Q, hQw, hQ⟩, hsg⟩ := hg
  have key : ∀ n a, Pre n a → tsB A' k b' n (Enc.size (f a))
      ≤ tsB (A' + b' * (A + 1)) k (b * b') n (Enc.size a) := fun n a ha =>
    (tsB_mono le_rfl le_rfl le_rfl le_rfl (hsf n a ha)).trans (tsB_comp_le A A' k b b' n _)
  refine ⟨A + (A' + b' * (A + 1)) + 2, b + b * b', ⟨seq P Q, wf_seq hPw hQw, fun n a ha =>
    ((hP n a ha).seq (hQ n (f a) (hPre n a ha))).mono ?_⟩, fun n a ha => ?_⟩
  · exact (Nat.add_le_add_left (key n a ha) _).trans (tsB_add_le _ _ _ _ _ _ _)
  · exact (hsg n (f a) (hPre n a ha)).trans ((key n a ha).trans ((Nat.le_add_left _ _).trans
      (tsB_add_le _ _ _ _ _ _ _)))

/-- Composition with a polynomial routine after. -/
theorem comp_poly {f : α → β} {g : β → γ} {Pre : ℕ → α → Prop} {k : ℕ} (hf : TN f Pre k)
    (hg : PolyFun g) : TN (fun a => g (f a)) Pre k :=
  hf.comp (ofPoly hg (fun _ _ => True) k) (fun _ _ _ => trivial)

/-- Composition with a polynomial routine before. -/
theorem poly_comp {f : α → β} {g : β → γ} {Pre : ℕ → β → Prop} {k : ℕ} (hf : PolyFun f)
    (hg : TN g Pre k) : TN (fun a => g (f a)) (fun n a => Pre n (f a)) k :=
  (ofPoly hf _ k).comp hg (fun _ _ h => h)

set_option maxRecDepth 10000 in
/-- **Pairing.** -/
theorem pair {f : α → β} {g : α → γ} {Pre : ℕ → α → Prop} {k : ℕ}
    (hf : TN f Pre k) (hg : TN g Pre k) : TN (fun a => (f a, g a)) Pre k := by
  obtain ⟨A, b, ⟨P, hPw, hP⟩, hsf⟩ := hf
  obtain ⟨A', b', ⟨Q, hQw, hQ⟩, hsg⟩ := hg
  have hM : ∀ (n : ℕ) (a : α), Enc.size a ≤ tsB (A + A') k (b + b' + 1) n (Enc.size a) ∧
      tsB A k b n (Enc.size a) ≤ tsB (A + A') k (b + b' + 1) n (Enc.size a) ∧
      tsB A' k b' n (Enc.size a) ≤ tsB (A + A') k (b + b' + 1) n (Enc.size a) ∧
      1 ≤ tsB (A + A') k (b + b' + 1) n (Enc.size a) := fun n a =>
    ⟨(self_le_tsB k n _).trans (tsB_mono (Nat.zero_le _) le_rfl (by omega) le_rfl le_rfl),
      tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl,
      tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl, one_le_tsB _ _ _ _ _⟩
  refine ⟨A + A' + 453, b + b' + 1, ⟨Pairing.pairProg 16 P Q, Pairing.wf_pairProg 16 hPw hQw,
    fun n a ha => ?_⟩, fun n a ha => ?_⟩
  · have hpair : Enc.encode (f a, g a)
        = ((Enc.encode (f a)).length :: Enc.encode (f a)) ++
          ((Enc.encode (g a)).length :: Enc.encode (g a)) := rfl
    have h := Pairing.runsTo_pairProg (K := 16) (E := Enc.encode a) (F := Enc.encode (f a))
      (G := Enc.encode (g a)) (by omega) (hP n a ha) (hQ n a ha)
    rw [← hpair] at h
    refine h.mono ?_
    have hE : (Enc.encode a).length ≤ Enc.size a := le_of_lt (length_lt_listSize _)
    have hF : (Enc.encode (f a)).length ≤ Enc.size (f a) := le_of_lt (length_lt_listSize _)
    have hG : (Enc.encode (g a)).length ≤ Enc.size (g a) := le_of_lt (length_lt_listSize _)
    obtain ⟨h1, h2, h3, h4⟩ := hM n a
    have h5 := hsf n a ha
    have h6 := hsg n a ha
    have h7 := mul_tsB_le 453 (A + A') k (b + b' + 1) n (Enc.size a)
    omega
  · have h := Combine.size_pair_le (f a) (g a)
    obtain ⟨h1, h2, h3, h4⟩ := hM n a
    have h5 := hsf n a ha
    have h6 := hsg n a ha
    have h7 := mul_tsB_le 453 (A + A') k (b + b' + 1) n (Enc.size a)
    omega

/-- **Case analysis on an `Option`** carried alongside a state. -/
theorem optionElim {g : σ → γ} {h : β × σ → γ} {Preg : ℕ → σ → Prop}
    {Preh : ℕ → β × σ → Prop} {Pre : ℕ → Option β × σ → Prop} {k : ℕ}
    (hg : TN g Preg k) (hh : TN h Preh k)
    (hPg : ∀ n s, Pre n (none, s) → Preg n s) (hPh : ∀ n x s, Pre n (some x, s) → Preh n (x, s)) :
    TN (fun p : Option β × σ => p.1.elim (g p.2) (fun x => h (x, p.2))) Pre k := by
  obtain ⟨A₁, b₁, hg⟩ := hg
  obtain ⟨A₂, b₂, hh⟩ := hh
  obtain ⟨⟨P, hPw, hP⟩, hsg⟩ := hg.mono (fun _ _ h => h) (Nat.le_add_right A₁ A₂) le_rfl
    (Nat.le_add_right b₁ b₂)
  obtain ⟨⟨Q, hQw, hQ⟩, hsh⟩ := hh.mono (fun _ _ h => h) (Nat.le_add_left A₂ A₁) le_rfl
    (Nat.le_add_left b₂ b₁)
  set A := A₁ + A₂
  set b := b₁ + b₂
  have hbound : ∀ n (p : Option β × σ), Pre n p →
      p.1.elim (tsB A k b n (Enc.size p.2))
        (fun x => tsB A k b n (Enc.size ((x, p.2) : β × σ)))
        ≤ tsB A k b n (Enc.size p) := by
    rintro n ⟨o, s⟩ hp
    cases o with
    | none => exact tsB_mono le_rfl le_rfl le_rfl le_rfl (Combine.size_snd_le _ _)
    | some x => exact tsB_mono le_rfl le_rfl le_rfl le_rfl (size_strip_le x s)
  refine ⟨A + 262, b + 1, ⟨Lists.optElimProg 16 P Q, Lists.wf_optElimProg le_rfl hPw hQw,
    fun n p hp => ?_⟩, fun n p hp => ?_⟩
  · have hpw := pw_optionElim (Pre := Pre n) (Preg := Preg n) (Preh := Preh n)
      (τg := fun s => tsB A k b n (Enc.size s))
      (τh := fun s => tsB A k b n (Enc.size s))
      ⟨hPw, fun s hs => hP n s hs⟩ ⟨hQw, fun s hs => hQ n s hs⟩ (hPg n) (hPh n)
    refine (hpw.2 p hp).mono ?_
    have h1 := hbound n p hp
    have h2 := self_le_tsB k n (Enc.size p)
    have h3 : tsB 0 k 1 n (Enc.size p) ≤ tsB A k (b + 1) n (Enc.size p) :=
      tsB_mono (Nat.zero_le _) le_rfl (by omega) le_rfl le_rfl
    have h4 : tsB A k b n (Enc.size p) ≤ tsB A k (b + 1) n (Enc.size p) :=
      tsB_mono le_rfl le_rfl (by omega) le_rfl le_rfl
    have h5 := one_le_tsB A k (b + 1) n (Enc.size p)
    have h6 := mul_tsB_le 262 A k (b + 1) n (Enc.size p)
    obtain ⟨o, s⟩ := p
    cases o <;> (simp only [Option.elim] at h1 ⊢; omega)
  · refine le_trans ?_ ((hbound n p hp).trans
      (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl))
    obtain ⟨o, s⟩ := p
    cases o with
    | none => exact hsg n s (hPg n s hp)
    | some x => exact hsh n (x, s) (hPh n x s hp)

/-- **The conditional**: a polynomial test, two bounded branches. Each branch needs its
precondition only where it is taken. -/
theorem ite {p : α → Bool} {f g : α → β} {Pre Pref Preg : ℕ → α → Prop} {k : ℕ}
    (hp : PolyFun p) (hf : TN f Pref k) (hg : TN g Preg k)
    (hPf : ∀ n a, Pre n a → p a = true → Pref n a)
    (hPg : ∀ n a, Pre n a → p a = false → Preg n a) :
    TN (fun a => if p a then f a else g a) Pre k := by
  have h₁ := ofPoly ((PolyFun.ite hp (polyFun_const none) polyFun_some).pair
    (polyFun_id (α := α))) Pre k
  have hg' : TN (fun q : α × α => g q.2) (fun n q => Preg n q.2) k :=
    (ofPoly polyFun_snd _ k).comp hg (fun _ _ h => h)
  have h₃ := optionElim (Pre := fun (n : ℕ) (q : Option α × α) =>
      (q.1 = none → Pref n q.2) ∧ ∀ x, q.1 = some x → Preg n (x, q.2).2)
    hf hg' (fun n s h => h.1 rfl) (fun n x s h => h.2 x rfl)
  refine (h₁.comp h₃ (fun n a ha => ?_)).of_eq (fun a => ?_)
  · constructor
    · intro h
      cases hpa : p a with
      | true => exact hPf n a ha hpa
      | false => simp [hpa] at h
    · intro x hx
      cases hpa : p a with
      | true => simp [hpa] at hx
      | false =>
        simp only [hpa] at hx
        simp at hx
        subst hx
        exact hPg n a ha hpa
  · by_cases h : p a <;> simp [h]

/-- **Case analysis on a list** carried alongside a state. -/
theorem listCases {g : σ → γ} {h : (α × List α) × σ → γ} {Preg : ℕ → σ → Prop}
    {Preh : ℕ → (α × List α) × σ → Prop} {Pre : ℕ → List α × σ → Prop} {k : ℕ}
    (hg : TN g Preg k) (hh : TN h Preh k) (hPg : ∀ n s, Pre n ([], s) → Preg n s)
    (hPh : ∀ n x l s, Pre n (x :: l, s) → Preh n ((x, l), s)) :
    TN (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2)) Pre k := by
  have h₁ := ofPoly (((polyFun_fst (α := List α) (β := σ)).comp polyFun_uncons).pair
    polyFun_snd) Pre k
  let back : Option (α × List α) × σ → List α × σ := fun q =>
    match q.1 with
    | none => ([], q.2)
    | some (x, l) => (x :: l, q.2)
  have h₂ := optionElim (Pre := fun n q => Pre n (back q)) hg hh
    (fun n s hs => hPg n s hs) (fun n xl s hs => by obtain ⟨x, l⟩ := xl; exact hPh n x l s hs)
  have hback : ∀ p : List α × σ, back (uncons p.1, p.2) = p := by
    rintro ⟨l, s⟩; cases l <;> rfl
  refine (h₁.comp h₂ (fun n p hp => by
      show Pre n (back (uncons p.1, p.2)); rw [hback]; exact hp)).of_eq (fun p => ?_)
  obtain ⟨l, s⟩ := p
  cases l <;> rfl

theorem id' (Pre : ℕ → α → Prop) (k : ℕ) : TN (id : α → α) Pre k := ofPoly polyFun_id Pre k

theorem const' (c : β) (Pre : ℕ → α → Prop) (k : ℕ) : TN (fun _ : α => c) Pre k :=
  ofPoly (polyFun_const c) Pre k

/-- A bound `c ≤ tsB A k b n (size a)`, for use in `iterate`. -/
def Bounded [Enc α] (c : ℕ → α → ℕ) (Pre : ℕ → α → Prop) (k : ℕ) : Prop :=
  ∃ A b, ∀ n a, Pre n a → c n a ≤ tsB A k b n (Enc.size a)

/-- **Bounded iteration from a set-up.** The number of rounds and the size of every state along
the orbit are bounded at the degree; each round (and the read-off) meets its precondition. -/
theorem iterateSetup {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β}
    {Pre : ℕ → α → Prop} {Pres Prer : ℕ → ℕ × σ → Prop} {k : ℕ}
    (hsetUp : TN setUp Pre k)
    (hstep : TN (fun x : ℕ × σ => (x.1 - 1, step x.2)) Pres k)
    (hread : TN (fun x : ℕ × σ => readOff x.2) Prer k)
    (hq : Bounded (fun _ a => (setUp a).1) Pre k)
    (hp : ∃ A b, ∀ n a, Pre n a → ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ tsB A k b n (Enc.size a))
    (hPs : ∀ n a, Pre n a → ∀ j < (setUp a).1, Pres n ((setUp a).1 - j, step^[j] (setUp a).2))
    (hPr : ∀ n a, Pre n a → Prer n (0, step^[(setUp a).1] (setUp a).2)) :
    TN (fun a => readOff (step^[(setUp a).1] (setUp a).2)) Pre k := by
  obtain ⟨A₀, b₀, h₀⟩ := hsetUp
  obtain ⟨A₁, b₁, h₁⟩ := hstep
  obtain ⟨A₂, b₂, h₂⟩ := hread
  obtain ⟨A₃, b₃, hq⟩ := hq
  obtain ⟨A₄, b₄, hp⟩ := hp
  obtain ⟨⟨P₁, hP₁w, hP₁⟩, -⟩ := h₀.mono (A' := A₀ + A₁ + A₂ + A₃ + A₄)
    (b' := b₀ + b₁ + b₂ + b₃ + b₄) (fun _ _ h => h) (by omega) le_rfl (by omega)
  obtain ⟨⟨Q, hQw, hQ⟩, -⟩ := h₁.mono (A' := A₀ + A₁ + A₂ + A₃ + A₄)
    (b' := b₀ + b₁ + b₂ + b₃ + b₄) (fun _ _ h => h) (by omega) le_rfl (by omega)
  obtain ⟨⟨P₃, hP₃w, hP₃⟩, hs₃⟩ := h₂.mono (A' := A₀ + A₁ + A₂ + A₃ + A₄)
    (b' := b₀ + b₁ + b₂ + b₃ + b₄) (fun _ _ h => h) (by omega) le_rfl (by omega)
  generalize hAdef : A₀ + A₁ + A₂ + A₃ + A₄ = A at *
  generalize hbdef : b₀ + b₁ + b₂ + b₃ + b₄ = b at *
  have hq' : ∀ n a, Pre n a → (setUp a).1 ≤ tsB A k b n (Enc.size a) := fun n a ha =>
    (hq n a ha).trans (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl)
  have hp' : ∀ n a, Pre n a → ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ tsB A k b n (Enc.size a) :=
    fun n a ha j hj => (hp n a ha j hj).trans (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl)
  clear hq hp
  have hround : ∀ n a, Pre n a → ∀ j < (setUp a).1,
      tsB A k b n (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ))
        ≤ tsB (A + b * (A + 1)) k (b * b) n (Enc.size a) := by
    intro n a ha j hj
    calc _ ≤ tsB A k b n (tsB A k b n (Enc.size a)) :=
          tsB_mono le_rfl le_rfl le_rfl le_rfl (hp' n a ha j hj.le)
      _ ≤ _ := tsB_comp_le A A k b b n (Enc.size a)
  have hlast : ∀ n a, Pre n a →
      tsB A k b n (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ))
        ≤ tsB (A + b * (A + 1)) k (b * b) n (Enc.size a) := by
    intro n a ha
    have h0 := hp' n a ha (setUp a).1 le_rfl
    rw [Nat.sub_self] at h0
    calc _ ≤ tsB A k b n (tsB A k b n (Enc.size a)) :=
          tsB_mono le_rfl le_rfl le_rfl le_rfl h0
      _ ≤ _ := tsB_comp_le A A k b b n (Enc.size a)
  generalize hA₅ : A + b * (A + 1) = A₅ at hround hlast
  refine ⟨A + (A + (A₅ + 3) + 2) + 2 + A₅ + 2, b + (b + (b * b + b * b)) + b * b,
    ⟨seq P₁ (seq (whileNz (16 + 2) Q) P₃),
      wf_seq hP₁w (wf_seq (wf_whileNz hQw) hP₃w), fun n a ha => ?_⟩, fun n a ha => ?_⟩
  · have hloop := pw_iterate (PreQ := Pres n) ⟨hQw, fun x hx => hQ n x hx⟩ (setUp a).1
      (setUp a).2 (tsB A₅ k (b * b) n (Enc.size a)) (hPs n a ha) (hround n a ha)
    have hrun := (hP₁ n a ha).seq (hloop.seq
      (hP₃ n ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ) (hPr n a ha)))
    refine hrun.mono ?_
    dsimp only
    have hN := hq' n a ha
    have hM2 : tsB A₅ k (b * b) n (Enc.size a) + 2 ≤ tsB (A₅ + 3) k (b * b) n (Enc.size a) := by
      have := mul_tsB_le 3 A₅ k (b * b) n (Enc.size a)
      have := one_le_tsB A₅ k (b * b) n (Enc.size a)
      omega
    have hNM : (setUp a).1 * (tsB A₅ k (b * b) n (Enc.size a) + 2) + 1
        ≤ tsB (A + (A₅ + 3) + 2) k (b + b * b) n (Enc.size a) := by
      have := Nat.mul_le_mul hN hM2
      rw [tsB_mul] at this
      have h2 := one_le_tsB (A + (A₅ + 3)) k (b + b * b) n (Enc.size a)
      have h3 := mul_tsB_le 2 (A + (A₅ + 3)) k (b + b * b) n (Enc.size a)
      omega
    have hl := hlast n a ha
    have hs := tsB_add_le A (A + (A₅ + 3) + 2) k b (b + b * b) n (Enc.size a)
    have hs' := tsB_add_le (A + (A + (A₅ + 3) + 2) + 2) A₅ k (b + (b + b * b)) (b * b) n
      (Enc.size a)
    have hmono := tsB_mono (A := A + (A + (A₅ + 3) + 2) + 2 + A₅ + 2)
      (A' := A + (A + (A₅ + 3) + 2) + 2 + A₅ + 2) (k := k) (k' := k)
      (b := b + (b + b * b) + b * b) (b' := b + (b + (b * b + b * b)) + b * b)
      (D := n) (D' := n) (n := Enc.size a) (n' := Enc.size a) le_rfl le_rfl (by omega)
      le_rfl le_rfl
    omega
  · refine (hs₃ n _ (hPr n a ha)).trans ((hlast n a ha).trans ?_)
    exact tsB_mono (by omega) le_rfl (by nlinarith) le_rfl le_rfl

end TN

/-! ## From the form `TN` to `StepBounds.step` -/

/-- **The bound of `StepBounds.step`** from a routine bounded at the root degree. -/
theorem stepForm_of_TNB [Enc α] {step : α → α} {Inv : ℕ → α → Prop} {A b : ℕ}
    (h : TNB (fun x : ℕ × α => (x.1 - 1, step x.2)) (fun n x => Inv n x.2) A 5 b) :
    ∃ Q : Program, ∀ (n k : ℕ) (x : α), Inv n x →
      RunsTo Q (fun m => m = initMemAt 16 (Enc.encode ((k, x) : ℕ × α)))
        (fun m' => m' = initMemAt 16 (Enc.encode ((k - 1, step x) : ℕ × α)))
        (2 ^ (A * (Nat.log 2 n + 2) ^ 5) * (Enc.size ((k, x) : ℕ × α) + 1) ^ b) := by
  obtain ⟨⟨Q, -, hQ⟩, -⟩ := h
  exact ⟨Q, fun n k x hx => hQ n (k, x) hx⟩

end Explicit
