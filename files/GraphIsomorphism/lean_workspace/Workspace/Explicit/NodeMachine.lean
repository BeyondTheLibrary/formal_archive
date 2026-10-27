import Workspace.Machine.QuasiFun
import Workspace.Machine.RunsOnLoop
import Workspace.Explicit.NodeBound

/-!
# Explicit running times: the two-scale class of routines

`Explicit.TS f Pre D A k b`: the function `f` is computed by one well-formed clean program of
the workspace convention (sixteen work registers, as `RAM.PolyFun`), which on every input `a`
with `Pre a` halts within `tsB A k b (D a) (Enc.size a)` steps, and on those inputs the output
has at most that size. Here `D : α → ℕ` is a degree read off the input. With `Pre = True` and
`D = Enc.size` this is `RAM.QuasiFun` with the exponent `k` made explicit; with a smaller `D`
it separates the quasipolynomial part of the cost (in the degree) from the polynomial part (in
the size). The precondition `Pre` is needed because some routines (the Split-or-Johnson run of
Sec. 9) are only fast on the inputs the algorithm actually produces.

The time bound is **pointwise** (`Explicit.PW`), not a function of the size alone, so the
closure rules are re-proved here from the machine lemmas that are already pointwise
(`RAM.RunsTo.seq`, `RAM.Pairing.runsTo_pairProg`, `RAM.runsTo_whileNz`); `optionElim` and the
loop repeat the proofs of `RAM.cleanComputeAt_optionElim` and `RAM.runsTo_iterateAt` with a
pointwise cost.
-/

namespace Explicit

open RAM

variable {α β γ σ : Type*}

/-- **Pointwise clean time under a precondition**: `P` is well formed, and from the workspace
memory holding an input `a` with `Pre a` it halts within `τ a` steps in the workspace memory
holding `f a`. -/
def PW [Enc α] [Enc β] (P : Program) (Pre : α → Prop) (f : α → β) (τ : α → ℕ) : Prop :=
  Wf P ∧ ∀ a, Pre a → RunsTo P (fun m => m = initMemAt 16 (Enc.encode a))
    (fun m' => m' = initMemAt 16 (Enc.encode (f a))) (τ a)

theorem PW.mono [Enc α] [Enc β] {P : Program} {Pre Pre' : α → Prop} {f : α → β}
    {τ τ' : α → ℕ} (h : PW P Pre f τ) (hPre : ∀ a, Pre' a → Pre a)
    (hτ : ∀ a, Pre' a → τ a ≤ τ' a) : PW P Pre' f τ' :=
  ⟨h.1, fun a ha => (h.2 a (hPre a ha)).mono (hτ a ha)⟩

/-- **The two-scale class.** -/
structure TS [Enc α] [Enc β] (f : α → β) (Pre : α → Prop) (D : α → ℕ) (A k b : ℕ) : Prop where
  time : ∃ P, PW P Pre f (fun a => tsB A k b (D a) (Enc.size a))
  size : ∀ a, Pre a → Enc.size (f a) ≤ tsB A k b (D a) (Enc.size a)

/-- No precondition. -/
abbrev Any (_ : α) : Prop := True

namespace TS

variable [Enc α] [Enc β] [Enc γ] [Enc σ]

theorem of_eq {f g : α → β} {Pre : α → Prop} {D : α → ℕ} {A k b : ℕ} (h : TS f Pre D A k b)
    (hfg : ∀ a, f a = g a) : TS g Pre D A k b := by
  have : f = g := funext hfg
  exact this ▸ h

theorem mono {f : α → β} {Pre Pre' : α → Prop} {D D' : α → ℕ} {A A' k k' b b' : ℕ}
    (h : TS f Pre D A k b) (hPre : ∀ a, Pre' a → Pre a) (hA : A ≤ A') (hk : k ≤ k') (hb : b ≤ b')
    (hD : ∀ a, Pre' a → D a ≤ D' a) : TS f Pre' D' A' k' b' := by
  obtain ⟨⟨P, hP⟩, hs⟩ := h
  exact ⟨⟨P, hP.mono hPre fun a ha => tsB_mono hA hk hb (hD a ha) le_rfl⟩,
    fun a ha => (hs a (hPre a ha)).trans (tsB_mono hA hk hb (hD a ha) le_rfl)⟩

theorem restrict {f : α → β} {Pre Pre' : α → Prop} {D : α → ℕ} {A k b : ℕ}
    (h : TS f Pre D A k b) (hPre : ∀ a, Pre' a → Pre a) : TS f Pre' D A k b :=
  h.mono hPre le_rfl le_rfl le_rfl (fun _ _ => le_rfl)

/-- **A polynomial change of degree.** -/
theorem polyD {f : α → β} {Pre : α → Prop} {D D' : α → ℕ} {A k b r₀ r : ℕ}
    (h : TS f Pre D A k b) (hD : ∀ a, Pre a → D a ≤ 2 ^ r₀ * (D' a + 1) ^ r) :
    TS f Pre D' (A * (r₀ + 2 * r + 3) ^ k) k b := by
  obtain ⟨⟨P, hP⟩, hs⟩ := h
  exact ⟨⟨P, hP.mono (fun _ h => h) fun a ha => tsB_le_of_poly (hD a ha)⟩,
    fun a ha => (hs a ha).trans (tsB_le_of_poly (hD a ha))⟩

/-- With `k = 0` the degree plays no role. -/
theorem anyD {f : α → β} {Pre : α → Prop} {D : α → ℕ} {A b : ℕ} (h : TS f Pre D A 0 b)
    (D' : α → ℕ) : TS f Pre D' A 0 b := by
  obtain ⟨⟨P, hP⟩, hs⟩ := h
  exact ⟨⟨P, hP.mono (fun _ h => h) fun a _ => (tsB_zero_k A b (D a) (D' a) _).le⟩,
    fun a ha => (hs a ha).trans (tsB_zero_k A b (D a) (D' a) _).le⟩

/-- **Composition.** The second routine's precondition must hold at the intermediate value,
and its degree there must be polynomially bounded by the degree of the input. -/
theorem comp {f : α → β} {g : β → γ} {Pre : α → Prop} {Pre' : β → Prop} {D : α → ℕ}
    {D' : β → ℕ} {A A' k b b' r₀ r : ℕ}
    (hf : TS f Pre D A k b) (hg : TS g Pre' D' A' k b') (hPre : ∀ a, Pre a → Pre' (f a))
    (hD : ∀ a, Pre a → D' (f a) ≤ 2 ^ r₀ * (D a + 1) ^ r) :
    TS (fun a => g (f a)) Pre D (A + (A' * (r₀ + 2 * r + 3) ^ k + b' * (A + 1)) + 2) k
      (b + b * b') := by
  obtain ⟨⟨P, hPw, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQw, hQ⟩, hsg⟩ := hg
  set A₂ := A' * (r₀ + 2 * r + 3) ^ k
  have key : ∀ a, Pre a → tsB A' k b' (D' (f a)) (Enc.size (f a))
      ≤ tsB (A₂ + b' * (A + 1)) k (b * b') (D a) (Enc.size a) := by
    intro a ha
    calc tsB A' k b' (D' (f a)) (Enc.size (f a))
        ≤ tsB A₂ k b' (D a) (Enc.size (f a)) := tsB_le_of_poly (hD a ha)
      _ ≤ tsB A₂ k b' (D a) (tsB A k b (D a) (Enc.size a)) :=
          tsB_mono le_rfl le_rfl le_rfl le_rfl (hsf a ha)
      _ ≤ _ := tsB_comp_le A A₂ k b b' (D a) (Enc.size a)
  refine ⟨⟨seq P Q, wf_seq hPw hQw, fun a ha =>
    ((hP a ha).seq (hQ (f a) (hPre a ha))).mono ?_⟩, fun a ha => ?_⟩
  · exact (Nat.add_le_add_left (key a ha) _).trans (tsB_add_le _ _ _ _ _ _ _)
  · exact (hsg (f a) (hPre a ha)).trans ((key a ha).trans ((Nat.le_add_left _ _).trans
      (tsB_add_le _ _ _ _ _ _ _)))

/-- **Composition with a polynomial second routine without precondition**: no condition on
the degree. -/
theorem comp0 {f : α → β} {g : β → γ} {Pre : α → Prop} {D : α → ℕ} {D' : β → ℕ}
    {A A' k b b' : ℕ} (hf : TS f Pre D A k b) (hg : TS g Any D' A' 0 b') :
    TS (fun a => g (f a)) Pre D (A + (A' * 3 ^ k + b' * (A + 1)) + 2) k (b + b * b') := by
  have hg' : TS g Any (fun _ => 0) A' k b' := (hg.anyD (fun _ => 0)).mono (fun _ h => h) le_rfl
    (Nat.zero_le k) le_rfl (fun _ _ => le_rfl)
  have := hf.comp (r₀ := 0) (r := 0) hg' (fun _ _ => trivial) (fun a _ => by simp)
  simpa using this

/-- **Every `RAM.PolyFun` is two-scale**, with any precondition, `k` and degree. -/
theorem ofPoly {f : α → β} (h : PolyFun f) :
    ∃ A b, ∀ (Pre : α → Prop) (D : α → ℕ) (k : ℕ), TS f Pre D A k b := by
  obtain ⟨⟨P, T, ⟨c, d, hT⟩, hP⟩, ⟨c', d', hs⟩⟩ := h.time, h.size
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, 0, fun Pre D k => ⟨⟨[], fun i hi => by simp at hi, fun a => (hα.false a).elim⟩,
      fun a => (hα.false a).elim⟩⟩
  have hw : Wf P := (hP (Classical.arbitrary _)).wf
  refine ⟨c + c', d + d', fun Pre D k => ⟨⟨P, hw, fun a _ => (hP a).mono ?_⟩, fun a _ => ?_⟩⟩
  · refine (hT _).trans ?_
    have h1 := const_le_tsB c k (D a) (Enc.size a)
    have h2 : (Enc.size a + 1) ^ d = tsB 0 k d (D a) (Enc.size a) := by simp [tsB]
    rw [h2]
    refine (Nat.mul_le_mul h1 le_rfl).trans ?_
    rw [tsB_mul]
    exact tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl
  · refine (hs a).trans ?_
    have h1 := const_le_tsB c' k (D a) (Enc.size a)
    have h2 : (Enc.size a + 1) ^ d' = tsB 0 k d' (D a) (Enc.size a) := by simp [tsB]
    rw [h2]
    refine (Nat.mul_le_mul h1 le_rfl).trans ?_
    rw [tsB_mul]
    exact tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl

set_option maxRecDepth 10000 in
/-- **Pairing.** -/
theorem pair {f : α → β} {g : α → γ} {Pre : α → Prop} {D : α → ℕ} {A A' k b b' : ℕ}
    (hf : TS f Pre D A k b) (hg : TS g Pre D A' k b') :
    TS (fun a => (f a, g a)) Pre D (A + A' + 453) k (b + b' + 1) := by
  obtain ⟨⟨P, hPw, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQw, hQ⟩, hsg⟩ := hg
  have hM : ∀ a, Enc.size a ≤ tsB (A + A') k (b + b' + 1) (D a) (Enc.size a) ∧
      tsB A k b (D a) (Enc.size a) ≤ tsB (A + A') k (b + b' + 1) (D a) (Enc.size a) ∧
      tsB A' k b' (D a) (Enc.size a) ≤ tsB (A + A') k (b + b' + 1) (D a) (Enc.size a) ∧
      1 ≤ tsB (A + A') k (b + b' + 1) (D a) (Enc.size a) := fun a =>
    ⟨(self_le_tsB k (D a) _).trans (tsB_mono (Nat.zero_le _) le_rfl (by omega) le_rfl le_rfl),
      tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl,
      tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl, one_le_tsB _ _ _ _ _⟩
  refine ⟨⟨Pairing.pairProg 16 P Q, Pairing.wf_pairProg 16 hPw hQw, fun a ha => ?_⟩,
    fun a ha => ?_⟩
  · have hpair : Enc.encode (f a, g a)
        = ((Enc.encode (f a)).length :: Enc.encode (f a)) ++
          ((Enc.encode (g a)).length :: Enc.encode (g a)) := rfl
    have h := Pairing.runsTo_pairProg (K := 16) (E := Enc.encode a) (F := Enc.encode (f a))
      (G := Enc.encode (g a)) (by omega) (hP a ha) (hQ a ha)
    rw [← hpair] at h
    refine h.mono ?_
    have hE : (Enc.encode a).length ≤ Enc.size a := le_of_lt (length_lt_listSize _)
    have hF : (Enc.encode (f a)).length ≤ Enc.size (f a) := le_of_lt (length_lt_listSize _)
    have hG : (Enc.encode (g a)).length ≤ Enc.size (g a) := le_of_lt (length_lt_listSize _)
    obtain ⟨h1, h2, h3, h4⟩ := hM a
    have h5 := hsf a ha
    have h6 := hsg a ha
    have h7 := mul_tsB_le 453 (A + A') k (b + b' + 1) (D a) (Enc.size a)
    dsimp only at *
    omega
  · have h := Combine.size_pair_le (f a) (g a)
    obtain ⟨h1, h2, h3, h4⟩ := hM a
    have h5 := hsf a ha
    have h6 := hsg a ha
    have h7 := mul_tsB_le 453 (A + A') k (b + b' + 1) (D a) (Enc.size a)
    omega

end TS

/-! ## `Option.elim` with a pointwise cost -/

set_option maxHeartbeats 1000000 in
/-- `RAM.cleanComputeAt_optionElim` with pointwise costs: the dispatcher pays for the branch it
takes only. -/
theorem pw_optionElim [Enc β] [Enc σ] [Enc γ] {Pg Ph : Program} {g : σ → γ}
    {h : β × σ → γ} {Preg : σ → Prop} {Preh : β × σ → Prop} {Pre : Option β × σ → Prop}
    {τg : σ → ℕ} {τh : β × σ → ℕ} (hg : PW Pg Preg g τg) (hh : PW Ph Preh h τh)
    (hPg : ∀ s, Pre (none, s) → Preg s) (hPh : ∀ x s, Pre (some x, s) → Preh (x, s)) :
    PW (Lists.optElimProg 16 Pg Ph) Pre
      (fun p : Option β × σ => p.1.elim (g p.2) (fun b => h (b, p.2)))
      (fun p => 43 * Enc.size p + 218 + p.1.elim (τg p.2) (fun b => τh (b, p.2))) := by
  have hK : 16 ≤ 16 := le_rfl
  refine ⟨Lists.wf_optElimProg hK hg.1 hh.1, ?_⟩
  rintro ⟨o, s⟩ hpre
  have hreg := initMemAt_option_tag (K := 16) o s
  have hsnd := Combine.cleanComputeAt_snd (α := Option β) (β := σ) hK (o, s)
  have hwfnone : Wf (seq (Combine.sndProg 16) Pg) := wf_seq hsnd.wf hg.1
  have hwfsome : Wf (seq (Lists.stripProg 16) Ph) :=
    wf_seq (Lists.runsTo_stripProg (K := 16) (eb := []) (es := []) hK rfl rfl).wf hh.1
  cases o with
  | none =>
      have hnone : RunsTo (seq (Combine.sndProg 16) Pg)
          (fun m => m = initMemAt 16 (Enc.encode ((none, s) : Option β × σ)))
          (fun m' => m' = initMemAt 16 (Enc.encode (g s)))
          (43 * Enc.size ((none, s) : Option β × σ) + 216 + τg s) :=
        (hsnd.seq (hg.2 s (hPg s hpre))).mono (by dsimp only; omega)
      have hbr1 : RunsTo (seq (Lists.stripProg 16) Ph)
          (fun m => m = initMemAt 16 (Enc.encode ((none, s) : Option β × σ)) ∧ m (16 + 2) ≠ 0)
          (fun m' => m' = initMemAt 16 (Enc.encode (g s))) 0 := by
        refine runsTo_of_false hwfsome ?_
        rintro m ⟨hm1, hm2⟩
        rw [hm1, hreg] at hm2
        simp at hm2
      exact (hbr1.ifz (hnone.strengthen (fun m hm => hm.1))).mono (by dsimp only; simp; omega)
  | some b =>
      have henc1 : Enc.encode ((some b, s) : Option β × σ)
          = ((Enc.encode b).length + 1) :: 1 ::
            (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
        show frame (1 :: Enc.encode b) ++ frame (Enc.encode s) = _
        simp [frame]
      have henc2 : Enc.encode ((b, s) : β × σ)
          = (Enc.encode b).length :: (Enc.encode b ++ ((Enc.encode s).length :: Enc.encode s)) := by
        show frame (Enc.encode b) ++ frame (Enc.encode s) = _
        simp [frame]
      have hlen : (Enc.encode ((some b, s) : Option β × σ)).length
          = (Enc.encode b).length + (Enc.encode s).length + 3 := by
        rw [henc1]; simp; all_goals omega
      have hlt : (Enc.encode b).length + (Enc.encode s).length + 3
          < Enc.size ((some b, s) : Option β × σ) := by
        have h1 := length_lt_listSize (Enc.encode ((some b, s) : Option β × σ))
        rw [hlen] at h1
        exact h1
      have hstrip : RunsTo (Lists.stripProg 16)
          (fun m => m = initMemAt 16 (Enc.encode ((some b, s) : Option β × σ)))
          (fun m' => m' = initMemAt 16 (Enc.encode ((b, s) : β × σ)))
          (19 * (Enc.encode b).length + 19 * (Enc.encode s).length + 16 + 104) := by
        rw [henc1, henc2]
        exact Lists.runsTo_stripProg hK rfl rfl
      have hsome : RunsTo (seq (Lists.stripProg 16) Ph)
          (fun m => m = initMemAt 16 (Enc.encode ((some b, s) : Option β × σ)))
          (fun m' => m' = initMemAt 16 (Enc.encode (h (b, s))))
          (43 * Enc.size ((some b, s) : Option β × σ) + 216 + τh (b, s)) :=
        (hstrip.seq (hh.2 (b, s) (hPh b s hpre))).mono (by omega)
      have hbr2 : RunsTo (seq (Combine.sndProg 16) Pg)
          (fun m => m = initMemAt 16 (Enc.encode ((some b, s) : Option β × σ)) ∧ m (16 + 2) = 0)
          (fun m' => m' = initMemAt 16 (Enc.encode (h (b, s)))) 0 := by
        refine runsTo_of_false hwfnone ?_
        rintro m ⟨hm1, hm2⟩
        rw [hm1, hreg] at hm2
        simp at hm2
      exact ((hsome.strengthen (fun m hm => hm.1)).ifz hbr2).mono (by dsimp only; simp; omega)

namespace TS

variable [Enc α] [Enc β] [Enc γ] [Enc σ]

/-- **Case analysis on an `Option`** carried alongside a state. -/
theorem optionElim {g : σ → γ} {h : β × σ → γ} {Preg : σ → Prop} {Preh : β × σ → Prop}
    {Pre : Option β × σ → Prop} {Dg : σ → ℕ} {Dh : β × σ → ℕ}
    {D : Option β × σ → ℕ} {A k b : ℕ} (hg : TS g Preg Dg A k b) (hh : TS h Preh Dh A k b)
    (hPg : ∀ s, Pre (none, s) → Preg s) (hPh : ∀ x s, Pre (some x, s) → Preh (x, s))
    (hDg : ∀ s, Pre (none, s) → Dg s ≤ D (none, s))
    (hDh : ∀ x s, Pre (some x, s) → Dh (x, s) ≤ D (some x, s)) :
    TS (fun p : Option β × σ => p.1.elim (g p.2) (fun x => h (x, p.2))) Pre D (A + 262) k
      (b + 1) := by
  obtain ⟨⟨P, hP⟩, hsg⟩ := hg
  obtain ⟨⟨Q, hQ⟩, hsh⟩ := hh
  have hbound : ∀ p : Option β × σ, Pre p →
      p.1.elim (tsB A k b (Dg p.2) (Enc.size p.2))
        (fun x => tsB A k b (Dh (x, p.2)) (Enc.size ((x, p.2) : β × σ)))
        ≤ tsB A k b (D p) (Enc.size p) := by
    rintro ⟨o, s⟩ hp
    cases o with
    | none => exact tsB_mono le_rfl le_rfl le_rfl (hDg _ hp) (Combine.size_snd_le _ _)
    | some x => exact tsB_mono le_rfl le_rfl le_rfl (hDh x s hp) (size_strip_le x s)
  refine ⟨⟨_, (pw_optionElim hP hQ hPg hPh).mono (fun _ h => h) fun p hp => ?_⟩, fun p hp => ?_⟩
  · have h1 := hbound p hp
    have h2 := self_le_tsB k (D p) (Enc.size p)
    have h3 : tsB 0 k 1 (D p) (Enc.size p) ≤ tsB A k (b + 1) (D p) (Enc.size p) :=
      tsB_mono (Nat.zero_le _) le_rfl (by omega) le_rfl le_rfl
    have h4 : tsB A k b (D p) (Enc.size p) ≤ tsB A k (b + 1) (D p) (Enc.size p) :=
      tsB_mono le_rfl le_rfl (by omega) le_rfl le_rfl
    have h5 := one_le_tsB A k (b + 1) (D p) (Enc.size p)
    have h6 := mul_tsB_le 262 A k (b + 1) (D p) (Enc.size p)
    obtain ⟨o, s⟩ := p
    cases o <;> (simp only [Option.elim] at h1 ⊢; omega)
  · refine le_trans ?_ ((hbound p hp).trans
      (tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl))
    obtain ⟨o, s⟩ := p
    cases o with
    | none => exact hsg s (hPg s hp)
    | some x => exact hsh (x, s) (hPh x s hp)

/-- **The conditional**: a polynomial test, two two-scale branches. -/
theorem ite {p : α → Bool} {f g : α → β} {Pre : α → Prop} {D : α → ℕ} {A k b : ℕ}
    (hp : PolyFun p) (hf : TS f Pre D A k b) (hg : TS g Pre D A k b) :
    ∃ A' b', TS (fun a => if p a then f a else g a) Pre D A' k b' := by
  obtain ⟨A₁, b₁, h₁⟩ := ofPoly ((PolyFun.ite hp (polyFun_const none) polyFun_some).pair
    (polyFun_id (α := α)))
  obtain ⟨A₂, b₂, h₂⟩ := ofPoly (polyFun_snd (α := α) (β := α))
  have hg' := (h₂ (fun q : α × α => Pre q.2) (fun q => D q.2) k).comp hg (r₀ := 0) (r := 1)
    (fun q hq => hq) (fun q _ => by simp)
  have h₃ := optionElim (Pre := fun q : Option α × α => Pre q.2) (D := fun q => D q.2)
    (hf.mono (A' := A + (A₂ + (A * (0 + 2 * 1 + 3) ^ k + b * (A₂ + 1)) + 2))
      (b' := b + (b₂ + b₂ * b)) (fun _ h => h) (Nat.le_add_right _ _) le_rfl
      (Nat.le_add_right _ _) (fun _ _ => le_rfl))
    (hg'.mono (A' := A + (A₂ + (A * (0 + 2 * 1 + 3) ^ k + b * (A₂ + 1)) + 2))
      (b' := b + (b₂ + b₂ * b)) (fun _ h => h) (Nat.le_add_left _ _) le_rfl
      (Nat.le_add_left _ _) (fun _ _ => le_rfl))
    (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl) (fun _ _ _ => le_rfl)
  refine ⟨_, _, ((h₁ Pre D k).comp h₃ (r₀ := 0) (r := 1) (fun a ha => ha)
    (fun a _ => by simp)).of_eq (fun a => ?_)⟩
  by_cases h : p a <;> simp [h]

/-- **Case analysis on a list** carried alongside a state. -/
theorem listCases {g : σ → γ} {h : (α × List α) × σ → γ} {Preg : σ → Prop}
    {Preh : (α × List α) × σ → Prop} {Pre : List α × σ → Prop} {Dg : σ → ℕ}
    {Dh : (α × List α) × σ → ℕ} {D : List α × σ → ℕ} {A k b : ℕ} (hg : TS g Preg Dg A k b)
    (hh : TS h Preh Dh A k b) (hPg : ∀ s, Pre ([], s) → Preg s)
    (hPh : ∀ x l s, Pre (x :: l, s) → Preh ((x, l), s))
    (hDg : ∀ s, Pre ([], s) → Dg s ≤ D ([], s))
    (hDh : ∀ x l s, Pre (x :: l, s) → Dh ((x, l), s) ≤ D (x :: l, s)) :
    ∃ A' b', TS (fun p : List α × σ =>
      match p.1 with
      | [] => g p.2
      | a :: l => h ((a, l), p.2)) Pre D A' k b' := by
  obtain ⟨A₁, b₁, h₁⟩ := ofPoly (((polyFun_fst (α := List α) (β := σ)).comp polyFun_uncons).pair
    polyFun_snd)
  let back : Option (α × List α) × σ → List α × σ := fun q =>
    match q.1 with
    | none => ([], q.2)
    | some (x, l) => (x :: l, q.2)
  have h₂ := optionElim (Pre := fun q => Pre (back q)) (D := fun q => D (back q)) hg hh
    (fun s hs => hPg s hs) (fun xl s hs => by obtain ⟨x, l⟩ := xl; exact hPh x l s hs)
    (fun s hs => hDg s hs) (fun xl s hs => by obtain ⟨x, l⟩ := xl; exact hDh x l s hs)
  have hback : ∀ p : List α × σ, back (uncons p.1, p.2) = p := by
    rintro ⟨l, s⟩; cases l <;> rfl
  refine ⟨_, _, ((h₁ Pre D k).comp h₂ (r₀ := 0) (r := 1) (fun p hp => by
      show Pre (back (uncons p.1, p.2)); rw [hback]; exact hp)
    (fun p _ => by show D (back (uncons p.1, p.2)) ≤ _; rw [hback]; simp)).of_eq
    (fun p => ?_)⟩
  obtain ⟨l, s⟩ := p
  cases l <;> rfl

theorem id' {Pre : α → Prop} {D : α → ℕ} (k : ℕ) : ∃ A b, TS (id : α → α) Pre D A k b := by
  obtain ⟨A, b, h⟩ := ofPoly (polyFun_id (α := α)); exact ⟨A, b, h Pre D k⟩

theorem const' (c : β) {Pre : α → Prop} {D : α → ℕ} (k : ℕ) :
    ∃ A b, TS (fun _ : α => c) Pre D A k b := by
  obtain ⟨A, b, h⟩ := ofPoly (polyFun_const (α := α) c); exact ⟨A, b, h Pre D k⟩

end TS

/-! ## The loop with a pointwise cost -/

set_option maxRecDepth 4000 in
/-- `RAM.runsTo_iterateAt` at `K = 16`, with a pointwise cost of the loop body. -/
theorem pw_iterate [Enc σ] {Q : Program} {step : σ → σ} {PreQ : ℕ × σ → Prop} {τ : ℕ × σ → ℕ}
    (hQ : PW Q PreQ (fun p : ℕ × σ => (p.1 - 1, step p.2)) τ)
    (N : ℕ) (s₀ : σ) (B : ℕ) (hPre : ∀ j < N, PreQ ((N - j, step^[j] s₀) : ℕ × σ))
    (hB : ∀ j < N, τ ((N - j, step^[j] s₀) : ℕ × σ) ≤ B) :
    RunsTo (whileNz (16 + 2) Q) (fun m => m = initMemAt 16 (Enc.encode ((N, s₀) : ℕ × σ)))
      (fun m' => m' = initMemAt 16 (Enc.encode ((0, step^[N] s₀) : ℕ × σ)))
      (N * (B + 2) + 1) := by
  set inv : Mem → Prop :=
    fun m => ∃ j ≤ N, m = initMemAt 16 (Enc.encode ((N - j, step^[j] s₀) : ℕ × σ)) with hinv
  have hbody : ∀ n : ℕ, RunsTo Q (fun m => inv m ∧ m (16 + 2) ≠ 0 ∧ m (16 + 2) = n)
      (fun m' => inv m' ∧ m' (16 + 2) < n) B := by
    intro n
    refine ⟨hQ.1, fun m hm => ?_⟩
    obtain ⟨⟨j, hjN, rfl⟩, hne, hμ⟩ := hm
    rw [initMemAt_prod_counter] at hne hμ
    have hj : j < N := by omega
    obtain ⟨k, hk, hhalt, hmem⟩ := (hQ.2 ((N - j, step^[j] s₀) : ℕ × σ) (hPre j hj)).spec _ rfl
    refine ⟨k, le_trans hk (hB j hj), hhalt, ?_⟩
    rw [hmem]
    have key : (fun x : ℕ × σ => (x.1 - 1, step x.2)) ((N - j, step^[j] s₀) : ℕ × σ)
        = ((N - (j + 1), step^[j + 1] s₀) : ℕ × σ) := by
      have h1 : N - j - 1 = N - (j + 1) := by omega
      simp [h1, Function.iterate_succ_apply']
    rw [key]
    exact ⟨⟨j + 1, by omega, rfl⟩, by rw [initMemAt_prod_counter]; omega⟩
  have hN : ∀ m, inv m → m (16 + 2) ≤ N := by
    rintro m ⟨j, hjN, rfl⟩
    rw [initMemAt_prod_counter]
    omega
  refine ((runsTo_whileNz (μ := fun m => m (16 + 2)) hbody hN).conseq ?_ ?_ (le_refl _))
  · rintro m rfl
    exact ⟨0, Nat.zero_le _, by simp⟩
  · rintro m' ⟨⟨j, hjN, rfl⟩, hz⟩
    rw [initMemAt_prod_counter] at hz
    have hjeq : j = N := by omega
    subst hjeq
    rw [Nat.sub_self]

namespace TS

variable [Enc α] [Enc β] [Enc σ]

/-- **Bounded iteration from a set-up, pointwise.** The number of rounds and the size of every
state along the orbit are bounded two-scale in the input; each round (and the read-off) meets
its precondition, and its degree is polynomially bounded by the degree of the input. -/
theorem iterateSetup {setUp : α → ℕ × σ} {step : σ → σ} {readOff : σ → β} {Pre : α → Prop}
    {Pres Prer : ℕ × σ → Prop} {D : α → ℕ} {Ds Dr : ℕ × σ → ℕ} {A k b r₀ r : ℕ}
    (hsetUp : TS setUp Pre D A k b)
    (hstep : TS (fun x : ℕ × σ => (x.1 - 1, step x.2)) Pres Ds A k b)
    (hread : TS (fun x : ℕ × σ => readOff x.2) Prer Dr A k b)
    (hq : ∀ a, Pre a → (setUp a).1 ≤ tsB A k b (D a) (Enc.size a))
    (hp : ∀ a, Pre a → ∀ j ≤ (setUp a).1,
      Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ) ≤ tsB A k b (D a) (Enc.size a))
    (hPs : ∀ a, Pre a → ∀ j < (setUp a).1, Pres ((setUp a).1 - j, step^[j] (setUp a).2))
    (hPr : ∀ a, Pre a → Prer (0, step^[(setUp a).1] (setUp a).2))
    (hDs : ∀ a, Pre a → ∀ j < (setUp a).1,
      Ds ((setUp a).1 - j, step^[j] (setUp a).2) ≤ 2 ^ r₀ * (D a + 1) ^ r)
    (hDr : ∀ a, Pre a → Dr (0, step^[(setUp a).1] (setUp a).2) ≤ 2 ^ r₀ * (D a + 1) ^ r) :
    ∃ A' b', TS (fun a => readOff (step^[(setUp a).1] (setUp a).2)) Pre D A' k b' := by
  obtain ⟨⟨P₁, hP₁⟩, -⟩ := hsetUp
  obtain ⟨⟨Q, hQ⟩, -⟩ := hstep
  obtain ⟨⟨P₃, hP₃⟩, hs₃⟩ := hread
  set A₂ := A * (r₀ + 2 * r + 3) ^ k
  set M := fun a => tsB (A₂ + b * (A + 1)) k (b * b) (D a) (Enc.size a) with hM
  have hround : ∀ a, Pre a → ∀ j < (setUp a).1,
      tsB A k b (Ds ((setUp a).1 - j, step^[j] (setUp a).2))
        (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) ≤ M a := by
    intro a ha j hj
    calc _ ≤ tsB A₂ k b (D a) (Enc.size (((setUp a).1 - j, step^[j] (setUp a).2) : ℕ × σ)) :=
          tsB_le_of_poly (hDs a ha j hj)
      _ ≤ tsB A₂ k b (D a) (tsB A k b (D a) (Enc.size a)) :=
          tsB_mono le_rfl le_rfl le_rfl le_rfl (hp a ha j hj.le)
      _ ≤ M a := tsB_comp_le A A₂ k b b (D a) (Enc.size a)
  have hlast : ∀ a, Pre a →
      tsB A k b (Dr (0, step^[(setUp a).1] (setUp a).2))
        (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) ≤ M a := by
    intro a ha
    have h0 := hp a ha (setUp a).1 le_rfl
    rw [Nat.sub_self] at h0
    calc _ ≤ tsB A₂ k b (D a) (Enc.size ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ)) :=
          tsB_le_of_poly (hDr a ha)
      _ ≤ tsB A₂ k b (D a) (tsB A k b (D a) (Enc.size a)) :=
          tsB_mono le_rfl le_rfl le_rfl le_rfl h0
      _ ≤ M a := tsB_comp_le A A₂ k b b (D a) (Enc.size a)
  set A₃ := A₂ + b * (A + 1)
  refine ⟨A + (A + (A₃ + 3) + 2) + 2 + (A₃) + 2, b + (b + (b * b + b * b)) + b * b,
    ⟨⟨seq P₁ (seq (whileNz (16 + 2) Q) P₃),
      wf_seq hP₁.1 (wf_seq (wf_whileNz hQ.1) hP₃.1), fun a ha => ?_⟩, fun a ha => ?_⟩⟩
  · have hloop := pw_iterate hQ (setUp a).1 (setUp a).2 (M a) (hPs a ha) (hround a ha)
    have hrun := (hP₁.2 a ha).seq (hloop.seq
      (hP₃.2 ((0, step^[(setUp a).1] (setUp a).2) : ℕ × σ) (hPr a ha)))
    refine hrun.mono ?_
    dsimp only
    have hN := hq a ha
    have hM2 : M a + 2 ≤ tsB (A₃ + 3) k (b * b) (D a) (Enc.size a) := by
      have := mul_tsB_le 3 A₃ k (b * b) (D a) (Enc.size a)
      have := one_le_tsB A₃ k (b * b) (D a) (Enc.size a)
      simp only [hM] at *
      omega
    have hNM : (setUp a).1 * (M a + 2) + 1
        ≤ tsB (A + (A₃ + 3) + 2) k (b + b * b) (D a) (Enc.size a) := by
      have := Nat.mul_le_mul hN hM2
      rw [tsB_mul] at this
      have h2 := one_le_tsB (A + (A₃ + 3)) k (b + b * b) (D a) (Enc.size a)
      have h3 := mul_tsB_le 2 (A + (A₃ + 3)) k (b + b * b) (D a) (Enc.size a)
      omega
    have hl := hlast a ha
    have hs := tsB_add_le A (A + (A₃ + 3) + 2) k b (b + b * b) (D a) (Enc.size a)
    have hs' := tsB_add_le (A + (A + (A₃ + 3) + 2) + 2) A₃ k (b + (b + b * b)) (b * b) (D a)
      (Enc.size a)
    have hmono := tsB_mono (A := A + (A + (A₃ + 3) + 2) + 2 + A₃ + 2)
      (A' := A + (A + (A₃ + 3) + 2) + 2 + (A₃) + 2) (k := k) (k' := k)
      (b := b + (b + b * b) + b * b) (b' := b + (b + (b * b + b * b)) + b * b)
      (D := D a) (D' := D a) (n := Enc.size a) (n' := Enc.size a) le_rfl le_rfl (by omega)
      le_rfl le_rfl
    simp only [hM] at hl
    omega
  · refine (hs₃ _ (hPr a ha)).trans ((hlast a ha).trans ?_)
    exact tsB_mono (by omega) le_rfl (by nlinarith) le_rfl le_rfl

end TS

end Explicit
