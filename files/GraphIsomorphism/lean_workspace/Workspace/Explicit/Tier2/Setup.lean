/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the set-up of the
top loop with explicit exponents. Not part of the faithful formalization.
-/
import Workspace.Explicit.Top.Setup
import Workspace.Explicit.Tier2.CountProg

/-!
# The set-up of the top loop, with explicit constants

`Explicit.ts_setUpE` gives the set-up `(countE K n, startState J)` as a two-scale routine with
exponents taken from `RAM.PolyFun` (existential). Here the same routine is assembled from
routines with numeric step counts:

* `Explicit.Lin f c s`: a workspace routine in time `c (N+1)` with outputs of size at most
  `s (N+1)`; closed under pairing and composition with explicit constants
  (`Explicit.Lin.pair`, `Explicit.Lin.comp`), with the projections, the identity, `cons` and
  constants as base cases;
* `Explicit.lin_build`: the start state `([(J, 0, st)], none)` from `(J, st)` is
  `Lin _ 175250 372`;
* the step count is `Explicit.cleanComputeAt_countE` (`Tier2/CountProg.lean`);
* `Explicit.ts_setUpX`: the set-up is `TS _ (RootPre p cam) Enc.size (setA sb K) 5 (setB sb)`
  with `Explicit.setA`, `Explicit.setB` closed formulas in `kP dP As ds kS` and `K`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM Algo Babai

variable {α β γ : Type*} [Enc α] [Enc β] [Enc γ]

/-! ## Routines with an explicit polynomial time -/

/-- **A routine with time `c (N+1)^b` and outputs of size at most `s (N+1)^b` is
two-scale** with `A = c + s`, for every precondition, degree and `k`. -/
theorem TS.ofPow {f : α → β} {P : Program} {c s b : ℕ}
    (h : CleanComputeAt 16 P f (fun N => c * (N + 1) ^ b))
    (hs : ∀ a, Enc.size (f a) ≤ s * (Enc.size a + 1) ^ b) (Pre : α → Prop) (D : α → ℕ)
    (k : ℕ) : TS f Pre D (c + s) k b := by
  have key : ∀ (e : ℕ) (a : α), e * (Enc.size a + 1) ^ b ≤ tsB (c + s) k b (D a) (Enc.size a) →
      e * (Enc.size a + 1) ^ b ≤ tsB (c + s) k b (D a) (Enc.size a) := fun _ _ h => h
  have hc : ∀ (e : ℕ) (a : α), e ≤ c + s →
      e * (Enc.size a + 1) ^ b ≤ tsB (c + s) k b (D a) (Enc.size a) := by
    intro e a he
    have h1 := const_le_tsB e k (D a) (Enc.size a)
    have h2 : (Enc.size a + 1) ^ b = tsB 0 k b (D a) (Enc.size a) := by simp [tsB]
    rw [h2]
    refine (Nat.mul_le_mul h1 le_rfl).trans ?_
    rw [tsB_mul]
    exact tsB_mono (by omega) le_rfl (by omega) le_rfl le_rfl
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨⟨[], fun i hi => by simp at hi, fun a => (hα.false a).elim⟩,
      fun a => (hα.false a).elim⟩
  refine ⟨⟨P, (h (Classical.arbitrary _)).wf, fun a _ => (h a).mono ?_⟩, fun a _ => ?_⟩
  · exact key _ a (hc c a (Nat.le_add_right _ _))
  · exact (hs a).trans (hc s a (Nat.le_add_left _ _))

/-- **Linear clean time**: a workspace routine in time `c (N+1)` whose outputs have size at
most `s (N+1)`. -/
structure Lin (f : α → β) (c s : ℕ) : Prop where
  time : ∃ P, CleanComputeAt 16 P f (fun N => c * (N + 1))
  size : ∀ a, Enc.size (f a) ≤ s * (Enc.size a + 1)

namespace Lin

theorem mono {f : α → β} {c s c' s' : ℕ} (h : Lin f c s) (hc : c ≤ c') (hs : s ≤ s') :
    Lin f c' s' := by
  obtain ⟨⟨P, hP⟩, hsz⟩ := h
  exact ⟨⟨P, fun a => (hP a).mono (Nat.mul_le_mul_right _ hc)⟩,
    fun a => (hsz a).trans (Nat.mul_le_mul_right _ hs)⟩

theorem toTS {f : α → β} {c s : ℕ} (h : Lin f c s) (Pre : α → Prop) (D : α → ℕ) (k : ℕ) :
    TS f Pre D (c + s) k 1 := by
  obtain ⟨⟨P, hP⟩, hsz⟩ := h
  exact TS.ofPow (P := P) (fun a => (hP a).mono (by simp)) (fun a => by simpa using hsz a)
    Pre D k

/-- **Pairing.** -/
theorem pair {f : α → β} {g : α → γ} {c s c' s' : ℕ} (hf : Lin f c s) (hg : Lin g c' s') :
    Lin (fun a => (f a, g a)) (19 + 19 * s + 19 * s' + 10 * c + 10 * c' + 376) (2 * s + 2 * s') := by
  obtain ⟨⟨P, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQ⟩, hsg⟩ := hg
  refine ⟨⟨Pairing.pairProg 16 P Q, fun a => ?_⟩, fun a => ?_⟩
  · refine (Pairing.cleanComputeAt_pair (K := 16) (by norm_num) hP hQ
      (Sf := fun n => s * (n + 1)) (Sg := fun n => s' * (n + 1)) hsf hsg a).mono ?_
    dsimp only
    have e : (19 + 19 * s + 19 * s' + 10 * c + 10 * c' + 376) * (Enc.size a + 1) =
        19 * (Enc.size a + 1) + 19 * (s * (Enc.size a + 1)) + 19 * (s' * (Enc.size a + 1)) +
        10 * (c * (Enc.size a + 1)) + 10 * (c' * (Enc.size a + 1)) + 376 * (Enc.size a + 1) := by
      ring
    omega
  · have h := Combine.size_pair_le (f a) (g a)
    have h1 := hsf a
    have h2 := hsg a
    have e : (2 * s + 2 * s') * (Enc.size a + 1) =
        2 * (s * (Enc.size a + 1)) + 2 * (s' * (Enc.size a + 1)) := by ring
    omega

/-- **Composition** (`f` first). -/
theorem comp {f : α → β} {g : β → γ} {c s c' s' : ℕ} (hf : Lin f c s) (hg : Lin g c' s') :
    Lin (fun a => g (f a)) (c + c' * s + c') (s' * s + s') := by
  obtain ⟨⟨P, hP⟩, hsf⟩ := hf
  obtain ⟨⟨Q, hQ⟩, hsg⟩ := hg
  refine ⟨⟨seq P Q, fun a => ?_⟩, fun a => ?_⟩
  · refine (CleanComputeAt.comp hP hQ (fun n n' h => Nat.mul_le_mul_left _ (by omega))
      (S := fun n => s * (n + 1)) hsf a).mono ?_
    dsimp only
    have e : (c + c' * s + c') * (Enc.size a + 1) =
        c * (Enc.size a + 1) + c' * (s * (Enc.size a + 1) + 1) + c' * Enc.size a := by ring
    rw [e]
    exact Nat.le_add_right _ _
  · have h1 := hsg (f a)
    have h2 : s' * (Enc.size (f a) + 1) ≤ s' * (s * (Enc.size a + 1) + 1) :=
      Nat.mul_le_mul_left _ (by have := hsf a; omega)
    have e : (s' * s + s') * (Enc.size a + 1) =
        s' * (s * (Enc.size a + 1) + 1) + s' * Enc.size a := by ring
    rw [e]
    omega

theorem fst : Lin (Prod.fst : α × β → α) 110 1 :=
  ⟨⟨_, fun a => (Combine.cleanComputeAt_fst (K := 16) (by norm_num) a).mono (by
    dsimp only; omega)⟩, fun a => by have := size_fst_le' a; omega⟩

theorem snd : Lin (Prod.snd : α × β → β) 120 1 :=
  ⟨⟨_, fun a => (Combine.cleanComputeAt_snd (K := 16) (by norm_num) a).mono (by
    dsimp only; omega)⟩, fun a => by have := size_snd_le' a; omega⟩

theorem id : Lin (fun a : α => a) 0 1 :=
  ⟨⟨[], fun a => (cleanComputeAt_id 16 a).mono (by simp)⟩, fun a => by omega⟩

theorem cons : Lin (fun p : β × List β => p.1 :: p.2) 123 1 :=
  ⟨⟨_, fun a => (cleanComputeAt_cons (K := 16) (by norm_num) a).mono (by
    dsimp only; omega)⟩, fun ⟨b, l⟩ => by have := size_cons_le b l; dsimp only; omega⟩

/-- A constant of size `S`. -/
theorem const (x : β) {S : ℕ} (hS : Enc.size x = S) :
    Lin (fun _ : α => x) (114 + 10 * S) S := by
  refine ⟨⟨_, fun a => (cleanComputeAt_of_cleanCompute (K := 16) (by norm_num)
    (cleanCompute_const (α := α) x) a).mono ?_⟩, fun a => ?_⟩
  · have hl : (Enc.encode x).length < Enc.size x := length_lt_listSize _
    show 10 * (5 * Enc.size a + (10 + ((Enc.encode x).length + 1))) + 4 ≤
      (114 + 10 * S) * (Enc.size a + 1)
    have e : (114 + 10 * S) * (Enc.size a + 1) = 114 * Enc.size a + 114 + 10 * (S * (Enc.size a + 1)) := by
      ring
    have h1 : S ≤ S * (Enc.size a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · rw [hS]; exact Nat.le_mul_of_pos_right _ (by omega)

end Lin

/-! ## The start state -/

/-- The start state from the root and its fold state. -/
def buildStart (q : RawMasterSI × StateE) : EvalStateE := ([(q.1, 0, q.2)], none)

theorem lin_build : Lin buildStart 175250 372 := by
  have h0 : Enc.size (0 : ℕ) = 2 := by rw [Small.size_nat]; rfl
  have g1 := (Lin.fst (α := RawMasterSI) (β := StateE)).pair
    ((Lin.const (α := RawMasterSI × StateE) (0 : ℕ) h0).pair Lin.snd)
  have g2 := (Lin.id (α := RawMasterSI × ℕ × StateE)).pair
    (Lin.const (α := RawMasterSI × ℕ × StateE) ([] : List (RawMasterSI × ℕ × StateE)) size_nil)
  have g4 := (Lin.id (α := List (RawMasterSI × ℕ × StateE))).pair
    (Lin.const (α := List (RawMasterSI × ℕ × StateE)) (none : Option RawCoset) size_none)
  have h := ((g1.comp g2).comp Lin.cons).comp g4
  exact h.mono (by norm_num) (by norm_num)

/-! ## The set-up -/

variable {p : Params} {cam : RawGens × List ℕ → Option RawCameron}

/-- The first exponent of the set-up (the step count at the degree). -/
def setA₁ (sb : StepBounds p cam) (K : ℕ) : ℕ :=
  sb.kP + 1 + ((countTime K + (K + 5)) * 3 ^ 5 + 5 * (sb.kP + 1 + 1)) + 2

/-- The first polynomial degree of the set-up. -/
def setB₁ (sb : StepBounds p cam) : ℕ := sb.dP + 1 + (sb.dP + 1) * 5

/-- The exponent of the root paired with its fold state. -/
def setA₂ (sb : StepBounds p cam) : ℕ := 0 + 1 + (sb.As + sb.kS) + 453

/-- The polynomial degree of the root paired with its fold state. -/
def setB₂ (sb : StepBounds p cam) : ℕ := 1 + sb.ds + 1

/-- **The exponent of the set-up.** -/
def setA (sb : StepBounds p cam) (K : ℕ) : ℕ :=
  setA₁ sb K + (setA₂ sb + ((175250 + 372) * 3 ^ 5 + 1 * (setA₂ sb + 1)) + 2) + 453

/-- **The polynomial degree of the set-up.** -/
def setB (sb : StepBounds p cam) : ℕ := setB₁ sb + (setB₂ sb + setB₂ sb * 1) + 1

/-- **The set-up is two-scale with explicit constants**, on good roots, the size as
degree. -/
theorem ts_setUpX (sb : StepBounds p cam) (K : ℕ) :
    TS (setUpE p cam K) (RootPre p cam) Enc.size (setA sb K) 5 (setB sb) := by
  -- the degree
  obtain ⟨G, hG⟩ := sb.ground
  have hground : TS (masterRoundE p cam).ground (RootPre p cam) Enc.size (sb.kP + 1) 5
      (sb.dP + 1) := by
    have hle : ∀ J : RawMasterSI, 2 ^ sb.kP * (Enc.size J + 1) ^ sb.dP
        ≤ tsB (sb.kP + 1) 5 (sb.dP + 1) (Enc.size J) (Enc.size J) := fun J => by
      have e : tsB sb.kP 0 sb.dP (Enc.size J) (Enc.size J)
          = 2 ^ sb.kP * (Enc.size J + 1) ^ sb.dP := by simp [tsB]
      rw [← e]
      exact tsB_mono (by omega) (by omega) (by omega) le_rfl le_rfl
    rcases isEmpty_or_nonempty RawMasterSI with hα | hα
    · exact ⟨⟨[], fun i hi => by simp at hi, fun a => (hα.false a).elim⟩,
        fun a => (hα.false a).elim⟩
    refine ⟨⟨G, (hG (Classical.arbitrary _)).wf, fun J _ => (hG J).mono (hle J)⟩,
      fun J _ => ?_⟩
    have h1 := sb.cost.ground_le J
    have h2 : Enc.size ((masterRoundE p cam).ground J)
        ≤ (masterRoundE p cam).ground J + 2 := by
      rw [Small.size_nat]; have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (masterRoundE p cam).ground J)); omega
    have h3 : Enc.size J + 2 ≤ tsB 1 0 1 (Enc.size J) (Enc.size J) := by
      simp [tsB]; omega
    exact (by omega : _ ≤ tsB 1 0 1 (Enc.size J) (Enc.size J)).trans
      (tsB_mono (by omega) (by omega) (by omega) le_rfl le_rfl)
  -- the step count at the degree
  have hcnt : TS (countE K) Any (fun _ => 0) (countTime K + (K + 5)) 0 5 :=
    TS.ofPow (cleanComputeAt_countE K) (size_countE_le K) Any _ 0
  have hce := hground.comp0 hcnt
  -- the root and its fold state
  obtain ⟨Q, hQw, hQ⟩ := sb.init
  have hinit : TS (masterRoundE p cam).init (RootPre p cam) Enc.size
      (sb.As + sb.kS) 5 sb.ds := by
    refine ⟨⟨Q, hQw, fun J hJ => (hQ J hJ.1 hJ.2.1).mono ?_⟩, fun J hJ => ?_⟩
    · exact (tsB_mono (Nat.le_add_right _ _) le_rfl le_rfl le_rfl le_rfl :
        tsB sb.As 5 sb.ds (Enc.size J) (Enc.size J)
          ≤ tsB (sb.As + sb.kS) 5 sb.ds (Enc.size J) (Enc.size J))
    · exact (size_initE_le sb J hJ).trans
        (tsB_mono (Nat.le_add_left _ _) le_rfl (Nat.zero_le _) le_rfl le_rfl)
  have hid : TS (fun J : RawMasterSI => J) (RootPre p cam) Enc.size (0 + 1) 5 1 :=
    Lin.id.toTS _ _ _
  have hpairJ := hid.pair hinit
  have hstart := hpairJ.comp0 (lin_build.toTS Any Enc.size 0)
  exact (hce.pair hstart).of_eq fun J => rfl

end Explicit
