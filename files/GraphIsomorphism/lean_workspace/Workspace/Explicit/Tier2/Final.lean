/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the constant of the
running time as a closed formula. Not part of the faithful formalization.
-/
import Workspace.Explicit.Line1.Top
import Workspace.Explicit.Tier2.Setup
import Workspace.Explicit.Main

/-!
# Theorem 1.1.1 with exponent 5 and an explicit constant

`Explicit.main_of_rec` closes the time bound with the class `Explicit.Q5`, whose constant is
existential. Here the same bound is closed with `Explicit.B5 c`, where `c` is given:

* `Explicit.B5 c T`: `T N ≤ 2^{c (log₂ N + 2)^5}` for all `N`, with the rules of `Q5` at
  explicit constants (sum `c + c' + 1`, product `c + c'`, power `d·c`, composition with a
  polynomial `2^a (N+1)^b`: `c (a + 2b + 3)^5`);
* `Explicit.cTop sb K A₁ b₁`: the constant of `Explicit.Tf`;
* `Explicit.cFinal sb`: the constant of the whole program (the bridges included), at
  `K = 4 Aw + 14 Ap + 24` and the set-up constants `Explicit.setA`, `Explicit.setB`;
* `Explicit.Theorem_1_1_1_exponent5_numeral c` and
  `Explicit.theorem_1_1_1_exponent5_numeral_of_bounds`: from `Explicit.ParamsOKX p` (the
  specifications of the parameters, line 1 at the explicit thresholds `B = 25`,
  `C₀ = (max 64 25!)! + 1` of `Explicit.line1OK_X`) and `StepBounds p masterCameron`, one RAM
  program solves String Isomorphism within `2^{cFinal sb · (log₂ N + 2)^5}` steps.

`cFinal sb` is a closed formula in the numeric fields `kP dP kB dB As ds kS Aw Ap` of
`StepBounds` (which part 1 gives in terms of the Cameron constants); `Explicit.cFinal_closed`
writes it out: with `r = (kP + 2dP + 3)^5` and `K = 4Aw + 14Ap + 24`,
`cFinal = 2kP + dP + 150 + r (6kP + 6dP + 3As + 2ds + 2kS + kB + dB + 19684 K + 42832816)
+ (ds + dP)((K + 5 + kS) r + 10)`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai

/-! ## Exponent 5 with a given constant -/

/-- **Exponent 5 with constant `c`**: `T N ≤ 2^{c (log₂ N + 2)^5}` for all `N`. -/
def B5 (c : ℕ) (T : ℕ → ℕ) : Prop := ∀ N, T N ≤ 2 ^ (c * lg N ^ 5)

theorem B5.q5 {c : ℕ} {T : ℕ → ℕ} (h : B5 c T) : Q5 T := ⟨c, h⟩

theorem B5.mono {c c' : ℕ} {T T' : ℕ → ℕ} (h : B5 c T') (hT : ∀ N, T N ≤ T' N) (hc : c ≤ c') :
    B5 c' T := fun N => (hT N).trans ((h N).trans
  (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc)))

theorem b5_const (a : ℕ) : B5 a (fun _ => a) := fun N =>
  (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (one_le_lg5 N)))

theorem B5.mul {c c' : ℕ} {T T' : ℕ → ℕ} (h : B5 c T) (h' : B5 c' T') :
    B5 (c + c') (fun N => T N * T' N) := fun N => by
  calc T N * T' N ≤ 2 ^ (c * lg N ^ 5) * 2 ^ (c' * lg N ^ 5) := Nat.mul_le_mul (h N) (h' N)
    _ = 2 ^ ((c + c') * lg N ^ 5) := by rw [← pow_add, add_mul]

theorem B5.add {c c' : ℕ} {T T' : ℕ → ℕ} (h : B5 c T) (h' : B5 c' T') :
    B5 (c + c' + 1) (fun N => T N + T' N) := fun N => by
  have h1 : 2 ^ (c * lg N ^ 5) ≤ 2 ^ ((c + c') * lg N ^ 5) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have h2 : 2 ^ (c' * lg N ^ 5) ≤ 2 ^ ((c + c') * lg N ^ 5) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have h3 : 2 * 2 ^ ((c + c') * lg N ^ 5) ≤ 2 ^ ((c + c' + 1) * lg N ^ 5) := by
    have : 2 ^ ((c + c' + 1) * lg N ^ 5) = 2 ^ ((c + c') * lg N ^ 5) * 2 ^ (lg N ^ 5) := by
      rw [← pow_add, add_mul, one_mul]
    rw [this]
    have h4 : 2 ≤ 2 ^ (lg N ^ 5) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (lg N ^ 5) := Nat.pow_le_pow_right (by norm_num) (one_le_lg5 N)
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h4
  have := h N
  have := h' N
  show T N + T' N ≤ _
  omega

theorem B5.pow {c : ℕ} {T : ℕ → ℕ} (h : B5 c T) (d : ℕ) : B5 (d * c) (fun N => T N ^ d) :=
  fun N => by
  calc T N ^ d ≤ (2 ^ (c * lg N ^ 5)) ^ d := Nat.pow_le_pow_left (h N) d
    _ = 2 ^ (d * c * lg N ^ 5) := by rw [← pow_mul]; ring_nf

theorem b5_two_pow_lg (A k : ℕ) (hk : k ≤ 5) : B5 A (fun N => 2 ^ (A * lg N ^ k)) := fun N =>
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (lg_pow_mono le_rfl hk))

theorem b5_two_pow (a : ℕ) : B5 a (fun _ => 2 ^ a) :=
  (b5_two_pow_lg a 0 (by norm_num)).mono (fun N => by simp) le_rfl

theorem b5_succ : B5 1 (fun N => N + 1) := fun N =>
  (succ_le_two_pow_lg N).trans (Nat.pow_le_pow_right (by norm_num) (by
    rw [one_mul]
    calc lg N = lg N ^ 1 := (pow_one _).symm
      _ ≤ lg N ^ 5 := Nat.pow_le_pow_right (by have := two_le_lg N; omega) (by norm_num)))

theorem b5_id : B5 1 (fun N => N) := b5_succ.mono (fun N => Nat.le_succ N) le_rfl

/-- A polynomial `2^a (N+1)^b`. -/
theorem b5_poly (a b : ℕ) : B5 (a + b * 1) (fun N => 2 ^ a * (N + 1) ^ b) :=
  (b5_two_pow a).mul (b5_succ.pow b)

/-- **Composition with a polynomially bounded function.** -/
theorem B5.comp_poly {c : ℕ} {T S : ℕ → ℕ} (h : B5 c T) {a b : ℕ}
    (hS : ∀ N, S N ≤ 2 ^ a * (N + 1) ^ b) : B5 (c * (a + 2 * b + 3) ^ 5) (fun N => T (S N)) :=
  fun N => by
  refine (h (S N)).trans ?_
  apply Nat.pow_le_pow_right (by norm_num)
  rw [mul_assoc, ← mul_pow]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lg_le_of_poly (hS N)) 5)

theorem b5_tsB (A b : ℕ) : B5 (A + b * 1) (fun N => tsB A 5 b N N) :=
  (b5_two_pow_lg A 5 le_rfl).mul (b5_succ.pow b)

theorem b5_countE (K : ℕ) : B5 (3 + K + 1 + 1) (countE K) :=
  (((b5_const 3).mul (b5_two_pow_lg K 5 le_rfl)).add (b5_const 1)).mono (fun _ => le_rfl) le_rfl

/-! ## The constant of the time bound -/

variable {p : Params} {cam : RawGens × List ℕ → Option RawCameron}

/-- The factor of a composition with the root bound `2^kP (N+1)^dP`. -/
def rF (sb : StepBounds p cam) : ℕ := (sb.kP + 2 * sb.dP + 3) ^ 5

/-- The constant of the step count at the root bound. -/
def cCount (sb : StepBounds p cam) (K : ℕ) : ℕ := (3 + K + 1 + 1) * rF sb

/-- The constant of the state bound `Explicit.STf`. -/
def cState (sb : StepBounds p cam) : ℕ := sb.kS * rF sb

/-- The constant of the loop-state bound `Explicit.PBf`. -/
def cPB (sb : StepBounds p cam) (K : ℕ) : ℕ :=
  2 + (cCount sb K + 2 + 1) + (2 + cState sb) + 1

/-- The constant of the round bound `Explicit.BBf`. -/
def cBB (sb : StepBounds p cam) (K : ℕ) : ℕ :=
  sb.As * rF sb + sb.ds * (cPB sb K + 1 + 1)

/-- **The constant of `Explicit.Tf`.** -/
def cTop (sb : StepBounds p cam) (K A₁ b₁ : ℕ) : ℕ :=
  (sb.kP + sb.dP * 1) +
    ((A₁ + b₁ * 1) * rF sb +
      ((cCount sb K + (cBB sb K + 2 + 1)) + 1 + 1 + (sb.kP + sb.dP * (cPB sb K + 1 + 1)) + 1) +
      1) + 1

theorem b5_Tf (sb : StepBounds p cam) (K A₁ b₁ : ℕ) : B5 (cTop sb K A₁ b₁) (Tf sb K A₁ b₁) := by
  have hS : ∀ N, SJf sb N ≤ 2 ^ sb.kP * (N + 1) ^ sb.dP := fun N => le_rfl
  have hSJ : B5 (sb.kP + sb.dP * 1) (SJf sb) := b5_poly sb.kP sb.dP
  have hce : B5 (cCount sb K) (fun N => countE K (SJf sb N)) := (b5_countE K).comp_poly hS
  have hst : B5 (cState sb) (STf sb) := (b5_two_pow_lg sb.kS 5 le_rfl).comp_poly hS
  have hPB : B5 (cPB sb K) (PBf sb K) :=
    (((b5_const 2).mul (hce.add (b5_const 2))).add ((b5_const 2).mul hst)).mono
      (fun _ => le_rfl) le_rfl
  have hBB : B5 (cBB sb K) (BBf sb K) :=
    (((b5_two_pow_lg sb.As 5 le_rfl).comp_poly hS).mul ((hPB.add (b5_const 1)).pow sb.ds)).mono
      (fun _ => le_rfl) le_rfl
  have hts : B5 ((A₁ + b₁ * 1) * rF sb) (fun N => tsB A₁ 5 b₁ (SJf sb N) (SJf sb N)) :=
    (b5_tsB A₁ b₁).comp_poly hS
  exact (hSJ.add (hts.add (((hce.mul (hBB.add (b5_const 2))).add (b5_const 1)).add
    ((b5_two_pow sb.kP).mul ((hPB.add (b5_const 1)).pow sb.dP))))).mono
    (fun _ => le_rfl) le_rfl

theorem b5_Sf (sb : StepBounds p cam) : B5 ((sb.kB + sb.dB * 1) * rF sb) (Sf sb) :=
  ((b5_poly sb.kB sb.dB).mono sb.bound_le le_rfl).comp_poly (fun _ => le_rfl)

/-- The node-count constant `K = 4 Aw + 14 Ap + 24` of `Explicit.recOK_of_paramsOKX`. -/
def kNodes (sb : StepBounds p cam) : ℕ := 4 * sb.Aw + 14 * sb.Ap + 24

/-- **The constant of the whole program**, bridges included. -/
def cFinal (sb : StepBounds p cam) : ℕ :=
  (18 + 1 + 78 + 1) +
    (cTop sb (kNodes sb) (setA sb (kNodes sb)) (setB sb) +
      (7 + (sb.kB + sb.dB * 1) * rF sb + 34 + 1) + 1) + 1

/-- **The set-up constants in closed form.** -/
theorem setA_eq (sb : StepBounds p cam) (K : ℕ) :
    setA sb K = 6 * sb.kP + 2 * sb.As + 2 * sb.kS + 19683 * K + 42832800 := by
  simp only [setA, setA₁, setA₂, countTime]; ring

theorem setB_eq (sb : StepBounds p cam) : setB sb = 6 * sb.dP + 2 * sb.ds + 11 := by
  simp only [setB, setB₁, setB₂]; ring

/-- **The constant in closed form**, with `r = (kP + 2 dP + 3)^5` and `K = 4 Aw + 14 Ap + 24`. -/
theorem cFinal_eq (sb : StepBounds p cam) :
    cFinal sb = 2 * sb.kP + sb.dP + 150 +
      rF sb * (setA sb (kNodes sb) + setB sb + kNodes sb + 5 + sb.As + sb.kB + sb.dB) +
      (sb.ds + sb.dP) * ((kNodes sb + 5 + sb.kS) * rF sb + 10) := by
  simp only [cFinal, cTop, cBB, cPB, cState, cCount]; ring

/-- **The constant in closed form, in the fields of `StepBounds` only.** -/
theorem cFinal_closed (sb : StepBounds p cam) :
    cFinal sb = 2 * sb.kP + sb.dP + 150 +
      (sb.kP + 2 * sb.dP + 3) ^ 5 * (6 * sb.kP + 6 * sb.dP + 3 * sb.As + 2 * sb.ds + 2 * sb.kS +
        sb.kB + sb.dB + 19684 * (4 * sb.Aw + 14 * sb.Ap + 24) + 42832816) +
      (sb.ds + sb.dP) *
        ((4 * sb.Aw + 14 * sb.Ap + 29 + sb.kS) * (sb.kP + 2 * sb.dP + 3) ^ 5 + 10) := by
  rw [cFinal_eq, setA_eq, setB_eq]
  simp only [rF, kNodes]
  ring

/-! ## The program -/

/-- **The workspace routine in time `Tf` at the explicit set-up constants.** -/
theorem cleanSolveAt_of_recX {K : ℕ} (rk : RecOK p cam K) (sb : StepBounds p cam) :
    ∃ P : Program, ∀ n s : ℕ, CleanSolveAt 16 P
      (fun (a : SIInput n s) (b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n))) =>
        SIRel n s a b ∧ Enc.size b ≤ Sf sb (Enc.size a))
      (Tf sb K (setA sb K) (setB sb)) := by
  obtain ⟨Pent, hPent⟩ := sb.entry
  obtain ⟨⟨P₁, hP₁⟩, -⟩ := ts_setUpX sb K
  obtain ⟨Q, hQ⟩ := sb.step
  obtain ⟨P₃, hP₃⟩ := sb.readOff
  exact ⟨seq Pent (seq P₁ (seq (whileNz (16 + 2) Q) P₃)), fun n s a =>
    runE_top rk sb hPent (fun J hJ => hP₁.2 J hJ) hQ hP₃ n s a⟩

/-- **The Master in time `2^{c (log₂ N+2)^5}` with the constant of the recursion.** -/
theorem main_of_recX (sb : StepBounds p cam) (rk : RecOK p cam (kNodes sb)) :
    ∃ P : Program, ∀ n s : ℕ,
      SolvesInTime P (SIRel n s) (fun N => 2 ^ (cFinal sb * (Nat.log 2 N + 2) ^ 5)) := by
  obtain ⟨P, hP⟩ := cleanSolveAt_of_recX rk sb
  have hq : B5 (cFinal sb) (bridgeTime (Tf sb (kNodes sb) (setA sb (kNodes sb)) (setB sb))
      (Sf sb)) :=
    (((((b5_const 18).mul b5_id).add (b5_const 78)).add
      ((b5_Tf sb _ _ _).add (((b5_const 7).mul (b5_Sf sb)).add (b5_const 34))))).mono
      (fun _ => le_rfl) le_rfl
  exact ⟨seq Bridge.up (seq P Bridge.down), fun n s =>
    (solvesInTime_of_cleanSolveAt_small (hP n s) (Sf_mono sb)).mono hq⟩

/-! ## The statement -/

/-- **Theorem 1.1.1 with exponent 5 and the constant `c`**: one RAM program solves String
Isomorphism, for every degree and alphabet, within `2^{c (log₂ N + 2)^5}` steps on inputs of
size `N`. -/
def Theorem_1_1_1_exponent5_numeral (c : ℕ) : Prop :=
  ∃ P : Program, ∀ n s : ℕ,
    SolvesInTime P (SIRel n s) (fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5))

theorem exponent5_of_numeral {c : ℕ} (h : Theorem_1_1_1_exponent5_numeral c) :
    Theorem_1_1_1_exponent5_statement :=
  ⟨c, h⟩

/-- **Theorem 1.1.1 with exponent 5 and the constant `cFinal sb`**, from the specifications of
the parameters at the explicit line-1 thresholds and the explicit costs of one node, with the
Cameron routine `Algo.masterCameron` of the cited Theorem 11.2.3. -/
theorem theorem_1_1_1_exponent5_numeral_of_bounds {p : Params} (ok : ParamsOKX p)
    (sb : StepBounds p masterCameron) :
    Theorem_1_1_1_exponent5_numeral (cFinal sb) := by
  obtain ⟨rk⟩ := recOK_of_paramsOKX ok sb masterCameron_spec.1 masterCameron_spec.2
  exact main_of_recX sb rk

end Explicit
