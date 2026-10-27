/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the local routines of a node
carrier bounded at the degree of the node. Not part of the faithful formalization.
-/
import Workspace.Explicit.NodeBounded
import Workspace.Explicit.Top.Q5
import Workspace.Algo.TopMasterHintCarrier

/-!
# Carriers bounded at the degree

For a carrier `F : MasterOps S` and a node predicate `R`, `Explicit.CarrierTN a b F R` says
that the four local routines `F.child`, `F.init`, `F.combine`, `F.finish` are bounded at the
degree with exponent 5 (`Explicit.TN _ _ 5`), on the admitted nodes (`MasterInputWF a b`) of
degree at most `n` with `R`; `F.combine` also asks that the answer handed back has size at
most `masterInputCap a b n`. No condition is put on the fold state: its size enters the
polynomial factor.

`Explicit.StateBoundsX a b K F` are the size fields of `Algo.MasterOpsCost` with the explicit
bound `2^{K (log₂ n + 2)^5}` on the fold states (for every fold state), and the bound
`masterInputCap a b n` on the answers.

Tools:

* `Explicit.master_size_poly`, `Explicit.TN.ofMaster`: a routine bounded at the size of its
  input (`TN g (fun n x => size x ≤ n) k`), read after a polynomial selector, is bounded at the
  degree of an admitted node (the node has size at most `masterInputCap a b n`);
* `Explicit.CarrierTN.ofPoly`, `.ite`, `.restrict`, and the same for `StateBoundsX`.
-/

namespace Explicit

open RAM Algo

variable {α β γ δ : Type*}

/-! ## Polynomial bounds -/

theorem polyBound_le_two_pow {T : ℕ → ℕ} (h : PolyBound T) :
    ∃ r₀ r : ℕ, ∀ n, T n ≤ 2 ^ r₀ * (n + 1) ^ r := by
  obtain ⟨c, d, hc⟩ := h
  exact ⟨c, d, fun n => (hc n).trans (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)⟩

theorem q5_of_polyBound {T : ℕ → ℕ} (h : PolyBound T) : Q5 T := by
  obtain ⟨r₀, r, h⟩ := polyBound_le_two_pow h
  exact (q5_poly r₀ r).mono h

theorem q5_masterInputCap (a b : ℕ) : Q5 (masterInputCap a b) :=
  q5_of_polyBound (polyBound_masterInputCap a b)

/-- `c (2^{r₀} (n+1)^r + 1)^d ≤ 2^{c + (r₀+1) d} (n+1)^{r d}`. -/
theorem poly_comp_le (c d r₀ r n x : ℕ) (hx : x ≤ 2 ^ r₀ * (n + 1) ^ r) :
    c * (x + 1) ^ d ≤ 2 ^ (c + (r₀ + 1) * d) * (n + 1) ^ (r * d) := by
  have h1 : 1 ≤ 2 ^ r₀ * (n + 1) ^ r :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by positivity))
  have h2 : x + 1 ≤ 2 ^ (r₀ + 1) * (n + 1) ^ r := by
    rw [pow_succ]
    nlinarith
  have h3 : (x + 1) ^ d ≤ 2 ^ ((r₀ + 1) * d) * (n + 1) ^ (r * d) := by
    calc (x + 1) ^ d ≤ (2 ^ (r₀ + 1) * (n + 1) ^ r) ^ d := Nat.pow_le_pow_left h2 d
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]
  calc c * (x + 1) ^ d ≤ 2 ^ c * (2 ^ ((r₀ + 1) * d) * (n + 1) ^ (r * d)) :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le h3
    _ = _ := by rw [pow_add, mul_assoc]

/-- **A polynomial selector at an admitted node** has output size polynomial in the degree. -/
theorem master_size_poly [Enc γ] {sel : RawMasterSI → γ} (hs : SizeBound sel) (a b : ℕ) :
    ∃ r₀ r : ℕ, ∀ n P, MasterInputWF a b P → masterDegree P ≤ n →
      Enc.size (sel P) ≤ 2 ^ r₀ * (n + 1) ^ r := by
  obtain ⟨c, d, hc⟩ := hs
  obtain ⟨r₀, r, hcap⟩ := polyBound_le_two_pow (polyBound_masterInputCap a b)
  refine ⟨c + (r₀ + 1) * d, r * d, fun n P hP hn => (hc P).trans (poly_comp_le c d r₀ r n _ ?_)⟩
  exact (hP.1.trans (mono_masterInputCap a b hn)).trans (hcap n)

/-- **A routine bounded at the size of its input, after a polynomial selector, is bounded at
the degree of an admitted node.** -/
theorem TN.ofMaster [Enc γ] [Enc β] {g : γ → β} {sel : RawMasterSI → γ} (hsel : PolyFun sel)
    {k : ℕ} (h : TN g (fun n x => Enc.size x ≤ n) k) (a b : ℕ) :
    TN (fun P => g (sel P)) (fun n P => MasterInputWF a b P ∧ masterDegree P ≤ n) k := by
  obtain ⟨r₀, r, hb⟩ := master_size_poly hsel.size a b
  exact (TN.poly_comp hsel h).scale r₀ r (fun n P hP => ⟨_, hb n P hP.1 hP.2, le_rfl⟩)

/-! ## Carriers bounded at the degree -/

/-- The precondition of the local routines at degree `n`: an admitted node of degree at most
`n` with `R`. -/
def CarrierPre (a b : ℕ) (R : RawMasterSI → Prop) (n : ℕ) (P : RawMasterSI) : Prop :=
  MasterInputWF a b P ∧ masterDegree P ≤ n ∧ R P

/-- **The local routines of a carrier, bounded at the degree with exponent 5.** -/
structure CarrierTN {S : Type} [Enc S] (a b : ℕ) (F : MasterOps S) (R : RawMasterSI → Prop) :
    Prop where
  child : TN F.child (fun n z => CarrierPre a b R n z.1) 5
  init : TN F.init (CarrierPre a b R) 5
  combine : TN F.combine
    (fun n z => CarrierPre a b R n z.1 ∧ Enc.size z.2.2.2 ≤ masterInputCap a b n) 5
  finish : TN F.finish (fun n z => CarrierPre a b R n z.1) 5

namespace CarrierTN

variable {S : Type} [Enc S] {a b : ℕ}

theorem restrict {F : MasterOps S} {R R' : RawMasterSI → Prop} (h : CarrierTN a b F R)
    (hR : ∀ P, R' P → R P) : CarrierTN a b F R' :=
  ⟨h.child.restrict fun _ _ h' => ⟨h'.1, h'.2.1, hR _ h'.2.2⟩,
    h.init.restrict fun _ _ h' => ⟨h'.1, h'.2.1, hR _ h'.2.2⟩,
    h.combine.restrict fun _ _ h' => ⟨⟨h'.1.1, h'.1.2.1, hR _ h'.1.2.2⟩, h'.2⟩,
    h.finish.restrict fun _ _ h' => ⟨h'.1, h'.2.1, hR _ h'.2.2⟩⟩

/-- A carrier whose four routines are polynomial. -/
theorem ofPoly {F : MasterOps S} (R : RawMasterSI → Prop) (hc : PolyFun F.child)
    (hi : PolyFun F.init) (hu : PolyFun F.combine) (hf : PolyFun F.finish) :
    CarrierTN a b F R :=
  ⟨TN.ofPoly hc _ 5, TN.ofPoly hi _ 5, TN.ofPoly hu _ 5, TN.ofPoly hf _ 5⟩

/-- **The branch test.** -/
theorem ite {sel : RawMasterSI → Bool} (hsel : PolyFun sel) {F G : MasterOps S}
    {R : RawMasterSI → Prop} (hF : CarrierTN a b F R) (hG : CarrierTN a b G R) :
    CarrierTN a b (MasterOps.ite sel F G) R := by
  have h1 : PolyFun (fun z : RawMasterSI × ℕ × S => sel z.1) := polyFun_fst.comp hsel
  have h2 : PolyFun (fun z : RawMasterSI × ℕ × S × RawCoset => sel z.1) := polyFun_fst.comp hsel
  have h3 : PolyFun (fun z : RawMasterSI × S => sel z.1) := polyFun_fst.comp hsel
  exact ⟨(TN.ite h1 hF.child hG.child (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq
      (fun _ => rfl),
    (TN.ite hsel hF.init hG.init (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq (fun _ => rfl),
    (TN.ite h2 hF.combine hG.combine (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq
      (fun _ => rfl),
    (TN.ite h3 hF.finish hG.finish (fun _ _ h _ => h) (fun _ _ h _ => h)).of_eq
      (fun _ => rfl)⟩

end CarrierTN

/-! ## Explicit state bounds -/

/-- **The size fields of `Algo.MasterOpsCost` with an explicit exponent**: the fold states
(from `init`, and from `combine` for every fold state) have size at most
`2^{K (log₂ n + 2)^5}` at an admitted node of degree `n`, and the answers at most
`masterInputCap a b n`, which is also below `2^{K (log₂ n + 2)^5}`. -/
def StateBoundsX {S : Type} [Enc S] (a b K : ℕ) (F : MasterOps S) : Prop :=
  (∀ P, MasterInputWF a b P → Enc.size (F.init P) ≤ 2 ^ (K * lg (masterDegree P) ^ 5)) ∧
  (∀ P j s A, MasterInputWF a b P → Enc.size A ≤ masterInputCap a b (masterDegree P) →
    Enc.size (F.combine (P, j, s, A)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5)) ∧
  (∀ P s, MasterInputWF a b P →
    Enc.size (F.finish (P, s)) ≤ masterInputCap a b (masterDegree P)) ∧
  (∀ P s, MasterInputWF a b P →
    Enc.size (F.finish (P, s)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))

namespace StateBoundsX

variable {S : Type} [Enc S] {a b : ℕ}

theorem two_pow_mono {K K' : ℕ} (h : K ≤ K') (n : ℕ) :
    2 ^ (K * lg n ^ 5) ≤ 2 ^ (K' * lg n ^ 5) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

theorem mono {F : MasterOps S} {K K' : ℕ} (h : StateBoundsX a b K F) (hK : K ≤ K') :
    StateBoundsX a b K' F :=
  ⟨fun P hP => (h.1 P hP).trans (two_pow_mono hK _),
    fun P j s A hP hA => (h.2.1 P j s A hP hA).trans (two_pow_mono hK _),
    h.2.2.1, fun P s hP => (h.2.2.2 P s hP).trans (two_pow_mono hK _)⟩

/-- **From the three `MasterOpsCost`-style bounds.** The answer bound gives the fourth
conjunct at `K` large enough for `masterInputCap a b`. -/
theorem of_three {F : MasterOps S} (K : ℕ)
    (hi : ∀ P, MasterInputWF a b P → Enc.size (F.init P) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))
    (hu : ∀ P j s A, MasterInputWF a b P → Enc.size A ≤ masterInputCap a b (masterDegree P) →
      Enc.size (F.combine (P, j, s, A)) ≤ 2 ^ (K * lg (masterDegree P) ^ 5))
    (hf : ∀ P s, MasterInputWF a b P →
      Enc.size (F.finish (P, s)) ≤ masterInputCap a b (masterDegree P)) :
    ∃ K', StateBoundsX a b K' F := by
  obtain ⟨c, hc⟩ := q5_masterInputCap a b
  refine ⟨K + c, fun P hP => (hi P hP).trans (two_pow_mono (Nat.le_add_right _ _) _),
    fun P j s A hP hA => (hu P j s A hP hA).trans (two_pow_mono (Nat.le_add_right _ _) _),
    hf, fun P s hP => ((hf P s hP).trans (hc _)).trans (two_pow_mono (Nat.le_add_left _ _) _)⟩

theorem ite {sel : RawMasterSI → Bool} {F G : MasterOps S} {K K' : ℕ}
    (hF : StateBoundsX a b K F) (hG : StateBoundsX a b K' G) :
    StateBoundsX a b (K + K') (MasterOps.ite sel F G) := by
  have hF' := hF.mono (Nat.le_add_right K K')
  have hG' := hG.mono (Nat.le_add_left K' K)
  refine ⟨fun P hP => ?_, fun P j s A hP hA => ?_, fun P s hP => ?_, fun P s hP => ?_⟩
  · show Enc.size (if sel P then F.init P else G.init P) ≤ _
    split
    · exact hF'.1 P hP
    · exact hG'.1 P hP
  · show Enc.size (if sel P then F.combine (P, j, s, A) else G.combine (P, j, s, A)) ≤ _
    split
    · exact hF'.2.1 P j s A hP hA
    · exact hG'.2.1 P j s A hP hA
  · show Enc.size (if sel P then F.finish (P, s) else G.finish (P, s)) ≤ _
    split
    · exact hF'.2.2.1 P s hP
    · exact hG'.2.2.1 P s hP
  · show Enc.size (if sel P then F.finish (P, s) else G.finish (P, s)) ≤ _
    split
    · exact hF'.2.2.2 P s hP
    · exact hG'.2.2.2 P s hP

end StateBoundsX

/-- A size bound that is a polynomial in the degree is below `2^{K (log₂ n + 2)^5}`. -/
theorem le_two_pow_of_polyBound {T : ℕ → ℕ} (h : PolyBound T) :
    ∃ K, ∀ n, T n ≤ 2 ^ (K * lg n ^ 5) :=
  q5_of_polyBound h

end Explicit
