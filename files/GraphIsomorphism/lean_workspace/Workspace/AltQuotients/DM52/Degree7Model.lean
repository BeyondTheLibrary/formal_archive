/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 7 (the models and the
lift `Babai.DM52.lift67` used to split the kernel checks of `Degree7`).
-/
import Workspace.AltQuotients.DM52.Degree5
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Primitive subgroups of small index in `A_7`

The degree-`7` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148): a primitive `G < A_7` with `|A_7 : G| < C(7,3) = 35` is
`PSL₃(2)` acting on the seven points of the Fano plane.

**Orders.**  Theorem 3.3E (with `p = 3`) makes `3` divide `h = |A : G|`, and `7 ∣ |G|`, so
`|G|` is one of `840, 420, 280, 210, 168, 140, 105, 84`.  With `N := N_S(⟨x⟩)` for a
`7`-cycle `x ∈ G`, `|A ∩ N| ∣ 21`, and the Sylow `7`-count leaves only `|G| = 168` with
`G ∩ N = A ∩ N` of order `21`, and `|G| ∈ {840, 105}` with `|G ∩ N| = 7`, where Burnside's
theorem gives a normal subgroup of order `120` or `15`, not divisible by `7`.

**Recognition.**  The Fano plane has points `ℤ/7` and lines `{i, i+1, i+3}`; with
`x ↦ x+1` and `x ↦ 2x` in `G` (after relabeling), an element `g ∈ G_0` outside
`⟨x ↦ 2x⟩` either preserves the Fano plane, or does so after conjugation by the odd
permutation `x ↦ 3x` (which normalizes `⟨x ↦ x+1, x ↦ 2x⟩`), or makes a `3`-cycle or an
element of order `5`.  The group `⟨x ↦ x + 1, x ↦ 2x, g⟩` then has order `168` by the
Sylow `7`-count again.  The model is the image `F7` of `SL₃(2)` acting on the seven nonzero
vectors of `F₂³`, numbered by the powers of a root `α` of `X³ + X + 1`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped MatrixGroups Matrix

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### Models -/

/-- `x ↦ x + 1` on `ℤ/7`. -/
def c7 : Perm (Fin 7) := ofVec ![1, 2, 3, 4, 5, 6, 0] ![6, 0, 1, 2, 3, 4, 5] (by decide)
/-- `x ↦ 2x`. -/
def mu7 : Perm (Fin 7) := ofVec ![0, 2, 4, 6, 1, 3, 5] ![0, 4, 1, 5, 2, 6, 3] (by decide)
/-- `x ↦ 3x`, odd. -/
def rho7 : Perm (Fin 7) := ofVec ![0, 3, 6, 2, 5, 1, 4] ![0, 5, 3, 1, 6, 4, 2] (by decide)

theorem mu7_conj : mu7 * c7 * mu7⁻¹ = c7 ^ (2 : ℤ) := by decide
theorem rho7_conj : rho7 * c7 * rho7⁻¹ = c7 ^ (3 : ℤ) := by decide
theorem rho7_sign : sign rho7 = -1 := by decide
theorem mu7_sign : sign mu7 = 1 := by decide
theorem rho7_mu7 : rho7 * mu7 = mu7 * rho7 := by decide
theorem orderOf_c7 : orderOf c7 = 7 := orderOf_eq_prime (by decide) (by decide)
theorem orderOf_mu7 : orderOf mu7 = 3 := orderOf_eq_prime (by decide) (by decide)
theorem cycleType_c7 : c7.cycleType = {7} :=
  cycleType_eq_of_orderOf_prime (by norm_num) orderOf_c7 (by norm_num)

/-! ### The Sylow `7`-count in `A_7` -/

/-- **Sylow `7`-count in `A_7`**: for `H ≤ A_7` with `7 ∥ |H|` there is a `7`-cycle `x ∈ H`
such that, with `N := N_S(⟨x⟩)`, `d := |H ∩ N|` divides `a := |A ∩ N|`, `a ∣ 21`,
`|H|/d ≡ 1 (mod 7)`, and `d = 7` gives Burnside's normal complement. -/
theorem sylow_seven_seven {H : Subgroup (Perm (Fin 7))} (hHA : H ≤ alternatingGroup (Fin 7))
    (h7 : 7 ∣ Nat.card H) (h49 : ¬ 7 ^ 2 ∣ Nat.card H) :
    ∃ x ∈ H, x.cycleType = {7} ∧
      Nat.card (alternatingGroup (Fin 7) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) ∣
          21 ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) ∣
        Nat.card (alternatingGroup (Fin 7) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) ∣
        Nat.card H ∧
      Nat.card H / Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) %
          7 = 1 ∧
      (Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) = 7 →
        ∃ K : Subgroup (Perm (Fin 7)), K ≤ H ∧ (K.subgroupOf H).Normal ∧
          Nat.card K * 7 = Nat.card H) := by
  obtain ⟨x, hxH, hxo, s1, s2, s3, s4, s5⟩ := sylow_normalizer_facts hHA (p := 7)
    (by norm_num) h7 h49
    (fun x _ hx => exists_odd_normalizer_of_model rho7_conj rho7_sign
      (by rw [cycleType_eq_of_orderOf_prime (by norm_num) hx (by norm_num), cycleType_c7]))
  have hxc : x.cycleType = {7} := cycleType_eq_of_orderOf_prime (by norm_num) hxo (by norm_num)
  rw [card_centralizer_of_cycleType hxc] at s1
  refine ⟨x, hxH, hxc, Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_, s2, s3, s4, s5⟩
  simpa using s1

/-- **Degree 7, the order of `G`**: a primitive `G < A_7` with `|A_7 : G| < 35` has order
`168` and contains the normalizer `A_7 ∩ N_S(⟨x⟩)` of a `7`-cycle `x ∈ G`. -/
theorem degree_seven_order {G : Subgroup (Perm (Fin 7))} (hGA : G ≤ alternatingGroup (Fin 7))
    (hG : IsPreprimitive G (Fin 7)) (hA : ¬ alternatingGroup (Fin 7) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 7)) < 35) :
    Nat.card G = 168 ∧ ∃ x ∈ G, x.cycleType = {7} ∧
      G ⊓ normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) =
        alternatingGroup (Fin 7) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
  obtain ⟨h1, -, h3, -⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  simp only [Fintype.card_fin] at h1 h3
  generalize hN : Nat.card G = N at *
  generalize G.relIndex (alternatingGroup (Fin 7)) = h at *
  have e1 : N * h = 2520 := by
    have : (7 : ℕ)! = 5040 := by decide
    rw [this] at h1; linarith
  have hN' : N = 840 ∨ N = 420 ∨ N = 280 ∨ N = 210 ∨ N = 168 ∨ N = 140 ∨ N = 105 ∨
      N = 84 := by
    obtain ⟨k, rfl⟩ := d3
    have hk : k ≤ 11 := by omega
    interval_cases k <;> omega
  obtain ⟨x, hxG, hxc, s1, s2, s3, s4, s5⟩ := sylow_seven_seven hGA
    (by rw [hN]; exact h3) (by rw [hN]; rcases hN' with h | h | h | h | h | h | h | h <;>
      rw [h] <;> norm_num)
  rw [hN] at s3 s4 s5
  generalize hNA : Nat.card (alternatingGroup (Fin 7) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (G ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) : Subgroup _) = d
    at *
  have hd7 : d ≠ 7 := by
    intro hd
    obtain ⟨K, hKG, hKn, hK⟩ := s5 hd
    have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hKne : K ≠ ⊥ := by
      rintro rfl; rw [Subgroup.card_bot] at hK
      rcases hN' with h | h | h | h | h | h | h | h <;> omega
    have := card_dvd_card_of_normal hG hKG hKn hKne
    rw [Fintype.card_fin] at this
    obtain ⟨m, hm⟩ := this
    subst hd
    rcases hN' with h | h | h | h | h | h | h | h <;> subst h <;> omega
  have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
  have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
  have hfin : d = 21 ∧ a = 21 ∧ N = 168 := by
    have hdle : d ≤ 21 := Nat.le_of_dvd (by norm_num) (s2.trans s1)
    have ha' : a = 1 ∨ a = 3 ∨ a = 7 ∨ a = 21 := by
      have := Nat.le_of_dvd (by norm_num) s1
      clear hNA s2
      interval_cases a <;> revert s1 <;> decide
    clear hNG hNA s5
    rcases hN' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases d <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := hfin
  exact ⟨rfl, x, hxG, hxc, Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hGA)
    (by rw [hNA, hNG])⟩

/-! ### The Fano plane and `SL₃(2)` -/

/-- The point `α^i` of the Fano plane as a vector of `F₂³`, with `α³ = α + 1`. -/
def enc7 : Fin 7 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![1, 0, 1]]

/-- The inverse numbering (`0 ↦ 0`, an arbitrary value). -/
def dec7 (v : Fin 3 → ZMod 2) : Fin 7 :=
  ((List.finRange 7).find? (fun i => enc7 i = v)).getD 0

theorem dec7_enc7 : ∀ i, dec7 (enc7 i) = i := by decide
theorem enc7_dec7 : ∀ v, v ≠ 0 → enc7 (dec7 v) = v := by decide
theorem enc7_ne_zero : ∀ i, enc7 i ≠ 0 := by decide

/-- A matrix acting on the numbered nonzero vectors. -/
def psi7F (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i : Fin 7) : Fin 7 := dec7 (A *ᵥ enc7 i)

theorem mulVec_ne_zero (A : SL(3, ZMod 2)) {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have : ((A⁻¹ * A : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  simpa using this

theorem psi7F_mul (A B : SL(3, ZMod 2)) (i : Fin 7) :
    psi7F ((A * B : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i =
      psi7F A (psi7F B i) := by
  simp only [psi7F, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rw [enc7_dec7 _ (mulVec_ne_zero B (enc7_ne_zero i))]

theorem psi7F_one (i : Fin 7) : psi7F 1 i = i := by
  simp [psi7F, dec7_enc7]

/-- `SL₃(2)` acting on the seven points of the Fano plane. -/
def psi7 : SL(3, ZMod 2) →* Perm (Fin 7) where
  toFun A :=
    { toFun := psi7F A
      invFun := psi7F ((A⁻¹ : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      left_inv := fun i => by
        rw [← psi7F_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]; exact psi7F_one i
      right_inv := fun i => by
        rw [← psi7F_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]; exact psi7F_one i }
  map_one' := Equiv.ext fun i => by
    show psi7F ((1 : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i = i
    rw [Matrix.SpecialLinearGroup.coe_one]; exact psi7F_one i
  map_mul' A B := Equiv.ext fun i => by
    show psi7F ((A * B : SL(3, ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i =
      psi7F (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (psi7F (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i)
    exact psi7F_mul A B i

theorem psi7_apply (A : SL(3, ZMod 2)) (i : Fin 7) : psi7 A i = psi7F A i := rfl

/-- The model of `PSL₃(2)` acting on the Fano plane. -/
def F7 : Subgroup (Perm (Fin 7)) := psi7.range

set_option maxRecDepth 100000 in
theorem psi7F_eq_id : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), (∀ i, psi7F A i = i) → A = 1 := by
  decide +kernel

theorem psi7_injective : Function.Injective psi7 := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker] at hA
  rw [Subgroup.mem_bot]
  exact Subtype.ext (psi7F_eq_id _ (fun i => by
    rw [← psi7_apply, hA]; rfl))

set_option maxRecDepth 100000 in
theorem card_SL32 : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_F7 : Nat.card F7 = 168 := by
  rw [F7, ← Nat.card_congr (MonoidHom.ofInjective psi7_injective).toEquiv, card_SL32]

theorem center_SL32 : center SL(3, ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hA⟩ := hA
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    fin_cases r
    · exact absurd hr (by decide)
    · rfl
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA, hr1]
  simp [Matrix.one_apply]

/-- `F7 ≃* PSL₃(2)`. -/
noncomputable def F7_mulEquiv : F7 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  ((QuotientGroup.quotientMulEquivOfEq
    (by rw [center_SL32, (MonoidHom.ker_eq_bot_iff _).mpr psi7_injective])).symm.trans
    (QuotientGroup.quotientKerEquivRange psi7)).symm

/-- The Fano plane is preserved: the lines `{i, i+1, i+3}` go to lines, i.e. to triples of
vectors with sum `0`. -/
def IsFano (g : Perm (Fin 7)) : Prop :=
  ∀ i : Fin 7, enc7 (g i) + enc7 (g (i + 1)) + enc7 (g (i + 3)) = 0

instance : DecidablePred IsFano := fun g => by unfold IsFano; infer_instance

/-- The matrix with columns the images of the basis vectors. -/
def fanoMatrix (g : Perm (Fin 7)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun r c => enc7 (g (dec7 (Pi.single c 1))) r

/-- Words in `[c7, mu7, g, g⁻¹]` (indices `0, 1, 2, 3`). -/
def words7 : List (List ℕ) :=
  [[2], [1, 2], [1, 2, 1, 3], [0, 2, 0, 2, 2], [0, 2, 0, 2], [0, 0, 0, 2], [0, 1, 2], [0, 2, 1]]

/-! ### Reduction of the kernel checks to `Perm (Fin 6)` -/

/-- The points `1, …, 6` of `Fin 7`. -/
def P67 (i : Fin 7) : Prop := 1 ≤ (i : ℕ)

instance : DecidablePred P67 := fun i => by unfold P67; infer_instance

/-- `Fin 6 ≃ {1, …, 6} ⊆ Fin 7`, `j ↦ j + 1`. -/
def e67 : Fin 6 ≃ {i : Fin 7 // P67 i} where
  toFun j := ⟨⟨j + 1, by omega⟩, by simp only [P67]; omega⟩
  invFun x := ⟨x.1 - 1, by have := x.2; simp only [P67] at this; omega⟩
  left_inv j := by ext; simp
  right_inv x := by
    have := x.2
    simp only [P67] at this
    ext; simp; omega

/-- A permutation of `{1, …, 6}`, extended by the identity on `0`. -/
def lift67 (p : Perm (Fin 6)) : Perm (Fin 7) := ofSubtype (e67.permCongr p)

/-- Every permutation of `Fin 7` fixing `0` is some `lift67 p`. -/
theorem exists_lift67 {g : Perm (Fin 7)} (h0 : g 0 = 0) :
    ∃ p : Perm (Fin 6), lift67 p = g := by
  have key : ∀ x : Fin 7, P67 x ↔ x ≠ 0 := by decide
  have hP : ∀ x, P67 x ↔ P67 (g x) := by
    intro x
    rw [key, key]
    constructor
    · intro hx h; exact hx (g.injective (h.trans h0.symm))
    · intro hx h; exact hx (h ▸ h0)
  refine ⟨e67.symm.permCongr (g.subtypePerm (fun x => (hP x).symm)), ?_⟩
  rw [lift67, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]
  apply ofSubtype_subtypePerm
  intro x hx
  rw [key]
  exact fun h => hx (h ▸ h0)

end Babai.DM52
