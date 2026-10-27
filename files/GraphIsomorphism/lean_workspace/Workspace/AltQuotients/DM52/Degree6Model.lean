/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 6 (the models, used by
the kernel checks of `Degree6Norm`).
-/
import Workspace.AltQuotients.DM52.Degree5
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Primitive subgroups of small index in `A_6`

The degree-`6` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148): a primitive `G < A_6` with `|A_6 : G| < C(6,3) = 20` is
`PSL₂(5)` acting on the projective line over `F₅`; and for [DiM, Thm. 5.2B], a subgroup
`G ≤ S_6` of order `120` whose even part is that group is `PGL₂(5)`.

**Orders.**  Theorem 3.3E (with `p = 3`) makes `3` divide `h = |A : G|`, so `|G|` is one of
`120, 60, 30, 24` (it is divisible by `6`).  The Sylow `5`-count excludes `120` and, for
`60`, puts the normalizer `A ∩ N_S(⟨x⟩)` of a `5`-cycle `x` into `G`.  For `|G| = 30` the
Sylow `3`-count (the elements of order `3` are products of two `3`-cycles, by Jordan's
theorem) gives, by Burnside's theorem, a normal subgroup of order `10`, which is not
divisible by `6`.  For `|G| = 24` a point stabilizer, of order `4`, lies properly inside a
Sylow `2`-subgroup of order `8`, against its maximality (the group is primitive).

**Recognition.**  The model is the image `C6` of `SL₂(5)` acting by Möbius transformations
on `P¹(F₅) = {0,…,4,∞}` (`∞ ↦ 5`).  After relabeling, `G` contains `x ↦ x + 1` and
`x ↦ -x`, and some `g` with `g(∞) = 0`; every even such `g` lies in `C6` or produces a
`3`-cycle, and `⟨x ↦ x + 1, x ↦ -x, g⟩` has order at least `6 · 10 = 60`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped MatrixGroups

/-! ### Models -/

/-- `x ↦ x + 1` on `ℤ/5`, fixing `∞ = 5`. -/
def c6 : Perm (Fin 6) := ofVec ![1, 2, 3, 4, 0, 5] ![4, 0, 1, 2, 3, 5] (by decide)
/-- `x ↦ 2x`, an odd permutation normalizing `⟨c6⟩`. -/
def mul6 : Perm (Fin 6) := ofVec ![0, 2, 4, 1, 3, 5] ![0, 3, 1, 4, 2, 5] (by decide)
/-- `x ↦ -x`. -/
def nu6 : Perm (Fin 6) := ofVec ![0, 4, 3, 2, 1, 5] ![0, 4, 3, 2, 1, 5] (by decide)
/-- `(0 1 2)(3 4 5)`. -/
def t33 : Perm (Fin 6) := ofVec ![1, 2, 0, 4, 5, 3] ![2, 0, 1, 5, 3, 4] (by decide)
/-- `(0 3)(1 4)(2 5)`, an odd permutation commuting with `t33`. -/
def swp6 : Perm (Fin 6) := ofVec ![3, 4, 5, 0, 1, 2] ![3, 4, 5, 0, 1, 2] (by decide)

/-- `x ↦ -1/x`, an element of `C6` moving `∞`. -/
def t6 : Perm (Fin 6) := ofVec ![5, 4, 2, 3, 1, 0] ![5, 4, 2, 3, 1, 0] (by decide)

theorem mul6_conj : mul6 * c6 * mul6⁻¹ = c6 ^ (2 : ℤ) := by decide
theorem mul6_sign : sign mul6 = -1 := by decide
theorem nu6_conj : nu6 * c6 * nu6⁻¹ = c6 ^ (-1 : ℤ) := by decide
theorem nu6_sign : sign nu6 = 1 := by decide
theorem swp6_conj : swp6 * t33 * swp6⁻¹ = t33 ^ (1 : ℤ) := by decide
theorem swp6_sign : sign swp6 = -1 := by decide
theorem orderOf_c6 : orderOf c6 = 5 := orderOf_eq_prime (by decide) (by decide)
theorem orderOf_nu6 : orderOf nu6 = 2 := orderOf_eq_prime (by decide) (by decide)
theorem orderOf_t33 : orderOf t33 = 3 := orderOf_eq_prime (by decide) (by decide)
theorem cycleType_c6 : c6.cycleType = {5} :=
  cycleType_eq_of_orderOf_prime Nat.prime_five orderOf_c6 (by norm_num)

/-- An element of order `3` of `Sym(6)` that is not a `3`-cycle has cycle type `3²`. -/
theorem cycleType_of_orderOf_three {x : Perm (Fin 6)} (hx : orderOf x = 3)
    (hxc : x.support.card ≠ 3) : x.cycleType = Multiset.replicate 2 3 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (hx ▸ Nat.prime_three)
  rw [hx] at hk
  have hsum : x.cycleType.sum ≤ 6 := by
    rw [sum_cycleType]; exact (Finset.card_le_univ _).trans (by simp)
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with rfl | rfl
  · exfalso; apply hxc; rw [← sum_cycleType, hk]; simp
  · exact hk

theorem cycleType_t33 : t33.cycleType = Multiset.replicate 2 3 :=
  cycleType_of_orderOf_three orderOf_t33 (by decide)

theorem card_centralizer_three_three {x : Perm (Fin 6)}
    (hx : x.cycleType = Multiset.replicate 2 3) :
    Nat.card (centralizer ({x} : Set (Perm (Fin 6)))) = 18 := by
  rw [nat_card_centralizer, hx]
  decide

/-! ### The order of `G` -/

/-- **Degree 6, the order of `G`** ([DiM, proof of Thm. 5.2A], the examination of the
primitive groups of degree `6`): a primitive `G < A_6` with `|A_6 : G| < 20` has order `60`,
and contains the normalizer `A_6 ∩ N_S(⟨x⟩)` of a `5`-cycle `x ∈ G`. -/
theorem degree_six_order {G : Subgroup (Perm (Fin 6))} (hGA : G ≤ alternatingGroup (Fin 6))
    (hG : IsPreprimitive G (Fin 6)) (hA : ¬ alternatingGroup (Fin 6) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 6)) < 20) :
    Nat.card G = 60 ∧ ∃ x ∈ G, x.cycleType = {5} ∧
      G ⊓ normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) =
        alternatingGroup (Fin 6) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
  obtain ⟨h1, -, h3, -⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  simp only [Fintype.card_fin] at h1 h3
  have hno3 : ∀ x ∈ G, x.support.card ≠ 3 := fun x hx => support_card_ne_three hG hA hx
  generalize hN : Nat.card G = N at *
  generalize G.relIndex (alternatingGroup (Fin 6)) = h at *
  have e1 : N * h = 360 := by
    have : (6 : ℕ)! = 720 := by decide
    rw [this] at h1; linarith
  have hN' : N = 120 ∨ N = 60 ∨ N = 30 ∨ N = 24 := by
    obtain ⟨k, rfl⟩ := d3
    have hk : k ≤ 6 := by omega
    interval_cases k <;> omega
  -- `|G| = 30`: the Sylow `3`-count and Burnside's theorem
  have n30 : N ≠ 30 := by
    intro h30
    obtain ⟨x, hxG, hxo, s1, s2, s3, s4, s5⟩ := sylow_normalizer_facts hGA (p := 3)
      Nat.prime_three (by rw [hN, h30]; norm_num) (by rw [hN, h30]; norm_num)
      (fun x hx hxo => exists_odd_normalizer_of_model swp6_conj swp6_sign
        (by rw [cycleType_of_orderOf_three hxo (hno3 x hx), cycleType_t33]))
    rw [card_centralizer_three_three (cycleType_of_orderOf_three hxo (hno3 x hxG))] at s1
    rw [hN, h30] at s3 s4 s5
    generalize hNA : Nat.card (alternatingGroup (Fin 6) ⊓
      normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) : Subgroup _) = a
      at *
    generalize hNG : Nat.card (G ⊓
      normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) : Subgroup _) = d
      at *
    have hd3 : d ≠ 3 := by
      intro hd
      obtain ⟨K, hKG, hKn, hK⟩ := s5 hd
      have hK10 : Nat.card K = 10 := by omega
      have hKne : K ≠ ⊥ := by rintro rfl; rw [Subgroup.card_bot] at hK10; omega
      have := card_dvd_card_of_normal hG hKG hKn hKne
      rw [hK10, Fintype.card_fin] at this
      omega
    have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
    have hdle : d ≤ 30 := Nat.le_of_dvd (by norm_num) s3
    have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
    have hale : a ≤ 18 := by
      have : 2 * a ∣ 2 * 18 := by simpa using s1
      exact Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mul_dvd_mul_left (by norm_num) this)
    clear s5 hNG hNA
    interval_cases d <;> omega
  -- `|G| = 24`: a point stabilizer is not maximal
  have n24 : N ≠ 24 := by
    intro h24
    haveI := hG
    have hcoat := (isCoatom_stabilizer_iff_preprimitive (G := G) (X := Fin 6) 0).mpr hG
    set S := stabilizer G (0 : Fin 6)
    have hSi : S.index = 6 := by
      rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hS : Nat.card S = 4 := by
      have := S.card_mul_index; rw [hSi, hN, h24] at this; omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ :=
      (IsPGroup.of_card (p := 2) (n := 2) (by rw [hS]; norm_num) : IsPGroup 2 S).exists_le_sylow
    have hne : S ≠ P := by
      intro h
      have := P.not_dvd_index
      rw [← h, hSi] at this
      exact this (by norm_num)
    have htop := hcoat.2 P (lt_of_le_of_ne hP hne)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [htop, Subgroup.card_top, hN, h24] at hk
    have h3k : 3 ∣ 2 ^ k := hk ▸ (by norm_num)
    have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h3k)
    omega
  -- `|G| = 120` or `60`: the Sylow `5`-count
  have h5 : N = 120 ∨ N = 60 := by omega
  obtain ⟨x, hxG, hxo, s1, s2, s3, s4, -⟩ := sylow_normalizer_facts hGA (p := 5)
    Nat.prime_five (by rw [hN]; rcases h5 with h5 | h5 <;> rw [h5] <;> norm_num)
    (by rw [hN]; rcases h5 with h5 | h5 <;> rw [h5] <;> norm_num)
    (fun x _ hx => exists_odd_normalizer_of_model mul6_conj mul6_sign
      (by rw [cycleType_eq_of_orderOf_prime Nat.prime_five hx (by norm_num), cycleType_c6]))
  have hxc : x.cycleType = {5} := cycleType_eq_of_orderOf_prime Nat.prime_five hxo (by norm_num)
  rw [card_centralizer_of_cycleType hxc] at s1
  rw [hN] at s3 s4
  have hs1 : (6 - 5)! * 5 * (5 - 1) = 20 := by decide
  rw [hs1] at s1
  generalize hNA : Nat.card (alternatingGroup (Fin 6) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (G ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))) : Subgroup _) = d
    at *
  have ha : a ∣ 10 := by
    have : 2 * a ∣ 2 * 10 := by simpa using s1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
  have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
  have hfin : d = 10 ∧ a = 10 ∧ N = 60 := by
    have hdle : d ≤ 10 := Nat.le_of_dvd (by norm_num) (s2.trans ha)
    have hale : a ≤ 10 := Nat.le_of_dvd (by norm_num) ha
    clear hNG hNA
    rcases h5 with rfl | rfl <;> interval_cases d <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := hfin
  exact ⟨rfl, x, hxG, hxc, Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hGA)
    (by rw [hNA, hNG])⟩

/-! ### The projective line over `F₅` -/

/-- The numbering `k ↦ k`, `∞ ↦ 5` of `P¹(F₅) = F₅ ∪ {∞}`. -/
def toFin6 (x : OnePoint (ZMod 5)) : Fin 6 :=
  x.elim 5 (fun k => ⟨k.val, (ZMod.val_lt k).trans (by norm_num)⟩)

/-- The inverse numbering. -/
def ofFin6 (i : Fin 6) : OnePoint (ZMod 5) :=
  if (i : ℕ) < 5 then (((i : ℕ) : ZMod 5) : OnePoint (ZMod 5)) else OnePoint.infty

instance : DecidableEq (OnePoint (ZMod 5)) := inferInstanceAs (DecidableEq (Option (ZMod 5)))

/-- `P¹(F₅) ≃ Fin 6`. -/
def e6 : OnePoint (ZMod 5) ≃ Fin 6 where
  toFun := toFin6
  invFun := ofFin6
  left_inv := by intro x; revert x; decide
  right_inv := by intro i; revert i; decide

/-- Inversion in `F₅`, by a table (so that the kernel evaluates it fast). -/
def inv5 (y : ZMod 5) : ZMod 5 := ![0, 1, 3, 2, 4] y

theorem inv_eq_inv5 : ∀ y : ZMod 5, y⁻¹ = inv5 y := by decide

/-- The Möbius transformation `x ↦ (a x + b)/(c x + d)` of `P¹(F₅)`. -/
def mobO (a b c d : ZMod 5) (x : OnePoint (ZMod 5)) : OnePoint (ZMod 5) :=
  x.elim (if c = 0 then OnePoint.infty else (((a * inv5 c : ZMod 5)) : OnePoint (ZMod 5)))
    (fun k => if c * k + d = 0 then OnePoint.infty
      else (((a * k + b) * inv5 (c * k + d) : ZMod 5) : OnePoint (ZMod 5)))

/-- The Möbius transformation on the numbered points. -/
def mobF (a b c d : ZMod 5) (i : Fin 6) : Fin 6 := toFin6 (mobO a b c d (ofFin6 i))

theorem smul_eq_mobO (g : GL (Fin 2) (ZMod 5)) (x : OnePoint (ZMod 5)) :
    g • x = mobO (g 0 0) (g 0 1) (g 1 0) (g 1 1) x := by
  induction x using OnePoint.rec with
  | infty => rw [OnePoint.smul_infty_eq_ite]; simp [mobO, div_eq_mul_inv, inv_eq_inv5]
  | coe k => rw [OnePoint.smul_some_eq_ite]; simp [mobO, div_eq_mul_inv, inv_eq_inv5]

/-- `GL₂(5)` acting on the six points of `P¹(F₅)`. -/
noncomputable def psiGL : GL (Fin 2) (ZMod 5) →* Perm (Fin 6) :=
  e6.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (GL (Fin 2) (ZMod 5)) (OnePoint (ZMod 5)))

theorem psiGL_apply (g : GL (Fin 2) (ZMod 5)) (i : Fin 6) :
    psiGL g i = mobF (g 0 0) (g 0 1) (g 1 0) (g 1 1) i := by
  simp only [psiGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    Equiv.permCongrHom_coe, Equiv.permCongr_apply, MulAction.toPermHom_apply,
    MulAction.toPerm_apply, mobF, smul_eq_mobO]
  rfl

/-- `SL₂(5)` acting on `P¹(F₅)`. -/
noncomputable def psiSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* Perm (Fin 6) :=
  psiGL.comp Matrix.SpecialLinearGroup.toGL

theorem psiSL_apply (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) (i : Fin 6) :
    psiSL A i = mobF (A 0 0) (A 0 1) (A 1 0) (A 1 1) i := by
  rw [psiSL, MonoidHom.comp_apply, psiGL_apply]
  rfl

/-- The model of `PSL₂(5)` in its action on six points. -/
noncomputable def C6 : Subgroup (Perm (Fin 6)) := psiSL.range

/-- The model of `PGL₂(5)` in its action on six points. -/
noncomputable def PGL6 : Subgroup (Perm (Fin 6)) := psiGL.range

/-! ### The elements of the models -/

/-- The `60` elements of `C6`, each with a matrix of `SL₂(5)` inducing it. -/
def C6data : List ((ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) × (Fin 6 → Fin 6)) := [
  ((1, 0, 0, 1), ![0, 1, 2, 3, 4, 5]),
  ((2, 0, 4, 3), ![0, 1, 4, 5, 2, 3]),
  ((2, 0, 3, 3), ![0, 2, 1, 3, 5, 4]),
  ((1, 0, 2, 1), ![0, 2, 5, 4, 1, 3]),
  ((1, 0, 1, 1), ![0, 3, 4, 2, 5, 1]),
  ((2, 0, 1, 3), ![0, 3, 5, 1, 4, 2]),
  ((1, 0, 3, 1), ![0, 4, 1, 5, 3, 2]),
  ((2, 0, 0, 3), ![0, 4, 3, 2, 1, 5]),
  ((2, 0, 2, 3), ![0, 5, 2, 4, 3, 1]),
  ((1, 0, 4, 1), ![0, 5, 3, 1, 2, 4]),
  ((1, 4, 2, 4), ![1, 0, 2, 5, 4, 3]),
  ((2, 3, 0, 3), ![1, 0, 4, 3, 2, 5]),
  ((1, 3, 4, 3), ![1, 2, 0, 5, 3, 4]),
  ((1, 1, 0, 1), ![1, 2, 3, 4, 0, 5]),
  ((0, 2, 2, 2), ![1, 3, 2, 4, 5, 0]),
  ((2, 4, 3, 4), ![1, 3, 5, 0, 2, 4]),
  ((2, 1, 1, 1), ![1, 4, 0, 3, 5, 2]),
  ((2, 2, 4, 2), ![1, 4, 5, 2, 0, 3]),
  ((1, 2, 3, 2), ![1, 5, 3, 0, 4, 2]),
  ((0, 1, 4, 1), ![1, 5, 4, 2, 3, 0]),
  ((2, 3, 4, 4), ![2, 0, 1, 4, 5, 3]),
  ((1, 4, 4, 2), ![2, 0, 5, 3, 1, 4]),
  ((2, 1, 0, 3), ![2, 1, 0, 4, 3, 5]),
  ((2, 2, 3, 1), ![2, 1, 3, 5, 0, 4]),
  ((0, 1, 4, 3), ![2, 3, 1, 5, 4, 0]),
  ((1, 2, 0, 1), ![2, 3, 4, 0, 1, 5]),
  ((2, 4, 2, 2), ![2, 4, 3, 0, 5, 1]),
  ((0, 2, 2, 1), ![2, 4, 5, 1, 3, 0]),
  ((1, 3, 1, 4), ![2, 5, 0, 3, 4, 1]),
  ((1, 1, 2, 3), ![2, 5, 4, 1, 0, 3]),
  ((1, 4, 3, 3), ![3, 0, 4, 1, 5, 2]),
  ((2, 3, 2, 1), ![3, 0, 5, 2, 4, 1]),
  ((1, 2, 4, 4), ![3, 1, 2, 0, 5, 4]),
  ((0, 1, 4, 2), ![3, 1, 5, 4, 2, 0]),
  ((2, 4, 0, 3), ![3, 2, 1, 0, 4, 5]),
  ((0, 2, 2, 4), ![3, 2, 4, 5, 1, 0]),
  ((1, 3, 0, 1), ![3, 4, 0, 1, 2, 5]),
  ((1, 1, 1, 2), ![3, 4, 2, 5, 0, 1]),
  ((2, 1, 3, 2), ![3, 5, 0, 2, 1, 4]),
  ((2, 2, 1, 4), ![3, 5, 1, 4, 0, 2]),
  ((1, 4, 0, 1), ![4, 0, 1, 2, 3, 5]),
  ((2, 3, 1, 2), ![4, 0, 3, 5, 1, 2]),
  ((1, 3, 2, 2), ![4, 1, 0, 2, 5, 3]),
  ((1, 1, 3, 4), ![4, 1, 5, 3, 0, 2]),
  ((0, 1, 4, 4), ![4, 2, 3, 1, 5, 0]),
  ((1, 2, 1, 3), ![4, 2, 5, 0, 3, 1]),
  ((2, 1, 2, 4), ![4, 3, 0, 5, 2, 1]),
  ((2, 2, 0, 3), ![4, 3, 2, 1, 0, 5]),
  ((0, 2, 2, 3), ![4, 5, 1, 3, 2, 0]),
  ((2, 4, 4, 1), ![4, 5, 2, 0, 1, 3]),
  ((2, 3, 3, 0), ![5, 0, 2, 1, 3, 4]),
  ((1, 4, 1, 0), ![5, 0, 3, 4, 2, 1]),
  ((0, 2, 2, 0), ![5, 1, 3, 2, 4, 0]),
  ((2, 4, 1, 0), ![5, 1, 4, 0, 3, 2]),
  ((2, 1, 4, 0), ![5, 2, 0, 1, 4, 3]),
  ((2, 2, 2, 0), ![5, 2, 4, 3, 0, 1]),
  ((1, 3, 3, 0), ![5, 3, 0, 4, 1, 2]),
  ((1, 1, 4, 0), ![5, 3, 1, 2, 0, 4]),
  ((1, 2, 2, 0), ![5, 4, 1, 0, 2, 3]),
  ((0, 1, 4, 0), ![5, 4, 2, 3, 1, 0])]


/-- The `120` elements of `PGL6`, each with a matrix of `GL₂(5)` inducing it. -/
def PGL6data : List ((ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) × (Fin 6 → Fin 6)) := [
  ((1, 0, 0, 1), ![0, 1, 2, 3, 4, 5]),
  ((1, 0, 3, 3), ![0, 1, 3, 4, 5, 2]),
  ((1, 0, 2, 4), ![0, 1, 4, 5, 2, 3]),
  ((1, 0, 4, 2), ![0, 1, 5, 2, 3, 4]),
  ((1, 0, 4, 4), ![0, 2, 1, 3, 5, 4]),
  ((1, 0, 1, 2), ![0, 2, 3, 5, 4, 1]),
  ((1, 0, 0, 3), ![0, 2, 4, 1, 3, 5]),
  ((1, 0, 2, 1), ![0, 2, 5, 4, 1, 3]),
  ((1, 0, 0, 2), ![0, 3, 1, 4, 2, 5]),
  ((1, 0, 4, 3), ![0, 3, 2, 5, 1, 4]),
  ((1, 0, 1, 1), ![0, 3, 4, 2, 5, 1]),
  ((1, 0, 3, 4), ![0, 3, 5, 1, 4, 2]),
  ((1, 0, 3, 1), ![0, 4, 1, 5, 3, 2]),
  ((1, 0, 2, 2), ![0, 4, 2, 1, 5, 3]),
  ((1, 0, 0, 4), ![0, 4, 3, 2, 1, 5]),
  ((1, 0, 1, 3), ![0, 4, 5, 3, 2, 1]),
  ((1, 0, 2, 3), ![0, 5, 1, 2, 4, 3]),
  ((1, 0, 1, 4), ![0, 5, 2, 4, 3, 1]),
  ((1, 0, 4, 1), ![0, 5, 3, 1, 2, 4]),
  ((1, 0, 3, 2), ![0, 5, 4, 3, 1, 2]),
  ((1, 4, 2, 4), ![1, 0, 2, 5, 4, 3]),
  ((1, 4, 4, 4), ![1, 0, 3, 2, 5, 4]),
  ((1, 4, 0, 4), ![1, 0, 4, 3, 2, 5]),
  ((1, 4, 3, 4), ![1, 0, 5, 4, 3, 2]),
  ((1, 3, 4, 3), ![1, 2, 0, 5, 3, 4]),
  ((1, 1, 0, 1), ![1, 2, 3, 4, 0, 5]),
  ((1, 2, 2, 2), ![1, 2, 4, 0, 5, 3]),
  ((0, 1, 2, 1), ![1, 2, 5, 3, 4, 0]),
  ((1, 3, 0, 3), ![1, 3, 0, 2, 4, 5]),
  ((0, 1, 1, 1), ![1, 3, 2, 4, 5, 0]),
  ((1, 1, 3, 1), ![1, 3, 4, 5, 0, 2]),
  ((1, 2, 4, 2), ![1, 3, 5, 0, 2, 4]),
  ((1, 3, 3, 3), ![1, 4, 0, 3, 5, 2]),
  ((1, 2, 0, 2), ![1, 4, 2, 0, 3, 5]),
  ((0, 1, 3, 1), ![1, 4, 3, 5, 2, 0]),
  ((1, 1, 2, 1), ![1, 4, 5, 2, 0, 3]),
  ((1, 3, 2, 3), ![1, 5, 0, 4, 2, 3]),
  ((1, 1, 4, 1), ![1, 5, 2, 3, 0, 4]),
  ((1, 2, 3, 2), ![1, 5, 3, 0, 4, 2]),
  ((0, 1, 4, 1), ![1, 5, 4, 2, 3, 0]),
  ((1, 4, 2, 2), ![2, 0, 1, 4, 5, 3]),
  ((1, 4, 0, 2), ![2, 0, 3, 1, 4, 5]),
  ((1, 4, 1, 2), ![2, 0, 4, 5, 3, 1]),
  ((1, 4, 4, 2), ![2, 0, 5, 3, 1, 4]),
  ((1, 3, 0, 4), ![2, 1, 0, 4, 3, 5]),
  ((1, 1, 4, 3), ![2, 1, 3, 5, 0, 4]),
  ((0, 1, 3, 3), ![2, 1, 4, 3, 5, 0]),
  ((1, 2, 2, 1), ![2, 1, 5, 0, 4, 3]),
  ((1, 3, 4, 4), ![2, 3, 0, 1, 5, 4]),
  ((0, 1, 4, 3), ![2, 3, 1, 5, 4, 0]),
  ((1, 2, 0, 1), ![2, 3, 4, 0, 1, 5]),
  ((1, 1, 1, 3), ![2, 3, 5, 4, 0, 1]),
  ((1, 3, 2, 4), ![2, 4, 0, 5, 1, 3]),
  ((1, 1, 0, 3), ![2, 4, 1, 3, 0, 5]),
  ((1, 2, 1, 1), ![2, 4, 3, 0, 5, 1]),
  ((0, 1, 1, 3), ![2, 4, 5, 1, 3, 0]),
  ((1, 3, 1, 4), ![2, 5, 0, 3, 4, 1]),
  ((1, 2, 4, 1), ![2, 5, 1, 0, 3, 4]),
  ((0, 1, 2, 3), ![2, 5, 3, 4, 1, 0]),
  ((1, 1, 2, 3), ![2, 5, 4, 1, 0, 3]),
  ((1, 4, 4, 3), ![3, 0, 1, 5, 2, 4]),
  ((1, 4, 0, 3), ![3, 0, 2, 4, 1, 5]),
  ((1, 4, 3, 3), ![3, 0, 4, 1, 5, 2]),
  ((1, 4, 1, 3), ![3, 0, 5, 2, 4, 1]),
  ((1, 3, 3, 1), ![3, 1, 0, 5, 4, 2]),
  ((1, 2, 4, 4), ![3, 1, 2, 0, 5, 4]),
  ((1, 1, 0, 2), ![3, 1, 4, 2, 0, 5]),
  ((0, 1, 4, 2), ![3, 1, 5, 4, 2, 0]),
  ((1, 3, 1, 1), ![3, 2, 0, 4, 5, 1]),
  ((1, 2, 0, 4), ![3, 2, 1, 0, 4, 5]),
  ((0, 1, 1, 2), ![3, 2, 4, 5, 1, 0]),
  ((1, 1, 4, 2), ![3, 2, 5, 1, 0, 4]),
  ((1, 3, 0, 1), ![3, 4, 0, 1, 2, 5]),
  ((0, 1, 2, 2), ![3, 4, 1, 2, 5, 0]),
  ((1, 1, 1, 2), ![3, 4, 2, 5, 0, 1]),
  ((1, 2, 3, 4), ![3, 4, 5, 0, 1, 2]),
  ((1, 3, 4, 1), ![3, 5, 0, 2, 1, 4]),
  ((1, 1, 3, 2), ![3, 5, 1, 4, 0, 2]),
  ((0, 1, 3, 2), ![3, 5, 2, 1, 4, 0]),
  ((1, 2, 1, 4), ![3, 5, 4, 0, 2, 1]),
  ((1, 4, 0, 1), ![4, 0, 1, 2, 3, 5]),
  ((1, 4, 1, 1), ![4, 0, 2, 3, 5, 1]),
  ((1, 4, 3, 1), ![4, 0, 3, 5, 1, 2]),
  ((1, 4, 2, 1), ![4, 0, 5, 1, 2, 3]),
  ((1, 3, 2, 2), ![4, 1, 0, 2, 5, 3]),
  ((0, 1, 2, 4), ![4, 1, 2, 5, 3, 0]),
  ((1, 2, 0, 3), ![4, 1, 3, 0, 2, 5]),
  ((1, 1, 3, 4), ![4, 1, 5, 3, 0, 2]),
  ((1, 3, 0, 2), ![4, 2, 0, 3, 1, 5]),
  ((1, 1, 2, 4), ![4, 2, 1, 5, 0, 3]),
  ((0, 1, 4, 4), ![4, 2, 3, 1, 5, 0]),
  ((1, 2, 1, 3), ![4, 2, 5, 0, 3, 1]),
  ((1, 3, 1, 2), ![4, 3, 0, 5, 2, 1]),
  ((1, 2, 3, 3), ![4, 3, 1, 0, 5, 2]),
  ((1, 1, 0, 4), ![4, 3, 2, 1, 0, 5]),
  ((0, 1, 3, 4), ![4, 3, 5, 2, 1, 0]),
  ((1, 3, 3, 2), ![4, 5, 0, 1, 3, 2]),
  ((0, 1, 1, 4), ![4, 5, 1, 3, 2, 0]),
  ((1, 2, 2, 3), ![4, 5, 2, 0, 1, 3]),
  ((1, 1, 1, 4), ![4, 5, 3, 2, 0, 1]),
  ((1, 4, 3, 0), ![5, 0, 1, 3, 4, 2]),
  ((1, 4, 4, 0), ![5, 0, 2, 1, 3, 4]),
  ((1, 4, 1, 0), ![5, 0, 3, 4, 2, 1]),
  ((1, 4, 2, 0), ![5, 0, 4, 2, 1, 3]),
  ((1, 3, 4, 0), ![5, 1, 0, 3, 2, 4]),
  ((1, 1, 2, 0), ![5, 1, 2, 4, 0, 3]),
  ((0, 1, 1, 0), ![5, 1, 3, 2, 4, 0]),
  ((1, 2, 3, 0), ![5, 1, 4, 0, 3, 2]),
  ((1, 3, 2, 0), ![5, 2, 0, 1, 4, 3]),
  ((0, 1, 3, 0), ![5, 2, 1, 4, 3, 0]),
  ((1, 2, 4, 0), ![5, 2, 3, 0, 1, 4]),
  ((1, 1, 1, 0), ![5, 2, 4, 3, 0, 1]),
  ((1, 3, 3, 0), ![5, 3, 0, 4, 1, 2]),
  ((1, 1, 4, 0), ![5, 3, 1, 2, 0, 4]),
  ((1, 2, 1, 0), ![5, 3, 2, 0, 4, 1]),
  ((0, 1, 2, 0), ![5, 3, 4, 1, 2, 0]),
  ((1, 3, 1, 0), ![5, 4, 0, 2, 3, 1]),
  ((1, 2, 2, 0), ![5, 4, 1, 0, 2, 3]),
  ((0, 1, 4, 0), ![5, 4, 2, 3, 1, 0]),
  ((1, 1, 3, 0), ![5, 4, 3, 1, 0, 2])]

/-- `g` is one of the listed elements of `C6`. -/
def InC6 (g : Perm (Fin 6)) : Prop := ∃ e ∈ C6data, ∀ i, g i = e.2 i

/- The decision procedures run over the lists, not over the (large) type of entries. -/
instance : DecidablePred InC6 := fun g =>
  decidable_of_iff (C6data.any fun e => decide (∀ i, g i = e.2 i)) (by simp [InC6])

/-- `g` is one of the listed elements of `PGL6`. -/
def InPGL6 (g : Perm (Fin 6)) : Prop := ∃ e ∈ PGL6data, ∀ i, g i = e.2 i

instance : DecidablePred InPGL6 := fun g =>
  decidable_of_iff (PGL6data.any fun e => decide (∀ i, g i = e.2 i)) (by simp [InPGL6])

end Babai.DM52
