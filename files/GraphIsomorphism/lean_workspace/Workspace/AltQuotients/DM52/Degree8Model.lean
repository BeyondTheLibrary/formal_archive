/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 8 (the models and the
lift `Babai.DM52.lift68` used to split the kernel checks of `Degree8`).
-/
import Workspace.AltQuotients.DM52.Degree7
import Workspace.AltQuotients.DM52.OrbitTools

/-!
# Primitive subgroups of small index in `A_8`

The degree-`8` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148, Exercise 5.2.3): a primitive `G < A_8` with
`|A_8 : G| < C(8,4) = 70` is `AGL₃(2)` acting on the eight vectors of `F₂³`.

**Orders.**  Theorem 3.3E (with `p = 3, 5`) makes `15` divide `h = |A : G|`, so `|G|` is one
of `1344, 672, 448, 336`.  With `N := N_S(⟨x⟩)` for a `7`-cycle `x ∈ G`, `|A ∩ N| ∣ 21`, and
the Sylow `7`-count leaves `|G| = 1344` with `G ∩ N = A ∩ N` of order `21`, and `|G| = 448`
with `|G ∩ N| = 7`.  In the second case the point stabilizer `G_α` has order `56`, and the
Sylow `7`-count in `G_α` together with Burnside's theorem gives a normal subgroup `K ⊴ G_α` of
order `8`.  The fixed points of `K` form a set invariant under a `7`-cycle of `G_α`, so it is
`{α}` or everything; the first is impossible for a `2`-group on `8` points (the number of
fixed points is even), and the second makes `K = 1`.

**Recognition.**  Number the points by `F₂³`: the point `i < 7` is `α^i` for a root `α` of
`X³ + X + 1`, and `7` is `0`.  After relabeling, `G` contains `x ↦ αx` and the Frobenius
`x ↦ x²`, which fix `0`; the stabilizer `G_0` is then recognized as in degree `7` (it
preserves the Fano plane of the nonzero vectors, possibly after conjugation by `x ↦ 3x`),
and one more element `g ∈ G` swapping `0` and `1` is affine or makes a `3`-cycle or an element
of order `5`.  The group generated has order `8 · 168 = 1344` by the orbit–stabilizer theorem.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### Models -/

/-- `α^i ↦ α^(i+1)` (multiplication by `α`), fixing `7` (the zero vector). -/
def c8 : Perm (Fin 8) := ofVec ![1, 2, 3, 4, 5, 6, 0, 7] ![6, 0, 1, 2, 3, 4, 5, 7] (by decide)
/-- `α^i ↦ α^(2i)` (the Frobenius). -/
def mu8 : Perm (Fin 8) := ofVec ![0, 2, 4, 6, 1, 3, 5, 7] ![0, 4, 1, 5, 2, 6, 3, 7] (by decide)
/-- `α^i ↦ α^(3i)`, odd. -/
def rho8 : Perm (Fin 8) := ofVec ![0, 3, 6, 2, 5, 1, 4, 7] ![0, 5, 3, 1, 6, 4, 2, 7] (by decide)
/-- The linear map `(2 4)(5 6)`, fixing the basis vector `1 = α⁰` and `α = α¹`. -/
def s8 : Perm (Fin 8) := ofVec ![0, 1, 4, 3, 2, 6, 5, 7] ![0, 1, 4, 3, 2, 6, 5, 7] (by decide)

theorem mu8_conj : mu8 * c8 * mu8⁻¹ = c8 ^ (2 : ℤ) := by decide
theorem rho8_conj : rho8 * c8 * rho8⁻¹ = c8 ^ (3 : ℤ) := by decide
theorem rho8_sign : sign rho8 = -1 := by decide
theorem mu8_sign : sign mu8 = 1 := by decide
theorem rho8_mu8 : rho8 * mu8 = mu8 * rho8 := by decide
theorem orderOf_c8 : orderOf c8 = 7 := orderOf_eq_prime (by decide) (by decide)
theorem orderOf_mu8 : orderOf mu8 = 3 := orderOf_eq_prime (by decide) (by decide)
theorem cycleType_c8 : c8.cycleType = {7} :=
  cycleType_eq_of_orderOf_prime (by norm_num) orderOf_c8 (by norm_num)

/-! ### The Sylow `7`-count in `A_8` -/

/-- **Sylow `7`-count in `A_8`**: for `H ≤ A_8` with `7 ∥ |H|` there is a `7`-cycle `x ∈ H`
such that, with `N := N_S(⟨x⟩)`, `d := |H ∩ N|` divides `a := |A ∩ N|`, `a ∣ 21`,
`|H|/d ≡ 1 (mod 7)`, and `d = 7` gives Burnside's normal complement. -/
theorem sylow_seven_eight {H : Subgroup (Perm (Fin 8))} (hHA : H ≤ alternatingGroup (Fin 8))
    (h7 : 7 ∣ Nat.card H) (h49 : ¬ 7 ^ 2 ∣ Nat.card H) :
    ∃ x ∈ H, x.cycleType = {7} ∧
      Nat.card (alternatingGroup (Fin 8) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) ∣
          21 ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) ∣
        Nat.card (alternatingGroup (Fin 8) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) ∣
        Nat.card H ∧
      Nat.card H / Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) %
          7 = 1 ∧
      (Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) = 7 →
        ∃ K : Subgroup (Perm (Fin 8)), K ≤ H ∧ (K.subgroupOf H).Normal ∧
          Nat.card K * 7 = Nat.card H) := by
  obtain ⟨x, hxH, hxo, s1, s2, s3, s4, s5⟩ := sylow_normalizer_facts hHA (p := 7)
    (by norm_num) h7 h49
    (fun x _ hx => exists_odd_normalizer_of_model rho8_conj rho8_sign
      (by rw [cycleType_eq_of_orderOf_prime (by norm_num) hx (by norm_num), cycleType_c8]))
  have hxc : x.cycleType = {7} := cycleType_eq_of_orderOf_prime (by norm_num) hxo (by norm_num)
  rw [card_centralizer_of_cycleType hxc] at s1
  refine ⟨x, hxH, hxc, Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_, s2, s3, s4, s5⟩
  simpa using s1

/-! ### A fixed-point argument -/

/-- A `2`-group `K` of permutations of a set of even size, fixing a point `p` and normalized
by a cycle `x` moving every other point, is trivial: the fixed-point set of `K` is invariant
under `x`, so it is `{p}` or everything, and it has even size. -/
theorem eq_bot_of_isPGroup_two_of_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {K : Subgroup (Perm α)} (hK2 : IsPGroup 2 K) (hα : Even (Fintype.card α)) {p : α}
    (hKp : ∀ k ∈ K, k p = p) {x : Perm α} (hx : x.IsCycle) (hxs : ∀ b, b ≠ p → x b ≠ b)
    (hxK : x ∈ normalizer (K : Set (Perm α))) : K = ⊥ := by
  -- a fixed point `a ≠ p` of `K` makes `K` trivial
  have hfix : ∀ a, a ≠ p → (∀ k ∈ K, k a = a) → ∀ k ∈ K, k = 1 := by
    intro a hap ha k hk
    ext b
    by_cases hbp : b = p
    · subst hbp; simpa using hKp k hk
    · obtain ⟨i, hi⟩ := hx.exists_pow_eq (hxs a hap) (hxs b hbp)
      have hxi : (x ^ i)⁻¹ ∈ normalizer (K : Set (Perm α)) := inv_mem (pow_mem hxK i)
      have hk' : (x ^ i)⁻¹ * k * (x ^ i)⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp hxi k).mp hk
      rw [inv_inv] at hk'
      have h2 : ((x ^ i)⁻¹ * k * x ^ i) a = a := ha _ hk'
      rw [Perm.mul_apply, Perm.mul_apply] at h2
      rw [← hi, Perm.coe_one, id]
      exact (Perm.inv_eq_iff_eq).mp h2
  by_contra hne
  obtain ⟨⟨k, hkK⟩, hk1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hK2.card_modEq_card_fixedPoints α
  have hF : fixedPoints K α = {p} := by
    ext a
    simp only [mem_fixedPoints, Set.mem_singleton_iff, Subgroup.smul_def, Perm.smul_def,
      Subtype.forall]
    constructor
    · intro ha
      by_contra hap
      exact hk1 (Subtype.ext (hfix a hap ha k hkK))
    · rintro rfl k hk
      exact hKp k hk
  have e1 : Nat.card (({p} : Set α)) = 1 := Nat.card_unique
  rw [hF, e1, Nat.card_eq_fintype_card] at hmod
  obtain ⟨m, hm⟩ := hα
  unfold Nat.ModEq at hmod
  omega

/-! ### The order of `G` -/

/-- **Degree 8, the order of `G`**: a primitive `G < A_8` with `|A_8 : G| < 70` has order
`1344` and contains the normalizer `A_8 ∩ N_S(⟨x⟩)` of a `7`-cycle `x ∈ G`. -/
theorem degree_eight_order {G : Subgroup (Perm (Fin 8))} (hGA : G ≤ alternatingGroup (Fin 8))
    (hG : IsPreprimitive G (Fin 8)) (hA : ¬ alternatingGroup (Fin 8) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 8)) < 70) :
    Nat.card G = 1344 ∧ ∃ x ∈ G, x.cycleType = {7} ∧
      G ⊓ normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) =
        alternatingGroup (Fin 8) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) := by
  obtain ⟨h1, -, -, -⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  have d5 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_five (by norm_num) (by simp)
  simp only [Fintype.card_fin] at h1
  -- the point stabilizer of `0` has order `|G| / 8`
  have hstab := card_eq_card_mul_stabilizer hG.toIsPretransitive (0 : Fin 8)
  simp only [Fintype.card_fin] at hstab
  generalize hN : Nat.card G = N at *
  generalize G.relIndex (alternatingGroup (Fin 8)) = h at *
  have e1 : N * h = 20160 := by
    have : (8 : ℕ)! = 40320 := by decide
    rw [this] at h1; linarith
  have hN' : N = 1344 ∨ N = 672 ∨ N = 448 ∨ N = 336 := by
    obtain ⟨k, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    have hk : k ≤ 4 := by omega
    interval_cases k <;> omega
  obtain ⟨x, hxG, hxc, s1, s2, s3, s4, s5⟩ := sylow_seven_eight hGA
    (by rw [hN]; rcases hN' with h | h | h | h <;> rw [h] <;> norm_num)
    (by rw [hN]; rcases hN' with h | h | h | h <;> rw [h] <;> norm_num)
  rw [hN] at s3 s4 s5
  generalize hNA : Nat.card (alternatingGroup (Fin 8) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (G ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) = d
    at *
  have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
  have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
  have ha' : a = 1 ∨ a = 3 ∨ a = 7 ∨ a = 21 := by
    have := Nat.le_of_dvd (by norm_num) s1
    clear hNA s2
    interval_cases a <;> revert s1 <;> decide
  have hdle : d ≤ 21 := Nat.le_of_dvd (by norm_num) (s2.trans s1)
  -- `d = 7` forces `|G| = 448`, which the point stabilizer excludes
  have hd7 : d ≠ 7 := by
    intro hd
    have h448 : N = 448 := by
      subst hd; rcases hN' with h | h | h | h <;> subst h <;> omega
    subst h448
    set H := G ⊓ stabilizer (Perm (Fin 8)) (0 : Fin 8) with hH
    have hHcard : Nat.card H = 56 := by omega
    have hHA : H ≤ alternatingGroup (Fin 8) := inf_le_left.trans hGA
    obtain ⟨y, hyH, hyc, t1, t2, t3, t4, t5⟩ := sylow_seven_eight hHA
      (by rw [hHcard]; norm_num) (by rw [hHcard]; norm_num)
    rw [hHcard] at t3 t4 t5
    generalize hNA' : Nat.card (alternatingGroup (Fin 8) ⊓
      normalizer ((zpowers y : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) =
        a' at *
    generalize hNG' : Nat.card (H ⊓
      normalizer ((zpowers y : Subgroup (Perm (Fin 8))) : Set (Perm (Fin 8))) : Subgroup _) =
        d' at *
    have hd'0 : 0 < d' := by rw [← hNG']; exact Nat.card_pos
    have hd' : d' = 7 := by
      have : d' ≤ 21 := Nat.le_of_dvd (by norm_num) (t2.trans t1)
      clear hNG' hNA' t5
      interval_cases d' <;> omega
    obtain ⟨K, hKH, hKn, hK⟩ := t5 hd'
    have hK8 : Nat.card K = 8 := by omega
    -- `y` is a `7`-cycle fixing `0`
    have hy0 : y 0 = 0 := hyH.2
    have hyc' : y.IsCycle := by
      rw [← card_cycleType_eq_one, hyc]; rfl
    have hysupp : y.support.card = 7 := by rw [← sum_cycleType, hyc]; simp
    have hys : ∀ b, b ≠ 0 → y b ≠ b := by
      intro b hb hyb
      have hsub : y.support ⊆ (Finset.univ.erase (0 : Fin 8)).erase b := by
        intro z hz
        rw [Perm.mem_support] at hz
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun h => hz (h ▸ hyb), fun h => hz (h ▸ hy0)⟩
      have := Finset.card_le_card hsub
      rw [hysupp, Finset.card_erase_of_mem (by simp [hb]), Finset.card_erase_of_mem (by simp)]
        at this
      simp at this
    have hyN : y ∈ normalizer (K : Set (Perm (Fin 8))) := by
      rw [mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have := hKn.conj_mem ⟨k, hKH hk⟩ (by simpa [Subgroup.mem_subgroupOf] using hk) ⟨y, hyH⟩
        simpa [Subgroup.mem_subgroupOf] using this
      · intro hk
        have := hKn.conj_mem ⟨y * k * y⁻¹, hKH hk⟩
          (by simpa [Subgroup.mem_subgroupOf] using hk) ⟨y⁻¹, inv_mem hyH⟩
        simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
    have hbot := eq_bot_of_isPGroup_two_of_cycle (K := K)
      (IsPGroup.of_card (n := 3) (by rw [hK8]; norm_num)) (by decide) (p := (0 : Fin 8))
      (fun k hk => (hKH hk).2) hyc' hys hyN
    rw [hbot, Subgroup.card_bot] at hK8
    omega
  have hfin : d = 21 ∧ a = 21 ∧ N = 1344 := by
    clear hNG hNA s5
    rcases ha' with rfl | rfl | rfl | rfl <;>
    rcases hN' with rfl | rfl | rfl | rfl <;> interval_cases d <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := hfin
  exact ⟨rfl, x, hxG, hxc, Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hGA)
    (by rw [hNA, hNG])⟩

/-! ### The affine model -/

/-- The point `i` as a vector of `F₂³`: `α^i` for `i < 7` (with `α³ = α + 1`), and `0` for
`i = 7`. -/
def enc8 : Fin 8 → (Fin 3 → ZMod 2) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![1, 0, 1],
    ![0, 0, 0]]

/-- The inverse numbering. -/
def dec8 (v : Fin 3 → ZMod 2) : Fin 8 :=
  ((List.finRange 8).find? (fun i => enc8 i = v)).getD 0

theorem dec8_enc8 : ∀ i, dec8 (enc8 i) = i := by decide
theorem enc8_dec8 : ∀ v, enc8 (dec8 v) = v := by decide

/-- The numbering `Fin 8 ≃ F₂³`. -/
def e8 : Fin 8 ≃ (Fin 3 → ZMod 2) := ⟨enc8, dec8, dec8_enc8, enc8_dec8⟩

/-- `g` is affine for the numbering `enc8`. -/
def IsAff8 (g : Perm (Fin 8)) : Prop :=
  ∀ i j : Fin 8, enc8 (g (dec8 (enc8 i + enc8 j))) + enc8 (g 7) = enc8 (g i) + enc8 (g j)

instance : DecidablePred IsAff8 := fun g => by unfold IsAff8; infer_instance

/-- The model of `AGL₃(2)`: the affine group of `F₂³`, transported to `Fin 8`. -/
def A8m : Subgroup (Perm (Fin 8)) := relabel e8.symm AGL_3_2

theorem mem_A8m_iff (g : Perm (Fin 8)) : g ∈ A8m ↔ IsAff8 g := by
  rw [A8m, mem_relabel, Equiv.symm_symm, mem_AGL_3_2_iff]
  have happ : ∀ v, (e8.permCongr g) v = enc8 (g (dec8 v)) := fun v => rfl
  have h07 : dec8 0 = 7 := by decide
  constructor
  · intro h i j
    have := h (enc8 i) (enc8 j)
    simp only [happ, dec8_enc8, h07] at this
    exact this
  · intro h u v
    have := h (dec8 u) (dec8 v)
    rw [enc8_dec8, enc8_dec8] at this
    simp only [happ, h07]
    exact this

/-- `A8m ≃* AGL₃(2)`. -/
noncomputable def A8m_mulEquiv : A8m ≃* AGL_3_2 := (relabelEquiv e8.symm AGL_3_2).symm

/-! ### Reduction of the candidate checks to `Perm (Fin 6)` -/

/-- Words in `[c8, mu8, s8, g, g⁻¹]` (indices `0, …, 4`). -/
def words8 : List (List ℕ) := [[2, 3, 2, 4], [1, 2, 3, 2, 4], [1, 3, 1, 4], [1, 2, 4, 1, 3]]

/-- The points `1, …, 6` of `Fin 8`. -/
def P68 (i : Fin 8) : Prop := 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 6

instance : DecidablePred P68 := fun i => by unfold P68; infer_instance

/-- `Fin 6 ≃ {1, …, 6} ⊆ Fin 8`, `j ↦ j + 1`. -/
def e68 : Fin 6 ≃ {i : Fin 8 // P68 i} where
  toFun j := ⟨⟨j + 1, by omega⟩, by simp only [P68]; omega⟩
  invFun x := ⟨x.1 - 1, by have := x.2; simp only [P68] at this; omega⟩
  left_inv j := by ext; simp
  right_inv x := by
    have := x.2
    simp only [P68] at this
    ext; simp; omega

/-- A permutation of `{1, …, 6}`, extended by the identity on `0` and `7`. -/
def lift68 (p : Perm (Fin 6)) : Perm (Fin 8) := ofSubtype (e68.permCongr p)

/-- Every permutation of `Fin 8` fixing `0` and `7` is some `lift68 p`. -/
theorem exists_lift68 {g : Perm (Fin 8)} (h0 : g 0 = 0) (h7 : g 7 = 7) :
    ∃ p : Perm (Fin 6), lift68 p = g := by
  have key : ∀ x : Fin 8, P68 x ↔ (x ≠ 0 ∧ x ≠ 7) := by decide
  have hne : ∀ x a : Fin 8, g a = a → (x ≠ a ↔ g x ≠ a) := by
    intro x a ha
    constructor
    · intro hx h; exact hx (g.injective (h.trans ha.symm))
    · intro hx h; exact hx (h ▸ ha)
  have hP : ∀ x, P68 x ↔ P68 (g x) := by
    intro x
    rw [key, key, hne x 0 h0, hne x 7 h7]
  refine ⟨e68.symm.permCongr (g.subtypePerm (fun x => (hP x).symm)), ?_⟩
  rw [lift68, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]
  apply ofSubtype_subtypePerm
  intro x hx
  rw [key]
  exact ⟨fun h => hx (h ▸ h0), fun h => hx (h ▸ h7)⟩

end Babai.DM52
