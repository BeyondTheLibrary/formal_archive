/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 9, the models.
-/
import Workspace.AltQuotients.DM52.Degree5
import Workspace.AltQuotients.DM52.PGL28
import Workspace.AltQuotients.DM52.SylowTwoNine

/-!
# Primitive subgroups of small index in `A_9`: the models

The models, the order of `G`, and the lift `Babai.DM52.lift6` used by the recognition
(`Workspace/AltQuotients/DM52/Degree9.lean`).
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup
open scoped Pointwise

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### Models -/

/-- `α^i ↦ α^(3i)` (the map `x ↦ x³` on `F₈^×`), fixing `7` and `8`; it normalizes `⟨c9⟩`
and is odd. -/
def rho9 : Perm (Fin 9) :=
  ofVec ![0, 3, 6, 2, 5, 1, 4, 7, 8] ![0, 5, 3, 1, 6, 4, 2, 7, 8] (by decide)

theorem c9_conj_mu9 : mu9 * c9 * mu9⁻¹ = c9 ^ (2 : ℤ) := by decide
theorem c9_conj_io9 : io9 * c9 * io9⁻¹ = c9 ^ (6 : ℤ) := by decide
theorem rho9_conj : rho9 * c9 * rho9⁻¹ = c9 ^ (3 : ℤ) := by decide
theorem rho9_sign : sign rho9 = -1 := by decide
theorem mu9_sign : sign mu9 = 1 := by decide
theorem io9_sign : sign io9 = 1 := by decide
theorem rho9_mu9 : rho9 * mu9 = mu9 * rho9 := by decide
theorem rho9_io9 : rho9 * io9 = io9 * rho9 := by decide
theorem orderOf_c9 : orderOf c9 = 7 := orderOf_eq_prime (by decide) (by decide)
theorem cycleType_c9 : c9.cycleType = {7} :=
  cycleType_eq_of_orderOf_prime (by norm_num) orderOf_c9 (by norm_num)

/-! ### The Sylow `7`-count in `A_9` -/

/-- **Sylow `7`-count in `A_9`**: for `H ≤ A_9` with `7 ∥ |H|` there is a `7`-cycle `x ∈ H`
such that, with `N := N_S(⟨x⟩)`, `d := |H ∩ N|` divides `a := |A ∩ N|`, `a ∣ 42`, and
`|H|/d ≡ 1 (mod 7)`. -/
theorem sylow_seven_nine {H : Subgroup (Perm (Fin 9))} (hHA : H ≤ alternatingGroup (Fin 9))
    (h7 : 7 ∣ Nat.card H) (h49 : ¬ 7 ^ 2 ∣ Nat.card H) :
    ∃ x ∈ H, x.cycleType = {7} ∧
      Nat.card (alternatingGroup (Fin 9) ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) ∣
          42 ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) ∣
        Nat.card (alternatingGroup (Fin 9) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) ∧
      Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) ∣
        Nat.card H ∧
      Nat.card H / Nat.card (H ⊓
        normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) %
          7 = 1 := by
  obtain ⟨x, hxH, hxo, s1, s2, s3, s4, -⟩ := sylow_normalizer_facts hHA (p := 7)
    (by norm_num) h7 h49
    (fun x _ hx => exists_odd_normalizer_of_model rho9_conj rho9_sign
      (by rw [cycleType_eq_of_orderOf_prime (by norm_num) hx (by norm_num), cycleType_c9]))
  have hxc : x.cycleType = {7} := cycleType_eq_of_orderOf_prime (by norm_num) hxo (by norm_num)
  rw [card_centralizer_of_cycleType hxc] at s1
  refine ⟨x, hxH, hxc, Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_, s2, s3, s4⟩
  simpa [Nat.factorial] using s1

/-! ### The order of `G` -/

/-- **Degree 9, the order of `G`**: a primitive `G < A_9` with `|A_9 : G| < 126` has order
`1512` and contains the normalizer `A_9 ∩ N_S(⟨x⟩)` of a `7`-cycle `x ∈ G`. -/
theorem degree_nine_order {G : Subgroup (Perm (Fin 9))} (hGA : G ≤ alternatingGroup (Fin 9))
    (hG : IsPreprimitive G (Fin 9)) (hA : ¬ alternatingGroup (Fin 9) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 9)) < 126) :
    Nat.card G = 1512 ∧ ∃ x ∈ G, x.cycleType = {7} ∧
      G ⊓ normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) =
        alternatingGroup (Fin 9) ⊓
          normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) := by
  obtain ⟨h1, -, -, h4⟩ := prim_facts hGA hG hA (by simp)
  have d3 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_three (by norm_num) (by simp)
  have d5 := odd_prime_dvd_relIndex hGA hG hA Nat.prime_five (by norm_num) (by simp)
  have h64 : ¬ 64 ∣ Nat.card G := fun h => hA (alternatingGroup_le_of_sixtyfour_dvd hGA hG h)
  simp only [Fintype.card_fin] at h1 h4
  have f9 : Nat.factorial 9 = 362880 := by decide
  have f5 : Nat.factorial (9 - 9 / 2) = 120 := by decide
  rw [f9] at h1
  rw [f9, f5] at h4
  -- the point stabilizer of `0` has order `|G| / 9`
  have hstab := card_eq_card_mul_stabilizer hG.toIsPretransitive (0 : Fin 9)
  simp only [Fintype.card_fin] at hstab
  generalize hN : Nat.card G = N at *
  generalize G.relIndex (alternatingGroup (Fin 9)) = h at *
  have e1 : N * h = 181440 := by linarith
  have hN' : N = 3024 ∨ N = 2016 ∨ N = 1512 := by
    obtain ⟨k, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) d3 d5
    have hk : k ≤ 8 := by omega
    have hk4 : 4 ≤ k := by
      by_contra hk4
      have : 3 * 5 * k ≤ 45 := by omega
      nlinarith
    interval_cases k <;> omega
  obtain ⟨x, hxG, hxc, s1, s2, s3, s4⟩ := sylow_seven_nine hGA
    (by rw [hN]; rcases hN' with h | h | h <;> rw [h] <;> norm_num)
    (by rw [hN]; rcases hN' with h | h | h <;> rw [h] <;> norm_num)
  rw [hN] at s3 s4
  generalize hNA : Nat.card (alternatingGroup (Fin 9) ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) = a
    at *
  generalize hNG : Nat.card (G ⊓
    normalizer ((zpowers x : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) = d
    at *
  have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
  have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
  have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 6 ∨ a = 7 ∨ a = 14 ∨ a = 21 ∨ a = 42 := by
    have := Nat.le_of_dvd (by norm_num) s1
    clear hNA s2
    interval_cases a <;> revert s1 <;> decide
  have hdle : d ≤ 42 := Nat.le_of_dvd (by norm_num) (s2.trans s1)
  -- `d = 7` forces `|G| = 2016`, which the point stabilizer excludes
  have hd7 : d ≠ 7 := by
    intro hd
    have h2016 : N = 2016 := by
      subst hd; rcases hN' with h | h | h <;> subst h <;> omega
    subst h2016
    set H := G ⊓ stabilizer (Perm (Fin 9)) (0 : Fin 9) with hH
    have hHcard : Nat.card H = 224 := by omega
    have hHA : H ≤ alternatingGroup (Fin 9) := inf_le_left.trans hGA
    obtain ⟨y, -, -, t1, t2, t3, t4⟩ := sylow_seven_nine hHA
      (by rw [hHcard]; norm_num) (by rw [hHcard]; norm_num)
    rw [hHcard] at t3 t4
    generalize Nat.card (alternatingGroup (Fin 9) ⊓
      normalizer ((zpowers y : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) =
        a' at *
    generalize hNG' : Nat.card (H ⊓
      normalizer ((zpowers y : Subgroup (Perm (Fin 9))) : Set (Perm (Fin 9))) : Subgroup _) =
        d' at *
    have hd'0 : 0 < d' := by rw [← hNG']; exact Nat.card_pos
    have t5 : d' ∣ 42 := t2.trans t1
    have : d' ≤ 42 := Nat.le_of_dvd (by norm_num) t5
    clear hNG'
    interval_cases d' <;> omega
  have hfin : d = 42 ∧ a = 42 ∧ N = 1512 := by
    clear hNG hNA
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hN' with rfl | rfl | rfl <;> interval_cases d <;> omega
  obtain ⟨rfl, rfl, rfl⟩ := hfin
  exact ⟨rfl, x, hxG, hxc, Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hGA)
    (by rw [hNA, hNG])⟩

/-! ### Recognition -/

theorem c9_orbit : ∀ b : Fin 9, b ≠ 7 → b ≠ 8 → ∃ m : Fin 7, (c9 ^ (m : ℕ)) 0 = b := by
  decide

theorem c9_orbit' : ∀ b : Fin 9, b ≠ 7 → b ≠ 8 → ∃ m : Fin 7, (c9 ^ (m : ℕ)) b = 0 := by
  decide

theorem c9_pow_fix (m : ℕ) : (c9 ^ m) 7 = 7 ∧ (c9 ^ m) 8 = 8 := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    rw [pow_succ, Perm.mul_apply, Perm.mul_apply, show c9 7 = 7 by decide,
      show c9 8 = 8 by decide]
    exact ih

theorem orderOf_mu9 : orderOf mu9 = 3 := orderOf_eq_prime (by decide) (by decide)

/-- The last step of the recognition: a group of order `1512` containing `c9`, `mu9`, `io9`
and an element `g` of `M9` fixing `∞ = 8` and sending `0 = 7` to `1 = 0` is `M9`. -/
theorem eq_M9 {G : Subgroup (Perm (Fin 9))} (hcard : Nat.card G = 1512) (hc : c9 ∈ G)
    (hm : mu9 ∈ G) (hi : io9 ∈ G) {g : Perm (Fin 9)} (hg : g ∈ G) (hg8 : g 8 = 8)
    (hg7 : g 7 = 0) (hgM : g ∈ M9) : G = M9 := by
  set K := closure ({c9, mu9, io9, g} : Set (Perm (Fin 9)))
  have hcK : c9 ∈ K := subset_closure (by simp)
  have hmK : mu9 ∈ K := subset_closure (by simp)
  have hiK : io9 ∈ K := subset_closure (by simp)
  have hgK : g ∈ K := subset_closure (by simp)
  have hKG : K ≤ G := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hc
    · exact hm
    · exact hi
    · exact hg
  have hKM : K ≤ M9 := by
    rw [closure_le]; intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact c9_mem_M9
    · exact mu9_mem_M9
    · exact io9_mem_M9
    · exact hgM
  set K8 := (K ⊓ stabilizer (Perm (Fin 9)) (8 : Fin 9) : Subgroup _)
  -- `c9` and `mu9` fix `7` and `8`, so `21` divides `|K_{8,7}|`
  have h87 : 21 ≤ Nat.card (K8 ⊓ stabilizer (Perm (Fin 9)) (7 : Fin 9) : Subgroup _) := by
    set K87 := (K8 ⊓ stabilizer (Perm (Fin 9)) (7 : Fin 9) : Subgroup _)
    have hc87 : c9 ∈ K87 := ⟨⟨hcK, MulAction.mem_stabilizer_iff.mpr (by decide)⟩,
      MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    have hm87 : mu9 ∈ K87 := ⟨⟨hmK, MulAction.mem_stabilizer_iff.mpr (by decide)⟩,
      MulAction.mem_stabilizer_iff.mpr (by decide)⟩
    have e1 := K87.orderOf_dvd_natCard hc87
    have e2 := K87.orderOf_dvd_natCard hm87
    rw [orderOf_c9] at e1
    rw [orderOf_mu9] at e2
    have h21 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 7 3) e1 e2
    exact Nat.le_of_dvd Nat.card_pos h21
  have hK8 : 8 * 21 ≤ Nat.card K8 := by
    have := card_le_card_of_orbit K8 7 (Finset.univ.erase 8) (fun b hb => by
      by_cases hb7 : b = 7
      · exact ⟨1, one_mem _, by rw [hb7]; rfl⟩
      · obtain ⟨m, hm'⟩ := c9_orbit b hb7 (Finset.ne_of_mem_erase hb)
        refine ⟨c9 ^ (m : ℕ) * g, ⟨mul_mem (pow_mem hcK _) hgK, ?_⟩, ?_⟩
        · show (c9 ^ (m : ℕ) * g) 8 = 8
          rw [Perm.mul_apply, hg8, (c9_pow_fix _).2]
        · rw [Perm.mul_apply, hg7, hm']) h87
    have e : ((Finset.univ : Finset (Fin 9)).erase 8).card = 8 := by decide
    rwa [e] at this
  have hK : 9 * (8 * 21) ≤ Nat.card K := by
    have := card_le_card_of_orbit K 8 Finset.univ (fun b _ => by
      by_cases hb8 : b = 8
      · exact ⟨1, one_mem _, by rw [hb8]; rfl⟩
      by_cases hb7 : b = 7
      · exact ⟨io9, hiK, by rw [hb7]; decide⟩
      obtain ⟨m, hm'⟩ := c9_orbit b hb7 hb8
      refine ⟨c9 ^ (m : ℕ) * g * io9, mul_mem (mul_mem (pow_mem hcK _) hgK) hiK, ?_⟩
      rw [Perm.mul_apply, Perm.mul_apply, show io9 8 = 7 by decide, hg7, hm']) hK8
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hKG' : K = G := Subgroup.eq_of_le_of_card_ge hKG (by rw [hcard]; omega)
  exact Subgroup.eq_of_le_of_card_ge (hKG' ▸ hKM) (by rw [hcard]; exact card_M9_le)

/-- Words in `[c9, mu9, io9, g, g⁻¹]` (indices `0, …, 4`): the powers `(c9 io9 g²)⁴`,
`(io9 g³)⁴`, `(c9 g² io9)⁴` and `(mu9 io9 g io9 g⁻¹)³`. -/
def words9 : List (List ℕ) :=
  [[0, 2, 3, 3, 0, 2, 3, 3, 0, 2, 3, 3, 0, 2, 3, 3],
    [2, 3, 3, 3, 2, 3, 3, 3, 2, 3, 3, 3, 2, 3, 3, 3],
    [0, 3, 3, 2, 0, 3, 3, 2, 0, 3, 3, 2, 0, 3, 3, 2],
    [1, 2, 3, 2, 4, 1, 2, 3, 2, 4, 1, 2, 3, 2, 4]]

/-- The points `1, …, 6`. -/
def P6 (i : Fin 9) : Prop := 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 6

instance : DecidablePred P6 := fun i => by unfold P6; infer_instance

/-- `Fin 6 ≃ {1, …, 6}`, `j ↦ j + 1`. -/
def e69 : Fin 6 ≃ {i : Fin 9 // P6 i} where
  toFun j := ⟨⟨j + 1, by omega⟩, by simp only [P6]; omega⟩
  invFun x := ⟨x.1 - 1, by have := x.2; simp only [P6] at this; omega⟩
  left_inv j := by ext; simp
  right_inv x := by
    have := x.2
    simp only [P6] at this
    ext; simp; omega

/-- A permutation of `{1, …, 6}`, extended by the identity on `0, 7, 8`. -/
def lift6 (p : Perm (Fin 6)) : Perm (Fin 9) := ofSubtype (e69.permCongr p)

/-- Every permutation of `Fin 9` fixing `0`, `7` and `8` is some `lift6 p`. -/
theorem exists_lift6 {g : Perm (Fin 9)} (h0 : g 0 = 0) (h7 : g 7 = 7) (h8 : g 8 = 8) :
    ∃ p : Perm (Fin 6), lift6 p = g := by
  have key : ∀ x : Fin 9, P6 x ↔ (x ≠ 0 ∧ x ≠ 7 ∧ x ≠ 8) := by decide
  have hne : ∀ x a : Fin 9, g a = a → (x ≠ a ↔ g x ≠ a) := by
    intro x a ha
    constructor
    · intro hx h; exact hx (g.injective (h.trans ha.symm))
    · intro hx h; exact hx (h ▸ ha)
  have hP : ∀ x, P6 x ↔ P6 (g x) := by
    intro x
    rw [key, key, hne x 0 h0, hne x 7 h7, hne x 8 h8]
  refine ⟨e69.symm.permCongr (g.subtypePerm (fun x => (hP x).symm)), ?_⟩
  rw [lift6, ← Equiv.permCongr_symm, Equiv.apply_symm_apply]
  apply ofSubtype_subtypePerm
  intro x hx
  rw [key]
  refine ⟨fun h => hx (h ▸ h0), fun h => hx (h ▸ h7), fun h => hx (h ▸ h8)⟩

end Babai.DM52
