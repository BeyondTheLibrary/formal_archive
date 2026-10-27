/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Tools for the proof of [DiM, Thm. 5.2A,B]: primitive groups of degree 5.
-/
import Workspace.AltQuotients.DM52.Recog
import Workspace.AltQuotients.DM52.PrimLarge
import Workspace.AltQuotients.DM52.Affine

/-!
# Primitive subgroups of small index in `A_5`

The degree-`5` case of the examination of the primitive groups of small degree in the proof
of [DiM, Thm. 5.2A] (p. 148, "An examination of the primitive groups of degrees up to
12 …"): a primitive `G < A_5` with `|A_5 : G| < C(5,2) = 10` is the Frobenius group `5:2`
of order `10`, i.e. the normalizer of a Sylow `5`-subgroup in `A_5`.

The argument: `5 ∣ |G|` and `|G| ∈ {10, 15, 20, 30}`.  With `N := N_S(⟨x⟩)` for a
`5`-cycle `x ∈ G`, `|A ∩ N| ∣ 10`, the number `|G : G ∩ N|` of Sylow `5`-subgroups is
`≡ 1 (mod 5)`, and for `|G ∩ N| = 5` Burnside's theorem gives a normal subgroup of order
`|G|/5`, which must be divisible by `5` (it is transitive).  Only `|G| = |G ∩ N| = 10`
survives, so `G = A ∩ N`.
-/

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

/-! ### The model -/

/-- The `5`-cycle `x ↦ x + 1` of `ℤ/5 = Fin 5`. -/
def cyc5 : Perm (Fin 5) := ofVec ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3] (by decide)

/-- `x ↦ 2x`, an odd permutation normalizing `⟨cyc5⟩`. -/
def mul5 : Perm (Fin 5) := ofVec ![0, 2, 4, 1, 3] ![0, 3, 1, 4, 2] (by decide)

/-- `x ↦ -x`, an even permutation inverting `cyc5`. -/
def neg5 : Perm (Fin 5) := ofVec ![0, 4, 3, 2, 1] ![0, 4, 3, 2, 1] (by decide)

theorem mul5_conj : mul5 * cyc5 * mul5⁻¹ = cyc5 ^ (2 : ℤ) := by decide
theorem mul5_sign : sign mul5 = -1 := by decide
theorem neg5_conj : neg5 * cyc5 * neg5⁻¹ = cyc5 ^ (-1 : ℤ) := by decide
theorem neg5_sign : sign neg5 = 1 := by decide

theorem orderOf_cyc5 : orderOf cyc5 = 5 := orderOf_eq_prime (by decide) (by decide)

theorem cycleType_cyc5 : cyc5.cycleType = {5} :=
  cycleType_eq_of_orderOf_prime Nat.prime_five orderOf_cyc5 (by norm_num)

/-- The dihedral group of order `10` acting on the vertices of a pentagon: `r i ↦ x ↦ x + i`,
`sr i ↦ x ↦ -(x + i)`. -/
def d10Fun : DihedralGroup 5 → Perm (Fin 5)
  | .r i => cyc5 ^ i.val
  | .sr i => neg5 * cyc5 ^ i.val

set_option maxRecDepth 100000 in
theorem d10Fun_mul : ∀ a b : DihedralGroup 5, d10Fun (a * b) = d10Fun a * d10Fun b := by
  decide +kernel

/-- The action of `D₁₀` on five points, as a homomorphism. -/
def d10Hom : DihedralGroup 5 →* Perm (Fin 5) where
  toFun := d10Fun
  map_one' := by decide
  map_mul' := d10Fun_mul

set_option maxRecDepth 100000 in
theorem d10Hom_injective : Function.Injective d10Hom := by
  intro a b h
  revert a b h
  decide +kernel

/-- The model of `5:2`: `D₁₀ ≤ A_5` acting on the pentagon. -/
def D10 : Subgroup (Perm (Fin 5)) := d10Hom.range

theorem card_D10 : Nat.card D10 = 10 := by
  rw [D10, ← Nat.card_congr (MonoidHom.ofInjective d10Hom_injective).toEquiv,
    DihedralGroup.nat_card]

/-- `D10 ≃* D₁₀`. -/
noncomputable def D10_mulEquiv : D10 ≃* DihedralGroup 5 :=
  mulEquivOfRangeEq d10Hom d10Hom_injective rfl

instance : DecidablePred (· ∈ D10) := fun h =>
  decidable_of_iff (∃ d, d10Fun d = h) (by simp [D10, MonoidHom.mem_range]; rfl)

theorem cyc5_mem_D10 : cyc5 ∈ D10 := ⟨.r 1, by decide⟩

set_option maxRecDepth 100000 in
/-- The normalizer of `⟨x ↦ x + 1⟩` in `Sym(ℤ/5)` consists of affine maps. -/
theorem isAff5_of_conj_mem : ∀ g : Perm (Fin 5), g * cyc5 * g⁻¹ ∈ D10 → IsAff5 g := by
  decide +kernel

/-! ### Centralizers -/

/-- `|C_S(x)| = (n - p)!·p` for a `p`-cycle `x ∈ Sym(n)`. -/
theorem card_centralizer_of_cycleType {n p : ℕ} {x : Perm (Fin n)} (hx : x.cycleType = {p}) :
    Nat.card (centralizer ({x} : Set (Perm (Fin n)))) = (n - p)! * p := by
  rw [nat_card_centralizer, hx]
  simp

/-! ### The classification in degree 5 -/

/-- **Degree 5** ([DiM, proof of Thm. 5.2A], the examination of the primitive groups of
degree `5`): a primitive `G < A_5` with `|A_5 : G| < 10` is conjugate to the model `D10` of
`5:2`. -/
theorem degree_five {G : Subgroup (Perm (Fin 5))} (hGA : G ≤ alternatingGroup (Fin 5))
    (hG : IsPreprimitive G (Fin 5)) (hA : ¬ alternatingGroup (Fin 5) ≤ G)
    (hidx : G.relIndex (alternatingGroup (Fin 5)) < 10) :
    ∃ σ : Perm (Fin 5), relabel σ G = D10 := by
  obtain ⟨h1, -, h3, -⟩ := prim_facts hGA hG hA (by simp)
  simp only [Fintype.card_fin] at h1 h3
  have hh1 : G.relIndex (alternatingGroup (Fin 5)) ≠ 1 :=
    fun h => hA (Subgroup.relIndex_eq_one.mp h)
  have hG0 : 0 < Nat.card G := Nat.card_pos
  generalize hN : Nat.card G = N at *
  generalize G.relIndex (alternatingGroup (Fin 5)) = h at *
  have e1 : N * h = 60 := by
    have : (5 : ℕ)! = 120 := by decide
    rw [this] at h1; linarith
  have hN' : N = 10 ∨ N = 15 ∨ N = 20 ∨ N = 30 := by
    have hh2 : 2 ≤ h := by
      rcases Nat.lt_or_ge h 2 with h' | h'
      · interval_cases h <;> omega
      · exact h'
    have : N ≤ 30 := by nlinarith
    have : 7 ≤ N := by nlinarith
    interval_cases N <;> omega
  have h5 : 5 ∣ N := h3
  have h25 : ¬ 5 ^ 2 ∣ N := by rcases hN' with rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨x, hxG, hxo, s1, s2, s3, s4, s5⟩ := sylow_normalizer_facts hGA (p := 5)
    Nat.prime_five (by rw [hN]; exact h5) (by rw [hN]; exact h25)
    (fun x _ hx => exists_odd_normalizer_of_model mul5_conj mul5_sign
      (by rw [cycleType_eq_of_orderOf_prime Nat.prime_five hx (by norm_num), cycleType_cyc5]))
  have hxc : x.cycleType = {5} := cycleType_eq_of_orderOf_prime Nat.prime_five hxo (by norm_num)
  rw [card_centralizer_of_cycleType hxc] at s1
  rw [hN] at s3 s4 s5
  set NX := normalizer ((zpowers x : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5)))
  generalize hNA : Nat.card (alternatingGroup (Fin 5) ⊓ NX : Subgroup _) = a at *
  generalize hNG : Nat.card (G ⊓ NX : Subgroup _) = d at *
  -- the Burnside case `d = 5` forces `|G| = 30` and a normal subgroup of order `6`
  have hd5 : d ≠ 5 := by
    intro hd
    obtain ⟨K, hKG, hKn, hK⟩ := s5 hd
    have hN30 : N = 30 := by subst hd; rcases hN' with rfl | rfl | rfl | rfl <;> omega
    have hK6 : Nat.card K = 6 := by rw [hN30] at hK; omega
    have hKne : K ≠ ⊥ := by rintro rfl; rw [Subgroup.card_bot] at hK6; omega
    have := card_dvd_card_of_normal hG hKG hKn hKne
    rw [hK6, Fintype.card_fin] at this
    omega
  have ha : a ∣ 10 := by
    have : 2 * a ∣ 2 * 10 := by simpa using s1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hd : d ∣ 10 := s2.trans ha
  have hd10 : d = 10 ∧ a = 10 := by
    have hdle : d ≤ 10 := Nat.le_of_dvd (by norm_num) hd
    have hale : a ≤ 10 := Nat.le_of_dvd (by norm_num) ha
    have hd0 : 0 < d := by rw [← hNG]; exact Nat.card_pos
    have hs1 : (5 - 5)! * 5 * (5 - 1) = 20 := by decide
    rw [hs1] at s1
    have ha0 : 0 < a := by rw [← hNA]; exact Nat.card_pos
    clear s5 hNG hNA
    rcases hN' with rfl | rfl | rfl | rfl <;> interval_cases d <;> omega
  obtain ⟨hd10, ha10⟩ := hd10
  subst hd10 ha10
  have hN10 : N = 10 := by
    rcases hN' with rfl | rfl | rfl | rfl <;> omega
  -- so `G ∩ N = A ∩ N`
  have hGN : G ⊓ NX = alternatingGroup (Fin 5) ⊓ NX :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hGA) (by rw [hNA, hNG])
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_cyc5.trans hxc.symm))
  have hν : τ * neg5 * τ⁻¹ ∈ G := by
    have hmem : τ * neg5 * τ⁻¹ ∈ alternatingGroup (Fin 5) ⊓ NX := by
      refine ⟨by simp [mem_alternatingGroup, neg5_sign], ?_⟩
      apply mem_normalizer_zpowers_of_conj_eq_zpow (k := -1)
      rw [← hτ, conj_zpow, ← neg5_conj]
      group
    rw [← hGN] at hmem
    exact hmem.1
  refine ⟨τ⁻¹, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rintro _ ⟨g, rfl⟩
    rw [mem_relabel_perm, inv_inv]
    cases g with
    | r i =>
      show τ * cyc5 ^ i.val * τ⁻¹ ∈ G
      rw [← conj_pow, hτ]
      exact pow_mem hxG _
    | sr i =>
      show τ * (neg5 * cyc5 ^ i.val) * τ⁻¹ ∈ G
      have : τ * (neg5 * cyc5 ^ i.val) * τ⁻¹ = (τ * neg5 * τ⁻¹) * (τ * cyc5 * τ⁻¹) ^ i.val := by
        rw [conj_pow]; group
      rw [this, hτ]
      exact mul_mem hν (pow_mem hxG _)
  · rw [card_relabel, hN, hN10, card_D10]

/-- **Degree 5, [DiM, Thm. 5.2B]**: a subgroup `G ≤ S_5` of order `20` with `G ∩ A_5 = D10`
is `AGL(1,5) = 5:4`. -/
theorem degree_five_sym {G : Subgroup (Perm (Fin 5))}
    (h0 : G ⊓ alternatingGroup (Fin 5) = D10) (hcard : Nat.card G = 20) :
    Nonempty (G ≃* AGL_1_5) := by
  have hle : ∀ g ∈ G, g ∈ AGL_1_5 := by
    intro g hg
    refine (mem_AGL_1_5_iff g).mpr (isAff5_of_conj_mem g ?_)
    rw [← h0]
    have hc : cyc5 ∈ G := (h0 ▸ cyc5_mem_D10 : cyc5 ∈ G ⊓ alternatingGroup (Fin 5)).1
    have : sign cyc5 = 1 := by decide
    exact Subgroup.mem_inf.mpr ⟨G.mul_mem (G.mul_mem hg hc) (G.inv_mem hg),
      by rw [mem_alternatingGroup]; simp [this]⟩
  have heq : G = AGL_1_5 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (card_AGL_1_5.trans hcard.symm))
  exact ⟨MulEquiv.subgroupCongr heq⟩

end Babai.DM52
