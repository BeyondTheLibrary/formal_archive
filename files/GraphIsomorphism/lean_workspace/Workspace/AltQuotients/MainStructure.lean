/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.5 (Large alternating quotient acts as a Johnson group on blocks:
the Main Structure Theorem).
-/
import Workspace.AltQuotients.Unaffected
import Workspace.AltQuotients.SmallIndex

/-!
# §10.5 The Main Structure Theorem

Theorem 10.5.1, items (a)–(g), each as its own statement under the common hypotheses
(`ϕ : G → S_k` a giant representation and `k ≥ max{9, 2 log₂ n₀}`), then Remarks 10.5.2,
10.5.3, Remark 10.3.8, and the algorithmic Proposition 10.5.4.

## Reading of item (e)

The paper says: "the equivalence relation `T(x) = T(y)` splits `Δ` into `(k choose t_Δ)`
blocks of imprimitivity, labeled by the `t_Δ`-subsets of `[k]`. … The action of `G` on the
set of standard blocks in `Δ` is `A_k^(t_Δ)` or `S_k^(t_Δ)`."  This is split into four
statements: the blocks form a system of imprimitivity (`_e_isSystem`); the labeling
`B ↦ T(x)` (`x ∈ B`) is a bijection onto the `t_Δ`-subsets of `[k]` (`_e_labels`); there
are `(k choose t_Δ)` of them (`_e_card`); and the kernel of the action is `ker ϕ` for
`t_Δ ≥ 1`, the action being trivial for `t_Δ = 0` (`_e_ker`, `_e_trivial`).  That the
action *is* the Johnson group `A_k^(t)` or `S_k^(t)` is the labeling bijection together
with Eq. (54) (`theorem_10_5_1_c_eq54`), which says that the labels transform by `ϕ`, and
`G^ϕ ∈ {A_k, S_k}`.
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}
  (ϕ : G →* Equiv.Perm (Fin k))

/-! ### Eq. (53): the binomial estimate `C(k, ⌊k/4⌋) > 2^{k/2} ≥ n₀`

The paper's Eq. (53) reads `C(k,⌊k/4⌋) > 2^{k/2} ≥ n₀ ≥ |x^G| = |G : G_x| ≥ |G^ϕ : G_x^ϕ|`.
Squaring removes the half-integral exponent: `n₀² ≤ 2^k < C(k,⌊k/4⌋)²`.  The right-hand
inequality is proved by comparing `C(k,⌊k/4⌋)` with `C(4m,m)`, `m = ⌊k/4⌋`, and running the
four-step Pascal recurrence, which multiplies `C(4m,m)` by more than `4` at each step. -/

/-- The four-step ratio identity
`C(4m+4, m+1)·(m+1)(3m+1)(3m+2)(3m+3) = C(4m,m)·(4m+1)(4m+2)(4m+3)(4m+4)`,
obtained by four applications of the Pascal recurrences
`Nat.succ_mul_choose_eq` and `Nat.choose_mul_succ_eq`. -/
theorem choose_four_step_identity (m : ℕ) :
    (4 * m + 4).choose (m + 1) * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3))
      = (4 * m).choose m * ((4 * m + 1) * (4 * m + 2) * (4 * m + 3) * (4 * m + 4)) := by
  have h1 : (4 * m + 1) * (4 * m).choose m = (4 * m + 1).choose (m + 1) * (m + 1) :=
    Nat.succ_mul_choose_eq (4 * m) m
  have h2 : (4 * m + 1).choose (m + 1) * (4 * m + 2)
      = (4 * m + 2).choose (m + 1) * (3 * m + 1) := by
    have h := Nat.choose_mul_succ_eq (4 * m + 1) (m + 1)
    have he : 4 * m + 1 + 1 - (m + 1) = 3 * m + 1 := by omega
    rw [he] at h
    convert h using 2 <;> omega
  have h3 : (4 * m + 2).choose (m + 1) * (4 * m + 3)
      = (4 * m + 3).choose (m + 1) * (3 * m + 2) := by
    have h := Nat.choose_mul_succ_eq (4 * m + 2) (m + 1)
    have he : 4 * m + 2 + 1 - (m + 1) = 3 * m + 2 := by omega
    rw [he] at h
    convert h using 2 <;> omega
  have h4 : (4 * m + 3).choose (m + 1) * (4 * m + 4)
      = (4 * m + 4).choose (m + 1) * (3 * m + 3) := by
    have h := Nat.choose_mul_succ_eq (4 * m + 3) (m + 1)
    have he : 4 * m + 3 + 1 - (m + 1) = 3 * m + 3 := by omega
    rw [he] at h
    convert h using 2 <;> omega
  zify at h1 h2 h3 h4 ⊢
  linear_combination
    (-((m : ℤ) + 1) * (3 * m + 1) * (3 * m + 2)) * h4
      + (-((m : ℤ) + 1) * (3 * m + 1) * (4 * m + 4)) * h3
      + (-((m : ℤ) + 1) * (4 * m + 3) * (4 * m + 4)) * h2
      + (-(4 * (m : ℤ) + 2) * (4 * m + 3) * (4 * m + 4)) * h1

/-- `4·C(4m,m) ≤ C(4m+4, m+1)`: the four-step ratio is at least `4`. -/
theorem four_mul_choose_le (m : ℕ) :
    4 * (4 * m).choose m ≤ (4 * m + 4).choose (m + 1) := by
  have hid := choose_four_step_identity m
  have hPpos : 0 < (m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3) := by positivity
  have hPQ : 4 * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3))
      ≤ (4 * m + 1) * (4 * m + 2) * (4 * m + 3) * (4 * m + 4) := by
    have h : (4 * m + 1) * (4 * m + 2) * (4 * m + 3) * (4 * m + 4)
        = 4 * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3))
          + (148 * m ^ 4 + 316 * m ^ 3 + 212 * m ^ 2 + 44 * m) := by ring
    rw [h]
    exact Nat.le_add_right _ _
  refine Nat.le_of_mul_le_mul_right ?_ hPpos
  calc 4 * (4 * m).choose m * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3))
      = (4 * m).choose m * (4 * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3))) := by ring
    _ ≤ (4 * m).choose m * ((4 * m + 1) * (4 * m + 2) * (4 * m + 3) * (4 * m + 4)) :=
        Nat.mul_le_mul_left _ hPQ
    _ = (4 * m + 4).choose (m + 1) * ((m + 1) * (3 * m + 1) * (3 * m + 2) * (3 * m + 3)) :=
        hid.symm

/-- `256·C(4m, m) ≥ 1820·4^m` for `m ≥ 4` (base case `C(16,4) = 1820`). -/
theorem choose_four_mul_ge {m : ℕ} (hm : 4 ≤ m) : 1820 * 4 ^ m ≤ 256 * (4 * m).choose m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
      have hstep := four_mul_choose_le m
      calc 1820 * 4 ^ (m + 1) = 4 * (1820 * 4 ^ m) := by ring
        _ ≤ 4 * (256 * (4 * m).choose m) := Nat.mul_le_mul_left _ ih
        _ = 256 * (4 * (4 * m).choose m) := by ring
        _ ≤ 256 * (4 * m + 4).choose (m + 1) := Nat.mul_le_mul_left _ hstep

/-- **Eq. (53)**, §10.5: `C(k, ⌊k/4⌋)² > 2^k` for `k ≥ 9`, the combinatorial form of
`C(k, ⌊k/4⌋) > 2^{k/2}`. -/
theorem two_pow_lt_choose_quarter_sq {k : ℕ} (hk : 9 ≤ k) :
    2 ^ k < (k.choose (k / 4)) ^ 2 := by
  rcases Nat.lt_or_ge k 16 with hsmall | hbig
  · interval_cases k <;> decide
  · set m := k / 4 with hm
    have hm4 : 4 ≤ m := by omega
    have h4m : 4 * m ≤ k := by omega
    have hk4m : k ≤ 4 * m + 3 := by omega
    have hmono : (4 * m).choose m ≤ k.choose m := Nat.choose_le_choose m h4m
    have hC : 1820 * 4 ^ m ≤ 256 * k.choose m :=
      le_trans (choose_four_mul_ge hm4) (Nat.mul_le_mul_left _ hmono)
    have h2k : 2 ^ k ≤ 8 * 16 ^ m := by
      calc 2 ^ k ≤ 2 ^ (4 * m + 3) := Nat.pow_le_pow_right (by norm_num) hk4m
        _ = 8 * 16 ^ m := by rw [pow_add, pow_mul]; ring
    have hsq : (1820 * 4 ^ m) ^ 2 ≤ (256 * k.choose m) ^ 2 := Nat.pow_le_pow_left hC 2
    have h16 : (4 : ℕ) ^ m * 4 ^ m = 16 ^ m := by rw [← mul_pow]; norm_num
    have hL : (1820 * 4 ^ m) ^ 2 = 3312400 * 16 ^ m := by
      rw [← h16]; ring
    have hR : (256 * k.choose m) ^ 2 = 65536 * (k.choose m) ^ 2 := by rw [mul_pow]; norm_num
    rw [hL, hR] at hsq
    have hpos : 0 < (16 : ℕ) ^ m := pow_pos (by norm_num) m
    have hgap : 65536 * (8 * 16 ^ m) < 3312400 * 16 ^ m := by
      calc 65536 * (8 * 16 ^ m) = 524288 * 16 ^ m := by ring
        _ < 3312400 * 16 ^ m := (Nat.mul_lt_mul_right hpos).2 (by norm_num)
    have hfin : 65536 * 2 ^ k < 65536 * (k.choose m) ^ 2 :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ h2k) (lt_of_lt_of_le hgap hsq)
    exact Nat.lt_of_mul_lt_mul_left hfin

/-- Conjugating a sandwich set: if `T` is sandwiched by `H` then `T^c` is sandwiched by
`H^c`.  This is the content of Eq. (54). -/
theorem IsSandwichSet.map_conj {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {H : Subgroup (Equiv.Perm Γ)} {T : Set Γ} (c : Equiv.Perm Γ) (h : IsSandwichSet H T) :
    IsSandwichSet (H.map (MulAut.conj c).toMonoidHom) (c '' T) := by
  obtain ⟨hcard, hlo, hhi⟩ := h
  refine ⟨by rwa [Set.ncard_image_of_injective _ c.injective], ?_, ?_⟩
  · rintro a ⟨haA, hafix⟩
    have hconj : c⁻¹ * a * c ∈ alternatingGroup Γ := by
      have := (alternatingGroup Γ).normal_of_characteristic.conj_mem a haA c⁻¹
      simpa [mul_assoc] using this
    have hfix : ∀ y ∈ T, (c⁻¹ * a * c) y = y := by
      intro y hy
      have : a (c y) = c y := hafix (c y) ⟨y, hy, rfl⟩
      simp only [Equiv.Perm.mul_apply, this]
      simp
    refine ⟨c⁻¹ * a * c, hlo ⟨hconj, hfix⟩, ?_⟩
    show c * (c⁻¹ * a * c) * c⁻¹ = a
    group
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨trivial, ?_⟩
    have hbT : (b : Equiv.Perm Γ) '' T = T := (hhi hb).2
    show ((MulAut.conj c) b : Equiv.Perm Γ) '' (c '' T) = c '' T
    have : ((MulAut.conj c) b : Equiv.Perm Γ) = c * b * c⁻¹ := rfl
    rw [this, ← image_image_eq_mul_image, ← image_image_eq_mul_image]
    have hc : (c⁻¹ : Equiv.Perm Γ) '' (c '' T) = T := by
      rw [← Set.image_comp]
      refine Set.image_congr' (fun y => ?_) |>.trans (Set.image_id T)
      simp
    rw [hc, hbT]

section MainTheorem

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}
  {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))

theorem VeryLargeK.sq_le_two_pow {n : ℕ} (h : VeryLargeK k n) : n ^ 2 ≤ 2 ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Nat.one_le_two_pow
  have h2 : 2 * Real.logb 2 (n : ℝ) ≤ (k : ℝ) := le_trans (le_max_right _ _) h
  have hpos : (0 : ℝ) < ((n : ℝ) ^ 2) := by positivity
  have hlog : Real.logb 2 ((n : ℝ) ^ 2) ≤ (k : ℝ) := by
    rw [Real.logb_pow]
    push_cast
    linarith
  have hle := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hpos).1 hlog
  have hrpow : (2 : ℝ) ^ (k : ℝ) = ((2 ^ k : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  rw [hrpow] at hle
  exact_mod_cast hle

/-- **Eq. (53)**, §10.5: `n₀ < C(k, ⌊k/4⌋)`. -/
theorem maxOrbitLength_lt_choose (hk : VeryLargeK k (maxOrbitLength G)) :
    maxOrbitLength G < k.choose (k / 4) := by
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have h1 := hk.sq_le_two_pow
  have h2 := two_pow_lt_choose_quarter_sq hk9
  by_contra hcon
  push_neg at hcon
  have : (k.choose (k / 4)) ^ 2 ≤ (maxOrbitLength G) ^ 2 := Nat.pow_le_pow_left hcon 2
  omega

/-- `|G^ϕ : G_x^ϕ| ≤ |G : G_x| = |x^G| ≤ n₀`, the first two inequalities of Eq. (53). -/
theorem relIndex_map_stabilizer_le (x : Ω) :
    ((stabilizer G x).map ϕ).relIndex ϕ.range ≤ maxOrbitLength G := by
  have hdvd : ((stabilizer G x).map ϕ.rangeRestrict).index ≤ (stabilizer G x).index := by
    refine Nat.le_of_dvd ?_ (Subgroup.index_map_dvd _ ϕ.rangeRestrict_surjective)
    rw [← card_orbit_eq_index]
    haveI : Nonempty ↥(orbit G x) := ⟨⟨x, mem_orbit_self x⟩⟩
    exact Nat.card_pos
  rw [map_rangeRestrict_eq_subgroupOf] at hdvd
  calc ((stabilizer G x).map ϕ).relIndex ϕ.range
      = (((stabilizer G x).map ϕ).subgroupOf ϕ.range).index := rfl
    _ ≤ (stabilizer G x).index := hdvd
    _ = Nat.card (orbit G x) := (card_orbit_eq_index G x).symm
    _ ≤ maxOrbitLength G := card_orbit_le_maxOrbitLength G x

theorem theorem_10_5_1_a_proof (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) :
    (4 * (Tpoint ϕ x).ncard < k ∧ IsSandwichSet ((stabilizer G x).map ϕ) (Tpoint ϕ x)) ∧
      ∀ T : Set (Fin k), 4 * T.ncard < k → IsSandwichSet ((stabilizer G x).map ϕ) T →
        T = Tpoint ϕ x := by
  classical
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hcard : Nat.card (Fin k) = k := by simp
  set H := (stabilizer G x).map ϕ with hH
  have hHK : H ≤ ϕ.range := by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  have hindex : H.relIndex ϕ.range < (Nat.card (Fin k)).choose (k / 4) := by
    rw [hcard]
    exact lt_of_le_of_lt (relIndex_map_stabilizer_le ϕ x) (maxOrbitLength_lt_choose hk)
  obtain ⟨T, hT, hTr, huniq⟩ := theorem_10_4_2_of_four_mul_le hϕ hHK (r := k / 4)
    (by omega) (by rw [hcard]; omega) (by rw [hcard]; omega) hindex
  have hTpoint : Tpoint ϕ x = T := huniq _ (isSandwichSet_sandwichSet ⟨T, hT⟩)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hTpoint]; omega
  · rw [hTpoint]; exact hT
  · intro T' _ hT'
    rw [hTpoint]
    exact huniq _ hT'

theorem theorem_10_5_1_c_eq54_proof (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) (σ : G) :
    Tpoint ϕ (σ • x) = (ϕ σ) '' (Tpoint ϕ x) := by
  have hstab : (stabilizer G (σ • x)).map ϕ
      = ((stabilizer G x).map ϕ).map (MulAut.conj (ϕ σ)).toMonoidHom := by
    rw [stabilizer_smul_eq_stabilizer_map_conj, map_map_conj]
  have hsand := ((theorem_10_5_1_a_proof ϕ hϕ hk x).1.2).map_conj (ϕ σ)
  rw [← hstab] at hsand
  refine ((theorem_10_5_1_a_proof ϕ hϕ hk (σ • x)).2 _ ?_ hsand).symm
  rw [Set.ncard_image_of_injective _ (ϕ σ).injective]
  exact (theorem_10_5_1_a_proof ϕ hϕ hk x).1.1

theorem pointwiseStab_univ_eq_bot (G : Subgroup (Equiv.Perm Ω)) :
    pointwiseStab G (Set.univ : Set Ω) = ⊥ := by
  refine le_antisymm (fun σ hσ => ?_) bot_le
  rw [mem_pointwiseStab] at hσ
  exact Subgroup.mem_bot.2 (Subtype.ext (Equiv.ext fun y => hσ y (Set.mem_univ y)))

theorem theorem_10_5_1_d_proof (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G)) :
    (∃ x : Ω, Affected ϕ x) ∧
      alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ := by
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hmain := theorem_10_3_5 ϕ hϕ hk.largeK
  refine ⟨?_, hmain⟩
  by_contra hcon
  push_neg at hcon
  have huniv : unaffectedSet ϕ = (Set.univ : Set Ω) :=
    Set.eq_univ_of_forall fun x => hcon x
  rw [huniv, pointwiseStab_univ_eq_bot, Subgroup.map_bot] at hmain
  haveI : Nontrivial (alternatingGroup (Fin k)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin k))
  exact ha (Subtype.ext (Subgroup.mem_bot.1 (hmain a.2)))

end MainTheorem


/-! ### Theorem 10.5.1 (Main Structure Theorem) -/

/-- **Theorem 10.5.1 (a)** (Main Structure Theorem), §10.5.

> For every `x ∈ Ω` there exists a unique subset `T(x) ⊂ [k]` such that `|T(x)| < k/4` and
> `(A_k)_(T(x)) ≤ G_x^ϕ ≤ (S_k)_{T(x)}`.  (52)

Proof (the paper's): the Jordan–Liebeck theorem (Thm. 10.4.2) with `K = G^ϕ`,
`H = G_x^ϕ`, `r = ⌊k/4⌋`, using
`(k choose ⌊k/4⌋) > 2^{k/2} ≥ n₀ ≥ |x^G| = |G : G_x| ≥ |G^ϕ : G_x^ϕ|`.  (53)

Since Theorem 10.4.2 is false as printed, the form to use here is
`Babai.theorem_10_4_2_of_four_mul_le`: its hypothesis `4r ≤ k` holds for `r = ⌊k/4⌋`, so
the paper's conclusion is available and item (a) stands exactly as printed. -/
theorem theorem_10_5_1_a (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) :
    (4 * (Tpoint ϕ x).ncard < k ∧ IsSandwichSet ((stabilizer G x).map ϕ) (Tpoint ϕ x)) ∧
      ∀ T : Set (Fin k), 4 * T.ncard < k → IsSandwichSet ((stabilizer G x).map ϕ) T →
        T = Tpoint ϕ x :=
  theorem_10_5_1_a_proof ϕ hϕ hk x

/-- **Theorem 10.5.1 (b)**, §10.5.

> The element `x ∈ Ω` is affected by `ϕ` if and only if `|T(x)| ≥ 1`.

"Immediate from Eq. (52) and the definition of being affected." -/
theorem theorem_10_5_1_b (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) :
    Affected ϕ x ↔ 1 ≤ (Tpoint ϕ x).ncard := by
  obtain ⟨⟨-, hsand⟩, -⟩ := theorem_10_5_1_a ϕ hϕ hk x
  constructor
  · intro haff
    by_contra hcon
    push_neg at hcon
    have hzero : (Tpoint ϕ x).ncard = 0 := by omega
    have hempty : Tpoint ϕ x = ∅ := by
      by_contra hne
      obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
      have : 0 < (Tpoint ϕ x).ncard :=
        Set.ncard_pos (Set.toFinite _) |>.2 ⟨z, hz⟩
      omega
    -- `T(x) = ∅` means `A_k ≤ G_x^ϕ`, i.e. `x` is unaffected
    exact haff (by simpa [hempty] using hsand.2.1)
  · intro hcard haff
    -- `x` unaffected means `A_k ≤ G_x^ϕ`, so `∅` is a sandwich set, so `T(x) = ∅`
    have hk9 : 9 ≤ k := by
      have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
      exact_mod_cast this
    have hempty : IsSandwichSet ((stabilizer G x).map ϕ) (∅ : Set (Fin k)) := by
      refine ⟨by simp only [Set.ncard_empty, Nat.card_eq_fintype_card, Fintype.card_fin]; omega,
        by simpa using haff, by simp⟩
    have hTe : Tpoint ϕ x = ∅ := sandwichSet_unique (Ω := Fin k)
      (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) hsand hempty
    have hcard' : 1 ≤ (Tpoint ϕ x).ncard := hcard
    rw [hTe] at hcard'
    simp at hcard'

/-- **Theorem 10.5.1 (c)**, Eq. (54), §10.5.

> `G_{x^σ} = G_x^σ` and therefore `T(x^σ) = T(x)^{σ^ϕ}`. -/
theorem theorem_10_5_1_c_eq54 (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) (σ : G) : Tpoint ϕ (σ • x) = (ϕ σ) '' (Tpoint ϕ x) :=
  theorem_10_5_1_c_eq54_proof ϕ hϕ hk x σ

/-- **Theorem 10.5.1 (c)**, §10.5.

> For each orbit `Δ` there is an integer `t_Δ ≥ 0` such that `|T(x)| = t_Δ` for every
> `x ∈ Δ`.  We say that `Δ` is affected by `ϕ` if `t_Δ ≥ 1`, i.e. the elements of `Δ` are
> affected. -/
theorem theorem_10_5_1_c (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    {x y : Ω} (hy : y ∈ orbit G x) : tPoint ϕ y = tPoint ϕ x := by
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hy
  rw [tPoint, tPoint, theorem_10_5_1_c_eq54 ϕ hϕ hk x σ]
  exact Set.ncard_image_of_injective _ (ϕ σ).injective

/-! ### The standard blocks -/

section StandardBlocks

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}
  {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))

theorem mem_standardBlock_self (x : Ω) : x ∈ standardBlock ϕ x :=
  ⟨mem_orbit_self x, rfl⟩

theorem standardBlock_subset_orbit (x : Ω) : standardBlock ϕ x ⊆ orbit G x := fun _ hy => hy.1

/-- Two points of the same orbit with the same label have the same standard block. -/
theorem standardBlock_eq_of {y z : Ω} (horb : y ∈ orbit G z) (hT : Tpoint ϕ y = Tpoint ϕ z) :
    standardBlock ϕ y = standardBlock ϕ z := by
  have ho : orbit G y = orbit G z := orbit_eq_iff.2 horb
  ext w
  simp only [standardBlock, Set.mem_setOf_eq, ho, hT]

theorem standardBlock_eq_iff {y z : Ω} (horb : y ∈ orbit G z) :
    standardBlock ϕ y = standardBlock ϕ z ↔ Tpoint ϕ y = Tpoint ϕ z := by
  refine ⟨fun h => ?_, standardBlock_eq_of ϕ horb⟩
  have : y ∈ standardBlock ϕ z := h ▸ mem_standardBlock_self ϕ y
  exact this.2

/-- Eq. (54) in block form: `(B_y)^σ = B_{y^σ}`. -/
theorem image_standardBlock (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (y : Ω) (σ : G) :
    (σ : Equiv.Perm Ω) '' standardBlock ϕ y = standardBlock ϕ (σ • y) := by
  have hT : ∀ z : Ω, Tpoint ϕ (σ • z) = (ϕ σ) '' (Tpoint ϕ z) := fun z =>
    theorem_10_5_1_c_eq54 ϕ hϕ hk z σ
  ext w
  constructor
  · rintro ⟨z, ⟨hzo, hzT⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : σ • z ∈ orbit G z := mem_orbit z σ
      rw [orbit_eq_iff.2 (mem_orbit y σ), orbit_eq_iff.2 hzo] at *
      exact h1
    · show Tpoint ϕ (σ • z) = Tpoint ϕ (σ • y)
      rw [hT, hT, hzT]
  · rintro ⟨hwo, hwT⟩
    refine ⟨(σ⁻¹ : G) • w, ⟨?_, ?_⟩, ?_⟩
    · have h1 : (σ⁻¹ : G) • w ∈ orbit G w := mem_orbit w (σ⁻¹ : G)
      have h2 : orbit G w = orbit G y := by
        rw [orbit_eq_iff.2 hwo, orbit_eq_iff.2 (mem_orbit y σ)]
      rwa [h2] at h1
    · have hwz : σ • ((σ⁻¹ : G) • w) = w := by rw [smul_smul]; simp
      have := hT ((σ⁻¹ : G) • w)
      rw [hwz, hwT, hT] at this
      exact Set.image_injective.2 (ϕ σ).injective this.symm
    · show (σ : Equiv.Perm Ω) ((σ⁻¹ : G) • w) = w
      have : σ • ((σ⁻¹ : G) • w) = w := by rw [smul_smul]; simp
      exact this

theorem standardBlock_mem (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    {x y : Ω} (hy : y ∈ orbit G x) : standardBlock ϕ y ∈ standardBlocks ϕ (orbit G x) :=
  ⟨y, hy, rfl⟩

/-- **Theorem 10.5.1 (e)**, first half. -/
theorem theorem_10_5_1_e_isSystem_proof (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) :
    IsSystemOfImprimitivity G (orbit G x) (standardBlocks ϕ (orbit G x)) := by
  have hinv := isInvariant_orbit G x
  refine ⟨hinv, ?_, ?_, ?_, ?_, ⟨standardBlock ϕ x, ⟨x, mem_orbit_self x, rfl⟩⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, mem_standardBlock_self ϕ y⟩
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hne
    rw [Set.disjoint_left]
    rintro w hwy hwz
    refine hne ?_
    have h1 : standardBlock ϕ w = standardBlock ϕ y :=
      standardBlock_eq_of ϕ hwy.1 hwy.2
    have h2 : standardBlock ϕ w = standardBlock ϕ z :=
      standardBlock_eq_of ϕ hwz.1 hwz.2
    rw [← h1, h2]
  · ext w
    constructor
    · rintro ⟨B, ⟨y, hy, rfl⟩, hwB⟩
      have : w ∈ orbit G y := hwB.1
      rwa [orbit_eq_iff.2 hy] at this
    · intro hw
      exact ⟨standardBlock ϕ w, ⟨w, hw, rfl⟩, mem_standardBlock_self ϕ w⟩
  · rintro σ hσ _ ⟨y, hy, rfl⟩
    rw [image_standardBlock ϕ hϕ hk y ⟨σ, hσ⟩]
    refine ⟨(⟨σ, hσ⟩ : G) • y, ?_, rfl⟩
    have h1 : (⟨σ, hσ⟩ : G) • y ∈ orbit G y := mem_orbit y _
    rwa [orbit_eq_iff.2 hy] at h1
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have hzy : z ∈ orbit G y := by rw [orbit_eq_iff.2 hy]; exact hz
    obtain ⟨σ, hσ⟩ := mem_orbit_iff.1 hzy
    refine ⟨(σ : Equiv.Perm Ω), σ.2, ?_⟩
    rw [show ((σ : Equiv.Perm Ω)) '' standardBlock ϕ y = standardBlock ϕ (σ • y) from
      image_standardBlock ϕ hϕ hk y σ, hσ]

/-- **Theorem 10.5.1 (f)**. -/
theorem theorem_10_5_1_f_proof (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) {B : Set Ω} (hB : B ∈ standardBlocks ϕ (orbit G x)) {y : Ω} (hy : y ∈ B) :
    (setwiseStab G B).map ϕ = setwiseStabilizer ϕ.range (Tpoint ϕ y) := by
  obtain ⟨z, hz, rfl⟩ := hB
  have hBy : standardBlock ϕ y = standardBlock ϕ z := standardBlock_eq_of ϕ hy.1 hy.2
  have hkey : ∀ σ : G, ((σ : Equiv.Perm Ω) '' standardBlock ϕ z = standardBlock ϕ z)
      ↔ (ϕ σ) '' (Tpoint ϕ y) = Tpoint ϕ y := by
    intro σ
    rw [← hBy, image_standardBlock ϕ hϕ hk y σ,
      standardBlock_eq_iff ϕ (mem_orbit y σ), theorem_10_5_1_c_eq54 ϕ hϕ hk y σ]
  ext a
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, rfl⟩, (hkey σ).1 (mem_setwiseStab.1 hσ)⟩
  · rintro ⟨⟨σ, rfl⟩, hfix⟩
    exact ⟨σ, mem_setwiseStab.2 ((hkey σ).2 hfix), rfl⟩

/-- **Theorem 10.5.1 (e)**, the case `t_Δ = 0`. -/
theorem theorem_10_5_1_e_trivial_proof (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) (ht : tPoint ϕ x = 0) :
    standardBlocks ϕ (orbit G x) = {orbit G x} := by
  have hempty : ∀ y ∈ orbit G x, Tpoint ϕ y = ∅ := by
    intro y hy
    have h1 : tPoint ϕ y = 0 := by rw [theorem_10_5_1_c ϕ hϕ hk hy, ht]
    by_contra hne
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
    have : 0 < (Tpoint ϕ y).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨z, hz⟩
    rw [tPoint] at h1
    omega
  have hall : ∀ y ∈ orbit G x, standardBlock ϕ y = orbit G x := by
    intro y hy
    have ho : orbit G y = orbit G x := orbit_eq_iff.2 hy
    ext w
    simp only [standardBlock, Set.mem_setOf_eq, ho]
    refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
    rw [hempty w hw, hempty y hy]
  ext B
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hall y hy
  · intro hB
    rw [Set.mem_singleton_iff] at hB
    exact ⟨x, mem_orbit_self x, by rw [hB, hall x (mem_orbit_self x)]⟩

end StandardBlocks

/-- **Theorem 10.5.1 (d)**, §10.5.

> At least one orbit is affected.  In fact, if `D` is the union of the unaffected blocks
> then `G_(D)^ϕ ≥ A_k`.

The second half is Theorem 10.3.5 (Unaffected Stabilizers Lemma); the first half follows
from it, since `A_k ≤ G_(Ω)^ϕ = 1` is impossible for `k ≥ 9`. -/
theorem theorem_10_5_1_d (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G)) :
    (∃ x : Ω, Affected ϕ x) ∧
      alternatingGroup (Fin k) ≤ (pointwiseStab G (unaffectedSet ϕ)).map ϕ :=
  theorem_10_5_1_d_proof ϕ hϕ hk

/-- **Theorem 10.5.1 (e)**, §10.5, first half: the equivalence relation `T(x) = T(y)`
splits the orbit `Δ` into blocks of imprimitivity — a system of imprimitivity, since `G`
acts transitively on them. -/
theorem theorem_10_5_1_e_isSystem (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) :
    IsSystemOfImprimitivity G (orbit G x) (standardBlocks ϕ (orbit G x)) :=
  theorem_10_5_1_e_isSystem_proof ϕ hϕ hk x

/-- `t_Δ + 2 ≤ k`: from `4 t_Δ < k` (item (a)) and `k ≥ 9`. -/
theorem tPoint_add_two_le (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) : tPoint ϕ x + 2 ≤ k := by
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have h := (theorem_10_5_1_a ϕ hϕ hk x).1.1
  have ht : tPoint ϕ x = (Tpoint ϕ x).ncard := rfl
  omega

/-- Every `t_Δ`-subset of `[k]` is the label `T(y)` of some point `y` of the orbit `Δ`:
by Eq. (54) the labels transform by `ϕ`, and `A_k ≤ G^ϕ` is transitive on the
`t_Δ`-subsets (`Babai.exists_mem_image_eq_of_ncard_eq`).  This is the paper's step
"noting that `A_k` acts transitively on `[k] choose t_Δ`". -/
theorem exists_Tpoint_eq (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) {T : Set (Fin k)} (hT : T.ncard = tPoint ϕ x) :
    ∃ y ∈ orbit G x, Tpoint ϕ y = T := by
  have hkc : Nat.card (Fin k) = k := by simp
  obtain ⟨π, hπ, himg⟩ := exists_mem_image_eq_of_ncard_eq (Ω := Fin k)
    (K := alternatingGroup (Fin k)) le_rfl (T := Tpoint ϕ x) (U := T) rfl hT
    (by rw [hkc]; exact tPoint_add_two_le ϕ hϕ hk x)
  obtain ⟨σ, hσ⟩ := hϕ hπ
  exact ⟨σ • x, mem_orbit x σ, by rw [theorem_10_5_1_c_eq54 ϕ hϕ hk x σ, hσ, himg]⟩

/-- **Theorem 10.5.1 (e)**, §10.5: the standard blocks in `Δ` are "labeled by the
`t_Δ`-subsets of `[k]`", the label of a block being the common value of `T` on it. -/
theorem theorem_10_5_1_e_labels (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) :
    ∃ e : standardBlocks ϕ (orbit G x) ≃ {T : Set (Fin k) // T.ncard = tPoint ϕ x},
      ∀ (B : standardBlocks ϕ (orbit G x)) (y : Ω), y ∈ (B : Set Ω) →
        ((e B : {T : Set (Fin k) // T.ncard = tPoint ϕ x}) : Set (Fin k)) = Tpoint ϕ y := by
  classical
  -- a representative of each standard block, and the constancy of `T` on a block
  have hrep : ∀ B : standardBlocks ϕ (orbit G x),
      B.2.choose ∈ orbit G x ∧ (B : Set Ω) = standardBlock ϕ B.2.choose :=
    fun B => B.2.choose_spec
  have hlabel : ∀ (B : standardBlocks ϕ (orbit G x)) (y : Ω), y ∈ (B : Set Ω) →
      Tpoint ϕ y = Tpoint ϕ B.2.choose := by
    intro B y hy
    rw [(hrep B).2] at hy
    exact hy.2
  have hcard : ∀ B : standardBlocks ϕ (orbit G x),
      (Tpoint ϕ B.2.choose).ncard = tPoint ϕ x :=
    fun B => theorem_10_5_1_c ϕ hϕ hk (hrep B).1
  set f : standardBlocks ϕ (orbit G x) → {T : Set (Fin k) // T.ncard = tPoint ϕ x} :=
    fun B => ⟨Tpoint ϕ B.2.choose, hcard B⟩ with hf
  have hinj : Function.Injective f := by
    intro B B' hBB'
    have hT : Tpoint ϕ B.2.choose = Tpoint ϕ B'.2.choose := congrArg Subtype.val hBB'
    have horb : B.2.choose ∈ orbit G B'.2.choose := by
      rw [orbit_eq_iff.2 (hrep B').1]; exact (hrep B).1
    refine Subtype.ext ?_
    rw [(hrep B).2, (hrep B').2]
    exact standardBlock_eq_of ϕ horb hT
  have hsurj : Function.Surjective f := by
    rintro ⟨T, hT⟩
    obtain ⟨y, hy, hTy⟩ := exists_Tpoint_eq ϕ hϕ hk x hT
    refine ⟨⟨standardBlock ϕ y, ⟨y, hy, rfl⟩⟩, Subtype.ext ?_⟩
    show Tpoint ϕ _ = T
    rw [← hlabel _ y (mem_standardBlock_self ϕ y), hTy]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun B y hy => ?_⟩
  show Tpoint ϕ B.2.choose = Tpoint ϕ y
  exact (hlabel B y hy).symm

/-- **Theorem 10.5.1 (e)**, §10.5: there are `(k choose t_Δ)` standard blocks in `Δ`. -/
theorem theorem_10_5_1_e_card (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) :
    Nat.card (standardBlocks ϕ (orbit G x)) = k.choose (tPoint ϕ x) := by
  classical
  obtain ⟨e, -⟩ := theorem_10_5_1_e_labels ϕ hϕ hk x
  have h1 : Nat.card (standardBlocks ϕ (orbit G x))
      = Nat.card {T : Set (Fin k) // T.ncard = tPoint ϕ x} := Nat.card_congr e
  have h2 : Nat.card {T : Set (Fin k) // T.ncard = tPoint ϕ x}
      = Nat.card (Set.powersetCard (Fin k) (tPoint ϕ x)) := by
    refine Nat.card_congr ⟨fun T => ⟨(T : Set (Fin k)).toFinset, ?_⟩,
      fun s => ⟨((s : Finset (Fin k)) : Set (Fin k)), ?_⟩, fun T => ?_, fun s => ?_⟩
    · show (T : Set (Fin k)).toFinset.card = tPoint ϕ x
      rw [← Set.ncard_eq_toFinset_card']; exact T.2
    · show ((s : Finset (Fin k)) : Set (Fin k)).ncard = tPoint ϕ x
      rw [Set.ncard_coe_finset]; exact s.2
    · exact Subtype.ext (by simp)
    · refine Subtype.ext (Finset.ext fun a => ?_)
      simp only [Set.mem_toFinset, Finset.mem_coe]
  rw [h1, h2, Set.powersetCard.card]
  simp

/-- **Theorem 10.5.1 (e)**, §10.5, the namesake conclusion:

> The action of `G` on the set of standard blocks in `Δ` is `A_k^(t_Δ)` or `S_k^(t_Δ)`.

The labelling bijection `e` of `theorem_10_5_1_e_labels` carries the block set onto the
`t_Δ`-subsets of `[k]`; transporting the action `G^ℬ` (`Babai.onBlocks`) along `e` gives
the Johnson group `A_k^(t_Δ)` (`Babai.JohnsonA`) or `S_k^(t_Δ)` (`Babai.JohnsonS`),
according to whether `G^ϕ = A_k` or `G^ϕ = S_k`.  The labelling clause is restated here
membershipwise (`a ∈ label ↔ a ∈ T(y)`) to avoid a `Set.toFinset` decidability side
condition. -/
theorem theorem_10_5_1_e_johnson (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) :
    ∃ e : (standardBlocks ϕ (orbit G x)) ≃ binom (Fin k) (tPoint ϕ x),
      (∀ (B : standardBlocks ϕ (orbit G x)) (y : Ω), y ∈ (B : Set Ω) →
          ∀ a : Fin k, a ∈ ((e B : binom (Fin k) (tPoint ϕ x)) : Finset (Fin k)) ↔
            a ∈ Tpoint ϕ y) ∧
        ((onBlocks G (standardBlocks ϕ (orbit G x))
              (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes).map
            (Equiv.permCongrHom e).toMonoidHom = JohnsonA k (tPoint ϕ x) ∨
          (onBlocks G (standardBlocks ϕ (orbit G x))
              (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes).map
            (Equiv.permCongrHom e).toMonoidHom = JohnsonS k (tPoint ϕ x)) := by
  classical
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  obtain ⟨e₀, he₀⟩ := theorem_10_5_1_e_labels ϕ hϕ hk x
  -- the labelling bijection, with `Finset`-valued labels
  have hlab : ∀ (B : standardBlocks ϕ (orbit G x)) (y : Ω), y ∈ (B : Set Ω) →
      ∀ a : Fin k,
        a ∈ (((e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))) B :
          binom (Fin k) (tPoint ϕ x)) : Finset (Fin k)) ↔ a ∈ Tpoint ϕ y := by
    intro B y hy a
    exact (mem_setNcardEquivBinom (e₀ B) a).trans (by rw [he₀ B y hy])
  refine ⟨e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x)), hlab, ?_⟩
  -- every standard block is nonempty
  have hne : ∀ B : standardBlocks ϕ (orbit G x), ((B : Set Ω)).Nonempty := by
    intro B
    obtain ⟨z, -, hBz⟩ := B.2
    exact ⟨z, by rw [hBz]; exact mem_standardBlock_self ϕ z⟩
  -- Eq. (54): through the labelling, `σ` acts on the blocks as `ϕ σ` acts on `t`-subsets
  have hkey : ∀ σ : G,
      (Equiv.permCongrHom (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))))
          (blockHom G (standardBlocks ϕ (orbit G x))
            (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes σ)
        = tAction (tPoint ϕ x) (ϕ σ) := by
    intro σ
    refine Equiv.ext fun s => Subtype.ext (Finset.ext fun a => ?_)
    obtain ⟨y, hy⟩ := hne ((e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))).symm s)
    set B := (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))).symm s with hB
    have hsB : (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))) B = s :=
      Equiv.apply_symm_apply _ s
    -- the image block, and the point `σ • y` in it
    have hyimg : (σ : Equiv.Perm Ω) • y ∈
        ((blockHom G (standardBlocks ϕ (orbit G x))
          (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes σ B : standardBlocks ϕ (orbit G x)) :
            Set Ω) := by
      rw [blockHom_apply_coe]
      exact ⟨y, hy, rfl⟩
    have hL := hlab _ _ hyimg a
    have hR : ∀ z : Fin k, z ∈ ((s : binom (Fin k) (tPoint ϕ x)) : Finset (Fin k)) ↔
        z ∈ Tpoint ϕ y := by
      intro z
      rw [← hsB]
      exact hlab B y hy z
    show a ∈ (((Equiv.permCongrHom
        (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x)))) _ s :
          binom (Fin k) (tPoint ϕ x)) : Finset (Fin k)) ↔ _
    rw [tAction_apply_coe]
    have hLHS : a ∈ (((Equiv.permCongrHom
        (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x))))
          (blockHom G (standardBlocks ϕ (orbit G x))
            (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes σ) s :
          binom (Fin k) (tPoint ϕ x)) : Finset (Fin k)) ↔ a ∈ Tpoint ϕ ((σ : G) • y) := hL
    rw [hLHS, theorem_10_5_1_c_eq54 ϕ hϕ hk y σ]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_image.2 ⟨z, (hR z).2 hz, rfl⟩
    · intro ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨z, (hR z).1 hz, rfl⟩
  -- so the transported group is `G^ϕ` acting on `t`-subsets
  have hrange : (onBlocks G (standardBlocks ϕ (orbit G x))
        (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes).map
      (Equiv.permCongrHom (e₀.trans (setNcardEquivBinom (Fin k) (tPoint ϕ x)))).toMonoidHom
      = inducedOnTSets ϕ.range (tPoint ϕ x) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨σ, rfl⟩ := hq
      exact ⟨ϕ σ, ⟨σ, rfl⟩, (hkey σ).symm⟩
    · rintro ⟨π, hπ, rfl⟩
      obtain ⟨σ, rfl⟩ := hπ
      exact ⟨blockHom G (standardBlocks ϕ (orbit G x))
        (theorem_10_5_1_e_isSystem ϕ hϕ hk x).permutes σ, ⟨σ, rfl⟩, hkey σ⟩
  rcases eq_alternating_or_top (K := ϕ.range) hϕ
      (by simp only [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) with hr | hr
  · exact Or.inl (by rw [hrange, hr]; rfl)
  · exact Or.inr (by rw [hrange, hr]; rfl)

/-- **Theorem 10.5.1 (e)**, §10.5: "If `t_Δ ≥ 1` then this is a Johnson group and the
kernel of this action is `ker ϕ`." -/
theorem theorem_10_5_1_e_ker (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) (ht : 1 ≤ tPoint ϕ x) (σ : G) :
    (∀ B ∈ standardBlocks ϕ (orbit G x), (σ : Equiv.Perm Ω) '' B = B) ↔ ϕ σ = 1 := by
  constructor
  · -- `σ` fixes every standard block ⇒ `ϕ σ` fixes every `t_Δ`-subset of `[k]` setwise
    intro hfix
    refine eq_one_of_image_eq_of_ncard_eq (t := tPoint ϕ x) ht ?_ ?_
    · have := tPoint_add_two_le ϕ hϕ hk x
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    · intro T hT
      obtain ⟨y, hy, hTy⟩ := exists_Tpoint_eq ϕ hϕ hk x hT
      have hB : standardBlock ϕ y ∈ standardBlocks ϕ (orbit G x) := ⟨y, hy, rfl⟩
      have himg := hfix _ hB
      rw [image_standardBlock ϕ hϕ hk y σ] at himg
      have hTeq : Tpoint ϕ (σ • y) = Tpoint ϕ y :=
        (standardBlock_eq_iff ϕ (mem_orbit y σ)).1 himg
      rw [theorem_10_5_1_c_eq54 ϕ hϕ hk y σ, hTy] at hTeq
      exact hTeq
  · -- `ϕ σ = 1` ⇒ `σ` maps each standard block to itself
    rintro h1 _ ⟨y, hy, rfl⟩
    rw [image_standardBlock ϕ hϕ hk y σ]
    refine standardBlock_eq_of ϕ (mem_orbit y σ) ?_
    rw [theorem_10_5_1_c_eq54 ϕ hϕ hk y σ, h1]
    simp

/-- **Theorem 10.5.1 (e)**, §10.5: "if `t_Δ = 0` then the action is trivial (its kernel is
`G`, there is just one block, namely `Δ`)." -/
theorem theorem_10_5_1_e_trivial (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) (ht : tPoint ϕ x = 0) :
    standardBlocks ϕ (orbit G x) = {orbit G x} :=
  theorem_10_5_1_e_trivial_proof ϕ hϕ hk x ht

/-- **Theorem 10.5.1 (f)**, §10.5.

> If `B ⊆ ∆` is a standard block and `x ∈ B` then `G_B^ϕ = (G^ϕ)_{T(x)}` (so it is either
> `(S_k)_{T(x)}` or `(A_k)_{T(x)}`). -/
theorem theorem_10_5_1_f (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) {B : Set Ω} (hB : B ∈ standardBlocks ϕ (orbit G x)) {y : Ω} (hy : y ∈ B) :
    (setwiseStab G B).map ϕ = setwiseStabilizer ϕ.range (Tpoint ϕ y) :=
  theorem_10_5_1_f_proof ϕ hϕ hk x hB hy

/-! ### Blocks and their setwise stabilizers

The three facts about a system of imprimitivity that the proof of item (g) uses. -/

section BlockStabilizers

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}

/-- In a system of imprimitivity, an element carrying a point of a block into that block
stabilizes the block setwise. -/
theorem mem_setwiseStab_of_smul_mem {Δ : Set Ω} {Ψ : Set (Set Ω)}
    (hΨ : IsSystemOfImprimitivity G Δ Ψ) {C : Set Ω} (hC : C ∈ Ψ) {y : Ω} (hy : y ∈ C)
    {σ : G} (hσ : σ • y ∈ C) : σ ∈ setwiseStab G C := by
  rw [mem_setwiseStab]
  by_contra hne
  have h1 : (σ : Equiv.Perm Ω) '' C ∈ Ψ := hΨ.permutes σ σ.2 C hC
  have hdisj := hΨ.pairwiseDisjoint _ h1 _ hC hne
  rw [Set.disjoint_left] at hdisj
  exact hdisj ⟨y, hy, rfl⟩ hσ

/-- The stabilizer of a point of a block lies in the setwise stabilizer of the block. -/
theorem stabilizer_le_setwiseStab {Δ : Set Ω} {Ψ : Set (Set Ω)}
    (hΨ : IsSystemOfImprimitivity G Δ Ψ) {C : Set Ω} (hC : C ∈ Ψ) {y : Ω} (hy : y ∈ C) :
    stabilizer G y ≤ setwiseStab G C := fun σ hσ =>
  mem_setwiseStab_of_smul_mem hΨ hC hy (by rw [mem_stabilizer_iff.1 hσ]; exact hy)

/-- A block of a system of imprimitivity on a `G`-orbit is a single orbit of its own
setwise stabilizer. -/
theorem exists_mem_setwiseStab_smul_eq {x : Ω} {Ψ : Set (Set Ω)}
    (hΨ : IsSystemOfImprimitivity G (orbit G x) Ψ) {C : Set Ω} (hC : C ∈ Ψ) {y z : Ω}
    (hy : y ∈ C) (hz : z ∈ C) : ∃ σ : G, σ ∈ setwiseStab G C ∧ σ • y = z := by
  have hyΔ : y ∈ orbit G x := by rw [← hΨ.covers]; exact ⟨C, hC, hy⟩
  have hzΔ : z ∈ orbit G x := by rw [← hΨ.covers]; exact ⟨C, hC, hz⟩
  have hzy : z ∈ orbit G y := by rw [orbit_eq_iff.2 hyΔ]; exact hzΔ
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hzy
  exact ⟨σ, mem_setwiseStab_of_smul_mem hΨ hC hy hz, rfl⟩

/-- "`H = G_{Cᵢ}` … is a maximal subgroup of `G`" (proof of Theorem 10.5.1 (g)): for a
*minimal* system of imprimitivity on a `G`-orbit — one whose blocks are maximal — the
setwise stabilizer of a block is a maximal subgroup of `G`.

Proof: for `G_C ≤ K ≤ G` the orbit `y^K` of a point `y ∈ C` is a block of imprimitivity
(because `G_y ≤ G_C ≤ K`) containing `C`, so by maximality of the blocks it is `C` or the
whole orbit; in the first case `K ≤ G_C`, in the second `K = G`. -/
theorem setwiseStab_maximal {x : Ω} {Ψ : Set (Set Ω)}
    (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ) {C : Set Ω} (hC : C ∈ Ψ) {y : Ω}
    (hy : y ∈ C) {K : Subgroup G} (hK : setwiseStab G C ≤ K) :
    K = setwiseStab G C ∨ K = ⊤ := by
  have hyΔ : y ∈ orbit G x := by rw [← hΨ.covers]; exact ⟨C, hC, hy⟩
  have hstab : stabilizer G y ≤ setwiseStab G C :=
    stabilizer_le_setwiseStab hΨ.toIsSystemOfImprimitivity hC hy
  -- `C' = y^K`
  have hmemC' : ∀ z : Ω, z ∈ orbit K y ↔ ∃ κ : K, ((κ : G) • y : Ω) = z := by
    intro z
    exact mem_orbit_iff
  have hCsub : C ⊆ orbit K y := by
    intro z hz
    obtain ⟨σ, hσ, rfl⟩ := exists_mem_setwiseStab_smul_eq hΨ.toIsSystemOfImprimitivity hC hy hz
    exact (hmemC' _).2 ⟨⟨σ, hK hσ⟩, rfl⟩
  have hC'sub : orbit K y ⊆ orbit G x := by
    intro z hz
    obtain ⟨κ, rfl⟩ := (hmemC' z).1 hz
    have : ((κ : G) • y : Ω) ∈ orbit G y := mem_orbit y _
    rwa [orbit_eq_iff.2 hyΔ] at this
  have hC'block : IsBlockOfImprimitivity G (orbit K y) := by
    refine ⟨⟨y, (hmemC' y).2 ⟨1, by simp⟩⟩, fun g hg => ?_⟩
    by_cases hmem : (⟨g, hg⟩ : G) ∈ K
    · left
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        obtain ⟨κ, rfl⟩ := (hmemC' z).1 hz
        refine (hmemC' _).2 ⟨⟨(⟨g, hg⟩ : G) * (κ : G), K.mul_mem hmem κ.2⟩, ?_⟩
        rw [← smul_smul]
        rfl
      · intro z hz
        obtain ⟨κ, rfl⟩ := (hmemC' z).1 hz
        refine ⟨(((⟨g, hg⟩ : G)⁻¹ * (κ : G)) • y : Ω),
          (hmemC' _).2 ⟨⟨(⟨g, hg⟩ : G)⁻¹ * (κ : G),
            K.mul_mem (K.inv_mem hmem) κ.2⟩, rfl⟩, ?_⟩
        show ((⟨g, hg⟩ : G) • (((⟨g, hg⟩ : G)⁻¹ * (κ : G)) • y) : Ω) = _
        rw [smul_smul, mul_inv_cancel_left]
    · right
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨⟨z, hz, rfl⟩, hw2⟩
      obtain ⟨κ₁, rfl⟩ := (hmemC' z).1 hz
      obtain ⟨κ₂, hκ₂⟩ := (hmemC' _).1 hw2
      refine hmem ?_
      have hfix : ((κ₂ : G)⁻¹ * (⟨g, hg⟩ : G) * (κ₁ : G)) • y = y := by
        have h2 : ((⟨g, hg⟩ : G) * (κ₁ : G)) • y = (κ₂ : G) • y := by
          rw [mul_smul]; exact hκ₂.symm
        calc ((κ₂ : G)⁻¹ * (⟨g, hg⟩ : G) * (κ₁ : G)) • y
            = (κ₂ : G)⁻¹ • (((⟨g, hg⟩ : G) * (κ₁ : G)) • y) := by
              rw [← mul_smul, ← mul_assoc]
          _ = (κ₂ : G)⁻¹ • ((κ₂ : G) • y) := by rw [h2]
          _ = y := inv_smul_smul _ _
      have : ((κ₂ : G)⁻¹ * (⟨g, hg⟩ : G) * (κ₁ : G)) ∈ stabilizer G y :=
        mem_stabilizer_iff.2 hfix
      have hK' : ((κ₂ : G)⁻¹ * (⟨g, hg⟩ : G) * (κ₁ : G)) ∈ K := hK (hstab this)
      have : (⟨g, hg⟩ : G) = (κ₂ : G) * ((κ₂ : G)⁻¹ * (⟨g, hg⟩ : G) * (κ₁ : G)) * (κ₁ : G)⁻¹ := by
        simp [mul_assoc]
      rw [this]
      exact K.mul_mem (K.mul_mem κ₂.2 hK') (K.inv_mem κ₁.2)
  rcases hΨ.blocks_maximal C hC (orbit K y) hC'sub hCsub hC'block with hCC | hCΔ
  · left
    refine le_antisymm (fun κ hκ => ?_) hK
    have : ((⟨κ, hκ⟩ : K) : G) • y ∈ orbit K y := mem_orbit y _
    rw [hCC] at this
    exact mem_setwiseStab_of_smul_mem hΨ.toIsSystemOfImprimitivity hC hy this
  · right
    refine (Subgroup.eq_top_iff' K).2 fun σ => ?_
    have hσ : (σ • y : Ω) ∈ orbit K y := by
      rw [hCΔ]
      have : (σ • y : Ω) ∈ orbit G y := mem_orbit y σ
      rwa [orbit_eq_iff.2 hyΔ] at this
    obtain ⟨κ, hκ⟩ := (hmemC' _).1 hσ
    have hfix : ((κ : G)⁻¹ * σ) • y = y := by
      rw [mul_smul, ← hκ, inv_smul_smul]
    have hK' : ((κ : G)⁻¹ * σ) ∈ K := hK (hstab (mem_stabilizer_iff.2 hfix))
    have : (σ : G) = (κ : G) * ((κ : G)⁻¹ * σ) := by simp
    rw [this]
    exact K.mul_mem κ.2 hK'

/-- Relative indices decrease along `A ≤ B ≤ K`. -/
theorem relIndex_le_of_le {M : Type*} [Group M] [Finite M] {A B K : Subgroup M}
    (hAB : A ≤ B) (hBK : B ≤ K) : B.relIndex K ≤ A.relIndex K := by
  have h := Subgroup.relIndex_mul_relIndex A B K hAB hBK
  have hpos : A.relIndex K ≠ 0 := by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) ⟨A.relIndex B, by rw [← h]; ring⟩

/-- Two subgroups containing the kernel of `f` and with the same image under `f` are
equal. -/
theorem eq_of_map_eq_of_ker_le {A B : Type*} [Group A] [Group B] {f : A →* B}
    {P Q : Subgroup A} (hP : f.ker ≤ P) (hQ : f.ker ≤ Q) (h : P.map f = Q.map f) : P = Q := by
  have key : ∀ (P Q : Subgroup A), f.ker ≤ Q → P.map f = Q.map f → P ≤ Q := by
    intro P Q hQ h a ha
    have : f a ∈ Q.map f := by rw [← h]; exact ⟨a, ha, rfl⟩
    obtain ⟨q, hq, hfq⟩ := this
    have hmem : a * q⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfq, mul_inv_cancel]
    have := Q.mul_mem (hQ hmem) hq
    simpa using this
  exact le_antisymm (key P Q hQ h) (key Q P hP h.symm)

/-- Orbit–stabilizer for a system of imprimitivity: `|G : G_C| = |Ψ|`. -/
theorem index_setwiseStab_eq_card {Δ : Set Ω} {Ψ : Set (Set Ω)}
    (hΨ : IsSystemOfImprimitivity G Δ Ψ) {C : Set Ω} (hC : C ∈ Ψ) :
    (setwiseStab G C).index = Nat.card Ψ := by
  classical
  refine Nat.card_eq_of_bijective
    (fun q : G ⧸ setwiseStab G C => Quotient.liftOn q
      (fun σ : G => (⟨(σ : Equiv.Perm Ω) '' C, hΨ.permutes σ σ.2 C hC⟩ : Ψ))
      (by
        intro a b hab
        have h : a⁻¹ * b ∈ setwiseStab G C := QuotientGroup.eq.1 (Quotient.sound hab)
        rw [mem_setwiseStab] at h
        refine Subtype.ext ?_
        show (a : Equiv.Perm Ω) '' C = (b : Equiv.Perm Ω) '' C
        have : ((a : Equiv.Perm Ω)⁻¹ * (b : Equiv.Perm Ω)) '' C = C := h
        rw [← image_image_eq_mul_image] at this
        have := congrArg (fun S => (a : Equiv.Perm Ω) '' S) this
        simp only [image_image_eq_mul_image, mul_inv_cancel_left] at this
        exact this.symm)) ?_
  constructor
  · intro p q hpq
    induction p using Quotient.inductionOn with
    | _ a =>
      induction q using Quotient.inductionOn with
      | _ b =>
        have h : (a : Equiv.Perm Ω) '' C = (b : Equiv.Perm Ω) '' C := by
          simpa [Subtype.ext_iff] using hpq
        refine QuotientGroup.eq.2 ?_
        rw [mem_setwiseStab]
        show ((a : Equiv.Perm Ω)⁻¹ * (b : Equiv.Perm Ω)) '' C = C
        rw [← image_image_eq_mul_image, ← h, image_image_eq_mul_image]
        simp
  · rintro ⟨C', hC'⟩
    obtain ⟨σ, hσ, hσC⟩ := hΨ.transitiveOnBlocks C hC C' hC'
    exact ⟨QuotientGroup.mk (⟨σ, hσ⟩ : G), Subtype.ext hσC⟩

end BlockStabilizers

section ItemG

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Equiv.Perm Ω)}
  {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))

/-- "First we note that `r ≥ 3` … because the kernel of the action on `Ψ` has index
`≥ k!/2` and therefore `r! ≥ k!/2`" (proof of Theorem 10.5.1 (g)). -/
theorem three_le_card_of_ker_eq (hϕ : IsGiantRep ϕ) (hk9 : 9 ≤ k)
    {Δ : Set Ω} {Ψ : Set (Set Ω)} (hΨ : IsSystemOfImprimitivity G Δ Ψ)
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1) :
    3 ≤ Nat.card Ψ := by
  classical
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hkereq : (blockHom G Ψ hΨ.permutes).ker = ϕ.ker := by
    ext σ
    constructor
    · intro h; exact MonoidHom.mem_ker.2 ((hker σ).1 (mem_ker_blockHom.1 h))
    · intro h; exact mem_ker_blockHom.2 ((hker σ).2 (MonoidHom.mem_ker.1 h))
  have hcard1 : Nat.card ϕ.range = Nat.card (blockHom G Ψ hΨ.permutes).range := by
    have e1 := (QuotientGroup.quotientKerEquivRange ϕ).toEquiv
    have e2 := (QuotientGroup.quotientKerEquivRange (blockHom G Ψ hΨ.permutes)).toEquiv
    rw [← Nat.card_congr e1, ← Nat.card_congr e2, hkereq]
  have hle : Nat.card (blockHom G Ψ hΨ.permutes).range ≤ Nat.card (Equiv.Perm ↥Ψ) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [Nat.card_perm] at hle
  have hA : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card ϕ.range :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hϕ) (Subgroup.inclusion_injective hϕ)
  have h2A : 2 * Nat.card (alternatingGroup (Fin k)) = Nat.card (Equiv.Perm (Fin k)) :=
    two_mul_nat_card_alternatingGroup
  rw [Nat.card_perm] at h2A
  have hfin : Nat.card (Fin k) = k := by simp
  rw [hfin] at h2A
  by_contra hcon
  push_neg at hcon
  have hr : (Nat.card ↥Ψ).factorial ≤ 2 := by
    have := Nat.factorial_le (show Nat.card ↥Ψ ≤ 2 by omega)
    simpa using this
  have h9 : Nat.factorial 9 ≤ Nat.factorial k := Nat.factorial_le hk9
  have h9v : Nat.factorial 9 = 362880 := by decide
  omega

/-- `ker ϕ` fixes every standard block setwise (the easy half of Theorem 10.5.1 (e)'s
kernel statement, which needs no hypothesis on `t_Δ`). -/
theorem ker_le_setwiseStab_standardBlock (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (y : Ω) :
    ϕ.ker ≤ setwiseStab G (standardBlock ϕ y) := by
  intro σ hσ
  rw [mem_setwiseStab, image_standardBlock ϕ hϕ hk y σ]
  refine standardBlock_eq_of ϕ (mem_orbit y σ) ?_
  rw [theorem_10_5_1_c_eq54 ϕ hϕ hk y σ, MonoidHom.mem_ker.1 hσ]
  simp

/-- The core of the proof of Theorem 10.5.1 (g).  For a block `C ∈ Ψ` and a point `y ∈ C`,
with `H = G_C` and `T' = T(H^ϕ)`:
`H^ϕ = (G^ϕ)_{T'}`, `|Ψ| = C(k, |T'|)`, and `T' ⊊ T(y)`. -/
theorem theorem_10_5_1_g_core (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) {Ψ : Set (Set Ω)} (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ)
    (hΨne : Ψ ≠ standardBlocks ϕ (orbit G x))
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1)
    {C : Set Ω} (hC : C ∈ Ψ) {y : Ω} (hy : y ∈ C) :
    4 * (sandwichSet ((setwiseStab G C).map ϕ)).ncard < k ∧
      (setwiseStab G C).map ϕ
          = setwiseStabilizer ϕ.range (sandwichSet ((setwiseStab G C).map ϕ)) ∧
        Nat.card Ψ = k.choose (sandwichSet ((setwiseStab G C).map ϕ)).ncard ∧
          sandwichSet ((setwiseStab G C).map ϕ) ⊂ Tpoint ϕ y := by
  classical
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hkc : Nat.card (Fin k) = k := by simp
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h3 := three_le_card_of_ker_eq ϕ hϕ hk9 hΨ.toIsSystemOfImprimitivity hker
  have hyΔ : y ∈ orbit G x := by rw [← hΨ.covers]; exact ⟨C, hC, hy⟩
  -- `N ≤ H` and `G_y ≤ H`
  have hNH : ϕ.ker ≤ setwiseStab G C := by
    intro σ hσ
    rw [mem_setwiseStab]
    exact (hker σ).2 (MonoidHom.mem_ker.1 hσ) C hC
  have hstabH : stabilizer G y ≤ setwiseStab G C :=
    stabilizer_le_setwiseStab hΨ.toIsSystemOfImprimitivity hC hy
  have hHK : (setwiseStab G C).map ϕ ≤ ϕ.range := by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  have hstabϕ : (stabilizer G y).map ϕ ≤ (setwiseStab G C).map ϕ := Subgroup.map_mono hstabH
  -- `|G^ϕ : H^ϕ| = |G : H| = r`
  have hindexr : ((setwiseStab G C).map ϕ).relIndex ϕ.range = Nat.card Ψ := by
    have h1 : ((setwiseStab G C).map ϕ).relIndex ϕ.range
        = ((setwiseStab G C).map ϕ.rangeRestrict).index := by
      rw [map_rangeRestrict_eq_subgroupOf]; rfl
    rw [h1, Subgroup.index_map_eq _ ϕ.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hNH),
      index_setwiseStab_eq_card hΨ.toIsSystemOfImprimitivity hC]
  -- Eq. (53)
  have hindexlt : ((setwiseStab G C).map ϕ).relIndex ϕ.range
      < (Nat.card (Fin k)).choose (k / 4) := by
    rw [hkc]
    exact lt_of_le_of_lt (le_trans (relIndex_le_of_le hstabϕ hHK)
      (relIndex_map_stabilizer_le ϕ y)) (maxOrbitLength_lt_choose hk)
  obtain ⟨T, hT, hTr, huniq⟩ := theorem_10_4_2_of_four_mul_le hϕ hHK (r := k / 4)
    (by omega) (by rw [hkc]; omega) (by rw [hkc]; omega) hindexlt
  have hTs : sandwichSet ((setwiseStab G C).map ϕ) = T :=
    huniq _ (isSandwichSet_sandwichSet ⟨T, hT⟩)
  rw [hTs]
  -- `T' ⊆ T(y)` by Observation 10.4.1
  have hTy := (theorem_10_5_1_a ϕ hϕ hk y).1.2
  have hsub : T ⊆ Tpoint ϕ y :=
    observation_10_4_1 hTy.1 hT.1 (by rw [hkc]; omega)
      (le_trans (le_trans hTy.2.1 hstabϕ) hT.2.2)
  -- `T' ≠ ∅`, because `r ≥ 3`
  have hTne : T ≠ ∅ := by
    intro h0
    have hAle : alternatingGroup (Fin k) ≤ (setwiseStab G C).map ϕ := by
      have := hT.2.1
      rwa [h0, pointwiseStabilizer_empty] at this
    have h1 : (alternatingGroup (Fin k)).relIndex ϕ.range * ϕ.range.index
        = (alternatingGroup (Fin k)).index := Subgroup.relIndex_mul_index hϕ
    have h2 : (alternatingGroup (Fin k)).index = 2 := alternatingGroup.index_eq_two
    have h4 : (alternatingGroup (Fin k)).relIndex ϕ.range ≤ 2 := by
      rw [h2] at h1
      exact Nat.le_of_dvd (by norm_num) ⟨ϕ.range.index, h1.symm⟩
    have h5 := relIndex_le_of_le hAle hHK
    omega
  -- `(G^ϕ)_{T'}` is a proper subgroup of `G^ϕ`
  have hproper : ¬ ϕ.range ≤ setwiseStabilizer ⊤ T := by
    intro hle
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hTne
    obtain ⟨b, hb⟩ : ∃ b : Fin k, b ∉ T := by
      by_contra hcon
      push_neg at hcon
      have huniv : T = Set.univ := Set.eq_univ_of_forall hcon
      have hT1 := hT.1
      rw [huniv, Set.ncard_univ, hkc] at hT1
      omega
    obtain ⟨π, hπ, hπa⟩ := exists_mem_alt_pointwiseStabilizer_apply_eq
      (T := (∅ : Set (Fin k))) (by simp only [Set.compl_empty, Set.ncard_univ, hkc]; omega)
      (Set.notMem_empty a) (Set.notMem_empty b)
    rw [pointwiseStabilizer_empty] at hπ
    have : (π : Equiv.Perm (Fin k)) '' T = T := (hle (hϕ hπ)).2
    exact hb (by rw [← this, ← hπa]; exact ⟨a, ha, rfl⟩)
  -- maximality: `H^ϕ = (G^ϕ)_{T'}`
  have hHle2 : setwiseStab G C ≤ (setwiseStabilizer ϕ.range T).comap ϕ := by
    intro σ hσ
    exact ⟨⟨σ, rfl⟩, (hT.2.2 ⟨σ, hσ, rfl⟩).2⟩
  have hKdef : (setwiseStabilizer ϕ.range T).comap ϕ = setwiseStab G C := by
    rcases setwiseStab_maximal hΨ hC hy hHle2 with h | h
    · exact h
    · exact absurd (by
        rintro _ ⟨σ, rfl⟩
        have : σ ∈ (setwiseStabilizer ϕ.range T).comap ϕ := by rw [h]; trivial
        exact ⟨trivial, this.2⟩) hproper
  have hHϕeq : (setwiseStab G C).map ϕ = setwiseStabilizer ϕ.range T := by
    refine le_antisymm (fun π hπ => ?_) (fun π hπ => ?_)
    · obtain ⟨σ, hσ, rfl⟩ := hπ
      exact ⟨⟨σ, rfl⟩, (hT.2.2 ⟨σ, hσ, rfl⟩).2⟩
    · obtain ⟨⟨σ, rfl⟩, hfix⟩ := hπ
      have hmem : σ ∈ (setwiseStabilizer ϕ.range T).comap ϕ := ⟨⟨σ, rfl⟩, hfix⟩
      rw [hKdef] at hmem
      exact ⟨σ, hmem, rfl⟩
  -- `r = C(k, t')`
  have hcardΨ : Nat.card Ψ = k.choose T.ncard := by
    rw [← hindexr, hHϕeq,
      relIndex_setwiseStabilizer hϕ (m := T.ncard) (by rw [hkc]; omega) rfl, hkc]
  -- `T' ≠ T(y)`, else `Ψ` is the standard system
  have hTneq : T ≠ Tpoint ϕ y := by
    intro heq
    have hB : standardBlock ϕ y ∈ standardBlocks ϕ (orbit G x) := ⟨y, hyΔ, rfl⟩
    have hf := theorem_10_5_1_f ϕ hϕ hk x hB (mem_standardBlock_self ϕ y)
    have hmapeq : (setwiseStab G C).map ϕ = (setwiseStab G (standardBlock ϕ y)).map ϕ := by
      rw [hHϕeq, hf, heq]
    have hHH : setwiseStab G C = setwiseStab G (standardBlock ϕ y) :=
      eq_of_map_eq_of_ker_le hNH (ker_le_setwiseStab_standardBlock ϕ hϕ hk y) hmapeq
    -- so `C` and the standard block of `y` are the same block
    have hCB : C = standardBlock ϕ y := by
      refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
      · obtain ⟨σ, hσ, rfl⟩ :=
          exists_mem_setwiseStab_smul_eq hΨ.toIsSystemOfImprimitivity hC hy hz
        rw [hHH, mem_setwiseStab] at hσ
        rw [← hσ]
        exact ⟨y, mem_standardBlock_self ϕ y, rfl⟩
      · obtain ⟨σ, hσ, rfl⟩ := exists_mem_setwiseStab_smul_eq
          (theorem_10_5_1_e_isSystem ϕ hϕ hk x) hB (mem_standardBlock_self ϕ y) hz
        rw [← hHH, mem_setwiseStab] at hσ
        rw [← hσ]
        exact ⟨y, hy, rfl⟩
    exact hΨne (by
      rw [hΨ.eq_images hC, (theorem_10_5_1_e_isSystem ϕ hϕ hk x).eq_images hB, hCB])
  exact ⟨by omega, hHϕeq, hcardΨ, Set.ssubset_iff_subset_ne.2 ⟨hsub, hTneq⟩⟩

/-- `(G^ϕ)_T` sandwiches `T` as soon as `A_k ≤ G^ϕ` and `2|T| < k`. -/
theorem isSandwichSet_setwiseStabilizer {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {R : Subgroup (Equiv.Perm Γ)} (hR : alternatingGroup Γ ≤ R) {T : Set Γ}
    (hcard : 2 * T.ncard < Nat.card Γ) : IsSandwichSet (setwiseStabilizer R T) T := by
  refine ⟨hcard, fun a ha => ⟨hR ha.1, ?_⟩, fun a ha => ⟨trivial, ha.2⟩⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    rw [ha.2 z hz]; exact hz
  · intro z hz
    exact ⟨z, hz, ha.2 z hz⟩

/-- `T(G_C^ϕ)` is a sandwich set for `G_C^ϕ` (Theorem 10.5.1 (g), Eq. (51) for the blocks
of `Ψ`). -/
theorem isSandwichSet_sandwichSet_setwiseStab (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) {Ψ : Set (Set Ω)}
    (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ)
    (hΨne : Ψ ≠ standardBlocks ϕ (orbit G x))
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1)
    {C : Set Ω} (hC : C ∈ Ψ) {y : Ω} (hy : y ∈ C) :
    IsSandwichSet ((setwiseStab G C).map ϕ) (sandwichSet ((setwiseStab G C).map ϕ)) := by
  obtain ⟨h4, heq, -, -⟩ := theorem_10_5_1_g_core ϕ hϕ hk x hΨ hΨne hker hC hy
  have hkc : Nat.card (Fin k) = k := by simp
  have h := isSandwichSet_setwiseStabilizer (R := ϕ.range) hϕ
    (T := sandwichSet ((setwiseStab G C).map ϕ)) (by rw [hkc]; omega)
  rwa [← heq] at h

/-- **Eq. (54) for `Ψ`**: `T(G_{C^σ}^ϕ) = T(G_C^ϕ)^{σ^ϕ}`.  This is what makes the
labelling of the blocks of `Ψ` by `t'`-subsets `G`-equivariant. -/
theorem sandwichSet_setwiseStab_image (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK k (maxOrbitLength G)) (x : Ω) {Ψ : Set (Set Ω)}
    (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ)
    (hΨne : Ψ ≠ standardBlocks ϕ (orbit G x))
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1)
    {C : Set Ω} (hC : C ∈ Ψ) {y : Ω} (hy : y ∈ C) (σ : G) :
    sandwichSet ((setwiseStab G ((σ : Equiv.Perm Ω) '' C)).map ϕ)
      = (ϕ σ) '' sandwichSet ((setwiseStab G C).map ϕ) := by
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hkc : Nat.card (Fin k) = k := by simp
  have hC' : (σ : Equiv.Perm Ω) '' C ∈ Ψ := hΨ.permutes σ σ.2 C hC
  have hy' : ((σ : Equiv.Perm Ω) y) ∈ (σ : Equiv.Perm Ω) '' C := ⟨y, hy, rfl⟩
  have hs1 := isSandwichSet_sandwichSet_setwiseStab ϕ hϕ hk x hΨ hΨne hker hC hy
  have hs2 := isSandwichSet_sandwichSet_setwiseStab ϕ hϕ hk x hΨ hΨne hker hC' hy'
  have hconj : setwiseStab G ((σ : Equiv.Perm Ω) '' C)
      = (setwiseStab G C).map (MulAut.conj σ).toMonoidHom := by
    ext τ
    rw [mem_setwiseStab, Subgroup.mem_map]
    constructor
    · intro hτ
      refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
      · rw [mem_setwiseStab]
        have hcoe : ((σ⁻¹ * τ * σ : G) : Equiv.Perm Ω) '' C
            = ((σ⁻¹ : G) : Equiv.Perm Ω) ''
              ((τ : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' C)) := by
          simp only [Subgroup.coe_mul, image_image_eq_mul_image, mul_assoc]
        rw [hcoe, hτ, image_image_eq_mul_image]
        simp [← Subgroup.coe_mul]
      · show σ * (σ⁻¹ * τ * σ) * σ⁻¹ = τ
        simp [mul_assoc]
    · rintro ⟨ρ, hρ, rfl⟩
      rw [mem_setwiseStab] at hρ
      show ((σ * ρ * σ⁻¹ : G) : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' C)
        = (σ : Equiv.Perm Ω) '' C
      have hcoe : ((σ * ρ * σ⁻¹ : G) : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' C)
          = (σ : Equiv.Perm Ω) '' ((ρ : Equiv.Perm Ω) ''
            (((σ⁻¹ : G) : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' C))) := by
        simp only [Subgroup.coe_mul, image_image_eq_mul_image, mul_assoc]
      have hinner : ((σ⁻¹ : G) : Equiv.Perm Ω) '' ((σ : Equiv.Perm Ω) '' C) = C := by
        rw [image_image_eq_mul_image]
        simp [← Subgroup.coe_mul]
      rw [hcoe, hinner, hρ]
  have hmap : (setwiseStab G ((σ : Equiv.Perm Ω) '' C)).map ϕ
      = ((setwiseStab G C).map ϕ).map (MulAut.conj (ϕ σ)).toMonoidHom := by
    rw [hconj, map_map_conj]
  have hs3 := hs1.map_conj (ϕ σ)
  rw [← hmap] at hs3
  exact sandwichSet_unique (by rw [hkc]; omega) hs2 hs3

/-- `|Ω choose t| = (|Ω| choose t)`. -/
theorem card_binom (Γ : Type*) [Fintype Γ] [DecidableEq Γ] (t : ℕ) :
    Nat.card (binom Γ t) = (Nat.card Γ).choose t := by
  rw [Nat.card_congr (binomEquiv Γ t), Set.powersetCard.card]

end ItemG

/-- **Theorem 10.5.1 (g)**, §10.5.

> If `Ψ = {C₁, …, C_r}` is another system of imprimitivity on the orbit `∆` such that the
> kernel of the action `G → S(Ψ)` is `ker(ϕ)` then `r = (k choose t')` for some
> `t' < t_Δ` and the `G`-action on `Ψ` is `S_k^(t')` or `A_k^(t')`.  In particular, the
> standard blocks form the unique largest system of imprimitivity on which the kernel of
> `G`-action is `ker(ϕ)`.  Moreover, if `x ∈ Cᵢ` then `|T(G_{Cᵢ})| = t'` and
> `T(G_{Cᵢ}) ⊂ T(x)`.

**"another".**  The paper's word *another* system of imprimitivity means: different from
the system of standard blocks.  Dropping it makes the statement false, because the
standard blocks themselves satisfy the remaining hypotheses (by item (e)) while having
`C(k, t_Δ)` blocks, not `C(k, t')` with `t' < t_Δ`.  So the hypothesis
`hΨne : Ψ ≠ standardBlocks ϕ (orbit G x)` is part of the theorem.  (A formalization
matter, not a correction from the paper.)

**correction: the blocks of `Ψ` must be maximal.**  As printed, (g) is false.  Let `S_k` act
on the ordered triples of distinct elements of `[k]` with `k = 32`, so `n₀ = 29760`,
`2 log₂ n₀ < 30 ≤ k`, `ϕ` is the identification of `G` with `S_k`, `ker ϕ = 1`,
`T(a,b,c) = {a,b,c}` and `t_Δ = 3`.  Let `Ψ` be the partition of the triples by their first
two coordinates.  It is a system of imprimitivity, the action on it is faithful, so its
kernel is `ker ϕ`, and it is not the standard system.  It has `r = 32 · 31 = 992` blocks,
which is none of `C(32,0) = 1`, `C(32,1) = 32`, `C(32,2) = 496`.  (The system of singletons
in the example of Remark 10.5.3 is a second counterexample.)  The paper's proof says
"`H = G_{Cᵢ}` is a maximal subgroup of `G`", which holds exactly when `Cᵢ` is a maximal
block.  So the hypothesis that the proof uses is added to the statement: `Ψ` is a
*minimal system of imprimitivity* in the paper's own term (Sec. 11.1: "systems with at
least two blocks that cannot be made coarser, i. e., the blocks are maximal"),
`Babai.IsMinimalSystemOfImprimitivity`.  See the corrected paper "Theorem 10.5.1 (g):
false unless the blocks of `Ψ` are maximal".

**Proof route.**  The paper's, with one unproved fact derived.  Let `x ∈ Cᵢ` and
`H = G_{Cᵢ}`.  Then `Gₓ ≤ H`, and `H` is a maximal subgroup of `G` because `Cᵢ` is a
maximal block.  The kernel `N = ker ϕ` fixes every block, so `N ≤ H`, and `H^ϕ` is a
maximal subgroup of `G^ϕ` with `|G : H| = |G^ϕ : H^ϕ| = r`.  First `r ≥ 3`, because
`r! ≥ |G : N| ≥ k!/2`.  The paper then quotes: "the only maximal subgroups of `S_k`
containing `(A_k)_(T)` are of the form `(S_k)_U` for `U ⊆ T`".  We get this from results
already in hand: `|G^ϕ : H^ϕ| ≤ |G^ϕ : Gₓ^ϕ| ≤ n₀ < C(k, ⌊k/4⌋)` by Eq. (53), so
Theorem 10.4.2 (form `Babai.theorem_10_4_2_of_four_mul_le`) gives `T' := T(H^ϕ)` with
`(A_k)_(T') ≤ H^ϕ ≤ (S_k)_{T'}`, and Observation 10.4.1 applied to
`(A_k)_(T(x)) ≤ Gₓ^ϕ ≤ H^ϕ ≤ (S_k)_{T'}` gives `T' ⊆ T(x)`.  Since `r ≥ 3`, `T' ≠ ∅`, so
`(G^ϕ)_{T'}` is a proper subgroup of `G^ϕ` containing `H^ϕ`, and maximality gives
`H^ϕ = (G^ϕ)_{T'}`.  Hence `r = C(k, t')` with `t' = |T'|`, and the Johnson action on `Ψ`
follows the lines of item (e).  If `T' = T(x)` then `H^ϕ = (G^ϕ)_{T(x)} = (G_B)^ϕ` for the
standard block `B ∋ x` by item (f), so `H = G_B` (both contain `N`), `Cᵢ = B`, and `Ψ` is
the standard system, contrary to `hΨne`.  So `T' ⊊ T(x)` and `t' < t_Δ`. -/
theorem theorem_10_5_1_g (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) (Ψ : Set (Set Ω)) (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ)
    (hΨne : Ψ ≠ standardBlocks ϕ (orbit G x))
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1) :
    ∃ t' : ℕ, t' < tPoint ϕ x ∧ Nat.card Ψ = k.choose t' ∧
      (∃ e : Ψ ≃ binom (Fin k) t',
        (onBlocks G Ψ hΨ.permutes).map (Equiv.permCongrHom e).toMonoidHom
            = JohnsonA k t' ∨
          (onBlocks G Ψ hΨ.permutes).map (Equiv.permCongrHom e).toMonoidHom
            = JohnsonS k t') ∧
      ∀ C ∈ Ψ, ∀ y ∈ C, (sandwichSet ((setwiseStab G C).map ϕ)).ncard = t' ∧
        sandwichSet ((setwiseStab G C).map ϕ) ⊂ Tpoint ϕ y := by
  classical
  have hk9 : 9 ≤ k := by
    have : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hkc : Nat.card (Fin k) = k := by simp
  obtain ⟨C₀, hC₀⟩ := hΨ.blocks_nonempty
  obtain ⟨y₀, hy₀⟩ := hΨ.nonempty C₀ hC₀
  obtain ⟨h4₀, heq₀, hcard₀, hss₀⟩ := theorem_10_5_1_g_core ϕ hϕ hk x hΨ hΨne hker hC₀ hy₀
  -- all blocks carry a label of the same size `t'` (Eq. (54) for `Ψ`)
  have hlabel : ∀ C ∈ Ψ, (sandwichSet ((setwiseStab G C).map ϕ)).ncard
      = (sandwichSet ((setwiseStab G C₀).map ϕ)).ncard := by
    intro C hC
    obtain ⟨σ, hσ, hσC⟩ := hΨ.transitiveOnBlocks C₀ hC₀ C hC
    rw [← hσC, sandwichSet_setwiseStab_image ϕ hϕ hk x hΨ hΨne hker hC₀ hy₀ ⟨σ, hσ⟩,
      Set.ncard_image_of_injective _ (ϕ ⟨σ, hσ⟩).injective]
  refine ⟨(sandwichSet ((setwiseStab G C₀).map ϕ)).ncard, ?_, hcard₀, ?_, ?_⟩
  · -- `t' < t_Δ`
    have hy₀Δ : y₀ ∈ orbit G x := by rw [← hΨ.covers]; exact ⟨C₀, hC₀, hy₀⟩
    have h := Set.ncard_lt_ncard hss₀ (Set.toFinite _)
    have h2 : (Tpoint ϕ y₀).ncard = tPoint ϕ x := theorem_10_5_1_c ϕ hϕ hk hy₀Δ
    omega
  · -- the Johnson action on `Ψ`
    have ht2 : (sandwichSet ((setwiseStab G C₀).map ϕ)).ncard + 2 ≤ k := by omega
    have hlabelcard : ∀ C : Ψ, (sandwichSet ((setwiseStab G (C : Set Ω)).map ϕ)).ncard
        = (sandwichSet ((setwiseStab G C₀).map ϕ)).ncard := fun C => hlabel (C : Set Ω) C.2
    set f : Ψ → binom (Fin k) ((sandwichSet ((setwiseStab G C₀).map ϕ)).ncard) := fun C =>
      setNcardEquivBinom (Fin k) _
        ⟨sandwichSet ((setwiseStab G (C : Set Ω)).map ϕ), hlabelcard C⟩ with hfdef
    have hfmem : ∀ (C : Ψ) (a : Fin k),
        a ∈ ((f C : binom (Fin k) _) : Finset (Fin k)) ↔
          a ∈ sandwichSet ((setwiseStab G (C : Set Ω)).map ϕ) :=
      fun C a => mem_setNcardEquivBinom _ a
    have hfequiv : ∀ (σ : G) (C : Ψ) (a : Fin k),
        a ∈ ((f (blockPerm G Ψ hΨ.permutes σ C) : binom (Fin k) _) : Finset (Fin k)) ↔
          a ∈ (ϕ σ) '' (sandwichSet ((setwiseStab G (C : Set Ω)).map ϕ)) := by
      intro σ C a
      rw [hfmem]
      obtain ⟨y, hy⟩ := hΨ.nonempty (C : Set Ω) C.2
      have himg := sandwichSet_setwiseStab_image ϕ hϕ hk x hΨ hΨne hker C.2 hy σ
      rw [show ((blockPerm G Ψ hΨ.permutes σ C : Ψ) : Set Ω)
        = (σ : Equiv.Perm Ω) '' (C : Set Ω) from rfl, himg]
    -- the label map is onto the `t'`-subsets
    have hsurj : Function.Surjective f := by
      intro s
      obtain ⟨π, hπ, himg⟩ := exists_mem_image_eq_of_ncard_eq (Ω := Fin k)
        (K := alternatingGroup (Fin k)) le_rfl
        (T := sandwichSet ((setwiseStab G C₀).map ϕ))
        (U := (((s : binom (Fin k) _) : Finset (Fin k)) : Set (Fin k))) rfl
        (by rw [Set.ncard_coe_finset]; exact s.2) (by rw [hkc]; exact ht2)
      obtain ⟨σ, hσ⟩ := hϕ hπ
      have hCmem : (σ : Equiv.Perm Ω) '' C₀ ∈ Ψ := hΨ.permutes σ σ.2 C₀ hC₀
      refine ⟨⟨(σ : Equiv.Perm Ω) '' C₀, hCmem⟩, Subtype.ext (Finset.ext fun a => ?_)⟩
      rw [hfmem]
      show a ∈ sandwichSet ((setwiseStab G ((σ : Equiv.Perm Ω) '' C₀)).map ϕ) ↔ _
      rw [sandwichSet_setwiseStab_image ϕ hϕ hk x hΨ hΨne hker hC₀ hy₀ σ, hσ, himg]
      exact Finset.mem_coe
    haveI : Fintype ↥Ψ := Fintype.ofFinite _
    have hcards : Fintype.card ↥Ψ
        = Fintype.card (binom (Fin k) ((sandwichSet ((setwiseStab G C₀).map ϕ)).ncard)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard₀,
        card_binom, hkc]
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcards⟩
    -- through the labelling, `σ` acts on `Ψ` as `ϕ σ` acts on `t'`-subsets
    have hkey : ∀ σ : G,
        (Equiv.permCongrHom (Equiv.ofBijective f hbij)) (blockHom G Ψ hΨ.permutes σ)
          = tAction ((sandwichSet ((setwiseStab G C₀).map ϕ)).ncard) (ϕ σ) := by
      intro σ
      refine Equiv.ext fun s => Subtype.ext (Finset.ext fun a => ?_)
      have hsC : f ((Equiv.ofBijective f hbij).symm s) = s :=
        (Equiv.ofBijective f hbij).apply_symm_apply s
      have hRHS : ∀ z : Fin k, z ∈ ((s : binom (Fin k) _) : Finset (Fin k)) ↔
          z ∈ sandwichSet ((setwiseStab G
            (((Equiv.ofBijective f hbij).symm s : Ψ) : Set Ω)).map ϕ) := by
        intro z
        have h := hfmem ((Equiv.ofBijective f hbij).symm s) z
        rwa [hsC] at h
      show a ∈ ((f (blockPerm G Ψ hΨ.permutes σ ((Equiv.ofBijective f hbij).symm s)) :
          binom (Fin k) _) : Finset (Fin k)) ↔ _
      rw [hfequiv, tAction_apply_coe]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact Finset.mem_image.2 ⟨z, (hRHS z).2 hz, rfl⟩
      · intro ha
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 ha
        exact ⟨z, (hRHS z).1 hz, rfl⟩
    have hrange : (onBlocks G Ψ hΨ.permutes).map
        (Equiv.permCongrHom (Equiv.ofBijective f hbij)).toMonoidHom
        = inducedOnTSets ϕ.range ((sandwichSet ((setwiseStab G C₀).map ϕ)).ncard) := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨σ, rfl⟩ := hq
        exact ⟨ϕ σ, ⟨σ, rfl⟩, (hkey σ).symm⟩
      · rintro ⟨π, hπ, rfl⟩
        obtain ⟨σ, rfl⟩ := hπ
        exact ⟨blockHom G Ψ hΨ.permutes σ, ⟨σ, rfl⟩, hkey σ⟩
    refine ⟨Equiv.ofBijective f hbij, ?_⟩
    rcases eq_alternating_or_top (K := ϕ.range) hϕ
        (by rw [hkc]; omega) with hr | hr
    · exact Or.inl (by rw [hrange, hr]; rfl)
    · exact Or.inr (by rw [hrange, hr]; rfl)
  · -- the last clause
    intro C hC y hy
    exact ⟨hlabel C hC, (theorem_10_5_1_g_core ϕ hϕ hk x hΨ hΨne hker hC hy).2.2.2⟩

/-- `C(k,a) < C(k,b)` for `a < b ≤ k/2`: the binomial coefficients increase strictly up to
the middle.  (By `Nat.choose_succ_right_eq`: `C(k,b+1)(b+1) = C(k,b)(k-b)` and
`k - b > b + 1`.) -/
theorem choose_lt_choose_of_lt_of_two_mul_le {k : ℕ} : ∀ {a b : ℕ}, a < b → 2 * b ≤ k →
    k.choose a < k.choose b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have hstep : k.choose b < k.choose (b + 1) := by
      have h := Nat.choose_succ_right_eq k b
      have hpos : 0 < k.choose b := Nat.choose_pos (by omega)
      have hkb : b + 2 ≤ k - b := by omega
      have h2 : k.choose b * (b + 2) ≤ k.choose b * (k - b) := Nat.mul_le_mul_left _ hkb
      have h3 : k.choose b * (b + 1) < k.choose (b + 1) * (b + 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right h3
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact lt_trans (ih h (by omega)) hstep
    · subst h; exact hstep

/-- **Theorem 10.5.1 (g)**, §10.5, the "In particular" clause:

> In particular, the standard blocks form the unique largest system of imprimitivity on
> which the kernel of `G`-action is `ker(ϕ)`.

As printed, over *all* systems of imprimitivity, this is false: in the example of
Remark 10.5.3 (`S_k` on ordered pairs, `k = 16`) the system of singletons has trivial
kernel `= ker ϕ` and `240` blocks, more than the `C(16,2) = 120` standard blocks.  It is
the consequence of item (g) as repaired (the corrected paper: `Ψ` is a minimal
system of imprimitivity), so it holds among minimal systems: every minimal system with
kernel `ker ϕ` has at most as many blocks as the standard system, and only the standard
system has that many.  *Proof.*  If `Ψ` is not the standard system, item (g) gives
`|Ψ| = C(k,t')` with `t' < t_Δ`, while there are `C(k,t_Δ)` standard blocks (item (e));
since `4 t_Δ < k` (item (a)), `C(k,t') < C(k,t_Δ)`. -/
theorem theorem_10_5_1_g_largest (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    (x : Ω) (Ψ : Set (Set Ω)) (hΨ : IsMinimalSystemOfImprimitivity G (orbit G x) Ψ)
    (hker : ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm Ω) '' C = C) ↔ ϕ σ = 1) :
    Nat.card Ψ ≤ Nat.card (standardBlocks ϕ (orbit G x)) ∧
      (Nat.card Ψ = Nat.card (standardBlocks ϕ (orbit G x)) →
        Ψ = standardBlocks ϕ (orbit G x)) := by
  by_cases hΨne : Ψ = standardBlocks ϕ (orbit G x)
  · exact ⟨by rw [hΨne], fun _ => hΨne⟩
  · obtain ⟨t', ht', hcard, -⟩ := theorem_10_5_1_g ϕ hϕ hk x Ψ hΨ hΨne hker
    have h4 : 4 * (Tpoint ϕ x).ncard < k := (theorem_10_5_1_a ϕ hϕ hk x).1.1
    have hlt : k.choose t' < k.choose (tPoint ϕ x) :=
      choose_lt_choose_of_lt_of_two_mul_le ht' (by change 2 * (Tpoint ϕ x).ncard ≤ k; omega)
    rw [hcard, theorem_10_5_1_e_card ϕ hϕ hk x]
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

/-- **Remark 10.3.8**, §10.3, proved (the statement is `Babai.Remark_10_3_8_statement`).

> We observe that `ker(ϕ)` fixes each standard block (setwise) (see item (e) in
> Theorem 10.5.1) so the length of each orbit of `ker(ϕ)` contained in `∆` is
> `≤ |∆| / (k choose t_Δ)`.

*Proof*, the paper's: the `ker ϕ`-orbit of `y` lies in the standard block `B` of `y`,
since `ker ϕ` fixes `B` setwise (`Babai.ker_le_setwiseStab_standardBlock`).  The
`C(k,t_Δ)` standard blocks (item (e)) are the images of `B` under `G`, pairwise disjoint and
inside `∆`, so `C(k,t_Δ)·|B| ≤ |∆|`: choosing for each block `C` some `σ_C ∈ G` with
`σ_C(B) = C`, the map `(C, z) ↦ σ_C(z)` is injective from `Ψ × B` to `∆`. -/
theorem remark_10_3_8 (hϕ : IsGiantRep ϕ) (hk : VeryLargeK k (maxOrbitLength G))
    {x y : Ω} (hy : y ∈ orbit G x) :
    k.choose (tPoint ϕ x) * Nat.card (orbit ϕ.ker y) ≤ Nat.card (orbit G x) := by
  classical
  have hΨ := theorem_10_5_1_e_isSystem ϕ hϕ hk x
  have hB : standardBlock ϕ y ∈ standardBlocks ϕ (orbit G x) := ⟨y, hy, rfl⟩
  -- the `ker ϕ`-orbit of `y` lies in the standard block of `y`
  have hsub : orbit ϕ.ker y ⊆ standardBlock ϕ y := by
    rintro _ ⟨σ, rfl⟩
    have h1 := mem_setwiseStab.1 (ker_le_setwiseStab_standardBlock ϕ hϕ hk y σ.2)
    have h2 : ((σ : G) : Equiv.Perm Ω) y ∈ ((σ : G) : Equiv.Perm Ω) '' standardBlock ϕ y :=
      ⟨y, mem_standardBlock_self ϕ y, rfl⟩
    rw [h1] at h2
    exact h2
  have h1 : Nat.card (orbit ϕ.ker y) ≤ Nat.card (standardBlock ϕ y) :=
    Nat.card_mono (Set.toFinite _) hsub
  -- `blocks × B` injects into the orbit
  have hchoice : ∀ C : standardBlocks ϕ (orbit G x), ∃ σ : G,
      (σ : Equiv.Perm Ω) '' standardBlock ϕ y = C := by
    intro C
    obtain ⟨σ, hσ, hσC⟩ := hΨ.transitiveOnBlocks _ hB C C.2
    exact ⟨⟨σ, hσ⟩, hσC⟩
  choose f hf using hchoice
  have hmemC : ∀ (C : standardBlocks ϕ (orbit G x)) (z : standardBlock ϕ y),
      ((f C : G) : Equiv.Perm Ω) z ∈ (C : Set Ω) := by
    intro C z
    rw [← hf C]
    exact ⟨z, z.2, rfl⟩
  have hcov : ∀ w : Ω, w ∈ ⋃₀ standardBlocks ϕ (orbit G x) → w ∈ orbit G x := by
    intro w hw
    rw [hΨ.covers] at hw
    exact hw
  let F : standardBlocks ϕ (orbit G x) × standardBlock ϕ y → orbit G x := fun p =>
    ⟨((f p.1 : G) : Equiv.Perm Ω) p.2, by
      exact hcov _ ⟨p.1, p.1.2, hmemC p.1 p.2⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨C, z⟩ ⟨C', z'⟩ h
    have hw : ((f C : G) : Equiv.Perm Ω) z = ((f C' : G) : Equiv.Perm Ω) z' :=
      congrArg Subtype.val h
    have hCC : C = C' := by
      by_contra hne
      have hne' : (C : Set Ω) ≠ C' := fun h' => hne (Subtype.ext h')
      have hd := hΨ.pairwiseDisjoint C C.2 C' C'.2 hne'
      have ha := hmemC C z
      have hb := hmemC C' z'
      rw [← hw] at hb
      exact Set.disjoint_left.1 hd ha hb
    subst hCC
    have : (z : Ω) = z' := ((f C : G) : Equiv.Perm Ω).injective hw
    exact Prod.ext rfl (Subtype.ext this)
  have h2 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, theorem_10_5_1_e_card ϕ hϕ hk x] at h2
  exact le_trans (Nat.mul_le_mul_left _ h1) h2

/-! ### Remarks 10.5.2, 10.5.3, 10.3.8, and Proposition 10.5.4 -/

/-- **Remark 10.5.2** (Tight bound for `k`), §10.5.

> The actual condition on `k`, sufficient for most conclusions of the theorem, is that
> `k > max{8, 2 + log₂ n₀}` and `(1/2)(k choose ⌊k/2⌋) > n₀`.  … The only difference would
> be that instead of `|T(x)| < k/4` we would only get `|T(x)| < k/2`, sufficient for our
> goals.

Recorded as a statement only: it asserts that items (a)–(g) hold under the weaker
hypothesis, with `|T(x)| < k/2` in place of `|T(x)| < k/4`.  Version 2.5 uses only the
`k ≥ max{9, 2 log₂ n₀}` form. -/
def Remark_10_5_2_statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) (k : ℕ)
    (ϕ : G →* Equiv.Perm (Fin k)), IsGiantRep ϕ → LargeK k (maxOrbitLength G) →
      2 * maxOrbitLength G < k.choose (k / 2) →
        ∀ x : Ω, 2 * (Tpoint ϕ x).ncard < k ∧
          IsSandwichSet ((stabilizer G x).map ϕ) (Tpoint ϕ x)

/-- **Remark 10.5.3** (Multiple systems of imprimitivity), §10.5.

> The presence of multiple systems of imprimitivity with the same kernel as discussed in
> Item (g) is a real possibility.  Consider for instance the action `S_k → S_{k(k−1)}`
> defined by the action of `S_k` on the `k(k−1)` ordered pairs; let `G ≤ S_{k(k−1)}` be the
> image of this action.  Then `G` has two systems of imprimitivity on which `S_k` acts in
> its natural action (there are `k` blocks in each system), and there is a unique system of
> imprimitivity with `(k choose 2)` blocks on which the action is `S_k^(2)`.  The latter
> are the standard blocks; in this case each standard block has 2 elements.  Each of the
> three actions is faithful, so their kernel is the same, namely, the identity.

An example, used nowhere; recorded as a statement only.  Its *content* is the last
sentence — the three systems have the same kernel, namely the identity — so that is
recorded too, as the triviality of the kernel of the action on each of the three systems
(`σ` fixes every block of the system setwise only if `σ = 1`); with it, the example shows
that the hypothesis of item (g) really is satisfiable by more than one system, which is
why item (g) needs its word "another". -/
def Remark_10_5_3_statement : Prop :=
  ∀ k : ℕ, 9 ≤ k →
    ∃ (G : Subgroup (Equiv.Perm {p : Fin k × Fin k // p.1 ≠ p.2}))
      (Ψ₁ Ψ₂ Ψ₃ : Set (Set {p : Fin k × Fin k // p.1 ≠ p.2})),
      Ψ₁ ≠ Ψ₂ ∧ Ψ₁ ≠ Ψ₃ ∧ Ψ₂ ≠ Ψ₃ ∧
        Nat.card Ψ₁ = k ∧ Nat.card Ψ₂ = k ∧ Nat.card Ψ₃ = k.choose 2 ∧
        IsSystemOfImprimitivity G Set.univ Ψ₁ ∧ IsSystemOfImprimitivity G Set.univ Ψ₂ ∧
        IsSystemOfImprimitivity G Set.univ Ψ₃ ∧
        ∀ Ψ ∈ ({Ψ₁, Ψ₂, Ψ₃} : Set (Set (Set {p : Fin k × Fin k // p.1 ≠ p.2}))),
          ∀ σ : G, (∀ C ∈ Ψ, (σ : Equiv.Perm {p : Fin k × Fin k // p.1 ≠ p.2}) '' C = C) →
            σ = 1

/-- **Remark 10.3.8**, §10.3 (it depends on Theorem 10.5.1, so it is stated here).

> If `k ≥ max{9, 2 log₂ n₀}` then we can use Theorem 10.5.1 to make a more detailed
> statement.  We observe that `ker(ϕ)` fixes each standard block (setwise) (see item (e) in
> Theorem 10.5.1) so the length of each orbit of `ker(ϕ)` contained in `∆` is
> `≤ |∆| / (k choose t_Δ)`.

A sharpening of Cor. 10.3.7 that the paper does not use; stated multiplicatively to avoid
truncated division.  It is proved: `Babai.remark_10_3_8` and
`Babai.remark_10_3_8_statement_holds`. -/
def Remark_10_3_8_statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) (k : ℕ)
    (ϕ : G →* Equiv.Perm (Fin k)), IsGiantRep ϕ → VeryLargeK k (maxOrbitLength G) →
      ∀ x y : Ω, y ∈ orbit G x →
        k.choose (tPoint ϕ x) * Nat.card (orbit ϕ.ker y) ≤ Nat.card (orbit G x)

/-- Remark 10.3.8 holds (`Babai.remark_10_3_8`). -/
theorem remark_10_3_8_statement_holds : Remark_10_3_8_statement :=
  fun _ _ _ _ _ ϕ hϕ hk _ _ hy => remark_10_3_8 ϕ hϕ hk hy

/-- **Proposition 10.5.4**, §10.5.

> Given a giant representation `ϕ : G → S_k`, we can find the standard blocks in each
> `G`-orbit in polynomial time.  *Proof.* Standard.

Purely algorithmic.  The mathematical content — that the standard blocks are well defined
and form a system of imprimitivity — is Theorem 10.5.1 (e), and that is what the `def`
below records.

**The running-time claim.**  Running time is modelled by the RAM model of
`Workspace/Machine/` (`PLAN.md`, Decision 2), which is not imported here.  The
polynomial-time half of this proposition — that the standard blocks of every `G`-orbit can
be computed in polynomial time from generators of `G` and their images under `ϕ` — is the
theorem `Algo.proposition_10_5_4` of `Workspace/Algo/StdBlocksProved.lean`.  It was an
axiom by a decision of the user until it was proved. -/
def Proposition_10_5_4_statement : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (G : Subgroup (Equiv.Perm Ω)) (k : ℕ)
    (ϕ : G →* Equiv.Perm (Fin k)), IsGiantRep ϕ → VeryLargeK k (maxOrbitLength G) →
      ∀ x : Ω, IsSystemOfImprimitivity G (orbit G x) (standardBlocks ϕ (orbit G x))

end Babai
