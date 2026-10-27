/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: the color classes of `Ω` that the proof of Corollary 12.0.10 runs the Chain
Rule over, and the bound `2n/3` on the size of all but the first of them.
-/
import Workspace.Canonical.Align

/-!
# The color classes of `Ω` in the proof of Cor. 12.0.10

The proof of Cor. 12.0.10 reads:

> Let `C_x = C`. … from the coloring `(C, Γ ∖ C)` of `Γ` we infer a canonical coloring of
> `Ω`; one of the color classes is `Ω(C)`; and we begin the application of the Chain Rule
> with this color class. … Then proceed to the remaining color classes in accordance with
> the Chain Rule.  The bound `2n/3` on the length of the remaining color classes comes
> from Lemma 7.2.1.

The coloring in question is the two-coloring `(C, Γ ∖ C)` of `Γ`, lifted to `Ω` through
the standard blocks by Lemma 7.2.1: the color of `u ∈ Ω` is the color vector of its label
`T(u)`, which for a two-coloring is determined by the single number `|T(u) ∩ C|`.  So the
color classes of `Ω` are

  `Ω_j = {u ∈ Ω | |T(u) ∩ C| = j}`   (`Babai.omegaCut`),  `0 ≤ j ≤ t`,

and `Ω_t = Ω(C)` (`Babai.omegaCut_eq_omegaOf`), the class the Chain Rule starts with.

This file provides:

* `Babai.labelF`, `Babai.labelFiber`: the label `T(u)` as a `Finset`, and the set of
  points carrying a given label — that is, the standard block with that label.
* `Babai.card_labelFiber_congr`: **all standard blocks have the same size.**  (`A(Γ)` is
  transitive on the `t`-subsets of `Γ` and `A(Γ) ≤ G^ϕ`, so some `ρ ∈ G` carries one block
  onto the other, by Eq. (54).)
* `Babai.card_filter_labelF_mem_eq_mul`, `Babai.card_univ_eq_mul`: hence
  `|{u | T(u) ∈ S}| = |S| · b` for any set `S` of `t`-subsets, and `n = C(m,t) · b`.
* `Babai.three_mul_ncard_omegaCut_le` : **`3|Ω_j| ≤ 2n` for `1 ≤ j < t`**, which is
  Lemma 7.2.1 (a) multiplied by the block size `b`, and
  `Babai.two_mul_ncard_omegaCut_zero_le`: `2|Ω_0| ≤ n`, the class `Ω_0 = Ω(Γ ∖ C)`, which
  Lemma 7.2.1 (a) does not cover (its color vector *is* exceptional) but which is small
  because `|Γ ∖ C| ≤ m/2`.
* `Babai.sum_ncard_omegaCut_le`: the remaining classes have total size at most `n`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm Finset

/-! ### Two pieces of arithmetic -/

/-- `VeryLargeK` is monotone in `n` (as `Babai.LargeK.mono` is for `LargeK`). -/
theorem VeryLargeK.mono {k n n' : ℕ} (h : VeryLargeK k n) (hn : n' ≤ n) :
    VeryLargeK k n' := by
  have h9 : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) h
  refine max_le h9 ?_
  rcases Nat.eq_zero_or_pos n' with rfl | hpos
  · simp only [Nat.cast_zero, Real.logb_zero, mul_zero]
    linarith
  · have hle : Real.logb 2 (n' : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hn)
    have := le_trans (le_max_right (9 : ℝ) (2 * Real.logb 2 (n : ℝ))) h
    linarith

/-- The hypothesis of Theorem 10.5.1 for the whole domain gives it for the longest orbit. -/
theorem veryLargeK_maxOrbitLength {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} (hm : VeryLargeK m (Nat.card Ω)) :
    VeryLargeK m (maxOrbitLength G) := by
  refine hm.mono ?_
  refine csSup_le ⟨Nat.card (orbit G (Classical.arbitrary Ω)), ⟨_, rfl⟩⟩ ?_
  rintro c ⟨x, rfl⟩
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- `C(m',t)/C(m,t) ≤ m'/m` for `t ≥ 1`, in the cross-multiplied integer form
`m · C(m',t) ≤ m' · C(m,t)`.

Both sides are computed by `t · C(n,t) = n · C(n−1,t−1)` (`Nat.succ_mul_choose_eq`), which
reduces the claim to `C(m'−1,t−1) ≤ C(m−1,t−1)`. -/
theorem mul_choose_le_mul_choose {m' m t : ℕ} (ht : 1 ≤ t) (hm : m' ≤ m) :
    m * m'.choose t ≤ m' * m.choose t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · simp [Nat.choose_eq_zero_of_lt (by omega : 0 < s + 1)]
  obtain ⟨a, rfl⟩ : ∃ a, m' = a + 1 := ⟨m' - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  -- `(a+1) * C(a,s) = C(a+1,s+1) * (s+1)` and likewise for `b`
  have ha := Nat.succ_mul_choose_eq a s
  have hb := Nat.succ_mul_choose_eq b s
  have hab : a.choose s ≤ b.choose s := Nat.choose_le_choose s (by omega)
  -- multiply the goal by `s+1`
  have key : (b + 1) * ((a + 1).choose (s + 1)) * (s + 1)
      ≤ (a + 1) * ((b + 1).choose (s + 1)) * (s + 1) := by
    calc (b + 1) * ((a + 1).choose (s + 1)) * (s + 1)
        = (b + 1) * (((a + 1).choose (s + 1)) * (s + 1)) := by ring
      _ = (b + 1) * ((a + 1) * a.choose s) := by rw [← ha]
      _ ≤ (b + 1) * ((a + 1) * b.choose s) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hab)
      _ = (a + 1) * ((b + 1) * b.choose s) := by ring
      _ = (a + 1) * (((b + 1).choose (s + 1)) * (s + 1)) := by rw [← hb]
      _ = (a + 1) * ((b + 1).choose (s + 1)) * (s + 1) := by ring
  exact Nat.le_of_mul_le_mul_right key (by omega)

/-- If `2m' ≤ m` and `t ≥ 1` then `2·C(m',t) ≤ C(m,t)`.

This is the estimate that bounds the size of the class `Ω_0 = Ω(Γ ∖ C)`, which
Lemma 7.2.1 (a) does not cover.  It follows from `Babai.mul_choose_le_mul_choose`:
`2m'·C(m',t) ≤ m·C(m',t) ≤ m'·C(m,t)`. -/
theorem two_mul_choose_le_of_two_mul_le {m' m t : ℕ} (ht : 1 ≤ t) (h : 2 * m' ≤ m) :
    2 * m'.choose t ≤ m.choose t := by
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · simp [Nat.choose_eq_zero_of_lt (by omega : 0 < t)]
  have h1 : m * m'.choose t ≤ m' * m.choose t :=
    mul_choose_le_mul_choose ht (by omega)
  have h2 : 2 * m' * m'.choose t ≤ m * m'.choose t :=
    Nat.mul_le_mul_right _ h
  have h3 : m' * (2 * m'.choose t) ≤ m' * m.choose t := by
    calc m' * (2 * m'.choose t) = 2 * m' * m'.choose t := by ring
      _ ≤ m * m'.choose t := h2
      _ ≤ m' * m.choose t := h1
  exact Nat.le_of_mul_le_mul_left h3 hm'

/-! ### Labels, standard blocks, and their common size -/

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- The label `T(u)` of Theorem 10.5.1 (e) as a `Finset`. -/
noncomputable def labelF (ϕ : G →* Equiv.Perm (Fin m)) (u : Ω) : Finset (Fin m) :=
  (Set.toFinite (Tpoint ϕ u)).toFinset

@[simp] theorem coe_labelF (ϕ : G →* Equiv.Perm (Fin m)) (u : Ω) :
    ((labelF ϕ u : Finset (Fin m)) : Set (Fin m)) = Tpoint ϕ u :=
  Set.Finite.coe_toFinset _

theorem card_labelF (ϕ : G →* Equiv.Perm (Fin m)) (u : Ω) :
    (labelF ϕ u).card = tPoint ϕ u := by
  rw [tPoint, ← coe_labelF ϕ u, Set.ncard_coe_finset]

theorem mem_labelF {ϕ : G →* Equiv.Perm (Fin m)} {u : Ω} {γ : Fin m} :
    γ ∈ labelF ϕ u ↔ γ ∈ Tpoint ϕ u := Set.Finite.mem_toFinset _

/-- Eq. (54) for the `Finset` form of the label. -/
theorem labelF_smul (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (u : Ω) (ρ : G) :
    labelF ϕ ((ρ : Equiv.Perm Ω) u) = (labelF ϕ u).image (ϕ ρ) := by
  apply Finset.coe_injective
  rw [coe_labelF, Finset.coe_image, coe_labelF]
  exact theorem_10_5_1_c_eq54 ϕ hϕ hk u ρ

open scoped Classical in
/-- The standard block labelled `T`: the set of points `u` with `T(u) = T`. -/
noncomputable def labelFiber (ϕ : G →* Equiv.Perm (Fin m)) (T : Finset (Fin m)) :
    Finset Ω :=
  Finset.univ.filter (fun u => labelF ϕ u = T)

open scoped Classical in
theorem mem_labelFiber {ϕ : G →* Equiv.Perm (Fin m)} {T : Finset (Fin m)} {u : Ω} :
    u ∈ labelFiber ϕ T ↔ labelF ϕ u = T := by
  rw [labelFiber, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
/-- §12, the step behind "the bound `2n/3` … comes from Lemma 7.2.1": **all standard blocks
have the same size**.

`A(Γ)` is transitive on the `t`-subsets of `Γ` (`Babai.exists_alternating_image_eq`) and
`A(Γ) ≤ G^ϕ`, so some `ρ ∈ G` has `T(u)^{ρ^ϕ} = T'` for the points `u` of the block
labelled `T`; by Eq. (54) it carries that block onto the block labelled `T'`. -/
theorem card_labelFiber_congr (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m)
    {T T' : Finset (Fin m)} (hcard : T.card = T'.card) :
    (labelFiber ϕ T).card = (labelFiber (Ω := Ω) ϕ T').card := by
  obtain ⟨α, hα, himg⟩ :=
    exists_alternating_image_eq (Δ := Fin m) (by simpa using hm3)
      (C := (T : Set (Fin m))) (D := (T' : Set (Fin m)))
      (by rw [Set.ncard_coe_finset, Set.ncard_coe_finset, hcard])
  obtain ⟨ρ, hρ⟩ := hϕ hα
  have himgF : T.image α = T' := by
    apply Finset.coe_injective; rw [Finset.coe_image]; exact himg
  have hstep : ∀ u : Ω, labelF ϕ u = T → labelF ϕ ((ρ : Equiv.Perm Ω) u) = T' := by
    intro u hu
    rw [labelF_smul ϕ hϕ hk u ρ, hu, hρ, himgF]
  have hback : ∀ v : Ω, labelF ϕ v = T' → labelF ϕ ((ρ : Equiv.Perm Ω)⁻¹ v) = T := by
    intro v hv
    have h1 : labelF ϕ ((ρ : Equiv.Perm Ω) ((ρ : Equiv.Perm Ω)⁻¹ v)) =
        (labelF ϕ ((ρ : Equiv.Perm Ω)⁻¹ v)).image (ϕ ρ) :=
      labelF_smul ϕ hϕ hk _ ρ
    rw [show (ρ : Equiv.Perm Ω) ((ρ : Equiv.Perm Ω)⁻¹ v) = v from by simp, hv, hρ] at h1
    -- `T' = image α (labelF (ρ⁻¹ v)) = image α T`, and `image α` is injective
    have h2 : (labelF ϕ ((ρ : Equiv.Perm Ω)⁻¹ v)).image (α : Equiv.Perm (Fin m)) =
        T.image (α : Equiv.Perm (Fin m)) := by
      rw [← h1, himgF]
    exact Finset.image_injective (α : Equiv.Perm (Fin m)).injective h2
  have hmap : (labelFiber (Ω := Ω) ϕ T).image (fun u => (ρ : Equiv.Perm Ω) u) =
      labelFiber ϕ T' := by
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_labelFiber.2 (hstep u (mem_labelFiber.1 hu))
    · intro hv
      exact ⟨(ρ : Equiv.Perm Ω)⁻¹ v,
        mem_labelFiber.2 (hback v (mem_labelFiber.1 hv)), by simp⟩
  rw [← hmap, Finset.card_image_of_injective _ (ρ : Equiv.Perm Ω).injective]

/-! ### Counting the points with a prescribed set of labels -/

open scoped Classical in
/-- The points whose label lies in `S`, as a `Finset`. -/
noncomputable def labelPreim (ϕ : G →* Equiv.Perm (Fin m)) (S : Finset (Finset (Fin m))) :
    Finset Ω :=
  Finset.univ.filter (fun u => labelF ϕ u ∈ S)

open scoped Classical in
theorem card_labelPreim (ϕ : G →* Equiv.Perm (Fin m)) (S : Finset (Finset (Fin m))) :
    (labelPreim (Ω := Ω) ϕ S).card = ∑ T ∈ S, (labelFiber ϕ T).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := labelF ϕ)
    (s := labelPreim (Ω := Ω) ϕ S) (t := S)
    (fun u hu => by
      simp only [Finset.mem_coe, labelPreim, Finset.mem_filter] at hu ⊢
      exact hu.2)
  rw [h]
  refine Finset.sum_congr rfl fun T hT => ?_
  congr 1
  ext u
  simp only [labelPreim, labelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hT, h⟩⟩

open scoped Classical in
/-- `|{u | T(u) ∈ S}| = |S| · b` when every member of `S` is a `t`-subset and `b` is the
common size of the standard blocks. -/
theorem card_labelPreim_eq_mul (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (S : Finset (Finset (Fin m))) (hS : ∀ T ∈ S, T.card = t)
    (T₀ : Finset (Fin m)) (hT₀ : T₀.card = t) :
    (labelPreim (Ω := Ω) ϕ S).card = S.card * (labelFiber (Ω := Ω) ϕ T₀).card := by
  rw [card_labelPreim ϕ S]
  rw [Finset.sum_congr rfl (fun T hT =>
    card_labelFiber_congr (Ω := Ω) ϕ hϕ hk hm3 ((hS T hT).trans hT₀.symm))]
  rw [Finset.sum_const, smul_eq_mul]

open scoped Classical in
/-- The whole domain: `n = C(m,t) · b`, for `t` the common label size of a transitive `G`. -/
theorem card_univ_eq_mul (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (T₀ : Finset (Fin m)) (hT₀ : T₀.card = t) :
    Fintype.card Ω = (m.choose t) * (labelFiber (Ω := Ω) ϕ T₀).card := by
  have hall : labelPreim (Ω := Ω) ϕ (Phi (Fin m) t) = Finset.univ := by
    ext u
    simp only [labelPreim, Finset.mem_filter, Finset.mem_univ, true_and, iff_true, Phi,
      Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [card_labelF, ht u]⟩
  have hcard := card_labelPreim_eq_mul (Ω := Ω) ϕ hϕ hk hm3 (Phi (Fin m) t)
    (fun T hT => (Finset.mem_powersetCard.1 hT).2) T₀ hT₀
  rw [hall, Finset.card_univ] at hcard
  rw [hcard, card_Phi, Fintype.card_fin]

/-! ### The color classes of the two-coloring `(C, Γ ∖ C)` -/

/-- §12, proof of Cor. 12.0.10, line 4 of Procedure Align for the two-coloring
`(C, Γ ∖ C)`: the color class of `Ω` consisting of the points whose label meets `C` in
exactly `j` points.

For a two-coloring the color vector of Lemma 7.2.1 is `(j, t − j)`, so it is determined by
the single number `j = |T(u) ∩ C|`, and `Ω_t = Ω(C)`
(`Babai.omegaCut_eq_omegaOf`). -/
def omegaCut (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) (j : ℕ) : Set Ω :=
  {u : Ω | (Tpoint ϕ u ∩ C).ncard = j}

theorem mem_omegaCut {ϕ : G →* Equiv.Perm (Fin m)} {C : Set (Fin m)} {j : ℕ} {u : Ω} :
    u ∈ omegaCut ϕ C j ↔ (Tpoint ϕ u ∩ C).ncard = j := Iff.rfl

/-- The top class is `Ω(C)`: `|T(u) ∩ C| = |T(u)|` exactly when `T(u) ⊆ C`. -/
theorem omegaCut_eq_omegaOf (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) : omegaCut ϕ C t = omegaOf (Ω := Ω) ϕ C := by
  ext u
  rw [mem_omegaCut, mem_omegaOf]
  constructor
  · intro h
    have heq : Tpoint ϕ u ∩ C = Tpoint ϕ u :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left
        (le_of_eq (by rw [h, ← ht u, tPoint])) (Set.toFinite _)
    rw [← heq]; exact Set.inter_subset_right
  · intro h
    rw [Set.inter_eq_self_of_subset_left h, ← tPoint, ht u]

/-- The classes are invariant under any subgroup of `G` whose `ϕ`-image preserves `C`
setwise — in particular under the group `G_C` of Prop. 12.0.9.  (Same proof as
`Babai.isInvariant_omegaOf_of_le`: the labels transform by `ϕ`, Eq. (54).) -/
theorem isInvariant_omegaCut (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (C : Set (Fin m)) (j : ℕ)
    (Gs : Subgroup (Equiv.Perm Ω)) (hle : Gs ≤ G)
    (hstab : ∀ τ : Equiv.Perm Ω, ∀ h : τ ∈ Gs, (ϕ ⟨τ, hle h⟩) '' C = C) :
    IsInvariant Gs (omegaCut ϕ C j) := by
  have key : ∀ (τ : Equiv.Perm Ω) (hτ : τ ∈ Gs) (u : Ω),
      (Tpoint ϕ (τ u) ∩ C).ncard = (Tpoint ϕ u ∩ C).ncard := by
    intro τ hτ u
    have hT : Tpoint ϕ (τ u) = (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ u) :=
      theorem_10_5_1_c_eq54 ϕ hϕ hk u ⟨τ, hle hτ⟩
    have hC := hstab τ hτ
    have : Tpoint ϕ (τ u) ∩ C = (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ u ∩ C) := by
      rw [hT, ← hC, ← Set.image_inter (ϕ ⟨τ, hle hτ⟩).injective, hC]
    rw [this, Set.ncard_image_of_injective _ (ϕ ⟨τ, hle hτ⟩).injective]
  intro τ hτ
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    show (Tpoint ϕ (τ w) ∩ C).ncard = j
    rw [key τ hτ w]; exact hw
  · intro hu
    refine ⟨τ⁻¹ u, ?_, by simp⟩
    show (Tpoint ϕ (τ⁻¹ u) ∩ C).ncard = j
    have := key τ hτ (τ⁻¹ u)
    rw [show (τ : Equiv.Perm Ω) (τ⁻¹ u) = u from by simp] at this
    rw [← this]; exact hu

/-- The classes cover `Ω`: `|T(u) ∩ C| ≤ |T(u)| = t` always. -/
theorem omegaCut_cover (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) :
    (omegaOf (Ω := Ω) ϕ C ∪ ⋃ j ∈ List.range t, omegaCut ϕ C j) = (Set.univ : Set Ω) := by
  rw [← omegaCut_eq_omegaOf ϕ C ht]
  ext u
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_univ, iff_true, List.mem_range,
    exists_prop]
  set j := (Tpoint ϕ u ∩ C).ncard with hj
  have hle : j ≤ t := by
    rw [hj, ← ht u, tPoint]
    exact Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
  rcases Nat.lt_or_ge j t with h | h
  · exact Or.inr ⟨j, h, rfl⟩
  · have hjt : j = t := by omega
    exact Or.inl (mem_omegaCut.2 hjt)

/-! ### The size of the classes -/

open scoped Classical in
/-- The set of `t`-subsets of `Γ` meeting `C` in exactly `j` points: the color class of
`Φ = (Γ choose t)` under the two-coloring `(C, Γ ∖ C)`. -/
noncomputable def phiCut (C : Set (Fin m)) (t j : ℕ) : Finset (Finset (Fin m)) :=
  (Phi (Fin m) t).filter (fun T => (T ∩ (Set.toFinite C).toFinset).card = j)

open scoped Classical in
theorem ncard_omegaCut_eq_mul (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (C : Set (Fin m)) (j : ℕ)
    (T₀ : Finset (Fin m)) (hT₀ : T₀.card = t) :
    (omegaCut (Ω := Ω) ϕ C j).ncard =
      (phiCut C t j).card * (labelFiber (Ω := Ω) ϕ T₀).card := by
  have hset : omegaCut (Ω := Ω) ϕ C j = ↑(labelPreim (Ω := Ω) ϕ (phiCut C t j)) := by
    ext u
    simp only [Finset.mem_coe, labelPreim, Finset.mem_filter, Finset.mem_univ, true_and,
      phiCut, Phi, Finset.mem_powersetCard, mem_omegaCut]
    constructor
    · intro h
      refine ⟨⟨Finset.subset_univ _, by rw [card_labelF, ht u]⟩, ?_⟩
      rw [← h, ← Set.ncard_coe_finset, Finset.coe_inter, coe_labelF,
        Set.Finite.coe_toFinset]
    · rintro ⟨-, h⟩
      rw [← h, ← Set.ncard_coe_finset, Finset.coe_inter, coe_labelF,
        Set.Finite.coe_toFinset]
  rw [hset, Set.ncard_coe_finset]
  exact card_labelPreim_eq_mul ϕ hϕ hk hm3 _
    (fun T hT => (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT).1).2) T₀ hT₀

open scoped Classical in
/-- `Babai.phiCut` is the color class of Lemma 7.2.1 for the two-coloring `(C, Γ ∖ C)`
with color vector `(j, t − j)`. -/
theorem phiCut_eq_tupleClass (C : Set (Fin m)) {t j : ℕ} (hj : j ≤ t) :
    phiCut C t j =
      tupleClass (fun γ : Fin m => decide (γ ∈ (Set.toFinite C).toFinset))
        t (fun b : Bool => cond b j (t - j)) := by
  ext T
  rw [phiCut, Finset.mem_filter, mem_tupleClass, Phi, Finset.mem_powersetCard]
  have hfilter : T.filter (fun γ => decide (γ ∈ (Set.toFinite C).toFinset) = true) =
      T ∩ (Set.toFinite C).toFinset := by
    ext γ
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      exact Finset.mem_inter.2 ⟨h.1, of_decide_eq_true h.2⟩
    · intro h
      rw [Finset.mem_inter] at h
      exact Finset.mem_filter.2 ⟨h.1, decide_eq_true h.2⟩
  have hfilterF : T.filter (fun γ => decide (γ ∈ (Set.toFinite C).toFinset) = false) =
      T \ (Set.toFinite C).toFinset := by
    ext γ
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      exact Finset.mem_sdiff.2 ⟨h.1, of_decide_eq_false h.2⟩
    · intro h
      rw [Finset.mem_sdiff] at h
      exact Finset.mem_filter.2 ⟨h.1, decide_eq_false h.2⟩
  have hsplit : (T ∩ (Set.toFinite C).toFinset).card +
      (T \ (Set.toFinite C).toFinset).card = T.card :=
    Finset.card_inter_add_card_sdiff _ _
  constructor
  · rintro ⟨⟨-, hTcard⟩, hj'⟩
    refine ⟨hTcard, ?_⟩
    funext b
    cases b with
    | true =>
      show (T.filter (fun γ => decide (γ ∈ (Set.toFinite C).toFinset) = true)).card = j
      rw [hfilter]; exact hj'
    | false =>
      show (T.filter (fun γ => decide (γ ∈ (Set.toFinite C).toFinset) = false)).card = t - j
      rw [hfilterF]; omega
  · rintro ⟨hTcard, hcol⟩
    refine ⟨⟨Finset.subset_univ _, hTcard⟩, ?_⟩
    have hc := congrFun hcol true
    rw [show tupleColor (fun γ : Fin m => decide (γ ∈ (Set.toFinite C).toFinset)) T true =
      (T.filter (fun γ => decide (γ ∈ (Set.toFinite C).toFinset) = true)).card from rfl,
      hfilter] at hc
    exact hc

open scoped Classical in
/-- §12, the bound the paper attributes to Lemma 7.2.1: **`3|Ω_j| ≤ 2n` for `1 ≤ j < t`**.

Lemma 7.2.1 (a) gives `3|Φ_j| ≤ 2|Φ|` for the color vector `(j, t − j)`, which is not
exceptional precisely when `j ≠ t` and `t − j ≠ t`, i.e. `1 ≤ j < t`.  Multiplying by the
common size `b` of the standard blocks turns this into the bound on `|Ω_j|`, because
`|Ω_j| = |Φ_j|·b` and `n = |Φ|·b`. -/
theorem three_mul_ncard_omegaCut_le (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (h2t : 2 * t ≤ m) (C : Set (Fin m)) {j : ℕ}
    (hj1 : 1 ≤ j) (hjt : j < t) :
    3 * (omegaCut (Ω := Ω) ϕ C j).ncard ≤ 2 * Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have hvne : ∀ b : Bool, (cond b j (t - j) : ℕ) ≠ t := by
    intro b
    cases b with
    | true => show j ≠ t; omega
    | false => show t - j ≠ t; omega
  have h721 := lemma_7_2_1a (Γ := Fin m) (ι := Bool)
    (fun γ : Fin m => decide (γ ∈ (Set.toFinite C).toFinset))
    (t := t) (by rw [Fintype.card_fin]; exact h2t)
    (v := fun b : Bool => cond b j (t - j)) hvne
  rw [← phiCut_eq_tupleClass C (le_of_lt hjt)] at h721
  rw [ncard_omegaCut_eq_mul hG ϕ hϕ hk hm3 ht C j T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 3 * ((phiCut C t j).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (3 * (phiCut C t j).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (2 * (Phi (Fin m) t).card) * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h721
    _ = 2 * (m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

open scoped Classical in
/-- §12, the class `Ω_0 = Ω(Γ ∖ C)`, which Lemma 7.2.1 (a) does not cover (its color
vector `(0, t)` *is* exceptional): **`2|Ω_0| ≤ n`** whenever `2|Γ ∖ C| ≤ m` and `t ≥ 1`.

The `t`-subsets counted by `Φ_0` are exactly the `t`-subsets of `Γ ∖ C`, so
`|Φ_0| ≤ C(|Γ ∖ C|, t)`, and `2·C(m', t) ≤ C(m, t)` for `2m' ≤ m` and `t ≥ 1`
(`Babai.two_mul_choose_le_of_two_mul_le`). -/
theorem two_mul_ncard_omegaCut_zero_le (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m) (C : Set (Fin m))
    (hC : 2 * (Cᶜ : Set (Fin m)).ncard ≤ m) :
    2 * (omegaCut (Ω := Ω) ϕ C 0).ncard ≤ Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  set CF : Finset (Fin m) := (Set.toFinite C).toFinset with hCF
  have hsub : phiCut C t 0 ⊆ Finset.powersetCard t CFᶜ := by
    intro T hT
    rw [phiCut, Finset.mem_filter, Phi, Finset.mem_powersetCard] at hT
    have hempty : T ∩ CF = ∅ := Finset.card_eq_zero.1 hT.2
    rw [Finset.mem_powersetCard]
    refine ⟨fun γ hγ => ?_, hT.1.2⟩
    rw [Finset.mem_compl]
    intro hγC
    have hmem : γ ∈ T ∩ CF := Finset.mem_inter.2 ⟨hγ, hγC⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty γ hmem
  have hcardCF : (CFᶜ : Finset (Fin m)).card = (Cᶜ : Set (Fin m)).ncard := by
    rw [← Set.ncard_coe_finset, Finset.coe_compl, hCF, Set.Finite.coe_toFinset]
  have hle : (phiCut C t 0).card ≤ ((Cᶜ : Set (Fin m)).ncard).choose t := by
    calc (phiCut C t 0).card ≤ (Finset.powersetCard t (CFᶜ : Finset (Fin m))).card :=
          Finset.card_le_card hsub
      _ = ((CFᶜ : Finset (Fin m)).card).choose t := Finset.card_powersetCard _ _
      _ = ((Cᶜ : Set (Fin m)).ncard).choose t := by rw [hcardCF]
  have hkey : 2 * (phiCut C t 0).card ≤ m.choose t :=
    le_trans (Nat.mul_le_mul_left _ hle) (two_mul_choose_le_of_two_mul_le ht1 hC)
  rw [ncard_omegaCut_eq_mul hG ϕ hϕ hk hm3 ht C 0 T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 2 * ((phiCut C t 0).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (2 * (phiCut C t 0).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card := Nat.mul_le_mul_right _ hkey

open scoped Classical in
/-- The remaining classes have total size at most `n`: they are pairwise disjoint subsets
of `Ω`.  (`n` is the sum over *all* `t + 1` values of `j`.) -/
theorem sum_ncard_omegaCut_le (ϕ : G →* Equiv.Perm (Fin m)) (C : Set (Fin m)) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (s : ℕ) (hs : s ≤ t + 1) :
    ∑ j ∈ Finset.range s, (omegaCut (Ω := Ω) ϕ C j).ncard ≤ Fintype.card Ω := by
  have hfin : ∀ j : ℕ, (omegaCut (Ω := Ω) ϕ C j).ncard =
      (Finset.univ.filter (fun u : Ω => (Tpoint ϕ u ∩ C).ncard = j)).card := by
    intro j
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext u
    simp [omegaCut]
  have hall : (Finset.univ : Finset Ω).card =
      ∑ j ∈ Finset.range (t + 1),
        (Finset.univ.filter (fun u : Ω => (Tpoint ϕ u ∩ C).ncard = j)).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := fun u : Ω => (Tpoint ϕ u ∩ C).ncard)
      (t := Finset.range (t + 1)) ?_
    intro u _
    simp only [Finset.mem_coe, Finset.mem_range]
    have : (Tpoint ϕ u ∩ C).ncard ≤ tPoint ϕ u :=
      Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    rw [ht u] at this
    omega
  have hrange : Finset.range s ⊆ Finset.range (t + 1) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hs)
  calc ∑ j ∈ Finset.range s, (omegaCut (Ω := Ω) ϕ C j).ncard
      = ∑ j ∈ Finset.range s,
          (Finset.univ.filter (fun u : Ω => (Tpoint ϕ u ∩ C).ncard = j)).card :=
        Finset.sum_congr rfl (fun j _ => hfin j)
    _ ≤ ∑ j ∈ Finset.range (t + 1),
          (Finset.univ.filter (fun u : Ω => (Tpoint ϕ u ∩ C).ncard = j)).card :=
        Finset.sum_le_sum_of_subset hrange
    _ = Fintype.card Ω := by rw [← hall, Finset.card_univ]

/-- A sum over `List.range n` as a `Finset.range` sum. -/
theorem sum_list_range {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

end Babai
