/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, lines 5–6 and Sec. 14.2, Eq. (72): with a dominant color class, every color
class of `Ω` other than the dominant window has at most two thirds of the points.
-/
import Workspace.Master.AlignDominantKer

/-!
# The classes other than the dominant window have at most `2n/3` points

The hint of line 11 of Procedure Align goes to the first call of the
Chain Rule over the orbits of `G*` in the dominant window, and only when that orbit has more
than `2n/3` points. The machine recognises that call by its size alone. For that it needs
every other call of the round to have at most `2n/3` points: the other orbits of `G*` in the
dominant window have fewer than `n/3` (`Babai.AlignDominant.other_orbit_small`), and this file
proves the bound for the other color classes of `Ω`.

A class `Ω_v` of line 4 is the set of points whose label `T(u)` has color vector `v`.

* If `v` is not `t` on a single color (a *mixed* class), Lemma 7.2.1 (a) gives at most `2n/3`
  (`Babai.three_mul_ncard_omegaColorClass_le`).
* If `v` is `t` on the color `j`, the class is the window `Ω(Δ_j)`. For `j ≠ i₀` the class `Δ_j`
  is disjoint from the dominant class, so `2|Δ_j| ≤ m`, and Lemma 7.2.1 (b) gives the relative
  size `C(|Δ_j|, t) / C(m, t) ≤ (|Δ_j|/m)^t ≤ 1/2`.

The mixed classes need not have fewer than `n/2` points: for `t = 2`, `m = 217` and a
two-coloring of `Γ` with classes of `109` and `108` vertices, the mixed class has
`109 · 108 = 11772` of the `C(217, 2) = 23436` labels, more than half
(`Babai.mixed_class_more_than_half_example`). The bound `2n/3` is what holds in general, and it is
what the test of the hinted call needs.

Main results:

* `Babai.three_mul_card_tupleClass_le_of_half_at`: the bound on `(Γ choose t)`;
* `Babai.three_mul_ncard_omegaColorClass_le_of_half_at`: the bound on `Ω`;
* `Babai.three_mul_ncard_omegaColorClass_le_of_ne_dom`: with a dominant class, every color class
  of `Ω` other than the dominant window has at most `2n/3` points (the form of
  `Babai.five_mul_ncard_omegaColorClass_le_of_ne_dom` with `2/3` in place of `4/5`);
* `Babai.two_mul_ncard_omegaOf_le_of_ne_dom`: a window `Ω(Δ_j)` with `j ≠ i₀` has at most `n/2`
  points.
-/

universe u

namespace Babai

open Equiv MulAction
open scoped Classical

/-- The arithmetic behind the remark that a mixed class can have more than half of the labels:
`t = 2`, `m = 217`, color classes of `109` and `108` vertices. -/
theorem mixed_class_more_than_half_example : Nat.choose 217 2 < 2 * (109 * 108) := by
  norm_num [Nat.choose_two_right]

section Tuples

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- §7.2 / §14.2, **Lemma 7.2.1 at the threshold `1/2`**, for one class of `(Γ choose t)`: if
the colors `i` with `v i = t` have at most `|Γ|/2` vertices, the class `Φ_v` has at most two
thirds of `(Γ choose t)`.

*Proof.* If some `v i = t`, Lemma 7.2.1 (b) bounds the relative size by
`(|Δ_i|/|Γ|)^t ≤ (1/2)^t ≤ 1/2 ≤ 2/3`, since `t ≥ 1`. Otherwise Lemma 7.2.1 (a) gives `2/3`. -/
theorem three_mul_card_tupleClass_le_of_half_at [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) (v : ι → ℕ)
    (hhalf : ∀ i, v i = t → 2 * (colorSet c i).card ≤ Fintype.card Γ) :
    3 * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
  by_cases hex : ∃ i, v i = t
  · obtain ⟨i, hvi⟩ := hex
    have hm : 0 < Fintype.card Γ := by omega
    have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
    have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : t ≤ Fintype.card Γ)
    have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
      have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
      rw [Finset.card_powersetCard] at this
      exact_mod_cast this
    have hb := lemma_7_2_1b c i hm (by omega : t ≤ Fintype.card Γ)
    have h2 : (2 : ℝ) * (colorSet c i).card ≤ Fintype.card Γ := by exact_mod_cast hhalf i hvi
    have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hmR]; linarith
    have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
    have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ (1 / 2 : ℝ) ^ t :=
      pow_le_pow_left₀ hratio0 hratio t
    have hαt : (1 / 2 : ℝ) ^ t ≤ 1 / 2 := by
      have h1 : (1 / 2 : ℝ) ^ t ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht1
      rwa [pow_one] at h1
    have hkey : ((tupleClass c t v).card : ℝ) ≤ 1 / 2 * ((Fintype.card Γ).choose t : ℝ) := by
      calc ((tupleClass c t v).card : ℝ)
          ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
        _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
              * ((Fintype.card Γ).choose t) := by field_simp
        _ ≤ 1 / 2 * ((Fintype.card Γ).choose t) :=
            mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
    have hR : (3 : ℝ) * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
      rw [card_Phi]
      nlinarith
    exact_mod_cast hR
  · push Not at hex
    exact lemma_7_2_1a c ht hex

/-- §7.2, **Lemma 7.2.1 (b) at the threshold `1/2`**: a class `Φ_v` whose vector is `t` on a
color `i` with at most `|Γ|/2` vertices has at most half of `(Γ choose t)`. -/
theorem two_mul_card_tupleClass_le_of_half (c : Γ → ι) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : t ≤ Fintype.card Γ) {v : ι → ℕ} {i : ι} (hvi : v i = t)
    (hhalf : 2 * (colorSet c i).card ≤ Fintype.card Γ) :
    2 * (tupleClass c t v).card ≤ (Phi Γ t).card := by
  have hm : 0 < Fintype.card Γ := by omega
  have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
  have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos ht
  have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
    have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
    rw [Finset.card_powersetCard] at this
    exact_mod_cast this
  have hb := lemma_7_2_1b c i hm ht
  have h2 : (2 : ℝ) * (colorSet c i).card ≤ Fintype.card Γ := by exact_mod_cast hhalf
  have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hmR]; linarith
  have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
  have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ (1 / 2 : ℝ) ^ t :=
    pow_le_pow_left₀ hratio0 hratio t
  have hαt : (1 / 2 : ℝ) ^ t ≤ 1 / 2 := by
    have h1 : (1 / 2 : ℝ) ^ t ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht1
    rwa [pow_one] at h1
  have hkey : ((tupleClass c t v).card : ℝ) ≤ 1 / 2 * ((Fintype.card Γ).choose t : ℝ) := by
    calc ((tupleClass c t v).card : ℝ)
        ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
      _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
            * ((Fintype.card Γ).choose t) := by field_simp
      _ ≤ 1 / 2 * ((Fintype.card Γ).choose t) :=
          mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
  have hR : (2 : ℝ) * (tupleClass c t v).card ≤ (Phi Γ t).card := by
    rw [card_Phi]
    nlinarith
  exact_mod_cast hR

end Tuples

section Classes

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Perm Ω)}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A `t`-subset of `Γ`, the label of a standard block. -/
private theorem exists_card_eq_t {t : ℕ} (h : t ≤ m) : ∃ T₀ : Finset (Fin m), T₀.card = t := by
  obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (n := t)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact h)
  exact ⟨T₀, hT₀⟩

/-- §14.1, lines 5–6, Eq. (72) at the threshold `1/2`, lifted to `Ω`: if the colors `i` with
`v i = t` have at most `m/2` vertices, the class `Ω_v` has at most `2n/3` points.
`Babai.three_mul_card_tupleClass_le_of_half_at` multiplied by the common size of a standard
block (`Babai.ncard_omegaColorClass_eq_mul`, `Babai.card_univ_eq_mul`). -/
theorem three_mul_ncard_omegaColorClass_le_of_half_at [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    (v : ι → ℕ) (hhalf : ∀ i, v i = t → 2 * (colorSet c i).card ≤ m) :
    3 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 2 * Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ := exists_card_eq_t (m := m) (t := t) (by omega)
  have h72 := three_mul_card_tupleClass_le_of_half_at (Γ := Fin m) (ι := ι) c ht1
    (by rw [Fintype.card_fin]; exact h2t) v
    (by intro i hi; rw [Fintype.card_fin]; exact hhalf i hi)
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 3 * ((tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (3 * (tupleClass c t v).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (2 * (Phi (Fin m) t).card) * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h72
    _ = 2 * (m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

omit [Fintype ι] in
/-- The color class `Δ_j` of `Γ` for a color other than the dominant one has at most `m/2`
vertices: it is disjoint from the dominant class, which has more than `m/2`. -/
theorem two_mul_card_colorSet_le_of_ne_dom (c : Fin m → ι) {i₀ j : ι}
    (hdom : m < 2 * (colorSet c i₀).card) (hj : j ≠ i₀) : 2 * (colorSet c j).card ≤ m := by
  have hdisj : Disjoint (colorSet c j) (colorSet c i₀) := by
    rw [Finset.disjoint_left]
    intro γ h1 h2
    simp only [colorSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hj (h1.symm.trans h2)
  have hsum : (colorSet c j).card + (colorSet c i₀).card ≤ m := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have h := Finset.card_le_univ ((colorSet c j) ∪ (colorSet c i₀))
    rwa [Fintype.card_fin] at h
  omega

/-- §14.1, lines 5–6: **with a dominant color class `Δ_{i₀}`, every color class of `Ω` other
than the window `Ω(Δ_{i₀})` has at most `2n/3` points.** A mixed class is Lemma 7.2.1 (a); a
class whose label lies inside one color class `Δ_j` has `j ≠ i₀` (else it is the window), so
`2|Δ_j| ≤ m` and Lemma 7.2.1 (b) gives at most `n/2`. This is
`Babai.five_mul_ncard_omegaColorClass_le_of_ne_dom` with `2/3` in place of `4/5`; it is what
lets the machine recognise the hinted call of line 11 by its size (more than `2n/3`). -/
theorem three_mul_ncard_omegaColorClass_le_of_ne_dom [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (hm3 : 3 ≤ m) {t : ℕ} (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m)
    (c : Fin m → ι) {i₀ : ι} (hdom : m < 2 * (colorSet c i₀).card) (v : ι → ℕ)
    (hv : omegaColorClass (Ω := Ω) ϕ c v ≠ omegaOf ϕ {γ : Fin m | c γ = i₀}) :
    3 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 2 * Fintype.card Ω := by
  by_cases hemp : (omegaColorClass (Ω := Ω) ϕ c v).ncard = 0
  · rw [hemp]; omega
  obtain ⟨u, hu⟩ : (omegaColorClass (Ω := Ω) ϕ c v).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, Set.ncard_empty] at hemp
    exact hemp rfl
  set v₀ : ι → ℕ := fun j => if j = i₀ then t else 0 with hv₀def
  have hS₀eq : omegaColorClass (Ω := Ω) ϕ c v₀ = omegaOf ϕ {γ : Fin m | c γ = i₀} :=
    omegaColorClass_eq_omegaOf ϕ ht c i₀ v₀ (by simp [hv₀def])
      (fun j hj => by simp [hv₀def, hj])
  refine three_mul_ncard_omegaColorClass_le_of_half_at hG ϕ hϕ hk hm3 ht ht1 h2t c v ?_
  intro j hj
  refine two_mul_card_colorSet_le_of_ne_dom c hdom ?_
  rintro rfl
  refine hv ?_
  have hvu : omegaColor ϕ c u = v := hu
  have hnc : (Tpoint ϕ u ∩ {γ : Fin m | c γ = j}).ncard = t := by
    have h := congrFun hvu j
    rw [hj] at h
    exact h
  have htot : (Tpoint ϕ u).ncard = t := ht u
  have hsub : Tpoint ϕ u ⊆ {γ : Fin m | c γ = j} := by
    have h1 : Tpoint ϕ u ∩ {γ : Fin m | c γ = j} = Tpoint ϕ u :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by rw [hnc, htot])
        (Set.toFinite _)
    rw [← h1]
    exact Set.inter_subset_right
  have huS : u ∈ omegaColorClass (Ω := Ω) ϕ c v₀ := by
    rw [hS₀eq, mem_omegaOf]; exact hsub
  have hvv : v = v₀ := hvu.symm.trans huS
  rw [hvv, hS₀eq]

/-- §14.1, lines 5–6: **a window `Ω(Δ_j)` of a color `j` other than the dominant one has at most
`n/2` points**: `2|Δ_j| ≤ m`, and Lemma 7.2.1 (b) gives the relative size
`C(|Δ_j|, t) / C(m, t) ≤ (|Δ_j|/m)^t ≤ 1/2`. (The mixed classes can have more than `n/2`
points, `Babai.mixed_class_more_than_half_example`; they have at most `2n/3`.) -/
theorem two_mul_ncard_omegaOf_le_of_ne_dom (hG : IsTransitive G)
    (ϕ : G →* Perm (Fin m)) (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    (hm3 : 3 ≤ m) {t : ℕ} (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (htm : t ≤ m)
    (c : Fin m → ι) {i₀ j : ι} (hdom : m < 2 * (colorSet c i₀).card) (hj : j ≠ i₀) :
    2 * (omegaOf ϕ {γ : Fin m | c γ = j} : Set Ω).ncard ≤ Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ := exists_card_eq_t (m := m) (t := t) htm
  set v : ι → ℕ := fun i => if i = j then t else 0 with hvdef
  have hS : omegaColorClass (Ω := Ω) ϕ c v = omegaOf ϕ {γ : Fin m | c γ = j} :=
    omegaColorClass_eq_omegaOf ϕ ht c j v (by simp [hvdef]) (fun i hi => by simp [hvdef, hi])
  have h72 := two_mul_card_tupleClass_le_of_half (Γ := Fin m) (ι := ι) c ht1
    (by rw [Fintype.card_fin]; exact htm) (v := v) (i := j) (by simp [hvdef])
    (by rw [Fintype.card_fin]; exact two_mul_card_colorSet_le_of_ne_dom c hdom hj)
  rw [← hS, ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 2 * ((tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (2 * (tupleClass c t v).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (Phi (Fin m) t).card * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h72
    _ = m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card := by
        rw [card_Phi, Fintype.card_fin]

end Classes

end Babai
