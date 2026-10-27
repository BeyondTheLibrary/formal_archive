/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 7.2: Effect of coloring on t-tuples.
-/
import Workspace.ColoredPartitions.Binomial
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# §7.2 Effect of coloring on `t`-tuples (Lemma 7.2.1, Corollary 7.2.2)

*"Let `Γ` be a set and `Φ = (Γ choose t)` the set of `t`-subsets of `Γ`.  Let `|Γ| = m`;
so `|Φ| = C(m,t)`."*

| Paper | Lean |
|---|---|
| `Φ` | `Babai.Phi`, `Babai.card_Phi` |
| `Δᵢ` | `Babai.colorSet` |
| the induced coloring of `Φ` | `Babai.tupleColor`, `Babai.tupleClass` |
| size of a color class of `Φ` | `Babai.card_tupleClass` |
| Lemma 7.2.1(a) | `Babai.lemma_7_2_1a` |
| Lemma 7.2.1(b) | `Babai.lemma_7_2_1b` |
| Corollary 7.2.2 | `Babai.cor_7_2_2` (all `t ≠ m`), `Babai.cor_7_2_2_of_two_mul_le` (the paper's proof, `2t ≤ m`), `Babai.cor_7_2_2_false_at_t_eq_m` |

Two points about the statements.

* Lemma 7.2.1(a) needs the hypothesis `2t ≤ m` (`t ≤ m/2`) of Proposition 7.2.3, which
  its proof uses; without it it is false.  Corollary 7.2.2 needs only `t ≠ m`; it is false
  at `t = m` (`cor_7_2_2_false_at_t_eq_m`).  See the corrected paper the counterexamples.
* The number `k` of color classes is at least `1` in the paper (the induction of the proof
  starts at `k = 1`); here this is `[Nonempty ι]`.  It is needed: for `k = 0` the set `Γ`
  is empty, `t = 0`, and the unique color class of `Φ = {∅}` is all of `Φ`, while there is
  no set `(Δᵢ choose t)` to exempt it.
-/

namespace Babai

open Finset

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- §7.2.  `Φ = (Γ choose t)`, the set of `t`-subsets of `Γ`. -/
def Phi (Γ : Type*) [Fintype Γ] [DecidableEq Γ] (t : ℕ) : Finset (Finset Γ) :=
  Finset.powersetCard t Finset.univ

/-- §7.2.  `|Φ| = C(m,t)` where `m = |Γ|`. -/
theorem card_Phi (t : ℕ) : (Phi Γ t).card = (Fintype.card Γ).choose t := by
  rw [Phi, Finset.card_powersetCard, Finset.card_univ]

/-- Lemma 7.2.1.  The color class `Δᵢ` of the coloring `c` of `Γ`. -/
def colorSet (c : Γ → ι) (i : ι) : Finset Γ := Finset.univ.filter fun x => c x = i

theorem sum_card_colorSet (c : Γ → ι) : ∑ i, (colorSet c i).card = Fintype.card Γ := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (f := c) (fun x _ => Finset.mem_univ (c x))).symm

/-- Lemma 7.2.1.  *"the color of `T ∈ (Γ choose t)` is the vector
`(|T ∩ Δᵢ| | 1 ≤ i ≤ k)`."* -/
def tupleColor (c : Γ → ι) (T : Finset Γ) : ι → ℕ :=
  fun i => (T.filter fun x => c x = i).card

theorem sum_tupleColor (c : Γ → ι) (T : Finset Γ) : ∑ i, tupleColor c T i = T.card :=
  (Finset.card_eq_sum_card_fiberwise (f := c) (fun x _ => Finset.mem_univ (c x))).symm

/-- Lemma 7.2.1.  The color class of `Φ` with color vector `v`. -/
def tupleClass (c : Γ → ι) (t : ℕ) (v : ι → ℕ) : Finset (Finset Γ) :=
  (Phi Γ t).filter fun T => tupleColor c T = v

theorem mem_tupleClass {c : Γ → ι} {t : ℕ} {v : ι → ℕ} {T : Finset Γ} :
    T ∈ tupleClass c t v ↔ T.card = t ∧ tupleColor c T = v := by
  simp [tupleClass, Phi, Finset.mem_powersetCard, Finset.subset_univ]

theorem filter_biUnion (c : Γ → ι) {F : ι → Finset Γ} (hF : ∀ i, F i ⊆ colorSet c i) (i : ι) :
    (Finset.univ.biUnion F).filter (fun x => c x = i) = F i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hxj⟩, hci⟩
    have hcj : c x = j := by simpa [colorSet] using hF j hxj
    have : j = i := by rw [← hcj, hci]
    subst this
    exact hxj
  · intro hx
    have : c x = i := by simpa [colorSet] using hF i hx
    exact ⟨⟨i, hx⟩, this⟩

/-- The size of a color class of `Φ`: `∏ᵢ C(|Δᵢ|, vᵢ)`.  (A `t`-subset with `|T ∩ Δᵢ| = vᵢ`
is the same thing as a choice, for each `i`, of a `vᵢ`-subset of `Δᵢ`.) -/
theorem card_tupleClass (c : Γ → ι) {t : ℕ} {v : ι → ℕ} (hv : ∑ i, v i = t) :
    (tupleClass c t v).card = ∏ i, (colorSet c i).card.choose (v i) := by
  have hdisj : ∀ {F : ι → Finset Γ}, (∀ i, F i ⊆ colorSet c i) →
      ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
        Disjoint (F i) (F j) := by
    intro F hF i _ j _ hij
    refine Finset.disjoint_left.2 fun x hxi hxj => hij ?_
    have h1 : c x = i := by simpa [colorSet] using hF i hxi
    have h2 : c x = j := by simpa [colorSet] using hF j hxj
    rw [← h1, ← h2]
  have hpi : (Fintype.piFinset (fun i => (colorSet c i).powersetCard (v i))).card
      = ∏ i, (colorSet c i).card.choose (v i) := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun i _ => Finset.card_powersetCard _ _
  rw [← hpi]
  refine Finset.card_bij'
    (fun T _ => fun i => T.filter fun x => c x = i)
    (fun F _ => Finset.univ.biUnion F) ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_tupleClass] at hT
    refine Fintype.mem_piFinset.2 fun i => ?_
    rw [Finset.mem_powersetCard]
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [Finset.mem_filter] at hx
      simpa [colorSet] using hx.2
    · exact congrFun hT.2 i
  · intro F hF
    rw [Fintype.mem_piFinset] at hF
    have hsub : ∀ i, F i ⊆ colorSet c i := fun i =>
      (Finset.mem_powersetCard.1 (hF i)).1
    have hcard : ∀ i, (F i).card = v i := fun i => (Finset.mem_powersetCard.1 (hF i)).2
    rw [mem_tupleClass]
    constructor
    · rw [Finset.card_biUnion (hdisj hsub)]
      simp only [hcard]
      exact hv
    · funext i
      rw [tupleColor, filter_biUnion c hsub i, hcard i]
  · intro T hT
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, hx, -⟩
      exact hx
    · intro hx
      exact ⟨c x, hx, rfl⟩
  · intro F hF
    rw [Fintype.mem_piFinset] at hF
    have hsub : ∀ i, F i ⊆ colorSet c i := fun i => (Finset.mem_powersetCard.1 (hF i)).1
    funext i
    exact filter_biUnion c hsub i

/-- The product bound used to reduce Lemma 7.2.1 to the case of two color classes:
`∏_{i ∈ s} C(mᵢ, vᵢ) ≤ C(∑_{i ∈ s} mᵢ, ∑_{i ∈ s} vᵢ)` (Vandermonde's identity, one term at
a time). -/
theorem prod_choose_le (s : Finset ι) (m v : ι → ℕ) :
    ∏ i ∈ s, (m i).choose (v i) ≤ (∑ i ∈ s, m i).choose (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Nat.mul_le_mul_left _ ih) (choose_mul_choose_le _ _ _ _)

/-- Lemma 7.2.1(a).  *"the size of each color class in `Φ` is `≤ (2/3)|Φ|` with the
possible exception of one of the `k` sets `(Δᵢ choose t)`."*

The exceptional color classes are those whose color vector has `vᵢ = t` for some `i`; such
a class is contained in `(Δᵢ choose t)` (`tupleClass_subset_powersetCard`).

Proof.  The paper proves this by induction on `k`, the case `k = 2` being Prop. 7.2.3.  We
reduce to the case `k = 2` directly, by grouping all classes other than `Δ_{i₀}` into one
(see the corrected paper why the paper's induction step is replaced): if `vᵢ ≠ t` for all
`i` and the class is non-empty, pick `i₀` with `v_{i₀} ≥ 1`; then
`∑_{i ≠ i₀} vᵢ = t - v_{i₀} ≥ 1`, and
`∏ᵢ C(mᵢ,vᵢ) ≤ C(m_{i₀}, v_{i₀}) · C(∑_{i≠i₀} mᵢ, ∑_{i≠i₀} vᵢ) ≤ (2/3) C(m,t)`
by `prod_choose_le` and Prop. 7.2.3. -/
theorem lemma_7_2_1a [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht : 2 * t ≤ Fintype.card Γ)
    {v : ι → ℕ} (hv : ∀ i, v i ≠ t) :
    3 * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
  rcases Finset.eq_empty_or_nonempty (tupleClass c t v) with hempty | ⟨T, hT⟩
  · simp [hempty]
  rw [mem_tupleClass] at hT
  have hsum : ∑ i, v i = t := by rw [← hT.2, sum_tupleColor, hT.1]
  -- `t ≥ 1`: otherwise every `vᵢ = 0 = t`, contradicting the hypothesis
  have ht1 : 1 ≤ t := by
    by_contra hcon
    have ht0 : t = 0 := by omega
    have hz : v (Classical.arbitrary ι) = 0 :=
      (Finset.sum_eq_zero_iff.1 (hsum.trans ht0)) _ (Finset.mem_univ _)
    exact hv (Classical.arbitrary ι) (by omega)
  -- pick `i₀` with `v i₀ ≥ 1`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, 1 ≤ v i₀ := by
    by_contra hcon
    push_neg at hcon
    have : ∑ i, v i = 0 := Finset.sum_eq_zero fun i _ => by have := hcon i; omega
    omega
  have hmsum : (colorSet c i₀).card + ∑ i ∈ Finset.univ.erase i₀, (colorSet c i).card
      = Fintype.card Γ := by
    rw [Finset.add_sum_erase _ (fun i => (colorSet c i).card) (Finset.mem_univ i₀)]
    exact sum_card_colorSet c
  have hvsum : v i₀ + ∑ i ∈ Finset.univ.erase i₀, v i = t := by
    rw [Finset.add_sum_erase _ v (Finset.mem_univ i₀)]
    exact hsum
  have hrest : 1 ≤ ∑ i ∈ Finset.univ.erase i₀, v i := by
    have := hv i₀
    omega
  have hprod : (tupleClass c t v).card
      ≤ (colorSet c i₀).card.choose (v i₀) *
        (∑ i ∈ Finset.univ.erase i₀, (colorSet c i).card).choose
          (∑ i ∈ Finset.univ.erase i₀, v i) := by
    rw [card_tupleClass c hsum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    exact Nat.mul_le_mul_left _ (prod_choose_le _ _ _)
  have h723 := choose_mul_choose_le_two_thirds
    (m₁ := (colorSet c i₀).card) (m₂ := ∑ i ∈ Finset.univ.erase i₀, (colorSet c i).card)
    (t₁ := v i₀) (t₂ := ∑ i ∈ Finset.univ.erase i₀, v i)
    (by rw [hmsum, hvsum]; exact ht) hi₀ hrest
  rw [hmsum, hvsum] at h723
  rw [card_Phi]
  omega

/-- A color class whose vector has `vᵢ = t` is contained in `(Δᵢ choose t)`. -/
theorem tupleClass_subset_powersetCard (c : Γ → ι) {t : ℕ} {v : ι → ℕ} {i : ι}
    (hvi : v i = t) : tupleClass c t v ⊆ (colorSet c i).powersetCard t := by
  intro T hT
  rw [mem_tupleClass] at hT
  rw [Finset.mem_powersetCard]
  refine ⟨?_, hT.1⟩
  have hcard : (T.filter fun x => c x = i).card = T.card := by
    rw [show (T.filter fun x => c x = i).card = tupleColor c T i from rfl, hT.2, hvi, hT.1]
  have := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ T) (le_of_eq hcard.symm)
  intro x hx
  rw [← this] at hx
  simp only [Finset.mem_filter] at hx
  simpa [colorSet] using hx.2

/-- The `ℕ` form of Lemma 7.2.1(b): `C(a,t) · m^t ≤ a^t · C(m,t)` for `a ≤ m`. -/
theorem choose_mul_pow_le {a m : ℕ} (h : a ≤ m) (t : ℕ) :
    a.choose t * m ^ t ≤ a ^ t * m.choose t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e1 : a.choose (t + 1) * (t + 1) = a.choose t * (a - t) := Nat.choose_succ_right_eq a t
    have e2 : m.choose (t + 1) * (t + 1) = m.choose t * (m - t) := Nat.choose_succ_right_eq m t
    have key : (a - t) * m ≤ a * (m - t) := by
      rcases Nat.lt_or_ge t a with hta | hta
      · obtain ⟨p, rfl⟩ : ∃ p, a = t + p + 1 := ⟨a - t - 1, by omega⟩
        obtain ⟨q, rfl⟩ : ∃ q, m = t + p + 1 + q := ⟨m - (t + p + 1), by omega⟩
        simp only [Nat.add_sub_cancel_left, show t + p + 1 - t = p + 1 by omega,
          show t + p + 1 + q - t = p + 1 + q by omega]
        nlinarith
      · simp [Nat.sub_eq_zero_of_le hta]
    have main : (a.choose (t + 1) * m ^ (t + 1)) * (t + 1)
        ≤ (a ^ (t + 1) * m.choose (t + 1)) * (t + 1) := by
      calc (a.choose (t + 1) * m ^ (t + 1)) * (t + 1)
          = (a.choose (t + 1) * (t + 1)) * (m ^ t * m) := by ring
        _ = (a.choose t * (a - t)) * (m ^ t * m) := by rw [e1]
        _ = (a.choose t * m ^ t) * ((a - t) * m) := by ring
        _ ≤ (a ^ t * m.choose t) * ((a - t) * m) := Nat.mul_le_mul_right _ ih
        _ ≤ (a ^ t * m.choose t) * (a * (m - t)) := Nat.mul_le_mul_left _ key
        _ = a ^ (t + 1) * (m.choose t * (m - t)) := by ring
        _ = a ^ (t + 1) * (m.choose (t + 1) * (t + 1)) := by rw [e2]
        _ = (a ^ (t + 1) * m.choose (t + 1)) * (t + 1) := by ring
    exact Nat.le_of_mul_le_mul_right main (by omega)

/-- Lemma 7.2.1(b).  *"`|(Δᵢ choose t)| / |Φ| ≤ (|Δᵢ|/m)^t`."*  (*"Item (b) is
trivial."*) -/
theorem lemma_7_2_1b (c : Γ → ι) (i : ι) {t : ℕ} (hm : 0 < Fintype.card Γ)
    (htm : t ≤ Fintype.card Γ) :
    (((colorSet c i).card.choose t : ℝ)) / ((Fintype.card Γ).choose t)
      ≤ (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t := by
  have hle : (colorSet c i).card ≤ Fintype.card Γ := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hchoose : 0 < ((Fintype.card Γ).choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos htm
  have hmpow : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ t := by positivity
  rw [div_pow, div_le_div_iff₀ hchoose hmpow]
  exact_mod_cast choose_mul_pow_le hle t

/-- Corollary 7.2.2 in the range `1 ≤ t ≤ m/2`, by the paper's proof: *"Combine the two
conclusions in Lemma 7.2.1."*  A color class of `Φ` whose vector has `vᵢ = t` for some `i`
is contained in `(Δᵢ choose t)`, whose relative size is at most `(|Δᵢ|/m)^t ≤ α^t ≤ α` by
Lemma 7.2.1(b); every other class has relative size at most `2/3` by Lemma 7.2.1(a), which
needs `2t ≤ m`. -/
theorem cor_7_2_2_of_two_mul_le [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht2 : 1 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) {α : ℝ} (hα1 : α < 1)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) (v : ι → ℕ) :
    ((tupleClass c t v).card : ℝ) ≤ max (2 / 3) α * (Phi Γ t).card := by
  have hm : 0 < Fintype.card Γ := by omega
  have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
  have hPhi : ((Phi Γ t).card : ℝ) = ((Fintype.card Γ).choose t : ℝ) := by
    rw [card_Phi]
  have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : t ≤ Fintype.card Γ)
  by_cases hex : ∃ i, v i = t
  · obtain ⟨i, hvi⟩ := hex
    have hα0 : 0 ≤ α := by
      have h1 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) := by positivity
      nlinarith [hα i]
    have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
      have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
      rw [Finset.card_powersetCard] at this
      exact_mod_cast this
    have hb := lemma_7_2_1b c i hm (by omega : t ≤ Fintype.card Γ)
    have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ α := by
      rw [div_le_iff₀ hmR]
      exact hα i
    have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
    have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ α ^ t :=
      pow_le_pow_left₀ hratio0 hratio t
    have hαt : α ^ t ≤ α := by
      calc α ^ t ≤ α ^ 1 := pow_le_pow_of_le_one hα0 (le_of_lt hα1) (by omega)
        _ = α := pow_one α
    calc ((tupleClass c t v).card : ℝ)
        ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
      _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
            * ((Fintype.card Γ).choose t) := by field_simp
      _ ≤ α * ((Fintype.card Γ).choose t) := by
          refine mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
      _ ≤ max (2 / 3) α * ((Fintype.card Γ).choose t) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hPhipos)
      _ = max (2 / 3) α * (Phi Γ t).card := by rw [hPhi]
  · push_neg at hex
    have ha := lemma_7_2_1a c ht hex
    have : ((tupleClass c t v).card : ℝ) ≤ (2 / 3) * (Phi Γ t).card := by
      have h3 : (3 : ℝ) * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
        exact_mod_cast ha
      linarith
    refine le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity

/-- A nonempty color class of `Φ` has `vᵢ ≤ |Δᵢ|` for every `i`. -/
theorem le_card_colorSet_of_mem_tupleClass {c : Γ → ι} {t : ℕ} {v : ι → ℕ} {T : Finset Γ}
    (hT : T ∈ tupleClass c t v) (i : ι) : v i ≤ (colorSet c i).card := by
  rw [mem_tupleClass] at hT
  rw [← hT.2]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx
  simp [colorSet, hx.2]

/-- Complementation `T ↦ Γ ∖ T` matches the color classes of `(Γ choose t)` with those of
`(Γ choose m-t)`: a nonempty class with vector `v` has the size of the class with vector
`(|Δᵢ| - vᵢ)ᵢ`. -/
theorem card_tupleClass_compl (c : Γ → ι) {t : ℕ} {v : ι → ℕ}
    (hne : (tupleClass c t v).Nonempty) :
    (tupleClass c t v).card
      = (tupleClass c (Fintype.card Γ - t) (fun i => (colorSet c i).card - v i)).card := by
  obtain ⟨T, hT⟩ := hne
  have hle := le_card_colorSet_of_mem_tupleClass hT
  have hsum : ∑ i, v i = t := by
    rw [mem_tupleClass] at hT
    rw [← hT.2, sum_tupleColor, hT.1]
  have hsum' : ∑ i, ((colorSet c i).card - v i) = Fintype.card Γ - t := by
    have h1 : ∑ i, ((colorSet c i).card - v i) + ∑ i, v i = Fintype.card Γ := by
      rw [← Finset.sum_add_distrib, ← sum_card_colorSet c]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
    omega
  rw [card_tupleClass c hsum, card_tupleClass c hsum']
  exact Finset.prod_congr rfl fun i _ => (Nat.choose_symm (hle i)).symm

/-- Corollary 7.2.2.  *"Let `α < 1` and `t ≥ 2`.  Then any `α`-coloring of `Γ` (every color
class has size `≤ α|Γ|`) induces a `max(2/3, α)`-coloring of `(Γ choose t)`."*

The statement needs `t ≠ m`, and nothing more.  At `t = m` it is false: `Φ = {Γ}` has one
color class, of relative size `1 > max(2/3, α)` (`cor_7_2_2_false_at_t_eq_m`).  For every
other `t` it holds (see the corrected paper 7.2.1 and Corollary 7.2.2):

* `2t ≤ m`: the paper's proof, `cor_7_2_2_of_two_mul_le`;
* `m/2 < t < m`: complementation `T ↦ Γ ∖ T` carries the color classes of `(Γ choose t)`
  to those of `(Γ choose m-t)` with the same sizes (`card_tupleClass_compl`), and
  `1 ≤ m - t < m/2`, so the first case applies to `m - t`;
* `t > m`: `Φ` is empty. -/
theorem cor_7_2_2 [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht2 : 2 ≤ t)
    (htm : t ≠ Fintype.card Γ) {α : ℝ} (hα1 : α < 1)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) (v : ι → ℕ) :
    ((tupleClass c t v).card : ℝ) ≤ max (2 / 3) α * (Phi Γ t).card := by
  rcases le_or_gt (2 * t) (Fintype.card Γ) with ht | ht
  · exact cor_7_2_2_of_two_mul_le c (by omega) ht hα1 hα v
  rcases (Nat.lt_or_gt_of_ne htm) with htm' | htm'
  · -- `m/2 < t < m`: pass to the complements
    rcases Finset.eq_empty_or_nonempty (tupleClass c t v) with hempty | hne
    · rw [hempty, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ 2 / 3 := by norm_num
      exact mul_nonneg (le_trans this (le_max_left _ _)) (Nat.cast_nonneg _)
    have hcompl := cor_7_2_2_of_two_mul_le c (t := Fintype.card Γ - t) (by omega) (by omega)
      hα1 hα (fun i => (colorSet c i).card - v i)
    rw [← card_tupleClass_compl c hne, card_Phi,
      Nat.choose_symm (le_of_lt htm')] at hcompl
    rwa [card_Phi]
  · -- `t > m`: there are no `t`-subsets
    have hPhi : Phi Γ t = ∅ := by
      rw [← Finset.card_eq_zero, card_Phi]
      exact Nat.choose_eq_zero_of_lt htm'
    have hcl : tupleClass c t v = ∅ := by
      rw [tupleClass, hPhi, Finset.filter_empty]
    simp [hcl, hPhi]

/-- Corollary 7.2.2 is false at `t = m`: on `Γ = {0, 1}` with two colors of size `1` (an
`α`-coloring for `α = 1/2`) and `t = 2`, the only `2`-subset forms a color class of
relative size `1 > max(2/3, 1/2)`. -/
theorem cor_7_2_2_false_at_t_eq_m :
    ¬ (((tupleClass (id : Fin 2 → Fin 2) 2 (fun _ => 1)).card : ℝ)
        ≤ max (2 / 3) (1 / 2 : ℝ) * (Phi (Fin 2) 2).card) := by
  have h1 : (tupleClass (id : Fin 2 → Fin 2) 2 (fun _ => 1)).card = 1 := by decide
  have h2 : (Phi (Fin 2) 2).card = 1 := by decide
  rw [h1, h2]
  norm_num

end Babai
