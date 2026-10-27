/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1, lines 4-6 and line 9: the color classes of `Ω` that Procedure Align's Chain
Rule runs over, and the group `G* = ϕ⁻¹(H)` of line 9.
-/
import Workspace.TopAction.Classes

/-!
# The color classes of Procedure Align

> 4. (: Each of our structures has an underlying coloring – possibly trivial :)
>    Let `(Δ₁, …, Δ_k)` be the coloring of `X(x)` (the `Δ_j` are the color classes); so `Γ`
>    is the disjoint union of the `Δ_j`.
>    This coloring induces a canonical coloring of `Φ = (Γ choose t)` as described in
>    Lemma 7.2.1; let `Φ₁, …, Φ_s` be the color classes.  This coloring in turn lifts to a
>    canonical coloring of `Ω` with corresponding color classes `Ω₁, …, Ω_s` where
>    `Ω_i = ⋃_{T ∈ Φ_i} B_T`.
> 5. Apply the Chain Rule to the color classes `Ω_i`.
> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j) = ⋃_{T ∈ (Δ_j choose t)} B_T`.

`Babai.omegaColor` (`Workspace/Canonical/Defs.lean`) is line 4's coloring of `Ω`: the color
of `u` is the color vector of its label `T(u)`.  This file has its color classes
(`Babai.omegaColorClass`) with the three facts Procedure Align needs of them:

* they are invariant under any subgroup of `G` whose `ϕ`-image preserves the coloring of `Γ`
  — in particular under `G₁ = ϕ⁻¹(Aut(X(x)))` (`Babai.isInvariant_omegaColorClass`);
* they cover `Ω` (`Babai.omegaColorClass_cover`);
* every class whose color vector is not `t` on a single color has at most `2n/3` points
  (`Babai.three_mul_ncard_omegaColorClass_le`), and the exceptional class of the color `i`
  is exactly the window `Ω(Δ_i)` (`Babai.omegaColorClass_eq_omegaOf`).

The route is the one of `Babai.three_mul_ncard_omegaCut_le` (`Workspace/TopAction/`) for the
two-coloring of Cor. 12.0.10: Lemma 7.2.1 (a) bounds the class of `Φ`, and the standard
blocks all have the same size, so `|Ω_v| = |Φ_v| · b` and `n = |Φ| · b`.

This is part of piece (iii) of Mismatch 2 in `Workspace/Master/DESIGN.md`.

## Line 9

> 9. let `G* = ϕ⁻¹(H)`

The preimage is taken **inside the current group**, which at line 9 is the `G₁` of line 2
(iv), because line 3 has already performed *"Update: … `G ← G₁`"*.  Since the structure `Y`
of line 7 is induced by `X(x)` on the color class `Δ_j`, every automorphism of `X(x)` is an
automorphism of `Y`, so `ϕ(G₁) = Aut(X(x)) ≤ Aut(Y) = H` and therefore `G* = G₁`
(`Babai.preimageSubgroup_eq_self`).  That is why the Chain Rule call on the dominant window,
which is made with respect to the current group, is a call with respect to `G*`.
-/

universe u

namespace Babai

open scoped Classical

/-! ### Line 9: the preimage is taken inside the current group -/

section Preimage

variable {Ω : Type u} {Γ : Type*} {G : Subgroup (Equiv.Perm Ω)}

/-- `ϕ⁻¹` is monotone. -/
theorem preimageSubgroup_mono (ϕ : G →* Equiv.Perm Γ) {H H' : Subgroup (Equiv.Perm Γ)}
    (hHH' : H ≤ H') : preimageSubgroup ϕ H ≤ preimageSubgroup ϕ H' := by
  intro τ hτ
  obtain ⟨h, hmem⟩ := mem_preimageSubgroup.1 hτ
  exact mem_preimageSubgroup.2 ⟨h, hHH' hmem⟩

/-- §14.1, **line 9**: if `ϕ` maps the current group into `H` then `ϕ⁻¹(H)` — the preimage
inside the current group — is the current group itself.

At line 9 the current group is `G₁ = ϕ⁻¹(Aut(X(x)))` and `H = Aut(Y)` for the structure `Y`
that `X(x)` induces on the dominant color class, so `ϕ(G₁) = Aut(X(x)) ≤ Aut(Y) = H` and the
hypothesis holds.  This is what identifies the group of the Chain Rule call on the dominant
window with the `G*` of line 9. -/
theorem preimageSubgroup_eq_self (ϕ : G →* Equiv.Perm Γ) {H : Subgroup (Equiv.Perm Γ)}
    (h : ∀ σ : G, ϕ σ ∈ H) : preimageSubgroup ϕ H = G := by
  refine le_antisymm (preimageSubgroup_le ϕ H) ?_
  intro τ hτ
  exact mem_preimageSubgroup.2 ⟨hτ, h ⟨τ, hτ⟩⟩

end Preimage

/-! ### Lines 4-6: the color classes of `Ω` -/

section Classes

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- §14.1, line 4: the color class `Ω_v` of `Ω` with color vector `v` — the points whose
label `T(u)` meets the color class `Δ_i` of `Γ` in `v i` points, for every `i`. -/
def omegaColorClass (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι) (v : ι → ℕ) : Set Ω :=
  {u : Ω | omegaColor ϕ c u = v}

theorem mem_omegaColorClass {ϕ : G →* Equiv.Perm (Fin m)} {c : Fin m → ι} {v : ι → ℕ}
    {u : Ω} : u ∈ omegaColorClass ϕ c v ↔ omegaColor ϕ c u = v := Iff.rfl

/-- The classes cover `Ω`: every point has a color. -/
theorem omegaColorClass_cover (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → ι) (u : Ω) :
    u ∈ omegaColorClass ϕ c (omegaColor ϕ c u) := rfl

/-- §14.1, line 4: **the coloring of `Ω` is canonical**, so its classes are invariant under
any subgroup of `G` whose `ϕ`-image preserves the coloring of `Γ` — in particular under
`G₁ = ϕ⁻¹(Aut(X(x)))`, whose image is the automorphism group of `X(x)` and so fixes every
color class of `Γ` setwise.

*Proof.*  Eq. (54) (`Babai.theorem_10_5_1_c_eq54`) says `T(u^τ) = T(u)^{ϕ(τ)}`, and `ϕ(τ)`
maps the color class `{c = i}` onto itself, so it maps `T(u) ∩ {c = i}` bijectively onto
`T(u^τ) ∩ {c = i}`. -/
theorem isInvariant_omegaColorClass (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (c : Fin m → ι) (v : ι → ℕ)
    (Gs : Subgroup (Equiv.Perm Ω)) (hle : Gs ≤ G)
    (hstab : ∀ (τ : Equiv.Perm Ω) (h : τ ∈ Gs) (γ : Fin m), c ((ϕ ⟨τ, hle h⟩) γ) = c γ) :
    IsInvariant Gs (omegaColorClass (Ω := Ω) ϕ c v) := by
  have hpres : ∀ (τ : Equiv.Perm Ω) (hτ : τ ∈ Gs) (i : ι),
      (ϕ ⟨τ, hle hτ⟩) '' {γ : Fin m | c γ = i} = {γ : Fin m | c γ = i} := by
    intro τ hτ i
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      show c _ = i
      rw [hstab τ hτ δ]
      exact hδ
    · intro hγ
      refine ⟨(ϕ ⟨τ, hle hτ⟩)⁻¹ γ, ?_, by simp⟩
      show c _ = i
      have h2 := hstab τ hτ ((ϕ ⟨τ, hle hτ⟩)⁻¹ γ)
      have hinv : (ϕ ⟨τ, hle hτ⟩) ((ϕ ⟨τ, hle hτ⟩)⁻¹ γ) = γ := by simp
      rw [hinv] at h2
      rw [← h2]
      exact hγ
  have key : ∀ (τ : Equiv.Perm Ω) (hτ : τ ∈ Gs) (u : Ω),
      omegaColor ϕ c (τ u) = omegaColor ϕ c u := by
    intro τ hτ u
    funext i
    have hT : Tpoint ϕ (τ u) = (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ u) :=
      theorem_10_5_1_c_eq54 ϕ hϕ hk u ⟨τ, hle hτ⟩
    have hinter : Tpoint ϕ (τ u) ∩ {γ : Fin m | c γ = i}
        = (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ u ∩ {γ : Fin m | c γ = i}) := by
      rw [hT, ← hpres τ hτ i, ← Set.image_inter (ϕ ⟨τ, hle hτ⟩).injective, hpres τ hτ i]
    show (Tpoint ϕ (τ u) ∩ {γ : Fin m | c γ = i}).ncard = _
    rw [hinter, Set.ncard_image_of_injective _ (ϕ ⟨τ, hle hτ⟩).injective]
    rfl
  intro τ hτ
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    show omegaColor ϕ c ((τ : Equiv.Perm Ω) w) = v
    rw [key τ hτ w]
    exact hw
  · intro hu
    refine ⟨(τ : Equiv.Perm Ω)⁻¹ u, ?_, by simp⟩
    show omegaColor ϕ c ((τ : Equiv.Perm Ω)⁻¹ u) = v
    have h2 := key τ hτ ((τ : Equiv.Perm Ω)⁻¹ u)
    rw [show (τ : Equiv.Perm Ω) ((τ : Equiv.Perm Ω)⁻¹ u) = u from by simp] at h2
    rw [← h2]
    exact hu

/-- §14.1, line 6: the exceptional class of the color `i`, the one whose color vector is `t`
on `i` and `0` elsewhere, **is the window `Ω(Δ_i)`** of line 6.

*Proof.*  `|T(u)| = t`, so `|T(u) ∩ Δ_i| = t` says `T(u) ⊆ Δ_i`; conversely if `T(u) ⊆ Δ_i`
then `T(u) ∩ Δ_i = T(u)` has `t` points and `T(u) ∩ Δ_j = ∅` for `j ≠ i`. -/
theorem omegaColorClass_eq_omegaOf (ϕ : G →* Equiv.Perm (Fin m)) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (c : Fin m → ι) (i : ι) (v : ι → ℕ) (hvi : v i = t)
    (hvj : ∀ j, j ≠ i → v j = 0) :
    omegaColorClass (Ω := Ω) ϕ c v = omegaOf ϕ {γ : Fin m | c γ = i} := by
  ext u
  rw [mem_omegaColorClass, mem_omegaOf]
  constructor
  · intro h
    have hi := congrFun h i
    rw [hvi] at hi
    have h3 : (Tpoint ϕ u ∩ {γ : Fin m | c γ = i}).ncard = t := hi
    have hsub : Tpoint ϕ u ∩ {γ : Fin m | c γ = i} = Tpoint ϕ u := by
      refine Set.eq_of_subset_of_ncard_le Set.inter_subset_left (le_of_eq ?_)
        (Set.toFinite _)
      rw [h3, ← ht u]
      rfl
    rw [← hsub]
    exact Set.inter_subset_right
  · intro h
    funext j
    show (Tpoint ϕ u ∩ {γ : Fin m | c γ = j}).ncard = v j
    by_cases hj : j = i
    · rw [hj, Set.inter_eq_self_of_subset_left h, hvi, ← ht u]
      rfl
    · have hempty : Tpoint ϕ u ∩ {γ : Fin m | c γ = j} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro γ ⟨hγ1, hγ2⟩
        exact hj ((show c γ = j from hγ2).symm.trans (h hγ1))
      rw [hempty, Set.ncard_empty, hvj j hj]


/-! ### Eq. (72): the sharper bound for the window classes -/

section Sq

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- §7.2 / §14.2, **Eq. (72)**: Lemma 7.2.1 in the form the progress of Procedure Align
needs.  If every color class of `Γ` has at most `α|Γ|` vertices, `t ≥ 2` and `3α² ≤ 2`, then
*every* color class of `(Γ choose t)` — the classes `Babai.lemma_7_2_1a` covers and the
window classes it does not — has at most two thirds of `(Γ choose t)`.

*Proof.*  Sec. 14.2 says the bound `n' ≤ 2n/3` of Eq. (72) holds *"by Lemma 7.2.1"*.  For a
class whose vector is `t` on one color, Lemma 7.2.1 (b) bounds its relative size by
`(|Δ_i|/|Γ|)^t ≤ α^t ≤ α²`, since `t ≥ 2` and `α ≤ 1`; then `3α² ≤ 2` is the claim.  Every
other class has relative size at most `2/3` by Lemma 7.2.1 (a).  The two thresholds the
paper uses satisfy `3α² ≤ 2`: `α = 3/4` in Theorem 9.2.3 (`3·9/16 = 27/16 ≤ 2`) and
`α = 4/5` in Sec. 13 (`3·16/25 = 48/25 ≤ 2`). -/
theorem three_mul_card_tupleClass_le_of_sq [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht2 : 2 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) {α : ℝ} (hα0 : 0 ≤ α) (hα2 : 3 * α ^ 2 ≤ 2)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) (v : ι → ℕ) :
    3 * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
  by_cases hex : ∃ i, v i = t
  · obtain ⟨i, hvi⟩ := hex
    have hm : 0 < Fintype.card Γ := by omega
    have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
    have hα1 : α ≤ 1 := by nlinarith
    have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : t ≤ Fintype.card Γ)
    have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
      have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
      rw [Finset.card_powersetCard] at this
      exact_mod_cast this
    have hb := lemma_7_2_1b c i hm (by omega : t ≤ Fintype.card Γ)
    have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ α := by
      rw [div_le_iff₀ hmR]; exact hα i
    have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
    have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ α ^ t :=
      pow_le_pow_left₀ hratio0 hratio t
    have hαt : α ^ t ≤ α ^ 2 := pow_le_pow_of_le_one hα0 hα1 ht2
    have hkey : ((tupleClass c t v).card : ℝ) ≤ α ^ 2 * ((Fintype.card Γ).choose t : ℝ) := by
      calc ((tupleClass c t v).card : ℝ)
          ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
        _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
              * ((Fintype.card Γ).choose t) := by field_simp
        _ ≤ α ^ 2 * ((Fintype.card Γ).choose t) :=
            mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
    have hR : (3 : ℝ) * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
      rw [card_Phi]
      nlinarith
    exact_mod_cast hR
  · push Not at hex
    exact lemma_7_2_1a c ht hex

/-- §7.2 / §14.2, **Eq. (72) at the threshold `4/5`**, for one color class: Lemma 7.2.1 for
`t ≥ 1`.  If the colors `i` on which the vector `v` is concentrated — those with `v i = t` —
have at most `α|Γ|` vertices each, and `5α ≤ 4`, then the class `Φ_v` has at most four
fifths of `(Γ choose t)`.

*Proof.*  If some `v i = t`, Lemma 7.2.1 (b) bounds the relative size of the class by
`(|Δ_i|/|Γ|)^t ≤ α^t ≤ α`, since `t ≥ 1` and `α ≤ 1`; then `5α ≤ 4` is the claim.  If no
color carries the whole vector, Lemma 7.2.1 (a) gives relative size at most `2/3 ≤ 4/5`.

This is the form the `t = 1` case needs: `α^t ≤ α²` is available only for `t ≥ 2`, while
`α^t ≤ α` holds for every `t ≥ 1`.  It is why the window alternative of
`Babai.MakesProgress` is `4/5` and not `2/3`; see the corrected paper entry on Sec. 15
lines 5–7a and Sec. 14.2 Eqs. (72)–(73). -/
theorem five_mul_card_tupleClass_le_of_le_at [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) {α : ℝ} (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4) (v : ι → ℕ)
    (hα : ∀ i, v i = t → ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) :
    5 * (tupleClass c t v).card ≤ 4 * (Phi Γ t).card := by
  by_cases hex : ∃ i, v i = t
  · obtain ⟨i, hvi⟩ := hex
    have hm : 0 < Fintype.card Γ := by omega
    have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
    have hα1 : α ≤ 1 := by linarith
    have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : t ≤ Fintype.card Γ)
    have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
      have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
      rw [Finset.card_powersetCard] at this
      exact_mod_cast this
    have hb := lemma_7_2_1b c i hm (by omega : t ≤ Fintype.card Γ)
    have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ α := by
      rw [div_le_iff₀ hmR]; exact hα i hvi
    have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
    have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ α ^ t :=
      pow_le_pow_left₀ hratio0 hratio t
    have hαt : α ^ t ≤ α := by
      have h1 : α ^ t ≤ α ^ 1 := pow_le_pow_of_le_one hα0 hα1 ht1
      rwa [pow_one] at h1
    have hkey : ((tupleClass c t v).card : ℝ) ≤ α * ((Fintype.card Γ).choose t : ℝ) := by
      calc ((tupleClass c t v).card : ℝ)
          ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
        _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
              * ((Fintype.card Γ).choose t) := by field_simp
        _ ≤ α * ((Fintype.card Γ).choose t) :=
            mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
    have hR : (5 : ℝ) * (tupleClass c t v).card ≤ 4 * (Phi Γ t).card := by
      rw [card_Phi]
      nlinarith
    exact_mod_cast hR
  · push Not at hex
    have := lemma_7_2_1a c ht hex
    omega

/-- §7.2 / §14.2, **Eq. (72) at the threshold `4/5`**: Lemma 7.2.1 for `t ≥ 1`.  If every
color class of `Γ` has at most `α|Γ|` vertices with `5α ≤ 4`, then every color class of
`(Γ choose t)` has at most four fifths of `(Γ choose t)`. -/
theorem five_mul_card_tupleClass_le_of_le [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) {α : ℝ} (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) (v : ι → ℕ) :
    5 * (tupleClass c t v).card ≤ 4 * (Phi Γ t).card :=
  five_mul_card_tupleClass_le_of_le_at c ht1 ht hα0 hα45 v (fun i _ => hα i)

end Sq

/-! ### The size of a class -/

/-- The color class of `Ω` is the preimage of the color class of `Φ` of Lemma 7.2.1. -/
theorem omegaColorClass_eq_labelPreim (ϕ : G →* Equiv.Perm (Fin m)) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (c : Fin m → ι) (v : ι → ℕ) :
    omegaColorClass (Ω := Ω) ϕ c v = ↑(labelPreim (Ω := Ω) ϕ (tupleClass c t v)) := by
  have hcol : ∀ (u : Ω) (i : ι),
      (Tpoint ϕ u ∩ {γ : Fin m | c γ = i}).ncard = tupleColor c (labelF ϕ u) i := by
    intro u i
    have hcoe : (↑(labelF ϕ u) : Set (Fin m)) = Tpoint ϕ u := coe_labelF ϕ u
    have hset : Tpoint ϕ u ∩ {γ : Fin m | c γ = i}
        = ↑((labelF ϕ u).filter fun γ => c γ = i) := by
      ext γ
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : γ ∈ labelF ϕ u := by rw [← Finset.mem_coe, hcoe]; exact h1
        exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨h1', h2⟩)
      · intro hγ
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        exact ⟨by rw [← hcoe]; exact Finset.mem_coe.2 h1, h2⟩
    rw [hset, Set.ncard_coe_finset]
    rfl
  ext u
  simp only [Finset.mem_coe, labelPreim, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_omegaColorClass, mem_tupleClass]
  constructor
  · intro h
    refine ⟨by rw [card_labelF, ht u], ?_⟩
    funext i
    rw [← hcol u i]
    exact congrFun h i
  · rintro ⟨-, h⟩
    funext i
    show (Tpoint ϕ u ∩ {γ : Fin m | c γ = i}).ncard = v i
    rw [hcol u i]
    exact congrFun h i

/-- `|Ω_v| = |Φ_v| · b`, with `b` the common size of a standard block. -/
theorem ncard_omegaColorClass_eq_mul (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (c : Fin m → ι) (v : ι → ℕ)
    (T₀ : Finset (Fin m)) (hT₀ : T₀.card = t) :
    (omegaColorClass (Ω := Ω) ϕ c v).ncard
      = (tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card := by
  rw [omegaColorClass_eq_labelPreim ϕ ht c v, Set.ncard_coe_finset]
  exact card_labelPreim_eq_mul ϕ hϕ hk hm3 _
    (fun T hT => (mem_tupleClass.1 hT).1) T₀ hT₀

/-- §14.1, lines 5-6, **the progress of the Chain Rule**: a color class of `Ω` whose color
vector is not `t` on a single color has at most `2n/3` points.

This is Lemma 7.2.1 (a) (`Babai.lemma_7_2_1a`) multiplied by the common size of a standard
block, exactly as `Babai.three_mul_ncard_omegaCut_le` does it for the two-coloring of
Cor. 12.0.10.  The classes it does not cover are the windows `Ω(Δ_i)`
(`Babai.omegaColorClass_eq_omegaOf`), one of which is the dominant window of line 6. -/
theorem three_mul_ncard_omegaColorClass_le [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (h2t : 2 * t ≤ m) (c : Fin m → ι) {v : ι → ℕ}
    (hv : ∀ i, v i ≠ t) :
    3 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 2 * Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h721 := lemma_7_2_1a (Γ := Fin m) (ι := ι) c (t := t)
    (by rw [Fintype.card_fin]; exact h2t) hv
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 3 * ((tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (3 * (tupleClass c t v).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (2 * (Phi (Fin m) t).card) * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h721
    _ = 2 * (m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

/-- §14.1, lines 5-6, **the progress of the Chain Rule in the undominated case**: when every
color class of `Γ` has at most `αm` vertices, *every* color class of `Ω` — including the
windows `Ω(Δ_i)`, which `Babai.three_mul_ncard_omegaColorClass_le` does not cover — has at
most `max(2/3, α)·n` points.

This is Corollary 7.2.2 (`Babai.cor_7_2_2`) multiplied by the common size of a standard
block, exactly as `Babai.three_mul_ncard_omegaColorClass_le` is Lemma 7.2.1 (a) multiplied
by it. -/
theorem ncard_omegaColorClass_le_of_alpha [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht2 : 2 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    {α : ℝ} (hα1 : α < 1) (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (m : ℝ)) (v : ι → ℕ) :
    ((omegaColorClass (Ω := Ω) ϕ c v).ncard : ℝ)
      ≤ max (2 / 3) α * (Fintype.card Ω : ℝ) := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h722 := cor_7_2_2 (Γ := Fin m) (ι := ι) c ht2
    (by rw [Fintype.card_fin]; omega) hα1
    (by intro i; rw [Fintype.card_fin]; exact hα i) v
  rw [card_Phi, Fintype.card_fin] at h722
  have hb : (0 : ℝ) ≤ ((labelFiber (Ω := Ω) ϕ T₀).card : ℝ) := Nat.cast_nonneg _
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  push_cast
  calc ((tupleClass c t v).card : ℝ) * ((labelFiber (Ω := Ω) ϕ T₀).card : ℝ)
      ≤ (max (2 / 3) α * ((m.choose t : ℕ) : ℝ)) *
        ((labelFiber (Ω := Ω) ϕ T₀).card : ℝ) := mul_le_mul_of_nonneg_right h722 hb
    _ = max (2 / 3) α *
        (((m.choose t : ℕ) : ℝ) * ((labelFiber (Ω := Ω) ϕ T₀).card : ℝ)) := by ring

/-- §14.2, **Eq. (72)**: with `3α² ≤ 2` the progress `n' ≤ 2n/3` holds for *every* color
class of `Ω`, the windows `Ω(Δ_i)` included.  This is
`Babai.three_mul_card_tupleClass_le_of_sq` multiplied by the common size of a standard
block, exactly as `Babai.three_mul_ncard_omegaColorClass_le` is Lemma 7.2.1 (a) multiplied
by it. -/
theorem three_mul_ncard_omegaColorClass_le_of_sq [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht2 : 2 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    {α : ℝ} (hα0 : 0 ≤ α) (hα2 : 3 * α ^ 2 ≤ 2)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (m : ℝ)) (v : ι → ℕ) :
    3 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 2 * Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h72 := three_mul_card_tupleClass_le_of_sq (Γ := Fin m) (ι := ι) c ht2
    (by rw [Fintype.card_fin]; exact h2t) hα0 hα2
    (by intro i; rw [Fintype.card_fin]; exact hα i) v
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 3 * ((tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (3 * (tupleClass c t v).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (2 * (Phi (Fin m) t).card) * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h72
    _ = 2 * (m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

/-- §14.2, **Eq. (72) at the threshold `4/5`**, lifted to `Ω`, for one color class at a
time: with `5α ≤ 4` and `t ≥ 1` the progress `n' ≤ 4n/5` holds for every color class of
`Ω`, the windows `Ω(Δ_i)` included.  This is
`Babai.five_mul_card_tupleClass_le_of_le_at` multiplied by the common size of a standard
block. -/
theorem five_mul_ncard_omegaColorClass_le_of_le_at [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    {α : ℝ} (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4) (v : ι → ℕ)
    (hα : ∀ i, v i = t → ((colorSet c i).card : ℝ) ≤ α * (m : ℝ)) :
    5 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 4 * Fintype.card Ω := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h72 := five_mul_card_tupleClass_le_of_le_at (Γ := Fin m) (ι := ι) c ht1
    (by rw [Fintype.card_fin]; exact h2t) hα0 hα45 v
    (by intro i hi; rw [Fintype.card_fin]; exact hα i hi)
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 5 * ((tupleClass c t v).card * (labelFiber (Ω := Ω) ϕ T₀).card)
      = (5 * (tupleClass c t v).card) * (labelFiber (Ω := Ω) ϕ T₀).card := by ring
    _ ≤ (4 * (Phi (Fin m) t).card) * (labelFiber (Ω := Ω) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h72
    _ = 4 * (m.choose t * (labelFiber (Ω := Ω) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

/-- §14.2, **Eq. (72) at the threshold `4/5`**, lifted to `Ω`: with `5α ≤ 4` and `t ≥ 1`
every color class of `Ω` has at most `4n/5` points. -/
theorem five_mul_ncard_omegaColorClass_le_of_le [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : Ω, tPoint ϕ u = t) (ht1 : 1 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    {α : ℝ} (hα0 : 0 ≤ α) (hα45 : 5 * α ≤ 4)
    (hα : ∀ i, ((colorSet c i).card : ℝ) ≤ α * (m : ℝ)) (v : ι → ℕ) :
    5 * (omegaColorClass (Ω := Ω) ϕ c v).ncard ≤ 4 * Fintype.card Ω :=
  five_mul_ncard_omegaColorClass_le_of_le_at hG ϕ hϕ hk hm3 ht ht1 h2t c hα0 hα45 v
    (fun i _ => hα i)

end Classes

end Babai
