/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 11.1 (Luks's framework).
-/
import Workspace.Luks.Defs

/-!
# §11.1 Luks's framework

"Once again we stress that everything in this section was a review of Luks's work."

The paper's right cosets `Kσ` are Lean's left translates `σ • K`; see the header of
`Workspace/Luks/Defs.lean` and `Babai.mem_perm_smul_set`.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω A : Type*}

/-! ### Basic properties of the string action -/

/-- §11.1, after Eq. (55): "(The purpose of the inversion is to ensure that
`x^{στ} = (x^σ)^τ` for `σ, τ ∈ S(Ω)`.)"

Under the translation (the paper's product `στ` is Lean's `τ * σ`), the paper's identity
`x^{στ} = (x^σ)^τ` reads `strAct x (τ * σ) = strAct (strAct x σ) τ`. -/
theorem strAct_mul (x : Ω → A) (σ τ : Equiv.Perm Ω) :
    strAct x (τ * σ) = strAct (strAct x σ) τ := by
  funext u
  simp [strAct, mul_inv_rev]

@[simp] theorem strAct_one (x : Ω → A) : strAct x (1 : Equiv.Perm Ω) = x := rfl

/-- `x^τ = y` iff `x(u) = y(u^τ)` for all `u`: the second description in Eq. (56). -/
theorem strAct_eq_iff {x y : Ω → A} {τ : Equiv.Perm Ω} :
    strAct x τ = y ↔ ∀ u, x u = y (τ u) := by
  constructor
  · intro h u
    rw [← h, strAct_apply]
  · intro h
    funext v
    simpa using h (τ⁻¹ v)

/-- §11.1, Eq. (56): `Iso_K(x,y) = {τ ∈ K | x^τ = y} = {τ ∈ K | (∀u ∈ Ω)(x(u) = y(u^τ))}`. -/
theorem strIso_eq_sep (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    strIso K x y = {τ ∈ K | ∀ u, x u = y (τ u)} := by
  ext τ
  simp [strIso, strAct_eq_iff]

@[simp] theorem mem_wIso {Δ : Set Ω} {K : Set (Equiv.Perm Ω)} {x y : Ω → A}
    {τ : Equiv.Perm Ω} : τ ∈ wIso Δ K x y ↔ τ ∈ K ∧ ∀ u ∈ Δ, x u = y (τ u) := Iff.rfl

@[simp] theorem mem_wAut {Δ : Set Ω} {K : Set (Equiv.Perm Ω)} {x : Ω → A}
    {τ : Equiv.Perm Ω} : τ ∈ wAut Δ K x ↔ τ ∈ K ∧ ∀ u ∈ Δ, x u = x (τ u) := Iff.rfl

/-- §11.1.  The window isomorphisms for the full window `Δ = Ω` are the isomorphisms:
`Iso^Ω_K(x,y) = Iso_K(x,y)`. -/
theorem wIso_univ (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso Set.univ K x y = strIso K x y := by
  rw [strIso_eq_sep]
  ext τ
  simp

theorem wIso_subset (Δ : Set Ω) (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso Δ K x y ⊆ K := fun _ h => h.1

/-! ### The shift identity, Eqs. (57) and (59) -/

/-- §11.1, **Eq. (59)** (shift identity for window isomorphism).

> For `K ⊆ S(Ω)` and `σ ∈ S(Ω)` we again have the shift identity:
> `Iso^Δ_{Kσ}(x,y) = Iso^Δ_K(x, y^{σ⁻¹})σ`.  (59)

The paper's right coset `Kσ` is `σ • K` and the paper's `Sσ` on the right-hand side is
`σ • S`; see `Babai.mem_perm_smul_set`. -/
theorem wIso_smul (Δ : Set Ω) (K : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) (x y : Ω → A) :
    wIso Δ (σ • K) x y = σ • wIso Δ K x (strAct y σ⁻¹) := by
  ext τ
  rw [mem_perm_smul_set, mem_wIso, mem_wIso, mem_perm_smul_set]
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨hK, fun u hu => by simpa using h u hu⟩
  · rintro ⟨hK, h⟩
    exact ⟨hK, fun u hu => by simpa using h u hu⟩

/-- §11.1, **Eq. (57)** (shift identity).

> For `K ⊆ S(Ω)` and `σ ∈ S(Ω)` we note the shift identity
> `Iso_{Kσ}(x,y) = Iso_K(x, y^{σ⁻¹})σ`.  (57) -/
theorem strIso_smul (K : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) (x y : Ω → A) :
    strIso (σ • K) x y = σ • strIso K x (strAct y σ⁻¹) := by
  rw [← wIso_univ, ← wIso_univ, wIso_smul]

/-- §11.1, **Remark 11.1.4** (Alignment).

> Applying Eq. (57) to a subgroup `K = G ≤ S(Ω)`, we see that the isomorphism problem for
> the pair `(x,y)` of strings with respect to a coset `Gσ` is the same as the isomorphism
> problem for `(x, y^{σ⁻¹})` with respect to the group `G`.  In view of Eq. (59), the same
> holds for window-isomorphism.  The shift `y ← y^{σ⁻¹}` is an important **alignment
> step** that will accompany every reduction of the ambient group `G`.

The precise content is that the two sets differ by the (bijective) translation by `σ`. -/
theorem Remark_11_1_4_alignment (G : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω)
    (x y : Ω → A) :
    strIso (σ • (G : Set (Equiv.Perm Ω))) x y =
      σ • strIso (G : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) :=
  strIso_smul _ _ _ _

/-- §11.1, **Remark 11.1.4** (Alignment), window version. -/
theorem Remark_11_1_4_alignment_window (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω)
    (σ : Equiv.Perm Ω) (x y : Ω → A) :
    wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y =
      σ • wIso Δ (G : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) :=
  wIso_smul _ _ _ _ _

/-! ### Remark 11.1.5 -/

/-- §11.1, **Remark 11.1.5 (i)**.

> When applying the concept of window-isomorphism, we shall always assume that the window
> is invariant under the group `G ≤ S(Ω)`, and `K` is a coset, `K = Gσ` for some
> `σ ∈ S(Ω)`.  Under these circumstances we make the following observations.
> (i) `Aut^Δ_G(x)` is a subgroup of `G`.

The subgroup is `Babai.wAutSubgroup`; this states that it is contained in `G`. -/
theorem wAutSubgroup_le (G : Subgroup (Equiv.Perm Ω)) (Δ : Set Ω) (h : IsInvariant G Δ)
    (x : Ω → A) : wAutSubgroup G Δ h x ≤ G :=
  fun _ hτ => hτ.1

/-- §11.1, **Remark 11.1.5 (ii)**, Eq. (60).

> (ii) `Iso^Δ_{Gσ}(x,y)` is either empty or a right coset of `Aut^Δ_G(x)`, namely,
> `Iso^Δ_{Gσ}(x,y) = Aut^Δ_G(x)σ'` for any `σ' ∈ Iso^Δ_{Gσ}(x,y)`.  (60)

The paper's right coset `Aut^Δ_G(x)σ'` is `σ' • Aut^Δ_G(x)` in Lean.  The window `Δ` is
`G`-invariant, as the standing assumption of Remark 11.1.5 requires. -/
theorem wIso_eq_smul_wAut {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} (h : IsInvariant G Δ)
    {x y : Ω → A} (σ : Equiv.Perm Ω) {σ' : Equiv.Perm Ω}
    (hσ' : σ' ∈ wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y) :
    wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y = σ' • wAut Δ (G : Set (Equiv.Perm Ω)) x := by
  obtain ⟨hσ'K, hσ'agree⟩ := hσ'
  rw [mem_perm_smul_set] at hσ'K
  ext τ
  rw [mem_wIso, mem_perm_smul_set, mem_perm_smul_set, mem_wAut]
  constructor
  · rintro ⟨hτK, hτ⟩
    have hmem : σ'⁻¹ * τ ∈ G := by
      have : σ'⁻¹ * τ = (σ⁻¹ * σ')⁻¹ * (σ⁻¹ * τ) := by group
      rw [this]
      exact mul_mem (inv_mem hσ'K) hτK
    refine ⟨hmem, fun u hu => ?_⟩
    have hv : (σ'⁻¹ * τ) u ∈ Δ := h.mem_of_mem hmem hu
    have h1 : x ((σ'⁻¹ * τ) u) = y (σ' ((σ'⁻¹ * τ) u)) := hσ'agree _ hv
    have h2 : σ' ((σ'⁻¹ * τ) u) = τ u := by
      simp [Equiv.Perm.mul_apply]
    rw [h2] at h1
    rw [h1, hτ u hu]
  · rintro ⟨ha, hτ⟩
    have hmem : σ⁻¹ * τ ∈ G := by
      have : σ⁻¹ * τ = (σ⁻¹ * σ') * (σ'⁻¹ * τ) := by group
      rw [this]
      exact mul_mem hσ'K ha
    refine ⟨hmem, fun u hu => ?_⟩
    have hv : (σ'⁻¹ * τ) u ∈ Δ := h.mem_of_mem ha hu
    have h1 : x ((σ'⁻¹ * τ) u) = y (σ' ((σ'⁻¹ * τ) u)) := hσ'agree _ hv
    have h2 : σ' ((σ'⁻¹ * τ) u) = τ u := by
      simp [Equiv.Perm.mul_apply]
    rw [h2] at h1
    rw [hτ u hu, h1]

/-- §11.1, Remark 11.1.5 (ii): `Iso^Δ_{Gσ}(x,y)` is *either empty or* a right coset of
`Aut^Δ_G(x)`. -/
theorem wIso_empty_or_smul_wAut {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}
    (h : IsInvariant G Δ) (x y : Ω → A) (σ : Equiv.Perm Ω) :
    wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y = ∅ ∨
      ∃ σ' : Equiv.Perm Ω, wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y =
        σ' • (wAutSubgroup G Δ h x : Set (Equiv.Perm Ω)) := by
  rcases Set.eq_empty_or_nonempty (wIso Δ (σ • (G : Set (Equiv.Perm Ω))) x y) with he | ⟨σ', hσ'⟩
  · exact Or.inl he
  · exact Or.inr ⟨σ', wIso_eq_smul_wAut h σ hσ'⟩

/-! ### Eq. (61) and the windows -/

/-- §11.1, **Eq. (61)**.

> The following straightforward identity plays a central role in Luks's method.  Let
> `K, L ⊆ S(Ω)` and `Δ ⊆ Ω`.  Then
> `Iso^Δ_{K ∪ L}(x,y) = Iso^Δ_K(x,y) ∪ Iso^Δ_L(x,y)`.  (61) -/
theorem wIso_union (Δ : Set Ω) (K L : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso Δ (K ∪ L) x y = wIso Δ K x y ∪ wIso Δ L x y := by
  ext τ
  simp only [mem_wIso, Set.mem_union]
  tauto

/-- Eq. (61) for an arbitrary union of sets of permutations. -/
theorem wIso_iUnion {ι : Sort*} (Δ : Set Ω) (K : ι → Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso Δ (⋃ i, K i) x y = ⋃ i, wIso Δ (K i) x y := by
  ext τ
  simp only [mem_wIso, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨⟨i, hi⟩, h⟩

/-- The dual identity for *windows*: enlarging the window intersects the answers.  This is
the identity behind the Chain Rule (Prop. 11.1.7) and behind the "sequential processing of
windows" of Theorem 11.1.9. -/
theorem wIso_window_union (Δ₁ Δ₂ : Set Ω) (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso (Δ₁ ∪ Δ₂) K x y = wIso Δ₁ K x y ∩ wIso Δ₂ K x y := by
  ext τ
  simp only [mem_wIso, Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨⟨hK, fun u hu => h u (Or.inl hu)⟩, ⟨hK, fun u hu => h u (Or.inr hu)⟩⟩
  · rintro ⟨⟨hK, h₁⟩, ⟨-, h₂⟩⟩
    exact ⟨hK, fun u hu => hu.elim (h₁ u) (h₂ u)⟩

/-- The window version of Eq. (61) for a family of windows: processing the blocks of a
partition one after the other. -/
theorem wIso_window_sUnion (ℬ : Set (Set Ω)) (K : Set (Equiv.Perm Ω)) (x y : Ω → A) :
    wIso (⋃₀ ℬ) K x y = K ∩ ⋂ B ∈ ℬ, wIso B K x y := by
  ext τ
  simp only [mem_wIso, Set.mem_inter_iff, Set.mem_iInter, Set.mem_sUnion]
  constructor
  · rintro ⟨hK, h⟩
    exact ⟨hK, fun B hB => ⟨hK, fun u hu => h u ⟨B, hB, hu⟩⟩⟩
  · rintro ⟨hK, h⟩
    exact ⟨hK, by rintro u ⟨B, hB, hu⟩; exact (h B hB).2 u hu⟩

/-! ### Proposition 11.1.6 (Descent) -/

/-- A canonical system of representatives for the cosets of `H` in `G`: the paper's
`σ` ranging "over a set of right coset representatives of `H` in `G`".  There is one for
each element of `G ⧸ H.subgroupOf G`, a set of size `|G : H|`. -/
noncomputable def cosetRep {H G : Subgroup (Equiv.Perm Ω)} (q : G ⧸ H.subgroupOf G) :
    Equiv.Perm Ω := ((Quotient.out q : G) : Equiv.Perm Ω)

theorem cosetRep_mem {H G : Subgroup (Equiv.Perm Ω)} (q : G ⧸ H.subgroupOf G) :
    (cosetRep q : Equiv.Perm Ω) ∈ G := (Quotient.out q : G).2

/-- The number of coset representatives is `|G : H|`. -/
theorem card_quotient_subgroupOf (H G : Subgroup (Equiv.Perm Ω)) :
    Nat.card (G ⧸ H.subgroupOf G) = H.relIndex G :=
  (Subgroup.index_eq_card _).symm

/-- "We can write `G = ⋃_σ Hσ` where `σ` ranges over a set of right coset representatives
of `H` in `G`" (proof of Prop. 11.1.6), with the canonical representatives. -/
theorem coe_eq_iUnion_cosetRep {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G) :
    (G : Set (Equiv.Perm Ω)) =
      ⋃ q : G ⧸ H.subgroupOf G, cosetRep q • (H : Set (Equiv.Perm Ω)) := by
  ext g
  constructor
  · intro hg
    refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨g, hg⟩ : G) : G ⧸ H.subgroupOf G), ?_⟩
    rw [mem_perm_smul_set]
    have h : (QuotientGroup.mk (Quotient.out
        (QuotientGroup.mk (⟨g, hg⟩ : G) : G ⧸ H.subgroupOf G)) : G ⧸ H.subgroupOf G) =
        QuotientGroup.mk (⟨g, hg⟩ : G) := Quotient.out_eq _
    have h2 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro hg
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hg
    rw [mem_perm_smul_set] at hq
    have : g = cosetRep q * ((cosetRep q)⁻¹ * g) := by group
    rw [this]
    exact mul_mem (cosetRep_mem q) (hHG hq)

/-- §11.1, **Proposition 11.1.6** (Descent).

> Let `H ≤ G`.  Then finding `Iso^Δ_G(x,y)` reduces to `|G : H|` instances of finding
> `Iso^Δ_H(x, y^σ)` for various `σ ∈ G`.
>
> *Proof.* We can write `G = ⋃_σ Hσ` where `σ` ranges over a set of right coset
> representatives of `H` in `G`.  Applying Eq. (61) to this decomposition, we obtain
> `Iso^Δ_G(x,y) = ⋃_σ Iso^Δ_{Hσ}(x,y) = ⋃_σ Iso^Δ_H(x, y^{σ⁻¹})σ`  (62)
> where we also employed the shift identity, Eq. (59).

This is Eq. (62) for an arbitrary decomposition `G = ⋃_{σ ∈ R} Hσ` into right cosets.
The number of instances is `|R|`; for the canonical representatives it is exactly
`|G : H|` (`Babai.Proposition_11_1_6_descent`). -/
theorem descent_of_cover {H G : Subgroup (Equiv.Perm Ω)} {R : Set (Equiv.Perm Ω)}
    (hcover : (G : Set (Equiv.Perm Ω)) = ⋃ σ ∈ R, σ • (H : Set (Equiv.Perm Ω)))
    (Δ : Set Ω) (x y : Ω → A) :
    wIso Δ (G : Set (Equiv.Perm Ω)) x y =
      ⋃ σ ∈ R, σ • wIso Δ (H : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) := by
  rw [hcover, wIso_iUnion]
  refine Set.iUnion_congr fun σ => ?_
  rw [wIso_iUnion]
  exact Set.iUnion_congr fun _ => wIso_smul _ _ _ _ _

/-- §11.1, **Proposition 11.1.6** (Descent), with the canonical coset representatives:
the union has exactly `|G : H|` terms (`Babai.card_quotient_subgroupOf`), one for each
right coset of `H` in `G`, and the `σ`-th term is the set of `H`-window-isomorphisms of
`x` and the shifted string `y^{σ⁻¹}`, translated by `σ`. -/
theorem Proposition_11_1_6_descent {H G : Subgroup (Equiv.Perm Ω)} (hHG : H ≤ G)
    (Δ : Set Ω) (x y : Ω → A) :
    wIso Δ (G : Set (Equiv.Perm Ω)) x y =
      ⋃ q : G ⧸ H.subgroupOf G,
        cosetRep q • wIso Δ (H : Set (Equiv.Perm Ω)) x (strAct y (cosetRep q)⁻¹) := by
  rw [coe_eq_iUnion_cosetRep hHG, wIso_iUnion]
  exact Set.iUnion_congr fun q => wIso_smul _ _ _ _ _

/-! ### Proposition 11.1.7 (Chain Rule) -/

/-- §11.1, **Proposition 11.1.7** (Chain Rule).

> Let `Δ₁` and `Δ₂` be `G`-invariant subsets of `Ω` and let `Iso^{Δ₁}_G(x,y) = G₁σ`, where
> `σ ∈ G` and `G₁ ≤ G`.  Then
> `Iso^{Δ₁ ∪ Δ₂}_G(x,y) = Iso^{Δ₂}_{G₁σ}(x,y) = Iso^{Δ₂}_{G₁}(x, y^{σ⁻¹})σ`.  (63)
>
> *Proof.* The first equation is immediate from the definitions.  The second equation uses
> the shift identity, Eq. (59).

The paper's coset `G₁σ` is `σ • G₁` in Lean. -/
theorem Proposition_11_1_7_chainRule {G G₁ : Subgroup (Equiv.Perm Ω)} {Δ₁ Δ₂ : Set Ω}
    (h₁ : IsInvariant G Δ₁) (h₂ : IsInvariant G Δ₂) (hG₁ : G₁ ≤ G) {σ : Equiv.Perm Ω}
    (hσ : σ ∈ G) {x y : Ω → A}
    (hIso : wIso Δ₁ (G : Set (Equiv.Perm Ω)) x y = σ • (G₁ : Set (Equiv.Perm Ω))) :
    wIso (Δ₁ ∪ Δ₂) (G : Set (Equiv.Perm Ω)) x y =
        wIso Δ₂ (σ • (G₁ : Set (Equiv.Perm Ω))) x y ∧
      wIso Δ₂ (σ • (G₁ : Set (Equiv.Perm Ω))) x y =
        σ • wIso Δ₂ (G₁ : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) := by
  refine ⟨?_, wIso_smul _ _ _ _ _⟩
  rw [wIso_window_union, ← hIso]
  ext τ
  simp only [Set.mem_inter_iff, mem_wIso]
  constructor
  · rintro ⟨⟨hτG, h1⟩, ⟨-, h2⟩⟩
    exact ⟨⟨hτG, h1⟩, h2⟩
  · rintro ⟨hτ1, h2⟩
    exact ⟨hτ1, ⟨hτ1.1, h2⟩⟩

/-! ### Fact 11.1.8 and strong descent -/

/-- §11.1, **Fact 11.1.8**.

> If `G` is a transitive group and `N ◁ G` then the orbits of `N` have equal length.

(The paper gives no proof; it is elementary.  `CITED.md`, entry C18.) -/
theorem Fact_11_1_8 {G N : Subgroup (Equiv.Perm Ω)} (hG : IsTransitive G)
    (hN : IsNormalIn N G) (u v : Ω) : (orbit N u).ncard = (orbit N v).ncard := by
  haveI : Nonempty Ω := ⟨u⟩
  have horb : orbit G u = Set.univ := (isTransitive_iff_orbit_eq_univ G).1 hG u
  have hv : v ∈ orbit G u := horb ▸ Set.mem_univ v
  obtain ⟨g, hgv⟩ := (mem_orbit_iff).1 hv
  rw [Subgroup.smul_def] at hgv
  have himg : orbit N v = (fun w => (g : Equiv.Perm Ω) • w) '' orbit N u := by
    ext w
    simp only [Set.mem_image, mem_orbit_iff, Subgroup.smul_def]
    constructor
    · rintro ⟨n, rfl⟩
      have hconj : (g : Equiv.Perm Ω)⁻¹ * (n : Equiv.Perm Ω) * (g : Equiv.Perm Ω) ∈ N := by
        have := hN.conj_mem ((g : Equiv.Perm Ω)⁻¹) (inv_mem g.2) (n : Equiv.Perm Ω) n.2
        simpa using this
      refine ⟨((g : Equiv.Perm Ω)⁻¹ * (n : Equiv.Perm Ω) * (g : Equiv.Perm Ω)) • u,
        ⟨⟨_, hconj⟩, rfl⟩, ?_⟩
      rw [← hgv, smul_smul, smul_smul]
      congr 1
      group
    · rintro ⟨w', ⟨n, rfl⟩, rfl⟩
      refine ⟨⟨(g : Equiv.Perm Ω) * (n : Equiv.Perm Ω) * (g : Equiv.Perm Ω)⁻¹,
        hN.conj_mem _ g.2 _ n.2⟩, ?_⟩
      rw [← hgv, smul_smul, smul_smul]
      congr 1
      group
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective (g : Equiv.Perm Ω))]

/-- §11.1, after Fact 11.1.8.

> It follows that if `N` is intransitive then each orbit of `N` has length `n/m` for some
> `m ≥ 2`, so we obtain a recurrence of the form `T(n) ≤ |G : N| m T(n/m)`  (64)
> for some `m ≥ 2`.

The mathematical content is the displayed sentence: there is an `m ≥ 2` (the number of
orbits of `N`) such that every orbit of `N` has length `n/m`, i.e. `|orbit| * m = n`.
The cost recurrence (64) itself is not modelled; see the corrected paper. -/
theorem orbit_ncard_mul_eq_card [Fintype Ω] {G N : Subgroup (Equiv.Perm Ω)}
    (hG : IsTransitive G) (hN : IsNormalIn N G) (hNint : ¬ IsTransitive N) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ u : Ω, (orbit N u).ncard * m = Fintype.card Ω := by
  obtain ⟨u₀, -⟩ := id hG
  haveI : Nonempty Ω := ⟨u₀⟩
  classical
  haveI : Nonempty (orbitRel.Quotient N Ω) := ⟨Quotient.mk'' u₀⟩
  refine ⟨Nat.card (orbitRel.Quotient N Ω), ?_, ?_⟩
  · -- `m ≥ 1` since `Ω` is nonempty, and `m = 1` would make `N` transitive
    rcases Nat.lt_or_ge (Nat.card (orbitRel.Quotient N Ω)) 2 with hlt | hge
    · exfalso
      have hpos : 0 < Nat.card (orbitRel.Quotient N Ω) := Nat.card_pos
      have hone : Nat.card (orbitRel.Quotient N Ω) = 1 := by omega
      refine hNint ⟨u₀, ?_⟩
      have hsub : Subsingleton (orbitRel.Quotient N Ω) :=
        (Nat.card_eq_one_iff_unique.1 hone).1
      ext w
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      have h1 : (Quotient.mk'' w : orbitRel.Quotient N Ω) = Quotient.mk'' u₀ :=
        Subsingleton.elim _ _
      exact orbitRel_apply.1 (Quotient.eq''.1 h1)
    · exact hge
  · intro u
    have hcard : Nat.card Ω = ∑ ω : orbitRel.Quotient N Ω, Nat.card (orbit N ω.out) := by
      rw [Nat.card_congr (selfEquivSigmaOrbits N Ω), Nat.card_sigma]
    have hconst : ∀ ω : orbitRel.Quotient N Ω,
        Nat.card (orbit N ω.out) = (orbit N u).ncard := fun ω => Fact_11_1_8 hG hN _ _
    rw [Finset.sum_congr rfl fun ω _ => hconst ω, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] at hcard
    rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card, mul_comm]

/-! ### Theorem 11.1.9 (Imprimitive Luks reduction) -/

section ImprimitiveLuks

variable {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω} {ℬ : Set (Set Ω)}

/-- The kernel `N = ker(ψ)` of the action `ψ : G → Ḡ` on the blocks, as a subgroup of
`S(Ω)`. -/
def blockKernel (G : Subgroup (Equiv.Perm Ω)) (ℬ : Set (Set Ω))
    (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) : Subgroup (Equiv.Perm Ω) :=
  (blockHom G ℬ hperm).ker.map G.subtype

theorem blockKernel_le (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) :
    blockKernel G ℬ hperm ≤ G :=
  Subgroup.map_subtype_le _

/-- Every block is invariant under `N = ker ψ`: this is what makes each `Bᵢ` a legitimate
window for the group `N` in the Chain Rule. -/
theorem isInvariant_blockKernel {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ}
    {B : Set Ω} (hB : B ∈ ℬ) : IsInvariant (blockKernel G ℬ hperm) B := by
  rintro σ hσ
  obtain ⟨⟨τ, hτG⟩, hτker, rfl⟩ := hσ
  exact mem_ker_blockHom.1 hτker B hB

/-- The identity of Theorem 11.1.9, from the two clauses of the `G`-invariant partition
that it uses: `G` permutes the blocks, and the blocks cover the window.  Stated
separately so that the window `Δ` may be rewritten to `⋃₀ ℬ` without the proof term
`hperm` depending on `Δ`; `Babai.Theorem_11_1_9` is the paper's statement. -/
theorem Theorem_11_1_9_of_cover (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ)
    (hcover : ⋃₀ ℬ = Δ) (x y : Ω → A) :
    wIso Δ (G : Set (Equiv.Perm Ω)) x y =
      ⋃ q : G ⧸ (blockKernel G ℬ hperm).subgroupOf G,
        cosetRep q • (((blockKernel G ℬ hperm) : Set (Equiv.Perm Ω)) ∩
          ⋂ B ∈ ℬ, wIso B ((blockKernel G ℬ hperm) : Set (Equiv.Perm Ω)) x
            (strAct y (cosetRep q)⁻¹)) := by
  rw [Proposition_11_1_6_descent (blockKernel_le hperm) Δ x y]
  refine Set.iUnion_congr fun q => ?_
  rw [← hcover, wIso_window_sUnion]

/-- §11.1, **Theorem 11.1.9** (Imprimitive Luks reduction).

> Let `G ≤ S(Ω)` and let `Δ ⊆ Ω` be a `G`-invariant subset.  Let `{B₁,…,B_m}` be a
> `G`-invariant partition of `Δ`.  Let `ψ : G → Ḡ ≤ S_m` be the induced action of `G` on
> the set of blocks and let `N = ker(ψ)`.  Then finding `Iso^Δ_G(x,y)` reduces to
> `m|Ḡ| = m|G/N|` instances of finding `Iso^{B_i}_{M_i}(x, y^{σ_i})` for the blocks `B_i`
> and certain subgroups `M_i ≤ N` and `σ_i ∈ G`.
>
> *Proof.*  First descend to `N = ker ψ`.  Then consider each `B_i` to be the window in
> succession, reducing the group at each round, following the Chain Rule.  In the end,
> combine all the results into a single coset.

The identity below is the two steps of the proof: descent to `N` (Prop. 11.1.6), which
produces `|G : N| = |Ḡ|` terms indexed by `G ⧸ N` (`Babai.Theorem_11_1_9_card`), and then
the decomposition of the window `Δ = ⋃ᵢ Bᵢ` into the `m` blocks (`Babai.wIso_window_sUnion`),
which produces `m` window-isomorphism problems on the blocks inside each term — `m|Ḡ|`
subproblems in total.  The subgroups `Mᵢ ≤ N` and the shifts `σᵢ` of the paper appear when
the intersection over the blocks is computed one block at a time; that is
`Babai.imprimitive_luks_step` below.

The paper's two standing hypotheses are carried: `Δ` is a `G`-invariant subset (`hΔ`) and
`{B₁,…,B_m}` is a `G`-invariant partition of `Δ` (`hℬ`, `Babai.IsInvariantPartitionOn`).
Of the clauses of `hℬ` the identity itself uses only "`G` permutes the blocks" and
"the union of the blocks is `Δ`"; the other clauses and `hΔ` are what make the blocks
legitimate windows in the Chain Rule step (`Babai.imprimitive_luks_step`). -/
theorem Theorem_11_1_9 (hΔ : IsInvariant G Δ) (hℬ : IsInvariantPartitionOn G Δ ℬ)
    (x y : Ω → A) :
    wIso Δ (G : Set (Equiv.Perm Ω)) x y =
      ⋃ q : G ⧸ (blockKernel G ℬ hℬ.permutes).subgroupOf G,
        cosetRep q • (((blockKernel G ℬ hℬ.permutes) : Set (Equiv.Perm Ω)) ∩
          ⋂ B ∈ ℬ, wIso B ((blockKernel G ℬ hℬ.permutes) : Set (Equiv.Perm Ω)) x
            (strAct y (cosetRep q)⁻¹)) :=
  Theorem_11_1_9_of_cover hℬ.permutes hℬ.covers x y

/-- §11.1, Theorem 11.1.9: the number of instances is `m|Ḡ| = m|G/N|`.  This is the
equality `|G : N| = |Ḡ|`; the factor `m = |ℬ|` is the number of blocks, i.e. the number of
terms of the intersection in `Babai.Theorem_11_1_9`. -/
theorem Theorem_11_1_9_card (hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ) :
    Nat.card (G ⧸ (blockKernel G ℬ hperm).subgroupOf G) =
      Nat.card (onBlocks G ℬ hperm) := by
  have hsub : (blockKernel G ℬ hperm).subgroupOf G = (blockHom G ℬ hperm).ker := by
    ext ⟨g, hg⟩
    simp only [blockKernel, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype,
      Subtype.exists, exists_prop, exists_eq_right, MonoidHom.mem_ker]
    constructor
    · rintro ⟨h', hk, hker, rfl⟩; exact hker
    · intro h; exact ⟨g, hg, h, rfl⟩
  rw [hsub]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (blockHom G ℬ hperm)).toEquiv

/-- §11.1, Theorem 11.1.9, the step of the "sequential processing of windows": with the
current group `M ≤ N` and the current shift `σ`, processing the block `B` is the single
window-isomorphism problem `Iso^B_M(x, y^{σ⁻¹})` of the theorem's statement, and its answer
is again empty or a coset of a subgroup of `M` — so the recursion stays in the same
shape. -/
theorem imprimitive_luks_step {hperm : ∀ σ ∈ G, ∀ B ∈ ℬ, (σ : Equiv.Perm Ω) '' B ∈ ℬ}
    {M : Subgroup (Equiv.Perm Ω)} (hM : M ≤ blockKernel G ℬ hperm) {B : Set Ω} (hB : B ∈ ℬ)
    (σ : Equiv.Perm Ω) (x y : Ω → A) :
    wIso B (σ • (M : Set (Equiv.Perm Ω))) x y =
        σ • wIso B (M : Set (Equiv.Perm Ω)) x (strAct y σ⁻¹) ∧
      (wIso B (σ • (M : Set (Equiv.Perm Ω))) x y = ∅ ∨
        ∃ σ' : Equiv.Perm Ω, wIso B (σ • (M : Set (Equiv.Perm Ω))) x y =
          σ' • (wAutSubgroup M B (fun τ hτ => isInvariant_blockKernel hB τ (hM hτ)) x :
            Set (Equiv.Perm Ω))) :=
  ⟨wIso_smul _ _ _ _ _,
    wIso_empty_or_smul_wAut (fun τ hτ => isInvariant_blockKernel hB τ (hM hτ)) x y σ⟩

end ImprimitiveLuks

/-! ### Observation 11.1.11 (Reducing to the window) -/

section ReducingToWindow

variable {G : Subgroup (Equiv.Perm Ω)} {Δ : Set Ω}

theorem isInvariant_univ (H : Subgroup (Equiv.Perm Ω)) : IsInvariant H Set.univ := by
  intro σ _
  simpa using (σ : Equiv.Perm Ω).surjective.range_eq

/-- `Aut_H(x)` as a subgroup, for a permutation group `H`: the case `Δ = Ω` of
`Babai.wAutSubgroup`. -/
def strAutSubgroup (H : Subgroup (Equiv.Perm Ω)) (x : Ω → A) : Subgroup (Equiv.Perm Ω) :=
  wAutSubgroup H Set.univ (isInvariant_univ H) x

/-- §11.1, **Observation 11.1.11** (Reducing to the window), the membership criterion.

> Let `G ≤ S(Ω)` and let `Δ` be a `G`-invariant subset of `Ω`.  Let `x^Δ` and `y^Δ` be the
> restriction of `x` and `y` to `Δ`, respectively.  […]  While we concentrate on the action
> of the elements of `G` on the window, we maintain their "tails" – their action on the rest
> of the permutation domain.

An element of `G` is a window isomorphism on `Δ` precisely when its restriction to `Δ` is
an isomorphism of the restricted strings; the "tail" is irrelevant. -/
theorem mem_wIso_iff_restrict (h : IsInvariant G Δ) (x y : Ω → A) {σ : Equiv.Perm Ω}
    (hσ : σ ∈ G) :
    σ ∈ wIso Δ (G : Set (Equiv.Perm Ω)) x y ↔
      restrictHom G Δ h ⟨σ, hσ⟩ ∈
        strIso ((restrictTo G Δ h : Subgroup (Equiv.Perm Δ)) : Set (Equiv.Perm Δ))
          (fun u : Δ => x (u : Ω)) (fun u : Δ => y (u : Ω)) := by
  rw [strIso_eq_sep]
  simp only [mem_wIso, Set.mem_sep_iff]
  constructor
  · rintro ⟨-, hagree⟩
    exact ⟨⟨⟨σ, hσ⟩, rfl⟩, fun u => hagree (u : Ω) u.2⟩
  · rintro ⟨-, hagree⟩
    exact ⟨hσ, fun u hu => hagree ⟨u, hu⟩⟩

/-- §11.1, **Observation 11.1.11**: "The set `Iso_{G^Δ}(x^Δ, y^Δ)` is empty if and only if
`Iso^Δ_G(x,y)` is empty." -/
theorem strIso_restrict_eq_empty_iff (h : IsInvariant G Δ) (x y : Ω → A) :
    strIso ((restrictTo G Δ h : Subgroup (Equiv.Perm Δ)) : Set (Equiv.Perm Δ))
        (fun u : Δ => x (u : Ω)) (fun u : Δ => y (u : Ω)) = ∅ ↔
      wIso Δ (G : Set (Equiv.Perm Ω)) x y = ∅ := by
  constructor
  · intro hempty
    rw [Set.eq_empty_iff_forall_notMem]
    intro σ hσ
    have := (mem_wIso_iff_restrict h x y hσ.1).1 hσ
    rw [hempty] at this
    exact this
  · intro hempty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro τ ⟨⟨⟨σ, hσ⟩, rfl⟩, hagree⟩
    have : σ ∈ wIso Δ (G : Set (Equiv.Perm Ω)) x y :=
      (mem_wIso_iff_restrict h x y hσ).2 ⟨⟨⟨σ, hσ⟩, rfl⟩, hagree⟩
    rw [hempty] at this
    exact this

/-- §11.1, **Observation 11.1.11**: `Aut^Δ_G(x)`, as a subgroup of `G`, is the preimage of
`Aut_{G^Δ}(x^Δ)` under the restriction homomorphism. -/
theorem wAutSubgroup_subgroupOf_eq_comap (h : IsInvariant G Δ) (x : Ω → A) :
    (wAutSubgroup G Δ h x).subgroupOf G =
      Subgroup.comap (restrictHom G Δ h)
        (strAutSubgroup (restrictTo G Δ h) (fun u : Δ => x (u : Ω))) := by
  ext ⟨σ, hσ⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  show σ ∈ wAut Δ (G : Set (Equiv.Perm Ω)) x ↔ _
  rw [wAut, mem_wIso_iff_restrict h x x hσ]
  show _ ↔ restrictHom G Δ h ⟨σ, hσ⟩ ∈ wAut Set.univ _ _
  rw [wAut, ← wIso_univ]

/-- §11.1, **Observation 11.1.11**: "Adding to `S` a set of generators of the kernel of the
`G`-action on `Δ` we obtain a set of generators of `Aut^Δ_G(x)`."

Here `S ⊆ G` is a set whose restriction to `Δ` generates `Aut_{G^Δ}(x^Δ)`. -/
theorem Observation_11_1_11_generators (h : IsInvariant G Δ) (x : Ω → A) (S : Set G)
    (hS : Subgroup.closure ((restrictHom G Δ h) '' S) =
      strAutSubgroup (restrictTo G Δ h) (fun u : Δ => x (u : Ω))) :
    (wAutSubgroup G Δ h x).subgroupOf G =
      Subgroup.closure (S ∪ ((restrictHom G Δ h).ker : Set G)) := by
  rw [wAutSubgroup_subgroupOf_eq_comap h x]
  exact comap_eq_closure_union_ker _ S _ hS

/-- §11.1, **Observation 11.1.11**: "and `Iso^Δ_G(x,y) = Aut^Δ_G(x)σ`."  This is
Remark 11.1.5 (ii) for the coset `G = G·1`. -/
theorem wIso_eq_smul_wAut_one (h : IsInvariant G Δ) {x y : Ω → A} {σ : Equiv.Perm Ω}
    (hσ : σ ∈ wIso Δ (G : Set (Equiv.Perm Ω)) x y) :
    wIso Δ (G : Set (Equiv.Perm Ω)) x y = σ • wAut Δ (G : Set (Equiv.Perm Ω)) x := by
  have h1 : (1 : Equiv.Perm Ω) • (G : Set (Equiv.Perm Ω)) = (G : Set (Equiv.Perm Ω)) := by
    simp
  have := wIso_eq_smul_wAut h (1 : Equiv.Perm Ω) (σ' := σ) (by rwa [h1])
  rwa [h1] at this

end ReducingToWindow

/-! ### §11.1, the cited bound on generating sets ([Ba86])

> Let `G ≤ S(Ω)` be a permutation group acting on the domain `Ω`.  `G` will be represented
> concisely by a list of generators; if `|Ω| = n` then every minimal set of generators has
> `≤ 2n` elements [Ba86].

"Minimal set of generators" means *irredundant*: no proper subset generates.  (For a
*minimum-size* generating set the sharp bound is `⌊n/2⌋`, a different theorem.)

Nothing in version 2.5 uses the bound `2n` in a proof or in a cost estimate — it only
justifies the phrase "represented concisely" — so it gets no axiom (`CITED.md`, C14) and
is recorded as a statement only. -/

universe u in
/-- §11.1, cited from `[Ba86]` (László Babai: *On the length of subgroup chains in the
symmetric group*, Comm. Algebra **14** (1986), 1729–1736): "if `|Ω| = n` then every
minimal set of generators has `≤ 2n` elements".  Statement only; never used by the paper
in a proof or a cost estimate, so it is not an axiom. -/
def Theorem_Ba86_minimal_generating_sets_statement : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (G : Subgroup (Equiv.Perm Ω)) (S : Set (Equiv.Perm Ω)),
    Subgroup.closure S = G → (∀ T ⊂ S, Subgroup.closure T ≠ G) →
    S.ncard ≤ 2 * Fintype.card Ω

end Babai
