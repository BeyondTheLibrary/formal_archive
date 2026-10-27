/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1 (Local Certificates: the core algorithm): the setting, Notation 13.1.1,
Definition 13.1.2, the two kinds of certificates, Definition 13.1.4 and Observation
13.1.5.
-/
import Workspace.LocalCertificates.PrelimExtra

/-!
# §13.1 Local certificates: definitions

## The situation (§13.1, opening)

> The input is a transitive permutation group `G ≤ S(Ω)` along with a giant representation
> `ϕ : G → S(Γ)` (i. e., a homomorphism such that `G^ϕ ≥ A(Γ)`) and two strings
> `x, y : Ω → Σ` (`Σ` is a finite alphabet).
> Notation: `n = |Ω|`, `m = |Γ|`.  We shall assume `m ≥ 10 log₂ n`.

The alphabet is written `Λ` here, because `Σ` is reserved in Lean and because `A` is the
paper's name for a subset of `Γ` in Notation 13.1.1.  The standing hypotheses are bundled
in `Babai.LocalCertSetting`; the individual statements take exactly the hypotheses the
paper's statement takes.

## Numbering map

| Paper | Lean |
|---|---|
| §13.1 the situation | `Babai.LocalCertSetting` |
| Notation 13.1.1 `L_A` | `Babai.stabIn` |
| Notation 13.1.1 `A` is `L`-invariant | `Babai.IsInvariantUnder` |
| Notation 13.1.1 `ψ_A` | `Babai.psi` |
| Notation 13.1.1 `L^A` | `Babai.imgOn` |
| Notation 13.1.1 `G_A = ϕ⁻¹((G^ϕ)_A)` | `Babai.stabIn_eq_preimage` |
| Notation 13.1.1 `ψ_A` is onto for `|A| ≤ m-2` | `Babai.psi_surjective` |
| Definition 13.1.2 (fullness) | `Babai.IsFull` |
| Definition 13.1.2 `F(x)`, `F̄(x)` | `Babai.fullSets`, `Babai.nonfullSets` |
| certificate of non-fullness | `Babai.IsNonFullnessCertificate` |
| certificate of fullness | `Babai.IsFullnessCertificate` |
| Definition 13.1.4 (Affected), Eq. (68) | `Babai.Aff` |
| Observation 13.1.5 | `Babai.observation_13_1_5` |
-/

namespace Babai

open MulAction Equiv Equiv.Perm

open scoped Classical

universe u

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G L L' : Subgroup (Equiv.Perm Ω)}

/-! ### §13.1 The situation -/

/-- §13.1, the opening paragraph.

> The input is a transitive permutation group `G ≤ S(Ω)` along with a giant representation
> `ϕ : G → S(Γ)` … and two strings `x, y : Ω → Σ`.  Notation: `n = |Ω|`, `m = |Γ|`.  We
> shall assume `m ≥ 10 log₂ n`. -/
structure LocalCertSetting {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ]
    [DecidableEq Γ] (G : Subgroup (Equiv.Perm Ω)) (ϕ : G →* Equiv.Perm Γ) : Prop where
  /-- "a transitive permutation group `G ≤ S(Ω)`" -/
  transitive : IsTransitive G
  /-- "a giant representation `ϕ : G → S(Γ)`" -/
  giant : IsGiantRep ϕ
  /-- "We shall assume `m ≥ 10 log₂ n`." -/
  large : 10 * Real.logb 2 (Nat.card Ω) ≤ (Nat.card Γ : ℝ)

/-! ### Notation 13.1.1 -/

/-- Notation 13.1.1.  The restriction `ϕ|_L : L → S(Γ)` of the representation `ϕ` to a
subgroup `L ≤ G`. -/
def phiOn (ϕ : G →* Equiv.Perm Γ) (hL : L ≤ G) : L →* Equiv.Perm Γ :=
  ϕ.comp (Subgroup.inclusion hL)

@[simp] theorem phiOn_apply (ϕ : G →* Equiv.Perm Γ) (hL : L ≤ G) (σ : L) :
    phiOn ϕ hL σ = ϕ ⟨(σ : Equiv.Perm Ω), hL σ.2⟩ := rfl

/-- Notation 13.1.1.  `L^ϕ`, the image of `L ≤ G` under `ϕ`. -/
def imgPhi (ϕ : G →* Equiv.Perm Γ) (hL : L ≤ G) : Subgroup (Equiv.Perm Γ) :=
  (phiOn ϕ hL).range

/-- Notation 13.1.1.

> Recall that for a subgroup `L ≤ G` and a subset `A ⊆ Γ` we write `L_A` to denote the
> setwise stabilizer of `A` in `L` with respect to the representation `ϕ|L : L → S(Γ)`.

`L_A` is returned as a subgroup of `S(Ω)`; it is contained in `L` (`Babai.stabIn_le`). -/
def stabIn (ϕ : G →* Equiv.Perm Γ) (hL : L ≤ G) (A : Set Γ) : Subgroup (Equiv.Perm Ω) :=
  ((setwiseStabilizer ⊤ A).comap (phiOn ϕ hL)).map L.subtype

theorem mem_stabIn {ϕ : G →* Equiv.Perm Γ} {hL : L ≤ G} {A : Set Γ} {σ : Equiv.Perm Ω} :
    σ ∈ stabIn ϕ hL A ↔ ∃ h : σ ∈ L, (ϕ ⟨σ, hL h⟩ : Equiv.Perm Γ) '' A = A := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hmem, rfl⟩
    exact ⟨hτ, hmem.2⟩
  · rintro ⟨hσ, himg⟩
    exact ⟨⟨σ, hσ⟩, ⟨Subgroup.mem_top _, himg⟩, rfl⟩

theorem stabIn_le {ϕ : G →* Equiv.Perm Γ} {hL : L ≤ G} {A : Set Γ} :
    stabIn ϕ hL A ≤ L := by
  rintro σ hσ
  exact (mem_stabIn.1 hσ).fst

theorem stabIn_le_top {ϕ : G →* Equiv.Perm Γ} {A : Set Γ} :
    stabIn ϕ (le_refl G) A ≤ G := stabIn_le

/-- `L_A` grows with `L`. -/
theorem stabIn_mono {ϕ : G →* Equiv.Perm Γ} {hL : L ≤ G} {hL' : L' ≤ G} (h : L ≤ L')
    {A : Set Γ} : stabIn ϕ hL A ≤ stabIn ϕ hL' A := by
  intro σ hσ
  obtain ⟨hσL, himg⟩ := mem_stabIn.1 hσ
  exact mem_stabIn.2 ⟨h hσL, himg⟩

/-- Notation 13.1.1.  "We say that `A` is `L`-invariant if `L_A = L`." -/
def IsInvariantUnder (ϕ : G →* Equiv.Perm Γ) (hL : L ≤ G) (A : Set Γ) : Prop :=
  stabIn ϕ hL A = L

/-- Notation 13.1.1, the first remark.

> We note that the group `(G^ϕ)_A` can be trivially computed because `ϕ` is a giant
> representation.  Therefore `G_A` can be computed in polynomial time as
> `G_A = ϕ⁻¹((G^ϕ)_A)`.

The mathematical content is the displayed identity `G_A = ϕ⁻¹((G^ϕ)_A)`; the running-time
claim is covered inside the RAM proof of Theorem 1.1.1 (`Algo.theorem_1_1_1`) and not stated as
a separate RAM theorem. -/
theorem stabIn_eq_preimage (ϕ : G →* Equiv.Perm Γ) (A : Set Γ) :
    stabIn ϕ (le_refl G) A
      = ((setwiseStabilizer (imgPhi ϕ (le_refl G)) A).comap (phiOn ϕ (le_refl G))).map
          G.subtype := by
  ext σ
  rw [mem_stabIn]
  constructor
  · rintro ⟨hσ, himg⟩
    exact ⟨⟨σ, hσ⟩, ⟨⟨⟨σ, hσ⟩, rfl⟩, himg⟩, rfl⟩
  · rintro ⟨⟨τ, hτ⟩, hmem, rfl⟩
    exact ⟨hτ, hmem.2⟩

/-- `A` is invariant under `G_A`, so the restriction of the `G^ϕ`-action to `A` is
defined on `G_A`. -/
theorem stabIn_mem_setwise {ϕ : G →* Equiv.Perm Γ} {A : Set Γ}
    (σ : stabIn ϕ (le_refl G) A) :
    (ϕ ⟨(σ : Equiv.Perm Ω), stabIn_le_top σ.2⟩ : Equiv.Perm Γ) ∈ setwiseStabilizer ⊤ A := by
  obtain ⟨hσ, himg⟩ := mem_stabIn.1 σ.2
  exact ⟨Subgroup.mem_top _, himg⟩

/-- Notation 13.1.1.

> We write `ψ_A : G_A → S(A)` for the map that restricts the `G^ϕ`-action to `A`. -/
def psi (ϕ : G →* Equiv.Perm Γ) (A : Set Γ) :
    (stabIn ϕ (le_refl G) A) →* Equiv.Perm A :=
  (setwiseRestrictHom ⊤ A).comp
    (MonoidHom.codRestrict (ϕ.comp (Subgroup.inclusion (stabIn_le_top (ϕ := ϕ) (A := A))))
      (setwiseStabilizer ⊤ A) (fun σ => stabIn_mem_setwise σ))

@[simp] theorem psi_apply_coe (ϕ : G →* Equiv.Perm Γ) (A : Set Γ)
    (σ : stabIn ϕ (le_refl G) A) (a : A) :
    ((psi ϕ A σ a : A) : Γ) = ϕ ⟨(σ : Equiv.Perm Ω), stabIn_le_top σ.2⟩ (a : Γ) := rfl

/-- Notation 13.1.1.

> If `A` is `L`-invariant then `L^A := L^{ψ_A}` is the restriction of `L^ϕ` to `A`.

The hypothesis under which this is used throughout §13.1 is `L ≤ G_A` (which is what
`A` being `L`-invariant amounts to, see `Babai.le_stabIn_iff_isInvariantUnder`). -/
def imgOn (ϕ : G →* Equiv.Perm Γ) (A : Set Γ) (hL : L ≤ stabIn ϕ (le_refl G) A) :
    Subgroup (Equiv.Perm A) :=
  ((psi ϕ A).comp (Subgroup.inclusion hL)).range

/-- `A` is `L`-invariant exactly when `L ≤ G_A`. -/
theorem le_stabIn_iff_isInvariantUnder (ϕ : G →* Equiv.Perm Γ) (A : Set Γ) (hL : L ≤ G) :
    L ≤ stabIn ϕ (le_refl G) A ↔ IsInvariantUnder ϕ hL A := by
  constructor
  · intro h
    refine le_antisymm stabIn_le fun σ hσ => ?_
    obtain ⟨hh, himg⟩ := mem_stabIn.1 (h hσ)
    exact mem_stabIn.2 ⟨hσ, himg⟩
  · intro h σ hσ
    rw [← h] at hσ
    obtain ⟨hσL, himg⟩ := mem_stabIn.1 hσ
    exact mem_stabIn.2 ⟨hL hσL, himg⟩

/-- Notation 13.1.1.  "In particular, `ψ_Γ = ϕ`": the restriction of the `G^ϕ`-action to
all of `Γ` is `ϕ` itself (`G_Γ = G` and the restriction map `S(Γ) → S(Γ)` is the
identity). -/
theorem stabIn_univ (ϕ : G →* Equiv.Perm Γ) :
    stabIn ϕ (le_refl G) (Set.univ : Set Γ) = G := by
  ext σ
  rw [mem_stabIn]
  constructor
  · rintro ⟨hσ, -⟩; exact hσ
  · intro hσ
    exact ⟨hσ, by simpa using (ϕ ⟨σ, hσ⟩ : Equiv.Perm Γ).surjective.range_eq⟩

/-! ### Notation 13.1.1, second remark: `ψ_A` is an epimorphism -/

/-- Notation 13.1.1, the second remark.

> We note further that if `|A| ≤ |Γ| - 2` then `ψ_A : G_A → S(A)` is an epimorphism.
> Indeed, in this case the setwise stabilizer of `A` in `A(Γ)` acts on `A` as `S(A)`.

(The hypothesis that `ϕ` is a giant representation is the standing assumption of §13.1.) -/
theorem psi_surjective (ϕ : G →* Equiv.Perm Γ) (hϕ : IsGiantRep ϕ) {A : Set Γ}
    (hA : A.ncard + 2 ≤ Nat.card Γ) : Function.Surjective (psi ϕ A) := by
  intro π
  -- two points outside `A`, which exist because `|A| ≤ |Γ| - 2`
  have hcompl : 2 ≤ (Aᶜ : Set Γ).ncard := by
    have h := Set.ncard_add_ncard_compl A
    rw [Nat.card_eq_fintype_card] at *
    omega
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ (Aᶜ : Set Γ), ∃ b ∈ (Aᶜ : Set Γ), a ≠ b := by
    rw [show (2 : ℕ) = 1 + 1 from rfl] at hcompl
    have h1 : (Aᶜ : Set Γ).Nontrivial := by
      rw [← Set.one_lt_ncard_iff_nontrivial]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    exact ⟨a, ha, b, hb, hab⟩
  -- extend `π` by the identity outside `A`, correcting the sign if necessary
  set p₀ : Equiv.Perm Γ := Equiv.Perm.ofSubtype π with hp₀
  set p : Equiv.Perm Γ := if Equiv.Perm.sign π = 1 then p₀ else p₀ * Equiv.swap a b with hp
  have hfix : ∀ (c : Γ) (hc : c ∈ A), p c = (π ⟨c, hc⟩ : Γ) := by
    intro c hc
    have hca : c ≠ a := fun h => ha (h ▸ hc)
    have hcb : c ≠ b := fun h => hb (h ▸ hc)
    by_cases hs : Equiv.Perm.sign π = 1 <;>
      simp [hp, hs, hp₀, Equiv.Perm.ofSubtype_apply_of_mem π hc, Equiv.swap_apply_of_ne_of_ne,
        hca, hcb]
  have hsign : Equiv.Perm.sign p = 1 := by
    by_cases hs : Equiv.Perm.sign π = 1
    · simp [hp, hs, hp₀]
    · have hs' : Equiv.Perm.sign π = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
        · exact absurd h hs
        · exact h
      simp [hp, hs, hp₀, hs', Equiv.Perm.sign_swap hab]
  have hmemA : p '' A = A := by
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [hfix d hd]
      exact (π ⟨d, hd⟩).2
    · intro hc
      refine ⟨(π.symm ⟨c, hc⟩ : Γ), (π.symm ⟨c, hc⟩).2, ?_⟩
      rw [hfix _ (π.symm ⟨c, hc⟩).2]
      simp
  -- `p ∈ A(Γ) ≤ G^ϕ`, so `p = ϕ σ` for some `σ ∈ G`, and `σ ∈ G_A`
  obtain ⟨σ, hσ⟩ := hϕ (Equiv.Perm.mem_alternatingGroup.2 hsign)
  have hσA : (σ : Equiv.Perm Ω) ∈ stabIn ϕ (le_refl G) A := by
    refine mem_stabIn.2 ⟨σ.2, ?_⟩
    have : ϕ ⟨(σ : Equiv.Perm Ω), σ.2⟩ = ϕ σ := by congr
    rw [this, hσ]
    exact hmemA
  refine ⟨⟨(σ : Equiv.Perm Ω), hσA⟩, ?_⟩
  ext c
  have hc : (c : Γ) ∈ A := c.2
  have hval : ((psi ϕ A ⟨(σ : Equiv.Perm Ω), hσA⟩ c : A) : Γ)
      = ϕ ⟨(σ : Equiv.Perm Ω), stabIn_le_top hσA⟩ (c : Γ) := rfl
  have hϕσ : ϕ ⟨(σ : Equiv.Perm Ω), stabIn_le_top hσA⟩ = p := by
    have : (⟨(σ : Equiv.Perm Ω), stabIn_le_top hσA⟩ : G) = σ := Subtype.ext rfl
    rw [this, hσ]
  rw [hval, hϕσ]
  have hf := hfix (c : Γ) hc
  rw [hf]

/-! ### Definition 13.1.2 (Fullness of test set) -/

variable (ϕ : G →* Equiv.Perm Γ) (x : Ω → Λ)

/-- §13.1.  `Aut_G(x)`, the `G`-automorphism group of the string `x` (§11.1). -/
abbrev autG (G : Subgroup (Equiv.Perm Ω)) (x : Ω → Λ) : Subgroup (Equiv.Perm Ω) :=
  strAutSubgroup G x

theorem autG_le (G : Subgroup (Equiv.Perm Ω)) (x : Ω → Λ) : autG G x ≤ G :=
  wAutSubgroup_le _ _ _ _

/-- `Aut_G(x)_T ≤ G_T`. -/
theorem autStab_le (T : Set Γ) :
    stabIn ϕ (autG_le G x) T ≤ stabIn ϕ (le_refl G) T :=
  stabIn_mono (autG_le G x)

/-- **Definition 13.1.2** (Fullness of test set), §13.1.

> Let `T ∈ (Γ choose t)` be a test set.  We say that `T` is *full* with respect to `x` if
> `Aut_G(x)_T^T ≥ A(T)`, i. e., the `G`-automorphisms of `x` induce a giant on `T`. -/
def IsFull (T : Set Γ) : Prop :=
  alternatingGroup T ≤ imgOn ϕ T (autStab_le ϕ x T)

/-- **Definition 13.1.2**, §13.1.

> Notation: `F(x) = {T ∈ (Γ choose t) | T is full}`. -/
def fullSets (t : ℕ) : Set (Set Γ) := {T | T.ncard = t ∧ IsFull ϕ x T}

/-- **Definition 13.1.2**, §13.1.

> `F̄(x) = (Γ choose t) ∖ F(x)`. -/
def nonfullSets (t : ℕ) : Set (Set Γ) := {T | T.ncard = t ∧ ¬ IsFull ϕ x T}

theorem fullSets_union_nonfullSets (t : ℕ) :
    fullSets ϕ x t ∪ nonfullSets ϕ x t = {T : Set Γ | T.ncard = t} := by
  ext T
  by_cases h : IsFull ϕ x T <;> simp [fullSets, nonfullSets, h]

/-! ### The two kinds of certificates (§13.1, before Theorem 13.1.3) -/

/-- §13.1, **Certificate of non-fullness**.

> A certificate of non-fullness of the test set `T ⊂ Γ` is a permutation group
> `M(T) ≤ S(T)` such that (i) `M(T) ≱ A(T)` and (ii) `M(T) ≥ Aut_G(x)_T^T` (`M(T)` is
> guaranteed to contain the projection of the `G`-automorphism group of `x`). -/
structure IsNonFullnessCertificate (T : Set Γ) (M : Subgroup (Equiv.Perm T)) : Prop where
  /-- (i) `M(T) ≱ A(T)` -/
  not_giant : ¬ alternatingGroup T ≤ M
  /-- (ii) `M(T) ≥ Aut_G(x)_T^T` -/
  ge_autProj : imgOn ϕ T (autStab_le ϕ x T) ≤ M

/-- §13.1, **Certificate of fullness**.

> A certificate of fullness of the test set `T ⊂ Γ` is a permutation group
> `K(T) ≤ S(Ω)` such that (i) `K(T)^T ≥ A(T)` and (ii) `K(T) ≤ Aut_{G_T}(x)`.

For `K(T)^T` to be defined, `T` must be `K(T)`-invariant, i. e. `K(T) ≤ G_T`; this is
implied by (ii) and recorded as the field `le_stab`. -/
structure IsFullnessCertificate (T : Set Γ) (K : Subgroup (Equiv.Perm Ω)) : Prop where
  /-- `K(T) ≤ G_T`, so that `K(T)^T` is defined. -/
  le_stab : K ≤ stabIn ϕ (le_refl G) T
  /-- (i) `K(T)^T ≥ A(T)` -/
  giant : alternatingGroup T ≤ imgOn ϕ T le_stab
  /-- (ii) `K(T) ≤ Aut_{G_T}(x)` -/
  le_aut : K ≤ autG (stabIn ϕ (le_refl G) T) x

/-- A certificate of fullness is in particular contained in `Aut_G(x)`, as Theorem
13.1.3 (a) and Claim 13.1.6 state it. -/
theorem IsFullnessCertificate.le_autG {T : Set Γ} {K : Subgroup (Equiv.Perm Ω)}
    (h : IsFullnessCertificate ϕ x T K) : K ≤ autG G x := by
  intro σ hσ
  have hmem := h.le_aut hσ
  exact ⟨stabIn_le hmem.1, hmem.2⟩

/-! ### Definition 13.1.4 (Affected) -/

/-- **Definition 13.1.4** (Affected), §13.1, Eq. (68).

> Let `G ≤ S(Ω)` be a permutation group and `ϕ : G → S(Γ)` a homomorphism.  Consistently
> with previous usage, for a subgroup `H ≤ G` we say that `x ∈ Ω` is *affected by*
> `(H, ϕ)` if `H_x^ϕ ≱ A(Γ)`.  Let `Aff(H, ϕ)` denote the set of elements affected by
> `(H, ϕ)`, i. e.
> `Aff(H, ϕ) = {x ∈ Ω | H_x^ϕ ≱ A(Γ)}`.  (68)

This is Definition 10.3.4 for the restricted representation `ϕ|_H` (`Babai.AffectedIn`).
The algorithm of §13.1 uses it both for `ϕ` itself and for the restrictions
`ψ_T : G_T → S(T)`. -/
def Aff (ϕ : G →* Equiv.Perm Γ) (hH : L ≤ G) : Set Ω :=
  {u | AffectedIn (phiOn ϕ hH) u}

@[simp] theorem mem_Aff {ϕ : G →* Equiv.Perm Γ} {hH : L ≤ G} {u : Ω} :
    u ∈ Aff ϕ hH ↔ ¬ alternatingGroup Γ ≤ (stabilizer L u).map (phiOn ϕ hH) := Iff.rfl

/-- §13.1, after Eq. (68).

> Note that if `ϕ` restricted to `H` is not a giant representation then all of `Ω` is
> affected by `(H, ϕ)`. -/
theorem Aff_eq_univ_of_not_giantRep {ϕ : G →* Equiv.Perm Γ} {hH : L ≤ G}
    (h : ¬ IsGiantRep (phiOn ϕ hH)) : Aff ϕ hH = Set.univ := by
  ext u
  simp only [mem_Aff, Set.mem_univ, iff_true]
  intro hle
  exact h (le_trans hle (Subgroup.map_le_range _ _))

/-- §13.1, after Eq. (68).  The general form of the previous remark: a point whose
stabilizer already induces a giant is a point where `ψ` is a giant representation. -/
theorem isGiantRep_of_not_affected {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] {ψ : H →* Equiv.Perm Δ} {u : Ω} (h : ¬ AffectedIn ψ u) :
    IsGiantRep ψ := by
  have hle : alternatingGroup Δ ≤ (stabilizer H u).map ψ := not_not.1 h
  exact le_trans hle (Subgroup.map_le_range _ _)

/-- §13.1, after Eq. (68).

> If `x ∈ Ω` is affected by `(H, ϕ)` then all elements of the orbit `x^H` are affected by
> `(H, ϕ)`.  In other words, `Aff(H, ϕ)` is an `H`-invariant set.

Stated for an arbitrary target, as the algorithm uses it for `ψ_T`. -/
theorem affectedIn_of_mem_orbit {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (ψ : H →* Equiv.Perm Δ) {u v : Ω} (hv : v ∈ orbit H u)
    (hu : AffectedIn ψ u) : AffectedIn ψ v := by
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.1 hv
  intro hle
  refine hu ?_
  -- `H_{σu} = σ H_u σ⁻¹`, so the two images under `ψ` are conjugate, and `A(Δ)` is normal
  have hconj : stabilizer H (σ • u) = (stabilizer H u).map (MulAut.conj σ).toMonoidHom :=
    stabilizer_smul_eq_stabilizer_map_conj σ u
  have hcomp : ((stabilizer H u).map (MulAut.conj σ).toMonoidHom).map ψ
      = ((stabilizer H u).map ψ).map (MulAut.conj (ψ σ)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp [MulAut.conj, map_mul, map_inv]
  rw [hconj, hcomp, ← map_alternatingGroup_conj (ψ σ),
    Subgroup.map_le_map_iff_of_injective (MulAut.conj (ψ σ)).injective] at hle
  exact hle

/-- §13.1, after Eq. (68).  "`Aff(H, ϕ)` is an `H`-invariant set.  So we can speak of
*affected orbits* of `H` (of which all elements are affected)." -/
theorem isInvariant_affectedIn {H : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (ψ : H →* Equiv.Perm Δ) :
    IsInvariant H {u | AffectedIn ψ u} := by
  rw [isInvariant_iff_mem]
  intro σ hσ u
  constructor
  · intro hu
    exact affectedIn_of_mem_orbit ψ (mem_orbit_iff.2 ⟨⟨σ, hσ⟩, rfl⟩) hu
  · intro hu
    refine affectedIn_of_mem_orbit ψ (u := σ u) (v := u) ?_ hu
    exact mem_orbit_iff.2 ⟨⟨σ, hσ⟩⁻¹, by simp [Subgroup.smul_def]⟩

theorem isInvariant_Aff {ϕ : G →* Equiv.Perm Γ} {hH : L ≤ G} : IsInvariant L (Aff ϕ hH) :=
  isInvariant_affectedIn _

/-! ### Observation 13.1.5 -/

/-- **Observation 13.1.5**, §13.1.

> If `H₁ ≤ H₂ ≤ G` then `Aff(H₁, ϕ) ⊇ Aff(H₂, ϕ)`.

(The "dual monotonicity of the `Aff` operator".)  Stated for an arbitrary target, as the
algorithm uses it for `ψ_T`. -/
theorem observation_13_1_5 {H₁ H₂ : Subgroup (Equiv.Perm Ω)} {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h : H₁ ≤ H₂) (ψ : H₂ →* Equiv.Perm Δ) :
    {u | AffectedIn (ψ.comp (Subgroup.inclusion h)) u} ⊇ {u | AffectedIn ψ u} := by
  intro u hu hcon
  refine hu (le_trans hcon ?_)
  rintro g ⟨σ, hσ, rfl⟩
  refine ⟨⟨(σ : Equiv.Perm Ω), h σ.2⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_stabilizer_iff] at hσ ⊢
  simpa [Subgroup.smul_def] using hσ

/-- **Observation 13.1.5** in the notation of Definition 13.1.4. -/
theorem observation_13_1_5' {ϕ : G →* Equiv.Perm Γ} {H₁ H₂ : Subgroup (Equiv.Perm Ω)}
    (h : H₁ ≤ H₂) (h₂ : H₂ ≤ G) : Aff ϕ (le_trans h h₂) ⊇ Aff ϕ h₂ :=
  observation_13_1_5 h (phiOn ϕ h₂)

end Babai
