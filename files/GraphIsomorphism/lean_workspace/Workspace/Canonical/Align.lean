/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.1: Procedure Align.  Section 14.2: the cost analysis.
-/
import Workspace.Canonical.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin

/-!
# §14.1 Procedure Align

> Let `X(z)` be the canonical structure associated with the input string `z ∈ {x, y}`.
> Alignment means that `X(x) = X(y')` for a `G`-shifted copy `y'` of `y`.
>
> **Procedure Align.**
> *Input*: canonical structures `X(x)`, `X(y)` on `Γ`.
> *Output*: string `y'`, permutation `σ ∈ G`, and group `G₁ ≤ G` such that
> `Iso_G(x,y) = Iso_{G₁}(x,y')σ` and `G₁^ϕ = Aut(X(x))`.  (70)
> (: Note that it follows that `X(x) = X(y')` :)
>
> 1. If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then reject isomorphism, exit
> 2. Else, let
>    (i) `σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))`          (: aligning in `Γ` :)
>    (ii) `σ ∈ ϕ⁻¹(σ̄)`                        (: lifting :)
>    (iii) `y' = y^{σ⁻¹}`                      (: aligning the inputs :)
>    (iv) `G₁ = ϕ⁻¹(Aut(X(x)))`                (: reducing the group :)
> 3. Update: `y ← y'`, `G ← G₁`.

This file states and proves each of these, for an abstract `S(Γ)`-set of structures
(`Babai.IsCanonicalStructure`), then lines 4–6 (the induced coloring of `Ω` and the Chain
Rule over its classes), then lines 7–11 (the reduced set `Γ*` and the claim
"(: this is a giant representation :)"), and finally the arithmetic of Sec. 14.2.

**One correction.**  The printed second clause of Eq. (70), `G₁^ϕ = Aut(X(x))`, is false:
`ϕ` maps `ϕ⁻¹(H)` onto `H ∩ G^ϕ`, not onto `H`.  What is true is
`G₁^ϕ = Aut(X(x)) ∩ G^ϕ` (`Babai.Align_G1_image`); see
`Babai.not_Align_G1_image_as_printed` for a counterexample and the corrected paper.

**Running time.**  Line 2 ("isomorphism of our canonical structures `X` is testable in
polynomial time") and the cost claims of Sec. 14.2 are
covered inside the RAM proof of Theorem 1.1.1 (`Algo.theorem_1_1_1`) and not stated as a
separate RAM theorem; see the Section 14 entry (53) in the corrected paper.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type u} {A : Type v} {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳]
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### The shift identity for a group -/

/-- Eq. (57) (shift identity) for a *group* `G` and `σ ∈ G`:
`Iso_G(x,y) = Iso_G(x, y^{σ⁻¹})σ`.  (Lean's left translate `σ • S` is the paper's right
coset `Sσ`.) -/
theorem strIso_eq_smul_shift (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A) (σ : G) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      (σ : Equiv.Perm Ω) •
        strIso (G : Set (Equiv.Perm Ω)) x (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
  have hGσ : (σ : Equiv.Perm Ω) • (G : Set (Equiv.Perm Ω)) = (G : Set (Equiv.Perm Ω)) := by
    ext τ
    rw [mem_perm_smul_set, SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h
      have hrw : τ = (σ : Equiv.Perm Ω) * ((σ : Equiv.Perm Ω)⁻¹ * τ) := by group
      rw [hrw]; exact mul_mem σ.2 h
    · intro h; exact mul_mem (inv_mem σ.2) h
  have h := strIso_smul (G : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) x y
  rwa [hGσ] at h

/-! ### Procedure Align, lines 1–3 -/

/-- Procedure Align, **line 1**: *"If `X(x)` and `X(y)` are not `G^ϕ`-isomorphic then
reject isomorphism, exit."*

The rejection is correct: if there is no `G^ϕ`-isomorphism of the two structures then `x`
and `y` are not `G`-isomorphic.  Indeed a `G`-isomorphism `τ` of the strings has
`X(y) = X(x^τ) = X(x)^{τ^ϕ}` by canonicity, so `τ^ϕ ∈ Iso_{G^ϕ}(X(x), X(y))`. -/
theorem Align_reject_struct {ϕ : G →* Equiv.Perm Γ} {X : (Ω → A) → 𝒳}
    (hcan : IsCanonicalStructure ϕ X) (x y : Ω → A)
    (hrej : structIso (ϕ.range : Set (Equiv.Perm Γ)) (X x) (X y) = ∅) :
    strIso (G : Set (Equiv.Perm Ω)) x y = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro τ hτ
  have hmem : ϕ ⟨τ, hτ.1⟩ ∈ structIso (ϕ.range : Set (Equiv.Perm Γ)) (X x) (X y) := by
    refine ⟨⟨⟨τ, hτ.1⟩, rfl⟩, ?_⟩
    rw [← hcan x ⟨τ, hτ.1⟩, hτ.2]
  rw [hrej] at hmem
  exact hmem

/-- Procedure Align, the parenthetical remark after Eq. (70): *"(: Note that it follows
that `X(x) = X(y')` :)"*, where `y' = y^{σ⁻¹}` and `σ^ϕ ∈ Iso_{G^ϕ}(X(x), X(y))`. -/
theorem Align_struct_shift {ϕ : G →* Equiv.Perm Γ} {X : (Ω → A) → 𝒳}
    (hcan : IsCanonicalStructure ϕ X) (x y : Ω → A) (σ : G) (hσ : ϕ σ • X x = X y) :
    X (strAct y (σ : Equiv.Perm Ω)⁻¹) = X x := by
  have h := hcan y ⟨((σ : Equiv.Perm Ω))⁻¹, inv_mem σ.2⟩
  have hinv : (⟨((σ : Equiv.Perm Ω))⁻¹, inv_mem σ.2⟩ : G) = σ⁻¹ := rfl
  rw [h, hinv, map_inv, ← hσ, inv_smul_smul]

/-- Procedure Align, line 2 (iv): once the inputs are aligned (`X(y') = X(x)`), every
`G`-isomorphism of `x` and `y'` already lies in `G₁ = ϕ⁻¹(Aut(X(x)))`, so
`Iso_G(x,y') = Iso_{G₁}(x,y')`. -/
theorem Align_strIso_eq_preimage {ϕ : G →* Equiv.Perm Γ} {X : (Ω → A) → 𝒳}
    (hcan : IsCanonicalStructure ϕ X) (x y' : Ω → A) (hX : X y' = X x) :
    strIso (G : Set (Equiv.Perm Ω)) x y' =
      strIso ((preimageSubgroup ϕ (structAut (X x)) : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) x y' := by
  ext τ
  constructor
  · rintro ⟨hτG, hτx⟩
    refine ⟨mem_preimageSubgroup.2 ⟨hτG, mem_structAut.2 ?_⟩, hτx⟩
    rw [← hcan x ⟨τ, hτG⟩, hτx, hX]
  · rintro ⟨hτ1, hτx⟩
    exact ⟨preimageSubgroup_le ϕ _ hτ1, hτx⟩

/-- §14.1, **Eq. (70)**, first clause: `Iso_G(x,y) = Iso_{G₁}(x,y')σ` with `y' = y^{σ⁻¹}`
and `G₁ = ϕ⁻¹(Aut(X(x)))`, where `σ ∈ G` is any lifting of a
`σ̄ ∈ Iso_{G^ϕ}(X(x), X(y))` (lines 2 (i)–(iv)).

The paper's right coset `Kσ` is Lean's left translate `σ • K`. -/
theorem Align_eq70 {ϕ : G →* Equiv.Perm Γ} {X : (Ω → A) → 𝒳}
    (hcan : IsCanonicalStructure ϕ X) (x y : Ω → A) (σ : G) (hσ : ϕ σ • X x = X y) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      (σ : Equiv.Perm Ω) •
        strIso ((preimageSubgroup ϕ (structAut (X x)) : Subgroup (Equiv.Perm Ω)) :
          Set (Equiv.Perm Ω)) x (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
  rw [strIso_eq_smul_shift G x y σ,
    Align_strIso_eq_preimage hcan x _ (Align_struct_shift hcan x y σ hσ)]

/-- §14.1, **Eq. (70)**, second clause, corrected: `G₁^ϕ = Aut(X(x)) ∩ G^ϕ`.

The printed form is `G₁^ϕ = Aut(X(x))`, which is false in general: `ϕ` maps `ϕ⁻¹(H)` onto
`H ∩ G^ϕ`, and when `G^ϕ = A(Γ)` while `Aut(X(x))` contains an odd permutation the two
differ (`Babai.not_Align_G1_image_as_printed`).  See the corrected paper. -/
theorem Align_G1_image (ϕ : G →* Equiv.Perm Γ) {X : (Ω → A) → 𝒳} (x : Ω → A) :
    homImage ϕ ((preimageSubgroup ϕ (structAut (X x)) : Subgroup (Equiv.Perm Ω)) :
        Set (Equiv.Perm Ω)) =
      (structAut (Γ := Γ) (X x) : Set (Equiv.Perm Γ)) ∩ (ϕ.range : Set (Equiv.Perm Γ)) :=
  homImage_preimageSubgroup ϕ _

/-! #### The printed second clause of Eq. (70) is false -/

/-- §14.1, Eq. (70), second clause **as printed**: `G₁^ϕ = Aut(X(x))` for
`G₁ = ϕ⁻¹(Aut(X(x)))`, under the standing hypotheses of Sec. 14 (`G ≤ S(Ω)` with a giant
representation `ϕ : G → S(Γ)` and a canonical structure `X`).

This is false; see `Babai.not_Align_G1_image_as_printed`. -/
def Align_G1_image_as_printed : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (m : ℕ) (κ : Type)
    (G : Subgroup (Equiv.Perm Ω)) (ϕ : G →* Equiv.Perm (Fin m))
    (X : (Ω → Bool) → ColStruct (Fin m) κ),
    IsGiantRep ϕ → IsCanonicalStructure ϕ X → ∀ x : Ω → Bool,
      homImage ϕ ((preimageSubgroup ϕ (structAut (X x)) : Subgroup (Equiv.Perm Ω)) :
          Set (Equiv.Perm Ω)) =
        (structAut (Γ := Fin m) (X x) : Set (Equiv.Perm (Fin m)))

/-- The printed second clause of Eq. (70) is false.

Counterexample: `Ω = Γ = [5]`, `G = A(Γ)` acting on itself, `ϕ` the inclusion (a giant
representation, `G^ϕ = A(Γ)`), and `X(z)` the constant structure (all of `Γ` one color, no
additional structure), which is canonical.  Then `Aut(X(x)) = S(Γ)`, so
`G₁ = ϕ⁻¹(S(Γ)) = G` and `G₁^ϕ = A(Γ)`, which does not contain the transposition
`(0 1) ∈ S(Γ) = Aut(X(x))`.

What is true is `G₁^ϕ = Aut(X(x)) ∩ G^ϕ` (`Babai.Align_G1_image`), which in the
counterexample reads `A(Γ) = S(Γ) ∩ A(Γ)`. -/
theorem not_Align_G1_image_as_printed : ¬ Align_G1_image_as_printed := by
  intro h
  classical
  set G : Subgroup (Equiv.Perm (Fin 5)) := alternatingGroup (Fin 5) with hG
  set X : (Fin 5 → Bool) → ColStruct (Fin 5) Unit :=
    fun _ => ⟨fun _ => (), fun _ _ => 0⟩ with hX
  have hgiant : IsGiantRep (G.subtype) := by
    rw [IsGiantRep, Subgroup.subtype_range]
  have hcan : IsCanonicalStructure (G.subtype) X := fun _ _ => rfl
  have haut : structAut (X (fun _ => true)) = (⊤ : Subgroup (Equiv.Perm (Fin 5))) := by
    ext α
    simp only [Subgroup.mem_top, iff_true]
    exact mem_structAut.2 rfl
  have key := @h (Fin 5) _ _ 5 Unit G G.subtype X hgiant hcan (fun _ => true)
  rw [haut] at key
  -- the right-hand side contains the transposition `(0 1)`
  have hmemR : (Equiv.swap (0 : Fin 5) 1) ∈
      ((⊤ : Subgroup (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) := trivial
  rw [← key] at hmemR
  obtain ⟨τ, -, hτG, hτϕ⟩ := hmemR
  have hodd : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hev : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) = 1 := by
    rw [← hτϕ]
    exact hτG
  rw [hev] at hodd
  exact absurd hodd (by decide)

/-! ### Procedure Align, lines 4–6: the induced coloring of `Ω` and the Chain Rule

> 4. (: Each of our structures has an underlying coloring – possibly trivial :)
>    Let `(Δ₁, …, Δ_k)` be the coloring of `X(x)` (the `Δ_j` are the color classes); so
>    `Γ` is the disjoint union of the `Δ_j`.  This coloring induces a canonical coloring of
>    `Φ = (Γ choose t)` as described in Lemma 7.2.1; let `Φ₁, …, Φ_s` be the color classes.
>    This coloring in turn lifts to a canonical coloring of `Ω` with corresponding color
>    classes `Ω₁, …, Ω_s` where `Ω_i = ⋃_{T ∈ Φ_i} B_T`.  For `A ⊆ Γ` recall the notation
>    `Φ(A) = (A choose t)` and `Ω(A) = ⋃_{T ∈ Φ(A)} B_T`.
> 5. Apply the Chain Rule to the color classes `Ω_i`.
> 6. If `(∃j)(|Δ_j| > m/2)` ("dominant color") then start the application of the Chain Rule
>    with the window `Ω(Δ_j)`. -/

section Lines456

variable {m : ℕ} {κ : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The color vector of a `t`-set is unchanged by a permutation of `Γ` that preserves the
coloring: `tColor c (T^α) = tColor c T` when `c ∘ α = c`. -/
theorem tColor_image {Γ : Type*} (c : Γ → κ) (α : Equiv.Perm Γ) (T : Set Γ)
    (hα : ∀ γ, c (α γ) = c γ) : tColor c (α '' T) = tColor c T := by
  funext i
  rw [tColor, tColor]
  have himg : (α '' T) ∩ {γ | c γ = i} = α '' (T ∩ {γ | c γ = i}) := by
    ext γ
    constructor
    · rintro ⟨⟨δ, hδ, rfl⟩, hci⟩
      refine ⟨δ, ⟨hδ, ?_⟩, rfl⟩
      show c δ = i
      rw [← hα δ]; exact hci
    · rintro ⟨δ, ⟨hδ, hci⟩, rfl⟩
      refine ⟨⟨δ, hδ, rfl⟩, ?_⟩
      show c (α δ) = i
      rw [hα δ]; exact hci
  rw [himg, Set.ncard_image_of_injective _ α.injective]

/-- §14.1, line 4: the coloring of `Ω` induced by a coloring `c` of `Γ` is invariant under
every `σ ∈ G` whose image `σ^ϕ` preserves `c`.

The label of the standard block containing `u` transforms by `ϕ`
(Theorem 10.5.1 (c), Eq. (54)): `T(u^σ) = T(u)^{σ^ϕ}`; so if `σ^ϕ` preserves `c` then the
color vector of the label is unchanged. -/
theorem omegaColor_smul {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G)) (c : Fin m → κ) (σ : G)
    (hσ : ∀ γ, c (ϕ σ γ) = c γ) (u : Ω) :
    omegaColor ϕ c ((σ : Equiv.Perm Ω) u) = omegaColor ϕ c u := by
  have hT : Tpoint ϕ (σ • u) = (ϕ σ) '' (Tpoint ϕ u) := theorem_10_5_1_c_eq54 ϕ hϕ hk u σ
  have hsmul : σ • u = (σ : Equiv.Perm Ω) u := rfl
  rw [omegaColor, omegaColor, ← hsmul, hT, tColor_image c (ϕ σ) _ hσ]

/-- §14.1, line 4.  The color class of the vector `v` in the induced coloring of `Ω`. -/
def omegaClass {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m)) (c : Fin m → κ)
    (v : κ → ℕ) : Set Ω :=
  {u | omegaColor ϕ c u = v}

/-- §14.1, line 4: **the color classes of `Ω` are `G₁`-invariant**, where
`G₁ = ϕ⁻¹(Aut(X(x)))` is the group of line 2 (iv).

Every `σ ∈ G₁` has `σ^ϕ ∈ Aut(X(x))`, hence `σ^ϕ` preserves the underlying coloring
`(X(x)).vcol`, and `Babai.omegaColor_smul` applies. -/
theorem isInvariant_omegaClass {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (hϕ : IsGiantRep ϕ) (hk : VeryLargeK m (maxOrbitLength G))
    {A : Type v} {X : (Ω → A) → ColStruct (Fin m) κ} (x : Ω → A) (v : κ → ℕ) :
    IsInvariant (preimageSubgroup ϕ (structAut (X x))) (omegaClass ϕ (X x).vcol v) := by
  intro τ hτ
  obtain ⟨hτG, hτA⟩ := mem_preimageSubgroup.1 hτ
  have hc : ∀ γ, (X x).vcol (ϕ ⟨τ, hτG⟩ γ) = (X x).vcol γ := by
    intro γ
    have h := congrArg (fun Y : ColStruct (Fin m) κ => Y.vcol (ϕ ⟨τ, hτG⟩ γ))
      (mem_structAut.1 hτA)
    simpa using h.symm
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    show omegaColor ϕ (X x).vcol (τ w) = v
    rw [omegaColor_smul ϕ hϕ hk _ ⟨τ, hτG⟩ hc w]
    exact hw
  · intro hu
    refine ⟨τ⁻¹ u, ?_, by simp⟩
    show omegaColor ϕ (X x).vcol (τ⁻¹ u) = v
    have := omegaColor_smul ϕ hϕ hk (X x).vcol ⟨τ, hτG⟩ hc (τ⁻¹ u)
    rw [show (τ : Equiv.Perm Ω) (τ⁻¹ u) = u from by simp] at this
    rw [← this]
    exact hu

/-- §14.1, line 4: `Ω(Δ)` is the color class of the vector that puts all of `t` on the
color of `Δ`.

For a `t`-set `T`, the color vector of `T` has `v_j = t` exactly when `T ⊆ Δ_j`, which is
the "exceptional" case of Lemma 7.2.1 (a).  Here `Δ_j` is the class of the color `i`. -/
theorem omegaOf_eq_omegaClass {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m))
    (c : Fin m → κ) (i : κ) (u : Ω) :
    (u ∈ omegaOf ϕ {γ | c γ = i}) ↔ omegaColor ϕ c u i = tPoint ϕ u := by
  have hEq : omegaColor ϕ c u i = (Tpoint ϕ u ∩ {γ | c γ = i}).ncard := rfl
  rw [mem_omegaOf, hEq, tPoint]
  constructor
  · intro h
    rw [Set.inter_eq_self_of_subset_left h]
  · intro h
    have heq : Tpoint ϕ u ∩ {γ | c γ = i} = Tpoint ϕ u :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_left (le_of_eq h.symm) (Set.toFinite _)
    rw [← heq]
    exact Set.inter_subset_right

/-! #### The Chain Rule over the color classes (line 5) -/

/-- §14.1, line 5: *"Apply the Chain Rule to the color classes `Ω_i`."*

The named reduction: Luks's Chain Rule (Prop. 11.1.7, `Babai.chainReduction`) run over the
list of windows `Δs`, starting from the whole group.  Line 6 ("start the application of
the Chain Rule with the window `Ω(Δ_j)`") is the choice of the *order* of `Δs`, i.e. of
which window heads the list. -/
noncomputable def alignChainReduction {A : Type v} (N : Subgroup (Equiv.Perm Ω))
    (Δs : List (Set Ω)) (x y : Ω → A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  chainReduction N x y Δs 1 N

/-- The Chain Rule step of line 5 is correct: if the windows are `N`-invariant and cover
`Ω`, the reduction computes `Iso_N(x,y)`. -/
theorem run_alignChainReduction {A : Type v} {N : Subgroup (Equiv.Perm Ω)}
    {Δs : List (Set Ω)} (x y : Ω → A) (hinv : ∀ Δ ∈ Δs, IsInvariant N Δ)
    (hcov : (⋃ Δ ∈ Δs, Δ) = (Set.univ : Set Ω)) :
    (alignChainReduction N Δs x y).run = strIso (N : Set (Equiv.Perm Ω)) x y := by
  have hrun := run_chainReduction (N := N) x y Δs ∅ 1 N hinv (by intro σ _; simp) le_rfl
    (one_mem _) (by rw [wIso_empty, one_smul])
  rw [alignChainReduction, hrun, hcov, Set.empty_union, wIso_univ]

/-- Line 5 makes at most one call per color class. -/
theorem calls_length_alignChainReduction {A : Type v} (N : Subgroup (Equiv.Perm Ω))
    (Δs : List (Set Ω)) (x y : Ω → A) :
    (alignChainReduction N Δs x y).calls.length ≤ Δs.length :=
  (calls_chainReduction N x y Δs 1 N).1

/-- Every call of line 5 has a color class for its window. -/
theorem calls_alignChainReduction_window {A : Type v} (N : Subgroup (Equiv.Perm Ω))
    (Δs : List (Set Ω)) (x y : Ω → A) :
    ∀ I ∈ (alignChainReduction N Δs x y).calls, I.Δ ∈ Δs :=
  (calls_chainReduction N x y Δs 1 N).2

end Lines456

/-! ### Procedure Align, lines 7–11: the reduced set `Γ*`

> 7. While processing window `Ω(Δ_j)`
>    (A) if `X` gives a nontrivial equipartition of `Δ_j` then let `Y` be this equivalence
>        relation on `Δ_j` and `Γ*` the set of blocks
>    (B) if `Δ_j` is the vertex set of a Johnson scheme `J(m*, t*)` (`t* ≥ 2`) then
>        identify `Δ_j` with `Δ_j = (Γ* choose t*)` where `|Γ*| = m*` and let `Y` denote
>        this Johnson scheme on `Δ_j`
> 8. let `H = Aut(Y)` and `ψ : H → S(Γ*)` be the natural epimorphism
> 9. let `G* = ϕ⁻¹(H)`
> 10. let `ϕ* : G* → S(Γ*)` be the composition of `ϕ` restricted to `G*` and `ψ`
>     (: this is a giant representation :)
> 11. update: `G ← G*`, `Γ ← Γ*`, `ϕ ← ϕ*`

`G*` is a subgroup of `G ≤ S(Ω)`, so it acts on all of `Ω`; `ϕ*` is a homomorphism defined
on that group, not on a subset of `Ω`.  The *window* on which the recursion continues is
`Ω(Δ_j)`, which is `G*`-invariant (`Babai.isInvariant_omegaOf_of_le`) because `ϕ(G*) ≤ H`
preserves `Δ_j` setwise and the labels transform by `ϕ` (Eq. (54)). -/

section Lines711

/-- Line 10: `ϕ` restricted to `G* = ϕ⁻¹(H)`, corestricted to `H`. -/
def phiStar (ϕ : G →* Equiv.Perm Γ) (H : Subgroup (Equiv.Perm Γ)) :
    preimageSubgroup ϕ H →* H :=
  MonoidHom.codRestrict (ϕ.comp (Subgroup.inclusion (preimageSubgroup_le ϕ H))) H
    (fun τ => (mem_preimageSubgroup.1 τ.2).choose_spec)

@[simp] theorem coe_phiStar (ϕ : G →* Equiv.Perm Γ) (H : Subgroup (Equiv.Perm Γ))
    (τ : preimageSubgroup ϕ H) :
    ((phiStar ϕ H τ : H) : Equiv.Perm Γ) =
      ϕ ⟨(τ : Equiv.Perm Ω), preimageSubgroup_le ϕ H τ.2⟩ := rfl

/-- §14.1, line 10, the claim **"(: this is a giant representation :)"**.

Hypotheses actually needed: `ϕ` is a giant representation (`A(Γ) ≤ G^ϕ`, the standing
assumption of Sec. 14) and `ψ : H → S(Γ*)` is onto (this is what *"the natural
epimorphism"* asserts; for a nontrivial equipartition `ψ` is the induced action on the
blocks, and for a Johnson scheme `Aut(J(m*,t*)) = S_{m*}^{(t*)}` for `m* ≥ 2t* + 1` — the
cited Prop. 3.2.11, `Babai.aut_johnsonGraph` — whose natural map onto `S(Γ*)` is onto).
No lower bound on `|Γ*|` is needed.

Proof.  Every square of `S(Γ*)` is in the image: for `β = ψ(h)` with `h ∈ H`, the
permutation `h²` of `Γ` is even, so `h² ∈ A(Γ) ≤ G^ϕ`, and `h² ∈ H`; hence `h²` is in the
image of `ϕ*` and `β² = ψ(h²)` is in the image of `ϕ*` composed with `ψ`.  A `3`-cycle `c`
satisfies `c = (c²)²` (its order is `3`), so every `3`-cycle is in the image, and the
`3`-cycles generate `A(Γ*)`. -/
theorem Align_phiStar_isGiant [Fintype Γ] [DecidableEq Γ] {Γ' : Type*} [Fintype Γ']
    [DecidableEq Γ'] (ϕ : G →* Equiv.Perm Γ)
    (hϕ : alternatingGroup Γ ≤ ϕ.range) (H : Subgroup (Equiv.Perm Γ))
    (ψ : H →* Equiv.Perm Γ') (hψ : Function.Surjective ψ) :
    alternatingGroup Γ' ≤ (ψ.comp (phiStar ϕ H)).range := by
  -- every square is in the image
  have hsq : ∀ β : Equiv.Perm Γ', β ^ 2 ∈ (ψ.comp (phiStar ϕ H)).range := by
    intro β
    obtain ⟨h, rfl⟩ := hψ β
    have hev : ((h : Equiv.Perm Γ)) ^ 2 ∈ alternatingGroup Γ := by
      rw [Equiv.Perm.mem_alternatingGroup, map_pow]
      simp
    obtain ⟨g, hg⟩ := hϕ hev
    have hgH : (g : Equiv.Perm Ω) ∈ preimageSubgroup ϕ H := by
      refine mem_preimageSubgroup.2 ⟨g.2, ?_⟩
      rw [show (⟨(g : Equiv.Perm Ω), g.2⟩ : G) = g from rfl, hg]
      exact pow_mem h.2 2
    refine ⟨⟨(g : Equiv.Perm Ω), hgH⟩, ?_⟩
    have hval : phiStar ϕ H ⟨(g : Equiv.Perm Ω), hgH⟩ = h ^ 2 := by
      apply Subtype.ext
      rw [coe_phiStar, show (⟨(g : Equiv.Perm Ω), preimageSubgroup_le ϕ H hgH⟩ : G) = g from rfl,
        hg]
      rw [Subgroup.coe_pow]
    rw [MonoidHom.comp_apply, hval, map_pow]
  -- hence every 3-cycle, hence all of `A(Γ*)`
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro c hc
  have hc3 : Equiv.Perm.IsThreeCycle c := hc
  have hpow : (c ^ 2) ^ 2 = c := by
    have h3 : c ^ 3 = 1 := by
      rw [← hc3.orderOf]; exact pow_orderOf_eq_one c
    calc (c ^ 2) ^ 2 = c ^ 3 * c := by group
      _ = c := by rw [h3, one_mul]
  have := hsq (c ^ 2)
  rwa [hpow] at this

/-- §14.1, lines 7–11: the window `Ω(Δ)` on which the recursion continues is
`G*`-invariant, for any subgroup `G*` of `G` whose image under `ϕ` preserves `Δ` setwise
(in particular for `G* = ϕ⁻¹(H)` with `H = Aut(Y) ≤ (S(Γ))_Δ`).

This is the precise sense in which `ϕ*` "processes the window `Ω(Δ_j)`": the group `G*`
acts on all of `Ω`, and `Ω(Δ)` is one of its invariant subsets. -/
theorem isInvariant_omegaOf_of_le [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    {G : Subgroup (Equiv.Perm Ω)} (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (Δ : Set (Fin m))
    (Gs : Subgroup (Equiv.Perm Ω)) (hle : Gs ≤ G)
    (hstab : ∀ τ : Equiv.Perm Ω, ∀ h : τ ∈ Gs, (ϕ ⟨τ, hle h⟩) '' Δ = Δ) :
    IsInvariant Gs (omegaOf ϕ Δ) := by
  intro τ hτ
  have hT : ∀ u : Ω, Tpoint ϕ ((τ : Equiv.Perm Ω) u) = (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ u) :=
    fun u => theorem_10_5_1_c_eq54 ϕ hϕ hk u ⟨τ, hle hτ⟩
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    show Tpoint ϕ (τ w) ⊆ Δ
    rw [hT w, ← hstab τ hτ]
    exact Set.image_mono hw
  · intro hu
    refine ⟨τ⁻¹ u, ?_, by simp⟩
    show Tpoint ϕ (τ⁻¹ u) ⊆ Δ
    have h1 := hT (τ⁻¹ u)
    rw [show (τ : Equiv.Perm Ω) (τ⁻¹ u) = u from by simp] at h1
    have h2 : (ϕ ⟨τ, hle hτ⟩) '' (Tpoint ϕ (τ⁻¹ u)) ⊆ Δ := by rw [← h1]; exact hu
    rw [← hstab τ hτ] at h2
    exact fun a ha => by
      have := h2 ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := this
      rwa [(ϕ ⟨τ, hle hτ⟩).injective hba] at hb

end Lines711

/-! ### §14.2 Cost analysis

> We are assuming that isomorphism of our canonical structures `X` is testable in
> polynomial time …, so Line 2 is executed in polynomial (in `m`) time. …
> In analyzing the complexity, we need to take into account the potentially
> quasipolynomial (in terms of `m`), say `q(m)`, multiplicative cost of reaching our
> canonical structures `X`. … So the overall cost, including the application of the Chain
> rule, will be `T(G,ϕ) ≤ q(m) ∑_i T(|Ω_i|)`.  (71)

The running-time content of Sec. 14.2 is
covered inside the RAM proof of Theorem 1.1.1 (`Algo.theorem_1_1_1`) and not stated as a
separate RAM theorem.  What is stated here is the mathematics:
the
two size estimates for the reduced set `Γ*` and the two inequalities (72), (73) as
statements about an abstract cost function. -/

section Cost

/-- §14.2: *"In the case of an equipartition, `Γ'` is the set of blocks of the partition,
so `|Γ'| ≤ m/2`."*

A nontrivial equipartition of `Δ` into `nb` blocks of common size `b ≥ 2` has
`nb · b = |Δ|`, hence `2·nb ≤ |Δ|`.  (Stated without division; with `|Δ| ≤ m` this is
`|Γ'| ≤ m/2`.) -/
theorem Align_equipartition_card {b nb d : ℕ} (hb : 2 ≤ b) (h : nb * b = d) :
    2 * nb ≤ d := by
  calc 2 * nb = nb * 2 := by ring
    _ ≤ nb * b := Nat.mul_le_mul_left _ hb
    _ = d := h

/-- §14.2, the Johnson case, first step: `(m* − 1)² < 2·|Δ|`.

*"In case of a Johnson scheme `J(m', t')` (`t' ≥ 2`) with vertex set `Δ_j = (Γ' choose t')`
we have `m ≥ |Δ_j| = C(m', t') ≥ C(m', 2) > (m' − 1)²/2`."*

The middle inequality `C(m', t') ≥ C(m', 2)` holds because `2 ≤ t' ≤ m'/2`, which follows
from the parameter constraints `t' ≥ 2` and `m' ≥ 2t' + 1` of Def. 3.2.9. -/
theorem Align_johnson_sq_lt {ms ts : ℕ} (h2 : 2 ≤ ts) (hp : 2 * ts + 1 ≤ ms) :
    (ms - 1) ^ 2 < 2 * ms.choose ts := by
  have hmono : ∀ r : ℕ, 2 ≤ r → r ≤ ts → ms.choose 2 ≤ ms.choose r := by
    intro r
    induction r with
    | zero => intro h _; omega
    | succ n ih =>
      intro _ hrt
      rcases Nat.lt_or_ge n 2 with hn | hn
      · have hn1 : n + 1 = 2 := by omega
        rw [hn1]
      · exact le_trans (ih hn (by omega)) (Nat.choose_le_succ_of_lt_half_left (by omega))
  have hchoose : ms.choose 2 ≤ ms.choose ts := hmono ts h2 le_rfl
  have hdvd : 2 ∣ ms * (ms - 1) := (Nat.even_mul_pred_self ms).two_dvd
  have h2c : 2 * ms.choose 2 = ms * (ms - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' hdvd]
  obtain ⟨r, hrms⟩ : ∃ r, ms = r + 1 := ⟨ms - 1, by omega⟩
  have hsub : ms - 1 = r := by omega
  have hrpos : 0 < r := by omega
  have hsq : (ms - 1) ^ 2 < ms * (ms - 1) := by
    rw [hsub, hrms]
    nlinarith
  calc (ms - 1) ^ 2 < ms * (ms - 1) := hsq
    _ = 2 * ms.choose 2 := h2c.symm
    _ ≤ 2 * ms.choose ts := Nat.mul_le_mul_left _ hchoose

/-- §14.2, the Johnson case: *"so `m' < 1 + √(2m) < m/2` (for `m ≥ 12`)"*.

Stated without square roots: if `(m* − 1)² < 2m` and `m ≥ 12` then `2m* < m`.  The
threshold `12` is sharp: the real inequality `1 + √(2m) < m/2` is `m² − 12m + 4 > 0`, which
fails at `m = 11` and holds at `m = 12`. -/
theorem Align_johnson_card {ms m : ℕ} (hm : 12 ≤ m) (h : (ms - 1) ^ 2 < 2 * m) :
    2 * ms < m := by
  by_contra hcon
  push_neg at hcon
  have hms1 : 1 ≤ ms := by omega
  set r := ms - 1 with hr
  have hmsr : ms = r + 1 := by omega
  have hle : m ≤ 2 * r + 2 := by omega
  have hrsq : r ^ 2 < 4 * r + 4 := by omega
  have hr5 : r ≤ 4 := by
    by_contra hc
    push_neg at hc
    nlinarith
  omega

/-! #### Superadditive cost functions

Both Eq. (72) and Eq. (73) compare a **sum** of values of `T` with a single value of `T`.
Neither step follows from Eq. (71) and monotonicity alone: the color classes of
`Φ = (Γ choose t)` are indexed by the color vectors of Lemma 7.2.1 and there can be many
more than `m` of them.  What makes both steps true is that `T` is *superadditive*,
`T(a) + T(b) ≤ T(a+b)`, which is part of what the paper asks of a "nice" function.  See
the corrected paper. -/

/-- A function superadditive on `[1, ∞)` satisfies `∑_{x ∈ L} T(x) ≤ T(∑_{x ∈ L} x)` for a list
of reals that are all at least `1` (the empty list uses `0 ≤ T(0)`). -/
theorem sum_map_le_of_superadditive {Tc : ℝ → ℝ}
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b)) (hT0 : 0 ≤ Tc 0) :
    ∀ L : List ℝ, (∀ x ∈ L, 1 ≤ x) → (L.map Tc).sum ≤ Tc L.sum := by
  intro L
  induction L with
  | nil => intro _; simpa using hT0
  | cons x L ih =>
    intro hL
    have hx : 1 ≤ x := hL x List.mem_cons_self
    have hLpos : ∀ y ∈ L, 1 ≤ y := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rcases L with _ | ⟨y, L'⟩
    · simp
    · have hLsum : 1 ≤ (y :: L').sum := by
        rw [List.sum_cons]
        have := List.sum_nonneg (fun z hz => le_trans zero_le_one
          (hLpos z (List.mem_cons_of_mem _ hz)))
        linarith [hLpos y List.mem_cons_self]
      calc ((x :: y :: L').map Tc).sum = Tc x + ((y :: L').map Tc).sum := by simp
        _ ≤ Tc x + Tc (y :: L').sum := by linarith [ih hLpos]
        _ ≤ Tc (x + (y :: L').sum) := hsuper x _ hx hLsum
        _ = Tc (x :: y :: L').sum := by simp

/-- The split used for Eq. (72): a list of nonnegative reals is `P ++ R` where `P` is a
prefix of sum at most `c` and, if `R` is not empty, adding its first entry already
overshoots `c`. -/
theorem exists_maximal_prefix {c : ℝ} :
    ∀ (L : List ℝ) (s : ℝ), (∀ x ∈ L, 0 ≤ x) → s ≤ c →
      ∃ P R : List ℝ, L = P ++ R ∧ s + P.sum ≤ c ∧
        (R = [] ∨ ∃ (a : ℝ) (R' : List ℝ), R = a :: R' ∧ c < s + P.sum + a) := by
  intro L
  induction L with
  | nil => intro s _ hs; exact ⟨[], [], rfl, by simpa using hs, Or.inl rfl⟩
  | cons x L ih =>
    intro s hL hs
    by_cases hx : c < s + x
    · exact ⟨[], x :: L, rfl, by simpa using hs, Or.inr ⟨x, L, rfl, by simpa using hx⟩⟩
    · push_neg at hx
      obtain ⟨P, R, hPR, hsum, hrest⟩ :=
        ih (s + x) (fun y hy => hL y (List.mem_cons_of_mem _ hy)) hx
      refine ⟨x :: P, R, by rw [List.cons_append, hPR], by rw [List.sum_cons]; linarith, ?_⟩
      rcases hrest with h | ⟨a, R', hR, ha⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, R', hR, by rw [List.sum_cons]; linarith⟩

/-- **The three-bin bound.**  If the sizes `a_i ≥ 0` add up to at most `n`, each is at most
`c`, and `n ≤ 2c`, then `∑ T(a_i) ≤ 3 T(c)` for a monotone, superadditive, nonnegative `T`.

This is the paper's "generously" in Eq. (72), where `c = 2n/3` (so `n ≤ 2c` holds).  The
proof is the first-fit argument in the form of three explicit groups: a maximal prefix `P`
(sum at most `c`), the next single item `a` (at most `c` by hypothesis), and the rest,
whose sum is below `n − c ≤ c` because `P`'s sum plus `a` already exceeds `c`. -/
theorem sum_map_le_three_mul {Tc : ℝ → ℝ} {c n : ℝ}
    (hmono : Monotone Tc)
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b))
    (hTnn : ∀ a : ℝ, 0 ≤ Tc a) (hc : 0 ≤ c) (hn : n ≤ 2 * c)
    (L : List ℝ) (hpos : ∀ x ∈ L, 1 ≤ x) (hle : ∀ x ∈ L, x ≤ c) (hsum : L.sum ≤ n) :
    (L.map Tc).sum ≤ 3 * Tc c := by
  have hT0 : 0 ≤ Tc 0 := hTnn 0
  obtain ⟨P, R, hPR, hPsum, hrest⟩ := exists_maximal_prefix L 0
    (fun x hx => le_trans zero_le_one (hpos x hx)) hc
  have hPpos : ∀ x ∈ P, 1 ≤ x := fun x hx => hpos x (by rw [hPR]; exact List.mem_append_left _ hx)
  have hRpos : ∀ x ∈ R, 1 ≤ x := fun x hx => hpos x (by rw [hPR]; exact List.mem_append_right _ hx)
  have hP : (P.map Tc).sum ≤ Tc c :=
    le_trans (sum_map_le_of_superadditive hsuper hT0 P hPpos) (hmono (by linarith))
  rcases hrest with hR | ⟨a, R', hR, ha⟩
  · subst hR
    have : L = P := by rw [hPR]; simp
    subst this
    linarith [hTnn c]
  · subst hR
    have hamem : a ∈ L := by rw [hPR]; exact List.mem_append_right _ List.mem_cons_self
    have hR'pos : ∀ x ∈ R', 1 ≤ x := fun x hx =>
      hRpos x (List.mem_cons_of_mem _ hx)
    have hsplit : L.sum = P.sum + (a + R'.sum) := by rw [hPR, List.sum_append, List.sum_cons]
    have hR'sum : R'.sum ≤ c := by
      have h1 : R'.sum ≤ n - (P.sum + a) := by rw [hsplit] at hsum; linarith
      linarith
    have hR' : (R'.map Tc).sum ≤ Tc c :=
      le_trans (sum_map_le_of_superadditive hsuper hT0 R' hR'pos) (hmono hR'sum)
    have hTa : Tc a ≤ Tc c := hmono (hle a hamem)
    have hLmap : (L.map Tc).sum = (P.map Tc).sum + (Tc a + (R'.map Tc).sum) := by
      rw [hPR]; simp
    rw [hLmap]
    linarith

/-- The same bound for a family indexed by `Fin s`. -/
theorem sum_le_three_mul {Tc : ℝ → ℝ} {c n : ℝ} {s : ℕ} {sizes : Fin s → ℝ}
    (hmono : Monotone Tc)
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b))
    (hTnn : ∀ a : ℝ, 0 ≤ Tc a) (hc : 0 ≤ c) (hn : n ≤ 2 * c)
    (hpos : ∀ i, 1 ≤ sizes i) (hle : ∀ i, sizes i ≤ c) (hsum : ∑ i, sizes i ≤ n) :
    ∑ i, Tc (sizes i) ≤ 3 * Tc c := by
  have hofn : (List.ofFn sizes).sum = ∑ i, sizes i := List.sum_ofFn
  have hmap : ((List.ofFn sizes).map Tc).sum = ∑ i, Tc (sizes i) := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  have hmem : ∀ x ∈ List.ofFn sizes, ∃ i, sizes i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.1 hx
    exact ⟨i, hi⟩
  rw [← hmap]
  refine sum_map_le_three_mul hmono hsuper hTnn hc hn _ ?_ ?_ (by rw [hofn]; exact hsum)
  · intro x hx; obtain ⟨i, rfl⟩ := hmem x hx; exact hpos i
  · intro x hx; obtain ⟨i, rfl⟩ := hmem x hx; exact hle i

/-- The "small classes" bound used for Eq. (73): if the sizes add up to at most `d`, their
terms add up to at most `T(d)`. -/
theorem sum_le_of_sum_le {Tc : ℝ → ℝ} {d : ℝ} {s : ℕ} {sizes : Fin s → ℝ}
    (hmono : Monotone Tc)
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b))
    (hTnn : ∀ a : ℝ, 0 ≤ Tc a)
    (hpos : ∀ i, 1 ≤ sizes i) (hsum : ∑ i, sizes i ≤ d) :
    ∑ i, Tc (sizes i) ≤ Tc d := by
  have hofn : (List.ofFn sizes).sum = ∑ i, sizes i := List.sum_ofFn
  have hmap : ((List.ofFn sizes).map Tc).sum = ∑ i, Tc (sizes i) := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  have hpos' : ∀ x ∈ List.ofFn sizes, 1 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hpos i
  rw [← hmap]
  refine le_trans (sum_map_le_of_superadditive hsuper (hTnn 0) _ hpos') (hmono ?_)
  rw [hofn]; exact hsum

/-- §14.2, **Eq. (72)**.

> If `(∀i)(|Ω_i| ≤ 2n/3)` then this yields (generously) the inequality
> `T(G,ϕ) ≤ m · q(m) · T(2n/3)`  (72)
> justifying Inequality (65).

Stated as an inequality about an abstract cost function `T` (as in
`Workspace/Luks/Cost.lean`, where the recurrences of Sec. 11.4 are resolved): from
Eq. (71), `T(G,ϕ) ≤ q(m) ∑_{i<s} T(|Ω_i|)`, and the three-bin bound
`∑_i T(|Ω_i|) ≤ 3 T(2n/3) ≤ m T(2n/3)` for `m ≥ 3`
(`Babai.sum_le_three_mul`).

The step needs no bound on the *number* `s` of color classes — there is none available,
since the classes are indexed by the color vectors of Lemma 7.2.1.  What it needs is that
`T` is monotone and **superadditive** on the range of the sizes: the classes `Ω_i` are
nonempty, so every size is at least `1`, and superadditivity is asked only on `[1, ∞)`.
See `Babai.superadditive_mul_expLogPow` for the paper's quasipolynomial bounds, and
the corrected paper. -/
theorem cost_72 {Tc : ℝ → ℝ} {cost : ℝ} {s : ℕ} {m qm n : ℝ} {sizes : Fin s → ℝ}
    (hmono : Monotone Tc)
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b))
    (hTnn : ∀ a : ℝ, 0 ≤ Tc a) (hq : 0 ≤ qm) (hn : 0 ≤ n)
    (h71 : cost ≤ qm * ∑ i, Tc (sizes i))
    (hpos : ∀ i, 1 ≤ sizes i) (hbound : ∀ i, sizes i ≤ 2 * n / 3)
    (hsum : ∑ i, sizes i ≤ n) (hm3 : 3 ≤ m) :
    cost ≤ m * qm * Tc (2 * n / 3) := by
  have hc : (0 : ℝ) ≤ 2 * n / 3 := by linarith
  have hn2 : n ≤ 2 * (2 * n / 3) := by linarith
  have h3 : ∑ i, Tc (sizes i) ≤ 3 * Tc (2 * n / 3) :=
    sum_le_three_mul hmono hsuper hTnn hc hn2 hpos hbound hsum
  have hTc : 0 ≤ Tc (2 * n / 3) := hTnn _
  calc cost ≤ qm * ∑ i, Tc (sizes i) := h71
    _ ≤ qm * (3 * Tc (2 * n / 3)) := mul_le_mul_of_nonneg_left h3 hq
    _ ≤ qm * (m * Tc (2 * n / 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm3 hTc) hq
    _ = m * qm * Tc (2 * n / 3) := by ring

/-- §14.2, **Eq. (73)**.

> If `(∃i)(|Ω_i| > 2n/3)` then by Lemma 7.2.1, for this `i = i₀` we must have
> `Ω_{i₀} = Ω(Δ_j)` where `|Δ_j| > 2m/3`.  The total contribution of all other `Ω_i` to the
> right-hand side of Eq. (71) is at most `q(m)T(n/3)`. … So in each case we obtain the
> inequality `T(G,ϕ) ≤ q(m)(T(n/3) + T_Jh(n, m/2))`  (73)
> justifying Eq. (v) in Sec. 11.4.

The exceptional class contributes `T_Jh(n, m/2)` — the recursive call on the window
`Ω(Δ_j)` with the reduced `Γ*`, whose size is at most `m/2` by
`Babai.Align_equipartition_card` and `Babai.Align_johnson_card`.  The remaining classes
have total size at most `n/3` (their union is the complement of `Ω_{i₀}`, which has more
than `2n/3` points), and superadditivity turns the sum of their terms into the single term
`T(n/3)` (`Babai.sum_le_of_sum_le`) — again, no bound on their *number* is available or
needed.  As in `Babai.cost_72`, the classes are nonempty and superadditivity is asked only
on `[1, ∞)`.  See the corrected paper. -/
theorem cost_73 {Tc : ℝ → ℝ} {qm cost exc n TJh : ℝ} {s : ℕ} {sizes : Fin s → ℝ}
    (hmono : Monotone Tc)
    (hsuper : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → Tc a + Tc b ≤ Tc (a + b))
    (hTnn : ∀ a : ℝ, 0 ≤ Tc a) (hq : 0 ≤ qm)
    (h71 : cost ≤ qm * ((∑ i, Tc (sizes i)) + exc))
    (hpos : ∀ i, 1 ≤ sizes i) (hsum : ∑ i, sizes i ≤ n / 3) (hexc : exc ≤ TJh) :
    cost ≤ qm * (Tc (n / 3) + TJh) := by
  have hrest : ∑ i, Tc (sizes i) ≤ Tc (n / 3) :=
    sum_le_of_sum_le hmono hsuper hTnn hpos hsum
  exact le_trans h71 (mul_le_mul_of_nonneg_left (add_le_add hrest hexc) hq)

/-! #### The paper's "nice" functions are superadditive

> In fact, for "nice" functions as postulated …

The cost functions the paper uses are `T(x) = exp((log x)^c)` with `c ≥ 1` (the
quasipolynomial functions of Sec. 11.4).  For these the ratio `T(x)/x` is nondecreasing on
`x ≥ e`, and a function with nondecreasing `T(x)/x` is superadditive there.  The range is
stated honestly: superadditivity is proved here for arguments `≥ e`; the range `[1, ∞)` that
Eqs. (72)–(73) use is treated at the end of this section. -/

/-- A function whose ratio `T(x)/x` is nondecreasing on `[x₀, ∞)` (with `x₀ > 0`) is
superadditive there: `T(a) ≤ T(a+b)·a/(a+b)` and `T(b) ≤ T(a+b)·b/(a+b)` add up to
`T(a) + T(b) ≤ T(a+b)`. -/
theorem superadditive_of_ratio_monotone {Tc : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hratio : ∀ x y : ℝ, x₀ ≤ x → x ≤ y → Tc x / x ≤ Tc y / y)
    {a b : ℝ} (ha : x₀ ≤ a) (hb : x₀ ≤ b) : Tc a + Tc b ≤ Tc (a + b) := by
  have hapos : 0 < a := lt_of_lt_of_le hx₀ ha
  have hbpos : 0 < b := lt_of_lt_of_le hx₀ hb
  have hab : 0 < a + b := by linarith
  have h1 : Tc a / a ≤ Tc (a + b) / (a + b) := hratio a (a + b) ha (by linarith)
  have h2 : Tc b / b ≤ Tc (a + b) / (a + b) := hratio b (a + b) hb (by linarith)
  have h1' : Tc a ≤ Tc (a + b) / (a + b) * a := by
    have := mul_le_mul_of_nonneg_right h1 hapos.le
    rwa [div_mul_cancel₀ _ hapos.ne'] at this
  have h2' : Tc b ≤ Tc (a + b) / (a + b) * b := by
    have := mul_le_mul_of_nonneg_right h2 hbpos.le
    rwa [div_mul_cancel₀ _ hbpos.ne'] at this
  have hsum : Tc (a + b) / (a + b) * a + Tc (a + b) / (a + b) * b = Tc (a + b) := by
    field_simp
  linarith

/-- For `u ≥ 1` and `c ≥ 1` the function `u ↦ u^c − u` is nondecreasing:
`v^c − u^c ≥ v·u^{c−1} − u·u^{c−1} = (v−u)u^{c−1} ≥ v − u`. -/
theorem sub_rpow_monotone {c u v : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (huv : u ≤ v) :
    u ^ c - u ≤ v ^ c - v := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hupos huv
  have hue : u ^ c = u * u ^ (c - 1) := by
    rw [← Real.rpow_one_add' hupos.le (by linarith)]
    norm_num
  have hve : v ^ c = v * v ^ (c - 1) := by
    rw [← Real.rpow_one_add' hvpos.le (by linarith)]
    norm_num
  have hpow : u ^ (c - 1) ≤ v ^ (c - 1) :=
    Real.rpow_le_rpow hupos.le huv (by linarith)
  have hone : (1 : ℝ) ≤ u ^ (c - 1) := Real.one_le_rpow hu (by linarith)
  have hstep : v * u ^ (c - 1) ≤ v ^ c := by
    rw [hve]; exact mul_le_mul_of_nonneg_left hpow hvpos.le
  nlinarith [hstep, hue, hone, sub_nonneg.2 huv]

/-- For `c ≥ 1`, the function `T(x) = exp((log x)^c)` has `T(x)/x` nondecreasing on
`x ≥ e`: `T(x)/x = exp((log x)^c − log x)` and `u ↦ u^c − u` is nondecreasing for
`u = log x ≥ 1` (`Babai.sub_rpow_monotone`). -/
theorem ratio_monotone_expLogPow {c : ℝ} (hc : 1 ≤ c) {x y : ℝ}
    (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    Real.exp ((Real.log x) ^ c) / x ≤ Real.exp ((Real.log y) ^ c) / y := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hlx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hly : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  have hxe : x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
  have hye : y = Real.exp (Real.log y) := (Real.exp_log hypos).symm
  have key : Real.exp ((Real.log x) ^ c - Real.log x) ≤
      Real.exp ((Real.log y) ^ c - Real.log y) :=
    Real.exp_le_exp.2 (sub_rpow_monotone hc hlx hly)
  calc Real.exp ((Real.log x) ^ c) / x
      = Real.exp ((Real.log x) ^ c - Real.log x) := by
        rw [Real.exp_sub]; congr 1
    _ ≤ Real.exp ((Real.log y) ^ c - Real.log y) := key
    _ = Real.exp ((Real.log y) ^ c) / y := by
        rw [Real.exp_sub]; congr 1
        exact hye.symm

/-- The conclusion: for `c ≥ 1` the quasipolynomial cost function `T(x) = exp((log x)^c)`
is superadditive on `[e, ∞)`.  (`Babai.cost_72` and `Babai.cost_73` ask for `[1, ∞)`; see
`Babai.superadditive_mul_expLogPow` for a bound of the same form that has it.) -/
theorem superadditive_expLogPow {c : ℝ} (hc : 1 ≤ c) {a b : ℝ}
    (ha : Real.exp 1 ≤ a) (hb : Real.exp 1 ≤ b) :
    Real.exp ((Real.log a) ^ c) + Real.exp ((Real.log b) ^ c) ≤
      Real.exp ((Real.log (a + b)) ^ c) :=
  superadditive_of_ratio_monotone (Real.exp_pos 1)
    (fun _ _ hx hxy => ratio_monotone_expLogPow hc hx hxy) ha hb

/-! #### Superadditivity on the range used

The classes `Ω_i` of Eq. (71) are nonempty, so `cost_72` and `cost_73` ask for
superadditivity on `[1, ∞)` only.  The bare function `exp((log x)^c)` is not superadditive
there (`Babai.not_superadditive_expLogPow`: `T(1) + T(1) = 2 > T(2)`), but the paper only asks
of its bound `T₁` that it be "nice" for sufficiently large `x` and absorbs bounded terms (Sec.
11.4).  The bound `x · exp((log x)^c)` has the same quasipolynomial form, lies above
`exp((log x)^c)`, and is superadditive on all of `[1, ∞)`. -/

/-- For `c > 1` the function `exp((log x)^c)` is not superadditive on `[1, ∞)`:
`T(1) + T(1) = 2 > exp((log 2)^c) = T(2)`, since `0 < log 2 < 1`. -/
theorem not_superadditive_expLogPow {c : ℝ} (hc : 1 < c) :
    Real.exp ((Real.log (1 + 1)) ^ c) <
      Real.exp ((Real.log 1) ^ c) + Real.exp ((Real.log 1) ^ c) := by
  have h2 : Real.log (1 + 1) = Real.log 2 := by norm_num
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have hpow : Real.log 2 ^ c < Real.log 2 := by
    have := Real.rpow_lt_rpow_of_exponent_gt hpos hlt1 hc
    simpa using this
  rw [h2, Real.log_one, Real.zero_rpow (by linarith), Real.exp_zero]
  calc Real.exp (Real.log 2 ^ c) < Real.exp (Real.log 2) := Real.exp_lt_exp.2 hpow
    _ = 2 := Real.exp_log (by norm_num)
    _ = 1 + 1 := by norm_num

/-- For `c ≥ 0` the bound `T(x) = x · exp((log x)^c)` is superadditive on `[1, ∞)`: its ratio
`T(x)/x = exp((log x)^c)` is nondecreasing there (`Babai.superadditive_of_ratio_monotone`). -/
theorem superadditive_mul_expLogPow {c : ℝ} (hc : 0 ≤ c) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * Real.exp ((Real.log a) ^ c) + b * Real.exp ((Real.log b) ^ c) ≤
      (a + b) * Real.exp ((Real.log (a + b)) ^ c) := by
  refine superadditive_of_ratio_monotone (Tc := fun x => x * Real.exp ((Real.log x) ^ c))
    zero_lt_one (fun x y hx hxy => ?_) ha hb
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  simp only [mul_div_cancel_left₀ _ hxpos.ne', mul_div_cancel_left₀ _ hypos.ne']
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow (Real.log_nonneg hx)
    (Real.log_le_log hxpos hxy) hc)

/-- The bound `x · exp((log x)^c)` lies above `exp((log x)^c)` for `x ≥ 1`. -/
theorem expLogPow_le_mul {c x : ℝ} (hx : 1 ≤ x) :
    Real.exp ((Real.log x) ^ c) ≤ x * Real.exp ((Real.log x) ^ c) :=
  le_mul_of_one_le_left (Real.exp_pos _).le hx

end Cost

end Babai
