/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 14.2 and Section 6: the multiplicative cost of reaching a canonical structure,
as a reduction of String Isomorphism.
-/
import Workspace.Canonical.Align

/-!
# The multiplicative-cost bridge

Steps 4c, 6a of the Master Algorithm (Sec. 15) and case 2b of Theorem 13.2.1 produce a
canonical structure on `Γ` only *after individualization*.  What is canonical is therefore
not a single structure `X(z)` but a finite **tuple** of "versions" of it (Sec. 6,
Definitions 6.0.1–6.0.7; `Workspace/Functors/Cost.lean`), and Sec. 14.2 says what the
algorithm does with that:

> In analyzing the complexity, we need to take into account the potentially
> quasipolynomial (in terms of `m`), say `q(m)`, multiplicative cost of reaching our
> canonical structures `X`: we need to compare not one but `q(m)` instances of `X(y)` with
> `X(x)`.

This file states and proves that step as an identity about **strings**, which is the form
the recursion of Sec. 15 uses.  Fix a giant representation `ϕ : G → S(Γ)` and an assignment
`z ↦ Vers z` of a set of structures on `Γ` to strings on `Ω`, canonical in the sense of
`Workspace/Canonical/Defs.lean`, i.e. `Vers(z^σ) = Vers(z)^{σ^ϕ}`
(`Babai.IsCanonicalVersions`).  Fix one version `X' ∈ Vers x`.  Then

* `Babai.strIso_eq_iUnion_versionPiece` — **Eq. (40) of Prop. 6.0.4 for strings**:
  `Iso_G(x,y) = ⋃_{Y' ∈ Vers y} Iso_G^{X' ↦ Y'}(x,y)`, where
  `Iso_G^{X' ↦ Y'}(x,y) = {τ ∈ Iso_G(x,y) | X'^{τ^ϕ} = Y'}` (`Babai.versionPiece`).
  The union is over the versions of `y` only; `X'` is fixed.
* `Babai.versionPiece_eq_smul` — **each piece is one call of Procedure Align**: if
  `σ ∈ G` has `X'^{σ^ϕ} = Y'` then
  `Iso_G^{X' ↦ Y'}(x,y) = Iso_{G₁}(x, y^{σ⁻¹})σ` with `G₁ = ϕ⁻¹(Aut(X'))`, which is
  Eq. (70) of Sec. 14.1 for the individualized pair;
  `Babai.versionPiece_eq_empty` — and if there is no such `σ`, the piece is empty (this is
  the rejection of Align line 1).
* `Babai.versionsReduction` — the **named reduction** that runs one sub-reduction per
  version of `y` and takes the union of the answers, with
  `Babai.run_versionsReduction` (its value is `Iso_G(x,y)`) and
  `Babai.calls_length_versionsReduction` (its number of calls is at most `q(m)` times the
  number of calls of one branch), which is the multiplicative cost of Eq. (71).

The *running time* is not modelled here; see the Sec. 15 entry in the corrected paper.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type u} {A : Type v} {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳]
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### Canonical tuples of structures -/

/-- §6, Definitions 6.0.3 and 6.0.7 in the form Sec. 14.2 uses them: an assignment of a
**set** of structures on `Γ` (the "versions" of the canonical structure, one per
individualization) to each string, canonical with respect to `ϕ`.

This is `Babai.IsCanonicalStructure` with a set-valued `X`: a `G`-shift of the string
shifts the whole tuple by the corresponding permutation of `Γ`. -/
def IsCanonicalVersions (ϕ : G →* Equiv.Perm Γ) (Vers : (Ω → A) → Set 𝒳) : Prop :=
  ∀ (z : Ω → A) (σ : G), Vers (strAct z (σ : Equiv.Perm Ω)) = (ϕ σ) • Vers z

/-- A single canonical structure is the special case of a one-element tuple. -/
theorem isCanonicalVersions_singleton {ϕ : G →* Equiv.Perm Γ} {X : (Ω → A) → 𝒳}
    (hcan : IsCanonicalStructure ϕ X) :
    IsCanonicalVersions ϕ (fun z => ({X z} : Set 𝒳)) := by
  intro z σ
  show ({X (strAct z (σ : Equiv.Perm Ω))} : Set 𝒳) = (ϕ σ) • ({X z} : Set 𝒳)
  rw [hcan z σ, Set.smul_set_singleton]

/-! ### The pieces of `Iso_G(x,y)` -/

/-- The part of `Iso_G(x,y)` that carries the fixed version `X'` of `x` to the version `Y'`
of `y`.  (Prop. 6.0.4 writes it `F⁻¹(Iso(X',Y'))`.) -/
def versionPiece (ϕ : G →* Equiv.Perm Γ) (x y : Ω → A) (X' Y' : 𝒳) :
    Set (Equiv.Perm Ω) :=
  {τ ∈ strIso (G : Set (Equiv.Perm Ω)) x y |
    ∃ h : τ ∈ G, (ϕ ⟨τ, h⟩) • X' = Y'}

theorem versionPiece_subset (ϕ : G →* Equiv.Perm Γ) (x y : Ω → A) (X' Y' : 𝒳) :
    versionPiece ϕ x y X' Y' ⊆ strIso (G : Set (Equiv.Perm Ω)) x y := fun _ h => h.1

/-- §6, **Proposition 6.0.4, Eq. (40)**, for strings:

> If `F` is a reduction of `Iso(X,Y)` to `D` as above then for any `X' ∈ F(X)` we have
> `Iso(X,Y) = ⋃ {F⁻¹(Iso(X',Y')) | Y' ∈ F(Y)}`.  (Note that `X'` is fixed in this union and
> is chosen arbitrarily from `F(X)`.)

*Proof.*  `⊇` is `Babai.versionPiece_subset`.  For `⊆`, let `τ ∈ Iso_G(x,y)`.  Canonicity
gives `Vers y = Vers (x^τ) = (Vers x)^{τ^ϕ}`, so `X'^{τ^ϕ} ∈ Vers y`, and `τ` lies in the
piece belonging to `Y' = X'^{τ^ϕ}`. -/
theorem strIso_eq_iUnion_versionPiece {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (x y : Ω → A) {X' : 𝒳} (hX' : X' ∈ Vers x) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      ⋃ Y' ∈ Vers y, versionPiece ϕ x y X' Y' := by
  refine Set.Subset.antisymm ?_ ?_
  · intro τ hτ
    obtain ⟨hτG, hτxy⟩ := hτ
    have hVy : Vers y = (ϕ ⟨τ, hτG⟩) • Vers x := by
      rw [← hτxy]; exact hcan x ⟨τ, hτG⟩
    refine Set.mem_iUnion₂.2 ⟨(ϕ ⟨τ, hτG⟩) • X', ?_, ⟨⟨hτG, hτxy⟩, hτG, rfl⟩⟩
    rw [hVy]
    exact ⟨X', hX', rfl⟩
  · exact Set.iUnion₂_subset fun Y' _ => versionPiece_subset ϕ x y X' Y'

/-- §14.1, **Eq. (70)** for an individualized pair of versions: if `σ ∈ G` carries the fixed
version `X'` of `x` to the version `Y'` of `y`, then

  `Iso_G^{X' ↦ Y'}(x,y) = Iso_{G₁}(x, y^{σ⁻¹})σ`,  `G₁ = ϕ⁻¹(Aut(X'))`.

(The paper's right coset `Kσ` is Lean's left translate `σ • K`.)

*Proof.*  By the shift identity Eq. (57), `τ ∈ Iso_G(x,y)` iff `τ = σρ` with
`ρ ∈ Iso_G(x, y^{σ⁻¹})`, and then `X'^{τ^ϕ} = (X'^{ρ^ϕ})^{σ^ϕ}`, so `X'^{τ^ϕ} = Y' =
X'^{σ^ϕ}` iff `X'^{ρ^ϕ} = X'`, i.e. iff `ρ ∈ G₁`. -/
theorem versionPiece_eq_smul {ϕ : G →* Equiv.Perm Γ} (x y : Ω → A) (X' Y' : 𝒳) (σ : G)
    (hσ : (ϕ σ) • X' = Y') :
    versionPiece ϕ x y X' Y' =
      (σ : Equiv.Perm Ω) •
        strIso ((preimageSubgroup ϕ (structAut X') : Subgroup (Equiv.Perm Ω)) :
          Set (Equiv.Perm Ω)) x (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
  ext τ
  rw [mem_perm_smul_set]
  constructor
  · rintro ⟨⟨hτG, hτxy⟩, hτG', hτX⟩
    set ρ : Equiv.Perm Ω := (σ : Equiv.Perm Ω)⁻¹ * τ with hρ
    have hρG : ρ ∈ G := mul_mem (inv_mem σ.2) hτG
    refine ⟨mem_preimageSubgroup.2 ⟨hρG, mem_structAut.2 ?_⟩, ?_⟩
    · -- `X'^{ρ^ϕ} = X'`
      have hsplit : (⟨ρ, hρG⟩ : G) = σ⁻¹ * ⟨τ, hτG⟩ := rfl
      rw [hsplit, map_mul, map_inv, mul_smul, hτX, ← hσ, inv_smul_smul]
    · -- `ρ` is an isomorphism of `x` and `y^{σ⁻¹}`
      have := strIso_eq_smul_shift G x y σ
      have hmem : τ ∈ (σ : Equiv.Perm Ω) •
          strIso (G : Set (Equiv.Perm Ω)) x (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
        rw [← this]; exact ⟨hτG, hτxy⟩
      rw [mem_perm_smul_set] at hmem
      exact hmem.2
  · rintro ⟨hρ1, hρ2⟩
    set ρ : Equiv.Perm Ω := (σ : Equiv.Perm Ω)⁻¹ * τ with hρdef
    have hρG : ρ ∈ G := preimageSubgroup_le ϕ _ hρ1
    have hτG : τ ∈ G := by
      have : τ = (σ : Equiv.Perm Ω) * ρ := by rw [hρdef]; group
      rw [this]; exact mul_mem σ.2 hρG
    have hτxy : strAct x τ = y := by
      have hmem : τ ∈ (σ : Equiv.Perm Ω) •
          strIso (G : Set (Equiv.Perm Ω)) x (strAct y (σ : Equiv.Perm Ω)⁻¹) := by
        rw [mem_perm_smul_set]
        exact ⟨hρG, hρ2⟩
      rw [← strIso_eq_smul_shift G x y σ] at hmem
      exact hmem.2
    refine ⟨⟨hτG, hτxy⟩, hτG, ?_⟩
    have hsplit : (⟨τ, hτG⟩ : G) = σ * ⟨ρ, hρG⟩ := by
      apply Subtype.ext; show τ = (σ : Equiv.Perm Ω) * ρ; rw [hρdef]; group
    have hfix : (ϕ ⟨ρ, hρG⟩) • X' = X' := mem_structAut.1 (mem_preimageSubgroup.1 hρ1).choose_spec
    rw [hsplit, map_mul, mul_smul, hfix, hσ]

/-- §14.1, **Procedure Align, line 1** for an individualized pair of versions: if no element
of `G` carries `X'` to `Y'` then that piece of `Iso_G(x,y)` is empty. -/
theorem versionPiece_eq_empty {ϕ : G →* Equiv.Perm Γ} (x y : Ω → A) (X' Y' : 𝒳)
    (hno : ¬ ∃ σ : G, (ϕ σ) • X' = Y') : versionPiece ϕ x y X' Y' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro τ ⟨-, hτG, hτX⟩
  exact hno ⟨⟨τ, hτG⟩, hτX⟩

/-! ### The branching reduction

The union of Eq. (40) is `q(m)`-fold, and the algorithm realizes it by running one
sub-reduction per version of `y` and taking the union of the answers. -/

namespace SIReduction

variable {α : Type w}

/-- Run `b Y` for every `Y` of the list and take the union of the values: the `q(m)`-fold
branching of Sec. 14.2. -/
def unionOver {𝒴 : Type*} : List 𝒴 → (𝒴 → SIReduction Ω A (Set (Equiv.Perm Ω))) →
    SIReduction Ω A (Set (Equiv.Perm Ω))
  | [], _ => .done ∅
  | Y :: rest, b =>
      (b Y).bind fun S => (unionOver rest b).bind fun S' => .done (S ∪ S')

theorem run_unionOver {𝒴 : Type*} (b : 𝒴 → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    ∀ L : List 𝒴, (unionOver L b).run = ⋃ Y ∈ L, (b Y).run := by
  intro L
  induction L with
  | nil => rw [unionOver, SIReduction.run_done]; simp
  | cons Y rest ih =>
    rw [unionOver, SIReduction.run_bind, SIReduction.run_bind, SIReduction.run_done, ih]
    ext τ
    simp only [Set.mem_union, Set.mem_iUnion, List.mem_cons, exists_prop]
    constructor
    · rintro (h | ⟨Z, hZ, hτ⟩)
      · exact ⟨Y, Or.inl rfl, h⟩
      · exact ⟨Z, Or.inr hZ, hτ⟩
    · rintro ⟨Z, (rfl | hZ), hτ⟩
      · exact Or.inl hτ
      · exact Or.inr ⟨Z, hZ, hτ⟩

theorem calls_unionOver {𝒴 : Type*} (b : 𝒴 → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    ∀ L : List 𝒴, (unionOver L b).calls = (L.map (fun Y => (b Y).calls)).flatten := by
  intro L
  induction L with
  | nil => rw [unionOver, SIReduction.calls_done]; simp
  | cons Y rest ih =>
    rw [unionOver, SIReduction.calls_bind, SIReduction.calls_bind,
      SIReduction.calls_done, List.append_nil, ih]
    simp

/-- The number of calls of the branching reduction is at most the number of branches times
the number of calls of one branch: this is the multiplicative cost `q(m)` of Eq. (71). -/
theorem calls_length_unionOver {𝒴 : Type*} (b : 𝒴 → SIReduction Ω A (Set (Equiv.Perm Ω)))
    {c : ℕ} (hb : ∀ Y, (b Y).calls.length ≤ c) :
    ∀ L : List 𝒴, (unionOver L b).calls.length ≤ L.length * c := by
  intro L
  induction L with
  | nil => rw [unionOver, SIReduction.calls_done]; simp
  | cons Y rest ih =>
    rw [unionOver, SIReduction.calls_bind, SIReduction.calls_bind,
      SIReduction.calls_done, List.append_nil, List.length_append, List.length_cons]
    calc (b Y).calls.length + (unionOver rest b).calls.length
        ≤ c + rest.length * c := Nat.add_le_add (hb Y) ih
      _ = (rest.length + 1) * c := by ring

/-- Every call of the branching reduction is a call of one of the branches. -/
theorem mem_calls_unionOver {𝒴 : Type*} (b : 𝒴 → SIReduction Ω A (Set (Equiv.Perm Ω)))
    {P : SIInstance Ω A → Prop} (hb : ∀ Y, ∀ J ∈ (b Y).calls, P J) :
    ∀ (L : List 𝒴), ∀ J ∈ (unionOver L b).calls, P J := by
  intro L J hJ
  rw [calls_unionOver] at hJ
  simp only [List.mem_flatten, List.mem_map] at hJ
  obtain ⟨l, ⟨Y, -, rfl⟩, hJl⟩ := hJ
  exact hb Y J hJl

end SIReduction

/-! ### The bridge -/

open scoped Classical in
/-- §14.2, **the branching over the versions of `X(y)`** as a named reduction:

> we need to compare not one but `q(m)` instances of `X(y)` with `X(x)`.

For the fixed version `X'` of `x` and each version `Y'` of `y`, run the sub-reduction
`b Y'` (Procedure Align on the pair `(X', Y')` followed by the recursion), and take the
union of the answers. -/
noncomputable def versionsReduction (Vers : (Ω → A) → Set 𝒳) (y : Ω → A)
    (hfin : (Vers y).Finite) (b : 𝒳 → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.unionOver hfin.toFinset.toList b

open scoped Classical in
/-- **The bridge.**  If every branch computes its piece of `Iso_G(x,y)` (which is what
Procedure Align followed by the recursion does, by `Babai.versionPiece_eq_smul` and
`Babai.versionPiece_eq_empty`), then the branching reduction computes `Iso_G(x,y)`. -/
theorem run_versionsReduction {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (x y : Ω → A) {X' : 𝒳} (hX' : X' ∈ Vers x)
    (hfin : (Vers y).Finite) (b : 𝒳 → SIReduction Ω A (Set (Equiv.Perm Ω)))
    (hb : ∀ Y' ∈ Vers y, (b Y').run = versionPiece ϕ x y X' Y') :
    (versionsReduction Vers y hfin b).run = strIso (G : Set (Equiv.Perm Ω)) x y := by
  rw [versionsReduction, SIReduction.run_unionOver,
    strIso_eq_iUnion_versionPiece hcan x y hX']
  refine Set.iUnion_congr fun Y' => ?_
  by_cases hY' : Y' ∈ Vers y
  · have hmem : Y' ∈ hfin.toFinset.toList := by
      rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact hY'
    rw [Set.iUnion_eq_if, Set.iUnion_eq_if, if_pos hmem, if_pos hY', hb Y' hY']
  · have hmem : Y' ∉ hfin.toFinset.toList := by
      rw [Finset.mem_toList, Set.Finite.mem_toFinset]; exact hY'
    rw [Set.iUnion_eq_if, Set.iUnion_eq_if, if_neg hmem, if_neg hY']

open scoped Classical in
/-- §14.2, Eq. (71): the multiplicative cost.  The branching reduction makes at most
`q · c` calls, where `q` bounds the number of versions of `y` and `c` the number of calls of
one branch. -/
theorem calls_length_versionsReduction {Vers : (Ω → A) → Set 𝒳} (y : Ω → A)
    (hfin : (Vers y).Finite) (b : 𝒳 → SIReduction Ω A (Set (Equiv.Perm Ω))) {q c : ℕ}
    (hq : (Vers y).ncard ≤ q) (hb : ∀ Y', (b Y').calls.length ≤ c) :
    (versionsReduction Vers y hfin b).calls.length ≤ q * c := by
  have hlen : hfin.toFinset.toList.length = (Vers y).ncard := by
    rw [Finset.length_toList, ← Set.ncard_eq_toFinset_card _ hfin]
  calc (versionsReduction Vers y hfin b).calls.length
      ≤ hfin.toFinset.toList.length * c :=
        SIReduction.calls_length_unionOver b hb _
    _ = (Vers y).ncard * c := by rw [hlen]
    _ ≤ q * c := Nat.mul_le_mul_right _ hq

open scoped Classical in
/-- Every call of the branching reduction is a call of one of the branches, so a window-size
bound proved for one branch holds for the whole reduction. -/
theorem calls_versionsReduction {Vers : (Ω → A) → Set 𝒳} (y : Ω → A)
    (hfin : (Vers y).Finite) (b : 𝒳 → SIReduction Ω A (Set (Equiv.Perm Ω)))
    {P : SIInstance Ω A → Prop} (hb : ∀ Y', ∀ J ∈ (b Y').calls, P J) :
    ∀ J ∈ (versionsReduction Vers y hfin b).calls, P J :=
  SIReduction.mem_calls_unionOver b hb _

/-! ### Instantiating the branch: Procedure Align on one pair of versions -/

open scoped Classical in
/-- Procedure Align, lines 1–3, for one pair of versions `(X', Y')`: reject if no `σ ∈ G`
carries `X'` to `Y'`, otherwise align `y` by such a `σ` and continue with
`G₁ = ϕ⁻¹(Aut(X'))` through the continuation `k`, which stands for the Chain Rule of
lines 4–6 (and, in Sec. 15, the recursive call). -/
noncomputable def alignBranch (ϕ : G →* Equiv.Perm Γ) (y : Ω → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm Ω) → (Ω → A) → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : ∃ σ : G, (ϕ σ) • X' = Y' then
    (k (preimageSubgroup ϕ (structAut X'))
        (strAct y ((h.choose : G) : Equiv.Perm Ω)⁻¹)).bind
      fun ans => .done (((h.choose : G) : Equiv.Perm Ω) • ans)
  else .done ∅

open scoped Classical in
/-- The branch is correct: it computes the piece of `Iso_G(x,y)` belonging to `Y'`, provided
the continuation computes `Iso_{G₁}(x, y^{σ⁻¹})`.  This is
`Babai.versionPiece_eq_smul` together with `Babai.versionPiece_eq_empty`. -/
theorem run_alignBranch {ϕ : G →* Equiv.Perm Γ} (x y : Ω → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm Ω) → (Ω → A) → SIReduction Ω A (Set (Equiv.Perm Ω)))
    (hk : ∀ z : Ω → A,
      (k (preimageSubgroup ϕ (structAut X')) z).run =
        strIso ((preimageSubgroup ϕ (structAut X') :
          Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x z) :
    (alignBranch ϕ y X' Y' k).run = versionPiece ϕ x y X' Y' := by
  classical
  by_cases h : ∃ σ : G, (ϕ σ) • X' = Y'
  · rw [alignBranch, dif_pos h, SIReduction.run_bind, SIReduction.run_done, hk]
    exact (versionPiece_eq_smul x y X' Y' h.choose h.choose_spec).symm
  · rw [alignBranch, dif_neg h, SIReduction.run_done]
    exact (versionPiece_eq_empty x y X' Y' h).symm

open scoped Classical in
/-- The branch makes exactly the calls of its continuation. -/
theorem calls_length_alignBranch {ϕ : G →* Equiv.Perm Γ} (y : Ω → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm Ω) → (Ω → A) → SIReduction Ω A (Set (Equiv.Perm Ω)))
    {c : ℕ} (hk : ∀ G₁ z, (k G₁ z).calls.length ≤ c) :
    (alignBranch ϕ y X' Y' k).calls.length ≤ c := by
  classical
  by_cases h : ∃ σ : G, (ϕ σ) • X' = Y'
  · rw [alignBranch, dif_pos h, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil]
    exact hk _ _
  · rw [alignBranch, dif_neg h, SIReduction.calls_done]
    simp

open scoped Classical in
theorem calls_alignBranch {ϕ : G →* Equiv.Perm Γ} (y : Ω → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm Ω) → (Ω → A) → SIReduction Ω A (Set (Equiv.Perm Ω)))
    {P : SIInstance Ω A → Prop} (hk : ∀ G₁ z, ∀ J ∈ (k G₁ z).calls, P J) :
    ∀ J ∈ (alignBranch ϕ y X' Y' k).calls, P J := by
  classical
  by_cases h : ∃ σ : G, (ϕ σ) • X' = Y'
  · rw [alignBranch, dif_pos h, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil]
    exact hk _ _
  · rw [alignBranch, dif_neg h, SIReduction.calls_done]
    simp

open scoped Classical in
/-- **The bridge, assembled.**  Sec. 14.2's *"compare not one but `q(m)` instances of `X(y)`
with `X(x)`"*: for a canonical tuple `Vers` of structures on `Γ` of size at most `q`, and a
continuation `k` that solves `Iso_{G₁}(x, z)` for the reduced group `G₁ = ϕ⁻¹(Aut(X'))`
with at most `c` calls, the reduction

  `Babai.versionsReduction Vers y hfin (fun Y' => Babai.alignBranch ϕ y X' Y' k)`

computes `Iso_G(x,y)` with at most `q · c` calls, and each of its calls is a call of `k`. -/
theorem multCost_bridge {ϕ : G →* Equiv.Perm Γ} {Vers : (Ω → A) → Set 𝒳}
    (hcan : IsCanonicalVersions ϕ Vers) (x y : Ω → A) {X' : 𝒳} (hX' : X' ∈ Vers x)
    (hfin : (Vers y).Finite) {q c : ℕ} (hq : (Vers y).ncard ≤ q)
    (k : Subgroup (Equiv.Perm Ω) → (Ω → A) → SIReduction Ω A (Set (Equiv.Perm Ω)))
    (hkrun : ∀ z : Ω → A,
      (k (preimageSubgroup ϕ (structAut X')) z).run =
        strIso ((preimageSubgroup ϕ (structAut X') :
          Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) x z)
    (hkcalls : ∀ G₁ z, (k G₁ z).calls.length ≤ c)
    {P : SIInstance Ω A → Prop} (hkP : ∀ G₁ z, ∀ J ∈ (k G₁ z).calls, P J) :
    (versionsReduction Vers y hfin (fun Y' => alignBranch ϕ y X' Y' k)).run =
        strIso (G : Set (Equiv.Perm Ω)) x y ∧
      (versionsReduction Vers y hfin
        (fun Y' => alignBranch ϕ y X' Y' k)).calls.length ≤ q * c ∧
      ∀ J ∈ (versionsReduction Vers y hfin
        (fun Y' => alignBranch ϕ y X' Y' k)).calls, P J :=
  ⟨run_versionsReduction hcan x y hX' hfin _
      (fun Y' _ => run_alignBranch x y X' Y' k hkrun),
    calls_length_versionsReduction y hfin _ hq
      (fun Y' => calls_length_alignBranch y X' Y' k hkcalls),
    calls_versionsReduction y hfin _ (fun Y' => calls_alignBranch y X' Y' k hkP)⟩

end Babai
