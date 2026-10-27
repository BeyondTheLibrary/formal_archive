/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12: Proposition 12.0.1 (Lifting), Remark 12.0.2, Observation 12.0.4,
Proposition 12.0.5 (TopAction1).
-/
import Workspace.TopAction.Defs

/-!
# §12 Lifting and TopAction1

Proposition 12.0.1 (Lifting), Remark 12.0.2, Proposition 12.0.5 (TopAction1).

Throughout, `G ≤ S(Ω)` and `H ≤ S(Γ)` are permutation groups, `ϕ : G → H` is a
homomorphism and `N = ker(ϕ)` (`Babai.kerSubgroup`, a subgroup of `S(Ω)`).

**Translation of the paper's displayed formulas.**  With the conventions of the header of
`Workspace/TopAction/Defs.lean`:

* `ϕ⁻¹(σ̄) = σN` — the paper's *left* coset `σN = {σν | ν ∈ N}` is Lean's
  `Babai.rightTranslate (N : Set (S(Ω))) σ = {ν * σ | ν ∈ N}`;
* `Iso_G(x,y) = σ Iso_G(x^σ, y)` — likewise `Babai.rightTranslate (Iso_G(x^σ,y)) σ`, with
  the paper's `x^σ` being `Babai.strAct x σ`;
* `ϕ⁻¹(σ̄) ∩ Iso_G(x,y) = σ (N ∩ Iso_G(x^σ,y)) = σ Iso_N(x^σ,y)` — the conclusion.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type u} {A : Type v}
variable {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]

/-! ### Proposition 12.0.1 (Lifting) -/

/-- The set of liftings of `σ̄` to isomorphisms: `ϕ⁻¹(σ̄) ∩ Iso_G(x,y)`. -/
def liftingSet (ϕ : G →* H) (x y : Ω → A) (σ : H) : Set (Equiv.Perm Ω) :=
  preimageSet ϕ σ ∩ strIso (G : Set (Equiv.Perm Ω)) x y

/-- Proof of Prop. 12.0.1, first step: "If `σ̄ ∉ G^ϕ` then return 'empty'." -/
theorem preimageSet_eq_empty (ϕ : G →* H) {σ : H} (h : σ ∉ ϕ.range) :
    preimageSet ϕ σ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro τ ⟨hτ, hϕ⟩
  exact h ⟨⟨τ, hτ⟩, hϕ⟩

theorem liftingSet_eq_empty (ϕ : G →* H) (x y : Ω → A) {σ : H} (h : σ ∉ ϕ.range) :
    liftingSet ϕ x y σ = ∅ := by
  rw [liftingSet, preimageSet_eq_empty ϕ h, Set.empty_inter]

/-- Proof of Prop. 12.0.1: "`ϕ⁻¹(σ̄) = σN`".

The paper's left coset `σN` is `Babai.rightTranslate (N : Set (S(Ω))) σ`, i.e.
`{ν * σ | ν ∈ N}`; see the header. -/
theorem preimageSet_eq_rightTranslate (ϕ : G →* H) (σ : G) :
    preimageSet ϕ (ϕ σ) = rightTranslate ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) :
      Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) := by
  ext τ
  rw [mem_rightTranslate, SetLike.mem_coe, mem_kerSubgroup]
  constructor
  · rintro ⟨hτ, hϕ⟩
    refine ⟨mul_mem hτ (inv_mem σ.2), ?_⟩
    have : (⟨τ * (σ : Equiv.Perm Ω)⁻¹, mul_mem hτ (inv_mem σ.2)⟩ : G) = ⟨τ, hτ⟩ * σ⁻¹ := rfl
    rw [this, map_mul, map_inv, hϕ, mul_inv_cancel]
  · rintro ⟨hτσ, hϕ⟩
    have hτ : τ ∈ G := by
      have : τ = (τ * (σ : Equiv.Perm Ω)⁻¹) * (σ : Equiv.Perm Ω) := by group
      rw [this]; exact mul_mem hτσ σ.2
    refine ⟨hτ, ?_⟩
    have hmul : (⟨τ, hτ⟩ : G) = ⟨τ * (σ : Equiv.Perm Ω)⁻¹, hτσ⟩ * σ := by
      apply Subtype.ext; simp
    rw [hmul, map_mul, hϕ, one_mul]

/-- Proof of Prop. 12.0.1: "`Iso_G(x,y) = σ Iso_G(x^σ, y)`", for `σ ∈ G`.

Again the paper's left coset: `Babai.rightTranslate (Iso_G(x^σ,y)) σ`. -/
theorem strIso_eq_rightTranslate (K : Set (Equiv.Perm Ω)) (x y : Ω → A)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ K) (hK : ∀ a ∈ K, ∀ b ∈ K, a * b⁻¹ ∈ K)
    (hK' : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K) :
    strIso K x y = rightTranslate (strIso K (strAct x σ) y) σ := by
  ext τ
  rw [mem_rightTranslate]
  simp only [strIso, Set.mem_sep_iff]
  constructor
  · rintro ⟨hτ, hx⟩
    refine ⟨hK _ hτ _ hσ, ?_⟩
    rw [← strAct_mul x σ (τ * σ⁻¹)]
    simpa using hx
  · rintro ⟨hτ, hx⟩
    have hmem : τ ∈ K := by
      have : τ = (τ * σ⁻¹) * σ := by group
      rw [this]; exact hK' _ hτ _ hσ
    refine ⟨hmem, ?_⟩
    rw [← strAct_mul x σ (τ * σ⁻¹)] at hx
    simpa using hx

/-- `Iso_G(x,y) = σ Iso_G(x^σ, y)` for a subgroup `G` and `σ ∈ G`. -/
theorem strIso_eq_rightTranslate_subgroup (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A)
    (σ : G) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      rightTranslate (strIso (G : Set (Equiv.Perm Ω)) (strAct x σ) y) (σ : Equiv.Perm Ω) :=
  strIso_eq_rightTranslate _ x y σ.2 (fun _ ha _ hb => mul_mem ha (inv_mem hb))
    (fun _ ha _ hb => mul_mem ha hb)

theorem rightTranslate_inter (K L : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) :
    rightTranslate K σ ∩ rightTranslate L σ = rightTranslate (K ∩ L) σ := by
  ext τ
  simp only [Set.mem_inter_iff, mem_rightTranslate]

/-- §12, **Proposition 12.0.1** (Lifting).

> Let `G ≤ S(Ω)` and `H ≤ S(Γ)` be permutation groups, `ϕ : G → H` a homomorphism, and
> `N = ker(ϕ)`.  Given these data, the strings `x, y : Ω → Σ` and `σ̄ ∈ H`, one can reduce,
> in polynomial time, the computation of the set `ϕ⁻¹(σ̄) ∩ Iso_G(x,y)` (set of liftings of
> `σ̄` to isomorphisms) to a single call to `Iso_N(x', y)` for some string `x'`.
>
> *Proof.*  If `σ̄ ∉ G^ϕ` then return "empty."  Otherwise let `σ ∈ ϕ⁻¹(σ̄)`. […]  Let
> `x' = x^σ`.  Then `ϕ⁻¹(σ̄) = σN` and `Iso_G(x,y) = σ Iso_G(x',y)`.  Consequently,
> `ϕ⁻¹(σ̄) ∩ Iso_G(x,y) = σ (N ∩ Iso_G(x',y)) = σ Iso_N(x',y)`.

This is the mathematical identity behind the reduction: for any lifting `σ` of `σ̄` and
`x' = x^σ`, the set of liftings of `σ̄` to isomorphisms is the paper's left coset
`σ Iso_N(x', y)`, i.e. `Babai.rightTranslate (Iso_N(x',y)) σ` (see the header).  The empty
case is `Babai.liftingSet_eq_empty`.  The single call is `Babai.liftingReduction`.  The polynomial-time
half is on the RAM in `Workspace/Algo/TopLift.lean` (`Algo.polyFun_actPreimage`,
`Algo.topLift_spec`). -/
theorem Proposition_12_0_1_lifting (ϕ : G →* H) (x y : Ω → A) (σ : G) :
    liftingSet ϕ x y (ϕ σ) =
      rightTranslate
        (strIso ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
          (strAct x (σ : Equiv.Perm Ω)) y) (σ : Equiv.Perm Ω) := by
  rw [liftingSet, preimageSet_eq_rightTranslate ϕ σ,
    strIso_eq_rightTranslate_subgroup G x y σ, rightTranslate_inter]
  congr 1
  ext τ
  simp only [Set.mem_inter_iff, strIso, Set.mem_sep_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hN, -, hx⟩; exact ⟨hN, hx⟩
  · rintro ⟨hN, hx⟩; exact ⟨hN, kerSubgroup_le ϕ hN, hx⟩

/-! ### Remark 12.0.2 -/

/-- §12, **Remark 12.0.2**.

> `H` does not need to be a permutation group.  What we need is that `H` permit
> *constructive membership testing*, i. e., for any list of elements `τ₁, …, τ_k, ρ ∈ H` we
> should be able to efficiently decide whether `ρ ∈ K` where `K` is the subgroup generated
> by the `τᵢ`, and if the answer is affirmative, to produce a straight-line program that
> constructs `ρ` from the `τᵢ` (see Def. 11.1.10).

The mathematical content of "constructive membership testing" is the existence of the
straight-line program (Def. 11.1.10, `Babai.IsStraightLineProgram`); efficiency is not
modelled.  The statement below is that this always holds mathematically in a finite group,
so the remark is about cost only. -/
def Remark_12_0_2_constructiveMembership (K : Type*) [Group K] : Prop :=
  ∀ (T : Set K) (ρ : K), ρ ∈ Subgroup.closure T →
    ∃ p : List K, IsStraightLineProgram T p ∧ SLPComputes p {ρ}

/-! ### A lifting representative -/

open Classical in
/-- A lifting `σ ∈ ϕ⁻¹(σ̄)`, when one exists ("let `σ ∈ ϕ⁻¹(σ̄)`.  We can find such a `σ` in
polynomial time by Prop. 2.2.6").  The choice is arbitrary; Prop. 12.0.1 holds for every
lifting. -/
noncomputable def liftRep (ϕ : G →* H) (σ : H) : Equiv.Perm Ω :=
  if h : ∃ τ : G, ϕ τ = σ then ((h.choose : G) : Equiv.Perm Ω) else 1

theorem liftRep_mem (ϕ : G →* H) {σ : H} (h : σ ∈ ϕ.range) :
    ∃ hG : liftRep ϕ σ ∈ G, ϕ ⟨liftRep ϕ σ, hG⟩ = σ := by
  classical
  have hex : ∃ τ : G, ϕ τ = σ := h
  rw [liftRep, dif_pos hex]
  refine ⟨hex.choose.2, ?_⟩
  have : (⟨(hex.choose : Equiv.Perm Ω), hex.choose.2⟩ : G) = hex.choose := rfl
  rw [this]
  exact hex.choose_spec

/-! ### Proposition 12.0.5 (TopAction1) -/

section TopAction1

variable (ϕ : G →* H) (x y : Ω → A)

/-- "`ϕ` maps `Iso_G(x,y)` onto `H`": every element of `H` lifts to a `G`-isomorphism of
`x` and `y` (Prop. 12.0.5 (i)). -/
def MapsOnto : Prop := ∀ σ : H, (liftingSet ϕ x y σ).Nonempty

variable {ϕ x y}

/-- `Iso_G(x,y)` is a subcoset of `S(Ω)` when it is nonempty: Remark 11.1.5 (ii). -/
theorem isSubcoset_strIso (h : (strIso (G : Set (Equiv.Perm Ω)) x y).Nonempty) :
    IsSubcoset (strIso (G : Set (Equiv.Perm Ω)) x y) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨strAutSubgroup G x, σ, ?_⟩
  have := wIso_eq_smul_wAut_one (isInvariant_univ G) (x := x) (y := y) (σ := σ)
    (by rwa [wIso_univ])
  rw [wIso_univ] at this
  exact this

/-- The image of `Iso_G(x,y)` under `ϕ`: the set of `σ̄ ∈ H` that lift to isomorphisms. -/
def liftableSet (ϕ : G →* H) (x y : Ω → A) : Set H := {σ | (liftingSet ϕ x y σ).Nonempty}

/-- The image of `Iso_G(x,y)` under `ϕ` is a subcoset of `H`, as soon as it is nonempty.
(This is the step "`Iso_G(x,y)` is the right subcoset … generated by the subcosets
`ϕ⁻¹(σ̄) ∩ Iso_G(x,y)`" of the proof of Prop. 12.0.5, in the form needed for item (i).) -/
theorem isSubcoset_liftableSet (h : (liftableSet ϕ x y).Nonempty) :
    IsSubcoset (liftableSet ϕ x y) := by
  rw [isSubcoset_iff]
  refine ⟨h, ?_⟩
  obtain ⟨σ₀, τ₀, hτ₀⟩ := h
  have hKne : (strIso (G : Set (Equiv.Perm Ω)) x y).Nonempty := ⟨τ₀, hτ₀.2⟩
  have hK := isSubcoset_iff.1 (isSubcoset_strIso hKne)
  rintro a ha b hb c hc
  obtain ⟨α, hα, hαI⟩ := ha
  obtain ⟨β, hβ, hβI⟩ := hb
  obtain ⟨γ, hγ, hγI⟩ := hc
  obtain ⟨hαG, hαϕ⟩ := hα
  obtain ⟨hβG, hβϕ⟩ := hβ
  obtain ⟨hγG, hγϕ⟩ := hγ
  have hmemG : α * β⁻¹ * γ ∈ G := mul_mem (mul_mem hαG (inv_mem hβG)) hγG
  refine ⟨α * β⁻¹ * γ, ⟨hmemG, ?_⟩, hK.2 _ hαI _ hβI _ hγI⟩
  have hsplit : (⟨α * β⁻¹ * γ, hmemG⟩ : G) = ⟨α, hαG⟩ * (⟨β, hβG⟩)⁻¹ * ⟨γ, hγG⟩ := rfl
  rw [hsplit, map_mul, map_mul, map_inv, hαϕ, hβϕ, hγϕ]

/-- §12, **Proposition 12.0.5** (TopAction1), item (i): the decision.

> (i) decide whether `ϕ` maps `Iso_G(x,y)` onto `H`;
>
> *Proof.*  Let `S' = S ∪ {1}`; so `S'` is a set of coset generators of `H`.  Apply
> Prop. 12.0.1 to each `σ̄ ∈ S'`.  If there is a `σ̄ ∈ S'` for which the algorithm returns
> the empty set (`σ̄` does not lift to an isomorphism), return the answer "no" to item (i).

`S` is the given set of generators of `H`, i.e. `⟨S⟩ = H`; since `H` is the ambient group
here, this reads `Subgroup.closure S = ⊤` in `H`.  The mathematical content is that it
suffices to test the `|S| + 1` elements of `S' = S ∪ {1}`. -/
theorem Proposition_12_0_5_i {S : Set H} (hS : Subgroup.closure S = ⊤) :
    MapsOnto ϕ x y ↔ ∀ σ ∈ insert (1 : H) S, (liftingSet ϕ x y σ).Nonempty := by
  constructor
  · intro h σ _; exact h σ
  · intro h
    have hsub : insert (1 : H) S ⊆ liftableSet ϕ x y := fun σ hσ => h σ hσ
    have hne : (liftableSet ϕ x y).Nonempty :=
      ⟨1, h 1 (Set.mem_insert _ _)⟩
    have := Observation_12_0_4_paper hS (isSubcoset_liftableSet hne) hsub
    intro σ
    have : σ ∈ liftableSet ϕ x y := this ▸ Set.mem_univ σ
    exact this

end TopAction1

/-! ### Proposition 12.0.5 (ii): `Iso_G(x,y)` is the subcoset generated by the liftings -/

/-- §12, **Proposition 12.0.5** (TopAction1), item (ii).

> (ii) if the answer is affirmative, find `Iso_G(x,y)`.
>
> *Proof.*  […] return the answer "yes" to item (i) and observe that `Iso_G(x,y)` is the
> right subcoset of `G` generated by the subcosets `ϕ⁻¹(σ̄) ∩ Iso_G(x,y)` (`σ̄ ∈ S'`) found
> by Prop. 12.0.1.

Here `S' = S ∪ {1}` and the subcoset generated is `Babai.subcosetClosure` (the smallest
subcoset containing the union), which for a subset of `G` is the same whether computed
inside `G` or inside `S(Ω)` since `G` itself is a subcoset. -/
theorem Proposition_12_0_5_ii {ϕ : G →* H} {x y : Ω → A} {S : Set H}
    (hS : Subgroup.closure S = ⊤)
    (hlift : ∀ σ ∈ insert (1 : H) S, (liftingSet ϕ x y σ).Nonempty) :
    strIso (G : Set (Equiv.Perm Ω)) x y =
      subcosetClosure (⋃ σ ∈ insert (1 : H) S, liftingSet ϕ x y σ) := by
  classical
  set K := strIso (G : Set (Equiv.Perm Ω)) x y with hKdef
  set U := ⋃ σ ∈ insert (1 : H) S, liftingSet ϕ x y σ with hUdef
  -- a lifting `τ₀` of `1`
  obtain ⟨τ₀, hτ₀pre, hτ₀K⟩ := hlift 1 (Set.mem_insert _ _)
  have hUK : U ⊆ K := by
    rw [hUdef]
    refine Set.iUnion₂_subset fun σ _ => ?_
    exact fun τ hτ => hτ.2
  have hτ₀U : τ₀ ∈ U := by
    rw [hUdef]
    exact Set.mem_biUnion (Set.mem_insert _ _) (⟨hτ₀pre, hτ₀K⟩ : τ₀ ∈ liftingSet ϕ x y 1)
  have hUne : U.Nonempty := ⟨τ₀, hτ₀U⟩
  have hKsub : IsSubcoset K := isSubcoset_strIso ⟨τ₀, hτ₀K⟩
  -- `D ⊆ K` since `K` is a subcoset containing `U`
  have hDK : subcosetClosure U ⊆ K := subcosetClosure_subset hKsub hUK
  -- `K = τ₀ • Aut_G(x)`
  have hKeq : K = (τ₀ : Equiv.Perm Ω) • (strAutSubgroup G x : Set (Equiv.Perm Ω)) := by
    have := wIso_eq_smul_wAut_one (isInvariant_univ G) (x := x) (y := y) (σ := τ₀)
      (by rw [wIso_univ]; exact hτ₀K)
    rw [wIso_univ] at this
    exact this
  -- `D = τ₀ • L` for a subgroup `L`
  have hτ₀D : τ₀ ∈ subcosetClosure U := subset_subcosetClosure U hτ₀U
  obtain ⟨L, hL⟩ := (isSubcoset_subcosetClosure hUne).exists_subgroup hτ₀D
  -- `L ≤ Aut_G(x)`
  have hLAut : L ≤ strAutSubgroup G x := by
    intro l hl
    have : (τ₀ : Equiv.Perm Ω) * l ∈ subcosetClosure U := by
      rw [hL]; exact ⟨l, hl, rfl⟩
    have h2 := hDK this
    rw [hKeq, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at h2
    simpa using h2
  have hLG : L ≤ G := hLAut.trans (wAutSubgroup_le G _ _ x)
  -- `Aut_G(x) ∩ N ≤ L`
  have hkerL : ∀ a ∈ strAutSubgroup G x, a ∈ kerSubgroup ϕ → a ∈ L := by
    intro a haAut haN
    have haG : a ∈ G := wAutSubgroup_le G _ _ x haAut
    have hmemK : (τ₀ : Equiv.Perm Ω) * a ∈ K := by
      rw [hKeq]; exact ⟨a, haAut, rfl⟩
    have hmemG : (τ₀ : Equiv.Perm Ω) * a ∈ G := mul_mem hτ₀pre.1 haG
    have hϕ : ϕ ⟨(τ₀ : Equiv.Perm Ω) * a, hmemG⟩ = 1 := by
      have hsplit : (⟨(τ₀ : Equiv.Perm Ω) * a, hmemG⟩ : G) = ⟨τ₀, hτ₀pre.1⟩ * ⟨a, haG⟩ := rfl
      obtain ⟨haG', haker⟩ := mem_kerSubgroup.1 haN
      rw [hsplit, map_mul, hτ₀pre.2, haker, mul_one]
    have hmemU : (τ₀ : Equiv.Perm Ω) * a ∈ U := by
      rw [hUdef]
      refine Set.mem_biUnion (Set.mem_insert _ _) ?_
      exact (⟨⟨hmemG, hϕ⟩, hmemK⟩ : (τ₀ : Equiv.Perm Ω) * a ∈ liftingSet ϕ x y 1)
    have h2 : (τ₀ : Equiv.Perm Ω) * a ∈ subcosetClosure U := subset_subcosetClosure U hmemU
    rw [hL, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at h2
    simpa using h2
  -- `ϕ(L) = H`
  have himg : (L.subgroupOf G).map ϕ = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hS, Subgroup.closure_le]
    intro σ hσ
    obtain ⟨τ, hτpre, hτK⟩ := hlift σ (Set.mem_insert_of_mem _ hσ)
    have hτU : τ ∈ U := by
      rw [hUdef]
      refine Set.mem_biUnion (Set.mem_insert_of_mem _ hσ) ?_
      exact (⟨hτpre, hτK⟩ : τ ∈ liftingSet ϕ x y σ)
    have hτD : τ ∈ subcosetClosure U := subset_subcosetClosure U hτU
    rw [hL, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hτD
    set l : Equiv.Perm Ω := (τ₀ : Equiv.Perm Ω)⁻¹ * τ with hldef
    have hlL : l ∈ L := hτD
    have hlG : l ∈ G := hLG hlL
    refine ⟨⟨l, hlG⟩, hlL, ?_⟩
    have hsplit : (⟨τ, hτpre.1⟩ : G) = ⟨τ₀, hτ₀pre.1⟩ * ⟨l, hlG⟩ := by
      apply Subtype.ext; simp [hldef]
    have := hτpre.2
    rw [hsplit, map_mul, hτ₀pre.2, one_mul] at this
    exact this
  -- `Aut_G(x) ≤ L`
  have hAutL : strAutSubgroup G x ≤ L := by
    intro a haAut
    have haG : a ∈ G := wAutSubgroup_le G _ _ x haAut
    have : ϕ ⟨a, haG⟩ ∈ (L.subgroupOf G).map ϕ := by rw [himg]; trivial
    obtain ⟨u, huL, hu⟩ := this
    have hulL : (u : Equiv.Perm Ω) ∈ L := huL
    have hulAut : (u : Equiv.Perm Ω) ∈ strAutSubgroup G x := hLAut hulL
    have hprod : a * ((u : Equiv.Perm Ω))⁻¹ ∈ strAutSubgroup G x :=
      mul_mem haAut (inv_mem hulAut)
    have hprodG : a * ((u : Equiv.Perm Ω))⁻¹ ∈ G := mul_mem haG (inv_mem u.2)
    have hprodN : a * ((u : Equiv.Perm Ω))⁻¹ ∈ kerSubgroup ϕ := by
      refine mem_kerSubgroup.2 ⟨hprodG, ?_⟩
      have hsplit : (⟨a * ((u : Equiv.Perm Ω))⁻¹, hprodG⟩ : G) = ⟨a, haG⟩ * u⁻¹ := rfl
      rw [hsplit, map_mul, map_inv, hu, mul_inv_cancel]
    have := hkerL _ hprod hprodN
    have heq : a = (a * ((u : Equiv.Perm Ω))⁻¹) * (u : Equiv.Perm Ω) := by group
    rw [heq]
    exact mul_mem this hulL
  -- conclude
  refine Set.Subset.antisymm ?_ hDK
  rw [hKeq, hL]
  exact Set.smul_set_mono (fun a ha => hAutL ha)


/-! ### The recursive calls of Prop. 12.0.1 and Prop. 12.0.5

Proposition 12.0.1 reduces the computation of `ϕ⁻¹(σ̄) ∩ Iso_G(x,y)` to **a single call**
to `Iso_N(x', y)`; Proposition 12.0.5 calls `|S| + 1` such instances, one for each
`σ̄ ∈ S' = S ∪ {1}`.  Both are `Babai.SIReduction`s; the number of calls is
`SIReduction.calls.length` and each call is an instance "with respect to `N`" in the
paper's sense, i.e. its group is `N` (and its window is all of `Ω`). -/

/-- The single `N`-instance called by Prop. 12.0.1: `Iso_N(x', y)` with `x' = x^σ`, where
`σ = liftRep ϕ σ̄` is a lifting of `σ̄`.  The window is all of `Ω`. -/
noncomputable def liftInstance (ϕ : G →* H) (x y : Ω → A) (σ : H) : SIInstance Ω A :=
  ⟨((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)), Set.univ,
    strAct x (liftRep ϕ σ), y⟩

theorem liftInstance_answer (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (liftInstance ϕ x y σ).answer =
      strIso ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω))
        (strAct x (liftRep ϕ σ)) y := by
  rw [SIInstance.answer, liftInstance, wIso_univ]

open Classical in
/-- §12, **Proposition 12.0.1** (Lifting), the reduction: one call to `Iso_N(x', y)`. -/
noncomputable def liftingReduction (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .call (liftInstance ϕ x y σ)
    (fun ans => .done (if σ ∈ ϕ.range then rightTranslate ans (liftRep ϕ σ) else ∅))

/-- Prop. 12.0.1: the reduction computes the set of liftings. -/
theorem run_liftingReduction (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (liftingReduction ϕ x y σ).run = liftingSet ϕ x y σ := by
  classical
  rw [liftingReduction, SIReduction.run_call, SIReduction.run_done, liftInstance_answer]
  by_cases h : σ ∈ ϕ.range
  · rw [if_pos h]
    obtain ⟨hG, hϕ⟩ := liftRep_mem ϕ h
    have := Proposition_12_0_1_lifting ϕ x y ⟨liftRep ϕ σ, hG⟩
    rw [hϕ] at this
    exact this.symm
  · rw [if_neg h, liftingSet_eq_empty ϕ x y h]

/-- Prop. 12.0.1: the reduction makes exactly one call, an instance with respect to `N`
(window all of `Ω`). -/
theorem calls_liftingReduction (ϕ : G →* H) (x y : Ω → A) (σ : H) :
    (liftingReduction ϕ x y σ).calls = [liftInstance ϕ x y σ] := by
  rw [liftingReduction, SIReduction.calls_call, SIReduction.calls_done]

/-- The `|S'|` independent calls of Prop. 12.0.5, one per element of `S'`. -/
noncomputable def liftAll (ϕ : G →* H) (x y : Ω → A) :
    List H → SIReduction Ω A (List (Set (Equiv.Perm Ω)))
  | [] => .done []
  | σ :: rest => (liftingReduction ϕ x y σ).bind
      (fun a => (liftAll ϕ x y rest).bind (fun as => .done (a :: as)))

theorem run_liftAll (ϕ : G →* H) (x y : Ω → A) (l : List H) :
    (liftAll ϕ x y l).run = l.map (liftingSet ϕ x y) := by
  induction l with
  | nil => rw [liftAll]; simp
  | cons σ rest ih =>
    rw [liftAll, SIReduction.run_bind, SIReduction.run_bind, SIReduction.run_done,
      run_liftingReduction, ih]
    simp

theorem calls_liftAll (ϕ : G →* H) (x y : Ω → A) (l : List H) :
    (liftAll ϕ x y l).calls = l.map (liftInstance ϕ x y) := by
  induction l with
  | nil => rw [liftAll]; simp
  | cons σ rest ih =>
    rw [liftAll, SIReduction.calls_bind, SIReduction.calls_bind, SIReduction.calls_done,
      calls_liftingReduction, ih]
    simp

open Classical in
/-- §12, **Proposition 12.0.5** (TopAction1), the reduction:

> we can achieve the following by recursively calling `|S| + 1` instances of String
> Isomorphism with respect to `N`, at polynomial cost per instance:
> (i) decide whether `ϕ` maps `Iso_G(x,y)` onto `H`;
> (ii) if the answer is affirmative, find `Iso_G(x,y)`.

The value is `none` when the answer to (i) is "no", and `some Iso_G(x,y)` when it is
"yes".  The RAM round is `Algo.top1Round` (`Workspace/Algo/TopRound.lean`,
`Algo.implements_top1Round`). -/
noncomputable def TopAction1Reduction (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    SIReduction Ω A (Option (Set (Equiv.Perm Ω))) :=
  (liftAll ϕ x y (1 :: S)).bind fun L =>
    .done (if ∀ s ∈ L, Set.Nonempty s then some (subcosetClosure (⋃ s ∈ L, s)) else none)

/-- Prop. 12.0.5: the reduction makes `|S| + 1` calls. -/
theorem calls_length_TopAction1Reduction (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    (TopAction1Reduction ϕ x y S).calls.length = S.length + 1 := by
  rw [TopAction1Reduction, SIReduction.calls_bind, SIReduction.calls_done,
    calls_liftAll]
  simp

/-- Prop. 12.0.5: every call is an instance "with respect to `N`" — its group is `N` and
its window is all of `Ω`. -/
theorem calls_TopAction1Reduction_wrt (ϕ : G →* H) (x y : Ω → A) (S : List H) :
    ∀ I ∈ (TopAction1Reduction ϕ x y S).calls,
      I.IsWithRespectTo ((kerSubgroup ϕ : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω)) ∧
        I.Δ = Set.univ := by
  rw [TopAction1Reduction, SIReduction.calls_bind, SIReduction.calls_done, calls_liftAll]
  intro I hI
  simp only [List.append_nil, List.mem_map] at hI
  obtain ⟨σ, -, rfl⟩ := hI
  exact ⟨rfl, rfl⟩

open Classical in
/-- §12, **Proposition 12.0.5** (TopAction1): the reduction decides (i) and, when the
answer is affirmative, returns `Iso_G(x,y)`, as in item (ii). -/
theorem run_TopAction1Reduction (ϕ : G →* H) (x y : Ω → A) (S : List H)
    (hS : Subgroup.closure {σ : H | σ ∈ S} = ⊤) :
    (TopAction1Reduction ϕ x y S).run =
      if MapsOnto ϕ x y then some (strIso (G : Set (Equiv.Perm Ω)) x y) else none := by
  classical
  have hset : {σ : H | σ ∈ (1 : H) :: S} = insert (1 : H) {σ : H | σ ∈ S} := by
    ext σ; simp
  have hmem : (∀ s ∈ (((1 : H) :: S).map (liftingSet ϕ x y)), Set.Nonempty s) ↔
      ∀ σ ∈ insert (1 : H) {σ : H | σ ∈ S}, (liftingSet ϕ x y σ).Nonempty := by
    rw [← hset]
    constructor
    · intro h σ hσ; exact h _ (List.mem_map_of_mem hσ)
    · intro h s hs
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hs
      exact h σ hσ
  have hunion : (⋃ s ∈ (((1 : H) :: S).map (liftingSet ϕ x y)), s) =
      ⋃ σ ∈ insert (1 : H) {σ : H | σ ∈ S}, liftingSet ϕ x y σ := by
    rw [← hset]
    ext τ
    simp only [Set.mem_iUnion, List.mem_map, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨s, ⟨σ, hσ, rfl⟩, hτ⟩; exact ⟨σ, hσ, hτ⟩
    · rintro ⟨σ, hσ, hτ⟩; exact ⟨_, ⟨σ, hσ, rfl⟩, hτ⟩
  rw [TopAction1Reduction, SIReduction.run_bind, SIReduction.run_done, run_liftAll]
  by_cases h : MapsOnto ϕ x y
  · have hall := (Proposition_12_0_5_i hS).1 h
    rw [if_pos (hmem.2 hall), if_pos h, hunion,
      ← Proposition_12_0_5_ii hS hall]
  · rw [if_neg h, if_neg]
    intro hcon
    exact h ((Proposition_12_0_5_i hS).2 (hmem.1 hcon))

end Babai
