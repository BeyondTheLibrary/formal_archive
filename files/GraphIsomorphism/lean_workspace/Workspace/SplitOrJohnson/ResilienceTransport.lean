/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.1: Resilience of Johnson schemes, the transport step of Proposition 9.1.1.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Workspace.AltQuotients.MainStructure
import Workspace.ColoredPartitions.Binomial
import Workspace.SplitOrJohnson.ResilienceAux

/-!
# §9.1 From Corollary 9.1.3 to Proposition 9.1.1

Proposition 9.1.1 is *"an immediate consequence of Corollary 9.1.3"* (version 2.5,
line 3937).  Corollary 9.1.3 is a statement about a subgroup of `S_m`; Proposition 9.1.1 is
a statement about the category of Johnson schemes and the reductions of §6.  This file
contains the passage between the two languages, and nothing else: the mathematical content
of §9.1 is in `Workspace/SplitOrJohnson/Resilience.lean` and
`Workspace/SplitOrJohnson/ResilienceAux.lean`.

The main result is `Babai.prop_9_1_1_of_cor`, which is Proposition 9.1.1 with the
conclusion of Corollary 9.1.3 as a hypothesis.

## What has to be transported

* the input `X` comes with a bijection to the `t`-subsets of `[m]` and the Johnson
  coloring equation. Its automorphism group equals that of the corresponding
  `Babai.johnsonPt` on the same carrier;
* `Aut(J(m,t)) = S_m` (Prop. 3.2.11, `Babai.aut_johnsonScheme`), so that a subgroup of
  `Aut(X)` of index `≤ s` becomes a subgroup of `S_m` of index `≤ s`
  (`Babai.johnsonPerm`, `Babai.range_johnsonPerm`);
* the Johnson group `A⁽ᵗ⁾(Δ)` of Corollary 9.1.3 has to act on the vertices of the scheme
  lying inside `Δ`, primitively (`Babai.isPreprimitive_inducedOnTSets_alternating`, the
  primitivity of §2.2.1 for an arbitrary ground set in place of `Fin k`).
-/

namespace Babai

open MulAction
open scoped Pointwise

/-! ### Primitivity of the Johnson groups on an arbitrary ground set

`Babai.isPrimitive_JohnsonA` (§2.2.1) is stated for the ground set `Fin k`.  Corollary
9.1.3 produces a *subset* `Δ` of the ground set, so we need the same statement for the
ground set `Δ`. -/

set_option backward.isDefEq.respectTransparency false in
/-- §2.2.1.  The Johnson group `A⁽ᵗ⁾(Γ)` is primitive on the `t`-subsets of `Γ` when
`1 ≤ t` and `2t + 1 ≤ |Γ|`.  This is `Babai.isPrimitive_JohnsonA` with an arbitrary finite
ground set in place of `Fin k`, and with the same proof. -/
theorem isPreprimitive_inducedOnTSets_alternating {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {t : ℕ} (ht : 1 ≤ t) (hk : 2 * t + 1 ≤ Nat.card Γ) :
    IsPreprimitive (inducedOnTSets (alternatingGroup Γ) t) (binom Γ t) := by
  have hn : t < Nat.card Γ := by omega
  haveI : IsPretransitive (alternatingGroup Γ) (Set.powersetCard Γ t) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by omega)
  haveI : Nontrivial (Set.powersetCard Γ t) := Set.powersetCard.nontrivial' (by omega) hn
  obtain ⟨s⟩ := (inferInstance : Nontrivial (Set.powersetCard Γ t)).to_nonempty
  refine isPreprimitive_inducedOnTSets _ ?_
  rw [← isCoatom_stabilizer_iff_preprimitive _ s, Set.powersetCard.stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [Set.powersetCard.coe_nonempty_iff]; omega
  · simp only [Set.nonempty_compl, ne_eq, Set.eq_univ_iff_ncard, Set.powersetCard.ncard_eq]
    exact ne_of_lt hn
  · simp only [Set.powersetCard.ncard_eq]; omega

/-- A finite permutation group containing a primitive subgroup is primitive.
Every block for the larger group is also a block for the subgroup. -/
theorem IsPrimitive.of_le {α : Type*} [Finite α] {H G : Subgroup (Equiv.Perm α)}
    (hH : IsPrimitive H) (hle : H ≤ G) : IsPrimitive G := by
  refine ⟨hH.1.trans (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)), ?_⟩
  intro B hB
  exact hH.2 B ⟨hB.1, fun g hg => hB.2 g (hle hg)⟩

open scoped Classical in
/-- Corollary 9.1.3, the induced action of `G` on the `t`-subsets of its invariant
label set `Δ`. Extending an even permutation of `Δ` by the identity shows that
`G^Δ` contains `A(Δ)`. Its action on the `t`-subsets is therefore primitive in the
paper's sense, including the condition that the group has at least two elements. -/
theorem cor_9_1_3_isPrimitive {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)} {Δ : Set Γ} {t : ℕ}
    (hΔ : IsInvariant G Δ) (hstab : pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G)
    (ht : 1 ≤ t) (hk : 2 * t + 1 ≤ Δ.ncard) :
    IsPrimitive (inducedOnTSets (restrictTo G Δ hΔ) t) := by
  have hle : alternatingGroup Δ ≤ restrictTo G Δ hΔ := by
    intro g hg
    have hmem : Equiv.Perm.ofSubtype g ∈ G := hstab ⟨by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.1 hg,
      fun x hx => Equiv.Perm.ofSubtype_apply_of_not_mem g hx⟩
    refine ⟨⟨Equiv.Perm.ofSubtype g, hmem⟩, ?_⟩
    exact Equiv.ext fun x => Subtype.ext (Equiv.Perm.ofSubtype_apply_of_mem g x.2)
  have hk' : 2 * t + 1 ≤ Nat.card Δ := by rwa [Nat.card_coe_set_eq]
  haveI : Nontrivial (binom Δ t) :=
    (binomEquiv Δ t).nontrivial_congr.2
      (Set.powersetCard.nontrivial' (by omega) (by omega))
  have hprim : IsPrimitive (inducedOnTSets (alternatingGroup Δ) t) :=
    (isPrimitive_iff_isPreprimitive _).2
      (isPreprimitive_inducedOnTSets_alternating ht hk')
  exact hprim.of_le (Subgroup.map_mono hle)

/-- If `G` preserves the labels `Δ`, its Johnson action preserves the vertices whose
labels all lie in `Δ`. -/
theorem isInvariant_binom_subset {Γ : Type*} [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)} {Δ : Set Γ} (hΔ : IsInvariant G Δ) (t : ℕ) :
    IsInvariant (inducedOnTSets G t) {S : binom Γ t | ∀ x ∈ S.val, x ∈ Δ} := by
  apply (isInvariant_iff_mem _ _).2
  rintro σ ⟨g, hg, rfl⟩ S
  change (∀ x ∈ S.val, x ∈ Δ) ↔ ∀ x ∈ S.val.image g, x ∈ Δ
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact ((isInvariant_iff_mem _ _).1 hΔ g hg y).1 (h y hy)
  · intro h x hx
    exact ((isInvariant_iff_mem _ _).1 hΔ g hg x).2
      (h (g x) (Finset.mem_image.2 ⟨x, hx, rfl⟩))

/-- The upper stabilizer bound on a set also preserves its complement. -/
theorem isInvariant_compl_of_le_setwiseStabilizer {Γ : Type*}
    {G : Subgroup (Equiv.Perm Γ)} {T : Set Γ}
    (hle : G ≤ setwiseStabilizer ⊤ T) : IsInvariant G Tᶜ := by
  apply (isInvariant_iff_mem _ _).2
  intro g hg x
  exact not_congr ((isInvariant_iff_mem G T).1 (fun g hg => (hle hg).2) g hg x)

/-! ### The `t`-subsets of a subset

Corollary 9.1.3 produces a subset `Δ` of `[m]`, and the vertices of `J(m,t)` that Prop.
9.1.1 uses are the `t`-subsets of `Δ`.  The two lemmas below are the inclusion of the
`t`-subsets of `Δ` among the `t`-subsets of `[m]` and its equivariance. -/

section SubBinom

/-- The `t`-subsets of `Δ ⊆ α`, read as `t`-subsets of `α`. -/
def finsetBinom {α : Type*} (Δ : Finset α) (t : ℕ) : binom {x // x ∈ Δ} t → binom α t := fun S =>
  ⟨(S : Finset {x // x ∈ Δ}).map (Function.Embedding.subtype _), by
    rw [Finset.card_map]; exact S.2⟩

theorem finsetBinom_injective {α : Type*} (Δ : Finset α) (t : ℕ) :
    Function.Injective (finsetBinom Δ t) := by
  intro S T h
  exact Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))

/-- `A(Δ)` acts on the `t`-subsets of `Δ` as `A(Δ)` extended by the identity acts on the
`t`-subsets of `α`: the inclusion of `finsetBinom` is equivariant. -/
theorem tAction_ofSubtype_finsetBinom {α : Type*} [DecidableEq α] (Δ : Finset α) (t : ℕ)
    (g : Equiv.Perm {x // x ∈ Δ}) (S : binom {x // x ∈ Δ} t) :
    tAction t (Equiv.Perm.ofSubtype g) (finsetBinom Δ t S)
      = finsetBinom Δ t (tAction t g S) := by
  refine Subtype.ext ?_
  show ((S : Finset {x // x ∈ Δ}).map (Function.Embedding.subtype _)).image
      (Equiv.Perm.ofSubtype g)
    = ((S : Finset {x // x ∈ Δ}).image g).map (Function.Embedding.subtype _)
  rw [Finset.map_eq_image, Finset.map_eq_image, Finset.image_image, Finset.image_image]
  refine Finset.image_congr ?_
  intro x _
  show Equiv.Perm.ofSubtype g (x : α) = ((g x : {x // x ∈ Δ}) : α)
  rw [Equiv.Perm.ofSubtype_apply_of_mem g x.2]

end SubBinom

/-! ### The Johnson scheme `J(m,t)` as an object of `JohnsonSchemes Ω` -/

section JohnsonObject

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- Conjugation by a bijection `φ : α ≃ β`, as a homomorphism `S(β) → S(α)`. -/
def conjPerm {α β : Type*} (φ : α ≃ β) : Equiv.Perm β →* Equiv.Perm α where
  toFun σ := (φ.trans σ).trans φ.symm
  map_one' := by ext x; simp
  map_mul' σ τ := by ext x; simp

@[simp] theorem conjPerm_apply {α β : Type*} (φ : α ≃ β) (σ : Equiv.Perm β) (x : α) :
    conjPerm φ σ x = φ.symm (σ (φ x)) := rfl

/-- Definition 3.2.13.  The Johnson scheme `J(m,t)`, carried onto a set `V₀` of `C(m,t)`
points of `Ω` along a bijection `φ` with the `t`-subsets of `[m]`, as an object of
`JohnsonSchemes Ω`. -/
def johnsonPt {m t : ℕ} (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m) (V₀ : Set Ω)
    (φ : ↥V₀ ≃ binom (Fin m) t) : Pt (JohnsonSchemes Ω) :=
  ⟨V₀, ⟨fun x y => ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card,
    ⟨m, t, φ, ht, hmt, fun _ _ => rfl⟩⟩⟩

/-- Proposition 3.2.11.  `S_m` acting on the vertices of `J(m,t)`: the permutation `π` of
`[m]` acts on the `t`-subsets, and the bijection `φ` carries that action onto the vertex
set. -/
def johnsonPerm {m t : ℕ} (V₀ : Set Ω) (φ : ↥V₀ ≃ binom (Fin m) t) :
    Equiv.Perm (Fin m) →* Equiv.Perm ↥V₀ := (conjPerm φ).comp (tAction t)

omit [Fintype Ω] [DecidableEq Ω] in
/-- Proposition 3.2.11, in the form Prop. 9.1.1 uses: `Aut(J(m,t)) = S⁽ᵗ⁾_m`.  This is
`Babai.aut_johnsonScheme` transported along `φ`. -/
theorem range_johnsonPerm {m t : ℕ} (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m) (V₀ : Set Ω)
    (φ : ↥V₀ ≃ binom (Fin m) t) :
    (johnsonPerm V₀ φ).range = (JohnsonSchemes Ω).Aut (johnsonPt ht hmt V₀ φ) := by
  have hparams : IsJohnsonGraphParams (Fin m) t := ⟨ht, by simpa using hmt⟩
  ext σ
  constructor
  · rintro ⟨π, rfl⟩
    show ∀ x y : ↥V₀, _ = _
    intro x y
    show (((φ ((conjPerm φ) (tAction t π) x) : binom (Fin m) t) : Finset (Fin m)) \
      ((φ ((conjPerm φ) (tAction t π) y) : binom (Fin m) t) : Finset (Fin m))).card = _
    simp only [conjPerm_apply, Equiv.apply_symm_apply]
    exact card_sdiff_tAction t π (φ x) (φ y)
  · intro hσ
    have hσ' : ∀ x y : ↥V₀, ((φ (σ x) : Finset (Fin m)) \ (φ (σ y) : Finset (Fin m))).card
        = ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card := hσ
    have hτmem : conjPerm φ.symm σ ∈ (johnsonScheme (Fin m) t).Aut := by
      refine PartitionStructure.mem_aut.2 fun S T => ?_
      refine (PartitionStructure.ofColoring_color_eq_iff
        (fun S T : binom (Fin m) t => ((S : Finset (Fin m)) \ (T : Finset (Fin m))).card)
        _ _ S T).2 ?_
      have h := hσ' (φ.symm S) (φ.symm T)
      simpa using h
    rw [aut_johnsonScheme t hparams] at hτmem
    obtain ⟨π, -, hπ⟩ := Subgroup.mem_map.1 hτmem
    refine ⟨π, Equiv.ext fun x => ?_⟩
    show φ.symm (tAction t π (φ x)) = σ x
    rw [hπ]
    simp

end JohnsonObject

/-! ### Proposition 9.1.1 from Corollary 9.1.3 -/

/-- Proposition 9.1.1 (version 2.5, lines 3934–3937) with the conclusion of Corollary 9.1.3
as a hypothesis: *"This is an immediate consequence of Corollary 9.1.3."*

Spelled out, the paper's one-line proof runs as follows.  Let `F` be a reduction of cost
`cost` and `G` a canonical `(1-ε)`-partition functor on `C^F`; take the given `X = J(m,t)` and any
`X' ∈ F(X)`. By Prop. 6.0.4 the group `Aut(X,X')` has index at most `|F(X)| ≤ cost X` in
`Aut(X) = S⁽ᵗ⁾_m` (`Babai.relIndex_aut_pairCat_le`), so Corollary 9.1.3 applies to it and
gives a subset `Δ` of `[m]` with `A⁽ᵗ⁾(Δ) ≤ Aut(X,X')` acting primitively on the
`C(|Δ|,t) > (1-ε)·C(m,t)` vertices lying in `Δ`.  The blocks of `G(X,X')` are
`Aut(X,X')`-invariant (a canonical embedding restricts automorphisms,
`Babai.Func.IsCanonicalEmbedding.autHom_apply`), hence `A⁽ᵗ⁾(Δ)`-invariant, so by
primitivity a block contains all those vertices
(`Babai.exists_ncard_block_ge_of_primitive_on`) and
`ρ(G(X,X')) ≥ C(|Δ|,t) > (1-ε)·n`, against `ρ ≤ (1-ε)·n`.
The strict corollary needed here is the repair recorded under Corollary 9.1.3 strictness
in the corrected paper; its small-degree companion gives the same strict bound. Thus the
cost lower bound remains non-strict. -/
theorem prop_9_1_1_of_cor {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ε : ℝ} (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) (m t : ℕ) (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m)
    (cost : Pt (JohnsonSchemes Ω) → ℕ)
    (hfind : FindsAtMultCost (JohnsonSchemes Ω) (ColoredPartitions Ω ℕ) cost
      (fun X P => P.car = X.car ∧ letI : Fintype ↥P.car := Fintype.ofFinite _;
        P.obj.IsAlphaPartition (1 - ε)))
    (X : Pt (JohnsonSchemes Ω)) (φ : ↥X.car ≃ binom (Fin m) t)
    (hφ : ∀ x y, X.obj.val x y = ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card)
    (hcor : ∀ G : Subgroup (Equiv.Perm (Fin m)),
      (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) →
      ∃ Δ : Set (Fin m), (1 - ε) * ((m.choose t : ℕ) : ℝ) < (((Δ.ncard).choose t : ℕ) : ℝ) ∧
        pointwiseStabilizer (alternatingGroup (Fin m)) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (cost X : ℝ) := by
  classical
  by_contra! hs
  obtain ⟨Dc, E, F, Gf, hemb, hcost, hgood⟩ := hfind
  let V₀ : Set Ω := X.car
  have hAut : (JohnsonSchemes Ω).Aut (johnsonPt ht hmt V₀ φ) =
      (JohnsonSchemes Ω).Aut X := by
    ext σ
    change (∀ x y, ((φ (σ x) : Finset (Fin m)) \ (φ (σ y) : Finset (Fin m))).card =
      ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card) ↔
      ∀ x y, X.obj.val (σ x) (σ y) = X.obj.val x y
    simp only [hφ]
  have hV₀ : V₀.ncard = m.choose t := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr φ, card_binom]
    simp
  -- Work at the given input `X`; the cost at other objects is not used.
  haveI : Fintype ↥V₀ := Fintype.ofFinite _
  obtain ⟨X', hX'⟩ := tupleOf_nonempty F X
  have hPcar : (Gf.obj (pairPt F hX')).car = V₀ := (hgood X X' hX').1
  haveI instW : Fintype ↥(Gf.obj (pairPt F hX')).car := Fintype.ofFinite _
  have hPalpha : @ColoredPartition.IsAlphaPartition _ _
      ((Gf.obj (pairPt F hX')).obj) instW (1 - ε) := by
    rw [Subsingleton.elim instW (Fintype.ofFinite _)]
    exact (hgood X X' hX').2
  have hcardW : ∀ i : Fintype ↥(Gf.obj (pairPt F hX')).car,
      @Fintype.card _ i = m.choose t := by
    intro i
    rw [← @Nat.card_eq_fintype_card _ i, Nat.card_coe_set_eq, hPcar]
    exact hV₀
  -- Prop. 6.0.4 bounds the index by the cost at `X`.
  have hAindex : ((pairCat F).Aut (pairPt F hX')).relIndex
      ((JohnsonSchemes Ω).Aut X) ≤ cost X :=
    le_trans (relIndex_aut_pairCat_le F hX' (hcost X).1) (hcost X).2
  have hG₀index : (((pairCat F).Aut (pairPt F hX')).comap (johnsonPerm V₀ φ)).index
      ≤ cost X := by
    rw [Subgroup.index_comap, range_johnsonPerm ht hmt V₀ φ, hAut]
    exact hAindex
  obtain ⟨Δ, hΔsize, hΔstab, hΔcard⟩ :=
    hcor (((pairCat F).Aut (pairPt F hX')).comap (johnsonPerm V₀ φ))
      (lt_of_le_of_lt (by exact_mod_cast hG₀index) hs)
  -- (c) the `t`-subsets of `Δ`, and the Johnson group `A⁽ᵗ⁾(Δ)` acting on them
  set Df : Finset (Fin m) := (Set.toFinite Δ).toFinset with hDfdef
  have hDfcard : Df.card = Δ.ncard := (Set.ncard_eq_toFinset_card Δ (Set.toFinite Δ)).symm
  have hDfmem : ∀ x : Fin m, x ∈ Df ↔ x ∈ Δ := fun x => Set.Finite.mem_toFinset _
  have hΓcard : Nat.card {x : Fin m // x ∈ Df} = Δ.ncard := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hDfcard]
  have hpre : IsPreprimitive
      (inducedOnTSets (alternatingGroup {x : Fin m // x ∈ Df}) t)
      (binom {x : Fin m // x ∈ Df} t) :=
    isPreprimitive_inducedOnTSets_alternating (by omega) (by rw [hΓcard]; omega)
  -- the vertices of `J(m,t)` lying inside `Δ`
  set ι : binom {x : Fin m // x ∈ Df} t → ↥V₀ := fun S => φ.symm (finsetBinom Df t S)
    with hιdef
  have hιinj : Function.Injective ι := fun S T h =>
    finsetBinom_injective Df t (φ.symm.injective h)
  set ιW : binom {x : Fin m // x ∈ Df} t → ↥(Gf.obj (pairPt F hX')).car :=
    fun S => ⟨((ι S : ↥V₀) : Ω), by rw [hPcar]; exact (ι S).2⟩ with hιWdef
  have hιWinj : Function.Injective ιW := by
    intro S T h
    refine hιinj (Subtype.ext ?_)
    exact congrArg (fun w : ↥(Gf.obj (pairPt F hX')).car => (w : Ω)) h
  -- `A⁽ᵗ⁾(Δ) ≤ Aut(X,X')`
  have hmemA : ∀ g : alternatingGroup {x : Fin m // x ∈ Df},
      johnsonPerm V₀ φ
          (Equiv.Perm.ofSubtype (g : Equiv.Perm {x : Fin m // x ∈ Df}))
        ∈ (pairCat F).Aut (pairPt F hX') := by
    intro g
    refine hΔstab ⟨?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.1 g.2
    · intro x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (fun hc => hx ((hDfmem x).1 hc))
  set Λ : alternatingGroup {x : Fin m // x ∈ Df} →*
      ↥((pairCat F).Aut (pairPt F hX')) :=
    MonoidHom.codRestrict
      (((johnsonPerm V₀ φ).comp Equiv.Perm.ofSubtype).comp
        (alternatingGroup {x : Fin m // x ∈ Df}).subtype) _ hmemA with hΛdef
  set Ξ : alternatingGroup {x : Fin m // x ∈ Df} →*
      Equiv.Perm ↥(Gf.obj (pairPt F hX')).car :=
    (Gf.autHom (pairPt F hX')).comp Λ with hΞdef
  -- the action of `A⁽ᵗ⁾(Δ)` on those vertices is its action on the `t`-subsets of `Δ`
  have hΛι : ∀ (g : alternatingGroup {x : Fin m // x ∈ Df})
      (S : binom {x : Fin m // x ∈ Df} t),
      (Λ g).1 (ι S) = ι (tAction t (g : Equiv.Perm {x : Fin m // x ∈ Df}) S) := by
    intro g S
    show conjPerm φ
        (tAction t (Equiv.Perm.ofSubtype (g : Equiv.Perm {x : Fin m // x ∈ Df})))
        (φ.symm (finsetBinom Df t S))
      = φ.symm (finsetBinom Df t (tAction t (g : Equiv.Perm {x : Fin m // x ∈ Df}) S))
    rw [conjPerm_apply, Equiv.apply_symm_apply, tAction_ofSubtype_finsetBinom]
  have hΞι : ∀ (g : alternatingGroup {x : Fin m // x ∈ Df})
      (S : binom {x : Fin m // x ∈ Df} t),
      Ξ g (ιW S) = ιW (tAction t (g : Equiv.Perm {x : Fin m // x ∈ Df}) S) := by
    intro g S
    refine Subtype.ext ?_
    have h := hemb.autHom_apply (pairPt F hX') (Λ g) (ιW S)
    rw [show Ξ g (ιW S) = Gf.autHom (pairPt F hX') (Λ g) (ιW S) from rfl, h]
    show (((Λ g).1 (ι S) : ↥V₀) : Ω) = _
    rw [hΛι g S]
  -- the set `Y` of those vertices
  set Y : Set ↥(Gf.obj (pairPt F hX')).car := Set.range ιW with hYdef
  have hYcard : Y.ncard = (Δ.ncard).choose t := by
    rw [hYdef, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hιWinj, card_binom,
      hΓcard]
  have hAutmem : ∀ σ ∈ Ξ.range,
      σ ∈ (ColoredPartitions Ω ℕ).Aut (Gf.obj (pairPt F hX')) := by
    rintro σ ⟨g, rfl⟩
    exact Gf.range_autHom_le (pairPt F hX') ⟨Λ g, rfl⟩
  -- the combinatorial step
  obtain ⟨z, hz⟩ := exists_ncard_block_ge_of_primitive_on
    ((Gf.obj (pairPt F hX')).obj) Ξ.range Y
    (fun σ hσ x => (hAutmem σ hσ).1 x)
    (fun σ hσ x y hxy => ((hAutmem σ hσ).2 x y).1 hxy)
    (by
      rintro σ ⟨g, rfl⟩ x ⟨S, rfl⟩
      exact ⟨_, (hΞι g S).symm⟩)
    (by
      rintro x ⟨S, rfl⟩ y ⟨T, rfl⟩
      obtain ⟨σ, hσ⟩ := hpre.toIsPretransitive.exists_smul_eq S T
      obtain ⟨g, hg, hgσ⟩ := Subgroup.mem_map.1 σ.2
      refine ⟨Ξ ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
      rw [hΞι]
      congr 1
      rw [show tAction t g S = (σ : Equiv.Perm (binom {x : Fin m // x ∈ Df} t)) S from
        by rw [hgσ]]
      exact hσ)
    (by
      intro B hBY hBne hBblock
      have himg : ιW '' (ιW ⁻¹' B) = B := Set.image_preimage_eq_of_subset (by rwa [← hYdef])
      have hblk : IsBlock (inducedOnTSets (alternatingGroup {x : Fin m // x ∈ Df}) t)
          (ιW ⁻¹' B) := by
        rw [isBlock_iff_smul_eq_or_disjoint]
        intro σ
        obtain ⟨g, hg, hgσ⟩ := Subgroup.mem_map.1 σ.2
        have hsmulset : σ • (ιW ⁻¹' B) = (tAction t g) '' (ιW ⁻¹' B) := by
          rw [← Set.image_smul]
          refine Set.image_congr' (fun S => ?_)
          have hs1 : σ • S = (σ : Equiv.Perm (binom {x : Fin m // x ∈ Df} t)) S := rfl
          rw [hs1, ← hgσ]
        have himg2 : ιW '' (σ • (ιW ⁻¹' B)) = (Ξ ⟨g, hg⟩ : Equiv.Perm _) '' B := by
          conv_rhs => rw [← himg]
          rw [hsmulset, ← Set.image_comp, ← Set.image_comp]
          exact Set.image_congr' (fun S => (hΞι ⟨g, hg⟩ S).symm)
        rcases hBblock (Ξ ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩ with h | h
        · left
          refine Set.image_injective.2 hιWinj ?_
          rw [himg2, h, himg]
        · right
          rw [Set.disjoint_iff_inter_eq_empty]
          refine Set.image_injective.2 hιWinj ?_
          rw [Set.image_inter hιWinj, himg2, himg, h, Set.image_empty]
      rcases hpre.isTrivialBlock_of_isBlock hblk with hsub | huniv
      · right
        obtain ⟨w, hw⟩ := hBne
        obtain ⟨S, rfl⟩ := hBY hw
        refine ⟨ιW S, ?_⟩
        rw [← himg, hsub.eq_singleton_of_mem (show S ∈ ιW ⁻¹' B from hw),
          Set.image_singleton]
      · left
        rw [← himg, huniv, Set.image_univ, hYdef])
    hPalpha.1
    (by
      rw [hYcard]
      calc 2 ≤ Δ.ncard := by omega
        _ = (Δ.ncard).choose 1 := (Nat.choose_one_right _).symm
        _ ≤ (Δ.ncard).choose t := choose_le_choose_of_le_half (by omega) (by omega))
    (by
      rw [hcardW instW, hYcard]
      have h0 : (0 : ℝ) ≤ ((m.choose t : ℕ) : ℝ) := Nat.cast_nonneg _
      have hlt : ((m.choose t : ℕ) : ℝ) < 2 * (((Δ.ncard).choose t : ℕ) : ℝ) := by nlinarith
      exact_mod_cast hlt)
  -- the contradiction
  have hrho : (Δ.ncard).choose t ≤ @ColoredPartition.rho _ _ ((Gf.obj (pairPt F hX')).obj) instW := by
    calc (Δ.ncard).choose t = Y.ncard := hYcard.symm
      _ ≤ _ := hz
      _ ≤ _ := ColoredPartition.ncard_block_le_rho _ z
  have h1 := hPalpha.2
  rw [hcardW instW] at h1
  have h2 : (((Δ.ncard).choose t : ℕ) : ℝ)
      ≤ ((@ColoredPartition.rho _ _ ((Gf.obj (pairPt F hX')).obj) instW : ℕ) : ℝ) := by
    exact_mod_cast hrho
  linarith

end Babai
