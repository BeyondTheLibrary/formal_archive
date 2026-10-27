/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Theorem 10.2.4, proved (it was an axiom citing Dixon–Mortimer, Thm. 4.1A).
-/
import Workspace.AltQuotients.ONanScottCore

/-!
# Theorem 10.2.4

> **Theorem 10.2.4** (Extracted from [DiM, Thm 4.1A]).  Let `G ≤ S_n` be a primitive group
> with socle `Soc(G) ≅ R^s` where `R` is a nonabelian simple group.  If `s ≥ 2` then
> either (a) `n ≥ |R|^{s−1}` or (b) there exists a proper divisor `d | s` and a primitive
> group `U` with socle `R^d` such that `n = ℓ^{s/d}` where `ℓ` is the degree of `U`.

The paper cites this from Dixon–Mortimer, *Permutation Groups*, GTM 163, Springer 1996,
Theorem 4.1A (the O'Nan–Scott theorem).  It was an axiom; it is proved here, with the
statement unchanged, along the proof in [DiM, §4.3, §4.5–4.7]:

* if `G` has two minimal normal subgroups `M₁ ≅ M₂` ([DiM, Thm. 4.3B]), both are regular,
  `M₁ ≅ R^{s/2}`, `n = |R|^{s/2}`: case (a) if `s = 2`, and case (b) with `d = 2` and the
  diagonal group `R² ⋊ S₂` of degree `|R|` if `s ≥ 4` (this is [DiM, Thm. 4.6A (iii)] with
  the components of type (ii));
* otherwise the socle `H` is the unique minimal normal subgroup.  If `H` is regular,
  `n = |R|^s`, case (a) ([DiM, §4.7]).  If not, [DiM, Thm. 4.6A] applies, in the form
  `Babai.ONS.core_case1` (Case 1: case (b) with `d = 1`) and `Babai.ONS.core_case2`
  (Case 2: case (a) or case (b) with a diagonal group).

The group `U` of case (b) is built from `R` alone (the diagonal type) or from `R` and the
automorphisms induced by `G` (the almost simple type), see
`Workspace/AltQuotients/ONanScottConstr.lean`.
-/

universe u v

namespace Babai

open MulAction Subgroup

/-- **Theorem 10.2.4** (Extracted from `[DiM, Thm 4.1A]`), §10.2.

Formerly an axiom; it is now proved, with the statement unchanged (route: module
docstring).

Quoted from the paper:

> **Theorem 10.2.4** (Extracted from [DiM, Thm 4.1A]).  Let `G ≤ S_n` be a primitive group
> with socle `Soc(G) ≅ R^s` where `R` is a nonabelian simple group.  If `s ≥ 2` then
> either (a) `n ≥ |R|^{s−1}` or (b) there exists a proper divisor `d | s` and a primitive
> group `U` with socle `R^d` such that `n = ℓ^{s/d}` where `ℓ` is the degree of `U`.

**Citation.** `[DiM, Thm. 4.1A]` (Dixon–Mortimer, *Permutation Groups*, GTM 163, 1996),
summarizing `[Sco]`, `[AsS]` and `[LiePS]` = Martin W. Liebeck, Cheryl E. Praeger, Jan
Saxl, *On the O'Nan–Scott theorem for finite primitive permutation groups*, J. Austral.
Math. Soc. (A) **44** (1988), 389–396.  The paper says: "This result is an immediate
consequence of the 'summary' of the O'Nan–Scott–Aschbacher Theorem … given by Dixon and
Mortimer … as Theorem 4.1A.  We further compress the result to suit our purposes."  The
statement is Babai's compression, verbatim, not a verbatim theorem of `[DiM]`.

**Used where.** Proposition 10.2.3, which the paper proves from it.

**Warning (consistency).** A "proper divisor `d | s`" is `d ∣ s ∧ d < s`; the paper uses
`d < s` at the corresponding place in the proof of Prop. 10.2.3.  `s / d` is exact since
`d ∣ s`.  `|R|^{s-1}` uses truncated subtraction, harmless since `s ≥ 2`.  The group `U`
of case (b) is produced on a permutation domain `Ω'` in the same universe as `Ω`, which is
no strengthening: a permutation group can be transported along any bijection of its
domain, and Prop. 10.2.3 applies the theorem repeatedly to the groups it produces.  "Nonabelian" is
`¬ ∀ a b : R, a * b = b * a`.

**Universes.** The simple group `R` lives in an arbitrary universe `v`, as the paper's
"`R` a nonabelian simple group" has no universe attached.  This is not a strengthening:
for a *finite* group the statement at one universe implies it at every other, by
transport along `Finite.exists_type_univ_nonempty_mulEquiv` — the same argument that
`Babai.schreierHypothesis_iff` carries out for Schreier's Hypothesis.  The polymorphic
form is what the call sites in Lemma 10.2.5 need, where `R` is a socle factor of a
permutation group on `Ω : Type u`. -/
theorem theorem_10_2_4 {Ω : Type u} [Finite Ω] (G : Subgroup (Equiv.Perm Ω))
    (hG : IsPrimitive G) (R : Type v) [Group R] [Finite R] [IsSimpleGroup R]
    (hRnonab : ¬ ∀ a b : R, a * b = b * a) {s : ℕ} (hs : 2 ≤ s)
    (hsoc : Nonempty (socle G ≃* (Fin s → R))) :
    Nat.card R ^ (s - 1) ≤ Nat.card Ω ∨
      ∃ d : ℕ, d ∣ s ∧ d < s ∧
        ∃ (Ω' : Type u) (_ : Finite Ω') (U : Subgroup (Equiv.Perm Ω')),
          IsPrimitive U ∧ Nonempty (socle U ≃* (Fin d → R)) ∧
            Nat.card Ω = Nat.card Ω' ^ (s / d) := by
  classical
  obtain ⟨e⟩ := hsoc
  set H := socle G with hHdef
  haveI hHn : H.Normal := ⟨fun x hx g => socle_conj_mem g hx⟩
  haveI := hG.nontrivial_dom
  obtain ⟨α⟩ := hG.nonempty_dom
  have hR1 : 1 < Nat.card R := Finite.one_lt_card
  have hRpos : 0 < Nat.card R := Nat.card_pos
  obtain ⟨r₀, hr₀⟩ := exists_ne (1 : R)
  have hi₀ : 0 < s := by omega
  set i₀ : Fin s := ⟨0, hi₀⟩
  haveI : Nonempty (Fin s) := ⟨i₀⟩
  haveI : Nontrivial H := e.symm.injective.nontrivial
  have hHne : H ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot H).1 inferInstance
  have hHtr : IsPretransitive H Ω := isPretransitive_of_normal_of_isPrimitive hG H hHne
  obtain ⟨M₁, h₁, hM₁H⟩ :=
    exists_isMinimalNormal_le (C := H) (fun g x hx => socle_conj_mem g hx) hHne
  by_cases h2 : ∃ M₂ : Subgroup G, IsMinimalNormal M₂ ∧ M₂ ≠ M₁
  · -- two minimal normal subgroups `M₁ ≠ M₂` ([DiM, Thm. 4.3B]): both are regular
    obtain ⟨M₂, h₂, hne⟩ := h2
    haveI := h₁.1
    haveI := h₂.1
    have hM₂H : M₂ ≤ H := le_socle_of_isMinimalNormal h₂
    have hd := disjoint_of_isMinimalNormal h₁ h₂ hne.symm
    have ht₁ := isPretransitive_of_normal_of_isPrimitive hG M₁ h₁.2.1
    have ht₂ := isPretransitive_of_normal_of_isPrimitive hG M₂ h₂.2.1
    have hc₁ : Nat.card M₁ = Nat.card Ω := by
      refine le_antisymm ?_ (card_le_of_isPretransitive ht₁ α)
      rw [eq_centralizer_of_isMinimalNormal hG h₂ h₁ hne]
      exact card_centralizer_le ht₂ α
    have hc₂ : Nat.card M₂ = Nat.card Ω := by
      refine le_antisymm ?_ (card_le_of_isPretransitive ht₂ α)
      rw [eq_centralizer_of_isMinimalNormal hG h₁ h₂ hne.symm]
      exact card_centralizer_le ht₁ α
    -- the socle is `M₁ ⊔ M₂`
    have hset : {M : Subgroup G | IsMinimalNormal M} = {M₁, M₂} := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hN
        by_cases hN1 : N = M₁
        · exact Or.inl hN1
        · exact Or.inr (isMinimalNormal_eq_of_three hG h₁ hN h₂ (Ne.symm hN1) hne.symm)
      · rintro (rfl | rfl)
        · exact h₁
        · exact h₂
    have hHsup : H = M₁ ⊔ M₂ := by rw [hHdef, socle, hset, sSup_pair]
    -- transfer to `R^s`: `M₁ ≅ R^{S₁}`, `M₂ ≅ R^{S₂}` with `S₁ ⊔ S₂ = {1, …, s}`
    set M₁' := (M₁.comap H.subtype).map e.toMonoidHom with hM₁'
    set M₂' := (M₂.comap H.subtype).map e.toMonoidHom with hM₂'
    haveI : M₁'.Normal := (h₁.1.comap _).map _ e.surjective
    haveI : M₂'.Normal := (h₂.1.comap _).map _ e.surjective
    have hcard' : ∀ M : Subgroup G, M ≤ H →
        Nat.card ((M.comap H.subtype).map e.toMonoidHom) = Nat.card M := by
      intro M hM
      rw [Subgroup.card_map_of_injective e.injective]
      have := Subgroup.card_map_of_injective (K := M.comap H.subtype) H.subtype_injective
      rw [Subgroup.map_comap_eq_self (by rwa [H.range_subtype])] at this
      exact this.symm
    set S₁ := Finset.univ.filter fun i => ONS.coord (R := R) i ≤ M₁' with hS₁
    set S₂ := Finset.univ.filter fun i => ONS.coord (R := R) i ≤ M₂' with hS₂
    have hM₁'eq : M₁' = ONS.suppSub (S₁ : Set (Fin s)) := ONS.normal_eq_suppSub hRnonab M₁'
    have hM₂'eq : M₂' = ONS.suppSub (S₂ : Set (Fin s)) := ONS.normal_eq_suppSub hRnonab M₂'
    have hcS₁ : Nat.card R ^ S₁.card = Nat.card Ω := by
      rw [← ONS.card_suppSub, ← hM₁'eq, hcard' M₁ hM₁H, hc₁]
    have hcS₂ : Nat.card R ^ S₂.card = Nat.card Ω := by
      rw [← ONS.card_suppSub, ← hM₂'eq, hcard' M₂ hM₂H, hc₂]
    have hmemM' : ∀ (M : Subgroup G) (x : H), (x : G) ∈ M →
        e x ∈ (M.comap H.subtype).map e.toMonoidHom := by
      intro M x hx
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
      exact hx
    have hdisjS : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have hm1 : Pi.mulSingle i r₀ ∈ M₁' :=
        (Finset.mem_filter.1 hi1).2 (ONS.mulSingle_mem_coord i r₀)
      have hm2 : Pi.mulSingle i r₀ ∈ M₂' :=
        (Finset.mem_filter.1 hi2).2 (ONS.mulSingle_mem_coord i r₀)
      rw [hM₁', Subgroup.mem_map_equiv] at hm1
      rw [hM₂', Subgroup.mem_map_equiv] at hm2
      have := Subgroup.disjoint_def.1 hd hm1 hm2
      have h1 : e.symm (Pi.mulSingle i r₀) = 1 := Subtype.ext this
      rw [MulEquiv.symm_apply_eq, map_one] at h1
      exact hr₀ (by simpa using congrFun h1 i)
    have hcover : S₁ ∪ S₂ = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      by_contra hcon
      rw [Finset.mem_union, not_or] at hcon
      obtain ⟨hn1, hn2⟩ := hcon
      set h : H := e.symm (Pi.mulSingle i r₀) with hh
      have hmem : ((h : G)) ∈ ((M₁ ⊔ M₂ : Subgroup G) : Set G) := by
        rw [← hHsup]; exact h.2
      rw [Subgroup.mul_normal M₁ M₂] at hmem
      obtain ⟨m₁, hm₁, m₂, hm₂, hm⟩ := hmem
      set a : H := ⟨m₁, hM₁H hm₁⟩
      set b : H := ⟨m₂, hM₂H hm₂⟩
      have hab : h = a * b := Subtype.ext hm.symm
      have ha : e a ∈ M₁' := hmemM' M₁ a hm₁
      have hb : e b ∈ M₂' := hmemM' M₂ b hm₂
      rw [hM₁'eq] at ha
      rw [hM₂'eq] at hb
      have hf : Pi.mulSingle i r₀ = e a * e b := by
        rw [← map_mul, ← hab, hh, MulEquiv.apply_symm_apply]
      have := congrFun hf i
      rw [Pi.mul_apply, ha i (by simpa using hn1), hb i (by simpa using hn2), mul_one] at this
      simp at this
      exact hr₀ this
    have hsum : S₁.card + S₂.card = s := by
      rw [← Finset.card_union_of_disjoint hdisjS, hcover, Finset.card_univ, Fintype.card_fin]
    have heqS : S₁.card = S₂.card :=
      Nat.pow_right_injective (by omega : 2 ≤ Nat.card R)
        (hcS₁.trans hcS₂.symm)
    set j := S₁.card with hj
    have hsj : s = 2 * j := by omega
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · left
      have : j = 1 := by omega
      rw [← hcS₁, hsj, this]
    · right
      obtain ⟨Ω', hΩ', U, hU, hsocU, hcardU⟩ : ∃ (Ω' : Type u) (_ : Finite Ω')
          (U : Subgroup (Equiv.Perm Ω')), IsPrimitive U ∧ Nonempty (socle U ≃* (Fin 2 → R)) ∧
            Nat.card Ω' = Nat.card R ^ (2 - 1) := ONS.exists_diag_primitive hRnonab le_rfl
      refine ⟨2, ⟨j, hsj⟩, by omega, Ω', hΩ', U, hU, hsocU, ?_⟩
      rw [hcardU, ← hcS₁, hsj, Nat.mul_div_cancel_left _ (by norm_num)]
      simp
  · -- `H` is the unique minimal normal subgroup
    push Not at h2
    have hset : {M : Subgroup G | IsMinimalNormal M} = {M₁} := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨h2 M, fun h => h ▸ h₁⟩
    have hHM : H = M₁ := by rw [hHdef, socle, hset, sSup_singleton]
    have hHmin : IsMinimalNormal H := hHM ▸ h₁
    -- the point stabilizer and the automorphisms of `R^s` it induces
    set Γ : Subgroup G := stabilizer G α with hΓ
    set ψ : Γ →* MulAut (Fin s → R) :=
      (MulAut.congr e).toMonoidHom.comp ((MulAut.conjNormal (H := H)).comp Γ.subtype) with hψ
    have hψapp : ∀ (g : Γ) (x : Fin s → R),
        ψ g x = e (MulAut.conjNormal (g : G) (e.symm x)) := fun g x => rfl
    set X : Subgroup (Fin s → R) := (stabilizer H α).map e.toMonoidHom with hX
    have hmemX : ∀ x, x ∈ X ↔ ((e.symm x : H) : G) • α = α := by
      intro x; rw [hX, Subgroup.mem_map_equiv]; rfl
    have hconjfix : ∀ γ : G, γ • α = α → ∀ h : H, (h : G) • α = α →
        ((MulAut.conjNormal γ h : H) : G) • α = α := by
      intro γ hγ h hh
      rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_eq_iff.2 hγ.symm, hh, hγ]
    have hXinv : ONS.PsiInv ψ X := by
      intro g x hx
      rw [hmemX] at hx ⊢
      rw [hψapp, MulEquiv.symm_apply_apply]
      exact hconjfix g g.2 _ hx
    have hindex : Nat.card Ω = X.index := by
      rw [hX, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective,
        index_stabilizer_of_transitive]
    -- `G = H G_α`
    have hGHΓ : ∀ g : G, ∃ h : H, ∃ γ ∈ Γ, g = (h : G) * γ := by
      intro g
      obtain ⟨h, hh⟩ := hHtr.exists_smul_eq α (g • α)
      refine ⟨h, (h : G)⁻¹ * g, ?_, by group⟩
      show ((h : G)⁻¹ * g) • α = α
      rw [mul_smul, ← hh]
      exact inv_smul_smul (h : G) α
    -- conjugation by `G_α` on the subgroups of `H` coming from `ψ`-invariant subgroups
    have hconj : ∀ Y : Subgroup (Fin s → R), ONS.PsiInv ψ Y → ∀ γ ∈ Γ,
        ∀ y ∈ (Y.comap e.toMonoidHom).map H.subtype,
          γ * y * γ⁻¹ ∈ (Y.comap e.toMonoidHom).map H.subtype := by
      intro Y hY γ hγ y hy
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨MulAut.conjNormal γ h, ?_, ?_⟩
      · have := hY ⟨γ, hγ⟩ (e h) hh
        rw [hψapp, MulEquiv.symm_apply_apply] at this
        exact this
      · exact MulAut.conjNormal_apply γ h
    have h1 : ∀ Y : Subgroup (Fin s → R), Y.Normal → ONS.PsiInv ψ Y → Y = ⊥ ∨ Y = ⊤ := by
      intro Y hYn hYinv
      set Y₁ := Y.comap e.toMonoidHom with hY₁
      haveI : Y₁.Normal := hYn.comap _
      set Y₂ := Y₁.map H.subtype with hY₂
      have hY₂n : Y₂.Normal := by
        constructor
        intro y hy g
        obtain ⟨h, γ, hγ, rfl⟩ := hGHΓ g
        have hy' := hconj Y hYinv γ hγ y hy
        obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.1 hy'
        have : (h : G) * γ * y * ((h : G) * γ)⁻¹ = H.subtype (h * h' * h⁻¹) := by
          simp only [map_mul, map_inv, Subgroup.coe_subtype]
          rw [show (h' : G) = γ * y * γ⁻¹ from hh'eq]
          group
        rw [this]
        exact Subgroup.mem_map_of_mem _ (‹Y₁.Normal›.conj_mem h' hh' h)
      have hY₂le : Y₂ ≤ H := (Subgroup.map_le_range _ _).trans_eq H.range_subtype
      by_cases hb : Y₂ = ⊥
      · left
        rw [eq_bot_iff]
        intro y hy
        have : ((e.symm y : H) : G) ∈ Y₂ :=
          Subgroup.mem_map_of_mem _ (show e (e.symm y) ∈ Y by simpa using hy)
        rw [hb, Subgroup.mem_bot] at this
        have h1 : e.symm y = 1 := Subtype.ext this
        rw [MulEquiv.symm_apply_eq, map_one] at h1
        rw [h1]; exact Subgroup.one_mem _
      · right
        have heq := hHmin.2.2 Y₂ hY₂n hb hY₂le
        rw [eq_top_iff]
        intro y _
        have : ((e.symm y : H) : G) ∈ Y₂ := by rw [heq]; exact (e.symm y).2
        obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.1 this
        have : h' = e.symm y := Subtype.ext hh'eq
        have hy : e h' ∈ Y := hh'
        rwa [this, MulEquiv.apply_symm_apply] at hy
    haveI hpre := (isPrimitive_iff_isPreprimitive G).1 hG
    have hcoat : IsCoatom Γ := IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G α
    have h2 : ∀ Y : Subgroup (Fin s → R), X ≤ Y → ONS.PsiInv ψ Y → Y = X ∨ Y = ⊤ := by
      intro Y hXY hYinv
      set Y₁ := Y.comap e.toMonoidHom with hY₁
      set Y₂ := Y₁.map H.subtype with hY₂
      rcases hcoat.le_iff.1 (le_sup_left : Γ ≤ Γ ⊔ Y₂) with h | h
      · right
        have hnorm : Γ ≤ Subgroup.normalizer (Y₂ : Set G) := by
          intro γ hγ
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · exact hconj Y hYinv γ hγ y
          · intro hy
            have := hconj Y hYinv γ⁻¹ (inv_mem hγ) _ hy
            have heq : γ⁻¹ * (γ * y * γ⁻¹) * γ⁻¹⁻¹ = y := by group
            rwa [heq] at this
        rw [eq_top_iff]
        intro f _
        have hmem : ((e.symm f : H) : G) ∈ ((Γ ⊔ Y₂ : Subgroup G) : Set G) := by
          rw [h]; trivial
        rw [Subgroup.coe_mul_of_left_le_normalizer_right Γ Y₂ hnorm] at hmem
        obtain ⟨γ, hγ, y, hy, hγy⟩ := hmem
        obtain ⟨y₁, hy₁, rfl⟩ := Subgroup.mem_map.1 hy
        set c : H := e.symm f * y₁⁻¹ with hc
        have hcγ : (c : G) = γ := by
          rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, ← hγy]
          simp
        have hcX : e c ∈ X := by
          rw [hmemX, MulEquiv.symm_apply_apply, hcγ]
          exact hγ
        have hf : f = e c * e y₁ := by
          rw [← map_mul, hc, inv_mul_cancel_right, MulEquiv.apply_symm_apply]
        rw [hf]
        exact mul_mem (hXY hcX) hy₁
      · left
        have hY₂Γ : Y₂ ≤ Γ := h ▸ le_sup_right
        refine le_antisymm (fun y hy => ?_) hXY
        rw [hmemX]
        have : ((e.symm y : H) : G) ∈ Y₂ :=
          Subgroup.mem_map_of_mem _ (show e (e.symm y) ∈ Y by simpa using hy)
        exact hY₂Γ this
    have h3 : X ≠ ⊤ := by
      intro h
      obtain ⟨β, hβ⟩ := exists_ne α
      obtain ⟨c, hc⟩ := hHtr.exists_smul_eq α β
      have hcX : e c ∈ X := by rw [h]; trivial
      rw [hmemX, MulEquiv.symm_apply_apply] at hcX
      exact hβ (hc.symm.trans hcX)
    -- the analysis inside `R^s`
    have hcardι : Fintype.card (Fin s) = s := Fintype.card_fin s
    by_cases hXbot : X = ⊥
    · left
      rw [hindex, hXbot, Subgroup.index_bot, Nat.card_fun, Nat.card_fin]
      exact Nat.pow_le_pow_right hRpos (Nat.sub_le s 1)
    by_cases hfull : ONS.rpart X i₀ = ⊤
    · have hall : ∀ i, ONS.rpart X i = ⊤ := by
        intro i
        rw [← Subgroup.card_eq_iff_eq_top, ONS.card_rpart_eq hRnonab ψ hXinv h1 i i₀, hfull,
          Subgroup.card_top]
      have := ONS.core_case2.{_, _, _, u} hRnonab ψ hXinv h1 h3 hall (by rw [hcardι]; exact hs)
      rw [hcardι] at this
      rwa [hindex]
    · right
      obtain ⟨Ω', hΩ', U, hU, hsocU, hcard⟩ :=
        ONS.core_case1.{_, _, _, u} hRnonab ψ hXinv h1 h2 hXbot i₀ hfull
      obtain ⟨φ⟩ := hsocU
      refine ⟨1, one_dvd s, by omega, Ω', hΩ', U, hU,
        ⟨φ.trans (MulEquiv.funUnique (Fin 1) R).symm⟩, ?_⟩
      rw [hindex, hcard, hcardι, Nat.div_one]


end Babai
