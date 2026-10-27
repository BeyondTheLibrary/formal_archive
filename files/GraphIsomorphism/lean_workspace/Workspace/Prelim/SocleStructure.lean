/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Background group theory used by Section 10: internal direct products of nonabelian
simple groups.
-/
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Workspace.Prelim.Socle

/-!
# Internal direct products of nonabelian simple groups

The proof of Lemma 10.2.5 (Case 2) speaks of "the induced permutation action `G → S_s`
(permuting the copies of `R` by conjugation by elements of `G`)".  What makes this
meaningful is that the copies `R₁, …, R_s` of the socle decomposition are *exactly* the
minimal normal subgroups of the socle, so that every automorphism of the socle permutes
them.  This file proves the group theory behind that, for a family `R : ι → Subgroup G`
whose members lie in a subgroup `N`, are normalized by `N`, are independent, and generate
`N` (the hypotheses of `Babai.IsInternalDirectProduct`, spelled out so that this file can
live under `Prelim/`):

* `Babai.commute_of_directProduct`: distinct factors commute elementwise;
* `Babai.center_eq_bot_of_simple_nonabelian`: a nonabelian simple group has trivial
  center;
* `Babai.eq_one_of_central_of_directProduct`: `Z(N) = 1`;
* `Babai.exists_eq_of_simple_normal`: a nonabelian simple subgroup that is normalized by
  `N` and contained in `N` is one of the factors;
* `Babai.injective_of_directProduct`: the factors are pairwise distinct.

This is the content of Dixon–Mortimer, *Permutation Groups*, GTM 163, Theorem 4.3A (iii),
(iv), p. 112 ("if the subgroups `Kᵢ` are all nonabelian, then `K₁, …, K_m` are the only
minimal normal subgroups"); the paper cites nothing for it, so it is proved, not
axiomatized.
-/

namespace Babai

open Subgroup

variable {G : Type*} [Group G] {ι : Type*} {N : Subgroup G} {R : ι → Subgroup G}

/-- Distinct factors of an internal direct product commute elementwise: the commutator
`⁅x, y⁆` lies in `R i ⊓ R j = ⊥`. -/
theorem commute_of_directProduct (hle : ∀ i, R i ≤ N)
    (hnorm : ∀ i, ∀ g ∈ N, ∀ x ∈ R i, g * x * g⁻¹ ∈ R i) (hind : iSupIndep R)
    {i j : ι} (hij : i ≠ j) {x y : G} (hx : x ∈ R i) (hy : y ∈ R j) : Commute x y := by
  have hdisj : Disjoint (R i) (R j) := hind.pairwiseDisjoint hij
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ R j := mul_mem (hnorm j x (hle i hx) y hy) (inv_mem hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ R i := by
    have hmem : y * x⁻¹ * y⁻¹ ∈ R i := hnorm i y (hle j hy) x⁻¹ (inv_mem hx)
    have := mul_mem hx hmem
    simpa [mul_assoc] using this
  have hone : x * y * x⁻¹ * y⁻¹ = 1 := Subgroup.disjoint_def.1 hdisj h2 h1
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
  exact hone

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple_nonabelian {S : Type*} [Group S] [IsSimpleGroup S]
    (hnonab : ¬ ∀ a b : S, a * b = b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) inferInstance with h | h
  · exact h
  · exact absurd (fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm) hnonab

/-- The center of a subgroup `R i` of an internal direct product of nonabelian simple
groups is trivial, as a subgroup of `G`. -/
theorem eq_one_of_mem_center_factor {i : ι} [IsSimpleGroup (R i)]
    (hnonab : ¬ ∀ a b : R i, a * b = b * a) {x : G} (hx : x ∈ R i)
    (hcent : ∀ y ∈ R i, x * y = y * x) : x = 1 := by
  have hb := center_eq_bot_of_simple_nonabelian (S := R i) hnonab
  have : (⟨x, hx⟩ : R i) ∈ Subgroup.center (R i) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨y, hy⟩
    exact Subtype.ext (by simpa using (hcent y hy).symm)
  rw [hb, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

section Fintype

variable [Fintype ι] [DecidableEq ι]

/-- `Z(N) = 1` for an internal direct product `N` of nonabelian simple groups. -/
theorem eq_one_of_central_of_directProduct (hle : ∀ i, R i ≤ N)
    (hnorm : ∀ i, ∀ g ∈ N, ∀ x ∈ R i, g * x * g⁻¹ ∈ R i) (hind : iSupIndep R)
    (hsup : ⨆ i, R i = N) [hsimple : ∀ i, IsSimpleGroup (R i)]
    (hnonab : ∀ i, ¬ ∀ a b : R i, a * b = b * a)
    {z : G} (hz : z ∈ N) (hcent : ∀ y ∈ N, z * y = y * z) : z = 1 := by
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ R i → y ∈ R j → Commute x y :=
    fun i j hij x y hx hy => commute_of_directProduct hle hnorm hind hij hx hy
  set φ := Subgroup.noncommPiCoprod hcomm with hφ
  have hrange : φ.range = N := by rw [hφ, Subgroup.noncommPiCoprod_range, hsup]
  obtain ⟨x, rfl⟩ : ∃ x, φ x = z := by
    rw [← MonoidHom.mem_range, hrange]; exact hz
  have hxone : ∀ j, x j = 1 := by
    intro j
    -- split off the `j`-th coordinate
    have hsplit : x = Function.update x j 1 * Pi.mulSingle j (x j) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, Pi.mulSingle_eq_of_ne hij]
    have hcomm' : ∀ y ∈ R j, Commute y (φ (Function.update x j 1)) := by
      intro y hy
      refine Commute.symm ?_
      have : ∀ i, Commute ((Function.update x j 1 i : R i) : G) y := by
        intro i
        by_cases hij : i = j
        · subst hij; simp [Commute, SemiconjBy]
        · exact hcomm hij _ _ (Function.update x j 1 i).2 hy
      -- `y` commutes with the product
      rw [hφ, Subgroup.noncommPiCoprod_apply]
      refine Commute.symm (Finset.noncommProd_commute _ _ _ _ ?_)
      intro i _
      exact (this i).symm
    -- from centrality of `z = φ x`
    have hkey : ∀ y ∈ R j, (x j : G) * y = y * (x j : G) := by
      intro y hy
      have hzy : φ x * y = y * φ x := hcent y (hsup ▸ le_iSup R j hy)
      rw [hsplit, map_mul, Subgroup.noncommPiCoprod_mulSingle] at hzy
      have hc := (hcomm' y hy).symm
      -- cancel the common left factor
      have : φ (Function.update x j 1) * ((x j : G) * y)
          = φ (Function.update x j 1) * (y * (x j : G)) := by
        rw [← mul_assoc, ← mul_assoc, hzy, hc.eq, mul_assoc]
      exact mul_left_cancel this
    have := eq_one_of_mem_center_factor (i := j) (hnonab j) (x j).2 hkey
    exact Subtype.ext this
  have : x = 1 := funext fun i => hxone i
  rw [this, map_one]

omit [DecidableEq ι] in
/-- A nonabelian simple subgroup `S ≤ N`, normalized by `N`, is one of the factors. -/
theorem exists_eq_of_simple_normal (hle : ∀ i, R i ≤ N)
    (hnorm : ∀ i, ∀ g ∈ N, ∀ x ∈ R i, g * x * g⁻¹ ∈ R i) (hind : iSupIndep R)
    (hsup : ⨆ i, R i = N) [hsimple : ∀ i, IsSimpleGroup (R i)]
    (hnonab : ∀ i, ¬ ∀ a b : R i, a * b = b * a)
    {S : Subgroup G} (hSle : S ≤ N)
    (hSnorm : ∀ g ∈ N, ∀ x ∈ S, g * x * g⁻¹ ∈ S) [IsSimpleGroup S]
    (hSnonab : ¬ ∀ a b : S, a * b = b * a) : ∃ i, S = R i := by
  by_cases hmeet : ∃ i, ∃ x ∈ S, x ∈ R i ∧ x ≠ 1
  · obtain ⟨i, x, hxS, hxR, hx1⟩ := hmeet
    -- `S ⊓ R i` is a nontrivial normal subgroup of the simple group `S`, so `S ≤ R i`
    have hnormS : ((S ⊓ R i).subgroupOf S).Normal := by
      constructor
      rintro ⟨a, ha⟩ ⟨haS, haR⟩ ⟨b, hb⟩
      show b * a * b⁻¹ ∈ S ⊓ R i
      exact ⟨S.mul_mem (S.mul_mem hb haS) (S.inv_mem hb), hnorm i b (hSle hb) a haR⟩
    have hne : ((S ⊓ R i).subgroupOf S) ≠ ⊥ := by
      intro hbot
      have : (⟨x, hxS⟩ : S) ∈ (S ⊓ R i).subgroupOf S := ⟨hxS, hxR⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hx1 (congrArg Subtype.val this)
    have htop : ((S ⊓ R i).subgroupOf S) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hnormS).resolve_left hne
    have hSR : S ≤ R i := by
      intro a ha
      have : (⟨a, ha⟩ : S) ∈ (S ⊓ R i).subgroupOf S := htop ▸ Subgroup.mem_top _
      exact this.2
    -- now `S` is a nontrivial normal subgroup of the simple group `R i`
    refine ⟨i, le_antisymm hSR ?_⟩
    have hnormR : (S.subgroupOf (R i)).Normal := by
      constructor
      rintro ⟨a, ha⟩ (haS : a ∈ S) ⟨b, hb⟩
      show b * a * b⁻¹ ∈ S
      exact hSnorm b (hle i hb) a haS
    have hne' : (S.subgroupOf (R i)) ≠ ⊥ := by
      intro hbot
      have : (⟨x, hxR⟩ : R i) ∈ S.subgroupOf (R i) := hxS
      rw [hbot, Subgroup.mem_bot] at this
      exact hx1 (congrArg Subtype.val this)
    have htop' : (S.subgroupOf (R i)) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hnormR).resolve_left hne'
    intro a ha
    have : (⟨a, ha⟩ : R i) ∈ S.subgroupOf (R i) := htop' ▸ Subgroup.mem_top _
    exact this
  · -- `S` meets every factor trivially, hence centralizes `N`, hence is abelian
    rw [not_exists] at hmeet
    simp only [not_exists, not_and] at hmeet
    exfalso
    have hcentS : ∀ x ∈ S, ∀ y ∈ N, x * y = y * x := by
      intro x hxS y hy
      have hcomm : ∀ i, ∀ y ∈ R i, x * y = y * x := by
        intro i y hy
        have h1 : x * y * x⁻¹ * y⁻¹ ∈ R i := mul_mem (hnorm i x (hSle hxS) y hy) (inv_mem hy)
        have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
          have hmem : y * x⁻¹ * y⁻¹ ∈ S := hSnorm y (hle i hy) x⁻¹ (inv_mem hxS)
          have := mul_mem hxS hmem
          simpa [mul_assoc] using this
        have hz := not_not.1 (hmeet i _ h2 h1)
        have hc : Commute x y := by
          rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
          exact hz
        exact hc
      -- extend from the generators to all of `N`
      rw [← hsup] at hy
      refine Subgroup.iSup_induction R (C := fun z => x * z = z * x) hy ?_ ?_ ?_
      · intro i z hz; exact hcomm i z hz
      · simp
      · intro a b ha hb
        calc x * (a * b) = (a * x) * b := by rw [← mul_assoc, ha]
          _ = a * (b * x) := by rw [mul_assoc, hb]
          _ = a * b * x := by rw [mul_assoc]
    -- `S ≤ N` centralizes `N`, so `S` is abelian
    refine hSnonab fun a b => ?_
    exact Subtype.ext (hcentS a a.2 b (hSle b.2))

omit [Fintype ι] [DecidableEq ι] in
/-- The factors of an internal direct product of nontrivial subgroups are pairwise
distinct. -/
theorem injective_of_directProduct (hind : iSupIndep R) (hne : ∀ i, R i ≠ ⊥) :
    Function.Injective R := by
  intro i j hij
  by_contra hne'
  have hdisj : Disjoint (R i) (R j) := hind.pairwiseDisjoint hne'
  rw [hij, disjoint_self] at hdisj
  exact hne j hdisj

/-- If every factor of an internal direct product is abelian, so is the product. -/
theorem commute_of_directProduct_of_abelian (hle : ∀ i, R i ≤ N)
    (hnorm : ∀ i, ∀ g ∈ N, ∀ x ∈ R i, g * x * g⁻¹ ∈ R i) (hind : iSupIndep R)
    (hsup : ⨆ i, R i = N) (habel : ∀ i, ∀ a b : R i, a * b = b * a) :
    ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hgen : ∀ i, ∀ x ∈ R i, ∀ y ∈ N, x * y = y * x := by
    intro i x hx y hy
    rw [← hsup] at hy
    refine Subgroup.iSup_induction R (C := fun z => x * z = z * x) hy ?_ ?_ ?_
    · intro j z hz
      by_cases hij : i = j
      · subst hij
        have := habel i ⟨x, hx⟩ ⟨z, hz⟩
        simpa using congrArg Subtype.val this
      · exact commute_of_directProduct hle hnorm hind hij hx hz
    · simp
    · intro a b ha hb
      calc x * (a * b) = (a * x) * b := by rw [← mul_assoc, ha]
        _ = a * (b * x) := by rw [mul_assoc, hb]
        _ = a * b * x := by rw [mul_assoc]
  intro x hx y hy
  rw [← hsup] at hx
  refine Subgroup.iSup_induction R (C := fun z => z * y = y * z) hx ?_ ?_ ?_
  · intro i z hz
    exact hgen i z hz y hy
  · simp
  · intro a b ha hb
    calc a * b * y = a * (y * b) := by rw [mul_assoc, hb]
      _ = (y * a) * b := by rw [← mul_assoc, ha]
      _ = y * (a * b) := by rw [mul_assoc]

end Fintype

section Minimal

/-- Every nontrivial normal subgroup of a finite group contains a minimal normal subgroup
of the group. -/
theorem exists_isMinimalNormal_le {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    (hCnorm : ∀ g : G, ∀ x ∈ C, g * x * g⁻¹ ∈ C) (hne : C ≠ ⊥) :
    ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ C := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  haveI : WellQuasiOrderedLE (Subgroup G) := Finite.to_wellQuasiOrderedLE
  have hCP : (fun M : Subgroup G => M.Normal ∧ M ≠ ⊥) C :=
    ⟨⟨fun n hn g => hCnorm g n hn⟩, hne⟩
  obtain ⟨M, hMC, hMmin⟩ :=
    exists_minimal_le_of_wellFoundedLT (fun M : Subgroup G => M.Normal ∧ M ≠ ⊥) C hCP
  refine ⟨M, ⟨hMmin.1.1, hMmin.1.2, ?_⟩, hMC⟩
  intro M' hM'norm hM'ne hM'le
  exact le_antisymm hM'le (hMmin.2 ⟨hM'norm, hM'ne⟩ hM'le)

/-- The socle is conjugation-invariant: it is a supremum of normal subgroups. -/
theorem socle_conj_mem {G : Type*} [Group G] (g : G) {x : G} (hx : x ∈ socle G) :
    g * x * g⁻¹ ∈ socle G := by
  rw [socle, sSup_eq_iSup'] at hx ⊢
  refine Subgroup.iSup_induction
    (fun M : {N : Subgroup G // IsMinimalNormal N} => (M : Subgroup G))
    (C := fun z => g * z * g⁻¹ ∈
      ⨆ M : {N : Subgroup G // IsMinimalNormal N}, (M : Subgroup G)) hx ?_ ?_ ?_
  · intro M z hz
    exact le_iSup (fun M : {N : Subgroup G // IsMinimalNormal N} => (M : Subgroup G)) M
      (M.2.1.conj_mem z hz g)
  · simp
  · intro a b ha hb
    have h : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [h]
    exact mul_mem ha hb

/-- A minimal normal subgroup is contained in the socle. -/
theorem le_socle_of_isMinimalNormal {G : Type*} [Group G] {M : Subgroup G}
    (hM : IsMinimalNormal M) : M ≤ socle G :=
  le_sSup hM

end Minimal

end Babai
