/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 12 (Verification of top action): definitions.
-/
import Workspace.Luks.Instances

/-!
# Section 12, definitions

## The translation between the paper and Lean

Section 12 inherits the conventions of Section 11 (see the header of
`Workspace/Luks/Defs.lean`):

* the paper's `u^τ` is Lean's `τ u`;
* the paper's product `στ` ("first `σ`, then `τ`") is Lean's `τ * σ`;
* consequently the paper's **right** coset `Kσ = {κσ | κ ∈ K}` is Lean's **left**
  translate `σ • K` (`Babai.mem_perm_smul_set`), and the paper's **left** coset
  `σK = {σκ | κ ∈ K}` is Lean's **right** translate `{κ * σ | κ ∈ K}`, written
  `Babai.rightTranslate K σ` below.

Section 12 uses both: Definition 12.0.3 is about the paper's right cosets `Hτ`, while the
displayed identities of Proposition 12.0.1 (`ϕ⁻¹(σ̄) = σN`, `Iso_G(x,y) = σ Iso_G(x^σ,y)`)
are about the paper's left cosets.

## Contents

* Definition 12.0.3: subcosets, coset generators (`Babai.IsSubcoset`,
  `Babai.subcosetClosure`, `Babai.IsCosetGenerators`).
* The data attached to a homomorphism `ϕ : G → H` of permutation groups: the set of
  liftings `ϕ⁻¹(σ̄) ⊆ S(Ω)` (`Babai.preimageSet`) and the kernel `N = ker(ϕ)` viewed as a
  subgroup of `S(Ω)` (`Babai.kerSubgroup`).
The model of the algorithmic statements — the String Isomorphism *instance*
(`Babai.SIInstance`) and the *reduction* (`Babai.SIReduction`) — lives in
`Workspace/Luks/Instances.lean`, since it is §11.1's vocabulary and §13.1 uses it too.

The *running time* ("at polynomial cost per instance") is **not** modelled here; see the
pending entry for Section 12 in the corrected paper.
-/

universe u v w

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

/-! ### The paper's left cosets -/

section LeftCoset

variable {Ω : Type*}

/-- The paper's **left** coset `σK = {σκ | κ ∈ K}`.  Under the translation of the header
(the paper's `στ` is Lean's `τ * σ`) this is the set `{κ * σ | κ ∈ K}`, the right
translate of `K` by `σ` in Lean.  One lemma, `Babai.mem_rightTranslate`, carries the
convention. -/
def rightTranslate (K : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) : Set (Equiv.Perm Ω) :=
  (· * σ) '' K

theorem mem_rightTranslate {K : Set (Equiv.Perm Ω)} {σ τ : Equiv.Perm Ω} :
    τ ∈ rightTranslate K σ ↔ τ * σ⁻¹ ∈ K := by
  constructor
  · rintro ⟨κ, hκ, rfl⟩; simpa using hκ
  · intro h; exact ⟨τ * σ⁻¹, h, by group⟩

theorem rightTranslate_eq (K : Set (Equiv.Perm Ω)) (σ : Equiv.Perm Ω) :
    rightTranslate K σ = {τ | ∃ κ ∈ K, τ = κ * σ} := by
  ext τ
  simp only [rightTranslate, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨κ, hκ, rfl⟩; exact ⟨κ, hκ, rfl⟩
  · rintro ⟨κ, hκ, rfl⟩; exact ⟨κ, hκ, rfl⟩

end LeftCoset

/-! ### Definition 12.0.3 (subcosets and coset generators) -/

section Subcoset

variable {Gr : Type*} [Group Gr]

/-- §12, **Definition 12.0.3**.

> A subcoset of a group `G` is a coset of a subgroup.

Stated with the paper's right cosets `Hτ`, i.e. Lean's left translates `τ • H` (see the
header).  The notion does not depend on the side: `Babai.isSubcoset_iff_left`. -/
def IsSubcoset (C : Set Gr) : Prop := ∃ (H : Subgroup Gr) (τ : Gr), C = τ • (H : Set Gr)

theorem mem_mul_singleton {s : Set Gr} {τ g : Gr} : g ∈ s * ({τ} : Set Gr) ↔ g * τ⁻¹ ∈ s := by
  rw [Set.mul_singleton]
  constructor
  · rintro ⟨h, hh, rfl⟩; simpa using hh
  · intro h; exact ⟨g * τ⁻¹, h, by group⟩

/-- The subgroup `τ⁻¹C` attached to a set `C` closed under `(a,b,c) ↦ a b⁻¹ c` and a
point `τ ∈ C`. -/
private def cosetSubgroup (C : Set Gr) (τ : Gr) (hτ : τ ∈ C)
    (hcl : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a * b⁻¹ * c ∈ C) : Subgroup Gr where
  carrier := {h | τ * h ∈ C}
  one_mem' := by simpa using hτ
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : τ * (a * b) = (τ * a) * τ⁻¹ * (τ * b) := by group
    rw [this]
    exact hcl _ ha _ hτ _ hb
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : τ * a⁻¹ = τ * (τ * a)⁻¹ * τ := by group
    rw [this]
    exact hcl _ hτ _ ha _ hτ

private theorem eq_smul_cosetSubgroup (C : Set Gr) (τ : Gr) (hτ : τ ∈ C)
    (hcl : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a * b⁻¹ * c ∈ C) :
    C = τ • ((cosetSubgroup C τ hτ hcl : Subgroup Gr) : Set Gr) := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
  show g ∈ C ↔ τ * (τ⁻¹ * g) ∈ C
  rw [mul_inv_cancel_left]

/-- The elementary characterization of a subcoset: a nonempty set closed under
`(a, b, c) ↦ a b⁻¹ c`.  This is what makes intersections of subcosets subcosets
(the parenthetical remark of Definition 12.0.3). -/
theorem isSubcoset_iff {C : Set Gr} :
    IsSubcoset C ↔ C.Nonempty ∧ ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a * b⁻¹ * c ∈ C := by
  constructor
  · rintro ⟨H, τ, rfl⟩
    refine ⟨⟨τ, ⟨1, one_mem _, by simp⟩⟩, ?_⟩
    rintro a ha b hb c hc
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at ha hb hc ⊢
    have : τ⁻¹ * (a * b⁻¹ * c) = (τ⁻¹ * a) * (τ⁻¹ * b)⁻¹ * (τ⁻¹ * c) := by group
    rw [SetLike.mem_coe] at ha hb hc ⊢
    rw [this]
    exact mul_mem (mul_mem ha (inv_mem hb)) hc
  · rintro ⟨⟨τ, hτ⟩, hcl⟩
    exact ⟨cosetSubgroup C τ hτ hcl, τ, eq_smul_cosetSubgroup C τ hτ hcl⟩

/-- A subcoset containing `τ` is the right coset `Hτ` (Lean: `τ • H`) of a subgroup
`H`. -/
theorem IsSubcoset.exists_subgroup {C : Set Gr} (hC : IsSubcoset C) {τ : Gr} (hτ : τ ∈ C) :
    ∃ H : Subgroup Gr, C = τ • (H : Set Gr) := by
  rw [isSubcoset_iff] at hC
  obtain ⟨-, hcl⟩ := hC
  exact ⟨cosetSubgroup C τ hτ hcl, eq_smul_cosetSubgroup C τ hτ hcl⟩

/-- The notion of Definition 12.0.3 does not depend on the side: a set is a right coset of
a subgroup precisely when it is a left coset of a (in general different) subgroup.  This
makes the translation between the paper's conventions and Lean's harmless here. -/
theorem isSubcoset_iff_left {C : Set Gr} :
    IsSubcoset C ↔ ∃ (H : Subgroup Gr) (τ : Gr), C = (H : Set Gr) * {τ} := by
  rw [isSubcoset_iff]
  constructor
  · rintro ⟨⟨τ, hτ⟩, hcl⟩
    refine ⟨{ carrier := {h | h * τ ∈ C}
              one_mem' := by simpa using hτ
              mul_mem' := ?_
              inv_mem' := ?_ }, τ, ?_⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      have : a * b * τ = (a * τ) * τ⁻¹ * (b * τ) := by group
      rw [this]; exact hcl _ ha _ hτ _ hb
    · intro a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      have : a⁻¹ * τ = τ * (a * τ)⁻¹ * τ := by group
      rw [this]; exact hcl _ hτ _ ha _ hτ
    · ext g
      rw [mem_mul_singleton, SetLike.mem_coe]
      show g ∈ C ↔ g * τ⁻¹ * τ ∈ C
      rw [inv_mul_cancel_right]
  · rintro ⟨H, τ, rfl⟩
    refine ⟨⟨τ, mem_mul_singleton.2 (by simpa using one_mem H)⟩, ?_⟩
    intro a ha b hb c hc
    rw [mem_mul_singleton] at ha hb hc ⊢
    have : a * b⁻¹ * c * τ⁻¹ = (a * τ⁻¹) * (b * τ⁻¹)⁻¹ * (c * τ⁻¹) := by group
    rw [SetLike.mem_coe] at ha hb hc ⊢
    rw [this]
    exact mul_mem (mul_mem ha (inv_mem hb)) hc

theorem IsSubcoset.subgroup (H : Subgroup Gr) : IsSubcoset (H : Set Gr) :=
  ⟨H, 1, by simp⟩

theorem IsSubcoset.smul (H : Subgroup Gr) (τ : Gr) : IsSubcoset (τ • (H : Set Gr)) :=
  ⟨H, τ, rfl⟩

/-- Definition 12.0.3, the parenthetical remark:

> Note that any intersection of subcosets of `G` is either empty or a subcoset. -/
theorem IsSubcoset.sInter {𝒞 : Set (Set Gr)} (h𝒞 : ∀ C ∈ 𝒞, IsSubcoset C)
    (hne : (⋂₀ 𝒞).Nonempty) : IsSubcoset (⋂₀ 𝒞) := by
  rw [isSubcoset_iff]
  refine ⟨hne, ?_⟩
  intro a ha b hb c hc C hC
  exact ((isSubcoset_iff.1 (h𝒞 C hC)).2) a (ha C hC) b (hb C hC) c (hc C hC)

/-- Definition 12.0.3:

> so every subset of `G` generates a subcoset of `G`.

The subcoset generated by `S`: the smallest subcoset containing `S`, i.e. the intersection
of all subcosets containing `S`. -/
def subcosetClosure (S : Set Gr) : Set Gr := ⋂₀ {C | IsSubcoset C ∧ S ⊆ C}

theorem subset_subcosetClosure (S : Set Gr) : S ⊆ subcosetClosure S := by
  intro s hs C hC
  exact hC.2 hs

theorem subcosetClosure_subset {S C : Set Gr} (hC : IsSubcoset C) (hSC : S ⊆ C) :
    subcosetClosure S ⊆ C := fun _ h => h C ⟨hC, hSC⟩

theorem isSubcoset_subcosetClosure {S : Set Gr} (hS : S.Nonempty) :
    IsSubcoset (subcosetClosure S) :=
  IsSubcoset.sInter (fun _ hC => hC.1) (hS.mono (subset_subcosetClosure S))

/-- §12, **Definition 12.0.3**.

> Let `H ≤ G` be groups and `τ ∈ G`.  We say that the subset `S ⊆ Hτ` is a set of *coset
> generators* of `Hτ` if `Hτ` is the smallest subcoset of `G` containing `S`.

Stated for an arbitrary subcoset `C` in place of `Hτ`. -/
def IsCosetGenerators (S C : Set Gr) : Prop :=
  IsSubcoset C ∧ S ⊆ C ∧ ∀ D : Set Gr, IsSubcoset D → S ⊆ D → C ⊆ D

theorem isCosetGenerators_iff {S C : Set Gr} (hS : S.Nonempty) :
    IsCosetGenerators S C ↔ IsSubcoset C ∧ S ⊆ C ∧ subcosetClosure S = C := by
  constructor
  · rintro ⟨hC, hSC, hmin⟩
    refine ⟨hC, hSC, Set.Subset.antisymm (subcosetClosure_subset hC hSC) ?_⟩
    exact hmin _ (isSubcoset_subcosetClosure hS) (subset_subcosetClosure S)
  · rintro ⟨hC, hSC, hcl⟩
    exact ⟨hC, hSC, fun D hD hSD => hcl ▸ subcosetClosure_subset hD hSD⟩

/-- §12, **Observation 12.0.4**.

> Let `S` be a set of generators of the group `G`.  Then `S ∪ {1}` is a set of coset
> generators of `G`, i. e., no proper subcoset of `G` contains `S ∪ {1}`.

Stated inside an arbitrary ambient group: the smallest subcoset containing `S ∪ {1}` is
the subgroup generated by `S`.  The paper's form is the special case where the ambient
group is `G = ⟨S⟩` itself (`Babai.Observation_12_0_4_paper`). -/
theorem Observation_12_0_4 (S : Set Gr) :
    subcosetClosure (insert 1 S) = (Subgroup.closure S : Set Gr) := by
  refine Set.Subset.antisymm
    (subcosetClosure_subset (IsSubcoset.subgroup _) ?_) ?_
  · rintro g (rfl | hg)
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  · -- any subcoset containing `S ∪ {1}` contains `⟨S⟩`
    intro g hg C hC
    obtain ⟨hCsub, hSC⟩ := hC
    have h1 : (1 : Gr) ∈ C := hSC (Set.mem_insert _ _)
    obtain ⟨H, hCH⟩ := hCsub.exists_subgroup h1
    have hCH' : C = (H : Set Gr) := by rw [hCH]; simp
    rw [hCH'] at hSC ⊢
    exact (Subgroup.closure_le H).2 (fun s hs => hSC (Set.mem_insert_of_mem _ hs)) hg

/-- §12, **Observation 12.0.4**, in the paper's words: if `S` generates the whole ambient
group, then no proper subcoset contains `S ∪ {1}`. -/
theorem Observation_12_0_4_paper {S : Set Gr} (hS : Subgroup.closure S = ⊤)
    {C : Set Gr} (hC : IsSubcoset C) (hSC : insert 1 S ⊆ C) : C = Set.univ := by
  have h := subcosetClosure_subset hC hSC
  rw [Observation_12_0_4, hS] at h
  refine Set.eq_univ_of_univ_subset ?_
  simpa using h

end Subcoset

/-! ### The data attached to `ϕ : G → H` -/

section Phi

variable {Ω : Type*} {G : Subgroup (Equiv.Perm Ω)} {H : Type*} [Group H]

/-- The set of *liftings* `ϕ⁻¹(σ̄) ⊆ S(Ω)` of `σ̄ ∈ H` (Proposition 12.0.1).

The paper takes `H ≤ S(Γ)`; as Remark 12.0.2 observes, only the group structure of `H` is
used, so `H` is an arbitrary group here. -/
def preimageSet (ϕ : G →* H) (σ : H) : Set (Equiv.Perm Ω) :=
  {τ | ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ = σ}

theorem preimageSet_subset (ϕ : G →* H) (σ : H) :
    preimageSet ϕ σ ⊆ (G : Set (Equiv.Perm Ω)) := fun _ h => h.1

/-- `N = ker(ϕ)`, as a subgroup of `S(Ω)` rather than of `G`. -/
def kerSubgroup (ϕ : G →* H) : Subgroup (Equiv.Perm Ω) := ϕ.ker.map G.subtype

theorem mem_kerSubgroup {ϕ : G →* H} {τ : Equiv.Perm Ω} :
    τ ∈ kerSubgroup ϕ ↔ ∃ h : τ ∈ G, ϕ ⟨τ, h⟩ = 1 := by
  constructor
  · rintro ⟨⟨g, hg⟩, hker, rfl⟩
    exact ⟨hg, hker⟩
  · rintro ⟨h, hker⟩
    exact ⟨⟨τ, h⟩, hker, rfl⟩

theorem kerSubgroup_le (ϕ : G →* H) : kerSubgroup ϕ ≤ G := Subgroup.map_subtype_le _

/-- `ϕ⁻¹(1) = N`: the preimage of the identity is the kernel. -/
theorem preimageSet_one (ϕ : G →* H) :
    preimageSet ϕ 1 = (kerSubgroup ϕ : Set (Equiv.Perm Ω)) := by
  ext τ
  rw [SetLike.mem_coe, mem_kerSubgroup]
  rfl

end Phi

end Babai
