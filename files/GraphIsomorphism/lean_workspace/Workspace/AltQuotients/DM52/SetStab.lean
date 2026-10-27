/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Setwise stabilizers in `A(Ω)` and `S(Ω)`: indices (used in §10.4 and in the proof of
[DiM, Thm. 5.2A,B]).
-/
import Workspace.AltQuotients.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
# Indices of setwise stabilizers

`|K : K_B| = C(n, |B|)` for `A(Ω) ≤ K`, and the index bound for groups preserving a
partition into two halves.  These lemmas were stated in `Workspace/AltQuotients/SmallIndex.lean`
(§10.4); they live here so that the proof of `[DiM, Thm. 5.2A,B]`, which `SmallIndex.lean`
uses, can use them too.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- `|T| + |Ω \ T| = |Ω|`. -/
theorem ncard_add_ncard_compl (T : Set Ω) : T.ncard + (Tᶜ : Set Ω).ncard = Nat.card Ω := by
  classical
  have := Set.ncard_add_ncard_compl T
  simpa [Nat.card_eq_fintype_card] using this

/-- If `A(Ω) ≤ K` then `K` is transitive on the `m`-subsets of `Ω`, as soon as
`m + 2 ≤ n`: the alternating group is `(n−2)`-transitive, hence transitive on `m`-sets. -/
theorem isPretransitive_powersetCard {K : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) {m : ℕ} (hm : m + 2 ≤ Nat.card Ω) :
    MulAction.IsPretransitive K (Set.powersetCard Ω m) := by
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω (Nat.card Ω - 2) :=
    alternatingGroup.isMultiplyPretransitive Ω
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω m :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card Ω - 2) (by omega) (by omega)
  haveI hA : MulAction.IsPretransitive (alternatingGroup Ω) (Set.powersetCard Ω m) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive _ inferInstance
  constructor
  intro s t
  obtain ⟨a, ha⟩ := hA.exists_smul_eq s t
  exact ⟨⟨(a : Equiv.Perm Ω), hK a.2⟩, by rw [← ha]; rfl⟩

/-- If `A(Ω) ≤ K` and `m + 2 ≤ n`, then `K` carries any `m`-subset of `Ω` onto any other:
the transitivity of `Babai.isPretransitive_powersetCard` read on plain sets.  This is the
step "noting that `A_k` acts transitively on `[k] choose t_Δ`" in the proof of Theorem
10.5.1 (e). -/
theorem exists_mem_image_eq_of_ncard_eq {K : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) {m : ℕ} {T U : Set Ω} (hT : T.ncard = m) (hU : U.ncard = m)
    (hm : m + 2 ≤ Nat.card Ω) :
    ∃ σ ∈ K, (σ : Equiv.Perm Ω) '' T = U := by
  classical
  haveI := isPretransitive_powersetCard hK hm
  have hTf : T.toFinset.card = m := by rw [← hT, Set.ncard_eq_toFinset_card']
  have hUf : U.toFinset.card = m := by rw [← hU, Set.ncard_eq_toFinset_card']
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq K
    (⟨T.toFinset, by simpa using hTf⟩ : Set.powersetCard Ω m)
    (⟨U.toFinset, by simpa using hUf⟩ : Set.powersetCard Ω m)
  refine ⟨(a : Equiv.Perm Ω), a.2, ?_⟩
  have h : (a : Equiv.Perm Ω) • T.toFinset = U.toFinset := by
    have := congrArg (fun z : Set.powersetCard Ω m => (z : Finset Ω)) ha
    simpa [Set.powersetCard.coe_smul] using this
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hmem : (a : Equiv.Perm Ω) z ∈ (a : Equiv.Perm Ω) • T.toFinset :=
      Finset.smul_mem_smul_finset (Set.mem_toFinset.2 hz)
    rw [h] at hmem
    exact Set.mem_toFinset.1 hmem
  · intro hy
    have hmem : y ∈ (a : Equiv.Perm Ω) • T.toFinset := by
      rw [h]; exact Set.mem_toFinset.2 hy
    rw [Finset.mem_smul_finset] at hmem
    obtain ⟨z, hz, rfl⟩ := hmem
    exact ⟨z, Set.mem_toFinset.1 hz, rfl⟩

/-- The setwise stabilizer `K_B` of Eq. (11), viewed inside `K`, is the stabilizer of `B`
for the action of `K` on the subsets of `Ω`. -/
theorem subgroupOf_setwiseStabilizer {K : Subgroup (Equiv.Perm Ω)} (B : Set Ω) :
    (setwiseStabilizer K B).subgroupOf K = MulAction.stabilizer K B := by
  ext σ
  simp [Subgroup.mem_subgroupOf, mem_setwiseStabilizer, σ.2, MulAction.mem_stabilizer_iff,
    ← Set.image_smul, Subgroup.smul_def, Equiv.Perm.smul_def]

/-- `|K : K_B| = (n choose |B|)` when `A(Ω) ≤ K` and `|B| + 2 ≤ n`: orbit–stabilizer
(Eq. (10)) for the transitive action of `K` on the `|B|`-subsets of `Ω`. -/
theorem relIndex_setwiseStabilizer {K : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) {m : ℕ} (hm : m + 2 ≤ Nat.card Ω) {B : Set Ω}
    (hB : B.ncard = m) :
    (setwiseStabilizer K B).relIndex K = (Nat.card Ω).choose m := by
  classical
  haveI := isPretransitive_powersetCard hK hm
  have hmem : B.toFinset.card = m := by rw [← hB, Set.ncard_eq_toFinset_card']
  set s : Set.powersetCard Ω m := ⟨B.toFinset, by simpa using hmem⟩ with hs
  have hcoe : (s : Set Ω) = B := by
    show ((s : Finset Ω) : Set Ω) = B
    simp [hs]
  have h2 := Set.powersetCard.stabilizer_coe (G := K) s
  have h1 : MulAction.stabilizer K s = (setwiseStabilizer K B).subgroupOf K :=
    h2.trans (by rw [hcoe]; exact (subgroupOf_setwiseStabilizer B).symm)
  have h3 : ((setwiseStabilizer K B).subgroupOf K).index = (MulAction.stabilizer K s).index :=
    congrArg Subgroup.index h1.symm
  rw [Subgroup.relIndex, h3, MulAction.index_stabilizer_of_transitive, Set.powersetCard.card]

/-- If every element of `H` maps `B` to `B` or to its complement, then the elements of `H`
that fix `B` setwise form a subgroup of index at most `2` in `H`: the map
`σ ↦ B^σ ∈ {B, Ω \ B}` is constant on its cosets and separates them. -/
theorem relIndex_inf_le_two {K H : Subgroup (Equiv.Perm Ω)} (hHK : H ≤ K) {B : Set Ω}
    (hpres : ∀ σ ∈ H, (σ : Equiv.Perm Ω) '' B = B ∨ (σ : Equiv.Perm Ω) '' B = Bᶜ) :
    (H ⊓ setwiseStabilizer K B).relIndex H ≤ 2 := by
  classical
  set Q := setwiseStabilizer K B with hQdef
  set L := H ⊓ Q with hLdef
  have hcast : ∀ a b : H, ((a⁻¹ * b : H) : Equiv.Perm Ω)
      = (a : Equiv.Perm Ω)⁻¹ * (b : Equiv.Perm Ω) := by
    intro a b; rfl
  have key : ∀ a b : H, ((a : Equiv.Perm Ω) '' B = (b : Equiv.Perm Ω) '' B) ↔
      a⁻¹ * b ∈ L.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf, hLdef, Subgroup.mem_inf]
    constructor
    · intro hab
      refine ⟨(a⁻¹ * b : H).2, hHK (a⁻¹ * b : H).2, ?_⟩
      rw [hcast, ← image_image_eq_mul_image, ← hab, image_image_eq_mul_image]
      simp
    · rintro ⟨-, -, h1⟩
      rw [hcast, ← image_image_eq_mul_image] at h1
      have := congrArg (fun S => (a : Equiv.Perm Ω) '' S) h1
      simp only [image_image_eq_mul_image] at this
      simpa using this.symm
  set T : Set (Set Ω) := {B, Bᶜ} with hT
  have hFmem : ∀ a : H, ((a : Equiv.Perm Ω) '' B) ∈ T := by
    intro a
    rcases hpres (a : Equiv.Perm Ω) a.2 with h | h <;> simp [hT, h]
  have hinj : Function.Injective (fun x : H ⧸ (L.subgroupOf H) => Quotient.liftOn x
      (fun a : H => (⟨(a : Equiv.Perm Ω) '' B, hFmem a⟩ : T))
      (by intro a b hab
          exact Subtype.ext ((key a b).2 (QuotientGroup.eq.1 (Quotient.sound hab))))) := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        have h : (a : Equiv.Perm Ω) '' B = (b : Equiv.Perm Ω) '' B := by
          simpa [Subtype.ext_iff] using hxy
        exact QuotientGroup.eq.2 ((key a b).1 h)
  have hcard : Nat.card (H ⧸ L.subgroupOf H) ≤ Nat.card T :=
    Nat.card_le_card_of_injective _ hinj
  have hT2 : Nat.card T ≤ 2 := by
    rw [Nat.card_coe_set_eq, hT]
    calc ({B, Bᶜ} : Set (Set Ω)).ncard ≤ ({Bᶜ} : Set (Set Ω)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ 2 := by simp
  calc L.relIndex H = Nat.card (H ⧸ L.subgroupOf H) := rfl
    _ ≤ Nat.card T := hcard
    _ ≤ 2 := hT2

/-- Case (ii) of Theorem 10.4.2 forces a large index, independently of the index value
that the cited source gives there:
if `A(Ω) ≤ K`, `H ≤ K` and `H` preserves a partition of `Ω` into two halves, then
`|K : H| ≥ (1/2)(n choose ⌊n/2⌋)`.

Proof: `H ∩ K_B` has index at most `2` in `H` (`Babai.relIndex_inf_le_two`) and
`|K : K_B| = (n choose n/2)` (`Babai.relIndex_setwiseStabilizer`), and indices multiply in
towers. -/
theorem choose_half_le_two_mul_relIndex {K H : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) (hHK : H ≤ K) (hn : 5 ≤ Nat.card Ω)
    (hh : PreservesHalvingPartition H) :
    (Nat.card Ω).choose (Nat.card Ω / 2) ≤ 2 * H.relIndex K := by
  obtain ⟨B, hB2, hpres⟩ := hh
  have hm2 : B.ncard + 2 ≤ Nat.card Ω := by omega
  have hhalf : B.ncard = Nat.card Ω / 2 := by omega
  set Q := setwiseStabilizer K B with hQdef
  set L := H ⊓ Q with hLdef
  have hQK : Q ≤ K := fun σ hσ => hσ.1
  have hA : Q.relIndex K = (Nat.card Ω).choose (Nat.card Ω / 2) := by
    rw [← hhalf]; exact relIndex_setwiseStabilizer hK hm2 rfl
  have hle2 : L.relIndex H ≤ 2 := relIndex_inf_le_two hHK hpres
  have e1 : L.relIndex Q * Q.relIndex K = L.relIndex K :=
    Subgroup.relIndex_mul_relIndex L Q K inf_le_right hQK
  have e2 : L.relIndex H * H.relIndex K = L.relIndex K :=
    Subgroup.relIndex_mul_relIndex L H K inf_le_left hHK
  have hpos : 0 < L.relIndex Q := Nat.pos_of_ne_zero (by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite)
  calc (Nat.card Ω).choose (Nat.card Ω / 2) = Q.relIndex K := hA.symm
    _ ≤ L.relIndex Q * Q.relIndex K := Nat.le_mul_of_pos_left _ hpos
    _ = L.relIndex H * H.relIndex K := by rw [e1, e2]
    _ ≤ 2 * H.relIndex K := Nat.mul_le_mul_right _ hle2

end Babai
