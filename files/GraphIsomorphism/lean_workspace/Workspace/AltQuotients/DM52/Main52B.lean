/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The proof of [DiM, Thm. 5.2B], cited by Theorem 10.4.2 (§10.4).
-/
import Workspace.AltQuotients.DM52.Main52A
import Workspace.AltQuotients.DM52.Sym52B

/-!
# [DiM, Thm. 5.2B]

[DiM, p. 150]: "If `G` is a subgroup of `S_n` for some `n` and `|S_n : G| < C(n,r)` for some
`r ≤ n/2` then `|A_n : G ∩ A_n| < C(n,r)` and Theorem 5.2A applies to `G ∩ A_n`.  However
some new exceptional cases arise.  We leave the proof as an exercise."

This file carries out the exercise.  With `G₀ := G ∩ A`, `|S : G| = 2|A : G₀|` when `G ≤ A`
and `|S : G| = |A : G₀|` otherwise (`index_cases`).  Theorem 5.2A for `G₀` gives:

* (i) for `G₀`: (i) for `G` (`image_eq_of_sandwich`);
* (ii) for `G₀`: `G ≤ A` is excluded by the index, and otherwise (ii) for `G`
  (`preservesHalvingPartition_of_normalizes`);
* (iii)(a) for `G₀`: `G ≤ A` is excluded by the index; otherwise `|S : G| = 15` is odd, so `G`
  contains a transposition and is not primitive, and its blocks have size `2`
  (`blocks_of_six`);
* (iii)(b) for `G₀`, degree `5` or `6` with `|A : G₀| = 6`: `G = G₀ ≅ PSL₂(5)` (index `12`),
  or `G ⊄ A` and `G ≅ 5:4`, `PGL₂(5)` (`degree_five_sym`, `degree_six_sym`); degree `5` with
  `G ≤ A` is excluded by the index;
* (iii)(b) for `G₀`, degree `7` or `8`: `G = G₀` (index `30`), or `G ⊄ A` has odd index
  `15` and contains a transposition, so it is `S` by Jordan's theorem, a contradiction;
* (iii)(b) for `G₀`, degree `9`: `G ≤ A` is excluded by the index, and otherwise `|G| = 3024`,
  which is impossible (`not_card_3024`).
-/

universe u

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

theorem relabel_inf {α β : Type*} (f : α ≃ β) (H K : Subgroup (Perm α)) :
    relabel f (H ⊓ K) = relabel f H ⊓ relabel f K :=
  Subgroup.map_inf_eq H K _ f.permCongrHom.injective

/-- The relabeled `G` and `G ∩ A`: if `σ (e (G ∩ A) e⁻¹) σ⁻¹ = M`, then
`σ (e G e⁻¹) σ⁻¹ ∩ A = M`. -/
theorem relabel_inf_alternatingGroup {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (σ : Perm β) (G : Subgroup (Perm α))
    {M : Subgroup (Perm β)} (h : relabel σ (relabel e (G ⊓ alternatingGroup α)) = M) :
    relabel σ (relabel e G) ⊓ alternatingGroup β = M := by
  rw [← h, relabel_inf, relabel_inf, relabel_alternatingGroup, relabel_alternatingGroup]

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

/-- **[DiM, Thm. 5.2B]**, derived from Theorem 5.2A as [DiM] indicate (p. 150). -/
theorem statement52B (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Equiv.Perm Ω)} (hindex : G.index < (Nat.card Ω).choose r) :
    (∃ Δ : Set Ω, Δ.ncard < r ∧
        pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G ∧
        G ≤ setwiseStabilizer ⊤ Δ) ∨
      (IsTransitive G ∧ PreservesHalvingPartition G ∧
        2 * G.index = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
      ((IsTransitive G ∧
          (∃ ℬ : Set (Set Ω), IsSystemOfImprimitivity G Set.univ ℬ ∧
            ∀ B ∈ ℬ, B.ncard = 2) ∧
          Nat.card Ω = 6 ∧ 3 ≤ r ∧ G.index = 15) ∨
        (IsPrimitive G ∧
          ((Nat.card Ω = 5 ∧ 2 ≤ r ∧ G.index = 6 ∧ Nonempty (G ≃* AGL_1_5)) ∨
            (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.index = 6 ∧
              Nonempty (G ≃* PGL (Fin 2) (ZMod 5))) ∨
            (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.index = 12 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) ∨
            (Nat.card Ω = 7 ∧ 3 ≤ r ∧ G.index = 30 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
            (Nat.card Ω = 8 ∧ 3 ≤ r ∧ G.index = 30 ∧
              Nonempty (G ≃* AGL_3_2))))) := by
  classical
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  have hG0A : G ⊓ alternatingGroup Ω ≤ alternatingGroup Ω := inf_le_right
  have hG0G : G ⊓ alternatingGroup Ω ≤ G := inf_le_left
  have hcases := index_cases G
  have h0le : (G ⊓ alternatingGroup Ω).relIndex (alternatingGroup Ω) ≤ G.index := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hnorm : ∀ g ∈ G, ∀ τ ∈ G ⊓ alternatingGroup Ω,
      g * τ * g⁻¹ ∈ G ⊓ alternatingGroup Ω := by
    intro g hg τ hτ
    have h2 := mem_alternatingGroup.mp hτ.2
    refine ⟨G.mul_mem (G.mul_mem hg hτ.1) (G.inv_mem hg), mem_alternatingGroup.mpr ?_⟩
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, h2]
    simp
  have hC : (Nat.card Ω).choose r ≤ (Nat.card Ω).choose (Nat.card Ω / 2) :=
    choose_le_choose_of_le_half (by omega) le_rfl
  have hcardF : Fintype.card Ω = Nat.card Ω := Nat.card_eq_fintype_card.symm
  have hcardG : Nat.card G * G.index = (Nat.card Ω)! := by
    rw [G.card_mul_index, Nat.card_perm]
  rcases Babai.dixonMortimer_5_2A hn hr1 hr2 hG0A (h0le.trans_lt hindex) with
    ⟨Δ, hΔr, hlow, hup⟩ | ⟨hT0, hH0, h2⟩ | ⟨⟨hT0, -, h6, hr3, h15⟩ | ⟨hP0, hcase⟩⟩
  · -- case (i)
    exact Or.inl ⟨Δ, hΔr, hlow.trans hG0G, fun σ hσ =>
      ⟨Subgroup.mem_top σ, image_eq_of_sandwich hn (by omega) hlow hup hnorm hσ⟩⟩
  · -- case (ii)
    rcases hcases with ⟨-, hidx⟩ | ⟨-, hidx⟩
    · exfalso; omega
    · exact Or.inr (Or.inl ⟨isTransitive_of_le hG0G hT0,
        preservesHalvingPartition_of_normalizes hn hG0A hH0 h2 hnorm, by rw [hidx]; exact h2⟩)
  · -- case (iii)(a)
    rcases hcases with ⟨-, hidx⟩ | ⟨-, hidx⟩
    · exfalso
      rw [h6, show (6 : ℕ).choose (6 / 2) = 20 by decide] at hC
      rw [h6] at hindex
      omega
    · have hT := isTransitive_of_le hG0G hT0
      have hidx15 : G.index = 15 := by omega
      have hnp : ¬ IsPreprimitive G Ω := fun hP => by
        have := eq_top_of_odd_of_isPreprimitive (by rw [hidx15]; decide) hP
        rw [this, Subgroup.index_top] at hidx15; omega
      exact Or.inr (Or.inr (Or.inl ⟨hT, blocks_of_six h6 hT hnp hidx15, h6, hr3, hidx15⟩))
  · -- case (iii)(b)
    have hP0' : IsPreprimitive ↥(G ⊓ alternatingGroup Ω) Ω :=
      (isPrimitive_iff_isPreprimitive _).mp hP0
    have hP : IsPreprimitive G Ω := isPreprimitive_of_le hG0G hP0'
    have hPrim : IsPrimitive G := (isPrimitive_iff_isPreprimitive G).mpr hP
    have hnotA : ∀ {k : ℕ} (e : Ω ≃ Fin k),
        (G ⊓ alternatingGroup Ω).relIndex (alternatingGroup Ω) ≠ 1 →
        ¬ alternatingGroup (Fin k) ≤ relabel e (G ⊓ alternatingGroup Ω) := fun e h1 h' =>
      h1 (Subgroup.relIndex_eq_one.mpr (alternatingGroup_le_of_relabel e h'))
    refine Or.inr (Or.inr (Or.inr ⟨hPrim, ?_⟩))
    rcases hcase with ⟨h5, hr, hi, -⟩ | ⟨h6, hr, hi, hiso⟩ | ⟨h7, hr, hi, hiso⟩ |
        ⟨h8, hr, hi, hiso⟩ | ⟨h9, hr, hi, -⟩
    · -- degree 5
      rcases hcases with ⟨-, hidx⟩ | ⟨-, hidx⟩
      · exfalso
        rw [h5, show (5 : ℕ).choose (5 / 2) = 10 by decide] at hC
        rw [h5] at hindex
        omega
      · refine Or.inl ⟨h5, hr, by omega, ?_⟩
        let e := Fintype.equivFinOfCardEq (hcardF.trans h5)
        obtain ⟨σ, hσ⟩ := degree_five (relabel_le_alternatingGroup e hG0A)
          ((isPreprimitive_relabel_iff e _).mpr hP0') (hnotA e (by omega))
          (by rw [relabel_relIndex_alternatingGroup, hi]; decide)
        have hinf := relabel_inf_alternatingGroup e σ G hσ
        have hcard : Nat.card (relabel σ (relabel e G)) = 20 := by
          rw [card_relabel, card_relabel]
          rw [h5, show (5 : ℕ)! = 120 by decide, hidx, hi] at hcardG
          omega
        obtain ⟨iso⟩ := degree_five_sym hinf hcard
        exact ⟨((relabelEquiv e G).trans (relabelEquiv σ _)).trans iso⟩
    · -- degree 6
      rcases hcases with ⟨hGA, hidx⟩ | ⟨-, hidx⟩
      · obtain ⟨iso⟩ := hiso
        refine Or.inr (Or.inr (Or.inl ⟨h6, hr, by omega, ⟨?_⟩⟩))
        exact (MulEquiv.subgroupCongr (inf_of_le_left hGA).symm).trans iso
      · refine Or.inr (Or.inl ⟨h6, hr, by omega, ?_⟩)
        let e := Fintype.equivFinOfCardEq (hcardF.trans h6)
        obtain ⟨σ, hσ⟩ := degree_six (relabel_le_alternatingGroup e hG0A)
          ((isPreprimitive_relabel_iff e _).mpr hP0') (hnotA e (by omega))
          (by rw [relabel_relIndex_alternatingGroup, hi]; decide)
        have hinf := relabel_inf_alternatingGroup e σ G hσ
        have hcard : Nat.card (relabel σ (relabel e G)) = 120 := by
          rw [card_relabel, card_relabel]
          rw [h6, show (6 : ℕ)! = 720 by decide, hidx, hi] at hcardG
          omega
        obtain ⟨iso⟩ := degree_six_sym hinf hcard
        exact ⟨((relabelEquiv e G).trans (relabelEquiv σ _)).trans iso⟩
    · -- degree 7
      rcases hcases with ⟨hGA, hidx⟩ | ⟨-, hidx⟩
      · obtain ⟨iso⟩ := hiso
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h7, ?_, by omega, ⟨?_⟩⟩)))
        · by_contra hr3
          rw [h7] at hindex hr2
          rw [hidx, hi] at hindex
          interval_cases r
          revert hindex; decide
        · exact (MulEquiv.subgroupCongr (inf_of_le_left hGA).symm).trans iso
      · exfalso
        have h15 : G.index = 15 := by omega
        have := eq_top_of_odd_of_isPreprimitive (by rw [h15]; decide) hP
        rw [this, Subgroup.index_top] at h15; omega
    · -- degree 8
      rcases hcases with ⟨hGA, hidx⟩ | ⟨-, hidx⟩
      · obtain ⟨iso⟩ := hiso
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h8, ?_, by omega, ⟨?_⟩⟩)))
        · by_contra hr3
          rw [h8] at hindex hr2
          rw [hidx, hi] at hindex
          interval_cases r
          revert hindex; decide
        · exact (MulEquiv.subgroupCongr (inf_of_le_left hGA).symm).trans iso
      · exfalso
        have h15 : G.index = 15 := by omega
        have := eq_top_of_odd_of_isPreprimitive (by rw [h15]; decide) hP
        rw [this, Subgroup.index_top] at h15; omega
    · -- degree 9
      exfalso
      rcases hcases with ⟨-, hidx⟩ | ⟨-, hidx⟩
      · rw [h9, show (9 : ℕ).choose (9 / 2) = 126 by decide] at hC
        rw [h9] at hindex
        omega
      · let e := Fintype.equivFinOfCardEq (hcardF.trans h9)
        have hcard : Nat.card (relabel e G) = 3024 := by
          rw [card_relabel]
          rw [h9, show (9 : ℕ)! = 362880 by decide, hidx, hi] at hcardG
          omega
        exact not_card_3024 ((isPreprimitive_relabel_iff e G).mpr hP) hcard

end Babai.DM52

namespace Babai

/-- **[DiM, Thm. 5.2B]** (Dixon–Mortimer, *Permutation Groups*, GTM 163, Springer 1996,
pp. 150–151), cited by Babai's Theorem 10.4.2, §10.4.  It was an axiom
(`Workspace/Cited/AltQuotients.lean`, `CITED.md` C12); it is now proved from
Theorem 5.2A along the route the source indicates (`Babai.DM52.statement52B`), with the same
statement.

Quoted from the source:

> **Theorem 5.2B.** Let `S := Sym(Ω)` and `A := Alt(Ω)` where `n := |Ω| ≥ 5`, and let `r`
> be an integer with `1 ≤ r ≤ n/2`.  Suppose that `G ≤ S` has index `|S : G| < (n choose
> r)`.  Then one of the following holds:
> (i) for some `Δ ⊆ Ω` with `|Δ| < r` we have `A_(Δ) ≤ G ≤ S_{Δ}`;
> (ii) `n = 2m` is even, `G` is imprimitive with two blocks of size `m`, and
> `|S : G| = (1/2)(n choose m)`; or
> (iii) one of six exceptional cases hold where:
> (a) `G` is imprimitive with blocks of size 2 on `Ω` and `(n, r, |S : G|) = (6,3,15)`;
> (b) `G` is primitive on `Ω` and `(n, r, |S : G|, G) = (5,2,6,5:4)`, `(6,2,6,PGL₂(5))`,
> `(6,2,12,PSL₂(5))`, `(7,3,30,PSL₃(2))`, or `(8,3,30,AGL₃(2))`.
>
> **Remark.** In part (iii) of the theorem, the groups are listed only with the minimum `r`
> for which they satisfy the hypotheses of the theorem.

So clause (iii) reads "`r` is at least the listed `r`" (see the note on [DiM, Thm. 5.2A,B]
in `Workspace/Cited/AltQuotients.lean`, which also explains the notation). -/
theorem dixonMortimer_5_2B {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Equiv.Perm Ω)} (hindex : G.index < (Nat.card Ω).choose r) :
    (∃ Δ : Set Ω, Δ.ncard < r ∧
        pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G ∧
        G ≤ setwiseStabilizer ⊤ Δ) ∨
      (IsTransitive G ∧ PreservesHalvingPartition G ∧
        2 * G.index = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
      ((IsTransitive G ∧
          (∃ ℬ : Set (Set Ω), IsSystemOfImprimitivity G Set.univ ℬ ∧
            ∀ B ∈ ℬ, B.ncard = 2) ∧
          Nat.card Ω = 6 ∧ 3 ≤ r ∧ G.index = 15) ∨
        (IsPrimitive G ∧
          ((Nat.card Ω = 5 ∧ 2 ≤ r ∧ G.index = 6 ∧ Nonempty (G ≃* AGL_1_5)) ∨
            (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.index = 6 ∧
              Nonempty (G ≃* PGL (Fin 2) (ZMod 5))) ∨
            (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.index = 12 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) ∨
            (Nat.card Ω = 7 ∧ 3 ≤ r ∧ G.index = 30 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
            (Nat.card Ω = 8 ∧ 3 ≤ r ∧ G.index = 30 ∧
              Nonempty (G ≃* AGL_3_2))))) :=
  DM52.statement52B hn hr1 hr2 hindex

end Babai
