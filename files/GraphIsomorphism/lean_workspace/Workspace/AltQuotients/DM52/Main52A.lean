/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The proof of [DiM, Thm. 5.2A], cited by Theorem 10.4.2 (§10.4).
-/
import Workspace.AltQuotients.DM52.Intrans
import Workspace.AltQuotients.DM52.Degree6
import Workspace.AltQuotients.DM52.Degree8
import Workspace.AltQuotients.DM52.Degree9

/-!
# [DiM, Thm. 5.2A]

The proof of Dixon–Mortimer (pp. 147–149) splits into three cases.

* `G` primitive: by [DiM, Thm. 5.2A]'s first paragraph (Bochert's theorem, and for small `n`
  the exercises 5.2.1–5.2.6), either `A ≤ G`, which is case (i) with `Δ = ∅`, or `n ≤ 9` and
  `G` is one of the exceptional groups (iii)(b) (`primitive_case`, from the degree-by-degree
  theorems `degree_five` … `degree_nine` and `alternatingGroup_le_of_primitive_of_ten_le`).
* `G` transitive and imprimitive: case (ii) or (iii)(a) (`imprimitive_case`).
* `G` intransitive: case (i), by induction on `n` (`intransitive_case`).

`Babai.DM52.statement52A` is the induction; `Babai.dixonMortimer_5_2A` is the theorem with
the statement of the former axiom of `Workspace/Cited/AltQuotients.lean`.
-/

universe u

namespace Babai.DM52

open Equiv Equiv.Perm MulAction Nat Subgroup

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The model group `M` of degree `k` transported back: if `σ (e G e⁻¹) σ⁻¹ = M` and
`M ≃* T`, then `G ≃* T`. -/
theorem nonempty_mulEquiv_of_relabel {k : ℕ} {G : Subgroup (Perm Ω)} (e : Ω ≃ Fin k)
    {M : Subgroup (Perm (Fin k))} {T : Type*} [Group T] (iso : M ≃* T) (σ : Perm (Fin k))
    (h : relabel σ (relabel e G) = M) : Nonempty (G ≃* T) :=
  ⟨((relabelEquiv e G).trans (relabelEquiv σ _)).trans ((MulEquiv.subgroupCongr h).trans iso)⟩

omit [Fintype Ω] [DecidableEq Ω] in
theorem card_eq_of_relabel {k : ℕ} {G : Subgroup (Perm Ω)} (e : Ω ≃ Fin k)
    {M : Subgroup (Perm (Fin k))} (σ : Perm (Fin k)) (h : relabel σ (relabel e G) = M) :
    Nat.card G = Nat.card M := by
  rw [← h, card_relabel, card_relabel]

/-- **The primitive case of [DiM, Thm. 5.2A]** (proof, first paragraph, with Exercises
5.2.1–5.2.6 for the small degrees): a primitive `G ≤ A` with `|A : G| < C(n, r)` contains `A`
(case (i) with `Δ = ∅`) or is one of the exceptional groups (iii)(b). -/
theorem primitive_case (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Perm Ω)} (hGA : G ≤ alternatingGroup Ω)
    (hindex : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose r)
    (hP : IsPreprimitive G Ω) : Concl52A Ω r G := by
  classical
  haveI : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  have hPrim : IsPrimitive G := (isPrimitive_iff_isPreprimitive G).mpr hP
  by_cases hA : alternatingGroup Ω ≤ G
  · refine Or.inl ⟨∅, by simp; omega, fun σ hσ => hA hσ.1, fun σ hσ => ⟨hGA hσ, by simp⟩⟩
  have hrm : (Nat.card Ω).choose r ≤ (Nat.card Ω).choose (Nat.card Ω / 2) :=
    choose_le_choose_of_le_half (by omega) le_rfl
  have hidx := hindex.trans_le hrm
  have hcardF : Fintype.card Ω = Nat.card Ω := Nat.card_eq_fintype_card.symm
  have hGh : 2 * (Nat.card G * G.relIndex (alternatingGroup Ω)) = (Nat.card Ω)! := by
    rw [card_mul_relIndex hGA, two_mul_card_alternatingGroup]
  refine Or.inr (Or.inr (Or.inr ⟨hPrim, ?_⟩))
  rcases (show Nat.card Ω = 5 ∨ Nat.card Ω = 6 ∨ Nat.card Ω = 7 ∨ Nat.card Ω = 8 ∨
      Nat.card Ω = 9 ∨ 10 ≤ Nat.card Ω by omega) with h | h | h | h | h | h
  · let e := Fintype.equivFinOfCardEq (hcardF.trans h)
    obtain ⟨σ, hσ⟩ := degree_five (relabel_le_alternatingGroup e hGA)
      ((isPreprimitive_relabel_iff e G).mpr hP)
      (fun h' => hA (alternatingGroup_le_of_relabel e h'))
      (by rw [relabel_relIndex_alternatingGroup]; rw [h] at hidx; exact hidx.trans_le (by decide))
    rw [card_eq_of_relabel e σ hσ, card_D10, h] at hGh
    have h6 : G.relIndex (alternatingGroup Ω) = 6 := by
      norm_num [Nat.factorial] at hGh; omega
    rw [h, h6] at hindex
    rw [h] at hr2
    refine Or.inl ⟨h, ?_, h6, nonempty_mulEquiv_of_relabel e D10_mulEquiv σ hσ⟩
    by_contra hr
    interval_cases r
    revert hindex; decide
  · let e := Fintype.equivFinOfCardEq (hcardF.trans h)
    have hGA' := relabel_le_alternatingGroup e hGA
    have hP' := (isPreprimitive_relabel_iff e G).mpr hP
    have hA' : ¬ alternatingGroup (Fin 6) ≤ relabel e G :=
      fun h' => hA (alternatingGroup_le_of_relabel e h')
    have hidx' : (relabel e G).relIndex (alternatingGroup (Fin 6)) < 20 := by
      rw [relabel_relIndex_alternatingGroup]; rw [h] at hidx; exact hidx.trans_le (by decide)
    obtain ⟨σ, hσ⟩ := degree_six hGA' hP' hA' hidx'
    have hc := (degree_six_order hGA' hP' hA' hidx').1
    rw [card_relabel] at hc
    rw [hc, h] at hGh
    rw [h] at hindex hr2
    have h6 : G.relIndex (alternatingGroup Ω) = 6 := by
      norm_num [Nat.factorial] at hGh; omega
    rw [h6] at hindex
    refine Or.inr (Or.inl ⟨h, ?_, h6, nonempty_mulEquiv_of_relabel e C6_mulEquiv σ hσ⟩)
    by_contra hr
    interval_cases r
    revert hindex; decide
  · let e := Fintype.equivFinOfCardEq (hcardF.trans h)
    have hGA' := relabel_le_alternatingGroup e hGA
    have hP' := (isPreprimitive_relabel_iff e G).mpr hP
    have hA' : ¬ alternatingGroup (Fin 7) ≤ relabel e G :=
      fun h' => hA (alternatingGroup_le_of_relabel e h')
    have hidx' : (relabel e G).relIndex (alternatingGroup (Fin 7)) < 35 := by
      rw [relabel_relIndex_alternatingGroup]; rw [h] at hidx; exact hidx.trans_le (by decide)
    obtain ⟨σ, hσ⟩ := degree_seven hGA' hP' hA' hidx'
    have hc := (degree_seven_order hGA' hP' hA' hidx').1
    rw [card_relabel] at hc
    rw [hc, h] at hGh
    rw [h] at hindex hr2
    have h6 : G.relIndex (alternatingGroup Ω) = 15 := by
      norm_num [Nat.factorial] at hGh; omega
    rw [h6] at hindex
    refine Or.inr (Or.inr (Or.inl ⟨h, ?_, h6, nonempty_mulEquiv_of_relabel e F7_mulEquiv σ hσ⟩))
    by_contra hr
    interval_cases r
    revert hindex; decide
  · let e := Fintype.equivFinOfCardEq (hcardF.trans h)
    have hGA' := relabel_le_alternatingGroup e hGA
    have hP' := (isPreprimitive_relabel_iff e G).mpr hP
    have hA' : ¬ alternatingGroup (Fin 8) ≤ relabel e G :=
      fun h' => hA (alternatingGroup_le_of_relabel e h')
    have hidx' : (relabel e G).relIndex (alternatingGroup (Fin 8)) < 70 := by
      rw [relabel_relIndex_alternatingGroup]; rw [h] at hidx; exact hidx.trans_le (by decide)
    obtain ⟨σ, hσ⟩ := degree_eight hGA' hP' hA' hidx'
    have hc := (degree_eight_order hGA' hP' hA' hidx').1
    rw [card_relabel] at hc
    rw [hc, h] at hGh
    rw [h] at hindex hr2
    have h6 : G.relIndex (alternatingGroup Ω) = 15 := by
      norm_num [Nat.factorial] at hGh; omega
    rw [h6] at hindex
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h, ?_, h6, nonempty_mulEquiv_of_relabel e A8m_mulEquiv σ hσ⟩)))
    by_contra hr
    interval_cases r
    revert hindex; decide
  · let e := Fintype.equivFinOfCardEq (hcardF.trans h)
    have hGA' := relabel_le_alternatingGroup e hGA
    have hP' := (isPreprimitive_relabel_iff e G).mpr hP
    have hA' : ¬ alternatingGroup (Fin 9) ≤ relabel e G :=
      fun h' => hA (alternatingGroup_le_of_relabel e h')
    have hidx' : (relabel e G).relIndex (alternatingGroup (Fin 9)) < 126 := by
      rw [relabel_relIndex_alternatingGroup]; rw [h] at hidx; exact hidx.trans_le (by decide)
    obtain ⟨σ, hσ⟩ := degree_nine hGA' hP' hA' hidx'
    have hc := (degree_nine_order hGA' hP' hA' hidx').1
    rw [card_relabel] at hc
    rw [hc, h] at hGh
    rw [h] at hindex hr2
    have h6 : G.relIndex (alternatingGroup Ω) = 120 := by
      norm_num [Nat.factorial] at hGh; omega
    rw [h6] at hindex
    refine Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h, ?_, h6, nonempty_mulEquiv_of_relabel e M9_mulEquiv σ hσ⟩)))
    by_contra hr
    interval_cases r
    all_goals (revert hindex; decide)
  · exact absurd (alternatingGroup_le_of_primitive_of_ten_le hGA hP (by omega)
      (by rw [hcardF]; exact hidx)) hA

/-- **[DiM, Thm. 5.2A]**, for every finite type, by strong induction on the degree. -/
theorem statement52A : ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], Statement52A Ω := by
  suffices H : ∀ n : ℕ, ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω], Nat.card Ω = n →
      Statement52A Ω from fun Ω _ _ => H _ Ω rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Ω _ _ hΩ hn r hr1 hr2 G hGA hindex
    by_cases hT : IsPretransitive G Ω
    · by_cases hP : IsPreprimitive G Ω
      · exact primitive_case hn hr1 hr2 hGA hindex hP
      · rcases imprimitive_case hn hr2 hGA hindex hT hP with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (intransitive_case (fun Γ _ _ hΓ => ih _ (hΓ.trans_eq hΩ) Γ rfl)
        hn hr1 hr2 hGA hindex hT)

end Babai.DM52

namespace Babai

/-- **[DiM, Thm. 5.2A]** (Dixon–Mortimer, *Permutation Groups*, GTM 163, Springer 1996,
p. 147), cited by Babai's Theorem 10.4.2, §10.4.  It was an axiom
(`Workspace/Cited/AltQuotients.lean`, `CITED.md` C12); it is now proved along the source
(`Babai.DM52.statement52A`), with the same statement.

Quoted from the source:

> **Theorem 5.2A.** Let `A := Alt(Ω)` where `n := |Ω| ≥ 5`, and let `r` be an integer with
> `1 ≤ r ≤ n/2`.  Suppose that `G ≤ A` has index `|A : G| < (n choose r)`.  Then one of the
> following holds:
> (i) for some `Δ ⊆ Ω` with `|Δ| < r` we have `A_(Δ) ≤ G ≤ A_{Δ}`;
> (ii) `n = 2m` is even, `G` is imprimitive with two blocks of size `m`, and
> `|A : G| = (1/2)(n choose m)`; or
> (iii) one of six exceptional cases hold where:
> (a) `G` is imprimitive on `Ω` and `(n, r, |A : G|) = (6,3,15)`;
> (b) `G` is primitive on `Ω` and `(n, r, |A : G|, G) = (5,2,6,5:2)`, `(6,2,6,PSL₂(5))`,
> `(7,2,15,PSL₃(2))`, `(8,2,15,AGL₃(2))`, or `(9,4,120,PΓL₂(8))`.
>
> **Remark.** […] In part (iii) of the theorem, the groups are listed only with the minimum
> `r` for which they satisfy the hypotheses of the theorem.

So clause (iii) reads "`r` is at least the listed `r`" (see the note on [DiM, Thm. 5.2A,B]
in `Workspace/Cited/AltQuotients.lean`, which also explains the notation). -/
theorem dixonMortimer_5_2A {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
    (hn : 5 ≤ Nat.card Ω) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.card Ω)
    {G : Subgroup (Equiv.Perm Ω)} (hGA : G ≤ alternatingGroup Ω)
    (hindex : G.relIndex (alternatingGroup Ω) < (Nat.card Ω).choose r) :
    (∃ Δ : Set Ω, Δ.ncard < r ∧
        pointwiseStabilizer (alternatingGroup Ω) Δ ≤ G ∧
        G ≤ setwiseStabilizer (alternatingGroup Ω) Δ) ∨
      (IsTransitive G ∧ PreservesHalvingPartition G ∧
        2 * G.relIndex (alternatingGroup Ω) = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
      ((IsTransitive G ∧ ¬ IsPrimitive G ∧
          Nat.card Ω = 6 ∧ 3 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15) ∨
        (IsPrimitive G ∧
          ((Nat.card Ω = 5 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 6 ∧
              Nonempty (G ≃* Frob_5_2)) ∨
            (Nat.card Ω = 6 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 6 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) ∨
            (Nat.card Ω = 7 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15 ∧
              Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) ∨
            (Nat.card Ω = 8 ∧ 2 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 15 ∧
              Nonempty (G ≃* AGL_3_2)) ∨
            (Nat.card Ω = 9 ∧ 4 ≤ r ∧ G.relIndex (alternatingGroup Ω) = 120 ∧
              Nonempty (G ≃* PGammaL_2_8))))) :=
  DM52.statement52A Ω hn hr1 hr2 hGA hindex

end Babai
