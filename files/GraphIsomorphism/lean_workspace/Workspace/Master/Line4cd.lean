/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 4c and 4d: the Extended Design Lemma and Procedure Align.
-/
import Workspace.Master.AlignDominantBuild
import Workspace.Master.AlignDominantRound
import Workspace.Master.Lines
import Workspace.Master.Round

/-!
# Lines 4c and 4d of the Master Algorithm

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :)
>     (: view these hypergraphs as `t`-ary relational structures :)
>     apply Extended Design Lemma (Theorem 9.2.3)
> 4d. (: canonical structure `X` on `Γ` found: colored equipartition or Johnson scheme :)
>     apply Procedure Align to `X` (Sec. 14.1)

This file puts together the pieces that the other files of `Workspace/Master/` have built:

* Theorem 9.2.3 as a canonical family of versions of the structure
  (`Babai.exists_canonicalVersions_of_uniform`, `Workspace/Master/DesignVersions.lean`);
* the coloring of `Γ` that a version carries, and the dichotomy *"every color class is
  small, or there is a dominant one"* (`Babai.alignColor_cases`,
  `Workspace/Master/AlignOutcome.lean`);
* the color classes of `Ω`, with the dominant window first
  (`Babai.omegaColorClassesDomFirst`);
* Procedure Align lines 7–11 on the dominant window
  (`Babai.AlignDominantRoundData.round`, `Workspace/Master/AlignDominantRound.lean`),
  built from the version by `Workspace/Master/AlignDominantBuild.lean`;
* the branching over the versions and the Chain Rule over the color classes
  (`Babai.designAlignReduction`, `Babai.designAlignDominantReduction`,
  `Workspace/Master/Lines.lean`).

## Two hypotheses, and why they are hypotheses

`Babai.theorem_9_2_3` fixes the ground set before it produces its constants `q` and `c`, so
the constants it returns may change with the ground set, while the cost of one round has to
be one function of the window size.  The construction therefore takes

* `q`, `c`, `RAM.QuasiPolyBound q` and `Babai.Theorem923Uniform q c`, the uniform form of
  Theorem 9.2.3 (see the entry *"the absolute constants are chosen after the ground set"* in
  the corrected paper), and
* the action of `S(Γ)` on the outcomes, which is `Babai.exists_isCatAction_splitOutcomes`
  and is chosen inside the construction.

**Neither is an axiom.**  The first is discharged once `Babai.theorem_9_2_3` is restated
with the binder of the ground set inside the existential — the repair that the corrected paper
describes and that is scheduled for `Workspace/SplitOrJohnson/`.

## The cost

`Babai.line4cdCost q c n` is the number of instances lines 4c–4d produce: at most
`q(m)·m^{c·t}` versions, times at most `n` color classes, times the cost of the round of the
dominant window.  It is bounded in terms of `n` alone by `m ≤ n` (the Johnson parameter is
no larger than the window) and `t ≤ log₂ n` (the window is the set of `t`-subsets of `Γ`,
and `C(m,t) ≥ 2^t` because `4t < m`).
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### The cost of one round of lines 4c–4d -/

/-- §15, lines 4c–4d, §14.2 Eq. (71): the number of instances one round of lines 4c–4d
produces.

The three factors are the three sources of branching: the versions of the canonical
structure (`q(m)·m^{c·t}`, bounded here by `qMax q(n)·n^{c·log₂ n}`), the color classes of
`Ω` that the Chain Rule runs over — at most `n`, and one more because line 6 puts the
dominant window in front of the list whether or not it already occurs in it — and the round
of the dominant window (`Babai.AlignDominantRoundData.alignDominantRoundCost`). -/
def line4cdCost (q : ℕ → ℕ) (c : ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup q * n ^ (c * Nat.log 2 n) * (n + 1) *
    AlignDominantRoundData.alignDominantRoundCost n

/-- `q` made monotone: the largest value of `q` up to `n`.

The multiplicative cost of Theorem 9.2.3 at line 4c is `q(m)m^{O(t)}` with `m ≤ n`, and
`Babai.Theorem923Uniform` says nothing about the shape of `q`, so `q(m) ≤ q(n)` is not
available.  `Babai.qMax` is the smallest monotone function above `q`, and it is
quasipolynomial whenever `q` is (`Babai.quasiPolyBound_qMax`). -/
def qMax (q : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup q

theorem le_qMax (q : ℕ → ℕ) {k n : ℕ} (h : k ≤ n) : q k ≤ qMax q n :=
  Finset.le_sup (f := q) (Finset.mem_range.2 (by omega))

/-- `Babai.qMax` is quasipolynomial whenever `q` is: every value of `q` below `n` is bounded
by the bound at `n`, because `log₂` is monotone. -/
theorem quasiPolyBound_qMax {q : ℕ → ℕ} (hq : RAM.QuasiPolyBound q) :
    RAM.QuasiPolyBound (qMax q) := by
  obtain ⟨d, hd⟩ := hq
  refine ⟨d, fun n => ?_⟩
  refine Finset.sup_le fun k hk => ?_
  refine le_trans (hd k) (Nat.pow_le_pow_right (by norm_num) ?_)
  exact Nat.pow_le_pow_left (by
    have : Nat.log 2 k ≤ Nat.log 2 n :=
      Nat.log_mono_right (by have := Finset.mem_range.1 hk; omega)
    omega) d

/-- `n + 1` is quasipolynomial. -/
theorem quasiPolyBound_succ : RAM.QuasiPolyBound (fun n : ℕ => n + 1) := by
  refine ⟨1, fun n => ?_⟩
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have h2 : 2 ^ (Nat.log 2 n + 1) + 1 ≤ 2 ^ (Nat.log 2 n + 2) := by
    have : 2 ^ (Nat.log 2 n + 2) = 2 ^ (Nat.log 2 n + 1) + 2 ^ (Nat.log 2 n + 1) := by
      rw [pow_succ]; ring
    have hpos : 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.one_le_two_pow
    omega
  calc n + 1 ≤ 2 ^ (Nat.log 2 n + 1) + 1 := by omega
    _ ≤ 2 ^ (Nat.log 2 n + 2) := h2
    _ ≤ 2 ^ ((Nat.log 2 n + 2) ^ 1) := by rw [pow_one]

/-- The identity function is quasipolynomially bounded. -/
theorem quasiPolyBound_id : RAM.QuasiPolyBound (fun n : ℕ => n) := by
  refine ⟨1, fun n => ?_⟩
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  calc n ≤ 2 ^ (Nat.log 2 n + 1) := le_of_lt h
    _ ≤ 2 ^ ((Nat.log 2 n + 2) ^ 1) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        rw [pow_one]; omega

/-- `k! ≤ 2^{k²}`: the factorial is below `k^k`, and `k ≤ 2^k`. -/
theorem factorial_le_two_pow_sq (k : ℕ) : Nat.factorial k ≤ 2 ^ (k * k) := by
  calc Nat.factorial k ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (le_of_lt (Nat.lt_two_pow_self)) k
    _ = 2 ^ (k * k) := by rw [← pow_mul]

/-- §15, line 2: the multiplicative cost `ℓ(n)!` of the imprimitive Luks reduction is
quasipolynomial, because `ℓ(n) = (log₂ n)³`. -/
theorem quasiPolyBound_factorial_ellOf :
    RAM.QuasiPolyBound (fun n => Nat.factorial (ellOf n)) := by
  refine ⟨6, fun n => ?_⟩
  refine le_trans (factorial_le_two_pow_sq (ellOf n)) ?_
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h : ellOf n * ellOf n = (Nat.log 2 n) ^ 6 := by
    rw [ellOf]; ring
  rw [h]
  exact Nat.pow_le_pow_left (by omega) 6

/-- §14.1, lines 7–11: the cost of the round of the dominant window is quasipolynomial. -/
theorem quasiPolyBound_alignDominantRoundCost :
    RAM.QuasiPolyBound AlignDominantRoundData.alignDominantRoundCost := by
  have h : RAM.QuasiPolyBound
      (fun n => Nat.factorial (ellOf n) * n + n) :=
    (quasiPolyBound_factorial_ellOf.mul quasiPolyBound_id).add quasiPolyBound_id
  exact h.mono fun n => le_of_eq rfl

/-- `n^{c·log₂ n}` is quasipolynomial: `n ≤ 2^{log₂ n + 2}`, so the exponent is at most
`c·(log₂ n + 2)² ≤ (log₂ n + 2)^{c+2}`. -/
theorem quasiPolyBound_pow_log (c : ℕ) :
    RAM.QuasiPolyBound (fun n => n ^ (c * Nat.log 2 n)) := by
  refine ⟨c + 2, fun n => ?_⟩
  set M := Nat.log 2 n + 2 with hM
  have hn : n ≤ 2 ^ M := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    exact le_trans (le_of_lt h) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hstep : n ^ (c * Nat.log 2 n) ≤ 2 ^ (M * (c * Nat.log 2 n)) := by
    calc n ^ (c * Nat.log 2 n) ≤ (2 ^ M) ^ (c * Nat.log 2 n) :=
          Nat.pow_le_pow_left hn _
      _ = 2 ^ (M * (c * Nat.log 2 n)) := by rw [← pow_mul]
  refine le_trans hstep (Nat.pow_le_pow_right (by norm_num) ?_)
  have hcM : c ≤ M ^ c :=
    le_trans (le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_left (by omega) c)
  calc M * (c * Nat.log 2 n) ≤ M * (c * M) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
        omega
    _ = c * (M * M) := by ring
    _ ≤ M ^ c * (M * M) := Nat.mul_le_mul_right _ hcM
    _ = M ^ (c + 2) := by ring

/-- §15, lines 4c–4d: **the cost of one round is quasipolynomial**, as Eq. (71) of
Sec. 14.2 says: a quasipolynomial multiplicative cost `q(m)m^{O(t)}` times a polynomial
number of Chain Rule calls times the quasipolynomial cost of the round of the dominant
window. -/
theorem quasiPolyBound_line4cdCost {q : ℕ → ℕ} (hq : RAM.QuasiPolyBound q) (c : ℕ) :
    RAM.QuasiPolyBound (line4cdCost q c) :=
  (((quasiPolyBound_qMax hq).mul (quasiPolyBound_pow_log c)).mul quasiPolyBound_succ).mul
    quasiPolyBound_alignDominantRoundCost

/-! ### Lines 6–11: the round of the dominant window, from the version

`Babai.alignColor_cases` hands over, in the dominant case, a `Babai.DominantStructure`:
the extra structure of line 7 on the dominant color class.
`Workspace/Master/AlignDominantBuild.lean` turns it into the data of lines 7–11, and
`Workspace/Master/AlignDominantRound.lean` into the round.  What is needed here is only the
three things the branch reads off that round: the Johnson parameter `m` of the instance the
round is compared against, the group `G* = ϕ⁻¹(Aut(X'))` the Chain Rule call is made with
respect to, and the window `Ω(Δ_j)`. -/

section DominantData

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {m : ℕ} {G : Subgroup (Equiv.Perm Ω)}

/-- §14.1, **lines 6–11**: the round of the dominant window, built from the version `X'` of
the canonical structure.

The three clauses are what lines 4c–4d use: the Johnson parameter of the ambient instance is
`m` (`Babai.AlignDominantRoundData.decreases_round`), the group of the round is
`G* = ϕ⁻¹(Aut(X'))`, which is the group `G₁` the Chain Rule call of line 5 is made with
respect to, and the window of the
round is `Ω(Δ_j)` for the dominant color class `Δ_j`.

The proof is a case distinction on line 7: case (A) is
`Babai.alignDominantABlocks_ofOutcome`, case (B) is `Babai.alignDominantBBlocks_of`, and
their `_spec` theorems give the last two clauses. -/
theorem exists_alignDominantRoundData
    [MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m)))
    (hG : IsTransitive G) (ϕ : G →* Equiv.Perm (Fin m)) (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (t : ℕ) (ht : ∀ u : Ω, tPoint ϕ u = t)
    {Z : Pt (SplitOutcomes (Fin m))} {α : ℝ}
    (hZ : IsSplitOutcome α (Set.univ : Set (Fin m)) Z)
    {i₀ : AlignColor} (hdom : m < 2 * (colorSet (alignColor Z) i₀).card)
    (hstruct : DominantStructure Z i₀) (hm12 : 12 ≤ m) (hn : 96 ≤ Fintype.card Ω) :
    ∃ D : AlignDominantRoundData Ω,
      D.toAlignDominant.m = m ∧
      D.toAlignDominant.Gs = preimageSubgroup ϕ (structAut Z) ∧
      D.toAlignDominant.window
        = omegaOf ϕ ((colorSet (alignColor Z) i₀ : Finset (Fin m)) : Set (Fin m)) := by
  classical
  obtain ⟨s, o⟩ := Z
  cases o with
  | inl P₀ =>
    rcases hstruct with ⟨P, j, hobj, hi, ⟨x, y, hx, hy, hxy⟩, hblk⟩ |
      ⟨-, ⟨J, hobj⟩, -⟩
    swap
    · exact absurd (hobj : (Sum.inl P₀ : (ColoredPartitions (Fin m) ℕ).Obj s ⊕
        (JohnsonSchemes (Fin m)).Obj s) = Sum.inr J) (by simp)
    -- case (A): a nontrivial equipartition of the dominant class
    have hPP : P₀ = P := by
      have h : (Sum.inl P₀ : (ColoredPartitions (Fin m) ℕ).Obj s ⊕
        (JohnsonSchemes (Fin m)).Obj s) = Sum.inl P := hobj
      exact (Sum.inl.injEq _ _ ▸ h)
    cases hPP
    subst hi
    obtain ⟨hs, -⟩ := hZ
    refine ⟨(alignDominantABlocks_ofOutcome G hG ϕ hgiant hvl t ht hs P₀ hdom hx hy hxy
      hblk).toAlignDominantA.roundData hn, rfl, ?_, ?_⟩
    · exact (alignDominantABlocks_ofOutcome_spec hK G hG ϕ hgiant hvl t ht hs P₀ hdom
        hx hy hxy hblk).2.2.2.2.2
    · show omegaOf _ _ = _
      congr 1
      exact (alignDominantABlocks_ofOutcome_spec hK G hG ϕ hgiant hvl t ht hs P₀ hdom
        hx hy hxy hblk).2.2.2.2.1
  | inr J₀ =>
    rcases hstruct with ⟨P, j, hobj, -, -, -⟩ | ⟨hi, ⟨J, hobj⟩, -⟩
    · exact absurd (hobj : (Sum.inr J₀ : (ColoredPartitions (Fin m) ℕ).Obj s ⊕
        (JohnsonSchemes (Fin m)).Obj s) = Sum.inl P) (by simp)
    -- case (B): a Johnson scheme on the dominant class
    have hJJ : J₀ = J := by
      have h : (Sum.inr J₀ : (ColoredPartitions (Fin m) ℕ).Obj s ⊕
        (JohnsonSchemes (Fin m)).Obj s) = Sum.inr J := hobj
      exact (Sum.inr.injEq _ _ ▸ h)
    cases hJJ
    subst hi
    obtain ⟨k, ts, φ, hts, hk, hφ⟩ := J₀.2
    have hdom' : m < 2 * s.ncard := by
      have hc : ((colorSet (alignColor (⟨s, Sum.inr J₀⟩ : Pt (SplitOutcomes (Fin m))))
          (Sum.inr true) : Finset (Fin m)) : Set (Fin m)) = s :=
        colorSet_alignColor_inr s J₀
      have hcard : (colorSet (alignColor (⟨s, Sum.inr J₀⟩ : Pt (SplitOutcomes (Fin m))))
          (Sum.inr true)).card = s.ncard := by
        rw [← Set.ncard_coe_finset, hc]
      omega
    refine ⟨(alignDominantBBlocks_of hK G hG ϕ hgiant hvl t ht J₀ φ hts hk hφ hdom'
      hm12).toAlignDominantB.roundData hn, rfl, ?_, ?_⟩
    · exact (alignDominantBBlocks_of_spec hK G hG ϕ hgiant hvl t ht J₀ φ hts hk hφ hdom'
        hm12).2.2.2.2.2
    · show omegaOf _ _ = _
      congr 1
      exact (alignDominantBBlocks_of_spec hK G hG ϕ hgiant hvl t ht J₀ φ hts hk hφ hdom'
        hm12).2.2.2.2.1

end DominantData

/-! ### Eq. (72) for one color class at a time

`Babai.three_mul_card_tupleClass_le_of_sq` asks every color class of `Γ` to have at most
`αm` vertices.  Line 6 needs the bound for the classes **other than the dominant one**, and
there the hypothesis is available only for the colors the class in question is concentrated
on.  These are the same proofs with the hypothesis asked only of those colors. -/

section Sharp

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- §7.2 / §14.2, **Eq. (72)**, for one color class: the bound `3|Φ_v| ≤ 2|Φ|` needs
`|Δ_i| ≤ α m` only for the colors `i` on which the vector `v` is concentrated, that is,
those with `v i = t`. -/
theorem three_mul_card_tupleClass_le_of_sq_at [Nonempty ι] (c : Γ → ι) {t : ℕ} (ht2 : 2 ≤ t)
    (ht : 2 * t ≤ Fintype.card Γ) {α : ℝ} (hα0 : 0 ≤ α) (hα2 : 3 * α ^ 2 ≤ 2) (v : ι → ℕ)
    (hα : ∀ i, v i = t → ((colorSet c i).card : ℝ) ≤ α * (Fintype.card Γ)) :
    3 * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
  by_cases hex : ∃ i, v i = t
  · obtain ⟨i, hvi⟩ := hex
    have hm : 0 < Fintype.card Γ := by omega
    have hmR : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hm
    have hα1 : α ≤ 1 := by nlinarith
    have hPhipos : (0 : ℝ) < ((Fintype.card Γ).choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : t ≤ Fintype.card Γ)
    have hsub : ((tupleClass c t v).card : ℝ) ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := by
      have := Finset.card_le_card (tupleClass_subset_powersetCard c hvi)
      rw [Finset.card_powersetCard] at this
      exact_mod_cast this
    have hb := lemma_7_2_1b c i hm (by omega : t ≤ Fintype.card Γ)
    have hratio : ((colorSet c i).card : ℝ) / (Fintype.card Γ) ≤ α := by
      rw [div_le_iff₀ hmR]; exact hα i hvi
    have hratio0 : (0 : ℝ) ≤ ((colorSet c i).card : ℝ) / (Fintype.card Γ) := by positivity
    have hpow : (((colorSet c i).card : ℝ) / (Fintype.card Γ)) ^ t ≤ α ^ t :=
      pow_le_pow_left₀ hratio0 hratio t
    have hαt : α ^ t ≤ α ^ 2 := pow_le_pow_of_le_one hα0 hα1 ht2
    have hkey : ((tupleClass c t v).card : ℝ) ≤ α ^ 2 * ((Fintype.card Γ).choose t : ℝ) := by
      calc ((tupleClass c t v).card : ℝ)
          ≤ (((colorSet c i).card.choose t : ℕ) : ℝ) := hsub
        _ = ((((colorSet c i).card.choose t : ℕ) : ℝ) / ((Fintype.card Γ).choose t))
              * ((Fintype.card Γ).choose t) := by field_simp
        _ ≤ α ^ 2 * ((Fintype.card Γ).choose t) :=
            mul_le_mul_of_nonneg_right (le_trans hb (le_trans hpow hαt)) (le_of_lt hPhipos)
    have hR : (3 : ℝ) * (tupleClass c t v).card ≤ 2 * (Phi Γ t).card := by
      rw [card_Phi]
      nlinarith
    exact_mod_cast hR
  · push Not at hex
    exact lemma_7_2_1a c ht hex

end Sharp

section SharpOmega

variable {W : Type u} [Fintype W] [DecidableEq W] {m : ℕ} {G : Subgroup (Equiv.Perm W)}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- §14.2, **Eq. (72)**, lifted to `Ω`, for one color class at a time.  This is
`Babai.three_mul_card_tupleClass_le_of_sq_at` multiplied by the common size of a standard
block, exactly as `Babai.three_mul_ncard_omegaColorClass_le_of_sq` is
`Babai.three_mul_card_tupleClass_le_of_sq` multiplied by it. -/
theorem three_mul_ncard_omegaColorClass_le_of_sq_at [Nonempty ι] (hG : IsTransitive G)
    (ϕ : G →* Equiv.Perm (Fin m)) (hϕ : IsGiantRep ϕ)
    (hk : VeryLargeK m (maxOrbitLength G)) (hm3 : 3 ≤ m) {t : ℕ}
    (ht : ∀ u : W, tPoint ϕ u = t) (ht2 : 2 ≤ t) (h2t : 2 * t ≤ m) (c : Fin m → ι)
    {α : ℝ} (hα0 : 0 ≤ α) (hα2 : 3 * α ^ 2 ≤ 2) (v : ι → ℕ)
    (hα : ∀ i, v i = t → ((colorSet c i).card : ℝ) ≤ α * (m : ℝ)) :
    3 * (omegaColorClass (Ω := W) ϕ c v).ncard ≤ 2 * Fintype.card W := by
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset (Fin m), T₀.card = t := by
    obtain ⟨T₀, -, hT₀⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin m))) (n := t)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact ⟨T₀, hT₀⟩
  have h72 := three_mul_card_tupleClass_le_of_sq_at (Γ := Fin m) (ι := ι) c ht2
    (by rw [Fintype.card_fin]; exact h2t) hα0 hα2 v
    (by intro i hi; rw [Fintype.card_fin]; exact hα i hi)
  rw [ncard_omegaColorClass_eq_mul ϕ hϕ hk hm3 ht c v T₀ hT₀,
    card_univ_eq_mul hG ϕ hϕ hk hm3 ht T₀ hT₀]
  calc 3 * ((tupleClass c t v).card * (labelFiber (Ω := W) ϕ T₀).card)
      = (3 * (tupleClass c t v).card) * (labelFiber (Ω := W) ϕ T₀).card := by ring
    _ ≤ (2 * (Phi (Fin m) t).card) * (labelFiber (Ω := W) ϕ T₀).card :=
        Nat.mul_le_mul_right _ h72
    _ = 2 * (m.choose t * (labelFiber (Ω := W) ϕ T₀).card) := by
        rw [card_Phi, Fintype.card_fin]; ring

end SharpOmega

/-! ### The calls of the branch

The branch of lines 4c–4d is `Babai.designAlignDominantReduction`: the Chain Rule of
line 5 over the color classes of `Ω`, with the dominant window first, and with the call on
the dominant window expanded by the round of lines 7–11.  Three things have to be known
about the calls of the Chain Rule before the expansion: their windows are color classes,
they are group instances, and the one whose window is the dominant class is made with
respect to `G₁ = ϕ⁻¹(Aut(X'))` — because it is the *first* call of the Chain Rule
(line 6, *"start the application of the Chain Rule with the window `Ω(Δ_j)`"*). -/

section Calls

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {Γ : Type*} {𝒳 : Type*} [MulAction (Equiv.Perm Γ) 𝒳] {G : Subgroup (Equiv.Perm W)}

/-- §14.1, lines 1–3: every call of `Babai.alignBranch` is a call of the continuation at
the **one** group the branch uses, `G₁ = ϕ⁻¹(Aut(X'))`.  This is
`Babai.calls_alignBranch` with the property asked only there. -/
theorem calls_alignBranch_at {ϕ : G →* Equiv.Perm Γ} (y : W → A) (X' Y' : 𝒳)
    (k : Subgroup (Equiv.Perm W) → (W → A) → SIReduction W A (Set (Equiv.Perm W)))
    {P : SIInstance W A → Prop}
    (hk : ∀ z, ∀ J ∈ (k (preimageSubgroup ϕ (structAut X')) z).calls, P J) :
    ∀ J ∈ (alignBranch ϕ y X' Y' k).calls, P J := by
  classical
  by_cases h : ∃ σ : G, (ϕ σ) • X' = Y'
  · rw [alignBranch, dif_pos h, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil]
    exact hk _
  · rw [alignBranch, dif_neg h, SIReduction.calls_done]
    simp

/-- §15, lines 4c–4d: what is known of a call of the Chain Rule of line 5 before the
expansion of line 6. -/
def Line4cdSpec (G₁ : Subgroup (Equiv.Perm W)) (Δs : List (Set W)) (S₀ : Set W)
    (J : SIInstance W A) : Prop :=
  J.Δ ∈ Δs ∧ IsGroupInstance J ∧ J.K ⊆ (G₁ : Set (Equiv.Perm W)) ∧
    (J.Δ = S₀ → J.K = (G₁ : Set (Equiv.Perm W)))

open scoped Classical in
/-- §15, lines 4c–4d: **the calls of the Chain Rule of line 5**.

Their windows are the color classes (`Babai.calls_designAlignReduction_window`), they are
group instances (the classes are invariant under `G₁`, and every call of the Chain Rule is
with respect to a subgroup of `G₁`), and the call on the dominant window is the **first**
call of the Chain Rule, which is made with respect to `G₁` itself — this is what line 6
buys by starting the Chain Rule with that window. -/
theorem calls_designAlignReduction_spec {ϕ : G →* Equiv.Perm Γ} {Vers : (W → A) → Set 𝒳}
    (x y : W → A) (hfin : (Vers y).Finite) (X' : 𝒳) (S₀ : Set W) (rest : List (Set W))
    (hS₀ : S₀ ∉ rest)
    (hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ) :
    ∀ J ∈ (designAlignReduction ϕ Vers x y hfin X' (S₀ :: rest)).calls,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J := by
  classical
  refine calls_versionsReduction y hfin _ (fun Y' => ?_)
  refine calls_alignBranch_at (ϕ := ϕ) y X' Y' _ (fun z J hJ => ?_)
  rw [alignChainReduction] at hJ
  obtain ⟨M', hKJ, hle, hΔ⟩ := calls_chainReduction_group
    (preimageSubgroup ϕ (structAut X')) x z (S₀ :: rest) 1
    (preimageSubgroup ϕ (structAut X')) J hJ
  refine ⟨hΔ, ⟨M', hKJ, fun τ hτ => hinv J.Δ hΔ τ (hle hτ)⟩,
    by rw [hKJ]; exact SetLike.coe_subset_coe.2 hle, fun hS => ?_⟩
  rcases calls_chainReduction_cons (preimageSubgroup ϕ (structAut X')) x z S₀ rest 1
    (preimageSubgroup ϕ (structAut X')) J hJ with heq | hmem
  · rw [heq]
  · exact absurd (hS ▸ hmem) hS₀

/-! ### The branch, with the dominant window expanded -/

open scoped Classical in
/-- §15, **lines 4c and 4d**: the Chain Rule of line 5 over the color classes, the dominant
window `S₀` first (line 6), with the call on `S₀` expanded by `g` — the round of lines
7–11 when there is a dominant color, and nothing when there is none. -/
noncomputable def alignExpandBranch (ϕ : G →* Equiv.Perm Γ) (Vers : (W → A) → Set 𝒳)
    (x y : W → A) (hfin : (Vers y).Finite) (X' : 𝒳) (S₀ : Set W) (rest : List (Set W))
    (g : SIInstance W A → SIReduction W A (Set (Equiv.Perm W))) :
    SIReduction W A (Set (Equiv.Perm W)) :=
  designAlignDominantReduction ϕ Vers x y hfin X' (S₀ :: rest)
    (fun J => if J.Δ = S₀ then g J else .call J .done)

section Facts

variable {ϕ : G →* Equiv.Perm Γ} {Vers : (W → A) → Set 𝒳} {x y : W → A}
  {hfin : (Vers y).Finite} {X' : 𝒳} {S₀ : Set W} {rest : List (Set W)}
  {g : SIInstance W A → SIReduction W A (Set (Equiv.Perm W))}

open scoped Classical in
theorem run_alignExpandBranch (hcan : IsCanonicalVersions ϕ Vers) (hX' : X' ∈ Vers x)
    (hS₀ : S₀ ∉ rest)
    (hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ)
    (hcov : (⋃ Δ ∈ S₀ :: rest, Δ) = (Set.univ : Set W))
    (hg : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ = S₀ → (g J).run = J.answer) :
    (alignExpandBranch ϕ Vers x y hfin X' S₀ rest g).run =
      strIso (G : Set (Equiv.Perm W)) x y := by
  classical
  rw [alignExpandBranch, designAlignDominantReduction,
    SIReduction.run_expand_of_calls (P := Line4cdSpec (preimageSubgroup ϕ (structAut X'))
      (S₀ :: rest) S₀)
      (fun J hJ => by
        by_cases hS : J.Δ = S₀
        · rw [if_pos hS]; exact hg J hJ hS
        · rw [if_neg hS]; rfl) _
      (calls_designAlignReduction_spec x y hfin X' S₀ rest hS₀ hinv),
    run_designAlignReduction hcan x y hX' hfin (S₀ :: rest) hinv hcov]

open scoped Classical in
theorem calls_length_alignExpandBranch (hS₀ : S₀ ∉ rest)
    (hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ)
    (hg : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ = S₀ → (g J).run = J.answer)
    {qv c : ℕ} (hqv : (Vers y).ncard ≤ qv) (hc1 : 1 ≤ c)
    (hgc : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ = S₀ → (g J).calls.length ≤ c) :
    (alignExpandBranch ϕ Vers x y hfin X' S₀ rest g).calls.length
      ≤ qv * (S₀ :: rest).length * c := by
  classical
  refine le_trans (SIReduction.calls_expand_length_le_of_calls
    (P := Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀)
      (fun J hJ => by
        by_cases hS : J.Δ = S₀
        · rw [if_pos hS]; exact hg J hJ hS
        · rw [if_neg hS]; rfl)
      (c := c)
      (fun J hJ => by
        by_cases hS : J.Δ = S₀
        · rw [if_pos hS]; exact hgc J hJ hS
        · rw [if_neg hS, SIReduction.calls_call, SIReduction.calls_done]; simpa using hc1)
      _ (calls_designAlignReduction_spec x y hfin X' S₀ rest hS₀ hinv)) ?_
  exact Nat.mul_le_mul_right c (calls_length_designAlignReduction x y hfin X' _ hqv)

open scoped Classical in
theorem calls_alignExpandBranch (hS₀ : S₀ ∉ rest)
    (hinv : ∀ Δ ∈ S₀ :: rest, IsInvariant (preimageSubgroup ϕ (structAut X')) Δ)
    (hg : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ = S₀ → (g J).run = J.answer)
    {Q : SIInstance W A → Prop}
    (hQg : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ = S₀ → ∀ K ∈ (g J).calls, Q K)
    (hQself : ∀ J : SIInstance W A,
      Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀ J →
      J.Δ ≠ S₀ → Q J) :
    ∀ K ∈ (alignExpandBranch ϕ Vers x y hfin X' S₀ rest g).calls, Q K := by
  classical
  refine SIReduction.mem_calls_expand_of_calls
    (P := Line4cdSpec (preimageSubgroup ϕ (structAut X')) (S₀ :: rest) S₀)
      (fun J hJ => by
        by_cases hS : J.Δ = S₀
        · rw [if_pos hS]; exact hg J hJ hS
        · rw [if_neg hS]; rfl)
      (fun J hJ K hK => by
        by_cases hS : J.Δ = S₀
        · rw [if_pos hS] at hK; exact hQg J hJ hS K hK
        · rw [if_neg hS, SIReduction.calls_call, SIReduction.calls_done] at hK
          rw [List.mem_singleton] at hK
          rw [hK]
          exact hQself J hJ hS) _
      (calls_designAlignReduction_spec x y hfin X' S₀ rest hS₀ hinv)

end Facts

end Calls

/-! ### The round of the dominant window stays inside `G*`

`Babai.liftWindow` carries a reduction on the window back to `Ω`, and it asks that every
call be with respect to a subset of the group induced on the window.  The Chain Rule of
line 5 gives this by `Babai.calls_chainReduction_K`; the round of lines 7–11 needs the same
statement, and it is the same argument in both of its cases. -/

section RoundK

variable {W : Type u} [Fintype W] [DecidableEq W] {A : Type v}

/-- §14.1, lines 7–11: **every call of the round of the dominant window is with respect to a
subset of `G*`**.

In cases 2 and 3 the round is the Chain Rule starting from `G*`; in case 1 it is the Luks
descent to `ker ϕ*` followed by the Chain Rule from `ker ϕ*`, and `ker ϕ* ≤ G*`. -/
theorem AlignDominantRoundData.calls_round_K_le (D : AlignDominantRoundData W)
    (I : SIInstance W A) :
    ∀ J ∈ (D.round (A := A) I).calls,
      J.K ⊆ (D.toAlignDominant.Gs : Set (Equiv.Perm W)) := by
  classical
  rw [AlignDominantRoundData.round]
  by_cases h : D.LargeParam
  · rw [if_pos h]
    exact calls_chainReduction_K _ I.x I.y _ 1 _
  · rw [if_neg h]
    refine SIReduction.mem_calls_expand_of_calls (D.run_chainOverOrbitsOn_descentCall)
      (fun J _ K hK => ?_) _ (D.calls_descent_descentCall I)
    exact le_trans (calls_chainOverOrbitsOn_K D.ker _ J K hK)
      (SetLike.coe_subset_coe.2 D.ker_le)

end RoundK

/-! ### The progress of the round, read numerically

`Babai.AlignDominantRoundData.decreases_round` states the progress as
`Babai.MakesProgress` against a *hinted instance* of the window type whose window size is
`n` and whose Johnson parameter is `m`.  The instance lines 4c–4d compare against is the
one of `Ω`, not of the window, so what is needed here is the same statement with the two
numbers written out.  The proof is the one of `decreases_round`. -/

section RoundNum

variable {W : Type u} [Fintype W] [DecidableEq W] {A : Type v}

/-- §14.1, lines 7–11, **the progress of the round**, with the window size and the Johnson
parameter of the ambient instance written out as numbers.

* In case 1 every call has a window of at most `2n/3` (item 1 of the repair).
* In cases 2 and 3 every call whose window is not dominant has at most `2n/3` points; the
  one call whose window is dominant is the first call of the Chain Rule, and it carries the
  hint, whose Johnson parameter is `m* ≤ m/2` (Eq. (73)). -/
theorem AlignDominantRoundData.decreases_round_num (D : AlignDominantRoundData W)
    (I : SIInstance W A) :
    ∀ J ∈ (D.round (A := A) I).calls,
      3 * J.windowSize ≤ 2 * Fintype.card W ∨
        (J.windowSize ≤ Fintype.card W ∧
          2 * param (⟨J, D.hint I J⟩ : HintedInstance W A) ≤ D.toAlignDominant.m) := by
  classical
  intro J hJ
  by_cases h : D.LargeParam
  · -- cases 2 and 3
    have hmem : J.Δ ∈ orbitListOn D.toAlignDominant.Gs D.toAlignDominant.window :=
      mem_orbitListDomFirst.1 (D.calls_round_window_case23 I h J hJ)
    obtain ⟨v, hv, hJv⟩ := exists_orbit_of_mem_orbitListOn hmem
    by_cases hsmall : 3 * J.Δ.ncard ≤ 2 * Fintype.card W
    · exact Or.inl hsmall
    · have hbig : 2 * Fintype.card W < 3 * (orbit D.toAlignDominant.Gs v).ncard := by
        rw [← hJv]; omega
      obtain ⟨S, hS, hSbig, hlist⟩ :=
        orbitListDomFirst_eq_cons hmem (by rw [hJv] at hsmall ⊢; omega)
      obtain ⟨w, hw, hSw⟩ := exists_orbit_of_mem_orbitListOn hS
      have hSJ : S = J.Δ := by
        rw [hSw, hJv]
        exact D.dominant_orbit_unique hbig (by rw [← hSw]; exact hSbig)
      have hhead : J = (⟨(D.toAlignDominant.Gs : Set (Equiv.Perm W)), S, I.x,
          strAct I.y (1 : Equiv.Perm W)⁻¹⟩ : SIInstance W A) := by
        have hJ' := hJ
        rw [AlignDominantRoundData.round, if_pos h, hlist] at hJ'
        rcases calls_chainReduction_cons _ I.x I.y S _ 1 _ J hJ' with heq | hmem'
        · exact heq
        · exact absurd (hSJ ▸ hmem') (not_mem_erase_orbitListOn _ _ _)
      have hhint : D.HasHint I J := by
        refine ⟨h, D.dominantOrbit h hv hbig, ?_⟩
        show (⟨(D.toAlignDominant.Gs : Set (Equiv.Perm W)),
          orbit D.toAlignDominant.Gs v, I.x, J.y⟩ : SIInstance W A) = J
        rw [← hJv, hhead]
      refine Or.inr ⟨?_, D.two_mul_param_hint_le I J hhint⟩
      exact AlignDominantRoundData.ncard_le_card (Ω := W) J.Δ
  · -- case 1
    have hmem := D.calls_round_window_case1 I h J hJ
    obtain ⟨v, hv, hJv⟩ := exists_orbit_of_mem_orbitListOn hmem
    refine Or.inl ?_
    show 3 * J.Δ.ncard ≤ 2 * Fintype.card W
    rw [hJv, AlignDominantRoundData.ker, orbit_kerSubgroup]
    exact D.orbit_ker_le v hv

end RoundNum

/-! ### The numeric tests line 4c has already passed

`Babai.AlignDominantRoundData.window_large` asks for `96` points in the window, and
`Babai.alignDominantBBlocks_of` asks for `12 ≤ m`.  Neither is an extra hypothesis on
line 4c: both follow from the tests lines 2 and 4 have already run. -/

section Numeric

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, lines 2 and 4c: an instance that reaches line 4c has a Johnson parameter of at
least `217`.

*Proof.*  Line 2 of Procedure Reduce-to-Johnson leaves a window of at least `64` points
(`Babai.JohnsonCaseData.window_large`), so `log₂ n ≥ 6` and `ℓ = (log₂ n)³ ≥ 216`.  Line 2
of Sec. 15 is *not* taken here, which is the test `m > ℓ`, so `m ≥ 217`. -/
theorem le_param_of_line4c {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) : 217 ≤ param i := by
  have hd := johnsonData hJ
  have hn : 64 ≤ i.inst.windowSize := hd.window_large
  have hL : 6 ≤ Nat.log 2 i.inst.windowSize := six_le_natLog hn
  have : 216 ≤ ellOf i.inst.windowSize := by
    rw [ellOf]
    calc (216 : ℕ) = 6 ^ 3 := by norm_num
    _ ≤ (Nat.log 2 i.inst.windowSize) ^ 3 := Nat.pow_le_pow_left hL 3
  omega

/-- §15, lines 2 and 4c: an instance that reaches line 4c has at least `217` points in its
window, because `m ≤ n` (`Babai.JohnsonCaseData.param_le`).  This is what
`Babai.AlignDominantRoundData.window_large` (`96 ≤ n`) needs. -/
theorem le_windowSize_of_line4c {i : HintedInstance Ω A} (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) : 217 ≤ i.inst.windowSize := by
  have h := le_param_of_line4c hJ hell
  have hle : param i ≤ i.inst.windowSize := param_le_windowSize hJ
  omega

end Numeric

end Babai
