/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10.4 (Subgroups of small index in S_n).
-/
import Workspace.AltQuotients.DM52.Main52B
import Workspace.AltQuotients.DM52.SetStab

/-!
# §10.4 Subgroups of small index in `S_n`

Observation 10.4.1 and its proof, the Jordan–Liebeck theorem (Theorem 10.4.2, proved here
from the two cited theorems `Babai.dixonMortimer_5_2A` and `Babai.dixonMortimer_5_2B` of
`[DiM, §5.2]` (proved in `Workspace/AltQuotients/DM52/`), with their exceptional cases — which the paper drops, making its printed
statement false — and with uniqueness proved from Observation 10.4.1 exactly as the paper
says), Notation 10.4.3 with Eq. (51), and Remark 10.4.4.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ### Observation 10.4.1 -/

/-- **Observation 10.4.1**, §10.4.

> Let `T, U ⊂ Ω`, `|T|, |U| < n/2`, where `n = |Ω| ≥ 5`.  Assume `A(Ω)_(T) ≤ S(Ω)_U`.
> Then `U ⊆ T`.

Proof (the paper's): `|Ω \ T| ≥ 3`, so `Ω \ T` is an orbit of `A(Ω)_(T)`, hence lies in an
orbit of `S(Ω)_U`; since `|Ω \ T| > n/2 > |U|` we get `Ω \ T ⊆ Ω \ U`. -/
theorem observation_10_4_1 {T U : Set Ω} (hT : 2 * T.ncard < Nat.card Ω)
    (hU : 2 * U.ncard < Nat.card Ω) (hn : 5 ≤ Nat.card Ω)
    (h : pointwiseStabilizer (alternatingGroup Ω) T ≤ setwiseStabilizer ⊤ U) :
    U ⊆ T := by
  classical
  -- "By assumption, `|Ω \ T| ≥ 3`"
  have hTc : 3 ≤ (Tᶜ : Set Ω).ncard := by
    have := ncard_add_ncard_compl T
    omega
  -- `Ω \ T ⊄ U`, because `|Ω \ T| > n/2 > |U|`
  have hcard : U.ncard < (Tᶜ : Set Ω).ncard := by
    have := ncard_add_ncard_compl T
    omega
  have hnotsub : ¬ (Tᶜ : Set Ω) ⊆ U := by
    intro hsub
    exact absurd (Set.ncard_le_ncard hsub (Set.toFinite _)) (by omega)
  obtain ⟨y, hyT, hyU⟩ := Set.not_subset.1 hnotsub
  -- Now suppose some `u ∈ U` lies outside `T`.
  intro u hu
  by_contra huT
  obtain ⟨σ, hσ, hσu⟩ :=
    exists_mem_alt_pointwiseStabilizer_apply_eq hTc huT (by simpa using hyT)
  have hσU : (σ : Equiv.Perm Ω) '' U = U := (h hσ).2
  have : y ∈ U := by
    rw [← hσU, ← hσu]
    exact ⟨u, hu, rfl⟩
  exact hyU this

/-! ### Theorem 10.4.2 as printed is false

See the the corrected paper "Theorem 10.4.2: the cited Jordan–Liebeck theorem is
mis-transcribed" and the docstrings of `Babai.dixonMortimer_5_2A` and
`Babai.dixonMortimer_5_2B`.  The
two ingredients of the counterexample are checked here. -/

/-- The arithmetic of the counterexamples to Theorem 10.4.2 as printed.

* `n = 10`, `K = S(Ω)`, `H = S_5 ≀ S_2` the stabilizer of a partition of `Ω` into two
  `5`-sets, `r = 4`: the number of such partitions is `(1/2)C(10,5) = 126`, so
  `|K : H| = 126 < 210 = C(10,4)`, and all the hypotheses of Theorem 10.4.2 hold.
* `n = 9`, `K = A(Ω)`, `H = PΓL(2,8)` of order `1512`, `r = 4`:
  `|K : H| = (9!/2)/1512 = 120 < 126 = C(9,4)`. -/
theorem jordanLiebeck_counterexample_arith :
    2 * 126 = Nat.choose 10 5 ∧ 126 < Nat.choose 10 4 ∧
      362880 / 2 / 1512 = 120 ∧ 120 < Nat.choose 9 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- A transitive group has no sandwich set other than `∅`: if `H` is transitive on `Ω` and
`H ≤ S(Ω)_T` for some `T ≠ Ω`, then `T = ∅`.

This is the structural half of the counterexamples to Theorem 10.4.2 as printed: the
partition stabilizer `S_{n/2} ≀ S_2 ≤ S_n` and `PΓL(2,8) ≤ A_9` are transitive and do not
contain `A(Ω)`, so by this lemma and Remark 10.4.4 no `T` as in Eq. (51) exists for
them. -/
theorem eq_empty_of_isTransitive_of_setwiseStabilizer_le {H : Subgroup (Equiv.Perm Ω)}
    (hH : IsTransitive H) {T : Set Ω} (hTne : T ≠ Set.univ)
    (hle : H ≤ setwiseStabilizer ⊤ T) : T = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ T := by
    by_contra hcon
    push_neg at hcon
    exact hTne (Set.eq_univ_of_forall hcon)
  haveI := hH.isPretransitive
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq H x y
  have himg : (σ : Equiv.Perm Ω) '' T = T := (hle σ.2).2
  have : y ∈ T := by
    rw [← himg]
    exact ⟨x, hx, hσ⟩
  exact hy this

/-! ### Theorem 10.4.2 (Jordan–Liebeck) -/

/-- Uniqueness in Theorem 10.4.2, §10.4: "Uniqueness follows from Observation 10.4.1."

If `T` and `T'` both satisfy Eq. (51) then `A(Ω)_(T) ≤ H ≤ S(Ω)_{T'}`, so `T' ⊆ T` by
Observation 10.4.1, and symmetrically `T ⊆ T'`. -/
theorem sandwichSet_unique (hn : 5 ≤ Nat.card Ω) {H : Subgroup (Equiv.Perm Ω)} {T T' : Set Ω}
    (h : IsSandwichSet H T) (h' : IsSandwichSet H T') : T = T' := by
  obtain ⟨hTcard, hTle, hTge⟩ := h
  obtain ⟨hT'card, hT'le, hT'ge⟩ := h'
  exact Set.Subset.antisymm
    (observation_10_4_1 hT'card hTcard hn (le_trans hT'le hTge))
    (observation_10_4_1 hTcard hT'card hn (le_trans hTle hT'ge))

/-- `A(Ω) ≤ K ≤ S(Ω)` leaves only two possibilities, since `|S(Ω) : A(Ω)| = 2`. -/
theorem eq_alternating_or_top {K : Subgroup (Equiv.Perm Ω)} (hK : alternatingGroup Ω ≤ K)
    (hn : 2 ≤ Nat.card Ω) : K = alternatingGroup Ω ∨ K = ⊤ := by
  haveI : Nontrivial Ω := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    simpa [Nat.card_eq_fintype_card] using hn
  have h2 : (alternatingGroup Ω).index = 2 := alternatingGroup.index_eq_two
  have hmul : (alternatingGroup Ω).relIndex K * K.index = 2 := by
    rw [Subgroup.relIndex_mul_index hK, h2]
  rcases Nat.lt_or_ge K.index 2 with hlt | hge
  · -- `|S : K| < 2`, so `|S : K| = 1` (it is nonzero) and `K = ⊤`
    have hne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : K.index = 1 := by omega
    exact Or.inr (Subgroup.index_eq_one.1 this)
  · -- `|S : K| ≥ 2`, so `|A : K ∩ A| = 1` and `K ≤ A`
    have h1 : (alternatingGroup Ω).relIndex K = 1 := by
      rcases Nat.eq_zero_or_pos ((alternatingGroup Ω).relIndex K) with h0 | hpos
      · rw [h0] at hmul; omega
      · nlinarith [hmul, hge, hpos]
    exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hK)

/-- The setwise stabilizer in `A(Ω)` is contained in the setwise stabilizer in `S(Ω)`. -/
theorem setwiseStabilizer_alternating_le_top (Δ : Set Ω) :
    setwiseStabilizer (alternatingGroup Ω) Δ ≤ setwiseStabilizer ⊤ Δ := by
  rintro σ ⟨-, hσ⟩
  exact ⟨trivial, hσ⟩

/-- **Theorem 10.4.2** (Jordan–Liebeck), §10.4, with the exceptional cases of the cited
source restored — the printed statement is false, see the corrected paper
"Theorem 10.4.2 (Jordan–Liebeck): the cited theorem is mis-transcribed".

> Let `A(Ω) ≤ K ≤ S(Ω)`.  Let `H ≤ K` and `1 ≤ r < n/2` where `n = |Ω| ≥ 9`.  Assume
> `|K : H| < (n choose r)`.  Then there exists a unique `T ⊂ Ω` with `|T| < n/2` such that
> `A(Ω)_(T) ≤ H ≤ S(Ω)_T`.  This unique `T` satisfies `|T| < r`.

Proved from the two cited theorems of the source, `Babai.dixonMortimer_5_2A` and
`Babai.dixonMortimer_5_2B` (`CITED.md`, C12): `A(Ω) ≤ K ≤ S(Ω)` forces `K = A(Ω)` or
`K = S(Ω)` (`Babai.eq_alternating_or_top`), and the two theorems cover the two cases.
All exceptional cases of the source have degree `n ≤ 9`, so for `n ≥ 9` only the case
`(9, 4, 120, PΓL₂(8))` of Theorem 5.2A survives, which needs `K = A(Ω)`.  Uniqueness of
`T` is proved from Observation 10.4.1, as the paper says.

For the paper's printed conclusion see `Babai.theorem_10_4_2_of_not_exceptional` and
`Babai.theorem_10_4_2_of_four_mul_le`. -/
theorem theorem_10_4_2 {K H : Subgroup (Equiv.Perm Ω)} (hK : alternatingGroup Ω ≤ K)
    (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r < Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r) :
    (∃ T : Set Ω, IsSandwichSet H T ∧ T.ncard < r ∧
        ∀ T' : Set Ω, IsSandwichSet H T' → T' = T) ∨
      (IsTransitive H ∧ PreservesHalvingPartition H ∧
        2 * H.relIndex K = (Nat.card Ω).choose (Nat.card Ω / 2)) ∨
      (Nat.card Ω = 9 ∧ r = 4 ∧ K = alternatingGroup Ω ∧ IsPrimitive H ∧
        H.relIndex K = 120 ∧ Nonempty (H ≃* PGammaL_2_8)) := by
  have hsandwich : ∀ Δ : Set Ω, Δ.ncard < r →
      pointwiseStabilizer (alternatingGroup Ω) Δ ≤ H → H ≤ setwiseStabilizer ⊤ Δ →
      (∃ T : Set Ω, IsSandwichSet H T ∧ T.ncard < r ∧
        ∀ T' : Set Ω, IsSandwichSet H T' → T' = T) := by
    intro Δ hΔ hlo hhi
    have hT : IsSandwichSet H Δ := ⟨by omega, hlo, hhi⟩
    exact ⟨Δ, hT, hΔ, fun T' hT' => sandwichSet_unique (by omega) hT' hT⟩
  rcases eq_alternating_or_top hK (by omega) with rfl | rfl
  · -- `K = A(Ω)`: Theorem 5.2A
    rcases dixonMortimer_5_2A (by omega) hr1 (by omega) hHK hindex with
      ⟨Δ, hΔ, hlo, hhi⟩ | hii | hiii
    · exact Or.inl (hsandwich Δ hΔ hlo
        (le_trans hhi (setwiseStabilizer_alternating_le_top Δ)))
    · exact Or.inr (Or.inl hii)
    · rcases hiii with ⟨-, -, h6, -⟩ | ⟨hprim, hcase⟩
      · omega
      · rcases hcase with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h9, hr4, hidx, hiso⟩
        · omega
        · omega
        · omega
        · omega
        · exact Or.inr (Or.inr ⟨h9, by omega, rfl, hprim, hidx, hiso⟩)
  · -- `K = S(Ω)`: Theorem 5.2B
    rw [Subgroup.relIndex_top_right] at hindex ⊢
    rcases dixonMortimer_5_2B (by omega) hr1 (by omega) hindex with
      ⟨Δ, hΔ, hlo, hhi⟩ | hii | hiii
    · exact Or.inl (hsandwich Δ hΔ hlo hhi)
    · exact Or.inr (Or.inl hii)
    · exfalso
      rcases hiii with ⟨-, -, h6, -⟩ | ⟨-, hcase⟩
      · omega
      · rcases hcase with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ <;> omega

/-- **Theorem 10.4.2** (Jordan–Liebeck), §10.4, as the paper prints it, under the extra
assumption that the two exceptional cases of the cited source are impossible.

This is the form in which the paper uses the theorem.  See
`Babai.theorem_10_4_2_of_four_mul_le` for a convenient sufficient condition covering every
use in §10.5. -/
theorem theorem_10_4_2_of_not_exceptional {K H : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r)
    (hr2 : 2 * r < Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r)
    (hii : ¬ (IsTransitive H ∧ PreservesHalvingPartition H ∧
      2 * H.relIndex K = (Nat.card Ω).choose (Nat.card Ω / 2)))
    (hiii : ¬ (Nat.card Ω = 9 ∧ r = 4 ∧ K = alternatingGroup Ω ∧ IsPrimitive H ∧
      H.relIndex K = 120 ∧ Nonempty (H ≃* PGammaL_2_8))) :
    ∃ T : Set Ω, IsSandwichSet H T ∧ T.ncard < r ∧
      ∀ T' : Set Ω, IsSandwichSet H T' → T' = T := by
  rcases theorem_10_4_2 hK hHK hr1 hr2 hn hindex with h | h | h
  · exact h
  · exact absurd h hii
  · exact absurd h hiii

/-! ### Excluding the exceptional alternatives -/

/-- `2·C(n,j) ≤ C(n,j+1)` as soon as `3j + 2 ≤ n`, from
`C(n,j+1)·(j+1) = C(n,j)·(n−j)`. -/
theorem two_mul_choose_le_choose_succ {n j : ℕ} (h : 3 * j + 2 ≤ n) :
    2 * n.choose j ≤ n.choose (j + 1) := by
  have key : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) := Nat.choose_succ_right_eq n j
  have h2 : 2 * (j + 1) ≤ n - j := by omega
  have hmul : 2 * n.choose j * (j + 1) ≤ n.choose (j + 1) * (j + 1) := by
    rw [key]
    calc 2 * n.choose j * (j + 1) = n.choose j * (2 * (j + 1)) := by ring
      _ ≤ n.choose j * (n - j) := Nat.mul_le_mul_left _ h2
  exact Nat.le_of_mul_le_mul_right hmul (by omega)

/-- The arithmetic behind the exclusion of alternative (ii) of the repaired Theorem
10.4.2: for `n ≥ 9` and `1 ≤ r ≤ n/4` we have `2·C(n,r) ≤ C(n, ⌊n/2⌋)`, i.e.
`C(n,r) ≤ (1/2)C(n,⌊n/2⌋)`.

This covers every use of Theorem 10.4.2 in §10.5, where `n = k` and `r = ⌊k/4⌋`. -/
theorem two_mul_choose_le_choose_half {n r : ℕ} (hn : 9 ≤ n) (hr1 : 1 ≤ r)
    (hr4 : 4 * r ≤ n) : 2 * n.choose r ≤ n.choose (n / 2) :=
  le_trans (two_mul_choose_le_choose_succ (by omega)) (Nat.choose_le_middle _ _)

/-- **Theorem 10.4.2** (Jordan–Liebeck), §10.4, as the paper prints it, under a convenient
sufficient condition that covers every use of the theorem in §10.5: `4r ≤ n` and
`(n, r) ≠ (9, 4)`.

`4r ≤ n` excludes the exceptional case (ii) of the cited source: that case gives
`2|K : H| = (n choose ⌊n/2⌋) ≥ 2(n choose r) > 2|K : H|`
(`Babai.two_mul_choose_le_choose_half`), a contradiction; and it also excludes the
exceptional case (iii), whose `(n, r) = (9, 4)` violates `4r ≤ n`.  In Theorem 10.5.1 the
theorem is applied with `n = k ≥ 9` and `r = ⌊k/4⌋`, so `4r ≤ k`. -/
theorem theorem_10_4_2_of_four_mul_le {K H : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r)
    (hr4 : 4 * r ≤ Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r) :
    ∃ T : Set Ω, IsSandwichSet H T ∧ T.ncard < r ∧
      ∀ T' : Set Ω, IsSandwichSet H T' → T' = T := by
  refine theorem_10_4_2_of_not_exceptional hK hHK hr1 (by omega) hn hindex ?_
    (fun h => by obtain ⟨h9, h4, -⟩ := h; omega)
  rintro ⟨-, -, heq⟩
  have h2 := two_mul_choose_le_choose_half hn hr1 hr4
  omega

/-! ### Notation 10.4.3 -/

/-- **Notation 10.4.3**, Eq. (51), §10.4:

> Under the assumptions of Theorem 10.4.2, we denote by `T(H)` the unique set `T` of
> Theorem 10.4.2.

Since the printed statement of Theorem 10.4.2 is false, the
notation needs the exclusion of the two exceptional alternatives of the repaired theorem,
so that Babai's conclusion holds.  Under exactly these hypotheses `T(H)` is the unique set
of that theorem, so `A(Ω)_(T(H)) ≤ H ≤ S(Ω)_{T(H)}` and `|T(H)| < r`.  The convenient
sufficient condition `4r ≤ n` is `Babai.sandwichSet_spec`. -/
theorem sandwichSet_spec_of_not_exceptional {K H : Subgroup (Equiv.Perm Ω)}
    (hK : alternatingGroup Ω ≤ K) (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r)
    (hr2 : 2 * r < Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r)
    (hii : ¬ (IsTransitive H ∧ PreservesHalvingPartition H ∧
      2 * H.relIndex K = (Nat.card Ω).choose (Nat.card Ω / 2)))
    (hiii : ¬ (Nat.card Ω = 9 ∧ r = 4 ∧ K = alternatingGroup Ω ∧ IsPrimitive H ∧
      H.relIndex K = 120 ∧ Nonempty (H ≃* PGammaL_2_8))) :
    IsSandwichSet H (sandwichSet H) ∧ (sandwichSet H).ncard < r := by
  obtain ⟨T, hT, hTr, huniq⟩ :=
    theorem_10_4_2_of_not_exceptional hK hHK hr1 hr2 hn hindex hii hiii
  have hex : ∃ T, IsSandwichSet H T := ⟨T, hT⟩
  have hspec := isSandwichSet_sandwichSet hex
  refine ⟨hspec, ?_⟩
  rw [huniq _ hspec]
  exact hTr

/-- **Notation 10.4.3**, Eq. (51), §10.4, under the sufficient condition `4r ≤ n` for the
exclusion of the exceptional alternatives of Theorem 10.4.2
(`Babai.theorem_10_4_2_of_four_mul_le`); this covers every use in §10.5.  The general
form is `Babai.sandwichSet_spec_of_not_exceptional`. -/
theorem sandwichSet_spec {K H : Subgroup (Equiv.Perm Ω)} (hK : alternatingGroup Ω ≤ K)
    (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r < Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r)
    (hr4 : 4 * r ≤ Nat.card Ω) :
    IsSandwichSet H (sandwichSet H) ∧ (sandwichSet H).ncard < r := by
  obtain ⟨T, hT, hTr, huniq⟩ :=
    theorem_10_4_2_of_four_mul_le hK hHK hr1 hr4 hn hindex
  have hex : ∃ T, IsSandwichSet H T := ⟨T, hT⟩
  have hspec := isSandwichSet_sandwichSet hex
  refine ⟨hspec, ?_⟩
  rw [huniq _ hspec]
  exact hTr

/-- `A(Ω)_(∅) = A(Ω)`: the pointwise stabilizer of the empty set is everything. -/
@[simp] theorem pointwiseStabilizer_empty (G : Subgroup (Equiv.Perm Ω)) :
    pointwiseStabilizer G (∅ : Set Ω) = G := by
  ext σ
  simp

/-- `S(Ω)_∅ = S(Ω)`. -/
@[simp] theorem setwiseStabilizer_empty (G : Subgroup (Equiv.Perm Ω)) :
    setwiseStabilizer G (∅ : Set Ω) = G := by
  ext σ
  simp

/-- **Remark 10.4.4**, §10.4, in its general form: "`T(H) = ∅` if and only if
`A(Ω) ≤ H ≤ S(Ω)`", whenever `H` has a sandwich set at all and `n ≥ 5` (this is where
the uniqueness of Observation 10.4.1 holds).  `H ≤ S(Ω)` is automatic.  Under the
assumptions of Notation 10.4.3 a sandwich set exists
(`Babai.sandwichSet_spec_of_not_exceptional`), so this covers the remark there. -/
theorem sandwichSet_eq_empty_iff_of_exists {H : Subgroup (Equiv.Perm Ω)}
    (hn : 5 ≤ Nat.card Ω) (hex : ∃ T, IsSandwichSet H T) :
    sandwichSet H = ∅ ↔ alternatingGroup Ω ≤ H := by
  have hspec := isSandwichSet_sandwichSet hex
  constructor
  · intro h
    have := hspec.2.1
    rwa [h, pointwiseStabilizer_empty] at this
  · intro h
    have hempty : IsSandwichSet H (∅ : Set Ω) := by
      refine ⟨by simp only [Set.ncard_empty]; omega, ?_, ?_⟩
      · simpa using h
      · simp
    exact sandwichSet_unique hn hspec hempty

/-- **Remark 10.4.4**, §10.4: "`T(H) = ∅` if and only if `A(Ω) ≤ H ≤ S(Ω)`."

(Under the assumptions of Theorem 10.4.2 and the sufficient condition `4r ≤ n` of
`Babai.sandwichSet_spec`; `H ≤ S(Ω)` is automatic.  The general form is
`Babai.sandwichSet_eq_empty_iff_of_exists`.) -/
theorem sandwichSet_eq_empty_iff {K H : Subgroup (Equiv.Perm Ω)} (hK : alternatingGroup Ω ≤ K)
    (hHK : H ≤ K) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r < Nat.card Ω) (hn : 9 ≤ Nat.card Ω)
    (hindex : H.relIndex K < (Nat.card Ω).choose r)
    (hr4 : 4 * r ≤ Nat.card Ω) :
    sandwichSet H = ∅ ↔ alternatingGroup Ω ≤ H :=
  sandwichSet_eq_empty_iff_of_exists (by omega)
    ⟨_, (sandwichSet_spec hK hHK hr1 hr2 hn hindex hr4).1⟩

end Babai
