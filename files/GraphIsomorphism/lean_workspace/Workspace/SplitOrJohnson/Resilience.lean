/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 9.1: Resilience of Johnson schemes.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Workspace.SplitOrJohnson.Defs
import Workspace.AltQuotients.SmallIndex
import Workspace.SplitOrJohnson.ResilienceAux
import Workspace.SplitOrJohnson.ResilienceTransport
import Workspace.ColoredPartitions.Binomial

/-!
# §9.1 Resilience of Johnson schemes

Version 2.5, lines 3928–4000 of `babai-gi-source/quasi25.txt`.

| Paper | Lean |
|---|---|
| Proposition 9.1.1 | `Babai.prop_9_1_1` (`Babai.prop_9_1_1_of_nine_le`, `Babai.prop_9_1_1_small`) |
| Lemma 9.1.2 (Intact Johnson subscheme), repaired | `Babai.lemma_9_1_2` |
| Corollary 9.1.3 | `Babai.cor_9_1_3`, `Babai.cor_9_1_3_strict`, `Babai.cor_9_1_3_strict_small` |
| Remark 9.1.4 | `Babai.remark_9_1_4` |

The passage from Corollary 9.1.3 to Proposition 9.1.1 — the Johnson scheme as an object of
`JohnsonSchemes Ω`, `Aut(J(m,t)) = S_m`, and the Johnson group `A⁽ᵗ⁾(Δ)` acting on the
vertices inside `Δ` — is `Babai.prop_9_1_1_of_cor`
(`Workspace/SplitOrJohnson/ResilienceTransport.lean`).

## The range `m ≤ 8`

Lemma 9.1.2 needs `m ≥ 9`, which Cor. 9.1.3 and Prop. 9.1.1 do not have.  The remaining
range is covered by `Babai.small_index_subgroup_perm`, the subgroups of small index of
`S_m` for `5 ≤ m ≤ 8`, proved from `[DiM, Thm. 5.2B]` (`Babai.dixonMortimer_5_2B`) at
`r = 2`.  Nothing in §9.1 is open.

The opening computation of the proof of Cor. 9.1.3 (*"the condition implies that
`|S_m : G| < 1.9^m`"*) is `Babai.johnson_cost_le_three_halves_rpow`
(`(t/ε)^{εm/t} ≤ (3/2)^m`), and the bound that excludes alternative (ii) of Lemma 9.1.2 is
`Babai.two_mul_three_pow_lt_choose` (`2·3^m < 2^m·C(m,(m-1)/2)` for `m ≥ 9`); the two are
combined in `Babai.two_mul_lt_choose_of_lt_cost`.

## The exponent

The text dump of version 2.5 prints the bound of Prop. 9.1.1 and Cor. 9.1.3 as
`(t/ε)^{m/t}`; the `ε` in the exponent is lost by the dump.  The formula is
`(t/ε)^{εm/t}` (`babai-gi.tex`, line 3371).  Note `(t/ε)^{ε/t} ≤ e^{1/e} < 1.4447`, which
is what the proof of Cor. 9.1.3 uses ("the condition implies `|S_m : G| < 1.9^m`").

## Lemma 9.1.2 is false as printed

See the entry *"Lemma 9.1.2 (Intact Johnson subscheme)"* in the corrected paper.  The lemma
applies Theorem 10.4.2, whose printed form drops the exceptional cases of its source; with
those cases restored, the conclusion of Lemma 9.1.2 has to carry them as well, and the
lemma needs `m ≥ 9` (Theorem 10.4.2 does).  Counterexamples to the printed statement:

* `m = 10`, `G = S₅ ≀ S₂ ≤ S₁₀`, `|S₁₀ : G| = 126 < 210 = C(10,4)`, `r = 3 < m/2 - 1`, but
  `7 ∤ |G| = 28800`, so `G` contains no `A₇`;
* `m = 6`, `G = PGL₂(5) ≤ S₆` (transitive, index `6 < 15 = C(6,2)`), `r = 1 < m/2 - 1`, but
  the point stabilizer of `G` is `F₂₀`, so `G` contains no `A₅` on a 5-subset.

The first falls under the restored alternative (ii) (a transitive group preserving a
partition into two halves, `2|S_m : G| = C(m, m/2)`), the second is excluded by `m ≥ 9`.
-/

namespace Babai

open scoped Classical

/-! ### Lemma 9.1.2 -/

/-- Lemma 9.1.2 (Intact Johnson subscheme), repaired.  *"Let `G ≤ Aut(J(m,t))`.  Assume
`m!/|G| < C(m, r+1)` for some `r < m/2 - 1`.  Then `G ≥ A⁽ᵗ⁾_{m-r}` where `A⁽ᵗ⁾_{m-r}` acts
on a `J(m-r,t)` subscheme of `J(m,t)` corresponding to a subset of size `m-r` of `[m]`."*
(Version 2.5, lines 3940–3951.)

Paper's proof: *"Let us view `G` as a subgroup of `S_m`, so `G⁽ᵗ⁾ ≤ S_m` is the subgroup of
`Aut(J(m,t))` in question.  Then, by the Jordan–Liebeck Theorem (Thm. 10.4.2) we have that
`G ≥ (A_m)_(T)` for some `T ⊂ [m]`, `|T| ≤ r`.  Let `Γ = [m] \ T`.  This means that
`G⁽ᵗ⁾ ≥ A⁽ᵗ⁾(Γ)` where `|Γ| ≥ m - r`."*

Since `Theorem 10.4.2` is false as the paper prints it, the
conclusion here is the true conclusion of `Babai.theorem_10_4_2` for `K = S_m` and
`r + 1` in place of `r`: either the paper's conclusion — a set `T` with `|T| ≤ r` whose
pointwise stabilizer in `A_m` lies in `G` (this is the paper's `G ≥ (A_m)_(T)`, and the
induced action on the `t`-subsets of `Γ = [m] \ T` is the Johnson group `A⁽ᵗ⁾_{m-r}` of the
`J(m-r,t)` subscheme) — or the exceptional alternative (ii) of the cited source.  The
alternative (iii) of Theorem 10.4.2 cannot occur here because it requires
`K = A(Ω)`, while `K = S_m`.  The hypothesis `m ≥ 9` is the one Theorem 10.4.2 carries.

`G` is a subgroup of `S_m = S(Γ)`; the paper's `G⁽ᵗ⁾` is the induced action on the
`t`-subsets, which is the same abstract group, so the statement is about `G ≤ S(Γ)`. -/
theorem lemma_9_1_2 {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Equiv.Perm Γ)}
    {r : ℕ} (hm : 9 ≤ Nat.card Γ) (hr : 2 * (r + 1) < Nat.card Γ)
    (hindex : G.index < (Nat.card Γ).choose (r + 1)) :
    (∃ T : Set Γ, T.ncard ≤ r ∧
        pointwiseStabilizer (alternatingGroup Γ) T ≤ G ∧ G ≤ setwiseStabilizer ⊤ T) ∨
      (IsTransitive G ∧ PreservesHalvingPartition G ∧
        2 * G.index = (Nat.card Γ).choose (Nat.card Γ / 2)) := by
  have hle : G ≤ (⊤ : Subgroup (Equiv.Perm Γ)) := le_top
  have hK : alternatingGroup Γ ≤ (⊤ : Subgroup (Equiv.Perm Γ)) := le_top
  have hindex' : G.relIndex ⊤ < (Nat.card Γ).choose (r + 1) := by
    rwa [Subgroup.relIndex_top_right]
  rcases theorem_10_4_2 hK hle (Nat.succ_le_succ (Nat.zero_le r)) hr hm hindex' with
    h | h | h
  · obtain ⟨T, ⟨-, hlo, hhi⟩, hcard, -⟩ := h
    exact Or.inl ⟨T, by omega, hlo, hhi⟩
  · rw [Subgroup.relIndex_top_right] at h
    exact Or.inr h
  · -- alternative (iii) requires `K = A(Ω)`, but here `K = S(Ω)`
    exfalso
    obtain ⟨h9, -, hKA, -⟩ := h
    have hnt : Nontrivial Γ := by
      have : 0 < Nat.card Γ := by omega
      rw [Nat.card_pos_iff] at this
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      have : Nat.card Γ = Fintype.card Γ := Nat.card_eq_fintype_card
      omega
    have hidx : (alternatingGroup Γ).index = 2 := alternatingGroup.index_eq_two
    rw [← hKA] at hidx
    simp at hidx

/-! ### Corollary 9.1.3 -/

/-- The binomial estimate of the proof of Corollary 9.1.3, repaired:
`C(m-r,t)/C(m,t) ≥ 1 - rt/m`, in cross-multiplied form.

The paper's chain is *"`C(m−r,t)/C(m,t) ≥ (1−r/m)^t > 1−(rt/m)`"*.  Its **first step is
false**: for `m = 10`, `r = 1`, `t = 2` it reads `36/45 = 0.8 ≥ 0.81 = (9/10)²`.  In fact
`C(m−r,t)/C(m,t) = ∏_{i<t} (m−r−i)/(m−i) ≤ ((m−r)/m)^t`, the opposite inequality, since
every factor `(m−r−i)/(m−i)` is at most `(m−r)/m`.  The **conclusion** of the chain is
nevertheless true, with `≥` in place of `>`; the strict form is false too, since for `r = 1`
one has `C(m−1,t)/C(m,t) = 1 − t/m` exactly.  See the corrected paper.

Proof (induction on `r`).  For `r = 0` both sides are `m·C(m,t)`.  For the step, write
`A = m − (r+1)t`, `D = m − r − t`; then `m − rt = A + t`, `m − r = D + t` and `A ≤ D`
because `r ≤ rt`, so `A(D+t) ≤ (A+t)D`, i.e.
`(m − (r+1)t)(m − r) ≤ (m − rt)(m − r − t)`.  Multiplying the induction hypothesis by
`m − r − t` and using `C(m−r−1,t)·(m−r) = C(m−r,t)·(m−r−t)`
(`Nat.choose_mul_succ_eq`) gives the claim after cancelling `m − r > 0`. -/
theorem choose_sub_mul_le {m t : ℕ} :
    ∀ r : ℕ, r * t ≤ m → r + t ≤ m → (m - r * t) * m.choose t ≤ m * (m - r).choose t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · intro r _ _; simp
  intro r
  induction r with
  | zero => intro _ _; simp
  | succ r ih =>
    intro h1 h2
    have hrt : r * t ≤ (r + 1) * t := Nat.mul_le_mul_right t (Nat.le_succ r)
    have hIH := ih (le_trans hrt h1) (by omega)
    have hsucc : (r + 1) * t = r * t + t := by ring
    have hrrt : r ≤ r * t := Nat.le_mul_of_pos_right r ht
    -- `C(m-r-1,t) * (m-r) = C(m-r,t) * (m-r-t)`
    have hid : (m - r - 1).choose t * (m - r) = (m - r).choose t * (m - r - t) := by
      have h := Nat.choose_mul_succ_eq (m - r - 1) t
      have e1 : m - r - 1 + 1 = m - r := by omega
      rwa [e1] at h
    -- `(m - (r+1)t)(m - r) ≤ (m - rt)(m - r - t)`
    have habs : ∀ A D u : ℕ, A ≤ D → A * (D + u) ≤ (A + u) * D := by
      intro A D u h; nlinarith
    have key : (m - (r + 1) * t) * (m - r) ≤ (m - r * t) * (m - r - t) := by
      have hA : m - r * t = (m - (r + 1) * t) + t := by omega
      have hB : m - r = (m - r - t) + t := by omega
      have hAD : m - (r + 1) * t ≤ m - r - t := by omega
      calc (m - (r + 1) * t) * (m - r)
          = (m - (r + 1) * t) * ((m - r - t) + t) := by rw [← hB]
        _ ≤ ((m - (r + 1) * t) + t) * (m - r - t) := habs _ _ _ hAD
        _ = (m - r * t) * (m - r - t) := by rw [← hA]
    have hpos : 0 < m - r := by omega
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (m - (r + 1) * t) * m.choose t * (m - r)
        = ((m - (r + 1) * t) * (m - r)) * m.choose t := by ring
      _ ≤ ((m - r * t) * (m - r - t)) * m.choose t := Nat.mul_le_mul_right _ key
      _ = ((m - r * t) * m.choose t) * (m - r - t) := by ring
      _ ≤ (m * (m - r).choose t) * (m - r - t) := Nat.mul_le_mul_right _ hIH
      _ = m * ((m - r).choose t * (m - r - t)) := by ring
      _ = m * ((m - r - 1).choose t * (m - r)) := by rw [hid]
      _ = m * (m - (r + 1)).choose t * (m - r) := by
          rw [show m - (r + 1) = m - r - 1 from by omega]; ring

/-! ### The bound `(t/ε)^{εm/t} < (3/2)^m`

The proof of Corollary 9.1.3 opens with *"The condition implies that `|S_m : G| < 1.9^m`"*
(version 2.5, line 3958), and the module docstring records where the constant comes from:
`(t/ε)^{ε/t} ≤ e^{1/e} < 1.4447`.  The three lemmas below are that computation, in the
sharper form `< 3/2` that the exclusion of alternative (ii) of Lemma 9.1.2 needs. -/

/-- `log c ≤ c/e` for `c > 0`: apply `log x ≤ x - 1` to `x = c/e` and use
`log (c/e) = log c - 1`.  (A step in the proof of Cor. 9.1.3.) -/
theorem log_le_div_exp_one {c : ℝ} (hc : 0 < c) : Real.log c ≤ c / Real.exp 1 := by
  have hpos : (0 : ℝ) < c / Real.exp 1 := div_pos hc (Real.exp_pos 1)
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (ne_of_gt hc) (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- `e^{1/e} < 3/2`.  From `2.5 < e` we get `1/e < 2/5`, and `(e^{2/5})^5 = e^2 < 7.39 <
7.59375 = (3/2)^5`.  (A step in the proof of Cor. 9.1.3.) -/
theorem exp_inv_exp_one_lt : Real.exp (1 / Real.exp 1) < 3 / 2 := by
  have hgt : (2.5 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h1 : 1 / Real.exp 1 < 2 / 5 := by
    rw [div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 5)]
    linarith
  have hexp2 : Real.exp 2 < (3 / 2 : ℝ) ^ 5 := by
    have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    rw [hsq]
    nlinarith
  have h2 : Real.exp (2 / 5 : ℝ) < 3 / 2 := by
    refine lt_of_pow_lt_pow_left₀ 5 (by norm_num) ?_
    have : Real.exp (2 / 5 : ℝ) ^ 5 = Real.exp 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]; exact hexp2
  exact lt_of_le_of_lt (Real.exp_le_exp.2 h1.le) h2

/-- `c^{m/c} ≤ (3/2)^m` for `c > 0` and `m ≥ 0`: `c^{m/c} = exp (m·(log c)/c) ≤
exp (m/e) = (e^{1/e})^m`.  (A step in the proof of Cor. 9.1.3; with `c = t/ε` and `m` the
degree, `m/c = εm/t`.) -/
theorem rpow_div_le_three_halves_rpow {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) :
    c ^ (m / c) ≤ (3 / 2 : ℝ) ^ m := by
  have hlog : Real.log c / c ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ hc (Real.exp_pos 1)]
    have h := log_le_div_exp_one hc
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos 1))
    rw [div_mul_cancel₀ _ (Real.exp_ne_zero 1)] at h2
    linarith
  have h1 : c ^ (m / c) = Real.exp (m * (Real.log c / c)) := by
    rw [Real.rpow_def_of_pos hc]
    exact congrArg Real.exp (by field_simp)
  have h2 : Real.exp (m * (Real.log c / c)) ≤ Real.exp (m * (1 / Real.exp 1)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog hm)
  have h3 : Real.exp (m * (1 / Real.exp 1)) = Real.exp (1 / Real.exp 1) ^ m := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    exact congrArg Real.exp (by ring)
  have h4 : Real.exp (1 / Real.exp 1) ^ m ≤ (3 / 2 : ℝ) ^ m :=
    Real.rpow_le_rpow (le_of_lt (Real.exp_pos _)) (le_of_lt exp_inv_exp_one_lt) hm
  rw [h1]
  exact le_trans h2 (le_trans (le_of_eq h3) h4)

/-- The opening line of the proof of Cor. 9.1.3, *"the condition implies that
`|S_m : G| < 1.9^m`"*, in the sharper form used to exclude alternative (ii) of
Lemma 9.1.2: `(t/ε)^{εm/t} ≤ (3/2)^m`. -/
theorem johnson_cost_le_three_halves_rpow {t : ℕ} {ε m : ℝ} (hε : 0 < ε)
    (ht : 0 < (t : ℝ)) (hm : 0 ≤ m) :
    ((t : ℝ) / ε) ^ (ε * m / (t : ℝ)) ≤ (3 / 2 : ℝ) ^ m := by
  have hc : 0 < (t : ℝ) / ε := div_pos ht hε
  have hexp : ε * m / (t : ℝ) = m / ((t : ℝ) / ε) := by
    field_simp
  rw [hexp]
  exact rpow_div_le_three_halves_rpow hc hm

/-- The inductive step of `two_mul_three_pow_lt_choose`: `3·C(m, (m-1)/2) ≤ 2·C(m+1, m/2)`
for `m ≥ 5`.  For `m = 2i+2` both `C(2i+2,i)` and `C(2i+2,i+1)` appear in Pascal's
identity for `C(2i+3,i+1)`, and the second is the larger; for `m = 2i+5` Pascal's identity
for `C(2i+6,i+2)` gives `C(2i+5,i+1) + C(2i+5,i+2)`, and
`C(2i+5,i+2)·(i+2) = C(2i+5,i+1)·(i+4) ≤ 2·C(2i+5,i+1)·(i+2)`. -/
theorem three_mul_choose_le_two_mul_choose_succ {m : ℕ} (hm : 5 ≤ m) :
    3 * m.choose ((m - 1) / 2) ≤ 2 * (m + 1).choose (m / 2) := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨i, rfl⟩ : ∃ i, m = 2 * i + 2 := by
      obtain ⟨k, hk⟩ := he; exact ⟨k - 1, by omega⟩
    have h1 : (2 * i + 2 - 1) / 2 = i := by omega
    have h2 : (2 * i + 2) / 2 = i + 1 := by omega
    rw [h1, h2]
    have hpascal : (2 * i + 2 + 1).choose (i + 1)
        = (2 * i + 2).choose i + (2 * i + 2).choose (i + 1) :=
      Nat.choose_succ_succ (2 * i + 2) i
    have hkey : (2 * i + 2).choose (i + 1) * (i + 1)
        = (2 * i + 2).choose i * (2 * i + 2 - i) := Nat.choose_succ_right_eq _ _
    have hge : (2 * i + 2).choose i ≤ (2 * i + 2).choose (i + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos i)
      rw [hkey]
      have : 2 * i + 2 - i = i + 2 := by omega
      rw [this]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [hpascal]
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, m = 2 * i + 5 := by
      obtain ⟨k, hk⟩ := ho; exact ⟨k - 2, by omega⟩
    have h1 : (2 * i + 5 - 1) / 2 = i + 2 := by omega
    have h2 : (2 * i + 5) / 2 = i + 2 := by omega
    rw [h1, h2]
    have hpascal : (2 * i + 5 + 1).choose (i + 2)
        = (2 * i + 5).choose (i + 1) + (2 * i + 5).choose (i + 2) :=
      Nat.choose_succ_succ (2 * i + 5) (i + 1)
    have hkey : (2 * i + 5).choose (i + 2) * (i + 2)
        = (2 * i + 5).choose (i + 1) * (2 * i + 5 - (i + 1)) :=
      Nat.choose_succ_right_eq _ _
    have hA : (2 * i + 5).choose (i + 2) ≤ 2 * (2 * i + 5).choose (i + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (show 0 < i + 2 by omega)
      rw [hkey]
      have hsub : 2 * i + 5 - (i + 1) = i + 4 := by omega
      rw [hsub]
      calc (2 * i + 5).choose (i + 1) * (i + 4)
          ≤ (2 * i + 5).choose (i + 1) * (2 * (i + 2)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (2 * i + 5).choose (i + 1) * (i + 2) := by ring
    rw [hpascal]
    omega

/-- `2·3^m < 2^m·C(m, (m-1)/2)` for `m ≥ 9`, i.e. `2·(3/2)^m < C(m, (m-1)/2)`.  This is
what excludes alternative (ii) of Lemma 9.1.2 in the proof of Cor. 9.1.3: in that case
`2·|S_m : G| = C(m, ⌊m/2⌋) ≥ C(m, (m-1)/2) > 2·(3/2)^m > 2·|S_m : G|`.  Induction on `m`,
with `three_mul_choose_le_two_mul_choose_succ` as the step and `2·3^9 = 39366 < 64512 =
2^9·C(9,4)` as the base. -/
theorem two_mul_three_pow_lt_choose {m : ℕ} (hm : 9 ≤ m) :
    2 * 3 ^ m < 2 ^ m * m.choose ((m - 1) / 2) := by
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 9 with hn | hn
    · have hn9 : n = 8 := by omega
      subst hn9
      norm_num [show (9:ℕ).choose 4 = 126 from by decide]
    · have hstep := three_mul_choose_le_two_mul_choose_succ (m := n) (by omega)
      have hih := ih (by omega)
      have hn1 : (n + 1 - 1) / 2 = n / 2 := by omega
      rw [hn1]
      calc 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
        _ < 3 * (2 ^ n * n.choose ((n - 1) / 2)) := by
            exact (Nat.mul_lt_mul_left (by omega)).2 hih
        _ = 2 ^ n * (3 * n.choose ((n - 1) / 2)) := by ring
        _ ≤ 2 ^ n * (2 * (n + 1).choose (n / 2)) := Nat.mul_le_mul_left _ hstep
        _ = 2 ^ (n + 1) * (n + 1).choose (n / 2) := by ring

/-- The two computations above combined, in the form the proof of Cor. 9.1.3 uses: a
number below the multiplicative cost `(t/ε)^{εm/t}` of the corollary satisfies
`2N < C(m, (m-1)/2)` for `m ≥ 9`.  With `N = |S_m : G|` this is both the opening line
*"the condition implies that `|S_m : G| < 1.9^m`"* and the exclusion of alternative (ii)
of Lemma 9.1.2. -/
theorem two_mul_lt_choose_of_lt_cost {m t N : ℕ} {ε : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hm : 9 ≤ m) (h : (N : ℝ) < ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ))) :
    2 * N < m.choose ((m - 1) / 2) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h1 : (N : ℝ) < (3 / 2 : ℝ) ^ ((m : ℕ) : ℝ) :=
    lt_of_lt_of_le h (johnson_cost_le_three_halves_rpow hε htR (Nat.cast_nonneg m))
  rw [Real.rpow_natCast] at h1
  have hpow : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2 : (N : ℝ) * (2 : ℝ) ^ m < (3 : ℝ) ^ m := by
    have := (mul_lt_mul_of_pos_right h1 hpow)
    rwa [div_pow, div_mul_cancel₀ _ (ne_of_gt hpow)] at this
  have h3 : N * 2 ^ m < 3 ^ m := by exact_mod_cast h2
  have h4 : 2 ^ m * (2 * N) < 2 ^ m * m.choose ((m - 1) / 2) := by
    calc 2 ^ m * (2 * N) = 2 * (N * 2 ^ m) := by ring
      _ < 2 * 3 ^ m := by omega
      _ < 2 ^ m * m.choose ((m - 1) / 2) := two_mul_three_pow_lt_choose hm
  exact Nat.lt_of_mul_lt_mul_left h4

/-- The first step of the paper's chain in the proof of Corollary 9.1.3 is false:
`C(9,2)/C(10,2) = 36/45 = 0.8`, while `(1 - 1/10)² = 0.81`.  In the cross-multiplied form
`(m-r)^t * C(m,t) ≤ m^t * C(m-r,t)` the paper's inequality would read
`9² * 45 ≤ 10² * 36`, i.e. `3645 ≤ 3600`. -/
example : ¬ ((10 - 1) ^ 2 * Nat.choose 10 2 ≤ 10 ^ 2 * Nat.choose (10 - 1) 2) := by decide

/-! ### The two estimates behind Eq. (50)

Eq. (50) of the proof of Cor. 9.1.3 is the chain
`|S_m : G| ≥ C(m,r) ≥ (m/r)^r = ((m/r)^{r/m})^m ≥ (t/ε)^{εm/t}`.  Its two steps are the
binomial bound `(m/x)^x ≤ C(m,x)` and the monotonicity of `x ↦ (m/x)^x` on `(0, m/e]`; the
two lemmas below are exactly these.  The paper is terse here, so both are filled in with the
smallest argument we found: an induction for the first, and `log y ≤ y - 1` for the second
(no derivative is needed). -/

/-- The binomial bound `(m/s)^s ≤ C(m,s)` of Eq. (50), in the integer form
`m^s ≤ s^s · C(m,s)` for `s ≤ m`.

Induction on `s`.  For the step, `C(m'+1, s+1)·(s+1) = (m'+1)·C(m',s)`
(`Nat.add_one_mul_choose_eq`) and `(m'+1)·s ≤ (s+1)·m'` (which is `s ≤ m'`) give
`(m'+1)^{s+2}·s^s = (m'+1)²·((m'+1)·s)^s ≤ (m'+1)²·(s+1)^s·m'^s ≤ (s+1)^{s+1}·C(m'+1,s+1)·
((m'+1)·s^s)`, and the positive factor `(m'+1)·s^s` cancels. -/
theorem pow_le_pow_mul_choose : ∀ s m : ℕ, s ≤ m → m ^ s ≤ s ^ s * m.choose s := by
  intro s
  induction s with
  | zero => intro m _; simp
  | succ s ih =>
    intro m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hs : s ≤ m' := by omega
    have hIH := ih m' hs
    have hid : (m' + 1) * m'.choose s = (m' + 1).choose (s + 1) * (s + 1) :=
      Nat.add_one_mul_choose_eq m' s
    have hmul : (m' + 1) * s ≤ (s + 1) * m' := by
      calc (m' + 1) * s = m' * s + s := by ring
        _ ≤ m' * s + m' := by omega
        _ = (s + 1) * m' := by ring
    have hss : 0 < s ^ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h
      · simp
      · exact Nat.pow_pos h
    have hpos : 0 < (m' + 1) * s ^ s := Nat.mul_pos (by omega) hss
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have hstep : (m' + 1) ^ s * s ^ s ≤ (s + 1) ^ s * m' ^ s := by
      rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left hmul s
    calc (m' + 1) ^ (s + 1) * ((m' + 1) * s ^ s)
        = (m' + 1) ^ 2 * ((m' + 1) ^ s * s ^ s) := by ring
      _ ≤ (m' + 1) ^ 2 * ((s + 1) ^ s * m' ^ s) := Nat.mul_le_mul_left _ hstep
      _ ≤ (m' + 1) ^ 2 * ((s + 1) ^ s * (s ^ s * m'.choose s)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hIH)
      _ = ((s + 1) ^ s * s ^ s) * ((m' + 1) * ((m' + 1) * m'.choose s)) := by ring
      _ = ((s + 1) ^ s * s ^ s) * ((m' + 1) * ((m' + 1).choose (s + 1) * (s + 1))) := by
          rw [hid]
      _ = (s + 1) ^ (s + 1) * (m' + 1).choose (s + 1) * ((m' + 1) * s ^ s) := by ring

/-- The monotonicity step of Eq. (50): `(m/a)^a ≤ (m/s)^s` for `0 < a ≤ s` and `s·e ≤ m`,
i.e. on the range `s ≤ m/e` where `x ↦ x·log(m/x)` increases.

No derivative is needed.  From `log y ≤ y - 1` at `y = s/a`,
`log(m/a) - log(m/s) = log(s/a) ≤ (s-a)/a`, so `a·log(m/a) ≤ a·log(m/s) + (s-a)`; and
`log(m/s) ≥ 1` because `m/s ≥ e`, so `s - a ≤ (s-a)·log(m/s)`.  Adding,
`a·log(m/a) ≤ s·log(m/s)`. -/
theorem rpow_div_le_rpow_div {m a s : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hsm : s * Real.exp 1 ≤ m) : (m / a) ^ a ≤ (m / s) ^ s := by
  have hs : 0 < s := lt_of_lt_of_le ha has
  have hepos : (0 : ℝ) < s * Real.exp 1 := mul_pos hs (Real.exp_pos 1)
  have hm : 0 < m := lt_of_lt_of_le hepos hsm
  have hms : Real.exp 1 ≤ m / s := by rw [le_div_iff₀ hs]; linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (m / s) := by
    have h := Real.log_le_log (Real.exp_pos 1) hms
    rwa [Real.log_exp] at h
  have hlogsa : Real.log (s / a) ≤ (s - a) / a := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < s / a from div_pos hs ha)
    have he : s / a - 1 = (s - a) / a := by field_simp
    linarith [h, he.ge, he.le]
  have hsplit : Real.log (m / a) = Real.log (m / s) + Real.log (s / a) := by
    rw [Real.log_div hm.ne' ha.ne', Real.log_div hm.ne' hs.ne', Real.log_div hs.ne' ha.ne']
    ring
  have h1 : a * Real.log (s / a) ≤ s - a := by
    have h := mul_le_mul_of_nonneg_left hlogsa ha.le
    have he : a * ((s - a) / a) = s - a := by field_simp
    linarith [h, he.ge, he.le]
  have h2 : s - a ≤ (s - a) * Real.log (m / s) := by nlinarith
  have hring : a * Real.log (m / s) + (s - a) * Real.log (m / s) = s * Real.log (m / s) := by
    ring
  have hkey : a * Real.log (m / a) ≤ s * Real.log (m / s) := by
    rw [hsplit, mul_add]; linarith
  rw [Real.rpow_def_of_pos (div_pos hm ha), Real.rpow_def_of_pos (div_pos hm hs)]
  exact Real.exp_le_exp.2 (by linarith [hkey, mul_comm a (Real.log (m / a))])

/-- Corollary 9.1.3.  *"Let `G ≤ Aut(J(m,t))` and `0 < ε ≤ 1/3`.  If `m!/|G| < (t/ε)^{εm/t}`
then `G` acts as a primitive group on a subset of relative size `≥ (1 - ε)`."*
(Version 2.5, lines 3953–3966.)

Paper's proof: *"The condition implies that `|S_m : G| < 1.9^m`.  Let `r` be the smallest
value such that `|S_m : G| < C(m, r+1)`.  By Lemma 9.1.2, we have a Johnson group
`A⁽ᵗ⁾_{m-r} ≤ G⁽ᵗ⁾` act on a subset of size `C(m-r,t)`.  This group is primitive on this
subset.  Now `C(m-r,t)/C(m,t) ≥ (1 - r/m)^t > 1 - (rt/m)`.  So we are done if `rt/m > ε`.
Let us assume `rt/m ≤ ε`.  Then `|S_m : G| ≥ C(m,r) ≥ (m/r)^r = (m/r)^{r/m·m} ≥
(t/ε)^{εm/t}`, contrary assumption."*

Three points about this proof:
* the two occurrences of the condition on `rt/m` are interchanged: the corollary is proved
  when `rt/m ≤ ε` (then the subset has relative size `> 1 - ε`), and the contradiction
  (50) is derived in the case `rt/m > ε`, where `r > εm/t` makes `C(m,r) ≥ (m/r)^r`
  exceed `(t/ε)^{εm/t}` — with the inequality as printed the chain (50) runs the wrong
  way, since `u ↦ (1/u)^u` is increasing on `(0, 1/e)` and `ε/t ≤ 1/3 < 1/e`;
* the displayed chain `C(m−r,t)/C(m,t) ≥ (1−r/m)^t > 1−(rt/m)` is false in both steps
  (`m = 10`, `r = 1`, `t = 2` gives `0.8 ≥ 0.81`; and `r = 1` gives equality in the second
  step).  Its conclusion holds with `≥`, and that is what is used; the repaired step is
  `Babai.choose_sub_mul_le` above;
* the alternative (ii) of the repaired Lemma 9.1.2 is excluded here by the index bound:
  in that case `|S_m : G| = C(m, ⌊m/2⌋)/2`, which exceeds `(t/ε)^{εm/t} ≤ 1.4447^m` for
  `m ≥ 6`.

The subset of relative size `≥ 1 - ε` is a subset of the **vertex set of the Johnson
scheme**, i.e. of the `t`-subsets: it is the set of `t`-subsets of `Γ = [m] \ T`, of size
`C(m-r,t) ≥ (1-ε)C(m,t)`.

The upper bound `G ≤ S(Γ)_T` from Lemma 9.1.2 makes `Δ = Tᶜ` invariant under `G`.
Thus `G` acts on the `t`-subsets of `Δ`. Its induced group contains `A(Δ)` acting on
those subsets. This subgroup is primitive when `2t + 1 ≤ |Δ|`, so the induced group
of `G` is primitive too (`Babai.cor_9_1_3_isPrimitive`). The returned bound
`2t + 1 ≤ |Δ|` follows from `rt < εm` and `ε ≤ 1/3`, as shown below.

*Strictness.*  This is the corollary with `>` in place of the paper's `≥`, which is what
Prop. 9.1.1 needs (a block of relative size exactly `1-ε` would not contradict
`ρ(Π) ≤ (1-ε)n`).  The paper's own proof gives it, once the case split is made at
`rt = εm` rather than at `rt/m > ε`: the contradiction of Eq. (50) needs only `εm ≤ rt`,
since then `εm/t ≤ r` and the chain runs as before; and in the remaining case `rt < εm` the
estimate `C(m-r,t) ≥ (1 - rt/m)·C(m,t) > (1-ε)·C(m,t)` is strict.  Equality really can
occur in `C(m-r,t) ≥ (1 - rt/m)·C(m,t)` (it is an equality for `r = 1`), so the case
split has to be the one above.  The paper's form is `Babai.cor_9_1_3` (below, after the
case `m ≤ 8`). -/
private theorem cor_9_1_3_strict_stabilizers {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)}
    {t : ℕ} {ε : ℝ} (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ Nat.card Γ) (hm : 9 ≤ Nat.card Γ)
    (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    ∃ Δ : Set Γ, (1 - ε) * ((Nat.card Γ).choose t : ℝ) < ((Δ.ncard).choose t : ℝ) ∧
      pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard ∧
      G ≤ setwiseStabilizer ⊤ Δ := by
  set m := Nat.card Γ with hmdef
  have hmpos : 0 < m := by omega
  have htpos : 0 < t := by omega
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
  have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hm9R : (9 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- Step 4: `r` is the least value with `|S_m : G| < C(m, r+1)`.  It exists because
  -- `2·|S_m : G| < C(m, (m-1)/2)`, which is the opening line of the proof.
  have htwo : 2 * G.index < m.choose ((m - 1) / 2) :=
    two_mul_lt_choose_of_lt_cost hε htpos hm hindex
  have hwit : G.index < m.choose ((m - 1) / 2 - 1 + 1) := by
    rw [show (m - 1) / 2 - 1 + 1 = (m - 1) / 2 by omega]; omega
  have hex : ∃ r : ℕ, G.index < m.choose (r + 1) := ⟨(m - 1) / 2 - 1, hwit⟩
  obtain ⟨r, hspec, hrle, hmin⟩ : ∃ r : ℕ, G.index < m.choose (r + 1) ∧
      r ≤ (m - 1) / 2 - 1 ∧ (1 ≤ r → m.choose r ≤ G.index) := by
    refine ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex hwit, ?_⟩
    intro h1
    have h := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at h
    omega
  have hr2 : 2 * (r + 1) < m := by omega
  rcases lemma_9_1_2 hm hr2 hspec with ⟨T, hTcard, hstab, hset⟩ | ⟨-, -, hhalf⟩
  · -- the main alternative of Lemma 9.1.2
    by_cases hcase : (r : ℝ) * t < ε * (m : ℝ)
    · -- Steps 6 and 8: `rt/m < ε`, and `Δ = Tᶜ` is the subset we want.
      have h3rtR : (3 * (r * t) : ℝ) ≤ (m : ℝ) := by nlinarith
      have h3rt : 3 * (r * t) ≤ m := by exact_mod_cast h3rtR
      have hrt : r * t ≤ m := by
        calc r * t ≤ 3 * (r * t) := by omega
          _ ≤ m := h3rt
      have hcompl : T.ncard + Tᶜ.ncard = m := Set.ncard_add_ncard_compl T
      have hk : m - r ≤ Tᶜ.ncard := by omega
      refine ⟨Tᶜ, ?_, ?_, ?_, fun g hg =>
        ⟨Subgroup.mem_top g, isInvariant_compl_of_le_setwiseStabilizer hset g hg⟩⟩
      · -- `(1-ε)·C(m,t) ≤ (1 - rt/m)·C(m,t) ≤ C(m-r,t) ≤ C(|Δ|,t)`
        have hrt2 : r + t ≤ m := by omega
        have hkey := choose_sub_mul_le (m := m) (t := t) r hrt hrt2
        have hmono : (m - r).choose t ≤ (Tᶜ.ncard).choose t := Nat.choose_le_choose t hk
        have hcast : ((m - r * t : ℕ) : ℝ) = (m : ℝ) - (r : ℝ) * t := by
          push_cast [hrt]; ring
        have hA : ((m - r * t : ℕ) : ℝ) * (m.choose t : ℝ)
            ≤ (m : ℝ) * ((m - r).choose t : ℝ) := by exact_mod_cast hkey
        have hB : ((m - r).choose t : ℝ) ≤ ((Tᶜ.ncard).choose t : ℝ) := by
          exact_mod_cast hmono
        have hC : (1 - ε) * (m : ℝ) < ((m - r * t : ℕ) : ℝ) := by rw [hcast]; nlinarith
        have hchoose_pos : (0 : ℝ) < (m.choose t : ℝ) := by
          have : 0 < m.choose t := Nat.choose_pos (by omega)
          exact_mod_cast this
        refine lt_of_mul_lt_mul_right ?_ hmR.le
        calc (1 - ε) * (m.choose t : ℝ) * (m : ℝ)
            = ((1 - ε) * (m : ℝ)) * (m.choose t : ℝ) := by ring
          _ < ((m - r * t : ℕ) : ℝ) * (m.choose t : ℝ) :=
              mul_lt_mul_of_pos_right hC hchoose_pos
          _ ≤ (m : ℝ) * ((m - r).choose t : ℝ) := hA
          _ ≤ (m : ℝ) * ((Tᶜ.ncard).choose t : ℝ) := mul_le_mul_of_nonneg_left hB hmR.le
          _ = ((Tᶜ.ncard).choose t : ℝ) * (m : ℝ) := by ring
      · rw [compl_compl]; exact hstab
      · -- `2t+1 ≤ |Δ|`: if `r = 0` then `|Δ| = m`; if `r ≥ 1` then `3t ≤ m` and `6r ≤ m`.
        rcases Nat.eq_zero_or_pos r with hr0 | hr1
        · omega
        · have h3t : 3 * t ≤ m := by
            calc 3 * t = 3 * (1 * t) := by ring
              _ ≤ 3 * (r * t) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right t hr1)
              _ ≤ m := h3rt
          have h6r : 6 * r ≤ m := by
            calc 6 * r = 3 * (r * 2) := by ring
              _ ≤ 3 * (r * t) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left r ht)
              _ ≤ m := h3rt
          omega
    · -- Step 7: `rt/m > ε` contradicts the hypothesis, by Eq. (50).
      exfalso
      rw [not_lt] at hcase
      have hapos : 0 < ε * (m : ℝ) / (t : ℝ) := by positivity
      set a : ℝ := ε * (m : ℝ) / (t : ℝ) with hadef
      have har : a ≤ (r : ℝ) := by rw [hadef, div_le_iff₀ htR]; linarith
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with hr0 | hr1
        · rw [hr0] at har; norm_num at har; linarith
        · exact hr1
      -- `s = ⌈εm/t⌉ ≤ r` is where the monotonicity of `x ↦ (m/x)^x` is applied.
      set s : ℕ := ⌈a⌉₊ with hsdef
      have has : a ≤ (s : ℝ) := Nat.le_ceil a
      have hsr : s ≤ r := Nat.ceil_le.2 har
      have hspos : 0 < s := Nat.ceil_pos.2 hapos
      have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hspos
      -- `s ≤ m/6 + 1 ≤ m/e`, which is what the monotonicity needs.
      have ha6 : a ≤ (m : ℝ) / 6 := by
        rw [hadef, div_le_div_iff₀ htR (by norm_num : (0:ℝ) < 6)]
        nlinarith
      have hsm6 : (s : ℝ) ≤ (m : ℝ) / 6 + 1 := by
        have := (Nat.ceil_lt_add_one hapos.le).le
        rw [← hsdef] at this
        linarith
      have hexp : (s : ℝ) * Real.exp 1 ≤ (m : ℝ) := by
        have he : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
        calc (s : ℝ) * Real.exp 1 ≤ ((m : ℝ) / 6 + 1) * Real.exp 1 :=
              mul_le_mul_of_nonneg_right hsm6 (Real.exp_pos 1).le
          _ ≤ ((m : ℝ) / 6 + 1) * 2.7183 := by nlinarith
          _ ≤ (m : ℝ) := by linarith
      -- Eq. (50): `(t/ε)^{εm/t} = (m/a)^a ≤ (m/s)^s ≤ C(m,s) ≤ C(m,r) ≤ |S_m : G|`.
      -- `C(m,s) ≤ C(m,r)`: binomial coefficients increase up to the middle
      have hmono : m.choose s ≤ m.choose r := choose_le_choose_of_le_half hsr (by omega)
      have hidx : m.choose r ≤ G.index := hmin hr1
      have hsle : s ≤ m := le_trans hsr (by omega)
      have hpow := pow_le_pow_mul_choose s m hsle
      have hbin : ((m : ℝ) / (s : ℝ)) ^ (s : ℕ) ≤ (m.choose s : ℝ) := by
        rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (s : ℝ) ^ (s : ℕ))]
        have hcast : ((m : ℝ)) ^ (s : ℕ) ≤ ((s : ℝ)) ^ (s : ℕ) * (m.choose s : ℝ) := by
          exact_mod_cast hpow
        linarith
      have hbase : (t : ℝ) / ε = (m : ℝ) / a := by
        rw [hadef]; field_simp
      have hchain : ((t : ℝ) / ε) ^ a ≤ (G.index : ℝ) := by
        rw [hbase]
        calc ((m : ℝ) / a) ^ a ≤ ((m : ℝ) / (s : ℝ)) ^ ((s : ℕ) : ℝ) :=
              rpow_div_le_rpow_div hapos has hexp
          _ = ((m : ℝ) / (s : ℝ)) ^ (s : ℕ) := Real.rpow_natCast _ _
          _ ≤ (m.choose s : ℝ) := hbin
          _ ≤ (m.choose r : ℝ) := by exact_mod_cast hmono
          _ ≤ (G.index : ℝ) := by exact_mod_cast hidx
      linarith
  · -- Step 5: alternative (ii) of Lemma 9.1.2 is excluded by the index bound.
    exfalso
    rw [← hmdef] at hhalf
    have hmid : m.choose ((m - 1) / 2) ≤ m.choose (m / 2) := Nat.choose_le_middle _ _
    omega

/-- Corollary 9.1.3, §9.1, with strict relative size. The upper stabilizer bound
makes the label set invariant under `G`. The action of `G` on its `t`-subsets contains
an alternating Johnson group, so that induced action is primitive. The strict size
bound uses the repaired split at `rt = εm`; see the Corollary 9.1.3 strictness entry
in the corrected paper. -/
theorem cor_9_1_3_strict {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Equiv.Perm Γ)}
    {t : ℕ} {ε : ℝ} (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ Nat.card Γ) (hm : 9 ≤ Nat.card Γ)
    (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    ∃ Δ : Set Γ, (1 - ε) * ((Nat.card Γ).choose t : ℝ) < ((Δ.ncard).choose t : ℝ) ∧
      pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard ∧
      G ≤ setwiseStabilizer ⊤ Δ ∧
      ∃ hΔ : IsInvariant G Δ,
        IsInvariant (inducedOnTSets G t) {S : binom Γ t | ∀ x ∈ S.val, x ∈ Δ} ∧
        IsPrimitive (inducedOnTSets (restrictTo G Δ hΔ) t) := by
  obtain ⟨Δ, hsize, hstab, hk, hset⟩ :=
    cor_9_1_3_strict_stabilizers ht hmt hm hε hε3 hindex
  have hΔ : IsInvariant G Δ := fun g hg => (hset hg).2
  exact ⟨Δ, hsize, hstab, hk, hset, hΔ, isInvariant_binom_subset hΔ t,
    cor_9_1_3_isPrimitive hΔ hstab (by omega) hk⟩

/-! ### Corollary 9.1.3 for `m ≤ 8`

The proof of Corollary 9.1.3 goes through Lemma 9.1.2, which needs `m ≥ 9`
(the corrected paper: the Jordan–Liebeck theorem the lemma cites carries that
hypothesis).  The corollary itself has no such hypothesis, and it is true for `m ≤ 8` as
well; the range `m ≤ 8` is finite and the proof there is a different one, by inspection of
the subgroups of small index of `S_m`.  That inspection is
`Babai.small_index_subgroup_perm` below, which uses the cited theorem
`[DiM, Thm. 5.2B]` at `r = 2`.

In this range `t ∈ {2,3}` and `5 ≤ m ≤ 8` (from `2 ≤ t` and `2t + 1 ≤ m ≤ 8`). -/

/-- The bound of Corollary 9.1.3 is at most `m` when `ε ≤ t/m`.

The exponent is `a = εm/t ≤ 1` and the bound is `(m/a)^a`, which increases on `(0, m/e]`
by `Babai.rpow_div_le_rpow_div`; at `a = 1` it is `m`.  (Used in the small cases of the
corollary: there `m ≤ |S_m : G|`, so the hypothesis of the corollary forces `ε > t/m`,
which is exactly what makes the complement of a point large enough.) -/
theorem cost_le_of_le_div {m t : ℕ} {ε : ℝ} (ht : 0 < t) (hm : 3 ≤ m) (hε : 0 < ε)
    (hle : ε ≤ (t : ℝ) / m) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (m : ℝ) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmR : (0 : ℝ) < (m : ℝ) := by linarith
  set a : ℝ := ε * (m : ℝ) / (t : ℝ) with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  have ha1 : a ≤ 1 := by
    rw [hadef, div_le_one htR]
    have h := mul_le_mul_of_nonneg_right hle hmR.le
    rw [div_mul_cancel₀ _ (ne_of_gt hmR)] at h
    linarith
  have hbase : (t : ℝ) / ε = (m : ℝ) / a := by rw [hadef]; field_simp
  have hexp : Real.exp 1 ≤ (m : ℝ) := by
    have h := lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 3)
    linarith
  have h := rpow_div_le_rpow_div (m := (m : ℝ)) (a := a) (s := 1) hapos ha1 (by simpa using hexp)
  rw [hbase]
  simpa using h

/-- The bound of Corollary 9.1.3 is at most `6^{m/6}` when `t ≥ 2` and `ε ≤ 1/3`.

The exponent is `a = εm/t`, the bound is `(m/a)^a`, and `a ≤ m/6` because `6ε ≤ 2 ≤ t`.
On `0 < a ≤ m/e` the function `a ↦ (m/a)^a` increases (`Babai.rpow_div_le_rpow_div`), and
`m/6 ≤ m/e`, so the bound is at most `(m/(m/6))^{m/6} = 6^{m/6}`.  (Used in the small
cases of the corollary, `Babai.small_index_subgroup_perm`.) -/
theorem cost_le_six_rpow {m t : ℕ} {ε : ℝ} (ht : 2 ≤ t) (hm : 0 < m) (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (6 : ℝ) ^ ((m : ℝ) / 6) := by
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set a : ℝ := ε * (m : ℝ) / (t : ℝ) with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  have has : a ≤ (m : ℝ) / 6 := by
    rw [hadef, div_le_div_iff₀ htpos (by norm_num : (0:ℝ) < 6)]
    nlinarith
  have hbase : (t : ℝ) / ε = (m : ℝ) / a := by rw [hadef]; field_simp
  have hexp : Real.exp 1 ≤ 6 := by
    have h := Real.exp_one_lt_d9
    linarith
  have hsm : ((m : ℝ) / 6) * Real.exp 1 ≤ (m : ℝ) := by
    have h : ((m : ℝ) / 6) * Real.exp 1 ≤ ((m : ℝ) / 6) * 6 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    have h6 : ((m : ℝ) / 6) * 6 = (m : ℝ) := by ring
    linarith
  have h := rpow_div_le_rpow_div hapos has hsm
  have hcancel : (m : ℝ) / ((m : ℝ) / 6) = 6 := by field_simp
  rw [hcancel] at h
  rw [hbase]
  exact h

/-- `6^{m/6} ≤ B` whenever `6^m ≤ B^6`: raise both sides to the sixth power.

(The numeric step of `Babai.small_index_subgroup_perm`, used at `(m, B) = (5,5)`, `(6,6)`,
`(7,21)` and `(8,28)`.) -/
theorem six_rpow_le_of_pow_le {m B : ℕ} (h : 6 ^ m ≤ B ^ 6) :
    (6 : ℝ) ^ ((m : ℝ) / 6) ≤ (B : ℝ) := by
  have hpow : ((6 : ℝ) ^ ((m : ℝ) / 6)) ^ (6 : ℕ) = (6 : ℝ) ^ (m : ℕ) := by
    rw [← Real.rpow_natCast ((6 : ℝ) ^ ((m : ℝ) / 6)) 6, ← Real.rpow_mul (by norm_num)]
    have he : (m : ℝ) / 6 * ((6 : ℕ) : ℝ) = ((m : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have key : ((6 : ℝ) ^ ((m : ℝ) / 6)) ^ (6 : ℕ) ≤ ((B : ℝ)) ^ (6 : ℕ) := by
    rw [hpow]; exact_mod_cast h
  exact le_of_pow_le_pow_left₀ (by norm_num) (Nat.cast_nonneg B) key

/-- **Subgroups of small index of `S_m` for `5 ≤ m ≤ 8`**, §9.1.

Under the hypotheses of Corollary 9.1.3 and `m ≤ 8`: either `|S_m : G| < m`, and then `G`
contains `A_m`; or `m ≤ |S_m : G|`, and then `G` fixes a point and contains its
pointwise stabilizer in `A_m`.  This is what replaces Lemma 9.1.2 in the range `m ≤ 8`, which the Jordan–
Liebeck theorem does not cover.

The proof is the cited theorem `[DiM, Thm. 5.2B]` (Dixon–Mortimer, *Permutation Groups*,
GTM 163, 1996, pp. 150–151; `Babai.dixonMortimer_5_2B`) at `r = 2`, which the project
already has for Theorem 10.4.2.  Write `n = |S_m : G|`.

*The index is small.*  Since `2 ≤ t` and `2t + 1 ≤ m ≤ 8` we have `5 ≤ m`.  The exponent
`εm/t` is at most `m/6`, and `(m/a)^a` grows with `a` up to `a = m/e`, so the bound of the
corollary is at most `6^{m/6}` (`Babai.cost_le_six_rpow`).  Hence `n < 5` for `m = 5`,
`n < 6` for `m = 6`, `n < 21` for `m = 7` and `n < 28` for `m = 8`
(`Babai.six_rpow_le_of_pow_le`).  In every case `n < C(m,2)`, the hypothesis of
`[DiM, Thm. 5.2B]` at `r = 2`.

*Case (i) of that theorem*: there is a set `Δ` with `|Δ| < 2` and
`A_{(Δ)} ≤ G ≤ S_{\{Δ\}}`.  If `Δ = ∅` then `A_m ≤ G`, so `n` divides `|S_m : A_m| = 2`,
and `n ≤ 2 < m`: the first alternative.  If `Δ = {a}` then `G` lies in the stabilizer of
the point `a`, whose index is `C(m,1) = m` by orbit–stabilizer
(`Babai.relIndex_setwiseStabilizer`), so `m` divides `n` and `m ≤ n`: the second
alternative, with `A_{(\{a\})} ≤ G`.

*Case (ii)*: `2n = C(m, m/2)`, that is `n = 5`, `10`, `35/2`, `35` for `m = 5, 6, 7, 8`.
Each contradicts the bound on `n` (for `m = 7` already because `35` is odd).

*Case (iii)*: the exceptional cases.  Those with `m = 6` blocks of size 2, `m = 7` and
`m = 8` require `3 ≤ r`, and `r = 2`.  The rest force `(m, n) = (5,6)`, `(6,6)` or
`(6,12)`, and again the bound on `n` excludes them. -/
theorem small_index_subgroup_perm {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)} {t : ℕ} {ε : ℝ} (ht : 2 ≤ t)
    (hmt : 2 * t + 1 ≤ Nat.card Γ) (hm : Nat.card Γ ≤ 8) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    (G.index < Nat.card Γ ∧ alternatingGroup Γ ≤ G) ∨
      (Nat.card Γ ≤ G.index ∧
        ∃ a : Γ, pointwiseStabilizer (alternatingGroup Γ) {a} ≤ G ∧
          G ≤ setwiseStabilizer ⊤ {a}) := by
  classical
  have hm5 : 5 ≤ Nat.card Γ := by omega
  -- Step A: the index is small.
  have hcost := cost_le_six_rpow (m := Nat.card Γ) (t := t) (ε := ε) ht (by omega) hε hε3
  have hlt : (G.index : ℝ) < (6 : ℝ) ^ ((Nat.card Γ : ℝ) / 6) := lt_of_lt_of_le hindex hcost
  have hb : ∀ B : ℕ, 6 ^ (Nat.card Γ) ≤ B ^ 6 → G.index < B := by
    intro B hB
    have h := six_rpow_le_of_pow_le (m := Nat.card Γ) (B := B) hB
    exact_mod_cast lt_of_lt_of_le hlt h
  have hm58 : Nat.card Γ = 5 ∨ Nat.card Γ = 6 ∨ Nat.card Γ = 7 ∨ Nat.card Γ = 8 := by omega
  have hn : (Nat.card Γ = 5 → G.index < 5) ∧ (Nat.card Γ = 6 → G.index < 6) ∧
      (Nat.card Γ = 7 → G.index < 21) ∧ (Nat.card Γ = 8 → G.index < 28) := by
    refine ⟨fun h => hb 5 ?_, fun h => hb 6 ?_, fun h => hb 21 ?_, fun h => hb 28 ?_⟩ <;>
      rw [h] <;> norm_num
  -- The hypothesis of `[DiM, Thm. 5.2B]` at `r = 2`.
  have hidx : G.index < (Nat.card Γ).choose 2 := by
    rcases hm58 with h | h | h | h
    · have h5 := hn.1 h; rw [h]; show G.index < 10; omega
    · have h6 := hn.2.1 h; rw [h]; show G.index < 15; omega
    · have h7 := hn.2.2.1 h; rw [h]; show G.index < 21; omega
    · have h8 := hn.2.2.2 h; rw [h]; show G.index < 28; omega
  have hDM := dixonMortimer_5_2B (Ω := Γ) hm5 (r := 2) (by norm_num) (by omega) (G := G) hidx
  rcases hDM with ⟨Δ, hΔ, hpt, hset⟩ | ⟨-, -, hhalf⟩ | hexc
  · -- Case (i): `A_{(Δ)} ≤ G ≤ S_{{Δ}}` with `|Δ| < 2`.
    have hΔ01 : Δ.ncard = 0 ∨ Δ.ncard = 1 := by omega
    rcases hΔ01 with h0 | h1
    · -- `Δ = ∅`, so `A_m ≤ G` and `n ≤ 2`.
      have hempty : Δ = ∅ := (Set.ncard_eq_zero (Set.toFinite Δ)).1 h0
      rw [hempty, pointwiseStabilizer_empty] at hpt
      refine Or.inl ⟨?_, hpt⟩
      haveI : Nontrivial Γ := by
        rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]; omega
      have hdvd : G.index ∣ (alternatingGroup Γ).index := Subgroup.index_dvd_of_le hpt
      rw [alternatingGroup.index_eq_two] at hdvd
      have : G.index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · -- `Δ = {a}`, so `G` lies in the stabilizer of the point `a`, of index `m`.
      obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h1
      refine Or.inr ⟨?_, a, hpt, hset⟩
      have hstab : (setwiseStabilizer (⊤ : Subgroup (Equiv.Perm Γ)) ({a} : Set Γ)).index
          = Nat.card Γ := by
        have h := relIndex_setwiseStabilizer (Ω := Γ) (K := ⊤) le_top (m := 1) (by omega)
          (B := ({a} : Set Γ)) (Set.ncard_singleton a)
        rw [Subgroup.relIndex_top_right, Nat.choose_one_right] at h
        exact h
      have hdvd : (setwiseStabilizer (⊤ : Subgroup (Equiv.Perm Γ)) ({a} : Set Γ)).index
          ∣ G.index := Subgroup.index_dvd_of_le hset
      rw [hstab] at hdvd
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  · -- Case (ii): `2n = C(m, m/2)`.
    exfalso
    rcases hm58 with h | h | h | h
    · have h5 := hn.1 h; rw [h] at hhalf
      rw [show (5 : ℕ) / 2 = 2 from rfl, show Nat.choose 5 2 = 10 from rfl] at hhalf; omega
    · have h6 := hn.2.1 h; rw [h] at hhalf
      rw [show (6 : ℕ) / 2 = 3 from rfl, show Nat.choose 6 3 = 20 from rfl] at hhalf; omega
    · have h7 := hn.2.2.1 h; rw [h] at hhalf
      rw [show (7 : ℕ) / 2 = 3 from rfl, show Nat.choose 7 3 = 35 from rfl] at hhalf; omega
    · have h8 := hn.2.2.2 h; rw [h] at hhalf
      rw [show (8 : ℕ) / 2 = 4 from rfl, show Nat.choose 8 4 = 70 from rfl] at hhalf; omega
  · -- Case (iii): the exceptional cases, all excluded by `r = 2` or by the bound on `n`.
    exfalso
    rcases hexc with ⟨-, -, hcard, hr, -⟩ | ⟨-, hlist⟩
    · omega
    · rcases hlist with ⟨hc, -, hi, -⟩ | ⟨hc, -, hi, -⟩ | ⟨hc, -, hi, -⟩ | ⟨-, hr, -⟩ |
        ⟨-, hr, -⟩
      · have := hn.1 hc; omega
      · have := hn.2.1 hc; omega
      · have := hn.2.1 hc; omega
      · omega
      · omega

/-- Corollary 9.1.3 in the strict form `Babai.cor_9_1_3_strict`, for `m ≤ 8`.

Corollary 9.1.3 has no hypothesis `m ≥ 9`; that hypothesis enters our proof only through
Lemma 9.1.2.  This is the corollary in the remaining range,
deduced from the inspection of the subgroups of small index of `S_m`
(`Babai.small_index_subgroup_perm`): if `A_m ≤ G` then `Δ = [m]` works, and if
`m ≤ |S_m : G|` then `ε > t/m` by `Babai.cost_le_of_le_div`, so the complement `Δ` of the
point supplied by that lemma satisfies `C(m-1,t)·m = C(m,t)·(m-t) > (1-ε)·C(m,t)·m`. -/
private theorem cor_9_1_3_strict_small_stabilizers {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)} {t : ℕ} {ε : ℝ} (ht : 2 ≤ t)
    (hmt : 2 * t + 1 ≤ Nat.card Γ) (hm : Nat.card Γ ≤ 8) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    ∃ Δ : Set Γ, (1 - ε) * ((Nat.card Γ).choose t : ℝ) < ((Δ.ncard).choose t : ℝ) ∧
      pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard ∧
      G ≤ setwiseStabilizer ⊤ Δ := by
  set m := Nat.card Γ with hmdef
  have hmpos : 0 < m := by omega
  have hchoose_pos : 0 < m.choose t := Nat.choose_pos (by omega)
  have hcp : (0 : ℝ) < (m.choose t : ℝ) := by exact_mod_cast hchoose_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  rcases small_index_subgroup_perm ht hmt hm hε hε3 hindex with ⟨hlt, halt⟩ | ⟨hge, a, ha, hset⟩
  · -- `A_m ≤ G`: the whole vertex set works
    refine ⟨Set.univ, ?_, ?_, ?_, fun g _ => ⟨Subgroup.mem_top g, Set.image_univ_of_surjective g.surjective⟩⟩
    · rw [Set.ncard_univ, ← hmdef]
      nlinarith
    · rw [Set.compl_univ, pointwiseStabilizer_empty]; exact halt
    · rw [Set.ncard_univ]; exact hmt
  · -- `|S_m : G| ≥ m`: the hypothesis forces `ε > t/m`
    have hεgt : (t : ℝ) / (m : ℝ) < ε := by
      by_contra hcon
      push Not at hcon
      have h := cost_le_of_le_div (m := m) (t := t) (by omega) (by omega) hε hcon
      have hmle : (m : ℝ) ≤ (G.index : ℝ) := by exact_mod_cast hge
      linarith
    have htmR : (t : ℝ) < ε * (m : ℝ) := by
      rw [div_lt_iff₀ hmR] at hεgt; linarith
    have h3t : 3 * t < m := by
      have h : (3 : ℝ) * (t : ℝ) < (m : ℝ) := by nlinarith
      exact_mod_cast h
    have hcard : (({a}ᶜ : Set Γ)).ncard = m - 1 := by
      have h := ncard_add_ncard_compl ({a} : Set Γ)
      rw [Set.ncard_singleton] at h
      omega
    refine ⟨({a}ᶜ : Set Γ), ?_, ?_, ?_, fun g hg =>
      ⟨Subgroup.mem_top g, isInvariant_compl_of_le_setwiseStabilizer hset g hg⟩⟩
    · rw [hcard]
      have hid : (m - 1).choose t * m = m.choose t * (m - t) := by
        have h := Nat.choose_mul_succ_eq (m - 1) t
        rw [show m - 1 + 1 = m from by omega] at h
        exact h
      have hcast : ((m - t : ℕ) : ℝ) = (m : ℝ) - (t : ℝ) := by
        have : t ≤ m := by omega
        push_cast [this]; ring
      have hidR : (((m - 1).choose t : ℕ) : ℝ) * (m : ℝ)
          = (m.choose t : ℝ) * ((m : ℝ) - (t : ℝ)) := by
        rw [← hcast]; exact_mod_cast hid
      refine lt_of_mul_lt_mul_right ?_ hmR.le
      calc (1 - ε) * (m.choose t : ℝ) * (m : ℝ)
          = (m.choose t : ℝ) * ((m : ℝ) - ε * (m : ℝ)) := by ring
        _ < (m.choose t : ℝ) * ((m : ℝ) - (t : ℝ)) := by nlinarith
        _ = (((m - 1).choose t : ℕ) : ℝ) * (m : ℝ) := hidR.symm
    · rw [compl_compl]; exact ha
    · rw [hcard]; omega

/-- Corollary 9.1.3, §9.1, for `m ≤ 8`, with strict relative size and the primitive
induced action of `G`. The small-index proof excludes all exceptional cases and
retains the upper stabilizer bound; see the small-degree entry in the corrected paper. -/
theorem cor_9_1_3_strict_small {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    {G : Subgroup (Equiv.Perm Γ)} {t : ℕ} {ε : ℝ} (ht : 2 ≤ t)
    (hmt : 2 * t + 1 ≤ Nat.card Γ) (hm : Nat.card Γ ≤ 8) (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    ∃ Δ : Set Γ, (1 - ε) * ((Nat.card Γ).choose t : ℝ) < ((Δ.ncard).choose t : ℝ) ∧
      pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard ∧
      G ≤ setwiseStabilizer ⊤ Δ ∧
      ∃ hΔ : IsInvariant G Δ,
        IsInvariant (inducedOnTSets G t) {S : binom Γ t | ∀ x ∈ S.val, x ∈ Δ} ∧
        IsPrimitive (inducedOnTSets (restrictTo G Δ hΔ) t) := by
  obtain ⟨Δ, hsize, hstab, hk, hset⟩ :=
    cor_9_1_3_strict_small_stabilizers ht hmt hm hε hε3 hindex
  have hΔ : IsInvariant G Δ := fun g hg => (hset hg).2
  exact ⟨Δ, hsize, hstab, hk, hset, hΔ, isInvariant_binom_subset hΔ t,
    cor_9_1_3_isPrimitive hΔ hstab (by omega) hk⟩

/-- Corollary 9.1.3, §9.1.  *"Let `G ≤ Aut(J(m,t))` and `0 < ε ≤ 1/3`.  If `m!/|G| < (t/ε)^{εm/t}`
then `G` acts as a primitive group on a subset of relative size `≥ (1 - ε)`."*
(Version 2.5, lines 3953–3966.)

This is the paper's statement, with no hypothesis on `m`.  The proof splits on `m`:
for `m ≥ 9` it is `Babai.cor_9_1_3_strict` (the paper's route through Lemma 9.1.2, with
the repairs recorded there), and for `m ≤ 8` it is `Babai.cor_9_1_3_strict_small`.
Both give the sharper form with `>` in place of `≥`. -/
theorem cor_9_1_3 {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {G : Subgroup (Equiv.Perm Γ)}
    {t : ℕ} {ε : ℝ} (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ Nat.card Γ)
    (hε : 0 < ε) (hε3 : ε ≤ 1 / 3)
    (hindex : (G.index : ℝ) < ((t : ℝ) / ε) ^ (ε * (Nat.card Γ : ℝ) / (t : ℝ))) :
    ∃ Δ : Set Γ, (1 - ε) * ((Nat.card Γ).choose t : ℝ) ≤ ((Δ.ncard).choose t : ℝ) ∧
      pointwiseStabilizer (alternatingGroup Γ) Δᶜ ≤ G ∧ 2 * t + 1 ≤ Δ.ncard ∧
      G ≤ setwiseStabilizer ⊤ Δ ∧
      ∃ hΔ : IsInvariant G Δ,
        IsInvariant (inducedOnTSets G t) {S : binom Γ t | ∀ x ∈ S.val, x ∈ Δ} ∧
        IsPrimitive (inducedOnTSets (restrictTo G Δ hΔ) t) := by
  rcases le_or_gt 9 (Nat.card Γ) with hm | hm
  · obtain ⟨Δ, hsize, hrest⟩ := cor_9_1_3_strict ht hmt hm hε hε3 hindex
    exact ⟨Δ, hsize.le, hrest⟩
  · obtain ⟨Δ, hsize, hrest⟩ := cor_9_1_3_strict_small ht hmt (by omega) hε hε3 hindex
    exact ⟨Δ, hsize.le, hrest⟩

/-! ### Proposition 9.1.1 -/

/-- Proposition 9.1.1 for `m ≥ 9`.  *"Let `0 < ε ≤ 1/3`.  The multiplicative cost of a
(relative) canonical `(1-ε)`-partition of the Johnson scheme `J(m,t)` is `≥ (t/ε)^{εm/t}`."*
(Version 2.5, lines 3934–3936.)  *"Proof.  This is an immediate consequence of
Corollary 9.1.3 below."*

This is the proposition as the paper proves it: through Lemma 9.1.2, which carries the
hypothesis `m ≥ 9` of the Jordan–Liebeck theorem.  The
remaining range is `Babai.prop_9_1_1_small`, and the two are combined, with the paper's
statement, in `Babai.prop_9_1_1`. -/
theorem prop_9_1_1_of_nine_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ε : ℝ} (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) (m t : ℕ) (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m) (hm9 : 9 ≤ m)
    (cost : Pt (JohnsonSchemes Ω) → ℕ)
    (hfind : FindsAtMultCost (JohnsonSchemes Ω) (ColoredPartitions Ω ℕ) cost
      (fun X P => P.car = X.car ∧ letI : Fintype ↥P.car := Fintype.ofFinite _;
        P.obj.IsAlphaPartition (1 - ε)))
    (X : Pt (JohnsonSchemes Ω)) (φ : ↥X.car ≃ binom (Fin m) t)
    (hφ : ∀ x y, X.obj.val x y = ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (cost X : ℝ) := by
  have hcard : Nat.card (Fin m) = m := by simp
  refine prop_9_1_1_of_cor hε hε3 m t ht hmt cost hfind X φ hφ ?_
  intro G hG
  obtain ⟨Δ, hsize, hstab, hk, -⟩ := cor_9_1_3_strict (Γ := Fin m) (G := G) (t := t)
    (ε := ε) ht (by rw [hcard]; exact hmt) (by rw [hcard]; exact hm9)
    hε hε3 (by rw [hcard]; exact hG)
  rw [hcard] at hsize
  exact ⟨Δ, hsize, hstab, hk⟩

/-- Proposition 9.1.1 for `m ≤ 8`, the range that the paper's route through Lemma 9.1.2
does not cover.  The proof is the same as for `Babai.prop_9_1_1_of_nine_le`; only the
corollary it uses is different (`Babai.cor_9_1_3_strict_small`). -/
theorem prop_9_1_1_small {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ε : ℝ} (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) (m t : ℕ) (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m) (hm8 : m ≤ 8)
    (cost : Pt (JohnsonSchemes Ω) → ℕ)
    (hfind : FindsAtMultCost (JohnsonSchemes Ω) (ColoredPartitions Ω ℕ) cost
      (fun X P => P.car = X.car ∧ letI : Fintype ↥P.car := Fintype.ofFinite _;
        P.obj.IsAlphaPartition (1 - ε)))
    (X : Pt (JohnsonSchemes Ω)) (φ : ↥X.car ≃ binom (Fin m) t)
    (hφ : ∀ x y, X.obj.val x y = ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (cost X : ℝ) := by
  have hcard : Nat.card (Fin m) = m := by simp
  refine prop_9_1_1_of_cor hε hε3 m t ht hmt cost hfind X φ hφ ?_
  intro G hG
  obtain ⟨Δ, hsize, hstab, hk, -⟩ := cor_9_1_3_strict_small (Γ := Fin m) (G := G) (t := t)
    (ε := ε) ht (by rw [hcard]; exact hmt) (by rw [hcard]; exact hm8)
    hε hε3 (by rw [hcard]; exact hG)
  rw [hcard] at hsize
  exact ⟨Δ, hsize, hstab, hk⟩

/-- Proposition 9.1.1.  *"Let `0 < ε ≤ 1/3`.  The multiplicative cost of a (relative)
canonical `(1-ε)`-partition of the Johnson scheme `J(m,t)` is `≥ (t/ε)^{εm/t}`."*
(Version 2.5, lines 3934–3936.)  *"Proof.  This is an immediate consequence of
Corollary 9.1.3 below."*

For any cost function and any canonical partition reduction with that cost bound,
the conclusion bounds `cost X` at each input `X` of parameters `(m,t)`. The bijection
`φ` and its coloring equation identify that input with `J(m,t)`. By Prop. 6.0.4,
`Aut(X,X')` has index at most `cost X` in `Aut(X)`. The strict form of Cor. 9.1.3
then forces a block larger than `(1-ε)|X|` whenever `cost X` is below the bound.

The passage from Cor. 9.1.3 to this statement is `Babai.prop_9_1_1_of_cor`
(`Workspace/SplitOrJohnson/ResilienceTransport.lean`), and the corollary is applied in its
strict form (`Babai.cor_9_1_3_strict`; the corrected paper).  The paper's proof of
Cor. 9.1.3 needs `m ≥ 9`, so the range `m ≤ 8` is done
separately, in `Babai.prop_9_1_1_small` (the small-degree repair, entry 92). These
repairs give the non-strict cost lower bound printed in the paper. -/
theorem prop_9_1_1 {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ε : ℝ} (hε : 0 < ε)
    (hε3 : ε ≤ 1 / 3) (m t : ℕ) (ht : 2 ≤ t) (hmt : 2 * t + 1 ≤ m)
    (cost : Pt (JohnsonSchemes Ω) → ℕ)
    (hfind : FindsAtMultCost (JohnsonSchemes Ω) (ColoredPartitions Ω ℕ) cost
      (fun X P => P.car = X.car ∧ letI : Fintype ↥P.car := Fintype.ofFinite _;
        P.obj.IsAlphaPartition (1 - ε)))
    (X : Pt (JohnsonSchemes Ω)) (φ : ↥X.car ≃ binom (Fin m) t)
    (hφ : ∀ x y, X.obj.val x y = ((φ x : Finset (Fin m)) \ (φ y : Finset (Fin m))).card) :
    ((t : ℝ) / ε) ^ (ε * (m : ℝ) / (t : ℝ)) ≤ (cost X : ℝ) := by
  rcases le_or_gt 9 m with h | h
  · exact prop_9_1_1_of_nine_le hε hε3 m t ht hmt h cost hfind X φ hφ
  · exact prop_9_1_1_small hε hε3 m t ht hmt (by omega) cost hfind X φ hφ

/-! ### Remark 9.1.4 -/

/-- Remark 9.1.4.  *"This result means that for fixed `t` (e.g., `t = 2`, the most severe
bottleneck case for decades), the multiplicative cost of obtaining a constant-factor
reduction in the domain size `n = C(m,t)` is exponential in `m`; and `m > n^{1/t}`."*
(Version 2.5, lines 3994–3999.)

The quantitative content is the inequality `m > n^{1/t}` for `n = C(m,t)`, i.e.
`C(m,t) < m^t`.  (For `t = 1` the two sides are equal; §9.1 is about `t ≥ 2`, and the
Johnson schemes of Def. 3.2.9 have `t ≥ 2`.) -/
theorem remark_9_1_4 (m t : ℕ) (ht : 2 ≤ t) (hmt : t ≤ m) : m.choose t < m ^ t := by
  have hfac : t.factorial * m.choose t = m.descFactorial t :=
    (Nat.descFactorial_eq_factorial_mul_choose m t).symm
  have hdesc : m.descFactorial t ≤ m ^ t := Nat.descFactorial_le_pow m t
  have hfac2 : 2 ≤ t.factorial := by
    calc 2 = Nat.factorial 2 := rfl
      _ ≤ t.factorial := Nat.factorial_le ht
  have hpos : 0 < m ^ t := Nat.pow_pos (show 0 < m by omega)
  have hle : 2 * m.choose t ≤ m ^ t := by
    calc 2 * m.choose t ≤ t.factorial * m.choose t := Nat.mul_le_mul_right _ hfac2
      _ = m.descFactorial t := hfac
      _ ≤ m ^ t := hdesc
  omega

end Babai
