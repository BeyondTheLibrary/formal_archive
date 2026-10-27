/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 10 (Alternating quotients of a permutation group): definitions and notation.
-/
import Workspace.AltQuotients.PrelimExtra
import Workspace.AltQuotients.NamedGroups
import Workspace.Prelim.Socle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic

/-!
# §10 Alternating quotients of a permutation group: definitions

Every definition and piece of notation of Section 10, in the paper's order.

## Numbering map

| Paper | Lean |
|---|---|
| §10.1 subdirect product | `Babai.IsSubdirectProduct` |
| §10.1 perfect group (Remark 10.1.2) | `Group.IsPerfect` (Mathlib) |
| §10.2 "`A_k` is involved in `H`" | `Babai.Involved` |
| Definition 10.2.1 socle | `Babai.IsMinimalNormal`, `Babai.socle` |
| Fact 10.2.2 "direct product of simple groups" | `Babai.IsInternalDirectProduct` |
| §10.2 `Pker(G)` (permutation kernel) | `Babai.Pker` |
| §10 `n₀(G)` | `Babai.maxOrbitLength` (in `PrelimExtra`) |
| §10 giant representation | `Babai.IsGiantRep` (Prelim) |
| Definition 10.3.4 affected | `Babai.Affected`, `Babai.unaffectedSet` |
| Notation 10.4.3 `T(H)`, Eq. (51) | `Babai.IsSandwichSet`, `Babai.sandwichSet` |
| Theorem 10.5.1 (a) `T(x)` | `Babai.Tpoint` |
| Theorem 10.5.1 (c) `t_Δ` | `Babai.tPoint` |
| Theorem 10.5.1 (e) standard blocks | `Babai.standardBlock`, `Babai.standardBlocks` |

## Conventions

Cardinalities are `Nat.card`, so that they need no instance argument inside existential
quantifiers.  The paper's `n = |Ω|`, `n₀ = n₀(G)`, `k` are `Nat.card Ω`,
`maxOrbitLength G`, `k`.

The paper's inequalities `|T| < n/2` and `r < n/2` are rendered as `2 * |T| < n` and
`2 * r < n`, which say the same thing over `ℕ` without truncated division.  Inequalities
with logarithms are kept over `ℝ` (`Real.logb 2`).
-/

universe u

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### §10.1 Subdirect products -/

/-- §10.1.  "Let `G ≤ K₁ × ⋯ × K_m` be a subdirect product": a subgroup of the direct
product that projects *onto* each factor.

Giving such a `G` is the same as giving a group `G` together with epimorphisms
`π i : G → K i` whose kernels intersect trivially (the intersection of the kernels is the
kernel of `G → ∏ K i`, which is injective exactly when `G` is a subgroup of the product).
The `Mi` of Lemma 10.1.1, "the kernel of the `G → Kᵢ` epimorphism", are `(π i).ker`. -/
structure IsSubdirectProduct {G : Type*} [Group G] {ι : Type*} {K : ι → Type*}
    [∀ i, Group (K i)] (π : ∀ i, G →* K i) : Prop where
  /-- `G` embeds into `∏ᵢ Kᵢ`, i.e. the kernels of the projections intersect trivially. -/
  faithful : ∀ g : G, (∀ i, π i g = 1) → g = 1
  /-- Each projection `G → Kᵢ` is onto (this is what "subdirect" means). -/
  surjective : ∀ i, Function.Surjective (π i)

/-! ### §10.2 Involvement, socle, permutation kernel -/

/-- §10.2 (proof of Lemma 10.2.5, Case 1), and §11.2.  "`A` is *involved* in `B`" is the
standard usage: `A` is isomorphic to a quotient of a subgroup of `B`, i.e. `A` is a
*section* of `B`.  The paper uses the word without defining it ("`A_k` is involved in
`GL(s, p)`", "`G/Pker G` cannot involve `A_k`").

Equivalently, and as stated here: some subgroup `H ≤ B` admits an epimorphism onto `A`
(take `H/ker` for the quotient, resp. the composite `H → H/K ≅ A`). -/
def Involved (A B : Type*) [Group A] [Group B] : Prop :=
  ∃ (H : Subgroup B) (f : H →* A), Function.Surjective f

/-! **Definition 10.2.1** (socle) is `Babai.IsMinimalNormal` and `Babai.socle`; since
§11.2 repeats the definition verbatim, it lives in `Workspace/Prelim/Socle.lean`. -/

/-- Fact 10.2.2, §10.2.  "`N` is a direct product of the subgroups `R i`", in the internal
sense: the `R i` are normal in `N`, independent, and generate `N`.  (For `N = Soc(G)` the
factors are in fact normal in `G`, but Fact 10.2.2 only claims a direct decomposition.) -/
structure IsInternalDirectProduct {G : Type*} [Group G] (N : Subgroup G) {ι : Type*}
    (R : ι → Subgroup G) : Prop where
  le : ∀ i, R i ≤ N
  normal : ∀ i, ∀ g ∈ N, ∀ x ∈ R i, g * x * g⁻¹ ∈ R i
  independent : iSupIndep R
  sup_eq : ⨆ i, R i = N

/-- §10.2 (proof of Lemma 10.2.5, Case 2), following [BaB].  The *permutation kernel*
`Pker(G)`: "the kernel of the induced permutation action `G → S_s` (permuting the copies
of `R` by conjugation by elements of `G`)".

Here `R : ι → Subgroup G` is the family of copies, and `Pker` is the subgroup of the
elements of `G` whose conjugation action fixes every copy setwise. -/
def Pker {G : Type*} [Group G] {ι : Type*} (R : ι → Subgroup G) : Subgroup G where
  carrier := {g | ∀ i, (R i).map (MulAut.conj g).toMonoidHom = R i}
  one_mem' := by
    intro i
    have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [h, Subgroup.map_id]
  mul_mem' := by
    intro a b ha hb i
    have h : (MulAut.conj (a * b)).toMonoidHom
        = (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
      ext x; simp [MulAut.conj, mul_assoc]
    rw [h, ← Subgroup.map_map, hb i, ha i]
  inv_mem' := by
    intro a ha i
    have h : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom
        = MonoidHom.id G := by
      ext x; simp [MulAut.conj, mul_assoc]
    calc (R i).map (MulAut.conj a⁻¹).toMonoidHom
        = ((R i).map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom := by
          rw [ha i]
      _ = (R i).map ((MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom) :=
          Subgroup.map_map _ _ _
      _ = R i := by rw [h, Subgroup.map_id]

/-! ### §10 The hypothesis on `k` -/

/-- §10, Lemmas 10.2.5, 10.3.1, 10.3.3 and Theorem 10.3.5: the hypothesis
`k > max{8, 2 + log₂ n}`. -/
def LargeK (k n : ℕ) : Prop := max 8 (2 + Real.logb 2 n) < (k : ℝ)

/-- §10.5, Theorem 10.5.1: the (stronger) hypothesis `k ≥ max{9, 2 log₂ n₀}`. -/
def VeryLargeK (k n : ℕ) : Prop := max 9 (2 * Real.logb 2 n) ≤ (k : ℝ)

theorem LargeK.eight_lt {k n : ℕ} (h : LargeK k n) : 8 < k := by
  have : (8 : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) h
  exact_mod_cast this

/-- `k > 2 + log₂ n` gives `n < 2 ^ (k - 2)`, the combinatorial form of the hypothesis. -/
theorem LargeK.lt_two_pow {k n : ℕ} (h : LargeK k n) : n < 2 ^ (k - 2) := by
  have hk8 : 8 < k := h.eight_lt
  have h2 : 2 + Real.logb 2 (n : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · positivity
  have hlog : Real.logb 2 (n : ℝ) < ((k - 2 : ℕ) : ℝ) := by
    have : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      have : (2 : ℕ) ≤ k := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have := (Real.logb_lt_iff_lt_rpow (by norm_num) hnpos).1 hlog
  have hrpow : (2 : ℝ) ^ ((k - 2 : ℕ) : ℝ) = ((2 ^ (k - 2) : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    push_cast
    ring
  rw [hrpow] at this
  exact_mod_cast this

/-- `LargeK` is monotone in `n`: the hypothesis for `n` gives the hypothesis for any
smaller `n'`.  Used whenever §10.3 passes from `G` to a subgroup or a restriction, whose
orbits are no longer than those of `G`. -/
theorem LargeK.mono {k n n' : ℕ} (h : LargeK k n) (hn : n' ≤ n) : LargeK k n' := by
  have h8 : (8 : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) h
  refine max_lt h8 ?_
  rcases Nat.eq_zero_or_pos n' with rfl | hpos
  · simp only [Nat.cast_zero, Real.logb_zero]
    linarith
  · have hle : Real.logb 2 (n' : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) (by exact_mod_cast hn)
    have := lt_of_le_of_lt (le_max_right (8 : ℝ) (2 + Real.logb 2 (n : ℝ))) h
    linarith

/-- The hypothesis of Theorem 10.5.1 implies the hypothesis of §10.3. -/
theorem VeryLargeK.largeK {k n : ℕ} (h : VeryLargeK k n) : LargeK k n := by
  have h9 : (9 : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) h
  have h2 : 2 * Real.logb 2 (n : ℝ) ≤ (k : ℝ) := le_trans (le_max_right _ _) h
  refine max_lt (by linarith) ?_
  rcases lt_trichotomy (Real.logb 2 (n : ℝ)) 7 with hL | hL | hL
  · linarith
  · rw [hL] at h2 ⊢; linarith
  · linarith

/-! ### §10.3 Affected points -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Definition 10.3.4** (Affected), §10.3.

> We say that the homomorphism `ϕ : G → S_k` is a *giant representation* if `G^ϕ ≥ A_k`.
> We say that `x ∈ Ω` is *affected by* `ϕ` if `G_x^ϕ ≱ A_k`.

The giant representation half is `Babai.IsGiantRep` (§2.2.1). -/
def Affected {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k))
    (x : Ω) : Prop :=
  ¬ alternatingGroup (Fin k) ≤ (stabilizer G x).map ϕ

/-- Theorem 10.3.5: "`D` is the set of elements of `Ω` not affected by `ϕ`". -/
def unaffectedSet {G : Subgroup (Equiv.Perm Ω)} {k : ℕ} (ϕ : G →* Equiv.Perm (Fin k)) :
    Set Ω :=
  {x | ¬ Affected ϕ x}

/-! ### §10.4 Notation 10.4.3: the set `T(H)` -/

/-- Eq. (51) of Notation 10.4.3, §10.4, as a predicate: `T` is *the* subset sandwiched by
`H`, i.e. `|T| < n/2` and `A(Ω)_(T) ≤ H ≤ S(Ω)_T`.

Theorem 10.4.2 says that under its hypotheses there is exactly one such `T`. -/
def IsSandwichSet (H : Subgroup (Equiv.Perm Ω)) (T : Set Ω) : Prop :=
  2 * T.ncard < Nat.card Ω ∧
    pointwiseStabilizer (alternatingGroup Ω) T ≤ H ∧
      H ≤ setwiseStabilizer ⊤ T

/-- "`G` preserves a partition of `Ω` into two blocks of size `n/2`": there is a set `B`
with `2|B| = n` such that every element of `H` maps `B` to `B` or to its complement.

Together with transitivity this is "`G` is imprimitive with two blocks of size `m`", case
(ii) of the cited theorems `[DiM, Thm. 5.2A]` and `[DiM, Thm. 5.2B]`
(`Babai.dixonMortimer_5_2A`, `Babai.dixonMortimer_5_2B`), hence case (ii) of Theorem
10.4.2 (`Babai.theorem_10_4_2`).  Note that `2 * B.ncard = Nat.card Ω` already forces `n`
to be even. -/
def PreservesHalvingPartition (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ B : Set Ω, 2 * B.ncard = Nat.card Ω ∧
    ∀ σ ∈ H, (σ : Equiv.Perm Ω) '' B = B ∨ (σ : Equiv.Perm Ω) '' B = Bᶜ

/-- **Notation 10.4.3**, §10.4.

> Under the assumptions of Theorem 10.4.2 we write `T(H)` for the unique subset
> `T ⊂ Ω` guaranteed by the Theorem.  So we have
> `A(Ω)_(T(H)) ≤ H ≤ S(Ω)_{T(H)}`.  (51)

Outside the assumptions of Theorem 10.4.2 the notation is undefined; we make the
definition total by returning `∅`, and `Babai.sandwichSet_spec` (Sec. 10.4) records that
under those assumptions it is the set of Eq. (51). -/
noncomputable def sandwichSet (H : Subgroup (Equiv.Perm Ω)) : Set Ω :=
  letI := Classical.dec (∃ T, IsSandwichSet H T)
  if h : ∃ T, IsSandwichSet H T then h.choose else ∅

theorem isSandwichSet_sandwichSet {H : Subgroup (Equiv.Perm Ω)}
    (h : ∃ T, IsSandwichSet H T) : IsSandwichSet H (sandwichSet H) := by
  have : sandwichSet H = h.choose := by
    rw [sandwichSet]
    exact dif_pos h
  rw [this]
  exact h.choose_spec

/-! ### §10.5 `T(x)`, `t_Δ`, and the standard blocks -/

variable {G : Subgroup (Equiv.Perm Ω)} {k : ℕ}

/-- Theorem 10.5.1 (a), §10.5.  `T(x) = T(G_x^ϕ)`, the unique subset of `[k]` with
`|T(x)| < k/4` and `(A_k)_(T(x)) ≤ G_x^ϕ ≤ (S_k)_{T(x)}` (Eq. (52)). -/
noncomputable def Tpoint (ϕ : G →* Equiv.Perm (Fin k)) (x : Ω) : Set (Fin k) :=
  sandwichSet ((stabilizer G x).map ϕ)

/-- Theorem 10.5.1 (c), §10.5.  `|T(x)|`; by item (c) this is constant on each orbit `Δ`,
where its value is the paper's `t_Δ`. -/
noncomputable def tPoint (ϕ : G →* Equiv.Perm (Fin k)) (x : Ω) : ℕ :=
  (Tpoint ϕ x).ncard

/-- Theorem 10.5.1 (e), §10.5.  The *standard block* of `x`: the class of `x` under the
equivalence relation `T(x) = T(y)` on the orbit of `x`. -/
noncomputable def standardBlock (ϕ : G →* Equiv.Perm (Fin k)) (x : Ω) : Set Ω :=
  {y | y ∈ orbit G x ∧ Tpoint ϕ y = Tpoint ϕ x}

/-- Theorem 10.5.1 (e), §10.5.  The set of standard blocks in the orbit `Δ`. -/
noncomputable def standardBlocks (ϕ : G →* Equiv.Perm (Fin k)) (Δ : Set Ω) :
    Set (Set Ω) :=
  {B | ∃ x ∈ Δ, B = standardBlock ϕ x}

end Babai
