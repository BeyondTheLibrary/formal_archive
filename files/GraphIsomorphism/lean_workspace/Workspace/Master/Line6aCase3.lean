/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 6, 6a and 7a at outcome (3) of Theorem 13.2.1.
-/
import Workspace.Master.Case3Versions
import Workspace.Master.Line567a

/-!
# Lines 6a and 7a at outcome (3): Procedure Align on the structure of `D(x)`

> 6.  if AggregateCertificates returns canonically embedded `k`-ary relational structure on
>     `Γ` with relative symmetry defect `≥ 1/2` then
> 6a.   apply Extended Design Lemma (Theorem 9.2.3); `X ←` canonical structure on `Γ`
> 7a. apply Procedure Align to `X` (Sec. 14.1)

`Babai.exists_canonicalVersions_case3` (`Workspace/Master/Case3Versions.lean`) has the
versions of line 6a at outcome (3), already read on all of `Γ`.  What this file adds is line
7a: the versions are handed to Procedure Align, which is
`Babai.nonempty_alignData_of_versions`, exactly as `Babai.nonempty_line7Core` does at
outcome (1).

Two things are different from outcome (1).

* The multiplicative cost is not `1`: Theorem 9.2.3 returns `q(m)m^{O(t)}` versions, so the
  number of calls is `q(m)m^{O(t)}·(n+1)·alignDominantRoundCost(n)`, the shape of
  `Babai.line4cdCost`.
* The threshold `α` of the Align core is not one number.  A version that is a colored
  partition of `D` extended by `Γ ∖ D` is a colored `3/4`-partition of `Γ`, while a version
  that is a Johnson scheme inside `D` covers only `(4/5)·(3/4) = 3/5` of `Γ`.  The Align core
  takes `α` as a parameter and asks only `1/2 < α`, `0 ≤ α` and `5α ≤ 4`, which both values
  meet, so the branch picks the `α` the chosen version comes with
  (`Babai.isSplitOutcome_extendOutcome`).

The label size `tlab` comes from Theorem 10.5.1 as at line 7
(`Babai.tPoint_eq_of_transitive`, `Babai.one_le_tPoint_of_transitive`,
`Babai.four_mul_tPoint_lt`), and the test set size `ts` of Sec. 13.1 is a parameter.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise

section Line6aCase3Core

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 6a and 7a on the window, at outcome (3) of Theorem 13.2.1**: the canonical
`t`-ary structure on `D(x)`, put through the Extended Design Lemma and then through
Procedure Align.

The hypotheses are those of `Babai.claim_13_2_1_3_onOrbits` — the local certificates
setting, `max{8, 2 + log₂ n} < ts < m/10`, and `4m < 5|D|` for both inputs — together with
the uniform form of Theorem 9.2.3 (`Babai.Theorem923Uniform`) and the conditions of
Procedure Align.

The number of calls is `q(m)m^{ct}·(n+1)·alignDominantRoundCost(n)`, the same shape as at
lines 4c–4d (`Babai.line4cdCost`), because line 6a is the same theorem as line 4c. -/
theorem nonempty_line6aCase3Core {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W)
    {x y : W → A} (ts : ℕ) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ m)
    (hx : 4 * m < 5 * (fixedGamma ϕ x ts).ncard)
    (hy : 4 * m < 5 * (fixedGamma ϕ y ts).ncard)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Nonempty (Line4cdData W A G x y m
      (qMax q m * m ^ (c * ts) * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W))) := by
  classical
  haveI : Nonempty W := hG.nonempty
  obtain ⟨u₀⟩ := ‹Nonempty W›
  set tlab : ℕ := tPoint ϕ u₀ with htlab
  have htl : ∀ u : W, tPoint ϕ u = tlab := fun u =>
    tPoint_eq_of_transitive hG hgiant hvl u₀ u
  have ht1 : 1 ≤ tlab := one_le_tPoint_of_transitive hG hgiant hvl u₀
  have h4t : 4 * tlab < m := four_mul_tPoint_lt hgiant hvl u₀
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  obtain ⟨Vers, hcanV, hne, hfin, hcost, hgood⟩ :=
    exists_canonicalVersions_case3 hK ϕ ts x y hset ht htm hx hy hu
  obtain ⟨X', hX'⟩ := hne x (mem_strOrbitPair_left G x y)
  obtain ⟨β, hβ12, hβ0, hβ45, hβZ⟩ := hgood x (mem_strOrbitPair_left G x y) X' hX'
  exact nonempty_alignData_of_versions hG hgiant hvl htl ht1 h4t hm hmn hK
    hcanV (hfin y) (V := qMax q m * m ^ (c * ts)) (hcost y) hX' hβ12 hβ0 hβ45 hβZ

end Line6aCase3Core

end Babai
