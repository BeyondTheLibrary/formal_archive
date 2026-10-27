/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, lines 5, 6, 6a and 7a: the branch taken when AggregateCertificates returns a
structure — outcomes (2b) and (3) of Theorem 13.2.1.
-/
import Workspace.Master.CostMono
import Workspace.Master.Line6aCase3
import Workspace.Master.Case2bVersions

/-!
# Lines 5, 6, 6a and 7a: the branch of outcomes (2b) and (3)

> 5. else (: `G` imprimitive :) apply AggregateCertificates (Theorem 13.2.1)
> 6. if AggregateCertificates returns canonically embedded `k`-ary relational structure on
>    `Γ` with relative symmetry defect `≥ 1/2` then
> 6a.  apply Extended Design Lemma (Theorem 9.2.3); `X ←` canonical structure on `Γ`
> 7a. apply Procedure Align to `X` (Sec. 14.1)

The test of line 6 is `Babai.aggregatesToStructure` (`Workspace/Master/Line567a.lean`):
*"the case distinction of Theorem 13.2.1 lands in (2b) or (3)"*, that is, neither case (1)
nor case (2a).  Which of the two it is, is the test `Babai.Case2Instance`:

* case (2) and not (2a) is case (2b) — the binary structure on `C' = C ∖ S`;
* not case (2) is case (3) — the `t`-ary structure on the set `D` of fixed points of `F^Γ`,
  with `4m < 5|D|` (`Babai.theorem_13_2_1_cases`).

Both go through the same two lines afterwards, 6a and 7a, so both produce a
`Babai.Line57Data` on the window and the branch is their case split, read on `Ω` by
`Babai.liftWindow` exactly as `Babai.line567aFun` reads outcome (1).

## The second input string

`Babai.nonempty_line6aCase3Core` asks `4m < 5|D(x)|` **and** `4m < 5|D(y)|`: the Claim of
case (3) builds one structure for the pair.  Line 6's test looks at `x` alone.  The gap is
closed by canonicity and not by an extra hypothesis: `|D(z)|` is constant on a `G`-orbit of
strings (`Babai.ncard_fixedGamma_of_mem_strOrbit`), so if `|D(y)| ≠ |D(x)|` then no `τ ∈ G`
carries `x` to `y`, `Iso_G(x,y)` is empty, and the branch returns `∅`
(`Babai.strIso_eq_empty_of_ncard_fixedGamma_ne`, `Babai.Line57Data.rejectDefect`).
Outcome (2b) has the same gap and the same repair, with the case test of Theorem 13.2.1 in
place of `|D(z)|` (`Babai.case2b_test_strAct`, `Babai.Line57Data.rejectCase`).  Both reject
exits carry the test they rest on, so neither is available where the test fails.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### The reject exits of lines 5–7

Both exits answer `∅` and make no call.  Each is a constructor of `Babai.Line57Shape` that
carries the test justifying the answer — a test on the second string alone, against the
first — so neither is available where its test fails.  `Babai.Line57Data.ofDoneEmpty` is the
private helper that turns such a shape into the five facts; it is not exported, so `∅` at
cost `0` is reachable only through one of the two constructors. -/

section Reject

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

open scoped Classical in
/-- The five facts of `Babai.Line57Data` for a shape that answers `∅` without a call.  All
of them but correctness are vacuous; correctness is the hypothesis `h`. -/
private noncomputable def Line57Data.ofDoneEmpty {G : Subgroup (Equiv.Perm W)}
    {x y : W → A} {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} {ts : ℕ}
    (S : Line57Shape W A G x y ϕ ts) (h5 : 5 ≤ ts) (hinner : S.inner = .done ∅)
    (hhint : ∀ J, S.hint J = none)
    (h : strIso (G : Set (Equiv.Perm W)) x y = ∅) (par cost : ℕ) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  Line57Data.ofInner S h5
    (by rw [hinner, SIReduction.run_done, h])
    (by intro J hJ; rw [hinner, SIReduction.calls_done] at hJ; simp at hJ)
    (by intro J hJ; rw [hinner, SIReduction.calls_done] at hJ; simp at hJ)
    (by rw [hinner, SIReduction.calls_done]; simp)
    (by intro J d hd; rw [hhint J] at hd; exact absurd hd (by simp))
    (by intro J hJ; rw [hinner, SIReduction.calls_done] at hJ; simp at hJ)

end Reject

/-! ### A string with a different `|D|` is not `G`-isomorphic to the input -/

section IsoEmpty

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

/-- §13.2: `|D(z)|` is a canonical invariant of the string, so two strings with different
`|D|` are not `G`-isomorphic.

*Proof.*  A `τ ∈ Iso_G(x,y)` puts `y` in the `G`-orbit of `x`, and `|D|` is constant on a
`G`-orbit (`Babai.ncard_fixedGamma_of_mem_strOrbit`). -/
theorem strIso_eq_empty_of_ncard_fixedGamma_ne (ϕ : G →* Equiv.Perm Γ) (x y : Ω → Λ) (t : ℕ)
    (h : (fixedGamma ϕ y t).ncard ≠ (fixedGamma ϕ x t).ncard) :
    strIso (G : Set (Equiv.Perm Ω)) x y = ∅ := by
  ext τ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hτ, hxy⟩
  exact h (ncard_fixedGamma_of_mem_strOrbit ϕ x t ⟨⟨τ, hτ⟩, hxy.symm⟩)

end IsoEmpty

/-! ### The two reject exits, with their tests -/

section RejectExits

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]
  {G : Subgroup (Equiv.Perm W)} {x y : W → A} {m : ℕ}

/-- §15, lines 5–7, **the reject exit of outcome (3)**: the second string has a different
number of fixed points of `F(z)^Γ`, so `Iso_G(x,y) = ∅` and the round answers `∅` without a
call.  The constructor carries the computed test, so this exit is not available when
`|D(y)| = |D(x)|`. -/
noncomputable def Line57Data.rejectDefect (ϕ : G →* Equiv.Perm (Fin m)) (ts : ℕ)
    (h5 : 5 ≤ ts)
    (hne : (fixedGamma ϕ y ts).ncard ≠ (fixedGamma ϕ x ts).ncard) (par cost : ℕ) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  Line57Data.ofDoneEmpty (.rejectDefect hne) h5 rfl (fun _ => rfl)
    (strIso_eq_empty_of_ncard_fixedGamma_ne ϕ x y ts hne) par cost

/-- §15, lines 5–7, **the reject exit of outcome (2b)**: the case test of Theorem 13.2.1
holds at `x` and fails at the second string.  The test is canonical
(`Babai.case2b_test_strAct`), so a `τ ∈ Iso_G(x,y)` would carry it from `x` to `y`; there is
none, `Iso_G(x,y) = ∅`, and the round answers `∅` without a call.  The constructor carries
both halves of the computed test. -/
noncomputable def Line57Data.rejectCase (ϕ : G →* Equiv.Perm (Fin m)) (ts : ℕ)
    (h5 : 5 ≤ ts)
    (hx : Case2 (bigFGamma ϕ x ts) ∧ ¬ AggregateCase2a ϕ x ts)
    (hy : ¬ (Case2 (bigFGamma ϕ y ts) ∧ ¬ AggregateCase2a ϕ y ts)) (par cost : ℕ) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  Line57Data.ofDoneEmpty (.rejectCase hx hy) h5 rfl (fun _ => rfl)
    (by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro σ ⟨hσ, hxy⟩
      exact hy (hxy ▸ (case2b_test_strAct ϕ x ts ⟨σ, hσ⟩).2 hx))
    par cost

/-- §15, lines 5–7, **the reject exit of the local guide in outcome (3)** (the corrected paper,
entry 121): some ordered `t`-tuple of `D(y)` is `∼` to no ordered `t`-tuple of `D(x)`. The
class is an invariant that differs for the two inputs, so `Iso_G(x,y) = ∅`
(`Babai.strIso_eq_empty_of_guideClassMissing`), and the round answers `∅` without a call.
The constructor carries the class condition. -/
noncomputable def Line57Data.rejectGuide (ϕ : G →* Equiv.Perm (Fin m)) (ts : ℕ)
    (h5 : 5 ≤ ts) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ Nat.card (Fin m)) (hW : Nonempty W)
    (h : GuideClassMissing ϕ ts x y hset ht htm hW) (par cost : ℕ) :
    Line57Data W A G x y ϕ ts par (cost + aggregateRoundCost m ts (Fintype.card W)) :=
  Line57Data.ofDoneEmpty (.rejectGuide hset ht htm hW h) h5 rfl (fun _ => rfl)
    (strIso_eq_empty_of_guideClassMissing h) par cost

end RejectExits

/-! ### Outcome (3), with the hypothesis on the second string removed -/

section Case3

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 6a and 7a at outcome (3) of Theorem 13.2.1**, asked only about the first
input string.

`Babai.nonempty_line6aCase3Core` needs `4m < 5|D|` for both strings, because the Claim of
case (3) builds one canonical structure for the pair.  Line 6's test reads the first string
only.  If the second string has a different `|D|` then `Iso_G(x,y) = ∅`
(`Babai.strIso_eq_empty_of_ncard_fixedGamma_ne`) and the branch answers `∅` at once. -/
theorem nonempty_line6aCase3Core_of_left {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W)
    {x y : W → A} (ts : ℕ) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ m)
    (h5 : 5 ≤ ts) (hx : 4 * m < 5 * (fixedGamma ϕ x ts).ncard)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Nonempty (Line57Data W A G x y ϕ ts m
      (qMax q m * m ^ (c * ts) * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W)
        + aggregateRoundCost (Fintype.card W) ts (Fintype.card W))) := by
  have hbump : ∀ cost : ℕ, cost + aggregateRoundCost m ts (Fintype.card W)
      ≤ cost + aggregateRoundCost (Fintype.card W) ts (Fintype.card W) := fun _ =>
    Nat.add_le_add_left (aggregateRoundCost_mono_left hmn) _
  by_cases hy : 4 * m < 5 * (fixedGamma ϕ y ts).ncard
  · exact Nonempty.map (fun C => (Line4cdData.toLine57 ϕ ts h5 C).mono (hbump _))
      (nonempty_line6aCase3Core hG hgiant hvl hm hmn ts hset ht htm hx hy hu)
  · exact ⟨(Line57Data.rejectDefect ϕ ts h5 (by omega) m _).mono (hbump _)⟩

end Case3

/-! ### Outcome (2b)

What the paper does at line 2b is:

> let `d` be the degree of transitivity of `F^C` (: so `1 ≤ d ≤ 5` :)
> individualize the elements of a set `S ∈ C^{(d−1)}`
> (: so `F^C_{(S)}` is transitive but not doubly transitive on `C' := C ∖ S` :)
> let `X = (C'; R₁, …, R_r)` be the orbital configuration of `F^C_{(S)}` on `C'`
> (: Warning: the numbering of the `R_i` is not canonical; isomorphisms may permute the
> `R_i` :)
> individualize one of the `X_i` (`i ≥ 2`) (: multiplicative cost `r − 1 ≤ m − 1` :)
> return `X_i`, exit
> (: `X_i` has relative symmetry defect `≥ 1/2` by Cor. 2.4.12 :)

`Babai.case2bFamily` (`Workspace/Master/Case2bFamily.lean`) is the family itself, read on
`Γ`: the pairs `(C ∖ S, R)` over all individualizations `S` and all off-diagonal orbitals
`R` of `F^C_{(S)}`, with `Babai.case2bFamily_canonical` for the Warning — a `G`-shift of the
string carries the family onto the family, member by member up to a permutation of the
members.

`Babai.case2bFamily` (`Workspace/Master/Case2bFamily.lean`) is the family itself, read on
`Γ`, and the branch is built from it in three steps:

1. `Babai.case2bFamily_facts` (`Workspace/Master/Case2bVersions.lean`) — the family is
   non-empty, has at most `m^5` members, and every member `(C ∖ S, R)` has
   `|C ∖ S| ≥ (11/15)m` and relative symmetry defect `≥ 1/2`.  The defect is Cor. 2.4.12
   (`Babai.half_le_structDefect_binStruct_orbitalOn`,
   `Workspace/Master/Case2bDefect.lean`): the orbital of `F^C_{(S)}` through an off-diagonal
   pair is an irreflexive, biregular, nontrivial digraph — nontrivial because `F^C_{(S)}` is
   *not doubly transitive* on `C ∖ S`, which is a shorter route than the rank-`3` argument
   of `Babai.defect_extConstituent_ge_half`.  The size bound is `m^{d−1}·m = m^d ≤ m^5`, the
   paper's `m^{d−1}(m−1)` weakened by one factor: an individualization is the range of a
   `(d−1)`-tuple, and by transitivity of `F^C_{(S)}` every orbital is the orbital through
   `(a₀, b)` for one fixed `a₀`.
2. `Babai.binStruct` (`Workspace/Master/Case2bStruct.lean`) reads a member as a binary
   `Babai.RelStructure` with the *same* automorphism group
   (`Babai.aut_binStruct`), so the defect is the same number, and
   `Babai.case2bPt` (`Workspace/Master/Case2bInput.lean`) is the resulting point of
   `Babai.KAryInputs Γ 2 (3/4)`, which moves by `π` when the member does
   (`Babai.case2bStr_car`, `Babai.case2bStr_iso`).
3. `Babai.exists_canonicalVersions_family_on` (`Workspace/Master/FamilyVersions.lean`) is
   the family form of the canonical-versions interface, stated once and in general: a
   canonical family of objects gives canonical versions, at the product of the two
   multiplicative costs.  Its one real step is `Babai.versAt_eq_smul`, *"a permutation
   carries the versions of an object onto the versions of the moved object"*.

The group facts themselves are `Babai.case2b_facts_on`
(`Workspace/Master/Case2bDefect.lean`): `Babai.degtrans_restrict_le_five`,
`Babai.isTransitive_pointwiseStab_individualize` and
`Babai.not_isDoublyTransitive_pointwiseStab_individualize` read on points of `Γ` instead of
on the double subtype `↥(Sᶜ : Set ↥C)` that `Babai.indivGroup` lives on, along
`Babai.degtransOn_eq_degtrans`.

The size condition needs the general form of `Babai.isSplitOutcome_extendOutcome`:
`|C'| = |C| − (d − 1) ≥ |C| − 4 > 4m/5 − 4`, which is **not** above `4m/5` (take `m = 100`,
`|C| = 81`, `d = 5`, `|C'| = 77 < 80`), so the `4m < 5|C'|` form does not apply.  What does
apply is `Babai.isSplitOutcome_extendOutcome_of` with `βJ = 11/20` and `βP = 3/4`: for
`m ≥ 217`, `15|C'| ≥ 11m`, so a Johnson scheme inside `C'` has at least `(3/4)|C'| ≥
(11/20)m` vertices, and `ρ ≤ max((3/4)|C'|, m − |C'|) ≤ (3/4)m.`
-/

section Case2b

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 6a and 7a at outcome (2b) of Theorem 13.2.1**: the binary structure `X_i`
on `C' = C ∖ S`, put through the Extended Design Lemma and then through Procedure Align.

The hypotheses are the setting of Theorem 13.2.1 together with its case distinction landing
in (2b): case (2) holds for `F(x)^Γ` and case (2a) does not.  The multiplicative cost is
`m^{d−1}(m−1) ≤ m^5` (`Babai.case2b_cost_le`) for the individualization, times the
`q(m)m^{O(t)}` of Theorem 9.2.3, times the cost of Procedure Align.

The proof is the one lines 6a and 7a prescribe: `Babai.exists_canonicalVersions_case2b` is
the Extended Design Lemma applied to every member of `Babai.case2bFamily`, read on all of
`Γ` by `Babai.extendOutcome`, and `Babai.nonempty_alignCore_of_versions` is Procedure Align
on the resulting versions.  The group facts it rests on are `Babai.case2b_facts_on`. -/
theorem nonempty_line6aCase2bCore {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W)
    {x y : W → A} (ts : ℕ) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ m)
    (h5 : 5 ≤ ts) (h2 : Case2 (bigFGamma ϕ x ts)) (h2a : ¬ AggregateCase2a ϕ x ts)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Nonempty (Line57Data W A G x y ϕ ts m
      (m ^ 5 * (qMax q m * m ^ (c * ts)) * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W)
        + aggregateRoundCost (Fintype.card W) ts (Fintype.card W))) := by
  classical
  have hbump : ∀ cost : ℕ, cost + aggregateRoundCost m ts (Fintype.card W)
      ≤ cost + aggregateRoundCost (Fintype.card W) ts (Fintype.card W) := fun _ =>
    Nat.add_le_add_left (aggregateRoundCost_mono_left hmn) _
  by_cases hy : Case2 (bigFGamma ϕ y ts) ∧ ¬ AggregateCase2a ϕ y ts
  swap
  · -- A failed case test on `y` rules out an isomorphism by canonicity.
    exact ⟨(Line57Data.rejectCase ϕ ts h5 ⟨h2, h2a⟩ hy m _).mono (hbump _)⟩
  haveI : Nonempty W := hG.nonempty
  obtain ⟨u₀⟩ := ‹Nonempty W›
  set tlab : ℕ := tPoint ϕ u₀ with htlab
  have htl : ∀ u : W, tPoint ϕ u = tlab := fun u =>
    tPoint_eq_of_transitive hG hgiant hvl u₀ u
  have ht1 : 1 ≤ tlab := one_le_tPoint_of_transitive hG hgiant hvl u₀
  have h4t : 4 * tlab < m := four_mul_tPoint_lt hgiant hvl u₀
  -- `2 ≤ ts` is what makes the member cost `q(|C'|)·|C'|^{2c}` fit under `m^{c·ts}`;
  -- it comes from `max{8, 2 + log₂ n} < ts` (`Babai.LargeK.eight_lt`).
  have hts : 2 ≤ ts := by have := ht.eight_lt; omega
  obtain ⟨inst, hK⟩ := exists_isCatAction_splitOutcomes (Γ := Fin m)
  letI := inst
  obtain ⟨Vers, hcanV, hne, hfin, hcost, hgood, _⟩ :=
    exists_canonicalVersions_case2b hK ϕ ts hm hts x h2 h2a hu
  -- Both families are nonempty. Align compares their versions.
  have _hyne : (Vers y).Nonempty := hne y hy
  obtain ⟨X', hX'⟩ := hne x ⟨h2, h2a⟩
  obtain ⟨β, hβ12, hβ0, hβ45, hβZ⟩ := hgood x ⟨h2, h2a⟩ X' hX'
  exact Nonempty.map (fun C => (Line4cdData.toLine57 ϕ ts h5 C).mono (hbump _))
    (nonempty_alignData_of_versions hG hgiant hvl htl ht1 h4t hm hmn hK
      hcanV (hfin y) (V := m ^ 5 * (qMax q m * m ^ (c * ts))) (hcost y) hX' hβ12 hβ0 hβ45
      hβZ)

end Case2b

/-! ### The two outcomes on the window, under one cost -/

section Line6aCore

open scoped Classical

variable {W : Type u} {A : Type v} [Fintype W] [DecidableEq W]

/-- §15, **lines 6a and 7a**: the branch of line 6, at either of the two outcomes the test
of line 6 accepts.  Case (2) and not (2a) is outcome (2b); not case (2) is outcome (3),
because the three cases of Theorem 13.2.1 are exhaustive
(`Babai.theorem_13_2_1_cases`). -/
theorem nonempty_line6aCore {G : Subgroup (Equiv.Perm W)} (hG : IsTransitive G)
    {m : ℕ} {ϕ : G →* Equiv.Perm (Fin m)} (hgiant : IsGiantRep ϕ)
    (hvl : VeryLargeK m (maxOrbitLength G)) (hm : 217 ≤ m) (hmn : m ≤ Fintype.card W)
    {x y : W → A} (ts : ℕ) (hset : LocalCertSetting G ϕ) (ht : LargeK ts (Nat.card W))
    (htm : 10 * ts ≤ m) (h5 : 5 ≤ ts) (hagg : AggregatesToStructureOn ϕ x ts)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Nonempty (Line57Data W A G x y ϕ ts m
      (m ^ 5 * (qMax q m * m ^ (c * ts)) * (Fintype.card W + 1) *
        AlignDominantRoundData.alignDominantRoundCost (Fintype.card W)
        + aggregateRoundCost (Fintype.card W) ts (Fintype.card W))) := by
  classical
  have hcardFin : Fintype.card (Fin m) = m := Fintype.card_fin m
  by_cases h2 : Case2 (bigFGamma ϕ x ts)
  · exact nonempty_line6aCase2bCore hG hgiant hvl hm hmn ts hset ht htm h5 h2 hagg.2 hu
  · have h3 : 4 * m < 5 * (fixedGamma ϕ x ts).ncard := by
      rcases theorem_13_2_1_cases ϕ x ts with h | h | h
      · exact absurd h hagg.1
      · exact absurd h h2
      · rw [hcardFin] at h
        exact h
    obtain ⟨C⟩ := nonempty_line6aCase3Core_of_left hG hgiant hvl hm hmn ts hset ht htm h5 h3 hu
    refine ⟨C.mono ?_⟩
    have h1 : 1 ≤ m ^ 5 := Nat.one_le_pow _ _ (by omega)
    have hmul : qMax q m * m ^ (c * ts) ≤ m ^ 5 * (qMax q m * m ^ (c * ts)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmul)) _

end Line6aCore

/-! ### Lines 5, 6, 6a and 7a as a branch of the round -/

section Branch

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, line 5: **the instance lands in case (2) of Theorem 13.2.1** — `F(x)^Γ` has an
orbit of more than `4m/5` points. -/
def Case2Instance (i : HintedInstance Ω A) : Prop :=
  ∃ hJ : IsJohnson i, Case2 (bigFGamma (johnsonData hJ).ϕ
    (restrictStr i.inst.Δ i.inst.x) (testSetSize i.inst.windowSize))

/-- §15, lines 5, 6, 6a and 7a: **the tests the branch is taken after** — lines 1, 2 and 4
have failed and line 6's test has succeeded. -/
def Line6aTest (i : HintedInstance Ω A) : Prop :=
  ((IsGroupInstance i.inst ∧ IsJohnson i) ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧
    aggregatesToStructure i

variable [Fintype A] [DecidableEq A]

/-- The number of instances lines 5, 6, 6a and 7a produce: the individualization of
case (2b) (`m^{d−1}(m−1) ≤ m^5`), the multiplicative cost `q(m)m^{O(t)}` of Theorem 9.2.3 at
line 6a, and the cost of Procedure Align at line 7a. -/
def line56a7aCost (q : ℕ → ℕ) (c : ℕ) (n : ℕ) : ℕ :=
  n ^ 5 * (qMax q n * n ^ (c * testSetSize n)) * (n + 1) *
    AlignDominantRoundData.alignDominantRoundCost n
    + aggregateAllowance n

/-- §15, lines 6a and 7a: **the type of one round on the window**, at an instance that
lands in outcome (2b) or outcome (3) of Theorem 13.2.1. -/
abbrev Line6aDataAt (i : HintedInstance Ω A) (h : Line6aTest i) (q : ℕ → ℕ) (c : ℕ) :=
  Line57Data i.inst.Δ A
    (restrictTo (johnsonData h.1.1.2).K i.inst.Δ (johnsonData h.1.1.2).invariant)
    (restrictStr i.inst.Δ i.inst.x) (restrictStr i.inst.Δ i.inst.y)
    (johnsonData h.1.1.2).ϕ (testSetSize i.inst.windowSize)
    (johnsonData h.1.1.2).m
    ((johnsonData h.1.1.2).m ^ 5 *
        (qMax q (johnsonData h.1.1.2).m *
          (johnsonData h.1.1.2).m ^ (c * testSetSize i.inst.windowSize)) *
      (Fintype.card i.inst.Δ + 1) *
      AlignDominantRoundData.alignDominantRoundCost (Fintype.card i.inst.Δ)
      + aggregateRoundCost (Fintype.card i.inst.Δ) (testSetSize i.inst.windowSize)
        (Fintype.card i.inst.Δ))

/-- §15, **lines 5, 6, 6a and 7a: what the branch chooses** — the round on the window at
every instance line 6's test accepts.  What is chosen is data: either the data of one round
of Procedure Align (`Babai.AlignShape`), or one of the two reject exits with the test that
justifies it.  The reduction is a named function of it (`Babai.Line57Shape.red`). -/
def Line56a7aChoice (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] [Fintype A]
    [DecidableEq A] (q : ℕ → ℕ) (c : ℕ) :=
  ∀ (i : HintedInstance Ω A) (h : Line6aTest i), Line6aDataAt i h q c

/-- §15, lines 6a and 7a: **the round on the window at outcomes (2b) and (3)**, chosen
once. -/
noncomputable def line6aDataOf {i : HintedInstance Ω A} (h : Line6aTest i) {q : ℕ → ℕ}
    {c : ℕ} (hu : Theorem923Uniform q c) : Line6aDataAt i h q c := by
  classical
  set d := johnsonData h.1.1.2 with hd
  have hcard : Fintype.card i.inst.Δ = i.inst.windowSize := card_window d
  have hncard : Nat.card i.inst.Δ = i.inst.windowSize := by
    rw [SIInstance.windowSize, Nat.card_coe_set_eq]
  have h217 : 217 ≤ d.m := by
    rw [hd]
    have := le_param_of_line4c h.1.1.2 h.1.2
    rwa [param_eq h.1.1.2] at this
  have hell : ellOf i.inst.windowSize < d.m := by
    rw [hd]
    have := h.1.2
    rw [param_eq h.1.1.2] at this
    omega
  have h64 : 64 ≤ i.inst.windowSize := d.window_large
  have hmcard : Nat.card (Fin d.m) = d.m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Classical.choice (nonempty_line6aCore d.transitive d.giant
    (veryLargeK_of_hugeM d.transitive (hugeM_of_data h.1.1.2 h.1.2)) h217
    (by have := d.param_le; omega)
    (testSetSize i.inst.windowSize)
    (localCertSetting_of_line3 d.transitive d.giant (by rw [hncard]; omega)
      (by rw [hncard, hmcard]; exact hell))
    (by rw [hncard]; exact largeK_testSetSize (by omega))
    (le_of_lt (ten_mul_testSetSize_lt (by omega) hell))
    (five_le_testSetSize _) h.2.choose_spec hu)

/-- §15, lines 5, 6, 6a and 7a: **`Babai.Line56a7aChoice` is inhabited**
(`Babai.nonempty_line6aCore`).  This is the only place where `Classical.choice` enters
lines 5, 6, 6a and 7a. -/
noncomputable def line56a7aChoiceOf {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    Line56a7aChoice Ω A q c := fun _ h => line6aDataOf h hu

/-- §15, **lines 5, 6, 6a and 7a** as a branch of the round: the branch on the window, read
on `Ω` (`Babai.liftWindow`).  Outside the tests of line 6 the branch is never taken, and the
leaf `.done I.answer` stands there. -/
noncomputable def line56a7aFunCoset {q : ℕ → ℕ} {c : ℕ} (C : Line56a7aChoice Ω A q c)
    (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if h : Line6aTest i then
    liftWindow (johnsonData h.1.1.2).K i.inst.Δ (johnsonData h.1.1.2).invariant i.inst.x
      (C i h).toCosetCore.red
  else cosetLeaf i.inst i.inst.answer

noncomputable def line56a7aFun {q : ℕ → ℕ} {c : ℕ} (C : Line56a7aChoice Ω A q c)
    (i : HintedInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  SIReduction.alignRed i.inst (line56a7aFunCoset C i)

/-- §15, lines 6a–7a, **line 11 of Procedure Align**: the hint the branch hands to each of
its calls, read on `Ω` (`Babai.cosetWindowHintLift`). -/
noncomputable def line56a7aLift {q : ℕ → ℕ} {c : ℕ} (C : Line56a7aChoice Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : HintedInstance Ω A :=
  if h : Line6aTest i then
    ⟨J, cosetWindowHintLift (johnsonData h.1.1.2).invariant i.inst.x (C i h).shape.hint J⟩
  else ⟨J, none⟩

@[simp] theorem inst_line56a7aLift {q : ℕ → ℕ} {c : ℕ} (C : Line56a7aChoice Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : (line56a7aLift C i J).inst = J := by
  rw [line56a7aLift]
  split <;> rfl

end Branch

/-! ### The four facts of lines 5, 6, 6a and 7a -/

section Fields

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {q : ℕ → ℕ} {c : ℕ}

/-- §15, lines 5, 6, 6a and 7a, **correct**: the branch returns `Iso^Δ_K(x,y)`. -/
theorem line56a7a_run (C : Line56a7aChoice Ω A q c) (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : aggregatesToStructure i) : (line56a7aFun C i).run = i.inst.answer := by
  have h : Line6aTest i := ⟨⟨⟨hgrp, hJ⟩, hell⟩, ha⟩
  rw [line56a7aFun, line56a7aFunCoset, dif_pos h]
  exact run_alignLiftWindow_core (C i h).toCosetCore i.inst (johnsonData h.1.1.2).isGroup rfl rfl
    rfl

/-- §15, lines 5, 6, 6a and 7a: **every call is a group instance**. -/
theorem line56a7a_group (C : Line56a7aChoice Ω A q c) (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : aggregatesToStructure i) :
    ∀ J ∈ (line56a7aFun C i).calls, IsGroupInstance J := by
  have h : Line6aTest i := ⟨⟨⟨hgrp, hJ⟩, hell⟩, ha⟩
  rw [line56a7aFun, line56a7aFunCoset, dif_pos h]
  exact calls_alignLiftWindow_core_group (C i h).toCosetCore i.inst i.inst.x

/-- §15, lines 5, 6, 6a and 7a, **the progress**: every call has a window of at most `4n/5`
points, or the same window and a Johnson parameter of at most `m/2` — Eq. (73). -/
theorem line56a7a_decreases (C : Line56a7aChoice Ω A q c) (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : aggregatesToStructure i) : ∀ J ∈ (line56a7aFun C i).calls,
    MakesProgress HintedInstance.win param i (line56a7aLift C i J) := by
  have h : Line6aTest i := ⟨⟨⟨hgrp, hJ⟩, hell⟩, ha⟩
  intro J hJmem
  rw [line56a7aFun, line56a7aFunCoset, dif_pos h] at hJmem
  have hcard : Fintype.card i.inst.Δ = i.inst.Δ.ncard := card_window (johnsonData hJ)
  have hwin : HintedInstance.win i = i.inst.Δ.ncard := rfl
  have hwinJ : HintedInstance.win (line56a7aLift C i J) = J.windowSize :=
    congrArg SIInstance.windowSize (inst_line56a7aLift C i J)
  have hpar : param i = (johnsonData hJ).m := param_eq hJ
  have h217 : 217 ≤ (johnsonData hJ).m := by
    have := le_param_of_line4c hJ hell
    rwa [param_eq hJ] at this
  have hd := decreases_alignLiftWindow_core (C i h).toCosetCore i.inst i.inst.x hcard J hJmem
  rw [show (C i h).toCosetCore.hint = (C i h).shape.hint from rfl] at hd
  have hliftJ : line56a7aLift C i J =
      ⟨J, cosetWindowHintLift (johnsonData h.1.1.2).invariant i.inst.x
        (C i h).shape.hint J⟩ := by rw [line56a7aLift, dif_pos h]
  rcases hd with hsmall | ⟨hle, hpar2⟩
  · exact Or.inl ⟨by rw [hwin]; exact (johnsonData hJ).one_le_windowSize,
      by rw [hwinJ, hwin]; exact hsmall⟩
  · refine Or.inr ⟨by rw [hwinJ, hwin]; exact hle, by omega, ?_⟩
    rw [hliftJ]
    omega

/-- §15, lines 5, 6, 6a and 7a, **the number of instances one round produces**. -/
theorem line56a7a_calls (C : Line56a7aChoice Ω A q c) (i : HintedInstance Ω A)
    (hgrp : IsGroupInstance i.inst) (hJ : IsJohnson i)
    (hell : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : aggregatesToStructure i) :
    ((line56a7aFun C i).calls).length ≤ line56a7aCost q c i.inst.windowSize := by
  have h : Line6aTest i := ⟨⟨⟨hgrp, hJ⟩, hell⟩, ha⟩
  rw [line56a7aFun, line56a7aFunCoset, dif_pos h]
  refine le_trans (calls_length_alignLiftWindow_core (C i h).toCosetCore i.inst i.inst.x) ?_
  set d := johnsonData h.1.1.2 with hddef
  have hcard : Fintype.card i.inst.Δ = i.inst.windowSize := card_window d
  have hmn : d.m ≤ i.inst.windowSize := d.param_le
  rw [line56a7aCost, hcard]
  refine Nat.add_le_add ?_ (aggregateRoundCost_le_aggregateAllowance _)
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ ?_))
  · exact Nat.pow_le_pow_left hmn 5
  · exact Nat.mul_le_mul (qMax_mono q hmn) (Nat.pow_le_pow_left hmn _)

/-- §15, lines 5, 6, 6a and 7a, **the regression of Finding 3**: when the tests of line 5
lead to outcome (2b) or (3), the branch makes at least as many calls as the two phases of
Procedure AggregateCertificates together, on the window.  Both reject exits are covered:
each reads `F(z)^Γ`, so each comes after the certificate runs. -/
theorem line56a7a_calls_ge_phases (C : Line56a7aChoice Ω A q c) (i : HintedInstance Ω A)
    (h : Line6aTest i) :
    (certPhaseStrong (johnsonData h.1.1.2).ϕ (restrictStr i.inst.Δ i.inst.x)
          (restrictStr i.inst.Δ i.inst.y) (C i h).enum
          (Λ := A)).calls.length
        + (comparePhaseStrong (johnsonData h.1.1.2).ϕ (restrictStr i.inst.Δ i.inst.x)
          (restrictStr i.inst.Δ i.inst.y) (C i h).enum
          (Λ := A)).calls.length
      ≤ ((line56a7aFun C i).calls).length := by
  rw [line56a7aFun, line56a7aFunCoset, dif_pos h,
    calls_length_alignRed, calls_liftWindow (johnsonData h.1.1.2).invariant i.inst.x _ (C i h).toCosetCore.calls_K,
    List.length_map]
  exact Line57Shape.calls_length_phases_le_red _ _

end Fields

end Babai
