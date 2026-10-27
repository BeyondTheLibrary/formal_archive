/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 6a, outcome (3) of Theorem 13.2.1: Theorem 9.2.3 applied to the canonical
`t`-ary structure on `D(x)`, as canonical versions of the outcome.
-/
import Workspace.Master.Case3
import Workspace.Master.Line4cd
import Workspace.Master.ExtendOutcome

/-!
# Line 6a, outcome (3): the canonical versions of the structure Theorem 9.2.3 finds

Outcome (3) of Theorem 13.2.1 is a canonical `t`-ary relational structure `𝔷(z)` on the set
`D(z)` of fixed points of `F(z)^Γ`, with `|D(z)| > 4m/5` and symmetry defect `> m/2`
(`Babai.claim_13_2_1_3_onOrbits`).  Line 6 of Sec. 15 hands it to line 6a, which is
Theorem 9.2.3, and line 6a hands the outcome to Procedure Align.

The three steps here are the same three as at line 4c (`Workspace/Master/DesignVersions.lean`),
with one difference: the object lives on `D(z) ⊆ Γ`, not on all of `Γ`.

1. **The object.**  `Babai.case3Input` is `𝔷(z)` as an admissible input of Theorem 9.2.3:
   `2 ≤ t` and `4t ≤ |D|` come from `10t ≤ m < (5/4)|D|`, and the relative symmetry defect
   is `1 − s/|D| > 3/4 > 1/4 = 1 − α` at `α = 3/4`, because the assignment has
   `|D| − t + 1 ≤ symDefect`, so `s ≤ t − 1`.
2. **Canonicity.**  `Babai.isCanonicalObjOn_case3Input`: `D(z^σ) = (ϕσ)(D(z))`
   (`Babai.canonical_fixedGamma`), and `ϕσ` carries `𝔷(z)` to `𝔷(z^σ)`, which is the
   canonicity clause of `Babai.IsCase3Output`.
3. **The versions, read on `Γ`.**  `Babai.exists_canonicalVersions_on` gives the versions on
   `D(z)`; `Babai.extendOutcome` reads each of them on all of `Γ`
   (`Workspace/Master/ExtendOutcome.lean`), which is the step the paper takes silently when
   Theorem 13.2.1 says *"on `Γ`"*.

`Babai.exists_canonicalVersions_case3` is the conclusion.  The admissible set of strings is
`Babai.strOrbitPair G x y`, the union of the `G`-orbits of the two input strings, which is
the set `Babai.claim_13_2_1_3_onOrbits` builds the assignment on and is `G`-invariant.
-/

universe u v

namespace Babai

open Equiv MulAction
open scoped Pointwise

section Case3Versions

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
  {G : Subgroup (Equiv.Perm Ω)}

/-! ### The admissible strings are a `G`-invariant set -/

theorem strAct_mem_strOrbit (x : Ω → A) {z : Ω → A} (σ : G) :
    strAct z (σ : Equiv.Perm Ω) ∈ strOrbit G x ↔ z ∈ strOrbit G x := by
  have hcoe : ∀ a b : G, ((a * b : G) : Equiv.Perm Ω)
      = ((a : G) : Equiv.Perm Ω) * ((b : G) : Equiv.Perm Ω) := fun _ _ => rfl
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨σ⁻¹ * τ, ?_⟩
    rw [hcoe, strAct_mul, ← hτ, ← strAct_mul]
    simp [strAct]
  · rintro ⟨τ, rfl⟩
    refine ⟨σ * τ, ?_⟩
    rw [hcoe, strAct_mul]

theorem strAct_mem_strOrbitPair (x y : Ω → A) {z : Ω → A} (σ : G) :
    strAct z (σ : Equiv.Perm Ω) ∈ strOrbitPair G x y ↔ z ∈ strOrbitPair G x y :=
  or_congr (strAct_mem_strOrbit x σ) (strAct_mem_strOrbit y σ)

/-! ### The assignment, made total -/

open scoped Classical in
/-- §15, line 6a: the string `z` itself when it lies in the set the assignment of outcome (3)
is built on, and the input string `x` otherwise.  This is how `z ↦ 𝔷(z)` is made total
without being asked anything off that set (the same device as `Babai.admStr` at
line 4c). -/
noncomputable def case3Pick (S : Set (Ω → A)) (x : Ω → A) (z : Ω → A) : Ω → A :=
  if z ∈ S then z else x

theorem case3Pick_mem {S : Set (Ω → A)} {x : Ω → A} (hx : x ∈ S) (z : Ω → A) :
    case3Pick S x z ∈ S := by
  classical
  rw [case3Pick]
  split
  · assumption
  · exact hx

theorem case3Pick_eq_self {S : Set (Ω → A)} {x z : Ω → A} (hz : z ∈ S) :
    case3Pick S x z = z := by
  classical
  rw [case3Pick, if_pos hz]


/-! ### Outcome (3) is an admissible input of Theorem 9.2.3 -/

variable {Γ : Type}

/-- §15, line 6a: **the relative symmetry defect of the structure of outcome (3) is above
`1/4`**, which is what Theorem 9.2.3 asks of its input at `α = 3/4`.

The assignment has absolute symmetry defect `|D| − t + 1` at least, so its symmetricity `s`
is at most `t − 1`; and `4t ≤ |D|`, so `4s < 4t ≤ |D| ≤ 3|D|`, giving `s/|D| < 3/4`. -/
theorem case3_defect_gt {D : Set Γ} [Fintype ↥D] [DecidableEq ↥D] (t : ℕ)
    (Z : RelStructure ↥D) (ht1 : 1 ≤ t) (h4t : 4 * t ≤ D.ncard)
    (hdef : Fintype.card ↥D - t + 1 ≤ symDefect Z.Aut) :
    1 - (3 / 4 : ℝ) < (structDefect Z : ℝ) := by
  have hncard : Fintype.card ↥D = D.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hncard] at hdef
  rw [← hncard] at h4t
  set cD := Fintype.card ↥D with hcD
  set s := symmetricity Z.Aut with hs
  have hsle : s ≤ cD := by
    by_contra hc
    have : symDefect Z.Aut = 0 := by
      rw [symDefect]; omega
    omega
  have hst : 4 * s < 3 * cD := by
    have h2 : symDefect Z.Aut = cD - s := rfl
    omega
  have hcDpos : 0 < cD := by omega
  have hcDR : (0 : ℝ) < (cD : ℝ) := by exact_mod_cast hcDpos
  have hstR : 4 * (s : ℝ) < 3 * (cD : ℝ) := by exact_mod_cast hst
  have hval : (structDefect Z : ℝ) = 1 - (s : ℝ) / (cD : ℝ) := by
    have h : structDefect Z = 1 - (s : ℚ) / (cD : ℚ) := rfl
    rw [h]
    push_cast
    ring
  rw [hval]
  have : (s : ℝ) / (cD : ℝ) < 3 / 4 := by
    rw [div_lt_iff₀ hcDR]
    linarith
  linarith


/-! ### The versions of outcome (3) -/

/-- §15, **line 6a at outcome (3) of Theorem 13.2.1**: the canonical versions of what
Theorem 9.2.3 finds, read on all of `Γ`.

For every string `z` in the union of the `G`-orbits of the two inputs, the algorithm finds a
set of at most `q(m)m^{O(t)}` outcomes on `Γ` — the multiplicative cost of Theorem 9.2.3 —
each of them a colored `β`-partition of `Γ` or a Johnson scheme on a subset of `Γ` with at
least `βm` vertices, for a `β` that Procedure Align accepts (`1/2 < β`, `5β ≤ 4`).  The
assignment is canonical: a `G`-shift of the string shifts the whole set of versions by the
corresponding permutation of `Γ`.

The `β` depends on which summand the outcome lands in: `3/4` for a colored partition of
`D(z)` extended by `Γ ∖ D(z)`, and `(4/5)·(3/4) = 3/5` for a Johnson scheme inside `D(z)`.
See `Babai.isSplitOutcome_extendOutcome`. -/
theorem exists_canonicalVersions_case3
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (ϕ : G →* Equiv.Perm (Fin m)) (t : ℕ)
    (x y : Ω → A) (hset : LocalCertSetting G ϕ) (ht : LargeK t (Nat.card Ω))
    (htm : 10 * t ≤ m)
    (hx : 4 * m < 5 * (fixedGamma ϕ x t).ncard)
    (hy : 4 * m < 5 * (fixedGamma ϕ y t).ncard)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    ∃ Vers : (Ω → A) → Set (Pt (SplitOutcomes (Fin m))),
      IsCanonicalVersions ϕ Vers ∧
      (∀ z ∈ strOrbitPair G x y, (Vers z).Nonempty) ∧
      (∀ z, (Vers z).Finite) ∧
      (∀ z, (Vers z).ncard ≤ qMax q m * m ^ (c * t)) ∧
      (∀ z ∈ strOrbitPair G x y, ∀ Z ∈ Vers z, ∃ β : ℝ,
        1 / 2 < β ∧ 0 ≤ β ∧ 5 * β ≤ 4 ∧
          IsSplitOutcome β (Set.univ : Set (Fin m)) Z) := by
  classical
  have hcardFin : Fintype.card (Fin m) = m := Fintype.card_fin m
  set S : Set (Ω → A) := strOrbitPair G x y with hSdef
  have hxS : x ∈ S := mem_strOrbitPair_left G x y
  have ht8 : 8 < t := ht.eight_lt
  obtain ⟨𝔷, hkary, hdefz, hhalf, hcanz⟩ :=
    claim_13_2_1_3_onOrbits ϕ t x y hset ht (by rw [hcardFin]; exact htm)
      (by rw [hcardFin]; exact hx) (by rw [hcardFin]; exact hy)
  -- every string of `S` lands in case (3)
  have hDbig : ∀ z ∈ S, 4 * m < 5 * (fixedGamma ϕ z t).ncard := by
    rintro z (hz | hz)
    · rw [ncard_fixedGamma_of_mem_strOrbit ϕ x t hz]; exact hx
    · rw [ncard_fixedGamma_of_mem_strOrbit ϕ y t hz]; exact hy
  -- the string the structure is read off
  set w : (Ω → A) → ↥S := fun z => ⟨case3Pick S x z, case3Pick_mem hxS z⟩ with hw
  have hwbig : ∀ z : Ω → A, 4 * m < 5 * (fixedGamma ϕ ((w z : Ω → A)) t).ncard :=
    fun z => hDbig _ (w z).2
  have hwself : ∀ {z : Ω → A}, z ∈ S → (w z : Ω → A) = z := fun hz =>
    case3Pick_eq_self hz
  -- the object of the input category of Theorem 9.2.3
  have hadm : ∀ z : Ω → A, 2 ≤ t ∧ 4 * t ≤ (fixedGamma ϕ ((w z : Ω → A)) t).ncard ∧
      1 - (3 / 4 : ℝ) < ((@structDefect ↥(fixedGamma ϕ ((w z : Ω → A)) t) _ _
        (Fintype.ofFinite _) (Classical.decEq _) (𝔷 (w z)) : ℚ) : ℝ) := by
    intro z
    refine ⟨by omega, ?_, ?_⟩
    · have hb := hwbig z
      omega
    · refine @case3_defect_gt (Fin m) (fixedGamma ϕ ((w z : Ω → A)) t)
        (Fintype.ofFinite _) (Classical.decEq _) t (𝔷 (w z)) (by omega) ?_ ?_
      · have hb := hwbig z; omega
      · have h := hdefz (w z)
        have ecard : @Fintype.card ↥(fixedGamma ϕ ((w z : Ω → A)) t) (Fintype.ofFinite _)
            = Fintype.card ↥(fixedGamma ϕ ((w z : Ω → A)) t) := by
          congr 1
          all_goals exact Subsingleton.elim _ _
        have edef : @symDefect ↥(fixedGamma ϕ ((w z : Ω → A)) t) (Fintype.ofFinite _)
              (Classical.decEq _) (𝔷 (w z)).Aut = symDefect (𝔷 (w z)).Aut := by
          congr 1
          all_goals exact Subsingleton.elim _ _
        rw [ecard, edef]
        exact h
  let Str : (Ω → A) → Pt (KAryInputs (Fin m) t (3 / 4 : ℝ)) :=
    fun z => ⟨fixedGamma ϕ ((w z : Ω → A)) t, ⟨⟨𝔷 (w z), hkary (w z)⟩, hadm z⟩⟩
  -- canonicity of the assignment on `S`
  have hcanStr : IsCanonicalObjOn ϕ (fun z => z ∈ S) Str := by
    have hcar : ∀ (z : Ω → A), z ∈ S → ∀ σ : G,
        (Str (strAct z (σ : Equiv.Perm Ω))).car = (ϕ σ) '' (Str z).car := by
      intro z hz σ
      have hzσ : strAct z (σ : Equiv.Perm Ω) ∈ S := (strAct_mem_strOrbitPair x y σ).2 hz
      show fixedGamma ϕ ((w (strAct z (σ : Equiv.Perm Ω)) : Ω → A)) t
        = (ϕ σ) '' fixedGamma ϕ ((w z : Ω → A)) t
      rw [hwself hzσ, hwself hz]
      exact canonical_fixedGamma ϕ z t σ
    refine ⟨hcar, fun z hz σ => ?_⟩
    have hzσ : strAct z (σ : Equiv.Perm Ω) ∈ S := (strAct_mem_strOrbitPair x y σ).2 hz
    have hstr : strAct ((w z : Ω → A)) (σ : Equiv.Perm Ω) = (w (strAct z (σ : Equiv.Perm Ω)) : Ω → A) := by
      rw [hwself hz, hwself hzσ]
    obtain ⟨f, hfval, hfmap⟩ := hcanz (w z) (w (strAct z (σ : Equiv.Perm Ω))) σ hstr
    have hfeq : f = permHom (ϕ σ) (Str z) (Str (strAct z (σ : Equiv.Perm Ω)))
        (hcar z hz σ) := by
      refine Equiv.ext fun a => Subtype.ext ?_
      rw [hfval a, permHom_apply]
    rw [← hfeq]
    exact hfmap
  -- Theorem 9.2.3 on that assignment
  obtain ⟨Vers, hcanV, hne, hfin, hcost, hgood, hoff⟩ :=
    exists_canonicalVersions_on (hu (Fin m) t (3 / 4 : ℝ) (le_refl _) (by norm_num)) hK ϕ
      (fun z => z ∈ S) (fun z σ => strAct_mem_strOrbitPair x y σ) Str hcanStr
  -- read on all of `Γ`
  refine ⟨fun z => extendOutcome '' Vers z,
    isCanonicalVersions_image_extendOutcome hK hcanV,
    fun z hz => (hne z hz).image _, fun z => (hfin z).image _, fun z => ?_,
    fun z hz Z hZ => ?_⟩
  · show (extendOutcome '' Vers z).ncard ≤ qMax q m * m ^ (c * t)
    by_cases hz : z ∈ S
    · refine le_trans (Set.ncard_image_le (hfin z)) ?_
      refine le_trans (hcost z hz) ?_
      have hsub : (fixedGamma ϕ ((w z : Ω → A)) t).ncard ≤ m := by
        have h := Set.ncard_le_ncard (Set.subset_univ (fixedGamma ϕ ((w z : Ω → A)) t))
          (Set.toFinite _)
        rwa [Set.ncard_univ, Nat.card_eq_fintype_card, hcardFin] at h
      exact Nat.mul_le_mul (le_qMax q hsub) (Nat.pow_le_pow_left hsub _)
    · rw [hoff z hz]
      simp
  · obtain ⟨W, hW, rfl⟩ := hZ
    have hgW : IsSplitOutcome (3 / 4 : ℝ) (fixedGamma ϕ ((w z : Ω → A)) t) W :=
      hgood z hz W hW
    rw [hwself hz] at hgW
    exact isSplitOutcome_extendOutcome (by norm_num) (by norm_num) (hDbig z hz) hgW

end Case3Versions

end Babai
