/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 6a, outcome (2b) of Theorem 13.2.1: Theorem 9.2.3 applied to the family of
individualized constituents, as canonical versions of the outcome.
-/
import Workspace.Master.Case2bInput
import Workspace.Master.Case3Versions

/-!
# Line 6a, outcome (2b): the canonical versions of the family

Outcome (2b) of Theorem 13.2.1 is not one structure but a **family**: the constituents
`X_i = (C ∖ S; R)` over all individualizations `S ∈ (C choose d−1)` and all off-diagonal
orbitals `R` of `F^C_{(S)}`, at a multiplicative cost of `m^{d−1}(m−1) ≤ m^5`.  The paper's

> **Warning**: the numbering of the `R_i` is not canonical; isomorphisms may permute the
> `R_i`

is what a family absorbs: `Babai.case2bFamily_canonical` says that a `G`-shift of the string
carries the family onto the family, as a set.

| piece | name |
|---|---|
| the family is non-empty, admissible and of size at most `m^5` | `Babai.case2bFamily_facts` |
| the versions of line 6a, read on `Γ` | `Babai.exists_canonicalVersions_case2b` |

The size bound is the paper's `m^{d−1}(m−1)` in the weaker form `m^d ≤ m^5`, which is all
Sec. 15 uses: an individualization is the range of a `(d−1)`-tuple of points of `Γ`, and by
transitivity of `F^C_{(S)}` on `C ∖ S` every off-diagonal orbital is the orbital through
`(a₀, b)` for one fixed `a₀` and some `b ∈ Γ`.  So the family is covered by
`(Fin (d−1) → Γ) × Γ`, of size `m^{d−1}·m = m^d`.
-/

universe u v

namespace Babai

open MulAction Equiv
open scoped Pointwise

section FamilyFacts

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

open scoped Classical in
/-- §13.2, **case (2b): the family is non-empty, every member is an admissible input of
Theorem 9.2.3 at `α = 3/4`, and the family has at most `m^5` members.**

The hypotheses are case (2) of Theorem 13.2.1 (`Babai.Case2`) together with the failure of
case (2a) — no orbit of more than `4m/5` points carries the alternating group — and
`m ≥ 217`, which is Theorem 9.2.3's own numeric hypothesis. -/
theorem case2bFamily_facts (H : Subgroup (Equiv.Perm Γ)) (hm : 217 ≤ Fintype.card Γ)
    (h2 : Case2 H)
    (h2a : ∀ γ : Γ, ¬ (4 * Fintype.card Γ < 5 * (orbit H γ : Set Γ).ncard ∧
      alternatingGroup ((orbit H γ : Set Γ)) ≤ restrictTo H _ (isInvariant_orbit H γ))) :
    (case2bFamily H).Nonempty ∧
      (∀ r ∈ case2bFamily H, Case2bOk (3 / 4 : ℝ) r ∧
        11 * Fintype.card Γ ≤ 15 * r.1.ncard) ∧
      (case2bFamily H).ncard ≤ (Fintype.card Γ) ^ 5 := by
  classical
  obtain ⟨γ₀, hγ₀⟩ := h2
  set m := Fintype.card Γ with hmdef
  set C : Set Γ := (orbit H γ₀ : Set Γ) with hCdef
  have hCbig : 4 * m < 5 * C.ncard := hγ₀
  have hCle : C.ncard ≤ m := by
    have h := Set.ncard_le_ncard (Set.subset_univ C) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  have h6 : 6 ≤ C.ncard := by omega
  obtain ⟨hd1, hd5, hfacts⟩ :=
    case2b_facts_on H γ₀ (fun hc => h2a γ₀ ⟨hCbig, hc⟩) h6
  set d := degtransOn H C with hddef
  -- the big orbit is unique
  have hCncard : (orbit H γ₀ : Set Γ).ncard = C.ncard := rfl
  have huniq : ∀ γ : Γ, 4 * m < 5 * (orbit H γ : Set Γ).ncard → (orbit H γ : Set Γ) = C := by
    intro γ hγ
    refine orbit_eq_of_two_large (by omega) ?_
    rw [hCncard]
    omega
  -- every member is admissible
  have hok : ∀ r ∈ case2bFamily H, Case2bOk (3 / 4 : ℝ) r ∧ 11 * m ≤ 15 * r.1.ncard := by
    rintro r ⟨γ, S, a, b, hbig, hSsub, hScard, ha, hb, hab, rfl⟩
    have horb : (orbit H γ : Set Γ) = C := huniq γ hbig
    have hScard' : S.ncard = d - 1 := by rw [hScard, hddef, horb]
    have hSsubC : S ⊆ C := by rw [← horb]; exact hSsub
    have hfac := hfacts S hSsubC hScard'
    have htr : TransOnDiff H (orbit H γ : Set Γ) S := by rw [horb]; exact hfac.1
    have h2nd : NotDoublyTransOnDiff H (orbit H γ : Set Γ) S := by rw [horb]; exact hfac.2
    have hdiff : ((orbit H γ : Set Γ) \ S).ncard + S.ncard = (orbit H γ : Set Γ).ncard :=
      Set.ncard_diff_add_ncard_of_subset hSsub (Set.toFinite _)
    have hSle : S.ncard ≤ 4 := by omega
    have hbnd : 11 * m ≤ 15 * ((orbit H γ : Set Γ) \ S).ncard := by omega
    have h8 : 4 * 2 ≤ ((orbit H γ : Set Γ) \ S).ncard := by omega
    -- the defect of the constituent
    have hdef : (1 : ℚ) / 2 ≤
        case2bDefect (((orbit H γ : Set Γ) \ S), orbitalOn H S a b) := by
      show (1 : ℚ) / 2 ≤ @structDefect ↥((orbit H γ : Set Γ) \ S) _ _ (Fintype.ofFinite _)
        (Classical.decEq _) (binStruct ((orbit H γ : Set Γ) \ S) (orbitalOn H S a b))
      letI : Fintype ↥((orbit H γ : Set Γ) \ S) := Fintype.ofFinite _
      letI : DecidableEq ↥((orbit H γ : Set Γ) \ S) := Classical.decEq _
      exact half_le_structDefect_binStruct_orbitalOn ha hb hab htr h2nd
    have hdefR : (1 : ℝ) - 3 / 4 <
        ((case2bDefect (((orbit H γ : Set Γ) \ S), orbitalOn H S a b) : ℚ) : ℝ) := by
      have h : ((1 : ℚ) / 2 : ℝ) ≤
          ((case2bDefect (((orbit H γ : Set Γ) \ S), orbitalOn H S a b) : ℚ) : ℝ) := by
        exact_mod_cast hdef
      norm_num at h ⊢
      linarith
    exact ⟨⟨le_rfl, h8, hdefR⟩, hbnd⟩
  -- the family is non-empty
  have hne : (case2bFamily H).Nonempty := by
    obtain ⟨S, hSsub, hScard⟩ := Set.exists_subset_card_eq (s := C) (n := d - 1) (by omega)
    have hdiff : (C \ S).ncard + S.ncard = C.ncard :=
      Set.ncard_diff_add_ncard_of_subset hSsub (Set.toFinite _)
    have h2le : 1 < (C \ S).ncard := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h2le
    exact ⟨_, ⟨γ₀, S, a, b, hCbig, hSsub, by rw [← hddef]; exact hScard, ha, hb, hab, rfl⟩⟩
  -- the size bound
  have hsize : (case2bFamily H).ncard ≤ m ^ 5 := by
    set pick : Set Γ → Γ := fun T => if h : (C \ T).Nonempty then h.choose else γ₀
      with hpickdef
    have hpick : ∀ T : Set Γ, (C \ T).Nonempty → pick T ∈ C \ T := by
      intro T hT
      rw [hpickdef]
      simp only [dif_pos hT]
      exact hT.choose_spec
    set k := d - 1 with hkdef
    set f : (Fin k → Γ) × Γ → Set Γ × Set (Γ × Γ) :=
      fun p => (C \ Set.range p.1, orbitalOn H (Set.range p.1) (pick (Set.range p.1)) p.2)
      with hfdef
    have hsub : case2bFamily H ⊆ Set.range f := by
      rintro r ⟨γ, S, a, b, hbig, hSsub, hScard, ha, hb, hab, rfl⟩
      have horb : (orbit H γ : Set Γ) = C := huniq γ hbig
      rw [horb] at hSsub hScard ha hb ⊢
      rw [← hddef] at hScard
      obtain ⟨htr, -⟩ := hfacts S hSsub hScard
      -- an enumeration of `S`
      obtain ⟨v, hv⟩ : ∃ v : Fin k → Γ, Set.range v = S := by
        haveI : Fintype ↥S := Fintype.ofFinite _
        have hcard : Fintype.card ↥S = k := by
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hScard]
        obtain e := Fintype.equivFinOfCardEq hcard
        refine ⟨fun i => ((e.symm i : ↥S) : Γ), ?_⟩
        ext w
        constructor
        · rintro ⟨i, rfl⟩; exact (e.symm i).2
        · intro hw
          exact ⟨e ⟨w, hw⟩, by simp⟩
      -- the base point, reached from `a` inside the stabilizer
      have hCSne : (C \ S).Nonempty := ⟨a, ha⟩
      have ha₀ : pick S ∈ C \ S := hpick S hCSne
      obtain ⟨h, hh, hval⟩ := htr a ha (pick S) ha₀
      refine ⟨(v, h b), ?_⟩
      show (C \ Set.range v, orbitalOn H (Set.range v) (pick (Set.range v)) (h b))
        = (C \ S, orbitalOn H S a b)
      rw [hv]
      refine Prod.ext rfl ?_
      show orbitalOn H S (pick S) (h b) = orbitalOn H S a b
      rw [← hval]
      exact orbitalOn_eq_of_stab H S a b hh
    have h1 : (Set.range f).ncard ≤ Nat.card ((Fin k → Γ) × Γ) := by
      rw [← Set.image_univ]
      have h := Set.ncard_image_le (s := (Set.univ : Set ((Fin k → Γ) × Γ))) (f := f)
        (Set.toFinite _)
      rwa [Set.ncard_univ] at h
    have h2 : Nat.card ((Fin k → Γ) × Γ) = m ^ k * m := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_pi_const]
    have h3 : m ^ k * m ≤ m ^ 5 := by
      have he : m ^ k * m = m ^ (k + 1) := by ring
      rw [he]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    calc (case2bFamily H).ncard ≤ (Set.range f).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Nat.card ((Fin k → Γ) × Γ) := h1
      _ = m ^ k * m := h2
      _ ≤ m ^ 5 := h3
  exact ⟨hne, hok, hsize⟩

end FamilyFacts

/-! ### The versions of outcome (2b) -/

section Case2bVersions

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
  {G : Subgroup (Equiv.Perm Ω)}

open scoped Classical in
/-- §15, **line 6a at outcome (2b) of Theorem 13.2.1**: the canonical versions of what
Theorem 9.2.3 finds on the family of individualized constituents, read on all of `Γ`.

For every string `z` whose own aggregate is in case (2b), the algorithm finds a non-empty set of
at most `m^5·q(m)m^{O(t)}` outcomes on `Γ` — the `m^{d−1}(m−1) ≤ m^5` individualizations of
case (2b) times the multiplicative cost of Theorem 9.2.3 on each — each of them a colored
`β`-partition of `Γ` or a Johnson scheme on a subset of `Γ` with at least `βm` vertices, for
a `β` that Procedure Align accepts (`1/2 < β`, `5β ≤ 4`).  The assignment is canonical: a
`G`-shift of the string shifts the whole set of versions by the corresponding permutation of
`Γ`, with no claim about which version goes to which, which is exactly what the paper's
*"Warning: the numbering of the `R_i` is not canonical"* allows.

The case test is `Case2 (bigFGamma ϕ z ts) ∧ ¬ AggregateCase2a ϕ z ts`.
Versions are empty off this test, and the same cost bound holds for every string.
The default object of `case2bStr` is chosen from the family at `x`. It is used only
outside `Case2bOk`, so no member of an admissible string's family uses it.

The two thresholds are `βJ = 11/20` for a Johnson scheme inside `C ∖ S` and `βP = 3/4` for a
colored partition of `C ∖ S` extended by `Γ ∖ (C ∖ S)`; both are reached because
`|C ∖ S| ≥ |C| − 4 > 4m/5 − 4 ≥ (11/15)m` for `m ≥ 217`.  See
`Babai.isSplitOutcome_extendOutcome_of`. -/
theorem exists_canonicalVersions_case2b
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (ϕ : G →* Equiv.Perm (Fin m)) (ts : ℕ)
    (hm : 217 ≤ m) (hts : 2 ≤ ts) (x : Ω → A)
    (h2 : Case2 (bigFGamma ϕ x ts)) (h2a : ¬ AggregateCase2a ϕ x ts)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    ∃ Vers : (Ω → A) → Set (Pt (SplitOutcomes (Fin m))),
      IsCanonicalVersions ϕ Vers ∧
      (∀ z, Case2 (bigFGamma ϕ z ts) ∧ ¬ AggregateCase2a ϕ z ts → (Vers z).Nonempty) ∧
      (∀ z, (Vers z).Finite) ∧
      (∀ z, (Vers z).ncard ≤ m ^ 5 * (qMax q m * m ^ (c * ts))) ∧
      (∀ z, Case2 (bigFGamma ϕ z ts) ∧ ¬ AggregateCase2a ϕ z ts →
        ∀ Z ∈ Vers z, ∃ β : ℝ,
        1 / 2 < β ∧ 0 ≤ β ∧ 5 * β ≤ 4 ∧
          IsSplitOutcome β (Set.univ : Set (Fin m)) Z) ∧
      (∀ z, ¬ (Case2 (bigFGamma ϕ z ts) ∧ ¬ AggregateCase2a ϕ z ts) → Vers z = ∅) := by
  classical
  have hcardFin : Fintype.card (Fin m) = m := Fintype.card_fin m
  let Adm : (Ω → A) → Prop := fun z =>
    Case2 (bigFGamma ϕ z ts) ∧ ¬ AggregateCase2a ϕ z ts
  set Ok : (Set (Fin m) × Set (Fin m × Fin m)) → Prop :=
    fun r => Case2bOk (3 / 4 : ℝ) r ∧ 11 * m ≤ 15 * r.1.ncard with hOk
  set Fam : (Ω → A) → Set (Set (Fin m) × Set (Fin m × Fin m)) :=
    fun z => case2bFamily (bigFGamma ϕ z ts) with hFam
  -- apply the family facts to each string that passes its own case test
  have hFacts : ∀ z, Adm z → (Fam z).Nonempty ∧
      (∀ r ∈ Fam z, Ok r) ∧ (Fam z).ncard ≤ m ^ 5 := by
    intro z hz
    simpa only [Fintype.card_fin] using
      case2bFamily_facts (bigFGamma ϕ z ts) (by rw [hcardFin]; exact hm) hz.1
        (fun γ hc => hz.2 ⟨γ, hc⟩)
  have hFamOk : ∀ z, Adm z → ∀ r ∈ Fam z, Ok r := fun z hz => (hFacts z hz).2.1
  have hFamFin : ∀ z : Ω → A, (Fam z).Finite := fun _ => Set.toFinite _
  have hFamNe : ∀ z, Adm z → (Fam z).Nonempty := fun z hz => (hFacts z hz).1
  have hFamCard : ∀ z, Adm z → (Fam z).ncard ≤ m ^ 5 := fun z hz => (hFacts z hz).2.2
  -- `x` supplies a default, used only outside `Case2bOk`
  obtain ⟨r₀, hr₀⟩ := hFamNe x ⟨h2, h2a⟩
  set X₀ : Pt (KAryInputs (Fin m) 2 (3 / 4 : ℝ)) :=
    case2bPt (3 / 4 : ℝ) r₀ (hFamOk x ⟨h2, h2a⟩ r₀ hr₀).1 with hX₀
  set Str : (Set (Fin m) × Set (Fin m × Fin m)) → Pt (KAryInputs (Fin m) 2 (3 / 4 : ℝ)) :=
    case2bStr (3 / 4 : ℝ) X₀ with hStr
  -- the family moves with the string
  have hFamMove : ∀ (z : Ω → A) (σ : G),
      Fam (strAct z (σ : Equiv.Perm Ω)) = moveCase2b (ϕ σ) '' Fam z :=
    fun z σ => case2bFamily_canonical ϕ z ts σ
  -- the cost of Theorem 9.2.3 on one member
  have hStrCar : ∀ r : Set (Fin m) × Set (Fin m × Fin m), (Str r).car.ncard ≤ m := by
    intro r
    have h := Set.ncard_le_ncard (Set.subset_univ (Str r).car) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, hcardFin] at h
  have hcost : ∀ r : Set (Fin m) × Set (Fin m × Fin m),
      q (Str r).car.ncard * (Str r).car.ncard ^ (c * 2) ≤ qMax q m * m ^ (c * ts) := by
    intro r
    refine Nat.mul_le_mul (le_qMax q (hStrCar r)) ?_
    calc (Str r).car.ncard ^ (c * 2) ≤ m ^ (c * 2) := Nat.pow_le_pow_left (hStrCar r) _
      -- `2 ≤ ts` is `Babai.LargeK.eight_lt` at the call site, through `hts`
      _ ≤ m ^ (c * ts) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hts)
  -- the versions on `C ∖ S`, by the family form of §14.2
  obtain ⟨Vers, hcanV, hne, hfin, hcard, hgood, hoff⟩ :=
    exists_canonicalVersions_family_on (hu (Fin m) 2 (3 / 4 : ℝ) (le_refl _) (by norm_num))
      hK ϕ Adm (case2b_test_strAct ϕ · ts ·) Fam Str
      moveCase2b Ok hFamOk (fun z _ σ => hFamMove z σ)
      (fun π r hr => case2bStr_car (3 / 4 : ℝ) X₀ π hr.1)
      (fun π r hr => case2bStr_iso (3 / 4 : ℝ) X₀ π hr.1)
      (m ^ 5) (qMax q m * m ^ (c * ts)) hFamNe hFamFin hFamCard
      (fun z _ r _ => hcost r)
  -- read on all of `Γ`
  refine ⟨fun z => extendOutcome '' Vers z,
    isCanonicalVersions_image_extendOutcome hK hcanV,
    fun z hz => (hne z hz).image _, fun z => (hfin z).image _, fun z => ?_,
    (fun z hz Z hZ => ?_), fun z hz => ?_⟩
  · show (extendOutcome '' Vers z).ncard ≤ m ^ 5 * (qMax q m * m ^ (c * ts))
    by_cases hz : Adm z
    · exact le_trans (Set.ncard_image_le (hfin z)) (hcard z hz)
    · rw [hoff z hz]; simp
  · obtain ⟨W, hW, rfl⟩ := hZ
    obtain ⟨r, hr, hgW⟩ := hgood z hz W hW
    obtain ⟨hok, hbig⟩ := hFamOk z hz r hr
    have hcarr : (Str r).car = r.1 := by rw [hStr, case2bStr_of (3 / 4 : ℝ) X₀ hok]; rfl
    rw [hcarr] at hgW
    have hle : r.1.ncard ≤ m := by rw [← hcarr]; exact hStrCar r
    have hbigR : (11 : ℝ) * (m : ℝ) ≤ 15 * (r.1.ncard : ℝ) := by exact_mod_cast hbig
    have hleR : (r.1.ncard : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    refine isSplitOutcome_extendOutcome_of (βJ := (11 / 20 : ℝ)) (βP := (3 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ hgW
    · show (11 / 20 : ℝ) * (m : ℝ) ≤ (3 / 4 : ℝ) * (r.1.ncard : ℝ)
      linarith
    · show (3 / 4 : ℝ) * (r.1.ncard : ℝ) ≤ (3 / 4 : ℝ) * (m : ℝ)
      linarith
    · show (m : ℝ) - (r.1.ncard : ℝ) ≤ (3 / 4 : ℝ) * (m : ℝ)
      linarith
  · change extendOutcome '' Vers z = ∅
    rw [hoff z hz, Set.image_empty]

end Case2bVersions

end Babai
