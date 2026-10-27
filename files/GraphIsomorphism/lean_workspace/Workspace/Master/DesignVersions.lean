/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15, line 4c: Theorem 9.2.3 applied to `H(x)`, as canonical versions of the outcome.
-/
import Workspace.Master.KAryOfString
import Workspace.Master.SplitTransport
import Workspace.SplitOrJohnson.Sec92

/-!
# Line 4c: the canonical versions of the structure Theorem 9.2.3 finds

> 4c. else (: now their relative symmetry defect is `≥ 1/2` :)
>     (: view these hypergraphs as `t`-ary relational structures :)
>     apply Extended Design Lemma (Theorem 9.2.3)

Theorem 9.2.3 is a canonical reduction of the category of admissible `t`-ary relational
structures (`Babai.KAryInputs`) into the category of its outcomes
(`Babai.SplitOutcomes`), at a multiplicative cost `q(n)n^{O(k)}`.  Sec. 14.2 uses the
outcome as a structure attached to the *string*, one per individualization:

> we need to compare not one but `q(m)` instances of `X(y)` with `X(x)`.

`Babai.exists_canonicalVersions_on` is the passage between the two.  Its three inputs are
here:

* the input object, `Babai.hyperInput` — `H(z)` as an admissible input of Theorem 9.2.3
  (`Workspace/Master/KAryOfString.lean`);
* the action of `S(Γ)` on the outcomes, `Babai.exists_isCatAction_splitOutcomes`
  (`Workspace/Master/SplitTransport.lean`);
* the admissible set of strings, `Babai.LargeDefectData id z α`, which is `G`-invariant
  because the symmetry defect of `H(z)` is (`Babai.defect_colorAut_strAct`).

The assignment `z ↦ H(z)` is defined on every string, admissible or not, by feeding the
admissible string `Babai.admStr` — which is `z` itself when `z` is admissible, and the
input string of line 4c otherwise — to `Babai.hyperInput`.  That keeps the underlying set
of the object equal to `Γ` for every `z`, which is what makes the two canonicity conditions
of `Babai.IsCanonicalObjOn` statements about `H(z)` alone.

`Babai.exists_canonicalVersions_9_2_3` is the conclusion.  This is piece (ii) of Mismatch 2
in `Workspace/Master/DESIGN.md`, at line 4c.
-/

universe u v

namespace Babai

open Equiv
open scoped Pointwise

section Line4c

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {m : ℕ} {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm (Fin m)} {t : ℕ}

/-! ### The admissible strings form a `G`-invariant set -/

/-- §15, line 4b: **the relative symmetry defect of `H(z)` is a `G`-invariant of the
string**.  A `G`-shift of the string conjugates `Aut(H(z))` by the corresponding
permutation of `Γ`, and the symmetry defect does not see a conjugation. -/
theorem defect_colorAut_strAct (id : PrimitiveCaseId ϕ t) (z : Ω → A) (σ : G) :
    defect (colorAut t (hyperColoring id (strAct z (σ : Equiv.Perm Ω))))
      = defect (colorAut t (hyperColoring id z)) := by
  rw [hyperColoring_strAct_eq id z σ, colorAut_smul, defect_map_permCongrHom]

/-- §15, line 4c: the admissible strings of line 4c form a `G`-invariant set. -/
theorem largeDefectData_strAct (id : PrimitiveCaseId ϕ t) {α : ℝ} (z : Ω → A) (σ : G) :
    LargeDefectData id (strAct z (σ : Equiv.Perm Ω)) α ↔ LargeDefectData id z α := by
  constructor
  · intro h
    exact ⟨h.t_two, h.four_t, by
      have := h.large_defect
      rwa [defect_colorAut_strAct id z σ] at this⟩
  · intro h
    exact ⟨h.t_two, h.four_t, by
      have := h.large_defect
      rwa [← defect_colorAut_strAct id z σ] at this⟩

/-! ### `z ↦ H(z)` as a total assignment -/

open scoped Classical in
/-- §15, line 4c: the string `z` itself when it is admissible, and the input string of
line 4c otherwise.  This is how the assignment `z ↦ H(z)` is made total without being
asked anything off the admissible set. -/
noncomputable def admStr (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (_hx : LargeDefectData id x α) (z : Ω → A) : Ω → A :=
  if LargeDefectData id z α then z else x

theorem largeDefectData_admStr (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (hx : LargeDefectData id x α) (z : Ω → A) :
    LargeDefectData id (admStr id hx z) α := by
  classical
  rw [admStr]
  split
  · assumption
  · exact hx

theorem admStr_eq_self (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (hx : LargeDefectData id x α) {z : Ω → A} (hz : LargeDefectData id z α) :
    admStr id hx z = z := by
  classical
  rw [admStr, if_pos hz]

/-- §15, line 4c: **`H(z)` as an object of the input category of Theorem 9.2.3**, for every
string `z`. -/
noncomputable def designStr (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (hx : LargeDefectData id x α) (z : Ω → A) : Pt (KAryInputs (Fin m) t α) :=
  hyperInput id (largeDefectData_admStr id hx z)

@[simp] theorem designStr_car (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (hx : LargeDefectData id x α) (z : Ω → A) : (designStr id hx z).car = Set.univ := rfl

/-- §15, line 4c: **the assignment is canonical on the admissible strings**. -/
theorem isCanonicalObjOn_designStr (id : PrimitiveCaseId ϕ t) {α : ℝ} {x : Ω → A}
    (hx : LargeDefectData id x α) :
    IsCanonicalObjOn ϕ (fun z => LargeDefectData id z α) (designStr id hx) where
  car z _ σ := by
    show (Set.univ : Set (Fin m)) = (ϕ σ) '' Set.univ
    simp [Set.image_univ]
  iso z hz σ := by
    have hzσ : LargeDefectData id (strAct z (σ : Equiv.Perm Ω)) α :=
      (largeDefectData_strAct id z σ).2 hz
    show (hyperStructure id (admStr id hx z)).map _
      = hyperStructure id (admStr id hx (strAct z (σ : Equiv.Perm Ω)))
    rw [admStr_eq_self id hx hz, admStr_eq_self id hx hzσ]
    exact hyperPt_iso id z σ (hyperPt_car_smul id z σ)

/-! ### Theorem 9.2.3 at line 4c -/

/-- §9.2, Theorem 9.2.3 **with its constants fixed before the ground set**.

`Babai.theorem_9_2_3` fixes the ground set `Ω` first and produces `q` and `c` after it, so
the constants it hands back may change with the ground set.  Line 4c of Sec. 15 calls
Theorem 9.2.3 once per round, each time on another set `Γ = Fin m`, and the cost of a
round has to be **one** function of the window size, so the constants must be the same at
every call.  This is the uniform form, with the binder of the ground set inside the
existential; see the entry *"the absolute constants are chosen after the ground set"* in
the corrected paper.

This is **not an axiom**.  It is a hypothesis of the construction of lines 4c–4d, and it is
discharged as soon as `Babai.theorem_9_2_3` is restated in this form, which is the repair
that entry describes. -/
def Theorem923Uniform (q : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ (Γ : Type) [Fintype Γ] [DecidableEq Γ] (k : ℕ) (α : ℝ), 3 / 4 ≤ α → α < 1 →
    FindsAtMultCost (KAryInputs Γ k α) (SplitOutcomes Γ)
      (fun X => q X.car.ncard * X.car.ncard ^ (c * k))
      (fun X Z => IsSplitOutcome α X.car Z)

/-- §15, **line 4c**, the part of `Babai.exists_canonicalVersions_9_2_3` that comes **after**
the constants of Theorem 9.2.3 are fixed.

The constants `q` and `c` are arguments, so the caller may use the same pair at every call.
Everything else is as in `Babai.exists_canonicalVersions_9_2_3`, which is the corollary
obtained by taking `q` and `c` from `Babai.theorem_9_2_3`. -/
theorem exists_canonicalVersions_of_finds
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (id : PrimitiveCaseId ϕ t) {α : ℝ}
    (hα : 3 / 4 ≤ α) (hα1 : α < 1) {x : Ω → A} (hx : LargeDefectData id x α)
    (q : ℕ → ℕ) (c : ℕ)
    (hfind : ∀ (k : ℕ) (β : ℝ), 3 / 4 ≤ β → β < 1 →
      FindsAtMultCost (KAryInputs (Fin m) k β) (SplitOutcomes (Fin m))
        (fun X => q X.car.ncard * X.car.ncard ^ (c * k))
        (fun X Z => IsSplitOutcome β X.car Z)) :
    ∃ Vers : (Ω → A) → Set (Pt (SplitOutcomes (Fin m))),
      IsCanonicalVersions ϕ Vers ∧
      (∀ z, LargeDefectData id z α → (Vers z).Nonempty) ∧
      (∀ z, (Vers z).Finite) ∧
      (∀ z, LargeDefectData id z α → (Vers z).ncard ≤ q m * m ^ (c * t)) ∧
      (∀ z, LargeDefectData id z α →
        ∀ Z ∈ Vers z, IsSplitOutcome α (Set.univ : Set (Fin m)) Z) ∧
      (∀ z, ¬ LargeDefectData id z α → Vers z = ∅) := by
  obtain ⟨Vers, hcan, hne, hfin, hcost, hgood, hoff⟩ :=
    exists_canonicalVersions_on (hfind t α hα hα1) hK ϕ
      (fun z => LargeDefectData id z α) (largeDefectData_strAct id)
      (designStr id hx) (isCanonicalObjOn_designStr id hx)
  have hm : (Set.univ : Set (Fin m)).ncard = m := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨Vers, hcan, hne, hfin, fun z hz => ?_, fun z hz => hgood z hz, hoff⟩
  have h := hcost z hz
  rwa [designStr_car, hm] at h

/-- §15, line 4c, the uniform form of `Babai.exists_canonicalVersions_of_finds`: the
constants come from `Babai.Theorem923Uniform`, so they do not depend on `m`. -/
theorem exists_canonicalVersions_of_uniform
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (id : PrimitiveCaseId ϕ t) {α : ℝ}
    (hα : 3 / 4 ≤ α) (hα1 : α < 1) {x : Ω → A} (hx : LargeDefectData id x α)
    {q : ℕ → ℕ} {c : ℕ} (hu : Theorem923Uniform q c) :
    ∃ Vers : (Ω → A) → Set (Pt (SplitOutcomes (Fin m))),
      IsCanonicalVersions ϕ Vers ∧
      (∀ z, LargeDefectData id z α → (Vers z).Nonempty) ∧
      (∀ z, (Vers z).Finite) ∧
      (∀ z, LargeDefectData id z α → (Vers z).ncard ≤ q m * m ^ (c * t)) ∧
      (∀ z, LargeDefectData id z α →
        ∀ Z ∈ Vers z, IsSplitOutcome α (Set.univ : Set (Fin m)) Z) ∧
      (∀ z, ¬ LargeDefectData id z α → Vers z = ∅) :=
  exists_canonicalVersions_of_finds hK id hα hα1 hx q c fun k β hβ hβ1 => hu (Fin m) k β hβ hβ1

/-- §15, **line 4c**: *"apply Extended Design Lemma (Theorem 9.2.3)"*, as the canonical
versions of the structure found.

For every string `z` whose hypergraph has a large enough symmetry defect, the algorithm
finds a set `Vers z` of at most `q(m)m^{O(t)}` structures on `Γ` — the multiplicative cost
of Theorem 9.2.3 — each of them a colored `α`-partition of `Γ` or a Johnson scheme on a
subset of `Γ` of at least `αm` vertices (`Babai.IsSplitOutcome`), and the assignment is
canonical: a `G`-shift of the string shifts the whole set of versions by the corresponding
permutation of `Γ` (`Babai.IsCanonicalVersions`).  Strings with a small defect, which line
4b has taken care of, get no version at all. -/
theorem exists_canonicalVersions_9_2_3
    [inst : MulAction (Equiv.Perm (Fin m)) (Pt (SplitOutcomes (Fin m)))]
    (hK : IsCatAction (SplitOutcomes (Fin m))) (id : PrimitiveCaseId ϕ t) {α : ℝ}
    (hα : 3 / 4 ≤ α) (hα1 : α < 1) {x : Ω → A} (hx : LargeDefectData id x α) :
    ∃ (q : ℕ → ℕ) (c : ℕ), RAM.QuasiPolyBound q ∧
      ∃ Vers : (Ω → A) → Set (Pt (SplitOutcomes (Fin m))),
        IsCanonicalVersions ϕ Vers ∧
        (∀ z, LargeDefectData id z α → (Vers z).Nonempty) ∧
        (∀ z, (Vers z).Finite) ∧
        (∀ z, LargeDefectData id z α → (Vers z).ncard ≤ q m * m ^ (c * t)) ∧
        (∀ z, LargeDefectData id z α →
          ∀ Z ∈ Vers z, IsSplitOutcome α (Set.univ : Set (Fin m)) Z) ∧
        (∀ z, ¬ LargeDefectData id z α → Vers z = ∅) := by
  obtain ⟨q, c, hq, hfind⟩ := theorem_9_2_3
  exact ⟨q, c, hq, exists_canonicalVersions_of_finds hK id hα hα1 hx q c (hfind (Fin m))⟩

end Line4c

end Babai
