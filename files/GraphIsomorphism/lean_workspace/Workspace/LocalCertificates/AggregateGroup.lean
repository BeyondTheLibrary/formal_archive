/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.1 and §13.2: the calls of Procedure AggregateCertificates are instances with
respect to a *group*, after the alignment step of Remark 11.1.4.
-/
import Workspace.LocalCertificates.AggregateRound
import Workspace.Master.Defs

/-!
# The calls of AggregateCertificates are group instances after alignment

Procedure Recompute `H(W)` (§13.1, lines 04a–04h) asks String Isomorphism on the cosets
`Nσ` of `N = ker ψ̄_T` inside `H(W)`, and Procedure CompareLocalCertificates asks it on the
cosets `(πσ)N`.  So its calls are **coset** instances, not group instances, and
`Babai.IsGroupInstance` is false for them as they stand.

The paper's own remedy is Remark 11.1.4:

> Applying Eq. (57) to a subgroup `K = G ≤ S(Ω)`, we see that the isomorphism problem for
> the pair `(x,y)` with respect to a coset `Gσ` is the same as the isomorphism problem for
> `(x, y^{σ⁻¹})` with respect to the group `G`. … The shift `y ← y^{σ⁻¹}` is an important
> **alignment step** that will accompany every reduction of the ambient group `G`.

`Babai.alignInst` is that step, made once for all: pick a member `σ` of the coset `K` and
replace `(K, Δ, x, y)` by `(σ⁻¹K, Δ, x, y^{σ⁻¹})`.  The set `σ⁻¹K` is the group `N` itself
when `K = σ₀N`, so the aligned instance is a group instance, and `σ` is in the ambient
group, so the aligned candidate set stays inside it.  `Babai.SIReduction.alignCalls` applies
the step to every call of a reduction: by Eq. (59) the value is unchanged, and the calls are
the old calls, aligned, so their number and their windows are unchanged.

`Babai.alignedAggregateRound` is `Babai.aggregateRound` with the two phases aligned.  It is
what lines 5–7 of the Master Algorithm run.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Pointwise
open scoped Classical

universe u v w

/-! ### The alignment step of Remark 11.1.4 -/

section Align

variable {Ω : Type u} {A : Type v} {α : Type w}

/-- A member of a nonempty set of permutations, and `1` otherwise: the `σ` of the
alignment step of Remark 11.1.4.

The identity is preferred whenever it is available.  A set that contains `1` is already
aligned — a group, for instance — and then the alignment step does nothing
(`Babai.alignInst_eq_self`).  This is what makes `Babai.alignInst` idempotent, so that a
round of the recursion may be aligned once and read again at its own children. -/
noncomputable def cosetRepOf (K : Set (Equiv.Perm Ω)) : Equiv.Perm Ω :=
  if (1 : Equiv.Perm Ω) ∈ K then 1
  else if h : K.Nonempty then h.choose else 1

theorem cosetRepOf_mem {K : Set (Equiv.Perm Ω)} (h : K.Nonempty) : cosetRepOf K ∈ K := by
  rw [cosetRepOf]
  by_cases h1 : (1 : Equiv.Perm Ω) ∈ K
  · rw [if_pos h1]; exact h1
  · rw [if_neg h1, dif_pos h]; exact h.choose_spec

/-- **The representative of an aligned set is the identity**: on a set that contains `1`
the alignment step of Remark 11.1.4 has nothing to do. -/
@[simp] theorem cosetRepOf_eq_one {K : Set (Equiv.Perm Ω)} (h : (1 : Equiv.Perm Ω) ∈ K) :
    cosetRepOf K = 1 := by
  rw [cosetRepOf, if_pos h]

/-- The representative of a subgroup is the identity. -/
@[simp] theorem cosetRepOf_coe_subgroup (N : Subgroup (Equiv.Perm Ω)) :
    cosetRepOf (N : Set (Equiv.Perm Ω)) = 1 :=
  cosetRepOf_eq_one N.one_mem

/-- §11.1, **Remark 11.1.4, the alignment step**: the instance with respect to a coset `K`,
rewritten with respect to the group `σ⁻¹K` and the shifted string `y^{σ⁻¹}`, where `σ` is a
member of `K`. -/
noncomputable def alignInst (I : SIInstance Ω A) : SIInstance Ω A :=
  ⟨(cosetRepOf I.K)⁻¹ • I.K, I.Δ, I.x, strAct I.y (cosetRepOf I.K)⁻¹⟩

@[simp] theorem alignInst_Δ (I : SIInstance Ω A) : (alignInst I).Δ = I.Δ := rfl

@[simp] theorem alignInst_x (I : SIInstance Ω A) : (alignInst I).x = I.x := rfl

@[simp] theorem alignInst_K (I : SIInstance Ω A) :
    (alignInst I).K = (cosetRepOf I.K)⁻¹ • I.K := rfl

/-- **An aligned instance is its own alignment**: when the candidate set contains `1` the
representative is `1` (`Babai.cosetRepOf_eq_one`) and nothing moves. -/
theorem alignInst_eq_self {I : SIInstance Ω A} (h : (1 : Equiv.Perm Ω) ∈ I.K) :
    alignInst I = I := by
  have hstr : strAct I.y (cosetRepOf I.K)⁻¹ = I.y := by
    rw [cosetRepOf_eq_one h]
    funext u
    simp [strAct]
  have hK : (cosetRepOf I.K)⁻¹ • I.K = I.K := by
    rw [cosetRepOf_eq_one h, inv_one, one_smul]
  rw [alignInst, hstr, hK]

/-- A **group instance is already aligned**: its candidate set is a subgroup, so it contains
`1`. -/
theorem alignInst_eq_self_of_isGroupInstance {I : SIInstance Ω A}
    (h : IsGroupInstance I) : alignInst I = I := by
  obtain ⟨K, hK, -⟩ := h
  exact alignInst_eq_self (by rw [hK]; exact K.one_mem)

/-- The candidate set of an aligned instance contains `1`, as soon as the original one is
nonempty: `1 = σ⁻¹σ` for the representative `σ`. -/
theorem one_mem_K_alignInst {I : SIInstance Ω A} (h : I.K.Nonempty) :
    (1 : Equiv.Perm Ω) ∈ (alignInst I).K :=
  ⟨cosetRepOf I.K, cosetRepOf_mem h, by simp⟩

/-- **The alignment step of Remark 11.1.4 is idempotent.**  Aligning an aligned instance
does nothing, because the aligned candidate set contains `1`. -/
theorem alignInst_alignInst {I : SIInstance Ω A} (h : I.K.Nonempty) :
    alignInst (alignInst I) = alignInst I :=
  alignInst_eq_self (one_mem_K_alignInst h)

@[simp] theorem windowSize_alignInst (I : SIInstance Ω A) :
    (alignInst I).windowSize = I.windowSize := rfl

/-- §11.1, **Eq. (59)**: the answer to the aligned instance, translated back by `σ`, is the
answer to the original instance. -/
theorem smul_answer_alignInst (I : SIInstance Ω A) :
    (cosetRepOf I.K) • (alignInst I).answer = I.answer := by
  show (cosetRepOf I.K) • wIso I.Δ ((cosetRepOf I.K)⁻¹ • I.K) I.x
      (strAct I.y (cosetRepOf I.K)⁻¹) = wIso I.Δ I.K I.x I.y
  rw [← wIso_smul, smul_inv_smul]

/-- The alignment step as a one-call reduction: ask the aligned instance and translate the
answer back. -/
noncomputable def alignStep (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  .call (alignInst I) fun a => .done ((cosetRepOf I.K) • a)

theorem run_alignStep (I : SIInstance Ω A) : (alignStep I).run = I.answer := by
  rw [alignStep, SIReduction.run_call, SIReduction.run_done, smul_answer_alignInst]

theorem calls_alignStep (I : SIInstance Ω A) : (alignStep I).calls = [alignInst I] := rfl

/-- **Every call aligned**: the reduction with the alignment step of Remark 11.1.4 put in
front of each of its calls. -/
noncomputable def SIReduction.alignCalls (R : SIReduction Ω A α) : SIReduction Ω A α :=
  R.expand alignStep

/-- Alignment does not change the value computed (Eq. (59)). -/
@[simp] theorem run_alignCalls (R : SIReduction Ω A α) : R.alignCalls.run = R.run :=
  SIReduction.run_expand run_alignStep R

/-- The calls of the aligned reduction are the old calls, aligned. -/
theorem calls_alignCalls (R : SIReduction Ω A α) :
    R.alignCalls.calls = R.calls.map alignInst :=
  SIReduction.calls_expand_eq_map run_alignStep calls_alignStep R

theorem calls_length_alignCalls (R : SIReduction Ω A α) :
    R.alignCalls.calls.length = R.calls.length := by
  rw [calls_alignCalls, List.length_map]

end Align

/-! ### Coset instances become group instances -/

section CosetInstance

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]
  {G : Subgroup (Equiv.Perm Ω)}

/-- An instance **with respect to a coset of a subgroup of `G`**, with an invariant window:
the shape every call of §13.1 has.  `N` is `ker ψ̄_T`, `σ` is the representative of line 04d
(or its product with a candidate of line 04c0), and the window is an orbit of `N`. -/
def IsCosetInstance (G : Subgroup (Equiv.Perm Ω)) (I : SIInstance Ω A) : Prop :=
  ∃ (N : Subgroup (Equiv.Perm Ω)) (σ : Equiv.Perm Ω), N ≤ G ∧ σ ∈ G ∧
    I.K = σ • (N : Set (Equiv.Perm Ω)) ∧ IsInvariant N I.Δ

/-- The instances of §13.1 are coset instances: group, representative, window. -/
theorem isCosetInstance_mk {N : Subgroup (Equiv.Perm Ω)} {σ : Equiv.Perm Ω} {Δ : Set Ω}
    {x y : Ω → A} (hN : N ≤ G) (hσ : σ ∈ G) (hΔ : IsInvariant N Δ) :
    IsCosetInstance G (⟨σ • (N : Set (Equiv.Perm Ω)), Δ, x, y⟩ : SIInstance Ω A) :=
  ⟨N, σ, hN, hσ, rfl, hΔ⟩

/-- The candidate set of a coset instance is the group itself, after alignment. -/
theorem K_alignInst_of_isCosetInstance {I : SIInstance Ω A} (h : IsCosetInstance G I) :
    ∃ N : Subgroup (Equiv.Perm Ω), N ≤ G ∧
      (alignInst I).K = (N : Set (Equiv.Perm Ω)) ∧ IsInvariant N I.Δ := by
  obtain ⟨N, σ, hNG, hσG, hK, hinv⟩ := h
  have hne : I.K.Nonempty := ⟨σ, by rw [hK]; exact ⟨1, one_mem N, by simp⟩⟩
  have hmem : cosetRepOf I.K ∈ I.K := cosetRepOf_mem hne
  rw [hK] at hmem
  obtain ⟨ν, hν, hrep⟩ := hmem
  refine ⟨N, hNG, ?_, hinv⟩
  show (cosetRepOf I.K)⁻¹ • I.K = (N : Set (Equiv.Perm Ω))
  rw [hK, ← hrep, smul_smul]
  show ((σ * ν)⁻¹ * σ) • (N : Set (Equiv.Perm Ω)) = (N : Set (Equiv.Perm Ω))
  rw [show (σ * ν)⁻¹ * σ = ν⁻¹ by group]
  exact smul_coe_set (inv_mem hν)

/-- **The aligned call is a group instance** (`Babai.IsGroupInstance`): its candidate set is
the group `N` of Eq. (69), and its window is a union of orbits of `N`. -/
theorem isGroupInstance_alignInst {I : SIInstance Ω A} (h : IsCosetInstance G I) :
    IsGroupInstance (alignInst I) := by
  obtain ⟨N, -, hK, hinv⟩ := K_alignInst_of_isCosetInstance h
  exact ⟨N, hK, hinv⟩

/-- **The aligned call stays inside the ambient group**: its candidate set is `N ≤ G`. -/
theorem K_alignInst_subset {I : SIInstance Ω A} (h : IsCosetInstance G I) :
    (alignInst I).K ⊆ (G : Set (Equiv.Perm Ω)) := by
  obtain ⟨N, hNG, hK, -⟩ := K_alignInst_of_isCosetInstance h
  rw [hK]
  exact fun σ hσ => hNG hσ

end CosetInstance

/-! ### Every call of §13.1 is a coset instance

The chain is the one the procedures are built in: the instances of one round of Procedure
Recompute `H(W)` (Eq. (69)), the comparison instances of lines 04c0–04f2, the while loop of
each, and then the two routines. -/

section Chain

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- The loop invariant `H(W) ≤ G_T` ends inside `G`: `G_T` is a subgroup of `G`. -/
theorem bigGT_le_ambient (ϕ : G →* Equiv.Perm Γ) (T : Set Γ) : bigGT ϕ T ≤ G :=
  fun _ h => stabIn_le_top h

/-- The kernel `N = ker ψ̄_T` of Eq. (69) is a subgroup of `G`. -/
theorem kerN_le_ambient (s : Stage ϕ x T) : kerN s ≤ G :=
  le_trans (kerN_le s) (le_trans s.le (bigGT_le_ambient ϕ T))

theorem stage_H_le_ambient (s : Stage ϕ x T) : (s.H : Subgroup (Equiv.Perm Ω)) ≤ G :=
  le_trans s.le (bigGT_le_ambient ϕ T)

/-- Every call of one round of Procedure Recompute `H(W)` is an instance with respect to a
coset `Nσ` of `N = ker ψ̄_T`, with an orbit of `N` for a window. -/
theorem isCosetInstance_calls_recomputeReduction (s : Stage ϕ x T)
    (lift : imgOn ϕ T s.le → Equiv.Perm Ω) (hlift : ∀ sb, lift sb ∈ s.H)
    {I : SIInstance Ω Λ} (hI : I ∈ (recomputeReduction (Λ := Λ) (x := x) s lift).calls) :
    IsCosetInstance G I := by
  rw [calls_recomputeReduction, List.mem_flatMap] at hI
  obtain ⟨l, hl, hIl⟩ := hI
  rw [roundLists, List.mem_map] at hl
  obtain ⟨sb, -, rfl⟩ := hl
  obtain ⟨u, -, rfl⟩ := (mem_roundInstances_iff s _).1 hIl
  exact isCosetInstance_mk (kerN_le_ambient s) (stage_H_le_ambient s (hlift sb))
    (isInvariant_orbit _ u)

theorem comparisonLift_mem (s : Stage ϕ x T) (sb : imgOn ϕ T s.le) :
    comparisonLift s sb ∈ s.H := (comparisonLift_spec s sb).choose

theorem certLift_mem (s : Stage ϕ x T) (sb : imgOn ϕ T s.le) :
    certLift s sb ∈ s.H := (certLift_spec s sb).choose

/-- Every comparison call of lines 04c0–04f2 is an instance with respect to a coset
`((πσ)N)` of `N`. -/
theorem isCosetInstance_calls_comparisonRound (s : Stage ϕ x T) {π : Equiv.Perm Ω}
    (hπ : π ∈ G) (y : Ω → Λ) {I : SIInstance Ω Λ}
    (hI : I ∈ (comparisonRound s π y).calls) : IsCosetInstance G I := by
  rw [calls_comparisonRound, List.mem_flatMap] at hI
  obtain ⟨sb, -, hI⟩ := hI
  obtain ⟨u, -, rfl⟩ := (mem_comparisonInstances s _ y).1 hI
  exact isCosetInstance_mk (kerN_le_ambient s)
    (G.mul_mem hπ (stage_H_le_ambient s (comparisonLift_mem s sb)))
    (isInvariant_orbit _ u)

theorem isCosetInstance_calls_updateComparison (s : Stage ϕ x T) (y : Ω → Λ)
    {Q : Set (Equiv.Perm Ω)} (hQ : Q ⊆ (G : Set (Equiv.Perm Ω))) {I : SIInstance Ω Λ}
    (hI : I ∈ (updateComparison s y Q).calls) : IsCosetInstance G I := by
  unfold updateComparison at hI
  split at hI
  · rename_i h
    exact isCosetInstance_calls_comparisonRound s (hQ h.some_mem) y hI
  · simp at hI

/-- The initial coset of line 01 lies in `G`. -/
theorem smul_bigGT_subset {σ₀ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G) (T : Set Γ) :
    σ₀ • (bigGT ϕ T : Set (Equiv.Perm Ω)) ⊆ (G : Set (Equiv.Perm Ω)) := by
  rintro τ ⟨κ, hκ, rfl⟩
  exact G.mul_mem hσ₀ (bigGT_le_ambient ϕ T hκ)

/-- Every candidate the comparison loop carries lies in `G`. -/
theorem pairedQ_subset_ambient (y : Ω → Λ) {σ₀ : Equiv.Perm Ω} (hσ₀ : σ₀ ∈ G) (i : ℕ) :
    pairedQ ϕ x y T σ₀ i ⊆ (G : Set (Equiv.Perm Ω)) :=
  le_trans (wIso_subset _ _ _ _) (smul_bigGT_subset hσ₀ T)

/-- Every call of the paired comparison loop is a coset instance. -/
theorem isCosetInstance_calls_pairedLoopReduction (y : Ω → Λ) {σ₀ : Equiv.Perm Ω}
    (hσ₀ : σ₀ ∈ G) : ∀ (i : ℕ) {I : SIInstance Ω Λ},
      I ∈ (pairedLoopReduction ϕ x T y σ₀ i).calls → IsCosetInstance G I := by
  intro i
  induction i with
  | zero => intro I hI; simp [pairedLoopReduction] at hI
  | succ i ih =>
    intro I hI
    rw [pairedLoopReduction, SIReduction.calls_bind, List.mem_append] at hI
    rcases hI with hI | hI
    · exact ih hI
    · have hrun := run_pairedLoopReduction (ϕ := ϕ) (x := x) (T := T) y σ₀ hσ₀ i
      cases hp : (pairedLoopReduction ϕ x T y σ₀ i).run with
      | none => rw [hp] at hI; simp at hI
      | some p =>
        have hQ : p.2.2 ⊆ (G : Set (Equiv.Perm Ω)) := by
          rw [hp] at hrun
          unfold comparisonState at hrun
          split at hrun
          · rw [Option.some_inj] at hrun
            rw [hrun]
            exact pairedQ_subset_ambient y hσ₀ i
          · exact absurd hrun (by simp)
        rw [hp] at hI
        simp only [SIReduction.calls_bind, SIReduction.calls_done, List.append_nil,
          List.mem_append] at hI
        rcases hI with hI | hI
        · exact isCosetInstance_calls_recomputeReduction _ _
            (comparisonLift_mem (stages ϕ x T i)) hI
        · exact isCosetInstance_calls_updateComparison _ y hQ hI

/-- **Every call of Prop. 13.1.11's reduction is a coset instance.** -/
theorem isCosetInstance_calls_compareReduction (y : Ω → Λ) (T' : Set Γ)
    {I : SIInstance Ω Λ} (hI : I ∈ (compareReduction ϕ x T y T').calls) :
    IsCosetInstance G I := by
  unfold compareReduction at hI
  split at hI
  · rename_i h
    rw [pairedComparisonReduction, SIReduction.calls_bind] at hI
    simp only [SIReduction.calls_done, List.append_nil] at hI
    exact isCosetInstance_calls_pairedLoopReduction y h.choose.property _ hI
  · simp at hI

/-- Every call of the while loop of Procedure LocalCertificates is a coset instance. -/
theorem isCosetInstance_calls_loopReduction
    (lift : ∀ i : ℕ, imgOn ϕ T (stages ϕ x T i).le → Equiv.Perm Ω)
    (hmem : ∀ (i : ℕ) (sb : imgOn ϕ T (stages ϕ x T i).le), lift i sb ∈ (stages ϕ x T i).H)
    (hlift : ∀ (i : ℕ) (sb : imgOn ϕ T (stages ϕ x T i).le),
      ∃ h : lift i sb ∈ (stages ϕ x T i).H,
        psiOn ϕ T (stages ϕ x T i).le ⟨lift i sb, h⟩ = (sb : Equiv.Perm T)) :
    ∀ (i : ℕ) {I : SIInstance Ω Λ},
      I ∈ (loopReduction ϕ x T lift i (Λ := Λ)).calls → IsCosetInstance G I := by
  intro i
  induction i with
  | zero => intro I hI; simp [loopReduction] at hI
  | succ i ih =>
    intro I hI
    rw [calls_loopReduction lift hlift i, List.mem_append] at hI
    rcases hI with hI | hI
    · exact ih hI
    · exact isCosetInstance_calls_recomputeReduction _ _ (hmem i) hI

/-- **Every call of Procedure LocalCertificates is a coset instance.** -/
theorem isCosetInstance_calls_localCertRound {I : SIInstance Ω Λ}
    (hI : I ∈ (localCertRound ϕ x T (Λ := Λ)).calls) : IsCosetInstance G I := by
  rw [localCertRound, localCertReduction, SIReduction.calls_bind] at hI
  simp only [SIReduction.calls_done, List.append_nil] at hI
  exact isCosetInstance_calls_loopReduction _ (fun i => certLift_mem (stages ϕ x T i))
    (fun i => certLift_spec (stages ϕ x T i)) _ hI

end Chain

/-! ### The two phases of §13.2 -/

section Phases

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ} {x y : Ω → Λ} {t : ℕ}

/-- **Every call of the certificate phase is a coset instance.** -/
theorem isCosetInstance_calls_certPhase {I : SIInstance Ω Λ}
    (hI : I ∈ (certPhase ϕ x y t (Λ := Λ)).calls) : IsCosetInstance G I := by
  obtain ⟨S, hS, hIS⟩ := SIReduction.mem_calls_sequence hI
  rw [List.mem_append] at hS
  have key : ∀ z : Ω → Λ, S ∈ (testSetList Γ t).map (fun T => certRun ϕ z T (Λ := Λ)) →
      IsCosetInstance G I := by
    intro z hmem
    obtain ⟨T, -, rfl⟩ := List.mem_map.1 hmem
    rw [calls_certRun] at hIS
    exact isCosetInstance_calls_localCertRound hIS
  rcases hS with hS | hS
  · exact key x hS
  · exact key y hS

/-- **Every call of the comparison phase is a coset instance.** -/
theorem isCosetInstance_calls_comparePhase {I : SIInstance Ω Λ}
    (hI : I ∈ (comparePhase ϕ x y t (Λ := Λ)).calls) : IsCosetInstance G I := by
  obtain ⟨S, hS, hIS⟩ := SIReduction.mem_calls_sequence hI
  rw [List.mem_append] at hS
  have key : ∀ z : Ω → Λ, S ∈ ((testSetList Γ t).flatMap fun T =>
      (testSetList Γ t).map fun T' => compareReduction ϕ x T z T') →
      IsCosetInstance G I := by
    intro z hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨T, -, hmem'⟩ := hmem
    obtain ⟨T', -, rfl⟩ := List.mem_map.1 hmem'
    exact isCosetInstance_calls_compareReduction z T' hIS
  rcases hS with hS | hS
  · exact key x hS
  · exact key y hS

end Phases

/-! ### Procedure AggregateCertificates as a round of group instances -/

section Round

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

variable (ϕ : G →* Equiv.Perm Γ) (x y : Ω → Λ) (t : ℕ)

/-- §13.2, **Procedure AggregateCertificates as a round of the recursion, aligned**: the
certificate runs, then the comparison runs, then the reduction `R` the Master Algorithm runs
on the aggregated objects — with the alignment step of Remark 11.1.4 in front of every call
of the two phases, so that every call is made with respect to a group. -/
noncomputable def alignedAggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    SIReduction Ω Λ α :=
  (certPhase ϕ x y t (Λ := Λ)).alignCalls.bind fun _ =>
    (comparePhase ϕ x y t (Λ := Λ)).alignCalls.bind fun _ => R

variable {ϕ x y t}

/-- **The round answers what the last part answers**: the phases produce the objects `R` is
written against, and alignment changes no value (Eq. (59)). -/
@[simp] theorem run_alignedAggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    (alignedAggregateRound ϕ x y t R).run = R.run := by
  rw [alignedAggregateRound, SIReduction.run_bind, SIReduction.run_bind]

/-- **The calls of the round**: the aligned calls of the two phases, then the calls of the
last part. -/
theorem calls_alignedAggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    (alignedAggregateRound ϕ x y t R).calls
      = (certPhase ϕ x y t (Λ := Λ)).calls.map alignInst
        ++ ((comparePhase ϕ x y t (Λ := Λ)).calls.map alignInst ++ R.calls) := by
  rw [alignedAggregateRound, SIReduction.calls_bind, SIReduction.calls_bind,
    calls_alignCalls, calls_alignCalls]

/-- **Every call of the round is either a call of the two phases** — with respect to a
subgroup of `G`, a group instance, and on a window of at most `n/t` points — **or a call of
the last part.** -/
theorem mem_calls_alignedAggregateRound {α : Type w} (R : SIReduction Ω Λ α) (h5 : 5 ≤ t)
    {J : SIInstance Ω Λ} (hJ : J ∈ (alignedAggregateRound ϕ x y t R).calls) :
    (J.K ⊆ (G : Set (Equiv.Perm Ω)) ∧ IsGroupInstance J ∧ t * J.Δ.ncard ≤ Nat.card Ω) ∨
      J ∈ R.calls := by
  rw [calls_alignedAggregateRound, List.mem_append, List.mem_append] at hJ
  rcases hJ with hJ | hJ | hJ
  · obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hJ
    have hc := isCosetInstance_calls_certPhase (G := G) hI
    refine Or.inl ⟨K_alignInst_subset hc, isGroupInstance_alignInst hc, ?_⟩
    rw [alignInst_Δ]
    exact window_calls_certPhase h5 hI
  · obtain ⟨I, hI, rfl⟩ := List.mem_map.1 hJ
    have hc := isCosetInstance_calls_comparePhase (G := G) hI
    refine Or.inl ⟨K_alignInst_subset hc, isGroupInstance_alignInst hc, ?_⟩
    rw [alignInst_Δ]
    exact window_calls_comparePhase h5 hI
  · exact Or.inr hJ

/-- **The number of calls of the round**: the calls of the last part, plus the
`Babai.aggregateRoundCost` calls of the two phases. -/
theorem calls_length_alignedAggregateRound {α : Type w} (R : SIReduction Ω Λ α) (h5 : 5 ≤ t) :
    (alignedAggregateRound ϕ x y t R).calls.length
      ≤ R.calls.length + aggregateRoundCost (Fintype.card Γ) t (Nat.card Ω) := by
  rw [calls_alignedAggregateRound, List.length_append, List.length_append, List.length_map,
    List.length_map]
  have h := calls_length_phases_le (ϕ := ϕ) (x := x) (y := y) (t := t) (Λ := Λ) h5
  omega

end Round

/-! ### The cost of the round is monotone in the number of points of `Γ` -/

section CostMono

/-- `C(m,t)` grows with `m`, so the allowance of the round does. -/
theorem aggregateRoundCost_mono_left {m m' t n : ℕ} (h : m ≤ m') :
    aggregateRoundCost m t n ≤ aggregateRoundCost m' t n := by
  have hc : m.choose t ≤ m'.choose t := Nat.choose_le_choose t h
  rw [aggregateRoundCost, aggregateRoundCost]
  exact Nat.add_le_add
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc))
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)))

end CostMono

end Babai
