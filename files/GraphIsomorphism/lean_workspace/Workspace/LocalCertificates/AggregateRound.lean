/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 13.2: Procedure AggregateCertificates as a round of the recursion — the calls of
Theorem 13.1.3 and of Prop. 13.1.11 bound in front of the work that follows.
-/
import Workspace.LocalCertificates.Aggregate
import Workspace.LocalCertificates.Calls
import Workspace.LocalCertificates.CompareCanonical

/-!
# §13.2 AggregateCertificates as a round

> Run the LocalCertificates routine for both inputs `x`, `y` and all test sets `T`.  Run
> the CompareLocalCertificates routine for all pairs `((x,T),(x',T'))` where `x` is fixed,
> `x' ∈ {x,y}` … (a total of `2·C(m,t)²` runs).

Those runs are String Isomorphism instances, answered by recursion, so they belong to the
recursion tree.  This file puts them there.  `Babai.aggregateRound` is the round: the
certificate runs first, then the comparison runs, then whatever the Master Algorithm does
with the aggregated objects.  By `Babai.SIReduction.run_bind` the value of the round is the
value of that last part, so correctness of the whole is the correctness of the last part;
by `Babai.SIReduction.calls_bind` its calls are the three lists, one after the other.

**The counts.**  Theorem 13.1.3 charges `t!n²` calls per certificate run, on windows of at
most `n/t` points (`Babai.calls_localCertRound`); there are `2·C(m,t)` runs.
Prop. 13.1.11 charges `2·t!n²` per comparison run, on windows of at most `n/t` points
(`Babai.calls_compareReduction`); there are `2·C(m,t)²` runs.  So the round costs

> `2·C(m,t)·t!n² + 2·C(m,t)²·(2·t!n²)`

calls, all on windows of at most `n/t` points — `Babai.aggregateRoundCost`.

**The progress.**  With `t ≥ 5` a window of at most `n/t` points is at most `4n/5`, which is
the window alternative of `Babai.MakesProgress`
(`Babai.five_mul_ncard_le_of_window_le`).  These calls carry no Johnson hint, which is
right: the paper recurses on them from line 1 of the Master Algorithm.
-/

namespace Babai

open MulAction Equiv Equiv.Perm
open scoped Classical

universe u v w

/-! ### The test sets -/

section TestSets

variable (Γ : Type*) [Fintype Γ] [DecidableEq Γ]

/-- §13.2: **all test sets**, the `t`-subsets of `Γ`, as a list.  Its length is `C(m,t)`. -/
noncomputable def testSetList (t : ℕ) : List (Set Γ) :=
  List.map (fun S : binom Γ t => ((S : Finset Γ) : Set Γ))
    (Finset.univ : Finset (binom Γ t)).toList

variable {Γ}

theorem length_testSetList (t : ℕ) :
    (testSetList Γ t).length = (Fintype.card Γ).choose t := by
  classical
  rw [testSetList, List.length_map, Finset.length_toList, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_binom, Nat.card_eq_fintype_card]

theorem ncard_of_mem_testSetList {t : ℕ} {T : Set Γ} (h : T ∈ testSetList Γ t) :
    T.ncard = t := by
  rw [testSetList, List.mem_map] at h
  obtain ⟨S, -, rfl⟩ := h
  rw [Set.ncard_coe_finset]
  exact S.2

end TestSets

/-! ### The two phases -/

section Phases

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)}

variable (ϕ : G →* Equiv.Perm Γ) (x y : Ω → Λ) (t : ℕ)

/-- One certificate run, with the group `M(T) ≤ S(T)` of line 10 dropped, so that the runs
for different test sets have one type.  What §13.2 aggregates is `K(T)`, the second
component. -/
noncomputable def certRun (T : Set Γ) :
    SIReduction Ω Λ (Set Ω × Subgroup (Equiv.Perm Ω)) :=
  (localCertRound ϕ x T (Λ := Λ)).bind fun p => .done (p.1, p.2.1)

variable {ϕ x y t}

theorem run_certRun (T : Set Γ) :
    (certRun ϕ x T (Λ := Λ)).run = (windowOut ϕ x T, certK ϕ x T) := by
  rw [certRun, SIReduction.run_bind, run_localCertRound, SIReduction.run_done]

theorem calls_certRun (T : Set Γ) :
    (certRun ϕ x T (Λ := Λ)).calls = (localCertRound ϕ x T (Λ := Λ)).calls := by
  rw [certRun, SIReduction.calls_bind, SIReduction.calls_done, List.append_nil]

/-- **Prop. 13.1.11**, the cost clause, with no hypothesis on the strings: the comparison
run makes at most `2·t!n²` calls, on windows of at most `n/t` points.  The factor two is
the recorded one; see the corrected paper Prop. 13.1.11 entry. -/
theorem calls_compareReduction {T T' : Set Γ} (h5 : 5 ≤ T.ncard) :
    (compareReduction ϕ x T y T').calls.length
        ≤ 2 * Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      ∀ I ∈ (compareReduction ϕ x T y T').calls, T.ncard * I.Δ.ncard ≤ Nat.card Ω := by
  unfold compareReduction
  split
  · exact proposition_13_1_11_paired_calls y h5 _
  · simp

variable (ϕ x y t)

/-- §13.2, **the certificate phase**: the LocalCertificates routine for both input strings
and all test sets. -/
noncomputable def certPhase : SIReduction Ω Λ (List (Set Ω × Subgroup (Equiv.Perm Ω))) :=
  SIReduction.sequence
    ((testSetList Γ t).map (fun T => certRun ϕ x T (Λ := Λ)) ++
      (testSetList Γ t).map fun T => certRun ϕ y T (Λ := Λ))

/-- §13.2, **the comparison phase**: the CompareLocalCertificates routine for all pairs
`((x,T),(x',T'))` with `x' ∈ {x,y}` — `2·C(m,t)²` runs. -/
noncomputable def comparePhase : SIReduction Ω Λ (List (Set (Equiv.Perm Ω))) :=
  SIReduction.sequence
    (((testSetList Γ t).flatMap fun T =>
        (testSetList Γ t).map fun T' => compareReduction ϕ x T x T') ++
      ((testSetList Γ t).flatMap fun T =>
        (testSetList Γ t).map fun T' => compareReduction ϕ x T y T'))

/-- §13.2, **Procedure AggregateCertificates as a round**: the certificate runs, then the
comparison runs, then the reduction `R` that the Master Algorithm runs on the aggregated
objects. -/
noncomputable def aggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    SIReduction Ω Λ α :=
  (certPhase ϕ x y t).bind fun _ => (comparePhase ϕ x y t).bind fun _ => R

variable {ϕ x y t}

/-- **The round answers what the last part answers.**  The two phases produce the objects
§13.2 aggregates — `Babai.run_certRun` and `Babai.run_compareReduction` say which — and
those objects are already what `R` is written against, so binding them in front changes no
value. -/
@[simp] theorem run_aggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    (aggregateRound ϕ x y t R).run = R.run := by
  rw [aggregateRound, SIReduction.run_bind, SIReduction.run_bind]

/-- **The calls of the round** are the calls of the two phases followed by the calls of the
last part. -/
theorem calls_aggregateRound {α : Type w} (R : SIReduction Ω Λ α) :
    (aggregateRound ϕ x y t R).calls
      = (certPhase ϕ x y t (Λ := Λ)).calls
        ++ ((comparePhase ϕ x y t (Λ := Λ)).calls ++ R.calls) := by
  rw [aggregateRound, SIReduction.calls_bind, SIReduction.calls_bind]

end Phases

/-! ### The cost of the round -/

section Cost

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Equiv.Perm Ω)} {ϕ : G →* Equiv.Perm Γ} {x y : Ω → Λ} {t : ℕ}

/-- §13.2, **the number of String Isomorphism instances Procedure AggregateCertificates
produces**: `2·C(m,t)` certificate runs at `t!n²` calls each (Theorem 13.1.3), and
`2·C(m,t)²` comparison runs at `2·t!n²` calls each (Prop. 13.1.11). -/
def aggregateRoundCost (m t n : ℕ) : ℕ :=
  2 * m.choose t * (Nat.factorial t * n ^ 2) +
    2 * (m.choose t) ^ 2 * (2 * Nat.factorial t * n ^ 2)

/-- Every call of the certificate phase has a window of at most `n/t` points. -/
theorem window_calls_certPhase (h5 : 5 ≤ t) {I : SIInstance Ω Λ}
    (hI : I ∈ (certPhase ϕ x y t (Λ := Λ)).calls) : t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨S, hS, hIS⟩ := SIReduction.mem_calls_sequence hI
  rw [List.mem_append] at hS
  have key : ∀ z : Ω → Λ, S ∈ (testSetList Γ t).map (fun T => certRun ϕ z T (Λ := Λ)) →
      t * I.Δ.ncard ≤ Nat.card Ω := by
    intro z hmem
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hmem
    have hnc : T.ncard = t := ncard_of_mem_testSetList hT
    rw [calls_certRun] at hIS
    have h := (calls_localCertRound (T := T) (x := z) (ϕ := ϕ) (Λ := Λ)
      (by rw [hnc]; exact h5)).2 I hIS
    rwa [hnc] at h
  rcases hS with hS | hS
  · exact key x hS
  · exact key y hS

/-- Every call of the comparison phase has a window of at most `n/t` points. -/
theorem window_calls_comparePhase (h5 : 5 ≤ t) {I : SIInstance Ω Λ}
    (hI : I ∈ (comparePhase ϕ x y t (Λ := Λ)).calls) : t * I.Δ.ncard ≤ Nat.card Ω := by
  obtain ⟨S, hS, hIS⟩ := SIReduction.mem_calls_sequence hI
  rw [List.mem_append] at hS
  have key : ∀ z : Ω → Λ, S ∈ ((testSetList Γ t).flatMap fun T =>
      (testSetList Γ t).map fun T' => compareReduction ϕ x T z T') →
      t * I.Δ.ncard ≤ Nat.card Ω := by
    intro z hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨T, hT, hmem'⟩ := hmem
    obtain ⟨T', -, rfl⟩ := List.mem_map.1 hmem'
    have hnc : T.ncard = t := ncard_of_mem_testSetList hT
    have h := (calls_compareReduction (ϕ := ϕ) (x := x) (y := z) (T := T) (T' := T')
      (by rw [hnc]; exact h5)).2 I hIS
    rwa [hnc] at h
  rcases hS with hS | hS
  · exact key x hS
  · exact key y hS

/-- **The round makes at most `Babai.aggregateRoundCost` calls of its own**, on top of the
calls of the last part. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (g : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (g a).length ≤ k) : (l.flatMap g).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : (g a).length ≤ k := h a List.mem_cons_self
    have h2 : (rest.flatMap g).length ≤ rest.length * k :=
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    calc (g a).length + (rest.flatMap g).length ≤ k + rest.length * k :=
          Nat.add_le_add h1 h2
      _ = (rest.length + 1) * k := by ring

/-- **The round makes at most `Babai.aggregateRoundCost` calls of its own**, on top of the
calls of the last part. -/
theorem calls_length_phases_le (h5 : 5 ≤ t) :
    (certPhase ϕ x y t (Λ := Λ)).calls.length
        + (comparePhase ϕ x y t (Λ := Λ)).calls.length
      ≤ aggregateRoundCost (Fintype.card Γ) t (Nat.card Ω) := by
  classical
  have hcert : (certPhase ϕ x y t (Λ := Λ)).calls.length
      ≤ 2 * (Fintype.card Γ).choose t * (Nat.factorial t * (Nat.card Ω) ^ 2) := by
    rw [certPhase]
    refine le_trans (SIReduction.calls_length_sequence_le
      (k := Nat.factorial t * (Nat.card Ω) ^ 2) ?_) ?_
    · intro S hS
      rw [List.mem_append] at hS
      have key : ∀ z : Ω → Λ,
          S ∈ (testSetList Γ t).map (fun T => certRun ϕ z T (Λ := Λ)) →
          S.calls.length ≤ Nat.factorial t * (Nat.card Ω) ^ 2 := by
        intro z hmem
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hmem
        have hnc : T.ncard = t := ncard_of_mem_testSetList hT
        have h := (calls_localCertRound (T := T) (x := z) (ϕ := ϕ) (Λ := Λ)
          (by rw [hnc]; exact h5)).1
        rw [hnc] at h
        rw [calls_certRun]
        exact h
      rcases hS with hS | hS
      · exact key x hS
      · exact key y hS
    · rw [List.length_append, List.length_map, List.length_map, length_testSetList]
      exact Nat.mul_le_mul_right _ (by omega)
  have hcmp : (comparePhase ϕ x y t (Λ := Λ)).calls.length
      ≤ 2 * ((Fintype.card Γ).choose t) ^ 2 *
        (2 * Nat.factorial t * (Nat.card Ω) ^ 2) := by
    rw [comparePhase]
    refine le_trans (SIReduction.calls_length_sequence_le
      (k := 2 * Nat.factorial t * (Nat.card Ω) ^ 2) ?_) ?_
    · intro S hS
      rw [List.mem_append] at hS
      have key : ∀ z : Ω → Λ, S ∈ ((testSetList Γ t).flatMap fun T =>
          (testSetList Γ t).map fun T' => compareReduction ϕ x T z T') →
          S.calls.length ≤ 2 * Nat.factorial t * (Nat.card Ω) ^ 2 := by
        intro z hmem
        rw [List.mem_flatMap] at hmem
        obtain ⟨T, hT, hmem'⟩ := hmem
        obtain ⟨T', -, rfl⟩ := List.mem_map.1 hmem'
        have hnc : T.ncard = t := ncard_of_mem_testSetList hT
        have h := (calls_compareReduction (ϕ := ϕ) (x := x) (y := z) (T := T) (T' := T')
          (by rw [hnc]; exact h5)).1
        rwa [hnc] at h
      rcases hS with hS | hS
      · exact key x hS
      · exact key y hS
    · have hlen : ∀ z : Ω → Λ, ((testSetList Γ t).flatMap fun T =>
          (testSetList Γ t).map fun T' => compareReduction ϕ x T z T').length
          ≤ (Fintype.card Γ).choose t * (Fintype.card Γ).choose t := by
        intro z
        refine le_trans (length_flatMap_le _ _ ((Fintype.card Γ).choose t) ?_) ?_
        · intro T _
          rw [List.length_map, length_testSetList]
        · rw [length_testSetList]
      have h2 := hlen x
      have h3 := hlen y
      rw [List.length_append]
      refine le_trans (Nat.mul_le_mul_right _ (Nat.add_le_add h2 h3)) ?_
      exact le_of_eq (by ring)
  rw [aggregateRoundCost]
  exact Nat.add_le_add hcert hcmp

end Cost

end Babai
