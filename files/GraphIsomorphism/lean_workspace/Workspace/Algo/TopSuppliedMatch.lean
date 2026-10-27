import Workspace.Algo.TopSuppliedTail

/-! # The complete supplied top-action-3 phase

The ordered lifting fold and the kernel continuation form one raw round.
Coset hulls only change the representation of the reconstructed answer:
the paper's final answer is already empty or a coset. The comparison below
proves the ordered calls and the returned value before transporting the
complete phase match to `cosetTopAction3With`.
-/

namespace Algo

open Babai Equiv
open scoped Pointwise Classical

noncomputable def topcsReduction (n : ℕ) (P : TopcsInput) :
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n)))) :=
  (topcsLiftFold (decStrN n (topcsX P)) (decStrN n (topcsX P))
    ((topcsWins P).map (winSet n)) ((topcsTests P).map (decCoset n)) (some ∅)).bind
    (topcsTail n P)

theorem topcsPhase_reduction {n : ℕ} {P : TopcsInput} (bound : ℕ → ℕ)
    (solve : RawWinSI → RawCoset) (hx : (topcsX P).length = n)
    (hw : 0 < (topcsWins P).length) (ht : 0 < topcsCount P)
    (hall : ∀ c ∈ topcsTests P, (decCoset n c).Nonempty)
    (hK : (decCoset n (topcsKernel P)).Nonempty)
    (hO : (decCoset n (topcsOdd P)).Nonempty) :
    PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
      (topcsJobs P * (topcsWins P).length) 0 (topcsInit (P, none))
      (topcsReduction n P) (TopcsDone n P) := by
  have h0 := topcsPhase_tests bound solve hx hw hall (topcsTests P) 0 (by omega) rfl
    (some ∅) ∅ ∅ 0 (topcsInit (P, none)) (by
      simp only [topcsView, topcsInit, topcsTestView, if_pos ht, decTop1State,
        Option.map_some, decCoset]) (by simp)
  have hh := phaseMatch_bind (k := topcsTail n P) (P' := TopcsDone n P) h0
    (fun A j s h => topcsPhase_tail bound solve hx hw hK hO h.1 h.2)
  simpa only [topcsJobs, topcsCount, Nat.add_mul, topcsReduction] using hh

noncomputable def topcsCheckedTail {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ))
    (x y : Fin n → ℕ) (A : Option (Set (Perm (Fin n)))) :
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n)))) :=
  if A = none then .done none else
    (Babai.cosetChain x y E.windows (kerSubgroup ϕ : Set (Perm (Fin n)))).bind fun B =>
      if ϕ.range ≤ alternatingGroup (Fin m) then .done (some (cosetUnion B (A.getD ∅))) else
        (Babai.cosetChain x y E.windows
          (O.representative • (kerSubgroup ϕ : Set (Perm (Fin n))))).bind fun D =>
          .done (some (cosetUnion B (A.getD ∅) ∪ cosetUnion D (A.getD ∅)))

theorem topcsChecked_eq {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    (ϕ : G →* Perm (Fin m)) (S : List (alternatingGroup (Fin m)))
    (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ)) (x y : Fin n → ℕ) :
    cosetTopAction3With ϕ S O E x y =
      (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).bind (topcsCheckedTail ϕ O E x y) := by
  unfold cosetTopAction3With
  congr 1

theorem topcsHull_union {Γ : Type*} [Group Γ] (A B : Set Γ) :
    cosetHull (cosetHull A ∪ cosetHull B) = cosetHull (A ∪ B) := by
  rw [cosetHull_hull_union, Set.union_comm A (cosetHull B), cosetHull_hull_union, Set.union_comm B A]

namespace TopcsSpec

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {P : TopcsInput}
    {ϕ : G →* Perm (Fin m)} {S : List (alternatingGroup (Fin m))} {O : TopActionOdd ϕ}
    {E : OrbitEnum (kerSubgroup ϕ)} {x y : Fin n → ℕ}
    (h : TopcsSpec P ϕ S O E x y)

include h

theorem fold_calls :
    (topcsLiftFold (decStrN n (topcsX P)) (decStrN n (topcsX P))
      ((topcsWins P).map (winSet n)) ((topcsTests P).map (decCoset n)) (some ∅)).calls =
      (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).calls := by
  rw [h.source, h.windows, h.tests]
  exact topcsLiftFold_giant_calls (altHom ϕ) S (E.alt ϕ) x x

theorem fold_run :
    (topcsLiftFold (decStrN n (topcsX P)) (decStrN n (topcsX P))
      ((topcsWins P).map (winSet n)) ((topcsTests P).map (decCoset n)) (some ∅)).run =
      (cosetGiantAWith (altHom ϕ) S (E.alt ϕ) x x).run := by
  rw [h.source, h.windows, h.tests]
  exact topcsLiftFold_giant_run (altHom ϕ) S (E.alt ϕ) x x

theorem tail_calls (A : Option (Set (Perm (Fin n)))) :
    (topcsTail n P A).calls = (topcsCheckedTail ϕ O E x y A).calls := by
  cases A with
  | none => simp [topcsTail, topcsCheckedTail]
  | some a =>
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · have he := h.even.mpr hr
      simp only [topcsTail, topcsCheckedTail, Option.some_ne_none, if_false, h.source,
        h.target, h.windows, h.kernel, h.odd, SIReduction.calls_bind, he, if_true, if_pos hr,
        SIReduction.calls_done]
    · have he : ¬ topcsEven P = true := fun he => hr (h.even.mp he)
      simp only [topcsTail, topcsCheckedTail, Option.some_ne_none, if_false, h.source,
        h.target, h.windows, h.kernel, h.odd, SIReduction.calls_bind, if_neg he, if_neg hr,
        SIReduction.calls_done]

theorem tail_run (A : Option (Set (Perm (Fin n)))) :
    (topcsTail n P A).run = ((topcsCheckedTail ϕ O E x y A).run).map cosetHull := by
  cases A with
  | none => simp [topcsTail, topcsCheckedTail]
  | some a =>
    by_cases hr : ϕ.range ≤ alternatingGroup (Fin m)
    · have he := h.even.mpr hr
      simp only [topcsTail, topcsCheckedTail, Option.some_ne_none, if_false, h.source,
        h.target, h.windows, h.kernel, h.odd, SIReduction.run_bind, he, if_true, if_pos hr,
        SIReduction.run_done, topcsFinalSet, Option.map_some, Option.getD_some, cosetUnion_eq_mul]
    · have he : ¬ topcsEven P = true := fun he => hr (h.even.mp he)
      simp only [topcsTail, topcsCheckedTail, Option.some_ne_none, if_false, h.source,
        h.target, h.windows, h.kernel, h.odd, SIReduction.run_bind, if_neg he, if_neg hr,
        SIReduction.run_done, topcsFinalSet, Option.map_some, Option.getD_some, cosetUnion_eq_mul,
        topcsHull_union]

theorem reduction_calls :
    (topcsReduction n P).calls = (cosetTopAction3With ϕ S O E x y).calls := by
  rw [topcsReduction, SIReduction.calls_bind, h.fold_calls, h.fold_run]
  rw [h.tail_calls, topcsChecked_eq, SIReduction.calls_bind]

theorem reduction_run (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    (topcsReduction n P).run = (cosetTopAction3With ϕ S O E x y).run := by
  have hh : (topcsReduction n P).run = ((cosetTopAction3With ϕ S O E x y).run).map cosetHull := by
    rw [topcsReduction, SIReduction.run_bind, h.fold_run, h.tail_run]
    rw [topcsChecked_eq, SIReduction.run_bind]
  rw [hh, run_cosetTopAction3With ϕ S O hS]
  split <;> simp only [Option.map_some, Option.map_none, cosetHull_strIso]

/-- The complete raw phase matches the live supplied top-action tree,
including the ordered giant tests and the conditional odd-image branch. -/
theorem phase (bound : ℕ → ℕ) (solve : RawWinSI → RawCoset) (hn : 0 < n)
    (hϕ : IsGiantRep ϕ) (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤) :
    PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
      (topcsJobs P * (topcsWins P).length) 0 (topcsInit (P, none))
      (cosetTopAction3With ϕ S O E x y) (TopcsDone n P) := by
  have hK : (decCoset n (topcsKernel P)).Nonempty := by
    rw [h.kernel]
    exact ⟨1, one_mem _⟩
  have hO : (decCoset n (topcsOdd P)).Nonempty := by
    rw [h.odd]
    exact ⟨O.representative, 1, one_mem _, by change O.representative * 1 = O.representative; rw [mul_one]⟩
  exact topcsPhaseMatch_congr
    (topcsPhase_reduction bound solve h.source_length (h.wins_pos hn) h.count_pos
      (h.tests_nonempty hϕ) hK hO) h.reduction_calls (h.reduction_run hS)

theorem width_eq (bound : ℕ → ℕ) (solve : RawWinSI → RawCoset) :
    (topcsRound n bound solve).width (P, none) = (S.length + 3) * orbCount ϕ := by
  change topcsJobs P * (topcsWins P).length = _
  rw [topcsJobs, h.count, h.wins_length]

end TopcsSpec

end Algo
