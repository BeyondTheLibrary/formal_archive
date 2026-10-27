import Workspace.Algo.TopSuppliedSem

/-! # The ordered giant-test phase

Each completed lifting chain is added to the generated coset. The failure
flag survives all later jobs. After the last test, the same combine step
either opens the kernel chain or stops the round.
-/

namespace Algo

open Babai Equiv
open scoped Classical

noncomputable def topcsTestView (n : ℕ) (P : TopcsInput) (t : ℕ)
    (A : Option (Set (Perm (Fin n)))) (B D : Set (Perm (Fin n))) : TopcsView n :=
  if t < topcsCount P then (t, 0, decCoset n (topcsBegin P t), A, B, D)
  else (if A.isSome then topcsCount P else topcsJobs P, 0,
    decCoset n (topcsBegin P (topcsCount P)), A, B, D)

theorem topcsClosedSet_test {n : ℕ} {P : TopcsInput} {t : ℕ} (ht : t < topcsCount P)
    (A : Option (Set (Perm (Fin n)))) (B D C : Set (Perm (Fin n))) :
    topcsClosedSet n P t A B D C = topcsTestView n P (t + 1) (top1JoinSet A C) B D := by
  by_cases h : t + 1 < topcsCount P
  · simp only [topcsClosedSet, topcsTestView, if_pos h]
  · have he : t + 1 = topcsCount P := by omega
    simp only [topcsClosedSet, topcsTestView, if_neg h, if_pos he]

/-- The machine executes every lifting test in order, even if an earlier
test has failed. This is the order of the checked `cosetLiftAll`. -/
theorem topcsPhase_tests {n : ℕ} {P : TopcsInput} (bound : ℕ → ℕ)
    (solve : RawWinSI → RawCoset) (hx : (topcsX P).length = n)
    (hw : 0 < (topcsWins P).length)
    (hall : ∀ c ∈ topcsTests P, (decCoset n c).Nonempty) :
    ∀ (L : List RawCoset) (t : ℕ), t ≤ topcsCount P → L = (topcsTests P).drop t →
    ∀ (A : Option (Set (Perm (Fin n)))) (B D : Set (Perm (Fin n))) (j : ℕ) (s : TopcsState),
      topcsView n s = topcsTestView n P t A B D → j ≤ t * (topcsWins P).length →
      PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
        (L.length * (topcsWins P).length) j s
        (topcsLiftFold (decStrN n (topcsX P)) (decStrN n (topcsX P))
          ((topcsWins P).map (winSet n)) (L.map (decCoset n)) A)
        (fun A' j' s' => topcsView n s' = topcsTestView n P (topcsCount P) A' B D ∧
          j' ≤ topcsCount P * (topcsWins P).length) := by
  intro L
  induction L with
  | nil =>
    intro t ht hL A B D j s hs hj
    have he : t = topcsCount P := by
      have hh := congrArg List.length hL
      simp only [List.length_nil, List.length_drop] at hh
      unfold topcsCount at ht ⊢
      omega
    subst t
    simp only [List.length_nil, Nat.zero_mul, List.map_nil, topcsLiftFold]
    exact phaseMatch_done ⟨hs, hj⟩
  | cons c L ih =>
    intro t ht hL A B D j s hs hj
    have hlt : t < topcsCount P := by
      have hh := congrArg List.length hL
      simp only [List.length_cons, List.length_drop] at hh
      unfold topcsCount at ht ⊢
      omega
    have hdrop := List.drop_eq_getElem_cons (show t < (topcsTests P).length from hlt)
    rw [hdrop] at hL
    obtain ⟨hc, hL⟩ := List.cons.inj hL
    have hmem : c ∈ topcsTests P := hc ▸ List.getElem_mem (show t < (topcsTests P).length from hlt)
    have hbegin : decCoset n (topcsBegin P t) = decCoset n c := by
      rw [topcsBegin, decCoset_top2NormC hx, if_pos hlt,
        List.getD_eq_getElem _ _ (show t < (topcsTests P).length from hlt), ← hc]
    rw [topcsTestView, if_pos hlt, hbegin] at hs
    have hjob := topcsPhase_job bound solve hx hw
      (show t < topcsJobs P by unfold topcsJobs; omega) (hall c hmem) hs hj
    rw [topcsTgt, if_pos hlt] at hjob
    simp only [List.length_cons, List.map_cons, topcsLiftFold]
    rw [Nat.succ_mul, Nat.add_comm]
    refine phaseMatch_bind hjob ?_
    intro C j' s' hh
    have hv := hh.1
    rw [topcsClosedSet_test hlt] at hv
    exact ih (t + 1) (by omega) hL _ B D j' s' hv hh.2

end Algo
