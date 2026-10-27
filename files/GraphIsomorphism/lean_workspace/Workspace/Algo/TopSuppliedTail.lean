import Workspace.Algo.TopSuppliedPrepare

/-! # The kernel and odd-coset continuation

After the giant test succeeds, the round follows the two kernel chains of
the repaired Corollary 12.0.8 proof. The odd representative is already in
the second initial coset. Products reconstruct the isomorphisms from the
automorphism group returned by the first phase.
-/

namespace Algo

open Babai Equiv
open scoped Pointwise Classical

noncomputable def topcsFinalSet (n : ℕ) (P : TopcsInput)
    (A : Option (Set (Perm (Fin n)))) (B D : Set (Perm (Fin n))) : Option (Set (Perm (Fin n))) :=
  A.map (fun a => if topcsEven P then cosetHull (B * a)
    else cosetHull (cosetHull (B * a) ∪ cosetHull (D * a)))

theorem topcsAnswer_dec {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (s : TopcsState) :
    decTop1State n (topcsAnswer P s) =
      topcsFinalSet n P (decTop1State n s.2.2.2.1)
        (decCoset n s.2.2.2.2.1) (decCoset n s.2.2.2.2.2) := by
  cases ha : s.2.2.2.1 with
  | none => simp [topcsAnswer, topcsFinalSet, decTop1State, ha]
  | some a =>
    simp only [topcsAnswer, topcsFinalSet, ha, decTop1State, Option.map_some]
    split <;> simp only [decCoset_top3Prod hx, decCoset_rawCosetJoin hx]

theorem topcsAnswer_of_view {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    {s : TopcsState} {t i : ℕ} {C B D : Set (Perm (Fin n))} {A : Option (Set (Perm (Fin n)))}
    (hs : topcsView n s = (t, i, C, A, B, D)) :
    decTop1State n (topcsAnswer P s) = topcsFinalSet n P A B D := by
  rw [topcsAnswer_dec hx]
  rcases s with ⟨t', i', c, acc, s1, s2⟩
  simp only [topcsView, Prod.mk.injEq] at hs
  obtain ⟨_, _, _, ha, hb, hd⟩ := hs
  rw [ha, hb, hd]

noncomputable def topcsTail (n : ℕ) (P : TopcsInput) (A : Option (Set (Perm (Fin n)))) :
    SIReduction (Fin n) ℕ (Option (Set (Perm (Fin n)))) :=
  if A = none then .done none else
    (Babai.cosetChain (decStrN n (topcsX P)) (decStrN n (topcsY P))
      ((topcsWins P).map (winSet n)) (decCoset n (topcsKernel P))).bind fun B =>
      if topcsEven P then .done (topcsFinalSet n P A B ∅) else
        (Babai.cosetChain (decStrN n (topcsX P)) (decStrN n (topcsY P))
          ((topcsWins P).map (winSet n)) (decCoset n (topcsOdd P))).bind fun D =>
          .done (topcsFinalSet n P A B D)

def TopcsDone (n : ℕ) (P : TopcsInput) (A : Option (Set (Perm (Fin n)))) (j : ℕ)
    (s : TopcsState) : Prop :=
  s.1 = topcsJobs P ∧ decTop1State n (topcsAnswer P s) = A ∧
    j ≤ topcsJobs P * (topcsWins P).length

theorem topcsDone_of_view {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    {s : TopcsState} {j i : ℕ} {C B D : Set (Perm (Fin n))} {A : Option (Set (Perm (Fin n)))}
    (hs : topcsView n s = (topcsJobs P, i, C, A, B, D))
    (hj : j ≤ topcsJobs P * (topcsWins P).length) :
    TopcsDone n P (topcsFinalSet n P A B D) j s :=
  ⟨congrArg Prod.fst hs, topcsAnswer_of_view hx hs, hj⟩

theorem topcsPhase_tail {n : ℕ} {P : TopcsInput} (bound : ℕ → ℕ)
    (solve : RawWinSI → RawCoset) (hx : (topcsX P).length = n)
    (hw : 0 < (topcsWins P).length)
    (hK : (decCoset n (topcsKernel P)).Nonempty)
    (hO : (decCoset n (topcsOdd P)).Nonempty)
    {A : Option (Set (Perm (Fin n)))} {j : ℕ} {s : TopcsState}
    (hs : topcsView n s = topcsTestView n P (topcsCount P) A ∅ ∅)
    (hj : j ≤ topcsCount P * (topcsWins P).length) :
    PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
      (2 * (topcsWins P).length) j s (topcsTail n P A) (TopcsDone n P) := by
  have hk : decCoset n (topcsBegin P (topcsCount P)) = decCoset n (topcsKernel P) := by
    rw [topcsBegin, decCoset_top2NormC hx, if_neg (by omega), if_pos rfl]
  have ho : decCoset n (topcsBegin P (topcsCount P + 1)) = decCoset n (topcsOdd P) := by
    rw [topcsBegin, decCoset_top2NormC hx, if_neg (by omega), if_neg (by omega)]
  simp only [topcsTestView, Nat.lt_irrefl, if_false] at hs
  cases hA : A with
  | none =>
    rw [hA] at hs
    simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hs
    rw [topcsTail, if_pos rfl]
    apply phaseMatch_mono (phaseMatch_done ?_) (Nat.zero_le _)
    have hh := topcsDone_of_view hx hs (show j ≤ topcsJobs P * (topcsWins P).length by
      unfold topcsJobs; nlinarith)
    simpa only [topcsFinalSet, Option.map_none] using hh
  | some a =>
    rw [hA] at hs
    simp only [Option.isSome_some, if_true, hk] at hs
    rw [topcsTail, if_neg (by simp)]
    have h1 := topcsPhase_job bound solve hx hw
      (show topcsCount P < topcsJobs P by unfold topcsJobs; omega) hK hs hj
    rw [topcsTgt, if_neg (by omega)] at h1
    rw [show 2 * (topcsWins P).length = (topcsWins P).length + (topcsWins P).length by omega]
    refine phaseMatch_bind h1 ?_
    intro B j' s' hh
    have hv := hh.1
    simp only [topcsClosedSet, show ¬ topcsCount P + 1 < topcsCount P by omega,
      show ¬ topcsCount P + 1 = topcsCount P by omega, if_false, if_true, ho] at hv
    by_cases he : topcsEven P = true
    · rw [if_pos he] at hv ⊢
      apply phaseMatch_mono (phaseMatch_done ?_) (Nat.zero_le _)
      exact topcsDone_of_view hx hv (by unfold topcsJobs; nlinarith [hh.2])
    · rw [if_neg he] at hv ⊢
      have h2 := topcsPhase_job bound solve hx hw
        (show topcsCount P + 1 < topcsJobs P by unfold topcsJobs; omega) hO hv hh.2
      rw [topcsTgt, if_neg (by omega)] at h2
      have h2' := phaseMatch_bind (c₂ := 0)
        (k := fun D => .done (topcsFinalSet n P (some a) B D))
        (P' := TopcsDone n P) h2 (fun D j'' s'' hd => ?_)
      · simpa only [Nat.add_zero] using h2'
      · apply phaseMatch_done
        have hv' := hd.1
        simp only [topcsClosedSet, show ¬ topcsCount P + 1 + 1 < topcsCount P by omega,
          show ¬ topcsCount P + 1 + 1 = topcsCount P by omega,
          show ¬ topcsCount P + 1 = topcsCount P by omega, if_false] at hv'
        exact topcsDone_of_view hx hv' (by simpa only [topcsJobs, Nat.add_assoc] using hd.2)

end Algo
