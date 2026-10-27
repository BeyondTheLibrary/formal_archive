import Workspace.Algo.TopSuppliedRound

/-! # Exact chain phases of the supplied top-action round

Decode the stored cosets, including the giant-test flag. The transition
identities below hold for every encoding of an answer. They let the Chain
Rule finish a job and open the next one inside the same raw combine step.
-/

namespace Algo

open Babai Equiv
open scoped Pointwise Classical

abbrev TopcsView (n : ℕ) := ℕ × ℕ × Set (Perm (Fin n)) ×
  Option (Set (Perm (Fin n))) × Set (Perm (Fin n)) × Set (Perm (Fin n))

noncomputable def topcsView (n : ℕ) (s : TopcsState) : TopcsView n :=
  (s.1, s.2.1, decCoset n s.2.2.1, decTop1State n s.2.2.2.1,
    decCoset n s.2.2.2.2.1, decCoset n s.2.2.2.2.2)

noncomputable def topcsClosedSet (n : ℕ) (P : TopcsInput) (t : ℕ)
    (acc : Option (Set (Perm (Fin n)))) (s1 s2 a : Set (Perm (Fin n))) : TopcsView n :=
  let A := top1JoinSet acc a
  if t + 1 < topcsCount P then
    (t + 1, 0, decCoset n (topcsBegin P (t + 1)), A, s1, s2)
  else if t + 1 = topcsCount P then
    (if A.isSome then topcsCount P else topcsJobs P, 0,
      decCoset n (topcsBegin P (topcsCount P)), A, s1, s2)
  else if t = topcsCount P then
    (if topcsEven P then topcsJobs P else topcsCount P + 1, 0,
      decCoset n (topcsBegin P (topcsCount P + 1)), acc, a, s2)
  else
    (topcsJobs P, 0, decCoset n (topcsBegin P (topcsJobs P)), acc, s1, a)

noncomputable def topcsStepSet (n : ℕ) (P : TopcsInput) (t i : ℕ)
    (acc : Option (Set (Perm (Fin n)))) (s1 s2 a : Set (Perm (Fin n))) : TopcsView n :=
  if a.Nonempty ∧ i + 1 < (topcsWins P).length then
    (min t (topcsJobs P), min (i + 1) (topcsWins P).length, a, acc, s1, s2)
  else topcsClosedSet n P t acc s1 s2 a

@[simp] theorem isSome_decTop1State (n : ℕ) (s : Top1State) :
    (decTop1State n s).isSome = s.isSome := by simp [decTop1State]

theorem topcsView_close {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t : ℕ) (acc : Top1State) (s1 s2 a : RawCoset) :
    topcsView n (topcsClose P t acc s1 s2 a) =
      topcsClosedSet n P t (decTop1State n acc) (decCoset n s1) (decCoset n s2) (decCoset n a) := by
  have hs : (top2NormS (topcsX P) (top1Join (topcsX P, acc, a))).isSome =
      (top1JoinSet (decTop1State n acc) (decCoset n a)).isSome := by
    rw [← decTop1State_top1Join hx, ← decTop1State_top2NormS hx, isSome_decTop1State]
  simp only [topcsClose, topcsClosedSet, hs]
  split_ifs <;> simp only [topcsView, decCoset_top2NormC hx, decTop1State_top2NormS hx,
    decTop1State_top1Join hx]

theorem topcsView_step {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t i : ℕ) (acc : Top1State) (s1 s2 a : RawCoset) :
    topcsView n (topcsStep P t i acc s1 s2 a) =
      topcsStepSet n P t i (decTop1State n acc) (decCoset n s1) (decCoset n s2) (decCoset n a) := by
  simp only [topcsStep, topcsStepSet, decCoset_nonempty]
  split_ifs
  · simp only [topcsView, decCoset_top2NormC hx, decTop1State_top2NormS hx]
  · exact topcsView_close hx _ _ _ _ _

/-- A chain is active at a window, or its last combine has already closed
the job. The latter also covers early termination on the empty answer. -/
def topcsChainInv (n : ℕ) (P : TopcsInput) (t : ℕ)
    (A : Option (Set (Perm (Fin n)))) (B D : Set (Perm (Fin n)))
    (Δs : List (Set (Fin n))) (C : Set (Perm (Fin n))) (j : ℕ) (s : TopcsState) : Prop :=
  (∃ i, i < (topcsWins P).length ∧ Δs = ((topcsWins P).drop i).map (winSet n) ∧
    C.Nonempty ∧ topcsView n s = (t, i, C, A, B, D) ∧
    j ≤ t * (topcsWins P).length + i) ∨
  ((Δs = [] ∨ C = ∅) ∧ topcsView n s = topcsClosedSet n P t A B D C ∧
    j ≤ (t + 1) * (topcsWins P).length)

theorem topcsPhase_chain {n : ℕ} {P : TopcsInput} (bound : ℕ → ℕ)
    (solve : RawWinSI → RawCoset) (hx : (topcsX P).length = n)
    {t : ℕ} (ht : t < topcsJobs P)
    (A : Option (Set (Perm (Fin n)))) (B D : Set (Perm (Fin n))) :
    ∀ Δs C j s, topcsChainInv n P t A B D Δs C j s →
      PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
        Δs.length j s
        (Babai.cosetChain (decStrN n (topcsX P)) (decStrN n (topcsTgt P t)) Δs C)
        (fun C' j' s' => topcsChainInv n P t A B D [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (topcsChainInv n P t A B D) ?_ ?_ Δs C j s h
  · intro Δ rest C j s h hC
    rcases h with ⟨i, hi, he, hne, hv, hj⟩ | ⟨he, _⟩
    · rw [List.drop_eq_getElem_cons hi, List.map_cons] at he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rcases s with ⟨t', i', c, acc, s1, s2⟩
      simp only [topcsView, Prod.mk.injEq] at hv
      obtain ⟨ht', hi', hc, hacc, hs1, hs2⟩ := hv
      subst t'
      subst i'
      obtain ⟨q, rfl⟩ : ∃ q, c = some q := by
        cases c with
        | none => exact (hC hc.symm).elim
        | some q => exact ⟨q, rfl⟩
      have hjlt : j < topcsJobs P * (topcsWins P).length := by
        have hmul := Nat.mul_le_mul_right (topcsWins P).length ht
        rw [Nat.succ_mul] at hmul
        omega
      let J : TopcsNode := (P, some (topcsLeaf P t i q))
      have hJ : topcsDecode n J =
          ⟨C, winSet n (topcsWins P)[i], decStrN n (topcsX P), decStrN n (topcsTgt P t)⟩ := by
        rw [topcsDecode_leaf hx, List.getD_eq_getElem _ _ hi, hc]
      refine ⟨J, ?_, hJ, ?_⟩
      · change topcsChild ((P, none), j, (t, i, some q, acc, s1, s2)) = some J
        simp only [topcsChild, Option.elim_none]
        rw [if_pos ⟨ht, hi, hjlt⟩]
        rfl
      · intro a ha
        have hv := topcsView_step hx t i acc s1 s2 a
        rw [hacc, hs1, hs2, ha] at hv
        change topcsChainInv n P t A B D _ _ (j + 1) (topcsStep P t i acc s1 s2 a)
        by_cases hn : (topcsDecode n J).answer.Nonempty ∧ i + 1 < (topcsWins P).length
        · rw [topcsStepSet, if_pos hn, Nat.min_eq_left (Nat.le_of_lt ht),
            Nat.min_eq_left (Nat.le_of_lt hn.2)] at hv
          exact Or.inl ⟨i + 1, hn.2, rfl, hn.1, hv, by omega⟩
        · rw [topcsStepSet, if_neg hn] at hv
          refine Or.inr ⟨?_, hv, by rw [Nat.succ_mul]; omega⟩
          by_cases hne : (topcsDecode n J).answer.Nonempty
          · have hh : (topcsWins P).length ≤ i + 1 := Nat.le_of_not_lt (fun h => hn ⟨hne, h⟩)
            exact Or.inl (by rw [List.drop_eq_nil_of_le hh, List.map_nil])
          · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hne)
    · rcases he with he | he
      · cases he
      · exact (hC he).elim
  · intro Δs C j s h he
    rcases h with ⟨i, _, _, hc, _⟩ | ⟨_, hv, hj⟩
    · exact (hc.ne_empty he).elim
    · exact Or.inr ⟨Or.inl rfl, by simpa only [he] using hv, hj⟩

/-- One complete job makes at most one call per stored kernel window. -/
theorem topcsPhase_job {n : ℕ} {P : TopcsInput} (bound : ℕ → ℕ)
    (solve : RawWinSI → RawCoset) (hx : (topcsX P).length = n)
    (hw : 0 < (topcsWins P).length) {t j : ℕ} (ht : t < topcsJobs P)
    {A : Option (Set (Perm (Fin n)))} {B D C : Set (Perm (Fin n))} {s : TopcsState}
    (hC : C.Nonempty) (hs : topcsView n s = (t, 0, C, A, B, D))
    (hj : j ≤ t * (topcsWins P).length) :
    PhaseMatch (topcsRound n bound solve) (topcsDecode n) (decCoset n) (P, none)
      (topcsWins P).length j s
      (Babai.cosetChain (decStrN n (topcsX P)) (decStrN n (topcsTgt P t))
        ((topcsWins P).map (winSet n)) C)
      (fun C' j' s' => topcsView n s' = topcsClosedSet n P t A B D C' ∧
        j' ≤ (t + 1) * (topcsWins P).length) := by
  have h := topcsPhase_chain bound solve hx ht A B D _ _ j s
    (Or.inl ⟨0, hw, rfl, hC, hs, by simpa using hj⟩)
  rw [List.length_map] at h
  refine phaseMatch_weaken h ?_
  intro C' j' s' hh
  rcases hh with ⟨i, hi, he, _⟩ | ⟨_, hv, hj⟩
  · have hl := congrArg List.length he
    simp only [List.length_nil, List.length_map, List.length_drop] at hl
    omega
  · exact ⟨hv, hj⟩

end Algo
