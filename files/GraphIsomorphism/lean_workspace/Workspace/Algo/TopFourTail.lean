import Workspace.Algo.TopFourFirst

/-! # The remaining windows in top-action 4
The invariant records the list suffix and the current decoded coset.
An empty answer stops immediately, as in the paper's Chain Rule.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 def Top4TailInv (n : ℕ) (P : Top4Context) (Δs : List (Set (Fin n)))
    (C : Set (Perm (Fin n))) (j : ℕ) (s : Top4State) : Prop :=
  topcsJobs P.1.2 ≤ s.1.1 ∧ decCoset n s.2.2 = C ∧
  (Δs = ((top4Wins P).drop s.2.1).map (winSet n) ∨ C = ∅) ∧
  s.2.1 ≤ (top4Wins P).length ∧ j ≤ top4Base P + s.2.1

 theorem top4Phase_tail {n c d e f : ℕ} (P : Top4Context)
    (hx : (top4X P).length = n) (solve : RawWinSI → RawCoset) :
    ∀ Δs C j s, Top4TailInv n P Δs C j s →
      PhaseMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (P, none)
        Δs.length j s (Babai.cosetChain (decStrN n (top4X P)) (decStrN n (top4Y P)) Δs C)
        (fun C' j' s' => Top4TailInv n P [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (Top4TailInv n P) ?_ ?_ Δs C j s h
  · intro Δ rest C j s hs hC
    obtain ⟨ht, hc, hlist, hi, hj⟩ := hs
    have he := hlist.resolve_right hC
    have hi' : s.2.1 < (top4Wins P).length := by
      by_contra hn
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at he
      simp at he
    rw [List.drop_eq_getElem_cons hi', List.map_cons] at he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    obtain ⟨q, hq⟩ : ∃ q, s.2.2 = some q := by
      cases hq : s.2.2 with
      | none => exact (hC (by simpa only [hq, decCoset] using hc.symm)).elim
      | some q => exact ⟨q, rfl⟩
    let W := top4Leaf P s.2.1 q
    have hchild : top4Child e f ((P, none), j, s) = some (P, some W) := by
      simp only [top4Child, Option.elim_none]
      rw [if_pos (show j < top4Width P by unfold top4Width; omega), if_neg (by omega), if_pos hi', hq]
      rfl
    have hdec : top4Decode n (P, some W) =
        ⟨C, winSet n ((top4Wins P)[s.2.1]), decStrN n (top4X P), decStrN n (top4Y P)⟩ := by
      change SIInstance.mk (decCoset n (some (tidyGens (top4X P, q.1), normPerm (top4X P, q.2))))
        (winSet n ((top4Wins P).getD s.2.1 [])) _ _ = _
      have hnorm : decCoset n (some (tidyGens (top4X P, q.1), normPerm (top4X P, q.2))) = decCoset n (some q) := by
        rcases q with ⟨g, r⟩
        simp only [decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]
      rw [hnorm, ← hq, hc, List.getD_eq_getElem _ _ hi']
      rfl
    refine ⟨(P, some W), hchild, hdec, ?_⟩
    intro a ha
    change Top4TailInv n P _ _ (j + 1) (top4Combine ((P, none), j, s, a))
    unfold top4Combine
    dsimp only
    rw [if_neg (by omega)]
    refine ⟨le_rfl, ?_, Or.inl ?_, Nat.min_le_right _ _, ?_⟩
    · exact (decCoset_top2NormC hx a).trans ha
    · dsimp only
      rw [Nat.min_eq_left (by omega)]
    · dsimp only
      rw [Nat.min_eq_left (by omega)]
      omega
  · intro Δs C j s hs hC
    exact ⟨hs.1, hs.2.1.trans hC, Or.inr rfl, hs.2.2.2⟩

 theorem top4Tail_finish {n c d e f : ℕ} {P : Top4Context}
    (hx : (top4X P).length = n) (solve : RawWinSI → RawCoset)
    {C : Set (Perm (Fin n))} {j : ℕ} {s : Top4State}
    (h : Top4TailInv n P [] C j s) :
    (top4Round c d e f solve).child ((P, none), j, s) = none ∧
      decCoset n ((top4Round c d e f solve).finish ((P, none), s)) = C := by
  obtain ⟨ht, hc, hl, hi, hj⟩ := h
  refine ⟨?_, (decCoset_top2NormC hx s.2.2).trans hc⟩
  change top4Child e f ((P, none), j, s) = none
  simp only [top4Child, Option.elim_none]
  split
  · rw [if_neg (by omega)]
    rcases hl with hl | hC
    · have hlen := congrArg List.length hl
      simp only [List.length_nil, List.length_map, List.length_drop] at hlen
      rw [if_neg (by omega)]
    · have hn := (decCoset_eq_empty_iff n s.2.2).mp (hc.trans hC)
      rw [hn]
      split <;> rfl
  · rfl

end Algo
