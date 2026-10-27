import Workspace.Algo.AggNodePairLoop

/-! # Reading the result of the paired comparison -/
namespace Algo
open Babai Equiv
open scoped Pointwise Classical

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {st0 : RawLCSt} {σ : Perm (Fin n)} {q0 : RawCoset}

/-- Proposition 13.1.11's complete paired comparison, with the final
comparison coset read from the raw state. -/
theorem aggnPairPhase_run (c : ℕ) (solve : RawWinSI → RawCoset)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE) (hσ : σ ∈ G)
    (hQ0 : decCoset n q0 = σ • (bigGT ϕ (winSet m tdom) : Set (Perm (Fin n)))) :
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((((xs, tdom), st0), ys, q0), none) (2 * n * (Nat.factorial tdom.length * n))
      0 (aggnPairStart c ((xs, tdom), st0) ys q0 none)
      (pairedComparisonStrong ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ
        (aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ))
      (fun B j v => decCoset n v.2.1 = B ∧
        aggnPairActive v = false ∧
        j ≤ 2 * n * (Nat.factorial tdom.length * n)) := by
  have hm := aggnPairPhase_loop (ys := ys) c solve h0 hg hs hσ hQ0
    (haltIndex ϕ (decStrN n xs) (winSet m tdom)) (le_refl _)
  have hindex : haltIndex ϕ (decStrN n xs) (winSet m tdom) ≤ n := by
    simpa only [Nat.card_fin] using (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom))
  have hbudget : haltIndex ϕ (decStrN n xs) (winSet m tdom) * (2 * (Nat.factorial tdom.length * n)) ≤
      2 * n * (Nat.factorial tdom.length * n) := by
    nlinarith [Nat.mul_le_mul_right (2 * (Nat.factorial tdom.length * n)) hindex]
  have hm' := phaseMatch_bind
    (P' := fun B j v => decCoset n v.2.1 = B ∧
      aggnPairActive v = false ∧
      j ≤ 2 * n * (Nat.factorial tdom.length * n))
    (k := fun b => .done (b.elim ∅ fun p => p.2.2)) (phaseMatch_mono hm hbudget) (by
      intro b j v hv
      obtain ⟨hj, hv⟩ := hv
      apply phaseMatch_done
      cases b with
      | none =>
        refine ⟨?_, ?_, hj.trans hbudget⟩
        · rw [hv]
          rfl
        · simp only [aggnPairActive, hv, Option.isSome_none, Bool.and_false]
      | some b =>
        obtain ⟨st, q, hst, rfl, hq, hQ, rfl⟩ := hv
        refine ⟨hQ, ?_, hj.trans hbudget⟩
        have hcond : lcCond ((xs, tdom), st) ≠ true := by
          intro he
          exact not_loopCond_outStage ϕ (decStrN n xs) (winSet m tdom)
            ((lcCond_eq_true_iff hst).mp he)
        simp only [aggnPairActive, aggnPairStart, Bool.eq_false_iff.mpr hcond, Bool.false_and])
  simpa only [Nat.add_zero, pairedComparisonStrong] using hm'

/-- The complete fold has the same tree, including the terminal read-out. -/
theorem aggnPairLoopMatch (c : ℕ) (solve : RawWinSI → RawCoset)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE) (hσ : σ ∈ G)
    (hQ0 : decCoset n q0 = σ • (bigGT ϕ (winSet m tdom) : Set (Perm (Fin n)))) :
    LoopMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((((xs, tdom), st0), ys, q0), none) (2 * n * (Nat.factorial tdom.length * n))
      0 (aggnPairStart c ((xs, tdom), st0) ys q0 none)
      (pairedComparisonStrong ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ
        (aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ)) := by
  apply loopMatch_of_phaseMatch (aggnPairPhase_run c solve h0 hg hs hσ hQ0) ?_ le_rfl
  intro B j v h
  refine ⟨?_, h.1⟩
  dsimp only [aggnPairRound]
  exact aggnPairChild_none_of_inactive ((((xs, tdom), st0), ys, q0), none) j v h.2.1

end Algo
