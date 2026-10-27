import Workspace.Algo.AggNodePairStage
import Workspace.Algo.TopRound

/-! # The complete paired comparison loop -/
set_option maxHeartbeats 1000000
namespace Algo
open Babai Equiv
open scoped Pointwise Classical

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {st0 : RawLCSt} {σ : Perm (Fin n)} {q0 : RawCoset}

/-- A rejected comparison keeps its empty coset. A live comparison retains
the exact source stage and the current comparison value. -/
def AggnPairInv (c : ℕ) (hc : LCCtxWF n m xs tdom)
    (ϕ : G →* Perm (Fin m)) (ys : RawStr) (σ : Perm (Fin n)) (i : ℕ)
    (b : Option (Set (Fin n) × Set (Perm (Fin n)) × Set (Perm (Fin n))))
    (j : ℕ) (v : AggnPairState) : Prop :=
  j ≤ i * (2 * (Nat.factorial tdom.length * n)) ∧
  match b with
  | none => v.2.1 = none
  | some b => ∃ st q,
      StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st ∧
      v = aggnPairStart c ((xs, tdom), st) ys q none ∧ q.isSome = true ∧
      decCoset n q = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i ∧
      b = ((stages ϕ (decStrN n xs) (winSet m tdom) i).W,
        ((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n))),
        pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i)

/-- Both source and comparison calls follow `pairedLoopStrong`, with the
same early rejection and every possible encoding of correct answers. -/
theorem aggnPairPhase_loop (c : ℕ) (solve : RawWinSI → RawCoset)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE) (hσ : σ ∈ G)
    (hQ0 : decCoset n q0 = σ • (bigGT ϕ (winSet m tdom) : Set (Perm (Fin n)))) :
    ∀ i, i ≤ haltIndex ϕ (decStrN n xs) (winSet m tdom) →
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((((xs, tdom), st0), ys, q0), none) (i * (2 * (Nat.factorial tdom.length * n)))
      0 (aggnPairStart c ((xs, tdom), st0) ys q0 none)
      (pairedLoopStrong ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ
        (aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ) i)
      (AggnPairInv c hc ϕ ys σ i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hne : (σ • (bigGT ϕ (winSet m tdom) : Set (Perm (Fin n)))).Nonempty :=
      ⟨σ, 1, (bigGT ϕ (winSet m tdom)).one_mem, by simp⟩
    have hq : q0.isSome = true := (decCoset_nonempty q0).mp (hQ0 ▸ hne)
    have he : pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ 0 =
        σ • (bigGT ϕ (winSet m tdom) : Set (Perm (Fin n))) := by
      ext r
      simp [pairedQ, stages, Stage.init, wIso]
    rw [Nat.zero_mul, pairedLoopStrong, comparisonState, if_pos hne]
    apply phaseMatch_done
    refine ⟨Nat.zero_le _, st0, q0, h0, rfl, hq, hQ0.trans he.symm, ?_⟩
    simp only [stages, Stage.init, he]
  | succ i ih =>
    intro hi
    rw [pairedLoopStrong, Nat.succ_mul]
    apply phaseMatch_bind (ih (by omega))
    intro b j v hv
    obtain ⟨hj, hv⟩ := hv
    cases b with
    | none =>
      apply phaseMatch_mono (phaseMatch_done ?_) (Nat.zero_le _)
      exact ⟨hj.trans (Nat.mul_le_mul_right _ (Nat.le_succ i)), hv⟩
    | some b =>
      obtain ⟨st, q, hst, rfl, hq, hQ, rfl⟩ := hv
      have hir : i < haltIndex ϕ (decStrN n xs) (winSet m tdom) := by omega
      have hsource := aggnPairPhase_source (ys := ys) (st0 := st0) (q0 := q0) (σ := σ)
        c solve hst hg hs hir hq hj
      have hboth := phaseMatch_bind (P' := AggnPairInv c hc ϕ ys σ (i + 1)) hsource (by
        rintro H j1 v1 ⟨rawH, hrawH, hH, rfl, hj1⟩
        have htarget := aggnPairPhase_target (st0 := st0) (q0 := q0)
          c solve hst hg hs hσ hir hq hQ (hrawH.trans hH) hj1
        have hdone := phaseMatch_bind (P' := AggnPairInv c hc ϕ ys σ (i + 1))
          (k := fun Q => .done (comparisonState
            (affOf ϕ (winSet m tdom) ((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n))))
            (((stages ϕ (decStrN n xs) (winSet m tdom) i).H : Set (Perm (Fin n))) ∩ H) Q))
          htarget (by
            rintro Q j2 v2 ⟨st', q', hst', hq', hQ', rfl, hj2⟩
            apply phaseMatch_done
            rw [hH, affOf_coe, Set.inter_eq_self_of_subset_right
              (stages ϕ (decStrN n xs) (winSet m tdom) i).step_H_le]
            by_cases hne : Q.Nonempty
            · rw [comparisonState, if_pos hne]
              refine ⟨hj2, st', q', hst', rfl, (decCoset_nonempty q').mp (hq' ▸ hne), hq'.trans hQ', ?_⟩
              rw [hQ']
              rfl
            · rw [comparisonState, if_neg hne]
              refine ⟨hj2, ?_⟩
              change q' = none
              exact (decCoset_eq_empty_iff n q').mp (hq'.trans (Set.not_nonempty_iff_eq_empty.mp hne)))
        simpa only [Nat.add_zero] using hdone)
      simpa only [two_mul] using hboth

end Algo
