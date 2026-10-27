import Workspace.Algo.AggNodePairRound

/-! # Matching the two descents of a paired stage -/
set_option maxHeartbeats 1000000
namespace Algo
open Babai Equiv
open scoped Pointwise

/-- An actual descent call is emitted by the paired carrier with the same
window instance. The phase endpoint may already prepare the next descent. -/
theorem aggnPairPhase_sim {n : ℕ} (c : ℕ) (solve : RawWinSI → RawCoset)
    (p0 p : RawLCLoop) (ys : RawStr) (q0 q : RawCoset) (mode : Option RawCoset)
    (start : ℕ) (hcond : lcCond p = true) (hq : q.isSome = true)
    (hpos : 0 < aggnrCount (aggnPairInput c p ys q mode))
    (hroom : start + aggnrCount (aggnPairInput c p ys q mode) *
      (aggnrWindows (aggnPairInput c p ys q mode)).length ≤ aggnPairWidth (p0, ys, q0))
    {S : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))} {Post : Set (Perm (Fin n)) → ℕ → AggnRecomputeState → Prop}
    (hm : let P := aggnPairInput c p ys q mode
      PhaseMatch (aggnrRound n solve) (aggnrDecode n) (decCoset n) (P, none)
        (aggnrCount P * (aggnrWindows P).length) 0 (aggnrInit (P, none)) S Post) :
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((p0, ys, q0), none)
      (aggnrCount (aggnPairInput c p ys q mode) * (aggnrWindows (aggnPairInput c p ys q mode)).length)
      start (aggnPairStart c p ys q mode) S
      (fun B j v => ∃ jR vR, Post B jR vR ∧ j = start + jR ∧
        v = aggnPairPack c p ys q mode jR vR) := by
  let P := aggnPairInput c p ys q mode
  change start + aggnrCount P * (aggnrWindows P).length ≤ _ at hroom
  let Rel := fun jR vR jM vM => jM = start + jR ∧ vM = aggnPairPack c p ys q mode jR vR
  have hinit : Rel 0 (aggnrInit (P, none)) start (aggnPairStart c p ys q mode) := by
    refine ⟨by omega, ?_⟩
    symm
    simp only [aggnPairPack, aggnrInit]
    rw [if_pos hpos]
    rfl
  exact aggnPhaseMatch_sim (R := aggnrRound n solve)
    (M := aggnPairRound c n solve) (decI := aggnrDecode n) (decI' := aggnPairDecode n)
    (decA := decCoset n) (I := (P, none)) (I' := ((p0, ys, q0), none)) Rel (by
      intro jR vR jM vM hr J hJ
      obtain ⟨hjM, rfl⟩ := hr
      change aggnrChild ((P, none), jR, vR) = some J at hJ
      obtain ⟨a, _, ha, ht, hiw, hjR, hJdef⟩ := aggnrChild_some hJ
      dsimp only at ht hjR hJdef
      have hglobal : jM < aggnPairWidth (p0, ys, q0) := by omega
      refine ⟨((p0, ys, q0), J.2), ?_, ?_, ?_⟩
      · dsimp only [aggnPairRound]
        rw [aggnPairPack, if_pos ht]
        simp only [aggnPairChild, Option.elim_none]
        rw [if_pos ⟨hcond, hq, hglobal⟩, hJ]
        rfl
      · rw [hJdef]
        rfl
      · intro a
        refine ⟨by omega, ?_⟩
        dsimp only [aggnPairRound, aggnrRound]
        rw [aggnPairPack, if_pos ht]
        rfl) hm hinit

section Stage
variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {i : ℕ} {st st0 : RawLCSt} {σ : Perm (Fin n)} {q0 q : RawCoset}

/-- Line 04e1 finishes with its answer saved for the second descent. -/
theorem aggnPairPhase_source (c : ℕ) (solve : RawWinSI → RawCoset)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE)
    (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom)) (hq : q.isSome = true)
    {start : ℕ} (hstart : start ≤ i * (2 * (Nat.factorial tdom.length * n))) :
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((((xs, tdom), st0), ys, q0), none) (Nat.factorial tdom.length * n)
      start (aggnPairStart c ((xs, tdom), st) ys q none)
      (recomputeStrong (stages ϕ (decStrN n xs) (winSet m tdom) i)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).reps i)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).windows i))
      (fun B j v => ∃ H, decCoset n H = B ∧
        B = ((stages ϕ (decStrN n xs) (winSet m tdom) i).step.H : Set (Perm (Fin n))) ∧
        v = aggnPairStart c ((xs, tdom), st) ys q (some H) ∧
        j ≤ i * (2 * (Nat.factorial tdom.length * n)) + Nat.factorial tdom.length * n) := by
  let p : RawLCLoop := ((xs, tdom), st)
  have hrun := loopCond_of_lt_haltIndex ϕ (decStrN n xs) (winSet m tdom) hi
  have hcond : lcCond p = true := (lcCond_eq_true_iff h).mpr hrun
  have hn : i < n := hi.trans_le (by simpa only [Nat.card_fin] using (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)))
  have hwidth := aggnrWidth_le c h hg
  have hpos : 0 < aggnrCount (aggnrInputOf c p) := by
    rw [aggnrCount_eq c h hg, aggkIdx_eq_card h]
    exact Nat.card_pos
  have hroom : start + aggnrCount (aggnrInputOf c p) * (aggnrWindows (aggnrInputOf c p)).length ≤
      aggnPairWidth (((xs, tdom), st0), ys, q0) := by
    dsimp only [aggnPairWidth, aggnCertWidth, aggnCertStageWidth]
    rw [hc.lenStr]
    have hh := Nat.mul_le_mul_right (2 * (Nat.factorial tdom.length * n)) (show i + 1 ≤ n by omega)
    nlinarith
  have hm := aggnPairPhase_sim c solve ((xs, tdom), st0) p ys q0 q none start hcond hq hpos hroom
    (aggnrPhase_recompute c solve h hg hrun)
  rw [aggkTypedT_eq_points hc hs] at hm
  apply phaseMatch_mono (phaseMatch_weaken hm ?_) hwidth
  rintro B j v ⟨jR, vR, hr, hj, hv⟩
  refine ⟨vR.2.2.2, hr.2.2.1, hr.2.1, ?_, ?_⟩
  · unfold aggnPairPack at hv
    dsimp only [aggnPairInput, Option.elim_none] at hv
    have hstop : ¬ vR.1 < aggnrCount (aggnrInputOf c p) := Nat.not_lt.mpr hr.1.ge
    rw [if_neg hstop] at hv
    exact hv
  · have hjR := hr.2.2.2
    omega

/-- Line 04e2 uses the old stage, then installs both new answers together. -/
theorem aggnPairPhase_target (c : ℕ) (solve : RawWinSI → RawCoset)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE)
    (hσ : σ ∈ G) (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom))
    (hq : q.isSome = true)
    (hQ : decCoset n q = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i)
    {H : RawCoset} (hH : decCoset n H = ((stages ϕ (decStrN n xs) (winSet m tdom) i).step.H : Set (Perm (Fin n))))
    {start : ℕ} (hstart : start ≤ i * (2 * (Nat.factorial tdom.length * n)) + Nat.factorial tdom.length * n) :
    PhaseMatch (aggnPairRound c n solve) (aggnPairDecode n) (decCoset n)
      ((((xs, tdom), st0), ys, q0), none) (Nat.factorial tdom.length * n)
      start (aggnPairStart c ((xs, tdom), st) ys q (some H))
      (strongDescent (kerN (stages ϕ (decStrN n xs) (winSet m tdom) i))
        (decStrN n xs) (decStrN n ys)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).compareReps i)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).windows i))
      (fun B j v => ∃ st' q', StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) (i + 1)) st' ∧
        decCoset n q' = B ∧ B = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ (i + 1) ∧
        v = aggnPairStart c ((xs, tdom), st') ys q' none ∧
        j ≤ (i + 1) * (2 * (Nat.factorial tdom.length * n))) := by
  let p : RawLCLoop := ((xs, tdom), st)
  have hrun := loopCond_of_lt_haltIndex ϕ (decStrN n xs) (winSet m tdom) hi
  have hcond : lcCond p = true := (lcCond_eq_true_iff h).mpr hrun
  have hn : i < n := hi.trans_le (by simpa only [Nat.card_fin] using (haltIndex_le_card (ϕ := ϕ) (x := decStrN n xs) (T := winSet m tdom)))
  have hwidth := aggnCompareWidth_le (ys := ys) (q := q) c h hg
  have hpos : 0 < aggnrCount (aggnCompareInputOf c (p, ys, q)) := by
    cases q with
    | none => simp at hq
    | some q =>
      change 0 < (aggnTranslateReps (xs, some q, aggkRawReps c p)).length
      simp only [aggnTranslateReps, Option.elim_some, rawGensMul, normGens, List.length_map]
      change 0 < aggnrCount (aggnrInputOf c p)
      rw [aggnrCount_eq c h hg, aggkIdx_eq_card h]
      exact Nat.card_pos
  have hroom : start + aggnrCount (aggnCompareInputOf c (p, ys, q)) *
      (aggnrWindows (aggnCompareInputOf c (p, ys, q))).length ≤
      aggnPairWidth (((xs, tdom), st0), ys, q0) := by
    dsimp only [aggnPairWidth, aggnCertWidth, aggnCertStageWidth]
    rw [hc.lenStr]
    have hh := Nat.mul_le_mul_right (2 * (Nat.factorial tdom.length * n)) (show i + 1 ≤ n by omega)
    nlinarith
  have hm := aggnPairPhase_sim c solve ((xs, tdom), st0) p ys q0 q (some H) start hcond hq hpos hroom
    (aggnComparePhase_stage c solve h hg hs hσ hi hQ)
  apply phaseMatch_mono (phaseMatch_weaken hm ?_) hwidth
  rintro B j v ⟨jR, vR, hr, hj, hv⟩
  have hst := aggrStateFor_step h hcond hH
  refine ⟨(lcStepWith H p).2, vR.2.2.2, hst, hr.2.2.1, hr.2.1, ?_, ?_⟩
  · unfold aggnPairPack at hv
    dsimp only [aggnPairInput, Option.elim_some] at hv
    have hstop : ¬ vR.1 < aggnrCount (aggnCompareInputOf c (p, ys, q)) := Nat.not_lt.mpr hr.1.ge
    rw [if_neg hstop] at hv
    rw [hv]
    congr 1
    exact Prod.ext (lcwStep_fst _ _) rfl
  · have hjR := hr.2.2.2
    rw [Nat.succ_mul]
    omega

end Stage
end Algo
