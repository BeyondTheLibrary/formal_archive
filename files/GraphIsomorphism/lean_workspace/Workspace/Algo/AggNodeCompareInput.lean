import Workspace.Algo.AggNodePairEnum
import Workspace.Algo.AggNodeCheckedLocal

/-! # Preparing the comparison descent

The comparison uses the source kernel and its ordered windows. Translate
its source representatives by the canonical element of the current coset.
The normalizers make this preparation insensitive to every raw encoding
of a correct comparison answer.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- Translate a stored representative list by the canonical coset element. -/
def aggnTranslateReps (p : RawStr × RawCoset × RawGens) : RawGens :=
  p.2.1.elim [] fun q =>
    rawGensMul (aggnCanonCoset ((p.1, q.1), q.2), normGens (p.1, p.2.2))

theorem aggnPolyFun_translateReps : PolyFun aggnTranslateReps := by
  have hsome : PolyFun (fun z : (RawGens × RawPerm) × (RawStr × RawGens) =>
      rawGensMul (aggnCanonCoset ((z.2.1, z.1.1), z.1.2), normGens z.2)) :=
    (((((polyFun_snd.comp polyFun_fst).pair (polyFun_fst.comp polyFun_fst)).pair
      (polyFun_fst.comp polyFun_snd)).comp aggnPolyFun_canonCoset).pair
      (polyFun_snd.comp polyFun_normGens)).comp polyFun_rawGensMul
  exact (((polyFun_snd.comp polyFun_fst).pair
    (polyFun_fst.pair (polyFun_snd.comp polyFun_snd))).comp
      (PolyFun.optionElim (polyFun_const []) hsome)).of_eq (fun p => by cases hq : p.2.1 <;> simp [aggnTranslateReps, hq])

/-- Translation decodes to multiplication by the mathematical coset choice
without any well-formedness premise on the stored coset or source lifts. -/
theorem aggnTranslateReps_decode {n : ℕ} {xs : RawStr} (hx : xs.length = n)
    (gs : RawGens) (r : RawPerm) (reps : RawGens) :
    (aggnTranslateReps (xs, some (gs, r), reps)).map (decPerm n) =
      (reps.map (decPerm n)).map (aggnLeastPerm (decCoset n (some (gs, r))) * ·) := by
  simp only [aggnTranslateReps, Option.elim_some, rawGensMul, normGens, List.map_map]
  apply List.map_congr_left
  intro a ha
  dsimp only [Function.comp_def]
  rw [rawMul_of_wf (aggnCanonCoset_spec hx gs r).1 (wf_normPerm hx a),
    decPerm_encPerm, decPerm_normPerm hx, aggnCanonCoset_eq_least hx, decPerm_encPerm]

abbrev AggnCompareInput := RawLCLoop × RawStr × RawCoset

/-- The comparison strings and current candidate coset. -/
def aggnCompareWindow (z : AggnCompareInput) : RawWinSI :=
  let q := z.2.2.getD ([], rawOne z.1.1.1)
  ((lcInst z.1).1.1, tidyGens (z.1.1.1, q.1), normPerm (z.1.1.1, q.2), z.1.1.1, z.2.1)

/-- Lines 04d2--04e2 use the same kernel and windows as the source descent. -/
def aggnCompareInputOf (c : ℕ) (z : AggnCompareInput) : AggnRecomputeInput :=
  let P := aggnrInputOf c z.1
  (aggnCompareWindow z, P.2.1, aggnTranslateReps (z.1.1.1, z.2.2, P.2.2.1), P.2.2.2)

theorem aggnPolyFun_compareWindow : PolyFun aggnCompareWindow := by
  have hx : PolyFun (fun z : AggnCompareInput => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hq : PolyFun (fun z : AggnCompareInput => z.2.2.getD ([], rawOne z.1.1.1)) :=
    ((polyFun_snd.comp polyFun_snd).pair
      ((polyFun_const ([] : RawGens)).pair (hx.comp polyFun_rawOne))).comp polyFun_optionGetD
  have hw : PolyFun (fun z : AggnCompareInput => (lcInst z.1).1.1) := ((polyFun_fst.comp polyFun_lcInst).comp polyFun_fst).comp polyFun_fst
  exact hw.pair (((hx.pair (hq.comp polyFun_fst)).comp polyFun_tidyGens).pair
    (((hx.pair (hq.comp polyFun_snd)).comp polyFun_normPerm).pair
      (hx.pair (polyFun_snd.comp polyFun_fst))))

theorem aggnQuasiFun_compareInput (c : ℕ) : QuasiFun (aggnCompareInputOf c) := by
  have hp : QuasiFun (fun z : AggnCompareInput => aggnrInputOf c z.1) := polyFun_fst.comp_quasiFun (aggnQuasiFun_recomputeInput c)
  have hx : PolyFun (fun z : AggnCompareInput => z.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hq : PolyFun (fun z : AggnCompareInput => z.2.2) := polyFun_snd.comp polyFun_snd
  have hrs := hp.comp_poly ((polyFun_snd.comp polyFun_snd).comp polyFun_fst)
  have ht := (hx.quasiFun.pair (hq.quasiFun.pair hrs)).comp_poly aggnPolyFun_translateReps
  exact aggnPolyFun_compareWindow.quasiFun.pair
    ((hp.comp_poly (polyFun_snd.comp polyFun_fst)).pair
      (ht.pair (hp.comp_poly ((polyFun_snd.comp polyFun_snd).comp polyFun_snd))))

section Stage
variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs ys : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {i : ℕ} {st : RawLCSt} {σ : Perm (Fin n)} {q : RawCoset}

/-- The prepared comparison gives exactly the fixed strong-descent tree. -/
theorem aggnCompareTree_eq (c : ℕ)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE)
    (hQ : decCoset n q = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i) :
    let P := aggnCompareInputOf c (((xs, tdom), st), ys, q)
    strongDescent (decGroup n P.2.1) (decStrN n xs) (decStrN n ys)
      (aggnrReps n P) ((aggnrWindows P).map (winSet n)) =
      strongDescent (kerN (stages ϕ (decStrN n xs) (winSet m tdom) i))
        (decStrN n xs) (decStrN n ys)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).compareReps i)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).windows i) := by
  dsimp only
  change strongDescent (decGroup n (aggnrInputOf c ((xs, tdom), st)).2.1) _ _
    ((aggnTranslateReps (xs, q, aggkRawReps c ((xs, tdom), st))).map (decPerm n))
    ((aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n)) = _
  rw [show decGroup n (aggnrInputOf c ((xs, tdom), st)).2.1 =
    kerN (stages ϕ (decStrN n xs) (winSet m tdom) i) from aggrKernel_eq h,
    aggkStage_windows_eq h]
  apply aggkStrongDescent_congr
  cases q with
  | none =>
    have hnil : ¬ (pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i).Nonempty := by
      rw [← hQ]
      exact Set.not_nonempty_empty
    simp [aggnTranslateReps, aggnCanonicalPair, hnil]
  | some q =>
    have hne : (pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i).Nonempty := by
      rw [← hQ, decCoset_some]
      exact ⟨decPerm n q.2, 1, (decGroup n q.1).one_mem, by simp⟩
    rw [aggnTranslateReps_decode hc.lenStr, hQ]
    simp only [aggnCanonicalPair, if_pos hne, List.map_map]
    have he := congrArg (List.map (fun K => aggnLeastPerm
      (pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i) • K))
        (aggkRawReps_cosets c h hg)
    rw [aggkTypedT_eq_points hc hs] at he
    simpa only [List.map_map, Function.comp_def, smul_smul] using he

/-- Preparing comparison representatives adds no calls to the source width. -/
theorem aggnCompareWidth_le (c : ℕ)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    let P := aggnCompareInputOf c (((xs, tdom), st), ys, q)
    aggnrCount P * (aggnrWindows P).length ≤ Nat.factorial tdom.length * n := by
  dsimp only
  apply le_trans (Nat.mul_le_mul_right _ ?_) (aggnrWidth_le c h hg)
  change (aggnTranslateReps (xs, q, aggkRawReps c ((xs, tdom), st))).length ≤
    (aggkRawReps c ((xs, tdom), st)).length
  cases q <;> simp [aggnTranslateReps, rawGensMul, normGens]

private theorem aggnCosetHull_paired (ϕ : G →* Perm (Fin m))
    (x y : Fin n → ℕ) (T : Set (Fin m)) {σ : Perm (Fin n)} (hσ : σ ∈ G) (i : ℕ) :
    cosetHull (pairedQ ϕ x y T σ i) = pairedQ ϕ x y T σ i := by
  rcases Set.eq_empty_or_nonempty (pairedQ ϕ x y T σ i) with he | ⟨π, hπ⟩
  · rw [he, cosetHull_empty]
  · rw [pairedQ_eq_coset hσ i hπ, cosetHull_smul_subgroup]

/-- Line 04e2, including every raw encoding of every recursive answer. -/
theorem aggnComparePhase_stage (c : ℕ) (solve : RawWinSI → RawCoset)
    (h : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) i) st)
    (hg : tdom.length ≤ guardBound c xs.length) (hs : tdom.SortedLE)
    (hσ : σ ∈ G) (hi : i < haltIndex ϕ (decStrN n xs) (winSet m tdom))
    (hQ : decCoset n q = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ i) :
    let P := aggnCompareInputOf c (((xs, tdom), st), ys, q)
    PhaseMatch (aggnrRound n solve) (aggnrDecode n) (decCoset n) (P, none)
      (aggnrCount P * (aggnrWindows P).length) 0 (aggnrInit (P, none))
      (strongDescent (kerN (stages ϕ (decStrN n xs) (winSet m tdom) i))
        (decStrN n xs) (decStrN n ys)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).compareReps i)
        ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).windows i))
      (fun B j v => v.1 = aggnrCount P ∧
        B = pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ (i + 1) ∧
        decCoset n v.2.2.2 = B ∧ j ≤ aggnrCount P * (aggnrWindows P).length) := by
  dsimp only
  let P := aggnCompareInputOf c (((xs, tdom), st), ys, q)
  have hpos : 0 < (aggnrWindows P).length :=
    aggrWindows_pos h (loopCond_of_lt_haltIndex ϕ (decStrN n xs) (winSet m tdom) hi)
  have hm := aggrPhaseMatch_value (aggnrPhase_descent (P := P) solve hc.lenStr hpos)
  have he := aggnCompareTree_eq c h hg hs hQ
  change strongDescent (decGroup n P.2.1) (decStrN n P.1.2.2.2.1)
    (decStrN n P.1.2.2.2.2) (aggnrReps n P) ((aggnrWindows P).map (winSet n)) = _ at he
  rw [he] at hm
  have hv : (strongDescent (kerN (stages ϕ (decStrN n xs) (winSet m tdom) i))
      (decStrN n xs) (decStrN n ys)
      ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).compareReps i)
      ((aggnCanonicalPair ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ).windows i)).run =
      pairedQ ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) σ (i + 1) := by
    rw [run_strongDescent,
      (aggnCanonicalPair_cover ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) hσ).source i hi |>.windows,
      ← (aggnCanonicalPair_cover ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) hσ).comparison i hi,
      ← pairedQ_succ]
  apply phaseMatch_weaken hm
  intro B j v hb
  have hB := hb.2.trans hv
  refine ⟨hb.1.1, hB, ?_, hb.1.2.2⟩
  rw [hb.1.2.1, hB, aggnCosetHull_paired ϕ _ _ _ hσ]

end Stage
end Algo
