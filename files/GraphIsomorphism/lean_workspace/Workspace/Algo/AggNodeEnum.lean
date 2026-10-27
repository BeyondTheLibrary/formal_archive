import Workspace.Algo.AggNodeRecompute
import Workspace.Algo.AggNodeCalls

/-! # The lists of one raw Recompute

Both lists come from the current raw loop state. The kernel action is renamed
by `tName`, which changes labels and leaves its kernel unchanged.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

/-- Extract the input of the flat Recompute from the local loop state. -/
def aggrInputOf (p : RawLCLoop) : AggrInput :=
  ((lcInst p).1, (p.1.2, p.2.2.2), lcIdx p)

section Stage

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}

/-- Renaming the test set does not change the kernel in line 04a. -/
theorem aggrKernel_eq (h : StateFor hc s st) :
    decGroup n (lcKer (aggrInputOf ((xs, tdom), st)).1
      (aggrInputOf ((xs, tdom), st)).2.1) = kerN s := by
  have hk := decGroup_lcKer (lcwf_lcInst h) rfl (h.himgs h.le)
  change decGroup n (lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2)) = _
  rw [hk]
  ext σ
  rw [mem_actKer, mem_kerN]
  let e := (tName m tdom hc.nodup hc.ltM).symm.permCongrHom
  constructor
  · rintro ⟨hσ, hker⟩
    have hσ' : σ ∈ s.H := h.grp ▸ hσ
    refine ⟨hσ', ?_⟩
    apply e.injective
    change e (psiOn ϕ (winSet m tdom) s.le ⟨σ, hσ'⟩) = e 1
    rw [map_one]
    exact hker
  · rintro ⟨hσ, hker⟩
    have hσ' : σ ∈ decGroup n st.2.1 := h.grp.symm ▸ hσ
    refine ⟨hσ', ?_⟩
    change e (psiOn ϕ (winSet m tdom) s.le ⟨σ, hσ⟩) = 1
    rw [hker, map_one]

/-- Eq. (69) for the representatives selected by the raw stage. -/
theorem aggrStage_cover (h : StateFor hc s st) :
    StrongStageCover s (aggrReps n (aggrInputOf ((xs, tdom), st)))
      ((aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n)) := by
  let P := aggrInputOf ((xs, tdom), st)
  have hI := lcwf_lcInst h
  have hker : decGroup n (lcKer P.1 P.2.1) = kerN s := aggrKernel_eq h
  constructor
  · have hcov := cover_lcPerms hI rfl
    rw [aggnDec_lcInst h] at hcov
    change (s.H : Set (Perm (Fin n))) =
      ⋃ σ ∈ aggrReps n P, σ • (kerN s : Set (Perm (Fin n)))
    rw [← hker]
    exact hcov
  · have hgs : RawGens.WF n (lcKer P.1 P.2.1) := wf_lcKer hI
    have hlt : ∀ u ∈ P.1.1, u < n := hI.1.2.2.2.1
    have hinv : rawIsInvariant (lcKer P.1 P.2.1, P.1.1) = true := by
      rw [rawIsInvariant_eq_true_iff hgs hlt]
      apply isInvariant_of_le ((rawIsInvariant_eq_true_iff hI.1.2.2.2.2.1 hlt).mp
        hI.1.2.2.2.2.2.2.2)
      exact lcKer_le hI rfl
    exact (iUnion_winOrbits hgs hlt hinv).trans (winSet_lcAffNew h)

/-- The raw lists have the factorial count and the orbit windows of §13.1. -/
theorem aggrStage_bound (h : StateFor hc s st) :
    StrongStageBound s (aggrReps n (aggrInputOf ((xs, tdom), st)))
      ((aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n)) := by
  let P := aggrInputOf ((xs, tdom), st)
  have hI := lcwf_lcInst h
  have hgs : RawGens.WF n (lcKer P.1 P.2.1) := wf_lcKer hI
  have hker : decGroup n (lcKer P.1 P.2.1) = kerN s := aggrKernel_eq h
  constructor
  · change (lcPerms n P.1 P.2).length ≤ Nat.factorial (winSet m tdom).ncard
    rw [length_lcPerms, ncard_winSet tdom hc.nodup hc.ltM]
    exact lcWidth_le_factorial hI rfl (h.himgs h.le)
  · change ((aggrWindows P).map (winSet n)).length ≤ Nat.card (Fin n)
    rw [List.length_map, Nat.card_fin]
    exact (length_winOrbits_le _ _).trans
      (length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1)
  · intro Δ hΔ
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hΔ
    obtain ⟨u, hu, rfl⟩ := winOrbits_mem hw
    have hu' : u < n := hI.1.2.2.2.1 u hu
    refine ⟨⟨u, hu'⟩, ?_, ?_⟩
    · rw [← winSet_lcAffNew h]
      exact hu
    · rw [← hker]
      ext v
      change (v : ℕ) ∈ rawOrbit (lcKer P.1 P.2.1, u) ↔ _
      rw [mem_rawOrbit_iff hgs hu']
      exact ⟨fun ⟨_, hv⟩ => hv, fun hv => ⟨v.isLt, hv⟩⟩

/-- A running stage has a window, so the flat phase can start its first chain. -/
theorem aggrWindows_pos (h : StateFor hc s st) (hrun : s.LoopCond) :
    0 < (aggrWindows (aggrInputOf ((xs, tdom), st))).length := by
  obtain ⟨u, hu, _⟩ := Set.not_subset.mp hrun.2
  have hcov := (aggrStage_cover h).windows
  rw [← hcov] at hu
  obtain ⟨Δ, hΔ, _⟩ := Set.mem_iUnion₂.mp hu
  obtain ⟨w, hw, _⟩ := List.mem_map.mp hΔ
  exact List.length_pos_of_mem hw

/-- The final hull is the whole answer of Recompute, hence a subgroup. -/
theorem aggrPhase_recompute (solve : RawWinSI → RawCoset)
    (h : StateFor hc s st) (hrun : s.LoopCond) :
    let P := aggrInputOf ((xs, tdom), st)
    PhaseMatch (aggrRound n solve) (aggrDecode n) (decCoset n) (P, none)
      (P.2.2 * (aggrWindows P).length) 0 (aggrInit (P, none))
      (recomputeStrong s (aggrReps n P) ((aggrWindows P).map (winSet n)))
      (fun B _ v => v.1 = P.2.2 ∧ B = (s.step.H : Set (Perm (Fin n))) ∧
        decCoset n v.2.2.2 = B) := by
  dsimp only
  let P := aggrInputOf ((xs, tdom), st)
  have hm := aggrPhaseMatch_value (aggrPhase_descent solve hc.lenStr
    (aggrWindows_pos h hrun))
  rw [aggrKernel_eq h] at hm
  have hv := run_recomputeStrong s _ _ (aggrStage_cover h)
  apply phaseMatch_weaken hm
  intro B j v hv'
  have hB : B = (s.step.H : Set (Perm (Fin n))) := hv'.2.trans hv
  refine ⟨hv'.1.1, hB, ?_⟩
  rw [hv'.1.2, hB]
  simpa only [one_smul] using cosetHull_smul_subgroup (1 : Perm (Fin n)) s.step.H

/-- The flattened round stops with the same answer as the whole Recompute child. -/
theorem aggrLoop_recompute (solve : RawWinSI → RawCoset)
    (h : StateFor hc s st) (hrun : s.LoopCond) :
    let P := aggrInputOf ((xs, tdom), st)
    LoopMatch (aggrRound n solve) (aggrDecode n) (decCoset n) (P, none)
      (P.2.2 * (aggrWindows P).length) 0 (aggrInit (P, none))
      (recomputeStrong s (aggrReps n P) ((aggrWindows P).map (winSet n))) := by
  dsimp only
  apply loopMatch_of_phaseMatch (aggrPhase_recompute solve h hrun) ?_ (le_refl _)
  intro B j v hv
  constructor
  · change aggrChild ((aggrInputOf ((xs, tdom), st), none), j, v) = none
    simp only [aggrChild, Option.elim_none]
    rw [if_neg (fun hh => by rw [hv.1] at hh; omega)]
  · exact hv.2.2

/-- The phase supplies precisely the hypothesis of `lcwStateFor_step`. -/
theorem aggrStateFor_step (h : StateFor hc s st)
    (hrun : lcCond ((xs, tdom), st) = true) {a : RawCoset}
    (ha : decCoset n a = (s.step.H : Set (Perm (Fin n)))) :
    StateFor hc s.step (lcStepWith a ((xs, tdom), st)).2 :=
  lcwStateFor_step (ha.trans (answer_lcInst h).symm) h hrun

/-- Flattening Recompute preserves the value of the existing two-level round. -/
theorem aggrRecompute_twoLevel (solve : RawWinSI → RawCoset) (h : StateFor hc s st) :
    let P := aggrInputOf ((xs, tdom), st)
    (recomputeStrong s (aggrReps n P) ((aggrWindows P).map (winSet n))).run =
      (lcRoundReduction n solve (lcInst ((xs, tdom), st))).run := by
  dsimp only
  rw [run_recomputeStrong _ _ _ (aggrStage_cover h),
    run_lcRoundReduction n solve (lcwf_lcInst h) (by intro hnone; cases hnone),
    answer_lcInst h]

end Stage

end Algo
