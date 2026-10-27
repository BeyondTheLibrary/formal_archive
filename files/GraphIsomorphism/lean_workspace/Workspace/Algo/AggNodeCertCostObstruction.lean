import Workspace.Algo.AggNodeCertBounds
import Workspace.Algo.RoundQ

/-! # The remaining machine-interface obligation

The phase carrier proves the fixed-tree match. Its child routine still trusts
cached Recompute data. `Round.child_wf` quantifies over every state, so a
machine round must check or normalize that cache before emitting a child.
The result below exhibits the exact failure. This is not a claim about the
paper or about a state reached by the matched certificate phase.
-/
namespace Algo
open RAM RAM.Targets

/-- The size of the source string is at most the size of its window instance. -/
theorem aggnWindow_source_size (W : RawWinSI) : Enc.size W.2.2.2.1 ≤ Enc.size W :=
  (size_fst_le' W.2.2.2).trans ((size_snd_le' W.2.2).trans
    ((size_snd_le' W.2).trans (size_snd_le' W)))

/-- Arbitrarily large cached strings can be emitted from the same parent.
The activity and width assumptions are exactly the gates in the child routine. -/
theorem aggnPhase_child_unbounded (c : ℕ) (C : AggnPhaseCtx) (a : AggnJob)
    (p : RawLCLoop) (hactive : lcCond p = true)
    (hphase : 0 < aggnPhaseWidth c C) (hjob : 0 < aggnCertWidth (aggnJobLoop C a))
    (B : ℕ) :
    ∃ s : AggnPhaseState, ∃ J : AggnPhaseNode,
      aggnPhaseChild c ((C, none), 0, s) = some J ∧ B < Enc.size J := by
  let xs : RawStr := List.replicate (B + 1) 0
  let P : AggnRecomputeInput := (([], [], [], xs, []), [], [[]], [[]])
  let v : AggnCertState := (p, P, 0, (0, 0, some ([], []), none))
  let s : AggnPhaseState := ([a], ([], []), 0, v)
  let W := aggnrLeaf P 0 ([], [])
  let J : AggnPhaseNode := (C, some W)
  refine ⟨s, J, ?_, ?_⟩
  · simp only [aggnPhaseChild, s, v, Option.elim_none, if_pos hphase]
    simp only [aggnCertChild, Option.elim_none, hactive, hjob, and_self, if_true]
    simp [aggnrChild, aggnrCount, aggnrWindows, P, J, W]
  · have hl : B + 1 ≤ Enc.size xs := by
      simpa only [xs, List.length_replicate] using length_le_size xs
    have hW : Enc.size xs ≤ Enc.size W := aggnWindow_source_size W
    have ho : Enc.size W ≤ Enc.size (some W) := by rw [size_some_eq]; omega
    have hJ : Enc.size (some W) ≤ Enc.size J := size_snd_le' J
    omega

/-- Any well-formedness predicate closed under these children fails a fixed
instance-size bound at a parent for which both width gates are open. -/
theorem aggnPhase_child_bound_impossible (c : ℕ) (C : AggnPhaseCtx) (a : AggnJob)
    (p : RawLCLoop) (hactive : lcCond p = true)
    (hphase : 0 < aggnPhaseWidth c C) (hjob : 0 < aggnCertWidth (aggnJobLoop C a))
    (WF : AggnPhaseNode → Prop) (hroot : WF (C, none))
    (hclosed : ∀ j s J, WF (C, none) → aggnPhaseChild c ((C, none), j, s) = some J → WF J) :
    ¬ ∃ B, ∀ J, WF J → Enc.size J ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨s, J, hJ, hs⟩ := aggnPhase_child_unbounded c C a p hactive hphase hjob B
  exact (Nat.not_lt_of_ge (hB J (hclosed 0 s J hroot hJ))) hs

/-- Even the carrier's instance bound alone cannot satisfy `CostQ`.
The carrier allows arbitrary window leaves at the fixed ground size one. -/
theorem aggnPhase_no_costQ (c : ℕ) : ¬ Nonempty (Round.CostQ (aggnPhaseRound c 1)) := by
  rintro ⟨K⟩
  let xs : RawStr := List.replicate (K.bound 1 + 1) 0
  let C : AggnPhaseCtx := ((([0], []), ([], [])), [0], [0], [])
  let W : RawWinSI := ([], [], [], xs, [])
  let I : AggnPhaseNode := (C, some W)
  have hI : (aggnPhaseRound c 1).WF I := rfl
  have hsize : Enc.size I ≤ K.bound 1 := K.size_le I hI
  have hl : K.bound 1 + 1 ≤ Enc.size xs := by
    simpa only [xs, List.length_replicate] using length_le_size xs
  have hW : Enc.size xs ≤ Enc.size W := aggnWindow_source_size W
  have ho : Enc.size W ≤ Enc.size (some W) := by rw [size_some_eq]; omega
  have hi : Enc.size (some W) ≤ Enc.size I := size_snd_le' I
  omega

end Algo
