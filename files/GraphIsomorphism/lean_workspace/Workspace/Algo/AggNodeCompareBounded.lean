import Workspace.Algo.AggNodeCompareEnvelope

/-! # A degree-uniform comparison program with bounded state

Shorten each answer and check the retained state size. The next file proves
that one fixed cap exponent preserves every legitimate comparison execution.
The machine bounds here hold for every state and supplied answer.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnCompareStateCap (d n : ℕ) : ℕ :=
  2 ^ ((Nat.log 2 n + 2) ^ d) + Enc.size (default : AggnCompareState)

def aggnCompareCapState (d : ℕ) (p : ℕ × AggnCompareState) : AggnCompareState :=
  if Enc.size p.2 ≤ aggnCompareStateCap d p.1 then p.2 else default

theorem aggnCompareCapState_size (d n : ℕ) (s : AggnCompareState) :
    Enc.size (aggnCompareCapState d (n, s)) ≤ aggnCompareStateCap d n := by
  unfold aggnCompareCapState
  split
  · assumption
  · exact Nat.le_add_left _ _

theorem aggnCompareCapState_eq {d n : ℕ} {s : AggnCompareState}
    (h : Enc.size s ≤ aggnCompareStateCap d n) : aggnCompareCapState d (n, s) = s := if_pos h

theorem aggnPolyFun_compareStateCap (d : ℕ) : PolyFun (aggnCompareStateCap d) :=
  (aggnPolyFun_sizeCap d).add (polyFun_const (Enc.size (default : AggnCompareState)))

theorem aggnQuasiPolyBound_compareStateCap (d : ℕ) : QuasiPolyBound (aggnCompareStateCap d) :=
  (quasiPolyBound_witness d).add (polyBound_const (Enc.size (default : AggnCompareState))).quasiPoly

theorem aggnMono_compareStateCap (d : ℕ) : Monotone (aggnCompareStateCap d) := by
  intro a b hab
  exact Nat.add_le_add_right (quasiPolyBound_witness_mono d hab) _

theorem aggnPolyFun_compareCapState (d : ℕ) : PolyFun (aggnCompareCapState d) := by
  have hs : PolyFun (Enc.size : AggnCompareState → ℕ) := AggnSizeRoutine.polyFun_size
  have ht : PolyFun (fun p : ℕ × AggnCompareState => decide (Enc.size p.2 ≤ aggnCompareStateCap d p.1)) :=
    ((polyFun_snd.comp hs).pair (polyFun_fst.comp (aggnPolyFun_compareStateCap d))).comp polyFun_le
  exact (PolyFun.ite ht polyFun_snd (polyFun_const default)).of_eq
    (fun p => by simp only [decide_eq_true_eq]; rfl)

def aggnCompareBoundedInit (c d : ℕ) (I : AggnPhaseNode) : AggnCompareState :=
  aggnCompareCapState d (I.1.2.1.length, (aggnCompareCheckedRound c).init I)

def aggnCompareBoundedCombine (c d : ℕ) (z : AggnPhaseNode × ℕ × AggnCompareState × RawCoset) :
    AggnCompareState :=
  aggnCompareCapState d (z.1.1.2.1.length,
    aggnCompareCombine c (z.1, z.2.1, z.2.2.1, aggnNormAnswer z.1.1.2.1 z.2.2.2))

def aggnCompareBoundedRound (c d : ℕ) : Round AggnPhaseNode AggnCompareState RawCoset where
  WF := (aggnCompareCheckedRound c).WF
  ground := (aggnCompareCheckedRound c).ground
  measure := (aggnCompareCheckedRound c).measure
  width := (aggnCompareCheckedRound c).width
  child := (aggnCompareCheckedRound c).child
  init := aggnCompareBoundedInit c d
  combine := aggnCompareBoundedCombine c d
  finish := (aggnCompareCheckedRound c).finish
  bot := none
  child_eq_none := (aggnCompareCheckedRound c).child_eq_none
  child_wf := (aggnCompareCheckedRound c).child_wf
  child_measure := (aggnCompareCheckedRound c).child_measure
  child_ground := (aggnCompareCheckedRound c).child_ground

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnQuasiFun_compareBoundedInit (c d : ℕ) : QuasiFun (aggnCompareBoundedRound c d).init := by
  have hg : PolyFun (aggnCompareBoundedRound c d).ground := aggnPolyFun_ground c d 0
  have hm := (hg.quasiFun.pair (aggnQuasiFun_compareInit c 0)).comp_poly (aggnPolyFun_compareCapState d)
  exact hm.of_eq (fun _ => by dsimp only [aggnCompareBoundedRound, aggnCompareBoundedInit,
    aggnCompareCheckedRound, aggnCompareRound])

theorem aggnQuasiFun_compareBoundedCombine (c d : ℕ) : QuasiFun (aggnCompareBoundedRound c d).combine := by
  have hz : PolyFun (fun z : AggnPhaseNode × ℕ × AggnCompareState × RawCoset => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hx := pfst (psnd (pfst hI))
  have hn := hx.comp polyFun_length
  have hans := (hx.pair ha).comp aggnPolyFun_normAnswer
  have hnext := (hI.pair (hj.pair (hs.pair hans))).comp_quasiFun (aggnQuasiFun_compareCombine c)
  have hm := (hn.quasiFun.pair hnext).comp_poly (aggnPolyFun_compareCapState d)
  exact hm.of_eq (fun _ => by dsimp only [aggnCompareBoundedRound, aggnCompareBoundedCombine])

/-- One executable comparison carrier for all degrees, including its validity test. -/
theorem aggnCompareBounded_hasRunCostQ (c d : ℕ) :
    Nonempty (Round.RunCostQ (aggnCompareBoundedRound c d)) := by
  obtain ⟨W, hW, hWmono, hwidth⟩ := aggnCompareChecked_width_bound c
  refine ⟨{
    bound := fun k => aggnCheckedBound k + 2
    polyBound_bound := aggnPolyBound_checked.add (polyBound_const 2)
    mono_bound := fun _ _ h => Nat.add_le_add_right (aggnMono_checkedBound h) 2
    stateBound := aggnCompareStateCap d
    quasiPolyBound_stateBound := aggnQuasiPolyBound_compareStateCap d
    mono_stateBound := aggnMono_compareStateCap d
    widthBound := W
    quasiPolyBound_widthBound := hW
    quasiFun_child := aggnQuasiFun_compareCheckedChild c
    quasiFun_init := aggnQuasiFun_compareBoundedInit c d
    quasiFun_combine := aggnQuasiFun_compareBoundedCombine c d
    quasiFun_finish := quasiFun_const none
    ground_le := fun I => (length_le_size I.1.2.1).trans
      ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans (size_fst_le' I)))
    size_le := fun I hI => (aggnCheckedRound_size c I.1.2.1.length I hI).trans (Nat.le_add_right _ 2)
    init_le := by
      intro I _
      dsimp only [aggnCompareBoundedRound, aggnCompareBoundedInit, aggnCompareCheckedRound, aggnCompareRound]
      exact aggnCompareCapState_size d I.1.2.1.length _
    combine_le := by
      intro I _ _ _ _ _ _
      dsimp only [aggnCompareBoundedRound, aggnCompareBoundedCombine, aggnCompareCheckedRound, aggnCompareRound]
      exact aggnCompareCapState_size d I.1.2.1.length _
    finish_le := fun I _ _ _ => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound I.1.2.1.length + 2
      rw [size_none]
      omega
    bot_le := fun m => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound m + 2
      rw [size_none]
      omega
    width_le := fun I hI => hwidth I hI
    polyFun_ground := aggnPolyFun_ground c d 0
    wfCheck := aggnUniformWfCheck
    polyFun_wfCheck := aggnPolyFun_uniformWfCheck
    wfCheck_eq_true := aggnUniformWfCheck_spec c d
    measureBound := fun _ => 1
    polyBound_measureBound := polyBound_const 1
    mono_measureBound := fun _ _ _ => le_rfl
    measure_le := ?_ }⟩
  intro I _
  change I.2.elim 1 (fun _ => 0) ≤ 1
  cases I.2 <;> simp

noncomputable def aggnCompareBoundedRunCostQ (c d : ℕ) : Round.RunCostQ (aggnCompareBoundedRound c d) :=
  Classical.choice (aggnCompareBounded_hasRunCostQ c d)

end Algo
