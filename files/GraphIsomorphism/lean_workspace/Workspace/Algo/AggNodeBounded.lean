import Workspace.Algo.AggNodeEnvelope

/-! # A certificate carrier whose state is bounded on every input

The size check is applied after initialization and after every update.
Later preservation lemmas use the proved execution bound to show that the
check never discards a valid certificate state. Arbitrary answer encodings
are shortened before they enter the retained state.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnZeroPhase : AggnPhaseState := default

def aggnStateCap (d n : ℕ) : ℕ :=
  2 ^ ((Nat.log 2 n + 2) ^ d) + Enc.size aggnZeroPhase

def aggnCapState (d : ℕ) (p : ℕ × AggnPhaseState) : AggnPhaseState :=
  if Enc.size p.2 ≤ aggnStateCap d p.1 then p.2 else aggnZeroPhase

theorem aggnCapState_size (d n : ℕ) (s : AggnPhaseState) :
    Enc.size (aggnCapState d (n, s)) ≤ aggnStateCap d n := by
  unfold aggnCapState
  split
  · assumption
  · exact Nat.le_add_left _ _

theorem aggnCapState_eq {d n : ℕ} {s : AggnPhaseState}
    (h : Enc.size s ≤ aggnStateCap d n) : aggnCapState d (n, s) = s := if_pos h

theorem aggnPolyFun_stateCap (d : ℕ) : PolyFun (aggnStateCap d) :=
  (aggnPolyFun_sizeCap d).add (polyFun_const (Enc.size aggnZeroPhase))

theorem aggnQuasiPolyBound_stateCap (d : ℕ) : QuasiPolyBound (aggnStateCap d) :=
  (quasiPolyBound_witness d).add (polyBound_const (Enc.size aggnZeroPhase)).quasiPoly

theorem aggnMono_stateCap (d : ℕ) : Monotone (aggnStateCap d) := by
  intro a b hab
  exact Nat.add_le_add_right (quasiPolyBound_witness_mono d hab) _

theorem aggnPolyFun_capState (d : ℕ) : PolyFun (aggnCapState d) := by
  have ht : PolyFun (fun p : ℕ × AggnPhaseState => decide (Enc.size p.2 ≤ aggnStateCap d p.1)) :=
    ((polyFun_snd.comp aggnPolyFun_stateSize).pair
      (polyFun_fst.comp (aggnPolyFun_stateCap d))).comp polyFun_le
  exact (PolyFun.ite ht polyFun_snd (polyFun_const aggnZeroPhase)).of_eq
    (fun p => by simp only [decide_eq_true_eq]; rfl)

def aggnBoundedInit (c d : ℕ) (I : AggnPhaseNode) : AggnPhaseState :=
  aggnCapState d (I.1.2.1.length, (aggnCheckedRound c 0).init I)

def aggnBoundedCombine (c d : ℕ) (z : AggnPhaseNode × ℕ × AggnPhaseState × RawCoset) : AggnPhaseState :=
  aggnCapState d (z.1.1.2.1.length,
    aggnPhaseCombine c (z.1, z.2.1, z.2.2.1, aggnNormAnswer z.1.1.2.1 z.2.2.2))

/-- The checked carrier with bounded retained state and normalized answers. -/
def aggnBoundedRound (c d n : ℕ) : Round AggnPhaseNode AggnPhaseState RawCoset where
  WF := (aggnCheckedRound c n).WF
  ground := (aggnCheckedRound c n).ground
  measure := (aggnCheckedRound c n).measure
  width := (aggnCheckedRound c n).width
  child := (aggnCheckedRound c n).child
  init := aggnBoundedInit c d
  combine := aggnBoundedCombine c d
  finish := (aggnCheckedRound c n).finish
  bot := (aggnCheckedRound c n).bot
  child_eq_none := (aggnCheckedRound c n).child_eq_none
  child_wf := (aggnCheckedRound c n).child_wf
  child_measure := (aggnCheckedRound c n).child_measure
  child_ground := (aggnCheckedRound c n).child_ground

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_ground (c d n : ℕ) : PolyFun (aggnBoundedRound c d n).ground :=
  (((polyFun_fst.comp polyFun_snd).comp polyFun_fst).comp polyFun_length)

theorem aggnQuasiFun_boundedInit (c d n : ℕ) : QuasiFun (aggnBoundedRound c d n).init := by
  have hm := ((aggnPolyFun_ground c d n).quasiFun.pair (aggnQuasiFun_phaseInit c 0)).comp_poly
    (aggnPolyFun_capState d)
  exact hm.of_eq (fun _ => by dsimp only [aggnBoundedRound, aggnBoundedInit, aggnCheckedRound, aggnPhaseRound])

theorem aggnQuasiFun_boundedCombine (c d n : ℕ) : QuasiFun (aggnBoundedRound c d n).combine := by
  have hz : PolyFun (fun z : AggnPhaseNode × ℕ × AggnPhaseState × RawCoset => z) := polyFun_id
  have hI := pfst hz
  have hj := pfst (psnd hz)
  have hs := pfst (psnd (psnd hz))
  have ha := psnd (psnd (psnd hz))
  have hx := pfst (psnd (pfst hI))
  have hn := hx.comp polyFun_length
  have hans := (hx.pair ha).comp aggnPolyFun_normAnswer
  have hnext := (hI.pair (hj.pair (hs.pair hans))).comp_quasiFun (aggnQuasiFun_phaseCombine c)
  have hm := (hn.quasiFun.pair hnext).comp_poly (aggnPolyFun_capState d)
  exact hm.of_eq (fun _ => by dsimp only [aggnBoundedRound, aggnBoundedCombine])

/-- All state-size clauses hold for every supplied state and answer. The choice
of cap exponent affects semantic preservation, not these unconditional costs. -/
theorem aggnBounded_hasCostQ (c d n : ℕ) : Nonempty (Round.CostQ (aggnBoundedRound c d n)) := by
  obtain ⟨W, hW, hWmono, hwidth⟩ := aggnChecked_width_bound c
  refine ⟨{
    bound := fun k => aggnCheckedBound k + 2
    polyBound_bound := aggnPolyBound_checked.add (polyBound_const 2)
    mono_bound := fun _ _ h => Nat.add_le_add_right (aggnMono_checkedBound h) 2
    stateBound := aggnStateCap d
    quasiPolyBound_stateBound := aggnQuasiPolyBound_stateCap d
    mono_stateBound := aggnMono_stateCap d
    widthBound := W
    quasiPolyBound_widthBound := hW
    quasiFun_child := by
      change QuasiFun (aggnCheckedChild c)
      exact aggnQuasiFun_checkedChild c
    quasiFun_init := aggnQuasiFun_boundedInit c d n
    quasiFun_combine := aggnQuasiFun_boundedCombine c d n
    quasiFun_finish := by
      change QuasiFun (fun _ : AggnPhaseNode × AggnPhaseState => (none : RawCoset))
      exact quasiFun_const none
    ground_le := fun I => (length_le_size I.1.2.1).trans
      ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans (size_fst_le' I)))
    size_le := fun I hI => (aggnCheckedRound_size c n I hI).trans (Nat.le_add_right _ 2)
    init_le := by
      intro I _
      dsimp only [aggnBoundedRound, aggnBoundedInit, aggnBoundedCombine,
        aggnCheckedRound, aggnPhaseRound]
      exact aggnCapState_size d I.1.2.1.length _
    combine_le := by
      intro I _ _ _ _ _ _
      dsimp only [aggnBoundedRound, aggnBoundedInit, aggnBoundedCombine,
        aggnCheckedRound, aggnPhaseRound]
      exact aggnCapState_size d I.1.2.1.length _
    finish_le := fun I _ _ _ => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound I.1.2.1.length + 2
      rw [size_none]
      omega
    bot_le := fun m => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound m + 2
      rw [size_none]
      omega
    width_le := fun I hI => hwidth n I hI }⟩

noncomputable def aggnBoundedCostQ (c d n : ℕ) : Round.CostQ (aggnBoundedRound c d n) :=
  Classical.choice (aggnBounded_hasCostQ c d n)

end Algo
