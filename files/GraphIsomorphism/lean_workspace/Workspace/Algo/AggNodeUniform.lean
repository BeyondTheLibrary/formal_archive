import Workspace.Algo.AggNodeBoundedRun

/-! # One certificate carrier for every input degree

The executable round reads its degree from the source string. Its four
operations and its well-formedness test have no externally supplied degree.
The fixed-degree carrier remains the semantic bridge to typed instances.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnUniformRound (c d : ℕ) : Round AggnPhaseNode AggnPhaseState RawCoset where
  WF := fun I => AggnCheckedWF I.1.2.1.length I
  ground := (aggnBoundedRound c d 0).ground
  measure := (aggnBoundedRound c d 0).measure
  width := (aggnBoundedRound c d 0).width
  child := (aggnBoundedRound c d 0).child
  init := aggnBoundedInit c d
  combine := aggnBoundedCombine c d
  finish := (aggnBoundedRound c d 0).finish
  bot := none
  child_eq_none := (aggnBoundedRound c d 0).child_eq_none
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCheckedChild_some hJ
    refine ⟨rfl, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    exact aggnCheckedWindow_wf _ _
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, _, rfl⟩ := aggnCheckedChild_some hJ
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, _, rfl⟩ := aggnCheckedChild_some hJ
    exact le_rfl

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_windowCheckWithDegree :
    PolyFun (fun z : ℕ × RawWinSI => aggnWindowCheck z.1 z.2) := by
  have hW : PolyFun (fun z : ℕ × RawWinSI => z.2) := polyFun_snd
  have hn : PolyFun (fun z : ℕ × RawWinSI => z.1) := polyFun_fst
  have hw := pfst hW
  have hg := pfst (psnd hW)
  have hr := pfst (psnd (psnd hW))
  have hx := pfst (psnd (psnd (psnd hW)))
  have hy := psnd (psnd (psnd (psnd hW)))
  have h1 := hw.comp wftPolyFun_nodup
  have h2 := (hn.pair hw).comp wftPolyFun_allLt
  have h3 := (hn.pair hg).comp wftPolyFun_isGensOf
  have h4 := ((hg.comp polyFun_length).pair (hn.mul hn)).comp polyFun_le
  have h5 := (hn.pair hr).comp wftPolyFun_isPermOf
  have hns := hn.pair (((polyFun_const 2).mul hn).add (polyFun_const 1))
  have h6 := (hns.pair hx).comp wftPolyFun_isStrOf
  have h7 := (hns.pair hy).comp wftPolyFun_isStrOf
  exact wftPolyFun_and (wftPolyFun_and (wftPolyFun_and (wftPolyFun_and
    (wftPolyFun_and (wftPolyFun_and h1 h2) h3) h4) h5) h6) h7

theorem aggnPolyFun_windowBound : PolyFun aggnCheckedWindowBound := by
  have hs : PolyFun strBound := (polyFun_const 1).add (polyFun_id.mul
    (((polyFun_const 2).mul (polyFun_id.add (polyFun_const 2))).add (polyFun_const 1)))
  have hg : PolyFun gensBound := (polyFun_const 1).add ((polyFun_id.mul polyFun_id).mul
    (((polyFun_const 2).mul hs).add (polyFun_const 1)))
  exact (polyFun_const 32).mul ((hg.add
    ((((polyFun_const 2).mul polyFun_id).add (polyFun_const 1)).comp hs)).add (polyFun_const 1))

def aggnUniformWfCheck (I : AggnPhaseNode) : Bool :=
  decide (Enc.size I.1 ≤ 2 * aggnCheckedWindowBound I.1.2.1.length) &&
    I.2.elim true (aggnWindowCheck I.1.2.1.length)

theorem aggnUniformWfCheck_spec (c d : ℕ) (I : AggnPhaseNode) :
    aggnUniformWfCheck I = true ↔ (aggnUniformRound c d).WF I := by
  change _ ↔ AggnCheckedWF I.1.2.1.length I
  cases ho : I.2 <;> simp [aggnUniformWfCheck, AggnCheckedWF, ho, aggnWindowCheck_spec]

theorem aggnPolyFun_uniformWfCheck : PolyFun aggnUniformWfCheck := by
  have hn := aggnPolyFun_ground 0 0 0
  have h1 : PolyFun (fun I : AggnPhaseNode => decide
      (Enc.size I.1 ≤ 2 * aggnCheckedWindowBound I.1.2.1.length)) :=
    ((polyFun_fst.comp aggnPolyFun_contextSize).pair
      ((polyFun_const 2).mul (hn.comp aggnPolyFun_windowBound))).comp polyFun_le
  have ho : PolyFun (fun z : Option RawWinSI × ℕ => z.1.elim true (aggnWindowCheck z.2)) :=
    PolyFun.optionElim (polyFun_const true)
      (polyFun_swap.comp aggnPolyFun_windowCheckWithDegree)
  exact wftPolyFun_and h1 ((polyFun_snd.pair hn).comp ho)

/-- All machine programs, including the validity test, are independent of the degree. -/
theorem aggnUniform_hasRunCostQ (c d : ℕ) : Nonempty (Round.RunCostQ (aggnUniformRound c d)) := by
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
    quasiFun_child := aggnQuasiFun_checkedChild c
    quasiFun_init := aggnQuasiFun_boundedInit c d 0
    quasiFun_combine := aggnQuasiFun_boundedCombine c d 0
    quasiFun_finish := (aggnPolyFun_checkedFinish c 0).quasiFun
    ground_le := fun I => (length_le_size I.1.2.1).trans
      ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans (size_fst_le' I)))
    size_le := fun I hI => (aggnCheckedRound_size c I.1.2.1.length I hI).trans (Nat.le_add_right _ 2)
    init_le := by
      intro I _
      dsimp only [aggnUniformRound, aggnBoundedRound, aggnBoundedInit, aggnCheckedRound, aggnPhaseRound]
      exact aggnCapState_size d I.1.2.1.length _
    combine_le := by
      intro I _ _ _ _ _ _
      dsimp only [aggnUniformRound, aggnBoundedRound, aggnBoundedCombine, aggnCheckedRound, aggnPhaseRound]
      exact aggnCapState_size d I.1.2.1.length _
    finish_le := fun I _ _ _ => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound I.1.2.1.length + 2
      rw [size_none]
      omega
    bot_le := fun m => by
      change Enc.size (none : RawCoset) ≤ aggnCheckedBound m + 2
      rw [size_none]
      omega
    width_le := fun I hI => hwidth I.1.2.1.length I hI
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

noncomputable def aggnUniformRunCostQ (c d : ℕ) : Round.RunCostQ (aggnUniformRound c d) :=
  Classical.choice (aggnUniform_hasRunCostQ c d)

end Algo
