import Workspace.Algo.AggNodeBounded
import Workspace.Algo.WFTests

/-! # The bounded certificate carrier has a runnable cost datum

The well-formedness test checks exactly the retained context-size condition
and the normalized child's structural conditions. Its meaning is proved
against the round's actual `WF` predicate.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets

def aggnWindowCheck (n : ℕ) (W : RawWinSI) : Bool :=
  wftNodup W.1 && wftAllLt (n, W.1) &&
    wftIsGensOf (n, W.2.1) && decide (W.2.1.length ≤ n * n) &&
    wftIsPermOf (n, W.2.2.1) && wftIsStrOf ((n, 2 * n + 1), W.2.2.2.1) &&
    wftIsStrOf ((n, 2 * n + 1), W.2.2.2.2)

theorem aggnWindowCheck_spec (n : ℕ) (W : RawWinSI) :
    aggnWindowCheck n W = true ↔ AggnCheckedWindowWF n W := by
  simp only [aggnWindowCheck, AggnCheckedWindowWF, Bool.and_eq_true,
    wftNodup_eq_true_iff, wftAllLt_eq_true_iff, wftIsGensOf_eq_true_iff,
    decide_eq_true_eq, wftIsPermOf_eq_true_iff, wftIsStrOf_eq_true_iff, and_assoc]

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

theorem aggnPolyFun_windowCheck (n : ℕ) : PolyFun (aggnWindowCheck n) := by
  have hW : PolyFun (fun W : RawWinSI => W) := polyFun_id
  have hw := pfst hW
  have hg := pfst (psnd hW)
  have hr := pfst (psnd (psnd hW))
  have hx := pfst (psnd (psnd (psnd hW)))
  have hy := psnd (psnd (psnd (psnd hW)))
  have h1 := hw.comp wftPolyFun_nodup
  have h2 := ((polyFun_const n).pair hw).comp wftPolyFun_allLt
  have h3 := ((polyFun_const n).pair hg).comp wftPolyFun_isGensOf
  have h4 := ((hg.comp polyFun_length).pair (polyFun_const (n * n))).comp polyFun_le
  have h5 := ((polyFun_const n).pair hr).comp wftPolyFun_isPermOf
  have h6 := ((polyFun_const (n, 2 * n + 1)).pair hx).comp wftPolyFun_isStrOf
  have h7 := ((polyFun_const (n, 2 * n + 1)).pair hy).comp wftPolyFun_isStrOf
  exact wftPolyFun_and (wftPolyFun_and (wftPolyFun_and (wftPolyFun_and
    (wftPolyFun_and (wftPolyFun_and h1 h2) h3) h4) h5) h6) h7

def aggnBoundedWfCheck (n : ℕ) (I : AggnPhaseNode) : Bool :=
  decide (I.1.2.1.length = n) && decide (Enc.size I.1 ≤ 2 * aggnCheckedWindowBound n) &&
    I.2.elim true (aggnWindowCheck n)

theorem aggnBoundedWfCheck_spec (c d n : ℕ) (I : AggnPhaseNode) :
    aggnBoundedWfCheck n I = true ↔ (aggnBoundedRound c d n).WF I := by
  change _ ↔ AggnCheckedWF n I
  cases ho : I.2 <;> simp [aggnBoundedWfCheck, AggnCheckedWF, ho,
    aggnWindowCheck_spec, and_assoc]

theorem aggnPolyFun_boundedWfCheck (n : ℕ) : PolyFun (aggnBoundedWfCheck n) := by
  have h1 := ((aggnPolyFun_ground 0 0 n).pair (polyFun_const n)).comp polyFun_natEq
  have h2 : PolyFun (fun I : AggnPhaseNode => decide (Enc.size I.1 ≤ 2 * aggnCheckedWindowBound n)) :=
    ((polyFun_fst.comp aggnPolyFun_contextSize).pair
    (polyFun_const (2 * aggnCheckedWindowBound n))).comp polyFun_le
  have ho : PolyFun (fun z : Option RawWinSI × AggnPhaseNode => z.1.elim true (aggnWindowCheck n)) :=
    PolyFun.optionElim (polyFun_const true) (polyFun_fst.comp (aggnPolyFun_windowCheck n))
  have h3 := (polyFun_snd.pair polyFun_id).comp ho
  exact wftPolyFun_and (wftPolyFun_and h1 h2) h3

/-- The runnable cost datum includes the exact test and a constant depth bound. -/
theorem aggnBounded_hasRunCostQ (c d n : ℕ) : Nonempty (Round.RunCostQ (aggnBoundedRound c d n)) := by
  obtain ⟨K⟩ := aggnBounded_hasCostQ c d n
  refine ⟨{
    toCostQ := K
    polyFun_ground := aggnPolyFun_ground c d n
    wfCheck := aggnBoundedWfCheck n
    polyFun_wfCheck := aggnPolyFun_boundedWfCheck n
    wfCheck_eq_true := aggnBoundedWfCheck_spec c d n
    measureBound := fun _ => 1
    polyBound_measureBound := polyBound_const 1
    mono_measureBound := fun _ _ _ => le_rfl
    measure_le := ?_ }⟩
  intro I _
  change I.2.elim 1 (fun _ => 0) ≤ 1
  cases I.2 <;> simp

noncomputable def aggnBoundedRunCostQ (c d n : ℕ) : Round.RunCostQ (aggnBoundedRound c d n) :=
  Classical.choice (aggnBounded_hasRunCostQ c d n)

end Algo
