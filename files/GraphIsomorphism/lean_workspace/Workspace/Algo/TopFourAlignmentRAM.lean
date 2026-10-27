import Workspace.Algo.TopFourAlignment

/-! # Uniform cost of the supplied alignment and cardinality guard -/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets
private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd
private theorem pmap {α β σ : Type*} [Enc α] [Enc β] [Enc σ] {f : α × σ → β}
    (hf : PolyFun f) : PolyFun (fun p : Option α × σ => p.1.map (fun a => f (a, p.2))) :=
  (PolyFun.optionElim (polyFun_const none) (hf.comp polyFun_some)).of_eq
    (fun p => by cases p.1 <;> rfl)

theorem polyFun_top4aGate : PolyFun top4aGate :=
  (((psnd polyFun_fst).pair polyFun_id).comp
    (PolyFun.optionElim (psnd polyFun_snd) (polyFun_const true)))

theorem polyFun_top4aChild (e f : ℕ) : PolyFun (top4aChild e f) := by
  let Z := Top4aNode × ℕ × Top4State
  have hinner : PolyFun (fun z : Z => top4Child e f (z.1.1, z.2)) :=
    ((pfst polyFun_fst).pair polyFun_snd).comp (polyFun_top4Child e f)
  have hb : PolyFun (fun z : Top4Node × Z => (z.1, z.2.1.2)) :=
    polyFun_fst.pair (polyFun_snd.comp (psnd polyFun_fst))
  exact PolyFun.ite (polyFun_fst.comp polyFun_top4aGate)
    ((hinner.pair polyFun_id).comp (pmap hb)) (polyFun_const none)

theorem polyFun_top4aInit : PolyFun top4aInit := polyFun_fst.comp polyFun_top4Init
theorem polyFun_top4aCombine : PolyFun top4aCombine :=
  ((pfst polyFun_fst).pair polyFun_snd).comp polyFun_top4Combine

theorem quasiFun_top4aFinish {solve : RawWinSI → RawCoset} (hsolve : QuasiFun solve) :
    QuasiFun (top4aFinish solve) := by
  let Z := Top4aNode × Top4State
  have hI : PolyFun (fun z : Z => z.1.1) := pfst polyFun_fst
  have hX := (pfst hI).comp polyFun_top4X
  have hα := pfst (psnd (polyFun_fst : PolyFun (fun z : Z => z.1)))
  have hflag := psnd (psnd (polyFun_fst : PolyFun (fun z : Z => z.1)))
  have hfin := (hI.pair polyFun_snd).quasiFun.comp (quasiFun_top4Finish hsolve)
  have hshift := (hX.quasiFun.pair (hα.quasiFun.pair hfin)).comp polyFun_top3Shift.quasiFun
  have hroot := QuasiFun.ite hflag hshift (polyFun_const none).quasiFun
  exact (((psnd hI).pair polyFun_id).quasiFun.comp
    (QuasiFun.optionElim hroot (polyFun_snd.quasiFun.comp hfin)))

theorem polyFun_top4aStrBound : PolyFun strBound :=
  (polyFun_const 1).add (polyFun_id.mul
    (((polyFun_const 2).mul (polyFun_id.add (polyFun_const 2))).add (polyFun_const 1)))

def top4aCheck (c d e f : ℕ) (I : Top4aNode) : Bool :=
  top4Check c d e f I.1 && decide (Enc.size I.2.1 ≤ strBound (top4X I.1.1).length)

theorem polyFun_top4aCheck (c d e f : ℕ) : PolyFun (top4aCheck c d e f) := by
  have ht : PolyFun (fun I : Top4aNode => decide (Enc.size I.2.1 ≤ strBound (top4X I.1.1).length)) :=
    ((pfst polyFun_snd).comp AggnSizeRoutine.polyFun_size).le
      ((((pfst polyFun_fst).comp polyFun_top4X).comp polyFun_length).comp polyFun_top4aStrBound)
  exact (PolyFun.ite (polyFun_fst.comp (polyFun_top4Check c d e f)) ht (polyFun_const false)).of_eq
    (fun I => by simp only [top4aCheck]; cases top4Check c d e f I.1 <;> rfl)

theorem top4aCheck_spec (c d e f : ℕ) (I : Top4aNode) :
    top4aCheck c d e f I = true ↔ Top4aWF c d e f I := by
  simp [top4aCheck, Top4aWF, top4Check_spec]

def top4aBound (c d e f n : ℕ) : ℕ := 16 * (top4Bound c d e f n + strBound n + 4)
theorem polyBound_top4aBound (c d e f : ℕ) : PolyBound (top4aBound c d e f) :=
  (polyBound_const 16).mul (((polyBound_top4Bound c d e f).add polyBound_strBound).add (polyBound_const 4))
theorem mono_top4aBound (c d e f : ℕ) : Monotone (top4aBound c d e f) := by
  intro a b hab
  have h1 := mono_top4Bound c d e f hab
  have h2 := mono_strBound hab
  unfold top4aBound
  omega

theorem top4Bound_le_top4aBound (c d e f n : ℕ) : top4Bound c d e f n ≤ top4aBound c d e f n := by
  unfold top4aBound
  omega

theorem top4aNode_size {c d e f : ℕ} {I : Top4aNode} (hI : Top4aWF c d e f I) :
    Enc.size I ≤ top4aBound c d e f (top4X I.1.1).length := by
  have hnode := top4Node_size hI.1
  have ha := hI.2
  have hb := Combine.size_bool_le I.2.2
  have h1 := size_pair_le' I
  have h2 := size_pair_le' I.2
  unfold top4aBound
  omega

theorem size_top4aFinish {solve : RawWinSI → RawCoset} (I : Top4aNode) (s : Top4State) :
    Enc.size (top4aFinish solve (I, s)) ≤ chainBound (top4X I.1.1).length := by
  have hfin := size_top2NormC_le (n := (top4X I.1.1).length) rfl le_rfl (I.1.2.elim s.2.2 solve)
  have hshift := size_top3Shift_le (n := (top4X I.1.1).length) rfl le_rfl I.2.1 (top4Finish solve (I.1, s))
  have hnone := chainBound_ge (top4X I.1.1).length
  unfold top4aFinish
  dsimp only
  cases ho : I.1.2 with
  | none =>
    simp only [Option.elim_none]
    split
    · exact hshift
    · rw [size_none]; omega
  | some W => exact hfin

def top4aRunCostQ (c d e f : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (top4aRound c d e f solve) where
  bound := top4aBound c d e f
  polyBound_bound := polyBound_top4aBound c d e f
  mono_bound := mono_top4aBound c d e f
  stateBound := top4aBound c d e f
  quasiPolyBound_stateBound := (polyBound_top4aBound c d e f).quasiPoly
  mono_stateBound := mono_top4aBound c d e f
  widthBound := (top4RunCostQ c d e f solve hsolve).widthBound
  quasiPolyBound_widthBound := (top4RunCostQ c d e f solve hsolve).quasiPolyBound_widthBound
  quasiFun_child := (polyFun_top4aChild e f).quasiFun
  quasiFun_init := polyFun_top4aInit.quasiFun
  quasiFun_combine := polyFun_top4aCombine.quasiFun
  quasiFun_finish := quasiFun_top4aFinish hsolve
  ground_le := fun I => ((top4RunCostQ c d e f solve hsolve).ground_le I.1).trans (size_fst_le' I)
  size_le := fun _ hI => top4aNode_size hI
  init_le := fun I hI => (top4Stored_size (e := e) (f := f) hI.1.1 (top4Init_stored I.1)).trans
    (top4Bound_le_top4aBound c d e f _)
  combine_le := fun I j s a hI _ _ => (top4Stored_size (e := e) (f := f) hI.1.1 (top4Combine_stored (I.1, j, s, a))).trans
    (top4Bound_le_top4aBound c d e f _)
  finish_le := by
    intro I s _ _
    have h := size_top4aFinish (solve := solve) I s
    change Enc.size (top4aFinish solve (I, s)) ≤ top4aBound c d e f (top4X I.1.1).length
    unfold top4aBound top4Bound
    omega
  bot_le := fun n => ((top4RunCostQ c d e f solve hsolve).bot_le n).trans (top4Bound_le_top4aBound c d e f n)
  width_le := by
    intro I hI
    change (if top4aGate I then _ else 0) ≤ _
    split
    · exact (top4RunCostQ c d e f solve hsolve).width_le I.1 hI.1
    · exact Nat.zero_le _
  polyFun_ground := (((pfst polyFun_fst).comp polyFun_top4X).comp polyFun_length)
  wfCheck := top4aCheck c d e f
  polyFun_wfCheck := polyFun_top4aCheck c d e f
  wfCheck_eq_true := top4aCheck_spec c d e f
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.1.2.elim 1 (fun _ => 0) ≤ 1
    cases I.1.2 <;> simp

end Algo
