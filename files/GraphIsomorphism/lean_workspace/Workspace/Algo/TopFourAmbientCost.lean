import Workspace.Algo.TopFourContextSize

/-! # A degree-uniform RAM bound for the outer window adapter
The source degree is read from the retained ambient string. Inner states
are charged to the retained context, and child encodings are checked against one
fixed polynomial of the retained context.
-/
set_option synthInstance.maxSize 4096
namespace Algo
open RAM RAM.Targets

def top4wBound (a b c d e f u v n : ℕ) : ℕ :=
  16 * (topcsContextCap a b n + top4ContextStateBound (topcsContextCap a b n) +
    topcsContextCap u v (topcsContextCap a b n) + chainBound n + 4)

theorem polyBound_top4wBound (a b c d e f u v : ℕ) : PolyBound (top4wBound a b c d e f u v) :=
  (polyBound_const 16).mul (((((polyBound_topcsContextCap a b).add
    (polyBound_top4ContextStateBound.comp (polyBound_topcsContextCap a b))).add
    ((polyBound_topcsContextCap u v).comp (polyBound_topcsContextCap a b))).add
    polyBound_chainBound).add (polyBound_const 4))

theorem mono_top4wBound (a b c d e f u v : ℕ) : Monotone (top4wBound a b c d e f u v) := by
  intro N M hNM
  have h1 := mono_topcsContextCap a b hNM
  have h2 := mono_top4ContextStateBound h1
  have h3 := mono_topcsContextCap u v h1
  have h4 := mono_chainBound hNM
  unfold top4wBound
  omega

theorem top4ContextBound_le_top4wBound (a b c d e f u v n : ℕ) :
    top4ContextStateBound (topcsContextCap a b n) ≤ top4wBound a b c d e f u v n := by
  unfold top4wBound
  omega

theorem top4wNode_size {a b c d e f u v : ℕ} {I : Top4wNode} (hI : Top4wWF a b c d e f u v I) :
    Enc.size I ≤ top4wBound a b c d e f u v I.1.1.2.2.length := by
  have hp := size_pair_le' I
  have hctx := hI.1
  cases ho : I.2 with
  | none =>
    have hs : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold top4wBound
    omega
  | some W =>
    have hW := hI.2 W ho
    have hm := mono_topcsContextCap u v hctx
    have hs : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold top4wBound
    omega

def top4wRunCostQ (a b c d e f u v : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (top4wRound a b c d e f u v solve) where
  bound := top4wBound a b c d e f u v
  polyBound_bound := polyBound_top4wBound a b c d e f u v
  mono_bound := mono_top4wBound a b c d e f u v
  stateBound := top4wBound a b c d e f u v
  quasiPolyBound_stateBound := (polyBound_top4wBound a b c d e f u v).quasiPoly
  mono_stateBound := mono_top4wBound a b c d e f u v
  widthBound := fun n => top4ContextWidthBound (topcsContextCap a b n)
  quasiPolyBound_widthBound := (polyBound_top4ContextWidthBound.comp (polyBound_topcsContextCap a b)).quasiPoly
  quasiFun_child := (polyFun_top4wChild e f u v).quasiFun
  quasiFun_init := polyFun_top4wInit.quasiFun
  quasiFun_combine := polyFun_top4wCombine.quasiFun
  quasiFun_finish := quasiFun_top4wFinish hsolve
  ground_le := fun I => (length_le_size _).trans ((size_snd_le' I.1.1.2).trans
    ((size_snd_le' I.1.1).trans ((size_fst_le' I.1).trans (size_fst_le' I))))
  size_le := fun _ hI => top4wNode_size hI
  init_le := by
    intro I hI
    have hctx := (size_fst_le' I.1.2.1).trans ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans hI.1))
    exact (top4Stored_size_context hctx (top4Init_stored I.1.2.1)).trans
      (top4ContextBound_le_top4wBound a b c d e f u v _)
  combine_le := by
    intro I j s z hI _ _
    have hctx := (size_fst_le' I.1.2.1).trans ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans hI.1))
    have hh := top4Stored_size_context hctx
      (top4Combine_stored (I.1.2.1, j, s, topwCosetImage (I.1.1.1.1, I.1.1.2.1, z)))
    exact hh.trans (top4ContextBound_le_top4wBound a b c d e f u v _)
  finish_le := by
    intro I s _ _
    have hh := size_top2NormC_le (n := I.1.1.2.2.length) rfl le_rfl
      (I.2.elim (topwCosetPreimage (I.1.1.1, I.1.1.2.1, top4aFinish solve (I.1.2, s))) solve)
    change Enc.size (top2NormC I.1.1.2.2 _) ≤ top4wBound a b c d e f u v I.1.1.2.2.length
    dsimp only at hh ⊢
    unfold top4wBound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    unfold top4wBound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    cases I.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      exact top4aWidth_context
        ((size_fst_le' I.1.2.1).trans ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans hI.1))) solve
  polyFun_ground := polyFun_top4wGround
  wfCheck := top4wCheck a b c d e f u v
  polyFun_wfCheck := polyFun_top4wCheck a b c d e f u v
  wfCheck_eq_true := top4wCheck_spec a b c d e f u v
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

end Algo
