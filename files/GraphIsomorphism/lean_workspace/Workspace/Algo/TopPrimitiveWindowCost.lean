import Workspace.Algo.TopPrimitiveWindow
import Workspace.Algo.TopSuppliedUniform
import Workspace.Master.Lines

/-! # The uniform RAM leaf for Section 15, line 4a
The ambient degree is read from the input string. The only well-formedness guard
in this carrier is the polynomial input-size cap. Mathematical group
hypotheses belong to its correctness theorem, not to the executable test.
-/
namespace Algo
open RAM RAM.Targets Babai

def primitiveWindowRound (a b : ℕ) : Round RawWinSI ℕ RawCoset where
  WF p := Enc.size p ≤ topcsContextCap a b p.2.2.2.1.length
  ground p := p.2.2.2.1.length
  measure _ := 0
  width _ := 0
  child _ := none
  init _ := 0
  combine _ := 0
  finish p := primitiveWindowLeaf p.1
  bot := none
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := by intros; contradiction
  child_measure := by intros; contradiction
  child_ground := by intros; contradiction

def primitiveWindowBound (a b n : ℕ) : ℕ := topcsContextCap a b n + chainBound n + 4
theorem polyBound_primitiveWindowBound (a b : ℕ) : PolyBound (primitiveWindowBound a b) :=
  ((polyBound_topcsContextCap a b).add polyBound_chainBound).add (polyBound_const 4)
theorem mono_primitiveWindowBound (a b : ℕ) : Monotone (primitiveWindowBound a b) := by
  intro n m h
  have := mono_topcsContextCap a b h
  have := mono_chainBound h
  unfold primitiveWindowBound
  omega

def primitiveWindowRunCostQ (a b : ℕ) : Round.RunCostQ (primitiveWindowRound a b) where
  bound := primitiveWindowBound a b
  polyBound_bound := polyBound_primitiveWindowBound a b
  mono_bound := mono_primitiveWindowBound a b
  stateBound := fun _ => 2
  quasiPolyBound_stateBound := (polyBound_const 2).quasiPoly
  mono_stateBound := fun _ _ _ => le_rfl
  widthBound := fun _ => 0
  quasiPolyBound_widthBound := (polyBound_const 0).quasiPoly
  quasiFun_child := (polyFun_const none).quasiFun
  quasiFun_init := (polyFun_const 0).quasiFun
  quasiFun_combine := (polyFun_const 0).quasiFun
  quasiFun_finish := (polyFun_fst.comp polyFun_primitiveWindowLeaf).quasiFun
  ground_le := fun p => (length_le_size _).trans ((size_fst_le' p.2.2.2).trans ((size_snd_le' p.2.2).trans ((size_snd_le' p.2).trans (size_snd_le' p))))
  size_le := by
    intro p hp
    change Enc.size p ≤ primitiveWindowBound a b p.2.2.2.1.length
    change Enc.size p ≤ topcsContextCap a b p.2.2.2.1.length at hp
    unfold primitiveWindowBound
    omega
  init_le := fun _ _ => by change Enc.size (0 : ℕ) ≤ 2; decide
  combine_le := fun _ _ _ _ _ _ _ => by change Enc.size (0 : ℕ) ≤ 2; decide
  finish_le := by
    intro p s hp hs
    change Enc.size (primitiveWindowLeaf p) ≤ primitiveWindowBound a b p.2.2.2.1.length
    exact (primitiveWindowLeaf_size p).trans (by unfold primitiveWindowBound; omega)
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ primitiveWindowBound a b n
    rw [size_none]
    unfold primitiveWindowBound
    omega
  width_le := fun _ _ => le_rfl
  polyFun_ground := (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).comp polyFun_length
  wfCheck p := decide (Enc.size p ≤ topcsContextCap a b p.2.2.2.1.length)
  polyFun_wfCheck := AggnSizeRoutine.polyFun_size.le
    (((((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst).comp polyFun_length).comp (polyFun_topcsContextCap a b))
  wfCheck_eq_true := fun _ => decide_eq_true_iff
  measureBound := fun _ => 0
  polyBound_measureBound := polyBound_const 0
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := fun _ _ => le_rfl

/-- The complete ambient leaf matches line 4a with no recursive calls. -/
theorem primitiveWindow_loop (a b : ℕ) {n : ℕ} {p : RawWinSI}
    (hx : p.2.2.2.1.length = n) (hgs : RawGens.WF n p.2.1)
    (hnd : p.1.Nodup) (hlt : ∀ u ∈ p.1, u < n)
    (hinv : IsInvariant (decGroup n p.2.1) (winSet n p.1))
    (hgiant : alternatingGroup (Fin p.1.length) ≤
      (winRestrictHom n p.1 hnd hlt (decGroup n p.2.1) hinv).range) :
    LoopMatch (primitiveWindowRound a b) (decWinSI n) (decCoset n) p 0 0 0
      (line4aReduction (decWinSI n p)) :=
  .done 0 0 0 _ rfl (primitiveWindowLeaf_spec hx hgs hnd hlt hinv hgiant)

end Algo
