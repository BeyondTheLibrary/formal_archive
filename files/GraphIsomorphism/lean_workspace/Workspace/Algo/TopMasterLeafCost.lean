import Workspace.Algo.TopMasterBrute

/-! # Uniform RAM leaves for the first Reduce-to-Johnson exits
Each carrier reads its degree from the ambient source string. The finish
bound follows from the normalized full-preimage return, on every raw input.
-/
namespace Algo
open RAM RAM.Targets Babai

def masterLeafRound (a b : ℕ) (f : RawWinSI → RawCoset) : Round RawWinSI ℕ RawCoset where
  WF p := Enc.size p ≤ topcsContextCap a b p.2.2.2.1.length
  ground p := p.2.2.2.1.length
  measure _ := 0
  width _ := 0
  child _ := none
  init _ := 0
  combine _ := 0
  finish p := f p.1
  bot := none
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := by intros; contradiction
  child_measure := by intros; contradiction
  child_ground := by intros; contradiction

def masterLeafRunCostQ (a b : ℕ) (f : RawWinSI → RawCoset) (hf : PolyFun f)
    (hsz : ∀ p, Enc.size (f p) ≤ chainBound p.2.2.2.1.length) :
    Round.RunCostQ (masterLeafRound a b f) where
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
  quasiFun_finish := (polyFun_fst.comp hf).quasiFun
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
    change Enc.size (f p) ≤ primitiveWindowBound a b p.2.2.2.1.length
    exact (hsz p).trans (by unfold primitiveWindowBound; omega)
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


def masterTrivialRunCostQ (a b : ℕ) :
    Round.RunCostQ (masterLeafRound a b masterWindowTrivialLeaf) :=
  masterLeafRunCostQ a b _ polyFun_masterWindowTrivialLeaf
    (fun p => masterWindowReturn_size (p, _))

def masterBruteRunCostQ (a b C₀ : ℕ) :
    Round.RunCostQ (masterLeafRound a b (masterWindowBruteLeaf C₀)) :=
  masterLeafRunCostQ a b _ (polyFun_masterWindowBruteLeaf C₀)
    (fun p => masterWindowReturn_size (p, _))

theorem masterTrivial_loop (a b : ℕ) {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 0) :
    LoopMatch (masterLeafRound a b masterWindowTrivialLeaf) (decWinSI n) (decCoset n)
      W 0 0 0 (bruteForceBranch (decWinSI n W)) :=
  .done 0 0 0 _ rfl (masterWindowTrivialLeaf_spec hx hw hnd hlt hinv hr)

theorem masterBrute_loop (a b : ℕ) {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 1) :
    LoopMatch (masterLeafRound a b (masterWindowBruteLeaf C₀)) (decWinSI n) (decCoset n)
      W 0 0 0 (bruteForceBranch (decWinSI n W)) :=
  .done 0 0 0 _ rfl (masterWindowBruteLeaf_spec hx hw hnd hlt hinv hr)
end Algo
