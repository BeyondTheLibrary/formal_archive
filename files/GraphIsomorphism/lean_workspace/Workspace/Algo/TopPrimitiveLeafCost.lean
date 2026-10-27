import Workspace.Algo.TopPrimitiveLeaf
import Workspace.Algo.TopSuppliedUniform
import Workspace.Master.Lines

/-! # The uniform RAM leaf for Section 15, line 4a
The degree is read from the input string. The only well-formedness guard
in this carrier is the polynomial input-size cap. Mathematical group
hypotheses belong to its correctness theorem, not to the executable test.
-/
namespace Algo
open RAM RAM.Targets Babai

def primitiveLeafRound (a b : ℕ) : Round RawSI ℕ RawCoset where
  WF p := Enc.size p ≤ topcsContextCap a b p.2.1.length
  ground p := p.2.1.length
  measure _ := 0
  width _ := 0
  child _ := none
  init _ := 0
  combine _ := 0
  finish p := primitiveLeaf p.1
  bot := none
  child_eq_none := fun _ _ _ _ => rfl
  child_wf := by intros; contradiction
  child_measure := by intros; contradiction
  child_ground := by intros; contradiction

def primitiveLeafBound (a b n : ℕ) : ℕ := topcsContextCap a b n + chainBound n + 4
theorem polyBound_primitiveLeafBound (a b : ℕ) : PolyBound (primitiveLeafBound a b) :=
  ((polyBound_topcsContextCap a b).add polyBound_chainBound).add (polyBound_const 4)
theorem mono_primitiveLeafBound (a b : ℕ) : Monotone (primitiveLeafBound a b) := by
  intro n m h
  have := mono_topcsContextCap a b h
  have := mono_chainBound h
  unfold primitiveLeafBound
  omega

def primitiveLeafRunCostQ (a b : ℕ) : Round.RunCostQ (primitiveLeafRound a b) where
  bound := primitiveLeafBound a b
  polyBound_bound := polyBound_primitiveLeafBound a b
  mono_bound := mono_primitiveLeafBound a b
  stateBound := fun _ => 2
  quasiPolyBound_stateBound := (polyBound_const 2).quasiPoly
  mono_stateBound := fun _ _ _ => le_rfl
  widthBound := fun _ => 0
  quasiPolyBound_widthBound := (polyBound_const 0).quasiPoly
  quasiFun_child := (polyFun_const none).quasiFun
  quasiFun_init := (polyFun_const 0).quasiFun
  quasiFun_combine := (polyFun_const 0).quasiFun
  quasiFun_finish := (polyFun_fst.comp polyFun_primitiveLeaf).quasiFun
  ground_le := fun p => (length_le_size _).trans ((size_fst_le' p.2).trans (size_snd_le' p))
  size_le := by
    intro p hp
    change Enc.size p ≤ primitiveLeafBound a b p.2.1.length
    change Enc.size p ≤ topcsContextCap a b p.2.1.length at hp
    unfold primitiveLeafBound
    omega
  init_le := fun _ _ => by change Enc.size (0 : ℕ) ≤ 2; decide
  combine_le := fun _ _ _ _ _ _ _ => by change Enc.size (0 : ℕ) ≤ 2; decide
  finish_le := by
    intro p s hp hs
    change Enc.size (primitiveLeaf p) ≤ primitiveLeafBound a b p.2.1.length
    exact (primitiveLeaf_size p).trans (by unfold primitiveLeafBound; omega)
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ primitiveLeafBound a b n
    rw [size_none]
    unfold primitiveLeafBound
    omega
  width_le := fun _ _ => le_rfl
  polyFun_ground := (polyFun_snd.comp polyFun_fst).comp polyFun_length
  wfCheck p := decide (Enc.size p ≤ topcsContextCap a b p.2.1.length)
  polyFun_wfCheck := AggnSizeRoutine.polyFun_size.le
    (((polyFun_snd.comp polyFun_fst).comp polyFun_length).comp (polyFun_topcsContextCap a b))
  wfCheck_eq_true := fun _ => decide_eq_true_iff
  measureBound := fun _ => 0
  polyBound_measureBound := polyBound_const 0
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := fun _ _ => le_rfl

noncomputable def primitiveLeafInstance (n : ℕ) (p : RawSI) : SIInstance (Fin n) ℕ :=
  ⟨decGroup n p.1, Set.univ, decStrN n p.2.1, decStrN n p.2.2⟩

/-- The machine makes no calls and matches the paper's literal leaf. -/
theorem primitiveLeaf_loop (a b : ℕ) {n : ℕ} {p : RawSI} (hgs : RawGens.WF n p.1)
    (hx : p.2.1.length = n) (hy : p.2.2.length = n)
    (hgiant : alternatingGroup (Fin n) ≤ decGroup n p.1) :
    LoopMatch (primitiveLeafRound a b) (primitiveLeafInstance n) (decCoset n) p 0 0 0
      (line4aReduction (primitiveLeafInstance n p)) := by
  apply LoopMatch.done
  · rfl
  · change decCoset n (primitiveLeaf p) = wIso Set.univ _ _ _
    rw [wIso_univ]
    exact primitiveLeaf_spec hgs hx hy hgiant

end Algo
