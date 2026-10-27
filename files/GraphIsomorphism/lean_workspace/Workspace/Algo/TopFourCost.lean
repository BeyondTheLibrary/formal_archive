import Workspace.Algo.TopFourRAM
import Workspace.Algo.TopFourMatch

/-! # One uniform RAM certificate for the composed top-action round
The carrier reads its ambient degree from the stored source. Every update
normalizes the coset it retains, so the bounds also hold on arbitrary raw
incoming states and answers.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets

 theorem polyBound_top4LeafCap (e f : ℕ) : PolyBound (top4LeafCap e f) :=
  (polyBound_topcsContextCap e f).add ((polyBound_const 64).mul
    ((polyBound_id.add polyBound_chainBound).add (polyBound_const 1)))
 theorem mono_top4LeafCap (e f : ℕ) : Monotone (top4LeafCap e f) := by
  intro a b hab
  have h1 := mono_topcsContextCap e f hab
  have h2 := mono_chainBound hab
  unfold top4LeafCap
  omega

def top4Bound (c d e f n : ℕ) : ℕ :=
  4096 * (topcsContextCap c d n + chainBound (topcsContextCap c d n) +
    top4LeafCap e f (topcsContextCap c d n) + chainBound n + 4)

theorem polyBound_top4Bound (c d e f : ℕ) : PolyBound (top4Bound c d e f) :=
  (polyBound_const 4096).mul (((((polyBound_topcsContextCap c d).add
    (polyBound_chainBound.comp (polyBound_topcsContextCap c d))).add
    ((polyBound_top4LeafCap e f).comp (polyBound_topcsContextCap c d))).add
    polyBound_chainBound).add (polyBound_const 4))
theorem mono_top4Bound (c d e f : ℕ) : Monotone (top4Bound c d e f) := by
  intro a b hab
  have h1 := mono_topcsContextCap c d hab
  have h2 := mono_chainBound h1
  have h3 := mono_top4LeafCap e f h1
  have h4 := mono_chainBound hab
  unfold top4Bound
  omega

def Top4Stored (C : Top4Context) (s : Top4State) : Prop :=
  TopcsStored (topcsX C.1.2).length C.1.2 s.1 ∧
  s.2.1 ≤ (top4Wins C).length ∧ Enc.size s.2.2 ≤ chainBound (top4X C).length

theorem top4Closed_stored (C : Top4Context) :
    TopcsStored (topcsX C.1.2).length C.1.2 (top4Closed C) := by
  have h := chainBound_ge (topcsX C.1.2).length
  refine ⟨le_rfl, Nat.zero_le _, ?_, ?_, ?_, ?_⟩ <;>
    change Enc.size (none : Option _) ≤ _ <;> rw [size_none] <;> omega

theorem top4Open_stored {C : Top4Context} {s : TopcsState}
    (h : TopcsStored (topcsX C.1.2).length C.1.2 s) : Top4Stored C (top4Open C s) :=
  ⟨h, Nat.zero_le _, size_top2NormC_le rfl le_rfl _⟩
theorem top4Init_stored (I : Top4Node) : Top4Stored I.1 (top4Init I) :=
  top4Open_stored (topcsInit_stored rfl)
theorem top4Combine_stored (z : Top4Node × ℕ × Top4State × RawCoset) :
    Top4Stored z.1.1 (top4Combine z) := by
  unfold top4Combine
  split
  · exact top4Open_stored (topcsStep_stored rfl _ _ _ _ _ _)
  · exact ⟨top4Closed_stored _, Nat.min_le_right _ _, size_top2NormC_le rfl le_rfl _⟩

theorem top4Stored_size {c d e f : ℕ} {C : Top4Context} {s : Top4State}
    (hC : Enc.size C ≤ topcsContextCap c d (top4X C).length) (hs : Top4Stored C s) :
    Enc.size s ≤ top4Bound c d e f (top4X C).length := by
  have hP := (size_snd_le' C.1).trans ((size_fst_le' C).trans hC)
  have hk : (topcsX C.1.2).length ≤ topcsContextCap c d (top4X C).length :=
    (length_le_size _).trans ((topcsFields_size C.1.2).1.trans hP)
  have hinner := size_topcsStored (B := fun _ => topcsContextCap c d (top4X C).length) hP hs.1
  have hm := mono_chainBound hk
  have hi := size_nat_le_self s.2.1
  have hw := (length_le_size (top4Wins C)).trans
    ((size_fst_le' C.2).trans ((size_snd_le' C).trans hC))
  have hp := size_pair_le' s
  have hp' := size_pair_le' s.2
  obtain ⟨_, hi', ha⟩ := hs
  unfold topcsBound at hinner
  dsimp only at hinner
  unfold top4Bound
  omega

theorem top4Node_size {c d e f : ℕ} {I : Top4Node} (hI : Top4WF c d e f I) :
    Enc.size I ≤ top4Bound c d e f (top4X I.1).length := by
  have hp := size_pair_le' I
  have hctx := hI.1
  cases ho : I.2 with
  | none =>
    have hs : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold top4Bound
    omega
  | some W =>
    have hW := hI.2 W ho
    have hm := mono_top4LeafCap e f hctx
    have hs : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold top4Bound
    omega

def top4RunCostQ (c d e f : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (top4Round c d e f solve) where
  bound := top4Bound c d e f
  polyBound_bound := polyBound_top4Bound c d e f
  mono_bound := mono_top4Bound c d e f
  stateBound := top4Bound c d e f
  quasiPolyBound_stateBound := (polyBound_top4Bound c d e f).quasiPoly
  mono_stateBound := mono_top4Bound c d e f
  widthBound := fun n => (topcsContextCap c d n + 2) * topcsContextCap c d n + topcsContextCap c d n
  quasiPolyBound_widthBound := ((((polyBound_topcsContextCap c d).add
    (polyBound_const 2)).mul (polyBound_topcsContextCap c d)).add (polyBound_topcsContextCap c d)).quasiPoly
  quasiFun_child := (polyFun_top4Child e f).quasiFun
  quasiFun_init := polyFun_top4Init.quasiFun
  quasiFun_combine := polyFun_top4Combine.quasiFun
  quasiFun_finish := quasiFun_top4Finish hsolve
  ground_le := fun I => (length_le_size _).trans ((size_snd_le' I.1.1.1.2).trans
    ((size_snd_le' I.1.1.1).trans ((size_fst_le' I.1.1).trans ((size_fst_le' I.1).trans (size_fst_le' I)))))
  size_le := fun _ hI => top4Node_size hI
  init_le := fun _ hI => top4Stored_size hI.1 (top4Init_stored _)
  combine_le := fun _ _ _ _ hI _ _ => top4Stored_size hI.1 (top4Combine_stored _)
  finish_le := by
    intro I s _ _
    have h := size_top2NormC_le (n := (top4X I.1).length) rfl (le_refl _)
      (I.2.elim s.2.2 solve)
    change Enc.size (top2NormC (top4X I.1) _) ≤ top4Bound c d e f (top4X I.1).length
    dsimp only
    unfold top4Bound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    unfold top4Bound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    have hP := (size_snd_le' I.1.1).trans ((size_fst_le' I.1).trans hI.1)
    cases I.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      apply Nat.add_le_add
      · apply Nat.mul_le_mul
        · exact Nat.add_le_add_right ((topcsCount_le I.1.1.2).trans hP) 2
        · exact (topcsWins_length_le I.1.1.2).trans hP
      · exact (length_le_size _).trans ((size_fst_le' I.1.2).trans ((size_snd_le' I.1).trans hI.1))
  polyFun_ground := (polyFun_fst.comp polyFun_top4X).comp polyFun_length
  wfCheck := top4Check c d e f
  polyFun_wfCheck := polyFun_top4Check c d e f
  wfCheck_eq_true := top4Check_spec c d e f
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

end Algo
