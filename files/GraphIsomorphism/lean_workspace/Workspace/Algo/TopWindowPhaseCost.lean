import Workspace.Algo.TopWindowPhaseRAM

/-! # Uniform executable cost certificate for the window phase

The degree is the length of the ambient reference source. The local state
is normalized on the inner source domain, whose length is bounded by the
retained context. Thus both domains are charged to the original input.
-/
set_option synthInstance.maxSize 1024
namespace Algo
open RAM RAM.Targets

 def topwpBound (c d e f n : ℕ) : ℕ :=
  256 * (topcsContextCap c d n + chainBound (topcsContextCap c d n) +
    topcsContextCap e f (topcsContextCap c d n) + chainBound n + 4)

 theorem polyBound_topwpBound (c d e f : ℕ) : PolyBound (topwpBound c d e f) :=
  (polyBound_const 256).mul (((((polyBound_topcsContextCap c d).add
    (polyBound_chainBound.comp (polyBound_topcsContextCap c d))).add
    ((polyBound_topcsContextCap e f).comp (polyBound_topcsContextCap c d))).add
    polyBound_chainBound).add (polyBound_const 4))

 theorem mono_topwpBound (c d e f : ℕ) : Monotone (topwpBound c d e f) := by
  intro a b hab
  have h1 := mono_topcsContextCap c d hab
  have h2 := mono_chainBound h1
  have h3 := mono_topcsContextCap e f h1
  have h4 := mono_chainBound hab
  unfold topwpBound
  omega

 theorem topwpStored_size {c d e f n : ℕ} {C : TopwpContext} {s : TopcsState}
    (hC : Enc.size C ≤ topcsContextCap c d n)
    (hs : TopcsStored (topcsX C.2).length C.2 s) :
    Enc.size s ≤ topwpBound c d e f n := by
  have hP := (size_snd_le' C).trans hC
  have hk : (topcsX C.2).length ≤ topcsContextCap c d n :=
    (length_le_size _).trans ((topcsFields_size C.2).1.trans hP)
  have hsmall := size_topcsStored (B := fun _ => topcsContextCap c d n) hP hs
  have hm := mono_chainBound hk
  unfold topcsBound at hsmall
  dsimp only at hsmall
  unfold topwpBound
  omega

 theorem topwpNode_size {c d e f : ℕ} {I : TopwpNode} (hI : TopwpWF c d e f I) :
    Enc.size I ≤ topwpBound c d e f I.1.1.2.2.length := by
  have hp := size_pair_le' I
  have hctx := hI.1
  cases ho : I.2 with
  | none =>
    have hs : Enc.size I.2 = 2 := by rw [ho, size_none]
    unfold topwpBound
    omega
  | some W =>
    have hW := hI.2 W ho
    have hm := mono_topcsContextCap e f hctx
    have hs : Enc.size I.2 = Enc.size W + 2 := by rw [ho, size_some_eq]
    unfold topwpBound
    omega

 def topwpRunCostQ (c d e f : ℕ) (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve) :
    Round.RunCostQ (topwpRound c d e f solve) where
  bound := topwpBound c d e f
  polyBound_bound := polyBound_topwpBound c d e f
  mono_bound := mono_topwpBound c d e f
  stateBound := topwpBound c d e f
  quasiPolyBound_stateBound := (polyBound_topwpBound c d e f).quasiPoly
  mono_stateBound := mono_topwpBound c d e f
  widthBound := fun n => (topcsContextCap c d n + 2) * topcsContextCap c d n
  quasiPolyBound_widthBound := (((polyBound_topcsContextCap c d).add
    (polyBound_const 2)).mul (polyBound_topcsContextCap c d)).quasiPoly
  quasiFun_child := (polyFun_topwpChild e f).quasiFun
  quasiFun_init := polyFun_topwpInit.quasiFun
  quasiFun_combine := polyFun_topwpCombine.quasiFun
  quasiFun_finish := quasiFun_topwpFinish hsolve
  ground_le := fun I => (length_le_size _).trans ((size_snd_le' I.1.1.2).trans
    ((size_snd_le' I.1.1).trans ((size_fst_le' I.1).trans (size_fst_le' I))))
  size_le := fun _ hI => topwpNode_size hI
  init_le := fun _ hI => topwpStored_size hI.1 (topcsInit_stored rfl)
  combine_le := fun _ _ _ _ hI _ _ => topwpStored_size hI.1 (topcsStep_stored rfl _ _ _ _ _ _)
  finish_le := by
    intro I s _ _
    dsimp only [topwpRound, topwpFinish]
    have h := size_top2NormC_le (n := I.1.1.2.2.length) rfl (le_refl _)
      (I.2.elim (topwCosetPreimage (I.1.1.1, I.1.1.2.1, (topcsAnswer I.1.2 s).getD none)) solve)
    change Enc.size (top2NormC I.1.1.2.2 _) ≤ topwpBound c d e f I.1.1.2.2.length
    unfold topwpBound
    omega
  bot_le := by
    intro n
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    unfold topwpBound
    omega
  width_le := by
    intro I hI
    change I.2.elim _ (fun _ => 0) ≤ _
    have hP := (size_snd_le' I.1).trans hI.1
    cases I.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      apply Nat.mul_le_mul
      · exact Nat.add_le_add_right ((topcsCount_le I.1.2).trans hP) 2
      · exact (topcsWins_length_le I.1.2).trans hP
  polyFun_ground := polyFun_topwpGround
  wfCheck := topwpCheck c d e f
  polyFun_wfCheck := polyFun_topwpCheck c d e f
  wfCheck_eq_true := topwpCheck_spec c d e f
  measureBound := fun _ => 1
  polyBound_measureBound := polyBound_const 1
  mono_measureBound := fun _ _ _ => le_rfl
  measure_le := by
    intro I _
    change I.2.elim 1 (fun _ => 0) ≤ 1
    cases I.2 <;> simp

/-- One fixed child cap accepts every actual constructed child, before any
input degree or ambient group is supplied. The same carrier has full RunCostQ. -/
 theorem topwpUniformCarrier : ∃ e f : ℕ, TopwpCap e f ∧
    ∀ (c d : ℕ) (solve : RawWinSI → RawCoset), QuasiFun solve →
      Nonempty (Round.RunCostQ (topwpRound c d e f solve)) := by
  obtain ⟨e, f, hcap⟩ := topwpCap_exists
  exact ⟨e, f, hcap, fun c d solve hs => ⟨topwpRunCostQ c d e f solve hs⟩⟩

end Algo
