import Workspace.Algo.TopSuppliedSize

/-! # Cost of the complete supplied top-action-3 round

The recursive solver is charged explicitly at leaves. All preparation, tests,
fold updates, and final reconstruction are concrete RAM routines. The round
retains only polynomially sized state, hence also satisfies `CostQ`.
-/

namespace Algo

open RAM RAM.Targets

/-- Full local cost data, with the recursive leaf solver and its output bound
as the usual composition hypotheses. The answer-size hypothesis only concerns
leaves actually made by this round. It does not assume their correctness. -/
def topcsCostQ (n : ℕ) (B : ℕ → ℕ) (hB : PolyBound B) (hmB : Monotone B)
    (solve : RawWinSI → RawCoset) (hsolve : QuasiFun solve)
    (hsize : ∀ P : TopcsInput, (topcsX P).length = n → Enc.size P ≤ B n →
      ∀ t i c, Enc.size (solve (topcsLeaf P t i c)) ≤ chainBound n) :
    Round.CostQ (topcsRound n B solve) where
  bound := topcsBound B
  polyBound_bound := polyBound_topcsBound hB
  mono_bound := mono_topcsBound hmB
  stateBound := topcsBound B
  quasiPolyBound_stateBound := (polyBound_topcsBound hB).quasiPoly
  mono_stateBound := mono_topcsBound hmB
  widthBound := fun m => (B m + 2) * B m
  quasiPolyBound_widthBound := ((hB.add (polyBound_const 2)).mul hB).quasiPoly
  quasiFun_child := polyFun_topcsChild.quasiFun
  quasiFun_init := polyFun_topcsInit.quasiFun
  quasiFun_combine := polyFun_topcsCombine.quasiFun
  quasiFun_finish := quasiFun_topcsFinish hsolve
  ground_le := by
    intro I
    exact le_trans (length_le_size _) (le_trans (topcsFields_size I.1).1 (size_fst_le' I))
  size_le := by
    intro I hI
    change Enc.size I ≤ topcsBound B (topcsX I.1).length
    rw [hI.1]
    exact size_topcsNode hI
  init_le := by
    intro I hI
    change Enc.size (topcsInit I) ≤ topcsBound B (topcsX I.1).length
    rw [hI.1]
    exact size_topcsStored hI.2.1 (topcsInit_stored hI.1)
  combine_le := by
    intro I j s a hI _ _
    change Enc.size (topcsStep I.1 s.1 s.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 a)
      ≤ topcsBound B (topcsX I.1).length
    rw [hI.1]
    exact size_topcsStored hI.2.1 (topcsStep_stored hI.1 _ _ _ _ _ _)
  finish_le := by
    intro I s hI _
    change Enc.size (topcsFinish solve (I, s)) ≤ topcsBound B (topcsX I.1).length
    rw [hI.1]
    have hc : Enc.size (topcsFinish solve (I, s)) ≤ chainBound n := by
      cases ho : I.2 with
      | none =>
        change Enc.size (I.2.elim ((topcsAnswer I.1 s).getD none) solve) ≤ _
        rw [ho, Option.elim_none]
        exact size_topcsAnswer hI.1 s
      | some W =>
        obtain ⟨t, i, c, rfl⟩ := hI.2.2 W ho
        change Enc.size (I.2.elim ((topcsAnswer I.1 s).getD none) solve) ≤ _
        rw [ho, Option.elim_some]
        exact hsize I.1 hI.1 hI.2.1 t i c
    unfold topcsBound
    omega
  bot_le := by
    intro m
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    unfold topcsBound
    omega
  width_le := by
    intro I hI
    change I.2.elim (topcsJobs I.1 * (topcsWins I.1).length) (fun _ => 0) ≤
      (B (topcsX I.1).length + 2) * B (topcsX I.1).length
    rw [hI.1]
    cases I.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      apply Nat.mul_le_mul
      · have := topcsCount_le I.1
        have := hI.2.1
        change topcsCount I.1 + 2 ≤ B n + 2
        omega
      · exact le_trans (topcsWins_length_le I.1) hI.2.1

/-- The local carrier itself needs no oracle to have a cost certificate. Its
placeholder leaf answer is ignored by phase matching, which quantifies over
all correctly decoded recursive answers. A master embedding supplies the
actual solver through `topcsCostQ`. -/
def topcsLocalCostQ (n : ℕ) (B : ℕ → ℕ) (hB : PolyBound B) (hmB : Monotone B) :
    Round.CostQ (topcsRound n B (fun _ => none)) :=
  topcsCostQ n B hB hmB (fun _ => none) (quasiFun_const none) (by
    intro P hx hP t i c
    rw [size_none]
    have := chainBound_ge n
    omega)

end Algo
