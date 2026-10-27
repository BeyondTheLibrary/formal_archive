import Workspace.Algo.TopFourAmbientRAM

/-! # Charging inner state to the retained ambient context
An inner window may contain color names from a larger input. Its state is
bounded by the retained context size, without assuming an encoding bound
in terms of the smaller window degree alone.
-/
namespace Algo
open RAM RAM.Targets

def top4ContextStateBound (N : ℕ) : ℕ := 4096 * (N + chainBound N + 4)

theorem polyBound_top4ContextStateBound : PolyBound top4ContextStateBound :=
  (polyBound_const 4096).mul ((polyBound_id.add polyBound_chainBound).add (polyBound_const 4))

theorem mono_top4ContextStateBound : Monotone top4ContextStateBound := by
  intro n m h
  have := mono_chainBound h
  unfold top4ContextStateBound
  omega

theorem top4Stored_size_context {N : ℕ} {C : Top4Context} {s : Top4State}
    (hC : Enc.size C ≤ N) (hs : Top4Stored C s) : Enc.size s ≤ top4ContextStateBound N := by
  have hP := (size_snd_le' C.1).trans ((size_fst_le' C).trans hC)
  have hk : (topcsX C.1.2).length ≤ N :=
    (length_le_size _).trans ((topcsFields_size C.1.2).1.trans hP)
  have hx : (top4X C).length ≤ N := (length_le_size _).trans
    ((size_snd_le' C.1.1.2).trans ((size_snd_le' C.1.1).trans ((size_fst_le' C.1).trans
      ((size_fst_le' C).trans hC))))
  have hinner := size_topcsStored (B := fun _ => N) hP hs.1
  have hm := mono_chainBound hk
  have hx' := mono_chainBound hx
  have hi := size_nat_le_self s.2.1
  have hw := (length_le_size (top4Wins C)).trans
    ((size_fst_le' C.2).trans ((size_snd_le' C).trans hC))
  have hp := size_pair_le' s
  have hp' := size_pair_le' s.2
  obtain ⟨_, hi', ha⟩ := hs
  unfold topcsBound at hinner
  dsimp only at hinner
  unfold top4ContextStateBound
  omega

def top4ContextWidthBound (N : ℕ) : ℕ := (N + 2) * N + N
theorem polyBound_top4ContextWidthBound : PolyBound top4ContextWidthBound :=
  ((polyBound_id.add (polyBound_const 2)).mul polyBound_id).add polyBound_id
theorem mono_top4ContextWidthBound : Monotone top4ContextWidthBound := by
  intro n m h
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.add_le_add_right h 2) h) h

theorem top4aWidth_context {c d e f N : ℕ} {I : Top4aNode}
    (hC : Enc.size I.1.1 ≤ N) (solve : RawWinSI → RawCoset) :
    (top4aRound c d e f solve).width I ≤ top4ContextWidthBound N := by
  change (if top4aGate I then I.1.2.elim (top4Width I.1.1) (fun _ => 0) else 0) ≤ _
  split
  · cases I.1.2 with
    | some _ => exact Nat.zero_le _
    | none =>
      have hP := (size_snd_le' I.1.1.1).trans ((size_fst_le' I.1.1).trans hC)
      apply Nat.add_le_add
      · apply Nat.mul_le_mul
        · exact Nat.add_le_add_right ((topcsCount_le I.1.1.1.2).trans hP) 2
        · exact (topcsWins_length_le I.1.1.1.2).trans hP
      · exact (length_le_size _).trans ((size_fst_le' I.1.1.2).trans ((size_snd_le' I.1.1).trans hC))
  · exact Nat.zero_le _

end Algo
