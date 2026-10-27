import Workspace.Algo.TopMasterCheckedCall

/-! # Exact matching survives master input checks
The call-tree invariant is used only at the actual calls reached with
correct answers. It proves that normalization and admission preserve each
instance. Malformed fold states need no semantic hypothesis.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 theorem masterAdmittedRound_checked_match {ι ω S : Type} (a b : ℕ)
    {R : Round ι ω RawCoset} {F : MasterOps S} {n : ℕ}
    {I : ι} {p : RawMasterSI} (hn : masterDegree p = n)
    (hp : masterWindowSize p ≤ masterDegree p)
    (read : ι → RawWinSI) (u : ω → S) (decI : ι → SIInstance (Fin n) ℕ)
    (hread : ∀ j s J, R.child (I, j, s) = some J → decI J = decWinSI n (read J))
    (hw : F.width p = R.width I)
    (hc : ∀ j s, F.child (p, j, u s) =
      (R.child (I, j, s)).map (fun J => masterCheckedCall (p.1.2.2.2.1, read J)))
    (hi : F.init p = u (R.init I))
    (hu : ∀ j s A, F.combine (p, j, u s, A) = u (R.combine (I, j, s, A)))
    (hf : ∀ s, F.finish (p, u s) = R.finish (I, s))
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch R decI (decCoset n) I (R.width I) 0 (R.init I) T)
    (hT : ∀ J ∈ T.calls, MasterCallLetters (2 * n + 1) J ∧ J.windowSize < masterWindowSize p ∧
      ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      p (F.width p) 0 (F.init p) T := by
  rw [hw, hi]
  apply loopMatch_reparent_onCalls
    (fun J => masterCheckedCall (p.1.2.2.2.1, read J)) u I p
    (fun J => MasterCallLetters (2 * n + 1) J ∧ J.windowSize < masterWindowSize p ∧
      ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J)
    (R := R) (M := masterAdmittedRound a b F) (decI := decI)
    (decN := fun J => decWinSI n J.1) (decA := decCoset n) _ _ _ hu hf
    _ _ _ T h hT
  · intro j s J hJ hv
    rw [hread j s J hJ] at hv ⊢
    exact masterCheckedCall_decode hn (read J) hv.1
  · intro j s hs
    change masterGuardedChild a b F (p, j, u s) = none
    unfold masterGuardedChild
    rw [hc, hs, Option.map_none]
    split_ifs <;> rfl
  · intro j s J hJ hv
    have hj : j < R.width I := by
      by_contra hj
      have hnone := R.child_eq_none I j s (Nat.le_of_not_gt hj)
      rw [hJ] at hnone
      contradiction
    change masterGuardedChild a b F (p, j, u s) = _
    unfold masterGuardedChild
    rw [hw, if_pos hj, hc, hJ, Option.map_some]
    rw [hread j s J hJ] at hv
    subst hn
    obtain ⟨hL, hlt, G, hG⟩ := hv
    exact masterCheckedCall_admitted a b (read J) hp hlt hL hG
end Algo
