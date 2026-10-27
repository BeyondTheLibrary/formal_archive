import Workspace.Algo.TopMasterFourCost

/-! # Exact matching and shrinking calls for the actual line 4b entry -/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Branch
variable {n m : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hgs : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3)

noncomputable def master4Tree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (masterLine4bTree hnd hlt hinv hp hG hϕ hn hr).bind
    (fun A => .done (decPerm n p.1.2.2.1 • A))

include hx hgs in
theorem master4Enter_loop {a b c d e f u v : ℕ} (hcap : TopwpCap e f)
    (houter : Top4wCap e f u v) (solve : RawWinSI → RawCoset) :
    let I := master4Enter p
    LoopMatch (master4Round a b c d e f u v solve) (master4Decode n) (decCoset n) I
      ((master4Round a b c d e f u v solve).width I) 0 (master4Init I)
      (master4Tree hnd hlt hinv hp hG hϕ hn hr) := by
  have h := master4LoopMatch (r := normPerm (p.1.2.2.2.1, p.1.2.2.1)) hx solve
    (masterLine4b_loop (a := a) (b := b) (c := c) (d := d)
      hx hgs hnd hlt hinv hp hG hϕ hn hr hcap houter solve)
  rw [decPerm_normPerm hx] at h
  exact h

include hx hgs in
theorem master4Tree_spec :
    let T := master4Tree hnd hlt hinv hp hG hϕ hn hr
    T.run = (decWinSI n p.1).answer ∧ T.calls.length ≤ 7 * p.1.1.length ∧
      ∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * p.1.1.length := by
  obtain ⟨hrun, hlen, hwin⟩ := masterLine4b_spec hx hgs hnd hlt hinv hp hG hϕ hn hr
  refine ⟨?_, ?_, ?_⟩
  · change (master4Tree hnd hlt hinv hp hG hϕ hn hr).run = _
    rw [master4Tree, SIReduction.run_bind, SIReduction.run_done, hrun]
    change _ = wIso (winSet n p.1.1) (decCoset n (some (p.1.2.1, p.1.2.2.1))) _ _
    rw [decCoset_some, wIso_smul]
    rfl
  · simpa only [master4Tree, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil] using hlen
  · simpa only [master4Tree, SIReduction.calls_bind, SIReduction.calls_done,
      List.append_nil] using hwin

end Branch
end Algo
