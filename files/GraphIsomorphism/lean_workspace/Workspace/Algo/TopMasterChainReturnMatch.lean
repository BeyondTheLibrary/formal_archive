import Workspace.Algo.TopMasterChainReturnCost

/-! # The complete orbit-chain phase restores the original candidate coset -/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Return
variable {n B C₀ : ℕ} {W : RawWinSI}
    (hx : W.2.2.2.1.length = n) (hw : RawGens.WF n W.2.1)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2) (q : ℕ) (hC : 1 < C₀)

noncomputable def masterChainReturnTree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (masterChainCase hw hnd hlt hinv hr q hC).cosetBranch.bind
    (fun A => .done (decPerm n W.2.2.1 • A))

include hx in
theorem masterChainReturn_match (a b : ℕ) (solve : RawWinSI → RawCoset) :
    LoopMatch (masterChainReturnRound a b solve) (masterChainReturnDecode n) (decCoset n)
      (masterChainReturnEnter W) (winOrbits (W.2.1, W.1)).length 0
      (masterChainReturnInit (masterChainReturnEnter W))
      (masterChainReturnTree hw hnd hlt hinv hr q hC) := by
  have h := masterChainReturnLoopMatch (r := normPerm (W.2.2.2.1, W.2.2.1)) hx solve
    (masterChainCase_loop hw hnd hlt hinv hr a b q hC solve hx)
  rw [decPerm_normPerm hx] at h
  exact h

include hx in
theorem masterChainReturn_spec :
    (masterChainReturnTree hw hnd hlt hinv hr q hC).run = (decWinSI n W).answer := by
  rw [masterChainReturnTree, SIReduction.run_bind, SIReduction.run_done]
  dsimp only [masterChainCase, Line1Case.cosetBranch]
  rw [run_chainRuleCoset, masterGroupInstance_answer hx]

 theorem masterChainReturn_calls :
    (masterChainReturnTree hw hnd hlt hinv hr q hC).calls =
      (masterChainCase hw hnd hlt hinv hr q hC).cosetBranch.calls := by
  simp [masterChainReturnTree]

 theorem masterChainReturn_progress :
    (∀ J ∈ (masterChainReturnTree hw hnd hlt hinv hr q hC).calls,
      J.windowSize < (decWinSI n W).windowSize) ∧
    (((masterChainReturnTree hw hnd hlt hinv hr q hC).calls).map SIInstance.windowSize).sum ≤
      (decWinSI n W).windowSize := by
  rw [masterChainReturn_calls]
  exact masterChainCase_progress hw hnd hlt hinv hr q hC
end Return
end Algo
