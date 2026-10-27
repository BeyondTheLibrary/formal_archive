import Workspace.Algo.TopMasterChainMatch

/-! # The computed orbit list enters the uniform chain
The entry routine retains the actual ordered orbit list. Its cost and
context cap are fixed before the degree or the instance is supplied.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem polyFun_masterChainEnter : PolyFun masterChainEnter :=
  (polyFun_id.pair ((((polyFun_snd.comp polyFun_fst).pair polyFun_fst).comp
    polyFun_winOrbits))).pair (polyFun_const none)

theorem masterChainEnter_uniform_wf (A B : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (W : RawWinSI), W.2.2.2.1.length = n → Enc.size W ≤ topcsContextCap A B n →
      MasterChainWF a b (masterChainEnter W) := by
  obtain ⟨F, hF, hmF, hsF⟩ := (polyFun_masterChainEnter.comp polyFun_fst).size.exists_polyBound
  obtain ⟨a, b, hab⟩ := hF.comp (polyBound_topcsContextCap A B)
  refine ⟨a, b, fun n W hn hW => ⟨?_, fun _ h => by contradiction⟩⟩
  change Enc.size (masterChainEnter W).1 ≤ topcsContextCap a b W.2.2.2.1.length
  rw [hn]
  exact (hsF W).trans ((hmF _ _ hW).trans (hab n))

noncomputable def masterChainTree (n : ℕ) (W : RawWinSI) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  Babai.cosetChain (decStrN n W.2.2.2.1) (decStrN n W.2.2.2.2)
    ((winOrbits (W.2.1, W.1)).map (winSet n)) (decCoset n (some (W.2.1, W.2.2.1)))

theorem masterChainEnter_loop (a b : ℕ) (solve : RawWinSI → RawCoset)
    {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n) :
    LoopMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n)
      (masterChainEnter W) (winOrbits (W.2.1, W.1)).length 0
      (masterChainInit (masterChainEnter W)) (masterChainTree n W) :=
  masterChainLoop_chain a b solve hx

theorem masterChainTree_spec {n : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : rawIsInvariant (W.2.1, W.1) = true) :
    (masterChainTree n W).run = (decWinSI n W).answer := by
  rw [masterChainTree, Babai.run_cosetChain, iUnion_winOrbits hw hlt hinv]
  rfl

theorem masterChainTree_calls (n : ℕ) (W : RawWinSI) :
    (masterChainTree n W).calls.length ≤ W.1.length :=
  (Babai.calls_cosetChain _ _ _ _).1.trans
    ((List.length_map _).le.trans (length_winOrbits_le _ _))

theorem masterChainChild_progress {n : ℕ} {W : RawWinSI} {j : ℕ} {s : RawCoset}
    {J : MasterChainNode} (hW : WinWF n W)
    (h2 : 1 < (winOrbits (W.2.1, W.1)).length)
    (hJ : masterChainChild (masterChainEnter W, j, s) = some J) :
    ∃ V, J.2 = some V ∧ V.1.length < W.1.length := by
  obtain ⟨c, _, _, hj, rfl⟩ := masterChainChild_some hJ
  refine ⟨_, rfl, ?_⟩
  change ((winOrbits (W.2.1, W.1)).getD j []).length < _
  change j < (winOrbits (W.2.1, W.1)).length at hj
  rw [List.getD_eq_getElem _ _ hj]
  exact winOrbits_length_lt hW.2.2.2.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2.2.2.2 hj h2

end Algo
