import Workspace.Algo.TopMasterChainOrbits

/-! # The computed Chain Rule enters the live line-1 choice
The group-frame target is restored on the parent window and equals the
source off that window. This is the exact convention of the paper's lift.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical Pointwise

noncomputable def masterChainData {n : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1)) :
    WindowData (masterGroupInstance n W) where
  K := decGroup n W.2.1
  isGroup := rfl
  invariant := hinv
  orbits := masterOrbitEnum hw hlt hinv

def masterChainPrepared (W : RawWinSI) : RawWinSI :=
  (W.1, W.2.1, rawOne W.2.2.2.1, W.2.2.2.1,
    topwExtendStr (W.2.2.2.1, W.1, (primitiveWindowInput W).2.2))

theorem polyFun_masterChainPrepared : PolyFun masterChainPrepared := by
  have hx : PolyFun (fun W : RawWinSI => W.2.2.2.1) :=
    (((polyFun_snd.comp polyFun_snd).comp polyFun_snd).comp polyFun_fst)
  have hy := ((hx.pair (polyFun_fst.pair
    ((polyFun_primitiveWindowInput.comp polyFun_snd).comp polyFun_snd))).comp polyFun_topwExtendStr)
  exact polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
    ((hx.comp polyFun_rawOne).pair (hx.pair hy)))

def masterChainPreparedEnter (W : RawWinSI) : MasterChainNode := masterChainEnter (masterChainPrepared W)

theorem polyFun_masterChainPreparedEnter : PolyFun masterChainPreparedEnter :=
  polyFun_masterChainPrepared.comp polyFun_masterChainEnter

 theorem masterChainPreparedEnter_uniform_wf (A B : ℕ) : ∃ a b : ℕ,
    ∀ (n : ℕ) (W : RawWinSI), W.2.2.2.1.length = n → Enc.size W ≤ topcsContextCap A B n →
      MasterChainWF a b (masterChainPreparedEnter W) := by
  obtain ⟨F, hF, hmF, hsF⟩ := polyFun_masterChainPrepared.size.exists_polyBound
  obtain ⟨aa, bb, hab⟩ := hF.comp (polyBound_topcsContextCap A B)
  obtain ⟨a, b, h⟩ := masterChainEnter_uniform_wf aa bb
  exact ⟨a, b, fun n W hn hW => h n (masterChainPrepared W) hn
    ((hsF W).trans ((hmF _ _ hW).trans (hab n)))⟩

section Choice
variable {n : ℕ} {W : RawWinSI} (hx : W.2.2.2.1.length = n)
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

include hx hnd hlt in
theorem masterChainPrepared_target :
    decStrN n (masterChainPrepared W).2.2.2.2 =
      extendStr (winSet n W.1) (masterGroupInstance n W).x
        (restrictStr (winSet n W.1) (masterGroupInstance n W).y) := by
  rw [masterChainPrepared, topwExtendStr_spec hx hnd hlt]
  congr 1
  funext u
  change decStrN W.1.length
      (rawRestrictStr (top4aTarget (W.2.2.2.1, W.2.2.1, W.2.2.2.2), W.1))
      ((winEquiv n W.1 hnd hlt).symm u) = _
  rw [topwRestrictStr_decode hnd hlt]
  simp only [Equiv.apply_symm_apply]
  rfl

include hx hnd in
 theorem masterChainData_trace (u : (masterGroupInstance n W).Δ) :
    (masterChainTree n (masterChainPrepared W)).calls = (chainRuleCoset (masterChainData hw hlt hinv) u).calls ∧
      (masterChainTree n (masterChainPrepared W)).run = (chainRuleCoset (masterChainData hw hlt hinv) u).run := by
  have h := masterWindowChain_trace hinv (masterGroupInstance n W).x
    (restrictStr (winSet n W.1) (masterGroupInstance n W).y)
    (masterOrbitWindows n W) (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) le_rfl
  dsimp only at h
  rw [masterWindowPreim_group hinv, masterOrbitWindows_image hw hlt hinv] at h
  have he : masterChainTree n (masterChainPrepared W) =
      Babai.cosetChain (masterGroupInstance n W).x
        (extendStr (winSet n W.1) (masterGroupInstance n W).x
          (restrictStr (winSet n W.1) (masterGroupInstance n W).y))
        ((winOrbits (W.2.1, W.1)).map (winSet n)) (decGroup n W.2.1) := by
    unfold masterChainTree
    rw [masterChainPrepared_target hx hnd hlt]
    change Babai.cosetChain _ _ _ (decCoset n (some (W.2.1, rawOne W.2.2.2.1))) = _
    rw [decCoset_some, decPerm_rawOne hx, one_smul]
    rfl
  rw [he]
  exact ⟨h.1.symm, h.2.symm⟩

include hx hnd in
 theorem masterChainData_loop (a b : ℕ) (solve : RawWinSI → RawCoset)
    (u : (masterGroupInstance n W).Δ) :
    LoopMatch (masterChainRound a b solve) (masterChainDecode n) (decCoset n)
      (masterChainPreparedEnter W) (winOrbits (W.2.1, W.1)).length 0
      (masterChainInit (masterChainPreparedEnter W)) (chainRuleCoset (masterChainData hw hlt hinv) u) := by
  have h := masterChainData_trace hx hw hnd hlt hinv u
  exact loopMatch_of_trace (masterChainEnter_loop a b solve hx) h.1 h.2
end Choice
end Algo
