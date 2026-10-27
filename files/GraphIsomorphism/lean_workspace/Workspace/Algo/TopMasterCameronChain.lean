import Workspace.Algo.TopMasterCameronLists
import Workspace.Algo.TopMasterStoredDescent

/-! # The Cameron orbit chains run inside the master node
Every coset representative is followed by the Chain Rule on the computed
subgroup orbits. The exact ordered tree and all returned hulls are kept.
No additional master recursion is used to dispatch those chains.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

def masterCamChainOps (f : RawMasterSI → RawCameron × MasterDescInput) :
    MasterOps AggnRecomputeState := masterStoredDescOps (fun p => masterCamLists (f p))

theorem masterCamChain_runCostQ (a b : ℕ) (f : RawMasterSI → RawCameron × MasterDescInput)
    (hf : PolyFun f) (hsource : ∀ p, (f p).2.1.2.2.2.1 = p.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterCamChainOps f))) :=
  masterStoredDesc_runCostQ a b _ (hf.comp polyFun_masterCamLists).quasiFun hsource

section Match
variable {n m a b : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (h2 : 1 < (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length)

include hp h hhi hW hm hidx hinv h2 in
theorem masterCamChain_loop :
    LoopMatch (aggnrRound n (fun _ => none)) (aggnrDecode n) (decCoset n)
      (masterCamLists (c, p), none) (masterDescFoldWidth (masterCamLists (c, p))) 0
      (aggnrInit (masterCamLists (c, p), none)) (masterCamStrongTree n (c, p)) := by
  have hh := masterCamStrongTree_hull hp h hhi hW hm hidx hinv
  have hx : (masterCamLists (c, p)).1.2.2.2.1.length = n := hp.1
  have hpos : 0 < (aggnrWindows (masterCamLists (c, p))).length := Nat.zero_lt_of_lt h2
  have he := aggrPhaseMatch_value (aggnrPhase_descent (P := masterCamLists (c, p))
    (fun _ => none) hx hpos)
  apply loopMatch_of_phaseMatch he _ le_rfl
  intro B j s hs
  constructor
  · simp only [aggnrRound, aggnrChild, Option.elim_none, hs.1.1, lt_self_iff_false, false_and, if_false]
  · change decCoset n s.2.2.2 = B
    rw [hs.1.2.1, hs.2]
    exact hh

variable {S : Type} {F : MasterOps S} (u : AggnRecomputeState → S) (P : RawMasterSI)
    (hP1 : P.1.1 = p.1.1) (hPx : P.1.2.2.2.1 = p.1.2.2.2.1)
    (hw : F.width P = masterDescFoldWidth (masterCamLists (c, p)))
    (hc : ∀ j s, F.child (P, j, u s) = masterDescFoldChild (masterCamLists (c, p), j, s))
    (hi : F.init P = u (masterDescFoldInit (masterCamLists (c, p))))
    (hu : ∀ j s A, F.combine (P, j, u s, A) =
      u (masterDescFoldCombine (masterCamLists (c, p), j, s, A)))
    (hf : ∀ s, F.finish (P, u s) = masterDescFoldFinish (masterCamLists (c, p), s))

include hp h hhi hW hm hidx hinv h2 hP1 hPx hw hc hi hu hf in
/-- The orbit chains at any node with the same window and source. -/
theorem masterCamChain_match_at :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      P (F.width P) 0 (F.init P)
      (masterCamStrongTree n (c, p)) := by
  apply masterAdmittedRound_descent_match a b hp.1 hPx
    (by
      change P.1.1.length ≤ P.1.2.2.2.1.length
      rw [hP1, hPx, hW.2.2.2.2.2.1.1]
      exact length_le_of_nodup_lt hW.1 hW.2.1)
    u hw hc hi hu hf (masterCamChain_loop hp h hhi hW hm hidx hinv h2)
  intro J hJ
  refine ⟨?_, ?_, ⊤, ?_⟩
  · rw [masterCamStrongTree, calls_strongDescent, List.mem_flatMap] at hJ
    obtain ⟨σ, _, hJ⟩ := hJ
    exact masterLetters_cosetChain (2 * n + 1) _ _
      ((masterStrWF_iff hW.2.2.2.2.2.1.1).mp hW.2.2.2.2.2.1)
      ((masterStrWF_iff hW.2.2.2.2.2.2.1).mp hW.2.2.2.2.2.2) _ _ J hJ
  · change J.windowSize < P.1.1.length
    rw [hP1]
    exact masterCamStrongTree_progress hp h hhi hW hinv h2 J hJ
  · refine isCosetInstance_calls_strongDescent le_top _ _ _ _ ?_
      (fun _ _ => Subgroup.mem_top _) hJ
    intro Δ hΔ
    obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hΔ
    exact winOrbits_isInvariant (camLiftGens_wf (p := masterDescAction p) (c := c) hp) hW.2.1 hO

include hp h hhi hW hm hidx hinv h2 in
theorem masterCamChain_match
    (hw : F.width (p.1, none) = masterDescFoldWidth (masterCamLists (c, p)))
    (hc : ∀ j s, F.child ((p.1, none), j, u s) = masterDescFoldChild (masterCamLists (c, p), j, s))
    (hi : F.init (p.1, none) = u (masterDescFoldInit (masterCamLists (c, p))))
    (hu : ∀ j s A, F.combine ((p.1, none), j, u s, A) =
      u (masterDescFoldCombine (masterCamLists (c, p), j, s, A)))
    (hf : ∀ s, F.finish ((p.1, none), u s) = masterDescFoldFinish (masterCamLists (c, p), s)) :
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, none) (F.width (p.1, none)) 0 (F.init (p.1, none))
      (masterCamStrongTree n (c, p)) :=
  masterCamChain_match_at hp h hhi hW hm hidx hinv h2 u (p.1, none) rfl rfl hw hc hi hu hf
end Match
end Algo
