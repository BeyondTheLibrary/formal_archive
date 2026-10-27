import Workspace.Algo.TopMasterCameronOpen

/-! # Cameron representatives followed by local kernel-orbit chains
The Cameron index is at most the degree. Thus the representative list
can be bounded directly, without a table of all signed-coordinate maps.
The Chain Rule is evaluated inside the same master node.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

def masterCamFuel (p : RawCameron × MasterDescInput) : List ℕ :=
  (rawOne p.2.1.2.2.2.1).take (masterCamOpenWidth p)

def masterCamReps (p : RawCameron × MasterDescInput) : RawGens :=
  (masterCamFuel p).map fun j => masterDescRep (masterCameronDescInput p, j)

def masterCamLists (p : RawCameron × MasterDescInput) : AggnRecomputeInput :=
  (p.2.1, camLiftGens (p.1, masterDescAction p.2), masterCamReps p,
    winOrbits (camLiftGens (p.1, masterDescAction p.2), p.2.1.1))

theorem polyFun_masterCamFuel : PolyFun masterCamFuel := by
  have hw : PolyFun (fun p : RawCameron × MasterDescInput => p.2.1) :=
    polyFun_snd.comp polyFun_fst
  have hx := (((hw.comp polyFun_snd).comp polyFun_snd).comp polyFun_snd).comp polyFun_fst
  exact (((hx.comp polyFun_rawOne).pair polyFun_masterCamOpenWidth).comp polyFun_take).of_eq
    (fun _ => rfl)

theorem polyFun_masterCamReps : PolyFun masterCamReps := by
  have hmap : PolyFun (fun q : MasterDescInput × List ℕ =>
      q.2.map (fun j => masterDescRep (q.1, j))) := PolyFun.mapParam polyFun_masterDescRep
  have hh := (polyFun_masterCameronDescInput.pair polyFun_masterCamFuel).comp hmap
  exact hh.of_eq (fun p => by dsimp only [masterCamReps])

theorem polyFun_masterCamLists : PolyFun masterCamLists := by
  have hk := (polyFun_fst.pair (polyFun_snd.comp polyFun_masterDescAction)).comp
    polyFun_camLiftGens
  exact (polyFun_snd.comp polyFun_fst).pair (hk.pair
    (polyFun_masterCamReps.pair
      ((hk.pair ((polyFun_snd.comp polyFun_fst).comp polyFun_fst)).comp polyFun_winOrbits)))

theorem masterCamFuel_eq (p : RawCameron × MasterDescInput) :
    masterCamFuel p = List.range (masterCamOpenWidth p) := by
  rw [masterCamFuel, rawOne, List.take_range]
  exact congrArg List.range (Nat.min_eq_left (Nat.min_le_right _ _))

section Action
variable {n m : ℕ} {p : MasterDescInput} {c : RawCameron}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ) (h : c.WF m)
    (hhi : (decGroup m p.2.2).map (permCongrHom (decCameron c h)).toMonoidHom ≤
      wreathProduct (JohnsonS c.k c.t) c.s)
    (hW : AggnCheckedWindowWF n p.1) (hm : m ≤ p.1.1.length)
    (hidx : (camNbar c h).relIndex (decGroup m p.2.2) ≤ m)

include hp h hhi hW hm hidx in
theorem masterCamLists_reps :
    aggnrReps n (masterCamLists (c, p)) = masterDescPerms n (masterCameronDescInput (c, p)) := by
  simp only [aggnrReps, masterCamLists, masterCamReps, masterCamFuel_eq,
    masterCamOpenWidth_eq hp h hhi hW hm hidx, masterDescPerms, List.map_map]
  rfl

include hp h hhi hW hm hidx in
theorem masterCamLists_cover : (decWinSI n p.1).K =
    ⋃ σ ∈ aggnrReps n (masterCamLists (c, p)),
      σ • (decGroup n (camLiftGens (c, masterDescAction p)) : Set (Perm (Fin n))) := by
  rw [masterCamLists_reps hp h hhi hW hm hidx]
  exact masterDesc_cover (p := masterCameronDescInput (c, p)) (masterCameronDesc_wf hp h hhi)

noncomputable def masterCamStrongTree (n : ℕ) (p : RawCameron × MasterDescInput) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  strongDescent (decGroup n (masterCamLists p).2.1)
    (decStrN n p.2.1.2.2.2.1) (decStrN n p.2.1.2.2.2.2)
    (aggnrReps n (masterCamLists p)) ((aggnrWindows (masterCamLists p)).map (winSet n))

include hp h hhi hW hm hidx in
theorem masterCamStrongTree_run
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1)) :
    (masterCamStrongTree n (c, p)).run = (decWinSI n p.1).answer := by
  rw [masterCamStrongTree, run_strongDescent]
  change wIso (⋃ U ∈ (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).map (winSet n), U)
    (⋃ σ ∈ aggnrReps n (masterCamLists (c, p)),
      σ • (decGroup n (camLiftGens (c, masterDescAction p)) : Set (Perm (Fin n)))) _ _ = _
  rw [← masterCamLists_cover hp h hhi hW hm hidx]
  change wIso (⋃ U ∈ (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).map (winSet n), U)
    (decWinSI n p.1).K _ _ = _
  rw [masterWinOrbits_union (camLiftGens_wf (p := masterDescAction p) (c := c) hp) hW.2.1
    (isInvariant_of_le hinv (camLiftGens_le (p := masterDescAction p) hp h hhi))]
  rfl

include hp h hhi hW hm hidx in
theorem masterCamStrongTree_hull
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1)) :
    cosetHull (masterCamStrongTree n (c, p)).run = (masterCamStrongTree n (c, p)).run := by
  rw [masterCamStrongTree_run hp h hhi hW hm hidx hinv]
  rcases Set.eq_empty_or_nonempty (decWinSI n p.1).answer with he | ⟨τ, hτ⟩
  · rw [he, cosetHull_empty]
  · simp only [SIInstance.answer, decWinSI, decCoset_some] at hτ ⊢
    have he := wIso_eq_smul_wAut hinv (decPerm n p.1.2.2.1) hτ
    change wIso (winSet n p.1.1) (decPerm n p.1.2.2.1 • (decGroup n p.1.2.1 : Set _))
      (decStrN n p.1.2.2.2.1) (decStrN n p.1.2.2.2.2) = _ at he
    change cosetHull (wIso _ _ _ _) = _
    rw [he]
    exact cosetHull_smul_subgroup τ (wAutSubgroup _ _ hinv _)

include hp h hhi hW hm hidx in
theorem masterCamStrongTree_calls :
    (masterCamStrongTree n (c, p)).calls.length ≤ m * p.1.1.length := by
  refine (length_calls_strongDescent _ _ _ _ _).trans ?_
  rw [masterCamLists_reps hp h hhi hW hm hidx]
  simp only [masterDescPerms, List.length_map, List.length_range]
  rw [masterCameronDesc_width hp h hhi]
  exact Nat.mul_le_mul hidx (length_winOrbits_le _ _)

include hp h hhi hW in
theorem masterCamStrongTree_progress
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (h2 : 1 < (winOrbits (camLiftGens (c, masterDescAction p), p.1.1)).length) :
    ∀ J ∈ (masterCamStrongTree n (c, p)).calls, J.windowSize < p.1.1.length := by
  intro J hJ
  have hD := (mem_calls_strongDescent _ _ _ _ _ hJ).1
  obtain ⟨D, hD, he⟩ := List.mem_map.mp hD
  change D ∈ winOrbits (camLiftGens (c, masterDescAction p), p.1.1) at hD
  have hw := camLiftGens_wf (p := masterDescAction p) (c := c) hp
  have hi := (rawIsInvariant_eq_true_iff hw hW.2.1).mpr
    (isInvariant_of_le hinv (camLiftGens_le (p := masterDescAction p) hp h hhi))
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hD
  change J.Δ.ncard < _
  rw [← he, ncard_winSet _ (winOrbits_nodup (List.getElem_mem hj))
    (winOrbits_lt hw hW.2.1 hi (List.getElem_mem hj))]
  exact winOrbits_length_lt hw hW.1 hW.2.1 hi hj h2
end Action
end Algo
