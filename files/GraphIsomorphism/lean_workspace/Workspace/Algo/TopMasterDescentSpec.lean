import Workspace.Algo.TopMasterDescentFold
import Workspace.Master.StrongAggregateAlign

/-! # Correctness and progress of the flattened kernel descent
The covering equations are obtained from the computed action and orbits.
The short-coset hull is harmless because the complete answer is itself
an isomorphism coset. Multiple kernel orbits make every call smaller.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

 theorem masterWinOrbits_union {n : ℕ} {gs : RawGens} {D : List ℕ}
    (hgs : RawGens.WF n gs) (hlt : ∀ u ∈ D, u < n)
    (hinv : IsInvariant (decGroup n gs) (winSet n D)) :
    (⋃ U ∈ (winOrbits (gs, D)).map (winSet n), U) = winSet n D := by
  ext u
  constructor
  · intro hu
    obtain ⟨U, hU, hu⟩ := Set.mem_iUnion₂.mp hu
    obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hU
    exact winOrbits_subset hgs hlt ((rawIsInvariant_eq_true_iff hgs hlt).mpr hinv) hV u.val hu
  · intro hu
    obtain ⟨V, hV, huV⟩ := List.mem_flatten.mp (winOrbits_cover hgs hlt hu)
    exact Set.mem_iUnion₂.mpr ⟨winSet n V, List.mem_map_of_mem hV, huV⟩

/-- Each listed orbit of a group is invariant under the group. -/
 theorem winOrbits_isInvariant {n : ℕ} {gs : RawGens} {D : List ℕ}
    (hgs : RawGens.WF n gs) (hlt : ∀ u ∈ D, u < n) {O : List ℕ} (hO : O ∈ winOrbits (gs, D)) :
    IsInvariant (decGroup n gs) (winSet n O) := by
  obtain ⟨i, hi, rfl⟩ := winOrbits_mem hO
  rw [winSet_rawOrbit hgs ⟨i, hlt i hi⟩]
  exact isInvariant_orbit _ _

section Action
variable {n m c : ℕ} {p : MasterDescInput}
    {ϕ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) ϕ)
    (hg : masterDescFuel c p = List.range (masterDescWidth p))
    (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))

include hp hinv in
 theorem masterDescKernel_invariant :
    IsInvariant (decGroup n (topKernel (masterDescAction p))) (winSet n p.1.1) := by
  rw [masterDescKernel_spec hp]
  exact (isInvariant_iff_mem _ _).mpr (fun σ hσ u => hinv.mem_iff (kerSubgroup_le ϕ hσ) u)

include hp hg hlt hinv in
 theorem masterDescStrongTree_run : (masterDescStrongTree n c p).run = (decWinSI n p.1).answer := by
  rw [masterDescStrongTree, run_strongDescent, ← masterDescLists_cover hp hg]
  change wIso (⋃ U ∈ (winOrbits (topKernel (masterDescAction p), p.1.1)).map (winSet n), U)
    (decWinSI n p.1).K _ _ = _
  rw [masterWinOrbits_union (wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1)
    hlt (masterDescKernel_invariant hp hinv)]
  rfl

include hp hg hlt hinv in
 theorem masterDescStrongTree_hull : cosetHull (masterDescStrongTree n c p).run =
    (masterDescStrongTree n c p).run := by
  rw [masterDescStrongTree_run hp hg hlt hinv]
  rcases Set.eq_empty_or_nonempty (decWinSI n p.1).answer with he | ⟨τ, hτ⟩
  · rw [he, cosetHull_empty]
  · simp only [SIInstance.answer, decWinSI, decCoset_some] at hτ ⊢
    have he := wIso_eq_smul_wAut hinv (decPerm n p.1.2.2.1) hτ
    change wIso (winSet n p.1.1) (decPerm n p.1.2.2.1 • (decGroup n p.1.2.1 : Set _))
      (decStrN n p.1.2.2.2.1) (decStrN n p.1.2.2.2.2) = _ at he
    change cosetHull (wIso _ _ _ _) = _
    rw [he]
    exact cosetHull_smul_subgroup τ (wAutSubgroup _ _ hinv _)

include hp hlt hinv in
 theorem masterDescStrongTree_progress (hnd : p.1.1.Nodup)
    (h2 : 1 < (winOrbits (topKernel (masterDescAction p), p.1.1)).length) :
    ∀ J ∈ (masterDescStrongTree n c p).calls, J.windowSize < p.1.1.length := by
  intro J hJ
  have hD := (mem_calls_strongDescent _ _ _ _ _ hJ).1
  obtain ⟨D, hD, he⟩ := List.mem_map.mp hD
  change D ∈ winOrbits (topKernel (masterDescAction p), p.1.1) at hD
  have hw := wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1
  have hi := (rawIsInvariant_eq_true_iff hw hlt).mpr (masterDescKernel_invariant hp hinv)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hD
  change J.Δ.ncard < _
  rw [← he, ncard_winSet _ (winOrbits_nodup (List.getElem_mem hj))
    (winOrbits_lt hw hlt hi (List.getElem_mem hj))]
  exact winOrbits_length_lt hw hnd hlt hi hj h2

include hp hlt in
/-- Every call of the kernel descent is a coset instance (Sec. 15; the calls of the strong
descent of Sec. 13 are coset instances, `isCosetInstance_calls_strongDescent`). -/
 theorem masterDescStrongTree_coset :
    ∀ J ∈ (masterDescStrongTree n c p).calls,
      IsCosetInstance (⊤ : Subgroup (Perm (Fin n))) J := by
  intro J hJ
  have hw := wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1
  refine isCosetInstance_calls_strongDescent le_top _ _ _ _ ?_
    (fun _ _ => Subgroup.mem_top _) hJ
  intro Δ hΔ
  obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hΔ
  exact winOrbits_isInvariant hw hlt hO

end Action

 theorem masterDescStrongTree_loop {n c : ℕ} {p : MasterDescInput}
    (hx : p.1.2.2.2.1.length = n)
    (hw : 0 < (aggnrWindows (masterDescLists c p)).length)
    (hh : cosetHull (masterDescStrongTree n c p).run = (masterDescStrongTree n c p).run) :
    LoopMatch (aggnrRound n (fun _ => none)) (aggnrDecode n) (decCoset n)
      (masterDescLists c p, none) (masterDescFoldWidth (masterDescLists c p)) 0
      (aggnrInit (masterDescLists c p, none)) (masterDescStrongTree n c p) := by
  have h := aggrPhaseMatch_value (aggnrPhase_descent (P := masterDescLists c p) (fun _ => none) hx hw)
  apply loopMatch_of_phaseMatch h _ le_rfl
  intro B j s hs
  constructor
  · change aggnrChild ((masterDescLists c p, none), j, s) = none
    simp only [aggnrChild, Option.elim_none, hs.1.1, lt_self_iff_false, false_and, if_false]
  · change decCoset n s.2.2.2 = B
    rw [hs.1.2.1, hs.2]
    exact hh

end Algo
