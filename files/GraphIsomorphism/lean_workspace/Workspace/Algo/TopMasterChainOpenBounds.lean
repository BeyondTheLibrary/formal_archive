import Workspace.Algo.TopMasterChainOpen
import Workspace.Algo.AggNodeCheckedWindow

/-! # Size and progress of direct master calls
The input's strings have the normalized alphabet bound. The chain keeps
that bound, normalizes every candidate, and strictly shrinks the window.
These facts hold for every raw fold state, including malformed candidates.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

 theorem masterChainRoute_multiple {n B C₀ : ℕ} {W : RawWinSI}
    (hw : RawGens.WF n W.2.1) (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    (hr : masterReduceRoute B C₀ W = 2) (hC : 1 < C₀) :
    1 < (winOrbits (W.2.1, W.1)).length := by
  by_contra h
  have hle : (masterOrbitWindows n W).length ≤ 1 := by
    simpa only [masterOrbitWindows, List.length_map] using (Nat.le_of_not_gt h)
  have huniq : ∀ U ∈ masterOrbitWindows n W, ∀ V ∈ masterOrbitWindows n W, U = V := by
    intro U hU V hV
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hU
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hV
    have hij : i = j := by omega
    subst j
    rfl
  have hp := masterOrbitWindows_perm hw hlt hinv
  obtain ⟨u, hu⟩ := masterChainRoute_nonempty hw hnd hlt hinv hr hC
  apply masterChainRoute_intransitive hw hnd hlt hinv hr
  refine ⟨⟨u, hu⟩, Set.eq_univ_of_forall fun v => ?_⟩
  have he := huniq _ (hp.mem_iff.mpr (orbit_mem_orbitList _ (⟨u, hu⟩ : winSet n W.1)))
    _ (hp.mem_iff.mpr (orbit_mem_orbitList _ v))
  change v ∈ orbit (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) (⟨u, hu⟩ : winSet n W.1)
  rw [he]
  exact mem_orbit_self v

 theorem masterStrWF_iff {n k : ℕ} {x : RawStr} (hx : x.length = n) :
    RawStr.WF n k x ↔ ∀ i : Fin n, decStrN n x i < k := by
  constructor
  · intro h i
    change x.getD i.val 0 < k
    rw [List.getD_eq_getElem _ _ (hx ▸ i.isLt)]
    exact h.2 _ (List.getElem_mem _)
  · intro h
    refine ⟨hx, ?_⟩
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hh := h ⟨i, hx ▸ hi⟩
    simpa only [decStrN, List.getD_eq_getElem _ _ hi] using hh

 theorem masterChainPrepared_strings {n k : ℕ} {W : RawWinSI}
    (hx : RawStr.WF n k W.2.2.2.1) (hy : RawStr.WF n k W.2.2.2.2)
    (hnd : W.1.Nodup) (hlt : ∀ u ∈ W.1, u < n) :
    RawStr.WF n k (masterChainPrepared W).2.2.2.1 ∧
      RawStr.WF n k (masterChainPrepared W).2.2.2.2 := by
  refine ⟨hx, (masterStrWF_iff (by simpa only [masterChainPrepared, length_topwExtendStr] using hx.1)).mpr ?_⟩
  intro i
  rw [masterChainPrepared_target hx.1 hnd hlt]
  have hxx := (masterStrWF_iff hx.1).mp hx
  have hyy := (masterStrWF_iff hy.1).mp hy
  unfold extendStr
  split_ifs with hi
  · change decStrN n (top4aTarget (W.2.2.2.1, W.2.2.1, W.2.2.2.2)) i < k
    rw [top4aTarget_spec hx.1]
    exact hyy _
  · exact hxx i

 theorem masterChainOpenChild_wf {n : ℕ} {W : RawWinSI} {j : ℕ} {s : RawCoset}
    {J : RawMasterSI} (hW : AggnCheckedWindowWF n W)
    (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (hc : masterChainOpenChild (W, j, s) = some J) :
    AggnCheckedWindowWF n J.1 ∧ J.2 = none := by
  obtain ⟨c, _, hj, rfl⟩ := masterChainOpenChild_some hc
  have hx := hW.2.2.2.2.2.1
  have hy := hW.2.2.2.2.2.2
  have hmem : (winOrbits (W.2.1, W.1)).getD j [] ∈ winOrbits (W.2.1, W.1) := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hs := masterChainPrepared_strings hx hy hW.1 hW.2.1
  exact ⟨⟨winOrbits_nodup hmem, winOrbits_lt hW.2.2.1 hW.2.1 hinv hmem,
    wf_tidyGens hx.1 _, length_tidyGens hx.1 _, wf_normPerm hx.1 _, hs.1, hs.2⟩, rfl⟩

 theorem masterChainOpenChild_size {n : ℕ} {W : RawWinSI} {j : ℕ} {s : RawCoset}
    {J : RawMasterSI} (hW : AggnCheckedWindowWF n W)
    (hinv : rawIsInvariant (W.2.1, W.1) = true)
    (hc : masterChainOpenChild (W, j, s) = some J) :
    Enc.size J ≤ 2 * aggnCheckedWindowBound n + 4 := by
  obtain ⟨hJ, hnone⟩ := masterChainOpenChild_wf hW hinv hc
  have hs := size_pair_le' J
  have hw := aggnCheckedWindow_size hJ
  have hn : Enc.size J.2 = 2 := by rw [hnone, size_none]
  omega

 theorem masterChainOpenInit_size (W : RawWinSI) :
    Enc.size (masterChainOpenInit W) ≤ chainBound W.2.2.2.1.length := by
  change Enc.size (top2NormC W.2.2.2.1 (some (W.2.1, rawOne W.2.2.2.1))) ≤ _
  exact size_top2NormC_le rfl le_rfl (some (W.2.1, rawOne W.2.2.2.1))

 theorem masterChainOpenCombine_size (W : RawWinSI) (j : ℕ) (s a : RawCoset) :
    Enc.size (masterChainOpenCombine (W, j, s, a)) ≤ chainBound W.2.2.2.1.length := by
  change Enc.size (top2NormC W.2.2.2.1 a) ≤ _
  exact size_top2NormC_le rfl le_rfl a

 theorem masterChainOpenFinish_size (W : RawWinSI) (s : RawCoset) :
    Enc.size (masterChainOpenFinish (W, s)) ≤ chainBound W.2.2.2.1.length := by
  unfold masterChainOpenFinish
  exact size_top3Shift_le rfl le_rfl _ _

end Algo
