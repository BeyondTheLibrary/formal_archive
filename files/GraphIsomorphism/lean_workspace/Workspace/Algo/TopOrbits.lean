import Workspace.Algo.TopGenerators

/-!
# Sec. 12: the computed kernel windows

The Chain Rule uses the orbits of the kernel. The computed list may
have a different order from `Babai.orbitList`. Its windows are the same,
with no repetitions, so the call and window bounds do not change.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open MulAction

/-- Short generators of the kernel used in Corollary 12.0.6. -/
def topKernel (p : RawAction) : RawGens := tidyGens (p.1.1, actKerGens p)

/-- The windows of Corollary 12.0.6, in the computed orbit order. -/
def topKernelWindows (p : RawAction) : List (List ℕ) :=
  winOrbits (topKernel p, rawOne p.1.1)

theorem polyFun_topKernel : PolyFun topKernel :=
  (((polyFun_fst.comp polyFun_fst).pair polyFun_actKerGens).comp polyFun_tidyGens)

theorem polyFun_topKernelWindows : PolyFun topKernelWindows :=
  (polyFun_topKernel.pair
    ((polyFun_fst.comp polyFun_fst).comp polyFun_rawOne)).comp polyFun_winOrbits

theorem decGroup_topKernel {n m : ℕ} {dom gdom : List ℕ}
    {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
    {ϕ : genGroup gens →* Perm (Fin m)} (hd : dom.length = n) (hm : gdom.length = m)
    (hI : ImgsOf gens imgs ϕ) :
    decGroup n (topKernel ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))) =
      Babai.kerSubgroup ϕ := by
  rw [topKernel, decGroup_tidyGens hd, decGroup_actKerGens hd hm hI]
  rfl

theorem winSet_rawOrbit {n : ℕ} {gs : RawGens} (hgs : RawGens.WF n gs)
    (i : Fin n) : winSet n (rawOrbit (gs, i.val)) = orbit (decGroup n gs) i := by
  ext j
  exact (mem_rawOrbit_iff hgs i.isLt j.val).trans
    ⟨fun h => h.2, fun h => ⟨j.isLt, h⟩⟩

theorem orbit_mem_orbitList {Ω : Type*} [Fintype Ω]
    (N : Subgroup (Perm Ω)) (u : Ω) : orbit N u ∈ Babai.orbitList N := by
  classical
  have hc : u ∈ ⋃ w ∈ Babai.orbitList N, w := by rw [Babai.iUnion_orbitList]; trivial
  obtain ⟨w, hw, hu⟩ := Set.mem_iUnion₂.1 hc
  obtain ⟨v, rfl⟩ := Babai.mem_orbitList hw
  rwa [← (orbit_eq_iff (a := u) (b := v)).2 hu] at hw

theorem mem_decoded_winOrbits {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hgs : RawGens.WF n gs) (hd : dom.length = n) {w : List ℕ}
    (hw : w ∈ winOrbits (gs, rawOne dom)) :
    winSet n w ∈ Babai.orbitList (decGroup n gs) := by
  obtain ⟨i, hi, rfl⟩ := winOrbits_mem hw
  have hin : i < n := by simpa [rawOne, hd] using hi
  rw [winSet_rawOrbit hgs ⟨i, hin⟩]
  exact orbit_mem_orbitList _ _

theorem nodup_decoded_winOrbits {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hgs : RawGens.WF n gs) (hd : dom.length = n) :
    ((winOrbits (gs, rawOne dom)).map (winSet n)).Nodup := by
  have hlt : ∀ j ∈ rawOne dom, j < n := by simpa [rawOne, hd]
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.pairwise_iff_getElem.2
  intro i j hi hj hij he
  have hwi := List.getElem_mem hi
  obtain ⟨a, ha, heq⟩ := winOrbits_mem hwi
  have han := hlt a ha
  have hamem : a ∈ (winOrbits (gs, rawOne dom))[i] := by
    rw [heq]
    exact (mem_rawOrbit_iff hgs han a).2 ⟨han, mem_orbit_self _⟩
  have hother : a ∈ (winOrbits (gs, rawOne dom))[j] :=
    show (⟨a, han⟩ : Fin n) ∈ winSet n _ from he ▸ hamem
  exact (List.pairwise_iff_getElem.1 (winOrbits_pairwise hgs hlt) i j hi hj hij) a hamem hother

/-- The raw orbit list has at most one entry for each mathematical orbit. -/
theorem length_winOrbits_le_orbitList {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hgs : RawGens.WF n gs) (hd : dom.length = n) :
    (winOrbits (gs, rawOne dom)).length ≤ (Babai.orbitList (decGroup n gs)).length := by
  have hs : ((winOrbits (gs, rawOne dom)).map (winSet n)) ⊆
      Babai.orbitList (decGroup n gs) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact mem_decoded_winOrbits hgs hd hv
  simpa using (List.subperm_of_subset (nodup_decoded_winOrbits hgs hd) hs).length_le

/-- The computed orbit windows cover the entire source domain. -/
theorem iUnion_decoded_winOrbits {n : ℕ} {gs : RawGens} {dom : List ℕ}
    (hgs : RawGens.WF n gs) (hd : dom.length = n) :
    (⋃ w ∈ (winOrbits (gs, rawOne dom)).map (winSet n), w) = Set.univ := by
  have hlt : ∀ j ∈ rawOne dom, j < n := by simpa [rawOne, hd]
  have he : winSet n (rawOne dom) = Set.univ := by ext j; simp [winSet, rawOne, hd]
  have hinv : rawIsInvariant (gs, rawOne dom) = true := by
    rw [rawIsInvariant_eq_true_iff hgs hlt]
    rw [show {j : Fin n | j.val ∈ rawOne dom} = Set.univ from he]
    exact Babai.isInvariant_univ _
  rw [iUnion_winOrbits hgs hlt hinv, he]

section Kernel

variable {n m : ℕ} {dom gdom : List ℕ}
  {gens : List (Perm (Fin n))} {imgs : List (Perm (Fin m))}
  {ϕ : genGroup gens →* Perm (Fin m)}
  (hd : dom.length = n) (hm : gdom.length = m) (hI : ImgsOf gens imgs ϕ)

include hd hm hI

/-- Corollary 12.0.6: the computed Chain Rule has at most `k` windows. -/
theorem length_topKernelWindows_le :
    (topKernelWindows ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))).length ≤
      Babai.orbCount ϕ := by
  change _ ≤ Nat.card (orbitRel.Quotient (Babai.kerSubgroup ϕ) (Fin n))
  rw [← Babai.length_orbitList, ← decGroup_topKernel hd hm hI]
  exact length_winOrbits_le_orbitList (wf_tidyGens hd _) hd

/-- Each computed window is an orbit of the kernel. This is the raw
counterpart of `Babai.calls_topAction2Reduction_window`. -/
theorem topKernelWindows_mem {w : List ℕ}
    (hw : w ∈ topKernelWindows ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m)))) :
    winSet n w ∈ Babai.orbitList (Babai.kerSubgroup ϕ) := by
  rw [← decGroup_topKernel hd hm hI]
  exact mem_decoded_winOrbits (wf_tidyGens hd _) hd hw

/-- Corollary 12.0.6: every computed window has size `n/k`. -/
theorem topKernelWindows_size {w : List ℕ}
    (hw : w ∈ topKernelWindows ((dom, gens.map (encPerm n)), (gdom, imgs.map (encPerm m))))
    (hG : Babai.IsTransitive (genGroup gens)) (hgiant : Babai.IsGiantRep ϕ)
    (hlarge : Babai.LargeK m (Nat.card (Fin n))) :
    (winSet n w).ncard * Babai.orbCount ϕ = n := by
  obtain ⟨u, hu⟩ := Babai.mem_orbitList (topKernelWindows_mem hd hm hI hw)
  rw [hu]
  simpa using (Babai.orbCount_spec hG ϕ hgiant hlarge).2.2 u

end Kernel

end Algo
