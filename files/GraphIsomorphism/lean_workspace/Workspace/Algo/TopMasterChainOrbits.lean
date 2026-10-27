import Workspace.Algo.TopMasterChainTransport

/-! # The computed orbit order is live mathematical data -/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

 theorem masterRestrictedOrbit {Ω : Type*} [Fintype Ω] {G : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant G Δ) (u : Δ) :
    Subtype.val ⁻¹' orbit G u.val = orbit (restrictTo G Δ hinv) u := by
  ext v
  constructor
  · intro hv
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hv
    apply mem_orbit_iff.mpr
    refine ⟨restrictOnto hinv g, Subtype.ext ?_⟩
    exact hg
  · intro hv
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hv
    obtain ⟨k, rfl⟩ := restrictOnto_surjective hinv g
    exact mem_orbit_iff.mpr ⟨k, congrArg Subtype.val hg⟩

section Orbits
variable {n : ℕ} {W : RawWinSI} (hw : RawGens.WF n W.2.1)
    (hlt : ∀ u ∈ W.1, u < n)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))

def masterOrbitWindows (n : ℕ) (W : RawWinSI) : List (Set (winSet n W.1)) :=
  (winOrbits (W.2.1, W.1)).map (fun D => Subtype.val ⁻¹' winSet n D)

include hw hlt hinv in
theorem masterOrbitWindows_mem {D : Set (winSet n W.1)} (hD : D ∈ masterOrbitWindows n W) :
    D ∈ orbitList (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) := by
  obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hD
  obtain ⟨u, hu, rfl⟩ := winOrbits_mem hV
  rw [winSet_rawOrbit hw ⟨u, hlt u hu⟩,
    masterRestrictedOrbit hinv (⟨⟨u, hlt u hu⟩, hu⟩ : winSet n W.1)]
  exact orbit_mem_orbitList _ _

include hw hlt in
theorem masterOrbitWindows_nodup : (masterOrbitWindows n W).Nodup := by
  rw [masterOrbitWindows, List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  obtain ⟨u, hu, huV⟩ := winOrbits_mem (List.getElem_mem hi)
  have huin : u ∈ (winOrbits (W.2.1, W.1))[i] := by
    rw [huV]
    exact mem_rawOrbit_self _ _
  have huout : u ∈ (winOrbits (W.2.1, W.1))[j] := by
    have hm : (⟨⟨u, hlt u hu⟩, hu⟩ : winSet n W.1) ∈
        Subtype.val ⁻¹' winSet n ((winOrbits (W.2.1, W.1))[i]) := huin
    have hm' := he ▸ hm
    exact hm'
  exact (List.pairwise_iff_getElem.mp (winOrbits_pairwise hw hlt) i j hi hj hij) u huin huout

include hw hlt hinv in
theorem masterOrbitWindows_perm : (masterOrbitWindows n W).Perm
    (orbitList (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv)) := by
  have hn := masterOrbitWindows_nodup hw hlt
  have ho : (orbitList (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv)).Nodup := by
    unfold orbitList
    exact List.Nodup.map orbitRel.Quotient.orbit_injective (Finset.nodup_toList _)
  have hf := fun D hD => masterOrbitWindows_mem hw hlt hinv (D := D) hD
  have hb : orbitList (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) ⊆
      masterOrbitWindows n W := by
    intro D hD
    obtain ⟨u, rfl⟩ := mem_orbitList hD
    have hcover := winOrbits_cover hw hlt u.property
    obtain ⟨V, hV, huV⟩ := List.mem_flatten.mp hcover
    have hm : Subtype.val ⁻¹' winSet n V ∈ masterOrbitWindows n W := List.mem_map_of_mem hV
    obtain ⟨v, hv⟩ := mem_orbitList (hf _ hm)
    have hmem : u ∈ orbit (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) v := hv ▸ huV
    rw [hv, ← (orbit_eq_iff (a := u) (b := v)).mpr hmem] at hm
    exact hm
  exact (hn.subperm hf).antisymm (ho.subperm hb)

noncomputable def masterOrbitEnum : OrbitEnum (restrictTo (decGroup n W.2.1) (winSet n W.1) hinv) :=
  ⟨masterOrbitWindows n W, masterOrbitWindows_perm hw hlt hinv⟩

include hw hlt hinv in
theorem masterOrbitWindows_image :
    (masterOrbitWindows n W).map (Subtype.val '' ·) = (winOrbits (W.2.1, W.1)).map (winSet n) := by
  rw [masterOrbitWindows, List.map_map]
  apply List.map_congr_left
  intro V hV
  have hraw := (rawIsInvariant_eq_true_iff hw hlt).mpr hinv
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hu
    exact ⟨⟨u, winOrbits_subset hw hlt hraw hV u.val hu⟩, hu, rfl⟩
end Orbits
end Algo
