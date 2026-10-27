import Workspace.Algo.TopMasterWindowKernel

/-! # Computed line-2 choices on an ambient window
Project the actual ambient coset representatives to the window and keep
the computed orbit order. The ambient action is the retained window
action composed with restriction, so no new representative is chosen.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section Window
variable {n m c : ℕ} {p : MasterDescInput}
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m))
    (hp : RawAction.WF n m (masterDescAction p) (φ.comp (restrictOnto hinv)))
    (hg : masterDescFuel c p = List.range (masterDescWidth p))
    (hid : decPerm n p.1.2.2.1 = 1) (hlt : ∀ u ∈ p.1.1, u < n)

 include hp in
 theorem masterDescWindowKernel :
    restrictTo (decGroup n (topKernel (masterDescAction p))) (winSet n p.1.1)
      (masterDescKernel_invariant hp hinv) = kerSubgroup φ := by
  have h := masterWindowKernel_restrict hinv φ
  simpa only [masterDescKernel_spec hp] using h

 noncomputable def masterDescWindowOrbitEnum : OrbitEnum (kerSubgroup φ) where
  windows := (winOrbits (topKernel (masterDescAction p), p.1.1)).map
    (fun D => Subtype.val ⁻¹' winSet n D)
  spec := by
    have h := masterOrbitWindows_perm
      (W := (p.1.1, topKernel (masterDescAction p), p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2))
      (wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1) hlt
      (masterDescKernel_invariant hp hinv)
    change ((winOrbits (topKernel (masterDescAction p), p.1.1)).map
      (fun D => Subtype.val ⁻¹' winSet n D)).Perm _ at h
    rw [masterDescWindowKernel hinv φ hp] at h
    exact h

 theorem masterDescWindowRange : (φ.comp (restrictOnto hinv)).range = φ.range := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨restrictOnto hinv g, rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨q, hq⟩ := restrictOnto_surjective hinv g
    exact ⟨q, congrArg φ hq⟩

 noncomputable def masterDescWindowReps :
    List (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv) :=
  (masterCosetTypedReps (φ.comp (restrictOnto hinv)) (masterDescCosetEnum hp hg hid)).map
    (restrictOnto hinv)

 theorem masterDescWindowImage_cover (a : φ.range) :
    a ∈ (masterDescWindowReps hinv φ hp hg hid).map φ.rangeRestrict := by
  have ha : a.val ∈ (φ.comp (restrictOnto hinv)).range :=
    (masterDescWindowRange hinv φ).symm ▸ a.property
  obtain ⟨g, hg', he⟩ := List.mem_map.mp
    (masterCosetImage_cover (φ.comp (restrictOnto hinv)) (masterDescCosetEnum hp hg hid) ⟨a, ha⟩)
  refine List.mem_map.mpr ⟨restrictOnto hinv g, List.mem_map_of_mem hg', ?_⟩
  have he' := congrArg (fun z : (φ.comp (restrictOnto hinv)).range => z.val) he
  exact Subtype.ext he'

 noncomputable def masterDescWindowLine2Enum : Line2Enum φ.rangeRestrict where
  elements := (masterDescWindowReps hinv φ hp hg hid).map φ.rangeRestrict
  cover := masterDescWindowImage_cover hinv φ hp hg hid
  length := by
    have h := (masterDescCosetEnum hp hg hid).length
    rw [masterKernel_index] at h
    have hc := congrArg (fun G : Subgroup (Perm (Fin m)) => Nat.card G) (masterDescWindowRange hinv φ)
    have h' := h.trans_eq hc
    simpa only [List.length_map, masterDescWindowReps, masterCosetTypedReps, List.length_attach,
      Nat.card_eq_fintype_card] using h'
  orbits := ⟨(masterDescWindowOrbitEnum hinv φ hp hlt).windows, by
    simpa only [kerSubgroup, MonoidHom.ker_rangeRestrict] using
      (masterDescWindowOrbitEnum hinv φ hp hlt).spec⟩
end Window
end Algo
