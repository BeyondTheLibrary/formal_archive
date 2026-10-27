import Workspace.Algo.TopMasterDescentWindowEnum

/-! # The computed ambient descent is the lifted window line 2
All image tests use the computed representatives, and all orbit chains
use the computed windows. The only string convention is the paper's
extension by the source outside the parent window.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

 theorem masterPreimage_rangeRestrict {Ω H : Type*} [Group H]
    {G : Subgroup (Perm Ω)} (φ : G →* H) (a : φ.range) :
    preimageSet φ.rangeRestrict a = preimageSet φ a.val := by
  ext g
  constructor
  · rintro ⟨hg, he⟩
    exact ⟨hg, congrArg Subtype.val he⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, Subtype.ext he⟩

section Window
variable {n m c : ℕ} {p : MasterDescInput}
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m))
    (hp : RawAction.WF n m (masterDescAction p) (φ.comp (restrictOnto hinv)))
    (hg : masterDescFuel c p = List.range (masterDescWidth p))
    (hid : decPerm n p.1.2.2.1 = 1) (hlt : ∀ u ∈ p.1.1, u < n)

 theorem masterDescWindowOrbit_image :
    (masterDescWindowLine2Enum hinv φ hp hg hid hlt).orbits.windows.map (Subtype.val '' ·) =
      (aggnrWindows (masterDescLists c p)).map (winSet n) :=
  masterOrbitWindows_image
    (W := (p.1.1, topKernel (masterDescAction p), p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2))
    (wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1) hlt (masterDescKernel_invariant hp hinv)

 theorem masterDescWindowUp_tree (y : winSet n p.1.1 → ℕ)
    (hy : decStrN n p.1.2.2.2.2 = extendStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1) y) :
    let E := masterDescWindowLine2Enum hinv φ hp hg hid hlt
    unionAnswers (E.elements.map (fun a =>
      Babai.cosetChain (decStrN n p.1.2.2.2.1) (extendStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1) y)
        (E.orbits.windows.map (Subtype.val '' ·))
        (windowPreim (decGroup n p.1.2.1) (winSet n p.1.1) hinv (preimageSet φ.rangeRestrict a)))) =
      masterDescStrongTree n c p := by
  dsimp only
  rw [masterDescWindowOrbit_image]
  let R := masterDescCosetEnum hp hg hid
  have hP (g : decGroup n p.1.2.1) :
      windowPreim (decGroup n p.1.2.1) (winSet n p.1.1) hinv
        (preimageSet φ.rangeRestrict (φ.rangeRestrict (restrictOnto hinv g))) =
        g.val • (kerSubgroup (φ.comp (restrictOnto hinv)) : Set (Perm (Fin n))) := by
    rw [masterPreimage_rangeRestrict, masterWindowPreimage_eq]
    exact masterPreimage_image (φ.comp (restrictOnto hinv)) g
  unfold masterDescStrongTree
  dsimp only
  rw [show (masterDescLists c p).2.1 = topKernel (masterDescAction p) from rfl,
    masterDescKernel_spec hp, hy, strongDescent]
  change unionAnswers ((((masterCosetTypedReps (φ.comp (restrictOnto hinv)) R).map
    (restrictOnto hinv)).map φ.rangeRestrict).map _) = _
  rw [List.map_map, List.map_map,
    ← show (masterCosetTypedReps (φ.comp (restrictOnto hinv)) R).map Subtype.val =
      aggnrReps n (masterDescLists c p) from masterCosetTypedReps_val _ R, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg'
  dsimp only [Function.comp_apply]
  rw [hP]
  rfl

 theorem masterDescWindow_trace (y : winSet n p.1.1 → ℕ)
    (hy : decStrN n p.1.2.2.2.2 = extendStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1) y) :
    let T := liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
      (cosetLine2ReductionWith φ.rangeRestrict (restrictStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1)) y
        (masterDescWindowLine2Enum hinv φ hp hg hid hlt))
    T.calls = (masterDescStrongTree n c p).calls ∧ T.run = (masterDescStrongTree n c p).run := by
  have h := masterWindowLine2_trace hinv (decStrN n p.1.2.2.2.1) φ.rangeRestrict y
    (masterDescWindowLine2Enum hinv φ hp hg hid hlt)
  dsimp only at h ⊢
  rw [masterDescWindowUp_tree hinv φ hp hg hid hlt y hy] at h
  exact h
end Window
end Algo
