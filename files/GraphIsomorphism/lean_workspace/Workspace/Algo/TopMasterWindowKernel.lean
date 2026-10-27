import Workspace.Algo.TopMasterLineTwoWindow

/-! # The ambient and window kernels use the same lifting cosets
Composing the retained action with restriction computes the full preimage
of each image test. Its kernel is the preimage of the window kernel, so
restricting that ambient kernel recovers exactly the window kernel.
-/
namespace Algo
open Babai Equiv
open scoped Classical

section Window
variable {Ω H : Type*} [Group H] {K : Subgroup (Perm Ω)} {Δ : Set Ω}
    (hinv : IsInvariant K Δ) (φ : restrictTo K Δ hinv →* H)

 theorem masterWindowPreimage_eq (a : H) :
    windowPreim K Δ hinv (preimageSet φ a) = preimageSet (φ.comp (restrictOnto hinv)) a := by
  ext g
  constructor
  · rintro ⟨hg, hR, he⟩
    exact ⟨hg, he⟩
  · rintro ⟨hg, he⟩
    exact ⟨hg, ⟨⟨g, hg⟩, rfl⟩, he⟩

 theorem masterWindowKernel_eq :
    windowPreimSubgroup K Δ hinv (kerSubgroup φ) = kerSubgroup (φ.comp (restrictOnto hinv)) := by
  apply SetLike.coe_injective
  rw [coe_windowPreimSubgroup, ← preimageSet_one, masterWindowPreimage_eq, preimageSet_one]

 theorem masterWindowKernel_restrict :
    restrictTo (kerSubgroup (φ.comp (restrictOnto hinv))) Δ
      (fun g hg => hinv g (kerSubgroup_le (φ.comp (restrictOnto hinv)) hg)) = kerSubgroup φ := by
  have h := restrictTo_windowPreimSubgroup hinv (kerSubgroup_le φ)
  simpa only [masterWindowKernel_eq hinv φ] using h
end Window
end Algo
