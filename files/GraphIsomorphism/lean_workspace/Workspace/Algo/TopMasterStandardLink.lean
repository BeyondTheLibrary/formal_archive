import Workspace.Algo.TopMasterHintLink

/-! # Standard-block hints carry the same giant action
Equation (54) makes the point labels equivariant. Using a point in each
block shows that the block labeling intertwines the exact homomorphism
stored by the dominant-orbit constructor, not merely its image group.
-/
namespace Algo
open Babai Equiv MulAction
open scoped Classical

 theorem masterHintBlockLink_standard {Ω : Type*} [Fintype Ω]
    {G : Subgroup (Perm Ω)} {m : ℕ} (φ : G →* Perm (Fin m))
    (hg : IsGiantRep φ) (hm : VeryLargeK m (maxOrbitLength G)) (x : Ω) :
    Nonempty (MasterHintBlockLink (t := tPoint φ x)
      (theorem_10_5_1_e_isSystem φ hg hm x).permutes φ) := by
  obtain ⟨e, hlab, _⟩ := theorem_10_5_1_e_johnson φ hg hm x
  refine ⟨⟨e, ?_⟩⟩
  intro g
  apply Equiv.ext
  intro T
  apply Subtype.ext
  apply Finset.ext
  intro a
  let B := e.symm T
  obtain ⟨y, hy⟩ := (theorem_10_5_1_e_isSystem φ hg hm x).nonempty B.val B.property
  have hyimg : (g : Perm Ω) y ∈
      ((blockHom G (standardBlocks φ (orbit G x))
        (theorem_10_5_1_e_isSystem φ hg hm x).permutes g B).val) := by
    rw [blockHom_apply_coe]
    exact ⟨y, hy, rfl⟩
  have hL := hlab _ _ hyimg a
  have hR : ∀ z : Fin m, z ∈ T.val ↔ z ∈ Tpoint φ y := by
    intro z
    rw [← e.apply_symm_apply T]
    exact hlab B y hy z
  change a ∈ (e (blockHom G (standardBlocks φ (orbit G x))
    (theorem_10_5_1_e_isSystem φ hg hm x).permutes g B)).val ↔ a ∈ (tAction (tPoint φ x) (φ g) T).val
  rw [hL, tAction_apply_coe]
  have h54 : Tpoint φ ((g : Perm Ω) y) = (φ g) '' Tpoint φ y :=
    theorem_10_5_1_c_eq54 φ hg hm y g
  rw [h54]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, (hR z).mpr hz, rfl⟩
  · intro ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨z, (hR z).mp hz, rfl⟩

 theorem masterHintLinked_dominant {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {D : AlignDominant Ω} (c : AlignDominantOrbit D) (x y : Ω → A) :
    MasterHintLinked (c.johnsonCaseData x y) :=
  masterHintBlockLink_standard c.phi c.isGiantRep_phi c.veryLargeK_phi c.basePoint

end Algo
