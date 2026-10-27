import Workspace.Algo.TopMasterLineTwoEnum

/-! # Flattening the actual line-2 image and orbit loops
Expanding each image lifting by its orbit chain gives the ordered union
of those chains. This is an equality of trees, before running any solver.
-/
namespace Algo
open Babai Equiv
open scoped Classical Pointwise

 theorem masterExpand_bind {Ω A α β : Type*} (R : SIReduction Ω A α)
    (f : α → SIReduction Ω A β) (C : SIInstance Ω A → SIReduction Ω A (Set (Perm Ω))) :
    (R.bind f).expand C = (R.expand C).bind (fun a => (f a).expand C) := by
  induction R with
  | done a => rfl
  | call I k ih =>
    simp only [SIReduction.bind, SIReduction.expand, SIReduction.bind_assoc]
    congr 1
    funext a
    exact ih a

 theorem masterUnion_sequence {Ω A : Type*} (L : List (SIReduction Ω A (Set (Perm Ω)))) :
    (SIReduction.sequence L).bind (fun S => .done (⋃ a ∈ S, a)) = unionAnswers L := by
  induction L with
  | nil => simp [SIReduction.sequence, SIReduction.bind, unionAnswers]
  | cons R L ih =>
    rw [SIReduction.sequence_cons, unionAnswers, SIReduction.bind_assoc, ← ih]
    congr 1
    funext a
    rw [SIReduction.bind_assoc, SIReduction.bind_assoc]
    congr 1
    funext S
    change SIReduction.done (⋃ b ∈ a :: S, b) = SIReduction.done (a ∪ ⋃ b ∈ S, b)
    congr 1
    ext g
    simp

section LineTwo
variable {Ω A H : Type*} [Fintype Ω] [DecidableEq Ω] {G : Subgroup (Perm Ω)} [Group H]
    (φ : G →* H) (x y : Ω → A) (D : List (Set Ω))

 theorem masterLiftAll_expand (S : List H) :
    (cosetLiftAll φ x y S).expand (fun I => Babai.cosetChain I.x I.y D I.K) =
      SIReduction.sequence (S.map (fun a => Babai.cosetChain x y D (preimageSet φ a))) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [cosetLiftAll, masterExpand_bind, cosetLift, SIReduction.expand,
      SIReduction.bind_done, List.map_cons, SIReduction.sequence_cons, ih]

 theorem masterLine2_flat [Fintype H] (E : Line2Enum φ) :
    cosetLine2ReductionWith φ x y E =
      unionAnswers (E.elements.map (fun a => Babai.cosetChain x y E.orbits.windows (preimageSet φ a))) := by
  unfold cosetLine2ReductionWith cosetLuksBruteForceWith
  rw [masterExpand_bind]
  change ((cosetLiftAll φ x y E.elements).expand (fun I => Babai.cosetChain I.x I.y E.orbits.windows I.K)).bind
    (fun S => .done (⋃ a ∈ S, a)) = _
  rw [masterLiftAll_expand]
  exact masterUnion_sequence _

 theorem masterPreimage_image (g : G) : preimageSet φ (φ g) = g.val • (kerSubgroup φ : Set (Perm Ω)) := by
  ext q
  constructor
  · rintro ⟨hq, he⟩
    refine ⟨g.val⁻¹ * q, mem_kerSubgroup.mpr ⟨G.mul_mem (G.inv_mem g.property) hq, ?_⟩, ?_⟩
    · change φ (g⁻¹ * ⟨q, hq⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    · change g.val * (g.val⁻¹ * q) = q
      group
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨hrG, hrφ⟩ := mem_kerSubgroup.mp hr
    refine ⟨G.mul_mem g.property hrG, ?_⟩
    change φ (g * ⟨r, hrG⟩) = φ g
    rw [map_mul, hrφ, mul_one]

 theorem masterLine2_strong [Fintype H] (E : Line2Enum φ) (L : List G)
    (he : E.elements = L.map φ) :
    cosetLine2ReductionWith φ x y E = strongDescent (kerSubgroup φ) x y
      (L.map Subtype.val) E.orbits.windows := by
  rw [masterLine2_flat, he, strongDescent, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g hg
  dsimp only [Function.comp_apply]
  rw [masterPreimage_image]

end LineTwo
end Algo
