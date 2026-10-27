import Workspace.Algo.SplitBipAbsolute

/-! # Reading first-part symmetricity through a bipartite graph

Only the colors on the first part matter here. The other points may have
different colors, as they do in the block-design input.
-/
namespace Algo
open Babai

section
variable {s : Type} [Fintype s] [DecidableEq s] (X : VColBipBlk s ℕ)
    (hf : ∀ x, X.part₁ x → ∀ y, X.part₁ y → X.f x = X.f y)
include hf

open scoped Classical in
theorem bipBlockSymmetricity_eq_sup :
    X.symmetricity₁ = (Finset.univ.filter fun T : Finset s =>
      (∀ x ∈ T, X.part₁ x) ∧
        ∀ x ∈ T, ∀ y ∈ T, ∀ B ∈ X.blocks, ((x,B) ∈ X.E ↔ (y,B) ∈ X.E)).sup
      Finset.card := by
  classical
  refine congrArg (fun u => Finset.sup u Finset.card) ?_
  ext T
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hp,hT⟩
    refine ⟨hp,fun x hx y hy B hB => ?_⟩
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    · exact ((X.isTwin_iff (hp x hx) (hp y hy) hxy).1 (hT x hx y hy hxy)).2 B hB
  · rintro ⟨hp,hT⟩
    refine ⟨hp,fun x hx y hy hxy => ?_⟩
    exact (X.isTwin_iff (hp x hx) (hp y hy) hxy).2
      ⟨hf x (hp x hx) y (hp y hy),fun B hB => hT x hx y hy B hB⟩

theorem bipBlockSymmetricity : X.toBip.symmetricity₁ = X.symmetricity₁ := by
  classical
  rw [BipGraph.symmetricity₁_eq_sup,bipBlockSymmetricity_eq_sup X hf]
  refine le_antisymm (Finset.sup_le fun T hT => ?_) (Finset.sup_le fun T hT => ?_)
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hT
    refine le_trans (le_of_eq (Finset.card_map (Function.Embedding.subtype _)).symm)
      (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro x hx
      simp only [Finset.mem_map,Function.Embedding.coe_subtype] at hx
      obtain ⟨z,_,rfl⟩ := hx
      exact z.property
    · rintro x hx y hy B hB
      simp only [Finset.mem_map,Function.Embedding.coe_subtype] at hx hy
      obtain ⟨z,hz,rfl⟩ := hx
      obtain ⟨w,hw,rfl⟩ := hy
      exact hT z hz w hw ⟨B,hB⟩
  · simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hT
    obtain ⟨hp,hpair⟩ := hT
    have hcard : T.card = (T.subtype (fun x => x ∈ X.V₁)).card := by
      rw [Finset.card_subtype]
      exact (congrArg Finset.card (Finset.filter_true_of_mem (fun x hx => hp x hx))).symm
    refine le_trans (le_of_eq hcard) (Finset.le_sup (f := Finset.card) ?_)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rintro x hx y hy B
    simp only [Finset.mem_subtype] at hx hy
    exact hpair _ hx _ hy (B : Set s) B.property

end
end Algo
