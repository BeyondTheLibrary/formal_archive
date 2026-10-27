import Workspace.Algo.SplitBipGraphEarlyDecode

/-! Read the first two exits directly from the common graph fields.
The stored orders give the numbering domains. The existing graph invariant
supplies the exact point colors and the nonzero matrix-entry test.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BipBlockInputs Ω)) (r : RawSbipGraph)
    (name : X.obj.1.1.Vtx → ℕ) (h : SbipGraphColorNames X.obj.1.1 r name)
    (hp : sbipGraphPointName X name '' Set.univ = {a | a ∈ r.1.1})
    (hb : sbipGraphBlockName X name '' Set.univ = {a | a ∈ r.1.2.1})

include h hp in
theorem sbipGraphEarly_point_equiv_exists (hl : r.1.1.Nodup) :
    ∃ e₁ : ↥X.obj.1.1.V₁ ≃ Fin r.1.1.length,
      ∀ x,r.1.1[(e₁ x).val] = sbipGraphPointName X name x := by
  refine splitNameEquiv_exists _ ?_ _ hl ?_
  · intro x y he
    have hh := congrArg (fun A : X.obj.1.1.Vtx => A.val) (h.injective he)
    exact Subtype.ext (Set.singleton_injective hh)
  · intro a
    rw [← show a ∈ sbipGraphPointName X name '' Set.univ ↔ a ∈ r.1.1 from by rw [hp]; rfl]
    simp

include h hb in
theorem sbipGraphEarly_block_equiv_exists (hr : r.1.2.1.Nodup) :
    ∃ e₂ : ↥X.obj.1.1.blocks ≃ Fin r.1.2.1.length,
      ∀ B,r.1.2.1[(e₂ B).val] = sbipGraphBlockName X name B := by
  refine splitNameEquiv_exists _ ?_ _ hr ?_
  · intro B C he
    exact Subtype.ext (congrArg (fun A : X.obj.1.1.Vtx => A.val) (h.injective he))
  · intro a
    rw [← show a ∈ sbipGraphBlockName X name '' Set.univ ↔ a ∈ r.1.2.1 from by rw [hb]; rfl]
    simp

variable (e₁ : ↥X.obj.1.1.V₁ ≃ Fin r.1.1.length)
    (e₂ : ↥X.obj.1.1.blocks ≃ Fin r.1.2.1.length)
    (he₁ : ∀ x,r.1.1[(e₁ x).val] = sbipGraphPointName X name x)
    (he₂ : ∀ B,r.1.2.1[(e₂ B).val] = sbipGraphBlockName X name B)

include e₁ in
theorem sbipGraphEarly_first_size : r.1.1.length = BipBlockInputs.n₁ X := by
  simpa only [Nat.card_fin,Nat.card_coe_set_eq] using (Nat.card_congr e₁).symm

include e₂ in
theorem sbipGraphEarly_block_size : r.1.2.1.length = BipBlockInputs.numBlocks X := by
  simpa only [Nat.card_fin,Nat.card_coe_set_eq,VColBipBlk.numBlocks] using (Nat.card_congr e₂).symm

include e₁ in
theorem sbipGraphSmall1_iff (c : ℕ) : sbipGraphSmall1 c r = true ↔ IsSmallPart₁ c X := by
  simp only [sbipGraphSmall1,decide_eq_true_eq,sbipGraphEarly_first_size X r e₁,IsSmallPart₁]

include e₁ e₂ in
theorem sbipGraphSmall2_iff (c : ℕ) : sbipGraphSmall2 c r = true ↔ IsSmallPart₂ c X := by
  simp only [sbipGraphSmall2,decide_eq_true_eq,sbipGraphEarly_first_size X r e₁,
    sbipGraphEarly_block_size X r e₂,IsSmallPart₂]

include h he₁ in
theorem sbipGraphEarly2_color (x : ↥X.obj.1.1.V₁) :
    (sbipGraphEarly2Input r).2.getD (e₁ x) 0 = X.obj.1.1.f x.val := by
  have hm : sbipGraphPointName X name x ∈ r.1.1 := he₁ x ▸ List.getElem_mem (e₁ x).isLt
  have hh := h.vertex ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩
  change (if decide (sbipGraphPointName X name x ∈ r.1.1) then _ else _) = _ at hh
  rw [if_pos (by simpa using hm),VColBipBlk.initVtxColor,if_pos ⟨x.val,x.property,rfl⟩] at hh
  have hcol : labAt r.2.1 (sbipGraphPointName X name x) = X.obj.1.1.f x.val := by
    simpa only [Nat.pair_eq_pair,true_and,Set.image_singleton,csSup_singleton] using hh
  change labAt (sbipGraphFirstColors r) (e₁ x) = _
  rw [sbipGraphFirstColors_get,he₁]
  exact hcol

include h he₁ he₂ in
theorem sbipGraphEarly2_edge (hl : r.1.1.Nodup) (hr : r.1.2.1.Nodup)
    (x : ↥X.obj.1.1.V₁) (B : ↥X.obj.1.1.blocks) :
    sbipMatrixEntry (r.1,((e₁ x).val,(e₂ B).val)) ≠ 0 ↔ (x.val,B.val) ∈ X.obj.1.1.E := by
  have hh := h.edge ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ ⟨B.val,Or.inr B.property⟩
  have hm := sbipGraphEdge_get r hl hr (e₁ x) (e₂ B)
  rw [he₁,he₂] at hm
  change sbipGraphEdge (r,(sbipGraphPointName X name x,sbipGraphBlockName X name B)) =
    X.obj.1.1.initEdge {x.val} B.val at hh
  rw [hm] at hh
  have hedge : (∃ y,X.obj.1.1.part₁ y ∧ ({x.val} : Set ↥X.car) = {y} ∧
      (y,B.val) ∈ X.obj.1.1.E) ↔ (x.val,B.val) ∈ X.obj.1.1.E := by
    constructor
    · rintro ⟨y,_,hy,he⟩
      rwa [← Set.singleton_injective hy] at he
    · intro he
      exact ⟨x.val,x.property,rfl,he⟩
  simp only [VColBipBlk.initEdge,hedge] at hh
  by_cases hz : sbipMatrixEntry (r.1,((e₁ x).val,(e₂ B).val)) = 0 <;>
    by_cases he : (x.val,B.val) ∈ X.obj.1.1.E <;> simp_all

end
end Algo
