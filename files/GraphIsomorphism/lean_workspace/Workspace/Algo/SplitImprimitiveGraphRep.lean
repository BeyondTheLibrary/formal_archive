import Workspace.Algo.SplitImprimitiveColumns

/-! # Section 9.6: the complete graph representation

The representation includes the column dictionary and every matrix entry.
It also records the zero colors and hint used by the paper's two graphs.
Injectivity of decoded columns ensures that list length counts new blocks.
-/
namespace Algo
open Babai RAM

section Representation
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : BlkImprimitiveObj s) (name₁ : ↥X.Pt₁ → ℕ) (name₂ : ↥X.blocks → ℕ)
    (r : RawUpccCase)

open scoped Classical in
structure ImpGraphRep (q : RawImpGraph) (Y : VColBipBlk ↥s ℕ) : Prop where
  left : q.1 = r.2.1
  part : Y.part₁ = X.part₁
  columns_nodup : q.2.1.Nodup
  columns_inj : Set.InjOn (impColumnSet X name₂) {g | g ∈ q.2.1}
  blocks : impColumnSet X name₂ '' {g | g ∈ q.2.1} = Y.blocks
  matrix : q.2.2 = q.1.map (fun a => q.2.1.map (fun g =>
    if ∃ x : ↥X.Pt₁, name₁ x = a ∧ (x.val,impColumnSet X name₂ g) ∈ Y.E then 1 else 0))
  point_colors : ∀ x, Y.f x = 0
  block_colors : ∀ B, Y.g B = 0
  hint : ∀ B C, Y.h B C = 0

theorem ImpGraphRep.numBlocks {q : RawImpGraph} {Y : VColBipBlk ↥s ℕ}
    (hq : ImpGraphRep X name₁ name₂ r q Y) : Y.numBlocks = q.2.1.length := by
  rw [VColBipBlk.numBlocks,← hq.blocks,hq.columns_inj.ncard_image]
  have he : {g | g ∈ q.2.1} = (↑q.2.1.toFinset : Set (List ℕ)) := by ext g; simp
  rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup hq.columns_nodup]

end Representation

section Construction
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r)

include h

/-- A matrix constructor represents a graph once its columns and edge test agree. -/
theorem impMakeGraph_rep (k : ℕ) (cols : List (List ℕ)) (Y : VColBipBlk ↥s ℕ)
    (hp : Y.part₁ = X.part₁) (hnd : cols.Nodup)
    (hi : Set.InjOn (impColumnSet X name₂) {g | g ∈ cols})
    (hb : impColumnSet X name₂ '' {g | g ∈ cols} = Y.blocks)
    (hE : ∀ x : ↥X.Pt₁, ∀ g ∈ cols,
      impColumnEdge (((r.1,k),g),name₁ x) = true ↔
        (x.val,impColumnSet X name₂ g) ∈ Y.E)
    (hf : ∀ x, Y.f x = 0) (hg : ∀ B, Y.g B = 0) (hh : ∀ B C, Y.h B C = 0) :
    ImpGraphRep X name₁ name₂ r (impMakeGraph ((r,k),cols)) Y := by
  classical
  refine ⟨rfl,hp,hnd,hi,hb,?_,hf,hg,hh⟩
  change r.2.1.map (fun a => cols.map (fun g =>
      if impColumnEdge (((r.1,k),g),a) then 1 else 0)) = _
  apply List.map_congr_left
  intro a ha
  obtain ⟨x,rfl⟩ := (h.left _).1 ha
  apply List.map_congr_left
  intro g hmem
  have ht : impColumnEdge (((r.1,k),g),name₁ x) = true ↔
      ∃ y : ↥X.Pt₁, name₁ y = name₁ x ∧ (y.val,impColumnSet X name₂ g) ∈ Y.E := by
    rw [hE x g hmem]
    constructor
    · intro he; exact ⟨x,rfl,he⟩
    · rintro ⟨y,hy,he⟩
      have : y = x := h.inj₁ hy
      subst y
      exact he
  simp only [ht]

end Construction

section Contraction
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : ImpNames X name₁ name₂ r) (hleft : r.2.1.Nodup)
    (e : ↥X.blocks ≃ Fin r.2.2.length) (he : ∀ B, r.2.2[(e B).val] = name₂ B)

include h hleft he

/-- Contracting a group joins a point to its union exactly as step 2(ii) requires. -/
theorem impContraction_edge (x : ↥X.Pt₁) (g : List ℕ) (hg : g ∈ impGroups r) :
    impColumnEdge (((r.1,impH r),g),name₁ x) = true ↔
      (x.val,impColumnSet X name₂ g) ∈ X.blkContr.E := by
  have hblock : impColumnSet X name₂ g ∈ X.blkContr.blocks := by
    rw [← impColumns_contraction h e he]
    exact ⟨g,hg,rfl⟩
  rw [impColumnEdge_spec]
  constructor
  · rintro ⟨a,ha,hc⟩
    obtain ⟨i,_,hgi⟩ := (impGroups_mem _ _).1 hg
    have har : a ∈ r.2.2 := impGroup_mem_right (hgi ▸ ha)
    obtain ⟨B,rfl⟩ := (h.right _).1 har
    rw [h.link,impH_spec h hleft] at hc
    exact ⟨hblock,x.property,B.val,B.property,fun z hz => ⟨B,ha,hz⟩,hc⟩
  · rintro ⟨_,_,D,hD,hsub,hc⟩
    obtain ⟨z,hz⟩ := X.blocks_nonempty D hD
    obtain ⟨B,hB,hzB⟩ := hsub hz
    have hDB : D = B.val := by
      by_contra hne
      exact (Set.disjoint_left.1 (X.blocks_disjoint D hD B.val B.property hne)) hz hzB
    refine ⟨name₂ B,hB,?_⟩
    rw [h.link,impH_spec h hleft,← hDB]
    exact hc

/-- Every field of the contracted graph agrees with the paper. -/
theorem impContractionGraph_rep :
    ImpGraphRep X name₁ name₂ r (impContractionGraph r) X.blkContr :=
  impMakeGraph_rep h (impH r) (impGroups r) X.blkContr rfl
    (impGroups_nodup r) (impColumns_contraction_inj h e he)
    (impColumns_contraction h e he) (impContraction_edge h hleft e he)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

end Contraction
end Algo
