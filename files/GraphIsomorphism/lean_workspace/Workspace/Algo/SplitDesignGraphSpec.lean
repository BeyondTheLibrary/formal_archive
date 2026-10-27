import Workspace.Algo.SplitDesignGraph

/-! # The next turn starts from the restricted link graph

The graph constructor is checked on all vertex pairs. Names are inherited
from the previous turn. The supplied hint is the only new field.
-/
namespace Algo
open Babai RAM

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r) (hw : r.WF)
    {S : Set (Set ↥s)} (g : List ℕ)
    (hg : ∀ B : ↥X.blocks, name₂ B ∈ g ↔ B.val ∈ S)
    (hgr : ∀ a ∈ g, a ∈ r.2.2)
    (H : Set ↥s → Set ↥s → ℕ) (hint : RawConfig)
variable (name : (X.linkGraph.restrictBlkHint S H).Vtx → ℕ)
    (hp : ∀ x : ↥X.Pt₁, name ⟨{x.val},Or.inl ⟨x.val,x.property,rfl⟩⟩ = name₁ x)
    (hb : ∀ B : ↥X.blocks, ∀ hB : B.val ∈ S, name ⟨B.val,Or.inr ⟨B.property,hB⟩⟩ = name₂ B)
include h hw hg hgr hp hb

open scoped Classical in
theorem designGraphVertex_spec (A : (X.linkGraph.restrictBlkHint S H).Vtx) :
    designGraphVertex (((r,g),hint),name A) = (X.linkGraph.restrictBlkHint S H).initVtxColor A.val := by
  classical
  rcases A with ⟨A,hA⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · have hn := hp ⟨x,hx⟩
    have hm : name₁ ⟨x,hx⟩ ∈ r.2.1 := (h.left _).2 ⟨_,rfl⟩
    rw [hn]
    simp only [designGraphVertex,hm,decide_true,if_true,h.points]
    rw [VColBipBlk.initVtxColor,if_pos ⟨x,hx,rfl⟩]
    simp only [Set.image_singleton,csSup_singleton]
    rfl
  · have hn := hb ⟨A,hA.1⟩ hA.2
    have hm : name₂ ⟨A,hA.1⟩ ∈ g := (hg _).2 hA.2
    have hleft : name₂ ⟨A,hA.1⟩ ∉ r.2.1 :=
      fun hl => hw.disjoint _ hl (hgr _ hm)
    have hnot : ¬ ∃ x, (X.linkGraph.restrictBlkHint S H).part₁ x ∧ A = {x} := by
      rintro ⟨x,hx,rfl⟩
      exact X.blocks_off₁ _ hA.1 _ (Set.mem_singleton _) hx
    rw [hn]
    simp only [designGraphVertex,hleft,decide_false,Bool.false_eq_true,if_false,hm,decide_true,if_true,h.blocks]
    rw [VColBipBlk.initVtxColor,if_neg hnot,if_pos hA]
    change Nat.pair 2 (X.c A A) = Nat.pair 2 (if A ∈ S then (if A ∈ X.blocks then X.c A A else 0) else 0)
    rw [if_pos hA.2]
    rw [if_pos (show A ∈ X.blocks from hA.1)]

open scoped Classical in
theorem designGraphEdge_all (A B : (X.linkGraph.restrictBlkHint S H).Vtx) :
    designGraphEdge (((r,g),hint),(name A,name B)) = (X.linkGraph.restrictBlkHint S H).initEdge A.val B.val := by
  classical
  rcases A with ⟨A,hA⟩
  rcases B with ⟨B,hB⟩
  rcases hA with ⟨x,hx,rfl⟩ | hA
  · rcases hB with ⟨y,hy,rfl⟩ | hB
    · have hxm : name₁ ⟨x,hx⟩ ∈ r.2.1 := (h.left _).2 ⟨_,rfl⟩
      have hym : name₁ ⟨y,hy⟩ ∈ r.2.1 := (h.left _).2 ⟨_,rfl⟩
      have hyng : name₁ ⟨y,hy⟩ ∉ g := fun hy => hw.disjoint _ hym (hgr _ hy)
      have hno : ¬ ∃ z, (X.linkGraph.restrictBlkHint S H).part₁ z ∧ ({x} : Set ↥s) = {z} ∧ (z,{y}) ∈ (X.linkGraph.restrictBlkHint S H).E := by
        rintro ⟨z,hz,he,hedge⟩
        exact X.blocks_off₁ _ hedge.1.2.1 _ (Set.mem_singleton _) hy
      rw [hp ⟨x,hx⟩,hp ⟨y,hy⟩]
      simp only [designGraphEdge,designGraphEdgeTest,hyng,decide_false,Bool.and_false,
        Bool.false_and,Bool.false_eq_true,if_false,VColBipBlk.initEdge,if_neg hno]
    · rw [hp ⟨x,hx⟩,hb ⟨B,hB.1⟩ hB.2]
      rw [designGraphEdge_spec h g hint (S := S) (fun C => hg C)]
      have he : (x,B) ∈ (X.linkGraph.restrictBlk S).E ↔
          ∃ z, (X.linkGraph.restrictBlkHint S H).part₁ z ∧ ({x} : Set ↥s) = {z} ∧ (z,B) ∈ (X.linkGraph.restrictBlkHint S H).E := by
        constructor
        · intro hh; exact ⟨x,hx,rfl,hh⟩
        · rintro ⟨z,hz,hz',hh⟩
          have := Set.singleton_injective hz'
          subst z
          exact hh
      simp only [VColBipBlk.initEdge,he]
      split_ifs <;> rfl
  · have ham : name₂ ⟨A,hA.1⟩ ∈ g := (hg _).2 hA.2
    have hal : name₂ ⟨A,hA.1⟩ ∉ r.2.1 := fun hh => hw.disjoint _ hh (hgr _ ham)
    have hno : ¬ ∃ z, (X.linkGraph.restrictBlkHint S H).part₁ z ∧ A = {z} ∧ (z,B) ∈ (X.linkGraph.restrictBlkHint S H).E := by
      rintro ⟨z,hz,rfl,_⟩
      exact X.blocks_off₁ _ hA.1 _ (Set.mem_singleton _) hz
    rw [hb ⟨A,hA.1⟩ hA.2]
    simp only [designGraphEdge,designGraphEdgeTest,hal,decide_false,Bool.false_and,
      Bool.false_eq_true,if_false,VColBipBlk.initEdge,if_neg hno]

include h hw hg hgr hp hb
open scoped Classical in
theorem designGraphPair_spec (hinj : Function.Injective name)
    (hh : ∀ A B : (X.linkGraph.restrictBlkHint S H).Vtx, binColor (hint,(name A,name B)) = (X.linkGraph.restrictBlkHint S H).h A.val B.val)
    (A B : (X.linkGraph.restrictBlkHint S H).Vtx) :
    designGraphPair (((r,g),hint),(name A,name B)) = (X.linkGraph.restrictBlkHint S H).vtxInitColor A B := by
  have he : name A = name B ↔ A.val = B.val := hinj.eq_iff.trans Subtype.val_inj.symm
  simp only [designGraphPair,VColBipBlk.vtxInitColor,VColBipBlk.initColor,decide_eq_true_eq,he,
    designGraphVertex_spec h hw g hg hgr H hint name hp hb,
    designGraphEdge_all h hw g hg hgr H hint name hp hb,hh]


/-- Refinement starts from the exact restricted graph, including its hint. -/
theorem designGraphRefine_spec (hinj : Function.Injective name)
    (hh : ∀ A B : (X.linkGraph.restrictBlkHint S H).Vtx,
      binColor (hint,(name A,name B)) = (X.linkGraph.restrictBlkHint S H).h A.val B.val)
    (e : (X.linkGraph.restrictBlkHint S H).Vtx ≃ Fin (r.2.1 ++ g).length)
    (hl : ∀ A, (r.2.1 ++ g)[(e A).val] = name A)
    (A B : (X.linkGraph.restrictBlkHint S H).Vtx) :
    binColor (designGraphRefine ((r,g),hint),(e A,e B)) =
      (X.linkGraph.restrictBlkHint S H).wlNamed A B := by
  have hi : ∀ C D : (X.linkGraph.restrictBlkHint S H).Vtx,
      namedBin (r.2.1 ++ g).length
        (sbipIndexed (designGraphInitial ((r,g),hint),r.2.1 ++ g)) (e C) (e D) =
          (X.linkGraph.restrictBlkHint S H).vtxInitColor C D := by
    intro C D
    rw [namedBin,sbipIndexed_get,hl,hl,designGraphInitial_get _
      (hl C ▸ List.getElem_mem (e C).isLt) (hl D ▸ List.getElem_mem (e D).isLt)]
    exact designGraphPair_spec h hw g hg hgr H hint name hp hb hinj hh C D
  exact sbipStep3_named (X.linkGraph.restrictBlkHint S H) e (sbipIndexed_wf _ _) hi A B

end
end Algo
