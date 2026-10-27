import Workspace.Algo.SplitBipGraphRaw

/-! The shared graph constructor reads exact matrix and decoration fields.
Its refinement keeps the old names, so later restrictions use the same
point and block dictionaries, including colors outside the first part. -/
namespace Algo
open Babai RAM

theorem sbipGraphEdge_get (r : RawSbipGraph) (hl : r.1.1.Nodup)
    (hr : r.1.2.1.Nodup) (i : Fin r.1.1.length) (j : Fin r.1.2.1.length) :
    sbipGraphEdge (r,(r.1.1[i.val],r.1.2.1[j.val])) =
      if sbipMatrixEntry (r.1,(i,j)) = 0 then 0 else 1 := by
  simp only [sbipGraphEdge,List.getElem_mem,decide_true,Bool.true_and,if_true,
    sbipLetterIndex_get hl,sbipLetterIndex_get hr]

theorem sbipGraphEdge_off (r : RawSbipGraph) (a b : ℕ)
    (h : a ∉ r.1.1 ∨ b ∉ r.1.2.1) : sbipGraphEdge (r,(a,b)) = 0 := by
  rcases h with h | h <;> simp [sbipGraphEdge,h]

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (G : VColBipBlk ↥s ℕ) (r : RawSbipGraph) (name : G.Vtx → ℕ)

/-- Every field read by the initial coloring, under one vertex naming. -/
structure SbipGraphColorNames : Prop where
  injective : Function.Injective name
  vertex : ∀ A, sbipGraphVertexColor (r,name A) = G.initVtxColor A.val
  edge : ∀ A B, sbipGraphEdge (r,(name A,name B)) = G.initEdge A.val B.val
  hint : ∀ A B, binColor (r.2.2.2,(name A,name B)) = G.h A.val B.val

theorem sbipGraphPair_spec (h : SbipGraphColorNames G r name) (A B : G.Vtx) :
    sbipGraphPair (r,(name A,name B)) = G.vtxInitColor A B := by
  have he : name A = name B ↔ A.val = B.val := h.injective.eq_iff.trans Subtype.val_inj.symm
  simp only [sbipGraphPair,VColBipBlk.vtxInitColor,VColBipBlk.initColor,
    decide_eq_true_eq,he,h.vertex,h.edge,h.hint]

theorem sbipGraphRefine_spec (h : SbipGraphColorNames G r name)
    (hnd : (sbipGraphVertices r).Nodup)
    (e : G.Vtx ≃ Fin (sbipGraphVertices r).length)
    (he : ∀ A, (sbipGraphVertices r)[(e A).val]'(e A).isLt = name A)
    (A B : G.Vtx) : binColor (sbipGraphRefine r,(name A,name B)) = G.wlNamed A B := by
  apply sbipRefineNames_spec G (sbipGraphInitial r) (sbipGraphVertices r) hnd name e he
  intro C D
  rw [sbipGraphInitial_get _ (he C ▸ List.getElem_mem (e C).isLt)
    (he D ▸ List.getElem_mem (e D).isLt)]
  exact sbipGraphPair_spec G r name h C D

end
end Algo
