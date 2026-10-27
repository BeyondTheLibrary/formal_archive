import Workspace.Algo.SplitImprimitiveStoredRep
import Workspace.Algo.SplitBipPackSpec
import Workspace.Algo.SplitBipStoredDictionary

/-! The stored ImprimitiveCase output satisfies the shared graph and member
row semantics used by the next recursive turn. All output fields come from
an actual selected graph and the incoming dictionary's point/block meaning.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} {q : RawImpGraph} {Y : VColBipBlk ↥s ℕ}
    (hr : ImpGraphRep X name₁ name₂ r q Y) (dom : List ℕ) (d : List (List ℕ))
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length)

noncomputable def impStoredPointEquiv :
    ↥Y.V₁ ≃ Fin (impStoredPack ((dom,d),q)).1.2.length :=
  (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hr.part)).trans
    (e₁.trans (finCongr (by simp [impStoredPack,sbipDictPoints,hr.left])))

noncomputable def impStoredBlockIndex :
    ↥Y.blocks ≃ Fin (impStoredPack ((dom,d),q)).2.1.length :=
  (impStoredBlockEquiv hr).symm.trans (finCongr (by simp [impStoredPack]))

variable {point : ↥s → ℕ}
    (hn : ImpNames X name₁ name₂ r) (hd : ImpStoredNames X name₁ name₂ point d)
    (hq : q ∈ impStep2Graphs r) (hleft : r.2.1.Nodup)
    (hp : Function.Injective point) (hlt : ∀ x,point x < dom.length)
    (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)

include hd he₁ in
theorem impStoredPointEquiv_get (x : ↥Y.V₁) :
    (impStoredPack ((dom,d),q)).1.2[(impStoredPointEquiv hr dom d e₁ x).val] = point x.val := by
  let x' : ↥X.Pt₁ := (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hr.part)) x
  have hh := impStoredGraph_point_get hr hd dom e₁ he₁ x'
  change rawGet ((impStoredPack ((dom,d),q)).1.2,impStoredPointEquiv hr dom d e₁ x) = point x.val at hh
  rw [rawGet,List.getD_eq_getElem _ _ (impStoredPointEquiv hr dom d e₁ x).isLt] at hh
  exact hh

include hn hd hq hleft hp hlt he₁ in
theorem impStoredGraph_colorNames :
    SbipGraphColorNames Y (impStoredGraph ((dom,d),q)).1
      (sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm) := by
  let z := impStoredPack ((dom,d),q)
  let ep := impStoredPointEquiv hr dom d e₁
  let eb := impStoredBlockIndex hr dom d
  apply sbipPack_colorNames Y point z ep eb hp (fun x _ => hlt x)
    (impStoredGraph_left_nodup hn hd hq dom hleft hp)
    (impStoredPointEquiv_get hr dom d e₁ hd he₁)
  · intro x
    exact impStoredGraph_full_point_colors hr dom x
  · intro B
    have hh := impStoredGraph_block_colors hr (d := d) dom ((impStoredBlockEquiv hr).symm B)
    change labAt (sbipPack z).1.2.2.1 (z.1.1.length+eb B) = _ at hh
    rw [sbipPack_blockColor] at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · intro x B
    let x' : ↥X.Pt₁ := (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hr.part)) x
    have hh := impStoredGraph_matrix_spec hr (d := d) hn dom e₁ he₁ x' ((impStoredBlockEquiv hr).symm B)
    simpa only [Equiv.apply_symm_apply] using hh
  · intro A B
    change 0 = Y.h A.val B.val
    exact (hr.hint A.val B.val).symm

include hn hd hq hlt he₁ in
theorem impStoredGraph_vertex_members (A : Y.Vtx) (a : ℕ) :
    a ∈ sbipVertexMembers (impStoredGraph ((dom,d),q),
      sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm A) ↔
        ∃ x ∈ A.val,point x = a := by
  apply sbipPack_vertex_members Y point (impStoredPack ((dom,d),q))
    (impStoredPointEquiv hr dom d e₁) (impStoredBlockIndex hr dom d)
    (fun x _ => hlt x) (impStoredPointEquiv_get hr dom d e₁ hd he₁)
  intro B u
  have hh := impStoredGraph_block_members hr hn hd hq dom ((impStoredBlockEquiv hr).symm B) u
  rw [impStoredGraph_dict] at hh
  simpa only [impStoredPack,List.getElem_map,Equiv.apply_symm_apply] using hh

include hd hlt he₁ in
theorem impStoredGraph_vertex_members_nodup (A : Y.Vtx) :
    (sbipVertexMembers (impStoredGraph ((dom,d),q),
      sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm A)).Nodup := by
  apply sbipPack_vertex_members_nodup Y point (impStoredPack ((dom,d),q))
    (impStoredPointEquiv hr dom d e₁) (impStoredBlockIndex hr dom d)
    (fun x _ => hlt x) (impStoredPointEquiv_get hr dom d e₁ hd he₁)
  intro B
  simpa only [impStoredPack,List.getElem_map] using
    sbipDictUnion_nodup (d,q.2.1[((impStoredBlockEquiv hr).symm B).val])

include hd hlt he₁ in
theorem impStoredGraph_names_cover (a : ℕ) :
    a ∈ sbipPackVertices (impStoredPack ((dom,d),q)) ↔
      ∃ A : Y.Vtx,sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm A = a := by
  exact sbipPackNames_cover Y point (impStoredPack ((dom,d),q))
    (impStoredPointEquiv hr dom d e₁) (impStoredBlockIndex hr dom d)
    (fun x _ => hlt x) (impStoredPointEquiv_get hr dom d e₁ hd he₁) a

include hr hn hd hq hleft hp hlt he₁ in
theorem impStoredGraph_vertices_nodup :
    (sbipPackVertices (impStoredPack ((dom,d),q))).Nodup := by
  apply sbipPackVertices_nodup (impStoredPack ((dom,d),q))
    (impStoredGraph_left_nodup hn hd hq dom hleft hp)
  exact sbipPack_left_bound Y point (impStoredPack ((dom,d),q))
    (impStoredPointEquiv hr dom d e₁) (fun x _ => hlt x)
    (impStoredPointEquiv_get hr dom d e₁ hd he₁)

include hn hd hq in
theorem impStoredGraph_storedDictionary :
    SbipStoredDictionary Y point (impStoredGraph ((dom,d),q))
      (sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm) := by
  apply sbipPack_storedDictionary Y point (impStoredPack ((dom,d),q))
    (impStoredBlockIndex hr dom d)
  · intro B
    simpa only [impStoredPack,List.getElem_map] using
      sbipDictUnion_nodup (d,q.2.1[((impStoredBlockEquiv hr).symm B).val])
  · intro B a
    have hh := impStoredGraph_block_members hr hn hd hq dom ((impStoredBlockEquiv hr).symm B) a
    rw [impStoredGraph_dict] at hh
    simpa only [impStoredPack,List.getElem_map,Equiv.apply_symm_apply] using hh

end

section Complete
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkImprimitiveObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} {q : RawImpGraph} {Y : VColBipBlk ↥s ℕ}
    (hr : ImpGraphRep X name₁ name₂ r q Y)
    (hn : ImpNames X name₁ name₂ r) (hleft : r.2.1.Nodup)
    (point : ↥s → ℕ) (dom : List ℕ) (d : List (List ℕ))
    (hd : ImpStoredNames X name₁ name₂ point d)
    (hq : q ∈ impStep2Graphs r) (hp : Function.Injective point)
    (hlt : ∀ x,point x < dom.length)
include hr hn hleft hd hq hp hlt

/-- The complete common output interface, with point positions derived
from the actual incoming list rather than supplied separately. -/
theorem impStoredGraph_complete :
    let z := impStoredGraph ((dom,d),q)
    ∃ name : Y.Vtx → ℕ,
      SbipGraphColorNames Y z.1 name ∧
      SbipStoredDictionary Y point z name ∧
      (∀ x,labAt z.1.2.1 (point x) = Y.f x) ∧
      (sbipGraphVertices z.1).Nodup ∧
      (∀ A,name A ∈ z.1.1.1 ↔ ∃ x,Y.part₁ x ∧ A.val = {x}) ∧
      (∀ A,name A ∈ z.1.1.2.1 ↔ A.val ∈ Y.blocks) ∧
      (∀ a,a ∈ sbipGraphVertices z.1 ↔ ∃ A,name A = a) := by
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists name₁ hn.inj₁ r.2.1 hleft hn.left
  refine ⟨sbipPackName Y point dom.length (impStoredBlockEquiv hr).symm,
    impStoredGraph_colorNames hr dom d e₁ hn hd hq hleft hp hlt he₁,
    impStoredGraph_storedDictionary hr dom d hn hd hq,
    impStoredGraph_full_point_colors hr dom,
    impStoredGraph_vertices_nodup hr dom d e₁ hn hd hq hleft hp hlt he₁,?_,?_,
    impStoredGraph_names_cover hr dom d e₁ hd hlt he₁⟩
  · exact sbipPackNames_left Y point (impStoredPack ((dom,d),q))
      (impStoredPointEquiv hr dom d e₁) (impStoredBlockIndex hr dom d)
      (fun x _ => hlt x) (impStoredPointEquiv_get hr dom d e₁ hd he₁)
  · exact sbipPackNames_right Y point (impStoredPack ((dom,d),q))
      (impStoredBlockIndex hr dom d) (fun x _ => hlt x)

end Complete
end Algo
