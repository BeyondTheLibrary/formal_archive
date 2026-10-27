import Workspace.Algo.SplitBipNodeRaw
import Workspace.Algo.SplitBipGraphEarlyNames
import Workspace.Algo.SplitBipCaseOutcomeStep9Johnson

/-! The semantic invariant is separate from the total raw recursion.
All persistent point names are coordinates in one fixed original `Fin m`.
A zero stage bit records a genuine hint on the mathematical graph.
-/
namespace Algo
open Babai RAM
open scoped Classical

structure SbipNodeRep (m : ℕ) (I : RawSbipNode) (X : Pt (BipBlockInputs (Fin m))) : Prop where
  ground : sbipNodeGround I = m
  stored : SbipStoredRep X.obj.1.1 (fun x => x.val.val) I.1.2.1
  alpha : sbipAlphaValue I.1.2.2 = BipBlockInputs.alpha X
  denominator : 0 < I.1.2.2.2
  hint : sbipNodeBit I = 0 → X.obj.1.1.HasHint

def SbipNodeValid (m : ℕ) (I : RawSbipNode) : Prop :=
  ∃ X : Pt (BipBlockInputs (Fin m)),SbipNodeRep m I X

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem names :
    ∃ (name : X.obj.1.1.Vtx → ℕ)
      (e : X.obj.1.1.Vtx ≃ Fin (sbipGraphVertices I.1.2.1.1).length),
      SbipGraphColorNames X.obj.1.1 I.1.2.1.1 name ∧
      SbipStoredDictionary X.obj.1.1 (fun x => x.val.val) I.1.2.1 name ∧
      (∀ x,labAt I.1.2.1.1.2.1 x.val.val = X.obj.1.1.f x) ∧
      (sbipGraphVertices I.1.2.1.1).Nodup ∧
      (∀ A,(sbipGraphVertices I.1.2.1.1)[(e A).val] = name A) ∧
      sbipGraphPointName X name '' Set.univ = {a | a ∈ I.1.2.1.1.1.1} ∧
      sbipGraphBlockName X name '' Set.univ = {a | a ∈ I.1.2.1.1.1.2.1} := by
  obtain ⟨name,hc,hd,hf,hn,hl,hr,hcover⟩ := h.stored
  obtain ⟨e,he⟩ := splitNameEquiv_exists name hc.injective _ hn hcover
  refine ⟨name,e,hc,hd,hf,hn,he,?_,?_⟩
  · ext a
    constructor
    · rintro ⟨x,_,rfl⟩
      exact (hl _).2 ⟨x.val,x.property,rfl⟩
    · intro ha
      obtain ⟨A,hA⟩ := (hcover a).1 (List.mem_append_left _ ha)
      obtain ⟨x,hx,hAx⟩ := (hl A).1 (hA ▸ ha)
      refine ⟨⟨x,hx⟩,Set.mem_univ _,?_⟩
      exact (congrArg name (Subtype.ext hAx.symm)).trans hA
  · ext a
    constructor
    · rintro ⟨B,_,rfl⟩
      exact (hr _).2 B.property
    · intro ha
      obtain ⟨A,hA⟩ := (hcover a).1 (List.mem_append_right _ ha)
      have hB := (hr A).1 (hA ▸ ha)
      exact ⟨⟨A.val,hB⟩,Set.mem_univ _,hA⟩

theorem left_nodup : I.1.2.1.1.1.1.Nodup := by
  obtain ⟨_,_,_,_,_,hnd,_,_,_⟩ := h.names
  exact (List.nodup_append.1 hnd).1

theorem right_nodup : I.1.2.1.1.1.2.1.Nodup := by
  obtain ⟨_,_,_,_,_,hnd,_,_,_⟩ := h.names
  exact (List.nodup_append.1 hnd).2.1

theorem point_cover (a : ℕ) :
    a ∈ I.1.2.1.1.1.1 ↔ ∃ x : ↥X.obj.1.1.V₁,x.val.val.val = a := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  rw [← show a ∈ sbipGraphPointName X name '' Set.univ ↔ a ∈ I.1.2.1.1.1.1 from by rw [hp]; rfl]
  constructor
  · rintro ⟨x,_,hx⟩
    exact ⟨x,(hd.point_name x.val x.property).symm.trans hx⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,Set.mem_univ _,hd.point_name x.val x.property⟩

theorem point_lt (a : ℕ) (ha : a ∈ I.1.2.1.1.1.1) : a < m := by
  obtain ⟨x,rfl⟩ := (h.point_cover a).1 ha
  exact x.val.val.isLt

theorem point_set : winSet m I.1.2.1.1.1.1 = BipBlockInputs.V₁ X := by
  ext x
  change x.val ∈ I.1.2.1.1.1.1 ↔ _
  rw [h.point_cover]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y.val,y.property,Fin.ext hy⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩

theorem block_count : sbipNodeBlocks I = BipBlockInputs.numBlocks X := by
  obtain ⟨name,e,hc,hd,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eB,heB⟩ := sbipGraphEarly_block_equiv_exists X I.1.2.1.1 name hc hr h.right_nodup
  exact sbipGraphEarly_block_size X I.1.2.1.1 eB

end SbipNodeRep
end Algo
