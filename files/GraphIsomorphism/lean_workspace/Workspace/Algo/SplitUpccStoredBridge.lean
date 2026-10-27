import Workspace.Algo.SplitUpccStoredNames
import Workspace.Algo.SplitBipPackSpec
import Workspace.Algo.SplitBipStoredDictionary

/-! The marked UPCC graph is packed with the same adjacency and decorations.
The original point naming remains fixed. New block names only index their
retained member rows, including singleton blocks outside the first part.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) (point : ↥s → ℕ) (d : List (List ℕ))
    (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    {lab : RawLab} {m : ℕ} {g : RawUpccBip} {Y : VColBipBlk ↥s ℕ}
    (hr : UpccCaseGraphRep X e lab m g Y)
    (w : List ℕ) (hlt : ∀ x,point x < w.length)

include hd hp hr hlt in
/-- Every field and member row follows from the selected UPCC graph and
the incoming dictionary. No packed graph invariant is assumed. -/
theorem upccStored_complete :
    ∃ name : Y.Vtx → ℕ,
      SbipGraphColorNames Y (upccStored ((w,d),(lab,(m,g)))).1 name ∧
      SbipStoredDictionary Y point (upccStored ((w,d),(lab,(m,g)))) name ∧
      (∀ x,labAt (upccStored ((w,d),(lab,(m,g)))).1.2.1 (point x) = Y.f x) ∧
      (sbipGraphVertices (upccStored ((w,d),(lab,(m,g)))).1).Nodup ∧
      (∀ A,name A ∈ (upccStored ((w,d),(lab,(m,g)))).1.1.1 ↔
        ∃ x,Y.part₁ x ∧ A.val = {x}) ∧
      (∀ A,name A ∈ (upccStored ((w,d),(lab,(m,g)))).1.1.2.1 ↔ A.val ∈ Y.blocks) ∧
      (∀ a,a ∈ sbipGraphVertices (upccStored ((w,d),(lab,(m,g)))).1 ↔
        ∃ A,name A = a) := by
  obtain ⟨e₁,he₁⟩ := upccStored_point_equiv_exists X d e hr
  obtain ⟨hsub,eB,heB⟩ := upccStored_block_equiv_exists X d e hr
  have hnd0 := upccStored_left_nodup X point d e hd hp hr
  obtain ⟨_,_,_,_,hpart,_,_,hf,hg,hh,hmat⟩ := hr
  let z := sbipFromCasePack (upccStoredInput ((w,d),(lab,(m,g))))
  let ep : ↥Y.V₁ ≃ Fin z.1.2.length :=
    (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hpart)).trans
      (e₁.trans (finCongr (by simp [z,sbipFromCasePack,upccStoredInput,sbipDictPoints])))
  let eb : ↥Y.blocks ≃ Fin z.2.1.length :=
    eB.trans (finCongr (by simp [z,sbipFromCasePack,upccStoredInput,sbipFromCaseColumns]))
  have hep (x : ↥Y.V₁) : z.1.2[(ep x).val] = point x.val := by
    let x' : ↥X.Pt₁ :=
      (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hpart)) x
    simp only [z,sbipFromCasePack,upccStoredInput,sbipDictPoints,List.getElem_map]
    change sbipDictPoint (d,g.1[(e₁ x').val]) = point x.val
    rw [he₁]
    exact upccStored_point X point d e hd hp x'
  have hnd : z.1.2.Nodup := hnd0
  have hbound : ∀ x,Y.part₁ x → point x < z.1.1.length := fun x _ => hlt x
  have hcolors (x : ↥s) : labAt z.2.2.2.1 (point x) = Y.f x :=
    (upccStored_pointColor X point d e hd hp w lab m g x (hlt x)).trans (hf x)
  have hcolumns (B : ↥Y.blocks) :
      z.2.1[(eb B).val] = sbipDictGet (d,upccCaseName₂ X e ⟨B.val,hsub B.property⟩) := by
    simp only [z,sbipFromCasePack,upccStoredInput,sbipFromCaseColumns,List.getElem_map]
    exact congrArg (fun a => sbipDictGet (d,a)) (heB B)
  have hrows (B : ↥Y.blocks) : (z.2.1[(eb B).val]).Nodup := by
    rw [hcolumns]
    exact upccStored_block_nodup X point d e hd ⟨B.val,hsub B.property⟩
  have hmembers (B : ↥Y.blocks) (a : ℕ) :
      a ∈ z.2.1[(eb B).val] ↔ ∃ x ∈ B.val,point x = a := by
    rw [hcolumns]
    exact upccStored_block_mem X point d e hd ⟨B.val,hsub B.property⟩ a
  refine ⟨sbipPackName Y point w.length eb,?_,?_,hcolors,?_,?_,?_,?_⟩
  · apply sbipPack_colorNames Y point z ep eb hp hbound hnd hep hcolors
    · intro B
      change labAt (sbipFromCaseBlockColors ([],g.2.1)) (eB B) = Y.g B.val
      rw [hg]
      simp [sbipFromCaseBlockColors,labAt,(eB B).isLt]
    · intro x B
      let x' : ↥X.Pt₁ :=
        (Equiv.setCongr (congrArg (fun p : ↥s → Prop => {x | p x}) hpart)) x
      change (g.2.2.getD (e₁ x') []).getD (eB B) 0 = _
      rw [hmat]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_eq_getElem (e₁ x').isLt,Option.map_some,Option.getD_some,he₁,
        List.getElem?_eq_getElem (eB B).isLt,heB]
      have hedge : (∃ y : ↥X.Pt₁,∃ C : ↥X.blocks,
          upccCaseName₁ X e y = upccCaseName₁ X e x' ∧
          upccCaseName₂ X e C = upccCaseName₂ X e ⟨B.val,hsub B.property⟩ ∧
          (y.val,C.val) ∈ Y.E) ↔ (x.val,B.val) ∈ Y.E := by
        constructor
        · rintro ⟨y,C,hy,hC,he⟩
          have hy' := upccCaseName₁_injective X e hy
          have hC' := upccCaseName₂_injective X e hC
          subst y
          subst C
          exact he
        · intro he
          exact ⟨x',⟨B.val,hsub B.property⟩,rfl,rfl,he⟩
      simp only [hedge]
    · intro A B
      have hz : ∀ a b,binColor (z.2.2.2.2.2,(a,b)) = 0 := by
        intro a b
        change (((tuplesOf (List.range (sbipGraphVertices (g,(lab,[],([],[])))).length) 2).map
          (fun t => sbipIndexRow ((([],[]),sbipGraphVertices (g,(lab,[],([],[])))),t))).lookup
            [a,b]).getD 0 = 0
        simp only [sbipIndexRow,tblGet,List.lookup_nil,Option.getD_none]
        rw [lookup_map_const]
        split_ifs <;> rfl
      exact (hz _ _).trans (hh A.val B.val).symm
  · exact sbipPack_storedDictionary Y point z eb hrows hmembers
  · exact sbipPackVertices_nodup z hnd (sbipPack_left_bound Y point z ep hbound hep)
  · exact sbipPackNames_left Y point z ep eb hbound hep
  · exact sbipPackNames_right Y point z eb hbound
  · exact sbipPackNames_cover Y point z ep eb hbound hep

end

section Actual
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) (point : ↥s → ℕ) (d : List (List ℕ))
    (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    (w : List ℕ) (hlt : ∀ x,point x < w.length)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r) (B : ↥X.blocks)
include hd hp hlt hw hn

/-- The actual Section 9.8 graph constructor satisfies the next turn's
complete graph, dictionary, and name-list requirements. -/
theorem upccStoredGraph_complete :
    let Y := X.upccBip B
    let z := upccStoredGraph ((w,d),(r,upccCaseName₂ X e B))
    ∃ name : Y.Vtx → ℕ,
      SbipGraphColorNames Y z.1 name ∧
      SbipStoredDictionary Y point z name ∧
      (∀ x,labAt z.1.2.1 (point x) = Y.f x) ∧
      (sbipGraphVertices z.1).Nodup ∧
      (∀ A,name A ∈ z.1.1.1 ↔ ∃ x,Y.part₁ x ∧ A.val = {x}) ∧
      (∀ A,name A ∈ z.1.1.2.1 ↔ A.val ∈ Y.blocks) ∧
      (∀ a,a ∈ sbipGraphVertices z.1 ↔ ∃ A,name A = a) :=
  upccStored_complete X point d e hd hp (upccCaseGraph_spec X e hw hn B) w hlt

end Actual
end Algo
