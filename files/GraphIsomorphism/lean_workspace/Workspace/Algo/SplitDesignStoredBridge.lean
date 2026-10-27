import Workspace.Algo.SplitDesignStoredHint

/-! A design-case graph is ready for the next recursive turn once all its
stored fields and member rows describe the selected mathematical graph. -/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (hn : DesignNames X name₁ name₂ r) (hw : r.WF)
    (point : ↥s → ℕ) (d : List (List ℕ)) (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)
    (h₁ : ∀ x, (e (X.vtxOfPt x)).val = name₁ x)
    (h₂ : ∀ B, (e (X.vtxOfBlk B)).val = name₂ B)
    (hnsize : r.1.1.length = d.length)
    (hc : ∀ A, binColor (r.1,(e A,e A)) = X.c A.val A.val)
    (w : List ℕ) (hlt : ∀ x, point x < w.length)
    (S : Set (Set ↥s)) (H : Set ↥s → Set ↥s → ℕ) (cols : List ℕ) (hint : RawConfig)
    (hnd : cols.Nodup) (hcols : ∀ a ∈ cols, a ∈ r.2.2)
    (hS : ∀ B : ↥X.blocks, name₂ B ∈ cols ↔ B.val ∈ S)
    (hH : ∀ A B : (X.linkGraph.restrictBlkHint S H).Vtx,
      binColor (hint,(designGraphName (name₁ := name₁) (name₂ := name₂) S H A,
        designGraphName (name₁ := name₁) (name₂ := name₂) S H B)) =
          (X.linkGraph.restrictBlkHint S H).h A.val B.val)
include hn hw hd hp h₁ h₂ hnsize hc hlt hnd hcols hS hH

theorem designStored_complete :
    let Y := X.linkGraph.restrictBlkHint S H
    let out := designStored ((w,d),((r,cols),hint))
    ∃ name : Y.Vtx → ℕ,
      SbipGraphColorNames Y out.1 name ∧ SbipStoredDictionary Y point out name ∧
      (∀ x, labAt out.1.2.1 (point x) = Y.f x) ∧ (sbipGraphVertices out.1).Nodup ∧
      (∀ A, name A ∈ out.1.1.1 ↔ ∃ x, Y.part₁ x ∧ A.val = {x}) ∧
      (∀ A, name A ∈ out.1.1.2.1 ↔ A.val ∈ Y.blocks) ∧
      (∀ a, a ∈ sbipGraphVertices out.1 ↔ ∃ A, name A = a) := by
  let Y := X.linkGraph.restrictBlkHint S H
  let z := sbipFromCasePack ((w,d),(designStoredRaw ((r,cols),hint),0))
  obtain ⟨e₁,he₁⟩ := designStored_point_equiv_exists hn hw
  obtain ⟨eB,heB⟩ := designStored_block_equiv_exists hn S H cols hnd hcols hS
  let ep := designStoredPointEquiv (r := r) d w S H cols hint e₁
  let eb := designStoredBlockEquiv (r := r) d w S H cols hint eB
  have hep : ∀ x : ↥Y.V₁, z.1.2[(ep x).val] = point x.val :=
    designStoredPointEquiv_get point d e hd hp h₁ w S H cols hint e₁ he₁
  have hl : z.1.2.Nodup := designStored_left_nodup hn hw point d e hd hp h₁
  have hbound : ∀ x, Y.part₁ x → point x < z.1.1.length := fun x _ => hlt x
  have hz : (sbipPackVertices z).Nodup :=
    sbipPackVertices_nodup z hl (sbipPack_left_bound Y point z ep hbound hep)
  have hf : ∀ x, labAt z.2.2.2.1 (point x) = Y.f x := fun x =>
    designStored_pointColor X point d e hd hp hnsize hc w cols hint x (hlt x)
  refine ⟨sbipPackName Y point w.length eb,?_,?_,hf,hz,?_,?_,?_⟩
  · apply sbipPack_colorNames Y point z ep eb hp hbound hl hep hf
    · exact designStored_column_color hn hw d w S H cols hint eB heB
    · exact designStored_matrix_spec hn d w S H cols hint e₁ he₁ eB heB hS
    · exact designStored_hint point d e hd hp h₁ w S H cols hint e₁ he₁ eB heB hz hH
  · exact sbipPack_storedDictionary Y point z eb
      (designStored_column_nodup point d e hd h₂ w S H cols hint eB heB)
      (designStored_column_mem point d e hd h₂ w S H cols hint eB heB)
  · exact sbipPackNames_left Y point z ep eb hbound hep
  · exact sbipPackNames_right Y point z eb hbound
  · exact sbipPackNames_cover Y point z ep eb hbound hep

end
end Algo
