import Workspace.Algo.SplitDesignStoredNames
import Workspace.Algo.SplitBipPackIndex

/-! Each stored design child inherits its exact matrix and decorations.
The point and block enumerations follow the already selected list order. -/
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
    (w : List ℕ) (S : Set (Set ↥s)) (H : Set ↥s → Set ↥s → ℕ)
    (cols : List ℕ) (hint : RawConfig)

local notation "z" => sbipFromCasePack ((w,d),(designStoredRaw ((r,cols),hint),0))

noncomputable def designStoredPointEquiv (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) :
    ↥(X.linkGraph.restrictBlkHint S H).V₁ ≃ Fin (z).1.2.length :=
  e₁.trans (finCongr (by simp [sbipFromCasePack,designStoredRaw,sbipDictPoints]))

noncomputable def designStoredBlockEquiv (eB : ↥(X.linkGraph.restrictBlkHint S H).blocks ≃ Fin cols.length) :
    ↥(X.linkGraph.restrictBlkHint S H).blocks ≃ Fin (z).2.1.length :=
  eB.trans (finCongr (by simp [sbipFromCasePack,designStoredRaw]))

variable (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length)
    (he₁ : ∀ x, r.2.1[(e₁ x).val] = name₁ x)
    (eB : ↥(X.linkGraph.restrictBlkHint S H).blocks ≃ Fin cols.length)
    (heB : ∀ B, cols[(eB B).val] = name₂ ⟨B.val,B.property.1⟩)

include hd hp h₁ he₁ in
theorem designStoredPointEquiv_get (x : ↥(X.linkGraph.restrictBlkHint S H).V₁) :
    (z).1.2[(designStoredPointEquiv (r := r) d w S H cols hint e₁ x).val] = point x.val := by
  change (r.2.1.map (fun a => sbipDictPoint (d,a)))[(e₁ x).val] = _
  rw [List.getElem_map,he₁]
  exact designStored_point point d e hd hp h₁ x

include hd h₂ heB in
theorem designStored_column_mem (B : ↥(X.linkGraph.restrictBlkHint S H).blocks) (a : ℕ) :
    a ∈ (z).2.1[(designStoredBlockEquiv (r := r) d w S H cols hint eB B).val] ↔
      ∃ x ∈ B.val, point x = a := by
  change a ∈ (cols.map (fun b => sbipDictGet (d,b)))[(eB B).val] ↔ _
  rw [List.getElem_map,heB]
  exact designStored_block_mem point d e hd h₂ ⟨B.val,B.property.1⟩ a

include hd h₂ heB in
theorem designStored_column_nodup (B : ↥(X.linkGraph.restrictBlkHint S H).blocks) :
    ((z).2.1[(designStoredBlockEquiv (r := r) d w S H cols hint eB B).val]).Nodup := by
  change ((cols.map (fun b => sbipDictGet (d,b)))[(eB B).val]).Nodup
  rw [List.getElem_map,heB]
  exact designStored_block_nodup point d e hd h₂ ⟨B.val,B.property.1⟩

include hn hw heB in
theorem designStored_column_color (B : ↥(X.linkGraph.restrictBlkHint S H).blocks) :
    labAt (z).2.2.2.2.1 (designStoredBlockEquiv (r := r) d w S H cols hint eB B) = (X.linkGraph.restrictBlkHint S H).g B.val := by
  have hlt : name₂ ⟨B.val,B.property.1⟩ < r.1.1.length :=
    hw.right_lt ((hn.right _).2 ⟨⟨B.val,B.property.1⟩,rfl⟩)
  change labAt (cols.map (fun a => labAt (sbipDiagColors r.1) a)) (eB B) = _
  rw [labAt,List.getD_eq_getElem _ _ (by simpa using (eB B).isLt),List.getElem_map,heB,
    sbipDiagColors_get _ _ hlt,hn.blocks]
  change X.c B.val B.val = if B.val ∈ S then (if B.val ∈ X.blocks then X.c B.val B.val else 0) else 0
  rw [if_pos B.property.2,if_pos (show B.val ∈ X.blocks from B.property.1)]

include hn he₁ heB in
theorem designStored_matrix_spec
    (hS : ∀ B : ↥X.blocks, name₂ B ∈ cols ↔ B.val ∈ S)
    (x : ↥(X.linkGraph.restrictBlkHint S H).V₁) (B : ↥(X.linkGraph.restrictBlkHint S H).blocks) :
    sbipMatrixEntry (((z).1.2,sbipPackBlocks z,(z).2.2.1),
      (designStoredPointEquiv (r := r) d w S H cols hint e₁ x,
        designStoredBlockEquiv (r := r) d w S H cols hint eB B)) =
      if (x.val,B.val) ∈ (X.linkGraph.restrictBlkHint S H).E then 1 else 0 := by
  change ((designStoredMatrix ((r,cols),hint)).getD (e₁ x) []).getD (eB B) 0 = _
  rw [designStoredMatrix_get,he₁,heB]
  exact designGraphEdge_spec hn cols hint hS x ⟨B.val,B.property.1⟩

end
end Algo
