import Workspace.Algo.SplitUpccStored
import Workspace.Algo.SplitNamedLists

/-! Position bijections follow the lists returned by the UPCC branch.
The dictionary restores original point names while each retained block
keeps its complete original point set.
-/
namespace Algo
open Babai RAM
open scoped Classical

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) (point : ↥s → ℕ) (d : List (List ℕ))
    (e : ↥X.vtxSet ≃ Fin d.length)
    (hd : SbipVertexDictionary X.vtxSet point d e) (hp : Function.Injective point)

include hd hp in
theorem upccStored_point (x : ↥X.Pt₁) :
    sbipDictPoint (d,upccCaseName₁ X e x) = point x.val :=
  sbipVertexDictionary_point hd hp x.val (X.vtxOfPt x).property

include hd in
theorem upccStored_block_nodup (B : ↥X.blocks) :
    (sbipDictGet (d,upccCaseName₂ X e B)).Nodup := by
  rw [upccCaseName₂,sbipDictGet_get]
  exact hd.row_nodup (X.vtxOfBlk B)

include hd in
theorem upccStored_block_mem (B : ↥X.blocks) (a : ℕ) :
    a ∈ sbipDictGet (d,upccCaseName₂ X e B) ↔ ∃ x ∈ B.val,point x = a := by
  rw [upccCaseName₂,sbipDictGet_get]
  exact hd.row_mem (X.vtxOfBlk B) a

variable {lab : RawLab} {m : ℕ} {g : RawUpccBip} {Y : VColBipBlk ↥s ℕ}
    (hr : UpccCaseGraphRep X e lab m g Y)

include hr in
theorem upccStored_point_equiv_exists :
    ∃ e₁ : ↥X.Pt₁ ≃ Fin g.1.length,∀ x,g.1[(e₁ x).val] = upccCaseName₁ X e x := by
  apply splitNameEquiv_exists (upccCaseName₁ X e) (upccCaseName₁_injective X e) g.1 hr.1
  intro a
  rw [← show a ∈ upccCaseName₁ X e '' Set.univ ↔ a ∈ g.1 from
    (Set.ext_iff.1 hr.2.2.1 a)]
  simp

include hr in
theorem upccStored_block_equiv_exists :
    ∃ hsub : Y.blocks ⊆ X.blocks,∃ eB : ↥Y.blocks ≃ Fin g.2.1.length,
      ∀ B,g.2.1[(eB B).val] = upccCaseName₂ X e ⟨B.val,hsub B.property⟩ := by
  obtain ⟨_,hnd,_,hcols,_,hsub,hmem,_⟩ := hr
  refine ⟨hsub,?_⟩
  refine splitNameEquiv_exists
    (fun B : ↥Y.blocks => upccCaseName₂ X e ⟨B.val,hsub B.property⟩) ?_ g.2.1 hnd ?_
  · intro B C he
    exact Subtype.ext (congrArg (fun B : ↥X.blocks => B.val)
      (upccCaseName₂_injective X e he))
  · intro a
    constructor
    · intro ha
      obtain ⟨B,rfl⟩ := hcols a ha
      exact ⟨⟨B.val,(hmem B).1 ha⟩,rfl⟩
    · rintro ⟨B,rfl⟩
      exact (hmem ⟨B.val,hsub B.property⟩).2 B.property

include hr hd hp in
theorem upccStored_left_nodup : (sbipDictPoints (d,g.1)).Nodup := by
  apply hr.1.map_on
  intro a ha b hb he
  have hname (u : ℕ) (hu : u ∈ g.1) : ∃ x : ↥X.Pt₁,upccCaseName₁ X e x = u := by
    have hm : u ∈ upccCaseName₁ X e '' Set.univ := hr.2.2.1.symm ▸ hu
    simpa only [Set.mem_image,Set.mem_univ,true_and] using hm
  obtain ⟨x,rfl⟩ := hname a ha
  obtain ⟨y,rfl⟩ := hname b hb
  rw [upccStored_point X point d e hd hp x,upccStored_point X point d e hd hp y] at he
  exact congrArg (upccCaseName₁ X e) (Subtype.ext (hp he))

end
end Algo
