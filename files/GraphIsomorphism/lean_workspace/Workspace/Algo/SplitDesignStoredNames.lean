import Workspace.Algo.SplitDesignStored
import Workspace.Algo.SplitBipPackSpec
import Workspace.Algo.SplitBipStoredDictionary

/-! The design return uses the stored order of first-part points and
selected blocks. Its new names describe the same original points and sets.
The position bijections below are only specifications of those lists. -/
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

include hd hp h₁ in
theorem designStored_point (x : ↥X.Pt₁) : sbipDictPoint (d,name₁ x) = point x.val := by
  rw [← h₁]
  exact sbipVertexDictionary_point hd hp x.val (X.vtxOfPt x).property

include hd h₂ in
theorem designStored_block_nodup (B : ↥X.blocks) : (sbipDictGet (d,name₂ B)).Nodup := by
  rw [← h₂,sbipDictGet_get]
  exact hd.row_nodup (X.vtxOfBlk B)

include hd h₂ in
theorem designStored_block_mem (B : ↥X.blocks) (a : ℕ) :
    a ∈ sbipDictGet (d,name₂ B) ↔ ∃ x ∈ B.val, point x = a := by
  rw [← h₂,sbipDictGet_get]
  exact hd.row_mem (X.vtxOfBlk B) a

include hn hd hp h₁ in
theorem designStored_left_mem (a : ℕ) :
    a ∈ sbipDictPoints (d,r.2.1) ↔ ∃ x : ↥X.Pt₁, point x.val = a := by
  constructor
  · intro ha
    obtain ⟨u,hu,hu'⟩ := List.mem_map.1 ha
    obtain ⟨x,rfl⟩ := (hn.left u).1 hu
    exact ⟨x,(designStored_point point d e hd hp h₁ x).symm.trans hu'⟩
  · rintro ⟨x,rfl⟩
    exact List.mem_map.2 ⟨name₁ x,(hn.left _).2 ⟨x,rfl⟩,
      designStored_point point d e hd hp h₁ x⟩

include hn hw hd hp h₁ in
theorem designStored_left_nodup : (sbipDictPoints (d,r.2.1)).Nodup := by
  apply hw.left_nodup.map_on
  intro a ha b hb he
  obtain ⟨x,rfl⟩ := (hn.left a).1 ha
  obtain ⟨y,rfl⟩ := (hn.left b).1 hb
  rw [designStored_point point d e hd hp h₁ x,designStored_point point d e hd hp h₁ y] at he
  exact congrArg name₁ (Subtype.ext (hp he))

include hn hw in
theorem designStored_point_equiv_exists :
    ∃ e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length, ∀ x, r.2.1[(e₁ x).val] = name₁ x :=
  splitNameEquiv_exists name₁ hn.inj₁ r.2.1 hw.left_nodup hn.left

variable (S : Set (Set ↥s)) (H : Set ↥s → Set ↥s → ℕ) (cols : List ℕ)
    (hnd : cols.Nodup) (hcols : ∀ a ∈ cols, a ∈ r.2.2)
    (hS : ∀ B : ↥X.blocks, name₂ B ∈ cols ↔ B.val ∈ S)

include hn hnd hcols hS in
theorem designStored_block_equiv_exists :
    ∃ eB : ↥(X.linkGraph.restrictBlkHint S H).blocks ≃ Fin cols.length,
      ∀ B, cols[(eB B).val] = name₂ ⟨B.val,B.property.1⟩ := by
  refine splitNameEquiv_exists (fun B : ↥(X.linkGraph.restrictBlkHint S H).blocks =>
    name₂ ⟨B.val,B.property.1⟩) ?_ cols hnd ?_
  · intro B C he
    exact Subtype.ext (congrArg (fun B : ↥X.blocks => B.val) (hn.inj₂ he))
  · intro a
    constructor
    · intro ha
      obtain ⟨B,rfl⟩ := (hn.right a).1 (hcols a ha)
      exact ⟨⟨B.val,B.property,(hS B).1 ha⟩,rfl⟩
    · rintro ⟨B,rfl⟩
      exact (hS ⟨B.val,B.property.1⟩).2 B.property.2

end
end Algo
