import Workspace.Algo.SplitBipCaseOutcomeRaw

/-! A case first part is a list of singleton table vertices. Restoring
those rows gives exactly its original point names, in the same order.
-/
namespace Algo
open Babai RAM

section
variable {α : Type} {W : Set α} (point : α → ℕ) (name : ↥W → ℕ)
    (d : List (List ℕ)) (l : List ℕ)
    (hrow : ∀ x,sbipDictPoint (d,name x) = point x.val)
    (hcover : ∀ a,a ∈ l ↔ ∃ x,name x = a)
include hrow hcover

theorem sbipCasePointList_mem (parent : List ℕ) (a : ℕ) :
    a ∈ sbipCasePointList (parent,d,l) ↔ ∃ x : ↥W,point x.val = a := by
  constructor
  · intro ha
    obtain ⟨u,hu,hea⟩ := List.mem_map.1 ha
    obtain ⟨x,rfl⟩ := (hcover u).1 hu
    exact ⟨x,(hrow x).symm.trans hea⟩
  · rintro ⟨x,rfl⟩
    exact List.mem_map.2 ⟨name x,(hcover _).2 ⟨x,rfl⟩,hrow x⟩

theorem sbipCasePointList_nodup (parent : List ℕ) (hl : l.Nodup)
    (hp : Set.InjOn point W) : (sbipCasePointList (parent,d,l)).Nodup := by
  apply hl.map_on
  intro a ha b hb he
  obtain ⟨x,rfl⟩ := (hcover a).1 ha
  obtain ⟨y,rfl⟩ := (hcover b).1 hb
  rw [hrow,hrow] at he
  exact congrArg name (Subtype.ext (hp x.property y.property he))

theorem sbipCasePointList_parent_mem {V : Set α} (hWV : W ⊆ V)
    (hp : Set.InjOn point V) (parent : List ℕ) (x : ↥V) :
    point x.val ∈ sbipCasePointList (parent,d,l) ↔ x.val ∈ W := by
  rw [sbipCasePointList_mem point name d l hrow hcover]
  constructor
  · rintro ⟨y,hy⟩
    exact hp (hWV y.property) x.property hy ▸ y.property
  · intro hx
    exact ⟨⟨x.val,hx⟩,rfl⟩

omit hcover in
theorem sbipCasePointList_get (parent : List ℕ) (e : ↥W ≃ Fin l.length)
    (he : ∀ x,l[(e x).val] = name x) (x : ↥W) :
    (sbipCasePointList (parent,d,l))[(e x).val]'(by simpa [sbipCasePointList,sbipDictPoints]
      using (e x).isLt) = point x.val := by
  simp only [sbipCasePointList,sbipDictPoints,List.getElem_map,he,hrow]

end
end Algo
