import Workspace.Algo.SplitBipCaseOutcomeRaw

/-! Numbering the current graph and then restoring its point rows returns
the original first-part list, in its original order, on every raw input.
This identifies the literal list used by the case extension.
-/
namespace Algo
open Babai RAM

theorem sbipCasePointList_numbered (parent : List ℕ) (z : RawSbipStored) :
    sbipCasePointList (parent,sbipNumberedDictionary z,(sbipGraphNumbered z.1).2.1) =
      z.1.1.1 := by
  apply List.ext_getElem
  · simp [sbipCasePointList,sbipDictPoints,sbipGraphNumbered]
  · intro i hi hj
    simp only [sbipCasePointList,sbipDictPoints,sbipGraphNumbered,List.getElem_map,
      List.getElem_range]
    apply sbipDictPoint_singleton
    have hin : z.1.1.2.1.length + i < (sbipGraphCaseVertices z.1).length := by
      simp only [sbipGraphCaseVertices,List.length_append]
      omega
    rw [sbipNumberedDictionary_get z ⟨_,hin⟩]
    have he : (sbipGraphCaseVertices z.1)[z.1.1.2.1.length + i] = z.1.1.1[i] := by
      simp [sbipGraphCaseVertices,List.getElem_append_right,show z.1.1.2.1.length ≤
        z.1.1.2.1.length + i from Nat.le_add_right _ _]
    rw [he]
    exact sbipVertexMembers_point z (List.getElem_mem hj)

theorem sbipCasePointList_step9 (z : RawSbipStored × (ℕ × ℕ)) :
    sbipCasePointList (z.1.1.1.1,sbipGraphStep9Dictionary z,
      (sbipGraphStep9Input (z.1.1,z.2)).2.1) = (sbipGraphConstituent (z.1.1,z.2)).1.1 :=
  sbipCasePointList_numbered _ _

theorem sbipCasePartition_step9 (z : RawSbipStored × (ℕ × ℕ)) (q : RawColPart) :
    sbipCasePartition ((z.1.1.1.1,sbipGraphStep9Dictionary z,
      (sbipGraphStep9Input (z.1.1,z.2)).2.1),q) =
      rawExtendPartition ((z.1.1.1.1,(sbipGraphConstituent (z.1.1,z.2)).1.1),q) := by
  unfold sbipCasePartition
  rw [sbipCasePointList_step9]

end Algo
