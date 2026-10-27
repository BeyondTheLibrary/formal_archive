import Workspace.Algo.SplitBipPackSpec

/-! Packing keeps the point-first order used for hint positions.
These exact indices let a case carry its hint into the next turn. -/
namespace Algo
open Babai RAM

theorem sbipPackIndex_point (z : RawSbipPack) (hnd : (sbipPackVertices z).Nodup)
    (i : Fin z.1.2.length) : rawLetterIndex (sbipPackVertices z,z.1.2[i.val]) = i := by
  have hi : i.val < (sbipPackVertices z).length := by
    simp only [sbipPackVertices,List.length_append]; omega
  have he : (sbipPackVertices z)[i.val]'hi = z.1.2[i.val] :=
    List.getElem_append_left i.isLt
  have hh := sbipLetterIndex_get hnd ⟨i.val,hi⟩
  simpa only [he] using hh

theorem sbipPackIndex_block (z : RawSbipPack) (hnd : (sbipPackVertices z).Nodup)
    (i : Fin z.2.1.length) :
    rawLetterIndex (sbipPackVertices z,z.1.1.length+i) = z.1.2.length+i := by
  have hi : z.1.2.length+i.val < (sbipPackVertices z).length := by
    simp only [sbipPackVertices,List.length_append,sbipPackBlocks_length]
    omega
  have he : (sbipPackVertices z)[z.1.2.length+i.val]'hi = z.1.1.length+i := by
    change (z.1.2 ++ sbipPackBlocks z)[z.1.2.length+i.val]'hi = _
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,sbipPackBlocks_get]
  have hh := sbipLetterIndex_get hnd ⟨z.1.2.length+i.val,hi⟩
  simpa only [he] using hh

end Algo
