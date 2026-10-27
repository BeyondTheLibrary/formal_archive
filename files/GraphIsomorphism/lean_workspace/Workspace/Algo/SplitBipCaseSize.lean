import Workspace.Algo.SplitBipStorageSize
import Workspace.Algo.SplitBipTurnInvariant

/-! Step 9's fresh table is bounded by the original point count. Thus
reading a new case does not repeatedly compose the previous input's
polynomial storage bound. -/
namespace Algo
open RAM Babai

theorem sbipGraphConstituent_left_length (z : RawSbipGraph × (ℕ × ℕ)) :
    (sbipGraphConstituent z).1.1.length ≤ z.1.1.1.length := List.length_filter_le _ _

theorem sbipGraphConstituent_right_length (z : RawSbipGraph × (ℕ × ℕ)) :
    (sbipGraphConstituent z).1.2.1.length ≤ z.1.1.2.1.length := List.length_filter_le _ _

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem first_length_le : I.1.2.1.1.1.1.length ≤ m :=
  length_le_of_nodup_lt h.left_nodup h.point_lt

theorem blocks_le : sbipNodeBlocks I ≤ m := by
  rw [h.block_count]
  exact (BipBlockInputs.numBlocks_le_ncard X).trans
    (by simpa using Set.ncard_le_card (s := X.car))

theorem case_degree_le : (sbipTurnCase I.1).2.1.1.1.length ≤ 2*m := by
  change (sbipGraphCaseTable (sbipGraphConstituent (sbipTurnGraphInput I.1))).1.length ≤ _
  rw [sbipGraphCaseTable_length]
  simp only [sbipGraphCaseVertices, List.length_append]
  have hl := sbipGraphConstituent_left_length (sbipTurnGraphInput I.1)
  have hr := sbipGraphConstituent_right_length (sbipTurnGraphInput I.1)
  have hp := h.first_length_le
  have hb := h.blocks_le
  change (sbipTurnGraphInput I.1).1.1.1.length ≤ m at hp
  change (sbipTurnGraphInput I.1).1.1.2.1.length ≤ m at hb
  omega

theorem case_size : Enc.size (sbipTurnCase I.1).2.1 ≤ sbipCaseSizeBound (2*m) :=
  (sbipCase_size (sbipGraphStep9Input_wf (sbipTurnGraphInput I.1))).trans
    (mono_sbipCaseSizeBound h.case_degree_le)

theorem case_dictionary_size (hd : ¬ AllClassesSmall X) :
    Enc.size (sbipTurnCase I.1).1.1.2 ≤ sbipDictionaryBound m := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,_,h9⟩ := sbipGraphStep9Dictionary_equiv_exists X name
    (fun x => x.val.val) I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  have hb := h9.rows_bounded (m := m) (fun x => x.val.isLt)
  apply sbipDictionary_size m _ _ hb.1 hb.2
  change (sbipGraphStep9Dictionary I.1.2).length ≤ _
  rw [sbipGraphStep9Dictionary_length]
  have hh := h.case_degree_le
  change (sbipGraphCaseTable (sbipGraphConstituent (sbipTurnGraphInput I.1))).1.length ≤ _ at hh
  rwa [sbipGraphCaseTable_length] at hh

end SbipNodeRep
end Algo
