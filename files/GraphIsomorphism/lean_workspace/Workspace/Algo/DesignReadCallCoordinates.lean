import Workspace.Algo.DesignReadFamilyRelabel
import Workspace.Algo.SplitUpccCaseTransport
import Workspace.Algo.SplitBipLinkTransport

/-! # Section 9.7 keeps compact block coordinates under relabeling

The two stored vertex lists move in their original order. Therefore their
positions, neighborhood rows, smaller rank, and relation labels stay the
same. Only the contents of size witnesses may change.
-/
namespace Algo
open Babai RAM

section
variable {r : RawUpccCase} {π : RawPerm} (hw : r.WF) (hπ : RawPerm.WF r.1.1.length π)
local notation "r'" => UpccCase.relabelInput π r
include hw hπ

theorem designBip_relabel : designBip r' = splitRelabelBipRaw (π,designBip r) := by
  unfold designBip
  rw [show sbipFirstInvolved r' = sbipFirstInvolved r from
    sbipFirstInvolved_relabel hw.table hπ r.2.1 r.2.2
      (fun _ h => hw.left_lt h) (fun _ h => hw.right_lt h)]
  rfl

theorem designNeighborhood_relabel {u : ℕ} (hu : u < r.2.1.length) :
    splitNeighborhoodRow (designBip r',u) = splitNeighborhoodRow (designBip r,u) := by
  rw [designBip_relabel hw hπ]
  unfold splitNeighborhoodRow
  rw [splitRelabelBipRaw_right_length]
  apply List.filter_congr
  intro v hv
  exact bipAdjRaw_relabel (z := designBip r) hw.table hπ
    (fun _ h => hw.left_lt h) (fun _ h => hw.right_lt h) hu (List.mem_range.mp hv)

theorem designDegree_relabel (hne : 0 < r.2.1.length) : designDegree r' = designDegree r :=
  congrArg List.length (designNeighborhood_relabel hw hπ hne)

theorem designRank_relabel (hne : 0 < r.2.1.length) : designRank r' = designRank r := by
  unfold designRank
  rw [designDegree_relabel hw hπ hne]
  simp only [UpccCase.relabelInput,length_permList]

theorem designCase3a_relabel (hne : 0 < r.2.1.length) : designCase3a r' = designCase3a r := by
  simp only [designCase3a,designSmallRank,designRankWitness_length]
  rw [designRank_relabel hw hπ hne]
  simp only [UpccCase.relabelInput,length_permList]

theorem designLabels_relabel (hne : 0 < r.2.1.length) : designLabels r' = designLabels r := by
  have hd : designUseDirect r' = designUseDirect r := by
    unfold designUseDirect
    rw [designDegree_relabel hw hπ hne]
    simp only [UpccCase.relabelInput,length_permList]
  unfold designLabels
  rw [show r'.2.1.length = r.2.1.length by simp [UpccCase.relabelInput]]
  apply List.map_congr_left
  intro u hu
  simp only [designLabel,hd,designNeighborhood_relabel hw hπ (List.mem_range.mp hu)]
  simp only [designComplementRow,UpccCase.relabelInput,length_permList]

theorem designCallWitness_relabel_length (hne : 0 < r.2.1.length) :
    (designCallWitness r').length = (designCallWitness r).length := by
  have hs : designSkel r'.2.1 = designSkel r.2.1 := by
    simp only [designSkel,designSkelCandidates,designSkelPass,UpccCase.relabelInput,length_permList]
  simp only [designCallWitness,designCase3a_relabel hw hπ hne]
  split
  · exact (designRankWitness_length r').trans
      ((designRank_relabel hw hπ hne).trans (designRankWitness_length r).symm)
  · simp only [designSkelWitness,List.length_take,designSkelPadding_length]
    rw [hs]
    simp only [UpccCase.relabelInput,length_permList]

end
end Algo
