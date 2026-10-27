import Workspace.Algo.SplitUpccCaseOutcome

/-!
# Section 9.8: shifted canonicity

Both part lists retain their transported order. The individualized name
moves with the permutation. A numbering of the second part by `[0,n₂)`
gives the indexed family. Relabelings preserving that interval preserve
this numbering convention. The raw equality below also holds for other
ambient permutations.
-/

namespace Algo
open Babai RAM

namespace RawUpccCase.WF

theorem left_lt {r : RawUpccCase} (h : r.WF) {a : ℕ} (ha : a ∈ r.2.1) :
    a < r.1.1.length :=
  (h.table.domMem a).1 ((h.cover a).1 (List.mem_append_left _ ha))

theorem right_lt {r : RawUpccCase} (h : r.WF) {a : ℕ} (ha : a ∈ r.2.2) :
    a < r.1.1.length :=
  (h.table.domMem a).1 ((h.cover a).1 (List.mem_append_right _ ha))

end RawUpccCase.WF

namespace UpccCase

/-- Section 9.8: transport the table and the two part lists. -/
def relabelInput (π : RawPerm) (r : RawUpccCase) : RawUpccCase :=
  (relabelWL (π,r.1),permList π r.2.1,permList π r.2.2)

/-- Section 9.8: move vertex names and point-color positions. Colors and
matrix entries stay fixed. The dominant-color header also stays fixed. -/
def relabelOutcome (π : RawPerm) (q : RawUpccCaseOutcome) : RawUpccCaseOutcome :=
  (permList π q.1,upccRelabelColors π q.2.1,
    q.2.2.map (fun g => (g.1,upccRelabelBip π g.2)))

@[simp] theorem widthF_relabel (π : RawPerm) (r : RawUpccCase) :
    widthF (relabelInput π r) = widthF r := by simp [widthF,relabelInput]

end UpccCase

section Transport
variable {r : RawUpccCase} {π : RawPerm} (hw : r.WF)
    (hπ : RawPerm.WF r.1.1.length π) (x : Fin r.1.1.length)

/-- A local cell transports as an ordered list of names. -/
theorem upccCaseCell_relabel {p : RawConfig} {n : ℕ} (hp : RawWL.WF n 2 p)
    {π : RawPerm} (hπ : RawPerm.WF n π) (l : List ℕ)
    (hl : ∀ a ∈ l, a < n) (x : Fin n) (k : ℕ) :
    upccCaseCell (((relabelWL (π,p),permList π l),rawApply (π,x)),k) =
      permList π (upccCaseCell (((p,l),x),k)) := by
  simp only [upccCaseCell,permList,List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  simp only [Function.comp_def,binColor_relabel hp hπ x.isLt (hl a ha)]

include hw hπ

theorem upccCaseLink_relabel (k : ℕ) :
    upccCaseLink ((UpccCase.relabelInput π r,rawApply (π,x)),k) =
      permList π (upccCaseLink ((r,x),k)) :=
  upccCaseCell_relabel hw.table hπ _ (fun _ ha => hw.left_lt ha) x k

theorem upccCaseBlock_relabel (k : ℕ) :
    upccCaseBlock ((UpccCase.relabelInput π r,rawApply (π,x)),k) =
      permList π (upccCaseBlock ((r,x),k)) :=
  upccCaseCell_relabel hw.table hπ _ (fun _ ha => hw.right_lt ha) x k

theorem upccCaseBig_relabel (k : ℕ) :
    upccCaseBig ((UpccCase.relabelInput π r,rawApply (π,x)),k) =
      upccCaseBig ((r,x),k) := by
  simp only [upccCaseBig]
  rw [upccCaseLink_relabel hw hπ x]
  simp only [UpccCase.relabelInput,length_permList]

theorem upccCaseSmall_relabel (k : ℕ) :
    upccCaseSmall ((UpccCase.relabelInput π r,rawApply (π,x)),k) =
      upccCaseSmall ((r,x),k) := by
  have hf : (permList π (upccCaseBlock ((r,x),k))).filter
      (fun a => decide (a ≠ rawApply (π,x))) =
      permList π ((upccCaseBlock ((r,x),k)).filter (fun a => decide (a ≠ x))) := by
    simp only [permList,List.filter_map]
    congr 1
    apply List.filter_congr
    intro a ha
    have ha' := hw.right_lt (List.mem_of_mem_filter ha)
    simp only [Function.comp_def]
    exact decide_eq_decide.2 (not_congr ⟨rawApply_inj hπ ha' x.isLt,fun h => congrArg (fun a => rawApply (π,a)) h⟩)
  simp only [upccCaseSmall]
  rw [upccCaseBlock_relabel hw hπ x,hf]
  simp only [UpccCase.relabelInput,permList,List.length_map,List.isEmpty_map]

theorem upccCaseCandidates_relabel {test : (RawUpccCase × ℕ) × ℕ → Bool}
    (ht : ∀ k, test ((UpccCase.relabelInput π r,rawApply (π,x)),k) = test ((r,x),k)) :
    upccCaseCandidates test (UpccCase.relabelInput π r,rawApply (π,x)) =
      upccCaseCandidates test (r,x) := by
  simp only [upccCaseCandidates,UpccCase.relabelInput,binaryColorsRaw_relabel hw.table hπ]
  exact List.filter_congr (fun k _ => ht k)

theorem upccCaseM_relabel :
    upccCaseM (UpccCase.relabelInput π r,rawApply (π,x)) = upccCaseM (r,x) := by
  rw [upccCaseM,upccCaseCandidates_relabel hw hπ x (upccCaseBig_relabel hw hπ x)]
  rfl

theorem upccCaseL_relabel :
    upccCaseL (UpccCase.relabelInput π r,rawApply (π,x)) = upccCaseL (r,x) := by
  rw [upccCaseL,upccCaseCandidates_relabel hw hπ x (upccCaseSmall_relabel hw hπ x)]
  rfl

theorem upccCaseSplits_relabel :
    upccCaseSplits (UpccCase.relabelInput π r,rawApply (π,x)) = upccCaseSplits (r,x) := by
  rw [upccCaseSplits,upccCaseCandidates_relabel hw hπ x (upccCaseBig_relabel hw hπ x)]
  rfl

theorem upccCaseLocalColors_relabel :
    upccCaseLocalColors (UpccCase.relabelInput π r,rawApply (π,x)) =
      upccRelabelColors π (upccCaseLocalColors (r,x)) :=
  upccCellsRaw_relabel hw.table hπ x

omit hw hπ in
/-- Reading a mapped labelling at an existing position. -/
theorem upccCaseLabAt_map (lab : RawLab) (f : ℕ → ℕ) {u : ℕ} (hu : u < lab.length) :
    labAt (lab.map f) u = f (labAt lab u) := by
  have hm : u < (lab.map f).length := by simpa using hu
  simp only [labAt,List.getD_eq_getElem _ 0 hm,List.getElem_map,
    List.getD_eq_getElem _ 0 hu]

omit hw hπ in
/-- Value maps commute with relocation of color positions. -/
theorem upccCaseRelabelColors_map {n : ℕ} {π : RawPerm} (hπ : RawPerm.WF n π)
    (lab : RawLab) (hlen : lab.length = n) (f : ℕ → ℕ) :
    (upccRelabelColors π lab).map f = upccRelabelColors π (lab.map f) := by
  simp only [upccRelabelColors,List.length_map,List.map_map]
  apply List.map_congr_left
  intro u hu
  have hi : invAt π u < lab.length := by
    rw [hlen]
    exact invAt_lt hπ (by simpa [hlen] using List.mem_range.1 hu)
  exact (upccCaseLabAt_map lab f hi).symm

theorem upccCaseMarks_relabel :
    upccCaseMarks (UpccCase.relabelInput π r,rawApply (π,x)) =
      upccRelabelColors π (upccCaseMarks (r,x)) := by
  rw [upccCaseMarks,upccCaseLocalColors_relabel hw hπ x,upccCaseM_relabel hw hπ x]
  exact upccCaseRelabelColors_map hπ _ (by simp [upccCaseLocalColors]) _

theorem upccCaseRow_relabel {u : ℕ} (hu : u ∈ r.2.1) :
    upccCaseRow ((UpccCase.relabelInput π r,rawApply (π,x)),rawApply (π,u)) =
      upccCaseRow ((r,x),u) := by
  simp only [upccCaseRow,upccCaseL_relabel hw hπ x,upccCaseBlock_relabel hw hπ x,
    permList,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro v hv
  have hv' := hw.right_lt (List.mem_of_mem_filter hv)
  rw [upccCaseM_relabel hw hπ x]
  simp only [UpccCase.relabelInput,binColor_relabel hw.table hπ x.isLt (hw.left_lt hu),
    binColor_relabel hw.table hπ hv' (hw.left_lt hu)]

theorem upccCaseGraph_relabel :
    upccCaseGraph (UpccCase.relabelInput π r,rawApply (π,x)) =
      upccRelabelBip π (upccCaseGraph (r,x)) := by
  simp only [upccCaseGraph,upccRelabelBip]
  rw [upccCaseL_relabel hw hπ x,upccCaseBlock_relabel hw hπ x]
  simp only [UpccCase.relabelInput,permList,List.map_map]
  congr 2
  apply List.map_congr_left
  intro u hu
  exact upccCaseRow_relabel hw hπ x hu

end Transport

namespace UpccCase

/-- Relabelings within the two parts preserve the raw input convention.
The second part uses the first `n₂` names, so its action also acts on indices. -/
theorem relabelInput_wf {r : RawUpccCase} {π : RawPerm} (hw : r.WF)
    (hπ : RawPerm.WF r.1.1.length π)
    (hcut : ∀ a < r.1.1.length, rawApply (π,a) < widthF r ↔ a < widthF r) :
    (relabelInput π r).WF := by
  have hl : (permList π r.2.1).Nodup :=
    List.Nodup.map_on (fun a ha b hb => rawApply_inj hπ (hw.left_lt ha) (hw.left_lt hb))
      hw.left_nodup
  have hr : (permList π r.2.2).Nodup :=
    List.Nodup.map_on (fun a ha b hb => rawApply_inj hπ (hw.right_lt ha) (hw.right_lt hb))
      hw.right_nodup
  have hn : r.2.2.length ≤ r.1.1.length :=
    (List.subperm_of_subset hw.right_nodup (fun a ha =>
      (hw.cover a).1 (List.mem_append_right _ ha))).length_le
  refine ⟨?_,hl,hr,?_,?_,?_⟩
  · simpa only [relabelInput,relabelWL_fst,length_permList] using relabelWL_wf hπ hw.table
  · intro a ha hb
    obtain ⟨u,hu,rfl⟩ := List.mem_map.1 ha
    obtain ⟨v,hv,he⟩ := List.mem_map.1 hb
    have huv := rawApply_inj hπ (hw.right_lt hv) (hw.left_lt hu) he
    subst v
    exact hw.disjoint u hu hv
  · intro a
    change a ∈ permList π r.2.1 ++ permList π r.2.2 ↔ a ∈ (relabelWL (π,r.1)).1
    rw [relabelWL_fst]
    simp only [permList,← List.map_append,List.mem_map]
    exact exists_congr (fun u => and_congr_left (fun _ => hw.cover u))
  · intro a
    change a ∈ permList π r.2.2 ↔ a < (permList π r.2.2).length
    rw [length_permList]
    constructor
    · intro ha
      obtain ⟨u,hu,rfl⟩ := List.mem_map.1 ha
      exact (hcut u (hw.right_lt hu)).2 ((hw.right_names u).1 hu)
    · intro ha
      have han := lt_of_lt_of_le ha hn
      apply List.mem_map.2
      refine ⟨invAt π a,?_,rawApply_invAt hπ han⟩
      apply (hw.right_names _).2
      apply (hcut _ (invAt_lt hπ han)).1
      simpa only [rawApply_invAt hπ han] using ha

/-- Section 9.8: transport the input and the individualized index together.
This is equality of whole raw outcomes, including the order of every row. -/
theorem versionF_relabel {r : RawUpccCase} {π : RawPerm} (hw : r.WF)
    (hπ : RawPerm.WF r.1.1.length π) (x : Fin r.1.1.length) :
    versionF (relabelInput π r,rawApply (π,x)) = relabelOutcome π (versionF (r,x)) := by
  simp only [versionF,upccCaseSplits_relabel hw hπ x,
    upccCaseLocalColors_relabel hw hπ x,upccCaseMarks_relabel hw hπ x,
    upccCaseM_relabel hw hπ x,upccCaseGraph_relabel hw hπ x]
  by_cases hs : upccCaseSplits (r,x) = true <;>
    simp [hs,relabelInput,relabelOutcome]

end UpccCase
end Algo
