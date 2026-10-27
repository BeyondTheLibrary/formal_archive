import Workspace.Algo.SplitUpccCaseSpec

/-!
# Section 9.8: exact read-off and valid outcomes

The graph representation includes colors on all ambient points. A singleton
that is not a table vertex uses the fixed padding color of the input.
Keeping the selected color in the graph tag makes this padding recoverable.
-/

namespace Algo
open Babai RAM

section Representation
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)

open scoped Classical in
/-- Decode point colors through the original singleton/block dictionary. -/
noncomputable def upccCasePointColor (lab : RawLab) (m : ℕ) (x : ↥s) : ℕ :=
  if h : {x} ∈ X.vtxSet then labAt lab (e ⟨{x},h⟩) else if m = 0 then 1 else 0

open scoped Classical in
/-- Exact representation of the marked graph, including the complete matrix,
point colors, block colors, and the zero hint. -/
def UpccCaseGraphRep (lab : RawLab) (m : ℕ) (g : RawUpccBip)
    (Y : VColBipBlk ↥s ℕ) : Prop :=
  g.1.Nodup ∧ g.2.1.Nodup ∧
    upccCaseName₁ X e '' Set.univ = {a | a ∈ g.1} ∧
    (∀ a ∈ g.2.1, ∃ B : ↥X.blocks, upccCaseName₂ X e B = a) ∧
    Y.part₁ = X.part₁ ∧ Y.blocks ⊆ X.blocks ∧
    (∀ B : ↥X.blocks, upccCaseName₂ X e B ∈ g.2.1 ↔ B.val ∈ Y.blocks) ∧
    (∀ x, upccCasePointColor X e lab m x = Y.f x) ∧
    (∀ B, Y.g B = 0) ∧ (∀ B C, Y.h B C = 0) ∧
    g.2.2 = g.1.map (fun a => g.2.1.map (fun b =>
      if ∃ x : ↥X.Pt₁, ∃ B : ↥X.blocks, upccCaseName₁ X e x = a ∧
        upccCaseName₂ X e B = b ∧ (x.val,B.val) ∈ Y.E then 1 else 0))

/-- Section 9.8: decoding relation for the two output tags. The partition
uses the identity on first-part points. The graph keeps the original carrier. -/
def UpccCaseOutcomeRep (q : RawUpccCaseOutcome)
    (Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ))) : Prop :=
  q.1.Nodup ∧ upccCaseName₁ X e '' Set.univ = {a | a ∈ q.1} ∧ q.2.1.length = n ∧
    match q.2.2 with
    | none => ∃ P : ColoredPartition ↥(Subtype.val '' X.Pt₁) ℕ,
        Z = ⟨Subtype.val '' X.Pt₁,Sum.inl P⟩ ∧
        (∀ x : ↥X.Pt₁, labAt q.2.1 (upccCaseName₁ X e x) = P.color (mkPt x.2)) ∧
        (∀ x y : ↥X.Pt₁, LabRel q.2.1 (upccCaseName₁ X e x) (upccCaseName₁ X e y) ↔
          P.part (mkPt x.2) (mkPt y.2))
    | some (m,g) => ∃ Y : VColBipBlk ↥s ℕ,
        Z = ⟨s,Sum.inr Y⟩ ∧ g.1 = q.1 ∧ UpccCaseGraphRep X e q.2.1 m g Y

end Representation

section ReadOff
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r)

include hw hn

/-- Section 9.8, step 2: individualization reads exactly the local coloring. -/
theorem upccCaseLocalColors_spec (B : ↥X.blocks) (v : ↥X.vtxSet) :
    labAt (upccCaseLocalColors (r,upccCaseName₂ X e B)) (e v) = X.c B v := by
  change labAt (upccCellsRaw (r.1,e (X.vtxOfBlk B))) (e v) = _
  rw [upccCellsRaw_get (hn.size ▸ hw.table)]
  exact hn.color _ _

/-- Section 9.8: all retained table vertices receive the correct mark. -/
theorem upccCaseMarks_get (B : ↥X.blocks) (v : ↥X.vtxSet) :
    labAt (upccCaseMarks (r,upccCaseName₂ X e B)) (e v) =
      if X.c B v = X.mColor B then 1 else 0 := by
  have hv : (e v : ℕ) < (upccCaseLocalColors (r,upccCaseName₂ X e B)).length := by
    simpa [upccCaseLocalColors,hn.size] using (e v).isLt
  have hget := upccCaseLocalColors_spec X e hw hn B v
  simp only [labAt] at hget
  have hvm : (e v : ℕ) < ((upccCaseLocalColors (r,upccCaseName₂ X e B)).map
      (fun k => if k = upccCaseM (r,upccCaseName₂ X e B) then 1 else 0)).length := by
    simpa only [List.length_map] using hv
  change ((upccCaseLocalColors (r,upccCaseName₂ X e B)).map
    (fun k => if k = upccCaseM (r,upccCaseName₂ X e B) then 1 else 0)).getD (e v) 0 = _
  rw [List.getD_eq_getElem _ 0 hvm,List.getElem_map,
    ← List.getD_eq_getElem _ 0 hv,hget,upccCaseM_spec X e hw hn]

/-- Section 9.8: the point coloring also agrees outside the first part. -/
theorem upccCaseMarks_spec (B : ↥X.blocks) (x : ↥s) :
    upccCasePointColor X e (upccCaseMarks (r,upccCaseName₂ X e B))
      (upccCaseM (r,upccCaseName₂ X e B)) x = (X.upccBip B).f x := by
  classical
  unfold upccCasePointColor
  by_cases hv : {x} ∈ X.vtxSet
  · rw [dif_pos hv,upccCaseMarks_get X e hw hn B ⟨{x},hv⟩]
    rfl
  · rw [dif_neg hv,upccCaseM_spec X e hw hn]
    have hz : X.c B {x} = 0 := X.c_off _ _ (fun h => hv h.2)
    simp [BlkCaseObj.upccBip,hz,eq_comm]

open scoped Classical in
/-- Section 9.8: a row in the returned matrix is a row of `upccBip`. -/
theorem upccCaseRow_spec (B : ↥X.blocks) (x : ↥X.Pt₁) :
    upccCaseRow ((r,upccCaseName₂ X e B),upccCaseName₁ X e x) =
      (upccCaseBlock ((r,upccCaseName₂ X e B),upccCaseL (r,upccCaseName₂ X e B))).map
        (fun a => if ∃ C : ↥X.blocks, upccCaseName₂ X e C = a ∧
          (x.val,C.val) ∈ (X.upccBip B).E then 1 else 0) := by
  classical
  unfold upccCaseRow
  apply List.map_congr_left
  intro a ha
  obtain ⟨C,rfl⟩ := upccCaseName₂_surj hn (List.mem_of_mem_filter ha)
  have hC : C.val ∈ X.blkClass B (X.lColor B) := by
    refine ⟨C.2,?_⟩
    rw [upccCaseL_spec X e hw hn] at ha
    exact (upccCaseBlock_mem X e hn B C _).1 ha
  have hc₁ := hn.color (X.vtxOfBlk B) (X.vtxOfPt x)
  have hc₂ := hn.color (X.vtxOfBlk C) (X.vtxOfPt x)
  change binColor (r.1,(upccCaseName₂ X e B,upccCaseName₁ X e x)) = X.c B {x.val} at hc₁
  change binColor (r.1,(upccCaseName₂ X e C,upccCaseName₁ X e x)) = X.c C {x.val} at hc₂
  rw [hc₁,hc₂,upccCaseM_spec X e hw hn]
  have he : (X.c B {x.val} = X.mColor B ∧ X.c C {x.val} = X.mColor B) ↔
      ∃ D : ↥X.blocks, upccCaseName₂ X e D = upccCaseName₂ X e C ∧
        (x.val,D.val) ∈ (X.upccBip B).E := by
    constructor
    · intro h; exact ⟨C,rfl,x.2,h.1,hC,h.2⟩
    · rintro ⟨D,hD,hE⟩
      have : D = C := upccCaseName₂_injective X e hD
      subst D
      exact ⟨hE.2.1,hE.2.2.2⟩
  simp only [he]

/-- Section 9.8, step 3: every field of the raw marked graph agrees. -/
theorem upccCaseGraph_spec (B : ↥X.blocks) :
    UpccCaseGraphRep X e (upccCaseMarks (r,upccCaseName₂ X e B))
      (upccCaseM (r,upccCaseName₂ X e B))
      (upccCaseGraph (r,upccCaseName₂ X e B)) (X.upccBip B) := by
  classical
  refine ⟨hw.left_nodup,hw.right_nodup.filter _,hn.left,?_,rfl,?_,?_,
    upccCaseMarks_spec X e hw hn B,fun _ => rfl,fun _ _ => rfl,?_⟩
  · intro a ha; exact upccCaseName₂_surj hn (List.mem_of_mem_filter ha)
  · intro C hC; exact hC.1
  · intro C
    change upccCaseName₂ X e C ∈ upccCaseBlock ((r,upccCaseName₂ X e B),
      upccCaseL (r,upccCaseName₂ X e B)) ↔ C.val ∈ X.blkClass B (X.lColor B)
    rw [upccCaseL_spec X e hw hn,upccCaseBlock_mem X e hn]
    exact ⟨fun h => ⟨C.2,h⟩,And.right⟩
  · change r.2.1.map _ = r.2.1.map _
    apply List.map_congr_left
    intro a ha
    obtain ⟨x,rfl⟩ := upccCaseName₁_surj hn ha
    rw [upccCaseRow_spec X e hw hn]
    apply List.map_congr_left
    intro b _
    have he : (∃ C : ↥X.blocks, upccCaseName₂ X e C = b ∧
        (x.val,C.val) ∈ (X.upccBip B).E) ↔
        ∃ y : ↥X.Pt₁, ∃ C : ↥X.blocks,
          upccCaseName₁ X e y = upccCaseName₁ X e x ∧
          upccCaseName₂ X e C = b ∧ (y.val,C.val) ∈ (X.upccBip B).E := by
      constructor
      · rintro ⟨C,hC,hE⟩; exact ⟨x,C,rfl,hC,hE⟩
      · rintro ⟨y,C,hy,hC,hE⟩
        have : y = x := upccCaseName₁_injective X e hy
        subst y
        exact ⟨C,hC,hE⟩
    simp only [he]

end ReadOff

namespace UpccCase

/-- Section 9.8: the width is the paper's `n₂`, the number of blocks. -/
theorem widthF_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r) :
    widthF r = X.blocks.ncard := upccCaseRight_size X e hw hn

/-- Section 9.8: every valid case has at least one named version. -/
theorem widthF_pos {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    (X : UPCCObj s) {n : ℕ} (e : ↥X.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X e r) : 0 < widthF r := by
  rw [widthF_spec X e hw hn]
  exact (Set.ncard_pos (Set.toFinite _)).2 X.upccBlocks_nonempty

/-- Section 9.8 on the RAM: every named version represents a valid outcome
of the reduction `Babai.case_9_8`. -/
theorem versionF_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BlkUPCCCases Ω)) {n : ℕ} (e : ↥X.obj.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X.obj e r) (B : ↥X.obj.blocks) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
      UpccCaseOutcomeRep X.obj e (versionF (r,upccCaseName₂ X.obj e B)) Z ∧
        IsBlkImprimitiveOutcome (BlkCases.V₁ X) (BlkCases.numBlocks X) Z := by
  classical
  have hlen : (upccCaseLocalColors (r,upccCaseName₂ X.obj e B)).length = n := by
    simp [upccCaseLocalColors,hn.size]
  by_cases hsplit : upccCaseSplits (r,upccCaseName₂ X.obj e B) = true
  · have hsmall := (upccCaseSplits_spec X.obj e hw hn B).1 hsplit
    let P := kerPartition X.obj.Pt₁ (fun x => X.obj.c B {x})
    refine ⟨⟨Subtype.val '' X.obj.Pt₁,Sum.inl P⟩,?_,?_,?_⟩
    · simp only [versionF,hsplit,ite_true,UpccCaseOutcomeRep]
      refine ⟨hw.left_nodup,hn.left,hlen,P,rfl,?_,?_⟩
      · intro x
        exact upccCaseLocalColors_spec X.obj e hw hn B (X.obj.vtxOfPt x)
      · intro x y
        change labAt _ _ = labAt _ _ ↔ X.obj.c B {x.val} = X.obj.c B {y.val}
        dsimp only [upccCaseName₁]
        rw [upccCaseLocalColors_spec X.obj e hw hn B (X.obj.vtxOfPt x),
          upccCaseLocalColors_spec X.obj e hw hn B (X.obj.vtxOfPt y)]
        rfl
    · rfl
    · apply kerPartition_isAlphaPartition (k := X.obj.Pt₁.ncard / 2)
      · intro x hx
        have := hsmall (X.obj.c B {x})
        change 2 * {y : ↥X.car | X.obj.part₁ y ∧ X.obj.c B {y} = X.obj.c B {x}}.ncard ≤
          X.obj.Pt₁.ncard at this
        change {y : ↥X.car | X.obj.part₁ y ∧ X.obj.c B {y} = X.obj.c B {x}}.ncard ≤ _
        omega
      · have h : 2 * (X.obj.Pt₁.ncard / 2) ≤ X.obj.Pt₁.ncard := by omega
        have hR : (2 : ℝ) * (X.obj.Pt₁.ncard / 2 : ℕ) ≤ (X.obj.Pt₁.ncard : ℝ) := by
          exact_mod_cast h
        linarith
  · have hbig : ∃ k, X.obj.IsBigColor₂ B k := by
      by_contra h
      apply hsplit
      apply (upccCaseSplits_spec X.obj e hw hn B).2
      intro k
      have : ¬ X.obj.IsBigColor₂ B k := fun hk => h ⟨k,hk⟩
      exact Nat.le_of_not_gt this
    refine ⟨⟨X.car,Sum.inr (X.obj.upccBip B)⟩,?_,rfl,
      (X.obj.isSmallColor₂_lColor B.2).2,X.obj.upccBip_defect₁ B.2 hbig⟩
    simp only [versionF,hsplit,ite_false,UpccCaseOutcomeRep]
    refine ⟨hw.left_nodup,hn.left,?_,X.obj.upccBip B,rfl,rfl,
      upccCaseGraph_spec X.obj e hw hn B⟩
    simpa [upccCaseMarks] using hlen

/-- Section 9.8: the outcome theorem for each raw index below the width. -/
theorem versionF_spec_index {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Pt (BlkUPCCCases Ω)) {n : ℕ} (e : ↥X.obj.vtxSet ≃ Fin n)
    {r : RawUpccCase} (hw : r.WF) (hn : UpccCaseNames X.obj e r) {i : ℕ}
    (hi : i < widthF r) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
      UpccCaseOutcomeRep X.obj e (versionF (r,i)) Z ∧
        IsBlkImprimitiveOutcome (BlkCases.V₁ X) (BlkCases.numBlocks X) Z := by
  obtain ⟨B,hB⟩ := upccCaseName₂_surj hn ((hw.right_names i).2 hi)
  simpa only [hB] using versionF_spec X e hw hn B

end UpccCase
end Algo
