import Workspace.Algo.SplitBipStep9Transport

/-!
# Section 9.4: the second refinement in the numbering used by Section 9.8

Put the second part first in the vertex list. Its positions are then exactly
the allowed version indices of `UpccCase.versionF`.
-/

namespace Algo
open Babai RAM

/-- The second refinement, with second-part positions before first-part positions. -/
def sbipStep9Table (r : RawSbipRefine) : RawConfig :=
  sbipStep3 (sbipIndexed (sbipStep8Initial r,r.1.2.2 ++ r.1.2.1))

theorem sbipPoly_step9Table : PolyFun sbipStep9Table :=
  (sbipPoly_step8Initial.pair
    (((polyFun_fst.comp polyFun_snd).comp polyFun_snd).pair
      ((polyFun_fst.comp polyFun_snd).comp polyFun_fst) |>.comp polyFun_append)).comp
    (sbipPoly_indexed.comp sbipPoly_step3)

/-- Prepare the whole input of step 9, including the two new part lists. -/
def sbipStep9Input (r : RawSbipRefine) : RawUpccCase :=
  (sbipStep9Table r,
    (List.range r.1.2.1.length).map (fun i => r.1.2.2.length + i),
    List.range r.1.2.2.length)

theorem sbipPoly_step9Input : PolyFun sbipStep9Input := by
  have hl : PolyFun (fun r : RawSbipRefine => r.1.2.1) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_fst
  have hr : PolyFun (fun r : RawSbipRefine => r.1.2.2) :=
    (polyFun_fst.comp polyFun_snd).comp polyFun_snd
  exact sbipPoly_step9Table.pair
    ((((hr.comp polyFun_length).pair (hl.comp polyFun_rangeLength)).comp
      (PolyFun.mapParam polyFun_add)).pair (hr.comp polyFun_rangeLength))

@[simp] theorem sbipStep9Table_length (r : RawSbipRefine) :
    (sbipStep9Table r).1.length = (r.1.2.2 ++ r.1.2.1).length := by
  simp [sbipStep9Table,sbipStep3,fst_rawWLStable,sbipIndexed]

theorem sbipStep9Input_left (r : RawSbipRefine) (a : ℕ) :
    a ∈ (sbipStep9Input r).2.1 ↔ r.1.2.2.length ≤ a ∧ a < (r.1.2.2 ++ r.1.2.1).length := by
  simp only [sbipStep9Input,List.mem_map,List.mem_range,List.length_append]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hlo,hhi⟩
    exact ⟨a - r.1.2.2.length,by omega,by omega⟩

@[simp] theorem sbipStep9Input_right (r : RawSbipRefine) (a : ℕ) :
    a ∈ (sbipStep9Input r).2.2 ↔ a < r.1.2.2.length := List.mem_range

/-- The prepared encoding is valid on every input, including junk. -/
theorem sbipStep9Input_wf (r : RawSbipRefine) : (sbipStep9Input r).WF := by
  have ht := sbipStep3_wf (sbipIndexed_wf (sbipStep8Initial r) (r.1.2.2 ++ r.1.2.1))
  refine ⟨?_,?_,List.nodup_range,?_,?_,?_⟩
  · simpa only [sbipStep9Input,sbipStep9Table_length] using ht
  · exact List.nodup_range.map (fun a b h => Nat.add_left_cancel h)
  · intro a ha hb
    have ha' := (sbipStep9Input_left r a).1 ha
    have hb' := (sbipStep9Input_right r a).1 hb
    omega
  · intro a
    rw [List.mem_append,sbipStep9Input_left,sbipStep9Input_right]
    change _ ↔ a ∈ (sbipStep3 (sbipIndexed (sbipStep8Initial r,r.1.2.2 ++ r.1.2.1))).1
    rw [ht.domMem]
    simp only [List.length_append]
    omega
  · intro a
    simp [sbipStep9Input]

/-- Membership in the prefix of a duplicate-free list is read from its position. -/
theorem sbipPrefix_mem (l k : List ℕ) (hd : (l ++ k).Nodup)
    (i : Fin (l ++ k).length) : (l ++ k)[i.val] ∈ l ↔ i.val < l.length := by
  constructor
  · intro hm
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm
    have hj' : j < (l ++ k).length := by simp only [List.length_append]; omega
    have he' : (l ++ k)[j] = (l ++ k)[i.val] := by
      rw [List.getElem_append_left hj]
      exact he
    have := (List.Nodup.getElem_inj_iff hd).1 he'
    omega
  · intro hi
    rw [List.getElem_append_left hi]
    exact List.getElem_mem hi

/-- Membership in the suffix is the complementary interval of positions. -/
theorem sbipSuffix_mem (l k : List ℕ) (hd : (l ++ k).Nodup)
    (i : Fin (l ++ k).length) : (l ++ k)[i.val] ∈ k ↔ l.length ≤ i.val := by
  constructor
  · intro hm
    obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm
    have hj' : l.length + j < (l ++ k).length := by simp only [List.length_append]; omega
    have he' : (l ++ k)[l.length + j] = (l ++ k)[i.val] := by
      rw [List.getElem_append_right (by omega)]
      simpa using he
    have := (List.Nodup.getElem_inj_iff hd).1 he'
    omega
  · intro hi
    rw [List.getElem_append_right hi]
    exact List.getElem_mem _

/-- The alternative vertex order leaves every mathematical color name unchanged. -/
theorem sbipStep9Table_spec {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X : Pt (BipBlockInputs Ω)} {r : RawSbipRefine}
    {name : (step8Obj X).Vtx → ℕ} (h : SbipStep8Names X r name)
    (e : (step8Obj X).Vtx ≃ Fin (r.1.2.2 ++ r.1.2.1).length)
    (hl : ∀ A, (r.1.2.2 ++ r.1.2.1)[(e A).val] = name A)
    (A B : (step8Obj X).Vtx) :
    binColor (sbipStep9Table r,(e A,e B)) = (step8Config X).natColor A B := by
  have hi : ∀ C D : (step8Obj X).Vtx,
      namedBin (r.1.2.2 ++ r.1.2.1).length
        (sbipIndexed (sbipStep8Initial r,r.1.2.2 ++ r.1.2.1)) (e C) (e D) =
          (step8Obj X).vtxInitColor C D := by
    intro C D
    have hm (A : (step8Obj X).Vtx) : name A ∈ r.1.2.1 ++ r.1.2.2 := by
      have ha : name A ∈ r.1.2.2 ++ r.1.2.1 := hl A ▸ List.getElem_mem (e A).isLt
      simpa only [List.mem_append,or_comm] using ha
    rw [namedBin,sbipIndexed_get,hl,hl,sbipStep8Initial_get r (hm C) (hm D)]
    exact sbipStep8Pair_spec h C D
  have hh := sbipStep3_named (step8Obj X) e (sbipIndexed_wf _ _) hi A B
  change binColor (sbipStep9Table r,(e A,e B)) = ((step8Obj X).wlConfig).natColor A B
  rw [VColBipBlk.natColor_wlConfig,VColBipBlk.wlCaseColor,dif_pos ⟨A.property,B.property⟩]
  exact hh

section UPCC
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
    (X : Pt (Step9UPCCInputs Ω N)) {r : RawSbipRefine}
    {name : (step8Obj (step9Base X)).Vtx → ℕ}
    (h : SbipStep8Names (step9Base X) r name)
    (hd : (r.1.2.2 ++ r.1.2.1).Nodup)
    (e : (step8Obj (step9Base X)).Vtx ≃ Fin (r.1.2.2 ++ r.1.2.1).length)
    (hl : ∀ A, (r.1.2.2 ++ r.1.2.1)[(e A).val] = name A)

include h hd hl

/-- The prepared table satisfies the actual naming contract of Section 9.8.
Only names of the graph before refinement are supplied as hypotheses. -/
theorem sbipStep9Input_names :
    UpccCaseNames ((step9UPCCFunc N).obj X).obj e (sbipStep9Input r) := by
  let Y := ((step9UPCCFunc N).obj X).obj
  have hleft (A : (step8Obj (step9Base X)).Vtx) :
      r.1.2.2.length ≤ (e A).val ↔ ∃ x, Y.part₁ x ∧ A.val = {x} := by
    rw [← sbipSuffix_mem _ _ hd (e A),hl A]
    exact h.left A
  have hright (A : (step8Obj (step9Base X)).Vtx) :
      (e A).val < r.1.2.2.length ↔ A.val ∈ Y.blocks := by
    rw [← sbipPrefix_mem _ _ hd (e A),hl A]
    exact h.right A
  refine ⟨sbipStep9Table_length r,?_,?_,?_⟩
  · intro A B
    change binColor (sbipStep9Table r,(e A,e B)) = step8CaseColor (step9Base X) A.val B.val
    rw [sbipStep9Table_spec h e hl,step8CaseColor_vtx]
  · ext a
    simp only [Set.mem_image,Set.mem_univ,true_and,Set.mem_setOf_eq]
    constructor
    · rintro ⟨x,rfl⟩
      apply (sbipStep9Input_left r _).2
      exact ⟨(hleft (Y.vtxOfPt x)).2 ⟨x,x.property,rfl⟩,(e (Y.vtxOfPt x)).isLt⟩
    · intro ha
      obtain ⟨hlo,hhi⟩ := (sbipStep9Input_left r _).1 ha
      let A := e.symm ⟨a,hhi⟩
      have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
      obtain ⟨x,hx,he⟩ := (hleft A).1 (hA.symm ▸ hlo)
      refine ⟨⟨x,hx⟩,?_⟩
      have hv : Y.vtxOfPt ⟨x,hx⟩ = A := Subtype.ext he.symm
      change (e (Y.vtxOfPt ⟨x,hx⟩)).val = a
      rw [hv,hA]
  · ext a
    simp only [Set.mem_image,Set.mem_univ,true_and,Set.mem_setOf_eq]
    constructor
    · rintro ⟨B,rfl⟩
      exact (sbipStep9Input_right r _).2 ((hright (Y.vtxOfBlk B)).2 B.property)
    · intro ha
      have hlo := (sbipStep9Input_right r _).1 ha
      have hhi : a < (r.1.2.2 ++ r.1.2.1).length := by simp only [List.length_append]; omega
      let A := e.symm ⟨a,hhi⟩
      have hA : (e A).val = a := congrArg Fin.val (e.apply_symm_apply ⟨a,hhi⟩)
      have hb := (hright A).1 (hA.symm ▸ hlo)
      refine ⟨⟨A.val,hb⟩,?_⟩
      have hv : Y.vtxOfBlk ⟨A.val,hb⟩ = A := Subtype.ext rfl
      change (e (Y.vtxOfBlk ⟨A.val,hb⟩)).val = a
      rw [hv,hA]

/-- The prepared case test reaches UPCC on the category of `step9UPCCFunc`. -/
theorem sbipStep9Input_case : sbipStep9Case (sbipStep9Input r) = 2 := by
  have hr (A : (step8Obj (step9Base X)).Vtx) :
      (e A).val < r.1.2.2.length ↔ A.val ∈ (step8Obj (step9Base X)).blocks := by
    rw [← sbipPrefix_mem _ _ hd (e A),hl A]
    exact h.right A
  let eb : ↥(step8Blks (step9Base X)) ≃ Fin r.1.2.2.length := {
    toFun := fun B => ⟨e B.val,(hr B.val).2 B.property⟩
    invFun := fun i => ⟨e.symm ⟨i.val,by simp only [List.length_append]; omega⟩,
      (hr _).1 (by simpa using i.isLt)⟩
    left_inv := fun B => Subtype.ext (e.symm_apply_apply B.val)
    right_inv := by
      intro i
      apply Fin.ext
      change (e (e.symm ⟨i.val,by simp only [List.length_append]; omega⟩)).val = i.val
      simp only [Equiv.apply_symm_apply] }
  let eb' : ↥(step8Blks (step9Base X)) ≃ Fin (sbipStep9Input r).2.2.length :=
    eb.trans (finCongr (by simp [sbipStep9Input]))
  have hc : ∀ u v, binColor ((sbipStep9Input r).1,
      ((sbipStep9Input r).2.2[(eb' u).val],(sbipStep9Input r).2.2[(eb' v).val])) =
        step9BlkColor (step9Base X) u v := by
    intro u v
    simp only [sbipStep9Input,List.getElem_range]
    change binColor (sbipStep9Table r,(e u.val,e v.val)) = _
    rw [sbipStep9Table_spec h e hl]
    exact (step8CaseColor_vtx (step9Base X) u.val v.val).symm
  exact (sbipStep9Case_spec (step9Base X) (sbipStep9Input r) eb' hc).2.2.mpr
    ⟨X.obj.2.2.1,X.obj.2.2.2⟩

/-- Running the prepared second refinement supplies every hypothesis needed
by the Section 9.8 valid-outcome theorem. -/
theorem sbipStep9Input_upcc_spec_index {i : ℕ} (hi : i < r.1.2.2.length) :
    ∃ Z : Pt (Cat.sum (ColoredPartitions Ω ℕ) (VColBlkGraphs Ω ℕ)),
      UpccCaseOutcomeRep ((step9UPCCFunc N).obj X).obj e
        (UpccCase.versionF (sbipStep9Input r,i)) Z ∧
      IsBlkImprimitiveOutcome (BlkCases.V₁ ((step9UPCCFunc N).obj X))
        (BlkCases.numBlocks ((step9UPCCFunc N).obj X)) Z := by
  apply UpccCase.versionF_spec_index ((step9UPCCFunc N).obj X) e (sbipStep9Input_wf r)
    (sbipStep9Input_names X h hd e hl)
  simpa only [UpccCase.widthF,sbipStep9Input,List.length_range] using hi

end UPCC
end Algo
