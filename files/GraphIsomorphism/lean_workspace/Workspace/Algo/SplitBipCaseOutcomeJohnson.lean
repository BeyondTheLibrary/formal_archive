import Workspace.Algo.SplitBipCaseOutcomeNames

/-! Restoring singleton names preserves every Johnson subset row. Only
injectivity on the returned carrier is needed: dictionary rows belonging
to blocks can share their first element with a point row.
-/
namespace Algo
open Babai RAM
open scoped Classical

variable {m n ms ts : ℕ} {d : List (List ℕ)} {J : RawJohnson}
    (hinj : Set.InjOn (fun a => sbipDictPoint (d,a)) {a | a ∈ J.1})
    (hlt : ∀ a ∈ J.1, sbipDictPoint (d,a) < m) (h : J.WF n ms ts)
include hinj hlt h

theorem sbipCaseJohnson_wf : (sbipCaseJohnson (d,J)).WF m ms ts := by
  refine ⟨h.two_le,h.params,h.hdr,?_,h.wNodup.map_on hinj,?_,
    h.rowSorted,h.rowLen,h.rowLt,h.rowsNodup,h.card⟩
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 ha
    exact hlt i hi
  · simpa only [sbipCaseJohnson,List.length_map] using h.rowsLen

theorem sbipCaseJohnson_row {a : ℕ} (ha : a ∈ J.1) :
    rawJRow (sbipCaseJohnson (d,J),sbipDictPoint (d,a)) = rawJRow (J,a) := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  have hr := sbipCaseJohnson_wf hinj hlt h
  have hir : i < (sbipCaseJohnson (d,J)).1.length := by simpa [sbipCaseJohnson] using hi
  have he : (sbipCaseJohnson (d,J)).1[i] = sbipDictPoint (d,J.1[i]) := by
    simp only [sbipCaseJohnson,List.getElem_map]
  rw [← he,hr.rawJRow_getElem hir,h.rawJRow_getElem hi]
  rfl

theorem sbipCaseJohnson_diff {a b : ℕ} (ha : a ∈ J.1) (hb : b ∈ J.1) :
    rawJDiff (sbipCaseJohnson (d,J),(sbipDictPoint (d,a),sbipDictPoint (d,b))) =
      rawJDiff (J,(a,b)) := by
  simp only [rawJDiff,sbipCaseJohnson_row hinj hlt h ha,sbipCaseJohnson_row hinj hlt h hb]

theorem sbipCaseJohnson_decode (parent loc : List ℕ) :
    decAlignOutcome m (sbipCaseOutcome ((parent,d,loc),rawAlignJohnson J)).2 =
      some (decAlignJohnson (sbipCaseJohnson (d,J)) (sbipCaseJohnson_wf hinj hlt h)) := by
  rw [sbipCaseOutcome_johnson,decAlignOutcome_johnson]

omit hinj hlt h in
theorem sbipCaseJohnson_mem (a : ℕ) :
    a ∈ (sbipCaseJohnson (d,J)).1 ↔ ∃ b ∈ J.1,sbipDictPoint (d,b) = a :=
  List.mem_map

/-- The decoder is an isomorphism on the explicit carrier bijection. -/
noncomputable def sbipCaseJohnsonEquiv :
    RawJohnson.carrier n J ≃ RawJohnson.carrier m (sbipCaseJohnson (d,J)) :=
  Equiv.ofBijective
    (fun a => ⟨⟨sbipDictPoint (d,a.val.val),hlt _ a.property⟩,
      List.mem_map.2 ⟨a.val.val,a.property,rfl⟩⟩)
    ⟨fun a b he => Subtype.ext (Fin.ext (hinj a.property b.property
        (congrArg (fun x => x.val.val) he))),by
      rintro ⟨a,ha⟩
      obtain ⟨b,hb,he⟩ := List.mem_map.1 ha
      exact ⟨⟨⟨b,h.wLt b hb⟩,hb⟩,Subtype.ext (Fin.ext he)⟩⟩

theorem sbipCaseJohnsonEquiv_color (a b : RawJohnson.carrier n J) :
    rawJDiff (sbipCaseJohnson (d,J),((sbipCaseJohnsonEquiv hinj hlt h a).val.val,
      (sbipCaseJohnsonEquiv hinj hlt h b).val.val)) = rawJDiff (J,(a.val.val,b.val.val)) :=
  sbipCaseJohnson_diff hinj hlt h a.property b.property

end Algo
