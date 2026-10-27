import Workspace.Algo.AggNodeRestoreRaw

/-! Restoring old names changes neither a Johnson subset row nor its color.
The dictionary is injective on every valid local carrier, so the full raw
Johnson well-formedness predicate, including its binomial bijection, survives.
-/
namespace Algo
open Babai RAM
open scoped Classical

variable {m ms ts : ℕ} {D : List ℕ} {J : RawJohnson}

theorem aggnRestoreJohnson_wf (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (h : J.WF D.length ms ts) : (aggnRestoreJohnson (D,J)).WF m ms ts := by
  have hinj : ∀ x ∈ J.1, ∀ y ∈ J.1, rawGet (D,x) = rawGet (D,y) → x = y := by
    intro x hx y hy he
    simp only [rawGet, List.getD_eq_getElem _ _ (h.wLt x hx),
      List.getD_eq_getElem _ _ (h.wLt y hy)] at he
    exact (List.Nodup.getElem_inj_iff hnd).1 he
  refine ⟨h.two_le,h.params,h.hdr,?_,?_,?_,h.rowSorted,h.rowLen,h.rowLt,h.rowsNodup,h.card⟩
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 ha
    exact hlt _ (by simpa only [rawGet, List.getD_eq_getElem _ _ (h.wLt i hi)]
      using List.getElem_mem (h.wLt i hi))
  · exact h.wNodup.map_on hinj
  · simpa only [aggnRestoreJohnson,length_rawRestrictStr] using h.rowsLen

theorem aggnRestoreJohnson_row (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (h : J.WF D.length ms ts) {i : ℕ} (hi : i ∈ J.1) :
    rawJRow (aggnRestoreJohnson (D,J),rawGet (D,i)) = rawJRow (J,i) := by
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hi
  have hr := aggnRestoreJohnson_wf hnd hlt h
  have hlen : j < (aggnRestoreJohnson (D,J)).1.length := by
    simpa only [aggnRestoreJohnson,length_rawRestrictStr] using hj
  have he : (aggnRestoreJohnson (D,J)).1[j] = rawGet (D,J.1[j]) := by
    simp only [aggnRestoreJohnson,rawRestrictStr,List.getElem_map]
  rw [← he,hr.rawJRow_getElem hlen,h.rawJRow_getElem hj]
  rfl

theorem aggnRestoreJohnson_diff (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (h : J.WF D.length ms ts) {i j : ℕ} (hi : i ∈ J.1) (hj : j ∈ J.1) :
    rawJDiff (aggnRestoreJohnson (D,J),(rawGet (D,i),rawGet (D,j))) =
      rawJDiff (J,(i,j)) := by
  simp only [rawJDiff,aggnRestoreJohnson_row hnd hlt h hi,
    aggnRestoreJohnson_row hnd hlt h hj]

/-- The restored carrier is exactly the image under the stored local numbering. -/
theorem aggnRestoreJohnson_carrier (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (h : J.WF D.length ms ts) :
    RawJohnson.carrier m (aggnRestoreJohnson (D,J)) =
      (fun i => (winEquiv m D hnd hlt i).val) '' RawJohnson.carrier D.length J := by
  ext a
  constructor
  · intro ha
    obtain ⟨i,hi,hia⟩ := List.mem_map.1 ha
    refine ⟨⟨i,h.wLt i hi⟩,hi,Fin.ext ?_⟩
    dsimp only
    rw [winEquiv_coe D hnd hlt]
    simpa only [rawGet,List.getD_eq_getElem _ _ (h.wLt i hi)] using hia
  · rintro ⟨i,hi,rfl⟩
    apply List.mem_map.2
    refine ⟨i.val,hi,?_⟩
    dsimp only
    rw [winEquiv_coe D hnd hlt]
    simp only [rawGet,List.getD_eq_getElem _ _ i.isLt]

theorem aggnRestoreJohnson_decode (hnd : D.Nodup) (hlt : ∀ a ∈ D, a < m)
    (h : J.WF D.length ms ts) (dom : List ℕ) :
    decAlignOutcome m (aggnRestoreOutcome ((dom,D),rawAlignJohnson J)) =
      some (decAlignJohnson (aggnRestoreJohnson (D,J)) (aggnRestoreJohnson_wf hnd hlt h)) := by
  rw [aggnRestoreOutcome_johnson,decAlignOutcome_johnson]

end Algo
