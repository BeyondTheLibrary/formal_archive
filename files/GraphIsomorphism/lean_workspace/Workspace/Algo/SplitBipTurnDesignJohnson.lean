import Workspace.Algo.SplitBipTurnJohnsonIso

/-! The two Johnson exits of the actual DesignCase call transport between
isomorphic parents: Case 1 on the whole first part, and the last exit of
Case 2 on the dominant class `A`. Both carriers are read through the
persistent point names, and both colors are the paper's `|S ∖ T|`.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

section
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {s : Set Ω}
    {X : BlkDesignObj s} {name₁ : ↥X.Pt₁ → ℕ} {name₂ : ↥X.blocks → ℕ}
    {r : RawUpccCase} (h : DesignNames X name₁ name₂ r)
    (e₁ : ↥X.Pt₁ ≃ Fin r.2.1.length) (he₁ : ∀ x,r.2.1[(e₁ x).val] = name₁ x)
    (e₂ : ↥X.blocks ≃ Fin r.2.2.length) (he₂ : ∀ B,r.2.2[(e₂ B).val] = name₂ B)
    (p : ℕ × ℕ) (hb : 0 < p.2)
include h he₁ he₂ hb

/-- Sec. 9.7, Case 2, the last exit: the stored Johnson points are exactly
the names of the dominant class `A`. -/
theorem designDomPoints_mem (a : ℕ) :
    a ∈ designDomPoints (r,p) ↔
      ∃ x : ↥(X.domClass (sbipAlphaValue p)),name₁ ⟨x.val,x.property.1⟩ = a := by
  obtain ⟨eA,heA⟩ := designDomEquiv_exists h e₁ he₁ e₂ he₂ p hb
  have hlab (x : ↥(X.domClass (sbipAlphaValue p))) :
      labAt r.2.1 (designDomPositions (r,p))[(eA x).val] = name₁ ⟨x.val,x.property.1⟩ := by
    rw [heA,labAt,List.getD_eq_getElem _ _ (e₁ _).isLt,he₁]
  constructor
  · intro ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.1 ha
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hi
    obtain ⟨x,hx⟩ := eA.surjective ⟨k,hk⟩
    refine ⟨x,?_⟩
    have hk' : (eA x).val = k := by rw [hx]
    rw [← hlab x]
    simp only [hk']
  · rintro ⟨x,rfl⟩
    rw [← hlab x]
    exact List.mem_map.2 ⟨_,List.getElem_mem _,rfl⟩

end

namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)

/-- The dictionary row of a named Step 9 point is its persistent point name. -/
theorem design_point_row (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X)
    (eD : ↥(step9DesignObj X hd h6 hcl).vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length)
    (hD : SbipVertexDictionary (step9DesignObj X hd h6 hcl).vtxSet (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2) eD)
    (u : ↥(step9DesignObj X hd h6 hcl).Pt₁) :
    sbipDictPoint (sbipGraphStep9Dictionary I.1.2,
      (eD ((step9DesignObj X hd h6 hcl).vtxOfPt u)).val) = (u.val.val : ℕ) :=
  sbipVertexDictionary_point hD (fun _ _ hh => Subtype.ext (Fin.ext hh)) u.val
    (Or.inl ⟨_,u.property,rfl⟩)

include h

/-- Sec. 9.7, Cases 1 and 2: every Johnson exit of the actual DesignCase
call is well formed on its local first part. -/
theorem design_johnson_wf (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (L : List ℕ) (K : RawJohnson)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,rawAlignJohnson K),none)) :
    ∃ ms ts,K.WF (sbipTurnCase I.1).2.1.1.1.length ms ts := by
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have ha : 2/3 ≤ sbipAlphaValue (sbipTurnCase I.1).2.2 := by
    rw [h.case_alpha hd]
    exact twothirds_le_alphaNew hd
  have ha1 : sbipAlphaValue (sbipTurnCase I.1).2.2 < 1 := by
    rw [h.case_alpha hd]
    exact alphaNew_lt_one hd
  have hnum : ((step9DesignObj X hd h6 hcl).n₂ : ℝ) <
      sbipAlphaValue (sbipTurnCase I.1).2.2 * (step9DesignObj X hd h6 hcl).n₁ := by
    rw [h.case_alpha hd]
    exact step8Obj_numBlocks_lt X hd
  exact (sbipCaseDesign_johnson hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd) ha ha1 hnum hw
    L K hout).2.2.2

include h' hφ

/-- Sec. 9.7, Case 1: the Johnson scheme on the neighborhoods of the first
part is carried by the input map. -/
theorem design_case1_johnson_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) {ms ts ms' ts' : ℕ}
    (hK : (designJohnson (sbipTurnCase I.1).2.1).WF (sbipTurnCase I.1).2.1.1.1.length ms ts)
    (hK' : (designJohnson (sbipTurnCase J.1).2.1).WF (sbipTurnCase J.1).2.1.1.1.length ms' ts') :
    SbipNamedOutcomeIso I J X Y φ
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),
        rawAlignJohnson (designJohnson (sbipTurnCase I.1).2.1))).2
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),
        rawAlignJohnson (designJohnson (sbipTurnCase J.1).2.1))).2 := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hcl' := step9Clique_congr ⟨φ,hφ⟩ hcl
  let U := step9DesignObj X hd h6 hcl
  let U' := step9DesignObj Y hd' h6' hcl'
  have hU : U.IsMorphOn U' (step7Equiv hφ) :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  obtain ⟨eD',hn',hD',_⟩ := h'.design_case_names hd' h6' hcl'
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hw' := sbipGraphStep9Input_wf (sbipTurnGraphInput J.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  obtain ⟨e₁',he₁'⟩ := splitNameEquiv_exists _ hn'.inj₁ _ hw'.left_nodup hn'.left
  obtain ⟨e₂',he₂'⟩ := splitNameEquiv_exists _ hn'.inj₂ _ hw'.right_nodup hn'.right
  simp only [sbipCaseOutcome_johnson]
  refine sbipNamedOutcomeIso_johnson_local hφ (P := U.Pt₁) (P' := U'.Pt₁) (fun z => (hU.part₁ z).symm)
    (design_point_row hd h6 hcl eD hD) (design_point_row hd' h6' hcl' eD' hD')
    hn.left hn'.left hK hK' ?_
  intro u v
  refine (designJohnson_color hn' e₁' he₁' e₂' he₂' hw'.left_nodup _ _).trans
    (Eq.trans ?_ (designJohnson_color hn e₁ he₁ e₂ he₂ hw.left_nodup u v).symm)
  exact hU.johnsonColor_eq u.val v.val

/-- Sec. 9.7, Case 2, the last exit: the Johnson scheme on the traces
`X(v) ∩ C` of the dominant class is carried by the input map. -/
theorem design_dom_johnson_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X)
    (hdom : (step9DesignObj X hd h6 hcl).DomHyp (sbipAlphaValue (sbipTurnCase I.1).2.2))
    (hdom' : (step9DesignObj Y
      (fun hh => hd (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh))
      (fun hh => h6 (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh))
      (step9Clique_congr ⟨φ,hφ⟩ hcl)).DomHyp (sbipAlphaValue (sbipTurnCase J.1).2.2))
    {ms ts ms' ts' : ℕ}
    (hK : (designDomJohnson (sbipTurnCase I.1).2).WF (sbipTurnCase I.1).2.1.1.1.length ms ts)
    (hK' : (designDomJohnson (sbipTurnCase J.1).2).WF
      (sbipTurnCase J.1).2.1.1.1.length ms' ts') :
    SbipNamedOutcomeIso I J X Y φ
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),
        rawAlignJohnson (designDomJohnson (sbipTurnCase I.1).2))).2
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),
        rawAlignJohnson (designDomJohnson (sbipTurnCase J.1).2))).2 := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hcl' := step9Clique_congr ⟨φ,hφ⟩ hcl
  let U := step9DesignObj X hd h6 hcl
  let U' := step9DesignObj Y hd' h6' hcl'
  have hU : U.IsMorphOn U' (step7Equiv hφ) :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  obtain ⟨eD',hn',hD',_⟩ := h'.design_case_names hd' h6' hcl'
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hw' := sbipGraphStep9Input_wf (sbipTurnGraphInput J.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  obtain ⟨e₁',he₁'⟩ := splitNameEquiv_exists _ hn'.inj₁ _ hw'.left_nodup hn'.left
  obtain ⟨e₂',he₂'⟩ := splitNameEquiv_exists _ hn'.inj₂ _ hw'.right_nodup hn'.right
  have ha : sbipAlphaValue (sbipTurnCase I.1).2.2 = sbipAlphaValue (sbipTurnCase J.1).2.2 := by
    rw [h.case_alpha hd,h'.case_alpha hd']
    exact alphaNew_congr ⟨φ,hφ⟩
  have hP (z : ↥(step7Set X)) : z ∈ U.domClass (sbipAlphaValue (sbipTurnCase I.1).2.2) ↔
      step7Equiv hφ z ∈ U'.domClass (sbipAlphaValue (sbipTurnCase J.1).2.2) := by
    rw [← ha]
    exact (hU.mem_domClass_iff _ z).symm
  simp only [sbipCaseOutcome_johnson]
  refine sbipNamedOutcomeIso_johnson_local hφ hP
    (name := fun u => (eD (U.vtxOfPt ⟨u.val,u.property.1⟩)).val)
    (name' := fun u => (eD' (U'.vtxOfPt ⟨u.val,u.property.1⟩)).val)
    (fun u => design_point_row hd h6 hcl eD hD ⟨u.val,u.property.1⟩)
    (fun u => design_point_row hd' h6' hcl' eD' hD' ⟨u.val,u.property.1⟩)
    (designDomPoints_mem hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd))
    (designDomPoints_mem hn' e₁' he₁' e₂' he₂' _ (h'.case_denominator hd')) hK hK' ?_
  intro u v
  refine (designDomJohnson_color hn' e₁' he₁' e₂' he₂' _ (h'.case_denominator hd')
    hw'.left_nodup hdom' _ _).trans (Eq.trans ?_ (designDomJohnson_color hn e₁ he₁ e₂ he₂ _
      (h.case_denominator hd) hw.left_nodup hdom u v).symm)
  simp only [BlkCaseObj.domJohnsonColor,liftPt_mkPt]
  rw [hU.trace_eq u.val,hU.trace_eq v.val,← Set.image_diff (imgEquiv _).injective,
    Set.ncard_image_of_injective _ (imgEquiv _).injective]

end SbipNodeRep
end Algo
