import Workspace.Algo.SplitBipTurnDesignPartition

/-! The actual DesignCase calls at isomorphic parent nodes make the
same seven branch decisions, with their thresholds read from Step 4.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hφ

/-- Sec. 9.7, Cases 1 and 2: the seven executable branch tests agree at isomorphic parents. -/
theorem design_tests_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    designCase1 (sbipTurnCase I.1).2.1 = designCase1 (sbipTurnCase J.1).2.1 ∧
    designCase2 (sbipTurnCase I.1).2.1 = designCase2 (sbipTurnCase J.1).2.1 ∧
    designTie (sbipTurnCase I.1).2.1 = designTie (sbipTurnCase J.1).2.1 ∧
    designSelectC (sbipTurnCase I.1).2.1 = designSelectC (sbipTurnCase J.1).2.1 ∧
    designSmall (sbipTurnCase I.1).2 = designSmall (sbipTurnCase J.1).2 ∧
    designHasDomTwins (sbipTurnCase I.1).2 = designHasDomTwins (sbipTurnCase J.1).2 ∧
    designDomBoundary (sbipTurnCase I.1).2 = designDomBoundary (sbipTurnCase J.1).2 := by
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
  exact ⟨designCase1_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂',
    designCase2_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂',
    designTie_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂',
    designSelectC_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂',
    designSmall_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂' _ _
      (h.case_denominator hd) (h'.case_denominator hd') ha,
    designHasDomTwins_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂' _ _
      (h.case_denominator hd) (h'.case_denominator hd') ha,
    designDomBoundary_transport hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂' _ _
      (h.case_denominator hd) (h'.case_denominator hd') ha⟩

end SbipNodeRep
end Algo
