import Workspace.Algo.SplitBipTurnDesignNames

/-! The three DesignCase partition exits preserve both the printed
color labels and the block relation. Each local partition is extended
once to its actual parent first part.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h

/-- Sec. 9.7, Case 2 (small local-size class exit): the decoded return is the
kernel partition of the local size, extended to the parent first part. -/
theorem design_small_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    let U := step9DesignObj X hd h6 hcl
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition
        (designSmallPartition (sbipTurnCase I.1).2.1))).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (step8V₁ X) (kerPartition U.Pt₁ U.localSize))⟩ := by
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have hs := designSmallPartition_spec hn e₁ he₁ e₂ he₂
  exact h.design_partition_named_decode hd h6 hcl eD hn hD e₁ he₁ _ _ hs.2.1 hs.2.2

/-- Sec. 9.7, Case 2 (dominant twin exit): the decoded return is the
dominant-class twin partition, extended to the parent first part. -/
theorem design_twins_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    let U := step9DesignObj X hd h6 hcl
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition
        (designDomPartition (sbipTurnCase I.1).2))).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (step8V₁ X) (labPartition U.Pt₁ U.localSize (U.domLab (alphaNew X))))⟩ := by
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have hs := designDomPartition_spec hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd)
  rw [h.case_alpha hd] at hs
  exact h.design_partition_named_decode hd h6 hcl eD hn hD e₁ he₁ _ _ hs.2.1 hs.2.2

/-- Sec. 9.7, Case 2 (complementary-pair exit): the decoded return is the
pair partition of the dominant class, extended to the parent first part. -/
theorem design_pairs_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    let U := step9DesignObj X hd h6 hcl
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition
        (designPairPartition (sbipTurnCase I.1).2))).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (step8V₁ X) (labPartition U.Pt₁ U.localSize (U.domPairLab (alphaNew X))))⟩ := by
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have hs := designPairPartition_spec hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd)
  rw [h.case_alpha hd] at hs
  exact h.design_partition_named_decode hd h6 hcl eD hn hD e₁ he₁ _ _ hs.2.1 hs.2.2

include h' hφ

/-- Sec. 9.7, Case 2: the small-class exit is carried by isomorphisms of the parent input. -/
theorem design_small_named_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    SbipNamedOutcomeIso I J X Y φ
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),
        rawAlignPartition (designSmallPartition (sbipTurnCase I.1).2.1))).2
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),
        rawAlignPartition (designSmallPartition (sbipTurnCase J.1).2.1))).2 := by
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
  refine ⟨_,_,h.design_small_named_decode hd h6 hcl,
    h'.design_small_named_decode hd' h6' hcl',?_,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · let eV := subEquiv φ (fun x => hφ.2.part₁ x)
    let eW := subEquiv (step7Equiv hφ) (W := U.Pt₁) (W' := U'.Pt₁) hU.part₁
    refine ⟨eV,fun _ => rfl,?_⟩
    apply extendPartition.mem_iso (step8V₁_subset X) (step8V₁_subset Y) eV eW (fun _ => rfl)
    exact kerPartition_mem_iso (step7Equiv hφ) hU.part₁ hU.localSize_eq

/-- Sec. 9.7, Case 2: the dominant twin exit is carried by isomorphisms of the parent input. -/
theorem design_twins_named_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    SbipNamedOutcomeIso I J X Y φ
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),
        rawAlignPartition (designDomPartition (sbipTurnCase I.1).2))).2
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),
        rawAlignPartition (designDomPartition (sbipTurnCase J.1).2))).2 := by
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
  refine ⟨_,_,h.design_twins_named_decode hd h6 hcl,
    h'.design_twins_named_decode hd' h6' hcl',?_,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · let eV := subEquiv φ (fun x => hφ.2.part₁ x)
    let eW := subEquiv (step7Equiv hφ) (W := U.Pt₁) (W' := U'.Pt₁) hU.part₁
    refine ⟨eV,fun _ => rfl,?_⟩
    apply extendPartition.mem_iso (step8V₁_subset X) (step8V₁_subset Y) eV eW (fun _ => rfl)
    rw [← alphaNew_congr ⟨φ,hφ⟩]
    exact labPartition_mem_iso (step7Equiv hφ) hU.part₁ hU.localSize_eq (hU.domLab_iff (alphaNew X))

/-- Sec. 9.7, Case 2: the complementary-pair exit is carried by isomorphisms of the parent input. -/
theorem design_pairs_named_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) :
    SbipNamedOutcomeIso I J X Y φ
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),
        rawAlignPartition (designPairPartition (sbipTurnCase I.1).2))).2
      (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),
        rawAlignPartition (designPairPartition (sbipTurnCase J.1).2))).2 := by
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
  refine ⟨_,_,h.design_pairs_named_decode hd h6 hcl,
    h'.design_pairs_named_decode hd' h6' hcl',?_,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · rintro _ ⟨x,_,rfl⟩
    exact x.property
  · let eV := subEquiv φ (fun x => hφ.2.part₁ x)
    let eW := subEquiv (step7Equiv hφ) (W := U.Pt₁) (W' := U'.Pt₁) hU.part₁
    refine ⟨eV,fun _ => rfl,?_⟩
    apply extendPartition.mem_iso (step8V₁_subset X) (step8V₁_subset Y) eV eW (fun _ => rfl)
    rw [← alphaNew_congr ⟨φ,hφ⟩]
    exact labPartition_mem_iso (step7Equiv hφ) hU.part₁ hU.localSize_eq (hU.domPairLab_iff (alphaNew X))

end SbipNodeRep
end Algo
