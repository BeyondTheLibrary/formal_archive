import Workspace.Algo.SplitBipTurnUpccTransport

/-! Read the gathered UPCC partition as the exact local-color kernel of
the chosen block, then extend it at its parent. The target family chooses
the image block and therefore returns the transported named outcome.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h

theorem upcc_partition_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : ¬ Step9Imprimitive X) (hcl : ¬ Step9Clique X)
    (eD : ↥(step9UPCCObj X hd h6 hi hcl).vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length)
    (hn : UpccCaseNames (step9UPCCObj X hd h6 hi hcl) eD (sbipTurnCase I.1).2.1)
    (hD : SbipVertexDictionary (step9UPCCObj X hd h6 hi hcl).vtxSet (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2) eD)
    (B : ↥(step9UPCCObj X hd h6 hi hcl).blocks) :
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseUpccExit (sbipTurnContext (sbipTurnCase I.1),
        upccCaseLocalColors ((sbipTurnCase I.1).2.1,upccCaseName₂ (step9UPCCObj X hd h6 hi hcl) eD B))).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (Subtype.val '' (step9UPCCObj X hd h6 hi hcl).Pt₁)
          (kerPartition (step9UPCCObj X hd h6 hi hcl).Pt₁
            (fun x => (step9UPCCObj X hd h6 hi hcl).c B.val {x})))⟩ := by
  let U := step9UPCCObj X hd h6 hi hcl
  let lab := upccCaseLocalColors ((sbipTurnCase I.1).2.1,upccCaseName₂ U eD B)
  let q := sbipCaseGather ((sbipTurnCase I.1).2.1.2.1,lab)
  let P := kerPartition U.Pt₁ (fun x => U.c B.val {x})
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hlocal (a : ℕ) : a ∈ (sbipTurnCase I.1).2.1.2.1 ↔
      ∃ x,upccCaseName₁ U eD x = a := by
    change a ∈ {a | a ∈ (sbipTurnCase I.1).2.1.2.1} ↔ _
    rw [← hn.left]
    constructor
    · rintro ⟨x,_,hx⟩
      exact ⟨x,hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,Set.mem_univ _,hx⟩
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ (upccCaseName₁_injective U eD) _ hw.left_nodup hlocal
  let eW := (splitImageEquiv U.Pt₁).trans e₁
  let name := fun x : ↥(Subtype.val '' U.Pt₁) => upccCaseName₁ U eD (wPt x)
  have heW (x : ↥(Subtype.val '' U.Pt₁)) :
      (sbipTurnCase I.1).2.1.2.1[(eW x).val] = name x := he₁ (wPt x)
  have hrow (x : ↥(Subtype.val '' U.Pt₁)) :
      sbipDictPoint (sbipGraphStep9Dictionary I.1.2,name x) = x.val.val :=
    upccStored_point U (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2) eD hD
      (fun _ _ hh => Subtype.ext (Fin.ext hh)) (wPt x)
  have hcover (a : ℕ) : a ∈ (sbipTurnCase I.1).2.1.2.1 ↔ ∃ x,name x = a := by
    rw [hlocal]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨mkPt x.property,by simpa only [name,wPt_mkPt] using hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨wPt x,hx⟩
  have hc (x : ↥(Subtype.val '' U.Pt₁)) : labAt q.1 (eW x) = P.color x := by
    exact ((sbipCaseGather_get (sbipTurnCase I.1).2.1.2.1 lab (e₁ (wPt x))).1).trans
      ((congrArg (labAt lab) (he₁ (wPt x))).trans
        (upccCaseLocalColors_spec U eD hw hn B (U.vtxOfPt (wPt x))))
  have hp (x y : ↥(Subtype.val '' U.Pt₁)) :
      cellOf q (eW x) = cellOf q (eW y) ↔ P.part x y := by
    change (labAt q.1 (eW x),labAt q.1 (eW x)) =
      (labAt q.1 (eW y),labAt q.1 (eW y)) ↔ P.part x y
    simp only [Prod.mk.injEq,hc,and_self]
    rfl
  exact h.case_partition_named_decode P (step8V₁_subset X) q name eW heW hrow hcover hc hp

include h' hφ

theorem upcc_return_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : ¬ Step9Imprimitive X) (hcl : ¬ Step9Clique X) (o : RawAlignOutcome)
    (hout : (o,none) ∈ sbipTurnUpccFamily (sbipTurnCase I.1)) :
    ∃ o',(o',none) ∈ sbipTurnUpccFamily (sbipTurnCase J.1) ∧
      SbipNamedOutcomeIso I J X Y φ o o' := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hi' : ¬ Step9Imprimitive Y := fun hh => hi
    (step9Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hcl' : ¬ Step9Clique Y := fun hh => hcl
    (step9Clique_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  let U := step9UPCCObj X hd h6 hi hcl
  let U' := step9UPCCObj Y hd' h6' hi' hcl'
  have hU : step7Equiv hφ ∈ (BlkUPCCCases (Fin m)).Iso U U' :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  obtain ⟨eD,hn,hD⟩ := h.upcc_case_names hd h6 hi hcl
  obtain ⟨eD',hn',hD'⟩ := h'.upcc_case_names hd' h6' hi' hcl'
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hw' := sbipGraphStep9Input_wf (sbipTurnGraphInput J.1)
  obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
  obtain ⟨B,rfl⟩ := upccCaseName₂_surj hn hb
  let B' : ↥U'.blocks := ⟨step7Equiv hφ '' B.val,(hU.2.1 B.val).2 B.property⟩
  have htest := upccCaseSplits_transport hU eD eD' hw hw' hn hn' B
  unfold sbipTurnUpcc at ho
  split at ho
  next hsplit =>
    have hs' : upccCaseSplits ((sbipTurnCase J.1).2.1,upccCaseName₂ U' eD' B') = true := htest.symm.trans hsplit
    have ho' := congrArg Prod.fst ho
    change (sbipCaseUpccExit (sbipTurnContext (sbipTurnCase I.1),
      upccCaseLocalColors ((sbipTurnCase I.1).2.1,upccCaseName₂ U eD B))).2 = o at ho'
    rw [← ho']
    refine ⟨(sbipCaseUpccExit (sbipTurnContext (sbipTurnCase J.1),
      upccCaseLocalColors ((sbipTurnCase J.1).2.1,upccCaseName₂ U' eD' B'))).2,?_,_,_,
      h.upcc_partition_named_decode hd h6 hi hcl eD hn hD B,
      h'.upcc_partition_named_decode hd' h6' hi' hcl' eD' hn' hD' B',?_,?_,?_⟩
    · apply List.mem_map.2
      refine ⟨upccCaseName₂ U' eD' B',?_,?_⟩
      · change upccCaseName₂ U' eD' B' ∈ {a | a ∈ (sbipTurnCase J.1).2.1.2.2}
        rw [← hn'.right]
        exact ⟨B',Set.mem_univ _,rfl⟩
      · simp only [sbipTurnUpcc,if_pos hs']
        rfl
    · rintro _ ⟨x,_,rfl⟩
      exact x.property
    · rintro _ ⟨x,_,rfl⟩
      exact x.property
    · let eV := subEquiv φ (fun x => hφ.2.part₁ x)
      let eW := subEquiv (step7Equiv hφ) (W := U.Pt₁) (W' := U'.Pt₁) hU.1
      refine ⟨eV,fun _ => rfl,?_⟩
      apply extendPartition.mem_iso (step8V₁_subset X) (step8V₁_subset Y) eV eW (fun _ => rfl)
      exact kerPartition_mem_iso (step7Equiv hφ) hU.1 (upcc_c_blk_singleton hU B.val)
  next hsplit =>
    have hh := congrArg Prod.snd ho
    cases hh

end SbipNodeRep
end Algo
