import Workspace.Algo.SplitBipTurnCasePartitionDecode

/-! The ImprimitiveCase partition exit is the exact link-color kernel
for the chosen block, followed by the current parent's complement
extension. All block choices therefore transport under the input map.
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

theorem imp_partition_named_decode (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : Step9Imprimitive X)
    (name₁ : ↥(step9ImpObj X hd h6 hi).Pt₁ → ℕ)
    (name₂ : ↥(step9ImpObj X hd h6 hi).blocks → ℕ)
    (hn : ImpNames (step9ImpObj X hd h6 hi) name₁ name₂ (sbipTurnCase I.1).2.1)
    (hD : ImpStoredNames (step9ImpObj X hd h6 hi) name₁ name₂ (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2))
    (B : ↥(step9ImpObj X hd h6 hi).blocks) :
    sbipDecodeNamed m I.1.2.1.1.1.1
      (sbipCaseImpExit (sbipTurnContext (sbipTurnCase I.1),
        impSplitLab ((sbipTurnCase I.1).2.1,name₂ B))).2 =
      some ⟨BipBlockInputs.V₁ X,Sum.inl
        (extendPartition (BipBlockInputs.V₁ X) (Subtype.val '' (step9ImpObj X hd h6 hi).Pt₁)
          (kerPartition (step9ImpObj X hd h6 hi).Pt₁
            (fun x => (step9ImpObj X hd h6 hi).c {x} B.val)))⟩ := by
  let U := step9ImpObj X hd h6 hi
  let lab := impSplitLab ((sbipTurnCase I.1).2.1,name₂ B)
  let P := kerPartition U.Pt₁ (fun x => U.c {x} B.val)
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  let eW := (splitImageEquiv U.Pt₁).trans e₁
  let name := fun x : ↥(Subtype.val '' U.Pt₁) => name₁ (wPt x)
  have heW (x : ↥(Subtype.val '' U.Pt₁)) :
      (sbipTurnCase I.1).2.1.2.1[(eW x).val] = name x := he₁ (wPt x)
  have hrow (x : ↥(Subtype.val '' U.Pt₁)) :
      sbipDictPoint (sbipGraphStep9Dictionary I.1.2,name x) = x.val.val :=
    impStored_point hD (wPt x)
  have hcover (a : ℕ) : a ∈ (sbipTurnCase I.1).2.1.2.1 ↔ ∃ x,name x = a := by
    rw [hn.left]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨mkPt x.property,by simpa only [name,wPt_mkPt] using hx⟩
    · rintro ⟨x,hx⟩
      exact ⟨wPt x,hx⟩
  have hc (x : ↥(Subtype.val '' U.Pt₁)) : labAt lab (eW x) = P.color x :=
    impSplitLab_spec hn B (wPt x) (e₁ (wPt x)) (he₁ (wPt x))
  have hp (x y : ↥(Subtype.val '' U.Pt₁)) :
      cellOf (lab,lab) (eW x) = cellOf (lab,lab) (eW y) ↔ P.part x y := by
    simp only [cellOf,Prod.mk.injEq,hc,and_self]
    rfl
  exact h.case_partition_named_decode P (step8V₁_subset X) (lab,lab) name eW heW hrow hcover hc hp

include h' hφ

theorem imp_return_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : Step9Imprimitive X) (o : RawAlignOutcome)
    (hout : (o,none) ∈ sbipTurnImp (sbipTurnCase I.1)) :
    ∃ o',(o',none) ∈ sbipTurnImp (sbipTurnCase J.1) ∧ SbipNamedOutcomeIso I J X Y φ o o' := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hi' := step9Imprimitive_congr ⟨φ,hφ⟩ hi
  let U := step9ImpObj X hd h6 hi
  let U' := step9ImpObj Y hd' h6' hi'
  have hU : step7Equiv hφ ∈ (BlkImprimitiveCases (Fin m)).Iso U U' :=
    ⟨fun x => (step8Obj_isIsoTo hφ).part₁ x,fun B => (step8Obj_isIsoTo hφ).blocks B,
      fun A B => step8CaseColor_map hφ A B⟩
  obtain ⟨n₁,n₂,hn,hD⟩ := h.imp_case_names hd h6 hi
  obtain ⟨n₁',n₂',hn',hD'⟩ := h'.imp_case_names hd' h6' hi'
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hw' := sbipGraphStep9Input_wf (sbipTurnGraphInput J.1)
  unfold sbipTurnImp at hout
  split at hout
  next hsplit =>
    obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
    obtain ⟨B,rfl⟩ := (hn.right _).1 hb
    let B' : ↥U'.blocks := ⟨step7Equiv hφ '' B.val,(hU.2.1 B.val).2 B.property⟩
    have hs' : impSplits (sbipTurnCase J.1).2.1 = true :=
      (impSplits_spec hn' hw'.left_nodup).2
        (imprimitiveSplits_congr (X := ⟨step7Set X,U⟩) (Y := ⟨step7Set Y,U'⟩)
          ⟨step7Equiv hφ,hU⟩ ((impSplits_spec hn hw.left_nodup).1 hsplit))
    have ho' := congrArg Prod.fst ho
    change (sbipCaseImpExit (sbipTurnContext (sbipTurnCase I.1),
      impSplitLab ((sbipTurnCase I.1).2.1,n₂ B))).2 = o at ho'
    rw [← ho']
    refine ⟨(sbipTurnImpPart (sbipTurnCase J.1,n₂' B')).1,?_,_,_,
      h.imp_partition_named_decode hd h6 hi n₁ n₂ hn hD B,
      h'.imp_partition_named_decode hd' h6' hi' n₁' n₂' hn' hD' B',?_,?_,?_⟩
    · rw [sbipTurnImp,if_pos hs']
      exact List.mem_map.2 ⟨n₂' B',(hn'.right _).2 ⟨B',rfl⟩,rfl⟩
    · rintro _ ⟨x,_,rfl⟩
      exact x.property
    · rintro _ ⟨x,_,rfl⟩
      exact x.property
    · let eV := subEquiv φ (fun x => hφ.2.part₁ x)
      let eW := subEquiv (step7Equiv hφ) (W := U.Pt₁) (W' := U'.Pt₁) hU.1
      refine ⟨eV,fun _ => rfl,?_⟩
      apply extendPartition.mem_iso (step8V₁_subset X) (step8V₁_subset Y) eV eW
        (fun _ => rfl)
      apply kerPartition_mem_iso (step7Equiv hφ) hU.1
      intro x
      simpa only [Set.image_singleton] using hU.2.2 {x} B.val
  next hsplit =>
    obtain ⟨g,hg,ho⟩ := List.mem_map.1 hout
    have hh := congrArg Prod.snd ho
    cases hh

end SbipNodeRep
end Algo
