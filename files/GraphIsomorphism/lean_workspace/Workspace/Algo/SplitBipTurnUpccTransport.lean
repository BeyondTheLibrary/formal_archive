import Workspace.Algo.SplitBipTurnImpPartition
import Workspace.Algo.SplitUpccFamilyTransport

/-! The UPCC graph branch keeps its mathematical marked graph after
restoring persistent point names. The chosen block maps to an actual
target block, and the resulting next inputs use the Step 7 restriction.
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

theorem upcc_case_names (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : ¬ Step9Imprimitive X) (hcl : ¬ Step9Clique X) :
    ∃ e : ↥(step9UPCCObj X hd h6 hi hcl).vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length,
      UpccCaseNames (step9UPCCObj X hd h6 hi hcl) e (sbipTurnCase I.1).2.1 ∧
      SbipVertexDictionary (step9UPCCObj X hd h6 hi hcl).vtxSet (fun x => x.val.val)
        (sbipGraphStep9Dictionary I.1.2) e := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  have hn := sbipGraphStep9Input_upccNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi hcl
  exact ⟨eD,⟨hn.size.trans (sbipGraphStep9Dictionary_length I.1.2).symm,
    hn.color,hn.left,hn.right⟩,hD⟩

include h' hφ

theorem upcc_child_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : ¬ Step9Imprimitive X) (hcl : ¬ Step9Clique X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnUpccFamily (sbipTurnCase I.1)) :
    ∃ g',sbipTurnRecur g' ∈ sbipTurnUpccFamily (sbipTurnCase J.1) ∧
      ∃ Z Z' : Pt (BipBlockInputs (Fin m)),
        SbipNodeRep m (sbipNodeMakeChild (I,g)) Z ∧
        SbipNodeRep m (sbipNodeMakeChild (J,g')) Z' ∧
        ∃ (hS : Z.car ⊆ X.car) (_hT : Z'.car ⊆ Y.car) (ψ : ↥Z.car ≃ ↥Z'.car),
          ψ ∈ (BipBlockInputs (Fin m)).IsoP Z Z' ∧
          ∀ x,(ψ x).val = (φ ⟨x.val,hS x.property⟩).val := by
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
    have hh := congrArg Prod.snd ho
    cases hh
  next hsplit =>
    have hsplit' : ¬ upccCaseSplits ((sbipTurnCase J.1).2.1,upccCaseName₂ U' eD' B') = true :=
      fun hh => hsplit (htest.trans hh)
    have hg := congrArg Prod.snd ho
    change some (upccStoredGraph ((I.1.1,sbipGraphStep9Dictionary I.1.2),
      ((sbipTurnCase I.1).2.1,upccCaseName₂ U eD B))) = some g at hg
    rw [← Option.some.inj hg]
    have hbig : ∃ k,U.IsBigColor₂ B k := by
      by_contra hh
      apply hsplit
      apply (upccCaseSplits_spec U eD hw hn B).2
      intro k
      exact Nat.le_of_not_gt (fun hk => hh ⟨k,hk⟩)
    have hbig' : ∃ k,U'.IsBigColor₂ B' k := by
      obtain ⟨k,hk⟩ := hbig
      exact ⟨k,(upcc_isBigColor₂_map hU B.val k).2 hk⟩
    let g' := upccStoredGraph ((J.1.1,sbipGraphStep9Dictionary J.1.2),
      ((sbipTurnCase J.1).2.1,upccCaseName₂ U' eD' B'))
    have hs := upccStoredGraph_complete U (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2) eD hD
      (fun _ _ hh => Subtype.ext (Fin.ext hh)) I.1.1 (fun x => by
        rw [show I.1.1.length = m from h.ground]; exact x.val.isLt) hw hn B
    have hs' : SbipStoredRep (U'.upccBip B') (fun x => x.val.val) g' :=
      upccStoredGraph_complete U' (fun x => x.val.val)
        (sbipGraphStep9Dictionary J.1.2) eD' hD'
        (fun _ _ hh => Subtype.ext (Fin.ext hh)) J.1.1 (fun x => by
          rw [show J.1.1.length = m from h'.ground]; exact x.val.isLt) hw' hn' B'
    obtain ⟨hadm,hZ⟩ := h.halved_child_rep hd (U.upccBip B) _ hs rfl
      (U.isSmallColor₂_lColor B.property).2 (U.upccBip_defect₁ B.property hbig)
    obtain ⟨hadm',hZ'⟩ := h'.halved_child_rep hd' (U'.upccBip B') g' hs' rfl
      (U'.isSmallColor₂_lColor B'.property).2 (U'.upccBip_defect₁ B'.property hbig')
    refine ⟨g',?_,_,_,hZ,hZ',step7Set_subset X,step7Set_subset Y,step7Equiv hφ,
      ⟨alphaNew_congr ⟨φ,hφ⟩,upccBip_isIsoTo hU B.val⟩,fun _ => rfl⟩
    apply List.mem_map.2
    refine ⟨upccCaseName₂ U' eD' B',?_,?_⟩
    · change upccCaseName₂ U' eD' B' ∈ {a | a ∈ (sbipTurnCase J.1).2.1.2.2}
      rw [← hn'.right]
      exact ⟨B',Set.mem_univ _,rfl⟩
    · simp only [sbipTurnUpcc,if_neg hsplit']
      rfl

end SbipNodeRep
end Algo
