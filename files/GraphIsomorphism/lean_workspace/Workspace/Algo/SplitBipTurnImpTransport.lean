import Workspace.Algo.SplitBipTurnHalvedTransport

/-! Every actual ImprimitiveCase child has a corresponding actual child
at an isomorphic parent. The next node keeps precisely the graph supplied
by the graph-family transport, and its map is the Step 7 restriction.
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

theorem imp_case_names (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : Step9Imprimitive X) :
    ∃ (name₁ : ↥(step9ImpObj X hd h6 hi).Pt₁ → ℕ)
      (name₂ : ↥(step9ImpObj X hd h6 hi).blocks → ℕ),
      ImpNames (step9ImpObj X hd h6 hi) name₁ name₂ (sbipTurnCase I.1).2.1 ∧
      ImpStoredNames (step9ImpObj X hd h6 hi) name₁ name₂ (fun x => x.val.val)
        (sbipGraphStep9Dictionary I.1.2) := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  refine ⟨_,_,sbipGraphStep9Input_impNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi,?_⟩
  exact impStoredNames_of_dictionary (X := step9ImpObj X hd h6 hi)
    (point := fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2) eD hD
    (fun _ _ hh => Subtype.ext (Fin.ext hh))

include h' hφ

theorem imp_child_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hi : Step9Imprimitive X) (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnImp (sbipTurnCase I.1)) :
    ∃ g',sbipTurnRecur g' ∈ sbipTurnImp (sbipTurnCase J.1) ∧
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
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  obtain ⟨e₂',he₂'⟩ := splitNameEquiv_exists _ hn'.inj₂ _ hw'.right_nodup hn'.right
  unfold sbipTurnImp at hout
  split at hout
  next hsplit =>
    obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
    have hh := congrArg Prod.snd ho
    cases hh
  next hsplit =>
    obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
    have hg := congrArg Prod.snd ho
    change some (impStoredGraph ((I.1.1,sbipGraphStep9Dictionary I.1.2),q)) = some g at hg
    have hg' := Option.some.inj hg
    rw [← hg']
    have hno : ¬ ImprimitiveSplits U := fun hh => hsplit ((impSplits_spec hn hw.left_nodup).2 hh)
    have hno' : ¬ ImprimitiveSplits U' := fun hh => hno
      (imprimitiveSplits_congr (X := ⟨step7Set Y,U'⟩) (Y := ⟨step7Set X,U⟩)
        ⟨(step7Equiv hφ).symm,(BlkImprimitiveCases (Fin m)).symm_mem hU⟩ hh)
    have hsplit' : ¬ impSplits (sbipTurnCase J.1).2.1 = true :=
      fun hh => hno' ((impSplits_spec hn' hw'.left_nodup).1 hh)
    obtain ⟨q',hq',G,G',hrep,hrep',hiso,hG,hdef,hG',hdef'⟩ :=
      impStep2Graphs_transport hU hn hn' hw.left_nodup hw.right_nodup
        hw'.left_nodup hw'.right_nodup e₂ he₂ e₂' he₂' hno q hq
    let g' := impStoredGraph ((J.1.1,sbipGraphStep9Dictionary J.1.2),q')
    have hs := impStoredGraph_complete hrep hn hw.left_nodup (fun x => x.val.val)
      I.1.1 (sbipGraphStep9Dictionary I.1.2) hD hq
      (fun _ _ hh => Subtype.ext (Fin.ext hh)) (fun x => by
        rw [show I.1.1.length = m from h.ground]; exact x.val.isLt)
    have hs' : SbipStoredRep G' (fun x => x.val.val) g' :=
      impStoredGraph_complete hrep' hn' hw'.left_nodup (fun x => x.val.val)
        J.1.1 (sbipGraphStep9Dictionary J.1.2) hD' hq'
        (fun _ _ hh => Subtype.ext (Fin.ext hh)) (fun x => by
          rw [show J.1.1.length = m from h'.ground]; exact x.val.isLt)
    have hV : Subtype.val '' G.V₁ = step8V₁ X := by
      change Subtype.val '' {x | G.part₁ x} = _
      rw [hrep.part]; rfl
    have hV' : Subtype.val '' G'.V₁ = step8V₁ Y := by
      change Subtype.val '' {x | G'.part₁ x} = _
      rw [hrep'.part]; rfl
    have hhalf : 2 * G.numBlocks ≤ step8NumBlocks X := step2Cands_two_mul_numBlocks_le U G hG
    have hhalf' : 2 * G'.numBlocks ≤ step8NumBlocks Y := step2Cands_two_mul_numBlocks_le U' G' hG'
    obtain ⟨hadm,hZ⟩ := h.halved_child_rep hd G _ hs hV hhalf hdef
    obtain ⟨hadm',hZ'⟩ := h'.halved_child_rep hd' G' g' hs' hV' hhalf' hdef'
    refine ⟨g',?_,_,_,hZ,hZ',step7Set_subset X,step7Set_subset Y,step7Equiv hφ,
      ⟨alphaNew_congr ⟨φ,hφ⟩,hiso⟩,fun _ => rfl⟩
    rw [sbipTurnImp,if_neg hsplit']
    exact List.mem_map.2 ⟨q',hq',rfl⟩

end SbipNodeRep
end Algo
