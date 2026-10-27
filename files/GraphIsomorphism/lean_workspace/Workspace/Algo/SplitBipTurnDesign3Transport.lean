import Workspace.Algo.SplitBipTurnChildTransport
import Workspace.Algo.SplitDesignCase3Iso
import Workspace.Algo.SplitBipTurnDesignTests

/-! # Sec. 9.7, Case 3 at isomorphic parents on the RAM

Case 3 of Sec. 9.7 (v2.5) applies the Design Lemma to the `k`-skeleton of the neighborhood
hypergraph on the blocks, and for each returned canonical object it recurses on the link
graph restricted to a selected block family, with a hint on pairs of blocks. Canonicity of
the Design Lemma makes these recursive calls correspond at isomorphic parents. Here this is
the statement `SbipDesign3ChildCovariant`: the block positions move by an isomorphism of the
stored relations (`designBlockPos_iso`), so the computed read family moves along it
(`designCallReadFamily_iso`), and the selected families and hints correspond
(`designReadSelectedSet_iso`, `designReadMathHint_iso`).
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

/-- Sec. 9.7, Case 3, at one node: the graph kept for a computed entry of the Design Lemma
family is a valid next input, written in the names fixed by `eD`, `e₁` and `e₂`. -/
theorem design3_rep (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (hcase : designCase12 (sbipTurnCase I.1).2 = none)
    (eD : ↥(step9DesignObj X hd h6 hcl).vtxSet ≃ Fin (sbipGraphStep9Dictionary I.1.2).length)
    (hn : DesignNames (step9DesignObj X hd h6 hcl)
      (fun x => (eD ((step9DesignObj X hd h6 hcl).vtxOfPt x)).val)
      (fun B => (eD ((step9DesignObj X hd h6 hcl).vtxOfBlk B)).val) (sbipTurnCase I.1).2.1)
    (hD : SbipVertexDictionary (step9DesignObj X hd h6 hcl).vtxSet (fun x => x.val.val)
      (sbipGraphStep9Dictionary I.1.2) eD)
    (hcolors : ∀ A,binColor ((sbipTurnCase I.1).2.1.1,(eD A,eD A)) =
      (step9DesignObj X hd h6 hcl).c A.val A.val)
    (e₁ : ↥(step9DesignObj X hd h6 hcl).Pt₁ ≃ Fin (sbipTurnCase I.1).2.1.2.1.length)
    (he₁ : ∀ x,(sbipTurnCase I.1).2.1.2.1[(e₁ x).val] =
      (eD ((step9DesignObj X hd h6 hcl).vtxOfPt x)).val)
    (e₂ : ↥(step9DesignObj X hd h6 hcl).blocks ≃ Fin (sbipTurnCase I.1).2.1.2.2.length)
    (he₂ : ∀ B,(sbipTurnCase I.1).2.1.2.2[(e₂ B).val] =
      (eD ((step9DesignObj X hd h6 hcl).vtxOfBlk B)).val)
    {xs : List ℕ} {d : RawDesignReadOut}
    (hdout : (xs,d) ∈ designCallReadFamily (sbipTurnCase I.1).2.1) :
    letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
    letI : DecidableEq ↥(step7Set X) := Classical.decEq _
    ∃ hadm,SbipNodeRep m (sbipNodeMakeChild (I,designStored ((I.1.1,sbipGraphStep9Dictionary I.1.2),
        designCase3Graph ((sbipTurnCase I.1).2.1,d))))
      ⟨step7Set X,⟨((step9DesignObj X hd h6 hcl).linkGraph.restrictBlkHint
        (designReadSelectedSet (sbipTurnCase I.1).2.1
          (fun B => (eD ((step9DesignObj X hd h6 hcl).vtxOfBlk B)).val) d)
        (designReadMathHint e₂ d),alphaNew X),
        twothirds_le_alphaNew hd,alphaNew_lt_one hd,hadm⟩⟩ := by
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  let U := step9DesignObj X hd h6 hcl
  have hpoint : Function.Injective (fun x : ↥(step7Set X) => x.val.val) :=
    fun _ _ hh => Subtype.ext (Fin.ext hh)
  have hbound (x : ↥(step7Set X)) : x.val.val < I.1.1.length := by
    rw [show I.1.1.length = m from h.ground]
    exact x.val.isLt
  have hsize : (sbipTurnCase I.1).2.1.1.1.length = (sbipGraphStep9Dictionary I.1.2).length := by
    simp [sbipTurnCase,sbipTurnGraphInput,sbipGraphStep9Input,sbipGraphNumbered,
      sbipGraphStep9Dictionary_length]
  let bbd : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(U,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt : U.n₂ < U.n₁ := BlkBlockDesignInputs.numBlocks_lt_n₁ bbd
  obtain ⟨h1,h2⟩ := (designCase12_none _).1 hcase
  have hn1 : ¬ U.IsCase1 := fun hh => by
    have := (designCase1_spec hn e₁ he₁ e₂ he₂).2 hh
    rw [h1] at this
    cases this
  have hn2 : ¬ U.IsCase2 := fun hh => by
    have := (designCase2_spec hn e₁ he₁ e₂ he₂).2 hh
    rw [h2] at this
    cases this
  exact h.design_restricted_rep hd h6 hcl _ _ _
    (designCallReadStored_complete hn hw (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2)
      eD hD hpoint (fun _ => rfl) (fun _ => rfl) hsize hcolors I.1.1 hbound e₂ he₂ hdout)
    (designReadSelectedSet_sub d)
    (designCallReadSelected_defect hn hw e₁ he₁ e₂ he₂ hdout)
    (designCallReadSelected_progress hn hw e₁ he₁ e₂ he₂ hlt hn1 hn2 hdout)

end SbipNodeRep

/-- **Sec. 9.7, Case 3 is canonical on the RAM.** Every graph that the computed Design Lemma
family passes to Reduce-Part2-by-Color at a represented node has a corresponding graph at any
isomorphic represented node, and the two next inputs are isomorphic by the restriction of the
given isomorphism. -/
theorem sbipDesign3ChildCovariant : SbipDesign3ChildCovariant := by
  intro m I J X Y h h' φ hφ hd h6 hcl hcase q hq
  letI : Fintype ↥(step7Set X) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set X) := Classical.decEq _
  letI : Fintype ↥(step7Set Y) := Fintype.ofFinite _
  letI : DecidableEq ↥(step7Set Y) := Classical.decEq _
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
  obtain ⟨h1e,h2e,-⟩ := h.design_tests_transport h' φ hφ hd h6 hcl
  have hcase' : designCase12 (sbipTurnCase J.1).2 = none := by
    obtain ⟨h1,h2⟩ := (designCase12_none _).1 hcase
    exact (designCase12_none _).2 ⟨h1e ▸ h1,h2e ▸ h2⟩
  obtain ⟨eD,hn,hD,hcolors⟩ := h.design_case_names hd h6 hcl
  obtain ⟨eD',hn',hD',hcolors'⟩ := h'.design_case_names hd' h6' hcl'
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  have hw' := sbipGraphStep9Input_wf (sbipTurnGraphInput J.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  obtain ⟨e₁',he₁'⟩ := splitNameEquiv_exists _ hn'.inj₁ _ hw'.left_nodup hn'.left
  obtain ⟨e₂',he₂'⟩ := splitNameEquiv_exists _ hn'.inj₂ _ hw'.right_nodup hn'.right
  let bbd : Pt (BlkBlockDesignInputs (Fin m)) := ⟨step7Set X,
    ⟨(U,alphaNew X),twothirds_le_alphaNew hd,alphaNew_lt_one hd,step8Obj_numBlocks_lt X hd⟩⟩
  have hlt : U.n₂ < U.n₁ := BlkBlockDesignInputs.numBlocks_lt_n₁ bbd
  obtain ⟨d,hdout,hqd⟩ := (designCase3Graphs_mem _ q.1 q.2).1 hq
  obtain ⟨⟨xs',d'⟩,hv,hi⟩ := designCallReadFamily_iso
    (designRight_length_eq hU e₂ e₂') (designCallWitness_length_eq hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂')
    (designLeft_length_eq hU e₁ e₁') (designCall_guard hn e₁ he₁ e₂ he₂ hlt) _
    (designBlockPos_iso hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂' hlt) hdout
  refine ⟨(xs',designCase3Graph ((sbipTurnCase J.1).2.1,d')),
    (designCase3Graphs_mem _ _ _).2 ⟨d',hv,rfl⟩,?_⟩
  rw [hqd]
  obtain ⟨hadm,hrep⟩ := h.design3_rep hd h6 hcl hcase eD hn hD hcolors e₁ he₁ e₂ he₂ hdout
  obtain ⟨hadm',hrep'⟩ := h'.design3_rep hd' h6' hcl' hcase' eD' hn' hD' hcolors' e₁' he₁' e₂' he₂' hv
  apply SbipNodeRep.design_restricted_transport (I := I) (J := J) hd φ hφ hd' h6 hcl h6' hcl' hadm hadm' hrep hrep'
  · exact designReadSelectedSet_iso hU hn hn' e₁ he₁ e₂ he₂ e₁' he₁' e₂' he₂' hdout hv hi hw hw'
  · intro A B hA hB
    exact designReadMathHint_iso hU e₂ e₂' hdout hv hi A B
      (designReadSelectedSet_sub d hA.2) (designReadSelectedSet_sub d hB.2)

end Algo
