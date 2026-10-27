import Workspace.Algo.SplitBipTurnChild

/-! Every graph version returned by the actual ImprimitiveCase satisfies
the next node invariant and the paper's block-halving progress bound.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem imp_child_good (h6 : ¬ Step6Imprimitive X) (hi : Step9Imprimitive X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnImp (sbipTurnCase I.1)) : SbipChildGood I X g := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  have hn := sbipGraphStep9Input_impNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  let U := step9ImpObj X hd h6 hi
  have hpoint : Function.Injective (fun x : ↥(step7Set X) => x.val.val) :=
    fun _ _ hh => Subtype.ext (Fin.ext hh)
  have hdict : ImpStoredNames U
      (sbipGraphNumberedPoint (step8Obj X) (sbipGraphConstituent (sbipTurnGraphInput I.1)) e9)
      (sbipGraphNumberedBlock (step8Obj X) (sbipGraphConstituent (sbipTurnGraphInput I.1)) e9)
      (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2) :=
    impStoredNames_of_dictionary (X := U) (point := fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2) eD hD hpoint
  have hbound (x : ↥(step7Set X)) : x.val.val < I.1.1.length := by
    rw [show I.1.1.length = m from h.ground]
    exact x.val.isLt
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
    obtain ⟨Y,hrep,hY,hdef,hbranch,hhalf⟩ := impStep2Graphs_spec hn hw.left_nodup hw.right_nodup
      e₂ he₂ hno q hq
    apply h.halved_child hd Y _ (impStoredGraph_complete hrep hn hw.left_nodup
      (fun x => x.val.val) I.1.1 (sbipGraphStep9Dictionary I.1.2) hdict hq hpoint hbound)
    · change Subtype.val '' {x | Y.part₁ x} = _
      rw [hrep.part]
      rfl
    · rw [hrep.numBlocks]
      exact hhalf
    · exact hdef

end SbipNodeRep
end Algo
