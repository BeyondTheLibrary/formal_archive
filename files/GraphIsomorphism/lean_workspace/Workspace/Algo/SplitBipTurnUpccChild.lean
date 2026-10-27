import Workspace.Algo.SplitBipTurnChild

/-! Each nonpartition UPCC version restores the marked bipartite graph.
Its small block color gives the half-size bound used by the next call.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem upcc_child_good (h6 : ¬ Step6Imprimitive X) (hi : ¬ Step9Imprimitive X)
    (hcl : ¬ Step9Clique X) (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnUpccFamily (sbipTurnCase I.1)) : SbipChildGood I X g := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨eD,heD,hD⟩ := sbipGraphStep9Dictionary_equiv_exists X name (fun x => x.val.val)
    I.1.2 hs hc hnd e he hp hr h.alpha h.denominator h.left_nodup hd
  let e9 := eD.trans (finCongr (sbipGraphStep9Dictionary_length I.1.2))
  have he9 : ∀ A,(sbipGraphCaseVertices (sbipGraphConstituent (sbipTurnGraphInput I.1)))[(e9 A).val] =
      sbipGraphStep8Name X name A := heD
  have hn := sbipGraphStep9Input_upccNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  let U := step9UPCCObj X hd h6 hi hcl
  have hnD : UpccCaseNames U eD (sbipTurnCase I.1).2.1 := by
    refine ⟨?_,hn.color,hn.left,hn.right⟩
    exact hn.size.trans (sbipGraphStep9Dictionary_length I.1.2).symm
  have hpoint : Function.Injective (fun x : ↥(step7Set X) => x.val.val) :=
    fun _ _ hh => Subtype.ext (Fin.ext hh)
  have hbound (x : ↥(step7Set X)) : x.val.val < I.1.1.length := by
    rw [show I.1.1.length = m from h.ground]
    exact x.val.isLt
  obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
  obtain ⟨B,rfl⟩ := upccCaseName₂_surj hnD hb
  unfold sbipTurnUpcc at ho
  split at ho
  next hsplit =>
    have hh := congrArg Prod.snd ho
    cases hh
  next hsplit =>
    change ¬ upccCaseSplits ((sbipTurnCase I.1).2.1,upccCaseName₂ U eD B) = true at hsplit
    have hg := congrArg Prod.snd ho
    change some (upccStoredGraph ((I.1.1,sbipGraphStep9Dictionary I.1.2),
      ((sbipTurnCase I.1).2.1,upccCaseName₂ U eD B))) = some g at hg
    rw [← Option.some.inj hg]
    have hbig : ∃ k,U.IsBigColor₂ B k := by
      by_contra hh
      apply hsplit
      apply (upccCaseSplits_spec U eD hw hnD B).2
      intro k
      exact Nat.le_of_not_gt (fun hk => hh ⟨k,hk⟩)
    apply h.halved_child hd (U.upccBip B) _
      (upccStoredGraph_complete U (fun x => x.val.val) (sbipGraphStep9Dictionary I.1.2)
        eD hD hpoint I.1.1 hbound hw hnD B)
    · rfl
    · exact (U.isSmallColor₂_lColor B.property).2
    · exact U.upccBip_defect₁ B.property hbig

end SbipNodeRep
end Algo
