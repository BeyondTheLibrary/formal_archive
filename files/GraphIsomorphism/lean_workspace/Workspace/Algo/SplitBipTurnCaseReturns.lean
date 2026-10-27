import Workspace.Algo.SplitBipTurnEarly
import Workspace.Algo.SplitBipCaseOutcomeLocal
import Workspace.Algo.SplitBipCaseOutcomeDesign

/-! Step 9 returns are read on the literal compact case input and restored
at this parent. The case hypotheses come from its tested mathematical
branch, and the local routines supply their partition/Johnson bounds.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem half_case_good (q : RawColPart)
    (hq : (decColPartition (sbipTurnCase I.1).2.1.2.1.length q).IsAlphaPartition (1/2)) :
    SbipReturnGood I X (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition q)).2 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  apply h.partition_good
  exact sbipCaseStep9_halfPartition_valid X name I.1.2 hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd q hq

theorem alpha_case_good (q : RawColPart)
    (hq : (decColPartition (sbipTurnCase I.1).2.1.2.1.length q).IsAlphaPartition (alphaNew X)) :
    SbipReturnGood I X (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition q)).2 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  apply h.partition_good
  exact sbipCaseStep9_partition_valid X name I.1.2 hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd q hq

theorem johnson_case_good {ms ts : ℕ} (J : RawJohnson)
    (hsub : ∀ a ∈ J.1,a ∈ (sbipTurnCase I.1).2.1.2.1)
    (hJ : J.WF (sbipTurnCase I.1).2.1.1.1.length ms ts)
    (hsize : alphaNew X * ((sbipTurnCase I.1).2.1.2.1.length : ℝ) ≤ J.1.length) :
    SbipReturnGood I X (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignJohnson J)).2 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  apply h.johnson_good _ (sbipCaseStep9_johnson_wf I.1.2 h.left_nodup h.point_lt hsub hJ)
  exact sbipCaseStep9_johnson_valid X name I.1.2 hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd h.point_lt J hsub hJ hsize

theorem case_alpha : sbipAlphaValue (sbipTurnCase I.1).2.2 = alphaNew X := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  exact (sbipGraphSteps35_continue X name (sbipTurnGraphInput I.1) hc hnd e he hp h.alpha
    h.denominator h.left_nodup hd).2.2

theorem case_denominator : 0 < (sbipTurnCase I.1).2.2.2 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  have hclass := sbipGraphClasses_names X (sbipTurnGraphInput I.1) name hc hnd e he hp h.alpha
  have hlen := sbipDominant_size hclass h.left_nodup h.denominator hd
  have hpos : 0 < (sbipDominant (sbipGraphClasses (sbipTurnGraphInput I.1))).length := by
    rw [hlen]
    have hh := two_le_dominantClass_ncard hd
    omega
  exact sbipAlphaUpdate_den_pos h.denominator hpos

theorem imp_return_good (h6 : ¬ Step6Imprimitive X) (hi : Step9Imprimitive X)
    (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnImp (sbipTurnCase I.1)) :
    SbipReturnGood I X o := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hn := sbipGraphStep9Input_impNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  unfold sbipTurnImp at hout
  split at hout
  next hsplit =>
    obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
    have ho' := congrArg Prod.fst ho
    change (sbipCaseImpExit (sbipTurnContext (sbipTurnCase I.1),
      impSplitLab ((sbipTurnCase I.1).2.1,b))).2 = o at ho'
    rw [← ho']
    apply h.half_case_good hd
    have hq : (impSplitLab ((sbipTurnCase I.1).2.1,b),none) ∈ impCase (sbipTurnCase I.1).2.1 := by
      simp only [impCase,hsplit,if_true]
      exact List.mem_map.2 ⟨b,hb,rfl⟩
    obtain ⟨P,hdec,hP,hraw⟩ := sbipCaseImp_local hn hw.left_nodup hw.right_nodup
      e₁ he₁ e₂ he₂ _ hq
    exact hraw
  next hsplit =>
    obtain ⟨g,hg,ho⟩ := List.mem_map.1 hout
    have ho' := congrArg Prod.snd ho
    cases ho'


theorem upcc_return_good (h6 : ¬ Step6Imprimitive X) (hi : ¬ Step9Imprimitive X)
    (hcl : ¬ Step9Clique X) (o : RawAlignOutcome)
    (hout : (o,none) ∈ sbipTurnUpccFamily (sbipTurnCase I.1)) : SbipReturnGood I X o := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hn := sbipGraphStep9Input_upccNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hi hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  let U : Pt (BlkUPCCCases (Fin m)) := ⟨step7Set X,step9UPCCObj X hd h6 hi hcl⟩
  have hcover (a : ℕ) : a ∈ (sbipTurnCase I.1).2.1.2.1 ↔
      ∃ x,upccCaseName₁ U.obj e9 x = a := by
    rw [← show a ∈ upccCaseName₁ U.obj e9 '' Set.univ ↔ a ∈ (sbipTurnCase I.1).2.1.2.1
      from by rw [hn.left]; rfl]
    simp
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ (upccCaseName₁_injective U.obj e9) _ hw.left_nodup hcover
  obtain ⟨b,hb,ho⟩ := List.mem_map.1 hout
  obtain ⟨B,rfl⟩ := upccCaseName₂_surj hn hb
  unfold sbipTurnUpcc at ho
  split at ho
  next hsplit =>
    change upccCaseSplits ((sbipTurnCase I.1).2.1,upccCaseName₂ U.obj e9 B) = true at hsplit
    have ho' := congrArg Prod.fst ho
    dsimp only [sbipTurnReturn] at ho'
    rw [← ho']
    apply h.half_case_good hd
    have hq : (UpccCase.versionF ((sbipTurnCase I.1).2.1,upccCaseName₂ U.obj e9 B)).2.2 = none := by
      simp only [UpccCase.versionF,hsplit,if_true]
    obtain ⟨P,hdec,hP,hraw⟩ := sbipCaseUpcc_local U e9 (r := (sbipTurnCase I.1).2.1) hw hn B hq e₁ he₁
    simpa only [UpccCase.versionF,hsplit,if_true] using hraw
  next hsplit =>
    have ho' := congrArg Prod.snd ho
    cases ho'

end SbipNodeRep
end Algo
