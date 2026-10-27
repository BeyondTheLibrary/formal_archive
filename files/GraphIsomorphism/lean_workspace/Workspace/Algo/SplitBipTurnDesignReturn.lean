import Workspace.Algo.SplitBipTurnCaseReturns

namespace Algo
open Babai RAM
open scoped Classical

private theorem designCase12_return_tag (z : RawDesignLocal) (L : List ℕ) (o : RawAlignOutcome)
    (hout : designCase12 z = some ((L,o),none)) :
    (∃ P,o = rawAlignPartition P) ∨ ∃ J,o = rawAlignJohnson J := by
  rcases o with ⟨P,J⟩
  cases P with
  | some P =>
    cases J with
    | none => exact Or.inl ⟨P,rfl⟩
    | some J =>
      unfold designCase12 designCase2Exit designDominantExit at hout
      split_ifs at hout <;> simp [designPartExit,designJohnsonExit,designGraphExit,
        rawAlignPartition,rawAlignJohnson] at hout
  | none =>
    cases J with
    | some J => exact Or.inr ⟨J,rfl⟩
    | none =>
      unfold designCase12 designCase2Exit designDominantExit at hout
      split_ifs at hout <;> simp [designPartExit,designJohnsonExit,designGraphExit,
        rawAlignPartition,rawAlignJohnson] at hout

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (hd : ¬ AllClassesSmall X)
include h hd

theorem design12_return_good (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (L : List ℕ) (o : RawAlignOutcome)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,o),none)) :
    SbipReturnGood I X (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),o)).2 := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hn := sbipGraphStep9Input_designNames X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9 h6 hcl
  have hw := sbipGraphStep9Input_wf (sbipTurnGraphInput I.1)
  obtain ⟨e₁,he₁⟩ := splitNameEquiv_exists _ hn.inj₁ _ hw.left_nodup hn.left
  obtain ⟨e₂,he₂⟩ := splitNameEquiv_exists _ hn.inj₂ _ hw.right_nodup hn.right
  have ha : 2/3 ≤ sbipAlphaValue (sbipTurnCase I.1).2.2 := by
    rw [h.case_alpha hd]
    exact twothirds_le_alphaNew hd
  have ha1 : sbipAlphaValue (sbipTurnCase I.1).2.2 < 1 := by
    rw [h.case_alpha hd]
    exact alphaNew_lt_one hd
  have hnum : ((step9DesignObj X hd h6 hcl).n₂ : ℝ) <
      sbipAlphaValue (sbipTurnCase I.1).2.2 * (step9DesignObj X hd h6 hcl).n₁ := by
    rw [h.case_alpha hd]
    exact step8Obj_numBlocks_lt X hd
  rcases designCase12_return_tag _ L o hout with ⟨P,rfl⟩ | ⟨J,rfl⟩
  · apply h.alpha_case_good hd
    rw [← h.case_alpha hd]
    exact (sbipCaseDesign_partition hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd) ha ha1 hnum L P hout).2
  · obtain ⟨_,hsub,hsize,ms,ts,hJ⟩ := sbipCaseDesign_johnson hn e₁ he₁ e₂ he₂ _
      (h.case_denominator hd) ha ha1 hnum hw L J hout
    apply h.johnson_case_good hd J hsub hJ
    rwa [h.case_alpha hd] at hsize

theorem design_return_good (h6 : ¬ Step6Imprimitive X) (hcl : Step9Clique X)
    (o : RawAlignOutcome) (hout : (o,none) ∈ sbipTurnDesign (sbipTurnCase I.1)) :
    SbipReturnGood I X o := by
  unfold sbipTurnDesign at hout
  cases hcase : designCase12 (sbipTurnCase I.1).2 with
  | none =>
    simp only [hcase,Option.elim_none] at hout
    obtain ⟨q,hq,he⟩ := List.mem_map.1 hout
    have hh := congrArg Prod.snd he
    cases hh
  | some q =>
    simp only [hcase,Option.elim_some,List.mem_singleton] at hout
    rcases q with ⟨⟨L,ro⟩,g⟩
    cases g with
    | some g =>
      have hh := congrArg Prod.snd hout
      cases hh
    | none =>
      have hh := congrArg Prod.fst hout
      change o = (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),ro)).2 at hh
      rw [hh]
      exact h.design12_return_good hd h6 hcl L ro hcase

end SbipNodeRep
end Algo
