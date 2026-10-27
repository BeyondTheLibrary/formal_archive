import Workspace.Algo.SplitBipTurnDesignJohnson

/-! Every return of the actual DesignCase call has the corresponding
return at an isomorphic parent. The proof follows the literal ordered
branch tests of Cases 1 and 2, so an exit is matched by the same exit.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000

private theorem designCase12_tag (z : RawDesignLocal) (L : List ℕ) (o : RawAlignOutcome)
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
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h

/-- Sec. 9.7, Case 2: the tests that reach the dominant exits give the
hypotheses of that part of the proof (`DomHyp`). -/
theorem design_domHyp (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (h2 : designCase2 (sbipTurnCase I.1).2.1 = true)
    (ht : designTie (sbipTurnCase I.1).2.1 ≠ true)
    (hs : designSmall (sbipTurnCase I.1).2 ≠ true) :
    (step9DesignObj X hd h6 hcl).DomHyp (sbipAlphaValue (sbipTurnCase I.1).2.2) := by
  obtain ⟨eD,hn,hD,_⟩ := h.design_case_names hd h6 hcl
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
  exact designDomHyp_of_tests hn e₁ he₁ e₂ he₂ _ (h.case_denominator hd) ha ha1 hnum h2 ht hs

include h' hφ

/-- Sec. 9.7, Cases 1 and 2: each Johnson return of the actual DesignCase
call has the same Johnson exit at an isomorphic parent. -/
theorem design12_johnson_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (L : List ℕ) (K : RawJohnson)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,rawAlignJohnson K),none)) :
    ∃ K',designCase12 (sbipTurnCase J.1).2 =
        some (((sbipTurnCase J.1).2.1.2.1,rawAlignJohnson K'),none) ∧
      SbipNamedOutcomeIso I J X Y φ
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignJohnson K)).2
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),rawAlignJohnson K')).2 := by
  have hd' : ¬ AllClassesSmall Y := fun hh => hd
    (allClassesSmall_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have h6' : ¬ Step6Imprimitive Y := fun hh => h6
    (step6Imprimitive_congr ⟨φ.symm,(BipBlockInputs (Fin m)).symm_mem hφ⟩ hh)
  have hcl' := step9Clique_congr ⟨φ,hφ⟩ hcl
  obtain ⟨ms,ts,hK⟩ := h.design_johnson_wf hd h6 hcl L K hout
  obtain ⟨h1e,h2e,hte,hce,hse,htwe,hbe⟩ := h.design_tests_transport h' φ hφ hd h6 hcl
  unfold designCase12 at hout
  split at hout
  next h1 =>
    simp only [designJohnsonExit,rawAlignJohnson,Option.some.injEq,Prod.mk.injEq,
      and_true,true_and] at hout
    rcases hout with ⟨rfl,hKe⟩
    subst hKe
    have hout' : designCase12 (sbipTurnCase J.1).2 =
        some (((sbipTurnCase J.1).2.1.2.1,
          rawAlignJohnson (designJohnson (sbipTurnCase J.1).2.1)),none) := by
      simp only [designCase12,← h1e,if_pos h1]
      rfl
    obtain ⟨ms',ts',hK'⟩ := h'.design_johnson_wf hd' h6' hcl' _ _ hout'
    exact ⟨_,hout',h.design_case1_johnson_transport h' φ hφ hd h6 hcl hK hK'⟩
  next h1 =>
    split at hout
    next h2 =>
      unfold designCase2Exit at hout
      split at hout
      · simp [designGraphExit,rawAlignJohnson] at hout
      next ht =>
        split at hout
        next hc =>
          split at hout
          · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
          next hs =>
            unfold designDominantExit at hout
            split at hout
            · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
            next htw =>
              split at hout
              · simp [designPartExit,rawAlignPartition,rawAlignJohnson] at hout
              next hb =>
                simp only [designJohnsonExit,rawAlignJohnson,Option.some.injEq,Prod.mk.injEq,
                  and_true,true_and] at hout
                rcases hout with ⟨rfl,hKe⟩
                subst hKe
                have hout' : designCase12 (sbipTurnCase J.1).2 =
                    some (((sbipTurnCase J.1).2.1.2.1,
                      rawAlignJohnson (designDomJohnson (sbipTurnCase J.1).2)),none) := by
                  simp only [designCase12,designCase2Exit,designDominantExit,
                    ← h1e,← h2e,← hte,← hce,← hse,← htwe,← hbe,
                    if_neg h1,if_pos h2,if_neg ht,if_pos hc,if_neg hs,if_neg htw,if_neg hb]
                  rfl
                obtain ⟨ms',ts',hK'⟩ := h'.design_johnson_wf hd' h6' hcl' _ _ hout'
                have hdom := h.design_domHyp hd h6 hcl h2 ht hs
                have hdom' := h'.design_domHyp hd' h6' hcl' (h2e ▸ h2) (hte ▸ ht) (hse ▸ hs)
                exact ⟨_,hout',h.design_dom_johnson_transport h' φ hφ hd h6 hcl hdom hdom' hK hK'⟩
        · simp [designGraphExit,rawAlignJohnson] at hout
    · simp at hout

/-- Sec. 9.7, Cases 1 and 2: each return of the actual DesignCase call,
partition or Johnson scheme, has its matching return at an isomorphic parent. -/
theorem design12_return_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (L : List ℕ) (o : RawAlignOutcome)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,o),none)) :
    ∃ L' o',designCase12 (sbipTurnCase J.1).2 = some ((L',o'),none) ∧
      SbipNamedOutcomeIso I J X Y φ
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),o)).2
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),o')).2 := by
  rcases designCase12_tag _ L o hout with ⟨P,rfl⟩ | ⟨K,rfl⟩
  · obtain ⟨q',hq',hiso⟩ := h.design12_partition_transport h' φ hφ hd h6 hcl L P hout
    exact ⟨_,_,hq',hiso⟩
  · obtain ⟨K',hK',hiso⟩ := h.design12_johnson_transport h' φ hφ hd h6 hcl L K hout
    exact ⟨_,_,hK',hiso⟩

/-- Sec. 9.7: every return of the DesignCase branch of the actual turn
has the corresponding return at an isomorphic parent. Case 3 returns
nothing directly; it only retains recursive graphs. -/
theorem design_return_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (o : RawAlignOutcome)
    (hout : (o,none) ∈ sbipTurnDesign (sbipTurnCase I.1)) :
    ∃ o',(o',none) ∈ sbipTurnDesign (sbipTurnCase J.1) ∧ SbipNamedOutcomeIso I J X Y φ o o' := by
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
      subst hh
      obtain ⟨L',o',hcase',hiso⟩ := h.design12_return_transport h' φ hφ hd h6 hcl L ro hcase
      refine ⟨_,?_,hiso⟩
      unfold sbipTurnDesign
      simp only [hcase',Option.elim_some,List.mem_singleton]
      rfl

end SbipNodeRep
end Algo
