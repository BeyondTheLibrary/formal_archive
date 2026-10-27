import Workspace.Algo.SplitBipTurnDesignTests

/-! Every actual DesignCase partition return has the corresponding
return at the isomorphic parent. The proof follows the literal ordered
branch tests, including the complementary-pair boundary exit.
-/
namespace Algo
open Babai RAM
open scoped Classical
namespace SbipNodeRep
variable {m : ℕ} {I J : RawSbipNode} {X Y : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X) (h' : SbipNodeRep m J Y)
    (φ : ↥X.car ≃ ↥Y.car) (hφ : φ ∈ (BipBlockInputs (Fin m)).IsoP X Y)
include h h' hφ

/-- Sec. 9.7, Cases 1 and 2: each partition return of the actual DesignCase call has the
corresponding return at an isomorphic parent. -/
theorem design12_partition_transport (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (hcl : Step9Clique X) (L : List ℕ) (q : RawColPart)
    (hout : designCase12 (sbipTurnCase I.1).2 = some ((L,rawAlignPartition q),none)) :
    ∃ q',designCase12 (sbipTurnCase J.1).2 =
        some (((sbipTurnCase J.1).2.1.2.1,rawAlignPartition q'),none) ∧
      SbipNamedOutcomeIso I J X Y φ
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase I.1),rawAlignPartition q)).2
        (sbipCaseOutcome (sbipTurnContext (sbipTurnCase J.1),rawAlignPartition q')).2 := by
  obtain ⟨h1e,h2e,hte,hce,hse,htwe,hbe⟩ := h.design_tests_transport h' φ hφ hd h6 hcl
  unfold designCase12 at hout
  split at hout
  · simp [designJohnsonExit,rawAlignJohnson,rawAlignPartition] at hout
  next h1 =>
    split at hout
    next h2 =>
      unfold designCase2Exit at hout
      split at hout
      · simp [designGraphExit,rawAlignPartition] at hout
      next ht =>
        split at hout
        next hc =>
          split at hout
          next hs =>
            simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
              and_true] at hout
            rcases hout with ⟨rfl,rfl⟩
            refine ⟨designSmallPartition (sbipTurnCase J.1).2.1,?_,
              h.design_small_named_transport h' φ hφ hd h6 hcl⟩
            simp only [designCase12,designCase2Exit,← h1e,← h2e,← hte,← hce,← hse,
              if_neg h1,if_pos h2,if_neg ht,if_pos hc,if_pos hs]
            rfl
          next hs =>
            unfold designDominantExit at hout
            split at hout
            next htw =>
              simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
                and_true] at hout
              rcases hout with ⟨rfl,rfl⟩
              refine ⟨designDomPartition (sbipTurnCase J.1).2,?_,
                h.design_twins_named_transport h' φ hφ hd h6 hcl⟩
              simp only [designCase12,designCase2Exit,designDominantExit,
                ← h1e,← h2e,← hte,← hce,← hse,← htwe,
                if_neg h1,if_pos h2,if_neg ht,if_pos hc,if_neg hs,if_pos htw]
              rfl
            next htw =>
              split at hout
              next hb =>
                simp only [designPartExit,rawAlignPartition,Option.some.injEq,Prod.mk.injEq,
                  and_true] at hout
                rcases hout with ⟨rfl,rfl⟩
                refine ⟨designPairPartition (sbipTurnCase J.1).2,?_,
                  h.design_pairs_named_transport h' φ hφ hd h6 hcl⟩
                simp only [designCase12,designCase2Exit,designDominantExit,
                  ← h1e,← h2e,← hte,← hce,← hse,← htwe,← hbe,
                  if_neg h1,if_pos h2,if_neg ht,if_pos hc,if_neg hs,if_neg htw,if_pos hb]
                rfl
              · simp [designJohnsonExit,rawAlignJohnson,rawAlignPartition] at hout
        · simp [designGraphExit,rawAlignPartition] at hout
    · simp at hout

end SbipNodeRep
end Algo
