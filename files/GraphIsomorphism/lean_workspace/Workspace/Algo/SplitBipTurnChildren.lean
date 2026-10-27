import Workspace.Algo.SplitBipTurnImpChild
import Workspace.Algo.SplitBipTurnUpccChild
import Workspace.Algo.SplitBipTurnDesignChild

/-! Every literal recursive entry preserves the semantic node invariant.
No valid entry is removed by admission, including the DesignCase branch
that gains a hint while retaining its number of blocks.
-/
namespace Algo
open Babai RAM
open scoped Classical
set_option maxHeartbeats 1000000
namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem cases_child_good (hd : ¬ AllClassesSmall X) (h6 : ¬ Step6Imprimitive X)
    (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnCases (sbipTurnCase I.1)) : SbipChildGood I X g := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  obtain ⟨e9,he9⟩ := sbipGraphStep9_equiv_exists X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd
  have hcases := sbipGraphStep9Input_case X name (sbipTurnGraphInput I.1) hc hnd e he hp hr
    h.alpha h.denominator h.left_nodup hd e9 he9
  unfold sbipTurnCases at hout
  split at hout
  next hi => exact h.imp_child_good hd h6 (hcases.1.1 hi) o g hout
  next hi =>
    split at hout
    next hcl => exact h.design_child_good hd h6 (hcases.2.1.1 hcl).2 o g hout
    next hcl =>
      have hi' : ¬ Step9Imprimitive X := fun hh => hi (hcases.1.2 hh)
      have hcl' : ¬ Step9Clique X := fun hh => hcl (hcases.2.1.2 ⟨hi',hh⟩)
      exact h.upcc_child_good hd h6 hi' hcl' o g hout

theorem after35_child_good (hd : ¬ AllClassesSmall X) (o : RawAlignOutcome)
    (g : RawSbipStored) (hout : (o,some g) ∈ sbipTurnAfter35 I.1) : SbipChildGood I X g := by
  obtain ⟨name,e,hc,hs,hf,hnd,he,hp,hr⟩ := h.names
  unfold sbipTurnAfter35 at hout
  split at hout
  next hi =>
    have hh := congrArg Prod.snd (List.mem_singleton.1 hout)
    cases hh
  next hi =>
    apply h.cases_child_good hd _ o g hout
    exact fun hh => hi ((sbipGraphComponentTable_test X (sbipTurnGraphInput I.1) name hc hnd e he hp hr
      h.alpha h.denominator h.left_nodup hd).2 hh)

theorem large_child_good (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurnLarge I.1) : SbipChildGood I X g := by
  unfold sbipTurnLarge at hout
  cases he : (sbipGraphSteps35 (sbipTurnGraphInput I.1)).2 with
  | none =>
    simp only [he,Option.elim_none,List.mem_singleton] at hout
    have hh := congrArg Prod.snd hout
    cases hh
  | some q =>
    simp only [he,Option.elim_some] at hout
    exact h.after35_child_good (h.dominant_of_continue (by rw [he]; simp)) o g hout

theorem turn_child_good (c : ℕ) (o : RawAlignOutcome) (g : RawSbipStored)
    (hout : (o,some g) ∈ sbipTurn c I.1) : SbipChildGood I X g := by
  unfold sbipTurn at hout
  split at hout
  next hsmall =>
    obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
    have hh := congrArg Prod.snd ho
    cases hh
  next hlarge =>
    split at hout
    next hsmall =>
      obtain ⟨q,hq,ho⟩ := List.mem_map.1 hout
      have hh := congrArg Prod.snd ho
      cases hh
    next hlarge' => exact h.large_child_good o g hout

theorem nodeGraph_good (c : ℕ) (g : RawSbipStored) (hg : g ∈ sbipNodeGraphs c I) :
    SbipChildGood I X g := by
  obtain ⟨o,ho⟩ := (sbipTurnChildren_mem _ g).1 hg
  exact h.turn_child_good c o g ho

/-- The literal recursive-call list loses no valid paper graph version. -/
theorem nodeGraph_admitted (c : ℕ) (g : RawSbipStored) (hg : g ∈ sbipNodeGraphs c I) :
    sbipNodeAdmit (I,g) = some (sbipNodeMakeChild (I,g)) :=
  (h.nodeGraph_good c g hg).choose_spec.2.2.2.2.2

theorem nodeChild_good {c j : ℕ} {J : RawSbipNode} (hc : sbipNodeChild c (I,j) = some J) :
    ∃ Y : Pt (BipBlockInputs (Fin m)), SbipNodeRep m J Y ∧
      BipBlockInputs.V₁ Y = step8V₁ X ∧ BipBlockInputs.alpha Y = alphaNew X ∧
      (10 * BipBlockInputs.numBlocks Y ≤ 9 * BipBlockInputs.numBlocks X ∨
        (BipBlockInputs.numBlocks Y ≤ BipBlockInputs.numBlocks X ∧ Y.obj.1.1.HasHint)) ∧
      ((0 < sbipNodeBlocks I ∧ 10 * sbipNodeBlocks J ≤ 9 * sbipNodeBlocks I) ∨
        (sbipNodeBlocks J ≤ sbipNodeBlocks I ∧ sbipNodeBit I = 1 ∧ sbipNodeBit J = 0)) := by
  obtain ⟨g,hg,rfl,_⟩ := sbipNodeChild_some hc
  obtain ⟨Y,hy,hV,ha,hp,hr,_⟩ := h.nodeGraph_good c g (List.mem_of_getElem? hg)
  exact ⟨Y,hy,hV,ha,hp,hr⟩

end SbipNodeRep

theorem sbipNodeChild_valid {m c j : ℕ} {I J : RawSbipNode}
    (hI : SbipNodeValid m I) (hc : sbipNodeChild c (I,j) = some J) : SbipNodeValid m J := by
  obtain ⟨X,hX⟩ := hI
  obtain ⟨Y,hY,_⟩ := hX.nodeChild_good hc
  exact ⟨Y,hY⟩

end Algo
