import Workspace.Algo.SplitBipTurnLift
import Workspace.Algo.SplitBipTurnNonempty

/-! All literal versions survive the fold. A represented node with enough
fuel returns at least one valid outcome: immediate returns persist, and
an admitted child contributes a nonempty recursive family.
-/
namespace Algo
open Babai RAM
open scoped Classical

theorem sbipLoop_keeps (c : ℕ) (rec : RawSbipNode → RawSbipAnswers) (I : RawSbipNode) :
    ∀ w j s,∀ o ∈ s,o ∈ (sbipRound c).loopAux rec w I j s := by
  intro w
  induction w with
  | zero => intro j s o ho; exact ho
  | succ w ih =>
    intro j s o ho
    cases hc : sbipNodeChild c (I,j) with
    | none =>
      rw [(sbipRound c).loopAux_succ_none
        (show (sbipRound c).child (I,j,s) = none from hc)]
      exact ho
    | some J =>
      rw [(sbipRound c).loopAux_succ_some
        (show (sbipRound c).child (I,j,s) = some J from hc)]
      exact ih (j+1) _ o (List.mem_append_left _ ho)

theorem sbipValue_nonempty {m c f : ℕ} {I : RawSbipNode}
    (hI : SbipNodeValid m I) (hf : sbipNodeMeasure I < f) :
    ∃ o,o ∈ (sbipRound c).value f I := by
  induction f generalizing I with
  | zero => omega
  | succ f ih =>
    obtain ⟨X,hX⟩ := hI
    obtain ⟨⟨o,g⟩,ho⟩ := hX.turn_nonempty c
    rw [Round.value_succ]
    cases g with
    | none =>
      exact ⟨o,sbipLoop_keeps c _ I _ _ _ o ((sbipTurnReturns_mem _ o).2 ho)⟩
    | some g =>
      have hmem : g ∈ sbipNodeGraphs c I := (sbipTurnChildren_mem _ g).2 ⟨o,ho⟩
      cases hgs : sbipNodeGraphs c I with
      | nil => simp [hgs] at hmem
      | cons g₀ gs =>
        have hg₀ : g₀ ∈ sbipNodeGraphs c I := by rw [hgs]; exact List.mem_cons_self
        have ha := hX.nodeGraph_admitted c g₀ hg₀
        have hc : sbipNodeChild c (I,0) = some (sbipNodeMakeChild (I,g₀)) := by
          simp only [sbipNodeChild,hgs,List.getElem?_cons_zero,Option.elim_some,ha]
        have hm := (sbipNodeChild_some hc).choose_spec.2.2
        obtain ⟨p,hp⟩ := ih (sbipNodeChild_valid ⟨X,hX⟩ hc) (by omega)
        change ∃ o,o ∈ (sbipRound c).loopAux ((sbipRound c).value f)
          (sbipNodeGraphs c I).length I 0 (sbipNodeInit c I)
        rw [hgs,List.length_cons,(sbipRound c).loopAux_succ_some
          (show (sbipRound c).child (I,0,sbipNodeInit c I) = some (sbipNodeMakeChild (I,g₀)) from hc)]
        let q := sbipNodeLift ((I.1.2.1.1.1.1,g₀.1.1.1),p)
        refine ⟨q,sbipLoop_keeps c _ I gs.length 1 _ q (List.mem_append_right _ ?_)⟩
        exact List.mem_map.2 ⟨p,hp,by simp [q,hgs,sbipTurnGraphInput]⟩

/-- The uncapped recursion returns a nonempty family of valid named
outcomes on every represented input once its raw measure is covered. -/
theorem sbipValue_valid_nonempty {m c f : ℕ} {I : RawSbipNode}
    (hI : SbipNodeValid m I) (hf : sbipNodeMeasure I < f) :
    (∃ o,o ∈ (sbipRound c).value f I) ∧ SbipAnswersGood m I ((sbipRound c).value f I) :=
  ⟨sbipValue_nonempty hI hf,sbipValue_good m c f I⟩

end Algo
