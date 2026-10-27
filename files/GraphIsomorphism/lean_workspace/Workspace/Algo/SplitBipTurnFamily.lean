import Workspace.Algo.SplitBipTurnValue

/-! The evaluator visits every graph version in its stored order. Its
value is exactly the immediate family followed by every extended child
family, so neither the admission test nor the fold loses a paper choice.
-/
namespace Algo
open Babai RAM
open scoped Classical

def sbipChildFamily (c : ℕ) (rec : RawSbipNode → RawSbipAnswers)
    (I : RawSbipNode) (j : ℕ) : RawSbipAnswers :=
  let g := (sbipNodeGraphs c I).getD j default
  (rec (sbipNodeMakeChild (I,g))).map (fun o =>
    sbipNodeLift ((I.1.2.1.1.1.1,g.1.1.1),o))

namespace SbipNodeRep
variable {m : ℕ} {I : RawSbipNode} {X : Pt (BipBlockInputs (Fin m))}
    (h : SbipNodeRep m I X)
include h

theorem loop_family_eq (c : ℕ) (rec : RawSbipNode → RawSbipAnswers) :
    ∀ w j s,j+w ≤ (sbipNodeGraphs c I).length →
      (sbipRound c).loopAux rec w I j s =
        s ++ (List.range' j w).flatMap (sbipChildFamily c rec I) := by
  intro w
  induction w with
  | zero => intro j s hb; simp [Round.loopAux,sbipRound]
  | succ w ih =>
    intro j s hb
    have hj : j < (sbipNodeGraphs c I).length := by omega
    let g := (sbipNodeGraphs c I)[j]
    have hg : g ∈ sbipNodeGraphs c I := List.getElem_mem hj
    have he : (sbipNodeGraphs c I)[j]? = some g := List.getElem?_eq_getElem hj
    have hd : (sbipNodeGraphs c I).getD j default = g := by
      simp only [List.getD_eq_getElem?_getD,he,Option.getD_some]
    have hc : (sbipRound c).child (I,j,s) = some (sbipNodeMakeChild (I,g)) := by
      change sbipNodeChild c (I,j) = _
      simp only [sbipNodeChild,he,Option.elim_some,h.nodeGraph_admitted c g hg]
    rw [(sbipRound c).loopAux_succ_some hc,ih (j+1) _ (by omega)]
    simp only [List.range'_succ,List.flatMap_cons]
    change (s ++ _) ++ _ = _
    simp only [sbipChildFamily,hd,sbipTurnGraphInput,List.append_assoc]

/-- Exact family equality, with every version and its original list order. -/
theorem value_family_eq (c f : ℕ) :
    (sbipRound c).value (f+1) I = sbipNodeInit c I ++
      (List.range (sbipNodeGraphs c I).length).flatMap
        (sbipChildFamily c ((sbipRound c).value f) I) := by
  rw [Round.value_succ]
  change (sbipRound c).loopAux ((sbipRound c).value f) (sbipNodeGraphs c I).length I 0 (sbipNodeInit c I) = _
  rw [h.loop_family_eq c _ _ _ _ (by omega)]
  simp only [List.range_eq_range']

/-- Every returned value comes from an immediate return or a literal
child answer. Conversely, every such choice is retained. -/
theorem value_mem_iff (c f : ℕ) (o : RawAlignOutcome) :
    o ∈ (sbipRound c).value (f+1) I ↔
      o ∈ sbipNodeInit c I ∨ ∃ g ∈ sbipNodeGraphs c I,
        ∃ p ∈ (sbipRound c).value f (sbipNodeMakeChild (I,g)),
          sbipNodeLift ((I.1.2.1.1.1.1,g.1.1.1),p) = o := by
  rw [h.value_family_eq,List.mem_append]
  apply or_congr Iff.rfl
  simp only [List.mem_flatMap,List.mem_range,sbipChildFamily,List.mem_map]
  constructor
  · rintro ⟨j,hj,p,hp,he⟩
    refine ⟨(sbipNodeGraphs c I).getD j default,?_,p,hp,he⟩
    simpa only [List.getD_eq_getElem _ _ hj] using List.getElem_mem (l := sbipNodeGraphs c I) hj
  · rintro ⟨g,hg,p,hp,he⟩
    obtain ⟨j,hj,hjg⟩ := List.getElem_of_mem hg
    refine ⟨j,hj,p,?_,?_⟩
    · simpa only [List.getD_eq_getElem _ _ hj,hjg] using hp
    · simpa only [List.getD_eq_getElem _ _ hj,hjg] using he

end SbipNodeRep
end Algo
