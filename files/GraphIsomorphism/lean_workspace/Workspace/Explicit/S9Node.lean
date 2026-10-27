/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the routines of one node of
the recursion of Sec. 9, bounded at an external degree. Not part of the faithful formalization.
-/
import Workspace.Explicit.S9Turn
import Workspace.Explicit.NodeStep
import Workspace.Explicit.NodeBounded
import Workspace.Algo.SplitBipRun
import Workspace.Algo.SplitBipResources

/-!
# One node of the recursion of Sec. 9, bounded at the degree

At a node `I` of the recursion of Theorem 9.2.2 whose resources (`Algo.SbipResources`: the
number of points, the witness and the threshold potential) are bounded by `n`, the turn of
`Explicit.TN.sbipTurn` meets its precondition at the degree `Algo.sbipCaseEnvelope n`, a
polynomial in `n` (`Algo.SbipNodeRep.case_envelope`). So the child, init and combine
routines of `Algo.sbipRound` are bounded at the degree `n`, and so is one step of its
depth-first evaluator, on every state whose frames carry such nodes.
-/

namespace Explicit

open RAM Algo Babai

/-- The precondition of a node of Sec. 9 at degree `n`: its resources are bounded by `n`. -/
def NodePre (n : ℕ) (I : RawSbipNode) : Prop := ∃ m, SbipResources m n I

/-- The frames of a state of the evaluator of Sec. 9 carry nodes whose resources are bounded
by `n`. -/
def SbipStatePre (n : ℕ) (x : Round.EvalState RawSbipNode RawSbipAnswers RawSbipAnswers) :
    Prop :=
  ∀ fr ∈ x.1, NodePre n fr.1

theorem NodePre.child {n c j : ℕ} {I J : RawSbipNode} (h : NodePre n I)
    (hc : sbipNodeChild c (I, j) = some J) : NodePre n J := by
  obtain ⟨m, h⟩ := h
  exact ⟨m, h.child hc⟩

theorem n_le_sbipCaseEnvelope (n : ℕ) : n ≤ sbipCaseEnvelope n := by
  unfold sbipCaseEnvelope; omega

/-- At a node with resources bounded by `n`, the turn meets its precondition at the degree
`sbipCaseEnvelope n`. -/
theorem NodePre.turnPre {n : ℕ} {I : RawSbipNode} (h : NodePre n I) :
    TN.TurnPre (sbipCaseEnvelope n) I.1 := by
  obtain ⟨m, h⟩ := h
  obtain ⟨X, hX⟩ := h.valid
  refine ⟨(hX.first_length_le.trans h.degree).trans (n_le_sbipCaseEnvelope n), fun hd => ?_⟩
  exact hX.case_envelope h.degree h.witness h.alpha (hX.dominant_of_continue hd)

/-- `sbipCaseEnvelope n ≤ 2^S (n+1)^d`. -/
theorem exists_caseEnvelope_poly : ∃ S d, ∀ n, sbipCaseEnvelope n ≤ 2 ^ S * (n + 1) ^ d := by
  obtain ⟨S, d, hs⟩ := polyBound_sbipCaseEnvelope
  exact ⟨S, d, fun n => (hs n).trans (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)⟩

namespace TN

/-- **The turn at a node**, at the degree of its resources. -/
theorem sbipNodeTurn (c : ℕ) :
    TN (fun I : RawSbipNode => Algo.sbipTurn c I.1) NodePre (max (c + 2) 4) := by
  obtain ⟨S, d, hs⟩ := exists_caseEnvelope_poly
  exact (poly_comp polyFun_fst (sbipTurn c)).scale S d
    (fun n I hI => ⟨sbipCaseEnvelope n, hs n, hI.turnPre⟩)

theorem sbipNodeGraphs (c : ℕ) :
    TN (Algo.sbipNodeGraphs c) NodePre (max (c + 2) 4) :=
  ((sbipNodeTurn c).comp_poly polyFun_sbipTurnChildren).of_eq
    (fun I => by unfold Algo.sbipNodeGraphs; rfl)

theorem sbipNodeInit (c : ℕ) :
    TN (Algo.sbipNodeInit c) NodePre (max (c + 2) 4) :=
  ((sbipNodeTurn c).comp_poly polyFun_sbipTurnReturns).of_eq
    (fun I => by unfold Algo.sbipNodeInit; rfl)

theorem sbipNodeChild (c : ℕ) :
    TN (Algo.sbipNodeChild c) (fun n z => NodePre n z.1) (max (c + 2) 4) := by
  have hl : TN (fun z : RawSbipNode × ℕ => Algo.sbipNodeGraphs c z.1)
      (fun n z => NodePre n z.1) (max (c + 2) 4) :=
    poly_comp polyFun_fst (sbipNodeGraphs c)
  have ho : TN (fun z : RawSbipNode × ℕ => (Algo.sbipNodeGraphs c z.1)[z.2]?)
      (fun n z => NodePre n z.1) (max (c + 2) 4) :=
    (hl.pair (ofPoly polyFun_snd _ _)).comp_poly polyFun_getElem?
  have hs : PolyFun (fun z : RawSbipStored × RawSbipNode => sbipNodeAdmit (z.2, z.1)) :=
    (polyFun_snd.pair polyFun_fst).comp polyFun_sbipNodeAdmit
  exact ((ho.pair (ofPoly polyFun_fst _ _)).comp_poly
    (PolyFun.optionElim (polyFun_const none) hs)).of_eq
      (fun z => by unfold Algo.sbipNodeChild; rfl)

theorem sbipNodeCombine (c : ℕ) :
    TN (Algo.sbipNodeCombine c)
      (fun n (z : RawSbipNode × ℕ × RawSbipAnswers × RawSbipAnswers) => NodePre n z.1)
      (max (c + 2) 4) := by
  let T := RawSbipNode × ℕ × RawSbipAnswers × RawSbipAnswers
  have hI : PolyFun (fun z : T => z.1) := polyFun_fst
  have hj : PolyFun (fun z : T => z.2.1) := polyFun_snd.comp polyFun_fst
  have hs : PolyFun (fun z : T => z.2.2.1) := (polyFun_snd.comp polyFun_snd).comp polyFun_fst
  have ha : PolyFun (fun z : T => z.2.2.2) := (polyFun_snd.comp polyFun_snd).comp polyFun_snd
  have hparent : PolyFun (fun z : T => (sbipTurnGraphInput z.1.1).1.1.1) :=
    (((hI.comp polyFun_fst).comp polyFun_sbipTurnGraphInput).comp polyFun_fst).comp
      ((polyFun_fst.comp polyFun_fst))
  have hgraphs : TN (fun z : T => Algo.sbipNodeGraphs c z.1) (fun n z => NodePre n z.1)
      (max (c + 2) 4) := poly_comp hI (sbipNodeGraphs c)
  have hchild : TN (fun z : T => (Algo.sbipNodeGraphs c z.1).getD z.2.1 default)
      (fun n z => NodePre n z.1) (max (c + 2) 4) :=
    ((hgraphs.pair (ofPoly hj _ _)).pair (ofPoly (polyFun_const default) _ _)).comp_poly
      polyFun_getD
  have hleft : PolyFun (fun g : RawSbipStored => g.1.1.1) :=
    (polyFun_fst.comp polyFun_fst).comp polyFun_fst
  have hnames := (ofPoly hparent (fun n (z : T) => NodePre n z.1) (max (c + 2) 4)).pair
    (hchild.comp_poly hleft)
  have hrestored := (hnames.pair (ofPoly ha _ _)).comp_poly
    (PolyFun.mapParam polyFun_sbipNodeLift)
  exact ((ofPoly hs _ _).pair hrestored).comp_poly polyFun_append |>.of_eq
    (fun z => by unfold Algo.sbipNodeCombine; rfl)

/-- **One step of the evaluator of Sec. 9**, on a state whose frames carry nodes with
resources bounded by `n`. -/
theorem sbipStepDFS (c : ℕ) :
    TN (sbipRound c).stepDFS SbipStatePre (max (c + 2) 4) := by
  have hch : TN (sbipRound c).child (fun n fr => NodePre n fr.1) (max (c + 2) 4) :=
    (poly_comp (f := fun fr : Round.Frame RawSbipNode RawSbipAnswers => (fr.1, fr.2.1))
      (polyFun_fst.pair (polyFun_snd.comp polyFun_fst)) (sbipNodeChild c)).of_eq
        (fun _ => rfl)
  refine stepDFS (sbipRound c) (PC := fun n fr => NodePre n fr.1) (PI := NodePre)
    (PCo := fun n z => NodePre n z.1) (PF := fun _ _ => True) hch
    (sbipNodeInit c) (sbipNodeCombine c) (ofPoly polyFun_snd _ _) ?_ ?_ ?_ ?_
  · exact fun n fr rest h => h fr (List.mem_cons_self ..)
  · intro n fr rest J h hc
    exact (h fr (List.mem_cons_self ..)).child hc
  · exact fun _ _ _ _ _ _ _ => trivial
  · exact fun n I j s rest a h => h (I, j, s) (List.mem_cons_self ..)

end TN

end Explicit
