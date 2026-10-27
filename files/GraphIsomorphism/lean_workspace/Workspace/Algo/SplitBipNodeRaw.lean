import Workspace.Algo.SplitBipTurnRaw
import Workspace.Algo.FamilyEvaluator

/-! A recursive node keeps one bit for the hint stage of Section 9.5.
A decrease of at least one tenth resets the bit. A smaller decrease,
or keeping the count, consumes it and requires a new hint.
The admission check makes the raw recursion total. Its removal on valid
paper calls is a separate progress obligation.

Each returned partition is extended at its own parent. Combining nested
extensions into one extension would merge their complement blocks. -/
namespace Algo
open RAM Babai
set_option maxHeartbeats 1000000

abbrev RawSbipNode := RawSbipTurnInput × ℕ
abbrev RawSbipAnswers := List RawAlignOutcome

def sbipNodeBlocks (I : RawSbipNode) : ℕ := (sbipTurnGraphInput I.1).1.1.2.1.length
def sbipNodeBit (I : RawSbipNode) : ℕ := if I.2 = 0 then 0 else 1
def sbipNodeMeasure (I : RawSbipNode) : ℕ := 2 * sbipNodeBlocks I + sbipNodeBit I
def sbipNodeGround (I : RawSbipNode) : ℕ := I.1.1.length

def sbipNodeGraphs (c : ℕ) (I : RawSbipNode) : List RawSbipStored :=
  sbipTurnChildren (sbipTurn c I.1)

def sbipNodeMakeChild (z : RawSbipNode × RawSbipStored) : RawSbipNode :=
  ((z.1.1.1,(z.2,(sbipTurnCase z.1.1).2.2)),
    if z.2.1.1.2.1.length < sbipNodeBlocks z.1 ∧
      10*z.2.1.1.2.1.length ≤ 9*sbipNodeBlocks z.1 then 1 else 0)

def sbipNodeAdmit (z : RawSbipNode × RawSbipStored) : Option RawSbipNode :=
  if sbipNodeMeasure (sbipNodeMakeChild z) < sbipNodeMeasure z.1 then
    some (sbipNodeMakeChild z) else none

def sbipNodeChild (c : ℕ) (z : RawSbipNode × ℕ) : Option RawSbipNode :=
  ((sbipNodeGraphs c z.1)[z.2]?).elim none (fun g => sbipNodeAdmit (z.1,g))

def sbipNodeInit (c : ℕ) (I : RawSbipNode) : RawSbipAnswers :=
  sbipTurnReturns (sbipTurn c I.1)

def sbipNodeLift (z : (List ℕ × List ℕ) × RawAlignOutcome) : RawAlignOutcome :=
  (z.2.1.map (fun P => rawExtendPartition (z.1,P)),z.2.2)

def sbipNodeCombine (c : ℕ) (z : RawSbipNode × ℕ × RawSbipAnswers × RawSbipAnswers) :
    RawSbipAnswers :=
  z.2.2.1 ++ z.2.2.2.map (fun o => sbipNodeLift
    (((sbipTurnGraphInput z.1.1).1.1.1,
      ((sbipNodeGraphs c z.1).getD z.2.1 default).1.1.1),o))

theorem sbipNodeChild_some {c : ℕ} {I J : RawSbipNode} {j : ℕ}
    (h : sbipNodeChild c (I,j) = some J) :
    ∃ g, (sbipNodeGraphs c I)[j]? = some g ∧
      J = sbipNodeMakeChild (I,g) ∧ sbipNodeMeasure J < sbipNodeMeasure I := by
  unfold sbipNodeChild at h
  cases he : (sbipNodeGraphs c I)[j]? with
  | none => simp [he] at h
  | some g =>
    simp only [he,Option.elim_some] at h
    unfold sbipNodeAdmit at h
    split at h
    · rename_i hm
      have hj : sbipNodeMakeChild (I,g) = J := Option.some.inj h
      exact ⟨g,rfl,hj.symm,hj ▸ hm⟩
    · contradiction

theorem sbipNodeChild_ground {c : ℕ} {I J : RawSbipNode} {j : ℕ}
    (h : sbipNodeChild c (I,j) = some J) : sbipNodeGround J = sbipNodeGround I := by
  obtain ⟨g,_,rfl,_⟩ := sbipNodeChild_some h
  rfl

theorem sbipNodeAdmit_eq (I : RawSbipNode) (g : RawSbipStored)
    (h : sbipNodeMeasure (sbipNodeMakeChild (I,g)) < sbipNodeMeasure I) :
    sbipNodeAdmit (I,g) = some (sbipNodeMakeChild (I,g)) := if_pos h

@[simp] theorem sbipNodeMakeChild_blocks (I : RawSbipNode) (g : RawSbipStored) :
    sbipNodeBlocks (sbipNodeMakeChild (I,g)) = g.1.1.2.1.length := rfl

theorem sbipNodeBit_le (I : RawSbipNode) : sbipNodeBit I ≤ 1 := by
  unfold sbipNodeBit
  split <;> omega

theorem sbipNodeMakeChild_measure (I : RawSbipNode) (g : RawSbipStored) :
    sbipNodeMeasure (sbipNodeMakeChild (I,g)) =
      2*g.1.1.2.1.length + if g.1.1.2.1.length < sbipNodeBlocks I ∧
        10*g.1.1.2.1.length ≤ 9*sbipNodeBlocks I then 1 else 0 := by
  rw [sbipNodeMeasure,sbipNodeMakeChild_blocks]
  by_cases h : g.1.1.2.1.length < sbipNodeBlocks I ∧
      10*g.1.1.2.1.length ≤ 9*sbipNodeBlocks I <;>
    simp [sbipNodeBit,sbipNodeMakeChild,h]

theorem sbipNodeMakeChild_lt_of_drop (I : RawSbipNode) (g : RawSbipStored)
    (h : g.1.1.2.1.length < sbipNodeBlocks I) :
    sbipNodeMeasure (sbipNodeMakeChild (I,g)) < sbipNodeMeasure I := by
  rw [sbipNodeMakeChild_measure,sbipNodeMeasure]
  split <;> omega

theorem sbipNodeMakeChild_lt_of_equal (I : RawSbipNode) (g : RawSbipStored)
    (h : g.1.1.2.1.length = sbipNodeBlocks I) (hb : sbipNodeBit I = 1) :
    sbipNodeMeasure (sbipNodeMakeChild (I,g)) < sbipNodeMeasure I := by
  rw [sbipNodeMakeChild_measure,h,if_neg (by omega),sbipNodeMeasure,hb]
  omega

def sbipRound (c : ℕ) : Round RawSbipNode RawSbipAnswers RawSbipAnswers where
  WF := fun _ => True
  ground := sbipNodeGround
  measure := sbipNodeMeasure
  width := fun I => (sbipNodeGraphs c I).length
  child := fun z => sbipNodeChild c (z.1,z.2.1)
  init := sbipNodeInit c
  combine := sbipNodeCombine c
  finish := Prod.snd
  bot := []
  child_eq_none := by
    intro I j s h
    change sbipNodeChild c (I,j) = none
    simp [sbipNodeChild,List.getElem?_eq_none h]
  child_wf := fun _ _ _ _ _ _ => trivial
  child_measure := by
    intro I j s J _ h
    exact (sbipNodeChild_some h).choose_spec.2.2
  child_ground := by
    intro I j s J _ h
    exact (sbipNodeChild_ground h).le

end Algo
