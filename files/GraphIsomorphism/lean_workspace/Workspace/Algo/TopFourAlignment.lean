import Workspace.Algo.TopFourCost

/-! # Supplied alignment around the top-action 4 body
The final alignment multiplies the answer on the left. Recursive child
answers remain in their own coordinates. The Boolean guard records equality
of the two relevant color-class cardinalities.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev Top4aNode := Top4Node × RawPerm × Bool

def top4aGate (I : Top4aNode) : Bool := I.1.2.elim I.2.2 (fun _ => true)
def top4aChild (e f : ℕ) (z : Top4aNode × ℕ × Top4State) : Option Top4aNode :=
  if top4aGate z.1 then (top4Child e f (z.1.1, z.2)).map (fun J => (J, z.1.2)) else none
def top4aInit (I : Top4aNode) : Top4State := top4Init I.1
def top4aCombine (z : Top4aNode × ℕ × Top4State × RawCoset) : Top4State := top4Combine (z.1.1, z.2)
def top4aFinish (solve : RawWinSI → RawCoset) (z : Top4aNode × Top4State) : RawCoset :=
  z.1.1.2.elim
    (if z.1.2.2 then top3Shift (top4X z.1.1.1, z.1.2.1, top4Finish solve (z.1.1, z.2)) else none)
    (fun _ => top4Finish solve (z.1.1, z.2))
def Top4aWF (c d e f : ℕ) (I : Top4aNode) : Prop :=
  Top4WF c d e f I.1 ∧ Enc.size I.2.1 ≤ strBound (top4X I.1.1).length
noncomputable def top4aDecode (n : ℕ) (I : Top4aNode) : SIInstance (Fin n) ℕ := top4Decode n I.1

theorem top4aChild_some {e f : ℕ} {z : Top4aNode × ℕ × Top4State} {J : Top4aNode}
    (h : top4aChild e f z = some J) :
    top4aGate z.1 = true ∧ ∃ K, top4Child e f (z.1.1, z.2) = some K ∧ J = (K, z.1.2) := by
  unfold top4aChild at h
  split at h
  next hg =>
    obtain ⟨K, hK, he⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hg, K, hK, he.symm⟩
  next => simp at h

def top4aRound (c d e f : ℕ) (solve : RawWinSI → RawCoset) : Round Top4aNode Top4State RawCoset where
  WF := Top4aWF c d e f
  ground := fun I => (top4X I.1.1).length
  measure := fun I => I.1.2.elim 1 (fun _ => 0)
  width := fun I => if top4aGate I then (top4Round c d e f solve).width I.1 else 0
  child := top4aChild e f
  init := top4aInit
  combine := top4aCombine
  finish := top4aFinish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold top4aChild
    split
    next hg =>
      rw [if_pos hg] at hj
      have hn := (top4Round c d e f solve).child_eq_none I.1 j s hj
      change top4Child e f (I.1, j, s) = none at hn
      rw [hn]
      rfl
    next => rfl
  child_wf := by
    intro I j s J hI hc
    obtain ⟨_, K, hK, rfl⟩ := top4aChild_some hc
    obtain ⟨_, W, rfl, hW⟩ := top4Child_some hK
    exact ⟨⟨hI.1.1, fun V hV => by cases Option.some.inj hV; exact hW⟩, hI.2⟩
  child_measure := by
    intro I j s J hI hc
    obtain ⟨_, K, hK, rfl⟩ := top4aChild_some hc
    exact (top4Round c d e f solve).child_measure I.1 j s K hI.1 hK
  child_ground := by
    intro I j s J hI hc
    obtain ⟨_, K, hK, rfl⟩ := top4aChild_some hc
    exact (top4Round c d e f solve).child_ground I.1 j s K hI.1 hK

 theorem top4aLoopMatch {n c d e f : ℕ} {C : Top4Context} {α : RawPerm}
    (hx : (top4X C).length = n) (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : Top4State} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))},
      LoopMatch (top4Round c d e f solve) (top4Decode n) (decCoset n) (C, none) w j s T →
      LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) ((C, none), α, true)
        w j s (T.bind (fun a => .done (decPerm n α • a))) := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    change top4Child e f ((C, none), j, s) = none at hc
    change decCoset n (top4Finish solve ((C, none), s)) = a at ha
    refine .done w j s _ ?_ ?_
    · change (top4Child e f ((C, none), j, s)).map _ = none
      rw [hc]
      rfl
    · change decCoset n (top3Shift (top4X C, α, top4Finish solve ((C, none), s))) = _
      rw [decCoset_top3Shift hx, ha]
  | call w j s J k hc hn ih =>
    change top4Child e f ((C, none), j, s) = some J at hc
    change LoopMatch _ _ _ _ (w + 1) j s (.call (top4aDecode n (J, α, true)) _) 
    refine .call w j s (J, α, true) _ ?_ ?_
    · change (top4Child e f ((C, none), j, s)).map _ = some (J, α, true)
      rw [hc]
      rfl
    · exact fun a ha => ih a ha

 theorem top4aLoopMismatch {n c d e f : ℕ} (C : Top4Context) (α : RawPerm)
    (solve : RawWinSI → RawCoset) (w j : ℕ) (s : Top4State) :
    LoopMatch (top4aRound c d e f solve) (top4aDecode n) (decCoset n) ((C, none), α, false)
      w j s (.done ∅) := .done w j s ∅ rfl rfl

end Algo
