import Workspace.Algo.TopMasterFour

/-! # Restoring the candidate representative after line 4b
The representative shifts the root answer. Recursive children retain
their own candidate cosets, so their answers are passed through unchanged.
This is Equation (59) around the supplied top-action phase.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev Master4Node := Top4wNode × RawPerm
def master4X (I : Master4Node) : RawStr := I.1.1.1.2.2
def master4Child (e f u v : ℕ) (z : Master4Node × ℕ × Top4State) : Option Master4Node :=
  (top4wChild e f u v (z.1.1, z.2)).map (fun J => (J, z.1.2))
def master4Init (I : Master4Node) : Top4State := top4wInit I.1
def master4Combine (z : Master4Node × ℕ × Top4State × RawCoset) : Top4State :=
  top4wCombine (z.1.1, z.2)
def master4Finish (solve : RawWinSI → RawCoset) (z : Master4Node × Top4State) : RawCoset :=
  z.1.1.2.elim
    (top3Shift (master4X z.1, z.1.2, top4wFinish solve (z.1.1, z.2)))
    (fun _ => top4wFinish solve (z.1.1, z.2))
def Master4WF (a b c d e f u v : ℕ) (I : Master4Node) : Prop :=
  Top4wWF a b c d e f u v I.1 ∧ Enc.size I.2 ≤ strBound (master4X I).length
noncomputable def master4Decode (n : ℕ) (I : Master4Node) : SIInstance (Fin n) ℕ :=
  top4wDecode n I.1

def master4Round (a b c d e f u v : ℕ) (solve : RawWinSI → RawCoset) :
    Round Master4Node Top4State RawCoset where
  WF := Master4WF a b c d e f u v
  ground I := (master4X I).length
  measure I := (top4wRound a b c d e f u v solve).measure I.1
  width I := (top4wRound a b c d e f u v solve).width I.1
  child := master4Child e f u v
  init := master4Init
  combine := master4Combine
  finish := master4Finish solve
  bot := none
  child_eq_none := by
    intro I j s hj
    have h := (top4wRound a b c d e f u v solve).child_eq_none I.1 j s hj
    change top4wChild e f u v (I.1, j, s) = none at h
    simp [master4Child, h]
  child_wf := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    have hK := (top4wRound a b c d e f u v solve).child_wf I.1 j s K hI.1 hk
    obtain ⟨_, W, rfl, _⟩ := top4wChild_some hk
    exact ⟨hK, hI.2⟩
  child_measure := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact (top4wRound a b c d e f u v solve).child_measure I.1 j s K hI.1 hk
  child_ground := by
    intro I j s J hI hc
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact (top4wRound a b c d e f u v solve).child_ground I.1 j s K hI.1 hk

theorem master4LoopMatch {n a b c d e f u v : ℕ} {C : Top4wContext} {r : RawPerm}
    (hx : C.1.2.2.length = n) (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : Top4State} {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))},
      LoopMatch (top4wRound a b c d e f u v solve) (top4wDecode n) (decCoset n) (C, none) w j s T →
      LoopMatch (master4Round a b c d e f u v solve) (master4Decode n) (decCoset n) ((C, none), r)
        w j s (T.bind (fun A => .done (decPerm n r • A))) := by
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    change top4wChild e f u v ((C, none), j, s) = none at hc
    change decCoset n (top4wFinish solve ((C, none), s)) = A at ha
    refine .done w j s _ ?_ ?_
    · change (top4wChild e f u v ((C, none), j, s)).map _ = none
      rw [hc]
      rfl
    · change decCoset n (top3Shift (C.1.2.2, r, top4wFinish solve ((C, none), s))) = _
      rw [decCoset_top3Shift hx, ha]
  | call w j s J k hc hn ih =>
    change top4wChild e f u v ((C, none), j, s) = some J at hc
    change LoopMatch _ _ _ _ (w + 1) j s (.call (master4Decode n (J, r)) _)
    refine .call w j s (J, r) _ ?_ ?_
    · change (top4wChild e f u v ((C, none), j, s)).map _ = some (J, r)
      rw [hc]
      rfl
    · exact fun A hA => ih A hA

def master4Enter (p : MasterHintInput) : Master4Node :=
  (masterLine4bEnter p, normPerm (p.1.2.2.2.1, p.1.2.2.1))

end Algo
