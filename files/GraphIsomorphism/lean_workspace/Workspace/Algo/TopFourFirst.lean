import Workspace.Algo.TopFourRound

/-! # Embedding the restricted phase in top-action 4
Only calls need to agree during this phase. At its last state the outer
round is already allowed to begin the next Chain Rule.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 theorem top4_inner_call {C : Top4Context} {e f j : ℕ} {s : TopcsState} {J : TopwpNode}
    (h : topwpChild e f ((C.1, none), j, s) = some J) :
    s.1 < topcsJobs C.1.2 ∧ j < top4Base C := by
  simp only [topwpChild, Option.elim_none] at h
  obtain ⟨K, hK, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, _, ht, _, hj, _⟩ := topcsChild_some hK
  exact ⟨ht, hj⟩

 theorem top4Loop_inner {n c d e f : ℕ} {β : Type*} (C : Top4Context)
    (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : TopcsState} {T : SIReduction (Fin n) ℕ β}
      {Q : β → ℕ → ℕ → TopcsState → Prop},
      LoopMatchK (topwpRound c d e f solve) (topwpDecode n) (decCoset n)
        (C.1, none) w j s T Q →
      LoopMatchK (top4Round c d e f solve) (top4Decode n) (decCoset n)
        (C, none) w j (top4Open C s) T
        (fun b w' j' s' => ∃ u, s' = top4Open C u ∧ Q b w' j' u) := by
  intro w j s T Q h
  induction h with
  | done w j s b Q hb => exact .done w j (top4Open C s) b _ ⟨s, rfl, hb⟩
  | call w j s J k Q hc hn ih =>
    change topwpChild e f ((C.1, none), j, s) = some J at hc
    obtain ⟨ht, hj⟩ := top4_inner_call hc
    obtain ⟨_, W, rfl, _⟩ := topwpChild_some hc
    have hchild : top4Child e f ((C, none), j, top4Open C s) = some (C, some W) := by
      simp only [top4Child, Option.elim_none, top4Open]
      rw [if_pos (show j < top4Width C by unfold top4Width; omega), if_pos ht, hc]
      rfl
    change LoopMatchK _ _ _ _ (w + 1) j (top4Open C s)
      (.call (top4Decode n (C, some W)) k) _
    refine .call w j (top4Open C s) (C, some W) k _ hchild ?_
    intro a ha
    change LoopMatchK _ _ _ _ w (j + 1) (top4Combine ((C, none), j, top4Open C s, a)) _ _
    simpa only [top4Combine, top4Open, if_pos ht] using ih a ha

 theorem top4Phase_inner {n c d e f b j : ℕ} {β : Type*} {C : Top4Context}
    {s : TopcsState} {T : SIReduction (Fin n) ℕ β} {Q : β → ℕ → TopcsState → Prop}
    (solve : RawWinSI → RawCoset)
    (h : PhaseMatch (topwpRound c d e f solve) (topwpDecode n) (decCoset n)
      (C.1, none) b j s T Q) :
    PhaseMatch (top4Round c d e f solve) (top4Decode n) (decCoset n)
      (C, none) b j (top4Open C s) T
      (fun a j' s' => ∃ u, s' = top4Open C u ∧ Q a j' u) := by
  intro r
  exact loopMatchK_mono_Q (fun a w' j' s' ⟨u, hs, hr, hq⟩ =>
    ⟨hr, u, hs, hq⟩) (top4Loop_inner C solve (h r))

/-- The value at the end of a matched phase is its checked mathematical
value. This follows from the answer used at each call, not a raw oracle. -/
 theorem top4Loop_value {ι ω α β : Type*} {Ω A : Type*}
    {R : Round ι ω α} {decI : ι → SIInstance Ω A} {decA : α → Set (Perm Ω)} {I : ι} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A β} {Q : β → ℕ → ℕ → ω → Prop},
      LoopMatchK R decI decA I w j s T Q →
      LoopMatchK R decI decA I w j s T (fun b w' j' s' => b = T.run ∧ Q b w' j' s') := by
  intro w j s T Q h
  induction h with
  | done w j s b Q hb => exact .done w j s b _ ⟨rfl, hb⟩
  | call w j s J k Q hc hn ih =>
    exact .call w j s J k _ hc (fun a ha => ih a ha)

 theorem top4Phase_value {ι ω α β : Type*} {Ω A : Type*}
    {R : Round ι ω α} {decI : ι → SIInstance Ω A} {decA : α → Set (Perm Ω)} {I : ι}
    {b j : ℕ} {s : ω} {T : SIReduction Ω A β} {Q : β → ℕ → ω → Prop}
    (h : PhaseMatch R decI decA I b j s T Q) :
    PhaseMatch R decI decA I b j s T (fun a j' s' => a = T.run ∧ Q a j' s') := by
  intro r
  exact loopMatchK_mono_Q (fun a w' j' s' ⟨he, hr, hq⟩ => ⟨hr, he, hq⟩) (top4Loop_value (h r))

end Algo
