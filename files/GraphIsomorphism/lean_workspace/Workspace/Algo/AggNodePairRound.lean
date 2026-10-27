import Workspace.Algo.AggNodeCompareInput

/-! # One paired local-certificate comparison

Each live stage first computes the source group and then the comparison
coset, in the order of `pairedLoopStrong`. The source answer is retained
while the comparison descent runs on the old source kernel and windows.
The last comparison answer opens the next stage, or stops on an empty coset.
-/
namespace Algo
open Babai Equiv
open scoped Pointwise

/-- Source loop, comparison coset, optional completed source answer, cache,
local call index, and state of the current strong descent. -/
abbrev AggnPairState := RawLCLoop × RawCoset × Option RawCoset ×
  AggnRecomputeInput × ℕ × AggnRecomputeState
abbrev AggnPairCtx := RawLCLoop × RawStr × RawCoset
abbrev AggnPairNode := AggnPairCtx × Option RawWinSI

/-- `none` selects the source descent. `some H` retains its completed answer. -/
def aggnPairInput (c : ℕ) (p : RawLCLoop) (ys : RawStr) (q : RawCoset)
    (mode : Option RawCoset) : AggnRecomputeInput :=
  mode.elim (aggnrInputOf c p) (fun _ => aggnCompareInputOf c (p, ys, q))

def aggnPairStart (c : ℕ) (p : RawLCLoop) (ys : RawStr) (q : RawCoset)
    (mode : Option RawCoset) : AggnPairState :=
  let P := aggnPairInput c p ys q mode
  (p, q, mode, P, 0, aggnrInit (P, none))

/-- At a descent boundary, move to line 04e2 or to the next paired stage. -/
def aggnPairPack (c : ℕ) (p : RawLCLoop) (ys : RawStr) (q : RawCoset)
    (mode : Option RawCoset) (j : ℕ) (v : AggnRecomputeState) : AggnPairState :=
  let P := aggnPairInput c p ys q mode
  if v.1 < aggnrCount P then (p, q, mode, P, j, v)
  else mode.elim (aggnPairStart c p ys q (some v.2.2.2))
    (fun H => aggnPairStart c (lcStepWith H p) ys v.2.2.2 none)

/-- A comparison stops after the source loop ends or its coset becomes empty. -/
def aggnPairActive (v : AggnPairState) : Bool := lcCond v.1 && v.2.1.isSome

def aggnPairWidth (C : AggnPairCtx) : ℕ := 2 * aggnCertWidth C.1

def aggnPairChild (z : AggnPairNode × ℕ × AggnPairState) : Option AggnPairNode :=
  z.1.2.elim
    (if lcCond z.2.2.1 = true ∧ z.2.2.2.1.isSome = true ∧ z.2.1 < aggnPairWidth z.1.1 then
      (aggnrChild ((z.2.2.2.2.2.1, none), z.2.2.2.2.2.2.1, z.2.2.2.2.2.2.2)).map
        (fun J => (z.1.1, J.2))
    else none) (fun _ => none)

def aggnPairCombine (c : ℕ) (z : AggnPairNode × ℕ × AggnPairState × RawCoset) : AggnPairState :=
  let v := z.2.2.1
  aggnPairPack c v.1 z.1.1.2.1 v.2.1 v.2.2.1 (v.2.2.2.2.1 + 1)
    (aggnrCombine ((v.2.2.2.1, none), v.2.2.2.2.1, v.2.2.2.2.2, z.2.2.2))

noncomputable def aggnPairDecode (n : ℕ) (I : AggnPairNode) : SIInstance (Fin n) ℕ :=
  I.2.elim (decLCSI n (lcInst I.1.1)) (decWinSI n)

theorem aggnPairChild_some {z : AggnPairNode × ℕ × AggnPairState} {J : AggnPairNode}
    (h : aggnPairChild z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) := by
  cases ho : z.1.2 with
  | some W => simp [aggnPairChild, ho] at h
  | none =>
    simp only [aggnPairChild, ho, Option.elim_none] at h
    split at h
    next hg =>
      obtain ⟨J', hJ', he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨q, _, _, _, _, _, hq⟩ := aggnrChild_some hJ'
      rw [hq] at he
      exact ⟨rfl, _, he.symm⟩
    next => simp at h

/-- Inactive comparisons issue no further calls, at every index. -/
theorem aggnPairChild_none_of_inactive (I : AggnPairNode) (j : ℕ) (v : AggnPairState)
    (h : aggnPairActive v = false) : aggnPairChild (I, j, v) = none := by
  cases ho : I.2 with
  | some W => simp [aggnPairChild, ho]
  | none =>
    simp only [aggnPairChild, ho, Option.elim_none]
    apply if_neg
    rintro ⟨hc, hq, _⟩
    simp [aggnPairActive, hc, hq] at h

/-- A semantic carrier for the paired computation. A checked state boundary
will provide the unconditional size and RAM bounds for this carrier. -/
def aggnPairRound (c n : ℕ) (solve : RawWinSI → RawCoset) :
    Round AggnPairNode AggnPairState RawCoset where
  WF := fun I => I.1.1.1.1.length = n
  ground := fun I => I.1.1.1.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnPairWidth I.1) (fun _ => 0)
  child := aggnPairChild
  init := fun I => aggnPairStart c I.1.1 I.1.2.1 I.1.2.2 none
  combine := aggnPairCombine c
  finish := fun z => z.1.2.elim z.2.2.1 solve
  bot := none
  child_eq_none := by
    intro I j v hj
    cases ho : I.2 with
    | some W => simp [aggnPairChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      simp only [aggnPairChild, ho, Option.elim_none]
      exact if_neg (fun h => Nat.not_lt_of_ge hj h.2.2)
  child_wf := by
    intro I j v J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnPairChild_some hJ
    exact hI
  child_measure := by
    intro I j v J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnPairChild_some hJ
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j v J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnPairChild_some hJ
    exact le_rfl

end Algo
