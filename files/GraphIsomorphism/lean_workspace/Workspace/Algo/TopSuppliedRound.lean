import Workspace.Algo.TopCosetRAM
import Workspace.Algo.TopThreeRound

/-! # The flat supplied-data round of Corollary 12.0.8

The first jobs test the identity and the supplied alternating generators on
the source string. The last two jobs test the kernel and the supplied odd
coset against the target. Every job uses the same stored kernel windows.
Cosets keep the original strings throughout. The outer option in the
accumulator distinguishes a failed giant test from an empty isomorphism set.
-/

namespace Algo

open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- Source, target, windows, lifting cosets, kernel, odd coset, all-even flag, ambient generators. -/
abbrev TopcsInput := RawStr × RawStr × List (List ℕ) × List RawCoset × RawCoset × RawCoset × (Bool × RawGens)
abbrev TopcsNode := TopcsInput × Option RawWinSI
abbrev TopcsState := Top3State

def topcsX (P : TopcsInput) : RawStr := P.1
def topcsY (P : TopcsInput) : RawStr := P.2.1
def topcsWins (P : TopcsInput) : List (List ℕ) := P.2.2.1
def topcsTests (P : TopcsInput) : List RawCoset := P.2.2.2.1
def topcsKernel (P : TopcsInput) : RawCoset := P.2.2.2.2.1
def topcsOdd (P : TopcsInput) : RawCoset := P.2.2.2.2.2.1
def topcsEven (P : TopcsInput) : Bool := P.2.2.2.2.2.2.1
def topcsAmbient (P : TopcsInput) : RawGens := P.2.2.2.2.2.2.2
def topcsCount (P : TopcsInput) : ℕ := (topcsTests P).length
def topcsJobs (P : TopcsInput) : ℕ := topcsCount P + 2

def topcsTgt (P : TopcsInput) (t : ℕ) : RawStr :=
  if t < topcsCount P then topcsX P else topcsY P

/-- Normalize every stored start, including starts selected on malformed input. -/
def topcsBegin (P : TopcsInput) (t : ℕ) : RawCoset :=
  top2NormC (topcsX P)
    (if t < topcsCount P then (topcsTests P).getD t none
     else if t = topcsCount P then topcsKernel P else topcsOdd P)

def topcsLeaf (P : TopcsInput) (t i : ℕ) (c : RawGens × RawPerm) : RawWinSI :=
  ((topcsWins P).getD i [], tidyGens (topcsX P, c.1), normPerm (topcsX P, c.2),
    topcsX P, topcsTgt P t)

def topcsChild (z : TopcsNode × ℕ × TopcsState) : Option TopcsNode :=
  z.1.2.elim
    (if z.2.2.1 < topcsJobs z.1.1 ∧ z.2.2.2.1 < (topcsWins z.1.1).length ∧
        z.2.1 < topcsJobs z.1.1 * (topcsWins z.1.1).length then
      z.2.2.2.2.1.map (fun c => (z.1.1, some (topcsLeaf z.1.1 z.2.2.1 z.2.2.2.1 c)))
    else none) (fun _ => none)

/-- Close a job, aggregate its result and open the next job in the same step. -/
def topcsClose (P : TopcsInput) (t : ℕ) (acc : Top1State) (s1 s2 a : RawCoset) : TopcsState :=
  let A := top2NormS (topcsX P) (top1Join (topcsX P, acc, a))
  if t + 1 < topcsCount P then
    (t + 1, 0, topcsBegin P (t + 1), A, top2NormC (topcsX P) s1, top2NormC (topcsX P) s2)
  else if t + 1 = topcsCount P then
    (if A.isSome then topcsCount P else topcsJobs P, 0, topcsBegin P (topcsCount P), A,
      top2NormC (topcsX P) s1, top2NormC (topcsX P) s2)
  else if t = topcsCount P then
    (if topcsEven P then topcsJobs P else topcsCount P + 1, 0,
      topcsBegin P (topcsCount P + 1), top2NormS (topcsX P) acc,
      top2NormC (topcsX P) a, top2NormC (topcsX P) s2)
  else
    (topcsJobs P, 0, topcsBegin P (topcsJobs P), top2NormS (topcsX P) acc,
      top2NormC (topcsX P) s1, top2NormC (topcsX P) a)

def topcsStep (P : TopcsInput) (t i : ℕ) (acc : Top1State) (s1 s2 a : RawCoset) : TopcsState :=
  if a.isSome = true ∧ i + 1 < (topcsWins P).length then
    (min t (topcsJobs P), min (i + 1) (topcsWins P).length, top2NormC (topcsX P) a,
      top2NormS (topcsX P) acc, top2NormC (topcsX P) s1, top2NormC (topcsX P) s2)
  else topcsClose P t acc s1 s2 a

def topcsInit (I : TopcsNode) : TopcsState :=
  (0, 0, topcsBegin I.1 0, some none, none, none)

def topcsCombine (z : TopcsNode × ℕ × TopcsState × RawCoset) : TopcsState :=
  topcsStep z.1.1 z.2.2.1.1 z.2.2.1.2.1 z.2.2.1.2.2.2.1
    z.2.2.1.2.2.2.2.1 z.2.2.1.2.2.2.2.2 z.2.2.2

/-- Reconstruct the answer with coset products. The odd coset was already
used as the second starting set, so no later translation is made. -/
def topcsAnswer (P : TopcsInput) (s : TopcsState) : Top1State :=
  s.2.2.2.1.map (fun a =>
    if topcsEven P then top3Prod (topcsX P, s.2.2.2.2.1, a)
    else rawCosetJoin (topcsX P, top3Prod (topcsX P, s.2.2.2.2.1, a),
      top3Prod (topcsX P, s.2.2.2.2.2, a)))

def topcsFinish (solve : RawWinSI → RawCoset) (z : TopcsNode × TopcsState) : RawCoset :=
  z.1.2.elim ((topcsAnswer z.1.1 z.2).getD none) solve

noncomputable def topcsDecode (n : ℕ) (I : TopcsNode) : SIInstance (Fin n) ℕ :=
  I.2.elim ⟨decGroup n (topcsAmbient I.1), Set.univ, decStrN n (topcsX I.1), decStrN n (topcsY I.1)⟩ (decWinSI n)

/-- `B` bounds the prepared context in the original domain size. It is an
input-size bound, not an assumption about the machine's behavior. -/
def TopcsWF (n : ℕ) (B : ℕ → ℕ) (I : TopcsNode) : Prop :=
  (topcsX I.1).length = n ∧ Enc.size I.1 ≤ B n ∧
    ∀ W, I.2 = some W → ∃ t i c, W = topcsLeaf I.1 t i c

theorem topcsChild_some {z : TopcsNode × ℕ × TopcsState} {J : TopcsNode}
    (h : topcsChild z = some J) :
    ∃ c, z.1.2 = none ∧ z.2.2.2.2.1 = some c ∧
      z.2.2.1 < topcsJobs z.1.1 ∧ z.2.2.2.1 < (topcsWins z.1.1).length ∧
      z.2.1 < topcsJobs z.1.1 * (topcsWins z.1.1).length ∧
      J = (z.1.1, some (topcsLeaf z.1.1 z.2.2.1 z.2.2.2.1 c)) := by
  cases ho : z.1.2 with
  | some W => simp [topcsChild, ho] at h
  | none =>
    simp only [topcsChild, ho, Option.elim_none] at h
    split at h
    next hc =>
      obtain ⟨c, hs, hJ⟩ := Option.map_eq_some_iff.mp h
      exact ⟨c, rfl, hs, hc.1, hc.2.1, hc.2.2, hJ.symm⟩
    next => simp at h

def topcsRound (n : ℕ) (B : ℕ → ℕ) (solve : RawWinSI → RawCoset) :
    Round TopcsNode TopcsState RawCoset where
  WF := TopcsWF n B
  ground := fun I => (topcsX I.1).length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (topcsJobs I.1 * (topcsWins I.1).length) (fun _ => 0)
  child := topcsChild
  init := topcsInit
  combine := topcsCombine
  finish := topcsFinish solve
  bot := none
  child_eq_none := by
    rintro ⟨P, o⟩ j s hj
    cases o with
    | some W => rfl
    | none =>
      simp only [topcsChild, Option.elim_none]
      exact if_neg (fun h => Nat.not_lt_of_ge hj h.2.2)
  child_wf := by
    intro I j s J hI hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := topcsChild_some hc
    exact ⟨hI.1, hI.2.1, fun W hW => ⟨s.1, s.2.1, c, (Option.some.inj hW).symm⟩⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨c, ho, _, _, _, _, rfl⟩ := topcsChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := topcsChild_some hc
    exact le_rfl

theorem topcsDecode_leaf {n : ℕ} {P : TopcsInput} (hx : (topcsX P).length = n)
    (t i : ℕ) (c : RawGens × RawPerm) :
    topcsDecode n (P, some (topcsLeaf P t i c)) =
      ⟨decCoset n (some c), winSet n ((topcsWins P).getD i []),
        decStrN n (topcsX P), decStrN n (topcsTgt P t)⟩ := by
  change decWinSI n (topcsLeaf P t i c) = _
  simp only [decWinSI, topcsLeaf, decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]
  rw [show c = (c.1, c.2) from rfl, decCoset_some]

end Algo
