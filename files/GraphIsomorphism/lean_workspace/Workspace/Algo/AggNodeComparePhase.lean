import Workspace.Algo.AggNodePairPrepare

/-! # Sequencing all local-certificate comparisons

Section 13.2 compares every ordered pair of test sets for the source
string and then for the target string. The state retains the pending jobs
and the answers already completed. The scan skips only jobs with no calls.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

abbrev AggnCompareJob := Bool × List ℕ × List ℕ
abbrev AggnCompareState := List AggnCompareJob × List RawCoset × ℕ × AggnPairState

def aggnCompareJobs (c : ℕ) (C : AggnPhaseCtx) : List AggnCompareJob :=
  [false, true].flatMap fun b => (aggnPhaseRows c C).flatMap fun row =>
    (aggnPhaseRows c C).map fun row' => (b, row, row')

def aggnCompareCtx (C : AggnPhaseCtx) (a : AggnCompareJob) : AggnPairCtx :=
  aggnPairPrepare (C.1, C.2.1, cond a.1 C.2.2.1 C.2.1, a.2.1, a.2.2)

def aggnCompareOpen (c : ℕ) (C : AggnPhaseCtx) (a : AggnCompareJob) : AggnPairState :=
  let P := aggnCompareCtx C a
  aggnPairStart c P.1 P.2.1 P.2.2 none

def aggnCompareScan (c : ℕ) (C : AggnPhaseCtx) :
    List AggnCompareJob → List RawCoset → AggnCompareState
  | [], answers => ([], answers, 0, aggnPairStart c (([], []), ([], [], [])) [] none none)
  | a :: rest, answers =>
    let v := aggnCompareOpen c C a
    if aggnPairActive v then (a :: rest, answers, 0, v)
    else aggnCompareScan c C rest (v.2.1 :: answers)

def aggnComparePack (c : ℕ) (C : AggnPhaseCtx) (a : AggnCompareJob) (rest : List AggnCompareJob)
    (answers : List RawCoset) (j : ℕ) (v : AggnPairState) : AggnCompareState :=
  if aggnPairActive v then (a :: rest, answers, j, v)
  else aggnCompareScan c C rest (v.2.1 :: answers)

def aggnCompareJobWidth (C : AggnPhaseCtx) : ℕ := 2 * aggnJobWidth C

def aggnCompareWidth (c : ℕ) (C : AggnPhaseCtx) : ℕ :=
  (aggnCompareJobs c C).length * aggnCompareJobWidth C

def aggnCompareChild (c : ℕ) (z : AggnPhaseNode × ℕ × AggnCompareState) : Option AggnPhaseNode :=
  z.1.2.elim
    (if z.2.1 < aggnCompareWidth c z.1.1 then
      match z.2.2.1 with
      | [] => none
      | a :: _ =>
        (aggnPairChild ((aggnCompareCtx z.1.1 a, none), z.2.2.2.2.1, z.2.2.2.2.2)).map
          (fun J => (z.1.1, J.2))
    else none) (fun _ => none)

def aggnCompareCombine (c : ℕ) (z : AggnPhaseNode × ℕ × AggnCompareState × RawCoset) :
    AggnCompareState :=
  match z.2.2.1.1 with
  | [] => aggnCompareScan c z.1.1 [] z.2.2.1.2.1
  | a :: rest => aggnComparePack c z.1.1 a rest z.2.2.1.2.1 (z.2.2.1.2.2.1 + 1)
      (aggnPairCombine c ((aggnCompareCtx z.1.1 a, none), z.2.2.1.2.2.1,
        z.2.2.1.2.2.2, z.2.2.2))

theorem aggnCompareChild_some {c : ℕ} {z : AggnPhaseNode × ℕ × AggnCompareState} {J : AggnPhaseNode}
    (h : aggnCompareChild c z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some W) := by
  cases ho : z.1.2 with
  | some W => simp [aggnCompareChild, ho] at h
  | none =>
    simp only [aggnCompareChild, ho, Option.elim_none] at h
    split at h
    next hg =>
      cases ht : z.2.2.1 with
      | nil => simp [ht] at h
      | cons a rest =>
        rw [ht] at h
        obtain ⟨J', hJ', he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨_, W, hW⟩ := aggnPairChild_some hJ'
        rw [hW] at he
        exact ⟨rfl, W, he.symm⟩
    next => simp at h

/-- The comparison phase retains its parent context at each window leaf. -/
def aggnCompareRound (c n : ℕ) : Round AggnPhaseNode AggnCompareState RawCoset where
  WF := fun I => I.1.2.1.length = n
  ground := fun I => I.1.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnCompareWidth c I.1) (fun _ => 0)
  child := aggnCompareChild c
  init := fun I => aggnCompareScan c I.1 (aggnCompareJobs c I.1) []
  combine := aggnCompareCombine c
  finish := fun _ => none
  bot := none
  child_eq_none := by
    intro I j v hj
    cases ho : I.2 with
    | some W => simp [aggnCompareChild, ho]
    | none =>
      simp only [ho, Option.elim_none] at hj
      simp only [aggnCompareChild, ho, Option.elim_none]
      exact if_neg (Nat.not_lt_of_ge hj)
  child_wf := by
    intro I j v J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnCompareChild_some hJ
    exact hI
  child_measure := by
    intro I j v J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnCompareChild_some hJ
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j v J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnCompareChild_some hJ
    exact le_rfl

end Algo
