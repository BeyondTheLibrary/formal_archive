import Workspace.Algo.TopCosetLift
import Workspace.Algo.PhaseUnion

/-! # A lifting test as an exact raw phase

The input stores the original strings, computed orbit order and preimage
coset. The node asks the Chain Rule calls itself. Answers may have arbitrary
encodings: the next child normalizes the group and representative before
using them. This is a local phase carrier, not the master recursion measure.
-/

namespace Algo

open Babai Equiv
open scoped Pointwise

/-- Original strings, ordered windows, and the initial candidate coset. -/
abbrev TopCosetChainInput := RawStr × RawStr × List (List ℕ) × RawCoset

abbrev TopCosetChainNode := TopCosetChainInput × Option RawWinSI

/-- Proposition 12.0.1 followed by the orbit chain of Corollary 12.0.6. -/
def topclPrepare (p : RawTopLift) : TopCosetChainInput :=
  (p.2.2.1, p.2.2.2, topKernelWindows p.1, topCosetStart (p.1, p.2.1))

/-- A child reads the original strings and the current candidate coset. -/
def topclLeaf (P : TopCosetChainInput) (j : ℕ) (c : RawGens × RawPerm) : RawWinSI :=
  (P.2.2.1.getD j [], tidyGens (P.1, c.1), normPerm (P.1, c.2), P.1, P.2.1)

def topclChild (z : TopCosetChainNode × ℕ × RawCoset) : Option TopCosetChainNode :=
  z.1.2.elim
    (if z.2.1 < z.1.1.2.2.1.length then
      z.2.2.map (fun c => (z.1.1, some (topclLeaf z.1.1 z.2.1 c)))
    else none) (fun _ => none)

def topclInit (I : TopCosetChainNode) : RawCoset := I.1.2.2.2

def topclCombine (z : TopCosetChainNode × ℕ × RawCoset × RawCoset) : RawCoset := z.2.2.2

def topclFinish (solve : RawWinSI → RawCoset) (z : TopCosetChainNode × RawCoset) : RawCoset :=
  z.1.2.elim z.2 solve

noncomputable def topclDecode (n : ℕ) (I : TopCosetChainNode) : SIInstance (Fin n) ℕ :=
  I.2.elim ⟨decCoset n I.1.2.2.2, Set.univ, decStrN n I.1.1, decStrN n I.1.2.1⟩
    (decWinSI n)

/-- The optional cached window is a leaf produced by this local carrier. -/
def topclWF (n : ℕ) (I : TopCosetChainNode) : Prop :=
  I.1.1.length = n ∧ ∀ W, I.2 = some W → ∃ j c, W = topclLeaf I.1 j c

theorem topclChild_some {z : TopCosetChainNode × ℕ × RawCoset} {J : TopCosetChainNode}
    (h : topclChild z = some J) :
    ∃ c, z.1.2 = none ∧ z.2.2 = some c ∧ z.2.1 < z.1.1.2.2.1.length ∧
      J = (z.1.1, some (topclLeaf z.1.1 z.2.1 c)) := by
  cases ho : z.1.2 with
  | some W => simp [topclChild, ho] at h
  | none =>
    simp only [topclChild, ho, Option.elim_none] at h
    split at h
    next hj =>
      obtain ⟨c, hs, hJ⟩ := Option.map_eq_some_iff.mp h
      exact ⟨c, rfl, hs, hj, hJ.symm⟩
    next => simp at h

/-- A local round for a single preimage chain. The leaf solver is external
to the phase, as are the master measure and its window size bounds. -/
def topclRound (n : ℕ) (solve : RawWinSI → RawCoset) :
    Round TopCosetChainNode RawCoset RawCoset where
  WF := topclWF n
  ground := fun I => I.1.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim I.1.2.2.1.length (fun _ => 0)
  child := topclChild
  init := topclInit
  combine := topclCombine
  finish := topclFinish solve
  bot := none
  child_eq_none := by
    rintro ⟨P, o⟩ j s hj
    cases o with
    | some W => rfl
    | none =>
      simp only [topclChild, Option.elim_none]
      exact if_neg (Nat.not_lt_of_ge hj)
  child_wf := by
    intro I j s J hI hc
    obtain ⟨c, _, _, _, rfl⟩ := topclChild_some hc
    exact ⟨hI.1, fun W hW => ⟨j, c, (Option.some.inj hW).symm⟩⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨c, ho, _, _, rfl⟩ := topclChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨c, _, _, _, rfl⟩ := topclChild_some hc
    exact le_rfl

section Match

variable {n : ℕ} {P : TopCosetChainInput}

theorem topclDecode_leaf (hx : P.1.length = n) (j : ℕ) (c : RawGens × RawPerm) :
    topclDecode n (P, some (topclLeaf P j c)) =
      ⟨decCoset n (some c), winSet n (P.2.2.1.getD j []), decStrN n P.1, decStrN n P.2.1⟩ := by
  change decWinSI n (topclLeaf P j c) = _
  simp only [decWinSI, topclLeaf, decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]
  rw [show c = (c.1, c.2) from rfl, decCoset_some]

/-- The remaining windows are the stored suffix, unless the chain has failed. -/
def topclInv (n : ℕ) (P : TopCosetChainInput)
    (Δs : List (Set (Fin n))) (C : Set (Perm (Fin n))) (j : ℕ) (s : RawCoset) : Prop :=
  decCoset n s = C ∧ (Δs = (P.2.2.1.drop j).map (winSet n) ∨ C = ∅)

/-- The raw fold matches each call, with the same strings and candidate set.
Only the decoding of each answer is required, not its representation. -/
theorem topclPhase_chain (solve : RawWinSI → RawCoset) (hx : P.1.length = n) :
    ∀ Δs C j s, topclInv n P Δs C j s →
      PhaseMatch (topclRound n solve) (topclDecode n) (decCoset n) (P, none)
        Δs.length j s (Babai.cosetChain (decStrN n P.1) (decStrN n P.2.1) Δs C)
        (fun C' j' s' => topclInv n P [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (topclInv n P) ?_ ?_ Δs C j s h
  · intro Δ rest C j s h hC
    obtain ⟨hs, hlist⟩ := h
    have he := hlist.resolve_right hC
    have hj : j < P.2.2.1.length := by
      by_contra hj
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at he
      cases he
    rw [List.drop_eq_getElem_cons hj, List.map_cons] at he
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    obtain ⟨q, rfl⟩ : ∃ q, s = some q := by
      cases s with
      | none => exact (hC hs.symm).elim
      | some q => exact ⟨q, rfl⟩
    refine ⟨(P, some (topclLeaf P j q)), ?_, ?_, ?_⟩
    · change topclChild ((P, none), j, some q) = _
      simp only [topclChild, Option.elim_none, if_pos hj, Option.map_some]
    · rw [topclDecode_leaf hx, List.getD_eq_getElem _ _ hj, hs]
    · intro a ha
      exact ⟨ha, Or.inl rfl⟩
  · intro Δs C j s h he
    exact ⟨h.1.trans he, Or.inr rfl⟩

theorem topclInv_finish (solve : RawWinSI → RawCoset)
    {C : Set (Perm (Fin n))} {j : ℕ} {s : RawCoset} (h : topclInv n P [] C j s) :
    (topclRound n solve).child ((P, none), j, s) = none ∧
      decCoset n ((topclRound n solve).finish ((P, none), s)) = C := by
  refine ⟨?_, h.1⟩
  change topclChild ((P, none), j, s) = none
  simp only [topclChild, Option.elim_none]
  rcases h.2 with hw | he
  · have hh := congrArg List.length hw
    simp only [List.length_nil, List.length_map, List.length_drop] at hh
    rw [if_neg (by omega)]
  · have hs : s = none := by
      cases s with
      | none => rfl
      | some q =>
        have hm : decPerm n q.2 ∈ decCoset n (some q) :=
          ⟨1, one_mem _, by rw [mul_one]⟩
        rw [h.1, he] at hm
        exact hm.elim
    simp [hs]

/-- Exact matching of the complete local chain, including its stopping rule. -/
theorem topclLoop_chain (solve : RawWinSI → RawCoset) (hx : P.1.length = n) :
    LoopMatch (topclRound n solve) (topclDecode n) (decCoset n) (P, none)
      P.2.2.1.length 0 (topclInit (P, none))
      (Babai.cosetChain (decStrN n P.1) (decStrN n P.2.1)
        (P.2.2.1.map (winSet n)) (decCoset n P.2.2.2)) := by
  apply loopMatch_of_phaseMatch (topclPhase_chain solve hx _ _ _ _ ⟨rfl, Or.inl rfl⟩)
    (fun _ _ _ h => topclInv_finish solve h)
  simp

end Match

end Algo
