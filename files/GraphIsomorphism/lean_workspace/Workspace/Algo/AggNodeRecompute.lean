import Workspace.Algo.PhaseUnion
import Workspace.Algo.LocalCertRound

/-! # Recompute with the chains inside the node

The state records the representative index, the window index, the current
candidate coset and the hull of the completed answers. Closing a chain opens
the next one in the same combine step. Thus `none` ends the whole phase.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

/-- The window problem and the action data for one Recompute. -/
abbrev AggrInput := RawWinSI × RawTAct × ℕ

/-- The optional window problem marks a recursive child. -/
abbrev AggrNode := AggrInput × Option RawWinSI

/-- Representative, window, current coset, accumulated hull. -/
abbrev AggrState := ℕ × ℕ × RawCoset × RawCoset

/-- The kernel orbits, in the order of the raw orbit routine. -/
def aggrWindows (P : AggrInput) : List (List ℕ) :=
  winOrbits (lcKer P.1 P.2.1, P.1.1)

/-- Start the chain of the indexed representative. -/
def aggrBegin (P : AggrInput) (t : ℕ) : RawCoset :=
  some (lcKer P.1 P.2.1, lcRep P.1 P.2.1 t)

/-- Normalize an answer before making it the next child's input. -/
def aggrLeaf (P : AggrInput) (i : ℕ) (c : RawGens × RawPerm) : RawWinSI :=
  ((aggrWindows P).getD i [], tidyGens (P.1.2.2.2.1, c.1),
    normPerm (P.1.2.2.2.1, c.2), P.1.2.2.2.1, P.1.2.2.2.2)

/-- The node issues each orbit call itself. -/
def aggrChild (z : AggrNode × ℕ × AggrState) : Option AggrNode :=
  z.1.2.elim
    (if z.2.2.1 < z.1.1.2.2 ∧ z.2.2.2.1 < (aggrWindows z.1.1).length ∧
        z.2.1 < z.1.1.2.2 * (aggrWindows z.1.1).length then
      z.2.2.2.2.1.map (fun c => (z.1.1, some (aggrLeaf z.1.1 z.2.2.2.1 c)))
    else none) (fun _ => none)

/-- At the end of a chain, add its answer and open the next representative. -/
def aggrStep (P : AggrInput) (t i : ℕ) (acc a : RawCoset) : AggrState :=
  if a.isSome = true ∧ i + 1 < (aggrWindows P).length then
    (min t P.2.2, min (i + 1) (aggrWindows P).length, a, acc)
  else
    (min (t + 1) P.2.2, 0, aggrBegin P (min (t + 1) P.2.2),
      rawCosetJoin (P.1.2.2.2.1, acc, a))

def aggrCombine (z : AggrNode × ℕ × AggrState × RawCoset) : AggrState :=
  aggrStep z.1.1 z.2.2.1.1 z.2.2.1.2.1 z.2.2.1.2.2.2 z.2.2.2

/-- With no windows the whole input coset is already the answer. -/
def aggrInit (I : AggrNode) : AggrState :=
  (0, 0, aggrBegin I.1 0,
    if (aggrWindows I.1).isEmpty then some (I.1.1.2.1, I.1.1.2.2.1) else none)

def aggrFinish (solve : RawWinSI → RawCoset) (z : AggrNode × AggrState) : RawCoset :=
  z.1.2.elim z.2.2.2.2 solve

noncomputable def aggrDecode (n : ℕ) (I : AggrNode) : SIInstance (Fin n) ℕ :=
  I.2.elim (decWinSI n I.1.1) (decWinSI n)

/-- The local round retains its parent data at the leaves. The master embedding
must provide its own window and measure conditions. -/
def aggrWF (n : ℕ) (I : AggrNode) : Prop :=
  I.1.1.2.2.2.1.length = n ∧
    ∀ W, I.2 = some W → ∃ i c, W = aggrLeaf I.1 i c

theorem aggrChild_some {z : AggrNode × ℕ × AggrState} {J : AggrNode}
    (h : aggrChild z = some J) :
    ∃ c, z.1.2 = none ∧ z.2.2.2.2.1 = some c ∧
      z.2.2.1 < z.1.1.2.2 ∧ z.2.2.2.1 < (aggrWindows z.1.1).length ∧
      z.2.1 < z.1.1.2.2 * (aggrWindows z.1.1).length ∧
      J = (z.1.1, some (aggrLeaf z.1.1 z.2.2.2.1 c)) := by
  cases ho : z.1.2 with
  | some W => simp [aggrChild, ho] at h
  | none =>
    simp only [aggrChild, ho, Option.elim_none] at h
    split at h
    next hc =>
      obtain ⟨c, hs, hJ⟩ := Option.map_eq_some_iff.mp h
      exact ⟨c, rfl, hs, hc.1, hc.2.1, hc.2.2, hJ.symm⟩
    next => simp at h

/-- Sec. 13.1, line 04e, as a stand-alone round. -/
def aggrRound (n : ℕ) (solve : RawWinSI → RawCoset) :
    Round AggrNode AggrState RawCoset where
  WF := aggrWF n
  ground := fun I => I.1.1.2.2.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (I.1.2.2 * (aggrWindows I.1).length) (fun _ => 0)
  child := aggrChild
  init := aggrInit
  combine := aggrCombine
  finish := aggrFinish solve
  bot := none
  child_eq_none := by
    rintro ⟨P, o⟩ j s hj
    cases o with
    | some W => rfl
    | none =>
      show aggrChild ((P, none), j, s) = none
      simp only [aggrChild, Option.elim_none]
      exact if_neg (fun h => Nat.not_lt_of_ge hj h.2.2)
  child_wf := by
    intro I j s J hI hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := aggrChild_some hc
    exact ⟨hI.1, fun W hW => ⟨s.2.1, c, (Option.some.inj hW).symm⟩⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨c, ho, _, _, _, _, rfl⟩ := aggrChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := aggrChild_some hc
    exact le_rfl

section Chain

variable {n : ℕ} {P : AggrInput}

theorem aggrDecode_leaf (hx : P.1.2.2.2.1.length = n) (i : ℕ)
    (c : RawGens × RawPerm) :
    aggrDecode n (P, some (aggrLeaf P i c)) =
      ⟨decCoset n (some c), winSet n ((aggrWindows P).getD i []),
        decStrN n P.1.2.2.2.1, decStrN n P.1.2.2.2.2⟩ := by
  change decWinSI n (aggrLeaf P i c) = _
  simp only [decWinSI, aggrLeaf, decCoset_some, decGroup_tidyGens hx,
    decPerm_normPerm hx]
  rw [show c = (c.1, c.2) from rfl, decCoset_some]

/-- The chain invariant allows a completed chain to have already opened
the next representative. This is needed when its answer is empty. -/
def aggrChainInv (n : ℕ) (P : AggrInput) (t : ℕ) (acc : RawCoset)
    (Δs : List (Set (Fin n))) (C : Set (Perm (Fin n))) (j : ℕ) (s : AggrState) : Prop :=
  (∃ i c, i < (aggrWindows P).length ∧
    Δs = ((aggrWindows P).drop i).map (winSet n) ∧ C = decCoset n c ∧
    c.isSome = true ∧ s = (t, i, c, acc) ∧ j ≤ t * (aggrWindows P).length + i) ∨
  ((Δs = [] ∨ C = ∅) ∧ ∃ acc',
    s = (t + 1, 0, aggrBegin P (t + 1), acc') ∧
    decCoset n acc' = cosetHull (decCoset n acc ∪ C) ∧
    j ≤ (t + 1) * (aggrWindows P).length)

theorem aggrPhase_chain (solve : RawWinSI → RawCoset)
    (hx : P.1.2.2.2.1.length = n) {t : ℕ} (ht : t < P.2.2)
    (acc : RawCoset) :
    ∀ Δs C j s, aggrChainInv n P t acc Δs C j s →
      PhaseMatch (aggrRound n solve) (aggrDecode n) (decCoset n) (P, none)
        Δs.length j s (Babai.cosetChain (decStrN n P.1.2.2.2.1)
          (decStrN n P.1.2.2.2.2) Δs C)
        (fun C' j' s' => aggrChainInv n P t acc [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (aggrChainInv n P t acc) ?_ ?_ Δs C j s h
  · intro Δ rest C j s h hC
    rcases h with ⟨i, c, hi, hlist, rfl, hc, rfl, hj⟩ | ⟨hstop, _⟩
    · obtain ⟨q, rfl⟩ := Option.isSome_iff_exists.mp hc
      have he := List.drop_eq_getElem_cons hi
      rw [he, List.map_cons] at hlist
      obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
      have hjlt : j < P.2.2 * (aggrWindows P).length := by
        have hmul := Nat.mul_le_mul_right (aggrWindows P).length ht
        rw [Nat.succ_mul] at hmul
        omega
      refine ⟨(P, some (aggrLeaf P i q)), ?_, ?_, ?_⟩
      · change aggrChild ((P, none), j, (t, i, (some q : RawCoset), acc)) = _
        simp only [aggrChild, Option.elim_none]
        rw [if_pos ⟨ht, hi, hjlt⟩]
        rfl
      · rw [aggrDecode_leaf hx, List.getD_eq_getElem _ _ hi]
      · intro a ha
        change aggrChainInv n P t acc _ _ (j + 1) (aggrStep P t i acc a)
        by_cases hnext : a.isSome = true ∧ i + 1 < (aggrWindows P).length
        · rw [aggrStep, if_pos hnext, Nat.min_eq_left (Nat.le_of_lt ht),
            Nat.min_eq_left (Nat.le_of_lt hnext.2)]
          exact Or.inl ⟨i + 1, a, hnext.2, rfl, ha.symm, hnext.1, rfl, by omega⟩
        · rw [aggrStep, if_neg hnext, Nat.min_eq_left ht]
          refine Or.inr ⟨?_, _, rfl, ?_, ?_⟩
          · cases ha' : a with
            | none => exact Or.inr (ha.symm.trans (by rw [ha']; rfl))
            | some q' =>
              have hn : (aggrWindows P).length ≤ i + 1 := by
                have hs : a.isSome = true := by rw [ha']; rfl
                exact Nat.le_of_not_lt (fun hi' => hnext ⟨hs, hi'⟩)
              exact Or.inl (by rw [List.drop_eq_nil_of_le hn, List.map_nil])
          · rw [decCoset_rawCosetJoin hx, ha]
          · rw [Nat.succ_mul]
            omega
    · rcases hstop with he | he
      · cases he
      · exact (hC he).elim
  · intro Δs C j s h hC
    rcases h with ⟨i, c, _, _, he, hc, _⟩ | ⟨_, acc', hs, ha, hj⟩
    · obtain ⟨q, rfl⟩ := Option.isSome_iff_exists.mp hc
      have hmem : decPerm n q.2 ∈ decCoset n (some q) :=
        ⟨1, one_mem _, by rw [mul_one]⟩
      rw [← he, hC] at hmem
      exact hmem.elim
    · exact Or.inr ⟨Or.inl rfl, acc', hs, by simpa [hC] using ha, hj⟩

end Chain

section Representatives

variable {n : ℕ} {P : AggrInput}

/-- The representative lists are read directly from the raw action routine. -/
noncomputable def aggrReps (n : ℕ) (P : AggrInput) : List (Perm (Fin n)) :=
  lcPerms n P.1 P.2

/-- At a representative boundary the current chain has just been opened. -/
def aggrRepInv (n : ℕ) (P : AggrInput) (L : List (Perm (Fin n)))
    (A : Set (Perm (Fin n))) (j : ℕ) (s : AggrState) : Prop :=
  ∃ t, t ≤ P.2.2 ∧ L = (aggrReps n P).drop t ∧ ∃ acc,
    s = (t, 0, aggrBegin P t, acc) ∧ decCoset n acc = cosetHull A ∧
    j ≤ t * (aggrWindows P).length

/-- Sec. 13.1, lines 04c--04g. All chains run inside the same raw node. -/
theorem aggrPhase_descent (solve : RawWinSI → RawCoset)
    (hx : P.1.2.2.2.1.length = n) (hw : 0 < (aggrWindows P).length) :
    PhaseMatch (aggrRound n solve) (aggrDecode n) (decCoset n) (P, none)
      (P.2.2 * (aggrWindows P).length) 0 (aggrInit (P, none))
      (strongDescent (decGroup n (lcKer P.1 P.2.1))
        (decStrN n P.1.2.2.2.1) (decStrN n P.1.2.2.2.2)
        (aggrReps n P) ((aggrWindows P).map (winSet n)))
      (fun B j s => s.1 = P.2.2 ∧ decCoset n s.2.2.2 = cosetHull B) := by
  have hm := aggrPhaseMatch_strongDescent (R := aggrRound n solve)
    (decI := aggrDecode n) (decA := decCoset n) (I := (P, none))
    (decGroup n (lcKer P.1 P.2.1)) (decStrN n P.1.2.2.2.1)
    (decStrN n P.1.2.2.2.2) (aggrReps n P) ((aggrWindows P).map (winSet n))
    (aggrRepInv n P) (by
      intro σ σs A j s h
      obtain ⟨t, ht, hL, acc, rfl, hacc, hj⟩ := h
      have ht' : t < P.2.2 := by
        have hl := congrArg List.length hL
        simp only [List.length_cons, List.length_drop, aggrReps, length_lcPerms] at hl
        omega
      have htl : t < (aggrReps n P).length := by simpa [aggrReps] using ht'
      rw [List.drop_eq_getElem_cons htl] at hL
      obtain ⟨hσ, hσs⟩ := List.cons.inj hL
      have hstart : σ • (decGroup n (lcKer P.1 P.2.1) : Set (Perm (Fin n))) =
          decCoset n (aggrBegin P t) := by
        have he : (aggrReps n P)[t] = decPerm n (lcRep P.1 P.2.1 t) :=
          getElem_lcPerms n P.1 P.2 htl
        rw [hσ, he, aggrBegin, decCoset_some]
      have hc := aggrPhase_chain solve hx ht' acc
        ((aggrWindows P).map (winSet n)) (decCoset n (aggrBegin P t)) j
        (t, 0, aggrBegin P t, acc)
        (Or.inl ⟨0, aggrBegin P t, hw, by rw [List.drop_zero], rfl, rfl, rfl,
          by simpa only [Nat.add_zero] using hj⟩)
      rw [List.length_map, ← hstart] at hc
      simp only [List.length_map]
      apply phaseMatch_weaken hc
      intro B j' s' hB
      rcases hB with ⟨i, c, hi, hnil, _⟩ | ⟨_, acc', hs', hacc', hj'⟩
      · have hl := congrArg List.length hnil
        simp only [List.length_nil, List.length_map, List.length_drop] at hl
        omega
      · refine ⟨t + 1, ht', hσs, acc', hs', ?_, hj'⟩
        rw [hacc', hacc, cosetHull_hull_union]) 0 (aggrInit (P, none)) (by
      refine ⟨0, Nat.zero_le _, by rw [List.drop_zero], none, ?_, ?_, by simp⟩
      · simp only [aggrInit]
        rw [if_neg (by simpa only [List.isEmpty_iff_length_eq_zero] using (Nat.ne_of_gt hw))]
      · exact cosetHull_empty.symm)
  simp only [aggrReps, length_lcPerms, List.length_map] at hm
  apply phaseMatch_weaken hm
  intro B j s h
  obtain ⟨t, ht, hL, acc, rfl, hacc, _⟩ := h
  have hl := congrArg List.length hL
  simp only [List.length_nil, List.length_drop, aggrReps, length_lcPerms] at hl
  exact ⟨by omega, hacc⟩

end Representatives

end Algo
