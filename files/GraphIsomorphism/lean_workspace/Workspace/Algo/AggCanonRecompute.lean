import Workspace.Algo.AggCanonReps
import Workspace.Algo.AggCanonOrbits

/-! # Recompute with stored canonical lists

The input carries the kernel, representatives, and windows. Each chain is
inlined in the node. Closing one chain opens the next in the same step.
-/

namespace Algo

open Babai Equiv
open scoped Classical Pointwise

/-- The window problem and the action data for one Recompute. -/
abbrev AggnRecomputeInput := RawWinSI × RawGens × RawGens × List (List ℕ)

/-- Read the number of stored representatives. -/
def aggnrCount (P : AggnRecomputeInput) : ℕ := P.2.2.1.length

/-- The optional window problem marks a recursive child. -/
abbrev AggnRecomputeNode := AggnRecomputeInput × Option RawWinSI

/-- Representative, window, current coset, accumulated hull. -/
abbrev AggnRecomputeState := ℕ × ℕ × RawCoset × RawCoset

/-- The kernel orbits, in the order of the raw orbit routine. -/
def aggnrWindows (P : AggnRecomputeInput) : List (List ℕ) :=
  P.2.2.2

/-- Start the chain of the indexed representative. -/
def aggnrBegin (P : AggnRecomputeInput) (t : ℕ) : RawCoset :=
  some (P.2.1, P.2.2.1.getD t [])

/-- Normalize an answer before making it the next child's input. -/
def aggnrLeaf (P : AggnRecomputeInput) (i : ℕ) (c : RawGens × RawPerm) : RawWinSI :=
  ((aggnrWindows P).getD i [], tidyGens (P.1.2.2.2.1, c.1),
    normPerm (P.1.2.2.2.1, c.2), P.1.2.2.2.1, P.1.2.2.2.2)

/-- The node issues each orbit call itself. -/
def aggnrChild (z : AggnRecomputeNode × ℕ × AggnRecomputeState) : Option AggnRecomputeNode :=
  z.1.2.elim
    (if z.2.2.1 < (aggnrCount z.1.1) ∧ z.2.2.2.1 < (aggnrWindows z.1.1).length ∧
        z.2.1 < (aggnrCount z.1.1) * (aggnrWindows z.1.1).length then
      z.2.2.2.2.1.map (fun c => (z.1.1, some (aggnrLeaf z.1.1 z.2.2.2.1 c)))
    else none) (fun _ => none)

/-- At the end of a chain, add its answer and open the next representative. -/
def aggnrStep (P : AggnRecomputeInput) (t i : ℕ) (acc a : RawCoset) : AggnRecomputeState :=
  if a.isSome = true ∧ i + 1 < (aggnrWindows P).length then
    (min t (aggnrCount P), min (i + 1) (aggnrWindows P).length, a, acc)
  else
    (min (t + 1) (aggnrCount P), 0, aggnrBegin P (min (t + 1) (aggnrCount P)),
      rawCosetJoin (P.1.2.2.2.1, acc, a))

def aggnrCombine (z : AggnRecomputeNode × ℕ × AggnRecomputeState × RawCoset) : AggnRecomputeState :=
  aggnrStep z.1.1 z.2.2.1.1 z.2.2.1.2.1 z.2.2.1.2.2.2 z.2.2.2

/-- With no windows the whole input coset is already the answer. -/
def aggnrInit (I : AggnRecomputeNode) : AggnRecomputeState :=
  (0, 0, aggnrBegin I.1 0,
    if (aggnrWindows I.1).isEmpty then some (I.1.1.2.1, I.1.1.2.2.1) else none)

def aggnrFinish (solve : RawWinSI → RawCoset) (z : AggnRecomputeNode × AggnRecomputeState) : RawCoset :=
  z.1.2.elim z.2.2.2.2 solve

noncomputable def aggnrDecode (n : ℕ) (I : AggnRecomputeNode) : SIInstance (Fin n) ℕ :=
  I.2.elim (decWinSI n I.1.1) (decWinSI n)

/-- The local round retains its parent data at the leaves. The master embedding
must provide its own window and measure conditions. -/
def aggnrWF (n : ℕ) (I : AggnRecomputeNode) : Prop :=
  I.1.1.2.2.2.1.length = n ∧
    ∀ W, I.2 = some W → ∃ i c, W = aggnrLeaf I.1 i c

theorem aggnrChild_some {z : AggnRecomputeNode × ℕ × AggnRecomputeState} {J : AggnRecomputeNode}
    (h : aggnrChild z = some J) :
    ∃ c, z.1.2 = none ∧ z.2.2.2.2.1 = some c ∧
      z.2.2.1 < (aggnrCount z.1.1) ∧ z.2.2.2.1 < (aggnrWindows z.1.1).length ∧
      z.2.1 < (aggnrCount z.1.1) * (aggnrWindows z.1.1).length ∧
      J = (z.1.1, some (aggnrLeaf z.1.1 z.2.2.2.1 c)) := by
  cases ho : z.1.2 with
  | some W => simp [aggnrChild, ho] at h
  | none =>
    simp only [aggnrChild, ho, Option.elim_none] at h
    split at h
    next hc =>
      obtain ⟨c, hs, hJ⟩ := Option.map_eq_some_iff.mp h
      exact ⟨c, rfl, hs, hc.1, hc.2.1, hc.2.2, hJ.symm⟩
    next => simp at h

/-- Sec. 13.1, line 04e, as a stand-alone round. -/
def aggnrRound (n : ℕ) (solve : RawWinSI → RawCoset) :
    Round AggnRecomputeNode AggnRecomputeState RawCoset where
  WF := aggnrWF n
  ground := fun I => I.1.1.2.2.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim ((aggnrCount I.1) * (aggnrWindows I.1).length) (fun _ => 0)
  child := aggnrChild
  init := aggnrInit
  combine := aggnrCombine
  finish := aggnrFinish solve
  bot := none
  child_eq_none := by
    rintro ⟨P, o⟩ j s hj
    cases o with
    | some W => rfl
    | none =>
      show aggnrChild ((P, none), j, s) = none
      simp only [aggnrChild, Option.elim_none]
      exact if_neg (fun h => Nat.not_lt_of_ge hj h.2.2)
  child_wf := by
    intro I j s J hI hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := aggnrChild_some hc
    exact ⟨hI.1, fun W hW => ⟨s.2.1, c, (Option.some.inj hW).symm⟩⟩
  child_measure := by
    intro I j s J _ hc
    obtain ⟨c, ho, _, _, _, _, rfl⟩ := aggnrChild_some hc
    change 0 < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hc
    obtain ⟨c, _, _, _, _, _, rfl⟩ := aggnrChild_some hc
    exact le_rfl

section Chain

variable {n : ℕ} {P : AggnRecomputeInput}

theorem aggnrDecode_leaf (hx : P.1.2.2.2.1.length = n) (i : ℕ)
    (c : RawGens × RawPerm) :
    aggnrDecode n (P, some (aggnrLeaf P i c)) =
      ⟨decCoset n (some c), winSet n ((aggnrWindows P).getD i []),
        decStrN n P.1.2.2.2.1, decStrN n P.1.2.2.2.2⟩ := by
  change decWinSI n (aggnrLeaf P i c) = _
  simp only [decWinSI, aggnrLeaf, decCoset_some, decGroup_tidyGens hx,
    decPerm_normPerm hx]
  rw [show c = (c.1, c.2) from rfl, decCoset_some]

/-- The chain invariant allows a completed chain to have already opened
the next representative. This is needed when its answer is empty. -/
def aggnrChainInv (n : ℕ) (P : AggnRecomputeInput) (t : ℕ) (acc : RawCoset)
    (Δs : List (Set (Fin n))) (C : Set (Perm (Fin n))) (j : ℕ) (s : AggnRecomputeState) : Prop :=
  (∃ i c, i < (aggnrWindows P).length ∧
    Δs = ((aggnrWindows P).drop i).map (winSet n) ∧ C = decCoset n c ∧
    c.isSome = true ∧ s = (t, i, c, acc) ∧ j ≤ t * (aggnrWindows P).length + i) ∨
  ((Δs = [] ∨ C = ∅) ∧ ∃ acc',
    s = (t + 1, 0, aggnrBegin P (t + 1), acc') ∧
    decCoset n acc' = cosetHull (decCoset n acc ∪ C) ∧
    j ≤ (t + 1) * (aggnrWindows P).length)

theorem aggnrPhase_chain (solve : RawWinSI → RawCoset)
    (hx : P.1.2.2.2.1.length = n) {t : ℕ} (ht : t < (aggnrCount P))
    (acc : RawCoset) :
    ∀ Δs C j s, aggnrChainInv n P t acc Δs C j s →
      PhaseMatch (aggnrRound n solve) (aggnrDecode n) (decCoset n) (P, none)
        Δs.length j s (Babai.cosetChain (decStrN n P.1.2.2.2.1)
          (decStrN n P.1.2.2.2.2) Δs C)
        (fun C' j' s' => aggnrChainInv n P t acc [] C' j' s') := by
  intro Δs C j s h
  rw [← aggrCosetChain_eq]
  refine phaseMatch_cosetChain _ _ (aggnrChainInv n P t acc) ?_ ?_ Δs C j s h
  · intro Δ rest C j s h hC
    rcases h with ⟨i, c, hi, hlist, rfl, hc, rfl, hj⟩ | ⟨hstop, _⟩
    · obtain ⟨q, rfl⟩ := Option.isSome_iff_exists.mp hc
      have he := List.drop_eq_getElem_cons hi
      rw [he, List.map_cons] at hlist
      obtain ⟨rfl, rfl⟩ := List.cons.inj hlist
      have hjlt : j < (aggnrCount P) * (aggnrWindows P).length := by
        have hmul := Nat.mul_le_mul_right (aggnrWindows P).length ht
        rw [Nat.succ_mul] at hmul
        omega
      refine ⟨(P, some (aggnrLeaf P i q)), ?_, ?_, ?_⟩
      · change aggnrChild ((P, none), j, (t, i, (some q : RawCoset), acc)) = _
        simp only [aggnrChild, Option.elim_none]
        rw [if_pos ⟨ht, hi, hjlt⟩]
        rfl
      · rw [aggnrDecode_leaf hx, List.getD_eq_getElem _ _ hi]
      · intro a ha
        change aggnrChainInv n P t acc _ _ (j + 1) (aggnrStep P t i acc a)
        by_cases hnext : a.isSome = true ∧ i + 1 < (aggnrWindows P).length
        · rw [aggnrStep, if_pos hnext, Nat.min_eq_left (Nat.le_of_lt ht),
            Nat.min_eq_left (Nat.le_of_lt hnext.2)]
          exact Or.inl ⟨i + 1, a, hnext.2, rfl, ha.symm, hnext.1, rfl, by omega⟩
        · rw [aggnrStep, if_neg hnext, Nat.min_eq_left ht]
          refine Or.inr ⟨?_, _, rfl, ?_, ?_⟩
          · cases ha' : a with
            | none => exact Or.inr (ha.symm.trans (by rw [ha']; rfl))
            | some q' =>
              have hn : (aggnrWindows P).length ≤ i + 1 := by
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

variable {n : ℕ} {P : AggnRecomputeInput}

/-- The representative lists are read directly from the raw action routine. -/
noncomputable def aggnrReps (n : ℕ) (P : AggnRecomputeInput) : List (Perm (Fin n)) :=
  P.2.2.1.map (decPerm n)

@[simp] theorem aggnrReps_length (n : ℕ) (P : AggnRecomputeInput) :
    (aggnrReps n P).length = aggnrCount P := by simp [aggnrReps, aggnrCount]

theorem aggnrReps_get (n : ℕ) (P : AggnRecomputeInput) {i : ℕ}
    (hi : i < (aggnrReps n P).length) :
    (aggnrReps n P)[i] = decPerm n (P.2.2.1.getD i []) := by
  change (P.2.2.1.map (decPerm n))[i] = _
  rw [List.getElem_map, List.getD_eq_getElem _ _ (by simpa [aggnrReps] using hi)]

/-- At a representative boundary the current chain has just been opened. -/
def aggnrRepInv (n : ℕ) (P : AggnRecomputeInput) (L : List (Perm (Fin n)))
    (A : Set (Perm (Fin n))) (j : ℕ) (s : AggnRecomputeState) : Prop :=
  ∃ t, t ≤ (aggnrCount P) ∧ L = (aggnrReps n P).drop t ∧ ∃ acc,
    s = (t, 0, aggnrBegin P t, acc) ∧ decCoset n acc = cosetHull A ∧
    j ≤ t * (aggnrWindows P).length

/-- Sec. 13.1, lines 04c--04g. All chains run inside the same raw node. -/
theorem aggnrPhase_descent (solve : RawWinSI → RawCoset)
    (hx : P.1.2.2.2.1.length = n) (hw : 0 < (aggnrWindows P).length) :
    PhaseMatch (aggnrRound n solve) (aggnrDecode n) (decCoset n) (P, none)
      ((aggnrCount P) * (aggnrWindows P).length) 0 (aggnrInit (P, none))
      (strongDescent (decGroup n (P.2.1))
        (decStrN n P.1.2.2.2.1) (decStrN n P.1.2.2.2.2)
        (aggnrReps n P) ((aggnrWindows P).map (winSet n)))
      (fun B j s => s.1 = (aggnrCount P) ∧ decCoset n s.2.2.2 = cosetHull B ∧
        j ≤ aggnrCount P * (aggnrWindows P).length) := by
  have hm := aggrPhaseMatch_strongDescent (R := aggnrRound n solve)
    (decI := aggnrDecode n) (decA := decCoset n) (I := (P, none))
    (decGroup n (P.2.1)) (decStrN n P.1.2.2.2.1)
    (decStrN n P.1.2.2.2.2) (aggnrReps n P) ((aggnrWindows P).map (winSet n))
    (aggnrRepInv n P) (by
      intro σ σs A j s h
      obtain ⟨t, ht, hL, acc, rfl, hacc, hj⟩ := h
      have ht' : t < (aggnrCount P) := by
        have hl := congrArg List.length hL
        simp only [List.length_cons, List.length_drop, aggnrReps_length] at hl
        omega
      have htl : t < (aggnrReps n P).length := by simpa [aggnrReps, aggnrCount] using ht'
      rw [List.drop_eq_getElem_cons htl] at hL
      obtain ⟨hσ, hσs⟩ := List.cons.inj hL
      have hstart : σ • (decGroup n (P.2.1) : Set (Perm (Fin n))) =
          decCoset n (aggnrBegin P t) := by
        have he : (aggnrReps n P)[t] = decPerm n (P.2.2.1.getD t []) :=
          aggnrReps_get n P htl
        rw [hσ, he, aggnrBegin, decCoset_some]
      have hc := aggnrPhase_chain solve hx ht' acc
        ((aggnrWindows P).map (winSet n)) (decCoset n (aggnrBegin P t)) j
        (t, 0, aggnrBegin P t, acc)
        (Or.inl ⟨0, aggnrBegin P t, hw, by rw [List.drop_zero], rfl, rfl, rfl,
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
        rw [hacc', hacc, cosetHull_hull_union]) 0 (aggnrInit (P, none)) (by
      refine ⟨0, Nat.zero_le _, by rw [List.drop_zero], none, ?_, ?_, by simp⟩
      · simp only [aggnrInit]
        rw [if_neg (by simpa only [List.isEmpty_iff_length_eq_zero] using (Nat.ne_of_gt hw))]
      · exact cosetHull_empty.symm)
  simp only [aggnrReps_length, List.length_map] at hm
  apply phaseMatch_weaken hm
  intro B j s h
  obtain ⟨t, ht, hL, acc, rfl, hacc, hj⟩ := h
  have hl := congrArg List.length hL
  simp only [List.length_nil, List.length_drop, aggnrReps_length] at hl
  have he : t = aggnrCount P := by omega
  exact ⟨he, hacc, by simpa only [he] using hj⟩

end Representatives

/-- Prepare one stage, keeping the computed lists in the state of its caller. -/
def aggnrInputOf (c : ℕ) (p : RawLCLoop) : AggnRecomputeInput :=
  ((lcInst p).1, lcKer (lcInst p).1 (p.1.2, p.2.2.2),
    aggkRawReps c p, aggrWindows (aggrInputOf p))

section Stage

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)}
  {xs : RawStr} {tdom : List ℕ} {hc : LCCtxWF n m xs tdom}
  {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}

/-- All encodings of a stage give the same Recompute tree. -/
theorem aggnrTree_eq (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    let P := aggnrInputOf c ((xs, tdom), st)
    strongDescent (decGroup n P.2.1) (decStrN n xs) (decStrN n xs)
      (aggnrReps n P) ((aggnrWindows P).map (winSet n)) =
      recomputeStrong s (aggkCanonReps s (aggkTypedT hc)) (aggkCanonWindows s) := by
  dsimp only
  change strongDescent (decGroup n (lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2)))
    (decStrN n xs) (decStrN n xs)
    ((aggkRawReps c ((xs, tdom), st)).map (decPerm n))
    ((aggrWindows (aggrInputOf ((xs, tdom), st))).map (winSet n)) = _
  have hk : decGroup n (lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2)) = kerN s :=
    aggrKernel_eq h
  rw [hk, aggkStage_windows_eq h]
  exact aggkRecomputeStrong_congr s _ _ _ (aggkRawReps_cosets c h hg)

/-- Sec. 13.1, line 04e, matched against the fixed canonical tree. -/
theorem aggnrPhase_recompute (c : ℕ) (solve : RawWinSI → RawCoset)
    (h : StateFor hc s st) (hg : tdom.length ≤ guardBound c xs.length)
    (hrun : s.LoopCond) :
    let P := aggnrInputOf c ((xs, tdom), st)
    PhaseMatch (aggnrRound n solve) (aggnrDecode n) (decCoset n) (P, none)
      (aggnrCount P * (aggnrWindows P).length) 0 (aggnrInit (P, none))
      (recomputeStrong s (aggkCanonReps s (aggkTypedT hc)) (aggkCanonWindows s))
      (fun B j v => v.1 = aggnrCount P ∧ B = (s.step.H : Set (Perm (Fin n))) ∧
        decCoset n v.2.2.2 = B ∧ j ≤ aggnrCount P * (aggnrWindows P).length) := by
  dsimp only
  let P := aggnrInputOf c ((xs, tdom), st)
  have hm := aggrPhaseMatch_value (aggnrPhase_descent (P := P) solve hc.lenStr
    (aggrWindows_pos h hrun))
  have he : strongDescent (decGroup n P.2.1)
      (decStrN n P.1.2.2.2.1) (decStrN n P.1.2.2.2.2)
      (aggnrReps n P) ((aggnrWindows P).map (winSet n)) =
      recomputeStrong s (aggkCanonReps s (aggkTypedT hc)) (aggkCanonWindows s) :=
    aggnrTree_eq c h hg
  rw [he] at hm
  have hv := run_recomputeStrong s _ _ (aggkStage_cover s (aggkTypedT hc))
  apply phaseMatch_weaken hm
  intro B j v hv'
  have hB : B = (s.step.H : Set (Perm (Fin n))) := hv'.2.trans hv
  refine ⟨hv'.1.1, hB, ?_, hv'.1.2.2⟩
  rw [hv'.1.2.1, hB]
  simpa only [one_smul] using cosetHull_smul_subgroup (1 : Perm (Fin n)) s.step.H

theorem aggnrCount_eq (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    aggnrCount (aggnrInputOf c ((xs, tdom), st)) = lcIdx ((xs, tdom), st) := by
  have he := (aggkRawReps_perm c h hg).length_eq
  simpa only [List.length_map, aggrReps, length_lcPerms] using he

theorem aggnrWidth_le (c : ℕ) (h : StateFor hc s st)
    (hg : tdom.length ≤ guardBound c xs.length) :
    let P := aggnrInputOf c ((xs, tdom), st)
    aggnrCount P * (aggnrWindows P).length ≤ Nat.factorial tdom.length * n := by
  dsimp only
  rw [aggnrCount_eq c h hg]
  apply Nat.mul_le_mul (lcWidth_le_factorial (lcwf_lcInst h) rfl (h.himgs h.le))
  have he := (aggrStage_bound h).length
  simpa only [List.length_map, Nat.card_fin] using he

end Stage

end Algo
