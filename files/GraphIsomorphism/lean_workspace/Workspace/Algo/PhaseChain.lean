/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Luks's Chain Rule as one phase of a round.
-/
import Workspace.Algo.Luks
import Workspace.Algo.PhaseMatch

/-!
# The Chain Rule is one phase

`Workspace/Algo/PhaseMatch.lean` gives the phase rules.  This file applies them to the
reduction every adaptive round of Secs. 12–14 is built from: Luks's Chain Rule, Eq. (63),
written as `Algo.cosetChain`.

## What is proved

* `Algo.cosetChain_eq_phaseFold` — the chain *is* a loop over its windows in the sense of
  `Algo.phaseFold`, so the iteration rule of `Workspace/Algo/PhaseMatch.lean` applies to it.
  The two sides differ in how they stop on an empty candidate set, and
  `Algo.phaseFold_empty` says the difference is invisible.
* `Algo.phaseMatch_cosetChain` — **the Chain Rule as a phase**: if at every state of the
  invariant the round's next child is the instance Eq. (63) asks for, then the chain over
  `Δs` is a phase of cost `Δs.length`.  Any round that runs a chain over a list of windows
  and then goes on with something else can use this lemma instead of an induction of its
  own.
* `Algo.loopMatch_chainRound_ofPhase` — the sanity instance: the statement of
  `Algo.loopMatch_chainRound` (`Workspace/Algo/Luks.lean`), proved again from the phase
  rules.  The round there is a single chain, so the derivation is
  `Algo.phaseMatch_cosetChain` followed by `Algo.loopMatch_of_phaseMatch`, and the only real
  work left is the one step of the loop — which is the point of the rule.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open Babai Equiv Equiv.Perm

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

/-! ## The chain is a loop over its windows -/

/-- One step of the Chain Rule as a job: with an empty candidate set there is nothing left
to do, otherwise ask for the window isomorphisms inside the next window. -/
noncomputable def chainStep (x y : Ω → A) (C : Set (Perm Ω)) (Δ : Set Ω) :
    SIReduction Ω A (Set (Perm Ω)) :=
  if C = ∅ then .done ∅ else .call ⟨C, Δ, x, y⟩ fun ans => .done ans

/-- Once the candidate set is empty the loop keeps returning the empty set. -/
theorem phaseFold_empty (x y : Ω → A) :
    ∀ Δs : List (Set Ω), phaseFold (chainStep x y) (∅ : Set (Perm Ω)) Δs = .done ∅ := by
  intro Δs
  induction Δs with
  | nil => rfl
  | cons Δ Δs ih =>
    rw [phaseFold_cons, chainStep, if_pos rfl]
    exact ih

/-- **The Chain Rule is a loop over its windows.**  The chain gives up as soon as the
candidate set is empty, the loop keeps going with the empty set; by `Algo.phaseFold_empty`
the two trees are the same. -/
theorem cosetChain_eq_phaseFold (x y : Ω → A) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)),
      cosetChain x y Δs C = phaseFold (chainStep x y) C Δs := by
  intro Δs
  induction Δs with
  | nil => intro C; rfl
  | cons Δ Δs ih =>
    intro C
    by_cases hC : C = ∅
    · rw [cosetChain, if_pos hC, phaseFold_cons, chainStep, if_pos hC]
      show (SIReduction.done ∅ : SIReduction Ω A (Set (Perm Ω))).bind _ = _
      rw [SIReduction.bind]
      exact (phaseFold_empty x y Δs).symm
    · rw [cosetChain, if_neg hC, phaseFold_cons, chainStep, if_neg hC]
      show _ = (SIReduction.call _ _).bind _
      rw [SIReduction.bind]
      exact congrArg (SIReduction.call _) (funext fun ans => ih ans)

/-! ## The Chain Rule as a phase of a round -/

variable {R : Round ι ω α} {decI : ι → SIInstance Ω A} {decA : α → Set (Perm Ω)} {I : ι}

/-- **Luks's Chain Rule, Eq. (63), is one phase of a round of cost `Δs.length`.**

`Inv Δs C j s` is the invariant before the windows `Δs`: the chain has reached the candidate
set `C` and the fold stands at `(j, s)`.  There are two hypotheses.  `hstep` says that at a
state of the invariant with a nonempty candidate set the round's next child is exactly the
instance `⟨C, Δ, x, y⟩` of Eq. (63), and that the invariant is restored for every raw answer
that decodes to that child's answer.  `hstop` says that a state with an empty candidate set
already satisfies the invariant at the end of the chain, which is how Eq. (63) gives up.

Every round that runs a chain over a list of windows and then continues can compose this
phase with the next one by `Algo.phaseMatch_bind`, instead of proving the sequencing by an
induction of its own. -/
theorem phaseMatch_cosetChain (x y : Ω → A) (Inv : List (Set Ω) → Set (Perm Ω) → ℕ → ω → Prop)
    (hstep : ∀ (Δ : Set Ω) (Δs : List (Set Ω)) (C : Set (Perm Ω)) (j : ℕ) (s : ω),
      Inv (Δ :: Δs) C j s → C ≠ ∅ → ∃ J : ι, R.child (I, j, s) = some J ∧
        decI J = ⟨C, Δ, x, y⟩ ∧
        ∀ a : α, decA a = (decI J).answer →
          Inv Δs (decI J).answer (j + 1) (R.combine (I, j, s, a)))
    (hstop : ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)) (j : ℕ) (s : ω),
      Inv Δs C j s → C = ∅ → Inv [] ∅ j s) :
    ∀ (Δs : List (Set Ω)) (C : Set (Perm Ω)) (j : ℕ) (s : ω), Inv Δs C j s →
      PhaseMatch R decI decA I Δs.length j s (cosetChain x y Δs C)
        fun C' j' s' => Inv [] C' j' s' := by
  intro Δs
  induction Δs with
  | nil =>
    intro C j s hInv
    rw [cosetChain, List.length_nil]
    exact phaseMatch_done hInv
  | cons Δ Δs ih =>
    intro C j s hInv
    by_cases hC : C = ∅
    · rw [cosetChain, if_pos hC]
      exact phaseMatch_mono (phaseMatch_done (R := R) (decI := decI) (decA := decA)
        (hstop (Δ :: Δs) C j s hInv hC)) (Nat.zero_le _)
    · obtain ⟨J, hc, hJ, hnext⟩ := hstep Δ Δs C j s hInv hC
      rw [cosetChain, if_neg hC, List.length_cons, ← hJ]
      refine phaseMatch_call hc fun a ha => ?_
      exact ih (decI J).answer (j + 1) (R.combine (I, j, s, a)) (hnext a ha)

/-! ## The sanity instance: the Chain Rule round again

`Algo.loopMatch_chainRound` (`Workspace/Algo/Luks.lean`) is proved there by one induction on
the remaining budget, which does the bookkeeping of the loop by hand.  Here is the same
statement from the phase rules: `Algo.phaseMatch_cosetChain` for the loop,
`Algo.loopMatch_of_phaseMatch` for the end of the round.  What is left to prove is one step
of the loop, and that is the part of the original proof that says something. -/

section ChainRound

variable {n : ℕ}

/-- **The fold of the Chain Rule round walks the chain**, proved from the phase rules.  This
is `Algo.loopMatch_chainRound` again, with the budget bookkeeping done by
`Algo.phaseMatch_cosetChain`. -/
theorem loopMatch_chainRound_ofPhase (n : ℕ) (solve : RawWinSI → RawCoset) {I : RawWinSI}
    (hI : WinWF n I) (h2 : 1 < (winOrbits (I.2.1, I.1)).length) (w : ℕ)
    (hw : (winOrbits (I.2.1, I.1)).length ≤ w) :
    LoopMatch (chainRound n solve) (decWinSI n) (decCoset n) I w 0
      (some (I.2.1, I.2.2.1))
      (cosetChain (decStrN n I.2.2.2.1) (decStrN n I.2.2.2.2)
        ((winOrbits (I.2.1, I.1)).map (winSet n)) (decWinSI n I).K) := by
  obtain ⟨hx, hy, hnd, hlt, hgs, hgl, hσ, hinv⟩ := hI
  -- the invariant: the windows left are the orbits from `j` on, or the chain has given up
  set Inv : List (Set (Fin n)) → Set (Perm (Fin n)) → ℕ → RawCoset → Prop :=
    fun Δs C j s => StateOK n I C s ∧
      (Δs = (((winOrbits (I.2.1, I.1)).drop j).map (winSet n)) ∨ C = ∅) with hInvDef
  -- an empty candidate set means an empty raw state
  have hnone : ∀ s : RawCoset, decCoset n s = (∅ : Set (Perm (Fin n))) → s = none := by
    intro s hs
    cases s with
    | none => rfl
    | some q =>
      obtain ⟨g, σ⟩ := q
      have hmem : decPerm n σ ∈ decCoset n (some (g, σ)) := ⟨1, one_mem _, by rw [mul_one]⟩
      rw [hs] at hmem
      exact absurd hmem (by simp)
  -- one step of the loop
  have hstep : ∀ (Δ : Set (Fin n)) (Δs : List (Set (Fin n))) (C : Set (Perm (Fin n)))
      (j : ℕ) (s : RawCoset), Inv (Δ :: Δs) C j s → C ≠ ∅ →
      ∃ J : RawWinSI, (chainRound n solve).child (I, j, s) = some J ∧
        decWinSI n J = ⟨C, Δ, decStrN n I.2.2.2.1, decStrN n I.2.2.2.2⟩ ∧
        ∀ a : RawCoset, decCoset n a = (decWinSI n J).answer →
          Inv Δs (decWinSI n J).answer (j + 1)
            ((chainRound n solve).combine (I, j, s, a)) := by
    intro Δ Δs C j s hInv hC
    obtain ⟨hs, hlist⟩ := hInv
    have hlist' : Δ :: Δs = ((winOrbits (I.2.1, I.1)).drop j).map (winSet n) :=
      hlist.resolve_right hC
    have hjl : j < (winOrbits (I.2.1, I.1)).length := by
      by_contra hj
      rw [List.drop_eq_nil_of_le (by omega), List.map_nil] at hlist'
      exact absurd hlist' (by simp)
    have hdrop : (winOrbits (I.2.1, I.1)).drop j
        = ((winOrbits (I.2.1, I.1))[j]'hjl) :: (winOrbits (I.2.1, I.1)).drop (j + 1) :=
      List.drop_eq_getElem_cons hjl
    rw [hdrop, List.map_cons] at hlist'
    have hΔ : Δ = winSet n ((winOrbits (I.2.1, I.1))[j]'hjl) := (List.cons.injEq _ _ _ _ ▸
      hlist').1
    have hΔs : Δs = (((winOrbits (I.2.1, I.1)).drop (j + 1)).map (winSet n)) :=
      (List.cons.injEq _ _ _ _ ▸ hlist').2
    -- the raw state is a nonempty coset
    obtain ⟨g, τ, rfl⟩ : ∃ g τ, s = some (g, τ) := by
      cases s with
      | none => exact absurd (show C = ∅ from hs.1.symm) hC
      | some q => exact ⟨q.1, q.2, rfl⟩
    have hsv : (some (g, τ) : RawCoset) = some (g, τ) := rfl
    -- the guards of `winChild`
    have hgetd : (winOrbits (I.2.1, I.1)).getD j [] = (winOrbits (I.2.1, I.1))[j]'hjl :=
      List.getD_eq_getElem _ _ hjl
    have hmemw : (winOrbits (I.2.1, I.1))[j]'hjl ∈ winOrbits (I.2.1, I.1) :=
      List.getElem_mem hjl
    have hne : (winOrbits (I.2.1, I.1)).getD j [] ≠ [] := by
      rw [hgetd]; exact winOrbits_ne_nil hmemw
    have hgle : decGroup n g ≤ decGroup n I.2.1 := hs.2.2 g τ hsv
    have htidy : decGroup n (tidyGens (I.2.2.2.1, g)) = decGroup n g :=
      decGroup_tidyGens hx g
    have hinvw : rawIsInvariant (tidyGens (I.2.2.2.1, g),
        (winOrbits (I.2.1, I.1)).getD j []) = true := by
      rw [rawIsInvariant_eq_true_iff (wf_tidyGens hx g)
        (by rw [hgetd]; exact winOrbits_lt hgs hlt hinv hmemw)]
      obtain ⟨p, hp, hpe⟩ := winOrbits_mem hmemw
      have hpn : p < n := hlt p hp
      have hset : {z : Fin n | (z : ℕ) ∈ (winOrbits (I.2.1, I.1)).getD j []}
          = {z : Fin n | (z : ℕ) ∈ rawOrbit (I.2.1, p)} := by
        rw [hgetd, hpe]
      rw [hset, htidy]
      exact isInvariant_of_le (isInvariant_rawOrbit hgs hpn) hgle
    refine ⟨((winOrbits (I.2.1, I.1)).getD j [], tidyGens (I.2.2.2.1, g),
      normPerm (I.2.2.2.1, τ), I.2.2.2.1, I.2.2.2.2), ?_, ?_, ?_⟩
    · exact winChild_eq_some_of (p := (I, j, (some (g, τ) : RawCoset))) hsv hne h2 hinvw
    · have hK : decCoset n (some (tidyGens (I.2.2.2.1, g), normPerm (I.2.2.2.1, τ))) = C := by
        rw [← hs.1, hsv]
        show {ρ | ∃ u ∈ decGroup n (tidyGens (I.2.2.2.1, g)),
          ρ = decPerm n (normPerm (I.2.2.2.1, τ)) * u} = _
        rw [htidy, decPerm_normPerm hx τ]
        rfl
      rw [decWinSI]
      simp only
      rw [hK, hgetd, hΔ]
    · intro a ha
      set J : RawWinSI := ((winOrbits (I.2.1, I.1)).getD j [], tidyGens (I.2.2.2.1, g),
        normPerm (I.2.2.2.1, τ), I.2.2.2.1, I.2.2.2.2) with hJdef
      have hsub : (decWinSI n J).answer ⊆ C := by
        have hK : decCoset n (some (tidyGens (I.2.2.2.1, g), normPerm (I.2.2.2.1, τ))) = C := by
          rw [← hs.1, hsv]
          show {ρ | ∃ u ∈ decGroup n (tidyGens (I.2.2.2.1, g)),
            ρ = decPerm n (normPerm (I.2.2.2.1, τ)) * u} = _
          rw [htidy, decPerm_normPerm hx τ]
          rfl
        intro ρ hρ
        have : ρ ∈ (decWinSI n J).K := hρ.1
        rw [decWinSI] at this
        exact hK ▸ this
      refine ⟨⟨ha, le_trans hsub hs.2.1, ?_⟩, Or.inl (by rw [hΔs])⟩
      intro g₂ τ₂ ha2
      refine decGroup_le_of_subset (σ₀ := decPerm n I.2.2.1) (τ := decPerm n τ₂) ?_
      have h1 : decCoset n (some (g₂, τ₂)) ⊆ (decWinSI n I).K := by
        rw [← ha2]
        show decCoset n ((chainRound n solve).combine (I, j, (some (g, τ) : RawCoset), a)) ⊆ _
        show decCoset n a ⊆ _
        rw [ha]
        exact le_trans hsub hs.2.1
      exact h1
  -- the end of the chain is the end of the round
  have hfin : ∀ (C : Set (Perm (Fin n))) (j : ℕ) (s : RawCoset), Inv [] C j s →
      (chainRound n solve).child (I, j, s) = none ∧
        decCoset n ((chainRound n solve).finish (I, s)) = C := by
    intro C j s hInv
    obtain ⟨hs, hlist⟩ := hInv
    have hchild : (chainRound n solve).child (I, j, s) = none := by
      rcases hlist with hl | hC
      · have hj : (winOrbits (I.2.1, I.1)).length ≤ j := by
          by_contra hj
          rw [List.drop_eq_getElem_cons (by omega), List.map_cons] at hl
          exact absurd hl (by simp)
        show winChild (I, j, s) = none
        cases s with
        | none => rfl
        | some q =>
          rw [winChild]
          simp only [Option.bind_some]
          rw [if_pos (List.getD_eq_default _ _ (by omega))]
      · rw [hnone s (hs.1.trans hC)]
        rfl
    refine ⟨hchild, ?_⟩
    show decCoset n (if (winOrbits (I.2.1, I.1)).length ≤ 1 then solve I else s) = C
    rw [if_neg (by omega)]
    exact hs.1
  have hphase := phaseMatch_cosetChain (R := chainRound n solve) (decI := decWinSI n)
    (decA := decCoset n) (I := I) (decStrN n I.2.2.2.1) (decStrN n I.2.2.2.2) Inv
    hstep (fun Δs C j s hInv hC => ⟨by rw [← hC]; exact hInv.1, Or.inr rfl⟩)
    ((winOrbits (I.2.1, I.1)).map (winSet n)) (decWinSI n I).K 0 (some (I.2.1, I.2.2.1))
    ⟨⟨rfl, le_refl _, fun g τ hgt => by
        have : g = I.2.1 := congrArg (fun z => (Option.getD z (I.2.1, I.2.2.1)).1) hgt.symm
        rw [this]⟩, Or.inl (by rw [List.drop_zero])⟩
  exact loopMatch_of_phaseMatch hphase (fun b j' s' hb => hfin b j' s' hb)
    (by rw [List.length_map]; exact hw)

end ChainRound

end Algo
