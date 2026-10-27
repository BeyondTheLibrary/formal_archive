/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: a round whose value is not a coset.
-/
import Workspace.Algo.Round

/-!
# A round with a general value

`Algo.LoopMatch` and `Algo.Implements` (`Workspace/Algo/Round.lean`) compare the fold of a
round with a reduction tree `Babai.SIReduction Ω A (Set (Equiv.Perm Ω))`: the value of a
node is the answer of a String Isomorphism instance, read off the raw answer by one decoder
`decA : α → Set (Equiv.Perm Ω)`.

Some procedures of the paper compute something else.  The while loop of Sec. 13.1 is the
example: its value is the pair *(the grown window `W`, the group `H(W)`)*, not a coset,
while the instances it calls — the Recompute instances of line 04 — are ordinary String
Isomorphism instances.  `Babai.SIReduction` already allows that: its value type is a
parameter, and only the *calls* are tied to `Set (Equiv.Perm Ω)`.  What has to be
generalized is the matching relation, and the generalization is small: **two** decoders of
the same raw answer type,

* `decA : α → Set (Equiv.Perm Ω)`, used at a call, because the answer of a child is the
  answer of a String Isomorphism instance;
* `decV : α → β`, used at a stop, because that is the value of the node.

`Algo.LoopMatchV` and `Algo.ImplementsV` below are `Algo.LoopMatch` and `Algo.Implements`
with those two decoders, and `Algo.loopMatchV_of_loopMatch` and
`Algo.loopMatch_of_loopMatchV` say that the old relation is the case `β = Set
(Equiv.Perm Ω)`, `decV = decA`, so nothing is lost.  `Algo.Round.loopAuxV_eq` is
`Algo.Round.loopAux_eq` for the general value.

## What does **not** generalize, and the consequence for the assembly

`Algo.roundValue_eq` does **not**.  It is the recursion: the value of a child is produced by
`Algo.Round.value` at the same round, so the child's value is decoded by the same pair of
decoders as the parent's; and the recursion needs the child's value as a `Set
(Equiv.Perm Ω)`, that is, through `decA`, while the parent's is a `β` through `decV`.  With
one answer type `α` and one round, a node cannot be both.  A general value type would have
to be a *family* over the node kinds, and `Algo.Round`, `Algo.Round.value`,
`Algo.Round.nodes_eq_count` and the evaluator would all have to carry it.

So this generalization is the right tool for a round run against an **external** solver, and
the wrong tool for the evaluator.  For the assembly, the while loop of Sec. 13.1 is
therefore **not** a node of the master round: its state `(W, gens, imgs)` is folded into the
`ω` of the certificate node, exactly as `Algo.Top2State` carries the coset the Chain Rule has
reached inside the top node of `Workspace/Algo/TopWindowRound.lean`.  Every node of the
master round then has a coset for its value, and the old `Algo.Implements` suffices.  See
the note "A15 session 0" of `Workspace/Algo/DESIGN.md`.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open Babai

variable {ι ω α β : Type*} {Ω : Type u} {A : Type v}

/-- **The fold of `R` walks the reduction `T`**, where the value of `T` is a `β` read off a
raw answer by `decV`, and the answer of a call is a set of permutations read off a raw
answer by `decA`.  This is `Algo.LoopMatch` with the value of the tree freed from the answer
of an instance. -/
inductive LoopMatchV (R : Round ι ω α) (decI : ι → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (decV : α → β) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A β → Prop where
  /-- Both stop, with the same value. -/
  | done (w j : ℕ) (s : ω) (b : β) (hc : R.child (I, j, s) = none)
      (hb : decV (R.finish (I, s)) = b) : LoopMatchV R decI decA decV I w j s (.done b)
  /-- Both ask the same instance, and continue to match for every raw answer that decodes to
  its true answer. -/
  | call (w j : ℕ) (s : ω) (J : ι) (k : Set (Equiv.Perm Ω) → SIReduction Ω A β)
      (hc : R.child (I, j, s) = some J)
      (hnext : ∀ a : α, decA a = (decI J).answer →
        LoopMatchV R decI decA decV I w (j + 1) (R.combine (I, j, s, a))
          (k (decI J).answer)) :
      LoopMatchV R decI decA decV I (w + 1) j s (.call (decI J) k)

/-- **The raw round implements a mathematical round with values in `β`**, against an
external solver for the instances it calls. -/
def ImplementsV {κ : Type*} (R : Round ι ω α) (decI : ι → κ) (inst : κ → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (decV : α → β)
    (ρ : κ → SIReduction Ω A β) : Prop :=
  ∀ I : ι, R.WF I →
    LoopMatchV R (fun J => inst (decI J)) decA decV I (R.width I) 0 (R.init I) (ρ (decI I))

/-! ## The old relation is the case `β = Set (Equiv.Perm Ω)` -/

/-- Every old matching derivation is a new one. -/
theorem loopMatchV_of_loopMatch {R : Round ι ω α} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatch R decI decA I w j s T → LoopMatchV R decI decA decA I w j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact LoopMatchV.done w j s a hc ha
  | call w j s J k hc hnext ih => exact LoopMatchV.call w j s J k hc (fun a ha => ih a ha)

/-- And conversely, so the two relations agree at `β = Set (Equiv.Perm Ω)`. -/
theorem loopMatch_of_loopMatchV {R : Round ι ω α} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatchV R decI decA decA I w j s T → LoopMatch R decI decA I w j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact LoopMatch.done w j s a hc ha
  | call w j s J k hc hnext ih => exact LoopMatch.call w j s J k hc (fun a ha => ih a ha)

/-- `Algo.Implements` is `Algo.ImplementsV` with the value decoder equal to the answer
decoder. -/
theorem implementsV_iff_implements {κ : Type*} (R : Round ι ω α) (decI : ι → κ)
    (inst : κ → SIInstance Ω A) (decA : α → Set (Equiv.Perm Ω))
    (ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    ImplementsV R decI inst decA decA ρ ↔ Implements R decI inst decA ρ :=
  ⟨fun h I hI => loopMatch_of_loopMatchV _ _ _ _ (h I hI),
   fun h I hI => loopMatchV_of_loopMatch _ _ _ _ (h I hI)⟩

namespace Round

/-- **The fold computes what the tree computes**, for a general value: `Algo.Round.loopAux_eq`
with the value read off by `decV`.

*Proof.*  Word for word the proof of `Algo.Round.loopAux_eq`; the value decoder is used only
at the stop, the answer decoder only at the call. -/
theorem loopAuxV_eq (R : Round ι ω α) {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {decV : α → β} {I : ι} {rec : ι → α} {Good : ι → Prop}
    (hgood : ∀ (j : ℕ) (s : ω) (J : ι), R.child (I, j, s) = some J → Good J)
    (hrec : ∀ J, Good J → decA (rec J) = (decI J).answer) :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A β),
      LoopMatchV R decI decA decV I w j s T →
        decV (R.loopAux rec w I j s) = T.run ∧
          (R.loopCalls rec w I j s).map decI = T.calls := by
  intro w j s T h
  induction h with
  | done w j s b hc hb =>
    cases w with
    | zero => exact ⟨by simpa using hb, by simp⟩
    | succ w =>
      refine ⟨?_, ?_⟩
      · rw [R.loopAux_succ_none hc]; simpa using hb
      · rw [R.loopCalls_succ_none hc]; simp
  | call w j s J k hc hnext ih =>
    have hG : Good J := hgood j s J hc
    have hA : decA (rec J) = (decI J).answer := hrec J hG
    obtain ⟨h1, h2⟩ := ih (rec J) hA
    refine ⟨?_, ?_⟩
    · rw [R.loopAux_succ_some hc, h1, SIReduction.run_call]
    · rw [R.loopCalls_succ_some hc, List.map_cons, h2, SIReduction.calls_call]

end Round

end Algo
