/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: how the rounds built one by one become cases of one master round.
-/
import Workspace.Algo.Round

/-!
# Composing rounds: a case of the master round

`Workspace/Algo/Round.lean` gives one computable round and the relation `Algo.Implements`
that ties it to a mathematical round of Sec. 15.  The rounds built so far — the Chain Rule
round (`Workspace/Algo/Luks.lean`), the imprimitive round
(`Workspace/Algo/Imprimitive.lean`), the two top rounds
(`Workspace/Algo/TopRound.lean`, `Workspace/Algo/TopWindowRound.lean`), the local
certificate round (`Workspace/Algo/LocalCertRound.lean`) — are each a `Algo.Round` of its
own, on its own raw instance type and its own state type.  The final assembly (package A15)
needs **one** round, because the evaluator of `Workspace/Algo/EvaluatorRAM.lean` runs one
round and nothing else.

This file supplies the two lemmas that turn the existing rounds into cases of that one
round.

## The picture

The master round `M` runs on a sum type of node kinds.  For each sub-round `R` there is an
injection `e : ι → ι'` of instances and an injection `u : ω → ω'` of fold states, and on the
image of `e` the master round *is* the sub-round: same width, same `init`, same `child` (up
to `e`), same `combine` (up to `u`), same `finish`.  `Algo.Implements.embed` says that the
sub-round's `Algo.Implements` then transfers to the master round.  Nothing about the two
rounds' cost data is needed, and nothing about the other cases of `M`: the transfer is
local to the image of `e`.

## The one thing that does not transfer: the abstract solver

Every sub-round takes a parameter `solve : RawWinSI → RawCoset` "the rest of Procedure
String-Isomorphism", and uses it inside `finish` at its leaves.  In the master round this
cannot stay a function: the recursive call has to be a **child**, because `finish` must be a
`RAM.QuasiPolyFun` and the running time of the recursive call is what is being proved.  So a
leaf of a sub-round becomes, in the master round, a node with exactly one child — the
instance that was handed to `solve` — whose `finish` returns that child's answer.  On the
mathematical side the leaf `.done (decA (solve J))` becomes `.call J (fun b => .done b)`.
`Algo.loopMatch_oneCall` is that step.

Consequently the existing `Algo.Implements` statements, which are about reductions such as
`Algo.chainRoundReduction n solve` with `solve` inside a `.done`, are **not** reusable as
they stand; what is reusable is their `LoopMatch` core (for the Chain Rule round, exactly
`Algo.loopMatch_chainRound`, which is already stated under the hypothesis that the node is
not a leaf), together with the two lemmas of this file.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open Babai

variable {ι ω α ι' ω' : Type*} {Ω : Type u} {A : Type v}

/-! ## Transferring a fold along an embedding -/

/-- **The fold of a sub-round is a fold of the master round.**

`e` embeds the instances of `R` into those of `M`, `u` embeds the fold states.  On the image
of the fixed instance `I` the master round does what the sub-round does.  Then every step of
matching between `R` and a reduction tree is a step of matching between `M` and the same
tree.

*Proof.*  Induction on the matching derivation.  At a stop, `hchild` turns `none` into
`none` and `hfin` identifies the two answers.  At a call, `hchild` turns the child `J` into
`e J`, which decodes to the same instance by `hdec`, and `hcomb` identifies the state after
the fold, so the induction hypothesis applies. -/
theorem loopMatch_embed {R : Round ι ω α} {M : Round ι' ω' α}
    {decI : ι → SIInstance Ω A} {decI' : ι' → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} (e : ι → ι') (u : ω → ω') (I : ι)
    (hdec : ∀ J : ι, decI' (e J) = decI J)
    (hchild : ∀ (j : ℕ) (s : ω), M.child (e I, j, u s) = (R.child (I, j, s)).map e)
    (hcomb : ∀ (j : ℕ) (s : ω) (a : α),
      M.combine (e I, j, u s, a) = u (R.combine (I, j, s, a)))
    (hfin : ∀ s : ω, M.finish (e I, u s) = R.finish (I, s)) :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatch R decI decA I w j s T → LoopMatch M decI' decA (e I) w j (u s) T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    refine LoopMatch.done w j (u s) a ?_ ?_
    · rw [hchild j s, hc]; rfl
    · rw [hfin s]; exact ha
  | call w j s J k hc hnext ih =>
    have hcM : M.child (e I, j, u s) = some (e J) := by rw [hchild j s, hc]; rfl
    have hJ : decI' (e J) = decI J := hdec J
    refine (hJ ▸ LoopMatch.call (R := M) (decI := decI') (decA := decA) (I := e I)
      w j (u s) (e J) k hcM ?_)
    intro a ha
    have ha' : decA a = (decI J).answer := by rw [← hJ]; exact ha
    have := ih a ha'
    rw [hcomb j s a]
    exact hJ ▸ this

/-- **A sub-round is a case of the master round.**  Every well-formed instance of `M` is an
embedded instance of `R`, and on those the master round is the sub-round; so the master
round implements the same mathematical round that the sub-round implements.

The hypothesis `hsurj` is what makes this a *case* lemma: the master round of Sec. 15
dispatches on the node kind, and `hsurj` is the statement that the kind under consideration
is exactly the image of `e`.  A master round assembled from several sub-rounds is handled by
applying this lemma once per kind, after a case split on the kind of the instance. -/
theorem implements_embed {κ : Type*} {R : Round ι ω α} {M : Round ι' ω' α}
    {decI : ι → κ} {decI' : ι' → κ} {inst : κ → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (e : ι → ι') (u : ω → ω')
    (hsurj : ∀ I' : ι', M.WF I' → ∃ I : ι, I' = e I ∧ R.WF I)
    (hdec : ∀ J : ι, decI' (e J) = decI J)
    (hwidth : ∀ I : ι, M.width (e I) = R.width I)
    (hinit : ∀ I : ι, M.init (e I) = u (R.init I))
    (hchild : ∀ (I : ι) (j : ℕ) (s : ω), M.child (e I, j, u s) = (R.child (I, j, s)).map e)
    (hcomb : ∀ (I : ι) (j : ℕ) (s : ω) (a : α),
      M.combine (e I, j, u s, a) = u (R.combine (I, j, s, a)))
    (hfin : ∀ (I : ι) (s : ω), M.finish (e I, u s) = R.finish (I, s))
    (himpl : Implements R decI inst decA ρ) :
    Implements M decI' inst decA ρ := by
  intro I' hI'
  obtain ⟨I, rfl, hR⟩ := hsurj I' hI'
  have hmatch := himpl I hR
  rw [hwidth I, hinit I, hdec I]
  exact loopMatch_embed (decI := fun J => inst (decI J))
    (decI' := fun J' => inst (decI' J')) e u I (fun J => congrArg inst (hdec J))
    (hchild I) (hcomb I) (hfin I) _ _ _ _ hmatch

/-! ## The abstract solver becomes a child

A leaf of a sub-round answers its instance by `solve`.  In the master round it gets one
child, the instance itself, and returns that child's answer. -/

/-- **A node with exactly one child, returning that child's answer.**  This is what a leaf of
a sub-round becomes in the master round: the instance the sub-round handed to `solve` is now
a genuine recursive call.

`hnone` says the node has no second child, and `hfin` says its answer is the answer of the
child.  Both are conditions on the master round only; no property of `solve` is used, which
is the point — `solve` has disappeared. -/
theorem loopMatch_oneCall {M : Round ι' ω' α} {decI' : ι' → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} (I : ι') (w j : ℕ) (s : ω') (J : ι')
    (hc : M.child (I, j, s) = some J)
    (hnone : ∀ a : α, decA a = (decI' J).answer →
      M.child (I, j + 1, M.combine (I, j, s, a)) = none)
    (hfin : ∀ a : α, decA a = (decI' J).answer →
      decA (M.finish (I, M.combine (I, j, s, a))) = (decI' J).answer) :
    LoopMatch M decI' decA I (w + 1) j s
      (.call (decI' J) (fun b => .done b)) := by
  refine LoopMatch.call w j s J (fun b => .done b) hc ?_
  intro a ha
  exact LoopMatch.done w (j + 1) (M.combine (I, j, s, a)) _ (hnone a ha) (hfin a ha)

end Algo
