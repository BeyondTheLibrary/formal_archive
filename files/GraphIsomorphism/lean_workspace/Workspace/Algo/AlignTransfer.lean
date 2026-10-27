/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: a coset-form round implements the aligned group-form round.
-/
import Workspace.Algo.EvaluatorN
import Workspace.LocalCertificates.AggregateGroup

/-!
# From the coset form to the group form, once, at the top

Sec. 11.1, Remark 11.1.4 prints Luks's Eqs. (62)–(63) in two forms.  A subproblem with
respect to a coset `σH` may be written

* in **coset form**, `⟨σH, Δ, x, y⟩`, or
* in **group form**, `⟨H, Δ, x, y^{σ⁻¹}⟩`, which is the first form after the *alignment step*
  `y ← y^{σ⁻¹}`.

Eq. (59) says the two have the same answer up to the shift by `σ`: `σ · Iso(group form) =
Iso(coset form)`, which is `Babai.smul_answer_alignInst`.

The machine layer builds the coset form and the mathematical layer the group form, for
reasons that are not negotiable on either side.

* A raw round has to walk **one fixed typed tree** for every raw answer that decodes to the
  true answer (`Algo.LoopMatch.call`).  A raw answer is a coset, presented by whatever
  generators and whatever representative the previous round happened to print.  So a child
  may be a function of the decoded coset, but not of the representative.  The coset form is
  a function of the coset; the group form is not.
* `Babai.IsGroupInstance` — which the whole cost analysis of `Workspace/Master/Cost.lean`
  rests on — holds for the group form and fails for the coset form.

This file reconciles them.  The machine never aligns.  Instead the *typed* round is aligned
once, by `Babai.SIReduction.alignCalls`, using the representative `Babai.cosetRepOf K`, which
is a function of the set `K` alone.  What comes out is:

* every call of the aligned round is the alignment of a call of the coset round
  (`Babai.calls_alignCalls`), so the number of calls and the window sizes are unchanged;
* the answer of an aligned node, read back through the shift by its own representative, is
  the answer of the coset node.  So the answer decoder of the machine has to be shifted, and
  the shift depends on the node: that is exactly `Algo.ImplementsN`
  (`Workspace/Algo/RoundN.lean`).

## Main definitions

* `Algo.alignRed` — the aligned form of one typed round: align every call, then shift the
  value back by the representative of the node;
* `Algo.alignDec` — the answer decoder of the aligned round.

## Main results

* `Algo.loopMatchN_alignCalls` — **the transfer lemma**: a fold that walks a coset-form tree
  walks the aligned tree, with the shifted decoder;
* `Algo.implementsN_align` — hence `Algo.Implements` of the coset form gives
  `Algo.ImplementsN` of the aligned form;
* `Algo.Round.runQ_eq_answer_align` — and at the root the shift cancels, so the routine
  returns a raw answer that the **unshifted** decoder sends to `Iso^Δ_K(x,y)`.  This is the
  old conclusion of `Algo.Round.runQ_eq_answer`, word for word.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open Babai RAM
open scoped Pointwise

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

/-! ## The aligned form of a typed round -/

/-- **The aligned round** of Remark 11.1.4: put the alignment step in front of every call
(`Babai.SIReduction.alignCalls`), then shift the value back by the representative of the node
`I₀` the round belongs to.

`Algo.alignRed I₀ T` is a round *of the aligned instance* `Babai.alignInst I₀`: it runs to
`(alignInst I₀).answer` when `T` runs to `I₀.answer` (`Algo.run_alignRed`). -/
noncomputable def alignRed (I₀ : SIInstance Ω A) (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  T.alignCalls.bind fun v => .done ((cosetRepOf I₀.K)⁻¹ • v)

/-- The aligned round of a leaf is a leaf, with the value shifted back. -/
@[simp] theorem alignRed_done (I₀ : SIInstance Ω A) (a : Set (Equiv.Perm Ω)) :
    alignRed I₀ (SIReduction.done (Ω := Ω) (A := A) a)
      = .done ((cosetRepOf I₀.K)⁻¹ • a) := rfl

/-- **One step of the aligned round**: it asks the *aligned* instance, and hands the
continuation of the coset round the answer shifted forward by the representative of the
instance asked.  That shift is Eq. (59) applied to the call. -/
theorem alignRed_call (I₀ J : SIInstance Ω A)
    (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω))) :
    alignRed I₀ (.call J k)
      = .call (alignInst J) fun a => alignRed I₀ (k ((cosetRepOf J.K) • a)) := rfl

/-- Alignment does not change the value, except for the shift at the root (Eq. (59)). -/
@[simp] theorem run_alignRed (I₀ : SIInstance Ω A)
    (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (alignRed I₀ T).run = (cosetRepOf I₀.K)⁻¹ • T.run := by
  rw [alignRed, SIReduction.run_bind, run_alignCalls, SIReduction.run_done]

/-- The calls of the aligned round are the calls of the coset round, aligned.  So their
number and their window sizes are unchanged (`Babai.windowSize_alignInst`). -/
theorem calls_alignRed (I₀ : SIInstance Ω A) (T : SIReduction Ω A (Set (Equiv.Perm Ω))) :
    (alignRed I₀ T).calls = T.calls.map alignInst := by
  rw [alignRed, SIReduction.calls_bind, calls_alignCalls, SIReduction.calls_done,
    List.append_nil]

/-- **The aligned round is correct** when the coset round is: if `T` computes the answer of
the coset instance `I₀`, then `Algo.alignRed I₀ T` computes the answer of `Babai.alignInst
I₀`. -/
theorem run_alignRed_eq_answer {I₀ : SIInstance Ω A}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : T.run = I₀.answer) :
    (alignRed I₀ T).run = (alignInst I₀).answer := by
  rw [run_alignRed, h, ← smul_answer_alignInst I₀, inv_smul_smul]

/-! ## The shifted answer decoder -/

/-- **The answer decoder of the aligned round**: read the raw answer of the node `J` as
before, then shift it back by the representative of `J`.  The shift depends on the node,
which is why `Algo.ImplementsN` and not `Algo.Implements`. -/
noncomputable def alignDec (decJ : ι → SIInstance Ω A) (decA : α → Set (Equiv.Perm Ω))
    (J : ι) (a : α) : Set (Equiv.Perm Ω) :=
  (cosetRepOf (decJ J).K)⁻¹ • decA a

/-- **Reading the shift back.**  A raw answer that the shifted decoder sends to the answer of
the aligned instance is one the plain decoder sends to the answer of the coset instance.
This is Eq. (59) once more, and it is what makes the root of the recursion come out in the
old form. -/
theorem eq_answer_of_alignDec {I₀ : SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)} {a : α}
    (h : (cosetRepOf I₀.K)⁻¹ • decA a = (alignInst I₀).answer) : decA a = I₀.answer := by
  rw [← smul_answer_alignInst I₀, ← h, smul_inv_smul]

/-! ## The transfer -/

/-- **The transfer lemma.**  A fold of the raw round `R` that walks the coset-form tree `T`,
reading answers with `decA`, walks the aligned tree `Algo.alignRed (decJ I) T`, reading
answers with `Algo.alignDec decJ decA`.

*Proof.*  Induction on the matching derivation.  At a stop, both sides return the value of
the node, and the aligned tree returns it shifted by the representative of the node, which is
what the shifted decoder produces.  At a call, the aligned tree asks `Babai.alignInst (decJ
J)` (`Algo.alignRed_call`), which is what `Algo.ImplementsN` demands of a child `J` whose
typed instance is the aligned one.  A raw answer `a` with `alignDec decJ decA J a = (alignInst
(decJ J)).answer` has `decA a = (decJ J).answer` by `Algo.eq_answer_of_alignDec`, so the
induction hypothesis applies; and the continuation of the aligned tree at `(alignInst (decJ
J)).answer` is the continuation of `T` at `cosetRepOf (decJ J).K • (alignInst (decJ J)).answer
= (decJ J).answer`, by Eq. (59). -/
theorem loopMatchN_alignCalls {R : Round ι ω α} {decJ : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} {w j : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : LoopMatch R decJ decA I w j s T) :
    LoopMatchN R (fun J => alignInst (decJ J)) (alignDec decJ decA) I w j s
      (alignRed (decJ I) T) := by
  induction h with
  | done w j s a hc ha =>
    refine LoopMatchN.done w j s _ hc ?_
    rw [alignDec, ha]
  | call w j s J k hc hnext ih =>
    rw [alignRed_call]
    refine LoopMatchN.call w j s J _ hc ?_
    intro a ha
    have ha' : decA a = (decJ J).answer := eq_answer_of_alignDec (I₀ := decJ J) ha
    have hk : alignRed (decJ I) (k (cosetRepOf (decJ J).K • (alignInst (decJ J)).answer))
        = alignRed (decJ I) (k (decJ J).answer) := by
      rw [smul_answer_alignInst]
    rw [hk]
    exact ih a ha'

/-- **A coset-form round implements the aligned group-form round.**  This is the transfer
lemma at the root of every well-formed instance.

The typed instance type `κ` and the raw decoding `decI` do not change: only the typed
instance attached to a node is aligned, and the round it runs is aligned with it. -/
theorem implementsN_align {κ : Type*} {R : Round ι ω α} {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))} (h : Implements R decI inst decA ρ) :
    ImplementsN R decI (fun c => alignInst (inst c))
      (alignDec (fun J => inst (decI J)) decA) (fun c => alignRed (inst c) (ρ c)) :=
  fun I hI => loopMatchN_alignCalls (h I hI)

/-! ## The routine, at the root

The aligned round is what the mathematical layer runs, so the evaluator chain of
`Workspace/Algo/EvaluatorN.lean` is applied to it.  At the root the shift cancels
(`Algo.eq_answer_of_alignDec`), so the conclusion is the old one: the raw answer of the
routine decodes, with the plain decoder, to `Iso^Δ_K(x,y)` of the **coset** instance the
machine holds.  No hypothesis `cosetRepOf (decI I).K = 1` is needed. -/

namespace Round

variable [Enc ι] [Enc ω] [Enc α]

/-- **The routine answers the instance, in the coset form the machine holds.**

`R` is a coset-form round: it implements `ρ` with the plain decoder `decA` over the coset
instances `instC`.  `M` is the round of Sec. 15, whose instances are the aligned ones and
whose step is the aligned round.  Then the packaged routine `Algo.Round.runQ` returns a raw
answer that `decA` sends to the answer of the coset instance.

This is `Algo.Round.runQ_eq_answer` with the alignment of Remark 11.1.4 inserted in the
middle, and it is the form `Algo.siWorkspaceRoutine_of_normQ_run` consumes. -/
theorem runQ_eq_answer_align {κ : Type*} (R : Round ι ω α) (C : RunCostQ R) {decI : ι → κ}
    {instC : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))} (M : MasterStep Ω A κ)
    (hMinst : ∀ I : ι, M.inst (decI I) = alignInst (instC (decI I)))
    (hMstep : ∀ I : ι, M.step (decI I) = alignRed (instC (decI I)) (ρ (decI I)))
    (himpl : Implements R decI instC decA ρ)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    ∃ a : α, R.runQ C c₁ I = some a ∧ decA a = (instC (decI I)).answer := by
  have himplN : ImplementsN R decI M.inst (alignDec (fun J => instC (decI J)) decA) M.step := by
    intro I' hI'
    rw [show (fun J => M.inst (decI J)) = fun J => alignInst (instC (decI J)) from
        funext hMinst, hMstep I']
    exact implementsN_align himpl I' hI'
  obtain ⟨a, ha, hdec⟩ :=
    runQ_eq_answerN R C M himplN hgrp hrank hlift hmono c₁ hq hwin f I hI hf
  rw [hMinst I] at hdec
  exact ⟨a, ha, eq_answer_of_alignDec (I₀ := instC (decI I)) hdec⟩

end Round

end Algo

#print axioms Algo.loopMatchN_alignCalls
#print axioms Algo.Round.runQ_eq_answer_align
