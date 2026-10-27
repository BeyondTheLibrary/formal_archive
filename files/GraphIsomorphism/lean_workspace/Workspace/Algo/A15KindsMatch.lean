/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the master round of a family of kinds implements the round of Sec. 15.
-/
import Workspace.Algo.A15KindsCost
import Workspace.Algo.EvaluatorQ

/-!
# The master round simulates the round of Sec. 15, kind by kind

`Algo.Implements` is a statement about every well-formed node of the master round.  A package
knows only its own kind.  This file cuts the statement along the family, so that a package
proves `Algo.LoopMatch` for its own nodes and nothing else.

## What a package proves

`Algo.A15.loopMatch_famRound` is the bridge.  A package has a round `R` of its own — the
Chain Rule round of `Workspace/Algo/Luks.lean`, say — and a `Algo.LoopMatch` derivation for
it.  If its kind `k` sits in the master list with only kinds that do not claim its nodes in
front of it (`Algo.A15.Misses`), and if `k` is `R` with children pushed into the master node
type, then the derivation is a derivation for the master round.  The proof is
`Algo.loopMatch_embed` (`Workspace/Algo/A15Compose.lean`) with the five equations of
`Workspace/Algo/A15Kinds.lean`; the package supplies none of them.

`Algo.A15.implements_famRound_of_cover` then puts the kinds together: a list of node
predicates that covers the well-formed nodes, and one `Algo.LoopMatch` per predicate.

## The shape of the mathematical side

The family of mathematical rounds is an arbitrary `ρ : κ → Babai.SIReduction Ω A (Set (Perm
Ω))` over an arbitrary index type `κ`, exactly as `Algo.Implements` takes it.  That is what
item 5 of the note "A15 session 0" needs: the master round of Sec. 15 cannot be
`Babai.sec15MasterStep Ω A ch` for one fixed `ch`, because the machine's choices are a
function of the **raw node**, not of the typed instance.  The reindexing
`A15.masterStepOfFamily` the Master track owes has
`step r = (sec15MasterStep Ω A (chOf r)).step (p r)`, which is a `ρ` of this shape with
`κ = κ'`.  Nothing here has to change when it arrives.

## Main results

* `Algo.A15.loopMatch_famRound` — a package's `Algo.LoopMatch` is the master round's;
* `Algo.A15.implements_famRound_of_cover` — `Algo.Implements` from one derivation per kind;
* `Algo.A15.runQ_eq_answer_famRound` — and then the machine answers the instance.

No axiom, no `sorry`.
-/

universe u v

namespace Algo.A15

open RAM Babai

variable {N S α : Type} {WF : N → Prop} {ground measure : N → ℕ}
variable {Ω : Type u} {A : Type v}

/-! ## One kind's derivation is the master round's -/

/-- **A package's `Algo.LoopMatch` is the master round's.**

`R` is the package's own round, on its own instances `k.ι` and states `k.ω`.  The kind `k` is
`R` with the children pushed into the master node type along `k.e` (`hchild`); the other four
routines agree (`hwidth`, `hinit`, `hcomb`, `hfin`).  `hmiss` says the kinds in front of `k`
in the master list do not claim `k`'s nodes, so `k` is the one the dispatch selects.

*Proof.*  `Algo.loopMatch_embed` with `e := k.e` and `u := k.u`; its three hypotheses are
`Algo.A15.famChild_eq`, `famCombine_eq` and `famFinish_eq` rewritten by the five equations
above. -/
theorem loopMatch_famRound (bot : α) (botS : S)
    (pre : List (Kind N S α WF ground measure)) (k : Kind N S α WF ground measure)
    (post : List (Kind N S α WF ground measure))
    {R : Round k.ι k.ω α} (i : k.ι)
    (hchild : ∀ (j : ℕ) (w : k.ω), k.child (i, j, w) = (R.child (i, j, w)).map k.e)
    (hcomb : ∀ (j : ℕ) (w : k.ω) (a : α),
      k.combine (i, j, w, a) = R.combine (i, j, w, a))
    (hfin : ∀ w : k.ω, k.finish (i, w) = R.finish (i, w))
    {decI : k.ι → SIInstance Ω A} {decI' : N → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)}
    (hdec : ∀ i : k.ι, decI' (k.e i) = decI i)
    (hmiss : Misses pre (k.e i))
    (w j : ℕ) (s : k.ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω)))
    (hm : LoopMatch R decI decA i w j s T) :
    LoopMatch (famRound bot botS (pre ++ k :: post)) decI' decA (k.e i) w j (k.u s) T := by
  refine loopMatch_embed (R := R) (M := famRound bot botS (pre ++ k :: post))
    (decI := decI) (decI' := decI') (decA := decA) k.e k.u i hdec ?_ ?_ ?_ w j s T hm
  · intro j' s'
    show famChild (pre ++ k :: post) (k.e i, j', k.u s') = _
    rw [famChild_eq pre k post i j' s' hmiss, hchild j' s']
  · intro j' s' a
    show famCombine (pre ++ k :: post) (k.e i, j', k.u s', a) = _
    rw [famCombine_eq pre k post i j' s' a hmiss, hcomb j' s' a]
  · intro s'
    show famFinish bot (pre ++ k :: post) (k.e i, k.u s') = _
    rw [famFinish_eq bot pre k post i s' hmiss, hfin s']

/-- The master round's fold at a node of the kind `k` starts where the package's fold starts.
This is what turns `Algo.A15.loopMatch_famRound` into one case of `Algo.Implements`. -/
theorem famRound_start (bot : α) (botS : S)
    (pre : List (Kind N S α WF ground measure)) (k : Kind N S α WF ground measure)
    (post : List (Kind N S α WF ground measure)) (i : k.ι) (hmiss : Misses pre (k.e i)) :
    (famRound bot botS (pre ++ k :: post)).width (k.e i) = k.width i ∧
      (famRound bot botS (pre ++ k :: post)).init (k.e i) = k.u (k.init i) :=
  ⟨famWidth_eq pre k post i hmiss, famInit_eq botS pre k post i hmiss⟩

/-- **A matching derivation may be given a larger budget.**  The budget `w` of
`Algo.LoopMatch` bounds the number of children still to come; a package proves its derivation
at its own round's width, and the master round's width may be larger.

*Proof.*  Induction on the derivation: a stop holds at every budget, and a call takes one off
both. -/
theorem loopMatch_mono {ι ω : Type} {R : Round ι ω α} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatch R decI decA I w j s T → ∀ w', w ≤ w' → LoopMatch R decI decA I w' j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => intro w' _; exact LoopMatch.done w' j s a hc ha
  | call w j s J kk hc hnext ih =>
      intro w' hw
      obtain ⟨w'', rfl⟩ : ∃ w'', w' = w'' + 1 := ⟨w' - 1, by omega⟩
      exact LoopMatch.call w'' j s J kk hc (fun a ha => ih a ha w'' (by omega))

/-! ## Putting the kinds together

`Algo.Implements` unfolds to one `Algo.LoopMatch` per well-formed node, so a list of node
predicates that covers the well-formed nodes cuts it into one statement per kind. -/

/-- **`Algo.Implements` from one derivation per kind.**

`covers` is one predicate per kind — in practice "the node is of kind `k`", that is
`fun x => (k.proj x).isSome`.  `hcover` says every well-formed node belongs to at least one
kind, and `hkind` is the package's obligation for that kind.  Nothing else is asked, and in
particular the kinds need not be disjoint: the master round dispatches by first match, and
`hkind` is a statement about the master round, so two kinds claiming one node is harmless. -/
theorem implements_famRound_of_cover {κ : Type*} (bot : α) (botS : S)
    (ks : List (Kind N S α WF ground measure)) (decI : N → κ) (inst : κ → SIInstance Ω A)
    (decA : α → Set (Equiv.Perm Ω)) (ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω)))
    (covers : List (N → Prop)) (hcover : ∀ x : N, WF x → ∃ P ∈ covers, P x)
    (hkind : ∀ P ∈ covers, ∀ x : N, WF x → P x →
      LoopMatch (famRound bot botS ks) (fun y => inst (decI y)) decA x
        (famWidth ks x) 0 (famInit botS ks x) (ρ (decI x))) :
    Implements (famRound bot botS ks) decI inst decA ρ := by
  intro x hx
  obtain ⟨P, hP, hPx⟩ := hcover x hx
  exact hkind P hP x hx hPx

/-! ## The machine answers the instance

`Algo.Round.runQ_eq_answer` (`Workspace/Algo/EvaluatorQ.lean`) restated for the master round
of a family.  The mathematical side is an arbitrary `Babai.MasterStep Ω A κ`, so
`A15.masterStepOfFamily` fits it unchanged. -/

variable [Enc N] [Enc S] [Enc α]

/-- **The master round of a family answers the instance.** -/
theorem runQ_eq_answer_famRound {κ : Type*} (bot : α) (botS : S)
    (ks : List (Kind N S α WF ground measure))
    (C : Round.RunCostQ (famRound bot botS ks)) {decI : N → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements (famRound bot botS ks) decI M.inst decA M.step)
    (hgrp : ∀ x : N, WF x → IsGroupInstance (M.inst (decI x)))
    (hrank : ∀ x : N, WF x → M.rank (decI x) ≤ measure x)
    (hlift : ∀ (f : ℕ) (x y : N), WF x → y ∈ (famRound bot botS ks).roundCalls f x →
      decI y = M.lift (decI x) (M.inst (decI y)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ x : N, WF x → (M.inst (decI x)).windowSize ≤ ground x)
    (f : ℕ) (x : N) (hx : WF x) (hf : measure x < f) :
    ∃ a : α, (famRound bot botS ks).runQ C c₁ x = some a ∧
      decA a = (M.inst (decI x)).answer :=
  Round.runQ_eq_answer (famRound bot botS ks) C M himpl hgrp hrank hlift hmono c₁ hq hwin
    f x hx hf

end Algo.A15
