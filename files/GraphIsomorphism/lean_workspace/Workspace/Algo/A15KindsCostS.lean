/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the master round packaged with a sound well-formedness test.
-/
import Workspace.Algo.A15KindsCost
import Workspace.Algo.RoundQS

/-!
# The master round with a sound well-formedness test

`Algo.A15.famRunCostQ` (`Workspace/Algo/A15KindsCost.lean`) assembles a
`Algo.Round.RunCostQ` of the master round from one `Algo.A15.KindCost` per kind and four
hypotheses about the master node type.  One of the four, `hwfCheck_eq`, asks for a routine
that **decides** master well-formedness.  `Workspace/Algo/WFTestsSI.lean` shows that no such
routine is available: several kinds carry facts that are not properties of the raw node.

This file is `Algo.A15.famRunCostQ` with that one hypothesis weakened to soundness, which is
what `Algo.Round.RunCostQS` (`Workspace/Algo/RoundQS.lean`) asks for.  Nothing else changes:
`Algo.A15.famCostQ` is reused unchanged, because it never mentions a test.

No axiom, no `sorry`.
-/

namespace Algo.A15

open RAM Babai

variable {N S α : Type} {WF : N → Prop} {ground measure : N → ℕ}
variable [Enc N] [Enc S] [Enc α]

/-- **The packaging the machine needs, with a sound test.**  Word for word
`Algo.A15.famRunCostQ`, with `hwfCheck_eq : ∀ x, wfCheck x = true ↔ WF x` replaced by
`hwfCheck_sound : ∀ x, wfCheck x = true → WF x`.

This is the shape a real family of kinds can meet: the test is the root test
`Algo.wftRootCheck` read at the root slot of the master node type, and `false` at every other
slot, which is sound because a master node in another slot is not the root. -/
def famRunCostQS (bot : α) (botS : S) (ks : List (Kind N S α WF ground measure))
    (bound stateBound widthBound : ℕ → ℕ)
    (hb : PolyBound bound) (hbm : Monotone bound)
    (hsb : QuasiPolyBound stateBound) (hsbm : Monotone stateBound)
    (hwb : QuasiPolyBound widthBound)
    (hground : ∀ x : N, ground x ≤ Enc.size x)
    (hsize : ∀ x : N, WF x → Enc.size x ≤ bound (ground x))
    (hbot : ∀ m, Enc.size bot ≤ bound m) (hbotS : ∀ m, Enc.size botS ≤ stateBound m)
    (h : ∀ k ∈ ks, KindCost bound stateBound widthBound k)
    (hgroundFun : PolyFun ground) (wfCheck : N → Bool) (hwfCheck : PolyFun wfCheck)
    (hwfCheck_sound : ∀ x, wfCheck x = true → WF x)
    (measureBound : ℕ → ℕ) (hmb : PolyBound measureBound) (hmbm : Monotone measureBound)
    (hmeasure : ∀ x, WF x → measure x ≤ measureBound (ground x)) :
    Round.RunCostQS (famRound bot botS ks) where
  toCostQ := famCostQ bot botS ks bound stateBound widthBound hb hbm hsb hsbm hwb hground
    hsize hbot hbotS h
  polyFun_ground := hgroundFun
  wfCheck := wfCheck
  polyFun_wfCheck := hwfCheck
  wfCheck_sound := hwfCheck_sound
  measureBound := measureBound
  polyBound_measureBound := hmb
  mono_measureBound := hmbm
  measure_le := hmeasure

end Algo.A15
