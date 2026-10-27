/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: what the round of the Master Algorithm is at each branch of its decision tree.
-/
import Workspace.Master.Sec15Value

/-!
# The round of Sec. 15, branch by branch

`Babai.sec15MasterStep Ω A ch` is the decision tree of lines 1–7a
(`Babai.Sec15Inputs.step`) with every line filled in.  A machine layer has to show that one
of its rounds *is* the reduction the Master Algorithm runs at the branch the machine took.
For that it must read the value of `Babai.MasterStep.step` at each branch, and nothing else:
it should never have to unfold `Babai.sec15Lift` or `Babai.sec15Remaining`.

This file is that reading.  For each of the seven branches there is one lemma
`Babai.sec15Step_eq_…`, stated under exactly the tests that lead to the branch, in the order
the pseudo-code evaluates them:

| branch | test | value of `step` |
|---|---|---|
| line 1 | `¬ IsJohnson i` | `Babai.line1Round ch.line1 i` |
| line 2 | `IsJohnson i`, `param i ≤ ellOf n` | `Babai.line2Fun ch.line2 i` |
| line 4a | `IsJohnson i`, `¬ param i ≤ ellOf n`, `IsPrimitiveCase i`, `TIsOne i` | `Babai.line4aReduction i.inst` |
| line 4b | the same with `¬ TIsOne i`, `SmallDefect i` | `Babai.line4bFun ch.line4b i` |
| lines 4c–4d | the same with `¬ SmallDefect i` | `Babai.line4cdFun ch.line4cd i` |
| lines 5, 6, 6a, 7a | `¬ IsPrimitiveCase i`, `aggregatesToStructure i` | `Babai.line56a7aFun ch.line56a7a i` |
| lines 5, 7, 7a | `¬ IsPrimitiveCase i`, `¬ aggregatesToStructure i` | `Babai.line567aFun ch.line567a i` |

Here `n = i.inst.windowSize` and `ellOf n = (log₂ n)³` is line 2's threshold `ℓ`.

The seven tests are the five tests of the pseudo-code.  They are not exclusive by
construction — `Babai.IsPrimitiveCase` and `Babai.aggregatesToStructure` are properties of
the instance, not flags — so the order matters, and each lemma carries the negations of the
tests that come before it.  That is the same order as in `Babai.Sec15Inputs.step_cases` and
in `Babai.sec15Lift`.

The companion `Babai.sec15Lift_…` lemmas of `Workspace/Master/Sec15Value.lean` read the
**hint** the same branch hands down.  The two together are all a machine layer needs about
the shape of one round.
-/

universe u v

namespace Babai

open scoped Classical

section Shape

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  (ch : Sec15Choices Ω A q923 c923) (i : HintedInstance Ω A)

/-- §15: the round is the decision tree of the seven lines, read on the hinted instance. -/
theorem sec15MasterStep_step :
    (sec15MasterStep Ω A ch).step = (sec15Remaining ch).toSec15Inputs.step := rfl

/-! The fields of `Babai.Sec15Remaining.toSec15Inputs` at the round of Sec. 15.  Each of
them holds by `rfl`; they are stated so that the decision tree can be unfolded without
unfolding the two structures. -/

theorem toSec15Inputs_inst :
    (sec15Remaining ch).toSec15Inputs.inst = HintedInstance.inst := rfl

theorem toSec15Inputs_param :
    (sec15Remaining ch).toSec15Inputs.param = (param : HintedInstance Ω A → ℕ) := rfl

theorem toSec15Inputs_ell : (sec15Remaining ch).toSec15Inputs.ell = ellOf := rfl

theorem toSec15Inputs_IsJohnson :
    (sec15Remaining ch).toSec15Inputs.IsJohnson = (IsJohnson : HintedInstance Ω A → Prop) :=
  rfl

theorem toSec15Inputs_IsPrimitiveCase :
    (sec15Remaining ch).toSec15Inputs.IsPrimitiveCase
      = (IsPrimitiveCase : HintedInstance Ω A → Prop) := rfl

theorem toSec15Inputs_TIsOne :
    (sec15Remaining ch).toSec15Inputs.TIsOne = (TIsOne : HintedInstance Ω A → Prop) := rfl

theorem toSec15Inputs_SmallDefect :
    (sec15Remaining ch).toSec15Inputs.SmallDefect
      = (SmallDefect : HintedInstance Ω A → Prop) := rfl

theorem toSec15Inputs_AggregatesToStructure :
    (sec15Remaining ch).toSec15Inputs.AggregatesToStructure
      = (aggregatesToStructure : HintedInstance Ω A → Prop) := rfl

theorem toSec15Inputs_line1 :
    (sec15Remaining ch).toSec15Inputs.line1 = line1Round ch.line1 := rfl

theorem toSec15Inputs_line2 :
    (sec15Remaining ch).toSec15Inputs.line2 = line2Fun ch.line2 := rfl

theorem toSec15Inputs_line4a :
    (sec15Remaining ch).toSec15Inputs.line4a = fun i : HintedInstance Ω A =>
      line4aReduction i.inst := rfl

theorem toSec15Inputs_line4b :
    (sec15Remaining ch).toSec15Inputs.line4b = line4bFun ch.line4b := rfl

theorem toSec15Inputs_line4cd :
    (sec15Remaining ch).toSec15Inputs.line4cd = line4cdFun ch.line4cd := rfl

theorem toSec15Inputs_line56a7a :
    (sec15Remaining ch).toSec15Inputs.line56a7a = line56a7aFun ch.line56a7a := rfl

theorem toSec15Inputs_line567a :
    (sec15Remaining ch).toSec15Inputs.line567a = line567aFun ch.line567a := rfl

/-- §15: **the decision tree of the seven lines**, with every test and every branch named.
This is `Babai.Sec15Inputs.step` at the round of Sec. 15, with the fields above substituted;
the seven lemmas below are the seven ways through it. -/
theorem sec15Step_unfold :
    (sec15Remaining ch).toSec15Inputs.step i =
      if ¬ IsJohnson i then line1Round ch.line1 i
      else if param i ≤ ellOf i.inst.windowSize then line2Fun ch.line2 i
      else if IsPrimitiveCase i then
        (if TIsOne i then line4aReduction i.inst
          else if SmallDefect i then line4bFun ch.line4b i else line4cdFun ch.line4cd i)
      else if aggregatesToStructure i then line56a7aFun ch.line56a7a i
      else line567aFun ch.line567a i := rfl

/-- §15, **line 1**: *"Apply Procedure Reduce-to-Johnson (Luks reductions, Sec. 11.3)"*.
This is the branch taken when line 1 has not been carried out yet, that is, when the
instance is not in the Johnson case. -/
theorem sec15Step_eq_line1 (h : ¬ IsJohnson i) :
    (sec15MasterStep Ω A ch).step i = line1Round ch.line1 i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_pos h]

/-- §15, **line 2**: *"set `ℓ = (log n)³`; if `m ≤ ℓ` then apply imprimitive Luks reduction
to reduce to the kernel of the `G`-action on the blocks"*.  The test of line 1 has already
failed, so the instance is in the Johnson case. -/
theorem sec15Step_eq_line2 (hJ : IsJohnson i) (hl : param i ≤ ellOf i.inst.windowSize) :
    (sec15MasterStep Ω A ch).step i = line2Fun ch.line2 i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_pos hl]

/-- §15, **line 4a**: *"if `t = 1` then find `Iso_G(x,y)`, exit"*.  Reached in the Johnson
case with `m > ℓ` and `G` primitive. -/
theorem sec15Step_eq_line4a (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : IsPrimitiveCase i) (ht : TIsOne i) :
    (sec15MasterStep Ω A ch).step i = line4aReduction i.inst := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_neg hl,
    if_pos hp, if_pos ht]

/-- §15, **line 4b**: *"else (: `t ≥ 2` :) view `x, y` as edge-colored `t`-uniform
hypergraphs; if the relative symmetry defect of `H(x)` is `< 1/2` then apply
Cor. 12.0.10"*. -/
theorem sec15Step_eq_line4b (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i) (hs : SmallDefect i) :
    (sec15MasterStep Ω A ch).step i = line4bFun ch.line4b i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_neg hl,
    if_pos hp, if_neg ht, if_pos hs]

/-- §15, **lines 4c and 4d**: *"else apply the Extended Design Lemma (Theorem 9.2.3)"* and
*"apply Procedure Align to `X` (Sec. 14.1)"*, on the geometric data `ch.line4cd`. -/
theorem sec15Step_eq_line4cd (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : IsPrimitiveCase i) (ht : ¬ TIsOne i) (hs : ¬ SmallDefect i) :
    (sec15MasterStep Ω A ch).step i = line4cdFun ch.line4cd i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_neg hl,
    if_pos hp, if_neg ht, if_neg hs]

/-- §15, **lines 5, 6, 6a and 7a**: *"apply AggregateCertificates (Theorem 13.2.1)"*, which
returns a canonically embedded `k`-ary relational structure of relative symmetry defect
`≥ 1/2`; then the Extended Design Lemma on it, then Procedure Align. -/
theorem sec15Step_eq_line56a7a (hJ : IsJohnson i)
    (hl : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : aggregatesToStructure i) :
    (sec15MasterStep Ω A ch).step i = line56a7aFun ch.line56a7a i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_neg hl,
    if_neg hp, if_pos ha]

/-- §15, **lines 5, 7 and 7a**: AggregateCertificates returns a colored equipartition, which
Procedure Align is then applied to. -/
theorem sec15Step_eq_line567a (hJ : IsJohnson i)
    (hl : ¬ param i ≤ ellOf i.inst.windowSize) (hp : ¬ IsPrimitiveCase i)
    (ha : ¬ aggregatesToStructure i) :
    (sec15MasterStep Ω A ch).step i = line567aFun ch.line567a i := by
  rw [sec15MasterStep_step, sec15Step_unfold, if_neg (not_not_intro hJ), if_neg hl,
    if_neg hp, if_neg ha]

end Shape

end Babai
