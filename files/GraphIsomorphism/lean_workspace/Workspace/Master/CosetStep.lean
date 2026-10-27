/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15 and Remark 11.1.4: one round of the Master Algorithm in coset form, and the
alignment step that turns it into the round the machine layer runs.
-/
import Workspace.Master.StepShape
import Workspace.Master.ChoiceFamily

/-!
# The round of Sec. 15 in coset form

Eqs. (62)–(63) of §11.1 print a Luks reduction in two ways: the **middle form**, where the
call is made with respect to the coset `σH` and the second string is left alone, and the
**right-hand form**, where the call is made with respect to the group `H` and the second
string is shifted by `σ⁻¹`.  Remark 11.1.4 says the two are the same reduction, read in two
frames, and the passage from the first to the second is the *alignment step*.

`Babai.SIReduction.alignRed` is that step.  This file writes one round of the Master
Algorithm in the middle form — `Babai.ρ₀` — and reads off the two equations a machine layer
needs (`Algo.Round.runQ_eq_answer_align`):

* `Babai.sec15MasterStep_inst_eq_alignInst`: the instance the round holds is the alignment
  of the coset instance, and
* `Babai.sec15MasterStep_step_eq_alignRed`: the round is the alignment of `Babai.ρ₀`.

The coset instance is `Babai.instC i = i.inst`: at a group node the two frames agree, which
is exactly `Babai.alignInst_eq_self_of_isGroupInstance`, and being at a group node is what
`Algo.Round.runQ_eq_answer_align` already assumes through its `hgrp`.

Every branch is now in coset form. The step equation holds without a branch
hypothesis. The instance equation uses the group invariant supplied by the machine.
-/

universe u v w

namespace Babai

open scoped Classical

section Coset

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]


/-- §15, **line 4a in coset form**: the branch answers outright, so its coset form is the
answer read in the shifted frame of Eq. (62). -/
noncomputable def line4aCoset (I : SIInstance Ω A) : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  cosetLeaf I (matchingSet I.K I.Δ I.x I.y)

/-- §15, line 4a: **the branch is the alignment of its coset form** (Remark 11.1.4). -/
theorem line4aReduction_eq_alignRed (I : SIInstance Ω A) :
    line4aReduction I = SIReduction.alignRed I (line4aCoset I) := by
  rw [line4aCoset, alignRed_cosetLeaf]
  exact rfl

/-- §11.1, Eqs. (62)–(63): **the coset instance a node of the Master Algorithm holds**.  At a
group node the middle and right-hand frames agree, so this is the instance itself. -/
noncomputable def instC (i : HintedInstance Ω A) : SIInstance Ω A := i.inst

/-- §15, **one round of the Master Algorithm in coset form** (Remark 11.1.4): the decision
tree of `Babai.sec15Step_unfold` with each branch replaced by the middle form of
Eqs. (62)–(63).

Each branch is kept in coset form through every window lift. The live round
aligns it once at its root, as in Remark 11.1.4. -/
noncomputable def ρ₀ (ch : Sec15Choices Ω A q923 c923) (i : HintedInstance Ω A) :
    SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  if ¬ IsJohnson i then line1RoundCoset ch.line1 i
  else if param i ≤ ellOf i.inst.windowSize then line2FunCoset ch.line2 i
  else if IsPrimitiveCase i then
    (if TIsOne i then line4aCoset i.inst
      else if SmallDefect i then line4bFunCoset ch.line4b i else line4cdFunCoset ch.line4cd i)
  else if aggregatesToStructure i then line56a7aFunCoset ch.line56a7a i
  else line567aFunCoset ch.line567a i

/-- §11.1, Remark 11.1.4: **the instance the round holds is the alignment of the coset
instance**.  This is the hypothesis `hMinst` of `Algo.Round.runQ_eq_answer_align`, and it
needs exactly what that lemma's `hgrp` supplies. -/
theorem sec15MasterStep_inst_eq_alignInst (ch : Sec15Choices Ω A q923 c923)
    (i : HintedInstance Ω A) (h : IsGroupInstance i.inst) :
    (sec15MasterStep Ω A ch).inst i = alignInst (instC i) :=
  (alignInst_eq_self_of_isGroupInstance h).symm

/-- Remark 11.1.4: every branch of the master step is the alignment of its
coset tree. This equation includes the continuations for every oracle answer. -/
theorem sec15MasterStep_step_eq_alignRed (ch : Sec15Choices Ω A q923 c923)
    (i : HintedInstance Ω A) :
    (sec15MasterStep Ω A ch).step i = SIReduction.alignRed (instC i) (ρ₀ ch i) := by
  change (sec15Remaining ch).toSec15Inputs.step i = _
  rw [sec15Step_unfold]
  unfold ρ₀ instC
  split_ifs <;> first
    | exact line1Round_eq_alignRed ch.line1 i
    | exact line2Fun_eq_alignRed ch.line2 i
    | exact line4aReduction_eq_alignRed i.inst
    | rfl

/-- §15, **line 1 is the alignment of `Babai.ρ₀`** (Remark 11.1.4). -/
theorem sec15MasterStep_step_eq_alignRed_line1 (ch : Sec15Choices Ω A q923 c923)
    (i : HintedInstance Ω A) (h : ¬ IsJohnson i) :
    (sec15MasterStep Ω A ch).step i = SIReduction.alignRed (instC i) (ρ₀ ch i) := by
  rw [sec15Step_eq_line1 ch i h, ρ₀, if_pos h, instC, line1Round_eq_alignRed]

/-- §15, **line 2 is the alignment of `Babai.ρ₀`** (Remark 11.1.4). -/
theorem sec15MasterStep_step_eq_alignRed_line2 (ch : Sec15Choices Ω A q923 c923)
    (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hl : param i ≤ ellOf i.inst.windowSize) :
    (sec15MasterStep Ω A ch).step i = SIReduction.alignRed (instC i) (ρ₀ ch i) := by
  rw [sec15Step_eq_line2 ch i hJ hl, ρ₀, if_neg (not_not_intro hJ), if_pos hl, instC,
    line2Fun_eq_alignRed]

/-- §15, **line 4a is the alignment of `Babai.ρ₀`** (Remark 11.1.4). -/
theorem sec15MasterStep_step_eq_alignRed_line4a (ch : Sec15Choices Ω A q923 c923)
    (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hl : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i) (ht : TIsOne i) :
    (sec15MasterStep Ω A ch).step i = SIReduction.alignRed (instC i) (ρ₀ ch i) := by
  rw [sec15Step_eq_line4a ch i hJ hl hp ht, ρ₀, if_neg (not_not_intro hJ), if_neg hl,
    if_pos hp, if_pos ht, instC, line4aReduction_eq_alignRed]

end Coset

section Family

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {κ' : Type w}

/-- §11.1, Eqs. (62)–(63): the coset instance a **raw** node holds, along a family of
choices (`Babai.masterStepOfFamily`). -/
noncomputable def instCOfFamily (p : κ' → HintedInstance Ω A) (r : κ') : SIInstance Ω A :=
  instC (p r)

/-- §15, **one round in coset form along a family of choices**. -/
noncomputable def ρ₀OfFamily (chOf : κ' → Sec15Choices Ω A q923 c923)
    (p : κ' → HintedInstance Ω A) (r : κ') : SIReduction Ω A (Set (Equiv.Perm Ω)) :=
  ρ₀ (chOf r) (p r)

variable (chOf : κ' → Sec15Choices Ω A q923 c923) (p : κ' → HintedInstance Ω A)
  (lift' : κ' → SIInstance Ω A → κ') (top' : SIInstance Ω A → κ')
  (hlift : ∀ (r : κ') (J : SIInstance Ω A),
    J ∈ ((sec15MasterStep Ω A (chOf r)).step (p r)).calls →
    p (lift' r J) = (sec15MasterStep Ω A (chOf r)).lift (p r) J)
  (htop : ∀ I : SIInstance Ω A, p (top' I) = (sec15MasterStep Ω A (chOf (top' I))).top I)

/-- `hMinst` of `Algo.Round.runQ_eq_answer_align` for `Babai.masterStepOfFamily`. -/
theorem masterStepOfFamily_inst_eq_alignInst (r : κ')
    (h : IsGroupInstance ((masterStepOfFamily chOf p lift' top' hlift htop).inst r)) :
    (masterStepOfFamily chOf p lift' top' hlift htop).inst r
      = alignInst (instCOfFamily p r) :=
  (alignInst_eq_self_of_isGroupInstance h).symm

/-- The master-step tree equation along a family of choices, without a case test. -/
theorem masterStepOfFamily_step_eq_alignRed (r : κ') :
    (masterStepOfFamily chOf p lift' top' hlift htop).step r =
      SIReduction.alignRed (instCOfFamily p r) (ρ₀OfFamily chOf p r) :=
  sec15MasterStep_step_eq_alignRed (chOf r) (p r)

/-- `hMstep` of `Algo.Round.runQ_eq_answer_align` for `Babai.masterStepOfFamily`, at the
branch of line 1. -/
theorem masterStepOfFamily_step_eq_alignRed_line1 (r : κ') (h : ¬ IsJohnson (p r)) :
    (masterStepOfFamily chOf p lift' top' hlift htop).step r
      = SIReduction.alignRed (instCOfFamily p r) (ρ₀OfFamily chOf p r) :=
  sec15MasterStep_step_eq_alignRed_line1 (chOf r) (p r) h

/-- `hMstep` for `Babai.masterStepOfFamily`, at the branch of line 2. -/
theorem masterStepOfFamily_step_eq_alignRed_line2 (r : κ') (hJ : IsJohnson (p r))
    (hl : param (p r) ≤ ellOf (p r).inst.windowSize) :
    (masterStepOfFamily chOf p lift' top' hlift htop).step r
      = SIReduction.alignRed (instCOfFamily p r) (ρ₀OfFamily chOf p r) :=
  sec15MasterStep_step_eq_alignRed_line2 (chOf r) (p r) hJ hl

/-- `hMstep` for `Babai.masterStepOfFamily`, at the branch of line 4a. -/
theorem masterStepOfFamily_step_eq_alignRed_line4a (r : κ') (hJ : IsJohnson (p r))
    (hl : ¬ param (p r) ≤ ellOf (p r).inst.windowSize) (hp : IsPrimitiveCase (p r))
    (ht : TIsOne (p r)) :
    (masterStepOfFamily chOf p lift' top' hlift htop).step r
      = SIReduction.alignRed (instCOfFamily p r) (ρ₀OfFamily chOf p r) :=
  sec15MasterStep_step_eq_alignRed_line4a (chOf r) (p r) hJ hl hp ht

end Family

end Babai
