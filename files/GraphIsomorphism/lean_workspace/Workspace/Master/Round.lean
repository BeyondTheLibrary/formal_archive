/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: one round of Procedure String-Isomorphism, with lines 1, 2 and 4a carried out
by named reductions.
-/
import Workspace.Master.Line1

/-!
# The round of Sec. 15, with line 1 filled in

`Workspace/Master/Assemble.lean` has the control flow of Sec. 15 as a `Babai.Sec15Inputs`.
`Babai.Sec15Remaining` is the same table with the branches that *are* named reductions
already filled:

| line | named reduction |
|---|---|
| 1 | `Babai.line1Round` (Procedure Reduce-to-Johnson, §11.3) |
| 2 | `Babai.line2Branch` (the imprimitive Luks reduction) |
| 4a | `Babai.line4aReduction` (the trivial case `t = 1`) |
| 4b | `Babai.line4bBranch` (Cor. 12.0.10) |

What is left are lines 4c–4d and lines 5–7a, which wait on Theorem 9.2.3 and
Theorem 13.2.1; see the "Mismatches" section of `Workspace/Master/DESIGN.md`.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

section Round

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω]

/-- §15, **the branches that are not yet named reductions**: lines 4c–4d and lines 5–7a.

The tests are no longer abstract: `Babai.IsJohnson`, `Babai.param`, `Babai.TIsOne` and
`Babai.IsPrimitiveCase` are read off the hint the instance carries
(`Babai.HintedInstance`), and the data itself is available to the branches through
`Babai.johnsonData`.  Lines 1, 2 and 4a are not fields: they are the named reductions
`Babai.line1Round` (Procedure Reduce-to-Johnson, §11.3), `Babai.line2Branch` and
`Babai.line4aReduction`, and their facts are theorems.

The field `lift` is what a round hands to each of its calls (Sec. 14.2; line 11 of
Procedure Align).  Lines 1, 2 and 4b prescribe it: line 1 attaches the Johnson case data of
step 7 of Procedure Reduce-to-Johnson (`Babai.line1Lift`), and lines 2 and 4b shrink the
window and start again at line 1, so their calls carry nothing. -/
structure Sec15Remaining (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] where
  /-- The number of instances one round produces. -/
  roundCost : ℕ → ℕ
  /-- It covers what lines 1, 2 and 4b cost. -/
  roundCost_ge : ∀ n, masterRoundCost n + line1RoundCost n ≤ roundCost n
  /-- §11.3: which branch of Procedure Reduce-to-Johnson line 1 takes at each instance.
  The round is built for every such choice; see the corrected paper entry on Finding 1 of
  the audit of Secs. 14–15. -/
  line1Choice : Line1Choice Ω A
  /-- The supplied image and orbit lists for line 2. -/
  line2Choice : Line2Choice Ω A
  /-- The supplied data and lists for line 4b. -/
  line4bChoice : Line4bChoice Ω A
  /-- What the round hands to each of its calls. -/
  lift : HintedInstance Ω A → SIInstance Ω A → HintedInstance Ω A
  /-- A hint does not change the instance it is attached to. -/
  lift_inst : ∀ (i : HintedInstance Ω A) (J : SIInstance Ω A), (lift i J).inst = J
  /-- Line 1 hands down the Johnson case data of step 7. -/
  lift_line1 : ∀ i : HintedInstance Ω A, ¬ IsJohnson i → lift i = line1Lift line1Choice i
  /-- Line 2 shrinks the window; its calls start again at line 1. -/
  lift_line2 : ∀ i : HintedInstance Ω A, IsJohnson i →
      param i ≤ ellOf i.inst.windowSize → lift i = fun J => ⟨J, none⟩
  /-- Line 4b shrinks the window; its calls start again at line 1. -/
  lift_line4b : ∀ i : HintedInstance Ω A, IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      SmallDefect i → lift i = fun J => ⟨J, none⟩
  /-- Line 6: *"if AggregateCertificates returns canonically embedded `k`-ary relational
  structure on `Γ` with relative symmetry defect `≥ 1/2`"*. -/
  AggregatesToStructure : HintedInstance Ω A → Prop
  /-- Lines 4c and 4d. -/
  line4cd : HintedInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Lines 5, 6, 6a and 7a. -/
  line56a7a : HintedInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- Lines 5, 7 and 7a. -/
  line567a : HintedInstance Ω A → SIReduction Ω A (Set (Equiv.Perm Ω))
  line4cd_run : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → (line4cd i).run = i.inst.answer
  line4cd_decreases : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ∀ J ∈ (line4cd i).calls,
      MakesProgress HintedInstance.win param i (lift i J)
  line4cd_calls : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ((line4cd i).calls).length ≤ roundCost i.inst.windowSize
  line56a7a_run : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → (line56a7a i).run = i.inst.answer
  line56a7a_decreases : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → ∀ J ∈ (line56a7a i).calls,
      MakesProgress HintedInstance.win param i (lift i J)
  line56a7a_calls : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → ((line56a7a i).calls).length ≤ roundCost i.inst.windowSize
  line567a_run : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → (line567a i).run = i.inst.answer
  line567a_decreases : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → ∀ J ∈ (line567a i).calls,
      MakesProgress HintedInstance.win param i (lift i J)
  line567a_calls : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → ((line567a i).calls).length ≤ roundCost i.inst.windowSize
  /-- Lines 4c and 4d produce group instances. -/
  line4cd_group : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → IsPrimitiveCase i → ¬ TIsOne i →
      ¬ SmallDefect i → ∀ J ∈ (line4cd i).calls, IsGroupInstance J
  /-- Lines 5, 6, 6a and 7a produce group instances. -/
  line56a7a_group : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      AggregatesToStructure i → ∀ J ∈ (line56a7a i).calls, IsGroupInstance J
  /-- Lines 5, 7 and 7a produce group instances. -/
  line567a_group : ∀ i : HintedInstance Ω A, IsGroupInstance i.inst → IsJohnson i →
      ¬ param i ≤ ellOf i.inst.windowSize → ¬ IsPrimitiveCase i →
      ¬ AggregatesToStructure i → ∀ J ∈ (line567a i).calls, IsGroupInstance J

namespace Sec15Remaining

variable (R : Sec15Remaining Ω A)

/-- §15, line 2, **correct**: at an instance of the Johnson case the branch returns the
answer. -/
theorem line2Fun_run (i : HintedInstance Ω A) (h : IsJohnson i) :
    (line2Fun R.line2Choice i).run = i.inst.answer := by
  rw [line2Fun, dif_pos h, run_line2Branch]

/-- §15, line 2, **the progress**: every call has a window of at most `2n/3` (indeed of at
most `n/2`), and the window of the instance is nonempty. -/
theorem line2Fun_decreases (i : HintedInstance Ω A) (h : IsJohnson i) :
    ∀ J ∈ (line2Fun R.line2Choice i).calls,
      MakesProgress HintedInstance.win param i (⟨J, none⟩ : HintedInstance Ω A) := by
  intro J hJ
  rw [line2Fun, dif_pos h] at hJ
  have h2 := decreases_line2Branch (johnsonData h) (R.line2Choice i h) J hJ
  have h1 := (johnsonData h).one_le_windowSize
  exact Or.inl ⟨h1, by show 5 * J.windowSize ≤ 4 * i.inst.windowSize; omega⟩

/-- §15, line 2, **the number of calls**: the multiplicative cost `ℓ!` of the brute force
over `Ḡ`, once per orbit of `N`. -/
theorem line2Fun_calls (i : HintedInstance Ω A) (h : IsJohnson i)
    (hℓ : param i ≤ ellOf i.inst.windowSize) :
    ((line2Fun R.line2Choice i).calls).length ≤ masterRoundCost i.inst.windowSize := by
  rw [line2Fun, dif_pos h]
  refine le_trans (calls_length_line2Branch (johnsonData h) (R.line2Choice i h)) ?_
  have hm : (johnsonData h).m ≤ ellOf i.inst.windowSize := by rw [← param_eq h]; exact hℓ
  have hfac : Nat.factorial (johnsonData h).m ≤ Nat.factorial (ellOf i.inst.windowSize) :=
    Nat.factorial_le hm
  have := Nat.mul_le_mul_right i.inst.windowSize hfac
  rw [masterRoundCost]
  omega

/-- §15, line 4b, **correct**. -/
theorem line4bFun_run (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hℓ : ¬ param i ≤ ellOf i.inst.windowSize) (hs : SmallDefect i) :
    (line4bFun R.line4bChoice i).run = i.inst.answer := by
  rw [line4bFun, line4bFunCoset, dif_pos (⟨⟨hJ, hℓ⟩, hs⟩ :
    (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ SmallDefect i)]
  exact run_line4bBranch _ _ _

/-- §15, line 4b, **the progress**: every call has a window of at most `2n/3`. -/
theorem line4bFun_decreases (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hℓ : ¬ param i ≤ ellOf i.inst.windowSize) (hs : SmallDefect i) :
    ∀ J ∈ (line4bFun R.line4bChoice i).calls,
      MakesProgress HintedInstance.win param i (⟨J, none⟩ : HintedInstance Ω A) := by
  intro J hJmem
  rw [line4bFun, line4bFunCoset, dif_pos (⟨⟨hJ, hℓ⟩, hs⟩ :
    (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ SmallDefect i)] at hJmem
  refine Or.inl ⟨(johnsonData hJ).one_le_windowSize, ?_⟩
  have := decreases_line4bBranch _ _ _ J hJmem
  show 5 * J.windowSize ≤ 4 * i.inst.windowSize
  omega

/-- §15, line 4b, **the number of calls**: at most `7n`. -/
theorem line4bFun_calls (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hℓ : ¬ param i ≤ ellOf i.inst.windowSize) (hs : SmallDefect i) :
    ((line4bFun R.line4bChoice i).calls).length ≤ masterRoundCost i.inst.windowSize := by
  rw [line4bFun, line4bFunCoset, dif_pos (⟨⟨hJ, hℓ⟩, hs⟩ :
    (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ SmallDefect i)]
  refine le_trans (calls_length_line4bBranch _ _ _) ?_
  rw [masterRoundCost]
  omega

/-- §15, line 2: **every call is a group instance**. -/
theorem line2Fun_group (i : HintedInstance Ω A) (h : IsJohnson i) :
    ∀ J ∈ (line2Fun R.line2Choice i).calls, IsGroupInstance J := by
  intro J hJ
  rw [line2Fun, dif_pos h] at hJ
  exact calls_line2Branch_isGroupInstance (johnsonData h) (R.line2Choice i h) J hJ

/-- §15, line 4b: **every call is a group instance**. -/
theorem line4bFun_group (i : HintedInstance Ω A) (hJ : IsJohnson i)
    (hℓ : ¬ param i ≤ ellOf i.inst.windowSize) (hs : SmallDefect i) :
    ∀ J ∈ (line4bFun R.line4bChoice i).calls, IsGroupInstance J := by
  intro J hJmem
  rw [line4bFun, line4bFunCoset, dif_pos (⟨⟨hJ, hℓ⟩, hs⟩ :
    (IsJohnson i ∧ ¬ param i ≤ ellOf i.inst.windowSize) ∧ SmallDefect i)] at hJmem
  exact calls_line4bBranch_isGroupInstance _ _ _ J hJmem

/-- §15, **the round**, with lines 1, 2, 4a and 4b filled by the named reductions and the
other three branches taken from `R`. -/
noncomputable def toSec15Inputs : Sec15Inputs Ω A (HintedInstance Ω A) where
  inst := HintedInstance.inst
  lift := R.lift
  top := fun I => ⟨I, none⟩
  lift_inst := R.lift_inst
  inst_top := fun _ => rfl
  param := param
  ell := ellOf
  roundCost := R.roundCost
  IsJohnson := IsJohnson
  IsPrimitiveCase := IsPrimitiveCase
  TIsOne := TIsOne
  SmallDefect := SmallDefect
  AggregatesToStructure := R.AggregatesToStructure
  line1 := line1Round R.line1Choice
  line2 := line2Fun R.line2Choice
  line4a := fun i => line4aReduction i.inst
  line4b := line4bFun R.line4bChoice
  line4cd := R.line4cd
  line56a7a := R.line56a7a
  line567a := R.line567a
  param_le := param_le
  line1_run := fun i _ _ => run_line1Round R.line1Choice i
  line1_decreases := fun i _ hJ => by
    rw [R.lift_line1 i hJ]
    exact decreases_line1Round R.line1Choice i hJ
  line1_calls := fun i _ _ =>
    le_trans (calls_length_line1Round R.line1Choice i)
      (le_trans (Nat.le_add_left _ _) (R.roundCost_ge i.inst.windowSize))
  line2_run := fun i _ h _ => line2Fun_run R i h
  line2_decreases := fun i _ h hℓ => by
    rw [R.lift_line2 i h hℓ]
    exact line2Fun_decreases R i h
  line2_calls := fun i _ h hℓ =>
    le_trans (line2Fun_calls R i h hℓ)
      (le_trans (Nat.le_add_right _ _) (R.roundCost_ge i.inst.windowSize))
  line4a_run := fun i _ _ _ _ _ => run_line4aReduction i.inst
  line4a_calls := fun i _ _ _ _ _ => calls_line4aReduction i.inst
  line4b_run := fun i _ hJ hℓ _ _ hs => line4bFun_run R i hJ hℓ hs
  line4b_decreases := fun i _ hJ hℓ hp ht hs => by
    rw [R.lift_line4b i hJ hℓ hp ht hs]
    exact line4bFun_decreases R i hJ hℓ hs
  line4b_calls := fun i _ hJ hℓ _ _ hs =>
    le_trans (line4bFun_calls R i hJ hℓ hs)
      (le_trans (Nat.le_add_right _ _) (R.roundCost_ge i.inst.windowSize))
  line4cd_run := R.line4cd_run
  line4cd_decreases := R.line4cd_decreases
  line4cd_calls := R.line4cd_calls
  line56a7a_run := R.line56a7a_run
  line56a7a_decreases := R.line56a7a_decreases
  line56a7a_calls := R.line56a7a_calls
  line567a_run := R.line567a_run
  line567a_decreases := R.line567a_decreases
  line567a_calls := R.line567a_calls
  line1_group := fun i _ _ => calls_line1Round_isGroupInstance R.line1Choice i
  line2_group := fun i _ h _ => line2Fun_group R i h
  line4b_group := fun i _ hJ hℓ _ _ hs => line4bFun_group R i hJ hℓ hs
  line4cd_group := R.line4cd_group
  line56a7a_group := R.line56a7a_group
  line567a_group := R.line567a_group

/-- §15, **Procedure String-Isomorphism** as one round of the Master Algorithm, with the
tests of the pseudo-code defined and lines 1, 2, 4a and 4b carried out by named
reductions. -/
noncomputable def masterStep : MasterStep Ω A (HintedInstance Ω A) :=
  masterStep_of_procedure R.toSec15Inputs

end Sec15Remaining

end Round

end Babai
