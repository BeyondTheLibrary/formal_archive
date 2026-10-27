/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: the seven lines of the Master Algorithm assembled into one round.
-/
import Workspace.Master.Round
import Workspace.Master.Line56a7a

/-!
# The round of Sec. 15, with every line filled in

`Babai.Sec15Remaining` is the table of the branches of one round that are not named
reductions: lines 4c–4d, lines 5–6a–7a and lines 5–7–7a.  Rounds 16–19 built the three of
them, and this file puts them together into a value of that table, `Babai.sec15Remaining`.

| line | branch | lift | cost |
|---|---|---|---|
| 1 | `Babai.line1Round` | `Babai.line1Lift` | `Babai.line1RoundCost` |
| 2 | `Babai.line2Fun` | none | `Babai.masterRoundCost` |
| 4a | `Babai.line4aReduction` | none | `0` |
| 4b | `Babai.line4bFun` | none | `Babai.masterRoundCost` |
| 4c–4d | `Babai.line4cdFun` | `Babai.line4cdLift` | `Babai.line4cdCost` |
| 5, 6, 6a, 7a | `Babai.line56a7aFun` | `Babai.line56a7aLift` | `Babai.line56a7aCost` |
| 5, 7, 7a | `Babai.line567aFun` | `Babai.line567aLift` | `Babai.line567aCost` |

**The lift.**  `Babai.sec15Lift` is the decision tree of the seven lines, read as a function
of the instance: it hands down what the line the instance is dispatched to hands down.  The
order of the tests is the order of the pseudo-code, which is what makes the three fields
`lift_line1`, `lift_line2` and `lift_line4b` of `Babai.Sec15Remaining` hold — line 4b's test
is reached only after line 4's, so a line-4b instance never falls to the branch of lines
5–7a even when Theorem 13.2.1 would land in case (1) on it.

**The cost.**  `Babai.sec15RoundCost` is the sum of the six costs, which is above each of
them; it is monotone and quasipolynomial whenever the multiplicative cost `q` of
Theorem 9.2.3 is (`Babai.quasiPolyBound_sec15RoundCost`).

**Status.**  All seven lines of Sec. 15 are proved, outcome (2b) of
Theorem 13.2.1 included (`Babai.nonempty_line6aCase2bCore`), and `Babai.Theorem_1_1_1_math`
depends on no `sorry`.  This file counts String Isomorphism instances only.  The running time
is proved on the RAM model of `Workspace/Machine/` by `Algo.theorem_1_1_1`
(`Workspace/Algo/TopMasterClose.lean`), whose program walks these same reductions.
-/

universe u v

namespace Babai

open MulAction Equiv Equiv.Perm

/-! ### The cost of one round -/

section Cost

/-- `n ↦ n^5`, the individualization cost of case (2b), is polynomially bounded. -/
theorem polyBound_pow_five : RAM.PolyBound (fun n : ℕ => n ^ 5) :=
  ⟨1, 5, fun n => by simpa using Nat.pow_le_pow_left (Nat.le_succ n) 5⟩

/-- §15, lines 5, 6, 6a and 7a: the cost of one round is non-decreasing. -/
theorem line56a7aCost_mono (q : ℕ → ℕ) (c : ℕ) : Monotone (line56a7aCost q c) := by
  intro a b hab
  have h1 : a ^ 5 ≤ b ^ 5 := Nat.pow_le_pow_left hab 5
  have h2 : qMax q a ≤ qMax q b := qMax_mono q hab
  have h3 : a ^ (c * testSetSize a) ≤ b ^ (c * testSetSize b) :=
    pow_mul_testSetSize_mono c hab
  have h4 : AlignDominantRoundData.alignDominantRoundCost a
      ≤ AlignDominantRoundData.alignDominantRoundCost b := alignDominantRoundCost_mono hab
  have h5 : aggregateAllowance a ≤ aggregateAllowance b := aggregateAllowance_mono hab
  rw [line56a7aCost, line56a7aCost]
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1
    (Nat.mul_le_mul h2 h3)) (by omega)) h4) h5

/-- §15, lines 5, 6, 6a and 7a: the cost of one round is quasipolynomial. -/
theorem quasiPolyBound_line56a7aCost {q : ℕ → ℕ} (hq : RAM.QuasiPolyBound q) (c : ℕ) :
    RAM.QuasiPolyBound (line56a7aCost q c) := by
  have h : RAM.QuasiPolyBound (fun n =>
      n ^ 5 * (qMax q n * n ^ (c * testSetSize n)) * (n + 1) *
        AlignDominantRoundData.alignDominantRoundCost n + aggregateAllowance n) :=
    (((polyBound_pow_five.quasiPoly.mul
        ((quasiPolyBound_qMax hq).mul (quasiPolyBound_pow_testSetSize c))).mul
      quasiPolyBound_succ).mul quasiPolyBound_alignDominantRoundCost).add
      quasiPolyBound_aggregateAllowance
  exact h.mono fun n => le_of_eq rfl

/-- §15: **the number of instances one round of the Master Algorithm produces** — the sum of
the costs of the six branches that make calls. -/
def sec15RoundCost (q : ℕ → ℕ) (c : ℕ) (n : ℕ) : ℕ :=
  masterRoundCost n + line1RoundCost n + line4cdCost q c n + line567aCost n +
    line56a7aCost q c n

theorem sec15RoundCost_mono (q : ℕ → ℕ) (c : ℕ) : Monotone (sec15RoundCost q c) := by
  intro a b hab
  have h1 := masterRoundCost_mono hab
  have h2 := line1RoundCost_mono hab
  have h3 := line4cdCost_mono q c hab
  have h4 := line567aCost_mono hab
  have h5 := line56a7aCost_mono q c hab
  rw [sec15RoundCost, sec15RoundCost]
  omega

/-- §15: **the cost of one round is quasipolynomial** whenever the multiplicative cost of
Theorem 9.2.3 is.  This is the hypothesis of `Babai.Theorem_1_1_1_math_of_sec15Inputs`, in
the `log₂ n + 2` form of `RAM.QuasiPolyBound` (see the the corrected paper the
round-cost hypothesis of Theorem 1.1.1). -/
theorem quasiPolyBound_sec15RoundCost {q : ℕ → ℕ} (hq : RAM.QuasiPolyBound q) (c : ℕ) :
    RAM.QuasiPolyBound (sec15RoundCost q c) := by
  have h : RAM.QuasiPolyBound (fun n => masterRoundCost n + line1RoundCost n +
      line4cdCost q c n + line567aCost n + line56a7aCost q c n) :=
    ((((quasiPolyBound_masterRoundCost.add quasiPolyBound_line1RoundCost).add
      (quasiPolyBound_line4cdCost hq c)).add quasiPolyBound_line567aCost).add
      (quasiPolyBound_line56a7aCost hq c))
  exact h.mono fun n => le_of_eq rfl

end Cost

/-! ### The lift: what a round hands to each of its calls -/

section Lift

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]
  {q : ℕ → ℕ} {c : ℕ}

/-- §15: **the choices one round of the Master Algorithm makes**.

Line 1 chooses the branch of Procedure Reduce-to-Johnson that applies, with the data that
branch runs on (`Babai.Line1Choice`); lines 4c–4d choose the geometric data of one round of
Procedure Align (`Babai.Line4cdChoice`).  Both are choices of *data*, as the paper's
*"find a minimal block system"* and *"apply the Extended Design Lemma"* are; the reduction
each line runs is a named function of the data.  The round, and `Babai.Theorem_1_1_1_math`
with it, is stated for **every** such structure of choices.

Lines 5–7 choose in the same way (`Babai.Line567aChoice`, `Babai.Line56a7aChoice`): one
round on the window at each outcome of Theorem 13.2.1, with a reject exit that carries its
own test.  See the corrected paper entries on Finding 1 of the audit of Secs. 14–15. -/
structure Sec15Choices (Ω : Type u) (A : Type v) [Fintype Ω] [DecidableEq Ω] [Fintype A]
    [DecidableEq A] (q : ℕ → ℕ) (c : ℕ) where
  /-- Line 1: which branch of Procedure Reduce-to-Johnson applies, and its data. -/
  line1 : Line1Choice Ω A
  /-- Line 2: image elements and kernel orbits. -/
  line2 : Line2Choice Ω A
  /-- Line 4b: the canonical coloring and top-action lists. -/
  line4b : Line4bChoice Ω A
  /-- Lines 4c–4d: the data Procedure Align runs on. -/
  line4cd : Line4cdChoice Ω A q c
  /-- Lines 5, 7 and 7a: outcome (1) of Theorem 13.2.1 and the Cor. 12.0.10 branch of
  outcome (2a). -/
  line567a : Line567aChoice Ω A
  /-- Lines 5, 6, 6a and 7a: outcomes (2b) and (3) of Theorem 13.2.1. -/
  line56a7a : Line56a7aChoice Ω A q c

/-- §15: **the choices are inhabited** (`Babai.line1Case`, `Babai.line4cdDataOf`).  This is
the one place where `Classical.choice` enters the concrete round. -/
noncomputable def sec15Choices (hu : Theorem923Uniform q c) : Sec15Choices Ω A q c where
  line1 := line1ChoiceOfCases
  line2 := line2ChoiceOf
  line4b := line4bChoiceOf
  line4cd := line4cdDataOf hu
  line567a := line567aChoiceOf
  line56a7a := line56a7aChoiceOf hu

/-- §15, **the hint one round hands to each of its calls**, as a function of the instance:
the decision tree of the seven lines, each leaf handing down what its line hands down.

Lines 2, 4a and 4b shrink the window and start again at line 1, so their calls carry
nothing; line 1 attaches the Johnson case data of step 7 of Procedure Reduce-to-Johnson;
lines 4c–4d and lines 5–7a attach the hint of line 11 of Procedure Align. -/
noncomputable def sec15Lift (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : HintedInstance Ω A :=
  if ¬ IsJohnson i then line1Lift ch.line1 i J
  else if param i ≤ ellOf i.inst.windowSize then ⟨J, none⟩
  else if IsPrimitiveCase i then
    (if ¬ TIsOne i ∧ ¬ SmallDefect i then line4cdLift ch.line4cd i J else ⟨J, none⟩)
  else if aggregatesToStructure i then line56a7aLift ch.line56a7a i J
  else line567aLift ch.line567a i J

theorem inst_sec15Lift (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A) (J : SIInstance Ω A) : (sec15Lift ch i J).inst = J := by
  rw [sec15Lift]
  split_ifs
  all_goals first
    | exact inst_line1Lift ch.line1 i J
    | exact inst_line4cdLift ch.line4cd i J
    | exact inst_line56a7aLift ch.line56a7a i J
    | exact inst_line567aLift ch.line567a i J
    | rfl

theorem sec15Lift_line1 (ch : Sec15Choices Ω A q c) (i : HintedInstance Ω A)
    (h : ¬ IsJohnson i) : sec15Lift ch i = line1Lift ch.line1 i :=
  funext fun J => by rw [sec15Lift, if_pos h]

theorem sec15Lift_line2 (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A)
    (hJ : IsJohnson i) (hl : param i ≤ ellOf i.inst.windowSize) :
    sec15Lift ch i = fun J => (⟨J, none⟩ : HintedInstance Ω A) :=
  funext fun J => by rw [sec15Lift, if_neg (not_not_intro hJ), if_pos hl]

theorem sec15Lift_line4b (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A)
    (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i)
    (ht : ¬ TIsOne i) (hs : SmallDefect i) :
    sec15Lift ch i = fun J => (⟨J, none⟩ : HintedInstance Ω A) :=
  funext fun J => by
    rw [sec15Lift, if_neg (not_not_intro hJ), if_neg hl, if_pos hp,
      if_neg (fun hc : ¬ TIsOne i ∧ ¬ SmallDefect i => hc.2 hs)]

theorem sec15Lift_line4cd (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A)
    (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize) (hp : IsPrimitiveCase i)
    (ht : ¬ TIsOne i) (hs : ¬ SmallDefect i) : sec15Lift ch i = line4cdLift ch.line4cd i :=
  funext fun J => by
    rw [sec15Lift, if_neg (not_not_intro hJ), if_neg hl, if_pos hp, if_pos ⟨ht, hs⟩]

theorem sec15Lift_line56a7a (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A)
    (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : aggregatesToStructure i) :
    sec15Lift ch i = line56a7aLift ch.line56a7a i :=
  funext fun J => by
    rw [sec15Lift, if_neg (not_not_intro hJ), if_neg hl, if_neg hp, if_pos ha]

theorem sec15Lift_line567a (ch : Sec15Choices Ω A q c)
    (i : HintedInstance Ω A)
    (hJ : IsJohnson i) (hl : ¬ param i ≤ ellOf i.inst.windowSize)
    (hp : ¬ IsPrimitiveCase i) (ha : ¬ aggregatesToStructure i) :
    sec15Lift ch i = line567aLift ch.line567a i :=
  funext fun J => by
    rw [sec15Lift, if_neg (not_not_intro hJ), if_neg hl, if_neg hp, if_neg ha]

end Lift

/-! ### The value of `Babai.Sec15Remaining` -/

section Value

open scoped Classical

variable {Ω : Type u} {A : Type v} [Fintype Ω] [DecidableEq Ω] [Fintype A] [DecidableEq A]

/-- §15, **the three branches of the round that are not named reductions**, with their
lift and their cost: lines 4c–4d, lines 5–6–6a–7a and lines 5–7–7a.

This is the value `Babai.Sec15Remaining` was waiting for, so `Babai.Sec15Remaining.masterStep`
is now one round of Procedure String-Isomorphism with every line of the pseudo-code carried
out. -/
noncomputable def sec15Remaining {q : ℕ → ℕ} {c : ℕ}
    (ch : Sec15Choices Ω A q c) : Sec15Remaining Ω A where
  roundCost := sec15RoundCost q c
  roundCost_ge n := by rw [sec15RoundCost]; omega
  line1Choice := ch.line1
  line2Choice := ch.line2
  line4bChoice := ch.line4b
  lift := sec15Lift ch
  lift_inst := inst_sec15Lift ch
  lift_line1 i h := sec15Lift_line1 ch i h
  lift_line2 i hJ hl := sec15Lift_line2 ch i hJ hl
  lift_line4b i hJ hl hp ht hs := sec15Lift_line4b ch i hJ hl hp ht hs
  AggregatesToStructure := aggregatesToStructure
  line4cd := line4cdFun ch.line4cd
  line56a7a := line56a7aFun ch.line56a7a
  line567a := line567aFun ch.line567a
  line4cd_run i hg hJ hl hp ht hs := line4cd_run ch.line4cd i hg hJ hl hp ht hs
  line4cd_decreases i hg hJ hl hp ht hs J hJmem := by
    rw [show sec15Lift ch i J = line4cdLift ch.line4cd i J from
      congrFun (sec15Lift_line4cd ch i hJ hl hp ht hs) J]
    exact line4cd_decreases ch.line4cd i hg hJ hl hp ht hs J hJmem
  line4cd_calls i hg hJ hl hp ht hs := by
    refine le_trans (line4cd_calls ch.line4cd i hg hJ hl hp ht hs) ?_
    rw [sec15RoundCost]
    omega
  line56a7a_run i hg hJ hl hp ha := line56a7a_run ch.line56a7a i hg hJ hl hp ha
  line56a7a_decreases i hg hJ hl hp ha J hJmem := by
    rw [show sec15Lift ch i J = line56a7aLift ch.line56a7a i J from
      congrFun (sec15Lift_line56a7a ch i hJ hl hp ha) J]
    exact line56a7a_decreases ch.line56a7a i hg hJ hl hp ha J hJmem
  line56a7a_calls i hg hJ hl hp ha := by
    refine le_trans (line56a7a_calls ch.line56a7a i hg hJ hl hp ha) ?_
    rw [sec15RoundCost]
    omega
  line567a_run i hg hJ hl hp ha := line567a_run ch.line567a i hg hJ hl hp ha
  line567a_decreases i hg hJ hl hp ha J hJmem := by
    rw [show sec15Lift ch i J = line567aLift ch.line567a i J from
      congrFun (sec15Lift_line567a ch i hJ hl hp ha) J]
    exact line567a_decreases ch.line567a i hg hJ hl hp ha J hJmem
  line567a_calls i hg hJ hl hp ha := by
    refine le_trans (line567a_calls ch.line567a i hg hJ hl hp ha) ?_
    rw [sec15RoundCost]
    omega
  line4cd_group i hg hJ hl hp ht hs := line4cd_group ch.line4cd i hg hJ hl hp ht hs
  line56a7a_group i hg hJ hl hp ha := line56a7a_group ch.line56a7a i hg hJ hl hp ha
  line567a_group i hg hJ hl hp ha := line567a_group ch.line567a i hg hJ hl hp ha

/-- **Theorem 1.1.1** (Sec. 1.1), the mathematical half, for the Master Algorithm of Sec. 15
with every one of its seven lines carried out.

Procedure String-Isomorphism, run with the round `Babai.sec15Remaining`, returns
`Iso_G(x,y)` and generates at most `exp(30 (log₂ n + 2)^{c₁+2})` String Isomorphism
instances.

Two remarks on the form.

* The multiplicative cost `(q, c)` of Theorem 9.2.3 is a parameter here (`hq`, and
  `Babai.Theorem923Uniform` where the choices are produced).  Theorem 9.2.3 is proved
  (`Babai.theorem_9_2_3`), and `Babai.Theorem_1_1_1_math` is this lemma at the pair it gives.
* What is counted is the number of String Isomorphism instances, not the running time.  The
  running time is `Algo.theorem_1_1_1`, on the RAM model of `Workspace/Machine/`. -/
theorem Theorem_1_1_1_math_of_sec15 {q : ℕ → ℕ} {c : ℕ}
    (hq : RAM.QuasiPolyBound q) (ch : Sec15Choices Ω A q c) (G : Subgroup (Equiv.Perm Ω))
    (x y : Ω → A) :
    ∃ c₁ : ℕ,
      let M := (sec15Remaining (Ω := Ω) (A := A) ch).masterStep
      let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
      let i := M.top I
      let f := M.rank i + 1
      M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
        M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) := by
  obtain ⟨c₁, hc₁⟩ := quasiPolyBound_sec15RoundCost hq c
  exact ⟨c₁, Theorem_1_1_1_math_of_sec15Inputs
    (sec15Remaining (Ω := Ω) (A := A) ch).toSec15Inputs (sec15RoundCost_mono q c) c₁ hc₁
    G x y⟩

end Value

/-! ### Theorem 1.1.1 for every admissible witness of Theorem 9.2.3 -/

section Admissible

/-- Theorem 9.2.3 **with a larger multiplicative cost**: a family found at cost
`q(m)·m^{c·k}` is found at cost `q'(m)·m^{c·k}` for every `q' ≥ q`. -/
theorem Theorem923Uniform.mono {q q' : ℕ → ℕ} {c : ℕ} (h : Theorem923Uniform q c)
    (hq : ∀ n, q n ≤ q' n) : Theorem923Uniform q' c := by
  intro Γ _ _ k α h1 h2
  obtain ⟨D, E, F, G, hG, hcost, hgood⟩ := h Γ k α h1 h2
  exact ⟨D, E, F, G, hG, fun X => ⟨(hcost X).1, (hcost X).2.trans
    (Nat.mul_le_mul_right _ (hq _))⟩, hgood⟩

/-- **Theorem 1.1.1, mathematical half, for every admissible witness of Theorem 9.2.3.**
Any pair `(q, c)` with `q` quasipolynomial for which Theorem 9.2.3 holds at cost
`q(m)·m^{c·k}` (`Babai.Theorem923Uniform q c`) gives the conclusion of
`Babai.Theorem_1_1_1_math` for the Master Algorithm run with `Babai.Sec15Choices` at `(q, c)`.

`Babai.Theorem_1_1_1_math` is the instance at the pair `Babai.theorem_9_2_3` provides.  The
RAM needs another instance: the pair `(q923, c923)` is known only through upper bounds, so
nothing the machine computes can be shown to be counted by it, while a larger admissible
`q` (`Babai.Theorem923Uniform.mono`) can dominate the machine's own count.  Theorem 9.2.3
itself is unchanged; only the witness is. -/
theorem Theorem_1_1_1_math_of_admissible {q : ℕ → ℕ} {c : ℕ} (hq : RAM.QuasiPolyBound q)
    (hu : Theorem923Uniform q c) :
    ∃ c₁ : ℕ, ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v) [Fintype A]
      [DecidableEq A],
      Nonempty (Sec15Choices Ω A q c) ∧
      ∀ (ch : Sec15Choices Ω A q c) (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A),
      let M := (sec15Remaining (Ω := Ω) (A := A) ch).masterStep
      let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
      let i := M.top I
      let f := M.rank i + 1
      M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
        M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) := by
  obtain ⟨c₁, hc₁⟩ := quasiPolyBound_sec15RoundCost hq c
  refine ⟨c₁, fun Ω _ _ A _ _ => ⟨⟨sec15Choices hu⟩, fun ch G x y => ?_⟩⟩
  exact Theorem_1_1_1_math_of_sec15Inputs
    (sec15Remaining (Ω := Ω) (A := A) ch).toSec15Inputs
    (sec15RoundCost_mono q c) c₁ hc₁ G x y

end Admissible

/-! ### Theorem 1.1.1 with the constants of Theorem 9.2.3 discharged -/

section Top

open scoped Classical

/-- The multiplicative cost `q` of Theorem 9.2.3, chosen once. -/
noncomputable def q923 : ℕ → ℕ := theorem_9_2_3.choose

/-- The exponent `c` of `n^{O(k)}` in Theorem 9.2.3, chosen once. -/
noncomputable def c923 : ℕ := theorem_9_2_3.choose_spec.choose

theorem quasiPolyBound_q923 : RAM.QuasiPolyBound q923 :=
  theorem_9_2_3.choose_spec.choose_spec.1

/-- Theorem 9.2.3 in the uniform form Sec. 15 uses: one pair of absolute constants for every
ground set, every arity and every threshold. -/
theorem theorem923Uniform_q923 : Theorem923Uniform q923 c923 :=
  theorem_9_2_3.choose_spec.choose_spec.2

/-- §15, **the round of the Master Algorithm**, with the constants of Theorem 9.2.3 fixed
once and for all. -/
noncomputable def sec15MasterStep (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v)
    [Fintype A] [DecidableEq A] (ch : Sec15Choices Ω A q923 c923) :
    MasterStep Ω A (HintedInstance Ω A) :=
  (sec15Remaining (Ω := Ω) (A := A) ch).masterStep

/-- **Theorem 1.1.1** (Sec. 1.1, version 2.5, `quasi25.txt` line 1089):

> **Theorem 1.1.1.** *The String Isomorphism problem can be solved in quasipolynomial time.*

This is the **mathematical half** of that statement for the Master Algorithm of Sec. 15 with
every one of its seven lines carried out: Procedure String-Isomorphism, run with the round
`Babai.sec15Remaining`, returns `Iso_G(x,y)`, and the number of String Isomorphism instances
it generates — the size of the recursion tree, which is the number of rounds and of leaves —
is at most `exp(30 (log₂ n + 2)^{c₁+2})` for an absolute constant `c₁`.  The constant is
quantified **before** the ground set, the alphabet, the group and the two strings, so it is
one absolute constant and not a function of the input; it comes from the quasipolynomial
bound on `q` of Theorem 9.2.3 alone (`Babai.quasiPolyBound_sec15RoundCost`).

**For every choice.**  The statement holds for every `Babai.Sec15Choices`: line 1 may take
any branch of Procedure Reduce-to-Johnson that applies, with any data that branch runs on,
lines 4c–4d may run Procedure Align on any admissible geometric data, and lines 5–7 may
take any outcome of Theorem 13.2.1 that applies, with the data of that outcome.  What each
line then does with the data is a named reduction, not a choice.  The first half of the
conclusion says that there is at least one such choice (`Babai.sec15Choices`), so the
second half is not vacuous.

What the Lean statement does **not** cover is the **running time**: what is bounded here is
the number of instances the recursion generates, not the number of RAM steps.  The running
time is `Algo.theorem_1_1_1` (`Workspace/Algo/TopMasterClose.lean`), a statement about the
RAM of `Workspace/Machine/`.

**What it rests on.**  No `sorry`: outcome (2b) of Theorem 13.2.1 is proved
(`Babai.nonempty_line6aCase2bCore`, from `Babai.case2b_facts_on`), and so is the last case
of Sec. 9.7 (`Babai.case_9_7_case2_dom`).  `#print axioms Babai.Theorem_1_1_1_math` lists
`propext`, `Classical.choice`, `Quot.sound` and the four results cited from the literature
(`Babai.schreierHypothesis`, `Babai.degtrans_le_five`, `Babai.le_add_two_of_involved_GL`,
`Babai.Theorem_11_2_3`), and nothing else (Fact 10.2.2 (ii), `Babai.fact_10_2_2_ii`,
Theorem 10.2.4, `Babai.theorem_10_2_4`, and [DiM, Thms. 5.2A, 5.2B],
`Babai.dixonMortimer_5_2A` and `Babai.dixonMortimer_5_2B`, are proved).  The
algorithmic axiom `Babai.cameronStructure_polyTime` is not among them: it concerns running
time only.

`Babai.Theorem_1_1_1_math_of_sec15` is the lemma this follows from, with the constants of
Theorem 9.2.3 still hypotheses. -/
theorem Theorem_1_1_1_math :
    ∃ c₁ : ℕ, ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (A : Type v) [Fintype A]
      [DecidableEq A],
      Nonempty (Sec15Choices Ω A q923 c923) ∧
      ∀ (ch : Sec15Choices Ω A q923 c923) (G : Subgroup (Equiv.Perm Ω)) (x y : Ω → A),
      let M := sec15MasterStep Ω A ch
      let I : SIInstance Ω A := ⟨(G : Set (Equiv.Perm Ω)), Set.univ, x, y⟩
      let i := M.top I
      let f := M.rank i + 1
      M.solve f i = strIso (G : Set (Equiv.Perm Ω)) x y ∧
        M.count f i ≤ 2 ^ (30 * (Nat.log 2 I.windowSize + 2) ^ (c₁ + 2)) := by
  exact Theorem_1_1_1_math_of_admissible quasiPolyBound_q923 theorem923Uniform_q923

end Top

end Babai
