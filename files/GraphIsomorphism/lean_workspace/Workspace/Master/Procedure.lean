/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

Section 15: Procedure String-Isomorphism, the Master Algorithm.
-/
import Workspace.Master.Defs

/-!
# Procedure String-Isomorphism (Sec. 15)

> **Procedure String-Isomorphism**
> Input: group `G ≤ S(Ω)`, strings `x, y : Ω → Σ`
> Output: `Iso_G(x,y)`
> 1. Apply Procedure Reduce-to-Johnson (Luks reductions, Sec. 11.3)
> 2. (: `G` is transitive, `G`-action on blocks is a Johnson group isomorphic to `S_m` or
>    `A_m` :) set `ℓ = (log n)³`; if `m ≤ ℓ` then apply imprimitive Luks reduction to reduce
>    to the kernel of the `G`-action on the blocks (brute force on the small primitive group
>    `Ḡ`, multiplicative cost `ℓ!`)
> 3. Let `ϕ : G → S(Γ)` be a giant representation, `N = ker ϕ`, and
>    `Φ = {B_T | T ∈ Γ^{(t)}}` the set of standard blocks (Thm. 10.5.1)
> 4. if `G` primitive (: i.e. `Ω = Φ` :)
>    4a. if `t = 1` then find `Iso_G(x,y)`, exit (: isomorphism only depends on the
>        multiplicity of each letter :)
>    4b. else view `x, y` as edge-colored `t`-uniform hypergraphs; if the relative symmetry
>        defect of `H(x)` is `< 1/2` then apply Cor. 12.0.10
>    4c. else apply the Extended Design Lemma (Thm. 9.2.3)
>    4d. (: canonical structure `X` on `Γ` found :) apply Procedure Align to `X` (Sec. 14.1)
> 5. else (: `G` imprimitive :) apply AggregateCertificates (Thm. 13.2.1)
> 6. if AggregateCertificates returns a canonically embedded `k`-ary relational structure on
>    `Γ` with relative symmetry defect `≥ 1/2` then
>    6a. apply the Extended Design Lemma (Thm. 9.2.3); `X ←` the canonical structure returned
> 7. else `X ←` the colored equipartition returned
>    7a. apply Procedure Align to `X` (Sec. 14.1)

Each execution of lines 1–7a is **one round**: it turns the instance `I` into a list of
smaller String Isomorphism instances plus a rule for assembling `Iso_G(x,y)` from their
answers, i.e. a `Babai.SIReduction` (Sec. 11.1).  Sec. 15 then answers each of those
instances by starting over, which is `Babai.solveFuel`.

`Babai.MasterStep` is exactly the list of properties of one round that Sec. 15's analysis
uses, and nothing else:

* `step` — the round itself, and `round_correct`: it computes `Iso_G(x,y)` as soon as the
  instances it produces are answered correctly (lines 1–7a, each of which is a reduction
  already formalized or being formalized elsewhere in this development);
* `param` — the Johnson parameter `m` of line 2, with `param_le`;
* `decreases` — the two ways in which a round makes progress, from Secs. 11.4 and 14.2:
  either the window shrinks to `2n/3` (line 2: the kernel of the action on the blocks fixes
  every block, so its orbits have length at most `n/2`; lines 4b, 4c, 6a, 7a: Cor. 12.0.10,
  the Extended Design Lemma and Procedure Align produce windows of size at most `2n/3`), or
  the window does not grow and the Johnson parameter `m` is at least halved (Procedure Align
  lines 7–11 on the window of a dominant color class, Sec. 14.2 Eq. (73), which is the
  Johnson-to-Johnson recursion of Sec. 11.4 item (v));
* `roundCost` — the number of instances one round produces, which for line 2 is the
  multiplicative cost `ℓ!` and for lines 4c, 6a and case 2b of Thm. 13.2.1 is the
  multiplicative cost `q(m)` of Sec. 14.2 (`Workspace/Master/Bridge.lean`).

The properties are spelled out as fields, not hidden behind an opaque `Prop` variable.  They
are stated for the **true oracle** — about `SIReduction.run` and `SIReduction.calls` — which
is the form every input theorem of Secs. 11–14 has.  The program does not see the true
answers, but that costs nothing here: an oracle that is right on the instances a round asks
under the true oracle drives the decision tree along the same path, so it makes the same
calls and returns the same value (`Babai.SIReduction.callsWith_eq_calls_of_agree`), and
`Babai.MasterStep.solve_eq_answer` supplies exactly that agreement, one level at a time.
An earlier version of this interface asked for the three properties at an *arbitrary*
oracle; no input theorem of Secs. 12–14 is stated that way, and the extra generality is
never used.  See the Sec. 15 entry of the corrected paper.

Constructing a `MasterStep` from the named reductions of Secs. 11–14 needs Theorems 9.2.1–
9.2.3 and Theorem 13.2.1, which are still being formalized; see the Sec. 15 entry of
the corrected paper.
-/

universe u v w

namespace Babai

variable {Ω : Type u} {A : Type v} {ι : Type w}

/-! ### The two forms of progress

Sec. 11.4 gives two different recurrences, and a round of Sec. 15 satisfies one of them.

* **Recurrences (ii) and (v)** — the *shrinking* rounds.  Each instance the round produces
  has a window of at most `2n/3` (lines 2, 4b, 4c, 6a, 7a), or has a window that does not
  grow and a Johnson parameter at most `m/2` (Procedure Align lines 7–11, Eq. (73)).  The
  number of instances is the multiplicative cost of the round.
* **Recurrence (i)** — the *Chain Rule* round, which is step 3 of Procedure
  Reduce-to-Johnson (Sec. 11.3) at line 1.  Here the windows of the instances are the
  orbits of an intransitive group: each of them is strictly smaller than `n`, but they need
  not be smaller by a constant factor.  What holds instead is that they **partition** the
  window, so their sizes add up to at most `n`.  This is exactly the hypothesis of
  recurrence (i), *"the maximum is taken over all partitions of `⌊x⌋`"*.

The two are genuinely different, and the second is not a special case of the first: an
intransitive group can have orbits of sizes `n - 1` and `1`.

Both are stated for a type `ι` of instances carrying the structure lines 1–3 have found,
with `win` the window size and `param` the Johnson parameter of such an instance.  Sec. 14.2
measures a pair `(G, ϕ)`, not a group, which is why `param` is read on `ι` and not on the
bare String Isomorphism instance; see the corrected paper Procedure Align. -/

/-- §11.4, recurrences (ii) and (v): the progress one *shrinking* call makes.  Either the
window drops to `4n/5`, or it does not grow and the Johnson parameter is at least halved.

Sec. 14.2 Eq. (73) writes `2n/3` for the first alternative.  The constant here is `4/5`
instead.  The reason is the `t = 1` case of Eq. (72): a dominant color class of a colored
`α`-partition can be a single block, and then Lemma 7.2.1 (b) gives only
`|Ω(Δ)| ≤ α·n`, with `α = 4/5` the threshold of Theorem 13.2.1.  So `4/5` is what the
window alternative can promise at line 5, and `2/3` is not.  Recurrences (i), (ii) and (v)
of Sec. 11.4 resolve for any fixed constant below `1`, so only this constant moves; see
the corrected paper entry on Sec. 15 lines 5–7a and Sec. 14.2 Eqs. (72)–(73). -/
def MakesProgress (win param : ι → ℕ) (i j : ι) : Prop :=
  (1 ≤ win i ∧ 5 * win j ≤ 4 * win i) ∨
    (win j ≤ win i ∧ 1 ≤ param i ∧ 2 * param j ≤ param i)

/-- §11.4, recurrence (i): the round is a **Chain Rule** round.  Its instances have windows
that are strictly smaller than `n` and whose sizes add up to at most `n`, because they are
the parts of a partition of the window; and none of them has a larger Johnson parameter. -/
def IsChainRuleRound (win param : ι → ℕ) (i : ι) (calls : List ι) : Prop :=
  1 ≤ win i ∧
    (∀ j ∈ calls, win j < win i ∧ param j ≤ param i) ∧
    (calls.map win).sum ≤ win i

theorem win_le_of_makesProgress {win param : ι → ℕ} {i j : ι}
    (h : MakesProgress win param i j) : win j ≤ win i := by
  rcases h with ⟨-, h⟩ | ⟨h, -, -⟩
  · omega
  · exact h

/-- §15: one round of Procedure String-Isomorphism, together with the three properties its
analysis uses: correctness of the round, the progress it makes, and the number of instances
it produces.

The round runs on a type `ι` of **hinted** instances: an element of `ι` is a String
Isomorphism instance `inst i` together with whatever lines 1–3 have already found for it
(in `Workspace/Master/Sec15.lean` this is an optional `Babai.JohnsonCaseData`).  A round
attaches such a hint to each of its calls through `lift`, which is what Sec. 14.2 does when
it measures the pair `(G, ϕ)` and what line 11 of Procedure Align does when it hands `ϕ*`
down *"for recursive processing of the corresponding window"*.  The hint does not touch the
instance: `lift_inst` says `inst (lift i J) = J`. -/
structure MasterStep (Ω : Type u) (A : Type v) (ι : Type w) where
  /-- The String Isomorphism instance underneath a hinted instance. -/
  inst : ι → SIInstance Ω A
  /-- Lines 1–7a: the round, as a reduction of `Iso_G(x,y)` to smaller instances. -/
  step : ι → SIReduction Ω A (Set (Equiv.Perm Ω))
  /-- What the round attaches to each of its calls: the Johnson structure the call is to be
  processed with (line 11 of Procedure Align), or nothing. -/
  lift : ι → SIInstance Ω A → ι
  /-- The instance with no hint at all, which is what Theorem 1.1.1 starts from. -/
  top : SIInstance Ω A → ι
  /-- The top instance is the instance it is built from. -/
  inst_top : ∀ I : SIInstance Ω A, inst (top I) = I
  /-- A hint does not change the instance it is attached to. -/
  lift_inst : ∀ i : ι, ∀ J ∈ (step i).calls, inst (lift i J) = J
  /-- Line 2: the Johnson parameter `m` of the top action of the hinted instance. -/
  param : ι → ℕ
  /-- The number of instances one round produces, as a function of the window size `n`:
  the multiplicative cost of lines 2, 4c, 6a and of case 2b of Thm. 13.2.1. -/
  roundCost : ℕ → ℕ
  /-- In the Johnson case the Johnson parameter never exceeds the window size (`Γ` is a
  quotient of a subset of the window: `m ≤ |Φ| ≤ n`).  Outside the Johnson case there is no
  Johnson parameter, and the instance is given the value `2n`, which is the top of the
  second component of the measure: an instance that Procedure Reduce-to-Johnson has not
  processed yet costs as much as the worst Johnson case on the same window.  The bound
  `param I ≤ 2n` covers both. -/
  param_le : ∀ i : ι, param i ≤ 2 * (inst i).windowSize
  /-- The round turns a group instance into group instances (`Babai.IsGroupInstance`).
  This is what lets the three facts below be asked only of the instances the algorithm ever
  sees; see `Workspace/Master/DESIGN.md`, Decision 7. -/
  calls_isGroupInstance : ∀ i : ι, IsGroupInstance (inst i) →
      ∀ J ∈ (step i).calls, IsGroupInstance J
  /-- Lines 1–7a are correct: the round returns `Iso^Δ_K(x,y)` once its instances are
  answered.  The round is a decision tree, so this is stated for the true answers; that the
  program may run it against the answers of the level below changes nothing, because an
  oracle that is right on the instances the round asks drives the tree along the same path
  (`Babai.SIReduction.callsWith_eq_calls_of_agree`). -/
  round_correct : ∀ i : ι, IsGroupInstance (inst i) → (step i).run = (inst i).answer
  /-- §11.4: a round makes progress in one of the two ways of `Babai.MakesProgress` and
  `Babai.IsChainRuleRound` — recurrences (ii)/(v), or recurrence (i). -/
  decreases : ∀ i : ι, IsGroupInstance (inst i) →
      (∀ J ∈ (step i).calls,
        MakesProgress (fun j => (inst j).windowSize) param i (lift i J)) ∨
        IsChainRuleRound (fun j => (inst j).windowSize) param i
          ((step i).calls.map (lift i))
  /-- The number of instances one round produces. -/
  calls_length_le : ∀ i : ι, IsGroupInstance (inst i) →
      ((step i).calls).length ≤ roundCost (inst i).windowSize

/-! ### The measure

Sec. 11.4 measures progress by two quantities: the window size `n` and the Johnson
parameter `m`.  A shrinking round either shrinks `n` by the factor `4/5` or halves `m`
without growing `n`, so the pair drops lexicographically.  `Babai.johnsonRank` packs that
pair into a single natural number whose size is `O(log² n)`, which is what makes the
*shrinking* part of the recursion `O(log² n)` deep and the bound of Eq. (67)/(74)
quasipolynomial.

The first component is `log₂(2n⁴)` rather than `log₂ n`, because a factor `4/5` does not
halve `n` but does halve `n⁴` (from `5n' ≤ 4n` we get `625 n'⁴ ≤ 256 n⁴`, hence
`2 n'⁴ ≤ n⁴`).  The cube is not enough: `(4/5)³ = 64/125 > 1/2`, while
`(4/5)⁴ = 256/625 < 1/2`.
The second is `log₂(2m)`, which drops when `m` is halved, including when `m` drops to `0`.

A Chain Rule round (recurrence (i)) shrinks neither of the two: the windows of its
instances are only *strictly* smaller.  The measure that terminates the recursion is
therefore `Babai.MasterStep.rank`, the pair `(n, johnsonRank)` read lexicographically, with
the window size in front.  That measure is linear in `n` rather than `O(log² n)`, but it is
used only for termination; the *count* of instances is bounded in
`Workspace/Master/Cost.lean` by a superadditive function of the instance, which is how
recurrence (i) is paid for. -/

/-- A doubling drops nothing: if `2a ≤ b` and `a ≥ 1` then `log₂ a < log₂ b`. -/
theorem log_lt_log_of_two_mul_le {a b : ℕ} (ha : 1 ≤ a) (h : 2 * a ≤ b) :
    Nat.log 2 a < Nat.log 2 b := by
  have h1 : Nat.log 2 (a * 2) = Nat.log 2 a + 1 :=
    Nat.log_mul_base (by norm_num) (by omega)
  have h2 : Nat.log 2 (a * 2) ≤ Nat.log 2 b :=
    Nat.log_mono_right (by omega)
  omega

/-- The first component of the measure: `log₂(2n⁴)`, where `n` is the window size.

It is `n⁴` rather than `n` because a factor `4/5` does not halve `n` but does halve `n⁴`
(`Babai.two_mul_pow_four_le`), and `2n⁴` rather than `n⁴` so that the component still drops
when the window becomes empty. -/
def windowRank (n : ℕ) : ℕ := Nat.log 2 (2 * n ^ 4)

/-- The weight the first component is given: one more than the largest possible value of the
second component.  The second component is `log₂(2m)` with `m ≤ 2n`, so the largest value it
can take is `log₂(4n)`. -/
def windowWeight (n : ℕ) : ℕ := Nat.log 2 (4 * n) + 1

/-- From `5n' ≤ 4n` follows `2n'⁴ ≤ n⁴`: a factor `4/5` halves the fourth power.  The cube
would not do: `(4/5)³ = 64/125 > 1/2`. -/
theorem two_mul_pow_four_le (n' n : ℕ) (h : 5 * n' ≤ 4 * n) : 2 * n' ^ 4 ≤ n ^ 4 := by
  have hpow : 625 * n' ^ 4 ≤ 256 * n ^ 4 := by
    calc 625 * n' ^ 4 = (5 * n') ^ 4 := by ring
      _ ≤ (4 * n) ^ 4 := Nat.pow_le_pow_left h 4
      _ = 256 * n ^ 4 := by ring
  have h625 : 625 * (2 * n' ^ 4) ≤ 625 * n ^ 4 := by omega
  omega

/-- Lines 4b, 4c, 6a, 7a: the first component of the measure drops. -/
theorem windowRank_lt (n n' : ℕ) (hI : 1 ≤ n) (h : 5 * n' ≤ 4 * n) :
    windowRank n' < windowRank n := by
  have hpow : 2 * n' ^ 4 ≤ n ^ 4 := two_mul_pow_four_le _ _ h
  have h1 : (1 : ℕ) ≤ n ^ 4 := Nat.one_le_pow _ _ hI
  rcases Nat.eq_zero_or_pos n' with hJ | hJ
  · -- the call has an empty window, and `I` does not
    have hz : windowRank n' = 0 := by rw [windowRank, hJ]; simp
    rw [hz, windowRank]
    exact Nat.log_pos (by norm_num) (by omega)
  · have hpos : 1 ≤ 2 * n' ^ 4 := by
      have := Nat.one_le_pow 4 _ hJ; omega
    exact log_lt_log_of_two_mul_le hpos (by omega)

/-- The first component of the measure does not grow when the window does not grow. -/
theorem windowRank_le (n n' : ℕ) (h : n' ≤ n) : windowRank n' ≤ windowRank n :=
  Nat.log_mono_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 4))

theorem windowWeight_le (n n' : ℕ) (h : n' ≤ n) : windowWeight n' ≤ windowWeight n :=
  Nat.succ_le_succ (Nat.log_mono_right (Nat.mul_le_mul_left 4 h))

/-- Three is the least possible weight: `log₂(4n) ≥ 2` as soon as the window is nonempty. -/
theorem three_le_windowWeight (n : ℕ) (h : 1 ≤ n) : 3 ≤ windowWeight n := by
  have : Nat.log 2 4 ≤ Nat.log 2 (4 * n) := Nat.log_mono_right (by omega)
  have h4 : Nat.log 2 4 = 2 := by
    rw [show (4:ℕ) = 2^2 by norm_num, Nat.log_pow (by norm_num)]
  rw [windowWeight]; omega

/-- The first component is at least `1` as soon as the window is nonempty. -/
theorem one_le_windowRank (n : ℕ) (h : 1 ≤ n) : 1 ≤ windowRank n := by
  have h1 : (1 : ℕ) ≤ n ^ 4 := Nat.one_le_pow _ _ h
  exact Nat.log_pos (by norm_num) (by omega)

namespace MasterStep

variable (M : MasterStep Ω A ι)

/-- The window size of a hinted instance. -/
noncomputable def win (i : ι) : ℕ := (M.inst i).windowSize

/-- §15, **Procedure String-Isomorphism**: repeat the round, answering each instance it
produces by starting over with the hint the round attaches to it.  The fuel `f` bounds the
depth of the recursion; `Babai.MasterStep.solve_eq_answer` says how much fuel is enough. -/
def solve (f : ℕ) (i : ι) : Set (Equiv.Perm Ω) := solveFuel M.step M.lift f i

/-- The number of String Isomorphism instances the whole recursion generates. -/
def count (f : ℕ) (i : ι) : ℕ := countCalls M.step M.lift f i

/-- The second component of the measure: `log₂(2m)`, where `m` is the Johnson parameter. -/
def rank2 (i : ι) : ℕ := Nat.log 2 (2 * M.param i)

/-- The measure of a *shrinking* round: the pair `(n, m)` in lexicographic order, packed
into a natural number.  It is `O(log² n)` (`Babai.MasterStep.johnsonRank_le`), which is the
exponent `log² n` of Eq. (74). -/
noncomputable def johnsonRank (i : ι) : ℕ :=
  windowRank (M.win i) * windowWeight (M.win i) + M.rank2 i

theorem decreases' (i : ι) (hi : IsGroupInstance (M.inst i)) :
    (∀ J ∈ (M.step i).calls, MakesProgress M.win M.param i (M.lift i J)) ∨
      IsChainRuleRound M.win M.param i ((M.step i).calls.map (M.lift i)) := M.decreases i hi

theorem rank2_lt_windowWeight (i : ι) : M.rank2 i < windowWeight (M.win i) := by
  refine Nat.lt_succ_of_le (Nat.log_mono_right ?_)
  have := M.param_le i
  show 2 * M.param i ≤ 4 * M.win i
  rw [win]
  omega

theorem rank2_le (i j : ι) (h : M.param j ≤ M.param i) : M.rank2 j ≤ M.rank2 i :=
  Nat.log_mono_right (Nat.mul_le_mul_left 2 h)

/-- Sec. 14.2 Eq. (73) and Sec. 11.4 item (v): the second component of the measure drops when
the Johnson parameter is at least halved. -/
theorem rank2_lt (i j : ι) (hm : 1 ≤ M.param i) (h : 2 * M.param j ≤ M.param i) :
    M.rank2 j < M.rank2 i := by
  rcases Nat.eq_zero_or_pos (M.param j) with hJ | hJ
  · have hz : M.rank2 j = 0 := by rw [rank2, hJ]; simp
    rw [hz, rank2]
    exact Nat.log_pos (by norm_num) (by omega)
  · exact log_lt_log_of_two_mul_le (by omega) (by omega)

/-- §11.4, recurrences (ii) and (v): **the Johnson measure drops** at a shrinking call.  In
the first case the window shrinks by the factor `4/5`, in the second the Johnson parameter
is halved while the window does not grow. -/
theorem johnsonRank_lt (i j : ι) (h : MakesProgress M.win M.param i j) :
    M.johnsonRank j < M.johnsonRank i := by
  rcases h with ⟨hI, h⟩ | ⟨hle, hm, h⟩
  · have h1 : windowRank (M.win j) < windowRank (M.win i) := windowRank_lt _ _ hI h
    have hw : windowWeight (M.win j) ≤ windowWeight (M.win i) :=
      windowWeight_le _ _ (by omega)
    have h2 : M.rank2 j < windowWeight (M.win i) :=
      lt_of_lt_of_le (M.rank2_lt_windowWeight j) hw
    have hmul : windowRank (M.win j) * windowWeight (M.win j) + windowWeight (M.win i)
        ≤ windowRank (M.win i) * windowWeight (M.win i) := by
      calc windowRank (M.win j) * windowWeight (M.win j) + windowWeight (M.win i)
          ≤ windowRank (M.win j) * windowWeight (M.win i) + windowWeight (M.win i) :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hw) _
        _ = (windowRank (M.win j) + 1) * windowWeight (M.win i) := by ring
        _ ≤ windowRank (M.win i) * windowWeight (M.win i) := Nat.mul_le_mul_right _ h1
    rw [johnsonRank, johnsonRank]
    omega
  · have h1 : windowRank (M.win j) ≤ windowRank (M.win i) := windowRank_le _ _ hle
    have hw : windowWeight (M.win j) ≤ windowWeight (M.win i) := windowWeight_le _ _ hle
    have h2 : M.rank2 j < M.rank2 i := M.rank2_lt i j hm h
    have hmul : windowRank (M.win j) * windowWeight (M.win j)
        ≤ windowRank (M.win i) * windowWeight (M.win i) := Nat.mul_le_mul h1 hw
    rw [johnsonRank, johnsonRank]
    omega

/-- §11.4, recurrence (i): **the Johnson measure does not grow** at a Chain Rule call.  The
window does not grow and neither does the Johnson parameter, and both components of
`johnsonRank` are monotone in those two quantities. -/
theorem johnsonRank_le (i j : ι) (hn : M.win j ≤ M.win i) (hp : M.param j ≤ M.param i) :
    M.johnsonRank j ≤ M.johnsonRank i := by
  have h1 : windowRank (M.win j) ≤ windowRank (M.win i) := windowRank_le _ _ hn
  have hw : windowWeight (M.win j) ≤ windowWeight (M.win i) := windowWeight_le _ _ hn
  have h2 : M.rank2 j ≤ M.rank2 i := M.rank2_le i j hp
  have hmul : windowRank (M.win j) * windowWeight (M.win j)
      ≤ windowRank (M.win i) * windowWeight (M.win i) := Nat.mul_le_mul h1 hw
  rw [johnsonRank, johnsonRank]
  omega

/-- The Johnson measure of an instance with a nonempty window is at least `3`: the window
component is at least `1` and its weight at least `3`. -/
theorem three_le_johnsonRank (i : ι) (h : 1 ≤ M.win i) : 3 ≤ M.johnsonRank i := by
  have h1 : 1 ≤ windowRank (M.win i) := one_le_windowRank _ h
  have h2 : 3 ≤ windowWeight (M.win i) := three_le_windowWeight _ h
  have : 1 * 3 ≤ windowRank (M.win i) * windowWeight (M.win i) := Nat.mul_le_mul h1 h2
  rw [johnsonRank]
  omega

/-! #### The Johnson measure is `O(log² n)` -/

end MasterStep

theorem windowRank_le_log (n : ℕ) : windowRank n ≤ 4 * (Nat.log 2 n + 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [windowRank, h0]; simp
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have key : (2 : ℕ) * (2 ^ (Nat.log 2 n + 1)) ^ 4 = 2 ^ (4 * Nat.log 2 n + 5) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      ring
    have hcube : 2 * n ^ 4 < 2 ^ (4 * Nat.log 2 n + 5) := by
      have h3 : n ^ 4 < (2 ^ (Nat.log 2 n + 1)) ^ 4 :=
        Nat.pow_lt_pow_left hlt (by norm_num)
      omega
    have hne : 2 * n ^ 4 ≠ 0 :=
      Nat.mul_ne_zero two_ne_zero (pow_ne_zero 4 (by omega))
    have := Nat.log_lt_of_lt_pow hne hcube
    rw [windowRank]
    omega

theorem windowWeight_le_log (n : ℕ) : windowWeight n ≤ Nat.log 2 n + 3 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [windowWeight, h0]; simp
  · have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have key : (4 : ℕ) * 2 ^ (Nat.log 2 n + 1) = 2 ^ (Nat.log 2 n + 3) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have h2 : 4 * n < 2 ^ (Nat.log 2 n + 3) := by omega
    have hne : 4 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) (by omega)
    have := Nat.log_lt_of_lt_pow hne h2
    rw [windowWeight]
    omega

namespace MasterStep

variable (M : MasterStep Ω A ι)

/-- The bound on the Johnson measure, as a function of the window size alone. -/
def rankBound (n : ℕ) : ℕ := 14 * (Nat.log 2 n + 1) ^ 2

theorem rankBound_mono : Monotone rankBound := by
  intro a b hab
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
    exact Nat.succ_le_succ (Nat.log_mono_right hab)) 2)

/-- §11.4: the Johnson measure is `O(log² n)`.  This is where the exponent `log² n` of
Eq. (74) comes from: one factor `log n` from the window shrinking by `4/5` at a time, one
from the Johnson parameter halving. -/
theorem johnsonRank_le_rankBound (i : ι) : M.johnsonRank i ≤ rankBound (M.win i) := by
  set L := Nat.log 2 (M.win i) + 1 with hL
  have h1 : windowRank (M.win i) ≤ 4 * L := windowRank_le_log _
  have h2 : windowWeight (M.win i) ≤ L + 2 := by have := windowWeight_le_log (M.win i); omega
  have h3 : M.rank2 i < windowWeight (M.win i) := M.rank2_lt_windowWeight i
  have hL1 : 1 ≤ L := by omega
  have hprod : windowRank (M.win i) * windowWeight (M.win i) ≤ (4 * L) * (L + 2) :=
    Nat.mul_le_mul h1 h2
  have hsq : (4 * L) * (L + 2) + (L + 1) ≤ 14 * L ^ 2 := by nlinarith
  rw [johnsonRank, rankBound, ← hL]
  omega

/-! #### The termination measure -/

/-- **The measure of the recursion**: the pair `(n, johnsonRank)` in lexicographic order,
packed into a natural number.  The window size comes first because a Chain Rule round
(recurrence (i)) shrinks only the window, and the Johnson measure comes second because a
shrinking round (recurrences (ii), (v)) may keep the window. -/
noncomputable def rank (i : ι) : ℕ :=
  M.win i * (1 + rankBound (M.win i)) + M.johnsonRank i

/-- The measure drops whenever the window shrinks strictly, or the window does not grow and
the Johnson measure drops. -/
theorem rank_lt_of (i j : ι) (hn : M.win j ≤ M.win i)
    (h : M.win j < M.win i ∨ M.johnsonRank j < M.johnsonRank i) :
    M.rank j < M.rank i := by
  rcases h with hlt | hjr
  · -- the window drops: the whole second component is absorbed by one unit of the first
    have hb : rankBound (M.win j) ≤ rankBound (M.win i) := rankBound_mono hn
    have hjr : M.johnsonRank j ≤ rankBound (M.win j) := M.johnsonRank_le_rankBound j
    have hstep : (M.win j + 1) * (1 + rankBound (M.win i))
        ≤ M.win i * (1 + rankBound (M.win i)) :=
      Nat.mul_le_mul_right _ (by omega)
    have hexp : (M.win j + 1) * (1 + rankBound (M.win i))
        = M.win j * (1 + rankBound (M.win i)) + 1 + rankBound (M.win i) := by
      ring
    have hmono : M.win j * (1 + rankBound (M.win j))
        ≤ M.win j * (1 + rankBound (M.win i)) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [rank, rank]
    omega
  · have hmono : M.win j * (1 + rankBound (M.win j))
        ≤ M.win i * (1 + rankBound (M.win i)) :=
      Nat.mul_le_mul hn (by have := rankBound_mono hn; omega)
    rw [rank, rank]
    omega

/-- **The measure decreases**: every instance produced by a round has smaller measure than
the instance the round was applied to.  This is the content of `decreases`: a shrinking
round drops the Johnson measure without growing the window, a Chain Rule round drops the
window. -/
theorem rank_lt (i : ι) (hi : IsGroupInstance (M.inst i)) (J : SIInstance Ω A)
    (hJ : J ∈ (M.step i).calls) : M.rank (M.lift i J) < M.rank i := by
  rcases M.decreases' i hi with hsh | ⟨-, hcalls, -⟩
  · have h := hsh J hJ
    exact M.rank_lt_of i _ (win_le_of_makesProgress h) (Or.inr (M.johnsonRank_lt i _ h))
  · obtain ⟨hlt, -⟩ := hcalls (M.lift i J) (List.mem_map_of_mem hJ)
    exact M.rank_lt_of i _ (le_of_lt hlt) (Or.inl hlt)

end MasterStep

end Babai
