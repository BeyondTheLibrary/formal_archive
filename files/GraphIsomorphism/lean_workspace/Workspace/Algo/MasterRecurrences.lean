/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Eqs. (71)–(74) of Sec. 14.2 on the recursion tree of the Master.
-/
import Workspace.Algo.TopMasterRecursion

/-!
# Eqs. (71)–(74) on the recursion tree of the Master Algorithm

> Let `T(G, ϕ)` be the maximum cost over all input strings for the pair `(G, ϕ)`. … So
> `T_Jh(x, y)` is the maximum of `T(G, ϕ)` over all `G` and `ϕ` with the parameters `n ≤ x`
> and `m ≤ y`. … `T(x)` is the upper bound for all groups `G` of degree `n ≤ x`. …
> `T(G,ϕ) ≤ q(m) ∑_i T(|Ω_i|)` (71)
> If `(∀i)(|Ω_i| ≤ 2n/3)` then this yields (generously) the inequality
> `T(G,ϕ) ≤ m · q(m) T(2n/3)` (72) …
> So in each case we obtain the inequality `T(G,ϕ) ≤ q(m)(T(n/3) + T_Jh(n, m/2))` (73)
> justifying Eq. (v) in Sec. 11.4 and yielding the conclusion `T(n) ≤ q(n)^{O(log² n)}` (74).
> (§14.2)

**The cost function.**  The Master Algorithm runs on the RAM as the evaluator of a round `R`
(`Algo.siWorkspaceRoutine_of_masterRecursion`, which is how `Algo.theorem_1_1_1` is proved):
a depth-first walk of the recursion tree, one DFS step at a time (`Algo.Round.stepDFS`, a
quasipolynomial-time routine, `Algo.Round.quasiFun_stepDFS`).  The walk of the subtree of a
node takes at most `3·(number of nodes) + 1` DFS steps (`Algo.Round.subSteps_le`).  So the
cost of a node is measured, as in Sec. 14.2, by the number `R.nodes f I` of instances in its
recursion tree:

* `Algo.Round.costAt` — `T(G, ϕ)` for the node `I` (its group, representation, strings);
* `Algo.Round.costT` — `T(x)`: the maximum of the cost over the nodes of window size `≤ x`;
* `Algo.Round.costTJh` — `T_Jh(x, y)`: the same with the Johnson parameter `≤ y` as well.

**The recurrences**, for the rounds of `Algo.RoundProgress` (every round of the Master
satisfies it, `Algo.MasterRecursion.progress`):

* `Algo.Round.eq_71` — Eq. (71): the cost of a node is at most the sum, over its calls, of
  one plus the cost at the call's window.  The calls of a round of Procedure Align are the
  pairs (version of `X(y)`, color class `Ω_i`), so this sum is the paper's `q(m) ∑_i`;
* `Algo.Round.eq_72` — Eq. (72): if every call has window `≤ 4n/5` then the cost is at most
  `q(n)·(1 + T(4n/5))`;
* `Algo.Round.eq_73` — Eq. (73): if every call either shrinks the window to `≤ 4n/5` or keeps
  the window and halves the Johnson parameter, the cost is at most
  `q(n)·(1 + T(4n/5) + T_Jh(n, m/2))`;
* `Algo.Round.eq_chainRule` — recurrence (i) of Sec. 11.4, the Chain Rule rounds that (71)
  is built from: windows that are strictly smaller and add up to at most `n`;
* `Algo.Round.eq_74` — Eq. (74): `T(n) ≤ n²·(q(n)+1)^{14 (log₂ n + 1)²}`, which is
  `q(n)^{O(log² n)}`, and `≤ 2^{30 (log₂ n + 2)^{c₁+2}}` when `q(n) ≤ 2^{(log₂ n + 2)^{c₁}}`.

The thresholds `4/5` for `2/3` and `n/3` are the repair of entry 96 of the corrected paper: the
progress the Master's rounds record is the window alternative `5n' ≤ 4n` of
`Babai.MakesProgress` (a dominant color class of Theorem 13.2.1's `4/5`-partition gives no
better for `t = 1`).  The number of calls `q(n)` of one round is the paper's multiplicative
cost `q(m)` times the number of color classes that (72) bounds by `m`; the formal bound counts
the calls directly, so no superadditivity of `T` is needed.

**The link to the RAM cost of the Master** (`Algo.Round.master_ram_link`): at a node of the
Master, the evaluator has the answer after `3·T(G, ϕ) + 1` DFS steps, and by Eq. (74) this is
at most the number `Algo.Round.roundCount c₁ n` of DFS steps the RAM program of
`Algo.theorem_1_1_1` runs.

No axiom, no `sorry`, no `native_decide`.
-/

universe u v

namespace Algo

open Babai RAM

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

namespace Round

variable (R : Round ι ω α) (Good : ι → Prop) (win param : ι → ℕ)

/-- `T(G, ϕ)` for the node `I`: the number of instances in the recursion tree below `I`
(`f` is the fuel of the recursion, larger than the measure of `I`). -/
def costAt (f : ℕ) (I : ι) : ℕ := R.nodes f I

/-- The costs of the nodes of window size `≤ x` and Johnson parameter `≤ y`. -/
def costSet (f x y : ℕ) : Set ℕ :=
  {k | ∃ I, Good I ∧ R.WF I ∧ R.measure I < f ∧ win I ≤ x ∧ param I ≤ y ∧ R.nodes f I = k}

/-- **`T_Jh(x, y)`** (§11.4, §14.2): the maximum cost over the nodes with window size
`n ≤ x` and Johnson parameter `m ≤ y`. -/
noncomputable def costTJh (f x y : ℕ) : ℕ := sSup (R.costSet Good win param f x y)

/-- **`T(x)`** (§14.2): the maximum cost over the nodes of window size `n ≤ x` (the Johnson
parameter is at most `2n`, `Algo.RoundProgress.param_le`). -/
noncomputable def costT (f x : ℕ) : ℕ := R.costTJh Good win param f x (2 * x)

variable {R Good win param} {Ch : ι → ι → Prop} {decI : ι → SIInstance Ω A}
  {decA : ι → α → Set (Equiv.Perm Ω)} {ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))}
  {q : ℕ → ℕ}

section Recurrences

variable (himpl : ImplementsG R Good Ch decI decA ρ)
  (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
  (hP : RoundProgress R Good Ch decI ρ win param q) (hmono : Monotone q)
include himpl hρ hP hmono

/-- The costs of the nodes of window size `≤ x` are bounded. -/
theorem costSet_le (f x y : ℕ) :
    ∀ k ∈ R.costSet Good win param f x y, k ≤ x ^ 2 * (q x + 1) ^ MasterStep.rankBound x := by
  rintro k ⟨I, hG, hI, hf, hx, -, rfl⟩
  have h1 := R.nodes_le_costBoundG himpl hρ hP hmono x f I hG hI hf hx
  have h2 : johnsonRankOf (win I) (param I) ≤ MasterStep.rankBound x :=
    (johnsonRankOf_le_rankBound (hP.param_le I hG hI)).trans (MasterStep.rankBound_mono hx)
  exact h1.trans (Nat.mul_le_mul (Nat.pow_le_pow_left hx 2)
    (Nat.pow_le_pow_right (by omega) h2))

theorem bddAbove_costSet (f x y : ℕ) : BddAbove (R.costSet Good win param f x y) :=
  ⟨_, R.costSet_le himpl hρ hP hmono f x y⟩

/-- The cost of a node is at most `T_Jh` at its window and parameter. -/
theorem costAt_le_costTJh {f x y : ℕ} {I : ι} (hG : Good I) (hI : R.WF I)
    (hf : R.measure I < f) (hx : win I ≤ x) (hy : param I ≤ y) :
    R.costAt f I ≤ R.costTJh Good win param f x y :=
  le_csSup (R.bddAbove_costSet himpl hρ hP hmono f x y) ⟨I, hG, hI, hf, hx, hy, rfl⟩

/-- The cost of a node is at most `T` at its window. -/
theorem costAt_le_costT {f x : ℕ} {I : ι} (hG : Good I) (hI : R.WF I)
    (hf : R.measure I < f) (hx : win I ≤ x) :
    R.costAt f I ≤ R.costT Good win param f x :=
  R.costAt_le_costTJh himpl hρ hP hmono hG hI hf hx
    ((hP.param_le I hG hI).trans (Nat.mul_le_mul_left 2 hx))

/-- The calls of a node are good, well formed, of smaller measure, and children. -/
theorem roundCalls_facts {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I)
    (hf : R.measure I < f + 1) :
    ∀ J ∈ R.roundCalls f I, Good J ∧ R.WF J ∧ R.measure J < f ∧ Ch I J := by
  obtain ⟨-, hch⟩ := roundCalls_eqG R himpl hP.good_child hρ f I hG hI hf
  intro J hJ
  obtain ⟨hw, hm⟩ := R.mem_roundCalls hI J hJ
  exact ⟨hP.good_child I J (hch J hJ), hw, by omega, hch J hJ⟩

/-- A node makes at most `q(n)` calls (the multiplicative cost of the round). -/
theorem length_roundCalls_le {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I)
    (hf : R.measure I < f + 1) : (R.roundCalls f I).length ≤ q (win I) := by
  obtain ⟨hmap, -⟩ := roundCalls_eqG R himpl hP.good_child hρ f I hG hI hf
  have h := hP.length_le I hG hI
  rw [← hmap, List.length_map] at h
  exact h

/-- **Eq. (71)** (§14.2) on the recursion tree: the cost of a node is the number of its
calls plus their costs, so at most the sum over its calls of one plus `T` at the call's
window; and there are at most `q(n)` calls.  The calls of a round of Procedure Align are the
pairs (version of `X(y)`, color class `Ω_i`), so the sum is the paper's
`q(m) ∑_i T(|Ω_i|)`. -/
theorem eq_71 {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I) (hf : R.measure I < f + 1) :
    R.costAt (f + 1) I = (R.roundCalls f I).length
        + ((R.roundCalls f I).map (R.costAt f)).sum ∧
      R.costAt (f + 1) I
        ≤ ((R.roundCalls f I).map (fun J => 1 + R.costT Good win param f (win J))).sum ∧
      (R.roundCalls f I).length ≤ q (win I) := by
  refine ⟨R.nodes_succ f I, ?_, R.length_roundCalls_le himpl hρ hP hmono hG hI hf⟩
  rw [costAt, R.nodes_succ]
  have hfacts := R.roundCalls_facts himpl hρ hP hmono hG hI hf
  have key : ∀ L : List ι, (∀ J ∈ L, Good J ∧ R.WF J ∧ R.measure J < f ∧ Ch I J) →
      L.length + (L.map (R.nodes f)).sum
        ≤ (L.map (fun J => 1 + R.costT Good win param f (win J))).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons J t ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := ih (fun K hK => hL K (List.mem_cons_of_mem _ hK))
      obtain ⟨hGJ, hWJ, hfJ, -⟩ := hL J List.mem_cons_self
      have h2 : R.nodes f J ≤ R.costT Good win param f (win J) :=
        R.costAt_le_costT himpl hρ hP hmono hGJ hWJ hfJ le_rfl
      omega
  exact key _ hfacts

omit himpl hρ hP hmono in
/-- A sum over at most `q` calls of terms at most `B`. -/
theorem sum_le_of_length_le {L : List ι} {g : ι → ℕ} {B Q : ℕ} (hL : L.length ≤ Q)
    (hg : ∀ J ∈ L, g J ≤ B) : (L.map g).sum ≤ Q * B := by
  have h := List.sum_le_card_nsmul (L.map g) B
    (by intro v hv; obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hv; exact hg J hJ)
  rw [List.length_map, smul_eq_mul] at h
  exact h.trans (Nat.mul_le_mul_right _ hL)

/-- **Eq. (72)** (§14.2) on the recursion tree, at the threshold `4/5` (entry 96 of
the corrected paper): if every call has window at most `4n/5`, the cost is at most
`q(n)·(1 + T(4n/5))`.  (The paper's `m · q(m) T(2n/3)`: the factor `m` bounds the number of
color classes, which `q(n)` counts here.) -/
theorem eq_72 {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I) (hf : R.measure I < f + 1)
    (hsmall : ∀ J ∈ R.roundCalls f I, 5 * win J ≤ 4 * win I) :
    R.costAt (f + 1) I ≤ q (win I) * (1 + R.costT Good win param f (4 * win I / 5)) := by
  obtain ⟨-, h71, hlen⟩ := R.eq_71 himpl hρ hP hmono hG hI hf
  refine h71.trans (sum_le_of_length_le hlen fun J hJ => ?_)
  obtain ⟨hGJ, hWJ, hfJ, -⟩ := R.roundCalls_facts himpl hρ hP hmono hG hI hf J hJ
  have hw : win J ≤ 4 * win I / 5 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by
    have := hsmall J hJ; omega)
  have h1 : R.costT Good win param f (win J) ≤ R.costT Good win param f (4 * win I / 5) := by
    -- every node counted at `win J` is counted at `4n/5`
    apply csSup_le_csSup (R.bddAbove_costSet himpl hρ hP hmono f _ _)
    · exact ⟨R.nodes f J, J, hGJ, hWJ, hfJ, le_rfl, hP.param_le J hGJ hWJ, rfl⟩
    · rintro k ⟨K, hGK, hWK, hfK, hxK, hyK, rfl⟩
      exact ⟨K, hGK, hWK, hfK, hxK.trans hw, hP.param_le K hGK hWK |>.trans
        (Nat.mul_le_mul_left 2 (hxK.trans hw)), rfl⟩
  omega

/-- **Eq. (73)** (§14.2) on the recursion tree: if every call makes progress — its window is
at most `4n/5`, or its window is at most `n` and its Johnson parameter at most `m/2` (the
reduced `Γ*` of lines 7–11 of Procedure Align, Eq. (73)'s `m/2`) — then the cost is at most
`q(n)·(1 + T(4n/5) + T_Jh(n, m/2))`.  The threshold `4/5` in place of `n/3` is entry 96 of
the corrected paper. -/
theorem eq_73 {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I) (hf : R.measure I < f + 1)
    (hprog : ∀ J ∈ R.roundCalls f I, MakesProgress win param I J) :
    R.costAt (f + 1) I ≤ q (win I) * (1 + R.costT Good win param f (4 * win I / 5)
      + R.costTJh Good win param f (win I) (param I / 2)) := by
  rw [costAt, R.nodes_succ]
  have hlen := R.length_roundCalls_le himpl hρ hP hmono hG hI hf
  have hsum : ((R.roundCalls f I).map (R.nodes f)).sum
      ≤ q (win I) * (R.costT Good win param f (4 * win I / 5)
        + R.costTJh Good win param f (win I) (param I / 2)) := by
    refine sum_le_of_length_le hlen fun J hJ => ?_
    obtain ⟨hGJ, hWJ, hfJ, -⟩ := R.roundCalls_facts himpl hρ hP hmono hG hI hf J hJ
    rcases hprog J hJ with ⟨-, h⟩ | ⟨h1, -, h2⟩
    · have hw : win J ≤ 4 * win I / 5 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
      have := R.costAt_le_costT himpl hρ hP hmono hGJ hWJ hfJ hw
      unfold costAt at this
      omega
    · have hp : param J ≤ param I / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
      have := R.costAt_le_costTJh himpl hρ hP hmono hGJ hWJ hfJ h1 hp
      unfold costAt at this
      omega
  have := Nat.mul_le_mul_right 1 hlen
  rw [Nat.mul_add, Nat.mul_add]
  rw [Nat.mul_add] at hsum
  omega

/-- **Recurrence (i) of Sec. 11.4** on the recursion tree, the Chain Rule rounds that Eq. (71)
sums over: the calls have strictly smaller windows, no larger Johnson parameter, and windows
adding up to at most `n`; the cost is at most the sum over the calls of one plus
`T_Jh(|Ω_i|, m)`. -/
theorem eq_chainRule {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I) (hf : R.measure I < f + 1)
    (hch : ∀ J ∈ R.roundCalls f I, win J < win I ∧ param J ≤ param I) :
    R.costAt (f + 1) I
      ≤ ((R.roundCalls f I).map
          (fun J => 1 + R.costTJh Good win param f (win J) (param I))).sum := by
  rw [costAt, R.nodes_succ]
  have hfacts := R.roundCalls_facts himpl hρ hP hmono hG hI hf
  have key : ∀ L : List ι, (∀ J ∈ L, Good J ∧ R.WF J ∧ R.measure J < f ∧ Ch I J) →
      (∀ J ∈ L, win J < win I ∧ param J ≤ param I) →
      L.length + (L.map (R.nodes f)).sum
        ≤ (L.map (fun J => 1 + R.costTJh Good win param f (win J) (param I))).sum := by
    intro L hL hL'
    induction L with
    | nil => simp
    | cons J t ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := ih (fun K hK => hL K (List.mem_cons_of_mem _ hK))
        (fun K hK => hL' K (List.mem_cons_of_mem _ hK))
      obtain ⟨hGJ, hWJ, hfJ, -⟩ := hL J List.mem_cons_self
      have h2 : R.nodes f J ≤ R.costTJh Good win param f (win J) (param I) :=
        R.costAt_le_costTJh himpl hρ hP hmono hGJ hWJ hfJ le_rfl (hL' J List.mem_cons_self).2
      omega
  exact key _ hfacts hch

/-- **Eq. (74)** (§14.2, and Eq. (67) of §11.4): `T(n) ≤ q(n)^{O(log² n)}`, explicitly
`T(n) ≤ n²·(q(n)+1)^{14 (log₂ n + 1)²}`. -/
theorem eq_74 (f n : ℕ) :
    R.costT Good win param f n ≤ n ^ 2 * (q n + 1) ^ MasterStep.rankBound n := by
  unfold costT costTJh
  rcases (R.costSet Good win param f n (2 * n)).eq_empty_or_nonempty with he | hne
  · rw [he, csSup_empty]; exact Nat.zero_le _
  · exact csSup_le hne (R.costSet_le himpl hρ hP hmono f n (2 * n))

/-- **Eq. (74)** with a quasipolynomial `q`: if `q(n) ≤ 2^{(log₂ n + 2)^{c₁}}` then
`T(n) ≤ 2^{30 (log₂ n + 2)^{c₁+2}}`. -/
theorem eq_74_quasi (c₁ : ℕ) (hq : ∀ n : ℕ, q n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁)) (f n : ℕ) :
    R.costT Good win param f n ≤ 2 ^ (30 * (Nat.log 2 n + 2) ^ (c₁ + 2)) := by
  unfold costT costTJh
  rcases (R.costSet Good win param f n (2 * n)).eq_empty_or_nonempty with he | hne
  · rw [he, csSup_empty]; exact Nat.zero_le _
  · refine csSup_le hne ?_
    rintro k ⟨I, hG, hI, hf, hx, -, rfl⟩
    exact (R.nodes_le_quasiPolyG himpl hρ hP hmono c₁ hq f I hG hI hf).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 30
        (Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) hx; omega) _)))

/-- **The link to the RAM cost of the Master.**  At a node of window size `n`, the evaluator
has the node's answer after any number `N ≥ 3·T(G, ϕ) + 1` of DFS steps; and by Eq. (74),
`3·T(n) + 1` is at most `Algo.Round.roundCount c₁ n`, the number of DFS steps the RAM program
of `Algo.theorem_1_1_1` runs (`Algo.Round.runQ`), each step a quasipolynomial-time routine
(`Algo.Round.quasiFun_stepDFS`). -/
theorem master_ram_link (c₁ : ℕ) (hq : ∀ n : ℕ, q n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    {f : ℕ} {I : ι} (hG : Good I) (hI : R.WF I) (hf : R.measure I < f) :
    (∀ N, 3 * R.costAt f I + 1 ≤ N → R.evaluate N I = some (R.value f I)) ∧
      3 * R.costAt f I + 1 ≤ 3 * R.costT Good win param f (win I) + 1 ∧
      3 * R.costT Good win param f (win I) + 1 ≤ roundCount c₁ (win I) := by
  refine ⟨fun N hN => R.evaluate_eq_value f N I hI hf ((R.subSteps_le f I).trans hN), ?_, ?_⟩
  · have := R.costAt_le_costT himpl hρ hP hmono hG hI hf le_rfl
    omega
  · have := R.eq_74_quasi himpl hρ hP hmono c₁ hq f (win I)
    unfold roundCount
    omega

end Recurrences

end Round

/-- **Eqs. (71)–(74) for the Master Algorithm.**  For the round `R` of the Master at degree
`n` (`Algo.MasterRecursion`, whose instances give `Algo.theorem_1_1_1` through
`Algo.siWorkspaceRoutine_of_masterRecursion`), every good node satisfies Eq. (71), and the
cost function satisfies Eq. (74) and covers the RAM step count. -/
theorem masterRecursion_eq_71_74 {ω : Type} {R : Round RawMasterSI ω RawCoset} {n : ℕ}
    (M : MasterRecursion R n) (c₁ : ℕ) (hq : ∀ m : ℕ, M.q m ≤ 2 ^ ((Nat.log 2 m + 2) ^ c₁))
    {f : ℕ} {P : RawMasterSI} (hG : M.Good P) (hW : R.WF P) (hf : R.measure P < f + 1) :
    R.costAt (f + 1) P
        ≤ ((R.roundCalls f P).map
            (fun J => 1 + R.costT M.Good masterWindowSize masterParameter f
              (masterWindowSize J))).sum ∧
      (R.roundCalls f P).length ≤ M.q (masterWindowSize P) ∧
      R.costT M.Good masterWindowSize masterParameter f (masterWindowSize P)
        ≤ 2 ^ (30 * (Nat.log 2 (masterWindowSize P) + 2) ^ (c₁ + 2)) := by
  obtain ⟨-, h71, hlen⟩ := R.eq_71 M.impl M.correct M.progress M.mono hG hW hf
  exact ⟨h71, hlen, R.eq_74_quasi M.impl M.correct M.progress M.mono c₁ hq f _⟩

end Algo
