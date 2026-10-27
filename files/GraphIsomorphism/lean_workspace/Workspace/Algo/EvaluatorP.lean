/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the evaluator of Sec. 15 without a lift.
-/
import Workspace.Algo.RoundN
import Workspace.Algo.EvaluatorQ

/-!
# The evaluator of Sec. 15 without a lift

`Algo.Round.runQ_eq_answerN` (`Workspace/Algo/EvaluatorN.lean`) asks for a
`Babai.MasterStep` on a type `κ` of typed nodes, and for the hypothesis `hlift`: the typed
node of every raw child is the lift, by the round of its parent, of the instance the child
decodes to.  At the master carrier this cannot hold.  The node works in the frame of its own
raw representative `g` of the coset (the representative of Remark 11.1.4, which the paper
lets be any element of the coset), so its calls depend on `g`, and `g` is raw data that the
typed instance does not determine; a typed node that keeps `g` cannot be recovered from the
parent and the child's instance when two siblings decode to the same instance.

This file removes `hlift`.  It asks for exactly what the recursion analysis of Sec. 11.4 and
Sec. 15 uses, at the raw nodes themselves:

* at every good node the fold of `R` walks a round `ρ I` of the paper, taken at the node's own
  representative, and every child it produces is good (`Algo.ImplementsG`);
* `ρ I` is correct: it returns `Iso^Δ_K(x,y)` of the decoded instance once its calls are
  answered;
* the progress of Sec. 11.4 (`Algo.RoundProgress`): at every good node, either every child
  makes the progress of recurrences (ii)/(v) (`Babai.MakesProgress`, read on the raw window
  size and the raw Johnson parameter), or the round is a Chain Rule round (recurrence (i));
  and the round has at most `q(n)` calls.

From these, correctness follows by induction on the measure of the round
(`Algo.roundValue_eqG`), and the number of nodes of the recursion tree is at most
`n² (q(n)+1)^{johnsonRank}` (`Algo.Round.nodes_le_costBoundG`), which is Sec. 11.4's
resolution of the recurrences, word for word `Babai.MasterStep.round_recurrence` with the
typed lift replaced by the raw child.  So the packaged routine answers every good node
(`Algo.Round.runQ_eq_answerG`).

"Good" is a predicate on raw nodes chosen by the user.  It is how raw nodes that are well
formed for the machine but carry no meaning (a junk hint, another degree) are kept out: the
hypotheses are asked only at good nodes, and the fold only reaches good children from a good
node.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

open Babai RAM

/-! ## The link relation with a condition on the children -/

/-- `Algo.LoopMatchN` in which every child the fold produces satisfies `C`. -/
inductive LoopMatchG (R : Round ι ω α) (C : ι → Prop) (decI : ι → SIInstance Ω A)
    (decA : ι → α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A (Set (Equiv.Perm Ω)) → Prop where
  /-- Both stop, with the same answer. -/
  | done (w j : ℕ) (s : ω) (a : Set (Equiv.Perm Ω)) (hc : R.child (I, j, s) = none)
      (ha : decA I (R.finish (I, s)) = a) : LoopMatchG R C decI decA I w j s (.done a)
  /-- Both ask the same instance, the child satisfies `C`, and the two continue to match for
  every raw answer that decodes to the true answer. -/
  | call (w j : ℕ) (s : ω) (J : ι)
      (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω)))
      (hc : R.child (I, j, s) = some J) (hC : C J)
      (hnext : ∀ a : α, decA J a = (decI J).answer →
        LoopMatchG R C decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer)) :
      LoopMatchG R C decI decA I (w + 1) j s (.call (decI J) k)

/-- **The raw round implements the family of rounds `ρ` at the good nodes**: at every good,
well-formed node `I`, the fold of `R` walks `ρ I`, and every child it produces is a child of
`I` in the sense of `Ch I`. -/
def ImplementsG (R : Round ι ω α) (Good : ι → Prop) (Ch : ι → ι → Prop)
    (decI : ι → SIInstance Ω A) (decA : ι → α → Set (Equiv.Perm Ω))
    (ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))) : Prop :=
  ∀ I : ι, Good I → R.WF I →
    LoopMatchG R (Ch I) decI decA I (R.width I) 0 (R.init I) (ρ I)

/-- A match without a condition on the children is a match with a condition that always
holds. -/
theorem loopMatchG_of_loopMatchN {R : Round ι ω α} {C : ι → Prop} {decI : ι → SIInstance Ω A}
    {decA : ι → α → Set (Equiv.Perm Ω)} {I : ι} {w j : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : LoopMatchN R decI decA I w j s T)
    (hC : ∀ j s J, R.child (I, j, s) = some J → C J) : LoopMatchG R C decI decA I w j s T := by
  induction h with
  | done w j s a hc ha => exact LoopMatchG.done w j s a hc ha
  | call w j s J k hc _ ih => exact LoopMatchG.call w j s J k hc (hC _ _ _ hc) fun a ha => ih a ha

/-- A weaker condition on the children: `Algo.LoopMatchG` is monotone in `C`. -/
theorem LoopMatchG.mono {R : Round ι ω α} {C C' : ι → Prop} {decI : ι → SIInstance Ω A}
    {decA : ι → α → Set (Equiv.Perm Ω)} {I : ι} {w j : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : LoopMatchG R C decI decA I w j s T)
    (hC : ∀ J, C J → C' J) : LoopMatchG R C' decI decA I w j s T := by
  induction h with
  | done w j s a hc ha => exact LoopMatchG.done w j s a hc ha
  | call w j s J k hc hJ _ ih => exact LoopMatchG.call w j s J k hc (hC J hJ) fun a ha => ih a ha

/-- **A match gives a match with a condition on the children, read on the calls.**  If every
call of the tree satisfies `V`, and every child the round produces whose decoded instance
satisfies `V` satisfies `C`, then the match carries `C`.  Only the children on the path of
the match are asked for: a fold state that the match does not reach needs no property. -/
theorem loopMatchG_of_loopMatch_onCalls {R : Round ι ω α} {C : ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)} {I : ι}
    (V : SIInstance Ω A → Prop)
    (hC : ∀ j s J, R.child (I, j, s) = some J → V (decI J) → C J) :
    ∀ {w j : ℕ} {s : ω} {T : SIReduction Ω A (Set (Equiv.Perm Ω))},
      LoopMatch R decI decA I w j s T → (∀ K ∈ T.calls, V K) →
        LoopMatchG R C decI (fun _ => decA) I w j s T := by
  intro w j s T h
  induction h with
  | done w j s a hc ha => exact fun _ => LoopMatchG.done w j s a hc ha
  | call w j s J k hc _ ih =>
    intro hV
    have hvJ : V (decI J) := hV _ (by simp [SIReduction.calls])
    refine LoopMatchG.call w j s J k hc (hC j s J hc hvJ) fun a ha => ih a ha fun K hK => ?_
    apply hV K
    simp only [SIReduction.calls_call, List.mem_cons]
    exact Or.inr hK

namespace Round

/-- **The fold computes what the tree computes**, and produces only children that satisfy
`C`.  `Algo.Round.loopAux_eqN` with the condition carried along. -/
theorem loopAux_eqG (R : Round ι ω α) {C : ι → Prop} {decI : ι → SIInstance Ω A}
    {decA : ι → α → Set (Equiv.Perm Ω)} {I : ι} {rec : ι → α} {Good : ι → Prop}
    (hgood : ∀ (j : ℕ) (s : ω) (J : ι), R.child (I, j, s) = some J → C J → Good J)
    (hrec : ∀ J, Good J → decA J (rec J) = (decI J).answer) :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatchG R C decI decA I w j s T →
        decA I (R.loopAux rec w I j s) = T.run ∧
          (R.loopCalls rec w I j s).map decI = T.calls ∧
            ∀ J ∈ R.loopCalls rec w I j s, C J := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    cases w with
    | zero => exact ⟨by simpa using ha, by simp, by simp⟩
    | succ w =>
      refine ⟨?_, ?_, ?_⟩
      · rw [R.loopAux_succ_none hc]; simpa using ha
      · rw [R.loopCalls_succ_none hc]; simp
      · rw [R.loopCalls_succ_none hc]; simp
  | call w j s J k hc hC hnext ih =>
    have hA : decA J (rec J) = (decI J).answer := hrec J (hgood j s J hc hC)
    obtain ⟨h1, h2, h3⟩ := ih (rec J) hA
    refine ⟨?_, ?_, ?_⟩
    · rw [R.loopAux_succ_some hc, h1, SIReduction.run_call]
    · rw [R.loopCalls_succ_some hc, List.map_cons, h2, SIReduction.calls_call]
    · rw [R.loopCalls_succ_some hc]
      intro J' hJ'
      rcases List.mem_cons.1 hJ' with rfl | hJ'
      · exact hC
      · exact h3 J' hJ'

end Round

section Value

variable (R : Round ι ω α) {Good : ι → Prop} {Ch : ι → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))}

/-- **The round computes the answer**, by induction on the measure, at every good node:
`Algo.roundValue_eqN` without a typed node. -/
theorem roundValue_eqG (himpl : ImplementsG R Good Ch decI decA ρ)
    (hch : ∀ I J, Ch I J → Good J)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer) :
    ∀ (f : ℕ) (I : ι), Good I → R.WF I → R.measure I < f →
      decA I (R.value f I) = (decI I).answer := by
  intro f
  induction f with
  | zero => intro I _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hG hI hf
    obtain ⟨h1, -, -⟩ :=
      R.loopAux_eqG (C := Ch I)
        (Good := fun J => Good J ∧ R.WF J ∧ R.measure J < R.measure I)
        (fun j s J hc hC => ⟨hch I J hC, R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
        (fun J hJ => ih J hJ.1 hJ.2.1 (lt_of_lt_of_le hJ.2.2 (Nat.lt_succ_iff.mp hf)))
        _ _ _ _ (himpl I hG hI)
    rw [R.value_succ, h1, hρ I hG hI]

/-- **The children of a good node are the calls of its round**, and each is a child in the
sense of `Ch`. -/
theorem roundCalls_eqG (himpl : ImplementsG R Good Ch decI decA ρ)
    (hch : ∀ I J, Ch I J → Good J)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (f : ℕ) (I : ι) (hG : Good I) (hI : R.WF I) (hf : R.measure I < f + 1) :
    (R.roundCalls f I).map decI = (ρ I).calls ∧ ∀ J ∈ R.roundCalls f I, Ch I J := by
  obtain ⟨-, h2, h3⟩ :=
    R.loopAux_eqG (rec := R.value f) (C := Ch I)
      (Good := fun J => Good J ∧ R.WF J ∧ R.measure J < R.measure I)
      (fun j s J hc hC => ⟨hch I J hC, R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
      (fun J hJ => roundValue_eqG R himpl hch hρ f J hJ.1 hJ.2.1
        (lt_of_lt_of_le hJ.2.2 (Nat.lt_succ_iff.mp hf)))
      _ _ _ _ (himpl I hG hI)
  exact ⟨h2, h3⟩

end Value

/-! ## The measure of Sec. 11.4, on numbers -/

/-- The Johnson measure `Babai.MasterStep.johnsonRank` of a node with window size `w` and
Johnson parameter `p`: the pair `(n, m)` of Sec. 11.4 packed into one number. -/
def johnsonRankOf (w p : ℕ) : ℕ := windowRank w * windowWeight w + Nat.log 2 (2 * p)

theorem log_two_mul_lt_windowWeight {w p : ℕ} (hp : p ≤ 2 * w) :
    Nat.log 2 (2 * p) < windowWeight w :=
  Nat.lt_succ_of_le (Nat.log_mono_right (by omega))

/-- §11.4, recurrences (ii) and (v): the measure drops at a shrinking call
(`Babai.MasterStep.johnsonRank_lt`). -/
theorem johnsonRankOf_lt {w p w' p' : ℕ} (hp' : p' ≤ 2 * w')
    (h : (1 ≤ w ∧ 5 * w' ≤ 4 * w) ∨ (w' ≤ w ∧ 1 ≤ p ∧ 2 * p' ≤ p)) :
    johnsonRankOf w' p' < johnsonRankOf w p := by
  rcases h with ⟨hI, h⟩ | ⟨hle, hm, h⟩
  · have h1 : windowRank w' < windowRank w := windowRank_lt _ _ hI h
    have hw : windowWeight w' ≤ windowWeight w := windowWeight_le _ _ (by omega)
    have h2 : Nat.log 2 (2 * p') < windowWeight w :=
      lt_of_lt_of_le (log_two_mul_lt_windowWeight hp') hw
    have hmul : windowRank w' * windowWeight w' + windowWeight w ≤ windowRank w * windowWeight w :=
      calc windowRank w' * windowWeight w' + windowWeight w
          ≤ windowRank w' * windowWeight w + windowWeight w :=
            Nat.add_le_add_right (Nat.mul_le_mul_left _ hw) _
        _ = (windowRank w' + 1) * windowWeight w := by ring
        _ ≤ windowRank w * windowWeight w := Nat.mul_le_mul_right _ h1
    unfold johnsonRankOf
    omega
  · have h1 : windowRank w' ≤ windowRank w := windowRank_le _ _ hle
    have hw : windowWeight w' ≤ windowWeight w := windowWeight_le _ _ hle
    have h2 : Nat.log 2 (2 * p') < Nat.log 2 (2 * p) := by
      rcases Nat.eq_zero_or_pos p' with hJ | hJ
      · rw [hJ]; simp only [mul_zero, Nat.log_zero_right]
        exact Nat.log_pos (by norm_num) (by omega)
      · exact log_lt_log_of_two_mul_le (by omega) (by omega)
    have hmul : windowRank w' * windowWeight w' ≤ windowRank w * windowWeight w :=
      Nat.mul_le_mul h1 hw
    unfold johnsonRankOf
    omega

/-- §11.4, recurrence (i): the measure does not grow at a Chain Rule call. -/
theorem johnsonRankOf_le {w p w' p' : ℕ} (hn : w' ≤ w) (hp : p' ≤ p) :
    johnsonRankOf w' p' ≤ johnsonRankOf w p := by
  have h1 : windowRank w' ≤ windowRank w := windowRank_le _ _ hn
  have hw : windowWeight w' ≤ windowWeight w := windowWeight_le _ _ hn
  have h2 : Nat.log 2 (2 * p') ≤ Nat.log 2 (2 * p) := Nat.log_mono_right (by omega)
  have hmul : windowRank w' * windowWeight w' ≤ windowRank w * windowWeight w :=
    Nat.mul_le_mul h1 hw
  unfold johnsonRankOf
  omega

theorem three_le_johnsonRankOf {w : ℕ} (p : ℕ) (h : 1 ≤ w) : 3 ≤ johnsonRankOf w p := by
  have h1 : 1 ≤ windowRank w := one_le_windowRank _ h
  have h2 : 3 ≤ windowWeight w := three_le_windowWeight _ h
  have : 1 * 3 ≤ windowRank w * windowWeight w := Nat.mul_le_mul h1 h2
  unfold johnsonRankOf
  omega

/-- §11.4: the measure is `O(log² n)` (`Babai.MasterStep.johnsonRank_le_rankBound`). -/
theorem johnsonRankOf_le_rankBound {w p : ℕ} (hp : p ≤ 2 * w) :
    johnsonRankOf w p ≤ MasterStep.rankBound w := by
  set L := Nat.log 2 w + 1 with hL
  have h1 : windowRank w ≤ 4 * L := windowRank_le_log _
  have h2 : windowWeight w ≤ L + 2 := by have := windowWeight_le_log w; omega
  have h3 := log_two_mul_lt_windowWeight hp
  have hL1 : 1 ≤ L := by omega
  have hprod : windowRank w * windowWeight w ≤ (4 * L) * (L + 2) := Nat.mul_le_mul h1 h2
  have hsq : (4 * L) * (L + 2) + (L + 1) ≤ 14 * L ^ 2 := by nlinarith
  unfold johnsonRankOf
  rw [MasterStep.rankBound, ← hL]
  omega

/-! ## The progress of Sec. 11.4 at the raw nodes -/

/-- §11.4 and §15, **what the recursion analysis uses of one round**, at the raw nodes:

* the raw Johnson parameter is at most twice the raw window size (`Babai.MasterStep.param_le`);
* the round `ρ I` has at most `q(n)` calls (`Babai.MasterStep.calls_length_le`);
* either every child makes the progress of recurrences (ii)/(v), or the round is a Chain
  Rule round, recurrence (i): its children have strictly smaller windows and no larger
  parameter, and the windows of its calls add up to at most `n`
  (`Babai.MasterStep.decreases`).

The window of a good node is the window of the instance it decodes to (`win_eq`), which is
how the sum of the windows of the calls of `ρ I` bounds that of the raw children. -/
structure RoundProgress (R : Round ι ω α) (Good : ι → Prop) (Ch : ι → ι → Prop)
    (decI : ι → SIInstance Ω A) (ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω)))
    (win param : ι → ℕ) (q : ℕ → ℕ) : Prop where
  good_child : ∀ I J, Ch I J → Good J
  win_eq : ∀ I, Good I → win I = (decI I).windowSize
  param_le : ∀ I, Good I → R.WF I → param I ≤ 2 * win I
  length_le : ∀ I, Good I → R.WF I → (ρ I).calls.length ≤ q (win I)
  decreases : ∀ I, Good I → R.WF I →
    (∀ J, Ch I J → MakesProgress win param I J) ∨
      (1 ≤ win I ∧ (∀ J, Ch I J → win J < win I ∧ param J ≤ param I) ∧
        ((ρ I).calls.map SIInstance.windowSize).sum ≤ win I)

namespace Round

variable (R : Round ι ω α) {Good : ι → Prop} {Ch : ι → ι → Prop}
    {decI : ι → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : ι → SIReduction Ω A (Set (Equiv.Perm Ω))} {win param : ι → ℕ} {q : ℕ → ℕ}

/-- **The recursion tree has at most `n² (q+1)^{johnsonRank}` nodes**: Sec. 11.4's
resolution of recurrences (i), (ii) and (v), at the raw nodes.  The proof is
`Babai.MasterStep.round_recurrence` with the lifted typed child replaced by the raw child. -/
theorem nodes_le_costBoundG (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q) (hmono : Monotone q) (n₀ : ℕ) :
    ∀ (f : ℕ) (I : ι), Good I → R.WF I → R.measure I < f → win I ≤ n₀ →
      R.nodes f I ≤ win I ^ 2 * (q n₀ + 1) ^ johnsonRankOf (win I) (param I) := by
  intro f
  induction f with
  | zero => intro I _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hG hI hf hn
    rw [R.nodes_succ]
    set B := q n₀ + 1 with hB
    have hB1 : 1 ≤ B := by omega
    obtain ⟨hmap, hch⟩ := roundCalls_eqG R himpl hP.good_child hρ f I hG hI hf
    set L := R.roundCalls f I with hL
    have hgoodL : ∀ J ∈ L, Good J ∧ R.WF J ∧ R.measure J < f := by
      intro J hJ
      obtain ⟨hw, hm⟩ := R.mem_roundCalls hI J hJ
      exact ⟨hP.good_child I J (hch J hJ), hw, by omega⟩
    have hlenρ : L.length = (ρ I).calls.length := by rw [← hmap, List.length_map]
    have hlen : L.length ≤ q n₀ := by
      rw [hlenρ]; exact (hP.length_le I hG hI).trans (hmono hn)
    have hpI := hP.param_le I hG hI
    rcases hP.decreases I hG hI with hsh | ⟨hpos, hcalls, hsum⟩
    · -- shrinking round
      by_cases hnil : L = []
      · rw [hnil]; simp
      obtain ⟨J₀, hmem⟩ : ∃ J₀, J₀ ∈ L := by
        cases hcase : L with
        | nil => exact absurd hcase hnil
        | cons a t => exact ⟨a, List.mem_cons_self⟩
      have hn1 : 1 ≤ win I := by
        rcases hsh J₀ (hch J₀ hmem) with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h
        · omega
      have hjr3 : 3 ≤ johnsonRankOf (win I) (param I) := three_le_johnsonRankOf _ hn1
      set d := johnsonRankOf (win I) (param I) with hd
      set c := win I ^ 2 * B ^ (d - 1) with hc
      have hterm : ∀ J ∈ L, R.nodes f J ≤ c := by
        intro J hJ
        obtain ⟨hGJ, hWJ, hmJ⟩ := hgoodL J hJ
        have hp := hsh J (hch J hJ)
        have h1 : win J ≤ win I := win_le_of_makesProgress hp
        have h2 : johnsonRankOf (win J) (param J) ≤ d - 1 := by
          have := johnsonRankOf_lt (hP.param_le J hGJ hWJ) hp; omega
        calc R.nodes f J ≤ win J ^ 2 * B ^ johnsonRankOf (win J) (param J) :=
              ih J hGJ hWJ hmJ (h1.trans hn)
          _ ≤ c := Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) (Nat.pow_le_pow_right hB1 h2)
      have hsumle : (L.map (R.nodes f)).sum ≤ L.length * c := by
        have := List.sum_le_card_nsmul (L.map (R.nodes f)) c
          (by intro v hv; obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hv; exact hterm J hJ)
        simpa [List.length_map, smul_eq_mul] using this
      have hcB : B ≤ c := by
        have h1 : (1:ℕ) ≤ win I ^ 2 := Nat.one_le_pow _ _ hn1
        have h2 : B ^ 1 ≤ B ^ (d - 1) := Nat.pow_le_pow_right hB1 (by omega)
        calc B ≤ B ^ (d - 1) := by simpa using h2
          _ = 1 * B ^ (d - 1) := (one_mul _).symm
          _ ≤ win I ^ 2 * B ^ (d - 1) := Nat.mul_le_mul_right _ h1
      have hsplit : B ^ d = B * B ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hpow : win I ^ 2 * B ^ d = q n₀ * c + c := by
        rw [hsplit, hc, hB]; ring
      have hmul : L.length * c ≤ q n₀ * c := Nat.mul_le_mul_right _ hlen
      rw [hpow]
      omega
    · -- Chain Rule round
      obtain ⟨k, hk⟩ : ∃ k, win I = k + 1 := ⟨win I - 1, by omega⟩
      set d := johnsonRankOf (win I) (param I) with hd
      have hterm : ∀ J ∈ L, R.nodes f J ≤ B ^ d * (win J * win J) := by
        intro J hJ
        obtain ⟨hGJ, hWJ, hmJ⟩ := hgoodL J hJ
        obtain ⟨h1, h2⟩ := hcalls J (hch J hJ)
        have hjr : johnsonRankOf (win J) (param J) ≤ d := johnsonRankOf_le (le_of_lt h1) h2
        calc R.nodes f J ≤ win J ^ 2 * B ^ johnsonRankOf (win J) (param J) :=
              ih J hGJ hWJ hmJ ((le_of_lt h1).trans hn)
          _ ≤ win J ^ 2 * B ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 hjr)
          _ = B ^ d * (win J * win J) := by ring
      have hsum1 : (L.map (R.nodes f)).sum ≤ B ^ d * (L.map (fun J => win J * win J)).sum :=
        sum_map_le_mul L _ _ _ hterm
      have hsq : (L.map (fun J => win J * win J)).sum ≤ k * (L.map win).sum :=
        sum_sq_le_mul L win k (fun J hJ => by have := (hcalls J (hch J hJ)).1; omega)
      have hwinsum : (L.map win).sum = ((ρ I).calls.map SIInstance.windowSize).sum := by
        rw [← hmap, List.map_map]
        congr 1
        refine List.map_congr_left fun J hJ => ?_
        exact hP.win_eq J (hgoodL J hJ).1
      have hsq2 : (L.map (fun J => win J * win J)).sum ≤ k * (k + 1) := by
        refine le_trans hsq (Nat.mul_le_mul_left _ ?_)
        rw [hwinsum, ← hk]
        exact hsum
      have hcount : L.length ≤ B ^ d * (k + 1) := by
        have h1 : B ≤ B ^ d := by
          have : B ^ 1 ≤ B ^ d := Nat.pow_le_pow_right hB1 (by
            have := three_le_johnsonRankOf (param I) hpos; omega)
          simpa using this
        have h2 : B ^ d ≤ B ^ d * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have htot : win I ^ 2 * B ^ d = B ^ d * (k + 1) + B ^ d * (k * (k + 1)) := by
        rw [hk]; ring
      have := Nat.mul_le_mul_left (B ^ d) hsq2
      rw [htot]
      omega

/-- **The bound the evaluator needs**: at most `2 ^ (30 (log₂ n + 2) ^ (c₁ + 2))` nodes, as
in `Algo.Round.nodes_le_quasiPolyN`. -/
theorem nodes_le_quasiPolyG (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q) (hmono : Monotone q) (c₁ : ℕ)
    (hq : ∀ n : ℕ, q n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f : ℕ) (I : ι) (hG : Good I) (hI : R.WF I) (hf : R.measure I < f) :
    R.nodes f I ≤ 2 ^ (30 * (Nat.log 2 (win I) + 2) ^ (c₁ + 2)) := by
  set n := win I with hn
  set L := Nat.log 2 n + 2 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hcount : R.nodes f I ≤ n ^ 2 * (q n + 1) ^ johnsonRankOf n (param I) :=
    R.nodes_le_costBoundG himpl hρ hP hmono n f I hG hI hf le_rfl
  have hQ : q n + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
    have h := hq n
    have h2 : (2 : ℕ) ^ (L ^ c₁) + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (L ^ c₁) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [← hLdef] at h
    omega
  have hrk : johnsonRankOf n (param I) ≤ 14 * L ^ 2 := by
    have h := johnsonRankOf_le_rankBound (hP.param_le I hG hI)
    rw [MasterStep.rankBound, ← hn] at h
    refine le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    omega
  have hn2 : n ^ 2 ≤ 2 ^ (2 * L) := by
    have hlt : n < 2 ^ L :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) n)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc n ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
      _ = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  calc R.nodes f I ≤ n ^ 2 * (q n + 1) ^ johnsonRankOf n (param I) := hcount
    _ ≤ 2 ^ (2 * L) * (2 ^ (L ^ c₁ + 1)) ^ (14 * L ^ 2) :=
        Nat.mul_le_mul hn2 ((Nat.pow_le_pow_left hQ _).trans
          (Nat.pow_le_pow_right Nat.one_le_two_pow hrk))
    _ = 2 ^ (2 * L + (L ^ c₁ + 1) * (14 * L ^ 2)) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (30 * L ^ (c₁ + 2)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have hle : L ^ 2 ≤ L ^ (c₁ + 2) := Nat.pow_le_pow_right hL1 (by omega)
        have hle1 : L ≤ L ^ 2 := by nlinarith
        have hexp : (L ^ c₁ + 1) * (14 * L ^ 2) = 14 * (L ^ c₁ * L ^ 2) + 14 * L ^ 2 := by
          ring
        rw [hexp, ← pow_add]
        omega

/-- **The evaluator answers every good node.**  `Algo.Round.evaluate_eq_answerN` without a
typed node and without `hlift`. -/
theorem evaluate_eq_answerG (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q) (hmono : Monotone q) (c₁ : ℕ)
    (hq : ∀ n : ℕ, q n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f N : ℕ) (I : ι) (hG : Good I) (hI : R.WF I) (hf : R.measure I < f)
    (hN : 3 * 2 ^ (30 * (Nat.log 2 (win I) + 2) ^ (c₁ + 2)) + 1 ≤ N) :
    ∃ a : α, R.evaluate N I = some a ∧ decA I a = (decI I).answer := by
  have hnodes := R.nodes_le_quasiPolyG himpl hρ hP hmono c₁ hq f I hG hI hf
  have hsteps : R.subSteps f I ≤ N := by
    have := R.subSteps_le f I
    omega
  exact ⟨R.value f I, R.evaluate_eq_value f N I hI hf hsteps,
    roundValue_eqG R himpl hP.good_child hρ f I hG hI hf⟩


/-- Every value of the fold is a value of `finish` at the node. -/
theorem loopAux_eq_finish (rec : ι → α) :
    ∀ (w : ℕ) (I : ι) (j : ℕ) (s : ω), ∃ s' : ω, R.loopAux rec w I j s = R.finish (I, s') := by
  intro w
  induction w with
  | zero => intro I j s; exact ⟨s, rfl⟩
  | succ w ih =>
    intro I j s
    cases hc : R.child (I, j, s) with
    | none => exact ⟨s, by rw [R.loopAux_succ_none hc]⟩
    | some J => rw [R.loopAux_succ_some hc]; exact ih I _ _

variable [Enc ι] [Enc ω] [Enc α]

/-- **The routine answers every good node**: `Algo.Round.runQ_eq_answerN` without a typed
node and without `hlift`.  The answer is a value of `finish` at the node, which is how its
well-formedness is read off.  This is the form the bridge
`Algo.siWorkspaceRoutine_of_normQ_run` is fed through its hypothesis `hdec`. -/
theorem runQ_eq_answerG (C : RunCostQ R) (himpl : ImplementsG R Good Ch decI decA ρ)
    (hρ : ∀ I : ι, Good I → R.WF I → (ρ I).run = (decI I).answer)
    (hP : RoundProgress R Good Ch decI ρ win param q) (hmono : Monotone q) (c₁ : ℕ)
    (hq : ∀ n : ℕ, q n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, Good I → R.WF I → win I ≤ R.ground I)
    (I : ι) (hG : Good I) (hI : R.WF I) :
    ∃ s : ω, R.runQ C c₁ I = some (R.finish (I, s)) ∧
      decA I (R.finish (I, s)) = (decI I).answer := by
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (win I) + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hG hI)
    simpa [roundCount] using this
  have hnodes := R.nodes_le_quasiPolyG himpl hρ hP hmono c₁ hq (R.measure I + 1) I hG hI
    (Nat.lt_succ_self _)
  have hsteps : R.subSteps (R.measure I + 1) I ≤ roundCount c₁ (R.ground I) := by
    have := R.subSteps_le (R.measure I + 1) I
    omega
  have hval := R.evaluate_eq_value (R.measure I + 1) _ I hI (Nat.lt_succ_self _) hsteps
  have hdec := roundValue_eqG R himpl hP.good_child hρ (R.measure I + 1) I hG hI
    (Nat.lt_succ_self _)
  obtain ⟨s, hs⟩ := R.loopAux_eq_finish (R.value (R.measure I)) (R.width I) I 0 (R.init I)
  rw [R.value_succ, hs] at hval hdec
  exact ⟨s, by rw [R.runQ_eq_evaluate C c₁ I hI]; exact hval, hdec⟩

end Round

end Algo

#print axioms Algo.Round.runQ_eq_answerG
