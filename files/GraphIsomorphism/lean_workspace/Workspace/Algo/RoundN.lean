/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: a round that implements a reduction, with an answer decoder that may
depend on the node.
-/
import Workspace.Algo.Round

/-!
# The round-to-reduction link with a node-dependent answer decoder

`Algo.LoopMatch` and `Algo.Implements` (`Workspace/Algo/Round.lean`) read a raw answer with
one fixed decoder `decA : α → Set (Equiv.Perm Ω)`.  That is enough as long as the machine and
the mathematics print the same typed instance at every node.  They do not: Sec. 11.1,
Remark 11.1.4 prints Luks's Eqs. (62)–(63) in two forms, the **coset** form `⟨σH, Δ, x, y⟩`
and the **group** form `⟨H, Δ, x, y^{σ⁻¹}⟩`, and the two layers chose different ones.

* `Workspace/Algo/` builds coset instances with unshifted strings.  It has to: a raw round
  must walk one fixed typed tree for **every** raw answer that decodes to the true answer
  (`Algo.LoopMatch.call`), so a child may depend on the decoded coset but not on which
  representative a raw answer happens to carry.
* `Workspace/Master/` builds group instances, which is what `Babai.IsGroupInstance` asks for.

By Eq. (59) the two answer the same question up to the shift by the representative, so the
*values* agree.  The *lists of calls* do not, and `Algo.Implements` compares lists of calls.

The repair, in one sentence: the machine never aligns, and the alignment of Remark 11.1.4 is
applied once, in the typed world, to the whole round.  After that move the answer of a node
is read off its raw answer by a decoder that shifts by the representative **of that node**,
so the decoder depends on the node.  This file is the link relation and the whole chain of
consequences written for such a decoder.  The transfer itself is
`Workspace/Algo/AlignTransfer.lean`; the evaluator is `Workspace/Algo/EvaluatorN.lean`.

## Main definitions

* `Algo.LoopMatchN`, `Algo.ImplementsN` — `Algo.LoopMatch` and `Algo.Implements` with
  `decA : ι → α → Set (Equiv.Perm Ω)`.

## Main results

* `Algo.loopMatchN_of_loopMatch`, `Algo.implementsN_of_implements` — the old notions are the
  case of a decoder that ignores the node;
* `Algo.Round.loopAux_eqN`, `Algo.roundValue_eqN`, `Algo.Round.roundCalls_eqN` — the value
  and the calls of the fold;
* `Algo.Round.nodes_eq_countN`, `Algo.Round.nodes_le_costBoundN`,
  `Algo.Round.nodes_le_quasiPolyN` — the node count, unchanged.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

variable {ι ω α : Type*} {Ω : Type u} {A : Type v}

open Babai

/-! ## The link relation -/

/-- The fold of `R` from the state `(j, s)` with budget `w` walks the reduction `T`, where a
raw answer is decoded by `decA J`, the decoder **of the node `J` that produced it**.

This is `Algo.LoopMatch` with the single decoder `decA` replaced by a family.  Only two
places see the change: the answer of the node `I` itself is read with `decA I`, and the
answer of a child `J` is read with `decA J`. -/
inductive LoopMatchN (R : Round ι ω α) (decI : ι → SIInstance Ω A)
    (decA : ι → α → Set (Equiv.Perm Ω)) (I : ι) :
    ℕ → ℕ → ω → SIReduction Ω A (Set (Equiv.Perm Ω)) → Prop where
  /-- Both stop, with the same answer. -/
  | done (w j : ℕ) (s : ω) (a : Set (Equiv.Perm Ω)) (hc : R.child (I, j, s) = none)
      (ha : decA I (R.finish (I, s)) = a) : LoopMatchN R decI decA I w j s (.done a)
  /-- Both ask the same instance, and continue to match for every raw answer that decodes to
  its true answer. -/
  | call (w j : ℕ) (s : ω) (J : ι)
      (k : Set (Equiv.Perm Ω) → SIReduction Ω A (Set (Equiv.Perm Ω)))
      (hc : R.child (I, j, s) = some J)
      (hnext : ∀ a : α, decA J a = (decI J).answer →
        LoopMatchN R decI decA I w (j + 1) (R.combine (I, j, s, a)) (k (decI J).answer)) :
      LoopMatchN R decI decA I (w + 1) j s (.call (decI J) k)

/-- **The raw round `R` implements the mathematical round `ρ`**, with an answer decoder that
may depend on the node.  This is `Algo.Implements` with `decA : ι → α → Set (Equiv.Perm Ω)`;
see the header of this file for why the family is needed. -/
def ImplementsN {κ : Type*} (R : Round ι ω α) (decI : ι → κ) (inst : κ → SIInstance Ω A)
    (decA : ι → α → Set (Equiv.Perm Ω))
    (ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))) : Prop :=
  ∀ I : ι, R.WF I →
    LoopMatchN R (fun J => inst (decI J)) decA I (R.width I) 0 (R.init I) (ρ (decI I))

/-! ### The old notions are the constant case -/

/-- A match with one fixed decoder is a match with the constant family. -/
theorem loopMatchN_of_loopMatch {R : Round ι ω α} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} {w j : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))} (h : LoopMatch R decI decA I w j s T) :
    LoopMatchN R decI (fun _ => decA) I w j s T := by
  induction h with
  | done w j s a hc ha => exact LoopMatchN.done w j s a hc ha
  | call w j s J k hc _ ih => exact LoopMatchN.call w j s J k hc fun a ha => ih a ha

/-- And back again. -/
theorem loopMatch_of_loopMatchN {R : Round ι ω α} {decI : ι → SIInstance Ω A}
    {decA : α → Set (Equiv.Perm Ω)} {I : ι} {w j : ℕ} {s : ω}
    {T : SIReduction Ω A (Set (Equiv.Perm Ω))}
    (h : LoopMatchN R decI (fun _ => decA) I w j s T) : LoopMatch R decI decA I w j s T := by
  induction h with
  | done w j s a hc ha => exact LoopMatch.done w j s a hc ha
  | call w j s J k hc _ ih => exact LoopMatch.call w j s J k hc fun a ha => ih a ha

/-- `Algo.Implements` is `Algo.ImplementsN` at a decoder that ignores the node. -/
theorem implementsN_of_implements {κ : Type*} {R : Round ι ω α} {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))} (h : Implements R decI inst decA ρ) :
    ImplementsN R decI inst (fun _ => decA) ρ :=
  fun I hI => loopMatchN_of_loopMatch (h I hI)

/-- And back again. -/
theorem implements_of_implementsN {κ : Type*} {R : Round ι ω α} {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (h : ImplementsN R decI inst (fun _ => decA) ρ) : Implements R decI inst decA ρ :=
  fun I hI => loopMatch_of_loopMatchN (h I hI)

namespace Round

/-! ## The value and the calls of the fold -/

/-- **The fold computes what the tree computes.**  `Algo.Round.loopAux_eq` with a
node-dependent decoder: the same induction, with `decA` applied to the node in hand. -/
theorem loopAux_eqN (R : Round ι ω α) {decI : ι → SIInstance Ω A}
    {decA : ι → α → Set (Equiv.Perm Ω)} {I : ι} {rec : ι → α} {Good : ι → Prop}
    (hgood : ∀ (j : ℕ) (s : ω) (J : ι), R.child (I, j, s) = some J → Good J)
    (hrec : ∀ J, Good J → decA J (rec J) = (decI J).answer) :
    ∀ (w j : ℕ) (s : ω) (T : SIReduction Ω A (Set (Equiv.Perm Ω))),
      LoopMatchN R decI decA I w j s T →
        decA I (R.loopAux rec w I j s) = T.run ∧
          (R.loopCalls rec w I j s).map decI = T.calls := by
  intro w j s T h
  induction h with
  | done w j s a hc ha =>
    cases w with
    | zero => exact ⟨by simpa using ha, by simp⟩
    | succ w =>
      refine ⟨?_, ?_⟩
      · rw [R.loopAux_succ_none hc]; simpa using ha
      · rw [R.loopCalls_succ_none hc]; simp
  | call w j s J k hc hnext ih =>
    have hG : Good J := hgood j s J hc
    have hA : decA J (rec J) = (decI J).answer := hrec J hG
    obtain ⟨h1, h2⟩ := ih (rec J) hA
    refine ⟨?_, ?_⟩
    · rw [R.loopAux_succ_some hc, h1, SIReduction.run_call]
    · rw [R.loopCalls_succ_some hc, List.map_cons, h2, SIReduction.calls_call]

end Round

/-- **The round computes the answer.**  `Algo.roundValue_eq` with a node-dependent
decoder. -/
theorem roundValue_eqN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (himpl : ImplementsN R decI inst decA ρ)
    (hρ : ∀ I : ι, R.WF I → (ρ (decI I)).run = (inst (decI I)).answer) :
    ∀ (f : ℕ) (I : ι), R.WF I → R.measure I < f →
      decA I (R.value f I) = (inst (decI I)).answer := by
  intro f
  induction f with
  | zero => intro I _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hI hf
    obtain ⟨h1, -⟩ :=
      R.loopAux_eqN (Good := fun J => R.WF J ∧ R.measure J < R.measure I)
        (fun j s J hc => ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
        (fun J hJ => ih J hJ.1 (lt_of_lt_of_le hJ.2 (Nat.lt_succ_iff.mp hf)))
        _ _ _ _ (himpl I hI)
    rw [R.value_succ, h1, hρ I hI]

namespace Round

/-- **The children of a round are the calls of the reduction.**  `Algo.Round.roundCalls_eq`
with a node-dependent decoder. -/
theorem roundCalls_eqN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {inst : κ → SIInstance Ω A} {decA : ι → α → Set (Equiv.Perm Ω)}
    {ρ : κ → SIReduction Ω A (Set (Equiv.Perm Ω))}
    (himpl : ImplementsN R decI inst decA ρ)
    (hρ : ∀ I : ι, R.WF I → (ρ (decI I)).run = (inst (decI I)).answer)
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f + 1) :
    (R.roundCalls f I).map (fun J => inst (decI J)) = (ρ (decI I)).calls := by
  obtain ⟨-, h2⟩ :=
    R.loopAux_eqN (rec := R.value f) (Good := fun J => R.WF J ∧ R.measure J < R.measure I)
      (fun j s J hc => ⟨R.child_wf I j s J hI hc, R.child_measure I j s J hI hc⟩)
      (fun J hJ => roundValue_eqN R himpl hρ f J hJ.1
        (lt_of_lt_of_le hJ.2 (Nat.lt_succ_iff.mp hf)))
      _ _ _ _ (himpl I hI)
  exact h2

/-! ## The number of nodes

Word for word `Algo.Round.nodes_eq_count`, `Algo.Round.nodes_le_costBound` and
`Algo.Round.nodes_le_quasiPoly`: none of the three mentions the decoder in its conclusion,
and each uses it only through `Algo.Round.roundCalls_eqN`. -/

/-- **The recursion tree of the round is the recursion tree of Sec. 15.**
`Algo.Round.nodes_eq_count` with a node-dependent decoder. -/
theorem nodes_eq_countN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J))) :
    ∀ (f : ℕ) (I : ι), R.WF I → R.measure I < f → R.nodes f I = M.count f (decI I) := by
  intro f
  induction f with
  | zero => intro I _ h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro I hI hf
    have hgrpI : IsGroupInstance (M.inst (decI I)) := hgrp I hI
    have hrankI : M.rank (decI I) < f + 1 := lt_of_le_of_lt (hrank I hI) hf
    have hagree : ∀ J : SIInstance Ω A,
        (∃ _ : J ∈ (M.step (decI I)).calls,
          IsGroupInstance (M.inst (M.lift (decI I) J)) ∧
            M.rank (M.lift (decI I) J) < M.rank (decI I)) →
        solveFuel M.step M.lift f (M.lift (decI I) J) = J.answer := by
      rintro J ⟨hJ, hg, hr⟩
      have h1 := M.solve_eq_answer f (M.lift (decI I) J) hg (by omega)
      rw [show solveFuel M.step M.lift f (M.lift (decI I) J)
          = M.solve f (M.lift (decI I) J) from rfl, h1, M.lift_inst (decI I) J hJ]
    obtain ⟨hcalls, -⟩ :=
      SIReduction.callsWith_eq_calls_of_agree
        (O := fun J => solveFuel M.step M.lift f (M.lift (decI I) J))
        hagree (M.step (decI I))
        (fun J hJ => ⟨hJ, by
            rw [M.lift_inst (decI I) J hJ]
            exact M.calls_isGroupInstance (decI I) hgrpI J hJ,
          M.rank_lt (decI I) hgrpI J hJ⟩)
    have hround : Babai.roundCalls M.step M.lift f (decI I) = (M.step (decI I)).calls :=
      hcalls
    have hmap : (R.roundCalls f I).map (fun J => M.inst (decI J)) = (M.step (decI I)).calls :=
      R.roundCalls_eqN himpl (fun I' hI' => M.round_correct (decI I') (hgrp I' hI')) f I hI hf
    have hsum : ((R.roundCalls f I).map (R.nodes f)).sum
        = (((R.roundCalls f I).map (fun J => M.inst (decI J))).map
            (fun J => countCalls M.step M.lift f (M.lift (decI I) J))).sum := by
      rw [List.map_map]
      refine congrArg List.sum (List.map_congr_left ?_)
      intro J hJ
      obtain ⟨hJwf, hJm⟩ := R.mem_roundCalls hI J hJ
      have hL : M.lift (decI I) (M.inst (decI J)) = decI J := (hlift f I J hI hJ).symm
      show R.nodes f J = countCalls M.step M.lift f (M.lift (decI I) (M.inst (decI J)))
      rw [hL]
      exact ih J hJwf (by omega)
    have hlen : (R.roundCalls f I).length = (M.step (decI I)).calls.length := by
      rw [← hmap, List.length_map]
    rw [R.nodes_succ, MasterStep.count, countCalls_succ, hround, ← hmap, hsum, hlen, ← hmap,
      List.length_map]

/-- The recursion tree of the round has at most `n² (q+1)^{johnsonRank}` nodes.
`Algo.Round.nodes_le_costBound` with a node-dependent decoder. -/
theorem nodes_le_costBoundN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (n₀ : ℕ) (f : ℕ) (I : ι) (hI : R.WF I)
    (hn : (M.inst (decI I)).windowSize ≤ n₀) (hf : R.measure I < f) :
    R.nodes f I ≤ M.costBound (M.roundCost n₀ + 1) (decI I) := by
  rw [R.nodes_eq_countN (decA := decA) M himpl hgrp hrank hlift f I hI hf]
  exact M.count_le n₀ hmono f (decI I) (hgrp I hI) hn (lt_of_le_of_lt (hrank I hI) hf)

/-- **The bound the evaluator needs.**  `Algo.Round.nodes_le_quasiPoly` with a
node-dependent decoder: at most `2 ^ (30 (log₂ n + 2) ^ (c₁ + 2))` nodes. -/
theorem nodes_le_quasiPolyN {κ : Type*} (R : Round ι ω α) {decI : ι → κ}
    {decA : ι → α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : ImplementsN R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (f : ℕ) (I : ι) (hI : R.WF I) (hf : R.measure I < f) :
    R.nodes f I ≤ 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) := by
  set n := (M.inst (decI I)).windowSize with hn
  set L := Nat.log 2 n + 2 with hLdef
  have hL1 : 1 ≤ L := by omega
  have hcount : R.nodes f I ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank (decI I) := by
    have := R.nodes_le_costBoundN (decA := decA) M himpl hgrp hrank hlift hmono n f I hI
      (le_refl _) hf
    rwa [MasterStep.costBound, MasterStep.win, ← hn] at this
  have hQ : M.roundCost n + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
    have h := hq n
    have h2 : (2 : ℕ) ^ (L ^ c₁) + 1 ≤ 2 ^ (L ^ c₁ + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (L ^ c₁) := Nat.one_le_two_pow
      rw [pow_succ]
      omega
    rw [← hLdef] at h
    omega
  have hrk : M.johnsonRank (decI I) ≤ 14 * L ^ 2 := by
    have h := M.johnsonRank_le_rankBound (decI I)
    rw [MasterStep.rankBound, MasterStep.win, ← hn] at h
    refine le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2))
    omega
  have hn2 : n ^ 2 ≤ 2 ^ (2 * L) := by
    have hlt : n < 2 ^ L :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) n)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc n ^ 2 ≤ (2 ^ L) ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
      _ = 2 ^ (2 * L) := by rw [← pow_mul, mul_comm]
  calc R.nodes f I ≤ n ^ 2 * (M.roundCost n + 1) ^ M.johnsonRank (decI I) := hcount
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

end Round

end Algo
