/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5): the fold states of the round of
lines 5–7 of the Master Algorithm (Sec. 15) along a run. Not part of the faithful formalization.
-/
import Workspace.Explicit.L57EnvX
import Workspace.Explicit.L57Master
import Workspace.Explicit.CarriersInv

/-!
# The fold states of lines 5–7 along a run

The round of lines 5–7 (`Algo.aggnL57GRound`) keeps the state of the two phases of Procedure
AggregateCertificates, the state of stretch 3 (Procedure Align, `Algo.ADState`), and the state
of the giant branch (`Algo.Top4State`). The phase states are capped by
`Algo.aggnAggregatePack` at `2^{(log |x| + 2)^{dc}}`, with an existential `dc`, so a bound on
the states that holds for every state `combine` may start from has no explicit exponent. The
states a run reaches are much smaller. `Explicit.L57GInv` describes them:

* the phase states satisfy the envelope invariants of `Workspace/Explicit/L57Env.lean` at the
  fold index (the certificate phase) and at the comparison cursor (the comparison phase), or
  were reset by the caps (`Explicit.AggInv`), with envelopes of explicit size
  (`Explicit.env_exists`);
* the state of stretch 3 is a step of `Algo.l57Step` at the header of the current stores, and
  the state of the giant branch is a step of `Algo.top4aCombine` at the node of the current
  stores (the caps are idempotent, `Explicit.aggnAggregatePack_idem`, so the header and the
  node do not move once the two phases are over).

`combine` keeps `L57GInv` (`Explicit.L57GInv.combine`), and `L57GInv` bounds the state by
`2^{K (log₂ n + 2)^5}` (`Explicit.l57GInv_size`).
-/

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

namespace Explicit

open RAM Algo

/-! ## The caps -/

theorem capState_cases (d m : ℕ) (s : AggnPhaseState) :
    aggnCapState d (m, s) = s ∨ aggnCapState d (m, s) = aggnZeroPhase := by
  unfold aggnCapState; split <;> simp

theorem compareCapState_cases (d m : ℕ) (s : AggnCompareState) :
    aggnCompareCapState d (m, s) = s ∨ aggnCompareCapState d (m, s) = default := by
  unfold aggnCompareCapState; split <;> simp

/-- **The caps of the aggregate carrier are idempotent.** -/
theorem aggnAggregatePack_idem (c dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnAggregatePack c dc dp C (aggnAggregatePack c dc dp C s) =
      aggnAggregatePack c dc dp C s := by
  simp only [aggnAggregatePack, aggnCapState_eq (aggnCapState_size _ _ _),
    aggnCompareCapState_eq (aggnCompareCapState_size _ _ _), min_assoc, min_self]

theorem aggnL57Hdr_pack (c b t d dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnL57Hdr c b t d dc dp (C, aggnAggregatePack c dc dp C s) =
      aggnL57Hdr c b t d dc dp (C, s) := by
  unfold aggnL57Hdr; rw [aggnAggregatePack_idem]

theorem aggnL57GNode_pack (c dc dp : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnL57GNode c dc dp (C, aggnAggregatePack c dc dp C s) = aggnL57GNode c dc dp (C, s) := by
  unfold aggnL57GNode; rw [aggnAggregatePack_idem]

/-! ## The children of the two phases -/

theorem aggnPhaseChild_facts {c : ℕ} {z : AggnPhaseNode × ℕ × AggnPhaseState}
    {J : AggnPhaseNode} (h : aggnPhaseChild c z = some J) :
    z.2.1 < aggnPhaseWidth c z.1.1 ∧ z.2.2.1 ≠ [] := by
  obtain ⟨I, j, jobs, rest⟩ := z
  obtain ⟨C, o⟩ := I
  cases o with
  | some W => simp [aggnPhaseChild] at h
  | none =>
    simp only [aggnPhaseChild, Option.elim_none] at h
    split_ifs at h with hw
    refine ⟨hw, fun he => ?_⟩
    subst he
    simp at h

theorem aggnCompareChild_facts {c : ℕ} {z : AggnPhaseNode × ℕ × AggnCompareState}
    {J : AggnPhaseNode} (h : aggnCompareChild c z = some J) :
    z.2.1 < aggnCompareWidth c z.1.1 ∧ z.2.2.1 ≠ [] := by
  obtain ⟨I, j, jobs, rest⟩ := z
  obtain ⟨C, o⟩ := I
  cases o with
  | some W => simp [aggnCompareChild] at h
  | none =>
    simp only [aggnCompareChild, Option.elim_none] at h
    split_ifs at h with hw
    refine ⟨hw, fun he => ?_⟩
    subst he
    simp at h

/-! ## The two phases -/

variable {c n : ℕ} {C : AggnPhaseCtx}

/-- **The states of the two phases along a run**: the certificate phase within its envelope
at the fold index (capped at its width), or reset by its cap; the comparison cursor within the
comparison width; the comparison phase within its envelope at the cursor, or reset by its
cap. -/
def AggInv (B : PhaseEnv c n C) (B' : CompEnv c n C) (j : ℕ) (s : AggnAggregateState) :
    Prop :=
  (PhaseB B (min j (aggnPhaseWidth c C)) s.1 ∨ s.1 = aggnZeroPhase) ∧
    s.2.1 ≤ aggnCompareWidth c C ∧ (CompB B' s.2.1 s.2.2 ∨ s.2.2 = default)

theorem AggInv.mono {B : PhaseEnv c n C} {B' : CompEnv c n C} {j k : ℕ}
    {s : AggnAggregateState} (h : AggInv B B' j s) (hjk : j ≤ k) : AggInv B B' k s :=
  ⟨h.1.imp_left (fun h1 => h1.mono (min_le_min_right _ hjk)), h.2⟩

theorem AggInv.pack {B : PhaseEnv c n C} {B' : CompEnv c n C} {j : ℕ}
    {s : AggnAggregateState} (h : AggInv B B' j s) (dc dp : ℕ) :
    AggInv B B' j (aggnAggregatePack c dc dp C s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · change PhaseB B _ (aggnCapState dc (C.2.1.length, s.1)) ∨
      aggnCapState dc (C.2.1.length, s.1) = aggnZeroPhase
    rcases capState_cases dc C.2.1.length s.1 with e | e <;> rw [e]
    · exact h1
    · exact Or.inr rfl
  · exact Nat.min_le_right _ _
  · change CompB B' (min s.2.1 (aggnCompareWidth c C)) (aggnCompareCapState dp
      (C.2.1.length, s.2.2)) ∨ aggnCompareCapState dp (C.2.1.length, s.2.2) = default
    rw [min_eq_left h2]
    rcases compareCapState_cases dp C.2.1.length s.2.2 with e | e <;> rw [e]
    · exact h3
    · exact Or.inr rfl

theorem aggInv_init (B : PhaseEnv c n C) (B' : CompEnv c n C) (dc dp : ℕ) :
    AggInv B B' 0 (aggnAggregateInit c dc dp (C, none)) := by
  simp only [Algo.aggnAggregateInit, aggnUniformRound, aggnCompareBoundedRound,
    aggnBoundedInit, aggnCompareBoundedInit]
  refine ⟨?_, Nat.zero_le _, ?_⟩
  · rw [Nat.zero_min]
    rcases capState_cases dc (C, (none : Option RawWinSI)).1.2.1.length
      ((aggnCheckedRound c 0).init (C, none)) with e | e <;> rw [e]
    · exact Or.inl (phaseB_init B)
    · exact Or.inr rfl
  · rcases compareCapState_cases dp (C, (none : Option RawWinSI)).1.2.1.length
      ((aggnCompareCheckedRound c).init (C, none)) with e | e <;> rw [e]
    · exact Or.inl (compB_init B')
    · exact Or.inr rfl

/-- **A combine of the two phases keeps the invariant**, when the carrier asked a child. -/
theorem AggInv.combine {B : PhaseEnv c n C} {B' : CompEnv c n C} {j : ℕ}
    {s : AggnAggregateState} (h : AggInv B B' j s) (dc dp : ℕ) {J : AggnPhaseNode}
    (hch : aggnAggregateChild c ((C, none), j, s) = some J) (A : RawCoset) :
    AggInv B B' (j + 1) (aggnAggregateCombine c dc dp ((C, none), j, s, A)) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [aggnAggregateChild, Option.elim_none] at hch
  split_ifs at hch with hw he
  · -- the comparison phase
    obtain ⟨-, W, hW, -⟩ := aggnCompareCheckedChild_some hch
    obtain ⟨hcw, hne⟩ := aggnCompareChild_facts hW
    have hB : CompB B' s.2.1 s.2.2 := h3.resolve_right (fun hd => hne (by rw [hd]; rfl))
    have hnew := hB.combine_norm A (C, none) rfl s.2.1
    simp only [aggnAggregateCombine, he, if_true, aggnCompareBoundedRound,
      aggnCompareBoundedCombine]
    apply AggInv.pack
    refine ⟨h1.imp_left (fun h => h.mono (min_le_min_right _ (Nat.le_succ j))), hcw, ?_⟩
    rcases compareCapState_cases dp (C, (none : Option RawWinSI)).1.2.1.length
      (aggnCompareCombine c ((C, none), s.2.1, s.2.2, aggnNormAnswer C.2.1 A)) with e | e <;>
      rw [e]
    · exact Or.inl hnew
    · exact Or.inr rfl
  · -- the certificate phase
    obtain ⟨-, W, hW, -⟩ := aggnCheckedChild_some hch
    obtain ⟨hpw, hne⟩ := aggnPhaseChild_facts hW
    have hB : PhaseB B j s.1 := by
      have := h1.resolve_right (fun hz => hne (by rw [hz]; rfl))
      rwa [min_eq_left hpw.le] at this
    have hnew := hB.combine_norm A (C, none) rfl j
    simp only [aggnAggregateCombine, he, Bool.false_eq_true, if_false, aggnUniformRound,
      aggnBoundedCombine]
    apply AggInv.pack
    refine ⟨?_, h2, h3⟩
    rw [min_eq_left hpw]
    rcases capState_cases dc (C, (none : Option RawWinSI)).1.2.1.length
      (aggnPhaseCombine c ((C, none), j, s.1, aggnNormAnswer C.2.1 A)) with e | e <;> rw [e]
    · exact Or.inl hnew
    · exact Or.inr rfl

/-! ## The round of lines 5–7 -/

/-- **The fold states of the round of lines 5–7 along a run**, at the context `C` of degree
`n`: the context is that of the round (`Explicit.L57CtxOK`) and has size at most
`2^{K₀ (log₂ n + 2)^5}`; the two phases satisfy `Explicit.AggInv` for envelopes whose fields
and the width of the phases sum to at most `2^{K₁ (log₂ n + 2)^5}`; the state of stretch 3 is
a step of `Algo.l57Step` at the header of the current stores; the state of the giant branch is
a count within the width of `Algo.top4aRound` and a step of `Algo.top4aCombine` at the node of
the current stores. -/
def L57GInv (c b t d dc dp K0 K1 n : ℕ) (C : AggnPhaseCtx) (j : ℕ) (s : AggnL57GState) :
    Prop :=
  L57CtxOK c n C ∧ Enc.size C ≤ 2 ^ (K0 * lg n ^ 5) ∧
    (∃ (B : PhaseEnv c n C) (B' : CompEnv c n C),
      phaseEnvTot B + compEnvTot B' + aggnAggregateWidth c C ≤ 2 ^ (K1 * lg n ^ 5) ∧
        AggInv B B' j s.1.1) ∧
    (∀ st, s.1.2 = some st →
      ∃ st' A, st = l57Step (aggnL57Hdr c b t d dc dp (C, s.1.1), st', A)) ∧
    (∀ q, s.2 = some q → q.1 ≤ l57gW4 (aggnL57GNode c dc dp (C, s.1.1)) ∧
      ∃ j' st' A, q.2 = top4aCombine (aggnL57GNode c dc dp (C, s.1.1), j', st', A))

variable {b t d dc dp K0 K1 : ℕ}

/-- **The start of the round.** -/
theorem l57GInv_init (hC : L57CtxOK c n C) (hs : Enc.size C ≤ 2 ^ (K0 * lg n ^ 5))
    (hB : ∃ (B : PhaseEnv c n C) (B' : CompEnv c n C),
      phaseEnvTot B + compEnvTot B' + aggnAggregateWidth c C ≤ 2 ^ (K1 * lg n ^ 5)) :
    L57GInv c b t d dc dp K0 K1 n C 0 ((aggnAggregateInit c dc dp (C, none), none), none) := by
  obtain ⟨B, B', hle⟩ := hB
  exact ⟨hC, hs, ⟨B, B', hle, aggInv_init B B' dc dp⟩, fun st h => absurd h (by simp),
    fun q h => absurd h (by simp)⟩

/-- **A combine of the round keeps the invariant**, whatever the answer. -/
theorem L57GInv.combine (u v e f : ℕ) {j : ℕ} {s : AggnL57GState}
    (h : L57GInv c b t d dc dp K0 K1 n C j s) (A : RawCoset) :
    L57GInv c b t d dc dp K0 K1 n C (j + 1)
      (aggnL57GCombine c b t d dc dp u v e f ((C, none), j, s, A)) := by
  obtain ⟨hC, hs, ⟨B, B', hle, hI⟩, -, -⟩ := h
  have hpack := (hI.pack dc dp).mono (Nat.le_succ j)
  unfold aggnL57GCombine
  split_ifs with hact
  · -- the giant branch
    dsimp only [aggnL57GTopCombine]
    refine ⟨hC, hs, ⟨B, B', hle, hpack⟩, fun st h => absurd h (by simp), fun q hq => ?_⟩
    cases hq
    refine ⟨?_, (aggnL57GPos c dc dp (C, s)).1, (aggnL57GPos c dc dp (C, s)).2, A, ?_⟩
    · dsimp only
      rw [aggnL57GNode_pack]
      exact Nat.min_le_right _ _
    · dsimp only
      rw [aggnL57GNode_pack]
  · -- stretches 1–3
    unfold aggnL57Combine
    dsimp only
    cases hch : aggnAggregateChild c ((C, none), j, s.1.1) with
    | none =>
      simp only [Option.elim_none]
      refine ⟨hC, hs, ⟨B, B', hle, hpack⟩, fun st hst => ?_, fun q h => absurd h (by simp)⟩
      cases hst
      exact ⟨_, _, by rw [aggnL57Hdr_pack]⟩
    | some J =>
      simp only [Option.elim_some]
      exact ⟨hC, hs, ⟨B, B', hle, hI.combine dc dp hch A⟩, fun st h => absurd h (by simp),
        fun q h => absurd h (by simp)⟩

/-! ## The size of the states -/

theorem size_option_le {α : Type*} [Enc α] {o : Option α} {M : ℕ}
    (h : ∀ x, o = some x → Enc.size x ≤ M) : Enc.size o ≤ M + 2 := by
  cases o with
  | none => rw [size_none]; omega
  | some x => rw [size_some_eq]; have := h x rfl; omega

/-- **The two phases along a run are small**: at most `2^{16} (Y² + 4 Y + 4)` plus the sizes of
the reset states, when the envelope fields and the widths sum to at most `Y`. -/
theorem AggInv.size {B : PhaseEnv c n C} {B' : CompEnv c n C} {j : ℕ} {s : AggnAggregateState}
    (h : AggInv B B' j s) {Y : ℕ}
    (hY : phaseEnvTot B + compEnvTot B' + aggnAggregateWidth c C ≤ Y) :
    Enc.size s ≤ 1048576 * (Y * Y + 4 * Y + 4) + 4 * Enc.size aggnZeroPhase +
      4 * Enc.size (default : AggnCompareState) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hW : aggnAggregateWidth c C = aggnPhaseWidth c C + aggnCompareWidth c C := rfl
  unfold phaseEnvTot compEnvTot at hY
  have hYY1 : B.entry * B.base ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hYY2 : B'.coset * B'.base ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
  have hp : Enc.size s.1 ≤ 4096 * (Y * Y + 4 * Y + 4) + Enc.size aggnZeroPhase := by
    rcases h1 with hB | hz
    · have := hB.size
      unfold phaseEnvBound at this
      have hm : min j (aggnPhaseWidth c C) ≤ aggnPhaseWidth c C := Nat.min_le_right _ _
      have : 2 * B.entry * B.base = 2 * (B.entry * B.base) := by ring
      omega
    · rw [hz]; omega
  have hk : Enc.size s.2.1 ≤ Y + 2 := by
    rw [Small.size_nat]; have := size_le_self s.2.1; omega
  have hq : Enc.size s.2.2 ≤ 131072 * (Y * Y + 4 * Y + 4) + Enc.size (default : AggnCompareState) := by
    rcases h3 with hB | hz
    · have := hB.size
      unfold compEnvBound at this
      have : 2 * B'.coset * B'.base = 2 * (B'.coset * B'.base) := by ring
      omega
    · rw [hz]; omega
  have e0 := Combine.size_pair_le s.1 s.2
  have e1 := Combine.size_pair_le s.2.1 s.2.2
  simp only [Prod.eta] at e0 e1
  omega

/-- **The fold states of lines 5–7 along a run have size at most `2^{K (log₂ n + 2)^5}`.** The
two phases by `Explicit.AggInv.size`; the state of stretch 3 by `Explicit.l57_state_q5`, as its
header is a routine bounded at the degree of the context and of the (small) stores
(`Explicit.TN.aggnL57Hdr`); the state of the giant branch by the size of the node of
Cor. 12.0.10, polynomial in the context (`Algo.top4AggregateInput_size_bdd`). -/
theorem l57GInv_size (hc : c + 2 ≤ 5) (hb : b + 2 ≤ 5) (ht : t + 2 ≤ 5) (K0 K1 : ℕ) :
    ∃ K, ∀ n C j s, L57GInv c b t d dc dp K0 K1 n C j s → Enc.size s ≤ 2 ^ (K * lg n ^ 5) := by
  obtain ⟨Ah, bh, hH⟩ := TN.aggnL57Hdr (c := c) (b := b) (t := t) (d := d) dc dp hc hb ht
  obtain ⟨Ki, hKi, hKim, hKis⟩ := top4AggregateInput_size_bdd
  obtain ⟨Fe, hFe, hFem, hFes⟩ := polyFun_top4AutoEnter.size.exists_polyBound
  let X0 : ℕ → ℕ := fun n => 2 ^ (K0 * lg n ^ 5)
  let Y : ℕ → ℕ := fun n => 2 ^ (K1 * lg n ^ 5)
  let Z : ℕ := 4 * Enc.size aggnZeroPhase + 4 * Enc.size (default : AggnCompareState)
  let G : ℕ → ℕ := fun n => 1048576 * (Y n * Y n + 4 * Y n + 4) + Z
  let Hd : ℕ → ℕ := fun n => tsB Ah 5 bh n (2 * X0 n + 2 * G n)
  have qX0 : Q5 X0 := q5_two_pow_lg K0 5 le_rfl
  have qY : Q5 Y := q5_two_pow_lg K1 5 le_rfl
  have qG : Q5 G := ((q5_const 1048576).mul (((qY.mul qY).add ((q5_const 4).mul qY)).add
    (q5_const 4))).add (q5_const Z)
  have qHd : Q5 Hd := q5_tsB5 (((q5_const 2).mul qX0).add ((q5_const 2).mul qG)) Ah bh
  obtain ⟨ch, hch⟩ := qHd
  obtain ⟨Kad, hKad⟩ := l57_state_q5 ch
  let Nd : ℕ → ℕ := fun n => Fe (Ki (X0 n))
  have qNd : Q5 Nd := Q5.polyB hFe (Q5.polyB hKi qX0)
  let T : ℕ → ℕ := fun n => 2 * (2 * G n + 2 * (2 ^ (Kad * lg n ^ 5) + 2)) +
    2 * (2 * (top4ContextWidthBound (Nd n) + 2) + 2 * top4ContextStateBound (Nd n) + 2)
  have qT : Q5 T := ((q5_const 2).mul (((q5_const 2).mul qG).add ((q5_const 2).mul
    ((q5_two_pow_lg Kad 5 le_rfl).add (q5_const 2))))).add ((q5_const 2).mul
    ((((q5_const 2).mul ((Q5.polyB polyBound_top4ContextWidthBound qNd).add (q5_const 2))).add
      ((q5_const 2).mul (Q5.polyB polyBound_top4ContextStateBound qNd))).add (q5_const 2)))
  obtain ⟨K, hK⟩ := qT
  refine ⟨K, fun n C j s h => le_trans ?_ (hK n)⟩
  obtain ⟨hC, hs, ⟨B, B', hle, hI⟩, hst, htop⟩ := h
  have hagg : Enc.size s.1.1 ≤ G n := hI.size hle
  -- the state of stretch 3
  have hhdr : Enc.size (aggnL57Hdr c b t d dc dp (C, s.1.1)) ≤ 2 ^ (ch * lg n ^ 5) := by
    refine (hH.size n (C, s.1.1) hC.1).trans ((tsB_mono_right _ _ _ _ ?_).trans (hch n))
    have := Combine.size_pair_le C s.1.1
    have : Enc.size C ≤ X0 n := hs
    omega
  have had : Enc.size s.1.2 ≤ 2 ^ (Kad * lg n ^ 5) + 2 := size_option_le (fun st hs' => by
    obtain ⟨st', A, rfl⟩ := hst st hs'
    exact (hKad n _ (avHdrOK_aggnL57Hdr hC) hhdr).1 st' A)
  -- the state of the giant branch
  have hnode : Enc.size (aggnL57GNode c dc dp (C, s.1.1)).1.1 ≤ Nd n := by
    have e1 : Enc.size (aggnL57GNode c dc dp (C, s.1.1)) ≤
        Fe (Enc.size (top4AggregateInput (C, aggnAggregatePack c dc dp C s.1.1))) := hFes _
    have e2 := hFem _ _ (hKis C (aggnAggregatePack c dc dp C s.1.1))
    have e3 : Fe (Ki (Enc.size C)) ≤ Nd n := hFem _ _ (hKim hs)
    have e4 := size_fst_le' (aggnL57GNode c dc dp (C, s.1.1))
    have e5 := size_fst_le' (aggnL57GNode c dc dp (C, s.1.1)).1
    omega
  have htp : Enc.size s.2 ≤ 2 * (top4ContextWidthBound (Nd n) + 2) +
      2 * top4ContextStateBound (Nd n) + 2 := size_option_le (fun q hq => by
    obtain ⟨hk, j', st', A, he⟩ := htop q hq
    have hw : q.1 ≤ top4ContextWidthBound (Nd n) := by
      have := top4aWidth_context (c := 0) (d := 0) (e := 0) (f := 0) hnode l57gSolve
      rw [l57gW4_eq] at this
      exact hk.trans this
    have hs2 : Enc.size q.2 ≤ top4ContextStateBound (Nd n) := by
      rw [he]
      exact top4Stored_size_context hnode
        (top4Combine_stored ((aggnL57GNode c dc dp (C, s.1.1)).1, j', st', A))
    have e1 := Combine.size_pair_le q.1 q.2
    have e2 := size_nat_le_self q.1
    simp only [Prod.eta] at e1
    omega)
  have e1 := Combine.size_pair_le s.1 s.2
  have e2 := Combine.size_pair_le s.1.1 s.1.2
  simp only [Prod.eta] at e1 e2
  show Enc.size s ≤ 2 * (2 * G n + 2 * (2 ^ (Kad * lg n ^ 5) + 2)) +
    2 * (2 * (top4ContextWidthBound (Nd n) + 2) + 2 * top4ContextStateBound (Nd n) + 2)
  omega

end Explicit
