import Workspace.Algo.AggNodeContinuation
import Workspace.Algo.AggNodeAggregateMatch
import Workspace.Master.CosetCompose

/-! # The reject exits of lines 5–7 are the aggregate carrier itself

At the two reject exits of Sec. 15, lines 5–7 (`Babai.Line57Data.rejectCase`,
`Babai.Line57Data.rejectDefect`) the round is the two phases of Procedure
AggregateCertificates (Sec. 13.2) followed by the answer `∅`:
`Babai.Line57Shape.red` at those shapes is `aggregateRoundStrong ϕ x y E (.done ∅)`.

The degree-uniform carrier `aggnAggregateRound` of the two phases already finishes with the
empty coset. This file proves that it matches that whole reduction tree, call for call, with
the uniform RAM cost of `aggnAggregate_phases`. Which exit is taken is decided by the tests
of `aggnContinuation` (tags `0` and `5`), whose meaning is `aggnContinuation_zero_spec` and
`aggnContinuation_five_spec`.

Tag `6` (at outcome (3) of `x`, with `|D(x)| = |D(y)|`, some class of `∼` meets `y` and not
`x`, `aggnContinuation_six_classes`) is the rejection of the original's Local guide proposition
on a differing invariant. Version 2.5 has no exit there (the corrected paper,
Theorem 13.2.1 (3)). On the RAM it is the same carrier, `aggnAggregate_reject`. On the
mathematical side `Babai.Line57Shape` has no constructor for it yet: there case (3) always
aligns, and the versions of `y` are not empty, so `aggnLine57Shape_align_nil_red` does not
apply to it. A reject constructor carrying the class condition of
`aggnContinuation_six_classes` is still to be added to `Babai.Line57Shape`.
-/
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

attribute [local irreducible] Enc.size

/-- **Phases, then `∅`.** The aggregate carrier matches the two phases followed by the
answer `∅`, for every correct raw answer encoding. -/
theorem aggnAggregate_reject (c : ℕ) : ∃ dc dp : ℕ,
    Nonempty (Round.RunCostQ (aggnAggregateRound c dc dp)) ∧
    ∀ (n m : ℕ) (C : AggnPhaseCtx) (ϕ : decGroup n C.1.1.2 →* Perm (Fin m)),
      (aggnAggregateRound c dc dp).WF (C, none) → AggnPhaseCtxWF c n m C ϕ →
      LocalCertSetting (decGroup n C.1.1.2) ϕ →
      LargeK C.2.2.2.length (Nat.card (Fin n)) → 10 * C.2.2.2.length ≤ m →
      RawStr.WF n (2 * n) C.2.1 → RawStr.WF n (2 * n) C.2.2.1 →
      LoopMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))) (.done ∅)) := by
  obtain ⟨dc, dp, hrc, hph⟩ := aggnAggregate_phases c
  refine ⟨dc, dp, hrc, ?_⟩
  intro n m C ϕ hI hC hset ht htm hx hy
  have hP := hph n m C ϕ hI hC hset ht htm hx hy
  have hB := phaseMatch_bind (k := fun _ => (.done ∅ : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))))
    (P' := fun (b : Set (Perm (Fin n))) (_ : ℕ) (v : AggnAggregateState) =>
      b = ∅ ∧ v.1.1 = [] ∧ v.2.2.1 = []) hP (by
      rintro _ j v ⟨h1, _, h2, _⟩
      exact phaseMatch_done ⟨rfl, h1, h2⟩)
  have he : (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ())).bind (fun _ => (.done ∅ : SIReduction (Fin n) ℕ (Set (Perm (Fin n))))) =
      aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
      (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1) ((aggnPhaseRows c C).map (winSet m)))
      (.done ∅) := by
    simp only [aggregateRoundStrong, SIReduction.bind_assoc]
    rfl
  rw [he] at hB
  refine loopMatch_of_phaseMatch hB ?_ (by omega)
  rintro b j' v ⟨rfl, h1, h2⟩
  exact ⟨aggnAggregateChild_done c (C, none) j' v h1 h2, rfl⟩

/-- §15, lines 5–7, **the reject exit of outcome (2b) on the RAM**: under the test of
`Babai.Line57Data.rejectCase` (computed as tag `0` of `aggnContinuation`), the aggregate
carrier matches the mathematical round `Babai.Line57Shape.red` of that exit exactly. -/
theorem aggnAggregate_rejectCase_match {c dc dp n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hmatch : LoopMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))) (.done ∅)))
    (hx : Case2 (bigFGamma ϕ (decStrN n C.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.1) C.2.2.2.length)
    (hy : ¬ (Case2 (bigFGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length) ∧
      ¬ AggregateCase2a ϕ (decStrN n C.2.2.1) C.2.2.2.length)) :
    LoopMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        ((Line57Shape.rejectCase (ϕ := ϕ) (ts := C.2.2.2.length) hx hy).red
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m)))) :=
  hmatch

/-- §15, lines 5–7, **the reject exit of outcome (3) on the RAM**: under the test of
`Babai.Line57Data.rejectDefect` (computed as tag `5` of `aggnContinuation`), the aggregate
carrier matches the mathematical round of that exit exactly. -/
theorem aggnAggregate_rejectDefect_match {c dc dp n m : ℕ} {C : AggnPhaseCtx}
    {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)}
    (hmatch : LoopMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        (aggregateRoundStrong ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m))) (.done ∅)))
    (hne : (fixedGamma ϕ (decStrN n C.2.2.1) C.2.2.2.length).ncard ≠
      (fixedGamma ϕ (decStrN n C.2.1) C.2.2.2.length).ncard) :
    LoopMatch (aggnAggregateRound c dc dp) (aggnPhaseDecode n) (decCoset n) (C, none)
        (aggnAggregateWidth c C) 0 ((aggnAggregateRound c dc dp).init (C, none))
        ((Line57Shape.rejectDefect (ϕ := ϕ) (ts := C.2.2.2.length) hne).red
          (aggnFullEnum ϕ (decStrN n C.2.1) (decStrN n C.2.2.1)
            ((aggnPhaseRows c C).map (winSet m)))) :=
  hmatch

/-- An Align round with no version of `y` is the answer `∅` with no call, so the round of
lines 5–7 is again the two phases followed by `∅`. (This is the case where Theorem 9.2.3
returns no version of `y`; it is not tag `6`, see the module note.) -/
theorem aggnLine57Shape_align_nil_red {W : Type} [Fintype W] [DecidableEq W] {A : Type}
    {G : Subgroup (Perm W)} {x y : W → A} {m : ℕ} {ϕ : G →* Perm (Fin m)} {ts : ℕ}
    (S : AlignShape W A G x y) (hS : S.versions = []) (E : AggEnum W (Fin m)) :
    (Line57Shape.align (ϕ := ϕ) (ts := ts) S).red E = aggregateRoundStrong ϕ x y E (.done ∅) := by
  change aggregateRoundStrong ϕ x y E S.red = _
  congr 1
  letI := S.act
  change (cosetDesignAlign S.ϕ x y S.X' S.versions (S.head :: S.tail)).expand _ = _
  rw [hS]
  rfl

end Algo
