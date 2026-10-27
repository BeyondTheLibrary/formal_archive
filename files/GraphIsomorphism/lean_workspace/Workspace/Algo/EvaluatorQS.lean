/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: the evaluator of a round whose well-formedness test is only sound.
-/
import Workspace.Algo.RoundQS
import Workspace.Algo.EvaluatorQ

/-!
# The evaluator with a sound well-formedness test

`Workspace/Algo/EvaluatorQ.lean` packages the depth-first evaluator as a
`RAM.QuasiPolyFun` from a `Algo.Round.RunCostQ`, whose test decides well-formedness.
`Workspace/Algo/RoundQS.lean` explains why the master round of Sec. 15 has only a **sound**
test.  This file repeats the packaging from a `Algo.Round.RunCostQS`.

## The one trick that avoids copying

`Algo.Round.quasiFun_stepDFS` and `Algo.Round.quasiPolyBound_statePolyQ` take a
`Algo.Round.RunCostQ`, but neither of them looks at the test: the first assembles the four
routines of the round, the second adds up three bounds.  To reuse them, note that a round may
always be *re-read with no well-formed instance at all*: `Algo.Round.qsVoid` is the round `R`
with `WF` replaced by `False`, which satisfies the four laws vacuously, and which carries a
full `Algo.Round.RunCostQ` — with the test `fun _ => false`, which is both sound and
complete for `False`.  Its `stepDFS` is `R.stepDFS` on the nose
(`Algo.Round.qsVoid_stepDFS`), and its bounds are the bounds of the given cost datum, so the
two lemmas transfer.  What genuinely needs the well-formedness of the root — the size
invariant along a run — is in `Workspace/Algo/RoundQS.lean`.

## Main results

* `Algo.Round.quasiFun_stepDFSQS` — one step is a routine;
* `Algo.Round.size_iterateQS_le` — every state of a run is quasipolynomially small;
* `Algo.Round.quasiPolyFun_runQS` — **the evaluator is a `RAM.QuasiPolyFun`**;
* `Algo.Round.runQS_eq_answer` — and it returns the answer of the instance, **at an instance
  that passes the test**;
* `Algo.siWorkspaceRoutine_of_normQS_run` — one such round gives `RAM.SIWorkspaceRoutine`.

No axiom, no `sorry`.
-/

universe u v

namespace Algo

open RAM Babai

variable {ι ω α : Type*}

namespace Round

variable [Enc ι] [Enc ω] [Enc α] (R : Round ι ω α)

/-! ## The round re-read with no well-formed instance

Nothing is claimed about `Algo.Round.qsVoid` beyond the two transfers below.  Its `WF` is
`False`, so every clause of `Algo.Round.CostQ` that has a well-formedness hypothesis holds
vacuously, and its own run answers `none` everywhere — which is why it is used only for
statements that do not mention a run. -/

/-- **The round with no well-formed instance.**  Same routines, same bounds, `WF := False`. -/
def qsVoid : Round ι ω α where
  WF := fun _ => False
  ground := R.ground
  measure := R.measure
  width := R.width
  child := R.child
  init := R.init
  combine := R.combine
  finish := R.finish
  bot := R.bot
  child_eq_none := R.child_eq_none
  child_wf := fun _ _ _ _ h _ => h.elim
  child_measure := fun _ _ _ _ h _ => h.elim
  child_ground := fun _ _ _ _ h _ => h.elim

omit [Enc ι] [Enc ω] [Enc α] in
/-- **The two rounds take the same step.** -/
theorem qsVoid_stepDFS : R.qsVoid.stepDFS = R.stepDFS := by
  funext x
  obtain ⟨st, ret⟩ := x
  cases st with
  | nil => rfl
  | cons fr rest =>
    obtain ⟨I, j, s⟩ := fr
    cases ret with
    | some a => rfl
    | none => rfl

/-- **The cost datum of the void reading.**  Every size clause is vacuous, and the test is
`fun _ => false`, which decides `False`. -/
def qsVoidCost (C : RunCostQS R) : RunCostQ R.qsVoid where
  bound := C.bound
  polyBound_bound := C.polyBound_bound
  mono_bound := C.mono_bound
  stateBound := C.stateBound
  quasiPolyBound_stateBound := C.quasiPolyBound_stateBound
  mono_stateBound := C.mono_stateBound
  widthBound := C.widthBound
  quasiPolyBound_widthBound := C.quasiPolyBound_widthBound
  quasiFun_child := C.quasiFun_child
  quasiFun_init := C.quasiFun_init
  quasiFun_combine := C.quasiFun_combine
  quasiFun_finish := C.quasiFun_finish
  ground_le := C.ground_le
  size_le := fun _ h => h.elim
  init_le := fun _ h => h.elim
  combine_le := fun _ _ _ _ h _ _ => h.elim
  finish_le := fun _ _ h _ => h.elim
  bot_le := C.bot_le
  width_le := fun _ h => h.elim
  polyFun_ground := C.polyFun_ground
  wfCheck := fun _ => false
  polyFun_wfCheck := polyFun_const false
  wfCheck_eq_true := fun _ => ⟨fun h => Bool.noConfusion h, fun h => h.elim⟩
  measureBound := C.measureBound
  polyBound_measureBound := C.polyBound_measureBound
  mono_measureBound := C.mono_measureBound
  measure_le := fun _ h => h.elim

/-- **One step of the evaluator is a machine routine.** -/
theorem quasiFun_stepDFSQS (C : RunCostQS R) : QuasiFun R.stepDFS := by
  rw [← R.qsVoid_stepDFS]
  exact R.qsVoid.quasiFun_stepDFS (R.qsVoidCost C)

/-! ## The size of every state of a run -/

/-- The quasipolynomial that bounds every state of a run.  `S` is the size of the start
state.  Word for word `Algo.Round.statePolyQ`. -/
def statePolyQS (C : RunCostQS R) (c : ℕ) (S : ℕ → ℕ) (N : ℕ) : ℕ :=
  S N + (2 * (1 + (C.measureBound N + 1)
      * (2 * (2 * C.bound N + 4 * C.stateBound N
          + 4 * (30 * (N + 1) ^ (c + 2) + 3) + 8) + 1))
    + 2 * (C.bound N + 2))

theorem statePolyQS_eq (C : RunCostQS R) (c : ℕ) (S : ℕ → ℕ) :
    R.statePolyQS C c S = R.qsVoid.statePolyQ (R.qsVoidCost C) c S := rfl

theorem quasiPolyBound_statePolyQS (C : RunCostQS R) (c : ℕ) (S : ℕ → ℕ)
    (hS : QuasiPolyBound S) : QuasiPolyBound (R.statePolyQS C c S) := by
  rw [statePolyQS_eq]
  exact R.qsVoid.quasiPolyBound_statePolyQ (R.qsVoidCost C) c S hS

/-- **Every state of a run is quasipolynomially small.**  The proof of
`Algo.Round.size_iterateQ_le`, with the case split made on the **test** rather than on
well-formedness: an instance that passes the test is well formed by soundness, and an
instance that fails it is not run at all. -/
theorem size_iterateQS_le (C : RunCostQS R) (c : ℕ) (S : ℕ → ℕ)
    (hS : ∀ I : ι, Enc.size (R.startState I) ≤ S (Enc.size I))
    (I : ι) (j : ℕ) (hj : j ≤ R.stepCountQS C c I) :
    Enc.size ((R.stepDFS)^[j] (R.startState I)) ≤ R.statePolyQS C c S (Enc.size I) := by
  by_cases hchk : C.wfCheck I = true
  · have hwf : R.WF I := C.wfCheck_sound I hchk
    have hn : R.ground I ≤ Enc.size I := C.ground_le I
    have hcount : R.stepCountQS C c I = roundCount c (R.ground I) := by
      rw [stepCountQS, if_pos hchk]
    have hok := R.stateOkQS_iterate C I hwf j
    have hlen := R.length_iterate_le I hwf j
    have hD : ((R.stepDFS)^[j] (R.startState I)).1.length
        ≤ C.measureBound (Enc.size I) + 1 :=
      le_trans hlen (by
        have := C.measure_le I hwf
        have h2 : C.measureBound (R.ground I) ≤ C.measureBound (Enc.size I) :=
          C.mono_measureBound hn
        omega)
    have hmain := R.size_stateQS_le C (R.ground I) j (C.measureBound (Enc.size I) + 1) _ hok hD
    have hjsize : Nat.size j ≤ 30 * (Enc.size I + 1) ^ (c + 2) + 3 := by
      have h1 : j ≤ roundCount c (R.ground I) := by rw [hcount] at hj; exact hj
      have h2 : Nat.size j ≤ Nat.size (roundCount c (R.ground I)) := Nat.size_le_size h1
      have h3 := size_roundCount_le c (R.ground I)
      have h4 : Nat.log 2 (R.ground I) + 2 ≤ Enc.size I + 1 := by
        rcases Nat.eq_zero_or_pos (R.ground I) with hg | hg
        · have := one_le_size I
          simp [hg]
          omega
        · have := Nat.log_lt_self 2 (Nat.pos_iff_ne_zero.1 hg)
          omega
      have h5 : (Nat.log 2 (R.ground I) + 2) ^ (c + 2) ≤ (Enc.size I + 1) ^ (c + 2) :=
        Nat.pow_le_pow_left h4 _
      omega
    have hb : C.bound (R.ground I) ≤ C.bound (Enc.size I) := C.mono_bound hn
    have hsb : C.stateBound (R.ground I) ≤ C.stateBound (Enc.size I) := C.mono_stateBound hn
    have hmono : 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (R.ground I) + 4 * C.stateBound (R.ground I)
              + 4 * Nat.size j + 8) + 1)) + 2 * (C.bound (R.ground I) + 2)
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := by
      have := Nat.mul_le_mul_left (C.measureBound (Enc.size I) + 1)
        (show 2 * (2 * C.bound (R.ground I) + 4 * C.stateBound (R.ground I)
            + 4 * Nat.size j + 8) + 1
          ≤ 2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
            + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1 by omega)
      omega
    have : Enc.size ((R.stepDFS)^[j] (R.startState I))
        ≤ 2 * (1 + (C.measureBound (Enc.size I) + 1)
          * (2 * (2 * C.bound (Enc.size I) + 4 * C.stateBound (Enc.size I)
              + 4 * (30 * (Enc.size I + 1) ^ (c + 2) + 3) + 8) + 1))
            + 2 * (C.bound (Enc.size I) + 2) := le_trans hmain hmono
    rw [statePolyQS]
    omega
  · have hcount : R.stepCountQS C c I = 0 := by
      rw [stepCountQS, if_neg hchk]
    have hj0 : j = 0 := by omega
    subst hj0
    have := hS I
    rw [statePolyQS]
    simpa using le_trans this (by omega)

/-! ## The routine -/

/-- **The evaluator is a machine routine of the quasipolynomially large class.** -/
theorem quasiFun_runQS (C : RunCostQS R) (c : ℕ) : QuasiFun (R.runQS C c) := by
  have hstart : QuasiFun R.startState := by
    have hframe : QuasiFun (fun I : ι => ((I, 0, R.init I) : Frame ι ω)) :=
      polyFun_id.quasiFun.pair ((polyFun_const 0).quasiFun.pair C.quasiFun_init)
    have hlist : QuasiFun (fun I : ι => [((I, 0, R.init I) : Frame ι ω)]) :=
      (hframe.pair (polyFun_const _).quasiFun).comp polyFun_cons.quasiFun
    exact (hlist.pair (polyFun_const _).quasiFun).of_eq (fun _ => rfl)
  obtain ⟨S, hSb, hSmono, hSle⟩ := hstart.size.exists_quasiPolyBound
  have hcount : PolyFun (R.stepCountQS C c) := by
    refine (PolyFun.ite C.polyFun_wfCheck
      (C.polyFun_ground.comp (polyFun_roundCount c)) (polyFun_const 0)).of_eq (fun _ => rfl)
  have hq : ∀ I : ι, R.stepCountQS C c I ≤ roundCount c (Enc.size I) := by
    intro I
    rw [stepCountQS]
    by_cases h : C.wfCheck I
    · rw [if_pos h]
      exact roundCount_mono c (C.ground_le I)
    · rw [if_neg h]
      exact Nat.zero_le _
  refine QuasiFun.iterateSetup (setUp := fun I => (R.stepCountQS C c I, R.startState I))
    (step := R.stepDFS) (readOff := Prod.snd) (q := fun n => roundCount c n)
    (p := R.statePolyQS C c S) (hcount.quasiFun.pair hstart) ?_
    polyFun_snd.quasiFun hq (quasiPolyBound_roundCount c) ?_
    (R.quasiPolyBound_statePolyQS C c S hSb)
  · exact ((polyFun_fst.sub (polyFun_const 1)).quasiFun.pair
      (polyFun_snd.quasiFun.comp (R.quasiFun_stepDFSQS C))).of_eq (fun x => by
        obtain ⟨k, y⟩ := x
        rfl)
  · exact fun I j hj => R.size_iterateQS_le C c S hSle I j hj

/-- **The answer of the routine is polynomially small.** -/
theorem size_runQS_le (C : RunCostQS R) (c : ℕ) (I : ι) :
    Enc.size (R.runQS C c I) ≤ C.bound (Enc.size I) + 2 := by
  by_cases hchk : C.wfCheck I = true
  · have hwf : R.WF I := C.wfCheck_sound I hchk
    have hok := R.stateOkQS_iterate C I hwf (R.stepCountQS C c I)
    cases hx : ((R.stepDFS)^[R.stepCountQS C c I] (R.startState I)).2 with
    | none =>
      have : R.runQS C c I = none := hx
      rw [this, size_none_eq]
      omega
    | some a =>
      have hrun : R.runQS C c I = some a := hx
      have hle : Enc.size a ≤ C.bound (R.ground I) :=
        R.retOkQS_le C (R.ground I) _ _ hok a hx
      have hb : C.bound (R.ground I) ≤ C.bound (Enc.size I) := C.mono_bound (C.ground_le I)
      rw [hrun, size_some_eq]
      omega
  · have hcount : R.stepCountQS C c I = 0 := by
      rw [stepCountQS, if_neg hchk]
    have : R.runQS C c I = none := by rw [runQS, hcount]; rfl
    rw [this, size_none_eq]
    omega

theorem sizeBound_runQS (C : RunCostQS R) (c : ℕ) : SizeBound (R.runQS C c) := by
  obtain ⟨k, d, hkd⟩ := C.polyBound_bound
  refine ⟨k + 2, d, fun I => ?_⟩
  have h1 := R.size_runQS_le C c I
  have h2 := hkd (Enc.size I)
  have h3 : (1 : ℕ) ≤ (Enc.size I + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have h4 : (k + 2) * (Enc.size I + 1) ^ d
      = k * (Enc.size I + 1) ^ d + 2 * (Enc.size I + 1) ^ d := by ring
  omega

/-- **The evaluator is a `RAM.QuasiPolyFun`**: quasipolynomial time, polynomially small
answer. -/
theorem quasiPolyFun_runQS (C : RunCostQS R) (c : ℕ) : QuasiPolyFun (R.runQS C c) :=
  (R.quasiFun_runQS C c).quasiPolyFun (R.sizeBound_runQS C c)

/-! ### The answer of the routine -/

/-- The answer of the routine, with the two `Option`s merged. -/
def runAnswerQS {β : Type*} [Enc β] (R : Round ι ω (Option β)) (C : RunCostQS R) (c : ℕ)
    (I : ι) : Option β := (R.runQS C c I).join

theorem quasiPolyFun_runAnswerQS {β : Type*} [Enc β] (R : Round ι ω (Option β))
    (C : RunCostQS R) (c : ℕ) : QuasiPolyFun (R.runAnswerQS C c) :=
  (R.quasiPolyFun_runQS C c).comp_poly polyFun_join

/-! ## The evaluator against the mathematical layer -/

variable {Ω : Type u} {A : Type v}

/-- **The routine answers the instance.**  `Algo.Round.runQ_eq_answer` with one hypothesis
added: the instance **passes the test**.  With a test that only has to be sound, that is no
longer a consequence of `R.WF I`, and it is what the final theorem supplies at its root
(`Algo.wftRootCheck_rawNormSI_rawOfSI`). -/
theorem runQS_eq_answer {κ : Type*} (C : RunCostQS R) {decI : ι → κ}
    {decA : α → Set (Equiv.Perm Ω)} (M : MasterStep Ω A κ)
    (himpl : Implements R decI M.inst decA M.step)
    (hgrp : ∀ I : ι, R.WF I → IsGroupInstance (M.inst (decI I)))
    (hrank : ∀ I : ι, R.WF I → M.rank (decI I) ≤ R.measure I)
    (hlift : ∀ (f : ℕ) (I J : ι), R.WF I → J ∈ R.roundCalls f I →
      decI J = M.lift (decI I) (M.inst (decI J)))
    (hmono : Monotone M.roundCost) (c₁ : ℕ)
    (hq : ∀ n : ℕ, M.roundCost n ≤ 2 ^ ((Nat.log 2 n + 2) ^ c₁))
    (hwin : ∀ I : ι, R.WF I → (M.inst (decI I)).windowSize ≤ R.ground I)
    (f : ℕ) (I : ι) (hI : C.wfCheck I = true) (hf : R.measure I < f) :
    ∃ a : α, R.runQS C c₁ I = some a ∧ decA a = (M.inst (decI I)).answer := by
  have hwf : R.WF I := C.wfCheck_sound I hI
  have hle : 3 * 2 ^ (30 * (Nat.log 2 (M.inst (decI I)).windowSize + 2) ^ (c₁ + 2)) + 1
      ≤ roundCount c₁ (R.ground I) := by
    have := roundCount_mono c₁ (hwin I hwf)
    simpa [roundCount] using this
  obtain ⟨a, ha, hdec⟩ :=
    evaluate_eq_answer R M himpl hgrp hrank hlift hmono c₁ hq f
      (roundCount c₁ (R.ground I)) I hwf hf hle
  exact ⟨a, by rw [R.runQS_eq_evaluate C c₁ I hI]; exact ha, hdec⟩

/-! ## The routine is not vacuous -/

/-- **The sound-test evaluator is a `RAM.QuasiPolyFun` on a round that really recurses.** -/
theorem quasiPolyFun_testRunQS (c : ℕ) :
    QuasiPolyFun (testRound.runQS testRunCostQS c) :=
  testRound.quasiPolyFun_runQS testRunCostQS c

end Round

/-! ## The bridge to the final obligation

`Algo.siWorkspaceRoutine_of_normQ_run` (`Workspace/Algo/EvaluatorQ.lean`) with
`Algo.Round.RunCostQ` replaced by `Algo.Round.RunCostQS`.  It is the same proof: all it uses
of the cost datum is `RAM.QuasiPolyFun (R.runAnswerQS …)`, which
`Algo.Round.quasiPolyFun_runAnswerQS` supplies.  The test appears nowhere in it, because the
caller has already used `Algo.Round.runQS_eq_answer` to build `hdec`, and that is where the
hypothesis "the root passes the test" is discharged. -/

section Bridge

variable {ω : Type*} [Enc ω]

/-- **One round with a sound well-formedness test gives the final obligation.** -/
theorem siWorkspaceRoutine_of_normQS_run (R : Round RawSI ω RawCoset)
    (C : Round.RunCostQS R) (c : ℕ) (norm : RawSI → RawSI) (hnorm : PolyFun norm)
    (hdec : ∀ (n s : ℕ) (a : Targets.SIInput n s),
      ∃ b : Option (List (Equiv.Perm (Fin n)) × Equiv.Perm (Fin n)),
        Enc.encode b = Enc.encode (R.runAnswerQS C c (norm (rawOfSI a))) ∧
          Targets.SIRel n s a b) : SIWorkspaceRoutine := by
  have hrun := hnorm.comp_quasi (R.quasiPolyFun_runAnswerQS C c)
  obtain ⟨P, T, hT, hP⟩ := hrun.time
  obtain ⟨S, hSb, hSmono, hSle⟩ := hrun.size.exists_polyBound
  refine ⟨P, T, S, hT, hSb, hSmono, fun n s => ?_⟩
  refine CleanSolveAt.transfer (e := rawOfSI)
    (R' := fun (r : RawSI) (b' : RawCoset) =>
      b' = R.runAnswerQS C c (norm r) ∧ Enc.size b' ≤ S (Enc.size r))
    (fun a => (encode_si_eq a).symm) ?_
    (fun r => ⟨R.runAnswerQS C c (norm r), ⟨rfl, hSle r⟩, hP r⟩)
  intro a b' hb'
  obtain ⟨b, hbenc, hbrel⟩ := hdec n s a
  have hbb : Enc.encode b = Enc.encode b' := by rw [hbenc, hb'.1]
  have hsize : Enc.size b ≤ S (Enc.size a) := by
    have h1 : Enc.size b = Enc.size b' := size_eq_of_encode_eq hbb
    have h2 : Enc.size (rawOfSI a) = Enc.size a :=
      size_eq_of_encode_eq (encode_si_eq a).symm
    rw [h1, ← h2]
    exact hb'.2
  exact ⟨b, hbb, hbrel, hsize⟩

end Bridge

end Algo

#print axioms Algo.Round.quasiPolyFun_runQS
#print axioms Algo.Round.runQS_eq_answer
#print axioms Algo.siWorkspaceRoutine_of_normQS_run
