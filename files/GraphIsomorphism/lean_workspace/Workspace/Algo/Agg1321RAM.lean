/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Theorem 13.2.1 as one RAM routine with the bound `m^{O(t)}`.
-/
import Workspace.Algo.Agg1321Spec

/-!
# Theorem 13.2.1 on the RAM

`Algo.theorem_13_2_1_ram` runs all of Procedure AggregateCertificates (§13.2) as one RAM
program: the enumeration of the test sets, the preparation of the `2·C(m,t)` certificate
runs and the `2·C(m,t)²` comparison runs, the two phases, the stores and the comparison
table, the tuple tables of case (3), and the case analysis (1), (2a), (2b), (3). Its output is
`Algo.a13Result`, whose meaning is `Algo.a13Result_eq` with the lemmas of
`Workspace/Algo/Agg1321Spec.lean`.

As in §13.1, the String Isomorphism calls are counted apart from the rest (a call bound plus
a step bound). The routine runs within

  `10¹² · ∑_{W ∈ calls} τ(W) + (m + 1)^{d·t} · poly(size of the input)`

steps, where `τ(W)` is the cost of the call `W`; the calls are `Algo.a13Calls`, at most
`Babai.aggregateRoundCost m t n` of them, each on a window of at most `n/t` points
(`Algo.a13_calls`). This is the paper's "at a multiplicative cost of `m^{O(t)}`": both the
number of calls and the work outside the calls are `m^{O(t)}` times a polynomial in the
input.

No bound on `t` beyond the theorem's hypothesis `t < m/10` is used: the Master chain's
restriction `t ≤ (log n + 1)^c` is not needed, because the tuple tables are built by
`Algo.exists_tuplesProg` at cost `(t + 2)·poly((m + 1)^t · size)` for every `t`.

The tuple tables on `D(x)`, `[|D(x)|]` and `[|D(y)|]` of case (3) are built in every run,
also when the case analysis ends in another case; their cost is within the same bound.
-/

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

namespace Algo
open RAM RAM.Targets Babai
open Equiv (Perm)

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

/-! ### Size bounds of the tuple tables -/

/-- A bound on the size of a table of `k`-tuples: `Y` bounds `k` and the number of tuples,
`Z` bounds the size of the domain list. -/
def a13TS (Z Y : ℕ) : ℕ := 1 + Y * (2 * (1 + Y * (2 * Z + 1)) + 1)

/-- A bound on `Algo.tuplesBound`, in the same terms. -/
def a13TB (Z Y : ℕ) : ℕ := 2 * Z + 2 * a13TS Z Y

theorem polyBound_a13TS {g : ℕ → ℕ} (hg : PolyBound g) :
    PolyBound (fun Y => a13TS (g Y) Y) := by
  unfold a13TS
  exact (polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul
    ((polyBound_const 1).add (polyBound_id.mul (((polyBound_const 2).mul hg).add
      (polyBound_const 1))))).add (polyBound_const 1)))

theorem polyBound_a13TB {g : ℕ → ℕ} (hg : PolyBound g) :
    PolyBound (fun Y => a13TB (g Y) Y) := by
  unfold a13TB
  exact ((polyBound_const 2).mul hg).add ((polyBound_const 2).mul (polyBound_a13TS hg))

theorem size_tuplesOf_le_TS {dom : List ℕ} {k Y Z : ℕ} (hL : dom.length ^ k ≤ Y) (hk : k ≤ Y)
    (hZ : Enc.size dom ≤ Z) : Enc.size (tuplesOf dom k) ≤ a13TS Z Y := by
  refine (size_tuplesOf_le dom k).trans ?_
  unfold a13TS
  gcongr

theorem tuplesBound_le_TB {L X k Y Z : ℕ} (hL : (L + 1) ^ k ≤ Y) (hk : k ≤ Y) (hX : X ≤ Z) :
    tuplesBound L X k ≤ a13TB Z Y := by
  unfold tuplesBound a13TB a13TS
  gcongr

/-- The final conversion: a polynomial in `(M + 1)^t · (S + 1)` is `(M + 1)^{O(t)}` times a
polynomial in `S`. -/
theorem pw_conv (c d M t S : ℕ) :
    pw c d ((M + 1) ^ t * (S + 1)) ≤ (M + 1) ^ (d * t) * pw (c * 2 ^ d) d S := by
  unfold pw
  have h1 : 1 ≤ (M + 1) ^ t := Nat.one_le_pow _ _ (by omega)
  have h2 : (M + 1) ^ t * (S + 1) + 1 ≤ (M + 1) ^ t * (2 * (S + 1)) := by nlinarith
  have h3 : ((M + 1) ^ t * (S + 1) + 1) ^ d ≤ ((M + 1) ^ t * (2 * (S + 1))) ^ d :=
    Nat.pow_le_pow_left h2 d
  calc c * ((M + 1) ^ t * (S + 1) + 1) ^ d ≤ c * ((M + 1) ^ t * (2 * (S + 1))) ^ d :=
        Nat.mul_le_mul_left _ h3
    _ = (M + 1) ^ (d * t) * (c * 2 ^ d * (S + 1) ^ d) := by
        rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm t d]; ring

/-- `D(z)` is a sublist of `[m]`. -/
theorem length_aggnFixed_le (z : AggnPhaseCtx × AggnAggregateState) (b : Bool) :
    (aggnAggregateData (z, b)).2.2.length ≤ z.1.1.2.1.length := by
  simp only [aggnAggregateData, aggFixedGamma, aggFixed]
  exact (List.length_filter_le _ _).trans (by simp)

/-! ### Stages -/

theorem exists_polyStage {α β : Type*} [Enc α] [Enc β] [Inhabited α] {f : α → β}
    (hf : PolyFun f) :
    ∃ (P : Program) (c d : ℕ), Wf P ∧ ∀ a, RunsOn 16 P a (f a) (pw c d (Enc.size a)) ∧
      Enc.size (f a) ≤ pw c d (Enc.size a) := by
  obtain ⟨P, c, d, hP, hs⟩ := polyFun_witness hf
  exact ⟨P, c, d, CleanComputeAt.wf' hP, fun a => ⟨hP.runsOn a, hs a⟩⟩

/-- Run one program on each component of a pair. -/
theorem exists_bothStage {α β : Type} [Enc α] [Enc β] [Inhabited α] [Inhabited β] :
    ∃ (Pf Ps : Program) (c d : ℕ), Wf Pf ∧ Wf Ps ∧
      ∀ {γ δ : Type} [Enc γ] [Enc δ] (P1 P2 : Program) (a : α × β) (b1 : γ) (b2 : δ)
        (T1 T2 : ℕ), RunsOn 16 P1 a.1 b1 T1 → RunsOn 16 P2 a.2 b2 T2 →
        RunsOn 16 (Pairing.pairProg 16 (RAM.seq Pf P1) (RAM.seq Ps P2)) a (b1, b2)
          (19 * Enc.size a + 19 * Enc.size b1 + 19 * Enc.size b2 + 10 * T1 + 10 * T2
            + 20 * pw c d (Enc.size a) + 376) := by
  obtain ⟨Pf, cf, df, hf, hrf⟩ := exists_polyStage (polyFun_fst : PolyFun (fun a : α × β => a.1))
  obtain ⟨Ps, cs, ds, hs, hrs⟩ := exists_polyStage (polyFun_snd : PolyFun (fun a : α × β => a.2))
  refine ⟨Pf, Ps, cf + cs, df + ds, hf, hs, ?_⟩
  intro γ δ _ _ P1 P2 a b1 b2 T1 T2 h1 h2
  have r := RunsOn.pair (K := 16) (by omega) ((hrf a).1.seq h1) ((hrs a).1.seq h2)
  refine r.mono ?_
  have e1 : pw cf df (Enc.size a) ≤ pw (cf + cs) (df + ds) (Enc.size a) :=
    Round.pw_le_pw (by omega) (by omega)
  have e2 : pw cs ds (Enc.size a) ≤ pw (cf + cs) (df + ds) (Enc.size a) :=
    Round.pw_le_pw (by omega) (by omega)
  omega

/-! ### The routine -/

/-- **Theorem 13.2.1** (AggregateCertificates, §13.2) **on the RAM**.

> Let `ϕ : G → S(Γ)` be a giant representation, where `G ≤ S(Ω)`, `|Ω| = n`, and `|Γ| = m`.
> Let `max{8, 2 + log₂ n} < t < m/10`. Then, at a multiplicative cost of `m^{O(t)}`, we can
> either find a canonical colored 4/5-partition of `Γ` or find a canonically embedded `t`-ary
> relational structure with relative symmetry defect `≥ 1/2` on `Γ`, or reduce the
> determination of `Iso_G(x,y)` to `n^{O(1)}` instances of size `≤ 2n/3`.

One program transformer `F`: for every program `Q` that answers String Isomorphism on the
well-formed windows (with answers of size at most `S` of the input), `F Q` computes
`Algo.a13Result ansQ C`, the output of the routine (its meaning: `Algo.a13Result_eq` and the
lemmas `Algo.a13_tag_one` … `Algo.a13_tag_four`), within

  `10¹² · ∑_{W ∈ a13Calls} τ(W) + (m + 1)^{d·t} · pw c d (size C)`

steps. The calls number at most `Babai.aggregateRoundCost m t n ≤ m^{O(t)}·n²`, all on
windows of at most `n/t` points (`Algo.a13_calls`). -/
theorem theorem_13_2_1_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ {n m : ℕ} {C : AggnPhaseCtx} {ϕ : decGroup n C.1.1.2 →* Perm (Fin m)},
        A13Hyp n m C ϕ → ∀ (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ),
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W) ∧
          decCoset n (ansQ W) = (decWinSI n W).answer) →
        RunsOn 16 (F Q) C (a13Result ansQ C)
          (10 ^ 12 * ((a13Calls ansQ C).map τ).sum
            + (m + 1) ^ (d * C.2.2.2.length) * pw c d (Enc.size C)) := by
  -- the programs
  obtain ⟨Pid, ci, di, hPid, hrid⟩ :=
    exists_polyStage (polyFun_id : PolyFun (fun C : AggnPhaseCtx => C))
  have hprepF : PolyFun (fun C : AggnPhaseCtx =>
      ((List.range C.1.2.1.length, C.2.2.2.length) : List ℕ × ℕ)) :=
    ((pfst (psnd (pfst polyFun_id))).comp polyFun_rangeLength).pair
      ((psnd (psnd (psnd polyFun_id))).comp polyFun_length)
  obtain ⟨Pp, cp, dp, hPp, hrp⟩ := exists_polyStage hprepF
  obtain ⟨Pt, ct, dt, hPt, hrt⟩ := exists_tuplesProg
  obtain ⟨P2, c2, d2, hP2, hr2⟩ := exists_polyStage polyFun_a13Prepare
  obtain ⟨Fph, cph, dph, hFph⟩ := theorem_13_2_1_phases_ram S hS
  obtain ⟨Pidx, cx, dx, hPidx, hrx⟩ :=
    exists_polyStage (polyFun_id : PolyFun (fun X : A13Ctx => X))
  obtain ⟨Pf3, Ps3, cb3, db3, hPf3, hPs3, hb3⟩ :=
    exists_bothStage (α := A13Ctx) (β := List RawLCLoop × List RawPCLoop)
  obtain ⟨co1, do1, hso1⟩ := exists_size_lcOut_le
  obtain ⟨P4, c4, d4, hP4, hr4⟩ := exists_polyStage polyFun_a13Collect
  obtain ⟨PfI, PsI, cbI, dbI, hPfI, hPsI, hbI⟩ :=
    exists_bothStage (α := List ℕ × ℕ) (β := List ℕ × ℕ)
  obtain ⟨PfO, PsO, cbO, dbO, hPfO, hPsO, hbO⟩ :=
    exists_bothStage (α := List ℕ × ℕ) (β := (List ℕ × ℕ) × (List ℕ × ℕ))
  obtain ⟨Pidy, cy, dy, hPidy, hry⟩ :=
    exists_polyStage (polyFun_id : PolyFun (fun X : AggnGuidePrepareInput => X))
  obtain ⟨Pf5, Ps5, cb5, db5, hPf5, hPs5, hb5⟩ :=
    exists_bothStage (α := AggnGuidePrepareInput)
      (β := (List ℕ × ℕ) × ((List ℕ × ℕ) × (List ℕ × ℕ)))
  obtain ⟨P6, c6, d6, hP6, hr6⟩ := exists_polyStage polyFun_a13Final
  -- the bounds, as functions of `Y = (m + 1)^t · (size C + 1)`
  obtain ⟨B1, hB1⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = pw cp dp Y := ⟨_, fun _ => rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 38 * Y + 19 * a13TS (B1 Y) Y + 10 * pw ci di Y
      + 10 * (B1 Y + (Y + 2) * pw ct dt (B1 Y + a13TB (B1 Y) Y)) + 376 := ⟨_, fun _ => rfl⟩
  obtain ⟨B4, hB4⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 2 * Y + 2 * a13TS (B1 Y) Y := ⟨_, fun _ => rfl⟩
  obtain ⟨B5, hB5⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = pw c2 d2 (B4 Y) := ⟨_, fun _ => rfl⟩
  obtain ⟨B6, hB6⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 1 + B5 Y * (2 * pw co1 do1 (B5 Y) + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B7, hB7⟩ : ∃ f : ℕ → ℕ, ∀ Y,
      f Y = 1 + B5 Y * (2 * (B5 Y + lcBound (4 * B5 Y)) + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨B8, hB8⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 2 * B6 Y + 2 * B7 Y := ⟨_, fun _ => rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 38 * B5 Y + 19 * B8 Y + 10 * pw cx dx (B5 Y)
      + 10 * ((2 * B5 Y + 2) * Y * pw cph dph (B5 Y)) + 20 * pw cb3 db3 (B5 Y) + 376 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B9, hB9⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 2 * B5 Y + 2 * B8 Y := ⟨_, fun _ => rfl⟩
  obtain ⟨B10, hB10⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = pw c4 d4 (B9 Y) := ⟨_, fun _ => rfl⟩
  obtain ⟨B12, hB12⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = a13TS (B10 Y) Y := ⟨_, fun _ => rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = (Y + 2) * pw ct dt (B10 Y + a13TB (B10 Y) Y) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Tin, hTin⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 19 * B10 Y + 38 * B12 Y + 20 * Tt Y
      + 20 * pw cbI dbI (B10 Y) + 376 := ⟨_, fun _ => rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 19 * B10 Y + 95 * B12 Y + 10 * Tt Y
      + 10 * Tin Y + 20 * pw cbO dbO (B10 Y) + 376 := ⟨_, fun _ => rfl⟩
  obtain ⟨K5, hK5⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 38 * B10 Y + 190 * B12 Y + 10 * pw cy dy (B10 Y)
      + 10 * T3 Y + 20 * pw cb5 db5 (B10 Y) + 376 := ⟨_, fun _ => rfl⟩
  obtain ⟨B13, hB13⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = 2 * B10 Y + 20 * B12 Y := ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℕ → ℕ, ∀ Y, f Y = K1 Y + pw c2 d2 (B4 Y) + K3 Y + pw c4 d4 (B9 Y)
      + K5 Y + pw c6 d6 (B13 Y) := ⟨_, fun _ => rfl⟩
  have pB1 : PolyBound B1 := by rw [show B1 = _ from funext hB1]; exact polyBound_pw cp dp
  have pK1 : PolyBound K1 := by
    rw [show K1 = _ from funext hK1]
    exact ((((polyBound_const 38).mul polyBound_id).add ((polyBound_const 19).mul
      (polyBound_a13TS pB1))).add ((polyBound_const 10).mul (polyBound_pw ci di))).add
      ((polyBound_const 10).mul (pB1.add ((polyBound_id.add (polyBound_const 2)).mul
        ((polyBound_pw ct dt).comp (pB1.add (polyBound_a13TB pB1)))))) |>.add
      (polyBound_const 376)
  have pB4 : PolyBound B4 := by
    rw [show B4 = _ from funext hB4]
    exact ((polyBound_const 2).mul polyBound_id).add ((polyBound_const 2).mul (polyBound_a13TS pB1))
  have pB5 : PolyBound B5 := by
    rw [show B5 = _ from funext hB5]; exact (polyBound_pw c2 d2).comp pB4
  have pB6 : PolyBound B6 := by
    rw [show B6 = _ from funext hB6]
    exact (polyBound_const 1).add (pB5.mul (((polyBound_const 2).mul
      ((polyBound_pw co1 do1).comp pB5)).add (polyBound_const 1)))
  have pB7 : PolyBound B7 := by
    rw [show B7 = _ from funext hB7]
    exact (polyBound_const 1).add (pB5.mul (((polyBound_const 2).mul
      (pB5.add (polyBound_lcBound.comp ((polyBound_const 4).mul pB5)))).add (polyBound_const 1)))
  have pB8 : PolyBound B8 := by
    rw [show B8 = _ from funext hB8]
    exact ((polyBound_const 2).mul pB6).add ((polyBound_const 2).mul pB7)
  have pK3 : PolyBound K3 := by
    rw [show K3 = _ from funext hK3]
    exact (((((((polyBound_const 38).mul pB5).add ((polyBound_const 19).mul pB8)).add
      ((polyBound_const 10).mul ((polyBound_pw cx dx).comp pB5))).add
      ((polyBound_const 10).mul (((((polyBound_const 2).mul pB5).add (polyBound_const 2)).mul
        polyBound_id).mul ((polyBound_pw cph dph).comp pB5)))).add
      ((polyBound_const 20).mul ((polyBound_pw cb3 db3).comp pB5))).add (polyBound_const 376))
  have pB9 : PolyBound B9 := by
    rw [show B9 = _ from funext hB9]
    exact ((polyBound_const 2).mul pB5).add ((polyBound_const 2).mul pB8)
  have pB10 : PolyBound B10 := by
    rw [show B10 = _ from funext hB10]; exact (polyBound_pw c4 d4).comp pB9
  have pB12 : PolyBound B12 := by
    rw [show B12 = _ from funext hB12]; exact polyBound_a13TS pB10
  have pTt : PolyBound Tt := by
    rw [show Tt = _ from funext hTt]
    exact (polyBound_id.add (polyBound_const 2)).mul
      ((polyBound_pw ct dt).comp (pB10.add (polyBound_a13TB pB10)))
  have pTin : PolyBound Tin := by
    rw [show Tin = _ from funext hTin]
    exact (((((polyBound_const 19).mul pB10).add ((polyBound_const 38).mul pB12)).add
      ((polyBound_const 20).mul pTt)).add ((polyBound_const 20).mul
        ((polyBound_pw cbI dbI).comp pB10))).add (polyBound_const 376)
  have pT3 : PolyBound T3 := by
    rw [show T3 = _ from funext hT3]
    exact ((((((polyBound_const 19).mul pB10).add ((polyBound_const 95).mul pB12)).add
      ((polyBound_const 10).mul pTt)).add ((polyBound_const 10).mul pTin)).add
      ((polyBound_const 20).mul ((polyBound_pw cbO dbO).comp pB10))).add (polyBound_const 376)
  have pK5 : PolyBound K5 := by
    rw [show K5 = _ from funext hK5]
    exact ((((((polyBound_const 38).mul pB10).add ((polyBound_const 190).mul pB12)).add
      ((polyBound_const 10).mul ((polyBound_pw cy dy).comp pB10))).add
      ((polyBound_const 10).mul pT3)).add ((polyBound_const 20).mul
        ((polyBound_pw cb5 db5).comp pB10))).add (polyBound_const 376)
  have pB13 : PolyBound B13 := by
    rw [show B13 = _ from funext hB13]
    exact ((polyBound_const 2).mul pB10).add ((polyBound_const 20).mul pB12)
  have pGf : PolyBound Gf := by
    rw [show Gf = _ from funext hGf]
    exact ((((pK1.add ((polyBound_pw c2 d2).comp pB4)).add pK3).add
      ((polyBound_pw c4 d4).comp pB9)).add pK5).add ((polyBound_pw c6 d6).comp pB13)
  obtain ⟨cG, dG, hG⟩ := pGf
  -- the program
  refine ⟨fun Q => RAM.seq (Pairing.pairProg 16 Pid (RAM.seq Pp Pt))
    (RAM.seq P2 (RAM.seq (Pairing.pairProg 16 (RAM.seq Pf3 Pidx) (RAM.seq Ps3 (Fph Q)))
      (RAM.seq P4 (RAM.seq (Pairing.pairProg 16 (RAM.seq Pf5 Pidy) (RAM.seq Ps5
        (Pairing.pairProg 16 (RAM.seq PfO Pt) (RAM.seq PsO
          (Pairing.pairProg 16 (RAM.seq PfI Pt) (RAM.seq PsI Pt)))))) P6)))),
    cG * 2 ^ dG, dG, ?_⟩
  intro Q hQwf
  obtain ⟨hFwf, hFrun⟩ := hFph Q hQwf
  refine ⟨wf_seq (Pairing.wf_pairProg 16 hPid (wf_seq hPp hPt))
    (wf_seq hP2 (wf_seq (Pairing.wf_pairProg 16 (wf_seq hPf3 hPidx) (wf_seq hPs3 hFwf))
      (wf_seq hP4 (wf_seq (Pairing.wf_pairProg 16 (wf_seq hPf5 hPidy) (wf_seq hPs5
        (Pairing.wf_pairProg 16 (wf_seq hPfO hPt) (wf_seq hPsO
          (Pairing.wf_pairProg 16 (wf_seq hPfI hPt) (wf_seq hPsI hPt)))))) hP6)))), ?_⟩
  intro n m C ϕ h ansQ τ hQ
  have hQc : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer :=
    fun W hW => (hQ W hW).2.2
  -- notation and the basic facts
  obtain ⟨t, ht⟩ : ∃ t, t = C.2.2.2.length := ⟨_, rfl⟩
  obtain ⟨Mv, hMv⟩ : ∃ M, M = C.1.2.1.length := ⟨_, rfl⟩
  obtain ⟨SC, hSC⟩ : ∃ S, S = Enc.size C := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (Mv + 1) ^ t * (SC + 1) := ⟨_, rfl⟩
  have hMm : Mv = m := hMv.trans h.action.2.1
  have htm : 10 * t < m := ht ▸ h.small
  have hpow1 : 1 ≤ (Mv + 1) ^ t := Nat.one_le_pow _ _ (by omega)
  have hSY : SC ≤ Y := by rw [hY]; nlinarith
  have hMY : (Mv + 1) ^ t ≤ Y := by rw [hY]; exact Nat.le_mul_of_pos_right _ (by omega)
  have htS : t ≤ SC := by
    rw [ht, hSC]
    exact ((length_le_size _).trans (size_snd_le' _)).trans
      ((size_snd_le' _).trans (size_snd_le' _))
  have htY : t ≤ Y := htS.trans hSY
  have hMpow : ∀ L, L ≤ Mv → (L + 1) ^ t ≤ Y := fun L hL =>
    (Nat.pow_le_pow_left (by omega) t).trans hMY
  have hMpow' : ∀ L, L ≤ Mv → L ^ t ≤ Y := fun L hL =>
    (Nat.pow_le_pow_left (by omega) t).trans ((hMpow L hL))
  have hfact : Nat.factorial t ≤ Y :=
    (Nat.factorial_le_pow t).trans ((Nat.pow_le_pow_left (by omega) t).trans hMY)
  -- stage 1: the `t`-tuples of `[m]`
  set tabs := a13Tuples C with htabs
  have hprep := hrp C
  have hprepS : Enc.size ((List.range C.1.2.1.length, C.2.2.2.length) : List ℕ × ℕ) ≤ B1 Y := by
    rw [hB1]; exact hprep.2.trans (pw_mono cp dp (hSC ▸ hSY))
  have hrangeS : Enc.size (List.range C.1.2.1.length) ≤ B1 Y :=
    (size_fst_le' ((List.range C.1.2.1.length, C.2.2.2.length) : List ℕ × ℕ)).trans hprepS
  have hrange : (List.range C.1.2.1.length).length ≤ Mv := by rw [List.length_range, hMv]
  have r1 := RunsOn.pair (K := 16) (by omega) (hrid C).1
    ((hprep.1).seq (hrt (List.range C.1.2.1.length) C.2.2.2.length))
  have htup1 : (C.2.2.2.length + 2) * pw ct dt (Enc.size ((List.range C.1.2.1.length,
      C.2.2.2.length) : List ℕ × ℕ) + tuplesBound (List.range C.1.2.1.length).length
        (Enc.size (List.range C.1.2.1.length)) C.2.2.2.length)
      ≤ (Y + 2) * pw ct dt (B1 Y + a13TB (B1 Y) Y) := by
    refine Nat.mul_le_mul (by omega) (pw_mono ct dt (Nat.add_le_add hprepS ?_))
    exact tuplesBound_le_TB (ht ▸ hMpow _ hrange) (ht ▸ htY) hrangeS
  have htabsS : Enc.size tabs ≤ a13TS (B1 Y) Y := by
    rw [htabs, a13Tuples]
    exact size_tuplesOf_le_TS (ht ▸ hMpow' _ hrange) (ht ▸ htY) hrangeS
  have hc1 : 19 * Enc.size C + 19 * Enc.size ((fun C : AggnPhaseCtx => C) C) + 19 * Enc.size tabs
      + 10 * pw ci di (Enc.size C) + 10 * (pw cp dp (Enc.size C) + (C.2.2.2.length + 2)
        * pw ct dt (Enc.size ((List.range C.1.2.1.length, C.2.2.2.length) : List ℕ × ℕ)
          + tuplesBound (List.range C.1.2.1.length).length
            (Enc.size (List.range C.1.2.1.length)) C.2.2.2.length)) + 11 * 16 + 200
      ≤ K1 Y := by
    have e1 : pw ci di (Enc.size C) ≤ pw ci di Y := pw_mono ci di (hSC ▸ hSY)
    have e2 : pw cp dp (Enc.size C) ≤ B1 Y := by rw [hB1]; exact pw_mono cp dp (hSC ▸ hSY)
    have e3 : Enc.size C ≤ Y := hSC ▸ hSY
    rw [hK1]
    simp only at *
    omega
  -- stage 2: the inputs of all runs
  have r2 := (hr2 (C, tabs)).1
  have hX2 : Enc.size ((C, tabs) : AggnPhaseCtx × List (List ℕ)) ≤ B4 Y := by
    have := size_pair_le' ((C, tabs) : AggnPhaseCtx × List (List ℕ))
    rw [hB4]; simp only at this; omega
  have hc2 : pw c2 d2 (Enc.size ((C, tabs) : AggnPhaseCtx × List (List ℕ))) ≤ pw c2 d2 (B4 Y) :=
    pw_mono c2 d2 hX2
  have hprepSz : Enc.size (a13Prep C) ≤ B5 Y := by
    rw [hB5]; exact (hr2 (C, tabs)).2.trans hc2
  -- stage 3: the two phases
  set l1 := (a13Prep C).2.1 with hl1
  set l2 := (a13Prep C).2.2 with hl2
  have hph := hFrun l1 l2 (a13_certRuns h) (a13_compareRuns h ansQ hQc) ansQ τ hQ
  have r3 := hb3 Pidx (Fph Q) (a13Prep C) _ _ _ _ (hrx (a13Prep C).1).1 hph
  have hl12S : Enc.size ((l1, l2) : List RawLCLoop × List RawPCLoop) ≤ B5 Y :=
    (size_snd_le' (a13Prep C)).trans hprepSz
  have hl1S : Enc.size l1 ≤ B5 Y := (size_fst_le' ((l1, l2) : List RawLCLoop × List RawPCLoop)).trans hl12S
  have hl2S : Enc.size l2 ≤ B5 Y := (size_snd_le' ((l1, l2) : List RawLCLoop × List RawPCLoop)).trans hl12S
  have hctxS : Enc.size (a13Prep C).1 ≤ B5 Y := (size_fst_le' (a13Prep C)).trans hprepSz
  have ho1S : Enc.size (l1.map (lcOut (lcSolveQ ansQ))) ≤ B6 Y := by
    have hmap := size_map_le_pw (lcOut (lcSolveQ ansQ)) l1 (pw_mono co1 do1)
      (fun p _ => hso1 _ p)
    have e : 1 + Enc.size l1 * (2 * pw co1 do1 (Enc.size l1) + 1)
        ≤ 1 + B5 Y * (2 * pw co1 do1 (B5 Y) + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul hl1S (by have := pw_mono co1 do1 hl1S; omega)) _
    rw [hB6]; omega
  have ho2S : Enc.size (l2.map (pcOut (lcSolveQ ansQ))) ≤ B7 Y := by
    have hmono : Monotone (fun x => x + lcBound (4 * x)) :=
      fun x y hxy => Nat.add_le_add hxy (mono_lcBound (by omega))
    have hmap := size_map_le_pw (pcOut (lcSolveQ ansQ)) l2 hmono
      (fun z hz => size_pcOut_le (a13_compareRuns h ansQ hQc z hz) hQc)
    have e : 1 + Enc.size l2 * (2 * (Enc.size l2 + lcBound (4 * Enc.size l2)) + 1)
        ≤ 1 + B5 Y * (2 * (B5 Y + lcBound (4 * B5 Y)) + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul hl2S (by have := hmono hl2S; simp only at this; omega)) _
    rw [hB7]; omega
  have hphS : Enc.size (a13Phases ansQ C) ≤ B8 Y := by
    have := size_pair_le' (a13Phases ansQ C)
    rw [hB8]
    change Enc.size (a13Phases ansQ C) ≤ 2 * B6 Y + 2 * B7 Y
    have e1 : Enc.size (a13Phases ansQ C).1 ≤ B6 Y := ho1S
    have e2 : Enc.size (a13Phases ansQ C).2 ≤ B7 Y := ho2S
    omega
  have hlen : l1.length + l2.length ≤ 2 * B5 Y := by
    have := length_le_size l1
    have := length_le_size l2
    omega
  have hc3 : 19 * Enc.size (a13Prep C) + 19 * Enc.size ((fun X : A13Ctx => X) (a13Prep C).1)
      + 19 * Enc.size ((l1.map (lcOut (lcSolveQ ansQ)), l2.map (pcOut (lcSolveQ ansQ)))
        : List RawLCOut × List RawCoset)
      + 10 * pw cx dx (Enc.size (a13Prep C).1)
      + 10 * (10 ^ 11 * ((phaseCalls ansQ l1 l2).map τ).sum
        + (l1.length + l2.length + 2) * Nat.factorial C.2.2.2.length
          * pw cph dph (Enc.size ((l1, l2) : List RawLCLoop × List RawPCLoop)))
      + 20 * pw cb3 db3 (Enc.size (a13Prep C)) + 376
      ≤ 10 ^ 12 * ((a13Calls ansQ C).map τ).sum + K3 Y := by
    have e1 : pw cx dx (Enc.size (a13Prep C).1) ≤ pw cx dx (B5 Y) := pw_mono cx dx hctxS
    have e2 : pw cb3 db3 (Enc.size (a13Prep C)) ≤ pw cb3 db3 (B5 Y) := pw_mono cb3 db3 hprepSz
    have e3 : (l1.length + l2.length + 2) * Nat.factorial C.2.2.2.length
          * pw cph dph (Enc.size ((l1, l2) : List RawLCLoop × List RawPCLoop))
        ≤ (2 * B5 Y + 2) * Y * pw cph dph (B5 Y) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (ht ▸ hfact)) (pw_mono cph dph hl12S)
    have e4 : Enc.size ((l1.map (lcOut (lcSolveQ ansQ)), l2.map (pcOut (lcSolveQ ansQ)))
        : List RawLCOut × List RawCoset) ≤ B8 Y := hphS
    have e5 : ((a13Calls ansQ C).map τ).sum = ((phaseCalls ansQ l1 l2).map τ).sum := rfl
    rw [hK3, e5]
    simp only at *
    omega
  -- stage 4: the stores, the table, and `D(x)`, `D(y)`
  have r4 := (hr4 ((a13Prep C).1, a13Phases ansQ C)).1
  have hX4 : Enc.size (((a13Prep C).1, a13Phases ansQ C) : A13Ctx × (List RawLCOut × List RawCoset))
      ≤ B9 Y := by
    have := size_pair_le' (((a13Prep C).1, a13Phases ansQ C) : A13Ctx × (List RawLCOut × List RawCoset))
    simp only at this
    rw [hB9]; omega
  have hc4 := pw_mono c4 d4 hX4
  set Mid := a13Mid ansQ C with hMid
  have hMidS : Enc.size Mid ≤ B10 Y := by
    rw [hB10]; exact (hr4 ((a13Prep C).1, a13Phases ansQ C)).2.trans hc4
  -- stage 5: the three tuple tables of case (3)
  have hM2 : Enc.size Mid.2 ≤ B10 Y := (size_snd_le' Mid).trans hMidS
  have hM1 : Enc.size Mid.1 ≤ B10 Y := (size_fst_le' Mid).trans hMidS
  have hM21 : Enc.size Mid.2.1 ≤ B10 Y := (size_fst_le' Mid.2).trans hM2
  have hM22 : Enc.size Mid.2.2 ≤ B10 Y := (size_snd_le' Mid.2).trans hM2
  have hM221 : Enc.size Mid.2.2.1 ≤ B10 Y := (size_fst_le' Mid.2.2).trans hM22
  have hM222 : Enc.size Mid.2.2.2 ≤ B10 Y := (size_snd_le' Mid.2.2).trans hM22
  have hDx : Mid.2.1.1.length ≤ Mv := by rw [hMv]; exact length_aggnFixed_le _ false
  have hDx' : Mid.2.2.1.1.length ≤ Mv := by
    rw [hMv]
    show (List.range _).length ≤ _
    rw [List.length_range]; exact length_aggnFixed_le _ false
  have hDy' : Mid.2.2.2.1.length ≤ Mv := by
    rw [hMv]
    show (List.range _).length ≤ _
    rw [List.length_range]; exact length_aggnFixed_le _ true
  have hk1 : Mid.2.1.2 = t := ht.symm
  have hk2 : Mid.2.2.1.2 = t := ht.symm
  have hk3 : Mid.2.2.2.2 = t := ht.symm
  have htupRun : ∀ (dom : List ℕ) (k : ℕ), k = t → dom.length ≤ Mv →
      Enc.size ((dom, k) : List ℕ × ℕ) ≤ B10 Y →
      RunsOn 16 Pt ((dom, k) : List ℕ × ℕ) (tuplesOf dom k) (Tt Y) ∧
        Enc.size (tuplesOf dom k) ≤ B12 Y := by
    intro dom k hk hd hs
    have hds : Enc.size dom ≤ B10 Y := (size_fst_le' ((dom, k) : List ℕ × ℕ)).trans hs
    refine ⟨(hrt dom k).mono ?_, ?_⟩
    · rw [hTt, hk]
      rw [hk] at hs
      exact Nat.mul_le_mul (by omega) (pw_mono ct dt (Nat.add_le_add hs
        (tuplesBound_le_TB (hMpow _ hd) htY hds)))
    · rw [hB12, hk]
      exact size_tuplesOf_le_TS (hMpow' _ hd) htY hds
  obtain ⟨rA, sA⟩ := htupRun Mid.2.1.1 Mid.2.1.2 hk1 hDx hM21
  obtain ⟨rB, sB⟩ := htupRun Mid.2.2.1.1 Mid.2.2.1.2 hk2 hDx' hM221
  obtain ⟨rC, sC⟩ := htupRun Mid.2.2.2.1 Mid.2.2.2.2 hk3 hDy' hM222
  have inner := (hbI Pt Pt Mid.2.2 _ _ _ _ rB rC).mono (T' := Tin Y) (by
    have e := pw_mono cbI dbI hM22
    rw [hTin]; omega)
  have sBC : Enc.size ((tuplesOf Mid.2.2.1.1 Mid.2.2.1.2, tuplesOf Mid.2.2.2.1 Mid.2.2.2.2)
      : List (List ℕ) × List (List ℕ)) ≤ 4 * B12 Y := by
    have := size_pair_le' ((tuplesOf Mid.2.2.1.1 Mid.2.2.1.2, tuplesOf Mid.2.2.2.1 Mid.2.2.2.2)
      : List (List ℕ) × List (List ℕ))
    simp only at this; omega
  have outer := (hbO Pt _ Mid.2 _ _ _ _ rA inner).mono (T' := T3 Y) (by
    have e := pw_mono cbO dbO hM2
    rw [hT3]; omega)
  have sABC : Enc.size (a13TabsOf Mid) ≤ 10 * B12 Y := by
    have := size_pair_le' (a13TabsOf Mid)
    have e2 : Enc.size (a13TabsOf Mid).2 ≤ 4 * B12 Y := sBC
    have e1 : Enc.size (a13TabsOf Mid).1 ≤ B12 Y := sA
    omega
  have r5 := (hb5 Pidy _ Mid _ (a13TabsOf Mid) _ _ (hry Mid.1).1 outer).mono (T' := K5 Y) (by
    have e1 := pw_mono cy dy hM1
    have e2 := pw_mono cb5 db5 hMidS
    have e3 : Enc.size (id Mid.1) ≤ B10 Y := hM1
    have e4 := sABC
    rw [hK5]
    omega)
  have hX6 : Enc.size ((Mid.1, a13TabsOf Mid) : AggnGuidePrepareInput × A13Tabs) ≤ B13 Y := by
    have := size_pair_le' ((Mid.1, a13TabsOf Mid) : AggnGuidePrepareInput × A13Tabs)
    simp only at this
    rw [hB13]; omega
  -- stage 6: the case analysis
  have r6 := (hr6 ((Mid.1, a13TabsOf Mid) : AggnGuidePrepareInput × A13Tabs)).1
  have hc6 := pw_mono c6 d6 hX6
  -- the whole run
  have r := (r1.mono hc1).seq (r2.seq ((r3.mono hc3).seq (r4.seq (r5.seq r6))))
  refine r.mono ?_
  have hGY := hG Y
  rw [hGf] at hGY
  have hconv := pw_conv cG dG Mv t SC
  rw [← hY, hMm] at hconv
  have hpw : cG * (Y + 1) ^ dG = pw cG dG Y := rfl
  rw [← ht, ← hSC]
  omega
end Algo
