/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: one node of a round, run on the RAM with its calls answered by a given
program.
-/
import Workspace.Algo.Round
import Workspace.Algo.PolyWitness
import Workspace.Machine.RunsOnLoop
import Workspace.Machine.ListOps2

/-!
# One node of a round with its calls answered by a program

The running-time claims of §13 split the cost of a procedure in two: the calls it makes to
String Isomorphism, and the rest ("by making `≤ t! n²` calls to String Isomorphism problems on
domains of size `≤ n/t` and performing `t! poly(n)` computation", Theorem 13.1.3). This file
gives the RAM form of that split for one node of an `Algo.Round`: the fold of `Algo.Round.loopAux`
over the children of one instance, where each child is answered by an arbitrary program `Q`.

The fold runs as `seq Pset (seq (whileNz 18 body) Pfin)`. One step of the body asks for the
next child (`Algo.Round.foldAsk`); if there is none, the fold stops (`Algo.Round.foldStop`);
otherwise `Q` answers the child and the answer is combined into the state
(`Algo.Round.foldFeed`). Everything except `Q` is a `RAM.PolyFun`.

## Main results

* `Algo.Round.foldOut_iterate`: the iteration computes `Algo.Round.loopAux`;
* `Algo.Round.sum_foldCost_iterate`: the calls it makes are `Algo.Round.loopCalls`;
* `Algo.Round.exists_foldProg`: **the cost split.** There are a program transformer `F` and a
  polynomial `pw c d` such that for every program `Q`, `F Q` runs the fold within
  `100 · ∑_{J ∈ calls} τ(J) + (cnt I + 2) · pw c d B`, where `τ(J)` is the running time of `Q`
  on the call `J` and `B` bounds the states of the fold. The factor `100` is the overhead of the
  machine's pairing routine, which is run twice around each call; it is an absolute constant.
-/

namespace Algo
open RAM

namespace Round

variable {ι ω α : Type*}

/-- The state of the fold: the node, the next index, the partial answer, and whether the fold
has stopped. -/
abbrev FoldSt (ι ω : Type*) := (ι × ℕ × ω) × Bool

variable (R : Round ι ω α)

/-- The next call: none once the fold has stopped, otherwise the next child. -/
def foldAsk (st : FoldSt ι ω) : Option ι := if st.2 then none else R.child st.1

/-- Stop the fold. -/
def foldStop (st : FoldSt ι ω) : FoldSt ι ω := (st.1, true)

/-- Combine the answer of the call into the state and move to the next index. -/
def foldFeed (p : α × FoldSt ι ω) : FoldSt ι ω :=
  ((p.2.1.1, p.2.1.2.1 + 1, R.combine (p.2.1.1, p.2.1.2.1, p.2.1.2.2, p.1)), false)

/-- One step of the fold, with the calls answered by `ans`. -/
def foldStep (ans : ι → α) (st : FoldSt ι ω) : FoldSt ι ω :=
  (R.foldAsk st).elim (foldStop st) (fun J => R.foldFeed (ans J, st))

/-- The answer read off a state. -/
def foldOut (p : ℕ × FoldSt ι ω) : α := R.finish (p.2.1.1, p.2.1.2.2)

/-- The start of the fold: the counter and the initial state. -/
def foldStart (cnt : ι → ℕ) (I : ι) : ℕ × FoldSt ι ω := (cnt I, ((I, 0, R.init I), false))

/-- What the call of one step costs: `τ` of the child it asks for, `0` if it asks for none. -/
def foldCost (τ : ι → ℕ) (st : FoldSt ι ω) : ℕ := (R.foldAsk st).elim 0 τ

theorem foldStep_done {ans : ι → α} {st : FoldSt ι ω} (h : st.2 = true) :
    R.foldStep ans st = st := by
  obtain ⟨st1, b⟩ := st
  simp only at h
  subst h
  simp [foldStep, foldAsk, foldStop]

theorem foldStep_iterate_done {ans : ι → α} {st : FoldSt ι ω} (h : st.2 = true) (k : ℕ) :
    (R.foldStep ans)^[k] st = st :=
  Function.iterate_fixed (R.foldStep_done h) k

theorem foldCost_done (τ : ι → ℕ) {st : FoldSt ι ω} (h : st.2 = true) : R.foldCost τ st = 0 := by
  simp [foldCost, foldAsk, h]

/-- **The iteration computes the fold.** -/
theorem foldOut_iterate (ans : ι → α) (I : ι) :
    ∀ (w j : ℕ) (s : ω) (k : ℕ),
      R.foldOut (k, (R.foldStep ans)^[w] ((I, j, s), false)) = R.loopAux ans w I j s := by
  intro w
  induction w with
  | zero => intro j s k; rfl
  | succ w ih =>
    intro j s k
    rw [Function.iterate_succ_apply]
    cases hc : R.child (I, j, s) with
    | none =>
      have h1 : R.foldStep ans ((I, j, s), false) = ((I, j, s), true) := by
        simp [foldStep, foldAsk, foldStop, hc]
      rw [h1, R.foldStep_iterate_done (st := ((I, j, s), true)) rfl, R.loopAux_succ_none hc]
      rfl
    | some J =>
      have h1 : R.foldStep ans ((I, j, s), false)
          = ((I, j + 1, R.combine (I, j, s, ans J)), false) := by
        simp [foldStep, foldAsk, foldFeed, hc]
      rw [h1, ih, R.loopAux_succ_some hc]

/-- **The calls of the iteration are the calls of the fold**, with their costs. -/
theorem sum_foldCost_iterate (ans : ι → α) (τ : ι → ℕ) (I : ι) :
    ∀ (w j : ℕ) (s : ω),
      ∑ i ∈ Finset.range w, R.foldCost τ ((R.foldStep ans)^[i] ((I, j, s), false))
        = ((R.loopCalls ans w I j s).map τ).sum := by
  intro w
  induction w with
  | zero => intro j s; simp
  | succ w ih =>
    intro j s
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply]
    cases hc : R.child (I, j, s) with
    | none =>
      have h1 : R.foldStep ans ((I, j, s), false) = ((I, j, s), true) := by
        simp [foldStep, foldAsk, foldStop, hc]
      rw [h1, R.loopCalls_succ_none hc]
      simp only [R.foldStep_iterate_done (st := ((I, j, s), true)) rfl, R.foldCost_done τ (st := ((I, j, s), true)) rfl, Finset.sum_const_zero]
      simp [foldCost, foldAsk, hc]
    | some J =>
      have h1 : R.foldStep ans ((I, j, s), false)
          = ((I, j + 1, R.combine (I, j, s, ans J)), false) := by
        simp [foldStep, foldAsk, foldFeed, hc]
      rw [h1, ih, R.loopCalls_succ_some hc]
      simp [foldCost, foldAsk, hc, Nat.add_comm]

/-- Every child the iteration asks for is a call of the fold. -/
theorem foldAsk_iterate_mem (ans : ι → α) (I : ι) :
    ∀ (w j : ℕ) (s : ω) (i : ℕ), i < w → ∀ J : ι,
      R.foldAsk ((R.foldStep ans)^[i] ((I, j, s), false)) = some J →
        J ∈ R.loopCalls ans w I j s := by
  intro w
  induction w with
  | zero => intro j s i hi; omega
  | succ w ih =>
    intro j s i hi J hJ
    cases hc : R.child (I, j, s) with
    | none =>
      have h1 : R.foldStep ans ((I, j, s), false) = ((I, j, s), true) := by
        simp [foldStep, foldAsk, foldStop, hc]
      cases i with
      | zero => simp [foldAsk, hc] at hJ
      | succ i =>
        rw [Function.iterate_succ_apply, h1, R.foldStep_iterate_done (st := ((I, j, s), true)) rfl] at hJ
        simp [foldAsk] at hJ
    | some J' =>
      have h1 : R.foldStep ans ((I, j, s), false)
          = ((I, j + 1, R.combine (I, j, s, ans J')), false) := by
        simp [foldStep, foldAsk, foldFeed, hc]
      rw [R.loopCalls_succ_some hc]
      cases i with
      | zero =>
        simp only [Function.iterate_zero, id, foldAsk, Bool.false_eq_true, if_false, hc,
          Option.some.injEq] at hJ
        subst hJ
        exact List.mem_cons_self ..
      | succ i =>
        rw [Function.iterate_succ_apply, h1] at hJ
        exact List.mem_cons_of_mem _ (ih (j + 1) _ i (by omega) J hJ)

/-! ## The routines -/

section Routines

variable [Enc ι] [Enc ω] [Enc α]

theorem polyFun_foldAsk (hch : PolyFun R.child) : PolyFun R.foldAsk :=
  (PolyFun.ite polyFun_snd polyFun_none (polyFun_fst.comp hch)).of_eq (fun _ => rfl)

theorem polyFun_foldAsk2 (hch : PolyFun R.child) :
    PolyFun (fun st : FoldSt ι ω => (R.foldAsk st, st)) :=
  (R.polyFun_foldAsk hch).pair polyFun_id

theorem polyFun_foldStop : PolyFun (foldStop : FoldSt ι ω → FoldSt ι ω) :=
  polyFun_fst.pair (polyFun_const true)

theorem polyFun_foldFeed (hco : PolyFun R.combine) : PolyFun R.foldFeed := by
  have hI : PolyFun (fun p : α × FoldSt ι ω => p.2.1.1) :=
    (polyFun_snd.comp polyFun_fst).comp polyFun_fst
  have hj : PolyFun (fun p : α × FoldSt ι ω => p.2.1.2.1) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hs : PolyFun (fun p : α × FoldSt ι ω => p.2.1.2.2) :=
    ((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd
  have hc : PolyFun (fun p : α × FoldSt ι ω => R.combine (p.2.1.1, p.2.1.2.1, p.2.1.2.2, p.1)) :=
    (hI.pair (hj.pair (hs.pair polyFun_fst))).comp hco
  exact ((hI.pair ((hj.add (polyFun_const 1)).pair hc)).pair (polyFun_const false)).of_eq
    (fun _ => rfl)

theorem polyFun_foldOut (hfi : PolyFun R.finish) : PolyFun R.foldOut :=
  (((polyFun_snd.comp polyFun_fst).comp polyFun_fst).pair
    (((polyFun_snd.comp polyFun_fst).comp polyFun_snd).comp polyFun_snd)).comp hfi

theorem polyFun_foldStart (hin : PolyFun R.init) {cnt : ι → ℕ} (hcnt : PolyFun cnt) :
    PolyFun (R.foldStart cnt) :=
  (hcnt.pair ((polyFun_id.pair ((polyFun_const 0).pair hin)).pair (polyFun_const false))).of_eq
    (fun _ => rfl)

end Routines

/-! ## The cost -/

theorem pw_le_pw {c c' d d' m : ℕ} (hc : c ≤ c') (hd : d ≤ d') : pw c d m ≤ pw c' d' m :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd)

/-- The arithmetic of one step of the body. -/
theorem foldBody_arith {Z P τ Sp Sk Sc Tpred Tsnd Task Topt : ℕ}
    (hSp : Sp ≤ Z) (hSk : Sk ≤ Z) (hSc : Sc ≤ Z) (hTpred : Tpred ≤ P) (hTsnd : Tsnd ≤ P)
    (hTask : Task ≤ P) (hTopt : Topt ≤ 10 * τ + 200 * Z + 30 * P + 2000) :
    19 * Sp + 19 * Sk + 19 * Sc + 10 * Tpred + 10 * (Tsnd + (Task + Topt)) + 11 * 16 + 200
      ≤ 100 * τ + (3000 * Z + 400 * P + 30000) := by
  omega

variable [Enc ι] [Enc ω] [Enc α]

set_option maxHeartbeats 4000000 in
/-- **The cost split for one node.**  One program transformer `F` and one polynomial `pw c d`
serve every node and every program `Q` answering its calls: if `Q` runs on each call `J` of
the fold to the answer `ans J` within `τ J` steps, and the states of the fold, the calls and
their answers have size at most `B`, then `F Q` runs from `I` to the value of the fold within
`100 · ∑_{J ∈ calls} τ(J) + (cnt I + 2) · pw c d B` steps. -/
theorem exists_foldProg (hch : PolyFun R.child) (hco : PolyFun R.combine)
    (hin : PolyFun R.init) (hfi : PolyFun R.finish) {cnt : ι → ℕ} (hcnt : PolyFun cnt) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → (∀ _ : ι, Wf (F Q)) ∧
      ∀ (ans : ι → α) (τ : ι → ℕ) (I : ι) (B : ℕ),
        (∀ J ∈ R.loopCalls ans (cnt I) I 0 (R.init I),
          RunsOn 16 Q J (ans J) (τ J) ∧ Enc.size J ≤ B ∧ Enc.size (ans J) ≤ B) →
        (∀ k ≤ cnt I, Enc.size ((R.foldStep ans)^[k] ((I, 0, R.init I), false)) ≤ B) →
        RunsOn 16 (F Q) I (R.loopAux ans (cnt I) I 0 (R.init I))
          (100 * ((R.loopCalls ans (cnt I) I 0 (R.init I)).map τ).sum
            + (cnt I + 2) * pw c d B) := by
  -- the routines and one common witness
  obtain ⟨Pask, c1, d1, hask, hask_s⟩ := polyFun_witness (R.polyFun_foldAsk2 hch)
  obtain ⟨Pstop, c2, d2, hstop, -⟩ := polyFun_witness (polyFun_foldStop (ι := ι) (ω := ω))
  obtain ⟨Pfeed, c3, d3, hfeed, -⟩ := polyFun_witness (R.polyFun_foldFeed hco)
  obtain ⟨Ppred, c4, d4, hpred, -⟩ :=
    polyFun_witness (polyFun_fst.sub (polyFun_const 1) :
      PolyFun (fun p : ℕ × FoldSt ι ω => p.1 - 1))
  obtain ⟨Psnd, c5, d5, hsnd, -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun p : ℕ × FoldSt ι ω => p.2))
  obtain ⟨Pfst', c6, d6, hfst', -⟩ :=
    polyFun_witness (polyFun_fst : PolyFun (fun p : ι × FoldSt ι ω => p.1))
  obtain ⟨Psnd', c7, d7, hsnd', -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun p : ι × FoldSt ι ω => p.2))
  obtain ⟨Pset, c8, d8, hset, hset_s⟩ := polyFun_witness (R.polyFun_foldStart hin hcnt)
  obtain ⟨Pfin, c9, d9, hfin, -⟩ := polyFun_witness (R.polyFun_foldOut hfi)
  set C := c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 1 with hC
  set D := d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 + d9 with hD
  have hw : ∀ {ci di : ℕ}, ci ≤ C → di ≤ D → ∀ m, ci * (m + 1) ^ di ≤ pw C D m :=
    fun hc hd m => pw_le_pw hc hd
  -- the bound on the sizes and the per-step polynomial
  obtain ⟨Zf, hZf⟩ : ∃ f : ℕ → ℕ, ∀ B, f B = 4 * B + 4 * pw C D B + 4 := ⟨_, fun _ => rfl⟩
  obtain ⟨Pf, hPf⟩ : ∃ f : ℕ → ℕ, ∀ B, f B = pw C D (Zf B) := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGd⟩ : ∃ f : ℕ → ℕ, ∀ B,
      f B = 3000 * Zf B + 400 * Pf B + 30000 + 2 + Pf B + Pf B + 1 := ⟨_, fun _ => rfl⟩
  have hG : PolyBound G := by
    have hZ : PolyBound Zf := by
      have e : Zf = fun B => 4 * B + 4 * pw C D B + 4 := funext hZf
      rw [e]
      exact (((polyBound_const 4).mul polyBound_id).add
        ((polyBound_const 4).mul (polyBound_pw C D))).add (polyBound_const 4)
    have hP : PolyBound Pf := by
      have e : Pf = fun B => pw C D (Zf B) := funext hPf
      rw [e]
      exact (polyBound_pw C D).comp hZ
    have e : G = fun B => 3000 * Zf B + 400 * Pf B + 30000 + 2 + Pf B + Pf B + 1 := funext hGd
    rw [e]
    exact ((((((polyBound_const 3000).mul hZ).add ((polyBound_const 400).mul hP)).add
      (polyBound_const 30000)).add (polyBound_const 2)).add hP |>.add hP).add (polyBound_const 1)
  obtain ⟨c, d, hcd⟩ := hG
  -- the programs
  let Psome : Program → Program := fun Q =>
    RAM.seq (Pairing.pairProg 16 (RAM.seq Pfst' Q) Psnd') Pfeed
  let Pbody : Program → Program := fun Q =>
    Pairing.pairProg 16 Ppred
      (RAM.seq Psnd (RAM.seq Pask (Lists.optElimProg 16 Pstop (Psome Q))))
  refine ⟨fun Q => RAM.seq Pset (RAM.seq (whileNz 18 (Pbody Q)) Pfin), c, d, ?_⟩
  intro Q hQwf
  have hWf : ∀ (I0 : ι) (a0 : α), Wf (RAM.seq Pset (RAM.seq (whileNz 18 (Pbody Q)) Pfin)) := by
    intro I0 a0
    set t0 : FoldSt ι ω := ((I0, 0, R.init I0), false)
    have hPwf0 : Wf (Psome Q) :=
      wf_seq (Pairing.wf_pairProg 16 (wf_seq (hfst'.runsOn (I0, t0)).wf hQwf)
        (hsnd'.runsOn (I0, t0)).wf) (hfeed.runsOn (a0, t0)).wf
    exact wf_seq (hset.runsOn I0).wf (wf_seq (wf_whileNz (Pairing.wf_pairProg 16
      (hpred.runsOn ((0 : ℕ), t0)).wf (wf_seq (hsnd.runsOn ((0 : ℕ), t0)).wf
        (wf_seq (hask.runsOn t0).wf (Lists.wf_optElimProg (by omega) (hstop.runsOn t0).wf
          hPwf0))))) (hfin.runsOn ((0 : ℕ), t0)).wf)
  refine ⟨fun I0 => hWf I0 (R.finish (I0, R.init I0)), ?_⟩
  intro ans τ I B hcalls hstates
  have hZB := hZf B
  have hPB := hPf B
  have hGB' := hGd B
  set N := cnt I with hN
  set s₀ : FoldSt ι ω := ((I, 0, R.init I), false) with hs₀
  set step := R.foldStep ans with hstep
  have hB0 : Enc.size s₀ ≤ B := by simpa using hstates 0 (Nat.zero_le _)
  have hIB : Enc.size I ≤ B :=
    le_trans (le_trans (size_fst_le' (I, 0, R.init I)) (size_fst_le' s₀)) hB0
  have hNB : Enc.size N ≤ pw C D B := by
    have h1 := hset_s I
    have h2 : Enc.size N ≤ Enc.size (R.foldStart cnt I) := size_fst_le' (R.foldStart cnt I)
    exact le_trans h2 (le_trans (le_trans h1 (hw (by omega) (by omega) _)) (pw_mono C D hIB))
  have hPwf : Wf (Psome Q) :=
    wf_seq (Pairing.wf_pairProg 16 (wf_seq (hfst'.runsOn (I, s₀)).wf hQwf)
      (hsnd'.runsOn (I, s₀)).wf) (hfeed.runsOn (ans I, s₀)).wf
  -- one step of the body
  have hbody : ∀ j < N, RunsOn 16 (Pbody Q) ((N - j, step^[j] s₀) : ℕ × FoldSt ι ω)
      ((N - (j + 1), step^[j + 1] s₀) : ℕ × FoldSt ι ω)
      (100 * R.foldCost τ (step^[j] s₀) + (3000 * Zf B + 400 * Pf B + 30000)) := by
    intro j hj
    set st := step^[j] s₀ with hst
    have hstB : Enc.size st ≤ B := hstates j (by omega)
    have hst1B : Enc.size (step st) ≤ B := by
      have := hstates (j + 1) (by omega)
      rwa [Function.iterate_succ_apply'] at this
    have hkB : Enc.size (N - j) ≤ pw C D B := le_trans (size_nat_le_of_le (by omega)) hNB
    have hk1B : Enc.size (N - (j + 1)) ≤ pw C D B := le_trans (size_nat_le_of_le (by omega)) hNB
    have hpB : Enc.size ((N - j, st) : ℕ × FoldSt ι ω) ≤ Zf B := by
      have := size_pair_le' ((N - j, st) : ℕ × FoldSt ι ω); simp only at this; omega
    have houtB : Enc.size ((N - (j + 1), step st) : ℕ × FoldSt ι ω) ≤ Zf B := by
      have := size_pair_le' ((N - (j + 1), step st) : ℕ × FoldSt ι ω); simp only at this; omega
    have haskB : Enc.size ((R.foldAsk st, st) : Option ι × FoldSt ι ω) ≤ Zf B := by
      have h1 := hask_s st
      have h2 := hw (ci := c1) (di := d1) (by omega) (by omega) (Enc.size st)
      have h3 := pw_mono C D hstB
      simp only at h1; omega
    have hPmono : ∀ {ci di m}, ci ≤ C → di ≤ D → m ≤ Zf B → ci * (m + 1) ^ di ≤ Pf B :=
      fun hc hd hm => le_trans (hw hc hd _) (by rw [hPB]; exact pw_mono C D hm)
    -- the predecessor
    have r1 := hpred.runsOn ((N - j, st) : ℕ × FoldSt ι ω)
    -- the inner part
    have r2 := hsnd.runsOn ((N - j, st) : ℕ × FoldSt ι ω)
    have r3 := hask.runsOn st
    have hopt : RunsOn 16 (Lists.optElimProg 16 Pstop (Psome Q))
        ((R.foldAsk st, st) : Option ι × FoldSt ι ω) (step st)
        (10 * R.foldCost τ st + 200 * Zf B + 30 * Pf B + 2000) := by
      cases ho : R.foldAsk st with
      | none =>
        have hs : step st = foldStop st := by
          rw [hstep, foldStep, ho]; rfl
        rw [hs]
        refine (RunsOn.optionElim_none (β := ι) (by omega) hPwf (hstop.runsOn st)).mono ?_
        have h1 : Enc.size ((none, st) : Option ι × FoldSt ι ω) ≤ Zf B := by rw [← ho]; exact haskB
        have h2 := hPmono (ci := c2) (di := d2) (m := Enc.size st) (by omega) (by omega)
          (by omega)
        omega
      | some J =>
        have hJmem : J ∈ R.loopCalls ans N I 0 (R.init I) :=
          R.foldAsk_iterate_mem ans I N 0 (R.init I) j hj J (by rw [← hst]; exact ho)
        obtain ⟨hQJ, hJB, haJB⟩ := hcalls J hJmem
        have hs : step st = R.foldFeed (ans J, st) := by
          rw [hstep, foldStep, ho]; rfl
        rw [hs]
        have q1 : RunsOn 16 (RAM.seq Pfst' Q) ((J, st) : ι × FoldSt ι ω) (ans J)
            (c6 * (Enc.size ((J, st) : ι × FoldSt ι ω) + 1) ^ d6 + τ J) :=
          (hfst'.runsOn (J, st)).seq hQJ
        have q2 := hsnd'.runsOn ((J, st) : ι × FoldSt ι ω)
        have q3 := RunsOn.pair (K := 16) (by omega) q1 q2
        have q4 := q3.seq (hfeed.runsOn ((ans J, st) : α × FoldSt ι ω))
        have q5 := RunsOn.optionElim_some (Pg := Pstop) (by omega) (hstop.runsOn st).wf q4
        refine q5.mono ?_
        have hJs : Enc.size ((J, st) : ι × FoldSt ι ω) ≤ Zf B := by
          have := size_pair_le' ((J, st) : ι × FoldSt ι ω); simp only at this; omega
        have has : Enc.size ((ans J, st) : α × FoldSt ι ω) ≤ Zf B := by
          have := size_pair_le' ((ans J, st) : α × FoldSt ι ω); simp only at this; omega
        have hsomeB : Enc.size ((some J, st) : Option ι × FoldSt ι ω) ≤ Zf B := by
          rw [← ho]; exact haskB
        have e1 := hPmono (ci := c6) (di := d6) (by omega) (by omega) hJs
        have e2 := hPmono (ci := c7) (di := d7) (by omega) (by omega) hJs
        have e3 := hPmono (ci := c3) (di := d3) (by omega) (by omega) has
        have hcost : R.foldCost τ st = τ J := by simp [foldCost, ho]
        simp only at e1 e2 e3 ⊢
        rw [hcost]
        have hstZ : Enc.size st ≤ Zf B := by omega
        have haZ : Enc.size (ans J) ≤ Zf B := by omega
        omega
    have r4 := r2.seq (r3.seq hopt)
    have r5 := RunsOn.pair (K := 16) (by omega) r1 r4
    have hout : (((N - j, st) : ℕ × FoldSt ι ω).1 - 1, step st)
        = ((N - (j + 1), step^[j + 1] s₀) : ℕ × FoldSt ι ω) := by
      rw [Function.iterate_succ_apply', ← hst]; simp only; congr 1
    rw [← hout]
    refine r5.mono ?_
    have t1 := hPmono (ci := c4) (di := d4) (by omega) (by omega) hpB
    have t2 := hPmono (ci := c5) (di := d5) (by omega) (by omega) hpB
    have t3 := hPmono (ci := c1) (di := d1) (m := Enc.size st) (by omega) (by omega) (by omega)
    have hk1 : Enc.size (((N - j, st) : ℕ × FoldSt ι ω).1 - 1) ≤ Zf B := by
      simp only
      have := size_nat_le_of_le (show N - j - 1 ≤ N by omega)
      omega
    have hc1 : Enc.size ((((N - j, st) : ℕ × FoldSt ι ω).1 - 1, step st) : ℕ × FoldSt ι ω)
        ≤ Zf B := by rw [hout, Function.iterate_succ_apply', ← hst]; exact houtB
    exact foldBody_arith hpB hk1 (by
      have := size_pair_le' ((((N - j, st) : ℕ × FoldSt ι ω).1 - 1, step st) : ℕ × FoldSt ι ω)
      simp only at this ⊢
      have h' : Enc.size (step st) ≤ Zf B := by omega
      exact h') t1 t2 t3 le_rfl
  -- the loop
  have hloop := runsOn_iterate_sum (K := 16) (Q := Pbody Q) (step := step)
    (Pairing.wf_pairProg 16 (hpred.runsOn ((0 : ℕ), s₀)).wf
      (wf_seq (hsnd.runsOn ((0 : ℕ), s₀)).wf (wf_seq (hask.runsOn s₀).wf
        (Lists.wf_optElimProg (by omega) (hstop.runsOn s₀).wf hPwf)))) N s₀ _ hbody
  -- the setup and the final read-off
  have hs1 : RunsOn 16 Pset I ((N, s₀) : ℕ × FoldSt ι ω) (c8 * (Enc.size I + 1) ^ d8) :=
    hset.runsOn I
  have hs3 := hfin.runsOn ((0 : ℕ), step^[N] s₀)
  have hall := hs1.seq (hloop.seq hs3)
  have hval : R.foldOut ((0 : ℕ), step^[N] s₀) = R.loopAux ans N I 0 (R.init I) :=
    R.foldOut_iterate ans I N 0 (R.init I) 0
  rw [hval] at hall
  refine hall.mono ?_
  have hsum : ∑ j ∈ Finset.range N, (100 * R.foldCost τ (step^[j] s₀)
        + (3000 * Zf B + 400 * Pf B + 30000) + 2)
      = 100 * ((R.loopCalls ans N I 0 (R.init I)).map τ).sum
        + N * (3000 * Zf B + 400 * Pf B + 30000 + 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      R.sum_foldCost_iterate ans τ I N 0 (R.init I)]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [hsum]
  have hfinB : Enc.size (((0 : ℕ), step^[N] s₀) : ℕ × FoldSt ι ω) ≤ Zf B := by
    have h1 := size_pair_le' (((0 : ℕ), step^[N] s₀) : ℕ × FoldSt ι ω)
    have h2 := hstates N le_rfl
    have h3 : Enc.size (0 : ℕ) ≤ pw C D B := le_trans (size_nat_le_of_le (Nat.zero_le N)) hNB
    simp only at h1
    omega
  have e1 : c8 * (Enc.size I + 1) ^ d8 ≤ Pf B :=
    le_trans (hw (by omega) (by omega) _) (by rw [hPB]; exact pw_mono C D (by omega))
  have e2 : c9 * (Enc.size (((0 : ℕ), step^[N] s₀) : ℕ × FoldSt ι ω) + 1) ^ d9 ≤ Pf B :=
    le_trans (hw (by omega) (by omega) _) (by rw [hPB]; exact pw_mono C D hfinB)
  have hGB : G B ≤ pw c d B := hcd B
  have hmul : (N + 2) * G B ≤ (N + 2) * pw c d B := Nat.mul_le_mul_left _ hGB
  have hexp : (N + 2) * G B = N * G B + 2 * G B := by ring
  have hNG : N * (3000 * Zf B + 400 * Pf B + 30000 + 2) ≤ N * G B :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Invariants of the fold -/

section Inv

variable {ι ω α : Type*} (R : Round ι ω α)

/-- A fold makes at most `w` calls. -/
theorem length_loopCalls_le (rec : ι → α) (I : ι) :
    ∀ (w j : ℕ) (s : ω), (R.loopCalls rec w I j s).length ≤ w := by
  intro w
  induction w with
  | zero => intro j s; simp
  | succ w ih =>
    intro j s
    cases hc : R.child (I, j, s) with
    | none => rw [R.loopCalls_succ_none hc]; simp
    | some J =>
      rw [R.loopCalls_succ_some hc, List.length_cons]
      have := ih (j + 1) (R.combine (I, j, s, rec J))
      omega

/-- **An invariant of the fold.**  If `P` holds at the start and is kept by every step that
makes a call, then every state of the iteration satisfies it, and every call is a child at
a state satisfying it. -/
theorem foldStep_iterate_inv (ans : ι → α) (I : ι) (P : ℕ → ω → Prop)
    (hP : ∀ j s J, P j s → R.child (I, j, s) = some J → P (j + 1) (R.combine (I, j, s, ans J))) :
    ∀ (k j : ℕ) (s : ω) (b : Bool), P j s →
      ∃ j' s' b', (R.foldStep ans)^[k] ((I, j, s), b) = ((I, j', s'), b') ∧ P j' s' := by
  intro k
  induction k with
  | zero => intro j s b h; exact ⟨j, s, b, rfl, h⟩
  | succ k ih =>
    intro j s b h
    rw [Function.iterate_succ_apply]
    cases b with
    | true =>
      rw [R.foldStep_done (st := ((I, j, s), true)) rfl]
      exact ih j s true h
    | false =>
      cases hc : R.child (I, j, s) with
      | none =>
        have h1 : R.foldStep ans ((I, j, s), false) = ((I, j, s), true) := by
          simp [foldStep, foldAsk, foldStop, hc]
        rw [h1]
        exact ih j s true h
      | some J =>
        have h1 : R.foldStep ans ((I, j, s), false)
            = ((I, j + 1, R.combine (I, j, s, ans J)), false) := by
          simp [foldStep, foldAsk, foldFeed, hc]
        rw [h1]
        exact ih _ _ false (hP j s J h hc)

/-- Every call of the fold is a child at a state satisfying an invariant. -/
theorem mem_loopCalls_inv (ans : ι → α) (I : ι) (P : ℕ → ω → Prop)
    (hP : ∀ j s J, P j s → R.child (I, j, s) = some J → P (j + 1) (R.combine (I, j, s, ans J))) :
    ∀ (w j : ℕ) (s : ω), P j s → ∀ J ∈ R.loopCalls ans w I j s,
      ∃ j' s', P j' s' ∧ R.child (I, j', s') = some J := by
  intro w
  induction w with
  | zero => intro j s _ J hJ; simp at hJ
  | succ w ih =>
    intro j s h J hJ
    cases hc : R.child (I, j, s) with
    | none => rw [R.loopCalls_succ_none hc] at hJ; simp at hJ
    | some J' =>
      rw [R.loopCalls_succ_some hc] at hJ
      rcases List.mem_cons.1 hJ with rfl | hJ
      · exact ⟨j, s, h, hc⟩
      · exact ih (j + 1) _ (hP j s J' h hc) J hJ

/-- The index of a child is below the width. -/
theorem lt_width_of_child {I : ι} {j : ℕ} {s : ω} {J : ι} (hc : R.child (I, j, s) = some J) :
    j < R.width I := by
  by_contra h
  rw [R.child_eq_none I j s (by omega)] at hc
  exact absurd hc (by simp)

/-- The size of a state of the fold. -/
theorem size_foldSt_le [Enc ι] [Enc ω] (I : ι) (j : ℕ) (s : ω) (b : Bool) :
    Enc.size (((I, j, s), b) : FoldSt ι ω)
      ≤ 4 * Enc.size I + 8 * Enc.size j + 8 * Enc.size s + 6 := by
  have h1 := size_pair_le' (((I, j, s), b) : FoldSt ι ω)
  have h2 := size_pair_le' ((I, j, s) : ι × ℕ × ω)
  have h3 := size_pair_le' ((j, s) : ℕ × ω)
  have h4 := Combine.size_bool_le b
  simp only at h1 h2 h3
  omega

end Inv

end Round

end Algo
