/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Proposition 13.1.11 on the RAM.
-/
import Workspace.Algo.LocalCertCompare

/-!
# Proposition 13.1.11 on the RAM

> **Proposition 13.1.11** (Comparing local certificates). For all test sets `T, T' ⊆ Γ` with
> `|T| = |T'| = t` and all strings `x, x' : Ω → Σ` we can compute
> `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})` by making `≤ t!n²` calls to String Isomorphism
> problems on domains of size `≤ n/t` and performing `t! poly(n)` computation.

The paper counts the String Isomorphism calls and the other computation separately, and so do
the statements here.  `Algo.proposition_13_1_11_ram` is one program transformer `F`: for every
program `Q` answering String Isomorphism on the windows, `F Q` runs the paired procedure of
`Workspace/Algo/LocalCertCompare.lean` within

  `10⁸ · ∑_{W ∈ calls} τ(W) + t! · poly(size of the input)`

RAM steps, `τ(W)` being the number of steps of `Q` on the call `W`: the calls are paid for at
their own cost, and everything else is `t! poly(n)`.  The calls are `Algo.pcCallsQ`: at most
`t!·n²` of them, each on a window of at most `n/t` points; and the output is
`Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})` (`Algo.proposition_13_1_11_ram_spec`).

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets Babai
open Equiv (Perm)

/-! ## The routines are polynomial time -/

theorem polyFun_isSome' {α : Type*} [Enc α] : PolyFun (@Option.isSome α) := by
  have h : PolyFun (fun z : Option α × Bool => z.1.elim false (fun _ => true)) :=
    PolyFun.optionElim (polyFun_const false) (polyFun_const true)
  exact ((polyFun_id.pair (polyFun_const false)).comp h).of_eq
    (fun z => by cases z <;> rfl)

theorem polyFun_pcCond : PolyFun pcCond := by
  have hp : PolyFun (fun z : RawPCLoop => lcCond z.1) := polyFun_fst.comp polyFun_lcCond
  have hq : PolyFun (fun z : RawPCLoop => z.2.2.isSome) :=
    (polyFun_snd.comp polyFun_snd).comp polyFun_isSome'
  exact (PolyFun.ite hp hq (polyFun_const false)).of_eq (fun z => by
    simp only [pcCond]; cases lcCond z.1 <;> rfl)

theorem polyFun_pcRep : PolyFun pcRep := by
  have hx : PolyFun (fun z : RawPCLoop => z.1.1.1) := polyFun_fst.comp polyFun_lcStr
  have hq : PolyFun (fun z : RawPCLoop => z.2.2.getD ([], rawOne z.1.1.1)) :=
    ((polyFun_snd.comp polyFun_snd).pair
      ((polyFun_const ([] : RawGens)).pair (hx.comp polyFun_rawOne))).comp polyFun_optionGetD
  exact ((hx.pair (hq.comp polyFun_snd)).comp polyFun_normPerm).of_eq (fun _ => rfl)

theorem polyFun_pcInst : PolyFun pcInst := by
  have hL : PolyFun (fun z : RawPCLoop => lcInst z.1) := polyFun_fst.comp polyFun_lcInst
  have hW : PolyFun (fun z : RawPCLoop => (lcInst z.1).1.1) := (hL.comp polyFun_fst).comp polyFun_fst
  have hG : PolyFun (fun z : RawPCLoop => (lcInst z.1).1.2.1) :=
    ((hL.comp polyFun_fst).comp polyFun_snd).comp polyFun_fst
  have hx : PolyFun (fun z : RawPCLoop => z.1.1.1) := polyFun_fst.comp polyFun_lcStr
  have hy : PolyFun (fun z : RawPCLoop => z.2.1) := polyFun_snd.comp polyFun_fst
  have hD : PolyFun (fun z : RawPCLoop => (lcInst z.1).2) := hL.comp polyFun_snd
  exact ((hW.pair (hG.pair (polyFun_pcRep.pair (hx.pair hy)))).pair hD).of_eq (fun _ => rfl)

theorem polyFun_pcPost :
    PolyFun (fun w : RawCoset × RawCoset × RawPCLoop => pcStepWith w.1 w.2.1 w.2.2) := by
  have hz : PolyFun (fun w : RawCoset × RawCoset × RawPCLoop => w.2.2) :=
    polyFun_snd.comp polyFun_snd
  have hs : PolyFun (fun w : RawCoset × RawCoset × RawPCLoop => lcStepWith w.1 w.2.2.1) :=
    (polyFun_fst.pair (hz.comp polyFun_fst)).comp lcwPolyFun_step
  have hy : PolyFun (fun w : RawCoset × RawCoset × RawPCLoop => w.2.2.2.1) :=
    (hz.comp polyFun_snd).comp polyFun_fst
  have hb : PolyFun (fun w : RawCoset × RawCoset × RawPCLoop => w.2.1) :=
    polyFun_snd.comp polyFun_fst
  exact (hs.pair (hy.pair hb)).of_eq (fun _ => rfl)

/-! ## The states stay small -/

theorem size_pcStep_iterate_p (solve : RawLCSI → RawCoset) :
    ∀ (j : ℕ) (z : RawPCLoop),
      Enc.size ((pcStep solve)^[j] z).1.2 ≤ max (Enc.size z.1.2) (lcStBound (Enc.size z.1.1))
  | 0, _ => le_max_left _ _
  | j + 1, z => by
    rw [Function.iterate_succ_apply']
    have ih := size_pcStep_iterate_p solve j z
    have hctx : ((pcStep solve)^[j] z).1.1 = z.1.1 := (pcStep_iterate_ctx solve j z).1
    unfold pcStep
    split
    · show Enc.size (lcStepWith _ ((pcStep solve)^[j] z).1).2 ≤ _
      refine (lcwSize_step _ _).trans (max_le ih ?_)
      rw [hctx]; exact le_max_right _ _
    · exact ih

theorem size_pcStep_iterate_q {n : ℕ} {ansQ : RawWinSI → RawCoset} {z : RawPCLoop}
    (hlive : ∀ j, pcCond ((pcStep (lcSolveQ ansQ))^[j] z) = true →
      LCWF n (pcInst ((pcStep (lcSolveQ ansQ))^[j] z))) :
    ∀ j, Enc.size ((pcStep (lcSolveQ ansQ))^[j] z).2.2
      ≤ max (Enc.size z.2.2) (lcBound (Enc.size ((z.1.1.1, z.2.1) : RawStr × RawStr)))
  | 0 => le_max_left _ _
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := size_pcStep_iterate_q hlive j
    have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z
    by_cases hcnd : pcCond ((pcStep (lcSolveQ ansQ))^[j] z) = true
    · rw [pcStep, if_pos hcnd]
      show Enc.size (lcSolveQ ansQ (pcInst ((pcStep (lcSolveQ ansQ))^[j] z))) ≤ _
      refine (size_lcSolveQ_desc_le (hlive j hcnd) rfl).trans
        (le_trans (le_of_eq ?_) (le_max_right _ _))
      show lcBound (Enc.size ((((pcStep (lcSolveQ ansQ))^[j] z).1.1.1,
        ((pcStep (lcSolveQ ansQ))^[j] z).2.1) : RawStr × RawStr)) = _
      rw [hctx.1, hctx.2]
    · rw [pcStep, if_neg hcnd]; exact ih

/-! ## Proposition 13.1.11 on the RAM -/

set_option maxHeartbeats 16000000 in
/-- **Proposition 13.1.11 on the RAM** (§13.1), the running time.  One program transformer
`F`: for every program `Q` that answers the well-formed String Isomorphism instances, `F Q`
runs the paired procedure (Procedure LocalCertificates on `(x, T)` with Procedure Recompute
`H(W)` and `Q`) within

  `10⁸ · ∑_{W ∈ calls} τ(W) + t! · poly(size of the input)`

steps, where `τ(W)` is the number of steps of `Q` on the call `W`: the String Isomorphism
calls at their own cost, and `t! poly(n)` other computation.  The calls are `Algo.pcCallsQ`
(at most `t!·n²`, on windows of at most `n/t` points); the output is
`Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})`: `Algo.proposition_13_1_11_ram_spec`.  The initial `Q`
is the transporter set of line 01, `G_Tσ`.  The polynomial depends on the polynomial `S`
that bounds the size of the answers of `Q`, and on nothing else. -/
theorem proposition_13_1_11_ram (S : ℕ → ℕ) (hS : PolyBound S) :
    ∃ (F : Program → Program) (c d : ℕ), ∀ Q : Program, Wf Q → Wf (F Q) ∧
      ∀ {n m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)} {xs ys : RawStr}
        {tdom : List ℕ} (hc : LCCtxWF n m xs tdom), ys.length = n → ∀ {T' : Set (Fin m)}
        {st0 : RawLCSt} {q0 : RawCoset},
        StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0 →
        decCoset n q0 = pcTransporters ϕ (winSet m tdom) T' →
        ∀ (ansQ : RawWinSI → RawCoset) (τ : RawWinSI → ℕ),
        (∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧ Enc.size (ansQ W) ≤ S (Enc.size W) ∧
          decCoset n (ansQ W) = (decWinSI n W).answer) →
        RunsOn 16 (F Q) ((((xs, tdom), st0), ys, q0) : RawPCLoop)
          (pcOut (lcSolveQ ansQ) (((xs, tdom), st0), ys, q0))
          (10 ^ 8 * ((pcCallsQ ansQ (((xs, tdom), st0), ys, q0)).map τ).sum
            + Nat.factorial tdom.length
              * pw c d (Enc.size ((((xs, tdom), st0), ys, q0) : RawPCLoop))) := by
  obtain ⟨RC, cR, dR, hRC⟩ := exists_recomputeProg S hS
  obtain ⟨Pstart, c6, d6, hstart, -⟩ := polyFun_witness
    (show PolyFun (fun z : RawPCLoop => (z.1.1.1.length, z)) from
      ((polyFun_fst.comp polyFun_lcStr).comp polyFun_length).pair polyFun_id)
  obtain ⟨Pend, c7, d7, hend, -⟩ := polyFun_witness
    (show PolyFun (fun w : ℕ × RawPCLoop => w.2.2.2) from
      (polyFun_snd.comp polyFun_snd).comp polyFun_snd)
  obtain ⟨Pcond, cC, dC, hcond, hcond_s⟩ := polyFun_witness
    (show PolyFun (fun z : RawPCLoop =>
        ((if pcCond z then some (lcInst z.1, pcInst z) else none, z)
          : Option (RawLCSI × RawLCSI) × RawPCLoop)) from
      (PolyFun.ite polyFun_pcCond
        (((polyFun_fst.comp polyFun_lcInst).pair polyFun_pcInst).comp polyFun_some)
        polyFun_none).pair polyFun_id)
  obtain ⟨Pid, cI, dI, hid, -⟩ :=
    polyFun_witness (polyFun_id : PolyFun (id : RawPCLoop → RawPCLoop))
  obtain ⟨Pa, ca, da, ha, -⟩ := polyFun_witness
    (show PolyFun (fun w : (RawLCSI × RawLCSI) × RawPCLoop => w.1.1) from
      polyFun_fst.comp polyFun_fst)
  obtain ⟨Pb, cb, db, hb, -⟩ := polyFun_witness
    (show PolyFun (fun w : (RawLCSI × RawLCSI) × RawPCLoop => w.1.2) from
      polyFun_fst.comp polyFun_snd)
  obtain ⟨Pz, cz, dz, hzp, -⟩ := polyFun_witness
    (show PolyFun (fun w : (RawLCSI × RawLCSI) × RawPCLoop => w.2) from polyFun_snd)
  obtain ⟨Ppost, c5, d5, hpost, -⟩ := polyFun_witness polyFun_pcPost
  obtain ⟨Ppred, cP, dP, hpred, -⟩ := polyFun_witness
    ((polyFun_fst.sub (polyFun_const 1)) : PolyFun (fun z : ℕ × RawPCLoop => z.1 - 1))
  obtain ⟨Psnd, cS, dS, hsnd, -⟩ :=
    polyFun_witness (polyFun_snd : PolyFun (fun z : ℕ × RawPCLoop => z.2))
  -- the size bounds, in the size `M` of the input
  obtain ⟨ZI, hZI⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = lcBound (4 * M) := ⟨_, fun _ => rfl⟩
  obtain ⟨Zq, hZq⟩ : ∃ f : ℕ → ℕ, ∀ M,
      f M = 4 * M + 4 * (M + lcStBound M) + 4 * M + 4 * (M + ZI M) := ⟨_, fun _ => rfl⟩
  obtain ⟨Zk, hZk⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = M + 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨Zp, hZp⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 2 * Zk M + 2 * Zq M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zw, hZw⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 8 * ZI M + 2 * Zq M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zbz, hZbz⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 2 * ZI M + 2 * Zq M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zabz, hZabz⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 2 * ZI M + 2 * Zbz M := ⟨_, fun _ => rfl⟩
  obtain ⟨Zc, hZc⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = pw cC dC (Zq M) := ⟨_, fun _ => rfl⟩
  obtain ⟨PR, hPR⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = pw cR dR (ZI M) := ⟨_, fun _ => rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 50 * Zc M + 300 * Zw M + 300 * ZI M
      + 300 * Zbz M + 300 * Zq M + 10 * pw ca da (Zw M) + 100 * pw cb db (Zw M)
      + 100 * pw cz dz (Zw M) + pw c5 d5 (Zabz M) + pw cI dI (Zq M) + 5000 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = 19 * Zp M + 19 * Zk M + 19 * Zq M
      + 10 * pw cP dP (Zp M) + 10 * pw cS dS (Zp M) + 376 + 10 * E1 M := ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℕ → ℕ, ∀ M, f M = M * (3300 * PR M + E2 M + 2) + 1 + pw c6 d6 M
      + pw c7 d7 (Zp M) := ⟨_, fun _ => rfl⟩
  have hGfP : PolyBound Gf := by
    have pZI : PolyBound ZI := by
      rw [show ZI = _ from funext hZI]
      exact polyBound_lcBound.comp ((polyBound_const 4).mul polyBound_id)
    have pZq : PolyBound Zq := by
      rw [show Zq = _ from funext hZq]
      exact ((((polyBound_const 4).mul polyBound_id).add ((polyBound_const 4).mul
        (polyBound_id.add polyBound_lcStBound))).add ((polyBound_const 4).mul polyBound_id)).add
        ((polyBound_const 4).mul (polyBound_id.add pZI))
    have pZk : PolyBound Zk := by
      rw [show Zk = _ from funext hZk]; exact polyBound_id.add (polyBound_const 2)
    have pZp : PolyBound Zp := by
      rw [show Zp = _ from funext hZp]
      exact ((polyBound_const 2).mul pZk).add ((polyBound_const 2).mul pZq)
    have pZw : PolyBound Zw := by
      rw [show Zw = _ from funext hZw]
      exact ((polyBound_const 8).mul pZI).add ((polyBound_const 2).mul pZq)
    have pZbz : PolyBound Zbz := by
      rw [show Zbz = _ from funext hZbz]
      exact ((polyBound_const 2).mul pZI).add ((polyBound_const 2).mul pZq)
    have pZabz : PolyBound Zabz := by
      rw [show Zabz = _ from funext hZabz]
      exact ((polyBound_const 2).mul pZI).add ((polyBound_const 2).mul pZbz)
    have pZc : PolyBound Zc := by
      rw [show Zc = _ from funext hZc]; exact (polyBound_pw cC dC).comp pZq
    have pPR : PolyBound PR := by
      rw [show PR = _ from funext hPR]; exact (polyBound_pw cR dR).comp pZI
    have pE1 : PolyBound E1 := by
      rw [show E1 = _ from funext hE1]
      exact ((((((((((((polyBound_const 50).mul pZc).add ((polyBound_const 300).mul pZw)).add
        ((polyBound_const 300).mul pZI)).add ((polyBound_const 300).mul pZbz)).add
        ((polyBound_const 300).mul pZq)).add ((polyBound_const 10).mul
          ((polyBound_pw ca da).comp pZw))).add ((polyBound_const 100).mul
          ((polyBound_pw cb db).comp pZw))).add ((polyBound_const 100).mul
          ((polyBound_pw cz dz).comp pZw))).add ((polyBound_pw c5 d5).comp pZabz)).add
        ((polyBound_pw cI dI).comp pZq)).add (polyBound_const 5000))
    have pE2 : PolyBound E2 := by
      rw [show E2 = _ from funext hE2]
      exact ((((((polyBound_const 19).mul pZp).add ((polyBound_const 19).mul pZk)).add
        ((polyBound_const 19).mul pZq)).add ((polyBound_const 10).mul
          ((polyBound_pw cP dP).comp pZp))).add ((polyBound_const 10).mul
          ((polyBound_pw cS dS).comp pZp))).add (polyBound_const 376) |>.add
        ((polyBound_const 10).mul pE1)
    rw [show Gf = _ from funext hGf]
    exact (((polyBound_id.mul ((((polyBound_const 3300).mul pPR).add pE2).add
      (polyBound_const 2))).add (polyBound_const 1)).add (polyBound_pw c6 d6)).add
      ((polyBound_pw c7 d7).comp pZp)
  obtain ⟨c, d, hcd⟩ := hGfP
  -- the programs
  let SomeBr : Program → Program := fun Q =>
    RAM.seq (Pairing.pairProg 16 (RAM.seq Pa (RC Q))
      (Pairing.pairProg 16 (RAM.seq Pb (RC Q)) Pz)) Ppost
  let Step : Program → Program := fun Q =>
    RAM.seq Pcond (Lists.optElimProg 16 Pid (SomeBr Q))
  let Body : Program → Program := fun Q => Pairing.pairProg 16 Ppred (RAM.seq Psnd (Step Q))
  refine ⟨fun Q => RAM.seq Pstart (RAM.seq (whileNz 18 (Body Q)) Pend), c, d, ?_⟩
  intro Q hQwf
  obtain ⟨hRCwf, hRCrun⟩ := hRC Q hQwf
  have hSomeWf : Wf (SomeBr Q) :=
    wf_seq (Pairing.wf_pairProg 16 (wf_seq (CleanComputeAt.wf' ha) hRCwf)
      (Pairing.wf_pairProg 16 (wf_seq (CleanComputeAt.wf' hb) hRCwf)
        (CleanComputeAt.wf' hzp))) (CleanComputeAt.wf' hpost)
  have hStepWf : Wf (Step Q) :=
    wf_seq (CleanComputeAt.wf' hcond) (Lists.wf_optElimProg (by omega) (CleanComputeAt.wf' hid)
      hSomeWf)
  have hBodyWf : Wf (Body Q) :=
    Pairing.wf_pairProg 16 (CleanComputeAt.wf' hpred) (wf_seq (CleanComputeAt.wf' hsnd) hStepWf)
  refine ⟨wf_seq (CleanComputeAt.wf' hstart) (wf_seq (wf_whileNz hBodyWf)
    (CleanComputeAt.wf' hend)), ?_⟩
  intro n m G ϕ xs ys tdom hc hy T' st0 q0 h0 hq0 ansQ τ hQ
  have hQ' : ∀ W, WinWF n W → RunsOn 16 Q W (ansQ W) (τ W) ∧
      Enc.size (ansQ W) ≤ S (Enc.size W) := fun W hW => ⟨(hQ W hW).1, (hQ W hW).2.1⟩
  have hQc : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer :=
    fun W hW => (hQ W hW).2.2
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQc hI
  -- notation
  set z0 : RawPCLoop := (((xs, tdom), st0), ys, q0) with hz0
  obtain ⟨M, hM⟩ : ∃ M, M = Enc.size z0 := ⟨_, rfl⟩
  set step := pcStep (lcSolveQ ansQ) with hstepdef
  set N := xs.length with hN
  set f := Nat.factorial tdom.length with hf
  have hf1 : 1 ≤ f := Nat.factorial_pos _
  have hp0M : Enc.size z0.1 ≤ M := hM ▸ size_fst_le' z0
  have hyq0M : Enc.size z0.2 ≤ M := hM ▸ size_snd_le' z0
  have hctx0M : Enc.size z0.1.1 ≤ M := le_trans (size_fst_le' z0.1) hp0M
  have hst0M : Enc.size z0.1.2 ≤ M := le_trans (size_snd_le' z0.1) hp0M
  have hxsM : Enc.size xs ≤ M := le_trans (size_fst_le' z0.1.1) hctx0M
  have hysM : Enc.size ys ≤ M := le_trans (size_fst_le' z0.2) hyq0M
  have hq0M : Enc.size q0 ≤ M := le_trans (size_snd_le' z0.2) hyq0M
  have hNM : N ≤ M := le_trans (lcDeg_le z0.1) hctx0M
  have hq0M' : Enc.size z0.2.2 ≤ M := hq0M
  have hxy : Enc.size ((xs, ys) : RawStr × RawStr) ≤ 4 * M := by
    have := size_pair_le' ((xs, ys) : RawStr × RawStr); simp only at this; omega
  have hxx : Enc.size ((xs, xs) : RawStr × RawStr) ≤ 4 * M := by
    have := size_pair_le' ((xs, xs) : RawStr × RawStr); simp only at this; omega
  have hZIM := hZI M
  have hZqM := hZq M
  have hZkM := hZk M
  have hZpM := hZp M
  have hZwM := hZw M
  have hZbzM := hZbz M
  have hZabzM := hZabz M
  have hZcM := hZc M
  have hPRM := hPR M
  have hE1M := hE1 M
  have hE2M := hE2 M
  -- the rounds that run are live
  have hlive : ∀ j, pcCond (step^[j] z0) = true →
      ∃ st, step^[j] z0 = (((xs, tdom), st), ys, (step^[j] z0).2.2) ∧
        StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) j) st := by
    intro j hj
    obtain ⟨-, st, h1, h2⟩ := pc_live hsolve hy h0 hq0 hj
    have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z0
    exact ⟨st, Prod.ext h1 (Prod.ext hctx.2 rfl), h2⟩
  have hliveI : ∀ j, pcCond (step^[j] z0) = true → LCWF n (pcInst (step^[j] z0)) := by
    intro j hj
    obtain ⟨st, he, h2⟩ := hlive j hj
    rw [he]; exact lcwf_pcInst h2 hy _
  -- the states of the loop are small
  have hqsize : ∀ j, Enc.size (step^[j] z0) ≤ Zq M := by
    intro j
    have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z0
    have h1 := size_pair_le' (step^[j] z0)
    have h2 := size_pair_le' (step^[j] z0).1
    have h3 := size_pair_le' (step^[j] z0).2
    have h4 : Enc.size (step^[j] z0).1.2 ≤ max (Enc.size z0.1.2) (lcStBound (Enc.size z0.1.1)) :=
      size_pcStep_iterate_p (lcSolveQ ansQ) j z0
    have h5 : Enc.size (step^[j] z0).2.2
        ≤ max (Enc.size z0.2.2) (lcBound (Enc.size ((z0.1.1.1, z0.2.1) : RawStr × RawStr))) :=
      size_pcStep_iterate_q hliveI j
    have h6 : lcStBound (Enc.size z0.1.1) ≤ lcStBound M := mono_lcStBound hctx0M
    have h7 : lcBound (Enc.size ((z0.1.1.1, z0.2.1) : RawStr × RawStr)) ≤ ZI M := by
      rw [hZIM]; exact mono_lcBound hxy
    have h8 : Enc.size (step^[j] z0).1.1 ≤ M := by rw [hctx.1]; exact hctx0M
    have h9 : Enc.size (step^[j] z0).2.1 ≤ M := by rw [hctx.2]; exact hysM
    have h10 : max (Enc.size z0.1.2) (lcStBound (Enc.size z0.1.1)) ≤ M + lcStBound M :=
      max_le (by omega) (by omega)
    have h11 : max (Enc.size z0.2.2) (lcBound (Enc.size ((z0.1.1.1, z0.2.1) : RawStr × RawStr)))
        ≤ M + ZI M := max_le (by omega) (by omega)
    omega
  have hksize : ∀ k ≤ N, Enc.size k ≤ Zk M := by
    intro k hk
    have := size_nat_le_add_two k
    omega
  -- one step of the while loop
  have hstep : ∀ j < N, RunsOn 16 (Step Q) (step^[j] z0) (step^[j + 1] z0)
      (10 ^ 7 * ((pcStepCalls ansQ (step^[j] z0)).map τ).sum + 110 * ((f + 2) * PR M)
        + E1 M) := by
    intro j hj
    set z := step^[j] z0 with hzdef
    have hzs : Enc.size z ≤ Zq M := hqsize j
    have hnext : step^[j + 1] z0 = step z := Function.iterate_succ_apply' step j z0
    rw [hnext]
    have ect : cC * (Enc.size z + 1) ^ dC ≤ Zc M := by
      have e2 : cC * (Enc.size z + 1) ^ dC ≤ pw cC dC (Zq M) := pw_mono cC dC hzs
      omega
    have hcs : Enc.size ((if pcCond z then some (lcInst z.1, pcInst z) else none, z)
        : Option (RawLCSI × RawLCSI) × RawPCLoop) ≤ Zc M := by
      have e1 := hcond_s z
      simp only at e1
      omega
    by_cases hcnd : pcCond z = true
    · -- lines 04a–04h run
      obtain ⟨st, he, hst⟩ := hlive j hcnd
      have hctx := pcStep_iterate_ctx (lcSolveQ ansQ) j z0
      set I1 := lcInst z.1 with hI1def
      set I2 := pcInst z with hI2def
      have hI1 : LCWF n I1 := by
        rw [hI1def, show z.1 = ((xs, tdom), st) from congrArg Prod.fst he]
        exact lcwf_lcInst hst
      have hI2 : LCWF n I2 := hliveI j hcnd
      have hs1 : I1.2 = some ((z.1.1.2, z.1.2.2.2), lcIdx z.1) := rfl
      have hs2 : I2.2 = some ((z.1.1.2, z.1.2.2.2), lcIdx z.1) := rfl
      obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI1.2 _ _ hs1
      have hidx0 : lcIdx z.1 ≤ Nat.factorial (z.1.1.2, z.1.2.2.2).1.length :=
        lcWidth_le_factorial hI1 hs1 hψ
      have htd : (z.1.1.2, z.1.2.2.2).1 = tdom := by
        show z.1.1.2 = tdom
        rw [hzdef, hctx.1]
      have hidx : lcIdx z.1 ≤ f := by rw [htd] at hidx0; exact hidx0
      have hrc1 := hRCrun n ansQ τ I1 _ _ hI1 hs1 hQ'
      have hrc2 := hRCrun n ansQ τ I2 _ _ hI2 hs2 hQ'
      have hg1 : lcGround I1 ≤ 4 * M := by
        have e1 : lcGround I1 = Enc.size ((z.1.1.1, z.1.1.1) : RawStr × RawStr) := by
          rw [hI1def]; rfl
        have e3 : z.1.1.1 = xs := by rw [hzdef, hctx.1]
        rw [e1, e3]; exact hxx
      have hg2 : lcGround I2 ≤ 4 * M := by
        have e1 : lcGround I2 = Enc.size ((z.1.1.1, z.2.1) : RawStr × RawStr) := by
          rw [hI2def]; rfl
        have e3 : z.1.1.1 = xs := by rw [hzdef, hctx.1]
        have e4 : z.2.1 = ys := by rw [hzdef, hctx.2]
        rw [e1, e3, e4]; exact hxy
      have hI1sz : Enc.size I1 ≤ ZI M := by
        have e1 : Enc.size I1 ≤ lcBound (lcGround I1) := size_lcSI_le hI1
        have e2 : lcBound (lcGround I1) ≤ lcBound (4 * M) := mono_lcBound hg1
        omega
      have hI2sz : Enc.size I2 ≤ ZI M := by
        have e1 : Enc.size I2 ≤ lcBound (lcGround I2) := size_lcSI_le hI2
        have e2 : lcBound (lcGround I2) ≤ lcBound (4 * M) := mono_lcBound hg2
        omega
      have ha1 : Enc.size (lcSolveQ ansQ I1) ≤ ZI M := by
        have e1 := size_lcSolveQ_desc_le (ansQ := ansQ) hI1 hs1
        have e2 : lcBound (lcGround I1) ≤ lcBound (4 * M) := mono_lcBound hg1
        omega
      have ha2 : Enc.size (lcSolveQ ansQ I2) ≤ ZI M := by
        have e1 := size_lcSolveQ_desc_le (ansQ := ansQ) hI2 hs2
        have e2 : lcBound (lcGround I2) ≤ lcBound (4 * M) := mono_lcBound hg2
        omega
      set w : (RawLCSI × RawLCSI) × RawPCLoop := ((I1, I2), z) with hw
      have ra := (ha.runsOn w).seq hrc1
      have rb := (hb.runsOn w).seq hrc2
      have rbz := RunsOn.pair (K := 16) (by omega) rb (hzp.runsOn w)
      have rall := RunsOn.pair (K := 16) (by omega) ra rbz
      have r3 := rall.seq (hpost.runsOn
        ((lcSolveQ ansQ I1, lcSolveQ ansQ I2, z) : RawCoset × RawCoset × RawPCLoop))
      have r4 := RunsOn.optionElim_some (Pg := Pid) (K := 16) (by omega)
        (CleanComputeAt.wf' hid) r3
      have ht : ((if pcCond z then some (lcInst z.1, pcInst z) else none, z)
          : Option (RawLCSI × RawLCSI) × RawPCLoop)
          = ((some (I1, I2), z) : Option (RawLCSI × RawLCSI) × RawPCLoop) := by
        rw [if_pos hcnd]
      rw [← ht] at r4
      have r5 := (hcond.runsOn z).seq r4
      have hval : pcStepWith (lcSolveQ ansQ I1) (lcSolveQ ansQ I2) z = step z := by
        show _ = pcStep (lcSolveQ ansQ) z
        rw [pcStep, if_pos hcnd]
      simp only at r5
      rw [hval] at r5
      refine r5.mono ?_
      have hcalls : pcStepCalls ansQ z = lcDescCalls ansQ I1 ++ lcDescCalls ansQ I2 := by
        rw [pcStepCalls, if_pos hcnd]
      rw [hcalls, List.map_append, List.sum_append]
      have hwsz : Enc.size w ≤ Zw M := by
        have e1 : Enc.size w ≤ 2 * Enc.size ((I1, I2) : RawLCSI × RawLCSI) + 2 * Enc.size z :=
          size_pair_le' w
        have e2 : Enc.size ((I1, I2) : RawLCSI × RawLCSI) ≤ 2 * Enc.size I1 + 2 * Enc.size I2 :=
          size_pair_le' _
        omega
      have hbz : Enc.size ((lcSolveQ ansQ I2, z) : RawCoset × RawPCLoop) ≤ Zbz M := by
        have := size_pair_le' ((lcSolveQ ansQ I2, z) : RawCoset × RawPCLoop)
        simp only at this; omega
      have habz : Enc.size ((lcSolveQ ansQ I1, lcSolveQ ansQ I2, z)
          : RawCoset × RawCoset × RawPCLoop) ≤ Zabz M := by
        have := size_pair_le' ((lcSolveQ ansQ I1, lcSolveQ ansQ I2, z)
          : RawCoset × RawCoset × RawPCLoop)
        simp only at this; omega
      have e3 : ca * (Enc.size w + 1) ^ da ≤ pw ca da (Zw M) := pw_mono ca da hwsz
      have e4 : cb * (Enc.size w + 1) ^ db ≤ pw cb db (Zw M) := pw_mono cb db hwsz
      have e4' : cz * (Enc.size w + 1) ^ dz ≤ pw cz dz (Zw M) := pw_mono cz dz hwsz
      have e5 : c5 * (Enc.size ((lcSolveQ ansQ I1, lcSolveQ ansQ I2, z)
          : RawCoset × RawCoset × RawPCLoop) + 1) ^ d5 ≤ pw c5 d5 (Zabz M) :=
        pw_mono c5 d5 habz
      have e6 : pw cR dR (Enc.size I1) ≤ PR M := by rw [hPRM]; exact pw_mono cR dR hI1sz
      have e6' : pw cR dR (Enc.size I2) ≤ PR M := by rw [hPRM]; exact pw_mono cR dR hI2sz
      have e7 : (lcIdx z.1 + 2) * pw cR dR (Enc.size I1) ≤ (f + 2) * PR M :=
        Nat.mul_le_mul (by omega) e6
      have e7' : (lcIdx z.1 + 2) * pw cR dR (Enc.size I2) ≤ (f + 2) * PR M :=
        Nat.mul_le_mul (by omega) e6'
      have hcs' : Enc.size ((if pcCond z then some (lcInst z.1, pcInst z) else none, z)
          : Option (RawLCSI × RawLCSI) × RawPCLoop) ≤ Zc M := hcs
      have e8 : 0 ≤ pw cI dI (Zq M) := Nat.zero_le _
      have ew2 : Enc.size w.2 = Enc.size z := rfl
      have ebz : Enc.size ((lcSolveQ ansQ I2, w.2) : RawCoset × RawPCLoop)
          = Enc.size ((lcSolveQ ansQ I2, z) : RawCoset × RawPCLoop) := rfl
      omega
    · -- the loop has stopped: the step is the identity
      have hcf : pcCond z = false := by simpa using hcnd
      have hsq : step z = z := pcStep_of_not_cond _ hcf
      have r4 := RunsOn.optionElim_none (β := RawLCSI × RawLCSI) (K := 16) (by omega) hSomeWf
        (hid.runsOn z)
      have ht : ((if pcCond z then some (lcInst z.1, pcInst z) else none, z)
          : Option (RawLCSI × RawLCSI) × RawPCLoop)
          = ((none, z) : Option (RawLCSI × RawLCSI) × RawPCLoop) := by rw [if_neg hcnd]
      rw [← ht] at r4
      have r5 := (hcond.runsOn z).seq r4
      rw [hsq]
      refine r5.mono ?_
      have hcalls : pcStepCalls ansQ z = [] := by rw [pcStepCalls, if_neg hcnd]
      rw [hcalls]
      have e1 : cI * (Enc.size (id z) + 1) ^ dI ≤ pw cI dI (Zq M) := pw_mono cI dI hzs
      simp only [List.map_nil, List.sum_nil, id] at e1 ⊢
      omega
  -- one pass of the body
  have hbody : ∀ j < N, RunsOn 16 (Body Q) ((N - j, step^[j] z0) : ℕ × RawPCLoop)
      ((N - (j + 1), step^[j + 1] z0) : ℕ × RawPCLoop)
      (10 ^ 8 * ((pcStepCalls ansQ (step^[j] z0)).map τ).sum + 1100 * ((f + 2) * PR M)
        + E2 M) := by
    intro j hj
    have r1 := hpred.runsOn ((N - j, step^[j] z0) : ℕ × RawPCLoop)
    have r2 := (hsnd.runsOn ((N - j, step^[j] z0) : ℕ × RawPCLoop)).seq (hstep j hj)
    have r3 := RunsOn.pair (K := 16) (by omega) r1 r2
    simp only at r3
    rw [show N - j - 1 = N - (j + 1) by omega] at r3
    refine r3.mono ?_
    have hp1 : Enc.size ((N - j, step^[j] z0) : ℕ × RawPCLoop) ≤ Zp M := by
      have := size_pair_le' ((N - j, step^[j] z0) : ℕ × RawPCLoop)
      have h1 := hksize (N - j) (by omega)
      have h2 := hqsize j
      simp only at this; omega
    have h3 := hksize (N - (j + 1)) (by omega)
    have h4 := hqsize (j + 1)
    have e1 : cP * (Enc.size ((N - j, step^[j] z0) : ℕ × RawPCLoop) + 1) ^ dP
        ≤ pw cP dP (Zp M) := pw_mono cP dP hp1
    have e2 : cS * (Enc.size ((N - j, step^[j] z0) : ℕ × RawPCLoop) + 1) ^ dS
        ≤ pw cS dS (Zp M) := pw_mono cS dS hp1
    omega
  -- the loop, the setup and the read-off
  have hloop := runsOn_iterate_sum (K := 16) (Q := Body Q) (step := step) hBodyWf N z0 _ hbody
  have hs1 : RunsOn 16 Pstart z0 ((N, z0) : ℕ × RawPCLoop) (c6 * (Enc.size z0 + 1) ^ d6) :=
    hstart.runsOn z0
  have hs3 := hend.runsOn ((0 : ℕ), step^[N] z0)
  have hall := hs1.seq (hloop.seq hs3)
  have hout : ((((0 : ℕ), step^[N] z0) : ℕ × RawPCLoop).2.2.2)
      = pcOut (lcSolveQ ansQ) z0 := rfl
  simp only at hall
  rw [hout] at hall
  refine hall.mono ?_
  -- the arithmetic
  have hsum : ∑ j ∈ Finset.range N, (10 ^ 8 * ((pcStepCalls ansQ (step^[j] z0)).map τ).sum
        + 1100 * ((f + 2) * PR M) + E2 M + 2)
      = 10 ^ 8 * ((pcCallsQ ansQ z0).map τ).sum
        + N * (1100 * ((f + 2) * PR M) + E2 M + 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_range_eq_list]
    have hc' : pcCallsQ ansQ z0
        = (List.range N).flatMap (fun j => pcStepCalls ansQ (step^[j] z0)) := rfl
    rw [hc', sum_map_flatMap]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  rw [hsum]
  have hfinB : Enc.size (((0 : ℕ), step^[N] z0) : ℕ × RawPCLoop) ≤ Zp M := by
    have := size_pair_le' (((0 : ℕ), step^[N] z0) : ℕ × RawPCLoop)
    have h1 := hksize 0 (Nat.zero_le _)
    have h2 := hqsize N
    simp only at this; omega
  have e1 : c7 * (Enc.size (((0 : ℕ), step^[N] z0) : ℕ × RawPCLoop) + 1) ^ d7
      ≤ pw c7 d7 (Zp M) := pw_mono c7 d7 hfinB
  have e2 : c6 * (M + 1) ^ d6 = pw c6 d6 M := rfl
  have e3 : N * (1100 * ((f + 2) * PR M) + E2 M + 2)
      ≤ f * (M * (3300 * PR M + E2 M + 2)) := by
    have k1 : 1100 * ((f + 2) * PR M) ≤ f * (3300 * PR M) := by nlinarith
    have k2 : E2 M + 2 ≤ f * (E2 M + 2) := by nlinarith
    calc N * (1100 * ((f + 2) * PR M) + E2 M + 2)
        ≤ M * (f * (3300 * PR M) + f * (E2 M + 2)) :=
          Nat.mul_le_mul hNM (by omega)
      _ = f * (M * (3300 * PR M + E2 M + 2)) := by ring
  have e4 : 1 + pw c6 d6 M + pw c7 d7 (Zp M) ≤ f * (1 + pw c6 d6 M + pw c7 d7 (Zp M)) := by
    nlinarith
  have e5 : f * Gf M ≤ f * pw c d M := Nat.mul_le_mul_left _ (hcd M)
  have e6 : f * Gf M = f * (M * (3300 * PR M + E2 M + 2))
      + f * (1 + pw c6 d6 M + pw c7 d7 (Zp M)) := by rw [hGf]; ring
  rw [← hM]
  omega

/-- **Proposition 13.1.11 on the RAM** (§13.1), what the program of
`Algo.proposition_13_1_11_ram` computes and which calls it makes.  For all test sets `T, T'`
with `|T| = |T'| = t` and all strings `x, x'`, with `Q` initialized on line 01 to the
transporter set `G_Tσ`, and with a program answering String Isomorphism on the windows, the
output is `Iso_G(x_T^{W(T)}, (x')_{T'}^{W(T')})`; the calls number at most `t!·n²`, and each is
on a window `W` with `t·|W| ≤ n` (when `t ≥ 5`). -/
theorem proposition_13_1_11_ram_spec {n m : ℕ} {G : Subgroup (Perm (Fin n))}
    {ϕ : G →* Perm (Fin m)} {xs ys : RawStr} {tdom : List ℕ} (hc : LCCtxWF n m xs tdom)
    (hy : ys.length = n) (hset : LocalCertSetting G ϕ)
    (ht : LargeK (winSet m tdom).ncard (Nat.card (Fin n)))
    (htm : 10 * (winSet m tdom).ncard ≤ Nat.card (Fin m))
    {T' : Set (Fin m)} (hT' : T'.ncard = (winSet m tdom).ncard) [Nonempty (Fin n)]
    {st0 : RawLCSt} {q0 : RawCoset}
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (hq0 : decCoset n q0 = pcTransporters ϕ (winSet m tdom) T')
    (ansQ : RawWinSI → RawCoset)
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer) :
    decCoset n (pcOut (lcSolveQ ansQ) (((xs, tdom), st0), ys, q0))
        = compareIso ϕ (decStrN n xs) (decStrN n ys) (winSet m tdom) T' ∧
      (pcCallsQ ansQ (((xs, tdom), st0), ys, q0)).length ≤ Nat.factorial tdom.length * n ^ 2 ∧
      ∀ W ∈ pcCallsQ ansQ (((xs, tdom), st0), ys, q0),
        WinWF n W ∧ tdom.length * W.1.length ≤ n := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  have hT : (winSet m tdom).ncard = tdom.length := ncard_winSet tdom hc.nodup hc.ltM
  have h5 : 5 ≤ tdom.length := by have := ht.eight_lt; omega
  exact ⟨pcOut_eq_compareIso hsolve hy hset ht htm hT' h0 hq0,
    length_pcCallsQ_le hQ hy h5 h0 hq0, window_pcCallsQ_le hQ hy h5 h0 hq0⟩

end Algo
