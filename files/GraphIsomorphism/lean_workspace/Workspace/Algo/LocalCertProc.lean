/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure LocalCertificates (§13.1) as a whole — the while loop and
the two certificates.
-/
import Workspace.Algo.LocalCertLoop

/-!
# Procedure LocalCertificates (§13.1, claims C2 and C3)

> 06  `W(T) ← W`
> 07  if `H(W)^T ≥ A(T)` then
> 08    `K(T) ← H(W)_(W̄)`            (: `W̄ = Ω ∖ W` :)
> 09  else
> 10    `M(T) ← H(W)^T`
> 11  end if

The while loop is `Algo.lcRun` (`Workspace/Algo/LocalCertLoop.lean`); this file reads the
three outputs off the stage it exits at.  Line 06 is the window the loop carries, line 07 is
the order test `Algo.rawIsFullT`, line 08 is `Algo.rawCertK` and line 10 is `Algo.rawCertM`
(`Workspace/Algo/LocalCertOut.lean`).

The output is the triple `(W(T), K(T), M(T))` together with the outcome of the test, so that
it can be compared with `Babai.localCertReduction`, which also returns all three: the paper
computes one certificate or the other, and which one is decided by line 07, whose value the
routine returns beside them.

## Main definitions

* `Algo.RawLCOut`, `Algo.lcOut` — **Procedure LocalCertificates** on raw data.

## Main results

* `Algo.winSet_lcOut` — line 06 returns `W(T)` (`Babai.windowOut`);
* `Algo.lcOut_isFull` — line 07 decides fullness (`Babai.isFullOut`, Definition 13.1.2);
* `Algo.decGroup_lcOut_certK` — line 08 returns `K(T)` (`Babai.certK`);
* `Algo.decGroup_lcOut_certM` — line 10 returns `M(T)` (`Babai.certM`), read in `S(T)`;
* `Algo.lcOut_eq_run_localCertReduction` — **the output decodes to the value of
  `Babai.localCertReduction`**, which is Theorem 13.1.3 (a), (b);
* `Algo.theorem_13_1_3_calls_raw` — the call accounting of Theorem 13.1.3: `≤ t!n²`
  instances, on windows with `t·|Δ| ≤ n`;
* `Algo.quasiPolyFun_lcOut_of` — the procedure is a machine routine, given a routine for
  Procedure Recompute `H(W)`.

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Classical

variable {n m : ℕ}

/-! ## The procedure -/

/-- The output of Procedure LocalCertificates: the window `W(T)` of line 06, the outcome of
the test of line 07, the certificate `K(T)` of line 08 and the certificate `M(T)` of
line 10. -/
abbrev RawLCOut := List ℕ × Bool × RawGens × RawGens

/-- The raw instance with a window that the final stage describes: candidate set `H(W(T))`
with the identity as representative, window `W(T)`, strings `x`, `x`.  This is what line 08
reads `K(T)` off. -/
def lcFinalWin (q : RawLCLoop) : RawWinSI :=
  (q.2.1, q.2.2.1, rawOne q.1.1, q.1.1, q.1.1)

/-- **Procedure LocalCertificates** (§13.1, lines 01–11): run the while loop, then read off
the window, the outcome of the fullness test, and the two certificates. -/
def lcOut (solve : RawLCSI → RawCoset) (p : RawLCLoop) : RawLCOut :=
  ((lcRun solve p).2.1,
    rawIsFullT ((lcRun solve p).1.2, (lcRun solve p).2.2.2),
    rawCertK (lcFinalWin (lcRun solve p)),
    rawCertM ((lcRun solve p).1.2, (lcRun solve p).2.2.2))

/-! ## The specification -/

section Spec

variable {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)} {xs : RawStr} {tdom : List ℕ}
  {hc : LCCtxWF n m xs tdom} {solve : RawLCSI → RawCoset} {st0 : RawLCSt}

/-- The state the loop exits at decodes to `Babai.outStage`. -/
theorem stateFor_out
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    StateFor hc (Babai.outStage ϕ (decStrN n xs) (winSet m tdom))
      (lcRun solve ((xs, tdom), st0)).2 :=
  stateFor_lcRun hsolve h0

/-- The context of the state the loop exits at is the one it started with. -/
theorem lcRun_fst : (lcRun solve ((xs, tdom), st0)).1 = (xs, tdom) :=
  lcLoop_fst solve _ _

/-- **Line 06 returns `W(T)`** (`Babai.windowOut`). -/
theorem winSet_lcOut
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    winSet n (lcOut solve ((xs, tdom), st0)).1
      = Babai.windowOut ϕ (decStrN n xs) (winSet m tdom) :=
  (stateFor_out hsolve h0).winW

/-- **Line 07 decides fullness** (Definition 13.1.2, `Babai.isFullOut`): the test is on the
order of `H(W)^T`, which is polynomial, and never on an enumeration of `A(T)`. -/
theorem lcOut_isFull
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    (lcOut solve ((xs, tdom), st0)).2.1 = true
      ↔ Babai.isFullOut ϕ (decStrN n xs) (winSet m tdom) := by
  have h := stateFor_out hsolve h0
  show rawIsFullT (((lcRun solve ((xs, tdom), st0)).1.2,
    (lcRun solve ((xs, tdom), st0)).2.2.2) : RawTAct) = true ↔ _
  rw [show (lcRun solve ((xs, tdom), st0)).1.2 = tdom from
    congrArg Prod.snd (lcRun_fst (solve := solve) (st0 := st0))]
  exact rawIsFullT_stateFor h

/-- The raw instance the certificate `K(T)` is read off is well formed. -/
theorem winWF_lcFinalWin
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    WinWF n (lcFinalWin (lcRun solve ((xs, tdom), st0))) := by
  have h := stateFor_out hsolve h0
  have hfst := lcRun_fst (xs := xs) (tdom := tdom) (solve := solve) (st0 := st0)
  have hxs : (lcRun solve ((xs, tdom), st0)).1.1 = xs := congrArg Prod.fst hfst
  have hinv : rawIsInvariant ((lcRun solve ((xs, tdom), st0)).2.2.1,
      (lcRun solve ((xs, tdom), st0)).2.1) = true := by
    rw [rawIsInvariant_eq_true_iff h.wfG h.ltW]
    have hset : {y : Fin n | (y : ℕ) ∈ (lcRun solve ((xs, tdom), st0)).2.1}
        = winSet n (lcRun solve ((xs, tdom), st0)).2.1 := rfl
    rw [hset, h.winW, h.grp]
    exact (Babai.outStage ϕ (decStrN n xs) (winSet m tdom)).inv
  refine ⟨?_, ?_, h.nodupW, h.ltW, h.wfG, h.lenG, ?_, hinv⟩
  · show (lcRun solve ((xs, tdom), st0)).1.1.length = n
    rw [hxs]; exact hc.lenStr
  · show (lcRun solve ((xs, tdom), st0)).1.1.length = n
    rw [hxs]; exact hc.lenStr
  · show RawPerm.WF n (rawOne (lcRun solve ((xs, tdom), st0)).1.1)
    rw [hxs, rawOne, hc.lenStr, ← encPerm_one]
    exact wf_encPerm n _

/-- **Line 08 returns `K(T) = H(W)_(W̄)`** (`Babai.certK`). -/
theorem decGroup_lcOut_certK
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    decGroup n (lcOut solve ((xs, tdom), st0)).2.2.1
      = Babai.certK ϕ (decStrN n xs) (winSet m tdom) := by
  have h := stateFor_out hsolve h0
  have hspec := decGroup_rawCertK (winWF_lcFinalWin hsolve h0)
  show decGroup n (rawCertK (lcFinalWin (lcRun solve ((xs, tdom), st0)))) = _
  rw [hspec]
  show Babai.pointwiseStabilizer (decGroup n (lcRun solve ((xs, tdom), st0)).2.2.1)
      (winSet n (lcRun solve ((xs, tdom), st0)).2.1)ᶜ = _
  rw [h.grp, h.winW]
  rfl

/-- **Line 10 returns `M(T) = H(W)^T`** (`Babai.certM`), read in `S(T)` through the naming of
the test set (`Algo.tName`). -/
theorem decGroup_lcOut_certM
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    decGroup tdom.length (lcOut solve ((xs, tdom), st0)).2.2.2
      = (Babai.certM ϕ (decStrN n xs) (winSet m tdom)).map
          ((tName m tdom hc.nodup hc.ltM).symm.permCongrHom :
            Perm ↥(winSet m tdom) ≃* Perm (Fin tdom.length)).toMonoidHom := by
  have h := stateFor_out hsolve h0
  have hfst := lcRun_fst (xs := xs) (tdom := tdom) (solve := solve) (st0 := st0)
  have htd : (lcRun solve ((xs, tdom), st0)).1.2 = tdom := congrArg Prod.snd hfst
  show decGroup tdom.length (rawCertM (((lcRun solve ((xs, tdom), st0)).1.2,
    (lcRun solve ((xs, tdom), st0)).2.2.2) : RawTAct)) = _
  rw [htd]
  have e1 : decGroup tdom.length
      (rawCertM ((tdom, (lcRun solve ((xs, tdom), st0)).2.2.2) : RawTAct))
      = (psiFin ϕ tdom hc.nodup hc.ltM h.le).range :=
    decGroup_rawCertM (gens := (lcRun solve ((xs, tdom), st0)).2.2.1.map (decPerm n))
      (td := ((tdom, (lcRun solve ((xs, tdom), st0)).2.2.2) : RawTAct)) h.wfI (h.himgs h.le)
  rw [e1, range_psiFin, Babai.imgOn_congr h.grp h.le
    (Babai.outStage ϕ (decStrN n xs) (winSet m tdom)).le]
  rfl

/-- **Procedure LocalCertificates returns what the paper's reduction returns**
(Theorem 13.1.3 (a), (b)).  `Babai.localCertReduction` assembles the triple
`(W(T), K(T), M(T))` from the answers of the String Isomorphism instances
(`Babai.run_localCertReduction`), and the routine returns the same triple, decoded. -/
theorem lcOut_eq_run_localCertReduction
    (hsolve : ∀ I, LCWF n I → decCoset n (solve I) = (decLCSI n I).answer)
    (h0 : StateFor hc (Babai.stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (lift : ∀ i : ℕ, Babai.imgOn ϕ (winSet m tdom)
        (Babai.stages ϕ (decStrN n xs) (winSet m tdom) i).le → Perm (Fin n))
    (hlift : ∀ (i : ℕ) (sb : Babai.imgOn ϕ (winSet m tdom)
        (Babai.stages ϕ (decStrN n xs) (winSet m tdom) i).le),
      ∃ h : lift i sb ∈ (Babai.stages ϕ (decStrN n xs) (winSet m tdom) i).H,
        Babai.psiOn ϕ (winSet m tdom)
            (Babai.stages ϕ (decStrN n xs) (winSet m tdom) i).le ⟨lift i sb, h⟩
          = (sb : Perm ↥(winSet m tdom))) :
    (winSet n (lcOut solve ((xs, tdom), st0)).1,
      decGroup n (lcOut solve ((xs, tdom), st0)).2.2.1)
      = ((Babai.localCertReduction ϕ (decStrN n xs) (winSet m tdom) lift (Λ := ℕ)).run.1,
        (Babai.localCertReduction ϕ (decStrN n xs) (winSet m tdom) lift (Λ := ℕ)).run.2.1) := by
  rw [Babai.run_localCertReduction lift hlift]
  exact Prod.ext (winSet_lcOut hsolve h0) (decGroup_lcOut_certK hsolve h0)

end Spec

/-! ## The call accounting of Theorem 13.1.3

The two bounds of Theorem 13.1.3 are properties of the *instances* Procedure
LocalCertificates solves, and they are proved in `Workspace/LocalCertificates/Calls.lean`.
They are restated here so that the claim row C2 has one name on the algorithmic side: at most
`t!n²` String Isomorphism instances, each on a window `Δ` with `t·|Δ| ≤ n`. -/

section Calls

variable {Ω Γ Λ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
  {G : Subgroup (Perm Ω)} {ϕ : G →* Perm Γ} {x : Ω → Λ} {T : Set Γ}

/-- **Theorem 13.1.3, the cost clause** (§13.1):

> By making `≤ t!n²` calls to String Isomorphism problems on domains of size `≤ n/t` …

This is `Babai.theorem_13_1_3_calls`, named on the algorithmic side: the while loop runs at
most `n` times (`Babai.haltIndex_le_card`), each round makes at most `t!` instances of string
`N`-isomorphism (`Algo.lcWidth_le_factorial`, `Babai.card_imgOn_le_factorial`), each of which
is split by the Chain Rule over the orbits of `N` in `W_new`, and each such orbit has at most
`n/t` points (Cor. 10.3.7, `Babai.orbit_kerN_card_le`). -/
theorem theorem_13_1_3_calls_raw (h5 : 5 ≤ T.ncard)
    (lift : ∀ i : ℕ, Babai.imgOn ϕ T (Babai.stages ϕ x T i).le → Perm Ω)
    (hlift : ∀ (i : ℕ) (sb : Babai.imgOn ϕ T (Babai.stages ϕ x T i).le),
      ∃ h : lift i sb ∈ (Babai.stages ϕ x T i).H,
        Babai.psiOn ϕ T (Babai.stages ϕ x T i).le ⟨lift i sb, h⟩ = (sb : Perm ↥T)) :
    (Babai.localCertReduction ϕ x T lift (Λ := Λ)).calls.length
        ≤ Nat.factorial T.ncard * (Nat.card Ω) ^ 2 ∧
      (∀ I ∈ (Babai.localCertReduction ϕ x T lift (Λ := Λ)).calls,
        T.ncard * I.Δ.ncard ≤ Nat.card Ω) ∧
      (Babai.localCertReduction ϕ x T lift (Λ := Λ)).run
        = (Babai.windowOut ϕ x T, Babai.certK ϕ x T, Babai.certM ϕ x T) :=
  Babai.theorem_13_1_3_calls h5 lift hlift

end Calls

/-! ## The running time -/

section Cost

variable {solve : RawLCSI → RawCoset}

theorem polyFun_lcFinalWin : PolyFun lcFinalWin :=
  (polyFun_lcWin.pair (polyFun_lcGens.pair
    ((polyFun_lcStr.comp polyFun_rawOne).pair (polyFun_lcStr.pair polyFun_lcStr)))).of_eq
    (fun _ => rfl)

/-- **Procedure LocalCertificates is a machine routine**: the while loop is the bounded
iteration of one round (`Algo.quasiPolyFun_lcRun`) and the four outputs are read off its
final state by `RAM.PolyFun`s.  The only quasipolynomial ingredient is `solve`, the
evaluation of Procedure Recompute `H(W)`, whose `t!` is the width of its descend phase — the
split of Theorem 13.1.3 into "`≤ t!n²` calls" and "`t!·poly(n)` computation". -/
theorem quasiPolyFun_lcOut_of (hsolve : QuasiPolyFun solve) :
    QuasiPolyFun (lcOut solve) := by
  have hrun : QuasiPolyFun (lcRun solve) := quasiPolyFun_lcRun solve hsolve
  have htd : QuasiPolyFun (fun p : RawLCLoop => (lcRun solve p).1.2) :=
    hrun.comp_poly polyFun_lcTdom
  have himgs : QuasiPolyFun (fun p : RawLCLoop => (lcRun solve p).2.2.2) :=
    hrun.comp_poly polyFun_lcImgsOf
  have hwin : QuasiPolyFun (fun p : RawLCLoop => (lcRun solve p).2.1) :=
    hrun.comp_poly polyFun_lcWin
  have hfull : QuasiPolyFun (fun p : RawLCLoop =>
      rawIsFullT ((lcRun solve p).1.2, (lcRun solve p).2.2.2)) :=
    (htd.pair himgs).comp polyFun_rawIsFullT.quasiPolyFun
  have hK : QuasiPolyFun (fun p : RawLCLoop => rawCertK (lcFinalWin (lcRun solve p))) :=
    (hrun.comp_poly polyFun_lcFinalWin).comp_poly polyFun_rawCertK
  have hM : QuasiPolyFun (fun p : RawLCLoop =>
      rawCertM ((lcRun solve p).1.2, (lcRun solve p).2.2.2)) :=
    (htd.pair himgs).comp polyFun_rawCertM.quasiPolyFun
  exact (hwin.pair (hfull.pair (hK.pair hM))).of_eq (fun _ => rfl)

end Cost

end Algo
