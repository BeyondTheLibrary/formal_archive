/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Procedure LocalCertificates (§13.1) with its String Isomorphism calls
answered by an oracle, and the calls it makes.
-/
import Workspace.Algo.LocalCertProc
import Workspace.Algo.OracleFold

/-!
# Procedure LocalCertificates with an oracle for String Isomorphism (§13.1)

Theorem 13.1.3 counts two things separately: the calls to String Isomorphism, and the rest
of the computation.

> By making `≤ t!n²` calls to String Isomorphism problems on domains of size `≤ n/t` and
> performing `t! poly(n)` computation we can decide whether `T` is full …

This file fixes what "a call" is.  Procedure Recompute `H(W)` (lines 04a–04h) descends to
`N = ker ψ_T` over the `≤ t!` cosets of Eq. (69), and on each coset runs the Chain Rule over
the orbits of `N` in `W_new` (strong descent, line 04e).  The instances the Chain Rule hands
on, one per orbit, are the String Isomorphism calls; when `N` has at most one orbit in the
window, the coset instance itself is the call.  Everything else is computation.

The answers come from a function `ansQ : RawWinSI → RawCoset`, the oracle.  Each answer is
normalized (`Algo.lcNormAns`: the generators shortened to at most `n²` of them, as
everywhere in the routines), which does not change what it decodes to.

## Main definitions

* `Algo.lcChainEval` — one coset of line 04e: the Chain Rule over the orbits of `N`, with the
  calls answered by the oracle;
* `Algo.lcSolveQ` — **Procedure Recompute `H(W)` with the oracle**, the union over the cosets;
* `Algo.lcCallsQ` — **the calls** Procedure LocalCertificates makes, in order.

## Main results

* `Algo.lcSolveQ_correct` — if the oracle answers every well-formed instance correctly, then
  so does Procedure Recompute; hence every specification theorem of
  `Workspace/Algo/LocalCertProc.lean` applies to `lcOut (lcSolveQ ansQ)`;
* `Algo.length_lcCallsQ_le` — at most `t!·n²` calls;
* `Algo.window_lcCallsQ_le` — every call is a well-formed instance whose window has at most
  `n/t` points (Cor. 10.3.7, `Babai.orbit_kerN_card_le`).

No axiom, no `sorry`, no `native_decide`.
-/

namespace Algo

open RAM RAM.Targets
open Equiv (Perm)
open scoped Pointwise

variable {n : ℕ}

/-! ## The normalized answer -/

/-- Normalize a raw coset: at most `n²` generators, each generator and the representative
capped to a permutation of the domain.  It changes nothing a correct answer decodes to. -/
def lcNormAns (p : RawStr × RawCoset) : RawCoset :=
  p.2.map fun q => (tidyGens (p.1, q.1), normPerm (p.1, q.2))

theorem decCoset_lcNormAns {xs : RawStr} (hx : xs.length = n) (a : RawCoset) :
    decCoset n (lcNormAns (xs, a)) = decCoset n a := by
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨gs, r⟩
    simp [lcNormAns, decCoset_some, decGroup_tidyGens hx, decPerm_normPerm hx]

theorem size_lcNormAns_le {xs : RawStr} {b : ℕ} (hx : xs.length ≤ b) (a : RawCoset) :
    Enc.size (lcNormAns (xs, a)) ≤ chainBound b := by
  cases a with
  | none =>
    change Enc.size (none : RawCoset) ≤ _
    rw [size_none]
    dsimp [chainBound]
    omega
  | some q =>
    exact size_coset_le' hx (wf_tidyGens rfl _) (length_tidyGens rfl _) (wf_normPerm rfl _)

theorem polyFun_lcNormAns : PolyFun lcNormAns := by
  have hq : PolyFun (fun z : (RawGens × RawPerm) × RawStr =>
      some (tidyGens (z.2, z.1.1), normPerm (z.2, z.1.2))) :=
    (((polyFun_snd.pair (polyFun_fst.comp polyFun_fst)).comp polyFun_tidyGens).pair
      ((polyFun_snd.pair (polyFun_fst.comp polyFun_snd)).comp polyFun_normPerm)).comp
      polyFun_some
  exact (polyFun_swap.comp (PolyFun.optionElim (polyFun_const none) hq)).of_eq
    (fun z => by obtain ⟨x, a⟩ := z; cases a <;> rfl)

/-- The oracle's answer to an instance, normalized against the instance's string. -/
def lcAnsN (ansQ : RawWinSI → RawCoset) (W : RawWinSI) : RawCoset :=
  lcNormAns (W.2.2.2.1, ansQ W)

/-! ## Procedure Recompute with the oracle -/

/-- The Recompute round with no leaf solver: its routines do not depend on the domain size,
and it is what the machine runs.  In the descend phase, and in the Chain Rule phase with at
least two orbits, it computes the same thing as `Algo.lcRound n solveW` for every `n` and
every `solveW` (`Algo.loopAux_lcRound_congr`). -/
def lcR0 : Round RawLCSI RawCoset RawCoset := lcRound 0 (fun _ => none)

/-- The number of orbits of the group of an instance in its window, Eq. (64). -/
def lcOrbCount (I : RawLCSI) : ℕ := (winOrbits (I.1.2.1, I.1.1)).length

/-- **One coset of line 04e.**  With at most one orbit of `N` in the window the instance is
itself a String Isomorphism call; otherwise the Chain Rule runs over the orbits, and each
orbit is a call. -/
def lcChainEval (ansQ : RawWinSI → RawCoset) (I : RawLCSI) : RawCoset :=
  if lcOrbCount I ≤ 1 then lcAnsN ansQ I.1
  else lcR0.loopAux (fun J => lcAnsN ansQ J.1) (lcR0.width I) I 0 (lcR0.init I)

/-- **Procedure Recompute `H(W)`** (lines 04a–04h) with the String Isomorphism calls answered
by the oracle: the union over the cosets of `N` (descend phase), each coset answered by
`Algo.lcChainEval`. -/
def lcSolveQ (ansQ : RawWinSI → RawCoset) (I : RawLCSI) : RawCoset :=
  I.2.elim (lcChainEval ansQ I)
    (fun _ => lcR0.loopAux (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I))

/-! ## The calls -/

/-- The calls of one coset of line 04e. -/
def lcChainCalls (ansQ : RawWinSI → RawCoset) (I : RawLCSI) : List RawWinSI :=
  if lcOrbCount I ≤ 1 then [I.1]
  else (lcR0.loopCalls (fun J => lcAnsN ansQ J.1) (lcR0.width I) I 0 (lcR0.init I)).map
    Prod.fst

/-- The calls of one run of Procedure Recompute `H(W)`. -/
def lcDescCalls (ansQ : RawWinSI → RawCoset) (I : RawLCSI) : List RawWinSI :=
  (lcR0.loopCalls (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I)).flatMap
    (lcChainCalls ansQ)

/-- The calls of one round of the while loop: those of line 04 if the test of line 02
passes, none otherwise. -/
def lcStepCalls (ansQ : RawWinSI → RawCoset) (p : RawLCLoop) : List RawWinSI :=
  if lcCond p then lcDescCalls ansQ (lcInst p) else []

/-- **The calls of Procedure LocalCertificates**, round by round of the while loop. -/
def lcCallsQ (ansQ : RawWinSI → RawCoset) (p : RawLCLoop) : List RawWinSI :=
  (List.range p.1.1.length).flatMap
    (fun j => lcStepCalls ansQ ((lcStep (lcSolveQ ansQ))^[j] p))

/-! ## The leaf solver does not matter where it is not called -/

theorem loopAux_lcRound_congr {n₁ n₂ : ℕ} {s₁ s₂ : RawWinSI → RawCoset}
    (rec : RawLCSI → RawCoset) (I : RawLCSI)
    (hfin : ∀ s, lcFinish s₁ (I, s) = lcFinish s₂ (I, s)) :
    ∀ (w j : ℕ) (s : RawCoset),
      (lcRound n₁ s₁).loopAux rec w I j s = (lcRound n₂ s₂).loopAux rec w I j s := by
  intro w
  induction w with
  | zero => intro j s; exact hfin s
  | succ w ih =>
    intro j s
    cases hc : lcChild (I, j, s) with
    | none =>
      rw [Round.loopAux_succ_none (R := lcRound n₁ s₁) hc,
        Round.loopAux_succ_none (R := lcRound n₂ s₂) hc]
      exact hfin s
    | some J =>
      rw [Round.loopAux_succ_some (R := lcRound n₁ s₁) hc,
        Round.loopAux_succ_some (R := lcRound n₂ s₂) hc]
      exact ih _ _

theorem loopCalls_lcRound_congr {n₁ n₂ : ℕ} {s₁ s₂ : RawWinSI → RawCoset}
    (rec : RawLCSI → RawCoset) (I : RawLCSI) :
    ∀ (w j : ℕ) (s : RawCoset),
      (lcRound n₁ s₁).loopCalls rec w I j s = (lcRound n₂ s₂).loopCalls rec w I j s := by
  intro w
  induction w with
  | zero => intro j s; rfl
  | succ w ih =>
    intro j s
    cases hc : lcChild (I, j, s) with
    | none =>
      rw [Round.loopCalls_succ_none (R := lcRound n₁ s₁) hc,
        Round.loopCalls_succ_none (R := lcRound n₂ s₂) hc]
    | some J =>
      rw [Round.loopCalls_succ_some (R := lcRound n₁ s₁) hc,
        Round.loopCalls_succ_some (R := lcRound n₂ s₂) hc]
      exact congrArg _ (ih _ _)

/-! ## Correctness -/

section Correct

variable {ansQ : RawWinSI → RawCoset}

theorem lcAnsN_correct
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    {W : RawWinSI} (hW : WinWF n W) :
    decCoset n (lcAnsN ansQ W) = (decWinSI n W).answer := by
  rw [lcAnsN, decCoset_lcNormAns hW.1]
  exact hQ W hW

/-- The children of a Chain Rule instance are Chain Rule instances. -/
theorem lcChild_chain_snd {I : RawLCSI} {j : ℕ} {s : RawCoset} {J : RawLCSI}
    (hq : I.2 = none) (hc : lcChild (I, j, s) = some J) : J.2 = none := by
  obtain ⟨J', -, rfl⟩ := lcChild_chain_eq_some (p := (I, j, s)) hq hc
  rfl

/-- The children of a descend instance are Chain Rule instances. -/
theorem lcChild_desc_snd {I : RawLCSI} {j : ℕ} {s : RawCoset} {J : RawLCSI}
    {td : RawTAct} {idx : ℕ}
    (hq : I.2 = some (td, idx)) (hc : lcChild (I, j, s) = some J) : J.2 = none := by
  obtain ⟨-, rfl⟩ := lcChild_desc_eq_some (p := (I, j, s)) hq hc
  rfl

/-- **One coset of line 04e is answered correctly.** -/
theorem lcChainEval_correct
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    {I : RawLCSI} (hI : LCWF n I) (hq : I.2 = none) :
    decCoset n (lcChainEval ansQ I) = (decLCSI n I).answer := by
  unfold lcChainEval
  by_cases h1 : lcOrbCount I ≤ 1
  · rw [if_pos h1]
    exact lcAnsN_correct hQ hI.1
  · rw [if_neg h1]
    have hfin : ∀ s, lcFinish (fun _ => none) (I, s) = lcFinish (lcAnsN ansQ) (I, s) := by
      intro s
      have h1' : ¬ (winOrbits (I.1.2.1, I.1.1)).length ≤ 1 := h1
      simp only [lcFinish, hq, Option.elim]
      rw [if_neg h1', if_neg h1']
    have hc := loopAux_lcRound_congr (n₁ := 0) (n₂ := n) (fun J => lcAnsN ansQ J.1) I hfin
      (lcR0.width I) 0 (lcR0.init I)
    rw [show lcR0.loopAux (fun J => lcAnsN ansQ J.1) (lcR0.width I) I 0 (lcR0.init I)
      = (lcRound 0 (fun _ => none)).loopAux (fun J => lcAnsN ansQ J.1) (lcR0.width I) I 0
        (lcR0.init I) from rfl, hc]
    obtain ⟨h, -⟩ := Round.loopAux_eq (lcRound n (lcAnsN ansQ))
      (Good := fun J => LCWF n J ∧ J.2 = none)
      (fun j s J hcJ => ⟨(lcRound n (lcAnsN ansQ)).child_wf I j s J hI hcJ,
        lcChild_chain_snd hq hcJ⟩)
      (fun J hJ => lcAnsN_correct hQ hJ.1.1) _ _ _ _
      (implements_lcRound n (lcAnsN ansQ) I hI)
    exact h.trans (run_lcRoundReduction n _ hI (fun _ h2 => absurd h2 h1))

/-- **Procedure Recompute `H(W)` with the oracle is correct** on every well-formed instance,
provided the oracle is. -/
theorem lcSolveQ_correct
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    {I : RawLCSI} (hI : LCWF n I) :
    decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer := by
  obtain ⟨o, ho⟩ : ∃ o, I.2 = o := ⟨_, rfl⟩
  cases o with
  | none =>
    have : lcSolveQ ansQ I = lcChainEval ansQ I := by simp [lcSolveQ, ho]
    rw [this]
    exact lcChainEval_correct hQ hI ho
  | some q =>
    obtain ⟨td, idx⟩ := q
    have e1 : lcSolveQ ansQ I
        = lcR0.loopAux (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I) := by
      simp [lcSolveQ, ho]
    have hfin : ∀ s, lcFinish (fun _ => none) (I, s) = lcFinish (lcAnsN ansQ) (I, s) := by
      intro s
      simp only [lcFinish, ho, Option.elim]
    have hc := loopAux_lcRound_congr (n₁ := 0) (n₂ := n) (lcChainEval ansQ) I hfin
      (lcR0.width I) 0 (lcR0.init I)
    rw [e1, show lcR0.loopAux (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I)
      = (lcRound 0 (fun _ => none)).loopAux (lcChainEval ansQ) (lcR0.width I) I 0
        (lcR0.init I) from rfl, hc]
    obtain ⟨h, -⟩ := Round.loopAux_eq (lcRound n (lcAnsN ansQ))
      (Good := fun J => LCWF n J ∧ J.2 = none)
      (fun j s J hcJ => ⟨(lcRound n (lcAnsN ansQ)).child_wf I j s J hI hcJ,
        lcChild_desc_snd ho hcJ⟩)
      (fun J hJ => lcChainEval_correct hQ hJ.1 hJ.2) _ _ _ _
      (implements_lcRound n (lcAnsN ansQ) I hI)
    exact h.trans (run_lcRoundReduction n _ hI (fun h' => absurd (show I.2 = none from h') (by rw [ho]; simp)))

end Correct

/-! ## The calls: how many, and on which windows -/

section Calls

variable {ansQ : RawWinSI → RawCoset}

/-- A Chain Rule instance makes at most `n` calls (one per orbit, or one). -/
theorem length_lcChainCalls_le {I : RawLCSI} (hI : LCWF n I) (hq : I.2 = none) (hn : 1 ≤ n) :
    (lcChainCalls ansQ I).length ≤ n := by
  unfold lcChainCalls
  by_cases h1 : lcOrbCount I ≤ 1
  · rw [if_pos h1]; simpa using hn
  · rw [if_neg h1, List.length_map]
    refine le_trans (lcR0.length_loopCalls_le _ I _ 0 _) ?_
    have hw : lcR0.width I = lcOrbCount I := by
      show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) = _
      rw [hq]; rfl
    rw [hw]
    exact le_trans (length_winOrbits_le _ _) (length_le_of_nodup_lt hI.1.2.2.1 hI.1.2.2.2.1)

/-- Every call of a fold of the Recompute round is a child. -/
theorem exists_child_of_mem_loopCalls {rec : RawLCSI → RawCoset} {w j : ℕ} {s : RawCoset}
    {I J : RawLCSI} (hJ : J ∈ lcR0.loopCalls rec w I j s) :
    ∃ j' s', lcChild (I, j', s') = some J := by
  obtain ⟨j', s', -, h⟩ := lcR0.mem_loopCalls_inv rec I (fun _ _ => True) (fun _ _ _ _ _ => trivial)
    w j s trivial J hJ
  exact ⟨j', s', h⟩

/-- **One run of Procedure Recompute makes at most `idx·n` calls**: at most `idx` cosets
(`idx = |H(W_old)^T|`), and at most `n` calls on each. -/
theorem length_lcDescCalls_le {I : RawLCSI} (hI : LCWF n I) {td : RawTAct} {idx : ℕ}
    (hs : I.2 = some (td, idx)) (hn : 1 ≤ n) :
    (lcDescCalls ansQ I).length ≤ idx * n := by
  unfold lcDescCalls
  rw [List.length_flatMap]
  have hle : ∀ x ∈ (lcR0.loopCalls (lcChainEval ansQ) (lcR0.width I) I 0 (lcR0.init I)).map
      (fun J => (lcChainCalls ansQ J).length), x ≤ n := by
    intro x hx
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j', s', hc⟩ := exists_child_of_mem_loopCalls hJ
    exact length_lcChainCalls_le ((lcRound n (fun _ => none)).child_wf I j' s' J hI hc)
      (lcChild_desc_snd hs hc) hn
  have h1 := List.sum_le_card_nsmul _ n hle
  rw [List.length_map, smul_eq_mul] at h1
  have h2 := lcR0.length_loopCalls_le (lcChainEval ansQ) I (lcR0.width I) 0 (lcR0.init I)
  have hw : lcR0.width I = idx := by
    show I.2.elim (winOrbits (I.1.2.1, I.1.1)).length (fun q => q.2) = _
    rw [hs]; rfl
  exact le_trans h1 (Nat.mul_le_mul_right _ (le_trans h2 (le_of_eq hw)))

end Calls

/-! ## The calls of the whole procedure -/

section Loop

open Babai

variable {m : ℕ} {G : Subgroup (Perm (Fin n))} {ϕ : G →* Perm (Fin m)} {xs : RawStr}
  {tdom : List ℕ} {hc : LCCtxWF n m xs tdom} {st0 : RawLCSt} {ansQ : RawWinSI → RawCoset}

/-- **The kernel of line 04a is `N`**: the generators `Algo.lcKer` computes decode to
`Babai.kerN` of the stage. -/
theorem decGroup_lcKer_lcInst {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}
    (h : StateFor hc s st) :
    decGroup n (lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2)) = kerN s := by
  have hk := decGroup_lcKer (lcwf_lcInst h) rfl (h.himgs h.le)
  rw [hk]
  ext σ
  rw [mem_actKer, mem_kerN]
  let e := (tName m tdom hc.nodup hc.ltM).symm.permCongrHom
  constructor
  · rintro ⟨hσ, hker⟩
    have hσ' : σ ∈ s.H := h.grp ▸ hσ
    refine ⟨hσ', ?_⟩
    apply e.injective
    change e (psiOn ϕ (winSet m tdom) s.le ⟨σ, hσ'⟩) = e 1
    rw [map_one]
    exact hker
  · rintro ⟨hσ, hker⟩
    have hσ' : σ ∈ decGroup n st.2.1 := h.grp.symm ▸ hσ
    refine ⟨hσ', ?_⟩
    change e (psiOn ϕ (winSet m tdom) s.le ⟨σ, hσ⟩) = 1
    rw [hker, map_one]

/-- **A round of the while loop that passes the test of line 02** is one of the first
`haltIndex` rounds, and its state decodes to the stage of that round. -/
theorem lcCond_iterate
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) {j : ℕ}
    (hj : lcCond ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)) = true) :
    j < haltIndex ϕ (decStrN n xs) (winSet m tdom) ∧
      StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) j)
        ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)).2 := by
  have hsolve : ∀ I, LCWF n I → decCoset n (lcSolveQ ansQ I) = (decLCSI n I).answer :=
    fun I hI => lcSolveQ_correct hQ hI
  have hlt : j < haltIndex ϕ (decStrN n xs) (winSet m tdom) := by
    by_contra hge
    push_neg at hge
    have hst : StateFor hc (outStage ϕ (decStrN n xs) (winSet m tdom))
        (lcLoop (lcSolveQ ansQ) (haltIndex ϕ (decStrN n xs) (winSet m tdom))
          ((xs, tdom), st0)).2 :=
      stateFor_lcLoop hsolve h0 _ (le_refl _)
    have heq := lcLoop_add_haltIndex hsolve h0 (j - haltIndex ϕ (decStrN n xs) (winSet m tdom))
    rw [Nat.add_sub_cancel' hge] at heq
    have hj' : lcCond ((xs, tdom), (lcLoop (lcSolveQ ansQ)
        (haltIndex ϕ (decStrN n xs) (winSet m tdom)) ((xs, tdom), st0)).2) = true := by
      rw [← lcLoop_eq_pair, ← heq]
      exact hj
    exact not_loopCond_outStage ϕ (decStrN n xs) (winSet m tdom)
      ((lcCond_eq_true_iff hst).1 hj')
  exact ⟨hlt, stateFor_lcLoop hsolve h0 j hlt.le⟩

/-- **Theorem 13.1.3, the number of calls**: Procedure LocalCertificates makes at most
`t!·n²` String Isomorphism calls, `t` being the size of the test set.  (At most `n` rounds
of the while loop, at most `t!` cosets in each (`Algo.lcWidth_le_factorial`), at most `n`
orbits on each coset.) -/
theorem length_lcCallsQ_le
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0) :
    (lcCallsQ ansQ ((xs, tdom), st0)).length ≤ Nat.factorial tdom.length * n ^ 2 := by
  unfold lcCallsQ
  rw [List.length_flatMap]
  have hle : ∀ x ∈ (List.range (((xs, tdom), st0) : RawLCLoop).1.1.length).map
      (fun j => (lcStepCalls ansQ ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0))).length),
      x ≤ Nat.factorial tdom.length * n := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hjn : j < n := by
      rw [List.mem_range] at hj
      simpa [hc.lenStr] using hj
    unfold lcStepCalls
    by_cases hcond : lcCond ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)) = true
    · rw [if_pos hcond]
      obtain ⟨-, hst⟩ := lcCond_iterate hQ h0 hcond
      have hpair : (lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)
          = ((xs, tdom), ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)).2) :=
        lcLoop_eq_pair (lcSolveQ ansQ) j st0
      rw [hpair]
      set st := ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)).2
      have hI := lcwf_lcInst hst
      have hs : (lcInst ((xs, tdom), st)).2 = some ((tdom, st.2.2), lcIdx ((xs, tdom), st)) :=
        rfl
      refine le_trans (length_lcDescCalls_le hI hs (by omega)) (Nat.mul_le_mul_right _ ?_)
      obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ := hI.2 _ _ hs
      exact lcWidth_le_factorial hI hs hψ
    · rw [if_neg hcond]; simp
  have h1 := List.sum_le_card_nsmul _ _ hle
  rw [List.length_map, List.length_range, smul_eq_mul] at h1
  have h2 : (((xs, tdom), st0) : RawLCLoop).1.1.length = n := hc.lenStr
  exact h1.trans (le_of_eq (by rw [h2]; ring))

/-- An orbit of `N` in the window of a round has at most `n/t` points (Cor. 10.3.7). -/
theorem length_rawOrbit_lcKer_le {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}
    (h : StateFor hc s st) (hrun : s.LoopCond) (h5 : 5 ≤ tdom.length) {v : ℕ}
    (hv : v ∈ lcAffNew ((xs, tdom), st)) :
    tdom.length * (rawOrbit (lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2), v)).length
      ≤ n := by
  set gs := lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2) with hgs
  have hvn : v < n := lt_lcAffNew hc hv
  have hwf : RawGens.WF n gs := wf_lcKer (lcwf_lcInst h)
  have hset : winSet n (rawOrbit (gs, v))
      = (MulAction.orbit (kerN s) (⟨v, hvn⟩ : Fin n) : Set (Fin n)) := by
    rw [← decGroup_lcKer_lcInst h]
    ext y
    rw [mem_winSet, mem_rawOrbit_iff hwf hvn]
    constructor
    · rintro ⟨hy, hyo⟩
      exact hyo
    · intro hyo
      exact ⟨y.isLt, hyo⟩
  have hlt : ∀ u ∈ rawOrbit (gs, v), u < n := by
    intro u hu
    exact ((mem_rawOrbit_iff hwf hvn u).1 hu).1
  have hlen : (rawOrbit (gs, v)).length = (winSet n (rawOrbit (gs, v))).ncard :=
    (ncard_winSet _ (nodup_rawOrbit gs v) hlt).symm
  have hT : (winSet m tdom).ncard = tdom.length := ncard_winSet tdom hc.nodup hc.ltM
  have hu : (⟨v, hvn⟩ : Fin n) ∈ s.aff := by
    rw [← winSet_lcAffNew h]
    exact hv
  have hk := orbit_kerN_card_le s hrun.1 (by rw [hT]; exact h5) hu
  rw [hT, Nat.card_eq_fintype_card, Fintype.card_fin] at hk
  rw [hlen, hset]
  exact hk

/-- **The windows of one run of Procedure Recompute** (a descent to `N` inside a round that
passes the test of line 02): every call is a well-formed instance on an orbit of `N`, so its
window has at most `n/t` points (Cor. 10.3.7).  Stated for any descent instance on the new
window whose kernel is the kernel of line 04a, so that it covers both the automorphism
instance of line 04 and the comparison instance of Prop. 13.1.11. -/
theorem window_lcDescCalls_le {s : Stage ϕ (decStrN n xs) (winSet m tdom)} {st : RawLCSt}
    (hst : StateFor hc s st) (hrun : s.LoopCond) (h5 : 5 ≤ tdom.length)
    {I : RawLCSI} (hI : LCWF n I) {idx : ℕ} (hs : I.2 = some ((tdom, st.2.2), idx))
    (hIw : I.1.1 = lcAffNew ((xs, tdom), st))
    (hIk : lcKer I.1 (tdom, st.2.2) = lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2)) :
    ∀ W ∈ lcDescCalls ansQ I, WinWF n W ∧ tdom.length * W.1.length ≤ n := by
  intro W hWj
  unfold lcDescCalls at hWj
  obtain ⟨C, hC, hWC⟩ := List.mem_flatMap.1 hWj
  obtain ⟨j', s', hcC⟩ := exists_child_of_mem_loopCalls hC
  have hCwf : LCWF n C := (lcRound n (fun _ => none)).child_wf I j' s' C hI hcC
  obtain ⟨-, hCeq⟩ := lcChild_desc_eq_some (p := (I, j', s')) hs hcC
  -- the group and window of the coset instance
  have hCg : C.1.2.1 = lcKer (lcInst ((xs, tdom), st)).1 (tdom, st.2.2) := by rw [hCeq]; exact hIk
  have hCw : C.1.1 = lcAffNew ((xs, tdom), st) := by rw [hCeq]; exact hIw
  have horb : ∀ o ∈ winOrbits (C.1.2.1, C.1.1), tdom.length * o.length ≤ n := by
    intro o ho
    obtain ⟨v, hv, rfl⟩ := winOrbits_mem ho
    rw [hCw] at hv
    rw [hCg]
    exact length_rawOrbit_lcKer_le hst hrun h5 hv
  unfold lcChainCalls at hWC
  by_cases h1 : lcOrbCount C ≤ 1
  · rw [if_pos h1, List.mem_singleton] at hWC
    subst hWC
    refine ⟨hCwf.1, ?_⟩
    rcases hnil : C.1.1 with _ | ⟨v₀, rest⟩
    · simp
    · -- every point of the window lies in the one orbit
      have hv₀ : v₀ ∈ C.1.1 := by rw [hnil]; exact List.mem_cons_self ..
      have hcov := winOrbits_cover hCwf.1.2.2.2.2.1 hCwf.1.2.2.2.1 hv₀
      obtain ⟨o, ho, -⟩ := List.mem_flatten.1 hcov
      have hone : winOrbits (C.1.2.1, C.1.1) = [o] := by
        have hl : (winOrbits (C.1.2.1, C.1.1)).length = 1 := by
          have : 0 < (winOrbits (C.1.2.1, C.1.1)).length := List.length_pos_of_mem ho
          have : (winOrbits (C.1.2.1, C.1.1)).length ≤ 1 := h1
          omega
        obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hl
        rw [ha] at ho ⊢
        rw [List.mem_singleton.1 ho]
      have hsub : C.1.1 ⊆ o := by
        intro u hu
        have := winOrbits_cover hCwf.1.2.2.2.2.1 hCwf.1.2.2.2.1 hu
        rw [hone] at this
        simpa using this
      have hle : C.1.1.length ≤ o.length :=
        (List.Nodup.subperm hCwf.1.2.2.1 hsub).length_le
      have := horb o ho
      rw [← hnil]
      calc tdom.length * C.1.1.length ≤ tdom.length * o.length :=
            Nat.mul_le_mul_left _ hle
        _ ≤ n := this
  · rw [if_neg h1] at hWC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hWC
    obtain ⟨i, sC, hcC'⟩ := exists_child_of_mem_loopCalls hC'
    have hC'wf : LCWF n C' := (lcRound n (fun _ => none)).child_wf C i sC C' hCwf hcC'
    refine ⟨hC'wf.1, ?_⟩
    have hCq : C.2 = none := lcChild_desc_snd hs hcC
    obtain ⟨W', hw, rfl⟩ := lcChild_chain_eq_some (p := (C, i, sC)) hCq hcC'
    obtain ⟨g, τ, -, hne, -, -, hW'⟩ := winChild_eq_some hw
    have hil : i < (winOrbits (C.1.2.1, C.1.1)).length := winChild_index_lt hw
    have hmem : (winOrbits (C.1.2.1, C.1.1)).getD i [] ∈ winOrbits (C.1.2.1, C.1.1) := by
      rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil
    rw [hW']
    exact horb _ hmem


/-- **Theorem 13.1.3, the size of the domains**: every call of Procedure LocalCertificates is a
well-formed instance whose window has at most `n/t` points. -/
theorem window_lcCallsQ_le
    (hQ : ∀ W, WinWF n W → decCoset n (ansQ W) = (decWinSI n W).answer)
    (h0 : StateFor hc (stages ϕ (decStrN n xs) (winSet m tdom) 0) st0)
    (h5 : 5 ≤ tdom.length) :
    ∀ W ∈ lcCallsQ ansQ ((xs, tdom), st0), WinWF n W ∧ tdom.length * W.1.length ≤ n := by
  intro W hW
  unfold lcCallsQ at hW
  obtain ⟨j, -, hWj⟩ := List.mem_flatMap.1 hW
  unfold lcStepCalls at hWj
  by_cases hcond : lcCond ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)) = true
  swap
  · rw [if_neg hcond] at hWj; simp at hWj
  rw [if_pos hcond] at hWj
  obtain ⟨hjlt, hst⟩ := lcCond_iterate hQ h0 hcond
  have hrun := loopCond_of_lt_haltIndex ϕ (decStrN n xs) (winSet m tdom) hjlt
  have hpair : (lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)
      = ((xs, tdom), ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)).2) :=
    lcLoop_eq_pair (lcSolveQ ansQ) j st0
  rw [hpair] at hWj
  set st := ((lcStep (lcSolveQ ansQ))^[j] ((xs, tdom), st0)).2
  exact window_lcDescCalls_le hst hrun h5 (lcwf_lcInst hst) rfl rfl rfl W hWj
end Loop

end Algo
