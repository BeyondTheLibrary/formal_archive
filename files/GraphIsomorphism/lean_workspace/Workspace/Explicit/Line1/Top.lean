/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), tier 2: the line-1 threshold.
Not part of the faithful formalization.
-/
import Workspace.Explicit.Top.Final
import Workspace.Explicit.Line1.Recursion

/-!
# The variant Master at explicit line-1 thresholds

`Explicit.ParamsOKX p` asks `Explicit.Line1OK p.B p.C₀` of the line-1 thresholds of `p`
(for instance `B = 25`, `C₀ = (max 64 25!)! + 1`, `Explicit.line1OK_X`), and of the other
parameters what `Explicit.ParamsOK` asks, through the parameters `Explicit.paramsL1 p` (the
same parameters at the fixed thresholds of `Algo.theorem_1_1_1`).

* `Explicit.exists_treesX`: the trees of the variant round at `p`: at a line-1 node from
  `Explicit.masterNodeH_line1_treeOKX`, at a hinted node from the tree at `paramsL1 p`
  (`Explicit.exists_treesE_q`), carried over by `Explicit.treeOKX_of_treeOK_hint`;
* `Explicit.nodesE_leX`: the refined Eq. (74) at `p`;
* `Explicit.main_of_boundsX`: the Master at `p` in time `2^{c (log₂ N+2)^5}`.
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai

variable {cam : RawGens × List ℕ → Option RawCameron}

/-- The parameters `p` at the fixed line-1 thresholds of `Algo.theorem_1_1_1`. -/
noncomputable def paramsL1 (p : Params) : Params := { p with B := masterLine1B, C₀ := masterLine1C₀ }

/-- **The specifications of the parameters, at explicit line-1 thresholds**: `Line1OK` for the
thresholds, and `Explicit.ParamsOK` for the other parameters (at `paramsL1 p`). -/
structure ParamsOKX (p : Params) : Prop where
  line1 : Line1OK p.B p.C₀
  rest : ParamsOK (paramsL1 p)

/-- **The trees of the variant round at explicit line-1 thresholds.** -/
theorem exists_treesX {p : Params} (ok : ParamsOKX p) (hc : PolyFun cam) (hs : CameronSpec cam) :
    ∃ q : ℕ → ℕ, Monotone q ∧ ∀ (n : ℕ) (P : RawMasterSI), MasterNodeGood n P →
      (masterRoundE p cam).WF P → ∃ T, MasterNodeTreeOKX p.B p.C₀ (masterRoundE p cam) n q P T := by
  obtain ⟨q45, hq45, h⟩ := exists_treesE_q ok.rest hc hs
  refine ⟨rawMasterRoundCost q45, rawMasterRoundCost_mono hq45, fun n P hP hWF => ?_⟩
  obtain ⟨W, o⟩ := P
  cases o with
  | none => exact masterNodeH_line1_treeOKX q45 hc hs ok.line1 (ok.rest.cap n) W hP
  | some hh =>
    obtain ⟨T, hT⟩ := h n (W, some hh) hP hWF
    exact ⟨T, treeOKX_of_treeOK_hint (by simp) hT⟩

/-- The master recursion of the variant round at degree `n`, from its trees. -/
noncomputable def masterRecEX {p : Params} {q : ℕ → ℕ} (hq : Monotone q) (n : ℕ)
    (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOKX p.B p.C₀ (masterRoundE p cam) n q P T) :
    MasterRecursion (masterRoundE p cam) n :=
  masterRecursionOfTreesX hT hq (fun P s hP => finishE_wf p n P s hP)

/-- `Explicit.roundCalls_line2_half` at explicit line-1 thresholds. -/
theorem roundCalls_line2_halfX {p : Params} {q : ℕ → ℕ} (hq : Monotone q)
    (n : ℕ) (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOKX p.B p.C₀ (masterRoundE p cam) n q P T)
    (I : RawMasterSI) (hG : MasterNodeGood n I) (hI : (masterRoundE p cam).WF I)
    (hr : masterRoute I = 1) (f : ℕ) (hf : (masterRoundE p cam).measure I < f + 1) :
    ∀ J ∈ (masterRoundE p cam).roundCalls f I,
      1 ≤ masterWindowSize I ∧ 2 * masterWindowSize J ≤ masterWindowSize I := by
  set M := masterRecEX hq n hT with hM
  have hI2 : I.2 ≠ none := by
    intro h0
    obtain ⟨W, o⟩ := I
    subst h0
    simp [masterRoute] at hr
  have hTl : ∃ T : SIReduction (Fin n) ℕ (Set (Equiv.Perm (Fin n))),
      LoopMatchG (masterRoundE p cam)
        (fun J => MasterNodeGood n J ∧ MasterStepProgressX p.B p.C₀ I J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) I
        ((masterRoundE p cam).width I) 0 ((masterRoundE p cam).init I) T ∧
      (∀ K ∈ T.calls, 2 * K.windowSize ≤ masterWindowSize I) ∧ 1 ≤ masterWindowSize I := by
    have hTl' : ∃ T : SIReduction (Fin n) ℕ (Set (Equiv.Perm (Fin n))),
        LoopMatchG (masterRoundE (paramsL1 p) cam)
          (fun J => MasterNodeGood n J ∧ MasterStepProgress I J)
          (fun J => decWinSI n J.1) (fun _ => decCoset n) I
          ((masterRoundE (paramsL1 p) cam).width I) 0
          ((masterRoundE (paramsL1 p) cam).init I) T ∧
        (∀ K ∈ T.calls, 2 * K.windowSize ≤ masterWindowSize I) ∧ 1 ≤ masterWindowSize I :=
      masterNodeH_line2_half hG hr
    obtain ⟨T, hm, hh, h1⟩ := hTl'
    have hnc : ¬ MasterChainRuleNode I := fun hch => hI2 hch.1
    have hncX : ¬ MasterChainRuleNodeX p.B p.C₀ I := fun hch => hI2 hch.1
    refine ⟨T, loopMatchG_hint_transport hI2 ?_ hm, hh, h1⟩
    rintro J ⟨hJ, hpr⟩
    exact ⟨hJ, fun hch => absurd hch hncX, fun _ => hpr.2 hnc⟩
  obtain ⟨T, hm, hhalf, h1⟩ := hTl
  obtain ⟨-, h2, h3⟩ := (masterRoundE p cam).loopAux_eqG (rec := (masterRoundE p cam).value f)
    (C := fun J => MasterNodeGood n J ∧ MasterStepProgressX p.B p.C₀ I J)
    (Good := fun J => M.Good J ∧ (masterRoundE p cam).WF J ∧
      (masterRoundE p cam).measure J < (masterRoundE p cam).measure I)
    (fun j s J hc hC => ⟨hC.1, (masterRoundE p cam).child_wf I j s J hI hc,
      (masterRoundE p cam).child_measure I j s J hI hc⟩)
    (fun J hJ => roundValue_eqG (masterRoundE p cam) M.impl M.progress.good_child M.correct f J
      hJ.1 hJ.2.1 (lt_of_lt_of_le hJ.2.2 (Nat.lt_succ_iff.mp hf)))
    _ _ _ _ hm
  intro J hJ
  have hJT : decWinSI n J.1 ∈ T.calls := by
    rw [← h2]
    exact List.mem_map_of_mem hJ
  have hwJ := masterWindowSize_eq_of_rawNode (h3 J hJ).1.1
  exact ⟨h1, by rw [hwJ]; exact hhalf _ hJT⟩

/-- **The refined Eq. (74) for the variant round at explicit line-1 thresholds.** -/
theorem nodesE_leX {p : Params} (sb : StepBounds p cam) {q : ℕ → ℕ}
    (hq : Monotone q) (n : ℕ) (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOKX p.B p.C₀ (masterRoundE p cam) n q P T)
    (I : RawMasterSI) (hG : MasterNodeGood n I) (hI : (masterRoundE p cam).WF I) :
    (masterRoundE p cam).nodes ((masterRoundE p cam).measure I + 1) I ≤
      2 ^ ((4 * sb.Aw + 14 * sb.Ap + 24) * (Nat.log 2 n + 2) ^ 5) := by
  set M := masterRecEX hq n hT with hM
  have hdeg : ∀ P, M.Good P → masterDegree P = n := fun P hP => hP.1.1
  refine nodes_le_exp5 (masterRoundE p cam) M.impl M.correct M.progress
    (fun P => masterRoute P = 1)
    (fun _ => 2 ^ (sb.Aw * (Nat.log 2 n + 2) ^ 4)) (fun _ => 2 ^ (sb.Ap * (Nat.log 2 n + 2) ^ 3))
    n sb.Aw sb.Ap ?_ ?_ ?_ le_rfl le_rfl M.win_le _ I hG hI (Nat.lt_succ_self _) ?_
  · intro P hP hW hr f hf J hJ
    obtain ⟨h1, h2⟩ := roundCalls_line2_halfX hq n hT P hP hW hr f hf J hJ
    exact ⟨h1, by omega⟩
  · intro P hP hW _ hr f hf
    exact sb.calls_line2 n P f hP hW hf hr
  · intro P hP hW _ hr f hf
    exact sb.calls_other n P f hP hW hf hr
  · exact le_of_eq (hdeg I hG)

/-- The recursion of the variant round at parameters with `Explicit.ParamsOKX`. -/
theorem recOK_of_paramsOKX {p : Params} (ok : ParamsOKX p) (sb : StepBounds p cam)
    (hc : PolyFun cam) (hs : CameronSpec cam) :
    Nonempty (RecOK p cam (4 * sb.Aw + 14 * sb.Ap + 24)) := by
  obtain ⟨q, hqm, hT⟩ := exists_treesX ok hc hs
  exact ⟨⟨fun n => masterRecEX hqm n (hT n), fun n J hJ => hJ,
    fun n J hJ hW => nodesE_leX sb hqm n (hT n) J hJ hW⟩⟩

/-- **The Master in time `2^{c(log₂ N+2)^5}` at explicit line-1 thresholds.** -/
theorem main_of_boundsX {p : Params} (hc : PolyFun cam) (hs : CameronSpec cam)
    (ok : ParamsOKX p) (sb : StepBounds p cam) :
    ∃ (c : ℕ) (P : Program), ∀ n s : ℕ,
      SolvesInTime P (SIRel n s) (fun N => 2 ^ (c * (Nat.log 2 N + 2) ^ 5)) := by
  obtain ⟨rk⟩ := recOK_of_paramsOKX ok sb hc hs
  exact main_of_rec rk sb

end Explicit
