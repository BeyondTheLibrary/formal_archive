/-
An explicit running time for Theorem 1.1.1 (Babai, version 2.5), part 2: the recursion of the
variant Master round, its correctness and its node count. Not part of the faithful
formalization.
-/
import Workspace.Explicit.Interface
import Workspace.Explicit.Top.Run
import Workspace.Explicit.Top.Line2Half

/-!
# The variant Master round: correctness and the node count

The existing correctness proofs are parametric in the constants, so they apply to
`Explicit.masterRoundE p cam` once `Explicit.ParamsOK p` holds:

* `Explicit.exists_treesE`: at every good node the variant round walks a tree with
  `Algo.MasterNodeTreeOK` (the proof of `Algo.siWorkspaceRoutine`, through
  `Algo.siWorkspaceRoutine_of_route5`, `Algo.siWorkspaceRoutine_of_openRoutes` and
  `Algo.siWorkspaceRoutine_of_hintedRoutes`, at the constants of `p`);
* `Explicit.finishE_wf`: the answers are well formed;
* `Explicit.roundCalls_line2_half`: at a node of route 1 (line 2) every call of the run has
  at most half the window (`Explicit.masterNodeH_line2_half`);
* `Explicit.nodesE_le`: **the refined Eq. (74)**: below a good root of degree `n`, the
  recursion tree has at most `2^{(4Aw + 14Ap + 24)(log₂ n+2)^5}` nodes
  (`Explicit.nodes_le_exp5` with the call bounds of `Explicit.StepBounds`).
-/

set_option synthInstance.maxSize 4096

namespace Explicit

open RAM RAM.Targets Algo Babai Equiv

variable {cam : RawGens × List ℕ → Option RawCameron}

/-- **The trees of the variant round**, with the call bound `Algo.rawMasterRoundCost q45`. At
every good, well-formed node of every degree, the variant round walks a tree with
`Algo.MasterNodeTreeOK`. -/
theorem exists_treesE_q {p : Params} (ok : ParamsOK p) (hc : PolyFun cam)
    (hs : CameronSpec cam) :
    ∃ q45 : ℕ → ℕ, Monotone q45 ∧ ∀ (n : ℕ) (P : RawMasterSI), MasterNodeGood n P →
      (masterRoundE p cam).WF P →
        ∃ T, MasterNodeTreeOK (masterRoundE p cam) n (rawMasterRoundCost q45) P T := by
  obtain ⟨B, C₀, a, b, e, f, u, v, u', v', tt, dd, t, d, dc, dp, E⟩ := p
  obtain ⟨⟨hB, hC₀⟩, htopwp, htop4w, ⟨hu', hv'⟩, hcap, hl4c, hentry, hbip, hphases, hreserve⟩ :=
    ok
  dsimp only at hB hC₀ hu' hv' htopwp htop4w hcap hl4c hentry hbip hphases hreserve
  subst hB hC₀ hu' hv'
  obtain ⟨q5, hq5m, -, h5⟩ := exists_masterL57SupplyH (E := E) hphases htopwp hentry hbip
    le_rfl hreserve
  let q45 : ℕ → ℕ := fun k => masterRoute4Cost 0 tt dd k + q5 k
  have hq45 : Monotone q45 := (masterRoute4Cost_mono _ _ _).add hq5m
  refine ⟨q45, hq45, fun n P hP hWF => ?_⟩
  have h4 : MasterParamRoute (masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f, u, v,
      (l57UV e f).1, (l57UV e f).2, tt, dd, t, d, dc, dp, E⟩ cam) n q45 4 := by
    refine masterParamRoute4H hl4c (fun k => Nat.le_add_right _ _) ?_
    intro W h hg _ hr hd
    obtain ⟨T, hT⟩ := masterNodeH_route4Dom_treeOK (cameron := cam) (e := e) (f := f) (u := u)
      (v := v) (c' := 2) (b' := 0) (t := t) (d := d) (dc := dc) (dp := dp) (E := E)
      (H5 := hint5E ⟨masterLine1B, masterLine1C₀, a, b, e, f, u, v,
        (l57UV e f).1, (l57UV e f).2, tt, dd, t, d, dc, dp, E⟩)
      hl4c (hcap n) hg hr hd
    exact ⟨T, hT.mono_q fun k => Nat.le_add_right _ _⟩
  have h5' : MasterParamRoute (masterRoundE ⟨masterLine1B, masterLine1C₀, a, b, e, f, u, v,
      (l57UV e f).1, (l57UV e f).2, tt, dd, t, d, dc, dp, E⟩ cam) n q45 5 :=
    masterParamRoute5H_of_supply (hcap n) hreserve ((h5 n).mono_q fun k => Nat.le_add_left _ _)
  exact masterNodeH_treeOK hc hs (hcap n) htopwp htop4w h4 h5' P hP hWF

/-- **The trees of the variant round.** At every good, well-formed node of every degree, the
variant round walks a tree with `Algo.MasterNodeTreeOK`, for one monotone call bound `q`. -/
theorem exists_treesE {p : Params} (ok : ParamsOK p) (hc : PolyFun cam) (hs : CameronSpec cam) :
    ∃ q : ℕ → ℕ, Monotone q ∧ ∀ (n : ℕ) (P : RawMasterSI), MasterNodeGood n P →
      (masterRoundE p cam).WF P → ∃ T, MasterNodeTreeOK (masterRoundE p cam) n q P T := by
  obtain ⟨q45, hq45, h⟩ := exists_treesE_q ok hc hs
  exact ⟨_, rawMasterRoundCost_mono hq45, h⟩

/-- **The answers of the variant round are well formed.** -/
theorem finishE_wf (p : Params) (n : ℕ) (P : RawMasterSI) (s : StateE)
    (hP : masterDegree P = n) : RawCoset.WF n ((masterRoundE p cam).finish (P, s)) := by
  change RawCoset.WF n ((masterOpsE p cam).finish (P, s))
  rw [masterNodeH_finish]
  exact masterNodeFull_finish_wf (fun P s hP => line4dDomOps_finish_wf P s hP) P s hP

/-- The master recursion of the variant round at degree `n`, from its trees. -/
noncomputable def masterRecE {p : Params} {q : ℕ → ℕ} (hq : Monotone q) (n : ℕ)
    (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOK (masterRoundE p cam) n q P T) :
    MasterRecursion (masterRoundE p cam) n :=
  masterRecursionOfTrees hT hq (fun P s hP => finishE_wf p n P s hP)

/-- **Line 2 halves the window, for the calls of the run.** At a good, well-formed node of
route 1, every call the run makes has at most half the window of the node (and the node's
window is not empty). -/
theorem roundCalls_line2_half {p : Params} (ok : ParamsOK p) {q : ℕ → ℕ} (hq : Monotone q)
    (n : ℕ) (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOK (masterRoundE p cam) n q P T)
    (I : RawMasterSI) (hG : MasterNodeGood n I) (hI : (masterRoundE p cam).WF I)
    (hr : masterRoute I = 1) (f : ℕ) (hf : (masterRoundE p cam).measure I < f + 1) :
    ∀ J ∈ (masterRoundE p cam).roundCalls f I,
      1 ≤ masterWindowSize I ∧ 2 * masterWindowSize J ≤ masterWindowSize I := by
  set M := masterRecE hq n hT with hM
  have hTl : ∃ T : SIReduction (Fin n) ℕ (Set (Perm (Fin n))),
      LoopMatchG (masterRoundE p cam) (fun J => MasterNodeGood n J ∧ MasterStepProgress I J)
        (fun J => decWinSI n J.1) (fun _ => decCoset n) I
        ((masterRoundE p cam).width I) 0 ((masterRoundE p cam).init I) T ∧
      (∀ K ∈ T.calls, 2 * K.windowSize ≤ masterWindowSize I) ∧ 1 ≤ masterWindowSize I := by
    obtain ⟨B, C₀, a, b, e, f, u, v, u', v', tt, dd, t, d, dc, dp, E⟩ := p
    obtain ⟨⟨hB, hC₀⟩, -⟩ := ok
    dsimp only at hB hC₀
    subst hB hC₀
    exact masterNodeH_line2_half hG hr
  obtain ⟨T, hm, hhalf, h1⟩ := hTl
  obtain ⟨-, h2, h3⟩ := (masterRoundE p cam).loopAux_eqG (rec := (masterRoundE p cam).value f)
    (C := fun J => MasterNodeGood n J ∧ MasterStepProgress I J)
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

/-- **The refined Eq. (74) for the variant round.** Below a good, well-formed root of degree
`n`, the recursion tree has at most `2^{(4Aw + 14Ap + 24)(log₂ n+2)^5}` nodes. -/
theorem nodesE_le {p : Params} (ok : ParamsOK p) (sb : StepBounds p cam) {q : ℕ → ℕ}
    (hq : Monotone q) (n : ℕ) (hT : ∀ P, MasterNodeGood n P → (masterRoundE p cam).WF P →
      ∃ T, MasterNodeTreeOK (masterRoundE p cam) n q P T)
    (I : RawMasterSI) (hG : MasterNodeGood n I) (hI : (masterRoundE p cam).WF I) :
    (masterRoundE p cam).nodes ((masterRoundE p cam).measure I + 1) I ≤
      2 ^ ((4 * sb.Aw + 14 * sb.Ap + 24) * (Nat.log 2 n + 2) ^ 5) := by
  set M := masterRecE hq n hT with hM
  have hdeg : ∀ P, M.Good P → masterDegree P = n := fun P hP => hP.1.1
  refine nodes_le_exp5 (masterRoundE p cam) M.impl M.correct M.progress
    (fun P => masterRoute P = 1)
    (fun _ => 2 ^ (sb.Aw * (Nat.log 2 n + 2) ^ 4)) (fun _ => 2 ^ (sb.Ap * (Nat.log 2 n + 2) ^ 3))
    n sb.Aw sb.Ap ?_ ?_ ?_ le_rfl le_rfl M.win_le _ I hG hI (Nat.lt_succ_self _) ?_
  · intro P hP hW hr f hf J hJ
    obtain ⟨h1, h2⟩ := roundCalls_line2_half ok hq n hT P hP hW hr f hf J hJ
    exact ⟨h1, by omega⟩
  · intro P hP hW _ hr f hf
    exact sb.calls_line2 n P f hP hW hf hr
  · intro P hP hW _ hr f hf
    exact sb.calls_other n P f hP hW hf hr
  · exact le_of_eq (hdeg I hG)

/-- **What the run of the variant round needs of its recursion**: a master recursion at every
degree whose good nodes are good in the sense of `Algo.MasterNodeGood`, with at most
`2^{K (log₂ n+2)^5}` nodes below a good, well-formed node of degree `n`. -/
structure RecOK (p : Params) (cam : RawGens × List ℕ → Option RawCameron) (K : ℕ) where
  M : ∀ n, MasterRecursion (masterRoundE p cam) n
  good : ∀ n J, (M n).Good J → MasterNodeGood n J
  nodes : ∀ n J, (M n).Good J → (masterRoundE p cam).WF J →
    (masterRoundE p cam).nodes ((masterRoundE p cam).measure J + 1) J ≤
      2 ^ (K * (Nat.log 2 n + 2) ^ 5)

/-- The recursion of the variant round at parameters with `Explicit.ParamsOK`. -/
theorem recOK_of_paramsOK {p : Params} (ok : ParamsOK p) (sb : StepBounds p cam)
    (hc : PolyFun cam) (hs : CameronSpec cam) :
    Nonempty (RecOK p cam (4 * sb.Aw + 14 * sb.Ap + 24)) := by
  obtain ⟨q, hqm, hT⟩ := exists_treesE ok hc hs
  exact ⟨⟨fun n => masterRecE hqm n (hT n), fun n J hJ => hJ,
    fun n J hJ hW => nodesE_le ok sb hqm n (hT n) J hJ hW⟩⟩

end Explicit
