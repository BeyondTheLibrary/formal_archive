import Workspace.Algo.TopMasterRecursionBuild
import Workspace.Algo.PrimitiveLine4dDom
import Workspace.Algo.TopMasterRecursionL57

/-! # The master recursion with the dominant-class carrier of lines 4c–4d

Section 15, lines 4c–4d, with a dominant color class (Procedure Align, lines 7–11): the
carrier `GD` of the full node carrier is `Algo.line4dDomOps` (Section 13 track).  This file
supplies what `Algo.siWorkspaceRoutine_of_masterParamRoutes` asks of `GD`: its local costs
(`Algo.line4dDomOps_cost`) and well-formed answers (`Algo.line4dDomOps_finish_wf`), and
states the final routine with `GD := line4dDomOps`, leaving only the rounds of lines 4c–7
(`Algo.MasterParamRoutes`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- **The answers of the dominant-class carrier are well formed**: it returns through the
final shift `top3Shift` to the node's candidate coset, as line 4d does. -/
theorem line4dDomOps_finish_wf {c tt dd n : ℕ} (P : RawMasterSI) (s : ADState)
    (hP : masterDegree P = n) : RawCoset.WF n ((line4dDomOps c tt dd).finish (P, s)) :=
  rawCoset_wf_top3Shift (dom := (line4dHint P).1.2.2.2.1) hP _ _

/-- **Theorem 1.1.1 on the RAM with the dominant-class carrier of the Section 13 track.**
With `GD := line4dDomOps`, the full node carrier solves String Isomorphism in
quasipolynomial time once the rounds of lines 4c–4d and 5–7 are supplied at every degree
(`Algo.MasterParamRoutes`, with a monotone quasipolynomial call bound `q45`). -/
theorem siWorkspaceRoutine_of_masterParamRoutes_dom
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {e f u v c tt dd : ℕ} (hTc : TopwpCap e f)
    (hTo : Top4wCap e f u v) {c' b' t d dc dp E : ℕ} {q45 : ℕ → ℕ}
    (hq45 : Monotone q45) (hq : QuasiPolyBound q45)
    (h45 : ∀ n, MasterParamRoutes (masterAdmittedRound masterCapA masterCapB
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd
        (line4dDomOps c tt dd) default c' b' t d dc dp E)) n q45) : SIWorkspaceRoutine := by
  obtain ⟨CD⟩ := line4dDomOps_cost c tt dd masterCapA masterCapB
  exact siWorkspaceRoutine_of_masterParamRoutes hc hs hTc hTo default CD hq45 hq
    (fun n P s hP => line4dDomOps_finish_wf P s hP) h45

/-- **Theorem 1.1.1 on the RAM, with route 5 reduced to the window.** As
`Algo.siWorkspaceRoutine_of_masterParamRoutes_dom`, with the two parameter routes supplied
separately: route 4 (lines 4c–4d) as `Algo.MasterParamRoute`, and route 5 (lines 5–7) as a
tree on the window at every node (`Algo.MasterL57Supply`), for a reserve exponent `E` that
bounds the reserves of the round of lines 5–7 (`Algo.MasterL57EOK`; one exists by
`Algo.exists_masterL57EOK`). -/
theorem siWorkspaceRoutine_of_routes_dom
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {e f u v c tt dd : ℕ} (hTc : TopwpCap e f)
    (hTo : Top4wCap e f u v) {c' b' t d dc dp E : ℕ} (hE : MasterL57EOK c' b' t d dc dp e f E)
    {q45 : ℕ → ℕ} (hq45 : Monotone q45) (hq : QuasiPolyBound q45)
    (h4 : ∀ n, MasterParamRoute (masterAdmittedRound masterCapA masterCapB
      (masterNodeFullOps masterLine1B masterLine1C₀ cameron e f u v c tt dd
        (line4dDomOps c tt dd) default c' b' t d dc dp E)) n q45 4)
    (h5 : ∀ n, MasterL57Supply c' b' t d dc dp e f n q45) : SIWorkspaceRoutine :=
  siWorkspaceRoutine_of_masterParamRoutes_dom hc hs hTc hTo hq45 hq
    (fun n => masterParamRoutes_of_route (h4 n) (masterParamRoute5_of_supply hE (h5 n)))

end Algo
