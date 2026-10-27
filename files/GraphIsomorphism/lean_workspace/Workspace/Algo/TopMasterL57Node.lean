import Workspace.Algo.TopMasterL57Calls
import Workspace.Algo.TopMasterWinLink
import Workspace.Algo.TopMasterConstants

/-! # Lines 5–7 at a node of the Master Algorithm
At a hinted node of route 5, the node carrier runs the round of lines 5–7 on the window and
lifts it (`Algo.masterNode_line57_match`). The Section 13 track matches that round, case by
case, against the Master's round `Babai.Line57Shape.red` (`Algo.aggnL57G_align_match`,
`Algo.aggnL57G_align_match_small`, `Algo.aggnL57G_rejectCase_match`,
`Algo.aggnL57G_rejectDefect_match`), and against outcome (2a) (`Algo.aggnL57G_giant_match`). Here any such match, for a round that is the round of a
`Babai.Line57Data` without a hint, becomes a match of the node carrier with every side
condition discharged: the calls lie in the restricted group, the answer too, and every lifted
call is admitted (`Algo.masterL57_calls_admitted`). The walked tree makes the calls of the
paper's lifted round and returns its value (`Algo.top4wTree_calls_eq_liftWindow`,
`Algo.top4wTree_run_eq_liftWindow`).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

section Node
variable {n : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1) (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))

include hx hy hgs in
/-- **Section 15, lines 5–7, at a node, with the side conditions discharged.** Let `D` be a
round of lines 5–7 on the window (`Babai.Line57Data`) that makes no hinted call, on the context
of the node (`Algo.masterL57Ctx`: the group `G_Δ` and the two strings on the window with their
letters renamed), and let the round of lines 5–7 on the machine walk `D`'s reduction at the
node's lines-5–7 node. Then the node carrier walks the lift to the node's domain of that
reduction with its letters renamed back, shifted to the node's frame; that lift makes the calls
of the paper's lift `Babai.liftWindow` of the renamed-back reduction and returns its value. -/
theorem masterNodeFull_line57_match {TD : Type} {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v c tt dd : ℕ}
    {GD : MasterOps TD} {dD : TD} {c' b' t d dc dp E : ℕ}
    (hE : MasterL57EOK c' b' t d dc dp e f E)
    (h5 : masterHintRoute p = 5) (hg : masterL57Guard (p.1, some p.2) = true)
    (hΔ : 0 < p.1.1.length)
    {m : ℕ} {ϕ : decGroup p.1.1.length (masterL57Ctx (p.1, some p.2)).1.1.2 →* Perm (Fin m)}
    {ts par cost : ℕ}
    (D : Line57Data (Fin p.1.1.length) ℕ
      (decGroup p.1.1.length (masterL57Ctx (p.1, some p.2)).1.1.2)
      (decStrN p.1.1.length (masterL57Ctx (p.1, some p.2)).2.1)
      (decStrN p.1.1.length (masterL57Ctx (p.1, some p.2)).2.2.1) ϕ ts par cost)
    (hno : line57NoDom D.shape)
    (h : LoopMatch (masterL57Round c' b' t d dc dp e f) (aggnPhaseDecode p.1.1.length)
      (decCoset p.1.1.length) (masterL57Enter (p.1, some p.2))
      ((masterL57Round c' b' t d dc dp e f).width (masterL57Enter (p.1, some p.2))) 0
      ((masterL57Round c' b' t d dc dp e f).init (masterL57Enter (p.1, some p.2)))
      (D.shape.red D.enum)) :
    LoopMatch (masterAdmittedRound a b
        (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).width
        (p.1, some p.2)) 0
      ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).init
        (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) (D.shape.red D.enum))).bind
          (fun A => .done (decPerm n p.1.2.2.1 • A))) ∧
    (top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) (D.shape.red D.enum))).calls =
      (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
        (topwSubtypeRed hnd hlt (masterL57Unl (p.1, some p.2) (D.shape.red D.enum)))).calls ∧
    (top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) (D.shape.red D.enum))).run =
      (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
        (topwSubtypeRed hnd hlt (masterL57Unl (p.1, some p.2) (D.shape.red D.enum)))).run := by
  have hgrp : decGroup p.1.1.length (masterL57Ctx (p.1, some p.2)).1.1.2 =
      (winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :=
    (masterL57Ctx_group (p.1, some p.2)).trans (masterLine4b_group (p := p) hgs hnd hlt hinv)
  have hN : p.1.1.length ≤ p.1.2.2.2.1.length := by
    rw [hx.1]; exact length_le_of_nodup_lt hnd hlt
  have hsmall := line57Data_calls_small D hno (k := 2 * p.1.1.length + 1)
    (masterL57Ctx_letters_x (p.1, some p.2)) (masterL57Ctx_letters_y (p.1, some p.2))
  have hlet : ∀ J ∈ (D.shape.red D.enum).calls, MasterCallLetters (2 * p.1.1.length + 1) J :=
    fun J hJ => (hsmall J hJ).1
  have hK : ∀ J ∈ (D.shape.red D.enum).calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  have hR : (D.shape.red D.enum).run ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [D.run_red, ← hgrp]
    exact fun _ h => h.1
  have hKU : ∀ J ∈ (masterL57Unl (p.1, some p.2) (D.shape.red D.enum)).calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [masterL57Unl_calls (P := (p.1, some p.2)) hN hlet]
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := List.mem_map.1 hJ
    exact hK J₀ hJ₀
  have hL := masterL57_calls_admitted hx hy hnd hlt hinv hΔ D hno hK
  refine ⟨?_, top4wTree_calls_eq_liftWindow hnd hlt hinv _ _ hKU,
    top4wTree_run_eq_liftWindow hnd hlt hinv _ _ hKU⟩
  exact masterNode_line57_match (gens := p.1.2.1.map (decPerm n)) hE h5 hg hx.1
    (map_encPerm_decPerm hgs).symm hnd hlt hinv h hlet hK hR hL
end Node

section Line4cd
variable {c tt dd : ℕ} {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 4)
    (hb : Line4cBounds c tt dd)

include hx hy hgs hp hG hϕ hn hr hb in
/-- **Section 15, lines 4c–4d, at a node, linked to the paper's lift.** Without a dominant
color class, the node carrier walks the lift of the round of Procedure Align of the Master
(`Algo.masterNodeFull_line4cd_match`), and that lift makes the calls of the paper's lift
`Babai.liftWindow` of the relabelled round and returns its value. -/
theorem masterNodeFull_line4cd_link {TD : Type} {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ} {GD : MasterOps TD}
    {dD : TD} {c' b' t d dc dp E : ℕ} (hnd' : line4dHasDom c tt dd p = false) :
    ∃ D : Line4cdData (Fin p.1.1.length) ℕ (decGroup p.1.1.length (masterHintTop p).1.1.2)
        (decStrN p.1.1.length (masterHintTop p).2.1)
        (decStrN p.1.1.length (masterHintTop p).2.2) m
        (line4cdCost (line4dQ c tt dd) c923 (Fintype.card (Fin p.1.1.length))),
      D.shape.dom = none ∧ AVDescribes p.1.1.length (line4dHdr c tt dd p) D.shape (D.shape.head :: D.shape.tail) ∧
      LoopMatch (masterAdmittedRound a b
          (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E))
        (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
        ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).width
          (p.1, some p.2)) 0
        ((masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E).init
          (p.1, some p.2))
        ((top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
          D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) ∧
      (top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
          D.shape.red).calls =
        (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
          (topwSubtypeRed hnd hlt D.shape.red)).calls ∧
      (top4wTree p.1.1 hnd hlt (decGroup n p.1.2.1) hinv (decStrN n p.1.2.2.2.1)
          D.shape.red).run =
        (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
          (topwSubtypeRed hnd hlt D.shape.red)).run := by
  obtain ⟨D, hdom, hD, hm⟩ := masterNodeFull_line4cd_match (a := a) (b := b) (B := B)
    (C₀ := C₀) (cameron := cameron) (e := e) (f := f) (u := u) (v := v) (GD := GD) (dD := dD)
    (c' := c') (b' := b') (t := t) (d := d) (dc := dc) (dp := dp) (E := E)
    hx hy hgs hnd hlt hinv hp hG hϕ hn hr hb hnd'
  have hgrp := masterLine4b_group hgs hnd hlt hinv
  have hK : ∀ J ∈ D.shape.red.calls, J.K ⊆
      ((winRestrictHom n p.1.1 hnd hlt (decGroup n p.1.2.1) hinv).range :
        Set (Perm (Fin p.1.1.length))) := by
    rw [← hgrp]
    exact D.calls_K
  exact ⟨D, hdom, hD, hm, top4wTree_calls_eq_liftWindow hnd hlt hinv _ _ hK,
    top4wTree_run_eq_liftWindow hnd hlt hinv _ _ hK⟩
end Line4cd

end Algo
