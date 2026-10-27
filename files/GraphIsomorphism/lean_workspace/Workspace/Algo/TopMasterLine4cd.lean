import Workspace.Algo.TopMasterNodeCarrier
import Workspace.Algo.PrimitiveLine4dCarrier

/-! # Lines 4c–4d in the node carrier
Section 15, lines 4c–4d run Procedure Align of Section 13 on the versions line 4c found. Line
6 of Align splits on whether a dominant color class exists. Without one, the round is the
loop of Eq. (71), run by `Algo.line4dOps` (Section 9 track). With one, Align goes on at its
lines 7–11; that carrier `GD` is a parameter here (Section 13 track). The test is the
machine's own (`Algo.line4dHasDom`), so the node carrier picks the branch the paper takes.
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The dominant-class test of line 6 of Procedure Align, at a node. -/
def masterHasDom (c tt dd : ℕ) (p : RawMasterSI) : Bool := line4dHasDom c tt dd (line4dHint p)

theorem quasiFun_masterHasDom (c tt dd : ℕ) : QuasiFun (masterHasDom c tt dd) :=
  polyFun_line4dHint.comp_quasiFun (quasiFun_line4dHasDom c tt dd)

/-- **Lines 4c–4d**: the dominant-class carrier `GD` where line 6 of Align finds a dominant
class, and the loop of Eq. (71) (`Algo.line4dOps`) where it does not. -/
def masterLine4cdOps {TD : Type} (c tt dd : ℕ) (GD : MasterOps TD) (dD : TD) :
    MasterOps (TD × AggnRecomputeState) :=
  MasterOps.pairIte (masterHasDom c tt dd) GD (line4dOps c tt dd) dD default

theorem masterLine4cd_cost {TD : Type} [Enc TD] (a b c tt dd : ℕ) {GD : MasterOps TD} (dD : TD)
    (CD : MasterOpsCost a b GD) :
    Nonempty (MasterOpsCost a b (masterLine4cdOps c tt dd GD dD)) := by
  obtain ⟨C⟩ := line4dOps_cost c tt dd a b
  exact ⟨.pairIteQ (quasiFun_masterHasDom c tt dd) CD C⟩

/-- **The node carrier of Section 15** with lines 1, 2, 4a, 4b, 4c–4d (no dominant class)
and 5–7 in place; the dominant-class carrier `GD` of Align lines 7–11 is the one
parameter left. -/
noncomputable def masterNodeFullOps {TD : Type} (B C₀ : ℕ)
    (cameron : RawGens × List ℕ → Option RawCameron) (e f u v c tt dd : ℕ) (GD : MasterOps TD)
    (dD : TD) (c' b' t d dc dp E : ℕ) :=
  masterNodeOps B C₀ cameron e f u v (masterLine4cdOps c tt dd GD dD) (dD, default)
    c' b' t d dc dp E

theorem masterNodeFull_cost {TD : Type} [Enc TD] (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (e f u v c tt dd : ℕ) {GD : MasterOps TD} (dD : TD) (CD : MasterOpsCost a b GD)
    (c' b' t d dc dp E : ℕ) :
    Nonempty (MasterOpsCost a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E)) := by
  obtain ⟨C4⟩ := masterLine4cd_cost a b c tt dd dD CD
  exact masterNode_cost a b B C₀ hc e f u v (dD, default) C4 c' b' t d dc dp E

theorem masterNodeFull_runCostQ {TD : Type} [Enc TD] (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (e f u v c tt dd : ℕ) {GD : MasterOps TD} (dD : TD) (CD : MasterOpsCost a b GD)
    (c' b' t d dc dp E : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b
      (masterNodeFullOps B C₀ cameron e f u v c tt dd GD dD c' b' t d dc dp E))) :=
  (masterNodeFull_cost a b B C₀ hc e f u v c tt dd dD CD c' b' t d dc dp E).map
    MasterOpsCost.runCostQ

section Match
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
/-- **Section 15, lines 4c–4d, in the node carrier, without a dominant class.** At a node of
route `4` where line 6 of Procedure Align finds no dominant color class, the node carrier
walks the round of Align of the Master (`Babai.Line4cdData`) on the window, read on the
node's domain and shifted by the node's representative (`Algo.line4dOps_match`). -/
theorem masterNodeFull_line4cd_match {TD : Type} {a b B C₀ : ℕ}
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
          D.shape.red).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) := by
  obtain ⟨D, hdom, hD, hm⟩ := line4dOps_match hx hy hgs hnd hlt hinv hp hG hϕ hn hr hb a b hnd'
  exact ⟨D, hdom, hD, masterTop_hinted_match (by simp) <| masterHint_line4cd_match hr <|
    masterPairIte_start_neg a b (show masterHasDom c tt dd (p.1, some p.2) = false from hnd') hm⟩
end Match

end Algo
