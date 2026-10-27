import Workspace.Algo.TopMasterHintCarrier

/-! # Section 15: line 1 and the hinted lines on one carrier
The Master Algorithm runs line 1 at a node without a Johnson hint, and one of
lines 2–7 at a node with a hint. This file puts the line-1 carrier and a
carrier `H` for the hinted nodes on one carrier; each keeps its own fold state
(`MasterOps.pairIte`). The hinted carrier is a parameter here; the lines 2–7
carrier `masterHintOps` is one instance. Whatever `H` matches at a hinted node,
the combined carrier matches too, and the local costs add.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The test of the first line: the node carries no hint. -/
def masterIsLine1 (p : RawMasterSI) : Bool := decide (masterRoute p = 0)

theorem polyFun_masterIsLine1 : PolyFun masterIsLine1 :=
  polyFun_masterRoute.natEq (polyFun_const 0)

theorem masterIsLine1_iff (p : RawMasterSI) : masterIsLine1 p = true ↔ p.2 = none := by
  rw [masterIsLine1, decide_eq_true_iff, masterRoute_line1]

/-- **The Master Algorithm's node carrier**, with the hinted lines supplied by `H`. -/
def masterTopOps {T : Type} (B C₀ : ℕ) (cameron : RawGens × List ℕ → Option RawCameron)
    (H : MasterOps T) (dT : T) : MasterOps (AggnRecomputeState × T) :=
  MasterOps.pairIte masterIsLine1 (masterLine1Ops B C₀ cameron) H (masterCamFoldEmbed none) dT

/-- The node carrier has one local cost package once the hinted carrier has one. -/
theorem masterTop_cost (a b B C₀ : ℕ) {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) {T : Type} [Enc T] {H : MasterOps T} (dT : T) (CH : MasterOpsCost a b H) :
    Nonempty (MasterOpsCost a b (masterTopOps B C₀ cameron H dT)) :=
  (masterLine1_cost a b B C₀ hc).map fun C => .pairIte polyFun_masterIsLine1 C CH

/-- The node carrier runs as one raw round at all ambient degrees. -/
theorem masterTop_runCostQ (a b B C₀ : ℕ) {cameron : RawGens × List ℕ → Option RawCameron}
    (hc : PolyFun cameron) {T : Type} [Enc T] {H : MasterOps T} (dT : T) (CH : MasterOpsCost a b H) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterTopOps B C₀ cameron H dT))) :=
  (masterTop_cost a b B C₀ hc dT CH).map MasterOpsCost.runCostQ

/-- **Section 15, line 1, in the node carrier.** At a node without hint the node
carrier runs line 1 as `masterLine1_match` describes. -/
theorem masterTop_line1_match {a b n : ℕ} {W : RawWinSI} (hW : AggnCheckedWindowWF n W)
    (hinv : IsInvariant (decGroup n W.2.1) (winSet n W.1))
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron)
    (hs : CameronSpec cameron) {T : Type} (H : MasterOps T) (dT : T)
    (hcap : masterCameronChildBound n ≤ masterInputCap a b n) :
    LoopMatch (masterAdmittedRound a b (masterTopOps masterLine1B masterLine1C₀ cameron H dT)) (fun J => decWinSI n J.1)
      (decCoset n) (W, none) ((masterTopOps masterLine1B masterLine1C₀ cameron H dT).width (W, none)) 0
      ((masterTopOps masterLine1B masterLine1C₀ cameron H dT).init (W, none)) (masterLine1Tree hW hinv hc hs) :=
  masterPairIte_start_pos a b ((masterIsLine1_iff _).mpr rfl) (masterLine1_match hW hinv hc hs hcap)

/-- **The hinted lines in the node carrier.** At a node with a hint, the node
carrier runs whatever the hinted carrier runs. -/
theorem masterTop_hinted_match {a b n B C₀ : ℕ} {p : RawMasterSI} (hp : p.2 ≠ none)
    {cameron : RawGens × List ℕ → Option RawCameron} {T' : Type} {H : MasterOps T'} {dT : T'}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (h : LoopMatch (masterAdmittedRound a b H) (fun J => decWinSI n J.1) (decCoset n) p
      (H.width p) 0 (H.init p) T) :
    LoopMatch (masterAdmittedRound a b (masterTopOps B C₀ cameron H dT)) (fun J => decWinSI n J.1)
      (decCoset n) p ((masterTopOps B C₀ cameron H dT).width p) 0 ((masterTopOps B C₀ cameron H dT).init p) T := by
  have hf : masterIsLine1 p = false := by
    cases hq : masterIsLine1 p
    · rfl
    · exact absurd ((masterIsLine1_iff p).mp hq) hp
  exact masterPairIte_start_neg a b hf h
end Algo
