import Workspace.Algo.TopMasterTopCarrier
import Workspace.Algo.TopMasterLine57Lift

/-! # The node carrier of the Master Algorithm, with lines 5–7 in place
Section 15 runs one of its lines at each node. Line 1 runs at nodes without hint
(`Algo.masterLine1Ops`); at hinted nodes, lines 2, 4a, 4b, 4c–4d and 5–7 run by the route of
the node (`Algo.masterHintOps`). Here the lines 5–7 slot is filled by the lifted round of
lines 5–7 (`Algo.masterL57Ops`). The lines 4c–4d carrier stays a parameter `G4`: it is built
with the primitive case (Section 9 of the formalization plan).
-/
set_option synthInstance.maxSize 2048
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

/-- The hinted carrier with lines 5–7 in place. -/
noncomputable def masterHintL57Ops {T4 : Type} (e f u v : ℕ) (G4 : MasterOps T4) (d4 : T4)
    (c b' t d dc dp E : ℕ) : MasterOps (MasterHintState T4 AggnL57GState) :=
  masterHintOps e f u v G4 (masterL57Ops c b' t d dc dp e f E) d4 default

/-- **The node carrier of Section 15**, with line 1, lines 2, 4a, 4b and 5–7 in place, and
lines 4c–4d as the parameter `G4`. -/
noncomputable def masterNodeOps {T4 : Type} (B C₀ : ℕ)
    (cameron : RawGens × List ℕ → Option RawCameron) (e f u v : ℕ) (G4 : MasterOps T4)
    (d4 : T4) (c b' t d dc dp E : ℕ) :
    MasterOps (AggnRecomputeState × MasterHintState T4 AggnL57GState) :=
  masterTopOps B C₀ cameron (masterHintL57Ops e f u v G4 d4 c b' t d dc dp E)
    (masterCamFoldEmbed none, masterCamFoldEmbed none, default, d4, default)

/-- The hinted carrier has local costs once the lines 4c–4d carrier has. -/
theorem masterHintL57_cost {T4 : Type} [Enc T4] (a b e f u v : ℕ) {G4 : MasterOps T4}
    (d4 : T4) (C4 : MasterOpsCost a b G4) (c b' t d dc dp E : ℕ) :
    Nonempty (MasterOpsCost a b (masterHintL57Ops e f u v G4 d4 c b' t d dc dp E)) := by
  obtain ⟨C5⟩ := masterL57_cost a b c b' t d dc dp e f E
  exact masterHint_cost a b e f u v d4 default C4 C5

/-- **The node carrier has local costs**, hence runs as one raw round at all ambient degrees,
once the lines 4c–4d carrier has local costs. -/
theorem masterNode_cost {T4 : Type} [Enc T4] (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron) (e f u v : ℕ)
    {G4 : MasterOps T4} (d4 : T4) (C4 : MasterOpsCost a b G4) (c b' t d dc dp E : ℕ) :
    Nonempty (MasterOpsCost a b (masterNodeOps B C₀ cameron e f u v G4 d4 c b' t d dc dp E)) := by
  obtain ⟨CH⟩ := masterHintL57_cost a b e f u v d4 C4 c b' t d dc dp E
  exact masterTop_cost a b B C₀ hc _ CH

theorem masterNode_runCostQ {T4 : Type} [Enc T4] (a b B C₀ : ℕ)
    {cameron : RawGens × List ℕ → Option RawCameron} (hc : PolyFun cameron) (e f u v : ℕ)
    {G4 : MasterOps T4} (d4 : T4) (C4 : MasterOpsCost a b G4) (c b' t d dc dp E : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b
      (masterNodeOps B C₀ cameron e f u v G4 d4 c b' t d dc dp E))) :=
  (masterNode_cost a b B C₀ hc e f u v d4 C4 c b' t d dc dp E).map MasterOpsCost.runCostQ

/-- **Section 15, lines 5–7, in the node carrier.** At a hinted node of route 5 whose
lines-5–7 node is well formed, the node carrier walks the lifted tree of the round of lines
5–7, with its letters renamed back, shifted back to the node's frame (`Algo.masterL57_match`). -/
theorem masterNode_line57_match {T4 : Type} {a b B C₀ : ℕ}
    {cameron : RawGens × List ℕ → Option RawCameron} {e f u v : ℕ} {G4 : MasterOps T4}
    {d4 : T4} {c b' t d dc dp E : ℕ}
    (hE : MasterL57EOK c b' t d dc dp e f E)
    {n : ℕ} {p : MasterHintInput} {gens : List (Perm (Fin n))}
    (h5 : masterHintRoute p = 5) (hg : masterL57Guard (p.1, some p.2) = true)
    (hx : p.1.2.2.2.1.length = n) (hgens : p.1.2.1 = gens.map (encPerm n))
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n p.1.1))
    {T₀ : SIReduction (Fin p.1.1.length) ℕ (Set (Perm (Fin p.1.1.length)))}
    (h : LoopMatch (masterL57Round c b' t d dc dp e f) (aggnPhaseDecode p.1.1.length)
      (decCoset p.1.1.length) (masterL57Enter (p.1, some p.2))
      ((masterL57Round c b' t d dc dp e f).width (masterL57Enter (p.1, some p.2))) 0
      ((masterL57Round c b' t d dc dp e f).init (masterL57Enter (p.1, some p.2))) T₀)
    (hlet : ∀ J ∈ T₀.calls, MasterCallLetters (2 * p.1.1.length + 1) J)
    (hK : ∀ J ∈ T₀.calls, J.K ⊆ ((winRestrictHom n p.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin p.1.1.length))))
    (hRun : T₀.run ⊆ ((winRestrictHom n p.1.1 hnd hlt (genGroup gens) hinv).range :
      Set (Perm (Fin p.1.1.length))))
    (hL : ∀ J ∈ (top4wTree p.1.1 hnd hlt (genGroup gens) hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) T₀)).calls,
      MasterCallLetters (2 * n + 1) J ∧ J.windowSize < p.1.1.length ∧
        ∃ G : Subgroup (Perm (Fin n)), IsCosetInstance G J) :
    LoopMatch (masterAdmittedRound a b
        (masterNodeOps B C₀ cameron e f u v G4 d4 c b' t d dc dp E))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterNodeOps B C₀ cameron e f u v G4 d4 c b' t d dc dp E).width (p.1, some p.2)) 0
      ((masterNodeOps B C₀ cameron e f u v G4 d4 c b' t d dc dp E).init (p.1, some p.2))
      ((top4wTree p.1.1 hnd hlt (genGroup gens) hinv (decStrN n p.1.2.2.2.1)
        (masterL57Unl (p.1, some p.2) T₀)).bind (fun A => .done (decPerm n p.1.2.2.1 • A))) :=
  masterTop_hinted_match (by simp) <| masterHint_line57_match h5 <|
    masterL57_match (P := (p.1, some p.2)) hE hg hx hgens hnd hlt hinv a b h hlet hK hRun hL

end Algo
