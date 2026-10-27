import Workspace.Algo.TopMasterLineOne
import Workspace.Algo.TopMasterLineTwoLive
import Workspace.Algo.TopMasterFourOpenCost

/-! # Section 15, lines 2–7 on the RAM: one carrier for the hinted nodes
A node with a Johnson hint runs one of lines 2–7 of the Master Algorithm. The computed test
`masterRoute` picks the line: 1 for line 2 (the Luks descent on the hint, when the Johnson
parameter is small), 2 for line 4a (the giant exit of the primitive case), 3 for line 4b
(Cor. 12.0.10 on the twins), 4 for lines 4c–4d (the Extended Design Lemma and Align), and
5 for lines 5–7 (AggregateCertificates, then Align).

Lines 2, 4a and 4b already have matched carriers. Lines 4c–4d and lines 5–7 enter as
parameter carriers with their own fold states and cost packages: the first is being built by
the Section 9 track, the second needs the window lift of the lines 5–7 round
(`Algo.aggnL57Round`) to the ambient node. This file puts all five on one carrier.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The route test at a node: whether `masterRoute` takes the given value. -/
def masterRouteAt (k : ℕ) (p : RawMasterSI) : Bool := decide (masterRoute p = k)

theorem polyFun_masterRouteAt (k : ℕ) : PolyFun (masterRouteAt k) :=
  polyFun_masterRoute.natEq (polyFun_const k)

/-- The hint input a node carries, with a default hint at a node without one. -/
def masterHintGet (p : RawMasterSI) : MasterHintInput := (p.1, p.2.getD default)

theorem polyFun_masterHintGet : PolyFun masterHintGet :=
  polyFun_fst.pair ((polyFun_snd.pair (polyFun_const default)).comp polyFun_optionGetD)

theorem polyFun_optionIsSome {α : Type} [Enc α] : PolyFun (fun o : Option α => o.isSome) :=
  ((polyFun_id.pair (polyFun_const (0 : ℕ))).comp
    (PolyFun.optionElim (polyFun_const false) (polyFun_const true))).of_eq
    (fun o => by cases o <;> rfl)

/-! ### A leaf carrier matched from any one-step round -/

/-- A leaf round that stops at once matches the leaf carrier at any node. -/
theorem masterLeafOps_match_of {ω : Type} {a b n : ℕ} {f : RawWinSI → RawCoset}
    (R : Round RawWinSI ω RawCoset) {P : RawMasterSI} {s : ω}
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hf : R.finish (P.1, s) = f P.1)
    (h : LoopMatch R (decWinSI n) (decCoset n) P.1 0 0 s T) :
    LoopMatch (masterAdmittedRound a b (masterLeafOps f)) (fun J => decWinSI n J.1) (decCoset n)
      P ((masterLeafOps f).width P) 0 ((masterLeafOps f).init P) T := by
  cases h with
  | done w j s A hc ha =>
    exact .done _ _ _ A (by
      show masterGuardedChild a b (masterLeafOps f) (P, 0, (masterLeafOps f).init P) = none
      exact if_neg (lt_irrefl 0)) (by
        change decCoset n (f P.1) = A
        rw [← hf]; exact ha)

/-! ### Line 4b on the master carrier -/

/-- The line-4b carrier of `TopMasterFourOpen` at a hinted node; it asks nothing at a node
without hint. -/
def master4bOps (e f u v : ℕ) : MasterOps Top4State where
  width P := if P.2.isSome then master4OpenWidth (masterHintGet P) else 0
  child z := if z.1.2.isSome then master4OpenChild e f u v (masterHintGet z.1, z.2.1, z.2.2)
    else none
  init P := if P.2.isSome then master4OpenInit (masterHintGet P) else default
  combine z := if z.1.2.isSome then
      master4OpenCombine (masterHintGet z.1, z.2.1, z.2.2.1, z.2.2.2) else default
  finish z := master4OpenFinish (masterHintGet z.1, z.2)

/-- The local cost data of the line-4b carrier. -/
theorem master4b_cost (a b e f u v : ℕ) : Nonempty (MasterOpsCost a b (master4bOps e f u v)) := by
  obtain ⟨c, d, hb⟩ := master4Open_uniform_bounds a b
  have hs : PolyFun (fun P : RawMasterSI => P.2.isSome) := polyFun_snd.comp polyFun_optionIsSome
  have hs1 : PolyFun (fun z : RawMasterSI × ℕ × Top4State => z.1.2.isSome) := polyFun_fst.comp hs
  have hs2 : PolyFun (fun z : RawMasterSI × ℕ × Top4State × RawCoset => z.1.2.isSome) :=
    polyFun_fst.comp hs
  have hg1 : PolyFun (fun z : RawMasterSI × ℕ × Top4State =>
      master4OpenChild e f u v (masterHintGet z.1, z.2.1, z.2.2)) :=
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp
      (polyFun_master4OpenChild e f u v)
  have hg2 : PolyFun (fun z : RawMasterSI × ℕ × Top4State × RawCoset =>
      master4OpenCombine (masterHintGet z.1, z.2.1, z.2.2.1, z.2.2.2)) :=
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp polyFun_master4OpenCombine
  have hdef : ∀ n, Enc.size (default : Top4State) ≤ master4OpenStateBound c d n +
      Enc.size (default : Top4State) := fun n => Nat.le_add_left _ _
  refine ⟨⟨fun n => master4OpenStateBound c d n + Enc.size (default : Top4State),
    master4OpenWidthBound c d,
    (polyBound_master4OpenStateBound c d).quasiPoly.add (polyBound_const _).quasiPoly,
    fun _ _ h => Nat.add_le_add_right (mono_master4OpenStateBound c d h) _,
    (polyBound_master4OpenWidthBound c d).quasiPoly,
    (PolyFun.ite hs (polyFun_masterHintGet.comp polyFun_master4OpenWidth)
      (polyFun_const 0)).quasiFun,
    (PolyFun.ite hs1 hg1 (polyFun_const none)).quasiFun,
    (PolyFun.ite hs (polyFun_masterHintGet.comp polyFun_master4OpenInit)
      (polyFun_const default)).quasiFun,
    (PolyFun.ite hs2 hg2 (polyFun_const default)).quasiFun,
    ((polyFun_fst.comp polyFun_masterHintGet).pair polyFun_snd).comp_quasiFun
      quasiFun_master4OpenFinish, ?_, ?_, ?_, ?_⟩⟩
  · intro P hP
    change Enc.size (if P.2.isSome then master4OpenInit (masterHintGet P) else default) ≤ _
    obtain ⟨W, o⟩ := P
    cases o with
    | none => exact hdef _
    | some h => exact ((hb (W, h) hP).1).trans (Nat.le_add_right _ _)
  · intro P j s A hP _
    change Enc.size (if P.2.isSome then
      master4OpenCombine (masterHintGet P, j, s, A) else default) ≤ _
    obtain ⟨W, o⟩ := P
    cases o with
    | none => exact hdef _
    | some h => exact (((hb (W, h) hP).2.1) j s A).trans (Nat.le_add_right _ _)
  · intro P s _
    exact (master4OpenFinish_size (masterHintGet P) s).trans (by
      change chainBound (masterDegree P) ≤ _
      unfold masterInputCap; omega)
  · intro P hP
    change (if P.2.isSome then master4OpenWidth (masterHintGet P) else 0) ≤ _
    obtain ⟨W, o⟩ := P
    cases o with
    | none => exact Nat.zero_le _
    | some h => exact (hb (W, h) hP).2.2

/-- **Section 15, line 4b, on the master carrier.** At a line-4b node the carrier runs
the tree of `masterAdmittedRound_four_match`. -/
theorem master4b_match (a b e f u v : ℕ) {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hgs : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ z ∈ p.1.1, z < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hϕ : IsGiantRep ϕ) (hn : 64 ≤ p.1.1.length) (hr : masterHintRoute p = 3)
    (hcap : TopwpCap e f) (houter : Top4wCap e f u v) :
    LoopMatch (masterAdmittedRound a b (master4bOps e f u v)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((master4bOps e f u v).width (p.1, some p.2)) 0
      ((master4bOps e f u v).init (p.1, some p.2))
      (master4Tree hnd hlt hinv hp hG hϕ hn hr) :=
  masterAdmittedRound_four_match a b e f u v hx hy hgs hnd hlt hinv hp hG hϕ hn hr hcap houter
    id rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl)

/-! ### The hinted carrier -/

/-- The fold state of the hinted carrier: line 2, line 4a, line 4b, then the two parameter
carriers. -/
abbrev MasterHintState (T4 T5 : Type) :=
  AggnRecomputeState × AggnRecomputeState × Top4State × T4 × T5

/-- **Section 15, lines 2–7, on one carrier.** `G4` is the carrier of lines 4c–4d and `G5`
the carrier of lines 5–7, with defaults `d4`, `d5` for their fold states. -/
def masterHintOps {T4 T5 : Type} (e f u v : ℕ) (G4 : MasterOps T4) (G5 : MasterOps T5)
    (d4 : T4) (d5 : T5) : MasterOps (MasterHintState T4 T5) :=
  MasterOps.pairIte (masterRouteAt 1) (masterDescPreparedOps 3)
    (MasterOps.pairIte (masterRouteAt 2) (masterLeafOps primitiveWindowLeaf)
      (MasterOps.pairIte (masterRouteAt 3) (master4bOps e f u v)
        (MasterOps.pairIte (masterRouteAt 4) G4 G5 d4 d5) default (d4, d5))
      (masterCamFoldEmbed none) (default, d4, d5))
    (masterCamFoldEmbed none) (masterCamFoldEmbed none, default, d4, d5)

/-- The hinted carrier has one local cost package once the two parameter carriers have one. -/
theorem masterHint_cost {T4 T5 : Type} [Enc T4] [Enc T5] (a b e f u v : ℕ)
    {G4 : MasterOps T4} {G5 : MasterOps T5} (d4 : T4) (d5 : T5)
    (C4 : MasterOpsCost a b G4) (C5 : MasterOpsCost a b G5) :
    Nonempty (MasterOpsCost a b (masterHintOps e f u v G4 G5 d4 d5)) := by
  obtain ⟨C1⟩ := masterShiftDescOpen_cost a b masterDescPreparedSelect
    polyFun_masterDescPreparedSelect (fun _ => rfl)
  obtain ⟨C2⟩ := masterLeafOps_cost a b polyFun_primitiveWindowLeaf primitiveWindowLeaf_size
  obtain ⟨C3⟩ := master4b_cost a b e f u v
  exact ⟨.pairIte (polyFun_masterRouteAt 1) C1 <| .pairIte (polyFun_masterRouteAt 2) C2 <|
    .pairIte (polyFun_masterRouteAt 3) C3 <| .pairIte (polyFun_masterRouteAt 4) C4 C5⟩

section HintMatch
variable {T4 T5 : Type} {e f u v a b n : ℕ} {G4 : MasterOps T4} {G5 : MasterOps T5}
    {d4 : T4} {d5 : T5} {p : MasterHintInput}

theorem masterRouteAt_true {k : ℕ} (h : masterHintRoute p = k) :
    masterRouteAt k (p.1, some p.2) = true := decide_eq_true h

theorem masterRouteAt_false {k : ℕ} (h : masterHintRoute p ≠ k) :
    masterRouteAt k (p.1, some p.2) = false := decide_eq_false h

/-- **Line 2 in the hinted carrier.** -/
theorem masterHint_line2_match (h1 : masterHintRoute p = 1)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatch (masterAdmittedRound a b (masterDescPreparedOps 3)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((masterDescPreparedOps 3).width (p.1, some p.2)) 0
      ((masterDescPreparedOps 3).init (p.1, some p.2)) T) :
    LoopMatch (masterAdmittedRound a b (masterHintOps e f u v G4 G5 d4 d5))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterHintOps e f u v G4 G5 d4 d5).width (p.1, some p.2)) 0
      ((masterHintOps e f u v G4 G5 d4 d5).init (p.1, some p.2)) T :=
  masterPairIte_start_pos a b (masterRouteAt_true h1) hm

/-- **Line 4a in the hinted carrier.** -/
theorem masterHint_line4a_match (h2 : masterHintRoute p = 2)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatch (primitiveWindowRound a b) (decWinSI n) (decCoset n) p.1 0 0 0 T) :
    LoopMatch (masterAdmittedRound a b (masterHintOps e f u v G4 G5 d4 d5))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterHintOps e f u v G4 G5 d4 d5).width (p.1, some p.2)) 0
      ((masterHintOps e f u v G4 G5 d4 d5).init (p.1, some p.2)) T :=
  masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
    masterPairIte_start_pos a b (masterRouteAt_true h2) <|
      masterLeafOps_match_of (P := (p.1, some p.2)) (primitiveWindowRound a b) rfl hm

/-- **Line 4b in the hinted carrier.** -/
theorem masterHint_line4b_match (h3 : masterHintRoute p = 3)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatch (masterAdmittedRound a b (master4bOps e f u v)) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) ((master4bOps e f u v).width (p.1, some p.2)) 0
      ((master4bOps e f u v).init (p.1, some p.2)) T) :
    LoopMatch (masterAdmittedRound a b (masterHintOps e f u v G4 G5 d4 d5))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterHintOps e f u v G4 G5 d4 d5).width (p.1, some p.2)) 0
      ((masterHintOps e f u v G4 G5 d4 d5).init (p.1, some p.2)) T :=
  masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
    masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
      masterPairIte_start_pos a b (masterRouteAt_true h3) hm

/-- **Lines 4c–4d in the hinted carrier**: whatever the parameter carrier matches. -/
theorem masterHint_line4cd_match (h4 : masterHintRoute p = 4)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatch (masterAdmittedRound a b G4) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) (G4.width (p.1, some p.2)) 0 (G4.init (p.1, some p.2)) T) :
    LoopMatch (masterAdmittedRound a b (masterHintOps e f u v G4 G5 d4 d5))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterHintOps e f u v G4 G5 d4 d5).width (p.1, some p.2)) 0
      ((masterHintOps e f u v G4 G5 d4 d5).init (p.1, some p.2)) T :=
  masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
    masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
      masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
        masterPairIte_start_pos a b (masterRouteAt_true h4) hm

/-- **Lines 5–7 in the hinted carrier**: whatever the parameter carrier matches. -/
theorem masterHint_line57_match (h5 : masterHintRoute p = 5)
    {T : SIReduction (Fin n) ℕ (Set (Perm (Fin n)))}
    (hm : LoopMatch (masterAdmittedRound a b G5) (fun J => decWinSI n J.1)
      (decCoset n) (p.1, some p.2) (G5.width (p.1, some p.2)) 0 (G5.init (p.1, some p.2)) T) :
    LoopMatch (masterAdmittedRound a b (masterHintOps e f u v G4 G5 d4 d5))
      (fun J => decWinSI n J.1) (decCoset n) (p.1, some p.2)
      ((masterHintOps e f u v G4 G5 d4 d5).width (p.1, some p.2)) 0
      ((masterHintOps e f u v G4 G5 d4 d5).init (p.1, some p.2)) T :=
  masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
    masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
      masterPairIte_start_neg a b (masterRouteAt_false (by omega)) <|
        masterPairIte_start_neg a b (masterRouteAt_false (by omega)) hm
end HintMatch
end Algo
