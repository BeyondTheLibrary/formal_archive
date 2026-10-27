/-
Formalization of

  László Babai, *Graph Isomorphism in Quasipolynomial Time*,
  Version 2.5 (2 November 2018).

The algorithmic layer: Sec. 15, lines 5–7 as one round, with outcome (2a) of Theorem 13.2.1
(the giant branch, Cor. 12.0.10) run inside the round.
-/
import Workspace.Algo.AggNodeLine57Round
import Workspace.Algo.AggNodeLine57GiantCalls
import Workspace.Algo.TopFourAlignmentRAM

/-!
# Sec. 15, lines 5–7, with the giant branch (2a)

`Algo.aggnL57Round` runs, after the two phases of Procedure AggregateCertificates, Procedure
Align over the versions the dispatch of Theorem 13.2.1 returns (`Algo.aggnContinuation`).  At
outcome (2a) (tag `2`) the dispatch returns no versions, so that round makes no further call.
The paper's outcome (2a) is instead *"reduce the determination of `Iso_G(x,y)` to `n^{O(1)}`
instances of size `≤ 2n/3`"* by Cor. 12.0.10, the same step as line 4b; on the Master side it
is `Babai.line5Case2aFunCoset`: the two phases, then `Babai.line4bBranchCoset`.

`Algo.aggnL57GRound` extends `Algo.aggnL57Round` by that step.  It is `Algo.aggnL57Round`
everywhere except after the two phases at tag `2`, where it runs the round of Cor. 12.0.10
with the supplied alignment (`Algo.top4aRound`) on the node `Algo.top4AggregateEnter`, which
reads the two large orbits off the completed certificate stores.  The extra part of the state
is the number of calls this stretch has made and the state of `Algo.top4aRound`.  Its calls,
window instances of `Fin n`, become children of the carrier through the same checked window
normalization as the other calls (`Algo.avEmb`), and its answer is the answer of the round.

The branch is entered only when the node of Cor. 12.0.10 passes the well-formedness test of
`Algo.top4aRound` (`Algo.top4aCheck` with the parameters `u v e f`); on the inputs of the
Master side the test holds (`Workspace/Algo/AggNodeLine57GiantMatch.lean`).  The test keeps
the cost analysis to the nodes on which `Algo.top4aRound` has its bounds.
-/
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000
namespace Algo
open RAM RAM.Targets Babai Equiv

/-- The state: the state of `Algo.aggnL57Round` and, once the giant branch has made a call,
the number of its calls so far and the state of `Algo.top4aRound`. -/
abbrev AggnL57GState := AggnL57State × Option (ℕ × Top4State)

/-- The answer routine for window nodes of `Algo.top4aRound`; the node of the giant branch is
not a window node, so it is never used. -/
def l57gSolve : RawWinSI → RawCoset := fun _ => none

/-- The node of Cor. 12.0.10 at outcome (2a), read off the stores through the caps of the
aggregate carrier. -/
def aggnL57GNode (c dc dp : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : Top4aNode :=
  top4AggregateEnter (z.1, aggnAggregatePack c dc dp z.1 z.2)

/-- The width of a node of `Algo.top4aRound`. -/
def l57gW4 (I : Top4aNode) : ℕ := if top4aGate I then I.1.2.elim (top4Width I.1.1) (fun _ => 0) else 0

theorem l57gW4_eq (u v e f : ℕ) (solve : RawWinSI → RawCoset) (I : Top4aNode) :
    (top4aRound u v e f solve).width I = l57gW4 I := rfl

/-- §15, line 5: **the test of outcome (2a)** after the two phases: the tag of the dispatch is
`2`, and the node of Cor. 12.0.10 is well formed. -/
def aggnL57GOn (c b t d dc dp u v e f : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : Bool :=
  decide ((aggnL57Cont c b t d (z.1, aggnAggregatePack c dc dp z.1 z.2)).1 = 2) &&
    top4aCheck u v e f (aggnL57GNode c dc dp z)

/-- The giant branch is running: the node is `(C, none)`, the two phases are over, and the
test of outcome (2a) holds. -/
def aggnL57GActive (c b t d dc dp u v e f : ℕ) (z : AggnPhaseNode × ℕ × AggnL57GState) : Bool :=
  z.1.2.isNone && (aggnAggregateChild c (z.1, z.2.1, z.2.2.1.1)).isNone &&
    aggnL57GOn c b t d dc dp u v e f (z.1.1, z.2.2.1.1)

/-- The position and state of `Algo.top4aRound` in the giant branch. -/
def aggnL57GPos (c dc dp : ℕ) (z : AggnPhaseCtx × AggnL57GState) : ℕ × Top4State :=
  z.2.2.getD (0, top4aInit (aggnL57GNode c dc dp (z.1, z.2.1.1)))

/-- The child of the giant branch: the child of `Algo.top4aRound`, as a window child of the
carrier. -/
def aggnL57GTopChild (c dc dp e f : ℕ) (z : AggnPhaseNode × ℕ × AggnL57GState) :
    Option AggnPhaseNode :=
  if z.2.1 < aggnAggregateWidth c z.1.1 + l57gW4 (aggnL57GNode c dc dp (z.1.1, z.2.2.1.1)) then
    (top4aChild e f (aggnL57GNode c dc dp (z.1.1, z.2.2.1.1),
      (aggnL57GPos c dc dp (z.1.1, z.2.2)).1, (aggnL57GPos c dc dp (z.1.1, z.2.2)).2)).bind
      (fun J => J.1.2.map (fun W => avEmb (z.1.1, W)))
  else none

/-- One step of the giant branch after the answer of a call. The stores are kept through the
caps of the carrier, and the count through the width of the node. -/
def aggnL57GTopCombine (c dc dp : ℕ) (z : AggnPhaseNode × ℕ × AggnL57GState × RawCoset) :
    AggnL57GState :=
  ((aggnAggregatePack c dc dp z.1.1 z.2.2.1.1.1, none),
    some (min ((aggnL57GPos c dc dp (z.1.1, z.2.2.1)).1 + 1)
        (l57gW4 (aggnL57GNode c dc dp (z.1.1, z.2.2.1.1.1))),
      top4aCombine (aggnL57GNode c dc dp (z.1.1, z.2.2.1.1.1),
        (aggnL57GPos c dc dp (z.1.1, z.2.2.1)).1, (aggnL57GPos c dc dp (z.1.1, z.2.2.1)).2,
        z.2.2.2)))

/-- §15, lines 5–7 with outcome (2a): **the child**. -/
def aggnL57GChild (c b t d dc dp u v e f : ℕ) (z : AggnPhaseNode × ℕ × AggnL57GState) :
    Option AggnPhaseNode :=
  if aggnL57GActive c b t d dc dp u v e f z then aggnL57GTopChild c dc dp e f z
  else aggnL57Child c b t d dc dp (z.1, z.2.1, z.2.2.1)

/-- §15, lines 5–7 with outcome (2a): **the combine**. -/
def aggnL57GCombine (c b t d dc dp u v e f : ℕ) (z : AggnPhaseNode × ℕ × AggnL57GState × RawCoset) :
    AggnL57GState :=
  if aggnL57GActive c b t d dc dp u v e f (z.1, z.2.1, z.2.2.1) then aggnL57GTopCombine c dc dp z
  else (aggnL57Combine c b t d dc dp (z.1, z.2.1, z.2.2.1.1, z.2.2.2), none)

/-- §15, lines 5–7 with outcome (2a): **the answer**, the answer of Cor. 12.0.10 in the giant
branch, and the answer of `Algo.aggnL57Round` otherwise. -/
def aggnL57GFinish (c b t d dc dp u v e f : ℕ) (z : AggnPhaseNode × AggnL57GState) : RawCoset :=
  if z.1.2.isNone && aggnL57GOn c b t d dc dp u v e f (z.1.1, z.2.1.1) then
    top4aFinish l57gSolve (aggnL57GNode c dc dp (z.1.1, z.2.1.1), (aggnL57GPos c dc dp (z.1.1, z.2)).2)
  else aggnL57Finish (z.1, z.2.1)

/-! ## The width of the giant branch -/

/-- The width the giant branch may use at a state. -/
def aggnL57GW (c b t d dc dp u v e f : ℕ) (z : AggnPhaseCtx × AggnAggregateState) : ℕ :=
  if aggnL57GOn c b t d dc dp u v e f z then l57gW4 (aggnL57GNode c dc dp z) else 0

/-- The width bound of `Algo.top4aRound` with the parameters `u v`. -/
def l57gW4Bound (u v n : ℕ) : ℕ :=
  (topcsContextCap u v n + 2) * topcsContextCap u v n + topcsContextCap u v n

theorem polyBound_l57gW4Bound (u v : ℕ) : PolyBound (l57gW4Bound u v) :=
  (((polyBound_topcsContextCap u v).add (polyBound_const 2)).mul
    (polyBound_topcsContextCap u v)).add (polyBound_topcsContextCap u v)

theorem mono_l57gW4Bound (u v : ℕ) : Monotone (l57gW4Bound u v) := by
  intro a b hab
  have h := mono_topcsContextCap u v hab
  unfold l57gW4Bound
  have := Nat.mul_le_mul (Nat.add_le_add_right h 2) h
  omega

/-- The input of Cor. 12.0.10 at outcome (2a) is polynomially small in the context: the
action and the two strings are read off it, and the two large orbits are lists of distinct
names of `Γ`. -/
theorem top4AggregateInput_size_bdd : ∃ K : ℕ → ℕ, PolyBound K ∧ Monotone K ∧
    ∀ (C : AggnPhaseCtx) (s : AggnAggregateState),
      Enc.size (top4AggregateInput (C, s)) ≤ K (Enc.size C) := by
  have hT : PolyFun (fun C : AggnPhaseCtx => (C.1, C.2.1, C.2.2.1)) :=
    polyFun_fst.pair ((polyFun_snd.comp polyFun_fst).pair
      ((polyFun_snd.comp polyFun_snd).comp polyFun_fst))
  obtain ⟨S, hS, hSm, hSs⟩ := hT.size.exists_polyBound
  let M : ℕ → ℕ := fun N => 1 + N * (2 * (N + 2) + 1)
  have hM : PolyBound M := (polyBound_const 1).add (polyBound_id.mul
    (((polyBound_const 2).mul (polyBound_id.add (polyBound_const 2))).add (polyBound_const 1)))
  have hMm : Monotone M := by
    intro a b hab
    have := Nat.mul_le_mul hab (show 2 * (a + 2) + 1 ≤ 2 * (b + 2) + 1 by omega)
    dsimp only [M]
    omega
  refine ⟨fun N => 4 * S N + 6 * M N, ((polyBound_const 4).mul hS).add
    ((polyBound_const 6).mul hM), fun a b hab => ?_, fun C s => ?_⟩
  · have := hSm a b hab
    have := hMm hab
    show 4 * S a + 6 * M a ≤ 4 * S b + 6 * M b
    omega
  · have hL : C.1.2.1.length ≤ Enc.size C :=
      (length_le_size _).trans ((size_fst_le' _).trans ((size_snd_le' _).trans (size_fst_le' _)))
    have hmaj : ∀ b, Enc.size (aggnAggregateMajority ((C, s), b)) ≤ M (Enc.size C) := by
      intro b
      have hlt : ∀ u ∈ aggnAggregateMajority ((C, s), b), u < C.1.2.1.length :=
        aggnLargeOrbitPoints_lt rfl
      have hlen : (aggnAggregateMajority ((C, s), b)).length ≤ C.1.2.1.length :=
        length_le_of_nodup_lt (aggnLargeOrbitPoints_nodup _) hlt
      exact (size_natList_le hlen hlt).trans (hMm hL)
    have h1 := Combine.size_pair_le ((C.1, C.2.1, C.2.2.1), aggnAggregateMajority ((C, s), false))
      (aggnAggregateMajority ((C, s), true))
    have h2 := Combine.size_pair_le (C.1, C.2.1, C.2.2.1) (aggnAggregateMajority ((C, s), false))
    have h3 := hSs C
    have h4 := hmaj false
    have h5 := hmaj true
    show Enc.size ((((C.1, C.2.1, C.2.2.1), aggnAggregateMajority ((C, s), false)),
      aggnAggregateMajority ((C, s), true)) : Top4AutoInput) ≤
        4 * S (Enc.size C) + 6 * M (Enc.size C)
    omega

/-- **The width of the giant branch is bounded by a polynomial in the size of the context.** -/
theorem aggnL57GW_bdd (c b t d dc dp u v e f : ℕ) : ∃ K : ℕ → ℕ, PolyBound K ∧ Monotone K ∧
    ∀ C s, aggnL57GW c b t d dc dp u v e f (C, s) ≤ K (Enc.size C) := by
  obtain ⟨K0, hK0, hK0m, hK0s⟩ := top4AggregateInput_size_bdd
  obtain ⟨F, hF, hFm, hFs⟩ := polyFun_top4AutoEnter.size.exists_polyBound
  refine ⟨fun N => l57gW4Bound u v (F (K0 N)), (polyBound_l57gW4Bound u v).comp (hF.comp hK0),
    fun a b hab => mono_l57gW4Bound u v (hFm _ _ (hK0m hab)), fun C s => ?_⟩
  unfold aggnL57GW
  split
  next hon =>
    set I := aggnL57GNode c dc dp (C, s) with hI
    have hwf : Top4aWF u v e f I := (top4aCheck_spec u v e f I).1 (by
      unfold aggnL57GOn at hon
      simp only [Bool.and_eq_true] at hon
      exact hon.2)
    have hw := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).width_le I hwf
    have hg := (top4aRunCostQ u v e f l57gSolve (quasiFun_const _)).ground_le I
    have hsz : Enc.size I ≤ F (K0 (Enc.size C)) :=
      (hFs _).trans (hFm _ _ (hK0s C _))
    change l57gW4 I ≤ l57gW4Bound u v (top4X I.1.1).length at hw
    change (top4X I.1.1).length ≤ Enc.size I at hg
    exact hw.trans (mono_l57gW4Bound u v (hg.trans hsz))
  next => exact Nat.zero_le _

/-- The width reserved for the giant branch: the largest width it may use at the node. It is
used only in the analysis. -/
noncomputable def aggnL57GCap (c b t d dc dp u v e f : ℕ) (C : AggnPhaseCtx) : ℕ :=
  sSup (Set.range fun s : AggnAggregateState => aggnL57GW c b t d dc dp u v e f (C, s))

theorem aggnL57GW_le_cap (c b t d dc dp u v e f : ℕ) (C : AggnPhaseCtx) (s : AggnAggregateState) :
    aggnL57GW c b t d dc dp u v e f (C, s) ≤ aggnL57GCap c b t d dc dp u v e f C := by
  obtain ⟨K, -, -, he⟩ := aggnL57GW_bdd c b t d dc dp u v e f
  exact le_csSup ⟨_, by rintro _ ⟨s', rfl⟩; exact he C s'⟩ ⟨s, rfl⟩

theorem aggnL57GCap_le (c b t d dc dp u v e f : ℕ) : ∃ K : ℕ → ℕ, PolyBound K ∧ Monotone K ∧
    ∀ C, aggnL57GCap c b t d dc dp u v e f C ≤ K (Enc.size C) := by
  obtain ⟨K, hK, hKm, he⟩ := aggnL57GW_bdd c b t d dc dp u v e f
  refine ⟨K, hK, hKm, fun C => csSup_le ⟨_, ⟨default, rfl⟩⟩ ?_⟩
  rintro _ ⟨s, rfl⟩
  exact he C s

/-! ## The children -/

theorem aggnL57GTopChild_some {c dc dp e f : ℕ} {z : AggnPhaseNode × ℕ × AggnL57GState}
    {J : AggnPhaseNode} (h : aggnL57GTopChild c dc dp e f z = some J) :
    ∃ W, J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  unfold aggnL57GTopChild at h
  split at h
  · obtain ⟨K, -, hK⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨W, -, rfl⟩ := Option.map_eq_some_iff.1 hK
    exact ⟨W, rfl⟩
  · simp at h

theorem aggnL57GChild_some {c b t d dc dp u v e f : ℕ} {z : AggnPhaseNode × ℕ × AggnL57GState}
    {J : AggnPhaseNode} (h : aggnL57GChild c b t d dc dp u v e f z = some J) :
    z.1.2 = none ∧ ∃ W, J = (z.1.1, some (aggnCheckedWindow (z.1.1.2.1, W))) := by
  unfold aggnL57GChild at h
  split at h
  next ha =>
    refine ⟨?_, aggnL57GTopChild_some h⟩
    unfold aggnL57GActive at ha
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at ha
    exact ha.1.1
  next => exact aggnL57Child_some h

/-- §15, lines 5–7 with outcome (2a): **the round.** It is `Algo.aggnL57Round` except in the
giant branch, whose calls are those of Cor. 12.0.10. -/
noncomputable def aggnL57GRound (c b t d dc dp u v e f : ℕ) :
    Round AggnPhaseNode AggnL57GState RawCoset where
  WF := fun I => AggnCheckedWF I.1.2.1.length I
  ground := fun I => I.1.2.1.length
  measure := fun I => I.2.elim 1 (fun _ => 0)
  width := fun I => I.2.elim (aggnAggregateWidth c I.1 + aggnL57Cap c b t d dc dp I.1 +
    aggnL57GCap c b t d dc dp u v e f I.1) (fun _ => 0)
  child := aggnL57GChild c b t d dc dp u v e f
  init := fun I => ((aggnAggregateInit c dc dp I, none), none)
  combine := aggnL57GCombine c b t d dc dp u v e f
  finish := aggnL57GFinish c b t d dc dp u v e f
  bot := none
  child_eq_none := by
    intro I j s hj
    unfold aggnL57GChild
    split
    next ha =>
      unfold aggnL57GActive at ha
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at ha
      obtain ⟨⟨ho, -⟩, hon⟩ := ha
      unfold aggnL57GTopChild
      have hcap := aggnL57GW_le_cap c b t d dc dp u v e f I.1 s.1.1
      unfold aggnL57GW at hcap
      rw [if_pos hon] at hcap
      rw [ho] at hj
      simp only [Option.elim_none] at hj
      rw [if_neg (show ¬ (j < aggnAggregateWidth c I.1 +
        l57gW4 (aggnL57GNode c dc dp (I.1, s.1.1))) by omega)]
    next =>
      refine (aggnL57Round c b t d dc dp).child_eq_none I j s.1 ?_
      show I.2.elim _ _ ≤ j
      cases ho : I.2 with
      | none =>
        rw [ho] at hj
        simp only [Option.elim_none] at hj ⊢
        omega
      | some W => simp
  child_wf := by
    intro I j s J hI hJ
    obtain ⟨_, W, rfl⟩ := aggnL57GChild_some hJ
    refine ⟨rfl, hI.2.1, ?_⟩
    intro W' hW'
    cases Option.some.inj hW'
    exact aggnCheckedWindow_wf _ _
  child_measure := by
    intro I j s J _ hJ
    obtain ⟨ho, W, rfl⟩ := aggnL57GChild_some hJ
    show (some _ : Option RawWinSI).elim 1 (fun _ => 0) < I.2.elim 1 (fun _ => 0)
    rw [ho]
    exact Nat.zero_lt_one
  child_ground := by
    intro I j s J _ hJ
    obtain ⟨_, W, rfl⟩ := aggnL57GChild_some hJ
    exact le_rfl

end Algo
