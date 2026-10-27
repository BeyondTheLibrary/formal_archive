import Workspace.Algo.TopMasterCameronCase
import Workspace.Algo.TopMasterDescentPreparedSpec

/-! # Line 1, step 5 on the RAM: the block Luks reduction
Section 11.3, step 5: the window group `G` is transitive, `ℬ` is a minimal
block system, and the action `Ḡ` of `G` on `ℬ` is small. The paper applies
the Luks reduction to the kernel of that action (Theorem 11.1.9). This is
`Babai.blockLuksCoset`: the line-2 reduction of the block action, on the
window and lifted to `Ω`.

The machine runs the descent carrier on the computed block action. Its index
scan has `|Ḡ|` entries, taken from the ground table of `n^{log₂ n + 2}` keys
(`masterDescFuel_eq_of_ground`). The route test of step 5 bounds `|Ḡ|` by
`line1Cost |Δ|` (`masterReduceRoute_block_cost`), so the scan is complete.
The block numbering of the computed minimal blocks is read as a labelling of
`ℬ` by one-element subsets, which is the link the line-2 matching uses.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

/-! ### The carrier at a node without hint -/

/-- The input of step 5 at a raw node: the node in its group frame, with the
computed block action. -/
def masterBlockSelect (P : RawMasterSI) : MasterDescInput :=
  masterDescPreparedInput (masterWindowBlockInput P.1)

theorem polyFun_masterBlockSelect : PolyFun masterBlockSelect :=
  (polyFun_fst.comp polyFun_masterWindowBlockInput).comp polyFun_masterDescPreparedInput

theorem masterBlockSelect_source (P : RawMasterSI) :
    (masterBlockSelect P).1.2.2.2.1 = P.1.2.2.2.1 := rfl

/-- The step-5 carrier: the descent fold on the block action, then the shift
back to the node's candidate coset. -/
def masterBlockOps : MasterOps AggnRecomputeState :=
  masterShiftOps (masterDescOpenOps 3 masterBlockSelect)

/-- The local cost data of a shifted descent carrier on any polynomial
selector that keeps the source, uniform in the degree. -/
theorem masterShiftDescOpen_cost (a b : ℕ) (f : RawMasterSI → MasterDescInput)
    (hfp : PolyFun f) (hsource : ∀ P, (f P).1.2.2.2.1 = P.1.2.2.2.1) :
    Nonempty (MasterOpsCost a b (masterShiftOps (masterDescOpenOps 3 f))) := by
  obtain ⟨B, hB, hmB, hbound⟩ := masterDescOpen_uniform_bounds a b 3 f hfp hsource
  have hf : QuasiFun (masterDescOpenOps 3 f).finish :=
    (((polyFun_fst.comp hfp).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenFinish 3))
  refine ⟨⟨B, B, hB, hmB, hB,
    (hfp.comp_quasiFun (quasiFun_masterDescOpenWidth 3)),
    (((polyFun_fst.comp hfp).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenChild 3)),
    (hfp.comp_quasiFun (quasiFun_masterDescOpenInit 3)),
    (((polyFun_fst.comp hfp).pair polyFun_snd).comp_quasiFun (quasiFun_masterDescOpenCombine 3)),
    (quasiFun_masterShiftFinish hf),
    (fun p hp => (hbound p hp).1),
    (fun p j s A hp _ => (hbound p hp).2.1 j s A), ?_,
    (fun p hp => (hbound p hp).2.2)⟩⟩
  intro p s _
  exact (masterShiftOps_finish_size _ p s).trans (by unfold masterInputCap; omega)

/-- A shifted descent carrier on any polynomial selector that keeps the
source has one raw carrier at all ambient degrees. -/
theorem masterShiftDescOpen_runCostQ (a b : ℕ) (f : RawMasterSI → MasterDescInput)
    (hfp : PolyFun f) (hsource : ∀ P, (f P).1.2.2.2.1 = P.1.2.2.2.1) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b (masterShiftOps (masterDescOpenOps 3 f)))) :=
  (masterShiftDescOpen_cost a b f hfp hsource).map MasterOpsCost.runCostQ

/-- The local cost data of the step-5 carrier, uniform in the degree. -/
theorem masterBlock_cost (a b : ℕ) : Nonempty (MasterOpsCost a b masterBlockOps) :=
  masterShiftDescOpen_cost a b masterBlockSelect polyFun_masterBlockSelect
    masterBlockSelect_source

/-- The step-5 carrier has one raw carrier at all ambient degrees. -/
theorem masterBlock_runCostQ (a b : ℕ) :
    Nonempty (Round.RunCostQ (masterAdmittedRound a b masterBlockOps)) :=
  masterShiftDescOpen_runCostQ a b masterBlockSelect polyFun_masterBlockSelect
    masterBlockSelect_source

/-! ### Matching the fold and the window branch at a node without hint -/

section Fold
variable {n m : ℕ} {p : MasterDescInput}
    (f : RawMasterSI → MasterDescInput) (hsel : f (p.1, none) = masterDescPreparedInput p)
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (h2 : 1 < (winOrbits (topKernel (masterDescAction p), p.1.1)).length)

include hsel hp hinv hx hy hg hnd hlt h2 in
/-- The unshifted step-5 fold at the node `(p.1, none)` runs the strong descent
tree of the prepared input. -/
theorem masterDescOpenFold_match_none (a b : ℕ) :
    LoopMatch (masterAdmittedRound a b (masterDescOpenOps 3 f))
      (fun J => decWinSI n J.1) (decCoset n)
      (p.1, none) ((masterDescOpenOps 3 f).width (p.1, none)) 0
      ((masterDescOpenOps 3 f).init (p.1, none))
      (masterDescStrongTree n 3 (masterDescPreparedInput p)) := by
  have hh := masterDescStrongTree_hull (p := masterDescPreparedInput p) hp hg hlt hinv
  have hloop := masterDescStrongTree_loop (p := masterDescPreparedInput p) (c := 3) hx.1
    (by exact Nat.zero_lt_of_lt h2) hh
  apply masterAdmittedRound_descent_match (P := masterDescLists 3 (masterDescPreparedInput p))
    (p := (p.1, none)) (F := masterDescOpenOps 3 f) a b hx.1 rfl
    (by change p.1.1.length ≤ p.1.2.2.2.1.length; rw [hx.1]; exact length_le_of_nodup_lt hnd hlt)
    id
    (by show masterDescOpenWidth 3 (f (p.1, none)) = _; rw [hsel]; rfl)
    (fun j s => by
      show masterDescOpenChild 3 (f (p.1, none), j, s) = _; rw [hsel]; rfl)
    (by show masterDescOpenInit 3 (f (p.1, none)) = _; rw [hsel]; rfl)
    (fun j s A => by
      show masterDescOpenCombine 3 (f (p.1, none), j, s, A) = _; rw [hsel]; rfl)
    (fun s => by
      show masterDescOpenFinish 3 (f (p.1, none), s) = _; rw [hsel]; rfl)
    hloop
  intro J hJ
  have hstrings := masterChainPrepared_strings hx hy hnd hlt
  exact ⟨masterDescStrongTree_letters (p := masterDescPreparedInput p)
    ((masterStrWF_iff hx.1).mp hstrings.1)
    ((masterStrWF_iff hstrings.2.1).mp hstrings.2) J hJ,
    masterDescStrongTree_progress (p := masterDescPreparedInput p) hp hlt hinv hnd h2 J hJ,
    _, masterDescStrongTree_coset (p := masterDescPreparedInput p) hp hlt J hJ⟩
end Fold

section Window
variable {n m : ℕ} {p : MasterDescInput}
    (f : RawMasterSI → MasterDescInput) (hsel : f (p.1, none) = masterDescPreparedInput p)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m))
    (hp : RawAction.WF n m (masterDescAction p) (φ.comp (restrictOnto hinv)))
    (hlt : ∀ u ∈ p.1.1, u < n)
    {B : Set (Set (winSet n p.1.1))}
    (hs : IsInvariantPartitionOn (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv) Set.univ B)
    (L : MasterHintBlockLink (t := 1) hs.permutes φ)
    (hm : 1 < m) (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V)
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hnd : p.1.1.Nodup)

include hsel hy hB hnd in
/-- **Section 11.3, step 5, at a node without hint.** The step-5 carrier runs
the window line-2 reduction of the block action, lifted to `Ω`, and shifts the
answer back to the node's candidate coset. -/
theorem masterShiftDescOpen_match_none (a b : ℕ) :
    LoopMatch (masterAdmittedRound a b (masterShiftOps (masterDescOpenOps 3 f))) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, none) ((masterShiftOps (masterDescOpenOps 3 f)).width (p.1, none)) 0 ((masterShiftOps (masterDescOpenOps 3 f)).init (p.1, none))
      (masterDescPreparedTree hinv φ hp hlt hs L le_rfl hm hx hg) := by
  apply masterShiftOps_match a b _ hx.1
  unfold masterDescPreparedEnum
  rw [L.line2Reduction_imageEquiv le_rfl hm]
  have htrace := masterDescWindow_trace (p := masterDescPreparedInput p)
    hinv φ hp hg (masterDescPrepared_id hx.1) hlt
    (restrictStr (winSet n p.1.1) (masterGroupInstance n p.1).y)
    (masterDescPrepared_target hx.1 hnd hlt)
  apply loopMatch_of_trace (T := masterDescStrongTree n 3 (masterDescPreparedInput p))
    ?_ htrace.1.symm htrace.2.symm
  have h2 := masterDescWindow_multiple (p := masterDescPreparedInput p)
    hinv φ hp hlt hs L le_rfl hm hB
  exact masterDescOpenFold_match_none f hsel hp hinv hx hy hg hnd hlt h2 a b
include hy hB hnd in
/-- **Section 11.3, step 5, at a node without hint.** The step-5 carrier runs
the window line-2 reduction of the block action, lifted to `Ω`, and shifts the
answer back to the node's candidate coset. -/
theorem masterBlock_match (hsel : masterBlockSelect (p.1, none) = masterDescPreparedInput p)
    (a b : ℕ) :
    LoopMatch (masterAdmittedRound a b masterBlockOps) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, none) (masterBlockOps.width (p.1, none)) 0 (masterBlockOps.init (p.1, none))
      (masterDescPreparedTree hinv φ hp hlt hs L le_rfl hm hx hg) :=
  masterShiftDescOpen_match_none masterBlockSelect hsel hinv φ hp hlt hs L hm hB hx hy hg hnd a b
end Window
end Algo
