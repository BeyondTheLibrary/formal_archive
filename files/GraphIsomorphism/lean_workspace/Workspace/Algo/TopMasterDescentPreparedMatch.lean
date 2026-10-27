import Workspace.Algo.TopMasterDescentPrepared

/-! # The prepared ambient descent executes live line 2
The input is computed from the parent candidate. Its representatives and
kernel windows are read from that input, and the return shift restores
the original coset after the lifted block-action branch has finished.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical Pointwise

section Fold
variable {n m t : ℕ} {p : MasterDescInput}
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (h2 : 1 < (winOrbits (topKernel (masterDescAction p), p.1.1)).length)

include hp hinv hx hy hg hnd hlt h2 in
 theorem masterDescPreparedFold_match (a b : ℕ) :
    let F := masterDescOpenOps 3 masterDescPreparedSelect
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some (p.2, t)) (F.width (p.1, some (p.2, t))) 0 (F.init (p.1, some (p.2, t)))
      (masterDescStrongTree n 3 (masterDescPreparedInput p)) := by
  have hh := masterDescStrongTree_hull (p := masterDescPreparedInput p) hp hg hlt hinv
  have hloop := masterDescStrongTree_loop (p := masterDescPreparedInput p) (c := 3) hx.1
    (by exact Nat.zero_lt_of_lt h2) hh
  apply masterAdmittedRound_descent_match (P := masterDescLists 3 (masterDescPreparedInput p))
    (p := (p.1, some (p.2, t))) (F := masterDescOpenOps 3 masterDescPreparedSelect) a b hx.1 rfl
    (by change p.1.1.length ≤ p.1.2.2.2.1.length; rw [hx.1]; exact length_le_of_nodup_lt hnd hlt)
    id rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl) hloop
  intro J hJ
  have hstrings := masterChainPrepared_strings hx hy hnd hlt
  exact ⟨masterDescStrongTree_letters (p := masterDescPreparedInput p)
    ((masterStrWF_iff hx.1).mp hstrings.1)
    ((masterStrWF_iff hstrings.2.1).mp hstrings.2) J hJ,
    masterDescStrongTree_progress (p := masterDescPreparedInput p) hp hlt hinv hnd h2 J hJ,
    _, masterDescStrongTree_coset (p := masterDescPreparedInput p) hp hlt J hJ⟩
end Fold

section Window
variable {n m t : ℕ} {p : MasterDescInput}
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m))
    (hp : RawAction.WF n m (masterDescAction p) (φ.comp (restrictOnto hinv)))
    (hlt : ∀ u ∈ p.1.1, u < n)
    {B : Set (Set (winSet n p.1.1))}
    (hs : IsInvariantPartitionOn (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv) Set.univ B)
    (L : MasterHintBlockLink (t := t) hs.permutes φ)
    (ht : 1 ≤ t) (hm : t < m) (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V)
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hnd : p.1.1.Nodup)

noncomputable def masterDescPreparedEnum :=
  L.line2Enum ht hm (masterDescWindowLine2Enum (p := masterDescPreparedInput p)
    hinv φ hp hg (masterDescPrepared_id hx.1) hlt)

noncomputable def masterDescPreparedTree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
    (cosetLine2ReductionWith (blockHom _ _ hs.permutes).rangeRestrict
      (restrictStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1))
      (restrictStr (winSet n p.1.1) (masterGroupInstance n p.1).y)
      (masterDescPreparedEnum hinv φ hp hlt hs L ht hm hx hg))).bind
    (fun A => .done (decPerm n p.1.2.2.1 • A))

include hy hB hnd in
 theorem masterDescPrepared_match (a b : ℕ) :
    let F := masterDescPreparedOps 3
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some (p.2, t)) (F.width (p.1, some (p.2, t))) 0 (F.init (p.1, some (p.2, t)))
      (masterDescPreparedTree hinv φ hp hlt hs L ht hm hx hg) := by
  apply masterShiftOps_match a b _ hx.1
  unfold masterDescPreparedEnum
  rw [L.line2Reduction_imageEquiv ht hm]
  have htrace := masterDescWindow_trace (p := masterDescPreparedInput p)
    hinv φ hp hg (masterDescPrepared_id hx.1) hlt
    (restrictStr (winSet n p.1.1) (masterGroupInstance n p.1).y)
    (masterDescPrepared_target hx.1 hnd hlt)
  apply loopMatch_of_trace (T := masterDescStrongTree n 3 (masterDescPreparedInput p))
    ?_ htrace.1.symm htrace.2.symm
  have h2 := masterDescWindow_multiple (p := masterDescPreparedInput p)
    hinv φ hp hlt hs L ht hm hB
  exact masterDescPreparedFold_match hp hinv hx hy hg hnd hlt h2 a b

end Window
end Algo
