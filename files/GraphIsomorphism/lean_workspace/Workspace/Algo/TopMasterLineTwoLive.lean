import Workspace.Algo.TopMasterHintWindowLink

/-! # The actual line-2 route in the uniform master carrier
The branch reads the inherited image rows, computes the candidate's group
frame, enumerates the image and its kernel orbits, and restores the coset.
Its supplied block labels justify both exact matching and halving.
-/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

section Hint
variable {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hw : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m))
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 φ)
    {B : Set (Set (Fin p.1.1.length))}
    (hs : IsSystemOfImprimitivity (decGroup p.1.1.length (masterHintTop p).1.1.2) Set.univ B)
    (L : MasterHintBlockLink (t := p.2.2) hs.permutes φ)
    (ht : 1 ≤ p.2.2) (hm : p.2.2 < m) (hr : masterHintRoute p = 1)

include hx hw hnd hlt hinv hp hr in
/-- The route test of line 2 bounds the number of blocks, so the scan covers the image. -/
theorem masterHintDescInput_fuel :
    masterDescFuel 3 (masterHintDescInput p) = List.range (masterDescWidth (masterHintDescInput p)) :=
  masterDescFuel_eq (masterHintDescInput_guard hx.1 hnd hlt hr)
    (masterDescWidth_le_factorial (masterHintDescInput_wf hx.1 hw hnd hlt hinv hp))

noncomputable def masterHintLine2Tree : SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  masterDescPreparedTree (p := masterHintDescInput p) hinv
    (masterHintWindowHom hw hnd hlt hinv φ) (masterHintWindowHom_wf hx.1 hw hnd hlt hinv φ hp)
    hlt (masterHintWindowSystem hw hnd hlt hinv hs).isInvariantPartitionOn
    (masterHintWindowLink hw hnd hlt hinv φ hs L) ht hm hx
    (masterHintDescInput_fuel hx hw hnd hlt hinv φ hp hr)

include hy in
 theorem masterHintLine2_match (a b : ℕ) (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) :
    let F := masterDescPreparedOps 3
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some p.2) (F.width (p.1, some p.2)) 0 (F.init (p.1, some p.2))
      (masterHintLine2Tree hx hw hnd hlt hinv φ hp hs L ht hm hr) :=
  masterDescPrepared_match (p := masterHintDescInput p) hinv
    (masterHintWindowHom hw hnd hlt hinv φ) (masterHintWindowHom_wf hx.1 hw hnd hlt hinv φ hp)
    hlt (masterHintWindowSystem hw hnd hlt hinv hs).isInvariantPartitionOn
    (masterHintWindowLink hw hnd hlt hinv φ hs L) ht hm
    (masterHintWindow_two hnd hlt hB) hx hy (masterHintDescInput_fuel hx hw hnd hlt hinv φ hp hr) hnd a b

 theorem masterHintLine2_run :
    (masterHintLine2Tree hx hw hnd hlt hinv φ hp hs L ht hm hr).run = (decWinSI n p.1).answer :=
  masterDescPreparedTree_run (p := masterHintDescInput p) hinv
    (masterHintWindowHom hw hnd hlt hinv φ) (masterHintWindowHom_wf hx.1 hw hnd hlt hinv φ hp)
    hlt (masterHintWindowSystem hw hnd hlt hinv hs).isInvariantPartitionOn
    (masterHintWindowLink hw hnd hlt hinv φ hs L) ht hm hx
    (masterHintDescInput_fuel hx hw hnd hlt hinv φ hp hr)

 theorem masterHintLine2_calls :
    (masterHintLine2Tree hx hw hnd hlt hinv φ hp hs L ht hm hr).calls.length ≤
      Nat.factorial (ellOf p.1.1.length) * p.1.1.length := by
  have h := masterDescPreparedTree_calls (p := masterHintDescInput p) hinv
    (masterHintWindowHom hw hnd hlt hinv φ) (masterHintWindowHom_wf hx.1 hw hnd hlt hinv φ hp)
    hlt (masterHintWindowSystem hw hnd hlt hinv hs).isInvariantPartitionOn
    (masterHintWindowLink hw hnd hlt hinv φ hs L) ht hm hx
    (masterHintDescInput_fuel hx hw hnd hlt hinv φ hp hr) hnd
  have he : p.2.1.1.length = m := hp.2.1
  have hle : m ≤ ellOf p.1.1.length := he ▸ ((masterHintRoute_line2 p).mp hr)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.factorial_le hle))

 theorem masterHintLine2_half
    (hG : IsTransitive (decGroup p.1.1.length (masterHintTop p).1.1.2))
    (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) :
    ∀ J ∈ (masterHintLine2Tree hx hw hnd hlt hinv φ hp hs L ht hm hr).calls,
      2 * J.windowSize ≤ p.1.1.length :=
  masterDescPreparedTree_half (p := masterHintDescInput p) hinv
    (masterHintWindowHom hw hnd hlt hinv φ) (masterHintWindowHom_wf hx.1 hw hnd hlt hinv φ hp)
    hlt (masterHintWindowSystem hw hnd hlt hinv hs).isInvariantPartitionOn
    (masterHintWindowLink hw hnd hlt hinv φ hs L) ht hm hx
    (masterHintDescInput_fuel hx hw hnd hlt hinv φ hp hr) hnd
    (masterHintWindow_transitive hw hnd hlt hinv hG) (masterHintWindow_two hnd hlt hB)
end Hint
end Algo
