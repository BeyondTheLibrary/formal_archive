import Workspace.Algo.TopMasterDescentPreparedMatch

/-! # Correctness and paper bounds of prepared line 2 -/
set_option maxHeartbeats 1200000
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical Pointwise

section Window
variable {n m t : ℕ} {p : MasterDescInput}
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    (φ : restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv →* Perm (Fin m))
    (hp : RawAction.WF n m (masterDescAction p) (φ.comp (restrictOnto hinv)))
    (hlt : ∀ u ∈ p.1.1, u < n)
    {B : Set (Set (winSet n p.1.1))}
    (hs : IsInvariantPartitionOn (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv) Set.univ B)
    (L : MasterHintBlockLink (t := t) hs.permutes φ)
    (ht : 1 ≤ t) (hm : t < m)
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))

 theorem masterDescPreparedTree_run :
    (masterDescPreparedTree hinv φ hp hlt hs L ht hm hx hg).run = (decWinSI n p.1).answer := by
  rw [masterDescPreparedTree, SIReduction.run_bind, SIReduction.run_done,
    run_liftWindow hinv (decStrN n p.1.2.2.2.1) (masterGroupInstance n p.1).y _
      (calls_cosetLine2ReductionWith_K _ _ _ _) (run_cosetLine2ReductionWith _ _ _ _)]
  exact masterGroupInstance_answer hx.1

 theorem masterDescPreparedTree_calls (hnd : p.1.1.Nodup) :
    (masterDescPreparedTree hinv φ hp hlt hs L ht hm hx hg).calls.length ≤
      Nat.factorial m * p.1.1.length := by
  simp only [masterDescPreparedTree, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, masterDescPreparedEnum]
  rw [L.line2Reduction_imageEquiv ht hm]
  have htrace := masterDescWindow_trace (p := masterDescPreparedInput p)
    hinv φ hp hg (masterDescPrepared_id hx.1) hlt
    (restrictStr (winSet n p.1.1) (masterGroupInstance n p.1).y)
    (masterDescPrepared_target hx.1 hnd hlt)
  apply (congrArg List.length htrace.1).trans_le
  have hb := (masterDescStrongTree_calls_le (p := masterDescPreparedInput p) hp hg).trans
    (Nat.mul_le_mul_right _ (masterDescWidth_le_factorial (p := masterDescPreparedInput p) hp))
  change (masterDescStrongTree n 3 (masterDescPreparedInput p)).calls.length ≤
    Nat.factorial p.2.1.length * p.1.1.length at hb
  have hlen : p.2.1.length = m := hp.2.1
  rw [hlen] at hb
  exact hb

 theorem masterDescPreparedTree_half (hnd : p.1.1.Nodup)
    (hG : IsTransitive (restrictTo (decGroup n p.1.2.1) (winSet n p.1.1) hinv))
    (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V) :
    ∀ J ∈ (masterDescPreparedTree hinv φ hp hlt hs L ht hm hx hg).calls,
      2 * J.windowSize ≤ p.1.1.length := by
  intro J hJ
  simp only [masterDescPreparedTree, SIReduction.calls_bind, SIReduction.calls_done,
    List.append_nil, masterDescPreparedEnum] at hJ
  rw [L.line2Reduction_imageEquiv ht hm] at hJ
  obtain ⟨J', hJ', hsize⟩ := calls_liftWindow_windowSize hinv (decStrN n p.1.2.2.2.1) _
    (calls_cosetLine2ReductionWith_K _ _ _ _) J hJ
  have hw := calls_cosetLine2ReductionWith_window _ _ _ _ J' hJ'
  obtain ⟨u, hu⟩ := mem_orbitList hw
  have hker : kerSubgroup φ.rangeRestrict = kerSubgroup φ := by
    ext g
    simp only [mem_kerSubgroup]
    constructor
    · rintro ⟨hg, he⟩
      exact ⟨hg, congrArg Subtype.val he⟩
    · rintro ⟨hg, he⟩
      exact ⟨hg, Subtype.ext he⟩
  have hhalf := L.orbit_half ht hm hG hs hB u
  have hcard : Fintype.card (winSet n p.1.1) = p.1.1.length := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ncard_winSet p.1.1 hnd hlt]
  rw [hsize, SIInstance.windowSize, hu, hker]
  exact hcard ▸ hhalf
end Window
end Algo
