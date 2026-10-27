import Workspace.Algo.TopMasterDescentEnum
import Workspace.Algo.TopMasterHintProgress

/-! # Exact raw line-2 matching on the full domain
The computed representative order supplies the live image enumeration.
The retained labels turn it into the actual block-action enumeration.
The kernel scan supplies the orbit order and the strict call decrease.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

section Full
variable {n m t : ℕ} {p : MasterDescInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    {φ : decGroup n p.1.2.1 →* Perm (Fin m)}
    (hp : RawAction.WF n m (masterDescAction p) φ)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hid : decPerm n p.1.2.2.1 = 1) (hfull : p.1.1 = rawOne p.1.2.2.2.1)
    {B : Set (Set (Fin n))}
    (hs : IsInvariantPartitionOn (decGroup n p.1.2.1) Set.univ B)
    (L : MasterHintBlockLink (t := t) hs.permutes φ)
    (ht : 1 ≤ t) (hm : t < m) (hB : ∃ U ∈ B, ∃ V ∈ B, U ≠ V)

 include hp hfull hs L ht hm hB in
 theorem masterDescFull_multiple :
    1 < (winOrbits (topKernel (masterDescAction p), p.1.1)).length := by
  by_contra h
  apply L.intransitive ht hm hs hB
  obtain ⟨U, hU, _, _, _⟩ := hB
  obtain ⟨u, _⟩ := hs.nonempty U hU
  refine ⟨u, Set.eq_univ_iff_forall.mpr (fun v => ?_)⟩
  have hn : p.1.2.2.2.1.length = n := hp.1
  have hlt : ∀ k ∈ p.1.1, k < n := by simpa [hfull, rawOne, hn]
  have hmem (v : Fin n) : v.val ∈ p.1.1 := by simp [hfull, rawOne, hn]
  have h1 : (winOrbits (topKernel (masterDescAction p), p.1.1)).length ≤ 1 := by omega
  obtain ⟨g, hguv⟩ := masterWinOrbit_pair
    (wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1) hlt h1 u v (hmem u) (hmem v)
  exact ⟨⟨g.val, (masterDescKernel_spec hp).le g.property⟩, hguv⟩

 include hx hy hp hg hid hfull hs L ht hm hB in
 theorem masterDescFull_block_match (a b : ℕ) :
    let F := masterDescOpenOps 3 masterHintDescSelect
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some (p.2, t)) (F.width (p.1, some (p.2, t))) 0 (F.init (p.1, some (p.2, t)))
      (cosetLine2ReductionWith (blockHom _ _ hs.permutes).rangeRestrict
        (decWinSI n p.1).x (decWinSI n p.1).y
        (L.line2Enum ht hm (masterDescLine2Enum hp hg hid hfull))) := by
  rw [L.line2Reduction_imageEquiv ht hm, masterDescLine2_tree hp hg hid hfull]
  dsimp only
  have hnd : p.1.1.Nodup := by rw [hfull]; exact List.nodup_range
  have hlt : ∀ k ∈ p.1.1, k < n := by simpa [hfull, rawOne, hx.1]
  have hΔ : winSet n p.1.1 = Set.univ := by ext v; simp [winSet, hfull, rawOne, hx.1]
  have hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1) := hΔ.symm ▸ isInvariant_univ _
  have h2 := masterDescFull_multiple hp hfull hs L ht hm hB
  have hh := masterDescStrongTree_hull hp hg hlt hinv
  have hloop := masterDescStrongTree_loop hx.1 (by exact Nat.zero_lt_of_lt h2) hh
  apply masterAdmittedRound_descent_match a b hx.1 rfl
    (by change p.1.1.length ≤ p.1.2.2.2.1.length; simp [hfull, rawOne])
    id rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl) hloop
  intro J hJ
  exact ⟨masterDescStrongTree_letters ((masterStrWF_iff hx.1).mp hx)
    ((masterStrWF_iff hy.1).mp hy) J hJ,
    masterDescStrongTree_progress hp hlt hinv hnd h2 J hJ,
    _, masterDescStrongTree_coset hp hlt J hJ⟩
end Full
end Algo
