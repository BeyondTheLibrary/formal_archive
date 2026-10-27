import Workspace.Algo.TopMasterDescentWindowTrace

/-! # The admitted ambient fold matches the window block-action branch
The retained block labels prove progress. The representative and orbit
enumerations come from the raw routines, and their window transport
preserves the executed calls and result of the actual line-2 reduction.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv MulAction
open scoped Classical

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

 include hp hlt hs L ht hm hB in
 theorem masterDescWindow_multiple :
    1 < (winOrbits (topKernel (masterDescAction p), p.1.1)).length := by
  by_contra h
  apply L.intransitive ht hm hs hB
  obtain ⟨U, hU, _, _, _⟩ := hB
  obtain ⟨u, _⟩ := hs.nonempty U hU
  refine ⟨u, Set.eq_univ_iff_forall.mpr (fun v => ?_)⟩
  have h1 : (winOrbits (topKernel (masterDescAction p), p.1.1)).length ≤ 1 := by omega
  obtain ⟨g, hguv⟩ := masterWinOrbit_pair
    (wf_topKernel (p := (masterDescAction p, [], [], [])) hp.1) hlt h1 u.val v.val u.property v.property
  obtain ⟨hgG, hgφ⟩ := mem_kerSubgroup.mp ((masterDescKernel_spec hp).le g.property)
  let a := restrictOnto hinv ⟨g.val, hgG⟩
  exact ⟨⟨a.val, mem_kerSubgroup.mpr ⟨a.property, hgφ⟩⟩, Subtype.ext hguv⟩

 include hp hlt hs L ht hm hB in
 theorem masterDescWindow_block_match (a b : ℕ)
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hg : masterDescFuel 3 p = List.range (masterDescWidth p))
    (hid : decPerm n p.1.2.2.1 = 1) (hnd : p.1.1.Nodup)
    (y : winSet n p.1.1 → ℕ)
    (hyt : decStrN n p.1.2.2.2.2 = extendStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1) y) :
    let F := masterDescOpenOps 3 masterHintDescSelect
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some (p.2, t)) (F.width (p.1, some (p.2, t))) 0 (F.init (p.1, some (p.2, t)))
      (liftWindow (decGroup n p.1.2.1) (winSet n p.1.1) hinv (decStrN n p.1.2.2.2.1)
        (cosetLine2ReductionWith (blockHom _ _ hs.permutes).rangeRestrict
          (restrictStr (winSet n p.1.1) (decStrN n p.1.2.2.2.1)) y
          (L.line2Enum ht hm (masterDescWindowLine2Enum hinv φ hp hg hid hlt)))) := by
  rw [L.line2Reduction_imageEquiv ht hm]
  have htrace := masterDescWindow_trace hinv φ hp hg hid hlt y hyt
  dsimp only at htrace ⊢
  apply loopMatch_of_trace (T := masterDescStrongTree n 3 p) ?_ htrace.1.symm htrace.2.symm
  have h2 := masterDescWindow_multiple hinv φ hp hlt hs L ht hm hB
  have hh := masterDescStrongTree_hull hp hg hlt hinv
  have hloop := masterDescStrongTree_loop hx.1 (by exact Nat.zero_lt_of_lt h2) hh
  apply masterAdmittedRound_descent_match a b hx.1 rfl
    (by change p.1.1.length ≤ p.1.2.2.2.1.length; rw [hx.1]; exact length_le_of_nodup_lt hnd hlt)
    id rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl) hloop
  intro J hJ
  exact ⟨masterDescStrongTree_letters ((masterStrWF_iff hx.1).mp hx)
    ((masterStrWF_iff hy.1).mp hy) J hJ,
    masterDescStrongTree_progress hp hlt hinv hnd h2 J hJ,
    _, masterDescStrongTree_coset hp hlt J hJ⟩
end Window
end Algo
