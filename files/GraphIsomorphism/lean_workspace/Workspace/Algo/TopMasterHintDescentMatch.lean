import Workspace.Algo.TopMasterHintDescent

/-! # Exact matching for the computed small-image descent
The supplied action determines both representative order and kernel
orbits. The proof of multiple kernel orbits belongs to the inherited
Johnson/block invariant; it is stated separately from the raw matcher.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 theorem masterHintDesc_match (a b : ℕ) {n m : ℕ} {p : MasterHintInput}
    (hx : RawStr.WF n (2 * n + 1) p.1.2.2.2.1)
    (hy : RawStr.WF n (2 * n + 1) p.1.2.2.2.2)
    (hw : RawGens.WF n p.1.2.1) (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hr : masterHintRoute p = 1)
    (h2 : 1 < (winOrbits (topKernel (masterDescAction (masterHintDescInput p)), p.1.1)).length) :
    let F := masterDescOpenOps 3 masterHintDescSelect
    LoopMatch (masterAdmittedRound a b F) (fun J => decWinSI n J.1) (decCoset n)
      (p.1, some p.2) (F.width (p.1, some p.2)) 0 (F.init (p.1, some p.2))
      (masterDescStrongTree n 3 (masterHintDescInput p)) := by
  dsimp only
  have hA := masterHintDescInput_wf hx.1 hw hnd hlt hinv hp
  have hg := masterDescFuel_eq (c := 3) (masterHintDescInput_guard hx.1 hnd hlt hr)
    (masterDescWidth_le_factorial hA)
  have hh := masterDescStrongTree_hull hA hg hlt hinv
  have hL := masterDescStrongTree_loop hx.1 (by exact Nat.zero_lt_of_lt h2) hh
  apply masterAdmittedRound_descent_match a b hx.1 rfl
    (by change p.1.1.length ≤ p.1.2.2.2.1.length; rw [hx.1]; exact length_le_of_nodup_lt hnd hlt)
    id rfl (fun _ _ => rfl) rfl (fun _ _ _ => rfl) (fun _ => rfl) hL
  intro J hJ
  exact ⟨masterDescStrongTree_letters ((masterStrWF_iff hx.1).mp hx)
    ((masterStrWF_iff hy.1).mp hy) J hJ,
    masterDescStrongTree_progress hA hlt hinv hnd h2 J hJ,
    _, masterDescStrongTree_coset hA hlt J hJ⟩

 theorem masterHintDesc_calls_le {n m : ℕ} {p : MasterHintInput}
    (hx : p.1.2.2.2.1.length = n) (hw : RawGens.WF n p.1.2.1)
    (hnd : p.1.1.Nodup) (hlt : ∀ u ∈ p.1.1, u < n)
    (hinv : IsInvariant (decGroup n p.1.2.1) (winSet n p.1.1))
    {ϕ : decGroup p.1.1.length (masterHintTop p).1.1.2 →* Perm (Fin m)}
    (hp : RawAction.WF p.1.1.length m (masterHintTop p).1 ϕ)
    (hr : masterHintRoute p = 1) :
    (masterDescStrongTree n 3 (masterHintDescInput p)).calls.length ≤
      Nat.factorial p.2.1.1.length * p.1.1.length := by
  have hA := masterHintDescInput_wf hx hw hnd hlt hinv hp
  have hg := masterDescFuel_eq (c := 3) (masterHintDescInput_guard hx hnd hlt hr)
    (masterDescWidth_le_factorial hA)
  exact (masterDescStrongTree_calls_le hA hg).trans
    (Nat.mul_le_mul_right _ (masterDescWidth_le_factorial hA))

end Algo
