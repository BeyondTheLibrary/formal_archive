import Workspace.Algo.AggNodeTransport
import Workspace.Algo.AggNodeCertEnum

/-! # Fixed choices for the comparison phase

Proposition 13.1.11 allows a choice of an element of the current comparison
coset. We use its least ambient permutation. Source image representatives
and kernel windows keep the orders already used by the certificate phase.
These choices depend only on mathematical sets, so different encodings of
correct answers produce the same comparison tree.
-/
namespace Algo
open Babai Equiv
open scoped Classical Pointwise

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))}

/-- Lines 04c0--04d2: translate the source list by the least element of `Q`. -/
noncomputable def aggnCanonicalPair (ϕ : G →* Perm (Fin m))
    (x y : Fin n → ℕ) (T : Set (Fin m)) (σ : Perm (Fin n)) : StrongPairEnum (Fin n) where
  reps := fun i => aggkCanonReps (stages ϕ x T i) (aggkPoints T)
  compareReps := fun i =>
    if (pairedQ ϕ x y T σ i).Nonempty then
      (aggkCanonReps (stages ϕ x T i) (aggkPoints T)).map
        (aggnLeastPerm (pairedQ ϕ x y T σ i) * ·)
    else []
  windows := fun i => aggkCanonWindows (stages ϕ x T i)

theorem aggnLeastPerm_mem_paired (ϕ : G →* Perm (Fin m))
    (x y : Fin n → ℕ) (T : Set (Fin m)) {σ : Perm (Fin n)} (hσ : σ ∈ G)
    (i : ℕ) (hQ : (pairedQ ϕ x y T σ i).Nonempty) :
    aggnLeastPerm (pairedQ ϕ x y T σ i) ∈ pairedQ ϕ x y T σ i := by
  obtain ⟨π, hπ⟩ := hQ
  rw [pairedQ_eq_coset hσ i hπ]
  exact (aggnLeastPerm_coset (stages ϕ x T i).H π).1

/-- The fixed lists cover both sets in lines 04e1 and 04e2. -/
theorem aggnCanonicalPair_cover (ϕ : G →* Perm (Fin m))
    (x y : Fin n → ℕ) (T : Set (Fin m)) {σ : Perm (Fin n)} (hσ : σ ∈ G) :
    StrongPairCover ϕ x y T σ (aggnCanonicalPair ϕ x y T σ) := by
  refine ⟨fun i _ => aggkStage_cover _ _, ?_⟩
  intro i hi
  by_cases hQ : (pairedQ ϕ x y T σ i).Nonempty
  · have hπ := aggnLeastPerm_mem_paired ϕ x y T hσ i hQ
    conv_lhs => rw [pairedQ_eq_coset hσ i hπ, aggkCanonReps_cover _ (aggkPoints T)]
    simp [aggnCanonicalPair, hQ, Set.smul_set_iUnion, smul_smul]
  · simp [aggnCanonicalPair, Set.not_nonempty_iff_eq_empty.mp hQ]

/-- Both fixed lists retain the factorial bound from the paper. -/
theorem aggnCanonicalPair_bound (ϕ : G →* Perm (Fin m))
    (x y : Fin n → ℕ) (T : Set (Fin m)) (σ : Perm (Fin n)) :
    StrongPairBound ϕ x T (aggnCanonicalPair ϕ x y T σ) := by
  refine ⟨fun i _ => aggkStage_bound _ _, ?_⟩
  intro i hi
  dsimp only [aggnCanonicalPair]
  split
  · rw [List.length_map, aggkCanonReps_length]
    exact card_imgOn_le_factorial _
  · exact Nat.zero_le _

/-- The aggregate enumeration with all comparison choices fixed explicitly. -/
noncomputable def aggnFullEnum (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ts : List (Set (Fin m))) : AggEnum (Fin n) (Fin m) :=
  { aggnCertEnum ϕ x y ts with
    transporter := fun _ T T' => aggnCanonTransport ϕ T T'
    pair := fun b T T' => aggnCanonicalPair ϕ x (cond b y x) T
      ((aggnCanonTransport ϕ T T').getD 1) }

theorem aggnFullEnum_cover (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ts : List (Set (Fin m))) : (aggnFullEnum ϕ x y ts).Cover ϕ x y := by
  refine ⟨(aggnCertEnum_cover ϕ x y ts).cert, ?_, ?_⟩
  · intro b T hT T' hT'
    exact aggnCanonTransport_spec ϕ T T'
  · intro b T hT T' hT' σ hs
    have ht := aggnCanonTransport_spec ϕ T T'
    change aggnCanonTransport ϕ T T' = some σ at hs
    rw [hs] at ht
    obtain ⟨hσ, hm⟩ := ht
    change StrongPairCover _ _ _ _ _ (aggnCanonicalPair _ _ _ _ _)
    simp only [hs, Option.getD_some]
    exact aggnCanonicalPair_cover ϕ x (cond b y x) T hσ

theorem aggnFullEnum_bound (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    {t : ℕ} {ts : List (Set (Fin m))} (ht : ts.Perm (testSetList (Fin m) t)) :
    (aggnFullEnum ϕ x y ts).Bound ϕ x y t := by
  refine ⟨ht, (aggnCertEnum_bound ϕ x y ht).cert, ?_⟩
  intro b T hT T' hT'
  exact aggnCanonicalPair_bound ϕ x (cond b y x) T _

/-- Replacing the comparison choices leaves the certificate tree unchanged. -/
theorem aggnFullEnum_certPhase (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ts : List (Set (Fin m))) :
    certPhaseStrong ϕ x y (aggnFullEnum ϕ x y ts) =
      certPhaseStrong ϕ x y (aggnCertEnum ϕ x y ts) := rfl

end Algo
