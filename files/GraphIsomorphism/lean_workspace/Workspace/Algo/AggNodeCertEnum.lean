import Workspace.Algo.AggCanonRecompute
import Workspace.LocalCertificates.StrongAggregate
import Workspace.Algo.AggregateTestsOn

/-! # The mathematical enumeration at a raw aggregate node

Test sets keep the order of the raw table. Certificate stages use only their
mathematical groups and windows. Comparison data are chosen separately and
will be replaced by the comparison routine in the next session.
-/
namespace Algo
open Babai Equiv
open scoped Classical

/-- The points of a test set, in increasing order of their natural names. -/
noncomputable def aggkPoints {m : ℕ} (T : Set (Fin m)) : List T :=
  Finset.univ.sort (· ≤ ·)

theorem aggkPoints_complete {m : ℕ} (T : Set (Fin m)) (u : T) : u ∈ aggkPoints T := by
  simp [aggkPoints]

theorem aggkTypedT_values {n m : ℕ} {xs row : List ℕ} (hc : LCCtxWF n m xs row) :
    (aggkTypedT hc).map (fun u => u.val.val) = row := by
  apply List.ext_getElem
  · simp [aggkTypedT]
  · intro i hi hi'
    simp only [List.getElem_map, aggkTypedT, List.getElem_ofFn]
    exact congrArg Fin.val (winEquiv_coe row hc.nodup hc.ltM hi')

theorem aggkTypedT_eq_points {n m : ℕ} {xs row : List ℕ} (hc : LCCtxWF n m xs row)
    (hs : row.SortedLE) : aggkTypedT hc = aggkPoints (winSet m row) := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ hab hba
    exact le_antisymm hab hba
  · have h := hs.pairwise
    rw [← aggkTypedT_values hc, List.pairwise_map] at h
    exact h
  · exact Finset.pairwise_sort _ _
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_ofFn.mpr (tName m row hc.nodup hc.ltM).injective
    · exact Finset.sort_nodup _ _
    · ext u
      simp [aggkTypedT_complete, aggkPoints_complete]

variable {n m : ℕ} {G : Subgroup (Perm (Fin n))}

/-- A mathematical aggregate enumeration with canonical certificate fields. -/
noncomputable def aggnCertEnum (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ts : List (Set (Fin m))) : AggEnum (Fin n) (Fin m) where
  tests := ts
  certReps := fun b T i => aggkCanonReps (stages ϕ (cond b y x) T i) (aggkPoints T)
  certWindows := fun b T i => aggkCanonWindows (stages ϕ (cond b y x) T i)
  transporter := fun b T T' => (strongCompareEnum_exists ϕ x (cond b y x) T T').choose
  pair := fun b T T' => (strongCompareEnum_exists ϕ x (cond b y x) T T').choose_spec.choose

theorem aggnCertEnum_cover (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ts : List (Set (Fin m))) : (aggnCertEnum ϕ x y ts).Cover ϕ x y := by
  constructor
  · intro b T _ i _
    exact aggkStage_cover _ _
  · intro b T _ T' _
    exact (strongCompareEnum_exists ϕ x (cond b y x) T T').choose_spec.choose_spec.1
  · intro b T _ T' _
    exact (strongCompareEnum_exists ϕ x (cond b y x) T T').choose_spec.choose_spec.2.1

theorem aggnCertEnum_bound (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    {t : ℕ} {ts : List (Set (Fin m))} (ht : ts.Perm (testSetList (Fin m) t)) :
    (aggnCertEnum ϕ x y ts).Bound ϕ x y t := by
  refine ⟨ht, ?_, ?_⟩
  · intro b T _ i _
    exact aggkStage_bound _ _
  · intro b T _ T' _
    exact (strongCompareEnum_exists ϕ x (cond b y x) T T').choose_spec.choose_spec.2.2.1

/-- The enumeration attached to a raw node fixes the raw test-set order as well. -/
noncomputable def aggnRawCertEnum (c : ℕ) (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    (ks dom gdom : List ℕ) : AggEnum (Fin n) (Fin m) :=
  aggnCertEnum ϕ x y ((aggTestSetsOn c (ks, dom, gdom)).map (winSet m))

theorem aggnRawCertEnum_spec (c : ℕ) (ϕ : G →* Perm (Fin m)) (x y : Fin n → ℕ)
    {ks dom gdom : List ℕ} (hg : ks.length ≤ guardBound c dom.length)
    (hm : gdom.length = m) (hmn : m ≤ dom.length) :
    (aggnRawCertEnum c ϕ x y ks dom gdom).Spec ϕ x y ks.length := by
  refine ⟨aggnCertEnum_cover _ _ _ _, aggnCertEnum_bound _ _ _ ?_⟩
  subst m
  exact aggTestSetsOn_perm hg hmn

end Algo
