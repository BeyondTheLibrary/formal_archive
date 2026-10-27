import Workspace.LocalCertificates.StrongDescent
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Lattice

/-! # Fixed orders for Procedure Recompute

An image permutation is named by its values on the listed points of the test
set. We sort these names lexicographically. We sort kernel orbits by their
least point. Neither order refers to generators of the current group.
-/

namespace Babai

open Equiv MulAction
open scoped Classical Pointwise

variable {n m : ℕ} {Λ : Type*} {G : Subgroup (Perm (Fin n))}
  {ϕ : G →* Perm (Fin m)} {x : Fin n → Λ} {T : Set (Fin m)}

/-- Values of an image permutation in the supplied order of the test set. -/
def aggkImageKey (tdom : List T) (σ : Perm T) : List ℕ :=
  tdom.map fun u => (σ u).val.val

theorem aggkImageKey_injective (tdom : List T) (ht : ∀ u, u ∈ tdom) :
    Function.Injective (aggkImageKey tdom) := by
  intro σ τ h
  apply Equiv.ext
  intro u
  apply Subtype.ext
  apply Fin.ext
  exact (List.map_inj_left.mp h) u (ht u)

/-- Sec. 13.1, line 04c: list image elements in lexicographic order. -/
noncomputable def aggkImages (s : Stage ϕ x T) (tdom : List T) :
    List (imgOn ϕ T s.le) :=
  (Finset.univ.toList).mergeSort
    (fun a b => decide (aggkImageKey tdom a ≤ aggkImageKey tdom b))

/-- Sec. 13.1, line 04d: choose one lift for each image in its fixed order. -/
noncomputable def aggkCanonReps (s : Stage ϕ x T) (tdom : List T) :
    List (Perm (Fin n)) :=
  (aggkImages s tdom).map (certLift s)

@[simp] theorem aggkImages_mem (s : Stage ϕ x T) (tdom : List T)
    (σ : imgOn ϕ T s.le) : σ ∈ aggkImages s tdom := by
  simp [aggkImages]

theorem aggkImages_nodup (s : Stage ϕ x T) (tdom : List T) :
    (aggkImages s tdom).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem aggkImages_sorted (s : Stage ϕ x T) (tdom : List T) :
    ((aggkImages s tdom).map (fun σ : imgOn ϕ T s.le => aggkImageKey tdom σ)).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map]
  simpa only [decide_eq_true_eq] using
    List.pairwise_mergeSort
      (le := fun a b : imgOn ϕ T s.le =>
        decide (aggkImageKey tdom a ≤ aggkImageKey tdom b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
      (by intro a b; simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        le_total (aggkImageKey tdom a) (aggkImageKey tdom b))
      Finset.univ.toList

theorem aggkCanonReps_length (s : Stage ϕ x T) (tdom : List T) :
    (aggkCanonReps s tdom).length = Nat.card (imgOn ϕ T s.le) := by
  simp [aggkCanonReps, aggkImages, Nat.card_eq_fintype_card]

theorem aggkCanonReps_cover (s : Stage ϕ x T) (tdom : List T) :
    (s.H : Set (Perm (Fin n))) =
      ⋃ σ ∈ aggkCanonReps s tdom, σ • (kerN s : Set (Perm (Fin n))) := by
  rw [eq_69 s (certLift s) (certLift_spec s)]
  ext τ
  simp [aggkCanonReps]

/-- The inverse image of an image element is the coset of any of its lifts. -/
theorem aggkCoset_eq_fiber (s : Stage ϕ x T) (σ : Perm (Fin n)) (hσ : σ ∈ s.H) :
    σ • (kerN s : Set (Perm (Fin n))) =
      {τ | ∃ hτ : τ ∈ s.H,
        psiOn ϕ T s.le ⟨τ, hτ⟩ = psiOn ϕ T s.le ⟨σ, hσ⟩} := by
  ext τ
  rw [mem_perm_smul_set]
  change σ⁻¹ * τ ∈ kerN s ↔ _
  rw [mem_kerN]
  constructor
  · rintro ⟨hν, he⟩
    have hτ : τ ∈ s.H := by
      simpa only [mul_inv_cancel_left] using s.H.mul_mem hσ hν
    refine ⟨hτ, ?_⟩
    have he' : (psiOn ϕ T s.le ⟨σ, hσ⟩)⁻¹ * psiOn ϕ T s.le ⟨τ, hτ⟩ = 1 := by
      rw [← map_inv, ← map_mul]
      exact he
    exact inv_mul_eq_one.mp he' |>.symm
  · rintro ⟨hτ, he⟩
    refine ⟨s.H.mul_mem (s.H.inv_mem hσ) hτ, ?_⟩
    change psiOn ϕ T s.le ((⟨σ, hσ⟩ : s.H)⁻¹ * ⟨τ, hτ⟩) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]

theorem aggkCoset_eq_of_image_eq (s : Stage ϕ x T)
    {σ τ : Perm (Fin n)} (hσ : σ ∈ s.H) (hτ : τ ∈ s.H)
    (he : psiOn ϕ T s.le ⟨σ, hσ⟩ = psiOn ϕ T s.le ⟨τ, hτ⟩) :
    σ • (kerN s : Set (Perm (Fin n))) = τ • (kerN s : Set (Perm (Fin n))) := by
  rw [aggkCoset_eq_fiber s σ hσ, aggkCoset_eq_fiber s τ hτ, he]

/-- The least natural name in a nonempty window. -/
noncomputable def aggkLeast (Δ : Set (Fin n)) : ℕ := sInf (Fin.val '' Δ)

theorem aggkLeast_mem {Δ : Set (Fin n)} (hΔ : Δ.Nonempty) :
    ∃ u ∈ Δ, u.val = aggkLeast Δ := Nat.sInf_mem (hΔ.image _)

theorem aggkLeast_le {Δ : Set (Fin n)} {u : Fin n} (hu : u ∈ Δ) :
    aggkLeast Δ ≤ u.val := Nat.sInf_le ⟨u, hu, rfl⟩

theorem aggkOrbit_eq_of_least_eq (N : Subgroup (Perm (Fin n))) (u v : Fin n)
    (h : aggkLeast (orbit N u) = aggkLeast (orbit N v)) :
    orbit N u = orbit N v := by
  obtain ⟨a, ha, hea⟩ := aggkLeast_mem ((⟨u, mem_orbit_self u⟩ : (orbit N u).Nonempty))
  obtain ⟨b, hb, heb⟩ := aggkLeast_mem ((⟨v, mem_orbit_self v⟩ : (orbit N v).Nonempty))
  have hab : a = b := Fin.ext (hea.trans (h.trans heb.symm))
  rw [← hab] at hb
  exact ((orbit_eq_iff).2 ha).symm.trans ((orbit_eq_iff).2 hb)

/-- Sec. 13.1, line 04e: list affected kernel orbits by their least point. -/
noncomputable def aggkCanonWindows (s : Stage ϕ x T) : List (Set (Fin n)) :=
  (strongWindows s).mergeSort (fun Δ Δ' => decide (aggkLeast Δ ≤ aggkLeast Δ'))

@[simp] theorem aggkCanonWindows_mem (s : Stage ϕ x T) (Δ : Set (Fin n)) :
    Δ ∈ aggkCanonWindows s ↔ Δ ∈ strongWindows s := by
  simp [aggkCanonWindows]

theorem aggkCanonWindows_nodup (s : Stage ϕ x T) :
    (aggkCanonWindows s).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (strongWindows_nodup s)

theorem aggkCanonWindows_sorted (s : Stage ϕ x T) :
    ((aggkCanonWindows s).map aggkLeast).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map]
  simpa only [decide_eq_true_eq] using
    List.pairwise_mergeSort
      (le := fun a b : Set (Fin n) => decide (aggkLeast a ≤ aggkLeast b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
      (by intro a b; simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        le_total (aggkLeast a) (aggkLeast b)) (strongWindows s)

theorem aggkCanonWindows_cover (s : Stage ϕ x T) :
    (⋃ Δ ∈ aggkCanonWindows s, Δ) = s.aff := by
  simpa only [aggkCanonWindows_mem] using strongWindows_cover s

theorem aggkStage_cover (s : Stage ϕ x T) (tdom : List T) :
    StrongStageCover s (aggkCanonReps s tdom) (aggkCanonWindows s) :=
  ⟨aggkCanonReps_cover s tdom, aggkCanonWindows_cover s⟩

theorem aggkStage_bound (s : Stage ϕ x T) (tdom : List T) :
    StrongStageBound s (aggkCanonReps s tdom) (aggkCanonWindows s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [aggkCanonReps_length]
    exact card_imgOn_le_factorial s.le
  · simpa only [aggkCanonWindows, List.length_mergeSort] using
      (List.length_filter_le _ (orbitList (kerN s))).trans (length_orbitList_le _)
  · intro Δ hΔ
    exact strongWindows_orbits s Δ ((aggkCanonWindows_mem s Δ).mp hΔ)

/-- Choosing a different lift in each coset leaves the entire reduction tree fixed. -/
theorem aggkStrongDescent_congr {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (N : Subgroup (Perm Ω)) (x y : Ω → Λ) (L L' : List (Perm Ω))
    (Δs : List (Set Ω))
    (h : L.map (fun σ => σ • (N : Set (Perm Ω))) =
      L'.map (fun σ => σ • (N : Set (Perm Ω)))) :
    strongDescent N x y L Δs = strongDescent N x y L' Δs := by
  have he := congrArg (List.map (cosetChain x y Δs)) h
  simp only [List.map_map] at he
  exact congrArg unionAnswers he

theorem aggkRecomputeStrong_congr (s : Stage ϕ x T) (L L' : List (Perm (Fin n)))
    (Δs : List (Set (Fin n)))
    (h : L.map (fun σ => σ • (kerN s : Set (Perm (Fin n)))) =
      L'.map (fun σ => σ • (kerN s : Set (Perm (Fin n))))) :
    recomputeStrong s L Δs = recomputeStrong s L' Δs :=
  aggkStrongDescent_congr _ _ _ _ _ _ h

end Babai
