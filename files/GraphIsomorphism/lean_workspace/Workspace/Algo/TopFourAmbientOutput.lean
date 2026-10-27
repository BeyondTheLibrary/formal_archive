import Workspace.Algo.TopFourAmbientEntry

/-! # The lifted answer and shrinking-call bounds
Restriction is expressed by the displayed list equivalence. Lifting the
full inner isomorphism set then gives the original window isomorphisms.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

theorem topwPreimage_strIso {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x y : Fin n → ℕ) :
    topwPreimageSet Δ hnd hlt G hinv
      (strIso ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))
        (fun i => x (winEquiv n Δ hnd hlt i)) (fun i => y (winEquiv n Δ hnd hlt i))) =
      wIso (winSet n Δ) (G : Set (Perm (Fin n))) x y := by
  rw [← wIso_univ]
  ext g
  constructor
  · rintro ⟨hg, _, hxy⟩
    refine ⟨hg, fun u hu => ?_⟩
    let i := (winEquiv n Δ hnd hlt).symm ⟨u, hu⟩
    have hh := hxy i (Set.mem_univ i)
    change x ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n) =
      y ((winEquiv n Δ hnd hlt (winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ i) : ↥(winSet n Δ)) : Fin n) at hh
    rw [topwRestrict_coe hnd hlt hinv ⟨g, hg⟩ i] at hh
    simpa only [i, Equiv.apply_symm_apply] using hh
  · rintro ⟨hg, hxy⟩
    refine ⟨hg, ⟨⟨g, hg⟩, rfl⟩, fun i _ => ?_⟩
    change x ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n) =
      y ((winEquiv n Δ hnd hlt (winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ i) : ↥(winSet n Δ)) : Fin n)
    rw [topwRestrict_coe hnd hlt hinv ⟨g, hg⟩ i]
    exact hxy _ (winEquiv n Δ hnd hlt i).property

theorem top4wTree_spec {n k : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x y : Fin n → ℕ)
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length))))
    (hT : ∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length))))
    (hr : T.run = strIso ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))
      (fun i => x (winEquiv n Δ hnd hlt i)) (fun i => y (winEquiv n Δ hnd hlt i)))
    (hlen : T.calls.length ≤ k) (hwin : ∀ J ∈ T.calls, 3 * J.windowSize ≤ 2 * Δ.length) :
    (top4wTree Δ hnd hlt G hinv x T).run = wIso (winSet n Δ) (G : Set (Perm (Fin n))) x y ∧
      (top4wTree Δ hnd hlt G hinv x T).calls.length ≤ k ∧
      (∀ J ∈ (top4wTree Δ hnd hlt G hinv x T).calls, 3 * J.windowSize ≤ 2 * Δ.length) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [top4wTree_run hnd hlt hinv x T hT, hr, topwPreimage_strIso hnd hlt hinv]
  · rw [top4wTree_calls hnd hlt hinv x T hT, List.length_map]
    exact hlen
  · intro J hJ
    rw [top4wTree_calls hnd hlt hinv x T hT, List.mem_map] at hJ
    obtain ⟨K, hK, rfl⟩ := hJ
    rw [topwInstance_windowSize hnd hlt hinv x]
    exact hwin K hK

end Algo
