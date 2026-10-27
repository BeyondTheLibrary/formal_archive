import Workspace.Algo.TopMasterLineTwoFull

/-! # Carrying the ordered line-2 chains back to the ambient window
The window lift preserves the order of the image tests and their orbit
chains. The target outside the window is restored to the source, just as
in `windowInstance`. These trace equations transfer the exact raw matcher.
-/
namespace Algo
open Babai Equiv
open scoped Classical

section Window
variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {K : Subgroup (Perm Ω)} {Δ : Set Ω} (hinv : IsInvariant K Δ) (x : Ω → A)

 theorem masterWindowUnion_trace (L : List (SIReduction Δ A (Set (Perm Δ))))
    (hL : ∀ R ∈ L, ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ hinv : Set (Perm Δ))) :
    (liftWindow K Δ hinv x (unionAnswers L)).calls =
        (unionAnswers (L.map (liftWindow K Δ hinv x))).calls ∧
      (liftWindow K Δ hinv x (unionAnswers L)).run =
        (unionAnswers (L.map (liftWindow K Δ hinv x))).run := by
  have hall : ∀ J ∈ (unionAnswers L).calls, J.K ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) := by
    intro J hJ
    rw [calls_unionAnswers, List.mem_flatMap] at hJ
    obtain ⟨R, hR, hJ⟩ := hJ
    exact hL R hR J hJ
  constructor
  · rw [calls_liftWindow hinv x _ hall, calls_unionAnswers, calls_unionAnswers,
      List.flatMap_map, List.map_flatMap]
    apply List.flatMap_congr
    intro R hR
    exact (calls_liftWindow hinv x R (hL R hR)).symm
  · have hv (R : SIReduction Δ A (Set (Perm Δ))) (hR : R ∈ L) :
        (liftWindow K Δ hinv x R).run = windowPreim K Δ hinv R.run := by
      rw [liftWindow, SIReduction.run_bind, SIReduction.run_done,
        SIReduction.run_window hinv x R (hL R hR)]
    rw [liftWindow, SIReduction.run_bind, SIReduction.run_done,
      SIReduction.run_window hinv x _ hall, run_unionAnswers, run_unionAnswers]
    ext g
    simp only [windowPreim, Set.mem_setOf_eq, Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨hg, R, hR, hRg⟩
      exact ⟨_, ⟨R, hR, rfl⟩, (hv R hR).symm ▸ ⟨hg, hRg⟩⟩
    · rintro ⟨_, ⟨R, hR, rfl⟩, hg⟩
      rw [hv R hR] at hg
      exact ⟨hg.1, R, hR, hg.2⟩

 theorem masterWindowImageChains_trace (y : Δ → A) (D : List (Set Δ))
    (C : List (Set (Perm Δ)))
    (hC : ∀ U ∈ C, U ⊆ (restrictTo K Δ hinv : Set (Perm Δ))) :
    let T := liftWindow K Δ hinv x
      (unionAnswers (C.map (Babai.cosetChain (restrictStr Δ x) y D)))
    let U := unionAnswers (C.map (fun S =>
      Babai.cosetChain x (extendStr Δ x y) (D.map (Subtype.val '' ·)) (windowPreim K Δ hinv S)))
    T.calls = U.calls ∧ T.run = U.run := by
  have hL : ∀ R ∈ C.map (Babai.cosetChain (restrictStr Δ x) y D),
      ∀ J ∈ R.calls, J.K ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) := by
    intro R hR
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hR
    intro J hJ
    exact (calls_cosetChain_K _ _ _ _ J hJ).trans (hC S hS)
  have h := masterWindowUnion_trace hinv x _ hL
  dsimp only
  constructor
  · refine h.1.trans ?_
    simp only [calls_unionAnswers, List.flatMap_map]
    apply List.flatMap_congr
    intro S hS
    exact (masterWindowChain_trace hinv x y D S (hC S hS)).1
  · refine h.2.trans ?_
    rw [List.map_map, run_unionAnswers, run_unionAnswers]
    ext g
    simp only [Set.mem_iUnion, List.mem_map, exists_prop]
    constructor
    · rintro ⟨_, ⟨S, hS, rfl⟩, hg⟩
      exact ⟨_, ⟨S, hS, rfl⟩, (masterWindowChain_trace hinv x y D S (hC S hS)).2 ▸ hg⟩
    · rintro ⟨_, ⟨S, hS, rfl⟩, hg⟩
      exact ⟨_, ⟨S, hS, rfl⟩, (masterWindowChain_trace hinv x y D S (hC S hS)).2.symm ▸ hg⟩

 theorem masterWindowLine2_trace {H : Type*} [Group H] [Fintype H]
    (φ : restrictTo K Δ hinv →* H) (y : Δ → A) (E : Line2Enum φ) :
    let T := liftWindow K Δ hinv x (cosetLine2ReductionWith φ (restrictStr Δ x) y E)
    let U := unionAnswers (E.elements.map (fun a =>
      Babai.cosetChain x (extendStr Δ x y) (E.orbits.windows.map (Subtype.val '' ·))
        (windowPreim K Δ hinv (preimageSet φ a))))
    T.calls = U.calls ∧ T.run = U.run := by
  have h := masterWindowImageChains_trace hinv x y E.orbits.windows
    (E.elements.map (preimageSet φ)) (by
      intro C hC
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hC
      exact preimageSet_subset φ a)
  rw [masterLine2_flat]
  simpa only [List.map_map, Function.comp_def] using h
end Window
end Algo
