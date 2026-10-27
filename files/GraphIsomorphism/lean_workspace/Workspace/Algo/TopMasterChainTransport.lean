import Workspace.Algo.TopMasterChainInput

/-! # Ordered orbit chains commute with the paper's window lift
The target outside the parent window is the reference source, exactly as
in `windowInstance`. Full preimages preserve the successive candidates.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Classical

/-- The matching judgment observes each actual recursive call and its answer.
Thus equal ordered calls and equal final values transfer a checked match. -/
theorem loopMatch_of_trace {ι ω α Ω A : Type*} {R : Round ι ω α}
    {decI : ι → SIInstance Ω A} {decA : α → Set (Perm Ω)} {I : ι}
    {w j : ℕ} {s : ω} {T U : SIReduction Ω A (Set (Perm Ω))}
    (h : LoopMatch R decI decA I w j s T) (hc : T.calls = U.calls) (hv : T.run = U.run) :
    LoopMatch R decI decA I w j s U := by
  induction h generalizing U with
  | done w j s A hstop hA =>
    cases U with
    | done B => exact .done w j s B hstop (hA.trans hv)
    | call J k => simp [SIReduction.calls] at hc
  | call w j s J k hchild hnext ih =>
    cases U with
    | done B => simp [SIReduction.calls] at hc
    | call V l =>
      have he := List.cons.inj hc
      cases he.1
      refine .call w j s J l hchild ?_
      intro a ha
      exact ih a ha he.2 hv

section Window
variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω]
    {K : Subgroup (Perm Ω)} {Δ : Set Ω} (hinv : IsInvariant K Δ)

 theorem masterWindowPreim_empty {C : Set (Perm Δ)}
    (hC : C ⊆ (restrictTo K Δ hinv : Set (Perm Δ))) :
    windowPreim K Δ hinv C = ∅ ↔ C = ∅ := by
  constructor
  · intro he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (hC hg)
    have hm : (k : Perm Ω) ∈ windowPreim K Δ hinv C := ⟨k.2, hk.symm ▸ hg⟩
    rw [he] at hm
    exact hm
  · rintro rfl
    ext g
    simp [windowPreim]

 theorem masterWindowPreim_group :
    windowPreim K Δ hinv (restrictTo K Δ hinv : Set (Perm Δ)) = K := by
  ext g
  exact ⟨fun ⟨hg, _⟩ => hg, fun hg => ⟨hg, ⟨⟨g, hg⟩, rfl⟩⟩⟩

 theorem masterWindowChain_trace (x : Ω → A) (y : Δ → A) :
    ∀ (L : List (Set Δ)) (C : Set (Perm Δ)), C ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) →
    let T := liftWindow K Δ hinv x (Babai.cosetChain (restrictStr Δ x) y L C)
    let U := Babai.cosetChain x (extendStr Δ x y) (L.map (Subtype.val '' ·)) (windowPreim K Δ hinv C)
    T.calls = U.calls ∧ T.run = U.run := by
  intro L
  induction L with
  | nil => intro C _; exact ⟨rfl, rfl⟩
  | cons S L ih =>
    intro C hC
    have hcalls := calls_cosetChain_K (restrictStr Δ x) y (S :: L) C
    have hsub : ∀ J ∈ (Babai.cosetChain (restrictStr Δ x) y (S :: L) C).calls,
        J.K ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) := fun J hJ => (hcalls J hJ).trans hC
    dsimp only
    rw [calls_liftWindow hinv x _ hsub, liftWindow, SIReduction.run_bind,
      SIReduction.run_done, SIReduction.run_window hinv x _ hsub]
    by_cases hE : C = ∅
    · have hPE := (masterWindowPreim_empty hinv hC).2 hE
      subst C
      simp [Babai.cosetChain, hPE]
    · have hPE := (masterWindowPreim_empty hinv hC).not.mpr hE
      have hI : windowInstance K Δ hinv x (⟨C, S, restrictStr Δ x, y⟩ : SIInstance Δ A) =
          (⟨windowPreim K Δ hinv C, Subtype.val '' S, x, extendStr Δ x y⟩ : SIInstance Ω A) := by
        simp only [windowInstance, extendStr_restrictStr]
      have hA := answer_windowInstance hinv x (⟨C, S, restrictStr Δ x, y⟩ : SIInstance Δ A)
      rw [hI] at hA
      have htail := ih (⟨C, S, restrictStr Δ x, y⟩ : SIInstance Δ A).answer
        ((wIso_subset S C _ _).trans hC)
      dsimp only at htail
      have htailSub : ∀ J ∈ (Babai.cosetChain (restrictStr Δ x) y L
          (⟨C, S, restrictStr Δ x, y⟩ : SIInstance Δ A).answer).calls,
          J.K ⊆ (restrictTo K Δ hinv : Set (Perm Δ)) := fun J hJ =>
        (calls_cosetChain_K _ _ _ _ J hJ).trans ((wIso_subset S C _ _).trans hC)
      rw [calls_liftWindow hinv x _ htailSub, liftWindow, SIReduction.run_bind,
        SIReduction.run_done, SIReduction.run_window hinv x _ htailSub] at htail
      simp only [List.map_cons, Babai.cosetChain, if_neg hE, if_neg hPE,
        SIReduction.calls_call, SIReduction.run_call, hI, hA]
      exact ⟨congrArg _ htail.1, htail.2⟩
end Window
end Algo
