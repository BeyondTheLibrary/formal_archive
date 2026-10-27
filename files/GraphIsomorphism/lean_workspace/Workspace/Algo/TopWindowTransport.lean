import Workspace.Algo.TopWindowInstance

/-! # Window transport in the machine's list labels

Every restricted-domain call is lifted as a full coset instance. The answer
is restricted before the continuation is run. Both the ordered call list and
the returned value are preserved, as in the paper's window reduction.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

noncomputable def topwReduction {n : ℕ} {β : Type*} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) :
    SIReduction (Fin Δ.length) ℕ β → SIReduction (Fin n) ℕ β
  | .done b => .done b
  | .call J k => .call (topwInstance Δ hnd hlt G hinv x J)
      (fun a => topwReduction Δ hnd hlt G hinv x (k (topwImageSet Δ hnd hlt G hinv a)))

 theorem calls_topwReduction {n : ℕ} {β : Type*} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) :
    ∀ T : SIReduction (Fin Δ.length) ℕ β,
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) →
      (topwReduction Δ hnd hlt G hinv x T).calls = T.calls.map (topwInstance Δ hnd hlt G hinv x) := by
  intro T
  induction T with
  | done b => intro _; rfl
  | call J k ih =>
    intro hT
    have hJ := hT J (by simp [SIReduction.calls])
    rw [topwReduction, SIReduction.calls_call, SIReduction.calls_call, List.map_cons,
      topwImage_answer hnd hlt hinv x J hJ]
    exact congrArg _ (ih J.answer (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ'])))

 theorem run_topwReduction {n : ℕ} {β : Type*} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) :
    ∀ T : SIReduction (Fin Δ.length) ℕ β,
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) →
      (topwReduction Δ hnd hlt G hinv x T).run = T.run := by
  intro T
  induction T with
  | done b => intro _; rfl
  | call J k ih =>
    intro hT
    have hJ := hT J (by simp [SIReduction.calls])
    rw [topwReduction, SIReduction.run_call, SIReduction.run_call,
      topwImage_answer hnd hlt hinv x J hJ]
    exact ih J.answer (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ']))

/-- Relabel a finite window instance by its explicit list equivalence. -/
noncomputable def topwSubtypeInstance {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (J : SIInstance (Fin Δ.length) ℕ) : SIInstance ↥(winSet n Δ) ℕ where
  K := (winEquiv n Δ hnd hlt).permCongr '' J.K
  Δ := (winEquiv n Δ hnd hlt) '' J.Δ
  x := fun w => J.x ((winEquiv n Δ hnd hlt).symm w)
  y := fun w => J.y ((winEquiv n Δ hnd hlt).symm w)

 theorem topwPreimage_eq_windowPreim {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (A : Set (Perm (Fin Δ.length))) :
    topwPreimageSet Δ hnd hlt G hinv A =
      windowPreim G (winSet n Δ) hinv ((winEquiv n Δ hnd hlt).permCongr '' A) := by
  ext g
  constructor
  · rintro ⟨hg, hA⟩
    refine ⟨hg, winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩, hA, ?_⟩
    ext w
    simp [winRestrictHom, Equiv.permCongr_apply]
  · rintro ⟨hg, a, ha, he⟩
    refine ⟨hg, ?_⟩
    have hh : winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ = a := by
      rw [winRestrictHom]
      change (winEquiv n Δ hnd hlt).symm.permCongr (restrictHom G (winSet n Δ) hinv ⟨g, hg⟩) = a
      rw [← he]
      ext i
      simp [Equiv.permCongr_apply]
    rwa [hh]

/-- The complete transported instance agrees with `Babai.windowInstance`,
using the displayed list equivalence as its domain isomorphism. -/
 theorem topwInstance_eq_windowInstance {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) (J : SIInstance (Fin Δ.length) ℕ) :
    topwInstance Δ hnd hlt G hinv x J =
      windowInstance G (winSet n Δ) hinv x (topwSubtypeInstance hnd hlt J) := by
  change SIInstance.mk _ _ _ _ = SIInstance.mk _ _ _ _
  congr 1
  · exact topwPreimage_eq_windowPreim hnd hlt hinv J.K
  · exact (Set.image_image Subtype.val (winEquiv n Δ hnd hlt) J.Δ).symm

end Algo
