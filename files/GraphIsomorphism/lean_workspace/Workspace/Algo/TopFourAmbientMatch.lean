import Workspace.Algo.TopFourAmbientRound

/-! # Exact matching through the ambient master window
The match quantifies over every raw encoding of every correct child answer.
The restriction routine, rather than a selected representative, passes that
answer back to the inner continuation.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

noncomputable def top4wTree {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ)
    (T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length)))) :
    SIReduction (Fin n) ℕ (Set (Perm (Fin n))) :=
  (topwReduction Δ hnd hlt G hinv x T).bind
    (fun A => .done (topwPreimageSet Δ hnd hlt G hinv A))

theorem top4wLoopMatch {n a b c d e f u v : ℕ}
    {dom Δ x : List ℕ} {gens : List (Perm (Fin n))} {P : Top4aNode}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ i ∈ Δ, i < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : Top4wCap e f u v)
    (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : Top4State} {T : SIReduction (Fin Δ.length) ℕ (Set (Perm (Fin Δ.length)))},
      LoopMatch (top4aRound c d e f solve) (top4aDecode Δ.length) (decCoset Δ.length) P w j s T →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length)))) →
      T.run ⊆ ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length))) →
      LoopMatch (top4wRound a b c d e f u v solve) (top4wDecode n) (decCoset n)
        ((((dom, gens.map (encPerm n)), Δ, x), P), none) w j s
        (top4wTree Δ hnd hlt (genGroup gens) hinv (decStrN n x) T) := by
  intro w j s T h
  induction h with
  | done w j s A hc ha =>
    intro _ hA
    change top4aChild e f (P, j, s) = none at hc
    change decCoset Δ.length (top4aFinish solve (P, s)) = A at ha
    refine .done w j s _ ?_ ?_
    · change (top4aChild e f (P, j, s)).bind _ = none
      rw [hc]
      rfl
    · change decCoset n (top2NormC x (topwCosetPreimage
        ((dom, gens.map (encPerm n)), Δ, top4aFinish solve (P, s)))) = _
      rw [decCoset_top2NormC hx, topwCosetPreimage_spec hd hnd hlt hinv _ (ha.symm ▸ hA), ha]
  | call w j s J k hc hn ih =>
    intro hT hR
    have hJ := hT (top4aDecode Δ.length J) (by simp [SIReduction.calls])
    change top4aChild e f (P, j, s) = some J at hc
    obtain ⟨_, K, hK, rfl⟩ := top4aChild_some hc
    obtain ⟨_, W, rfl, _⟩ := top4Child_some hK
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec hd hx hnd hlt hinv W hJ
    let C : Top4wContext := (((dom, gens.map (encPerm n)), Δ, x), P)
    have hsmall := hcap C j s ((P.1.1, some W), P.2) W V hc rfl hV
    have hchild : top4wChild e f u v ((C, none), j, s) = some (C, some V) := by
      simp only [top4wChild, Option.elim_none]
      change (top4aChild e f (P, j, s)).bind _ = _
      rw [hc]
      simp only [Option.bind_some]
      rw [hV]
      simp only [Option.bind_some, top4wAccept, if_pos hsmall]
    have hDV : top4wDecode n (C, some V) =
        topwInstance Δ hnd hlt (genGroup gens) hinv (decStrN n x)
          (top4aDecode Δ.length ((P.1.1, some W), P.2)) := hdec
    change LoopMatch _ _ _ _ (w + 1) j s (.call
      (topwInstance Δ hnd hlt (genGroup gens) hinv (decStrN n x)
        (top4aDecode Δ.length ((P.1.1, some W), P.2))) _)
    rw [← hDV]
    refine .call w j s (C, some V) _ hchild ?_
    intro z hz
    have hzsub : decCoset n z ⊆ (genGroup gens : Set (Perm (Fin n))) := by
      rw [hz, hDV, topwInstance_answer]
      rintro g ⟨hg, _⟩
      exact hg
    have hanswer : decCoset Δ.length (topwCosetImage (dom, Δ, z)) =
        (top4aDecode Δ.length ((P.1.1, some W), P.2)).answer := by
      rw [topwCosetImage_spec hd hnd hlt hinv z hzsub, hz, hDV,
        topwImage_answer hnd hlt hinv (decStrN n x) _ hJ]
    have htail := ih (topwCosetImage (dom, Δ, z)) hanswer
      (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ'])) hR
    change LoopMatch _ _ _ _ w (j + 1)
      (top4aCombine (P, j, s, topwCosetImage (dom, Δ, z)))
      (top4wTree Δ hnd hlt (genGroup gens) hinv (decStrN n x)
        (k (topwImageSet Δ hnd hlt (genGroup gens) hinv (top4wDecode n (C, some V)).answer)))
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n x) _ hJ]
    exact htail

end Algo
