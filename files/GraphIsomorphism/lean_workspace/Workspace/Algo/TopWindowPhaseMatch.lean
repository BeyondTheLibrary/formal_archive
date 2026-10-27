import Workspace.Algo.TopWindowPhaseRound

/-! # The full supplied top-action phase through the raw window adapter

The induction uses the actual computed full-preimage coset for each call
and the actual restriction routine for each returned encoding. No equality
between independently chosen representatives is needed.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

 def TopwpCap (e f : ℕ) : Prop := ∀ (C : TopwpContext) (t i : ℕ)
    (q : RawGens × RawPerm) (W : RawWinSI),
    topwRawInstance (C.1, topcsLeaf C.2 t i q) = some W →
      Enc.size W ≤ topcsContextCap e f (Enc.size C)

 theorem topwpCap_exists : ∃ e f : ℕ, TopwpCap e f := topwp_child_bound

 theorem topwpLoopMatch {n c d e f : ℕ} {β : Type*} {B : ℕ → ℕ}
    {dom Δ x : List ℕ} {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (solve : RawWinSI → RawCoset) :
    ∀ {w j : ℕ} {s : TopcsState} {T : SIReduction (Fin Δ.length) ℕ β}
      {Q : β → ℕ → ℕ → TopcsState → Prop},
      LoopMatchK (topcsRound Δ.length B solve) (topcsDecode Δ.length) (decCoset Δ.length)
        (P, none) w j s T Q →
      (∀ J ∈ T.calls, J.K ⊆ ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length)))) →
      LoopMatchK (topwpRound c d e f solve) (topwpDecode n) (decCoset n)
        ((((dom, gens.map (encPerm n)), Δ, x), P), none) w j s
        (topwReduction Δ hnd hlt (genGroup gens) hinv (decStrN n x) T) Q := by
  intro w j s T Q h
  induction h with
  | done w j s b Q hb => intro _; exact .done w j s b Q hb
  | call w j s J k Q hc hn ih =>
    intro hT
    have hJ := hT (topcsDecode Δ.length J) (by simp [SIReduction.calls])
    change topcsChild ((P, none), j, s) = some J at hc
    obtain ⟨q, _, hcur, ht, hi, hj, rfl⟩ := topcsChild_some hc
    let W := topcsLeaf P s.1 s.2.1 q
    obtain ⟨V, hV, hdec⟩ := topwRawInstance_spec hd hx hnd hlt hinv W hJ
    let C : TopwpContext := (((dom, gens.map (encPerm n)), Δ, x), P)
    have hsmall := hcap C s.1 s.2.1 q V hV
    have hchild : topwpChild e f ((C, none), j, s) = some (C, some V) := by
      simp only [topwpChild, Option.elim_none]
      change (topcsChild ((P, none), j, s)).bind _ = _
      rw [hc]
      simp only [Option.bind_some]
      rw [hV]
      simp only [Option.bind_some, topwpAccept, if_pos hsmall]
    have hDV : topwpDecode n (C, some V) =
        topwInstance Δ hnd hlt (genGroup gens) hinv (decStrN n x)
          (topcsDecode Δ.length (P, some W)) := hdec
    change LoopMatchK _ _ _ _ (w + 1) j s
      (.call (topwInstance Δ hnd hlt (genGroup gens) hinv (decStrN n x)
        (topcsDecode Δ.length (P, some W))) _) Q
    rw [← hDV]
    refine .call w j s (C, some V) _ Q hchild ?_
    intro a ha
    have hasub : decCoset n a ⊆ (genGroup gens : Set (Perm (Fin n))) := by
      rw [ha, hDV, topwInstance_answer]
      rintro g ⟨hg, _⟩
      exact hg
    have hanswer : decCoset Δ.length (topwCosetImage (dom, Δ, a)) =
        (topcsDecode Δ.length (P, some W)).answer := by
      rw [topwCosetImage_spec hd hnd hlt hinv a hasub, ha, hDV,
        topwImage_answer hnd hlt hinv (decStrN n x) _ hJ]
    have htail := ih (topwCosetImage (dom, Δ, a)) hanswer
      (fun J' hJ' => hT J' (by simp [SIReduction.calls, hJ']))
    change LoopMatchK _ _ _ _ w (j + 1)
      (topcsCombine ((P, none), j, s, topwCosetImage (dom, Δ, a)))
      (topwReduction Δ hnd hlt (genGroup gens) hinv (decStrN n x)
        (k (topwImageSet Δ hnd hlt (genGroup gens) hinv (topwpDecode n (C, some V)).answer))) Q
    rw [hDV, topwImage_answer hnd hlt hinv (decStrN n x) _ hJ]
    exact htail

 theorem topwpPhaseMatch {n m c d e f : ℕ} {dom Δ x : List ℕ}
    {gens : List (Perm (Fin n))} {P : TopcsInput}
    (hd : dom.length = n) (hx : x.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (hcap : TopwpCap e f)
    (ϕ : (winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range →* Perm (Fin m))
    (S : List (alternatingGroup (Fin m))) (O : TopActionOdd ϕ) (E : OrbitEnum (kerSubgroup ϕ))
    (ix iy : Fin Δ.length → ℕ) (hP : TopcsSpec P ϕ S O E ix iy)
    (hpos : 0 < Δ.length) (hϕ : IsGiantRep ϕ)
    (hS : Subgroup.closure {σ : alternatingGroup (Fin m) | σ ∈ S} = ⊤)
    (solve : RawWinSI → RawCoset) :
    PhaseMatch (topwpRound c d e f solve) (topwpDecode n) (decCoset n)
      ((((dom, gens.map (encPerm n)), Δ, x), P), none)
      (topcsJobs P * (topcsWins P).length) 0 (topwpInit ((((dom, gens.map (encPerm n)), Δ, x), P), none))
      (topwReduction Δ hnd hlt (genGroup gens) hinv (decStrN n x) (cosetTopAction3With ϕ S O E ix iy))
      (TopcsDone Δ.length P) := by
  intro r
  exact topwpLoopMatch hd hx hnd hlt hinv hcap solve
    (hP.phase (fun _ => 0) solve hpos hϕ hS r)
    (calls_cosetTopAction3With_K ϕ S O E ix iy)

end Algo
