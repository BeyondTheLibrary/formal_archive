import Workspace.Algo.TopWindowStrings

/-! # Exact raw instances for the window transport

The adapter lifts a coset, its window, and both strings together. It keeps
the reference source outside the restricted domain. The decoded instance
is the full window instance, including its candidate coset and every letter.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv

abbrev TopwContext := (List ℕ × RawGens) × List ℕ × RawStr

 def topwRawInstance (p : TopwContext × RawWinSI) : Option RawWinSI :=
  (topwCosetPreimage (p.1.1, p.1.2.1, some (p.2.2.1, p.2.2.2.1))).map fun q =>
    (topw3LiftWindow (p.1.2.1, p.2.1), q.1, q.2,
      topwExtendStr (p.1.2.2, p.1.2.1, p.2.2.2.2.1),
      topwExtendStr (p.1.2.2, p.1.2.1, p.2.2.2.2.2))

noncomputable def topwInstance {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ)
    (J : SIInstance (Fin Δ.length) ℕ) : SIInstance (Fin n) ℕ where
  K := topwPreimageSet Δ hnd hlt G hinv J.K
  Δ := (fun i : Fin Δ.length => ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n)) '' J.Δ
  x := extendStr (winSet n Δ) x (fun w => J.x ((winEquiv n Δ hnd hlt).symm w))
  y := extendStr (winSet n Δ) x (fun w => J.y ((winEquiv n Δ hnd hlt).symm w))

 theorem topwInstance_windowSize {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) (J : SIInstance (Fin Δ.length) ℕ) :
    (topwInstance Δ hnd hlt G hinv x J).windowSize = J.windowSize := by
  exact Set.ncard_image_of_injective _ (Subtype.val_injective.comp (winEquiv n Δ hnd hlt).injective)

 theorem topwRestrict_coe {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (g : G) (i : Fin Δ.length) :
    ((winEquiv n Δ hnd hlt (winRestrictHom n Δ hnd hlt G hinv g i) : ↥(winSet n Δ)) : Fin n) =
      (g : Perm (Fin n)) ((winEquiv n Δ hnd hlt i : ↥(winSet n Δ)) : Fin n) := by
  rw [winRestrictHom_apply, Equiv.apply_symm_apply]
  rfl

 theorem topwInstance_answer {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) (J : SIInstance (Fin Δ.length) ℕ) :
    (topwInstance Δ hnd hlt G hinv x J).answer = topwPreimageSet Δ hnd hlt G hinv J.answer := by
  ext g
  constructor
  · rintro ⟨⟨hg, hK⟩, hxy⟩
    refine ⟨hg, hK, fun i hi => ?_⟩
    have he := hxy _ ⟨i, hi, rfl⟩
    dsimp only [topwInstance] at he
    rw [← topwRestrict_coe hnd hlt hinv ⟨g, hg⟩ i] at he
    simpa only [extendStr_coe, Equiv.symm_apply_apply] using he
  · rintro ⟨hg, hK, hxy⟩
    refine ⟨⟨hg, hK⟩, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    dsimp only [topwInstance]
    rw [← topwRestrict_coe hnd hlt hinv ⟨g, hg⟩ i]
    simpa only [extendStr_coe, Equiv.symm_apply_apply] using hxy i hi

 theorem topwImage_answer {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) (x : Fin n → ℕ) (J : SIInstance (Fin Δ.length) ℕ)
    (hJ : J.K ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    topwImageSet Δ hnd hlt G hinv (topwInstance Δ hnd hlt G hinv x J).answer = J.answer := by
  rw [topwInstance_answer]
  exact topwImage_preimage hnd hlt hinv (fun _ h => hJ h.1)

 theorem topwRawInstance_spec {n : ℕ} {dom Δ x : List ℕ}
    {gens : List (Perm (Fin n))} (hd : dom.length = n) (hx : x.length = n)
    (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant (genGroup gens) (winSet n Δ)) (W : RawWinSI)
    (hW : (decWinSI Δ.length W).K ⊆
      ((winRestrictHom n Δ hnd hlt (genGroup gens) hinv).range : Set (Perm (Fin Δ.length)))) :
    ∃ Z, topwRawInstance (((dom, gens.map (encPerm n)), Δ, x), W) = some Z ∧
      decWinSI n Z = topwInstance Δ hnd hlt (genGroup gens) hinv (decStrN n x) (decWinSI Δ.length W) := by
  have hpre := topwCosetPreimage_spec hd hnd hlt hinv (some (W.2.1, W.2.2.1)) hW
  cases hp : topwCosetPreimage ((dom, gens.map (encPerm n)), Δ, some (W.2.1, W.2.2.1)) with
  | none =>
    have hr : decPerm Δ.length W.2.2.1 ∈ (decWinSI Δ.length W).K :=
      ⟨1, one_mem _, by simp⟩
    obtain ⟨g, hg⟩ := hW hr
    have hg' : (g : Perm (Fin n)) ∈ topwPreimageSet Δ hnd hlt (genGroup gens) hinv
        (decCoset Δ.length (some (W.2.1, W.2.2.1))) := ⟨g.2, by rwa [hg]⟩
    rw [← hpre, hp] at hg'
    exact False.elim hg'
  | some q =>
    refine ⟨(topw3LiftWindow (Δ, W.1), q.1, q.2,
      topwExtendStr (x, Δ, W.2.2.2.1), topwExtendStr (x, Δ, W.2.2.2.2)),
      by simp only [topwRawInstance, hp, Option.map_some], ?_⟩
    have hq : decCoset n (some q) = topwPreimageSet Δ hnd hlt (genGroup gens) hinv
        (decCoset Δ.length (some (W.2.1, W.2.2.1))) := by simpa only [hp] using hpre
    rcases q with ⟨gs, r⟩
    change SIInstance.mk _ _ _ _ = SIInstance.mk _ _ _ _
    congr 1
    · exact topw3LiftWindow_spec Δ W.1 hnd hlt
    · exact topwExtendStr_spec hx hnd hlt W.2.2.2.1
    · exact topwExtendStr_spec hx hnd hlt W.2.2.2.2

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

 theorem polyFun_topwRawInstance : PolyFun topwRawInstance := by
  let X := TopwContext × RawWinSI
  have hc : PolyFun (fun z : X => z.1) := polyFun_fst
  have hW : PolyFun (fun z : X => z.2) := polyFun_snd
  have hg := pfst hc
  have hwin := pfst (psnd hc)
  have hx := psnd (psnd hc)
  have hws := pfst hW
  have hgens := pfst (psnd hW)
  have hrep := pfst (psnd (psnd hW))
  have hsrc := pfst (psnd (psnd (psnd hW)))
  have htgt := psnd (psnd (psnd (psnd hW)))
  have hp := (hg.pair (hwin.pair ((hgens.pair hrep).comp polyFun_some))).comp polyFun_topwCosetPreimage
  have hwindow := (hwin.pair hws).comp polyFun_topw3LiftWindow
  have hs := (hx.pair (hwin.pair hsrc)).comp polyFun_topwExtendStr
  have ht := (hx.pair (hwin.pair htgt)).comp polyFun_topwExtendStr
  have hb : PolyFun (fun z : (RawGens × RawPerm) × X => some
      (topw3LiftWindow (z.2.1.2.1, z.2.2.1), z.1.1, z.1.2,
        topwExtendStr (z.2.1.2.2, z.2.1.2.1, z.2.2.2.2.2.1),
        topwExtendStr (z.2.1.2.2, z.2.1.2.1, z.2.2.2.2.2.2))) :=
    ((polyFun_snd.comp hwindow).pair ((pfst polyFun_fst).pair ((psnd polyFun_fst).pair
      ((polyFun_snd.comp hs).pair (polyFun_snd.comp ht))))).comp polyFun_some
  exact ((hp.pair polyFun_id).comp (PolyFun.optionElim (polyFun_const none) hb)).of_eq (fun p => by
    unfold topwRawInstance
    cases topwCosetPreimage (p.1.1, p.1.2.1, some (p.2.2.1, p.2.2.2.1)) <;> rfl)

end Algo
