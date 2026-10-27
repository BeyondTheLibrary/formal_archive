import Workspace.Algo.TopWindowCoset

/-! # Restricting returned cosets to the window

The window computation receives the restriction of the full-domain answer.
The routine below accepts every encoding of that answer and normalizes its
restricted generators. Its specification assumes only that the decoded
answer lies in the ambient group, as every correct recursive answer does.
-/
namespace Algo
open RAM RAM.Targets Babai Equiv
open scoped Pointwise

abbrev TopwImageInput := List ℕ × List ℕ × RawCoset

 def topwCosetImage (p : TopwImageInput) : RawCoset :=
  p.2.2.map fun a =>
    (tidyGens (p.2.1, rawRestrictGens ((p.1, normGens (p.1, a.1)), p.2.1)),
      normPerm (p.2.1, rawRestrictPerm (p.2.1, normPerm (p.1, a.2))))

noncomputable def topwImageSet {n : ℕ} (Δ : List ℕ) (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) (G : Subgroup (Perm (Fin n)))
    (hinv : IsInvariant G (winSet n Δ)) (A : Set (Perm (Fin n))) : Set (Perm (Fin Δ.length)) :=
  {r | ∃ g ∈ A, ∃ hg : g ∈ G, winRestrictHom n Δ hnd hlt G hinv ⟨g, hg⟩ = r}

 theorem topwImage_preimage {n : ℕ} {Δ : List ℕ} (hnd : Δ.Nodup)
    (hlt : ∀ u ∈ Δ, u < n) {G : Subgroup (Perm (Fin n))}
    (hinv : IsInvariant G (winSet n Δ)) {A : Set (Perm (Fin Δ.length))}
    (hA : A ⊆ ((winRestrictHom n Δ hnd hlt G hinv).range : Set (Perm (Fin Δ.length)))) :
    topwImageSet Δ hnd hlt G hinv (topwPreimageSet Δ hnd hlt G hinv A) = A := by
  ext r
  constructor
  · rintro ⟨g, ⟨hg, hmem⟩, hg', rfl⟩
    exact hmem
  · intro hr
    obtain ⟨g, hg⟩ := hA hr
    exact ⟨g, ⟨g.2, by rwa [hg]⟩, g.2, hg⟩

 theorem topwCosetImage_spec {n : ℕ} {dom Δ : List ℕ} {G : Subgroup (Perm (Fin n))}
    (hd : dom.length = n) (hnd : Δ.Nodup) (hlt : ∀ u ∈ Δ, u < n)
    (hinv : IsInvariant G (winSet n Δ)) (a : RawCoset)
    (ha : decCoset n a ⊆ (G : Set (Perm (Fin n)))) :
    decCoset Δ.length (topwCosetImage (dom, Δ, a)) =
      topwImageSet Δ hnd hlt G hinv (decCoset n a) := by
  cases a with
  | none => simp [topwCosetImage, decCoset, topwImageSet]
  | some a =>
    rcases a with ⟨gs, r⟩
    rw [decCoset_some] at ha
    obtain ⟨hr, hg⟩ := topwCoset_parts ha
    let H := decGroup n gs
    have hinvH : IsInvariant H (winSet n Δ) := fun g h => hinv g (hg h)
    let θ := winRestrictHom n Δ hnd hlt G hinv
    let θH := winRestrictHom n Δ hnd hlt H hinvH
    have he : ∀ h : H, θH h = θ ⟨h, hg h.2⟩ := fun _ => rfl
    have hnr := normPerm_eq_enc hd r
    have hng := normGens_eq_enc hd gs
    have hgr := decGroup_rawRestrictGens hnd hlt dom (gs.map (decPerm n)) hinvH
    simp only [topwCosetImage, Option.map_some, decCoset_some, decGroup_tidyGens rfl,
      decPerm_normPerm rfl, hng, hnr]
    rw [hgr, rawRestrictPerm_spec hnd hlt hinv hr, decPerm_encPerm]
    change θ ⟨decPerm n r, hr⟩ • (θH.range : Set (Perm (Fin Δ.length))) =
      topwImageSet Δ hnd hlt G hinv (decPerm n r • (H : Set (Perm (Fin n))))
    ext s
    constructor
    · rintro ⟨k, ⟨h, hh⟩, hks⟩
      subst k
      refine ⟨decPerm n r * (h : Perm (Fin n)), ⟨h, h.2, rfl⟩, G.mul_mem hr (hg h.2), ?_⟩
      change θ (⟨decPerm n r, hr⟩ * ⟨h, hg h.2⟩) = s
      rw [map_mul, ← he]
      exact hks
    · rintro ⟨g, ⟨k, hk, hkg⟩, hgG, hgs⟩
      have hkg' : decPerm n r * k = g := hkg
      subst g
      refine ⟨θH ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, ?_⟩
      change θ ⟨decPerm n r, hr⟩ * θH ⟨k, hk⟩ = s
      rw [he, ← map_mul]
      exact hgs

 theorem size_topwCosetImage (p : TopwImageInput) :
    Enc.size (topwCosetImage p) ≤ chainBound p.2.1.length := by
  have h0 := chainBound_ge p.2.1.length
  unfold topwCosetImage
  cases p.2.2 with
  | none => simp only [Option.map_none, size_none]; omega
  | some a =>
    exact size_coset_le' le_rfl (wf_tidyGens rfl _) (length_tidyGens rfl _) (wf_normPerm rfl _)

private theorem pfst {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).1) := h.comp polyFun_fst
private theorem psnd {α β γ : Type*} [Enc α] [Enc β] [Enc γ] {f : α → β × γ}
    (h : PolyFun f) : PolyFun (fun a => (f a).2) := h.comp polyFun_snd

 theorem polyFun_topwCosetImage : PolyFun topwCosetImage := by
  let X := (RawGens × RawPerm) × TopwImageInput
  have hd : PolyFun (fun z : X => z.2.1) := pfst polyFun_snd
  have hw : PolyFun (fun z : X => z.2.2.1) := pfst (psnd polyFun_snd)
  have hg : PolyFun (fun z : X => z.1.1) := pfst polyFun_fst
  have hr : PolyFun (fun z : X => z.1.2) := psnd polyFun_fst
  have hgens := (hw.pair (((hd.pair ((hd.pair hg).comp polyFun_normGens)).pair hw).comp
    polyFun_rawRestrictGens)).comp polyFun_tidyGens
  have hrep := (hw.pair ((hw.pair ((hd.pair hr).comp polyFun_normPerm)).comp
    polyFun_rawRestrictPerm)).comp polyFun_normPerm
  exact ((((psnd polyFun_snd).pair polyFun_id).comp
    (PolyFun.optionElim (polyFun_const none) ((hgens.pair hrep).comp polyFun_some)))).of_eq
      (fun p => by cases ha : p.2.2 <;> simp [topwCosetImage, ha])

end Algo
