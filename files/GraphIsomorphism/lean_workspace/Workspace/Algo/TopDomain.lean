import Workspace.Algo.TopFourAction

/-! # Explicit domain labels in the top-action tree
Conjugation by a supplied domain equivalence transports candidate sets,
windows, strings, and each Chain Rule call. The statements retain the exact
ordered calls, not only the final isomorphism set.
-/
namespace Algo
open Babai Equiv
open scoped Pointwise Classical

noncomputable def topdInstance {Ω Ω' A : Type*} (e : Ω ≃ Ω') (J : SIInstance Ω A) : SIInstance Ω' A :=
  ⟨e.permCongr '' J.K, e '' J.Δ, J.x ∘ e.symm, J.y ∘ e.symm⟩

 theorem topd_wIso {Ω Ω' A : Type*} (e : Ω ≃ Ω') (Δ : Set Ω) (C : Set (Perm Ω)) (x y : Ω → A) :
    wIso (e '' Δ) (e.permCongr '' C) (x ∘ e.symm) (y ∘ e.symm) = e.permCongr '' wIso Δ C x y := by
  ext r
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, h⟩
    refine ⟨g, ⟨hg, fun u hu => ?_⟩, rfl⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.permCongr_apply] using h (e u) ⟨u, hu, rfl⟩
  · rintro ⟨g, ⟨hg, h⟩, rfl⟩
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.permCongr_apply] using h u hu

 theorem topdInstance_answer {Ω Ω' A : Type*} (e : Ω ≃ Ω') (J : SIInstance Ω A) :
    (topdInstance e J).answer = e.permCongr '' J.answer := topd_wIso e J.Δ J.K J.x J.y

 theorem topd_strIso {Ω Ω' A : Type*} (e : Ω ≃ Ω') (C : Set (Perm Ω)) (x y : Ω → A) :
    strIso (e.permCongr '' C) (x ∘ e.symm) (y ∘ e.symm) = e.permCongr '' strIso C x y := by
  have h := topd_wIso e Set.univ C x y
  have he : e '' (Set.univ : Set Ω) = Set.univ := Set.image_univ_of_surjective e.surjective
  simpa only [he, wIso_univ] using h

 theorem topd_chain {Ω Ω' A : Type*} (e : Ω ≃ Ω') (x y : Ω → A) :
    ∀ (ws : List (Set Ω)) (C : Set (Perm Ω)),
      (Babai.cosetChain (x ∘ e.symm) (y ∘ e.symm) (ws.map (fun W => e '' W)) (e.permCongr '' C)).calls =
        (Babai.cosetChain x y ws C).calls.map (topdInstance e) ∧
      (Babai.cosetChain (x ∘ e.symm) (y ∘ e.symm) (ws.map (fun W => e '' W)) (e.permCongr '' C)).run =
        e.permCongr '' (Babai.cosetChain x y ws C).run := by
  intro ws
  induction ws with
  | nil => intro C; exact ⟨rfl, rfl⟩
  | cons W ws ih =>
    intro C
    by_cases hC : C = ∅
    · subst C
      simp only [List.map_cons, Set.image_empty, Babai.cosetChain, if_true, SIReduction.calls_done,
        List.map_nil, SIReduction.run_done]
      exact ⟨True.intro, True.intro⟩
    · have hC' : e.permCongr '' C ≠ ∅ := fun hn => hC (Set.image_eq_empty.mp hn)
      simp only [List.map_cons, Babai.cosetChain, if_neg hC, if_neg hC',
        SIReduction.calls_call, SIReduction.run_call, List.map_cons]
      have ha : (⟨e.permCongr '' C, e '' W, x ∘ e.symm, y ∘ e.symm⟩ : SIInstance Ω' A).answer =
          e.permCongr '' (⟨C, W, x, y⟩ : SIInstance Ω A).answer := topd_wIso e W C x y
      rw [ha]
      exact ⟨congrArg (List.cons (topdInstance e ⟨C, W, x, y⟩)) (ih _).1, (ih _).2⟩

/-- The algebraic compatibility of two representations in supplied domain labels. -/
structure TopdCompat {Ω Ω' : Type*} {m : ℕ} (e : Ω ≃ Ω')
    {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Ω')}
    (ϕ : G →* Perm (Fin m)) (ψ : H →* Perm (Fin m)) where
  group : G ≃* H
  coe : ∀ g : G, (group g : Perm Ω') = e.permCongr (g : Perm Ω)
  hom : ∀ g : G, ψ (group g) = ϕ g

namespace TopdCompat
variable {Ω Ω' : Type*} {m : ℕ} {e : Ω ≃ Ω'}
    {G : Subgroup (Perm Ω)} {H : Subgroup (Perm Ω')}
    {ϕ : G →* Perm (Fin m)} {ψ : H →* Perm (Fin m)} (h : TopdCompat e ϕ ψ)
include h

 theorem group_image : e.permCongr '' (G : Set (Perm Ω)) = (H : Set (Perm Ω')) := by
  ext r
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← h.coe ⟨g, hg⟩]
    exact (h.group ⟨g, hg⟩).2
  · intro hr
    obtain ⟨g, hg⟩ := h.group.surjective ⟨r, hr⟩
    exact ⟨g, g.2, (h.coe g).symm.trans (congrArg Subtype.val hg)⟩

 theorem preimage (σ : Perm (Fin m)) : e.permCongr '' preimageSet ϕ σ = preimageSet ψ σ := by
  ext r
  constructor
  · rintro ⟨g, ⟨hg, hσ⟩, rfl⟩
    have he := h.coe ⟨g, hg⟩
    refine ⟨by rw [← he]; exact (h.group ⟨g, hg⟩).2, ?_⟩
    have hh := (h.hom ⟨g, hg⟩).trans hσ
    exact (congrArg ψ (Subtype.ext he)).symm.trans hh
  · rintro ⟨hr, hσ⟩
    obtain ⟨g, hg⟩ := h.group.surjective ⟨r, hr⟩
    refine ⟨g, ⟨g.2, ?_⟩, (h.coe g).symm.trans (congrArg Subtype.val hg)⟩
    rw [← h.hom, hg]
    exact hσ

 theorem kernel : e.permCongr '' (kerSubgroup ϕ : Set (Perm Ω)) = (kerSubgroup ψ : Set (Perm Ω')) := by
  rw [← preimageSet_one ϕ, ← preimageSet_one ψ]
  exact h.preimage 1

 theorem range : ϕ.range = ψ.range := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨h.group g, h.hom g⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := h.group.surjective g
    exact ⟨a, (h.hom a).symm⟩

 theorem homImage (C : Set (Perm Ω)) :
    Babai.homImage ψ (e.permCongr '' C) = Babai.homImage ϕ C := by
  ext σ
  constructor
  · rintro ⟨r, ⟨g, hg, he⟩, hr, hσ⟩
    obtain ⟨a, ha⟩ := h.group.surjective ⟨r, hr⟩
    have hag : (a : Perm Ω) = g := e.permCongr.injective
      ((h.coe a).symm.trans ((congrArg Subtype.val ha).trans he.symm))
    refine ⟨a, hag ▸ hg, a.2, ?_⟩
    rw [← h.hom, ha]
    exact hσ
  · rintro ⟨g, hg, hG, hσ⟩
    refine ⟨h.group ⟨g, hG⟩, ⟨g, hg, (h.coe ⟨g, hG⟩).symm⟩, (h.group ⟨g, hG⟩).2, ?_⟩
    exact (h.hom _).trans hσ

 theorem mapsOntoGiant (x : Ω → ℕ) : MapsOntoGiant ψ (x ∘ e.symm) ↔ MapsOntoGiant ϕ x := by
  unfold MapsOntoGiant strAut
  rw [← h.group_image, topd_strIso, h.homImage]

end TopdCompat
end Algo
